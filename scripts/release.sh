#!/usr/bin/env bash
# Release helper for provenance-lean. Ported from the sibling
# `descriptive-complexity` repository, whose `PACKAGING.md` records why the
# version cannot mirror Mathlib's; that rationale is not repeated here.
#
# What a tag is *for* differs, though, and that shapes the script. This library
# supports ProvSQL and the ProvSQL papers: a tag exists to freeze a state a
# paper's claims were checked against, so that a citation still resolves after
# the code has moved on or been rewritten. There is no downstream `require` to
# serve, so the README states no version *range* contract — versions are the
# library's own and `lean-toolchain` at each tag is authoritative. The
# minor-on-pin-move rule survives inside this script anyway, since `next-minor`
# costs nothing and `update.yml` wants it.
#
# One Mathlib version is pinned in *five* places here, one more than in
# descriptive-complexity, which is itself the fifth:
#
#   /lean-toolchain            /lakefile.lean          (the Mathlib `require`)
#   /docbuild/lean-toolchain   /docbuild/lakefile.toml (the doc-gen4 `rev`)
#   /lakefile.lean             (the descriptive-complexity `require`)
#
# Lake resolves one Mathlib per workspace, so this repository can only move to a
# Mathlib that descriptive-complexity has already released against. That
# ordering constraint is a gate in `next-pin`: "waiting for
# descriptive-complexity" is a normal outcome, not a failure.
#
#   release.sh check              verify every version/pin location agrees
#   release.sh next-pin           print the Mathlib tag to move to, if any
#   release.sh pins <tag> [dc]    move the five pins to <tag> (dc tag: auto)
#   release.sh next-minor         print the next minor library version
#   release.sh prepare <version>  bump the library version everywhere, then check
#   release.sh notes              print draft release notes for the current version
#   release.sh publish            tag the current commit and cut the GitHub release
#
# `check` and `next-minor` are offline and safe to run any time; `next-pin` and
# `pins` ask GitHub what exists; `pins` and `prepare` only edit tracked files and
# leave the commit to you; `publish` is the only step that touches origin.

set -euo pipefail

cd "$(dirname "$0")/.."

readonly REPO="PierreSenellart/provenance-lean"
readonly BRANCH="main"
readonly DC_REPO="PierreSenellart/descriptive-complexity"
# The frozen restatement of a published paper's claims (T1.8, layer 2). Its
# statements are fixed at publication and never edited to follow the library;
# only the proof terms may be re-plumbed. `check` compares the file against the
# hash recorded beside it, so an edit is a deliberate act that shows in a diff.
readonly PAPER_MODULE="Provenance/Papers/Icde2026.lean"
readonly PAPER_HASH="scripts/icde2026.sha256"

die() { printf 'error: %s\n' "$*" >&2; exit 1; }

# --- readers -----------------------------------------------------------------
# Each returns the version string recorded in one place, or the empty string.

lib_lakefile()   { grep -oP '(?<=version := v!")[^"]+' lakefile.lean; }
lib_citation()   { grep -oP '(?<=^version: ")[^"]+' CITATION.cff; }
lib_cff_date()   { grep -oP '(?<=^date-released: ")[^"]+' CITATION.cff; }
lib_readme_git() { grep -oP '(?<=provenance-lean" @ ")v[^"]+' README.md; }
# The release table is marked in the README rather than found by its shape:
# several other tables there have the same column count.
readme_table()   { sed -n '/^<!-- release-table -->$/,/^$/p' README.md; }
lib_readme_row() { readme_table | sed -n 's/^| `v\([^`]*\)`.*/\1/p' | head -1; }

pin_toolchain()  { grep -oP '(?<=leanprover/lean4:)\S+' lean-toolchain; }
pin_docbuild()   { grep -oP '(?<=leanprover/lean4:)\S+' docbuild/lean-toolchain; }
pin_mathlib()    { grep -oP '(?<=/ "mathlib" @ git ")[^"]+' lakefile.lean; }
pin_docgen()     { grep -oP '(?<=^rev = ")[^"]+' docbuild/lakefile.toml; }
pin_readme_row() {
  readme_table | sed -n 's/^| `[^`]*` | `leanprover\/lean4:\([^`]*\)`.*/\1/p' | head -1
}
# shields.io escapes a literal hyphen as `--`, so undo that before comparing.
pin_readme_badge() { grep -oP '(?<=/badge/Mathlib-)[^-][^)]*?(?=-blue\))' README.md | sed 's/--/-/g'; }

# The fifth pin: descriptive-complexity's own SemVer tag, and the README link
# that must name the same one.
dc_lakefile()    { grep -oP '(?<=descriptive-complexity" @ ")[^"]+' lakefile.lean; }
dc_readme()      { grep -oP '(?<=descriptive-complexity/releases/tag/)v[0-9][^)]*' README.md | head -1; }

# The concept DOI: minted once by Zenodo, then the same for every later version.
# Empty until the first release exists, which `check` reports as a skip.
doi_citation()   { grep -oP '(?<=value: ")10\.5281/zenodo\.[0-9]+' CITATION.cff | head -1; }
# Read the badge's *link target*, not its image URL: the image is a styling
# choice, the doi.org link is what must be right.
doi_readme()     { grep -oP '(?<=doi\.org/)10\.5281/zenodo\.[0-9]+' README.md | head -1; }

# --- check -------------------------------------------------------------------

report() { # name expected actual
  if [[ "$2" == "$3" ]]; then
    printf '  ok    %-34s %s\n' "$1" "$3"
  else
    printf '  FAIL  %-34s %s (expected %s)\n' "$1" "${3:-<missing>}" "$2"
    failed=1
  fi
}

skip() { printf '  skip  %-34s %s\n' "$1" "$2"; }

cmd_check() {
  local version pin failed=0
  version="$(lib_lakefile)" || die "no version in lakefile.lean"
  pin="$(pin_toolchain)"    || die "no toolchain in lean-toolchain"

  printf 'Library version (from lakefile.lean): %s\n' "$version"
  report "CITATION.cff version"          "$version"  "$(lib_citation)"
  report "README require (from git)"     "v$version" "$(lib_readme_git)"
  report "README release table, newest"  "$version"  "$(lib_readme_row)"

  printf 'Mathlib/toolchain pin (from lean-toolchain): %s\n' "$pin"
  report "docbuild/lean-toolchain"       "$pin" "$(pin_docbuild)"
  report "lakefile.lean mathlib require" "$pin" "$(pin_mathlib)"
  report "docbuild doc-gen4 rev"         "$pin" "$(pin_docgen)"
  report "README table, toolchain col"   "$pin" "$(pin_readme_row)"
  report "README Mathlib badge"          "$pin" "$(pin_readme_badge)"

  printf 'descriptive-complexity pin (from lakefile.lean): %s\n' "$(dc_lakefile)"
  report "README descriptive-complexity" "$(dc_lakefile)" "$(dc_readme)"

  printf 'Other:\n'
  if [[ -n "$(doi_citation)" ]]; then
    report "README DOI badge" "$(doi_citation)" "$(doi_readme)"
  else
    skip "README DOI badge" "no concept DOI yet (minted on the first release)"
  fi

  local today; today="$(date -u +%Y-%m-%d)"
  if [[ "$(lib_cff_date)" > "$today" ]]; then
    printf '  FAIL  %-34s %s is in the future\n' "CITATION.cff date-released" "$(lib_cff_date)"
    failed=1
  else
    printf '  ok    %-34s %s\n' "CITATION.cff date-released" "$(lib_cff_date)"
  fi

  if command -v cffconvert >/dev/null 2>&1; then
    if cffconvert --validate -i CITATION.cff >/dev/null 2>&1; then
      printf '  ok    %-34s valid CFF 1.2.0\n' "CITATION.cff schema"
    else
      printf '  FAIL  %-34s does not validate\n' "CITATION.cff schema"; failed=1
    fi
  else
    skip "CITATION.cff schema" "cffconvert not installed"
  fi

  # The frozen paper module. Its *statements* are the contract with a published
  # paper; the kernel checks that the library still proves them, and this checks
  # that nobody quietly reworded them into something easier.
  if [[ -f "$PAPER_HASH" ]]; then
    local want have
    want="$(cut -d' ' -f1 < "$PAPER_HASH")"
    have="$(sha256sum "$PAPER_MODULE" | cut -d' ' -f1)"
    if [[ "$want" == "$have" ]]; then
      printf '  ok    %-34s unchanged since publication\n' "$PAPER_MODULE"
    else
      printf '  FAIL  %-34s differs from %s\n' "$PAPER_MODULE" "$PAPER_HASH"
      printf '        The statements in that file are frozen: they are what a published\n'
      printf '        paper claims. Re-plumbing a *proof* is fine, and then the new hash\n'
      printf '        is deliberate — record it with:\n'
      printf '            sha256sum %s > %s\n' "$PAPER_MODULE" "$PAPER_HASH"
      printf '        Changing a *statement* is not; restore it instead.\n'
      failed=1
    fi
  else
    skip "$PAPER_MODULE" "no recorded hash yet"
  fi

  [[ $failed -eq 0 ]] || die "some locations disagree; fix them (or run: $0 prepare <version>)"
  printf '\nAll release metadata agrees.\n'
}

# --- pins --------------------------------------------------------------------
# Moving the Mathlib pin is the other half of a release; `next-pin` decides
# whether there is anything to move to, and `pins` performs the move. The
# library version is `prepare`'s business, below: a new pin always takes at
# least a minor bump, which is what `next-minor` computes.

# Lake's own order on version strings (`Lake/Util/Version.lean`): the numeric
# `major.minor.patch` first, then the *empty* suffix ranks highest, and two
# non-empty suffixes compare as plain strings. A leading `v` is ignored, so
# `v4.33.0-rc1 < v4.33.0 < v4.33.1`.
ver_lt() { # ver_lt A B -- true when A is strictly older than B
  local a="${1#v}" b="${2#v}" an as bn bs first
  an="${a%%-*}"; as="${a#"$an"}"; as="${as#-}"
  bn="${b%%-*}"; bs="${b#"$bn"}"; bs="${bs#-}"
  if [[ "$an" != "$bn" ]]; then
    [[ "$(printf '%s\n%s\n' "$an" "$bn" | sort -V | head -1)" == "$an" ]]
    return
  fi
  # Same numbers: a suffixed version is older than the unsuffixed one.
  [[ -n "$as" && -z "$bs" ]] && return 0
  if [[ -n "$as" && -n "$bs" ]]; then
    first="$(LC_ALL=C printf '%s\n%s\n' "$as" "$bs" | LC_ALL=C sort | head -1)"
    [[ "$first" == "$as" && "$as" != "$bs" ]]
    return
  fi
  return 1
}

cmd_next_minor() {
  local version major minor
  version="$(lib_lakefile)" || die "no version in lakefile.lean"
  IFS=. read -r major minor _ <<< "$version"
  printf '%d.%d.0\n' "$major" $((minor + 1))
}

# The newest descriptive-complexity release cut against a given Mathlib pin, or
# nothing. Its versions are its own SemVer, decoupled from the toolchain, so the
# only reliable test is to read `lean-toolchain` at each tag, newest first.
dc_tag_for() { # dc_tag_for <mathlib tag>
  local pin="$1" tag toolchain
  command -v gh >/dev/null || die "finding the descriptive-complexity tag needs the gh CLI"
  while read -r tag; do
    [[ -n "$tag" ]] || continue
    toolchain="$(curl -fsSL \
      "https://raw.githubusercontent.com/$DC_REPO/$tag/lean-toolchain" 2>/dev/null \
      | tr -d '[:space:]')" || continue
    if [[ "$toolchain" == "leanprover/lean4:$pin" ]]; then
      printf '%s\n' "$tag"
      return 0
    fi
  done < <(gh api --paginate "repos/$DC_REPO/git/matching-refs/tags/v" \
             -q '.[].ref' 2>/dev/null | sed 's|^refs/tags/||' \
             | grep -E '^v[0-9]+\.[0-9]+\.[0-9]+$' | sort -Vr)
  return 1
}

# Prints the tag to move to on stdout, or nothing at all when the answer is
# "stay where you are"; everything else goes to stderr, so the caller can just
# test whether stdout is empty.
cmd_next_pin() {
  local pin latest mathlib_toolchain dc
  pin="$(pin_toolchain)" || die "no toolchain in lean-toolchain"
  command -v gh >/dev/null || die "next-pin needs the gh CLI"

  # Tags, not releases: Mathlib only started publishing GitHub releases in 2026,
  # and the tag is what the `require` names anyway. Stable lines only, since
  # main tracks a stable Mathlib.
  latest="$(gh api --paginate repos/leanprover-community/mathlib4/git/matching-refs/tags/v4. \
              -q '.[].ref' | sed 's|^refs/tags/||' \
              | grep -E '^v[0-9]+\.[0-9]+\.[0-9]+$' | sort -V | tail -1)" \
    || die "could not list the Mathlib tags"
  [[ -n "$latest" ]] || die "no stable Mathlib tag found"
  printf 'Pinned: %s. Newest stable Mathlib tag: %s.\n' "$pin" "$latest" >&2

  if ! ver_lt "$pin" "$latest"; then
    printf 'Nothing to move to: the pin is not older than that.\n' >&2
    return 0
  fi
  # A patch release *inside* the pinned line is deliberately not chased: Mathlib
  # cuts those often, and each would spend a minor bump here on no new content.
  # Take such a pin by hand when it fixes something the library needs. An rc
  # pin, on the other hand, is exactly what its own stable release supersedes,
  # so that move is offered.
  if [[ "$pin" != *-* && "${pin%.*}" == "${latest%.*}" ]]; then
    printf 'Nothing to do: %s is only a patch release of the pinned line.\n' "$latest" >&2
    return 0
  fi
  # All five pins move together, so refuse unless the whole set exists and
  # agrees: Mathlib's own toolchain at that tag, a doc-gen4 tag to match, and a
  # descriptive-complexity release cut against the same Mathlib.
  mathlib_toolchain="$(curl -fsSL \
    "https://raw.githubusercontent.com/leanprover-community/mathlib4/$latest/lean-toolchain" \
    | tr -d '[:space:]')" || die "could not read Mathlib's lean-toolchain at $latest"
  [[ "$mathlib_toolchain" == "leanprover/lean4:$latest" ]] \
    || die "Mathlib $latest is built with $mathlib_toolchain, so the pins do not
       share one version any more; move them by hand"
  if ! gh api "repos/leanprover/doc-gen4/git/ref/tags/$latest" >/dev/null 2>&1; then
    printf 'Waiting: doc-gen4 has no %s tag yet, so docbuild cannot follow.\n' "$latest" >&2
    return 0
  fi
  # The ordering constraint of decision 3: Lake builds one Mathlib per
  # workspace, so this repository cannot precede its own dependency. Saying so
  # and standing still is the *normal* outcome in the days after a Mathlib
  # release, not a failure.
  if ! dc="$(dc_tag_for "$latest")"; then
    printf 'Waiting for descriptive-complexity: no release of it is cut against Mathlib %s\n' "$latest" >&2
    printf 'yet, and Lake resolves one Mathlib per workspace. Release it there first.\n' >&2
    return 0
  fi
  printf 'descriptive-complexity %s is cut against %s.\n' "$dc" "$latest" >&2

  printf '%s\n' "$latest"
}

cmd_pins() {
  local ver="${1:-}" dc="${2:-}" old olddc
  [[ -n "$ver" ]] || die "usage: $0 pins <mathlib tag> [descriptive-complexity tag]"
  [[ "$ver" =~ ^v[0-9]+\.[0-9]+\.[0-9]+(-[0-9A-Za-z.]+)?$ ]] || die "not a Mathlib tag: $ver"
  old="$(pin_toolchain)" || die "no toolchain in lean-toolchain"
  olddc="$(dc_lakefile)" || die "no descriptive-complexity require in lakefile.lean"
  [[ "$ver" != "$old" ]] || die "already pinned to $ver"

  # The fifth pin is on its own version line, so it has to be looked up rather
  # than derived. `next-pin` already gated on this existing.
  if [[ -z "$dc" ]]; then
    dc="$(dc_tag_for "$ver")" \
      || die "no descriptive-complexity release is cut against Mathlib $ver;
       release it there first, or pass the tag explicitly as a second argument"
  fi

  printf 'leanprover/lean4:%s\n' "$ver" > lean-toolchain
  printf 'leanprover/lean4:%s\n' "$ver" > docbuild/lean-toolchain
  sed -i "s|\"mathlib\" @ git \"[^\"]*\"|\"mathlib\" @ git \"$ver\"|" lakefile.lean
  # The only `rev` in that file is doc-gen4's; the local package uses `path`.
  sed -i "s|^rev = \"[^\"]*\"|rev = \"$ver\"|" docbuild/lakefile.toml
  sed -i "s|descriptive-complexity\" @ \"[^\"]*\"|descriptive-complexity\" @ \"$dc\"|" lakefile.lean
  sed -i "s|descriptive-complexity/releases/tag/[^)]*|descriptive-complexity/releases/tag/$dc|" README.md

  printf 'Moved the Mathlib pin %s -> %s in the four Mathlib places,\n' "$old" "$ver"
  printf 'and descriptive-complexity %s -> %s in the fifth.\n\n' "$olddc" "$dc"
  printf 'Next: `lake update` (the manifest still records the old Mathlib), let the\n'
  printf 'build go green, then `%s prepare %s`. The README badge and table\n' "$0" "$(cmd_next_minor)"
  printf 'follow the pin from there, so `check` stays red until that runs.\n'
}

# --- prepare -----------------------------------------------------------------

cmd_prepare() {
  local version="${1:-}" old pin today
  [[ -n "$version" ]] || die "usage: $0 prepare <version>   (e.g. 1.0.1)"
  [[ "$version" =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]] \
    || die "version must be major.minor.patch with no suffix"

  old="$(lib_lakefile)"
  pin="$(pin_toolchain)"
  today="$(date -u +%Y-%m-%d)"
  [[ "$version" != "$old" ]] || die "lakefile.lean is already at $version"

  # There is no dependant to protect here, so this is a reminder of the scheme
  # rather than a contract: a pin move still takes at least a minor, which keeps
  # the tags legible and lets `update.yml` compute the number.
  if [[ "$pin" != "$(pin_readme_row)" && "${version%.*}" == "${old%.*}" ]]; then
    die "the Mathlib pin changed ($(pin_readme_row) -> $pin) but $version is only a patch bump;
       a new pin takes at least a minor bump"
  fi

  sed -i "s|version := v!\"$old\"|version := v!\"$version\"|" lakefile.lean
  sed -i "s|^version: \"$old\"|version: \"$version\"|"        CITATION.cff
  sed -i "s|^date-released: \".*\"|date-released: \"$today\"|" CITATION.cff
  sed -i "s|provenance-lean\" @ \"v$old\"|provenance-lean\" @ \"v$version\"|" README.md
  # Newest release first, directly under the marked table's header. The marker
  # is what disambiguates it: other tables in the README have four columns too.
  # The paper and DOI cells are left empty on purpose — a tag joins the paper
  # table only once the paper it supports is public, and the version DOI does
  # not exist until Zenodo has seen the release.
  sed -i "/^<!-- release-table -->$/{n;n;s@\$@\n| \`v$version\` | \`leanprover/lean4:$pin\` | – | – |@}" README.md
  # Badge tracks the pin; shields.io wants a literal hyphen doubled.
  sed -i "s|/badge/Mathlib-[^)]*-blue|/badge/Mathlib-${pin//-/--}-blue|" README.md
  sed -i "s|mathlib4/releases/tag/[^)]*|mathlib4/releases/tag/$pin|" README.md

  printf 'Bumped %s -> %s (Mathlib pin %s).\n\n' "$old" "$version" "$pin"
  cmd_check
  printf '\nReview the diff — the new release-table row has empty paper and DOI cells,\n'
  printf 'which is right until the paper is public and Zenodo has minted the version\n'
  printf 'DOI. Then commit and run: %s publish\n' "$0"
}

# --- notes -------------------------------------------------------------------
# A draft, not the final word: the commit subjects are one line each and read
# well as a changelog, but they are written for the log, not for a reader
# arriving at the release page. Curate before publishing — and describe what the
# release *proves*, never a paper that is not yet public.

cmd_notes() {
  local version pin tag prev
  version="$(lib_lakefile)"; pin="$(pin_toolchain)"; tag="v$version"
  # No previous tag (or none but this one) is not an error: the first release
  # simply has nothing to list. `|| true` keeps `pipefail` from treating the
  # empty grep as a failure.
  prev="$(git tag --sort=-creatordate | grep -v "^$tag\$" | head -1 || true)"

  printf 'Built with Mathlib `%s` and toolchain `leanprover/lean4:%s`.\n\n' "$pin" "$pin"
  if [[ -n "$prev" ]]; then
    printf '## Changes since %s\n\n' "$prev"
    git log --no-merges --reverse --pretty='- %s' "$prev..HEAD"
    printf '\n'
  fi
  printf '## Use\n\n```lean\nrequire "provenance" from git\n  "https://github.com/%s" @ "%s"\n```\n\n' \
    "$REPO" "$tag"
  printf 'This tag freezes a citable state of the library; `lean-toolchain` here is\n'
  printf 'authoritative for the Mathlib it was checked against. API documentation:\n'
  printf 'https://provsql.org/lean-docs/Provenance.html\n'
  [[ -z "$prev" ]] || printf '\n**Full changelog**: https://github.com/%s/compare/%s...%s\n' "$REPO" "$prev" "$tag"
}

# --- publish -----------------------------------------------------------------

cmd_publish() {
  local version pin tag
  version="$(lib_lakefile)"; pin="$(pin_toolchain)"; tag="v$version"

  cmd_check
  # -uno: this repo deliberately keeps untracked working notes at the root.
  [[ -z "$(git status --porcelain -uno)" ]] || die "tracked files have uncommitted changes"
  [[ "$(git rev-parse --abbrev-ref HEAD)" == "$BRANCH" ]] || die "not on $BRANCH"
  git fetch -q origin "$BRANCH"
  [[ "$(git rev-parse HEAD)" == "$(git rev-parse "origin/$BRANCH")" ]] \
    || die "HEAD and origin/$BRANCH differ; push first, and let CI go green"
  ! git rev-parse -q --verify "refs/tags/$tag" >/dev/null || die "tag $tag already exists"

  # Kept in .git/, so a draft is never mistaken for a tracked file.
  local notes_file=".git/RELEASE_NOTES-$tag.md"
  cmd_notes > "$notes_file"
  if [[ -t 0 ]]; then
    printf '\nDrafted release notes from the log into %s.\n' "$notes_file"
    read -r -p "Edit them in ${EDITOR:-vi} before publishing? [Y/n] " edit_reply || true
    [[ "$edit_reply" == "n" || "$edit_reply" == "N" ]] || "${EDITOR:-vi}" "$notes_file"
  fi
  printf '\n--- release notes ---\n'; cat "$notes_file"; printf -- '--- end notes -------\n'

  printf '\nAbout to publish %s (Mathlib %s) from %s.\n' "$tag" "$pin" "$(git rev-parse --short HEAD)"
  read -r -p 'This mints a permanent Zenodo DOI. Continue? [y/N] ' reply
  [[ "$reply" == "y" || "$reply" == "Y" ]] || die "aborted"

  git tag -a "$tag" -m "$tag – for Mathlib $pin"
  git push origin "$tag"
  gh release create "$tag" --repo "$REPO" \
    --title "$tag – for Mathlib $pin" \
    --notes-file "$notes_file"

  printf '\nReleased %s (Mathlib %s). Zenodo archives it on the release event, under the\n' "$tag" "$pin"
  printf 'concept DOI recorded in CITATION.cff, which covers every version; the release\n'
  printf 'also gets a *version* DOI, which is the one a paper should cite. Add it to the\n'
  printf 'README release table once Zenodo has minted it.\n'
}

case "${1:-}" in
  check)      cmd_check ;;
  next-pin)   cmd_next_pin ;;
  pins)       shift; cmd_pins "$@" ;;
  next-minor) cmd_next_minor ;;
  prepare)    shift; cmd_prepare "$@" ;;
  notes)      cmd_notes ;;
  publish)    cmd_publish ;;
  *) die "usage: $0 {check | next-pin | pins <tag> [dc tag] | next-minor | prepare <version> | notes | publish}" ;;
esac
