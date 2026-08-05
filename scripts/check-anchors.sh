#!/usr/bin/env bash
# Layer 1 of the paper-link durability check: the anchors a published paper
# hard-codes still exist.
#
# There is one published documentation tree, tracking `main`, so a paper's links
# deliberately reach material that has grown beyond the paper. What must hold is
# narrower: the page is still there, and the fragment still names something on
# it. Generalization is expected; a rename or a disappearance is not.
#
# The list is not maintained here. It lives in the frozen paper module
# `Provenance/Papers/Icde2026.lean`, one `Anchor:` line per docstring, next to
# the theorem that restates the claim the anchor points at – which is what ties
# the two layers together: layer 2 pins the content, layer 1 pins the link, and
# they cannot drift apart because they are written in the same place. The paper
# itself defines `\lean{module}{decl}` and `\leanmain`, so
#
#     grep -ohE '\\lean\{[^}]*\}\{[^}]*\}|\\leanmain' *.tex | sort -u
#
# over its sources regenerates the list exactly; that is how it was derived, and
# how it should be re-derived if the paper's links ever change.
#
#   check-anchors.sh --tree docbuild/.lake/build/doc
#   check-anchors.sh --site https://provsql.org/lean-docs
#
# Run in both places, for different reasons: against the freshly built tree in
# `docs.yml`, so a rename fails CI *before* a broken site is deployed; and
# against the live site in the daily staleness job, which catches a deploy that
# never happened.

set -euo pipefail

readonly SOURCE="Provenance/Papers/Icde2026.lean"

die() { printf 'error: %s\n' "$*" >&2; exit 1; }

usage() { die "usage: $0 (--tree <doc directory> | --site <base URL>)"; }

mode="" target=""
case "${1:-}" in
  --tree) mode=tree; target="${2:-}" ;;
  --site) mode=site; target="${2:-}" ;;
  *) usage ;;
esac
[[ -n "$target" ]] || usage
target="${target%/}"

# Resolve a directory target *before* moving to the repository root: `make docs`
# calls this from `docbuild/` with a path relative to there.
if [[ "$mode" == tree ]]; then
  [[ -d "$target" ]] || die "no such directory: $target"
  target="$(cd "$target" && pwd)"
fi

cd "$(dirname "$0")/.."

[[ -f "$SOURCE" ]] || die "$SOURCE is missing: it is where the anchor list lives"

# `Anchor: <page>` or `Anchor: <page>#<fragment>`, one per line, from the
# docstrings of the frozen module.
mapfile -t anchors < <(grep -oP '(?<=^Anchor: )\S+' "$SOURCE" || true)
[[ ${#anchors[@]} -gt 0 ]] || die "no 'Anchor:' lines in $SOURCE"

printf 'Checking %d anchors from %s against %s %s\n\n' \
  "${#anchors[@]}" "$SOURCE" "$mode" "$target"

# Fetches one page's HTML to stdout, or fails.
fetch() { # fetch <page>
  case "$mode" in
    tree) cat "$target/$1" ;;
    site) curl -fsSL --max-time 60 "$target/$1" ;;
  esac
}

failed=0
declare -A page_cache=()

for anchor in "${anchors[@]}"; do
  page="${anchor%%#*}"
  frag=""
  [[ "$anchor" == *"#"* ]] && frag="${anchor#*#}"

  if [[ -z "${page_cache[$page]+set}" ]]; then
    if html="$(fetch "$page" 2>/dev/null)"; then
      page_cache["$page"]="$html"
    else
      page_cache["$page"]=""
    fi
  fi
  html="${page_cache[$page]}"

  if [[ -z "$html" ]]; then
    printf '  FAIL  %-60s page not found\n' "$anchor"
    failed=1
    continue
  fi
  if [[ -z "$frag" ]]; then
    printf '  ok    %-60s page present\n' "$anchor"
    continue
  fi
  # doc-gen4 renders a declaration as `<div class="decl" id="Name">`; the
  # hand-injected back-compat anchor is a bare `<a id="…"></a>`. Matching the
  # `id="…"` attribute alone covers both, and is what a browser resolves.
  if grep -qF "id=\"$frag\"" <<< "$html"; then
    printf '  ok    %-60s\n' "$anchor"
  else
    printf '  FAIL  %-60s fragment absent from the page\n' "$anchor"
    failed=1
  fi
done

if [[ $failed -ne 0 ]]; then
  printf '\n'
  die "some anchors a published paper hard-codes no longer resolve.
       A link in a PDF cannot be fixed after the fact, so the declaration has to
       keep its name and its module: restore them, and if a declaration really
       must move, leave the old anchor behind (see the back-compat injection in
       docbuild/Makefile)."
fi

printf '\nAll %d anchors resolve.\n' "${#anchors[@]}"
