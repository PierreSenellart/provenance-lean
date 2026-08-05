DOCOUT      = .lake/build/doc
DEPLOY_HOST = provsql:/var/www/provsql/lean-docs/
BRANDING    = ../../provsql/branding
DOCS_URL    = https://provsql.org/lean-docs

# `deploy-ci` takes the newest successful run of this workflow on this branch,
# unless a run id is given: `make deploy-ci RUN=1234567890`.
DOCS_WORKFLOW = docs.yml
DOCS_BRANCH   = main
DOCS_ARTIFACT = docs-site
RUN          ?=

# Per-declaration dependency figures, from result-graph. Entirely optional: if
# the binary is not built, `make docs` produces exactly what it did before.
# Point RESULT_GRAPH_REPO elsewhere if your checkout is not a sibling of this one.
RESULT_GRAPH_REPO ?= ../../result-graph
RESULT_GRAPH      := $(abspath $(RESULT_GRAPH_REPO)/.lake/build/bin/result-graph)
RG_INJECT         := $(abspath $(RESULT_GRAPH_REPO)/scripts/inject-docs.py)
RG_CSS            := $(abspath $(RESULT_GRAPH_REPO)/scripts/result-graph.css)
RG_OUT            := .lake/build/result-graph
LEAN_SOURCES      := $(shell find .. -name '*.lean' -not -path '../.lake/*' \
                       -not -path '../docbuild/*')

docs: graphs
	# Force a fresh HTML stitching step: `lake build Provenance:docs` can
	# otherwise reuse a stale "library built" marker that pre-dates a newly
	# added module (the underlying .olean/docInfo artifacts are still
	# cached, so the cost is just the final fromDb HTML pass).
	rm -f .lake/build/doc-data/Provenance--library.docs_built
	# Same for the bibliography prepass, for a sharper reason: the output Lake
	# tracks for it sits in doc-data/, but the files it really emits –
	# doc/references.bib and doc/declarations/references.json – sit under doc/.
	# Carry doc-data/ over without doc/, as CI does when it caches the database
	# alone, and Lake finds the prepass up to date while its real outputs are
	# absent, so the final fromDb pass dies on a missing doc/references.bib.
	# This repository has a 200-entry bibliography, so it would hit that on the
	# first cache hit. Re-running the prepass is cheap.
	rm -f .lake/build/doc-data/references.json
	lake build Provenance:docs
	# Remove previously appended theme (if lake cached style.css)
	sed -i '/\/\* ProvSQL branding overrides/,$$d' $(DOCOUT)/style.css
	cat provsql-theme.css >> $(DOCOUT)/style.css
	# Replace Lean's default favicon with the ProvSQL one, when a provsql
	# checkout is at hand. Conditional, as the result-graph block below is: the
	# documentation must build without a sibling checkout (CI clones one, but a
	# plain local build should not be a hard failure).
	@if [ -f "$(BRANDING)/favicon.ico" ]; then \
	  cp "$(BRANDING)/favicon.ico" $(DOCOUT)/favicon.ico; \
	  find $(DOCOUT) -name '*.html' -exec sed -i \
	    -e 's|rel="icon" href="\([^"]*\)favicon\.svg"|rel="icon" href="\1favicon.ico"|g' \
	    -e 's|<link rel="mask-icon" href="[^"]*favicon\.svg"[^>]*> *||g' {} + ; \
	else \
	  echo "note: no favicon at $(BRANDING) – keeping the Lean default"; \
	fi
	# Inject site-wide footer nav into each HTML page (idempotent)
	find $(DOCOUT) -name '*.html' -exec perl inject-footer.pl {} \;
	# Backward-compat anchor: the ICDE 2026 paper hard-codes a Lean link
	# to QueryRewriting.html#query.Rewriting (typo: lowercase q, capital R).
	# Inject an empty <a id="query.Rewriting"> ahead of the real
	# Query.rewriting declaration so the fragment still scrolls there.
	# Idempotent: skipped on lines that already contain "query.Rewriting".
	perl -i -pe 's|<div class="decl" id="Query\.rewriting"|<a id="query.Rewriting"></a><div class="decl" id="Query.rewriting"| unless /query\.Rewriting/' $(DOCOUT)/Provenance/QueryRewriting.html
	# …and check that it actually landed. A `perl -i -pe` that matches nothing
	# exits successfully, so without this the anchor would die silently the day
	# `Query.rewriting` is renamed – and it is a link in a published PDF.
	@grep -q 'id="query\.Rewriting"' $(DOCOUT)/Provenance/QueryRewriting.html || { \
	  echo "error: the query.Rewriting back-compat anchor was not injected."; \
	  echo "       Its hook is <div class=\"decl\" id=\"Query.rewriting\">, so the"; \
	  echo "       declaration was renamed or moved. The ICDE 2026 paper links to"; \
	  echo "       that fragment; restore the name, or re-point the substitution."; \
	  exit 1; }
	# Dependency figure at the foot of each declaration, folded away by
	# default. Idempotent, and skipped entirely when result-graph is absent,
	# so this cannot break a docs build. Undo with `make ungraph`.
	@if [ -d "$(RG_OUT)/svg" ]; then \
	  cat "$(RG_CSS)" >> $(DOCOUT)/style.css && \
	  "$(RG_INJECT)" --doc $(DOCOUT) --graphs $(RG_OUT)/svg; \
	else \
	  echo "note: no figures in $(RG_OUT)/svg – skipping"; \
	fi
	# What is in this tree, in one line, so that "what is actually live?" is
	# answerable with curl. `docs-stale.yml` reads it off the deployed site and
	# compares with origin/main.
	@printf 'commit=%s date=%s toolchain=%s\n' \
	  "$$(git -C .. rev-parse HEAD)" \
	  "$$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
	  "$$(tr -d '[:space:]' < lean-toolchain)" > $(DOCOUT)/BUILD-INFO
	@cat $(DOCOUT)/BUILD-INFO
	# Layer 1 of the paper-link check, against the tree just built: a rename
	# fails here, before a broken site is ever deployed.
	@bash ../scripts/check-anchors.sh --tree $(DOCOUT)

# The graph of the whole library. Importing Mathlib is the slow part (about a
# minute), so it is redone only when a source file, or result-graph itself,
# changed. The $(wildcard) is what makes the whole feature optional: with no
# result-graph checkout there is simply no prerequisite, and the guard below
# turns the recipe into a no-op.
$(RG_OUT)/deps.json: $(LEAN_SOURCES) $(wildcard $(RESULT_GRAPH))
	@if [ ! -x "$(RESULT_GRAPH)" ]; then \
	  echo "note: no result-graph at $(RESULT_GRAPH) – skipping dependency figures"; \
	  exit 0; \
	fi; \
	set -e; mkdir -p $(RG_OUT); \
	cd .. && LEAN_PATH="$$(find .lake -type d -path '*/build/lib/lean' | tr '\n' ':')" \
	  "$(RESULT_GRAPH)" --root Provenance --json docbuild/$@ --stats

# One figure per declaration. `dot` runs once per declaration, so this is the
# expensive step; radius 2 keeps them small (median 6 nodes for this library).
# Cleaned first, or declarations you deleted leave orphan SVGs behind.
$(RG_OUT)/svg: $(RG_OUT)/deps.json
	@if [ ! -f "$<" ]; then exit 0; fi; \
	set -e; rm -rf $@; \
	"$(RESULT_GRAPH)" --from-json $< --all $@ --render \
	  --depth 2 --dir uses --reduce --url-base $(DOCS_URL); \
	touch $@

graphs: $(RG_OUT)/svg

ungraph:
	"$(RG_INJECT)" --doc $(DOCOUT) --remove

# Full local build, then publish. The fallback: it needs the whole Mathlib
# closure documented locally, which is some thirty minutes cold.
deploy: docs
	rsync -avzP --delete-after $(DOCOUT)/ $(DEPLOY_HOST)

# The normal path. `provsql.org` is rsync-writable from Pierre's machine only,
# so CI builds the site and uploads it as one artefact; this downloads the
# newest such build and publishes it. Everything before the rsync is a check:
# an artefact that is not a documentation tree must not reach the server.
deploy-ci:
	@command -v gh >/dev/null || { echo "deploy-ci needs the gh CLI"; exit 1; }
	@set -e; \
	tmp=$$(mktemp -d); trap 'rm -rf "$$tmp"' EXIT; \
	run="$(RUN)"; \
	if [ -z "$$run" ]; then \
	  run=$$(gh run list --workflow $(DOCS_WORKFLOW) --branch $(DOCS_BRANCH) \
	           --status success --limit 1 --json databaseId -q '.[0].databaseId'); \
	fi; \
	[ -n "$$run" ] || { echo "no successful $(DOCS_WORKFLOW) run on $(DOCS_BRANCH); pass RUN=<id>"; exit 1; }; \
	echo "Downloading artefact $(DOCS_ARTIFACT) from run $$run…"; \
	gh run download "$$run" -n $(DOCS_ARTIFACT) -D "$$tmp"; \
	mkdir -p "$$tmp/site"; \
	tar xzf "$$tmp/docs.tar.gz" -C "$$tmp/site"; \
	[ -f "$$tmp/site/Provenance.html" ] || { echo "no Provenance.html in the artefact"; exit 1; }; \
	[ -r "$$tmp/site/BUILD-INFO" ] || { echo "no BUILD-INFO in the artefact"; exit 1; }; \
	bash ../scripts/check-anchors.sh --tree "$$tmp/site"; \
	echo; echo "About to deploy:"; cat "$$tmp/site/BUILD-INFO"; echo; \
	rsync -avz --delete-after "$$tmp/site/" $(DEPLOY_HOST); \
	echo; echo "Deployed $$(cat "$$tmp/site/BUILD-INFO")"

.PHONY: docs deploy deploy-ci graphs ungraph
