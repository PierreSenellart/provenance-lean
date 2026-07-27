DOCOUT      = .lake/build/doc
DEPLOY_HOST = provsql:/var/www/provsql/lean-docs/
BRANDING    = ../../provsql/branding
DOCS_URL    = https://provsql.org/lean-docs

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
	lake build Provenance:docs
	# Remove previously appended theme (if lake cached style.css)
	sed -i '/\/\* ProvSQL branding overrides/,$$d' $(DOCOUT)/style.css
	cat provsql-theme.css >> $(DOCOUT)/style.css
	# Replace Lean default favicon with ProvSQL favicon
	cp $(BRANDING)/favicon.ico $(DOCOUT)/favicon.ico
	find $(DOCOUT) -name '*.html' -exec sed -i \
	  -e 's|rel="icon" href="\([^"]*\)favicon\.svg"|rel="icon" href="\1favicon.ico"|g' \
	  -e 's|<link rel="mask-icon" href="[^"]*favicon\.svg"[^>]*> *||g' {} +
	# Inject site-wide footer nav into each HTML page (idempotent)
	find $(DOCOUT) -name '*.html' -exec perl inject-footer.pl {} \;
	# Backward-compat anchor: the ICDE 2026 paper hard-codes a Lean link
	# to QueryRewriting.html#query.Rewriting (typo: lowercase q, capital R).
	# Inject an empty <a id="query.Rewriting"> ahead of the real
	# Query.rewriting declaration so the fragment still scrolls there.
	# Idempotent: skipped on lines that already contain "query.Rewriting".
	perl -i -pe 's|<div class="decl" id="Query\.rewriting"|<a id="query.Rewriting"></a><div class="decl" id="Query.rewriting"| unless /query\.Rewriting/' $(DOCOUT)/Provenance/QueryRewriting.html
	# Dependency figure at the foot of each declaration, folded away by
	# default. Idempotent, and skipped entirely when result-graph is absent,
	# so this cannot break a docs build. Undo with `make ungraph`.
	@if [ -d "$(RG_OUT)/svg" ]; then \
	  cat "$(RG_CSS)" >> $(DOCOUT)/style.css && \
	  "$(RG_INJECT)" --doc $(DOCOUT) --graphs $(RG_OUT)/svg; \
	else \
	  echo "note: no figures in $(RG_OUT)/svg — skipping"; \
	fi

# The graph of the whole library. Importing Mathlib is the slow part (about a
# minute), so it is redone only when a source file, or result-graph itself,
# changed. The $(wildcard) is what makes the whole feature optional: with no
# result-graph checkout there is simply no prerequisite, and the guard below
# turns the recipe into a no-op.
$(RG_OUT)/deps.json: $(LEAN_SOURCES) $(wildcard $(RESULT_GRAPH))
	@if [ ! -x "$(RESULT_GRAPH)" ]; then \
	  echo "note: no result-graph at $(RESULT_GRAPH) — skipping dependency figures"; \
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

deploy: docs
	rsync -avzP --delete-after $(DOCOUT)/ $(DEPLOY_HOST)

.PHONY: docs deploy graphs ungraph
