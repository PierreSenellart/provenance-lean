DOCOUT      = .lake/build/doc
DEPLOY_HOST = provsql:/var/www/provsql/lean-docs/
BRANDING    = ../../provsql/branding

docs:
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

deploy: docs
	rsync -avzP --delete-after $(DOCOUT)/ $(DEPLOY_HOST)

.PHONY: docs deploy
