DOCOUT      = .lake/build/doc
DEPLOY_HOST = provsql:/var/www/provsql/lean-docs/
BRANDING    = ../../provsql/branding

docs:
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

deploy: docs
	rsync -avzP --delete-after $(DOCOUT)/ $(DEPLOY_HOST)

.PHONY: docs deploy
