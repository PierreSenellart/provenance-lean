DOCOUT      = .lake/build/doc
DEPLOY_HOST = provsql:/var/www/provsql/lean-docs/

docs:
	lake build Provenance:docs
	cat provsql-theme.css >> $(DOCOUT)/style.css

deploy: docs
	rsync -avzP --delete-after $(DOCOUT)/ $(DEPLOY_HOST)

.PHONY: docs deploy
