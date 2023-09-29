.PHONY: docs test style lint package

lint: style
	@python3 -m pylint --rcfile=pylint3.cfg \
		--reports=no \
		--score=no \
		trlc trlc*.py lobster-*.py

style:
	@python3 -m pycodestyle trlc trlc*.py lobster-*.py

test: unit-tests system-tests
	make coverage
	util/check_local_modifications.sh

test-all: unit-tests system-tests-all
	make coverage
	util/check_local_modifications.sh

coverage:
	coverage combine -q
	coverage html --rcfile=coverage.cfg
	coverage report --rcfile=coverage.cfg --fail-under=94

unit-tests:
	coverage run -p \
                --branch --rcfile=coverage.cfg \
                --data-file .coverage \
                -m unittest discover -s tests-unit -v

system-tests:
	mkdir -p docs
	coverage run -p --rcfile=coverage.cfg --branch --data-file .coverage \
		./trlc-lrm-generator.py
	make -C tests-system -B -j8 fast

system-tests-all:
	mkdir -p docs
	coverage run -p --rcfile=coverage.cfg --branch --data-file .coverage \
		./trlc-lrm-generator.py
	make -C tests-system -B -j8 all

docs:
	rm -rf docs
	mkdir docs
	cp documentation/assets/bmw_favicon.ico docs/
	@util/rebuild_old_lrm.sh
	@python3 trlc-lrm-generator.py --tag
	@python3 -m util.mk_ast_hierarchy | \
		dot -Tsvg > docs/ast_hierarchy.svg
	@python3 -m util.mk_parser_hierarchy | \
		dot -Tsvg > docs/parser_hierarchy.svg
	@-make tracing
	@sphinx-build -c sphinx -b html . docs

package:
	@git clean -xdf
	@python3 setup.py sdist bdist_wheel
	@python3 setup.py bdist_wheel -p manylinux2014_x86_64

upload_main: package
	python3 -m twine upload --repository pypi dist/*

remove_dev:
	python3 -m util.release

github_release:
	git push
	python3 -m util.github_release

bump:
	python3 -m util.bump_version_post_release

full_release:
	make remove_dev
	git push
	make github_release
	make bump
	git push

requirements.lobster: language-reference-manual/lobster-trlc.conf \
                      language-reference-manual/lrm.rsl \
                      language-reference-manual/lrm.trlc
	lobster-trlc \
		--config-file=language-reference-manual/lobster-trlc.conf \
		--out requirements.lobster \
		language-reference-manual

code.lobster: $(wildcard trlc/*.py)
	lobster-python --out code.lobster trlc

unit-tests.lobster: $(wildcard tests-unit/*.py)
	lobster-python --activity --out unit-tests.lobster tests-unit

system-tests.lobster: $(wildcard tests-system/*/*.rsl) \
                      $(wildcard tests-system/*/*.check) \
                      $(wildcard tests-system/*/*.trlc) \
                      $(wildcard tests-system/*/tracing)
	python3 lobster-trlc-system-test.py

report.lobster: lobster.conf \
                requirements.lobster \
                code.lobster \
                system-tests.lobster \
		unit-tests.lobster
	lobster-report \
		--lobster-config=lobster.conf \
		--out=report.lobster
	lobster-online-report report.lobster

tracing: report.lobster
	mkdir -p docs
	lobster-html-report report.lobster --out=docs/tracing.html
	lobster-ci-report report.lobster
