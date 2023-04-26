.PHONY: docs test style lint package

lint: style
	@python3 -m pylint --rcfile=pylint3.cfg \
		--reports=no trlc trlc*.py

style:
	@python3 -m pycodestyle trlc trlc*.py

test:
	coverage run -p --rcfile=tests/coverage.cfg --branch --data-file tests/.coverage ./trlc-lrm-generator.py
	make -C tests -B -j6 fast

test-all:
	coverage run -p --rcfile=tests/coverage.cfg --branch --data-file tests/.coverage ./trlc-lrm-generator.py
	make -C tests -B -j6 all

docs:
	rm -rf docs
	sphinx-build -c sphinx -b html . docs
	@python3 trlc-lrm-generator.py

docs-and-commit: docs
	git add docs
	git commit -m "Re-generate documentation for release."

package:
	@git clean -xdf
	@python3 setup.py sdist bdist_wheel

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
	make docs-and-commit
	git push
	make package
	make upload_main
	make github_release
	make bump
	git push
