.PHONY: docs test style lint package

lint: style
	@python3 -m pylint --rcfile=pylint3.cfg \
		--reports=no trlc

style:
	@python3 -m pycodestyle trlc

test:
	make -C tests -B -j6 fast

test-all:
	make -C tests -B -j6 all

docs:
	rm -rf docs
	sphinx-build -c sphinx -b html . docs
	git add docs

package:
	@git clean -xdf
	@python3 setup.py sdist bdist_wheel

release:
	python3 -m util.release

github_release:
	git push
	python3 -m util.github_release

bump:
	python3 -m util.bump_version_post_release
