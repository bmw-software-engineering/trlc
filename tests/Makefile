TARGETS=$(addsuffix /output,$(filter-out bulk, $(subst ./,,$(shell find . -mindepth 1 -maxdepth 1 -type d))))

fast: $(TARGETS)
	coverage combine
	coverage html --rcfile=coverage.cfg
	coverage report --rcfile=coverage.cfg

all: $(TARGETS) bulk/output
	coverage combine
	coverage html --rcfile=coverage.cfg
	coverage report --rcfile=coverage.cfg

.PRECIOUS: %/output
%/output:
	-coverage run -p --rcfile=coverage.cfg --branch ../trlc.py $(dir $@) > $@
