RAW_TARGETS=$(filter-out bulk, $(subst ./,,$(shell find . -mindepth 1 -maxdepth 1 -type d)))

TARGETS=$(addsuffix /output, $(RAW_TARGETS)) $(addsuffix /output.brief, $(RAW_TARGETS))

fast: $(TARGETS)
	coverage combine
	coverage html --rcfile=coverage.cfg
	coverage report --rcfile=coverage.cfg

all: $(TARGETS) bulk/output bulk/output.brief
	coverage combine
	coverage html --rcfile=coverage.cfg
	coverage report --rcfile=coverage.cfg

.PRECIOUS: %/output
%/output:
	-coverage run -p --rcfile=coverage.cfg --branch ../trlc.py $(dir $@) > $@

%/output.brief:
	-coverage run -p --rcfile=coverage.cfg --branch ../trlc.py --brief $(dir $@) > $@
