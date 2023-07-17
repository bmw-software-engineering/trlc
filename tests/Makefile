RAW_TARGETS=$(filter-out bulk, $(subst ./,,$(shell find . -mindepth 1 -maxdepth 1 -type d)))

TARGETS=\
	$(addsuffix /output, $(RAW_TARGETS)) \
	$(addsuffix /output.brief, $(RAW_TARGETS)) \
	$(addsuffix /output.lint, $(RAW_TARGETS)) \
	$(addsuffix /output.json, $(RAW_TARGETS))

fast: $(TARGETS)
	coverage combine
	coverage html --rcfile=coverage.cfg
	coverage report --rcfile=coverage.cfg --fail-under=93

all: $(TARGETS) bulk/output bulk/output.brief bulk/output.lint bulk/output.json
	coverage combine
	coverage html --rcfile=coverage.cfg
	coverage report --rcfile=coverage.cfg --fail-under=93

.PRECIOUS: %/output
%/output:
	-coverage run -p --rcfile=coverage.cfg --branch \
		../trlc.py $(dir $@) > $@

%/output.brief:
	-coverage run -p --rcfile=coverage.cfg --branch \
		../trlc.py --brief $(dir $@) > $@

%/output.lint:
	-coverage run -p --rcfile=coverage.cfg --branch \
		../trlc.py --lint --verify $(dir $@) > $@

%/output.json:
	-coverage run -p --rcfile=coverage.cfg --branch \
		../trlc.py --debug-api-dump $(dir $@) > $@
