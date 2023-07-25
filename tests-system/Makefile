RAW_TARGETS=$(filter-out bulk, $(subst ./,,$(shell find . -mindepth 1 -maxdepth 1 -type d)))

TARGETS=\
	$(addsuffix /output, $(RAW_TARGETS)) \
	$(addsuffix /output.brief, $(RAW_TARGETS)) \
	$(addsuffix /output.lint, $(RAW_TARGETS)) \
	$(addsuffix /output.json, $(RAW_TARGETS))

fast: $(TARGETS)

all: $(TARGETS) bulk/output bulk/output.brief bulk/output.lint bulk/output.json

.PRECIOUS: %/output
%/output:
	-coverage run -p --rcfile=../coverage.cfg --branch \
		--data-file ../.coverage \
		../trlc.py $(dir $@) > $@

%/output.brief:
	-coverage run -p --rcfile=../coverage.cfg --branch \
		--data-file ../.coverage \
		../trlc.py --brief $(dir $@) > $@

%/output.lint:
	-coverage run -p --rcfile=../coverage.cfg --branch \
		--data-file ../.coverage \
		../trlc.py --lint --verify $(dir $@) > $@

%/output.json:
	-coverage run -p --rcfile=../coverage.cfg --branch \
		--data-file ../.coverage \
		../trlc.py --debug-api-dump $(dir $@) > $@