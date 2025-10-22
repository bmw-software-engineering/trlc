RAW_TARGETS=$(if $(TARGET),$(TARGET),$(filter-out bulk, $(subst ./,,$(shell find . -mindepth 1 -maxdepth 1 -type d))))

TARGETS=\
	$(addsuffix /output, $(RAW_TARGETS)) \
	$(addsuffix /output.smtlib, $(RAW_TARGETS)) \
	$(addsuffix /output.brief, $(RAW_TARGETS)) \
	$(addsuffix /output.json, $(RAW_TARGETS))

fast: $(TARGETS)

all: $(TARGETS) bulk/output bulk/output.brief bulk/output.json

.PRECIOUS: %/output
%/output:
	-@coverage run -p --rcfile=../coverage.cfg --branch \
		--data-file ../.coverage \
		../trlc.py --verify $(file < $(dir $@)options) \
			$(dir $@) > $@ 2>&1

%/output.smtlib:
	-@coverage run -p --rcfile=../coverage.cfg --branch \
		--data-file ../.coverage \
		../trlc.py --verify --use-cvc5-binary=cvc5 \
			$(file < $(dir $@)options) \
			$(dir $@) > $@ 2>&1

%/output.brief:
	-@coverage run -p --rcfile=../coverage.cfg --branch \
		--data-file ../.coverage \
		../trlc.py $(file < $(dir $@)options) \
			--no-lint --brief $(dir $@) > $@ 2>&1

%/output.json:
	-@coverage run -p --rcfile=../coverage.cfg --branch \
		--data-file ../.coverage \
		../trlc.py $(file < $(dir $@)options) \
			--no-lint --debug-api-dump $(dir $@) > $@ 2>&1
