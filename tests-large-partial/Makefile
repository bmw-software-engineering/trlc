TESTS=$(wildcard */options)
TARGETS=$(patsubst %/options,%/output,$(TESTS))

all: $(TARGETS)
fast: $(TARGETS)

%/output: %/options
	-@coverage run -p --rcfile=../coverage.cfg --branch \
		--data-file ../.coverage \
		../trlc.py $(file < $<) \
		> $@ 2>&1

rebuild-canned-tests:
	rm -rf large
	../util/large-test-generator.py \
		--packages 50 \
		--max-files-per-package 5 \
		--max-items-per-package 1000 \
		--max-imports-per-package 4 \
		--max-links-per-item 10 \
		large
