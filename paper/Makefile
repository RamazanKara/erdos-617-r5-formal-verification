LATEXMK ?= latexmk
PDF := erdos617-r5-formal-verification.pdf
SOURCE_DATE_EPOCH ?= 1784851200

export SOURCE_DATE_EPOCH
export FORCE_SOURCE_DATE := 1
export TZ := UTC
export LC_ALL := C

.PHONY: all clean

all: $(PDF)

$(PDF): main.tex references.bib
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error -file-line-error \
		-jobname=erdos617-r5-formal-verification main.tex

clean:
	$(LATEXMK) -C -jobname=erdos617-r5-formal-verification main.tex
