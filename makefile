default: pdf

pdf:
	cd docs && latexmk -f -pdf -use-make main.tex

install: pdf
	mkdir -p $(out)
	cp docs/main.pdf $(out)/thesis.pdf

clean:
	rm *.pdf; \
	rm *.log; \
	rm *.aux; \
	rm *latexmk; \
	rm *.toc; \
	rm *.fls; \
	rm -f agda.sty; \
	rm -rf latex; \
	rm *.ptb; \
	rm *.bbl; \
	rm *.blg; \
