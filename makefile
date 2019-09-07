default: pdf

pdf:
	latexmk -f -pdf -use-make docs/main.tex

install: pdf
	mkdir -p $(out)
	cp main.pdf $(out)/texto-qualificacao.pdf

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
