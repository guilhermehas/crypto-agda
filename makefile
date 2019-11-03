default: pdf

pdf:
	mkdir -p docs/res
	cd docs && latexmk -interaction=nonstopmode -f -pdf -use-make -outdir=res main.tex

install:
	mkdir -p $(out)/tex/latex
	bash copylatexout.bash $(out)/tex/latex $(out)/tex
	cp docs/res/main.pdf $(out)/thesis.pdf

clean:
	rm docs/main.pdf; \
	rm -rf docs/latex; \
	rm docs/agda.sty \
	rm -rf docs/res; \
	rm docs/*.log; \
	rm docs/*.aux; \
	rm docs/*latexmk; \
	rm docs/*.toc; \
	rm docs/*.fls; \
	rm docs/*f agda.sty; \
	rm docs/*rf latex; \
	rm docs/*.ptb; \
	rm docs/*.bbl; \
	rm docs/*.blg; \
