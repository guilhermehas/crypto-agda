default: pdf

pdf:
	mkdir -p docs/res
	cd docs && latexmk -interaction=nonstopmode -f -pdf -use-make -outdir=res main.tex

install: pdf
	cd docs && cp -r res/* .

clean:
	rm -rf docs/main.pdf; \
	rm -rf docs/latex; \
	rm -rf docs/agda.sty \
	rm -rf docs/res; \
	rm -rf docs/latex; \
	rm -f docs/*.log; \
	rm -f docs/*.aux; \
	rm -f docs/*latexmk; \
	rm -f docs/*.toc; \
	rm -f docs/*.fls; \
	rm -f docs/*f agda.sty; \
	rm -f docs/*rf latex; \
	rm -f docs/*.ptb; \
	rm -f docs/*.bbl; \
	rm -f docs/*.blg; \
