default: pdf

pdf:
	mkdir -p docs/res
	cd docs && latexmk -interaction=nonstopmode -f -pdf -use-make -outdir=res main.tex

install:
	mkdir -p $(out)
	cp docs/res/main.pdf $(out)/thesis.pdf

clean:
	rm -rf docs/res
