default: pdf slide

pdf:
	mkdir -p docs/res
	cd docs && latexmk -interaction=nonstopmode -f -pdf -use-make -outdir=res main.tex

slide:
	mkdir -p slides/res
	cd slides && latexmk -interaction=nonstopmode -f -pdf -use-make -outdir=res main.tex

install:
	mkdir -p $(out)/tex/latex
	bash copylatexout.bash $(out)/tex/latex $(out)/tex
	cp docs/res/main.pdf $(out)/thesis.pdf
	cp slides/res/main.pdf $(out)/slides.pdf

clean:
	rm -rf {slides,docs}/{main.pdf,res,latex,agda.sty}
	for ext in {log,aux,latexmk,toc,fls,ptb,bbl,blg,fdb_latexmk,nav,out,snm}; \
	do rm -f {slides,docs}/*.$$ext ; done
