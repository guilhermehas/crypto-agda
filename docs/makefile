default: pdf

pdf:
	rm -f main.pdf
	rm -rf ../src/build
	cd .. && nix-shell --command make
	mv res/main.pdf .

prepare: clean
	cd .. && nix-build
	cp -Lr ../result/tex/* .

local:
	latexmk -interaction=nonstopmode -f -pdf -use-make -outdir=. main.tex

clean:
	cd .. && make clean
