default: pdf

pdf:
	rm -f main.pdf
	cd .. && nix-shell --command "make"
	mv res/main.pdf .

clean:
	rm -rf res
