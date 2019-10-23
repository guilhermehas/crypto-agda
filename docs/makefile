default: pdf

pdf:
	rm -f main.pdf
	rm -rf ../src/build
	cd .. && nix-shell --command "make"
	mv res/main.pdf .

clean:
	rm -rf res
