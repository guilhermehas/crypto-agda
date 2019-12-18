default: pdf

pdf:
	mkdir build
	cp *.lagda build
	cp -r /nix/store/kz6dgb8acmb6y3xsfdk38s0zs7wpm9jg-agda-prelude-d193a94bfac9505148cb5cd1b68d08a08260b59c/share/agda/* build
	chmod -R +w build
	cd build ; for file in *.lagda; do agda --no-default-libraries --latex $$file; done

install:
	mkdir -p $(out)/tex
	mv build/latex/ $(out)/tex

clean:
	rm -rf build
