default: pdf

pdf:
	mkdir build
	cp *.lagda build
	cp -r libraries/agda-prelude/src/* build
	cd build ; for file in *.lagda; do agda --no-default-libraries --latex $$file; done

install:
	mkdir -p $(out)/tex
	mv build/latex/ $(out)/tex

clean:
	rm -rf build
