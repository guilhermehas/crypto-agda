default: pdf

pdf:
	mkdir build
	cp main.lagda build
	cp -r libraries/agda-prelude/src/* build
	cd ./build && pwd && ls && agda --no-default-libraries --latex main.lagda

install:
	mkdir -p $(out)/tex
	mv build/latex/* $(out)/tex

clean:
	rm -rf build
