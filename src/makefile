default: pdf

pdf:
	mkdir build
	cp *.lagda build
	cp -r libraries/agda-prelude/src/* build
	cd ./build && pwd && ls \
	&& agda --no-default-libraries --latex agdaExamples.lagda \
	&& agda --no-default-libraries --latex Cripto.lagda

install:
	mkdir -p $(out)/tex
	mv build/latex/ $(out)/tex

clean:
	rm -rf build
