default: pdf

pdf:
	# mkdir build
	cp main.lagda build
	# cp -r ../libraries/agda-prelude/src build
	pwd
	cd ./build && pwd && ls && agda --latex main.lagda

install: pdf
	mkdir -p $(out)/tex
	mv build/latex $(out)/tex
