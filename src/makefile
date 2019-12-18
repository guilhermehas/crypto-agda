default: pdf

pdf:
	mkdir build
	cp *.lagda build
	cp -r /nix/store/dhpbi065nxndl56ijphyb8c6l5xd2lcf-agda-prelude/src/* build
	chmod -R +w build
	cd build ; for file in *.lagda; do agda --no-default-libraries --latex $$file; done

install:
	mkdir -p $(out)/tex
	mv build/latex/ $(out)/tex

clean:
	rm -rf build
