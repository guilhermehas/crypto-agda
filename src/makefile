default: pdf

pdf:
	mkdir build
	cp *.lagda build
	cp -r $$PRELUDE/share/agda/* build
	chmod -R +w build
	cd build ; for file in *.lagda; do agda --no-default-libraries --latex $$file; echo $$file; done
	cd build/latex ; for file in *.tex; do sed -i 's/∷/::/g' $$file ; done

install:
	mkdir -p $(out)/tex
	mv build/latex/ $(out)/tex

clean:
	rm -rf build
