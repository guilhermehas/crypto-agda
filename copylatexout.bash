cd $(dirname $(dirname $(which latexmk)))/share/texmf/tex/latex && cp -Lr *.tex $1 && cp agda.sty $2
