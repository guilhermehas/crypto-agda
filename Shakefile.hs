
import Development.Shake
import Development.Shake.Command
import Development.Shake.FilePath
import Development.Shake.Util

pdfRule :: FilePattern -> FilePath   -> Rules ()
pdfRule dir name = "_build" </> name <.> "pdf" %> \out -> do
    cmd_ [Cwd dir] ["latexmk", "-interaction=nonstopmode", "-f", "-pdf", "-use-make",
     "-outdir=res" , "main.tex" ]
    cmd_ ["mv", dir </> "res/main.pdf", "_build" </> name <.> "pdf"]

main :: IO ()
main = shakeArgs shakeOptions{shakeFiles="_build"} $ do
  want ["_build/thesis.pdf"]
  want ["_build/slides.pdf"]

  pdfRule "docs" "thesis"
  pdfRule "slides" "slides"

  phony "clean" $ do
      putInfo "Cleaning files in _build"
      removeFilesAfter "_build" ["//*"]
      putInfo "Cleaning files in docs/res"
      removeFilesAfter "docs/res" ["//*"]
      putInfo "Cleaning files in slides/res"
      removeFilesAfter "slides/res" ["//*"]