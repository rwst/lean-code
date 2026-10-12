# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
# Build the book: `make` (output in _build/book.pdf), `make clean`.
book:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=_build book.tex
clean:
	latexmk -C -outdir=_build book.tex
.PHONY: book clean
