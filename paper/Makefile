# Build "How a Proof Becomes a Program".
#
# The LaTeX source (how-a-proof-becomes-a-program.tex) is authoritative and is
# authored directly; preamble.tex is \input by it. The retired Markdown draft
# lives in draft/ for reference only and is no longer part of the build.
#
# Requirements: a TeX Live / MacTeX distribution providing pdflatex, latexmk,
# and the newpx (Palatino-family) and inconsolata (zi4) font packages. The
# source is pure ASCII; every mathematical symbol is a LaTeX command, so no
# special fonts or Unicode handling are needed.

NAME = how-a-proof-becomes-a-program
TEX  = $(NAME).tex
PDF  = $(NAME).pdf

.PHONY: all clean

all: $(PDF)

$(PDF): $(TEX) preamble.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(TEX)

# Remove LaTeX auxiliary files (keeps the committed .tex and .pdf).
clean:
	latexmk -c $(TEX) >/dev/null 2>&1 || true
	rm -f $(NAME).fls $(NAME).fdb_latexmk build.log
