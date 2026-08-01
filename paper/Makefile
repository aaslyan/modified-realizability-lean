# Build "How a Proof Becomes a Program" from the Markdown source.
#
# Requirements: pandoc, a LuaLaTeX TeX distribution (TeX Live / MacTeX),
# and the DejaVu Sans Mono font (ships with TeX Live) for the code blocks'
# Unicode glyphs.  The prose math symbols are font-independent (mapped to
# Computer Modern math in preamble.tex), so only the mono font matters.

NAME = how-a-proof-becomes-a-program
SRC  = $(NAME).md
TEX  = $(NAME).tex
PDF  = $(NAME).pdf

PANDOC_FLAGS = --standalone --shift-heading-level-by=-1 --wrap=none \
               --include-in-header=preamble.tex \
               -V documentclass=article -V fontsize=11pt

.PHONY: all clean

all: $(PDF)

$(PDF): $(SRC) preamble.tex
	pandoc $(SRC) -o $(TEX) $(PANDOC_FLAGS)
	latexmk -lualatex -interaction=nonstopmode $(TEX)

# Remove LaTeX auxiliary files (keeps the committed .tex and .pdf).
clean:
	latexmk -c $(TEX) >/dev/null 2>&1 || true
	rm -f $(NAME).fls $(NAME).fdb_latexmk build.log
