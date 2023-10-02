
PANDOC_ARGS = --standalone  \
			  --css handout_pandoc.css \
			  --toc \
			  --toc-depth=3 \
  			  --template src/tutorial_template.html 

all:
	gpp -T src/tutorial.md | pandoc ${PANDOC_ARGS} -o tutorial.html
	gpp -T src/errors.md | pandoc ${PANDOC_ARGS}  -o errors.html

