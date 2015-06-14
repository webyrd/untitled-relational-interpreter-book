BOOK=urib

all:
	./build

clean:
	rm -f .Z*
	rm -f .q*
	rm -f .old*
	rm -f *.aux
	rm -f *.log
	rm -f *.toc
	rm -f ${BOOK}.out
	rm -f ${BOOK}.bbl
	rm -f ${BOOK}.blg
	rm -f *.idx

squeaky:
	make clean
	rm -f ${BOOK}.pdf
	rm -f ${BOOK}.dvi
	rm -f *~
