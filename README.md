Relational Programming in miniKanren
====================================

by

William E. Byrd

-------------------------------------------------------------------

I'm currently (as of July 4th, 2014) working on a detailed outline for
the book:

https://github.com/webyrd/relational-programming-in-miniKanren/blob/master/outline.org

I'll begin writing prose in earnest once the outline is complete.  I
expect to be finished with the outline by mid-August, 2014.

Before writing prose, I might first use the outline as a basis for a
Google-Hangout based mini-course on relational programming.  This
mini-course would help me flesh out examples, help me understand where
people get confused, and help ensure the structure and order of
presentation makes sense.  Anyone interested in such a course can
email me at `webyrd@gmail.com`.

Cheers,

--Will

-------------------------------------------------------------------


This work is licensed under a Creative Commons Attribution 4.0 International License.
(CC BY 4.0)  (http://creativecommons.org/licenses/by/4.0/)


The PDF file for the book is at:

`latex/rpim.pdf`


Build instructions:

I build the book under Mac OS 10.8 using the MacTeX-2012 Distribution of TeX Live. (http://tug.org/mactex/) For some bizarre reason, you need to be careful when downloading the `MacTeX.pkg` file, or it will be corrupted; one safe way to download the file is to use Safari.  I'm typesetting the book using XeLaTeX, which should be included in any modern TeX distribution.

I'm using SLaTeX (http://www.ccs.neu.edu/home/dorai/slatex/) to typeset Scheme and miniKanren code.  I've included SLaTeX in the Github repo, but SLaTeX expects a Scheme implementation in order to work.  I'm using the 32-bit nonthreaded version of Petite Chez Scheme 8.4 (http://www.scheme.com/download/).  If you use another Scheme implementation, you'll have to update the `xeslatex` file in the main directory, replacing `petite` with your Scheme implementation of choice.  Of course you will need to make sure your Scheme implementation is on your `PATH`.

Once you have installed your TeX distribution and a Scheme implementation, you should be ready to typeset the book:

`cd latex`

`make squeaky; make`

`make squeaky` removes all generated files, including the PDF of the book.  `make clean` removes temporary files, but not the book PDF.
