Untitled Relational Interpreter Book
====================================

by

William E. Byrd

-------------------------------------------------------------------

Update (July 14th, 02015):

I've changed the name of the book/repository too many times, so I'll
just call the repo 'untitled-relational-interpreter-book' for now.

The working title of the book is:

  'Playing with Relational Interpreters'

I hope I can capture the sense of play and excitement
I get from playing with the relational interpreter.

My current plan is to write a *thin*, very focused book on relational
interpreters, with all non-awesomeness removed.  I want the book to be
readable by as general an audience as possible.  Narrow focus, wide
audience.

I'm working on a new outline (`outline.txt`).  I've moved the old
outlines to the `old-outlines` directory.

I've been moderating/hosting a series of weekly miniKanren "uncourse"
Hangouts
(https://www.youtube.com/playlist?list=PLO4TbomOdn2cks2n5PvifialL8kQwt0aW).
These hangouts have been extremely helpful for helping me understand
how to teach relational interpreters.  Many thanks to everyone who has
participated!

Special thanks to: Celeste Hollenbeck for pushing me to keep working
on this book; Michael Ballantyne for close collaboration on miniKanren
and relational interpreters; Matt Might, who has made this
collaboration possible; Michael Adams, for collaboration on tree
automata for miniKanren, and countless helpful conversations; Celeste
Hollenbeck and Maria Jenkins for helping figure out how to teach a
minimal introduction to Scheme; Tom Gilray for explorations in 0-CFA
in miniKanren; and all my other colleagues in the U Combinator lab and
at University of Utah for creating an intellectually stimulating
environment.

Special thanks to David Nolen for porting my dissertation to Clojure.
I doubt I would have had the courage to continue working on miniKanren
otherwise.

Special thanks to Stu Halloway for his quines observation, which has
driven my research (and my sleep patterns) for the past three years.
Thanks also to Stu and Joey for their amazing hospitality.

Special thanks to Rich Hickey, Lynn Grogan, Alex Miller, and the
Clojure community for being so welcoming.

Special thanks to Andy Lumsdaine and Rebecca Schmidt for their
tremendous support -- and their friendship -- while I was at the
Center for Research in Extreme Scale Technologies (CREST).  And thanks
to all the other CREST researchers and employees, who I'll not even
try to name here for fear of leaving someone out.  I'll save it for
the book.

Special thanks to Alan Sherman at UMBC for his support and mentorship
over the years.

And, of course, thanks to the usual suspects -- all the people who
have developed and improved miniKanren and its variants and ports.
Special thanks to my 'Reasoned Schemer' co-authors Dan Friedman and
Oleg Kiselyov.  I'm not going to try to name anyone else, since I know
I'll accidentally leave people out.  I'll try to thank everyone
properly in the book.  I fear this is already an impossible task.

Special thanks to my H211/C211/C311 students, and to my teaching
assistants: Lindsey Kuper, Michael Adams, and Abdulaziz Ghuloum.

Finally, a very special thanks to my family for your love and support.

-------------------------------------------------------------------

Old, hilariously optimistic update:

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
