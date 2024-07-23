Instructions
============

FILES
-----

* README.        This document. 
* runlength8.txt An implementation of run-length compression. 
* RLMain.hs      Haskell program that use the generated inverse of runlength8.txt.
* orig.bmp       A raw-bitmap file to compress. 

How to Generate Inverse
-----------------------

Run the following command.

    ../PaI -i MyData -m RUNLENGTH8 -f runlength8.txt > RUNLENGTH8.hs 

Then, `RUNLENGTH8.hs` has been generated, which is to be imported in `RLMain.hs`.

How to Compile `RLMain.hs`
--------------------------

Run the following command.

    ghc -j -i.. --make RLMain.hs

This may take a time.

Demonstration
-------------

    $ display orig.bmp # Or, use the "open" command if you are using Mac. 
    $ ./RLMain encode orig.bmp test_out
    $ ls -lht 
    ...
    $ ./RLMain decode test_out new.bmp
    $ ls -lht 
    ... 
    $ display new.bmp # Or, open if you are using Mac. 
    $ diff orig.bmp new.bmp 

Make sure that you must delete generated files before and/or after the
demonstration by `./cleanup.sh`