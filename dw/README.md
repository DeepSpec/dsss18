DeepSpec Swap Server Demo
=========================

Directory Structure
-------------------

    docs/            HTML files 
                     (docs/toc.html gives a reasonable order for reading)

    Custom/          Miscellaneous standard library extensions
    DeepWeb/         Swap server demo
       Free/Monad/     Interaction trees 
       Spec            Specifications     
       Proofs          Proofs
       Lib             Effect types
       Test            Testing

Building
--------

Make sure QuickChick is installed.  Then do:

    make

Building with VST
-----------------

[Warning: You may need to install the upo-to-the-minute version of VST 
from https://github.com/PrincetonUniversity/VST.git to do this]

In this `dw/` directory, create a `CONFIGURE` file containing

    VST_LOC= /file/path/to/VST

where you replace `/file/path/to/VST` with the location of your VST
installation.

Then run

    make build-with-vst

Reading
-------

The links in 

    html/toc.html

offer a good sequence for reading the first several files (up to
DeepWed/Spec/TopLevelSpec -- the files after that are internal).

