DeepSpec Web Server Demo
========================

Directory Structure
-------------------

    Custom/       Miscellaneous standard library extensions
    FreeMonad/    Interaction trees 
    IODemo/       Simple I/O demo
    DeepWeb/      Larger server demo
       Spec         Specifications     
       Proofs       Proofs
       Util         Miscellaneous utilities
       Lib          Effect types
       Test         Testing

Building
--------

In this `dw/` directory, create a `CONFIGURE` file containing

    VST_LOC= /file/path/to/VST

where you replace `/file/path/to/VST` with the location of your VST
installation.

Then run

    make

Reading
-------

The top-level spec lives in Spec/TopLevelSpec.v



