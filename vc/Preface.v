(** * Preface *)

(* ################################################################# *)
(** * Welcome *)

(** Here's a good way to build formally verified correct software:
 - Write your program in an expressive language with a good proof theory
      (the Gallina language embedded in Coq's logic).
 - Prove it correct in Coq.
 - Extract it to ML and compile it with an optimizing ML compiler.
 
 Unfortunately, for some applications you cannot afford to use
 a higher-order garbage-collected functional programming language
 such as Gallina or ML.  Perhaps you are writing an operating-system
 kernel, or a bit-shuffling cryptographic primitive, or the
 runtime system and garbage-collector of your functional language!
 In those cases, you might want to use a low-level imperative systems
 programming language such as C.

 But you still want your OS, or crypto, or GC, to be correct!
 So you should use machine-checked program verification in Coq.
 For that purpose:

 Use _Verifiable C_, a program logic and proof system for C.
 What is a program logic?  One example of a program logic is
 the Hoare logic that you studied  in the _Programming Language 
 Foundations_ volume of this series.  (If you have not done so 
 already, study the Hoare and Hoare2 chapters of that volume,
 and do the exercises.)

 Verifiable C is based on Hoare logic, but a 21st-century version:
 higher-order impredicative concurrent separation logic.  Back
 in the 20th century, computer scientists discovered that Hoare Logic
 was not very good at verifying programs with pointer data structures;
 so _separation logic_ was developed.  Hoare Logic was clumsy at
 verifying concurrent programs, so _concurrent separation logic_ was
 developed.  Hoare Logic could not handle higher-order object-oriented
 programming patterns, or function-closures; so _higher-order 
 impredicative program logics_ were developed.

 This electronic book is Volume 5 of the _Software Foundations_
 series, which presents the mathematical underpinnings of reliable
 software.   The principal novelty of _Software Foundations_ is that it is one
 hundred percent formalized and machine-checked: the entire text is
 literally a script for Coq.  It is intended to be read alongside an
 interactive session with Coq.  All the details in the text are fully
 formalized in Coq, and the exercises are designed to be worked using
 Coq.

 Before studying this volume, you should be a competent
 user of Coq:
 - Study  _Software Foundations Volume 1_  (Logical Foundations), and
   do the exercises!
 - Study the Hoare and Hoare2 chapters of 
   _Software Foundations Volume 2_  (Programming Language Foundations), and
   do the exercises!
 - Study the Sort, SearchTree, and ADT chapters of 
   _Software Foundations Volume 3_  (Verified Functional Algorithms), and
   do the exercises!
 You will also need a working knowledge of the C programming language.

*)

(* ################################################################# *)
(** * Practicalities *)

(* ================================================================= *)
(** ** System Requirements *)

(** Coq runs on Windows, Linux, and OS X.  The Preface of Volume 1
    describes the Coq installation you will need.  This edition was
    built with Coq 8.7.1 or 8.8.0.

    You must install the Verified Software Toolchain.
    Download the latest version from the web site,
    http://vst.cs.princeton.edu/download/
    (these chapters are currently tested on VST version 2.2)
    and build by doing [make -jN], where [N] is the number of 
    threads your machine can run in parallel (typically twice the
    number of cores).

    _You do not need to install CompCert_ to do the exercises in this 
    volume.  But if you wish to modify and reparse the .c files,
    or verify C programs of your own, install the CompCert verified
    optimizing C compiler.  Download from compcert.inria.fr (this
    volume of Software Foundations you are reading now was tested with 
    CompCert version 3.2), and [./configure -clightgen x86_32/linux]

 *)

(* ================================================================= *)
(** ** Configuration *)

(** In this [vc] directory, create a one-line CONFIGURE file containing

    [VST_LOC= /file/path/to/VST]

    where you replace [/file/path/to/VST] with the location of your VST
    installation.

    If you have installed CompCert, you may add a second line to CONFIGURE,
    [CC_LOC= /file/path/to/CompCert].
    This will allow you to run the CompCert/clightgen program,
    which turns (for example) [hash.c] into [hash.v].  But we have already
    produced [hash.v] for you, so you would need clightgen only
    if you modify or create a .c file.

    When running coqc, or CoqIDE, or Proof General, etc., you will
    need to give Coq the extra "include flags" that allow it to import
    from VST.  The Makefile in this [vc] directory will build the 
    [_CoqProject] file automatically--just do [make] or [make _CoqProject].
*)

   

(* ================================================================= *)
(** ** Exercises *)

(** Each chapter includes exercises.  Each is marked with a
    "star rating," which can be interpreted as follows:

       - One star: easy exercises that underscore points in the text
         and that, for most readers, should take only a minute or two.
         Get in the habit of working these as you reach them.

       - Two stars: straightforward exercises (five or ten minutes).

       - Three stars: exercises requiring a bit of thought (ten
         minutes to half an hour).

       - Four and five stars: more difficult exercises (half an hour
         and up).

    _Please do not post solutions to the exercises in any public place_: 
    Software Foundations is widely used both for self-study and for
    university courses.  Having solutions easily available makes it
    much less useful for courses, which typically have graded homework
    assignments.  The authors especially request that readers not post
    solutions to the exercises anyplace where they can be found by
    search engines.
*)

(* ================================================================= *)
(** ** Downloading the Coq Files *)

(** A tar file containing the full sources for the "release version"
    of this book (as a collection of Coq scripts and HTML files) is
    available at http://www.cs.princeton.edu/~appel/vc.

    (If you are using the book as part of a class, your professor may
    give you access to a locally modified version of the files, which
    you should use instead of the release version.) *)

(* ================================================================= *)
(** ** For Instructors and Contributors *)

(** If you plan to use these materials in your own course, you will
    undoubtedly find things you'd like to change, improve, or add.
    Your contributions are welcome!  Please see the [Preface]
    to _Logical Foundations_ for instructions. *)

(* ################################################################# *)
(** * Thanks *)

(** Development of the _Software Foundations_ series has been
    supported, in part, by the National Science Foundation under the
    NSF Expeditions grant 1521523, _The Science of Deep
    Specification_. *)

