Require Extraction.

Require Import String.
Require Import Arith.
Require Import BinNums.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

(** We declare an ML module called [ExtractionClient]. It has one
    function [send_coq_req] that has the type given below. Coq allows
    us to use this function, even though there is no Gallina
    implementation in it. **)
Declare ML Module "Util/ExtractionClient".

Parameter file_descr : Type.

Parameter check7232 : bool.
Parameter suppressConditionalPut : bool.
Parameter close : file_descr -> unit.
Parameter gettimeofday : unit -> string.
Parameter init  : forall {A}, A -> A.
Parameter isApache : bool.
Parameter log   : string -> unit.
Parameter looseDelete : bool.
Parameter port  : N.
Parameter read  : file_descr -> nat -> string.
Parameter send  : string -> N -> string -> file_descr.
Parameter send_req : string -> file_descr -> nat.
Parameter socket   : string -> N -> file_descr.
Parameter fixpoint : forall {A B}, ((A -> B) -> A -> B) -> A -> B.

Extract Constant file_descr => "Unix.file_descr".

Extract Constant check7232 => "ExtractionClient.check7232".
Extract Constant suppressConditionalPut => "ExtractionClient.suppressConditionalPut".
Extract Constant close => "Unix.close".
Extract Constant gettimeofday => "ExtractionClient.time_string".
Extract Constant init  => "ExtractionClient.init".
Extract Constant isApache => "ExtractionClient.isApache".
Extract Constant log   => "ExtractionClient.log_string".
Extract Constant looseDelete => "ExtractionClient.looseDelete".
Extract Constant port  => "ExtractionClient.port".
Extract Constant read  => "ExtractionClient.read_string".
Extract Constant send  => "ExtractionClient.send".
Extract Constant send_req => "ExtractionClient.send_req".
Extract Constant socket   => "ExtractionClient.socket".
Extract Constant fixpoint => "ExtractionClient.fixpoint".
