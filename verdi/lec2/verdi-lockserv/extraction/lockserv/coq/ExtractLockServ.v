Require Import Verdi.Verdi.

Require Import LockServ.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlList.
Require Import Verdi.ExtrOcamlFinInt.

Extraction "extraction/lockserv/ocaml/LockServ.ml" seq LockServ_BaseParams LockServ_MultiParams.
