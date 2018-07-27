Require Import Verdi.Verdi.

Require Import LockServSeqNum.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlList.
Require Import Verdi.ExtrOcamlFinInt.

Extraction "extraction/lockserv-seqnum/ocaml/LockServSeqNum.ml" seq transformed_base_params transformed_multi_params.
