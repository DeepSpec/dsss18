Require Import Verdi.Verdi.

Require Import Cheerios.Cheerios.

Require Import LockServSerialized.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlList.
Require Import Verdi.ExtrOcamlFinInt.

Require Import Cheerios.ExtrOcamlCheeriosBasic.
Require Import Cheerios.ExtrOcamlCheeriosNatInt.
Require Import Cheerios.ExtrOcamlCheeriosFinInt.

Extraction "extraction/lockserv-serialized/ocaml/LockServSerialized.ml" seq transformed_base_params transformed_multi_params.
