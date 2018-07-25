Require Import List.
Import ListNotations.

Set Implicit Arguments.

(* Note that we have to order definitions carefully when modules
   are involved... *)

(* a coarse abstraction of packets sent on the network *)
Record packet (D: Set) (P: Set) : Set :=
  mkpacket {
    dest : D;
    payload : P
  }.

(* Module types are just collections of parameters and axioms. *)
Module Type BaseSystemParams.
  (* external client I/O *)
  Parameter input : Set.
  Parameter output : Set.

  (* nodes -- roughly uids *)
  Parameter node : Set.

  (* node local state *)
  Parameter state : Set.

  (* internal messages between nodes *)
  Parameter msg : Set.

  (* Here we use Notations because module types cannot contain
     any definitions! *)
  
  Notation packet :=
    (packet node msg).

  Notation handler :=
    (state -> state * list packet * list output).

  (* Our "network semantics" will want every system to have
     decidable equality for node and msg types so that it can
     compare packets. *)
  
  Parameter node_eq_dec :
    forall x y : node, {x = y} + {x <> y}.

  Parameter msg_eq_dec :
    forall x y : msg, {x = y} + {x <> y}.
End BaseSystemParams.

Module Type SystemParams.
  (* This makes it as though we copy/pasted everything from
     BaseSystemParams right here. *)
  Include BaseSystemParams.
  
  (* initial state of system *)
  Parameter init_state :
    node -> state.

  (* client request handler *)
  Parameter handle_input :
    node -> input -> handler.

  (* node message handler *)
  Parameter handle_msg :
    node -> msg -> handler.
End SystemParams.

(* Now we'll define a functor which, given the base params for a
   system, provides a monad and some syntax to make writing
   handlers less painful.  Functors are sort of like functions,
   but over modules.  In this case, if we apply the functor to a
   module that satisfies the constraints of BaseParams, we will
   get a new module which contains all the definitions below. *)
   
(* monad to make writing handlers less painful *)
Module HandlerMonad (P : BaseSystemParams).
  Include P.

  (* This export helps folks who instantiate this functor get all
     the notations etc. back out. *)
  Export P.

  Definition handler_monad A :=
    state -> A * state * list packet * list output.

  Definition do {A : Set} (m : handler_monad A) : handler :=
    fun s =>
      let '(a, s', ps, os) := m s in
      (s', ps, os).

  Definition ret {A : Set} (x : A) : handler_monad A :=
    fun s =>
      (x, s, [], []).
  
  Definition bind {A B : Set} (ma : handler_monad A)
             (f : A -> handler_monad B) : handler_monad B :=
    fun s =>
      let '(a, s', ps, os) := ma s in
      let '(b, s'', ps', os') := f a s' in
      (b, s'', ps ++ ps', os ++ os').

  Definition nop :=
    ret tt.

  Definition send to msg : handler_monad unit :=
    fun s =>
      (tt, s, [mkpacket to msg], []).

  Definition out o : handler_monad unit :=
    fun s =>
      (tt, s, [], [o]).

  Definition get : handler_monad state :=
    fun s =>
      (s, s, [], []).

  Definition set s : handler_monad unit :=
    fun _ =>
      (tt, s, [], []).

  (* notations to make the monad look better *)

  Notation "x <- c1 ;; c2" :=
    (@bind _ _ c1 (fun x => c2))
      (at level 100, c1 at next level, right associativity).

  Notation "e1 ;; e2" :=
    (_ <- e1 ;; e2)
      (at level 100, right associativity).
End HandlerMonad.