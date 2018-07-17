Set Implicit Arguments.

Require Import List.
Import ListNotations.

Require DeepWeb.Free.Monad.Free.
Import Monad.MonadNotations.

Module WRITER.

Export Monad.Free.

(* ========================================================================= *)
(** A monad instance for programs whose only effect is to write things
    of type A. *)

Inductive WriterEvent (A : Type) : Type -> Type :=
| Write (x: A) : WriterEvent A unit.

(** A [Writer A X] is equivalent to a coinductive stream of [A]s and
    [Tau]s, and possibly a [X] if the stream is finite *)
Definition Writer (A : Type) := M (WriterEvent A).

(* TODO: We could make a generic definition for the Vis...Ret idiom
   and simplify this. *)
Definition tell {A} (x : A) : Writer A unit := Vis (Write x) (fun _ => Ret tt).

(** TODO: We could probably make a generic version of this in MONAD.
    First make an inductive variant IM of M.  Then write a "take"
    function that converts from [M E X] to [IM E (option X)].  Then
    runWriter would operate on IM and not take fuel. *)
Fixpoint runWriter {A} {X} (t : Writer A X) (n : nat) : list A :=
  match n with
  | 0 => []
  | S n' => match t with
            | Ret x => []  
            | Vis (Write x) k => x :: runWriter (k tt) n' 
            | Tau k => runWriter k n'
            end 
  end.

End WRITER.

Module IO.

Export Monad.Free.
Export WRITER.

Section IO_Section.

Context {value : Type}.

(* TODO: replace value by a type parameter (or two).  Or perhaps it's
   just as easy to write new concrete instances when we need them. *)
Inductive IOEvent : Type -> Type :=
| Output (v: value) : IOEvent unit
| Input : IOEvent value.

Definition IO := M IOEvent.

Definition send (v : value) : IO unit := Vis (Output v) (fun _ => Ret tt).
Definition recv : IO value := Vis Input (fun v => Ret v).

Inductive Ev :=
| In  (v: value) 
| Out (v: value).

(** Given a list of inputs, we can turn an [IO] into a [Writer]. *)
CoFixpoint ioToWriter {X} (t : IO X) (q : list value) : Writer Ev X :=
  match t with
    | Ret x => Ret x
    | Vis (Output v) k => tell (Out v) ;; ioToWriter (k tt) q
    | Vis Input k =>
      match q with
        | [] => spin
        | v::q' => tell (In v) ;; ioToWriter (k v) q'
      end
    | Tau k => Tau (ioToWriter k q)
  end.

Definition runIO {X} (t : IO X) (q : list value) (n : nat) : list Ev :=
  runWriter (ioToWriter t q) n.

End IO_Section.
End IO.
