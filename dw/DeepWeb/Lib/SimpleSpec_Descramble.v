Generalizable Variable E.
Typeclasses eauto := 6.

From QuickChick Require Import QuickChick.

Require Import Ascii.
Require Import String.
Require Import List.
Require Import PArith.
Require Fin.
Import ListNotations.

From Custom Require Import Show.

Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.
Import NonDeterminismBis.

Require Import DeepWeb.Lib.Util.
Require Import DeepWeb.Lib.SimpleSpec_Observer.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Open Scope string_scope.
(* end hide *)

(* The constraints on the network are:
   - a connection must be open before bytes can be exchanged on it;
   - two bytes going in the same direction on the same connection
     must arrive in-order;
   - if we get a byte [b1] from the server before we send some [b2]
     to it, then the server definitely sent [b1] before it
     can receive [b2]. ([FromServer,ToServer] cannot be descrambled
     to [ToServer,FromServer], regardless of the connections
     where the two events happen.)
 *)

(* Unary tree node carrying some event. *)
Inductive eventE : Type -> Type :=
| Happened : event -> eventE unit.

(* We enumerate descramblings in a tree structure, using
   [nondetE] to branch, so that each successful pat (i.e., not
   leading to failure) is a descrambling of a given trace. *)
Definition eventE' := nondetE +' eventE.

(* Helper for [pick_event]. *)
CoFixpoint pick_event' (t_prev t : trace) : M eventE' trace :=
  match t with
  | [] => fail "empty trace"
  | Event _ e _ as ev :: t =>
    let pick_this :=
        _ <- ^ Happened ev;;
       ret (List.rev t_prev ++ t)%list in
    disj "pick_event'"
      ( match e with
        | ObsConnect =>
          if forallb (fun ev =>
                match ev with
                | Event _ (ObsFromServer _) _ => false
                | _ => true
                end) t_prev then
            pick_this
          else
            fail "inaccessible ObsConnect"

        | ObsToServer c =>
          if forallb (fun ev =>
               match ev with
               | Event _ (ObsFromServer c') _ => false
               | Event _ ObsConnect c'
               | Event _ (ObsToServer c') _ => c <> c' ?
               end) t_prev then
            pick_this
          else
            fail "inaccessible ObsToServer"

        | ObsFromServer c =>
          if forallb (fun ev =>
               match ev with
               | Event _ (ObsToServer _) _ => true
               | Event _ ObsConnect c'
               | Event _ (ObsFromServer c') _ => c <> c' ?
               end) t_prev then
            pick_this
          else
            fail "inaccessible ObsFromServer"

        end
      | pick_event' (ev :: t_prev) t
      )
  end.

(* Given a scrambled trace, remove one event that could potentially
   be the next one in a descrambling.
 *)
Definition pick_event : trace -> M eventE' trace :=
  pick_event' [].

Definition is_ObsFromServer (ev : event) :=
  match ev with
  | Event _ (ObsFromServer _) _ => true
  | _ => false
  end.

(* Once the only things left are messages sent to the server,
   we drop them, since there is no response to compare them
   against. *)
CoFixpoint descramble (t : trace) : M eventE' unit :=
  match filter is_ObsFromServer t with
  | [] => ret tt
  | _ :: _ =>
    t' <- pick_event t;;
    descramble t'
  end.

(* Functions to list the descrambled traces *)
Section ListDescramble.

Fixpoint list_eventE' (fuel : nat) (s : M eventE' unit)
           (acc : list trace) (new : trace -> trace) :
  option (list trace) :=
  match fuel with
  | O => None
  | S fuel =>
    match s with
    | Tau s => list_eventE' fuel s acc new
    | Ret tt => Some (new [] :: acc)
    | Vis _ (| e ) k =>
      match e in eventE X return (X -> _) -> _ with
      | Happened ev => fun k =>
        list_eventE' fuel (k tt) acc (fun t => new (ev :: t))
      end k
    | Vis X ( _Or |) k =>
      match _Or in nondetE X' return (X' -> _) -> _ with
      | Or n _ =>
        (fix go n0 : (Fin.t n0 -> X) -> _ :=
           match n0 with
           | O => fun _ => Some acc
           | S n0 => fun f =>
             match list_eventE' fuel (k (f Fin.F1)) acc new with
             | None => None
             | Some acc => go n0 (fun m => f (Fin.FS m))
             end
           end) n
      end (fun x => x)
    end
  end.

(* [None] if not enough fuel. *)
Definition list_eventE (fuel : nat) (s : M eventE' unit) :
  option (list trace) :=
  list_eventE' fuel s [] (fun t => t).

(* Fuel of the order of [length t ^ 2] should suffice. *)
Definition list_descramblings (fuel : nat) (t : trace) :
  option (list trace) :=
  list_eventE fuel (descramble t).

(*
Compute list_descramblings 50 [
  Event ObsConnect 0;
  Event (ObsToServer 0 tt) "A";
  Event ObsConnect 1;
  Event (ObsToServer 0 tt) "B";
  Event (ObsFromServer 0) (Some "C")
]%char.
*)

End ListDescramble.

(* Those descramblings are still missing [ObsFromServer] events
   with holes (i.e., with [None] in the last field of [Event]).
   We will insert them as needed when comparing the tree of
   descramblings with the spec tree. *)

CoFixpoint select_event' {X}
           (e : observerE X) (t_prev t : trace) :
  M (nondetE +' eventE) (X * trace) :=
  match t with
  | [] =>
    match e with
    | ObsFromServer _ as e =>
      (* If we're expecting a reply from the server, we
         can temporarily put a hole to see what should happen
         next. *)
      ^ Happened (Event e None);;
      ret (None, rev t_prev)
    | _ => fail "no event left to pick"
    end
  | Event X' e' x as ev :: t =>
    match observer_eq e' e with
    | Some p => (* e' = e *)
        ^ Happened ev;;
        ret (coerce p x, rev t_prev ++ t)%list
    | None => (* e' <> e *)
      let try_next := Tau (select_event' e (ev :: t_prev) t) in
      match e, e' with

      | ObsConnect as e, ObsToServer _
      | ObsToServer _ as e, (ObsConnect | ObsToServer _)
      | ObsFromServer _ as e, _ =>
        try_next

        (* We're looking for a [Connect/ToServer] event
           but there is still a [FromServer] event to explain. *)
      | (ObsConnect | ObsToServer _), ObsFromServer _ =>
        fail "inaccessible event"

      | ObsConnect, ObsConnect => fail "should not happen"
      end
    end
  end.

Definition select_event {X} (e : observerE X) :
  trace -> M (nondetE +' eventE) (X * trace) := select_event' e [].

(* [s]: tree of acceptable traces (spec)
   [t]: scrambled trace

   The result tree has a [Ret] leaf iff there is a descrambled
   trace accepted by [s] ([is_trace_of]).
 *)
CoFixpoint intersect_trace
            (s : M (nondetE +' observerE) unit)
            (t : trace) :
  M (nondetE +' eventE) unit :=
  match s with
  | Tau s => Tau (intersect_trace s t)
  | Ret tt =>
    match filter is_ObsFromServer t with
    | [] => ret tt
    | _ :: _ => fail "unexplained events remain"
    end
  | Vis _ ( e |) k => Vis ( e |) (fun x => intersect_trace (k x) t)
  | Vis X (| e ) k =>
    match filter is_ObsFromServer t with
    | [] => ret tt
    | _ :: _ =>
      xt <- select_event e t;;
      let '(x, t) := xt in
      intersect_trace (k x) t
    end
  end.

CoFixpoint find' (ts : list (M (nondetE +' eventE) unit)) :
  M emptyE bool :=
  match ts with
  | [] => ret false
  | t :: ts =>
    match t with
    | Tau t => Tau (find' (t :: ts))
    | Ret tt => ret true
    | Vis X e k =>
      match e with
      | (| ev ) =>
        match ev in eventE X' return (X' -> X) -> _ with
        | Happened _ => fun id => Tau (find' (k (id tt) :: ts))
        end (fun x => x)
      | ( _Or |) =>
        match _Or in nondetE X' return (X' -> X) -> _ with
        | Or n _ => fun id =>
          Tau (find' (map (fun n => k (id n)) every_fin ++ ts)%list)
        end (fun x => x)
      end
    end
  end.

Inductive result := Found | NotFound | OutOfFuel.

Definition option_to_list {A} (o : option A) : list A :=
  match o with
  | None => []
  | Some a => [a]
  end.

Fixpoint to_result (fuel : nat) (m : M emptyE bool) : result :=
  match fuel with
  | O => OutOfFuel
  | S fuel =>
    match m with
    | Ret b => if b then Found else NotFound
    | Tau m => to_result fuel m
    | Vis X e k => match e in emptyE X' with end
    end
  end.

(* SHOW *)
(* BCP: This will probably move up too. *)
Definition is_scrambled_trace_of
           (fuel : nat) (s : itree_spec) (t : trace) : result :=
  to_result fuel (find' [intersect_trace s t]).

(* We will then generate traces produced by a server to test them.
   See [Lib/SimpleSpec_ServerTrace.v] *)
(* /SHOW *)