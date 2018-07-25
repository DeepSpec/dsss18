(* Traces that a client observes are scrambled by the network.
   We try to explain it by "descrambling" it into a trace
   that is recognized by a given spec. *)

Generalizable Variable E.
Typeclasses eauto := 6.

From QuickChick Require Import QuickChick.

Require Import Ascii.
Require Import String.
Require Import List.
Require Import PArith.
Require Fin.
Import ListNotations.

From Custom Require Import
     List Show.

Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.

Require Import DeepWeb.Lib.Util.

Require Import DeepWeb.Lib.SimpleSpec_Traces.
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
| Happened : hypo_event -> eventE unit.

(* We enumerate descramblings in a tree structure, using
   [nondetE] to branch, so that each successful pat (i.e., not
   leading to failure) is a descrambling of a given trace. *)
Definition eventE' := failureE +' nondetE +' eventE.

(* Helper for [pick_event]. *)
CoFixpoint pick_event' (t_prev t : real_trace) : M eventE' real_trace :=
  match t with
  | [] => fail "empty trace"
  | ev :: t =>
    let pick_this :=
        _ <- ^ Happened ev;;
       ret (List.rev t_prev ++ t)%list in
    disj
      ( match ev with
        | NewConnection c =>
          if forallb (fun ev =>
                match ev with
                | FromServer _ _ => false
                | _ => true
                end) t_prev then
            pick_this
          else
            fail "inaccessible ObsConnect"

        | ToServer c _ =>
          if forallb (fun ev =>
               match ev with
               | FromServer c' _ => false
               | NewConnection c'
               | ToServer c' _ => c <> c' ?
               end) t_prev then
            pick_this
          else
            fail "inaccessible ObsToServer"

        | FromServer c _ =>
          if forallb (fun ev =>
               match ev with
               | ToServer _ _ => true
               | NewConnection c'
               | FromServer c' _ => c <> c' ?
               end) t_prev then
            pick_this
          else
            fail "inaccessible ObsFromServer"

        end
      | pick_event' (ev :: t_prev) t
      )
  end%nondet.

(* Given a scrambled trace, remove one event that could potentially
   be the next one in a descrambling.
 *)
Definition pick_event : real_trace -> M eventE' real_trace :=
  pick_event' [].

(* Once the only things left are messages sent to the server,
   we drop them, since there is no response to compare them
   against. *)
CoFixpoint descramble (t : real_trace) : M eventE' unit :=
  match filter is_FromServer t with
  | [] => ret tt
  | _ :: _ =>
    t' <- pick_event t;;
    descramble t'
  end.

(* Functions to list the descrambled traces *)
Section ListDescramble.

Fixpoint list_eventE' (fuel : nat) (s : M eventE' unit)
           (acc : list hypo_trace) (new : hypo_trace -> hypo_trace) :
  option (list hypo_trace) :=
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
    | Vis _ (| _Or |) k =>
      match _Or in nondetE X' return (X' -> _) -> _ with
      | Or => fun id =>
        let go b := list_eventE' fuel (k (id b)) acc new in
        (go true <|> go false)%option
      end (fun x => x)
    | Vis _ ( _Fail ||) _ => None
    end
  end.

(* [None] if not enough fuel. *)
Definition list_eventE (fuel : nat) (s : M eventE' unit) :
  option (list hypo_trace) :=
  list_eventE' fuel s [] (fun t => t).

(* Fuel of the order of [length t ^ 2] should suffice. *)
Definition list_descramblings (fuel : nat) (t : real_trace) :
  option (list hypo_trace) :=
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

Definition select_input_events : real_trace -> list (real_event * real_trace) :=
  fun tr =>
    take_while
      (fun '(ev, _) => negb (is_FromServer ev))
      (picks tr).

Definition select_connect :
  real_trace -> list (hypo_event * real_trace * connection_id) :=
  fun tr =>
    filter_opt
      (fun '(ev, tr) =>
         match ev with
         | NewConnection c => Some (real_to_hypo_event ev, tr, c)
         | _ => None
         end)
      (select_input_events tr).

Definition select_to_server :
  connection_id -> real_trace -> option (hypo_event * real_trace * byte) :=
  fun c tr =>
    find_opt
      (fun '(ev, tr) =>
         match ev with
         | ToServer c' b =>
           if c = c' ? then Some (real_to_hypo_event ev, tr, b) else None
         | _ => None
         end)
      (select_input_events tr).

Definition select_from_server :
  connection_id -> real_trace -> hypo_event * real_trace * option byte :=
  fun c tr =>
    let res := find_opt (fun '(ev, tr) =>
                           match ev with
                           | FromServer c' b =>
                             if c = c' ? then Some (ev, tr, b) else None
                           | _ => None
                           end) (picks tr) in
    match res with
    | Some (ev, tr, b) => (real_to_hypo_event ev, tr, Some b)
    | None => (FromServer c None, tr, None)
    end.

Definition select_event {X} (e : observerE X) (tr : real_trace) :
  M eventE' (X * real_trace) :=
  match e with
  | ObsConnect =>
    '(ev, tr, c) <- choose (select_connect tr);;
    ^ Happened ev;;
    ret (c, tr)
  | ObsToServer c =>
    match select_to_server c tr with
    | None => fail "Missing ToServer"
    | Some (ev, tr, b) =>
      ^ Happened ev;;
      ret (b, tr)
    end
  | ObsFromServer c =>
    let '(ev, tr, ob) := select_from_server c tr in
    ^ Happened ev;;
    ret (ob, tr)
  end.

(* [s]: tree of acceptable traces (spec)
   [t]: scrambled trace

   The result tree has a [Ret] leaf iff there is a descrambled
   trace accepted by [s] ([is_trace_of]).
 *)
CoFixpoint intersect_trace
            (s : ObserverM unit)
            (t : real_trace) :
  M (failureE +' nondetE +' eventE) unit :=
  match s with
  | Tau s => Tau (intersect_trace s t)
  | Ret tt =>
    match filter is_FromServer t with
    | [] => ret tt
    | _ :: _ => fail "unexplained events remain"
    end
  | Vis _ ( e |) k => Vis ( e |) (fun x => intersect_trace (k x) t)
  | Vis X (| e ) k =>
    match filter is_FromServer t with
    | [] => ret tt
    | _ :: _ =>
      xt <- select_event e t;;
      let '(x, t) := xt in
      intersect_trace (k x) t
    end
  end.

CoFixpoint find' (ts : list (hypo_trace * M eventE' unit)) :
  M emptyE (option hypo_trace) :=
  match ts with
  | [] => ret None
  | (tr, t) :: ts =>
    match t with
    | Tau t => Tau (find' ((tr, t) :: ts))
    | Ret tt => ret (Some (rev tr))
    | Vis X e k =>
      match e with
      | (| e ) =>
        match e in eventE X' return (X' -> X) -> _ with
        | Happened ev => fun id => Tau (find' ((ev :: tr, k (id tt)) :: ts))
        end (fun x => x)
      | (| _Or |) =>
        match _Or in nondetE X' return (X' -> X) -> _ with
        | Or => fun id =>
          Tau (find' ((tr, k (id true)) :: (tr, k (id false)) :: ts)%list)
        end (fun x => x)
      | ( _Fail ||) => Tau (find' ts)
      end
    end
  end.

Definition option_to_list {A} (o : option A) : list A :=
  match o with
  | None => []
  | Some a => [a]
  end.

Fixpoint to_result (fuel : nat) (m : M emptyE (option hypo_trace)) :
  result hypo_trace unit :=
  match fuel with
  | O => DONTKNOW
  | S fuel =>
    match m with
    | Ret (Some tr) => OK tr
    | Ret None => FAIL tt
    | Tau m => to_result fuel m
    | Vis X e k => match e in emptyE X' with end
    end
  end.

Definition is_scrambled_trace_test_
           (fuel : nat) (s : ObserverM unit) (t : real_trace) :
  result hypo_trace unit :=
  to_result fuel (find' [([], intersect_trace s t)]).

Definition is_scrambled_trace_test :
           ObserverM unit -> real_trace -> result hypo_trace unit :=
  is_scrambled_trace_test_ (5 * _1000).

(* We will then generate traces produced by a server to test them
   with [is_scrambled_trace_test].
   There are two ways:
   - We can compile and run the actual C server,
     talking to it over actual sockets. This is implemented in
     [Test.TestExternal].
   - We can generate traces by walking through the itree model of
     the C program. [Lib.SimpleSpec_ServerTrace]
 *)
