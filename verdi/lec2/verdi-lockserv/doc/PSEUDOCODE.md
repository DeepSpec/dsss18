Pseudocode for the Lock Server Protocol
=======================================

Nodes
-----

```ocaml
Name := Server | Agent(int)
```

API
---

```ocaml
Input := Lock | Unlock
Out := Granted
```

Internal Messages
----------------

```ocaml
Msg := LockMsg | UnlockMsg | GrantedMsg
```

State
-----

```ocaml
State Server := list Name (* head agent holds lock, tail agents wait *)
State (Agent _) := bool (* true iff client holds lock *)

InitState Server := []
InitState (Agent _) := false
```

API Handlers
------------

```ocaml
HandleInp (n: Name) (s: State n) (inp: Inp) :=
match n with
| Server => nop (* server performs no external IO *)
| Agent _ => 
  match inp with
  | Lock => 
    send (Server, LockMsg)
  | Unlock =>
    if s == true then s := false ; send (Server, UnlockMsg)
```

Internal Message Handlers
-------------------------

```ocaml
HandleMsg (n: Name) (s: State n) (src: Name) (msg: Msg) :=
match n with
| Server =>
  match msg with
  | LockMsg => 
    (* if lock not held, immediately grant *)
    if s == [] then send (src, GrantedMsg) ;
    (* add requestor to end of queue *)
    s := s ++ [src]
  | UnlockMsg =>
    (* head of queue no longer holds lock *)
    s := tail s ;
    (* grant lock to next waiting agent, if any *)
    if s != [] then send (head s, GrantedMsg)
  | _ => nop (* never happens *)
| Agent _ => 
  match msg with
  | GrantedMsg =>
    s := true ;
    output Granted
  | _ => nop (* never happens *)
```
