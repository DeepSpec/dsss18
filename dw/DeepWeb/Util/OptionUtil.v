Definition isSome {A} (a: option A): bool :=
  match a with
  | Some _ => true
  | None => false
  end.
