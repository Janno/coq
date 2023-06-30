Primitive run : forall (T : Type) (K : T -> Type) (e : T), (forall v : T, K v) -> K e := #run.

Primitive Blocked := #blocked_type.
Primitive block : forall (T : Type), T -> Blocked T := #block.
Primitive unblock : forall (T : Type), Blocked T -> T := #unblock.

Arguments run {_ _} _ _.
Arguments block {_} _.
Arguments unblock {_} _.
