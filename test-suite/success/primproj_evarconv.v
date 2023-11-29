Section S.
  #[local] Set Printing Unfolded Projection As Match.
  #[projections(primitive=yes)]
  Record r (u : unit) := { r_car : Type }.

  Axiom u : unit.

  Definition rO : r u -> r u := fun o => {| r_car := option (r_car u o) |}.

  Goal forall o, exists M, M (r_car u o)= r_car u (rO o).
  Proof.
    intros. eexists _.
    Timeout 1 refine (eq_refl _).
  Qed.
End S.

