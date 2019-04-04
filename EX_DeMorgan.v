Theorem deMorgan : forall P Q : Prop, ~(P \/ Q) <-> ~P /\ ~Q.
  Proof.
    intros Po Qo.
    unfold not.
    split.
    - intro H.
      split.
      + intro H0.
        assert (Po \/ Qo).
        * left.  assumption.
        * apply H in H1.
          assumption.
      + intro H0.
        assert (Po \/ Qo).
        * right.  assumption.
        * apply H in H1.
          assumption.
     - intro H.
       intro H1.
       destruct H.
       elim H1.
       + assumption.
       + assumption.
  Qed.