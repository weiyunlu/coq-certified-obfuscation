Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import SF_Maps.
Require Import SF_Imp.
Require Import SF_Hoare.
Require Import SF_Equiv.

(* ----------------------------------------------------------------------------------------------------------------- *)

Section StateEquivalence.

(* The trivial transformation just inserts dummy -If- branches with 'true'.
   Usage: c1 is the program or commands you want to protect, c2 is whatever. *)

Definition trivial_trans (c1 c2 : com) :=
  (IFB true THEN c1 ELSE c2 FI).

(* Extending notation from Maps.v from up to 6 arguments to up to 10+ arguments.
   Apparently there's no better way to do this, according to Software Foundations...
   I could write a script in, say, Python, to generate the text for the Coq code
   automatically, if I need to scale this up any further. *)

Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w }" :=
  (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }) g w) (at level 20).

Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i }" :=
  (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w }) h i) (at level 20).

Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k }" :=
  (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; g --> w ; h --> i}) j k) (at level 20).

Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k ; l --> n }" :=
  (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; g --> w ; h --> i ; j --> k}) l n) (at level 20).

Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }) g w) (at level 0).

Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w}) h i) (at level 0).

Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i}) j k) (at level 0).

Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k ; l --> m }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k}) l m) (at level 0).

Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k ; l --> m ; n --> o }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k ; l --> m}) n o) (at level 0).

Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k ; l --> m ; n --> o ; p --> q }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k ; l --> m ; n --> o}) p q) (at level 0).

Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k ; l --> m ; n --> o ; p --> q ; r --> s }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k ; l --> m ; n --> o ; p --> q}) r s) (at level 0).

Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k ; l --> m ; n --> o ; p --> q ; r --> s ; t2 --> t3 }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k ; l --> m ; n --> o ; p --> q ; r --> s}) t2 t3) (at level 0).

(* Creating some more variables for the opaque predicates to come. *)

Definition X' : string := "X'".
Definition Y' : string := "Y'".
Definition Z' : string := "Z'".
Definition Z'' : string := "Z''".

(* Example demonstrating factorial program and its trivial transform do the same thing on X = 3.
   Program takes X as input, uses Z as a temp variable, and stores the output in Y. *)

Definition fact_nonzero : com :=
  Z ::= X;;
  Y ::= 1;;
  WHILE ! (Z <= 1) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END.

Example factorial_3:
  fact_nonzero / { X --> 3 } \\
    { X --> 3; Z --> 3; Y --> 1; Y --> 3; Z --> 2; Y --> 6; Z --> 1 }.
  Proof.
    unfold fact_in_coq.
    apply E_Seq with { X --> 3 ; Z --> 3 }.
    - apply E_Ass.  reflexivity.
    - apply E_Seq with { X --> 3 ; Z --> 3 ; Y --> 1 }.
      + apply E_Ass; reflexivity.
      + apply E_WhileTrue with { X --> 3; Z --> 3; Y --> 1; Y --> 3; Z --> 2 }.
        * reflexivity.
        * apply E_Seq with { X --> 3; Z --> 3; Y --> 1; Y --> 3 }; apply E_Ass; reflexivity.
        * apply E_WhileTrue with { X --> 3; Z --> 3; Y --> 1; Y --> 3; Z --> 2; Y --> 6; Z --> 1 }.
          -- reflexivity.
          -- apply E_Seq with {X --> 3; Z --> 3; Y --> 1; Y --> 3; Z --> 2; Y --> 6};
             apply E_Ass; reflexivity.
          -- apply E_WhileFalse.  reflexivity.
  Qed.

Example factorial_3_trivial_trans:
  forall c2 : com, (trivial_trans fact_nonzero c2) / { X --> 3 } \\
    { X --> 3; Z --> 3; Y --> 1; Y --> 3; Z --> 2; Y --> 6; Z --> 1 }.
  Proof.
    unfold fact_nonzero.  unfold trivial_trans.  intro c2.
    apply E_IfTrue.  reflexivity.  apply factorial_3.
  Qed.

(* Some remarks:
   1. This notion of both programs having the 'same' output is stronger than we want.
      It not only looks at the state of variables at the end of execution, but also
      considers the intermediate assignments.  Need to check if cequiv is this strict.
   2. Perhaps Hoare Logic would be a better approach; it would allow us to specify the
      useful pre and post conditions without worrying about comparing all intermediate
      assignments. *)

(* Ok, now let's do the simple opaque predicate of degree 2.  This is nothing more than the
   kindergarten formula (x + 1)^2 = x^2 + 2x + 1, but it should be out of reach of SMT solvers
   that only work on linear arithmetic. *)

Definition opaque_trans x c1 c2 :=
  X' ::= (ANum x) ;;
  Z' ::= X' * X' ;;
  Z' ::= Z' + X' ;;
  Z' ::= Z' + X' ;;
  Z' ::= Z' + 1 ;;
  Z'' ::= X' + 1 ;;
  Z'' ::= Z'' * Z'' ;;
  IFB (BEq Z' Z'') THEN c1 ELSE c2 FI.

(* An idea: what about higher order opaque predicates?  We could, for example, hide the two
   applications of Z' ::= Z' + X' behind some kind of loop that evaluates a predicate, but always
   will run exactly twice? *)

(* The final output isn't actually exactly the same, since we need to account for the extra
   variables introduced by the opaque predicate.  However, the 'tails' are the same. *)

(* Let's run the opaque transformer with x=2 and show the output is still y=6. *)

Example factorial_3_opaque_trans_constant:
  forall c2, (opaque_trans 2 fact_nonzero c2) / { X --> 3 } \\
    { X --> 3;
      X' --> 2 ; Z' --> 4 ; Z' --> 6 ; Z' --> 8 ; Z' --> 9 ; Z'' --> 3 ; Z'' --> 9 ;
      Z --> 3; Y --> 1; Y --> 3; Z --> 2; Y --> 6; Z --> 1 }.
  Proof.
    intros.
    unfold fact_nonzero.  unfold opaque_trans.
    apply E_Seq with { X --> 3; X' --> 2 }. apply E_Ass; reflexivity.
    apply E_Seq with { X --> 3; X' --> 2; Z' --> 4 }.  apply E_Ass; reflexivity.
    apply E_Seq with { X --> 3; X' --> 2; Z' --> 4 ; Z' --> 6 }.  apply E_Ass; reflexivity.
    apply E_Seq with { X --> 3; X' --> 2; Z' --> 4 ; Z' --> 6 ; Z' --> 8 }.
      apply E_Ass; reflexivity.
    apply E_Seq with { X --> 3; X' --> 2; Z' --> 4 ; Z' --> 6 ; Z' --> 8 ; Z' --> 9 }.
      apply E_Ass; reflexivity.
    apply E_Seq with { X --> 3; X' --> 2; Z' --> 4 ; Z' --> 6 ; Z' --> 8 ; Z' --> 9 ; Z'' --> 3 }.
      apply E_Ass; reflexivity.
    apply E_Seq with { X --> 3; X' --> 2; Z' --> 4 ; Z' --> 6 ; Z' --> 8 ; Z' --> 9 ; Z'' --> 3 ;
      Z'' --> 9 }.  apply E_Ass; reflexivity.
    apply E_IfTrue.  reflexivity.
    (* Copy paste of factorial_3 proof with additional assignments for the opaque predicate. *)
    apply E_Seq with { X --> 3; X' --> 2; Z' --> 4 ; Z' --> 6 ; Z' --> 8 ; Z' --> 9 ; Z'' --> 3 ;
      Z'' --> 9 ; Z --> 3 }.
    - apply E_Ass.  reflexivity.
    - apply E_Seq with { X --> 3 ; X' --> 2; Z' --> 4 ; Z' --> 6 ; Z' --> 8 ; Z' --> 9 ; Z'' --> 3 ;
        Z'' --> 9 ; Z --> 3 ; Y --> 1 }.
      + apply E_Ass; reflexivity.
      + apply E_WhileTrue with { X --> 3; X' --> 2; Z' --> 4 ; Z' --> 6 ; Z' --> 8 ; Z' --> 9 ;
          Z'' --> 3 ; Z'' --> 9 ; Z --> 3; Y --> 1; Y --> 3; Z --> 2 }.
        * reflexivity.
        * apply E_Seq with { X --> 3; X' --> 2; Z' --> 4 ; Z' --> 6 ; Z' --> 8 ; Z' --> 9 ;
          Z'' --> 3 ; Z'' --> 9 ; Z --> 3; Y --> 1; Y --> 3 }; apply E_Ass; reflexivity.
        * apply E_WhileTrue with { X --> 3; X' --> 2; Z' --> 4 ; Z' --> 6 ; Z' --> 8 ; Z' --> 9 ;
            Z'' --> 3 ; Z'' --> 9 ; Z --> 3; Y --> 1; Y --> 3; Z --> 2; Y --> 6; Z --> 1 }.
          -- reflexivity.
          -- apply E_Seq with {X --> 3; X' --> 2; Z' --> 4 ; Z' --> 6 ; Z' --> 8 ; Z' --> 9 ;
              Z'' --> 3 ; Z'' --> 9 ; Z --> 3; Y --> 1; Y --> 3; Z --> 2; Y --> 6};
              apply E_Ass; reflexivity.
          -- apply E_WhileFalse.  reflexivity.
  Qed.


Lemma opaque_taut : forall x : nat, x * x + x + x + 1 = (x + 1) * (x + 1).
Proof.
  intro x.
  rewrite -> mult_plus_distr_l.   rewrite -> mult_plus_distr_r.  omega.
Qed.

Lemma opaque_taut' : forall x : nat, beq_nat (x * x + x + x + 1) ((x + 1) * (x + 1)) = true.
Proof.
  intro x.  rewrite beq_nat_true_iff.  apply opaque_taut.
Qed.

Lemma opaque_taut_sym : forall x : nat, (x + 1) * (x + 1) = x * x + x + x + 1.
Proof.
  intros.  symmetry.  apply opaque_taut.
Qed.

Lemma opaque_taut'_sym : forall x : nat, beq_nat ((x + 1) * (x + 1)) (x * x + x + x + 1) = true.
Proof.
  intro x.  rewrite beq_nat_true_iff.  apply opaque_taut_sym.
Qed.

(* Remark: even with copy/paste these proofs are getting brutally tedious.
   I may need to learn how to write an LTAC to make this easier. *)

(* Example of the general transformation on factorial 3. *)

Example factorial_3_opaque_trans:
  forall x c2, (opaque_trans x fact_nonzero c2) / { X --> 3 } \\
    { X --> 3; X' --> x; Z' --> x * x; Z' --> x * x + x; Z' --> x * x + x + x;
      Z' --> x * x + x + x + 1; Z'' --> x + 1; Z'' --> (x + 1) * (x + 1); Z --> 3; Y --> 1;
      Y --> 3; Z --> 2; Y --> 6; Z --> 1 }.
  Proof.
    intros.
    unfold fact_nonzero.  unfold opaque_trans.
    apply E_Seq with { X --> 3; X' --> x }.  apply E_Ass; reflexivity.
    apply E_Seq with { X --> 3; X' --> x; Z' --> x * x }.  apply E_Ass; reflexivity.
    apply E_Seq with { X --> 3; X' --> x; Z' --> x * x ; Z' --> x * x + x }.  apply E_Ass; reflexivity.
    apply E_Seq with { X --> 3; X' --> x; Z' --> x * x ; Z' --> x * x + x ; Z' --> x * x + x + x }.
      apply E_Ass; reflexivity.
    apply E_Seq with { X --> 3; X' --> x; Z' --> x * x ; Z' --> x * x + x ; Z' --> x * x + x + x ;
      Z' --> x * x + x + x + 1}.  apply E_Ass; reflexivity.
    apply E_Seq with { X --> 3; X' --> x; Z' --> x * x ; Z' --> x * x + x ; Z' --> x * x + x + x ;
      Z' --> x * x + x + x + 1 ; Z'' --> x + 1}.  apply E_Ass; reflexivity.
    apply E_Seq with { X --> 3; X' --> x; Z' --> x * x ; Z' --> x * x + x ; Z' --> x * x + x + x ;
      Z' --> x * x + x + x + 1 ; Z'' --> x + 1 ; Z'' --> (x + 1) * (x + 1)}.  apply E_Ass; reflexivity.
    apply E_IfTrue.  simpl.  apply opaque_taut'.
    apply E_Seq with { X --> 3; X' --> x; Z' --> x * x ; Z' --> x * x + x ; Z' --> x * x + x + x ;
      Z' --> x * x + x + x + 1 ; Z'' --> x + 1 ; Z'' --> (x + 1) * (x + 1) ; Z --> 3 }.
    - apply E_Ass.  reflexivity.
      - apply E_Seq with { X --> 3 ; X' --> x; Z' --> x * x ; Z' --> x * x + x ; Z' --> x * x + x + x ;
          Z' --> x * x + x + x + 1 ; Z'' --> x + 1 ; Z'' --> (x + 1) * (x + 1) ; Z --> 3 ; Y --> 1 }.
      + apply E_Ass; reflexivity.
      + apply E_WhileTrue with { X --> 3; X' --> x; Z' --> x * x ; Z' --> x * x + x ;
          Z' --> x * x + x + x ; Z' --> x * x + x + x + 1 ; Z'' --> x + 1 ; Z'' --> (x + 1) * (x + 1) ;
          Z --> 3; Y --> 1; Y --> 3; Z --> 2 }.
        * reflexivity.
        * apply E_Seq with { X --> 3; X' --> x; Z' --> x * x ; Z' --> x * x + x ; Z' --> x * x + x + x ;
            Z' --> x * x + x + x + 1 ; Z'' --> x + 1 ; Z'' --> (x + 1) * (x + 1) ; Z --> 3; Y --> 1;
            Y --> 3 }; apply E_Ass; reflexivity.
        * apply E_WhileTrue with { X --> 3; X' --> x; Z' --> x * x ; Z' --> x * x + x ;
            Z' --> x * x + x + x ; Z' --> x * x + x + x + 1 ; Z'' --> x + 1 ; Z'' --> (x + 1) * (x + 1) ;
            Z --> 3; Y --> 1; Y --> 3; Z --> 2; Y --> 6; Z --> 1 }.
          -- reflexivity.
          -- apply E_Seq with {X --> 3; X' --> x; Z' --> x * x ; Z' --> x * x + x ; Z' --> x * x + x + x ;
               Z' --> x * x + x + x + 1 ; Z'' --> x + 1 ; Z'' --> (x + 1) * (x + 1) ; Z --> 3; Y --> 1;
               Y --> 3; Z --> 2; Y --> 6}; apply E_Ass; reflexivity.
          -- apply E_WhileFalse.  reflexivity.
  Qed.

(* Cequiv is too strong a notion of equivalence.  Indeed, the original and transformed version of
   the program aren't equivalent in this sense, because the state keeps track of all intermediate
   assignments including the variables used strictly in the opaque predicate.  We really just care
   about the precondition X = 3 implying the post-condition Y = 6... so Hoare Logic seems a better
   way to formalize this.

   The challenge there is, how do we formulate equivalence in general?  We'll start by using a
   single input and single output being the same between one program and another. *)

End StateEquivalence.

(* ----------------------------------------------------------------------------------------------------------------- *)

Section HoareEquivalence.

Definition as_x (x0 : nat) : Assertion := (fun st => st X = x0).
Definition as_y (y0 : nat) : Assertion := (fun st => st Y = y0).

(* We reformulate our factorial program slightly, counting up from zero rather than down from X. *)

Definition fact_program : com :=
  Y ::= 1;;
  Z ::= 0;;
  WHILE ! (Z = X) DO
    Z ::= Z + 1;;
    Y ::= Y * Z
  END.

Lemma fact_dist : forall x : nat, fact x * (x + 1) = fact (x + 1).
  Proof.
    intros.
    induction x.
    - auto.
    - simpl.  rewrite <- Nat.add_1_r.  rewrite <- IHx.  simpl.
      repeat rewrite mult_plus_distr_r.  repeat rewrite mult_plus_distr_l.  simpl.
      repeat rewrite plus_0_r.  repeat rewrite mult_1_r.  repeat rewrite mult_assoc.
      repeat rewrite plus_assoc.
      assert (H1: fact x * x = x * fact x).
        { rewrite mult_comm.  auto. }
      repeat rewrite H1.
      assert (H2: forall y z : nat, y * z + z + z + y * z * y + y * z + y * z =
        y * z + z + y * z * y + y * z + y * z + z).
        { intros.   omega. }
      apply H2.
   Qed.

Ltac disp :=
  simpl; unfold assert_implies; auto.

(* Now the specification of factorial of 3 for the original and transformed programs looks
   syntactically the same, modulo the name of the program itself. *)

Example factorial_3_hoare:
  {{ as_x 3 }} fact_program {{ as_y 6 }}.
  Proof.
    unfold as_x, as_y, fact_program.
    apply hoare_consequence_post with (fun st : state => st Y = fact 3).  2: disp.
    apply hoare_consequence_pre with (fun st : state => 1 = 1 /\ st X = 3).  2: disp.
    apply hoare_consequence_pre with (fun st : state => 1 = fact 0 /\ st X = 3).  2: disp.
    eapply hoare_seq.  eapply hoare_seq.
    apply hoare_consequence_post with
      (fun st : state => (fun st0 : state => st0 Y = fact (st0 Z) /\ st0 X = 3) st /\ ~ bassn (! (Z = X)) st).
    apply hoare_while.
    3: apply hoare_asgn.
    3: apply hoare_consequence_post with (fun st : state => st Y = fact 0 /\ st X = 3).  4: disp.
    3: apply hoare_consequence_pre with ((fun st : state => st Y = fact 0 /\ st X = 3) [Y |-> 1]).
    3: apply hoare_asgn.  3: disp.
    2: { disp.  unfold bassn.  simpl.  intros.  destruct H.  destruct H.
      rewrite not_true_iff_false in H0.  rewrite negb_false_iff in H0.  rewrite Nat.eqb_eq in H0.
      rewrite H.  rewrite H0.  rewrite H1.  auto. }
    eapply hoare_seq.
    apply hoare_asgn.
    apply hoare_consequence_post with (fun st : state => (st Y * st Z) = fact (st Z) /\ st X = 3).
      2: disp.
    eapply hoare_consequence_pre.  apply hoare_asgn.
    disp.  intros.  simpl.  unfold assn_sub.  simpl.
    destruct H.  destruct H.  split.  2: auto.  unfold t_update.  simpl.  rewrite H.
    symmetry.  rewrite fact_dist.  auto.
  Qed.

(* Let's fold some of the assignments of opaque_trans together to make the proofs less tedious. *)

Definition opaque_trans' x c1 c2 :=
  X' ::= (ANum x) ;;
  Z' ::= X' * X' + X' + X' + 1 ;;
  Z'' ::= (X' + 1) * (X' + 1) ;;
  IFB (BEq Z' Z'') THEN c1 ELSE c2 FI.

Example factorial_3_hoare_opaque: forall x c2,
  {{ as_x 3 }} (opaque_trans' x fact_program c2) {{ as_y 6 }}.
  Proof.
    intros x c2.  unfold as_x, as_y, fact_program, opaque_trans'.

    (* Massaging and steps in opaque predicate *)
    eapply hoare_seq.  eapply hoare_seq.  eapply hoare_seq.  apply hoare_if.
    5: apply hoare_consequence_pre with ((fun st : state => st X = 3 /\ st X' = x) [X' |-> x]).
    6: disp; unfold assn_sub; unfold t_update; simpl; auto.  5: apply hoare_asgn.
    4: apply hoare_consequence_pre with
      ((fun st : state => st X = 3 /\ st X' = x /\ st Z' = x * x + x + x + 1) [Z' |-> X' * X' + X' + X' + 1]).
    4: apply hoare_asgn.  4: unfold assert_implies.
    4: { intros.  unfold assn_sub, t_update.  simpl.  destruct H.  repeat split.  auto.  auto.  auto. }
    3: apply hoare_consequence_pre with
      ((fun st : state => st X = 3 /\ st X' = x /\ st Z' = x * x + x + x + 1 /\ st Z'' = (x + 1) * (x + 1))
      [Z'' |-> (X' + 1) * (X' + 1)]).
    3: apply hoare_asgn.
    3: { unfold assert_implies.  intros.  unfold assn_sub, t_update.  simpl.  destruct H.  destruct H0.
    repeat split.  auto.  auto.  auto.  subst.  auto. }

    (* Else branch never executes *)
    2: { unfold hoare_triple.  intros.  unfold bassn in H0.  destruct H0.  destruct H0.  destruct H0.
    destruct H2.  destruct H2.  contradiction H1.  simpl.  rewrite H2.  rewrite H3.  rewrite Nat.eqb_eq.
    apply opaque_taut. }

    (* If branch always executes *)
    apply hoare_consequence_pre with (fun st : state => st X = 3).
    apply factorial_3_hoare.
    disp.  intros.  repeat destruct H.  auto.
  Qed.

(* The proofs above should generalize fairly easily to factorial of arbitrary numbers.
   Then: formulate and prove an equivalence between these two fact programs in general.

   Then: do it for -any- program with -any- pre and post assignments. *)

Example factorial_all_hoare: forall xo,
  {{ as_x xo }} fact_program {{ as_y (fact xo) }}.
  Proof.
    intros.  unfold as_x, as_y, fact_program.
    apply hoare_consequence_post with (fun st : state => st Y = fact xo).  2: disp.
    apply hoare_consequence_pre with (fun st : state => 1 = 1 /\ st X = xo).  2: disp.
    apply hoare_consequence_pre with (fun st : state => 1 = fact 0 /\ st X = xo).  2: disp.
    eapply hoare_seq.  eapply hoare_seq.
    apply hoare_consequence_post with
      (fun st : state => (fun st0 : state => st0 Y = fact (st0 Z) /\ st0 X = xo) st /\ ~ bassn (! (Z = X)) st).
    apply hoare_while.
    3: apply hoare_asgn.
    3: apply hoare_consequence_post with (fun st : state => st Y = fact 0 /\ st X = xo).  4: disp.
    3: apply hoare_consequence_pre with ((fun st : state => st Y = fact 0 /\ st X = xo) [Y |-> 1]).
    3: apply hoare_asgn.  3: disp.
    2: { disp.  unfold bassn.  simpl.  intros.  destruct H.  destruct H.
      rewrite not_true_iff_false in H0.  rewrite negb_false_iff in H0.  rewrite Nat.eqb_eq in H0.
      rewrite H.  rewrite H0.  rewrite H1.  auto. }
    eapply hoare_seq.
    apply hoare_asgn.
    apply hoare_consequence_post with (fun st : state => (st Y * st Z) = fact (st Z) /\ st X = xo).
      2: disp.
    eapply hoare_consequence_pre.  apply hoare_asgn.
    disp.  intros.  simpl.  unfold assn_sub.  simpl.
    destruct H.  destruct H.  split.  2: auto.  unfold t_update.  simpl.  rewrite H.
    symmetry.  rewrite fact_dist.  auto.
  Qed.

Example factorial_all_hoare_opaque: forall x xo c2,
  {{ as_x xo }} (opaque_trans' x fact_program c2) {{ as_y (fact xo) }}.
  Proof.
    intros x xo c2.  unfold as_x, as_y, fact_program, opaque_trans'.

    (* Massaging and steps in opaque predicate *)
    eapply hoare_seq.  eapply hoare_seq.  eapply hoare_seq.  apply hoare_if.
    5: apply hoare_consequence_pre with ((fun st : state => st X = xo /\ st X' = x) [X' |-> x]).
    6: disp; unfold assn_sub; unfold t_update; simpl; auto.  5: apply hoare_asgn.
    4: apply hoare_consequence_pre with
      ((fun st : state => st X = xo /\ st X' = x /\ st Z' = x * x + x + x + 1) [Z' |-> X' * X' + X' + X' + 1]).
    4: apply hoare_asgn.  4: unfold assert_implies.
    4: { intros.  unfold assn_sub, t_update.  simpl.  destruct H.  repeat split.  auto.  auto.  auto. }
    3: apply hoare_consequence_pre with
      ((fun st : state => st X = xo /\ st X' = x /\ st Z' = x * x + x + x + 1 /\ st Z'' = (x + 1) * (x + 1))
      [Z'' |-> (X' + 1) * (X' + 1)]).
    3: apply hoare_asgn.
    3: { unfold assert_implies.  intros.  unfold assn_sub, t_update.  simpl.  destruct H.  destruct H0.
    repeat split.  auto.  auto.  auto.  subst.  auto. }

    (* Else branch never executes *)
    2: { unfold hoare_triple.  intros.  unfold bassn in H0.  destruct H0.  destruct H0.  destruct H0.
    destruct H2.  destruct H2.  contradiction H1.  simpl.  rewrite H2.  rewrite H3.  rewrite Nat.eqb_eq.
    apply opaque_taut. }

    (* If branch always executes *)
    apply hoare_consequence_pre with (fun st : state => st X = xo).
    apply factorial_all_hoare.
    disp.  intros.  repeat destruct H.  auto.
  Qed.

(* Generalize: we'll say a transformation satisfies Hoare Fidelity with regard to input X = xo yielding
   output Y = yo if any time the original program satisfies the triple, so does the transformed program.

   Do we need to make it an if and only if?  Maybe not.  We only really care about the transformed program
   still preserving the requirement given to the original program.  There is not much useful about knowing
   that the transformed program satisfying a requirement implies the original one does as well (or equivalently,
   that the original program NOT satisfying implies the transformed one also does not.   It would also be
   difficult to prove, as you would have to take knowledge about an obfuscated program (which is supposed to
   be hard to understand!) and reason with it backwards. *)


Definition Hoare_fidelity_xy c1 c2 := forall xo yo,
  hoare_triple (as_x xo) c1 (as_y yo) -> hoare_triple (as_x xo) c2 (as_y yo).

(* Any hoare triple with any pre and post condition of the form X=x0 P Y=y0 is preserved by opaque_trans. *)

Lemma Opaque_trans_hoare_fidelity_xy : forall x c1 c2,
  Hoare_fidelity_xy c1 (opaque_trans' x c1 c2).
  Proof.
    intros.  unfold Hoare_fidelity_xy, opaque_trans'.  intros.

    (* Nearly exact generalization copy/paste from factorial_all_hoare. *)
    eapply hoare_seq.  eapply hoare_seq.  eapply hoare_seq.  apply hoare_if.
    5: apply hoare_consequence_pre with ((fun st : state => as_x xo st /\ st X' = x) [X' |-> x]).
    6: disp; unfold assn_sub; unfold t_update; simpl; auto.  5: apply hoare_asgn.
    4: apply hoare_consequence_pre with
      ((fun st : state => st X = xo /\ st X' = x /\ st Z' = x * x + x + x + 1) [Z' |-> X' * X' + X' + X' + 1]).
    4: apply hoare_asgn.  4: unfold assert_implies.
    4: { intros.  unfold assn_sub, t_update.  simpl.  destruct H0.  repeat split.  auto.  auto.  auto. }
    3: apply hoare_consequence_pre with
      ((fun st : state => st X = xo /\ st X' = x /\ st Z' = x * x + x + x + 1 /\ st Z'' = (x + 1) * (x + 1))
      [Z'' |-> (X' + 1) * (X' + 1)]).
    3: apply hoare_asgn.
    3: { unfold assert_implies.  intros.  unfold assn_sub, t_update.  simpl.  destruct H0.  destruct H1.
    repeat split.  auto.  auto.  auto.  subst.  auto. }

    (* Else branch never executes *)
    2: { unfold hoare_triple.  intros.  unfold bassn in H1.  destruct H1.  destruct H1.  destruct H1.
    destruct H3.  destruct H3.  contradiction H2.  simpl.  rewrite H3.  rewrite H4.  rewrite Nat.eqb_eq.
    apply opaque_taut. }

    (* If branch always executes *)
    apply hoare_consequence_pre with (fun st : state => st X = xo).  apply H.
    disp.  intros.  repeat destruct H0.  auto.
Qed.

(* But wait... can we do better?  Could we just generalize to ANY pre and post condition?
   Let's attempt it... *)

Definition Hoare_fidelity c1 c2 P Q :=
  hoare_triple P c1 Q -> hoare_triple P c2 Q.


Lemma Opaque_trans_hoare_fidelity : forall x c1 c2 P Q,
  Hoare_fidelity c1 (opaque_trans' x c1 c2) P Q.
  Proof.
    intros.  unfold Hoare_fidelity, opaque_trans'.  intros.

    (* Straightforward generalization : replace condition X = xo with P st. *)
    eapply hoare_seq.  eapply hoare_seq.  eapply hoare_seq.  apply hoare_if.


    5: apply hoare_consequence_pre with ((fun st : state => P st /\ st X' = x) [X' |-> x]).
    6: disp; unfold assn_sub; unfold t_update; simpl; auto.

    (* Whoops!  This doesn't work!  We're left with extra goals (the last one) we can't prove.  Why?
       We were too hasty in our generalization.  It seemed like it should work, but there's a problem...
       our specific precondition before was 'X = xo', but now P is an arbitrary assertion.  The problem is,
       what if it contains the variable X' which is supposed to be reserved for the opaque predicate?  Then,
       the assignment X' |-> x could change the statement of P, and our assumption that P c1 Q is no longer
       able to lift to the new goal. *)
  Abort.

End HoareEquivalence.

(* ----------------------------------------------------------------------------------------------------------------- *)

Section NoAssignment_State.

(* Bahman's reformulation *)

Definition make_opaque_pred (a1 a2: aexp): bexp :=
  BEq a1 a2.
  
Example bexp1 :
  beval { X --> 0 } (((X + 1) * (X + 1)) = (X * X + 2 * X + 1)) = true.
Proof. simpl. reflexivity. Qed.

Definition make_opaque_pred_IFB b c1 c2 :=
  IFB b THEN c1 ELSE c2 FI.


(* Let X be any variable *)
Definition ifb_opaque_command X : com := 
  make_opaque_pred_IFB (make_opaque_pred ((X + 1) * (X + 1)) (X * X + 2 * X + 1)) fact_nonzero SKIP.

Theorem factorial_trans: forall opaque_pred c2,
  bequiv opaque_pred BTrue ->
  cequiv fact_nonzero (make_opaque_pred_IFB opaque_pred fact_nonzero c2).
Proof.
  intros opaque_pred c2 H. unfold cequiv. intros st st'.
  refine (conj _ _).
  - (* -> *)
    intros proof_of_fact_nonzero_st_st'.
    unfold make_opaque_pred_IFB.
    pose (proof1 := IFB_true opaque_pred fact_nonzero c2 H).
    unfold cequiv in proof1. apply proof1. assumption.
  - (* <- *)
    unfold make_opaque_pred_IFB.
    intros H1.
    unfold bequiv in H. simpl in H.
    pose (proof1 := IFB_true opaque_pred fact_nonzero c2 H).
    unfold cequiv in proof1. apply proof1. assumption.
Qed.

Theorem anycom_trans: forall opaque_pred c1 c2,
  bequiv opaque_pred BTrue ->
  cequiv c1 (make_opaque_pred_IFB opaque_pred c1 c2).
Proof.
  intros opaque_pred c1 c2 H. unfold cequiv. intros st st'.
  refine (conj _ _).
  - (* -> *)
    intros proof_of_fact_nonzero_st_st'.
    unfold make_opaque_pred_IFB.
    pose (proof1 := IFB_true opaque_pred c1 c2 H).
    unfold cequiv in proof1. apply proof1. assumption.
  - (* <- *)
    unfold make_opaque_pred_IFB.
    intros H1.
    unfold bequiv in H. simpl in H.
    pose (proof1 := IFB_true opaque_pred c1 c2 H).
    unfold cequiv in proof1. apply proof1. assumption.
Qed.

Check (anycom_trans 
        (make_opaque_pred ((X + 1) * (X + 1)) (X * X + 2 * X + 1)) 
        fact_nonzero SKIP _).

Theorem proof_of_bequiv_opaque_pred : bequiv (make_opaque_pred ((X + 1) * (X + 1)) (X * X + X + X + 1)) BTrue.
Proof.
  unfold bequiv.
  intros st.
  unfold make_opaque_pred. 
  unfold beval.  simpl.  apply opaque_taut'_sym.
Qed.

Theorem proof_of_bequiv_same_BTrue : bequiv (BEq 0 0) BTrue.
Proof.
  intros st. reflexivity. Qed.

Example test_SKIP : cequiv SKIP (make_opaque_pred_IFB (BEq 0 0) SKIP SKIP).
Proof.
  pose (proof1 := anycom_trans (BEq 0 0) SKIP SKIP proof_of_bequiv_same_BTrue). assumption.
Qed.

Example example0_opaque_pred:
  cequiv 
    fact_nonzero 
    (make_opaque_pred_IFB BTrue fact_nonzero SKIP).
  Proof.
  unfold cequiv. intros st st'.
  refine (conj _ _).
  - (* -> *)
    intros proof_of_fact_nonzero_st_st'.
    unfold make_opaque_pred_IFB. unfold make_opaque_pred.
    apply E_IfTrue.
    + unfold beval.  unfold aeval.  auto.
    + assumption.
  - (* <- *)
    unfold make_opaque_pred_IFB.  unfold make_opaque_pred.  intros.
    inversion H.  apply H6.  subst.  inversion H5.
  Qed.

Example example1_opaque_pred:
  cequiv 
    fact_nonzero 
    (make_opaque_pred_IFB (make_opaque_pred ((X + 1) * (X + 1)) (X * X + X + X + 1)) fact_nonzero SKIP).
  Proof.
  unfold cequiv. intros st st'.
  refine (conj _ _).
  - (* -> *)
    intros proof_of_fact_nonzero_st_st'.
    unfold make_opaque_pred_IFB. unfold make_opaque_pred.
    apply E_IfTrue.
    + unfold beval.  unfold aeval.  apply opaque_taut'_sym.
    + assumption.
  - (* <- *)
    unfold make_opaque_pred_IFB.  unfold make_opaque_pred.  intros.
    inversion H.  
    + apply H6.
    + assert (beval st ((X + 1) * (X + 1) = X * X + X + X + 1) = true) by (apply opaque_taut'_sym).
      rewrite H5 in H7.  inversion H7.
  Qed.

End NoAssignment_State.

(* ----------------------------------------------------------------------------------------------------------------- *)

Section NoAssignment_Hoare.

Definition square_program : com :=
  Y ::= X * X.

Definition trans_fact_square_program : com :=
  (make_opaque_pred_IFB (make_opaque_pred ((X + 1) * (X + 1)) (X * X + X + X + 1))
    fact_program square_program).

(* Pre and post condition of base program. *)

Example fact_3_hoare :
  {{ as_x 3 }} fact_program {{ as_y 6 }}.
  Proof.
    replace 6 with (fact 3).
    - apply factorial_all_hoare.
    - auto.
  Qed.

(* With knowledge of opaque predicate value, we get same thing. *)

Example trans_fact_square_3_hoare :
  {{ as_x 3 }} trans_fact_square_program {{ as_y 6 }}.
  Proof.
    replace 6 with (fact 3).  2: auto.
    unfold trans_fact_square_program.  unfold make_opaque_pred_IFB, make_opaque_pred.
    unfold fact_program, square_program.  apply hoare_if.
    
    (* Else branch never executes *)
    2: { unfold hoare_triple.  intros.  unfold bassn in H0.  destruct H0.  destruct H0.
    destruct H1.  unfold beval.  unfold aeval.  apply opaque_taut'_sym. }

    (* If branch always executes *) 
    apply hoare_consequence_pre with (fun st : state => st X = 3).
    apply factorial_3_hoare.  simpl; unfold assert_implies; auto.
    intros.  repeat destruct H.  auto.
  Qed.

(* Without knowledge of opaque predicate value, we get can show only a weaker postcondition. *)

Example trans_fact_square_3_hoare_noknowledge :
  {{ as_x 3 }} trans_fact_square_program {{ fun st : state => st Y = 6 \/ st Y = 9 }}.
  Proof.
    unfold trans_fact_square_program.  unfold make_opaque_pred_IFB, make_opaque_pred.
    unfold fact_program, square_program.  apply hoare_if.

    (* Now pretend we don't know anything about the opaque predicate *)

    (* If branch executes *)
    apply hoare_consequence_pre with (fun st : state => st X = 3).
    apply hoare_consequence_post with (as_y (fact 3)).
    apply factorial_3_hoare.  unfold assert_implies.  intros.  unfold as_y, fact in H.  
    simpl in H.  left; auto.

    (* Precondition *)
    simpl; unfold assert_implies; auto.
    intros.  repeat destruct H.  auto.

    (* Else branch executes *)
    apply hoare_consequence_pre with (fun st : state => st X = 3).
    apply hoare_consequence_post with (fun st : state => st Y = 9).
    apply hoare_consequence_pre with ((fun st : state => st Y = 9) [Y |-> X* X]).
    apply hoare_asgn.
    unfold assert_implies.  intros.  unfold assn_sub.  unfold aeval.  rewrite H.  auto.
    unfold assert_implies.  intros.  right; auto.
    unfold assert_implies.  intros.  destruct H.  auto.
  Qed.

End NoAssignment_Hoare.