Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

Require Import Maps.
Require Import Imp.
Require Import Hoare.
Require Import Equiv.

Require Import OBFS_opaque_predicate.
Require Import SF_Imp_Switch.


(* ----------------------------------------------------------------------------------------------------------------- *)


(* Reformulating the if-statement flattening with Imppp2 and the new switching behaviour.  We make a few other changes
   
   1. Instead of building `getters` to break apart a program, we'll construct them from the ground up with
      original_program and transformed_program functions.  This should make proofs more natural?

   2. This way, `original_program` can also add dummy SWITCH assignments to the beginning and end of every
      program.  Maybe now we can finally prove cequiv proper? *)

Definition swVar : string := "swVar".

Definition original_program header cond c1 c2 footer : com :=
  swVar ::= 0 ;;
  header ;;
  IFB cond THEN 
    c1 
  ELSE 
    c2 
  FI ;;
  footer ;;
  swVar ::= 5.

Definition transform_program header cond c1 c2 footer : com :=
  swVar ::= 0 ;;
  WHILE (swVar <= 4) DO
    SWITCH swVar [
      (0, header ;; 
          swVar ::= 1) ;
      (1, IFB cond THEN
            swVar ::= 2 
          ELSE 
            swVar ::= 3 
          FI) ;
      (2, c1 ;;
          swVar ::= 4) ;
      (3, c2 ;;
          swVar ::= 4) ;
      (4, footer ;;
          swVar ::= 5)
    ]
  END.

(* Same WorldEater example from before *)

Definition WorldEater := original_program SKIP (X = 0) SKIP (X ::= 1) SKIP.
Definition TransWorldEater := transform_program SKIP (X = 0) SKIP (X ::= 1) SKIP.

Compute WorldEater.
Compute TransWorldEater.

Definition cequiv' (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st \\ st') <-> (c2 / st \\ st').

(* Lemma we need: updating two different variables in a different order is the same thing. *)

Lemma t_update_comm : forall A (m: total_map A) v1 v2 x y, 
    x <> y -> m & {x --> v1 ; y --> v2} = m & {y --> v2; x --> v1}.
  Proof.
    intros.  apply functional_extensionality.  intros.
    unfold t_update.  destruct (beq_string y x0) eqn:Heq.
    - destruct (beq_string x x0) eqn:Heq2.
      + rewrite beq_string_true_iff in *.  rewrite <- Heq2 in Heq.  symmetry in Heq.  apply H in Heq.  inversion Heq.
      + auto.
    - destruct (beq_string x x0) eqn:Heq2.
      + auto.
      + auto.
  Qed.

(* Bona fide command equivalence of the example program and its transformed state, not just Hoare logic! *)

Example WorldEaterTransEquiv : cequiv' WorldEater TransWorldEater.
  Proof.
    unfold cequiv'.  intros.  split.

      (* Notation *)
      Notation aDict := (loadDict (swVar ::= 0;; SKIP;; (IFB X = 0 THEN SKIP ELSE X ::= 1 FI);; 
                           SKIP;; swVar ::= 5)).
    
      (* (I) Original -> Transformed. *)
      - unfold WorldEater, TransWorldEater.  unfold original_program, transform_program.  intro H.

      (* Break apart sequencing in hypothesis. *)
      inversion H; subst.  inversion H6; subst.  inversion H8; subst.  inversion H10; subst.

      (* Assert initial and final values of swVar *)
      inversion H4; subst.
      assert (A0 : aeval st'1 swVar = 0).  inversion H3.  subst.  auto.
      assert (A5 : aeval st' swVar = 5).  inversion H12.  subst.  auto.

      (* Law of excluded middle: X is 0 or X is nonzero at point of branching statement *)
      destruct (beval (st'1 & {swVar --> 1}) (X = 0)) eqn:LEM.

        (* (I.i Case 1: X = 0. *)
        + unfold ceval_autoload.  eapply E_Seq.  apply H3.  eapply E_WhileTrue.
            * unfold beval.  rewrite A0.  auto.
            * eapply E_Switch.  auto.  rewrite A0.  simpl.  auto.  eapply E_Seq.  apply E_Skip.  apply E_Ass.  auto.
            * simpl.  eapply E_WhileTrue.
              -- unfold beval.  simpl.  auto.
              -- eapply E_Switch.  auto.  simpl.  auto.  apply E_IfTrue.  assumption.  apply E_Ass.  auto.
              -- eapply E_WhileTrue.
                 ++ auto.
                 ++ eapply E_Switch.  auto.  simpl.  auto.  eapply E_Seq.  apply E_Skip.  apply E_Ass.  auto.
                 ++ simpl.  eapply E_WhileTrue.
                    ** auto.
                    ** eapply E_Switch.  auto.  simpl.  auto.  eapply E_Seq.  apply E_Skip.  apply E_Ass.  auto.
                    ** simpl.
                       assert (sameState : st'1 & {swVar --> 1; swVar --> 2; swVar --> 4; swVar --> 5} = st').
                       { apply ceval_deterministic with aDict ((IFB X = 0 THEN SKIP ELSE X ::= 1 FI);; SKIP;; swVar ::= 5) st'1.  
                             2: auto.  eapply E_Seq.  apply E_IfTrue.  auto.  apply E_Skip. 
                                assert (sameState' : st'1 & {swVar --> 1; swVar --> 2; swVar --> 4; swVar --> 5} = st'1 & {swVar --> 5}).
                                  { rewrite t_update_shadow.  rewrite t_update_shadow.  rewrite t_update_shadow.  auto. }
                                rewrite sameState'.  eapply E_Seq.  apply E_Skip.  apply E_Ass.  auto. }
                       rewrite sameState.  eapply E_WhileFalse.
                       --- unfold beval.  rewrite A5.  auto.

         (* I.ii Case 2: X =/= 0 *)
         + unfold ceval_autoload.  eapply E_Seq.  apply H3.  eapply E_WhileTrue.
            * unfold beval.  rewrite A0.  auto.
            * eapply E_Switch.  auto.  rewrite A0.  simpl.  auto.  eapply E_Seq.  apply E_Skip.  apply E_Ass.  auto.
            * simpl.  eapply E_WhileTrue.
              -- unfold beval.  simpl.  auto.
              -- eapply E_Switch.  auto.  simpl.  auto.  apply E_IfFalse.  assumption.  apply E_Ass.  auto.
              -- eapply E_WhileTrue.
                 ++ auto.
                 ++ eapply E_Switch.  auto.  simpl.  auto.  eapply E_Seq.  apply E_Ass.  auto.  apply E_Ass.  auto.
                 ++ simpl.  eapply E_WhileTrue.
                    ** auto.
                    ** eapply E_Switch.  auto.  simpl.  auto.  eapply E_Seq.  apply E_Skip.  apply E_Ass.  auto.
                    ** simpl.
                       assert (sameState : st'1 & {swVar --> 1; swVar --> 3; X --> 1; swVar --> 4; swVar --> 5} = st').
                       { apply ceval_deterministic with aDict ((IFB X = 0 THEN SKIP ELSE X ::= 1 FI);; SKIP;; swVar ::= 5) st'1.  
                             2: auto.  eapply E_Seq.  apply E_IfFalse.  auto.  apply E_Ass.  auto.  simpl.
                             eapply E_Seq.  apply E_Skip.
                                assert (sameState' : st'1 & {swVar --> 1; swVar --> 3; X --> 1; swVar --> 4; swVar --> 5} = 
                                  st'1 & {X --> 1; swVar --> 5}).
                                  { rewrite t_update_shadow.  rewrite t_update_shadow.  rewrite t_update_comm.  rewrite t_update_shadow.
                                    rewrite t_update_comm.  auto.  unfold not.  intro.  inversion H0.  unfold not.  intro.  inversion H0. }
                                rewrite sameState'.  apply E_Ass.  auto. }
                       rewrite sameState.  eapply E_WhileFalse.
                       --- unfold beval.  rewrite A5.  auto.  Admitted. (* Something broke, fix it. *)
(*
      (* (II) Transformed -> Original. *) 
      + unfold TransWorldEater, WorldEater.  unfold transform_program, original_program.  intro H.
        apply E_Seq with (st & {swVar --> 0}).  apply E_Ass.  auto.  eapply E_Seq.  apply E_Skip.

        (* Avoid typing out the dictionary every time *)
        Notation theDict := (loadDict
           (swVar ::= 0;;
           WHILE swVar <= 4
           DO SWITCH swVar
           [(0, SKIP;; swVar ::= 1); (1, IFB X = 0 THEN swVar ::= 2 ELSE swVar ::= 3 FI); (2, SKIP;; swVar ::= 4); (3, X ::= 1;; swVar ::= 4);
           (4, SKIP;; swVar ::= 5)] END)).

        (* Invoke LEM at this point *)
        destruct (beval (st & {swVar --> 0}) (X = 0)) eqn:LEM.

          (* II.i Case 1: X = 0 *)

          + eapply E_Seq.  apply E_IfTrue.  auto.  apply E_Skip.  eapply E_Seq.  apply E_Skip.
            assert (sameState : st & {swVar --> 0 ; swVar --> 5} = st').
            { apply ceval_deterministic with theDict ((swVar ::= 0;;
              WHILE swVar <= 4
              DO SWITCH swVar
                [(0, SKIP;; swVar ::= 1); 
                  (1, IFB X = 0 THEN swVar ::= 2 ELSE swVar ::= 3 FI); 
                  (2, SKIP;; swVar ::= 4); 
                  (3, X ::= 1;; swVar ::= 4);
                  (4, SKIP;; swVar ::= 5)] END)) st.
              2: auto.
              assert (sameState : st & {swVar --> 0; swVar --> 5} = st & {swVar --> 0 ; swVar --> 1 ; swVar --> 2 ; swVar --> 4 ; swVar --> 5}).
              { repeat (rewrite t_update_shadow).  auto. }
              rewrite sameState.  apply E_Seq with (st & {swVar --> 0}).  apply E_Ass.  auto.

              (* While Loop *)
              eapply E_WhileTrue.  auto.  apply E_Switch with 0 (SKIP;; swVar ::= 1).  auto.  auto.
              eapply E_Seq.  apply E_Skip.  apply E_Ass.  auto.  simpl.

              eapply E_WhileTrue.  auto.  apply E_Switch with 1 (IFB X = 0 THEN swVar ::= 2 ELSE swVar ::= 3 FI).  auto.  auto.
              apply E_IfTrue.  auto.  apply E_Ass.  auto.  simpl.

              eapply E_WhileTrue.  auto.  apply E_Switch with 2 (SKIP;; swVar ::= 4).  auto.  auto.
              eapply E_Seq.  apply E_Skip.  apply E_Ass.  auto.  simpl.

              eapply E_WhileTrue.  auto.  apply E_Switch with 4 (SKIP;; swVar ::= 5).  auto.  auto.
              eapply E_Seq.  apply E_Skip.  apply E_Ass.  auto.  simpl.

              eapply E_WhileFalse.  auto. }

              (* Now finish off the original program *)
              rewrite <- sameState.   apply E_Ass.  auto.

          (* II.ii Case 2: X =/= 0 *)
              
          + eapply E_Seq.  apply E_IfFalse.  auto.  apply E_Ass.  auto.  simpl.
            assert (sameState : st & {swVar --> 0 ; X --> 1 ; swVar --> 5} = st').
            { apply ceval_deterministic with theDict ((swVar ::= 0;;
              WHILE swVar <= 4
              DO SWITCH swVar
                [(0, SKIP;; swVar ::= 1); 
                  (1, IFB X = 0 THEN swVar ::= 2 ELSE swVar ::= 3 FI); 
                  (2, SKIP;; swVar ::= 4); 
                  (3, X ::= 1;; swVar ::= 4);
                  (4, SKIP;; swVar ::= 5)] END)) st.
              2: auto.
              assert (sameState : st & {swVar --> 0; X --> 1 ; swVar --> 5} = st & {swVar --> 0 ; swVar --> 1 ; swVar --> 3 ; X --> 1 ; swVar --> 4 ; swVar --> 5}).
              { repeat (rewrite t_update_shadow).  rewrite t_update_comm.  rewrite t_update_shadow.  symmetry.  rewrite t_update_comm.
                rewrite t_update_shadow.  auto.  intro H0; inversion H0.  intro H0; inversion H0. }
              rewrite sameState.

              apply E_Seq with (st & {swVar --> 0}).  apply E_Ass.  auto.

              (* While Loop *)
              eapply E_WhileTrue.  auto.  apply E_Switch with 0 (SKIP;; swVar ::= 1).  auto.  auto.
              eapply E_Seq.  apply E_Skip.  apply E_Ass.  auto.  simpl.

              eapply E_WhileTrue.  auto.  apply E_Switch with 1 (IFB X = 0 THEN swVar ::= 2 ELSE swVar ::= 3 FI).  auto.  auto.
              apply E_IfFalse.  auto.  apply E_Ass.  auto.  simpl.

              eapply E_WhileTrue.  auto.  apply E_Switch with 3 (X ::= 1 ;; swVar ::= 4).  auto.  auto.
              eapply E_Seq.  apply E_Ass.  auto.  apply E_Ass.  auto.  simpl.

              eapply E_WhileTrue.  auto.  apply E_Switch with 4 (SKIP;; swVar ::= 5).  auto.  auto.
              eapply E_Seq.  apply E_Skip.  apply E_Ass.  auto.  simpl.

              eapply E_WhileFalse.  auto. }

              (* Now finish off the original program *)
              rewrite <- sameState.  eapply E_Seq.  apply E_Skip.  apply E_Ass.  auto.
  Qed.
*)
         
(* Generalize to the arbitrary case.  

   We need to know that c1 and c2 don't use the switchVar in any way.  Actually expressing this is
   very messy, so let's come up with something else that encompasses the right idea - the notion of evaluation of a program being invariant
   from the state of a particular variable.  In other words, if the only thing about the state that changes is the value of some particular
   variable X, this has no impact on the rest of the state when evaluating this program.

   We also have to this invariance for the boolean guard condition - IE, the IF statement's evaluation also doesn't depend on swVar.

   One more necessary assumption: since our LoadDict doesn't look inside if and while branches, the transformed program will always have an
   empty lc.  So assume the header and footer don't have any addresses or GoTos either so that loadDict of the original program is also empty lc.

   This isn't desirable in the long run since we'll want to be able to combine transformations, but for now we're black boxing this If-flattening
   transformation, which doesn't deal with GoTo and Jumps at all.
*)

Definition noGoTo c := loadDict c = empty_lc.

Definition eval_invariant (l : lc) c X :=
  forall l n st st', l && c / st \\ st' <-> l && c / st & { X --> n } \\ st' & { X --> n }.

Definition beval_invariant b X :=
  forall n st, beval st b = beval (st & { X --> n }) b. 

(* Lemma: evaluation invariance implies evaluation independence *)

Lemma eval_inv_imp_eval_ind : forall  lc c X n st st', 
  eval_invariant lc c X ->
  lc && c / st & { X --> n } \\ st' -> 
  lc && c / st \\ st'.
  Proof.
    intros.
      assert (lc && c / (st & {X --> n}) & {X --> n} \\ st' & {X --> n}).
      apply H.  apply H0.  rewrite t_update_shadow in H1.  unfold eval_invariant in H.
      unfold ceval_autoload in H1.  rewrite <- H in H1.  auto.
  Qed. 

(* Something broke: fix it.

Theorem AllTransEquiv : forall header cond c1 c2 footer, 
  eval_invariant empty_lc c1 swVar -> eval_invariant empty_lc c2 swVar -> 
  eval_invariant empty_lc footer swVar -> beval_invariant cond swVar ->
  noGoTo (original_program header cond c1 c2 footer) ->
  noGoTo (transform_program header cond c1 c2 footer) ->
  cequiv' (original_program header cond c1 c2 footer) (transform_program header cond c1 c2 footer).
  Proof.
    unfold cequiv'.  intros header cond c1 c2 footer HI1 HI2 HIf HB HGT HGT2 st st'.  
    unfold noGoTo in HGT.  unfold original_program in HGT.  split.

      (* (I) Original -> Transformed. *)
      - unfold original_program, transform_program.  intro H.

      (* Break apart sequencing in hypothesis. *)
      inversion H; subst.  inversion H6; subst.  inversion H8; subst.  inversion H10; subst. 

      (* Assert initial and final values of swVar *)
      assert (A0 : aeval st'0 swVar = 0).  inversion H3.  subst.  auto.
      assert (A5 : aeval st' swVar = 5).  inversion H12.  subst.  auto.
      rewrite HGT in *.

      (* Law of excluded middle: cond is true or false at point of branching statement *)
      destruct (beval st'1 cond) eqn:LEM.

        (* I.i Case 1: cond is true *)
        + unfold ceval_autoload.  eapply E_Seq.  simpl.  apply H3.  eapply E_WhileTrue.
            * unfold beval.  rewrite A0.  auto.
            * eapply E_Switch.  auto.  rewrite A0.  simpl.  auto.  eapply E_Seq.  simpl.  apply H4.  apply E_Ass.  auto.
            * simpl.  eapply E_WhileTrue.
              -- unfold beval.  simpl.  auto.
              -- eapply E_Switch.  auto.  simpl.  auto.  apply E_IfTrue.  rewrite <- HB.  assumption.  apply E_Ass.  auto.
              -- eapply E_WhileTrue.
                 ++ auto.
                 ++ eapply E_Switch.  auto.  simpl.  auto.  apply E_Seq with (st'2 & { swVar --> 2 }).  simpl.
                    inversion H5.  rewrite t_update_shadow.  unfold eval_invariant in HI1.  rewrite <- HI1.
                    assumption.  rewrite H14 in LEM.  inversion LEM.  apply E_Ass.  auto.
                 ++ simpl.  eapply E_WhileTrue.
                    ** auto.
                    ** eapply E_Switch.  auto.  simpl.  auto.  apply E_Seq with (st'3 & { swVar --> 4 }).  rewrite t_update_shadow.  
                       unfold eval_invariant in HIf.  rewrite <- HIf.  assumption.  apply E_Ass.  auto.
                    ** simpl.  rewrite t_update_shadow.
                       assert (sameState : st'3 & {swVar --> 5} = st').
                       { apply ceval_deterministic with empty_lc ((IFB cond THEN c1 ELSE c2 FI);; footer;; swVar ::= 5) st'1.  
                             2: auto.  eapply E_Seq.  apply E_IfTrue.  auto.  simpl.
                                inversion H5.  apply H15.  rewrite H14 in LEM.  inversion LEM.  eapply E_Seq.  apply H7.  apply E_Ass.  auto. } 
                       rewrite sameState.  eapply E_WhileFalse.
                       --- unfold beval.  rewrite A5.  auto.

      
         (* I.ii Case 2: X =/= 0 *)
         + unfold ceval_autoload.  eapply E_Seq.  apply H3.  eapply E_WhileTrue.
            * unfold beval.  rewrite A0.  auto.
            * eapply E_Switch.  auto.  rewrite A0.  simpl.  auto.  eapply E_Seq.  simpl.  apply H4.  apply E_Ass.  auto.
            * simpl.  eapply E_WhileTrue.
              -- unfold beval.  simpl.  auto.
              -- eapply E_Switch.  auto.  simpl.  auto.  apply E_IfFalse.  rewrite <- HB.  assumption.  apply E_Ass.  auto.
              -- eapply E_WhileTrue.
                 ++ auto.
                 ++ eapply E_Switch.  auto.  simpl.  auto.  apply E_Seq with (st'2 & { swVar --> 3 } ).
                    inversion H5.  rewrite H14 in LEM.  inversion LEM.
                    simpl.  rewrite t_update_shadow.  unfold eval_invariant in HI2.  rewrite <- HI2.  auto.  apply E_Ass.  auto.   
                 ++ simpl.  eapply E_WhileTrue.
                    ** auto.
                    ** eapply E_Switch.  auto.  simpl.  auto.  apply E_Seq with (st'3 & {swVar --> 4 }).  rewrite t_update_shadow.
                       unfold eval_invariant in HIf.  rewrite <- HIf.  assumption.  apply E_Ass.  auto.
                    ** simpl.  rewrite t_update_shadow.
                       assert (sameState : st'3 & {swVar --> 5} = st').
                       { apply ceval_deterministic with empty_lc ((IFB cond THEN c1 ELSE c2 FI);; footer;; swVar ::= 5) st'1.  
                             2: auto.  eapply E_Seq.  apply E_IfFalse.  auto.  simpl.
                             inversion H5.  rewrite H14 in LEM.  inversion LEM.  apply H15.  eapply E_Seq.  apply H7.  apply E_Ass.  auto. } 
                       rewrite sameState.  eapply E_WhileFalse.
                       --- unfold beval.  rewrite A5.  auto.

       (* (II) Transformed -> Original. *) 
      - unfold transform_program, original_program.  intro H.
        apply E_Seq with (st & {swVar --> 0}).  apply E_Ass.  auto.
        unfold noGoTo in HGT2.  unfold transform_program in HGT2.  rewrite HGT.  unfold ceval_autoload in H.  rewrite HGT2 in H.

        (* Header isn't just SKIP anymore, so we have some work to do... *)

        inversion H.  subst.

        assert (sameState : st & {swVar --> 0} = st'0).
        { apply ceval_deterministic with empty_lc (swVar ::= 0) st.  apply E_Ass.  auto.  auto. }
        subst.

        inversion H6.  subst.  simpl in H7.  inversion H7.  subst.  inversion H5.  subst.  simpl in H8.
        inversion H8.  rewrite <- H1 in H12.  inversion H12.  subst.
        
        eapply E_Seq.  apply H10.

        assert (sameState : st'1 & {swVar --> 1} = st'0).
        { apply ceval_deterministic with empty_lc (swVar ::= 1) st'1.  apply E_Ass.  auto.  auto. }
        subst.

        (* Invoke LEM at this point *)
        destruct (beval st'1 cond) eqn:LEM.

          (* II.i Case 1: cond is true *)

            (* Fetch effects of c1 out of hypothesis... break down hypotheses to go through two iterations of while-switch. *)
            inversion H9.  inversion H13.  subst.  inversion H11.  subst.  simpl in H15.  inversion H15.  subst.
            inversion H19.  subst.  2: { rewrite <- HB in H20.  rewrite H20 in LEM.  inversion LEM. }

            assert (sameState : st'0 = st'1 & { swVar --> 1 ; swVar --> 2 }).
            { apply ceval_deterministic with empty_lc (swVar ::= 2) (st'1 & {swVar --> 1}).
              auto.  apply E_Ass.  auto. }

            subst.  inversion H16.  subst.  inversion H18.  subst.  inversion H17.  subst.  simpl in H22.  subst.
            inversion H22.  subst.  inversion H26.  subst.  rewrite t_update_shadow in H18.

            assert (empty_lc && c1 / st'1 \\ st'2).
            { apply eval_inv_imp_eval_ind with swVar 2.  auto.  auto. }

            + eapply E_Seq.  apply E_IfTrue.  auto.  apply H0.

            (* Footer and close it off *)
 
             assert (sameState : st'0 = st'2 & { swVar --> 4 }).
             { apply ceval_deterministic with empty_lc (swVar ::= 4) st'2.  auto.  apply E_Ass.  auto. }
             subst.  inversion H23.  subst.  inversion H29.  inversion H28.  subst.  simpl in H36.  inversion H36.  subst.
             inversion H39.  subst.
 
             assert (empty_lc && footer / st'2 \\ st'3).
             { apply eval_inv_imp_eval_ind with swVar 4.  auto.  auto. }
             subst.
 
             inversion H31.  subst.
             assert (empty_lc && footer / st'2 \\ st'3).
             { apply eval_inv_imp_eval_ind with swVar 4.  auto.  auto. }
             
             eapply E_Seq.  apply H1.  apply H33.
 
             (* Impossible case of while loop true *)
 
             subst.  assert (sameState : st'0 = st'3 & { swVar --> 5 } ).
             { apply ceval_deterministic with empty_lc (swVar ::= 5) st'3.
               auto.  apply E_Ass.  auto. }
             subst.  inversion H30.
 
           (* II.ii Case 2: cond is false *)
               
             (* Fetch effects of c2 out of hypothesis... break down hypotheses to go through two iterations of while-switch. *)
             + inversion H9.  inversion H13.  subst.  inversion H11.  subst.  simpl in H15.  inversion H15.  subst.
             inversion H19.  subst.  rewrite <- HB in H20.  rewrite H20 in LEM.  inversion LEM.
 
             assert (sameState : st'0 = st'1 & { swVar --> 1 ; swVar --> 3 }).
             { apply ceval_deterministic with empty_lc (swVar ::= 3) (st'1 & {swVar --> 1}).
               auto.  apply E_Ass.  auto. }
 
             subst.  inversion H16.  subst.  inversion H18.  subst.  inversion H17.  subst.  simpl in H22.  subst.
             inversion H22.  subst.  inversion H26.  subst.  rewrite t_update_shadow in H18.
 
             assert (empty_lc && c2 / st'1 \\ st'2).
             { apply eval_inv_imp_eval_ind with swVar 3.  auto.  auto. }
 
             eapply E_Seq.  apply E_IfFalse.  auto.  apply H0.
 
             (* Footer and close it off *)
 
             assert (sameState : st'0 = st'2 & { swVar --> 4 }).
             { apply ceval_deterministic with empty_lc (swVar ::= 4) st'2.  auto.  apply E_Ass.  auto. }
             subst.  inversion H23.  subst.  inversion H29.  inversion H28.  subst.  simpl in H36.  inversion H36.  subst.
             inversion H39.  subst.
 
             assert (empty_lc && footer / st'2 \\ st'3).
             { apply eval_inv_imp_eval_ind with swVar 4.  auto.  auto. }
             subst.
 
             inversion H31.  subst.
             assert (empty_lc && footer / st'2 \\ st'3).
             { apply eval_inv_imp_eval_ind with swVar 4.  auto.  auto. }
             
             eapply E_Seq.  apply H1.  apply H33.
 
             (* Impossible case of while loop true *)
 
             subst.  assert (sameState : st'0 = st'3 & { swVar --> 5 } ).
             { apply ceval_deterministic with empty_lc (swVar ::= 5) st'3.
               auto.  apply E_Ass.  auto. }
             subst.  inversion H30.
  Qed.

*)