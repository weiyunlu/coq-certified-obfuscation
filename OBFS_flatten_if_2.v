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
Require Import SimpleObfuscator.

Ltac hoareImplies :=
  unfold assert_implies; intros; unfold assn_sub; simpl; auto.

Ltac bassnEval :=
  unfold bassn; unfold beval; unfold aeval. 

Ltac bassnEvalh H :=
  unfold bassn in H; unfold beval in H; unfold aeval in H.

(* ----------------------------------------------------------------------------------------------------------------- *)

Section HelperFunctions.

(* These helper functions do the following, respectively:
   - Check if a program has an if statement.
   - Return the first if block of a program (default to SKIP if it doesn't exist).
   - Return the boolean condition of an if statement (default to BFalse if any other program is passed).
   - Return the if branch of an if block (default to SKIP if any other kind of program is passed).
   - Return the else branch of an if block (default to SKIP if any other kind of program is passed).
   - Get everything before the first If block, if it exists; else return nothing.
   - Get everything after the first If block, if it exists; else return nothing.                          *)


Fixpoint ExistsIf (program : com) : bool :=
  match program with
  | IFB _ THEN _ ELSE _ FI       => true
  | IFB _ THEN _ ELSE _ FI ;; c2 => true
  | SKIP ;; c2                   => ExistsIf c2
  | _ ::= _ ;; c2                => ExistsIf c2
  | WHILE _ DO _ END ;; c2       => ExistsIf c2
  | (c1 ;; c2) ;; c3             => ExistsIf c1 || ExistsIf c2 || ExistsIf c3
  | SKIP                         => false
  | _ ::= _                      => false
  | WHILE _ DO _ END             => false
  end.

Fixpoint GetFirstIf (program : com) : com :=
  match program with
  | IFB _ THEN _ ELSE _ FI       => program
  | IFB a THEN b ELSE c FI ;; c2 => IFB a THEN b ELSE c FI
  | SKIP ;; c2                   => GetFirstIf c2
  | _ ::= _ ;; c2                => GetFirstIf c2
  | WHILE _ DO _ END ;; c2       => GetFirstIf c2
  | (c1 ;; c2) ;; c3             => if (ExistsIf c1) then GetFirstIf c1 else
                                      (if (ExistsIf c2) then GetFirstIf c2 else
                                        GetFirstIf c3)
  | SKIP                         => SKIP
  | _ ::= _                      => SKIP
  | WHILE _ DO _ END             => SKIP
  end.

Fixpoint GetBranchCondition (program : com) : bexp :=
  match program with
  | IFB a THEN b ELSE c FI    => a
  | SKIP                      => BFalse
  | _ ::= _                   => BFalse
  | WHILE _ DO _ END          => BFalse
  | c1 ;; c2                  => BFalse
  end.

Fixpoint GetIfBranch (program : com) : com :=
  match program with
  | IFB a THEN b ELSE c FI => b
  | SKIP                      => SKIP
  | _ ::= _                   => SKIP
  | WHILE _ DO _ END          => SKIP
  | c1 ;; c2                  => SKIP
  end.

Fixpoint GetElseBranch (program : com) : com :=
  match program with
  | IFB a THEN b ELSE c FI => c
  | SKIP                      => SKIP
  | _ ::= _                   => SKIP
  | WHILE _ DO _ END          => SKIP
  | c1 ;; c2                  => SKIP
  end.

Fixpoint GetHeader (program : com) : com :=
  match program with
  | SKIP ;; c2                   => SKIP ;; GetHeader c2
  | a ::= b ;; c2                => a ::= b ;; GetHeader c2
  | WHILE a DO b END ;; c2       => WHILE a DO b END ;; GetHeader c2
  | IFB a THEN b ELSE c FI ;; c2 => SKIP
  | SKIP                         => SKIP
  | _ ::= _                      => SKIP
  | WHILE _ DO _ END             => SKIP
  | IFB _ THEN _ ELSE _ FI       => SKIP
  | (c1 ;; c2) ;; c3             => if ExistsIf c1 then GetHeader c1 else
                                      if ExistsIf c2 then c1 ;; GetHeader c2 else
                                          c1 ;; c2 ;; GetHeader c3 
  end.

Fixpoint GetFooter (program : com) : com :=
  match program with
  | IFB a THEN b ELSE c FI ;; c2 => c2
  | SKIP ;; c2                   => GetFooter c2
  | a ::= b ;; c2                => GetFooter c2
  | WHILE a DO b END ;; c2       => GetFooter c2
  | SKIP                         => SKIP
  | _ ::= _                      => SKIP
  | WHILE _ DO _ END             => SKIP
  | IFB _ THEN _ ELSE _ FI       => SKIP
  | (c1 ;; c2) ;; c3             => if ExistsIf c1 then GetFooter c1 ;; c2 ;; c3 else
                                       if ExistsIf c2 then GetFooter c2 ;; c3 else
                                          GetFooter c3
  end.

End HelperFunctions.

(* ----------------------------------------------------------------------------------------------------------------- *)

Section DemoHelper.

(* The dramatically named WorldEater function maps 0 to 0 and maps all other numbers to 1.
   I.e. let's do something simpler than factorial to start. *)

Definition WorldEater : com :=
  IFB (X = 0) THEN
    SKIP
  ELSE
    X ::= 1
  FI.

Compute ExistsIf WorldEater.
Compute GetFirstIf WorldEater.
Compute GetBranchCondition (GetFirstIf WorldEater).
Compute GetIfBranch (GetFirstIf WorldEater).
Compute GetElseBranch (GetFirstIf WorldEater).
Compute GetHeader WorldEater.
Compute GetFooter WorldEater.

(* Some non-use cases where the helpers spit out a meaningless default value. *)

Compute ExistsIf SKIP.
Compute GetFirstIf (X ::= 0).
Compute GetBranchCondition SKIP.
Compute GetIfBranch (X ::= 0).
Compute GetElseBranch (X ::= 0).
Compute GetHeader (X ::= 0).
Compute GetFooter (X ::= 0).

End DemoHelper.

(* ----------------------------------------------------------------------------------------------------------------- *)

Section TransformationCFG.

(* Control flow flattening on the first if block of a program.  If there is none, then do nothing. *)
(* We mimic switching behaviour with nested ifs. *)

Definition BREAK : string := "BREAK".
Definition SWITCH : string := "SWITCH".

Definition TransformationCFG (program : com) :=
  match (ExistsIf program) with
  | false =>  program
  | true  =>  let ifBlock := GetFirstIf program in
                let ifBranch := GetIfBranch ifBlock in
                let elseBranch := GetElseBranch ifBlock in
                let branchCondition := GetBranchCondition ifBlock in
              let header := GetHeader program in
              let footer := GetFooter program in
                  BREAK ::= 0 ;;
                  SWITCH ::= 0 ;;
                  WHILE (BREAK = 0) DO
                    IFB (SWITCH = 0) THEN
                      header ;;
                      SWITCH ::= 1
                    ELSE
                      IFB (SWITCH = 1) THEN
                        IFB (branchCondition) THEN
                          SWITCH ::= 2
                        ELSE
                          SWITCH ::= 3
                        FI
                      ELSE
                        IFB (SWITCH = 2) THEN
                          ifBranch ;;
                          SWITCH ::= 4
                        ELSE
                          IFB (SWITCH = 3) THEN
                            elseBranch ;;
                            SWITCH ::= 4
                          ELSE
                            IFB (SWITCH = 4) THEN
                              footer ;;
                              BREAK ::= 1
                            ELSE
                              SKIP
                            FI
                          FI
                        FI
                      FI
                    FI
                  END
  end.

Definition TransWorldEater := TransformationCFG WorldEater.

Compute TransWorldEater.

End TransformationCFG.

(* ----------------------------------------------------------------------------------------------------------------- *)

Section HoareEquivalenceCFG_EX1.

(* We show Hoare equivalence, of the CFG transformation on the dummy program *)

(* Input 0 => output 0 *)

Example WorldEater_hoare_zero:
  {{ as_x 0 }} WorldEater {{ as_x 0 }}.
  Proof.
    unfold as_x, WorldEater.
    apply hoare_if.
    - eapply hoare_consequence_pre.  apply hoare_skip.  unfold assert_implies.  
      intros.  destruct H; auto.
    - apply hoare_consequence_pre with ((fun st : state => st X = 0) [X |-> 1]).
      + apply hoare_asgn.
      + unfold assert_implies.  intros.  destruct H.  unfold bassn in H0.  unfold beval in H0.
        unfold aeval in H0.  rewrite beq_nat_true_iff in H0.  apply H0 in H.  inversion H.
  Qed.

Lemma WorldEaterHasIf : ExistsIf WorldEater = true.
  Proof.
    auto.
  Qed.

Example TransWorldEater_hoare_zero:
  {{ as_x 0 }} TransWorldEater {{ as_x 0 }}.
  Proof.
    unfold as_x, TransWorldEater.  unfold TransformationCFG.  rewrite WorldEaterHasIf.

    (* Initialization of break and switch variables.  *)
    eapply hoare_seq.
    2: apply hoare_consequence_pre with ((fun st : state => st X = 0 /\ st BREAK = 0) [BREAK |-> 0]).
    2: apply hoare_asgn.
    2: { unfold assert_implies.  intros.  unfold assn_sub.  auto. }
    eapply hoare_seq.
    2: apply hoare_consequence_pre with ((fun st : state => st X = 0 /\ st BREAK = 0 /\ st SWITCH = 0)
       [SWITCH |-> 0]).
    2: apply hoare_asgn.
    2: { unfold assert_implies.  intros.  unfold assn_sub.  destruct H.  auto. }

    (* Loop invariant is X = 0 and SWITCH != 3 (only if branch of original program is executed). *)
    unfold GetHeader, GetBranchCondition, GetIfBranch, GetElseBranch, GetFooter, GetFirstIf, WorldEater.
    simpl.  apply hoare_consequence_post with (fun st : state => (st X = 0 /\ ~ (st SWITCH = 3)) /\
       ~ bassn (BREAK = 0) st).
    2: { unfold assert_implies.  intros.  destruct H; auto.  destruct H.  auto. }
    apply hoare_consequence_pre with (fun st : state => st X = 0 /\ ~ (st SWITCH = 3)).
    2: { unfold assert_implies.  intros.  destruct H; auto.  destruct H0.  split.  auto.
         rewrite <- beq_nat_false_iff.  rewrite H1.  auto. }
    apply hoare_while.

    (* Into the while loop proper: nested if statements simulate switch behaviour. *)

    (* First layer: header. *)
    apply hoare_if.  eapply hoare_seq.  apply hoare_asgn.
    eapply hoare_consequence_pre.
      apply hoare_skip.
    unfold assert_implies.  intros.  unfold assn_sub.  simpl.  destruct H.  destruct H.  destruct H.  split.
      unfold t_update.  simpl.  auto.
      unfold t_update.  simpl.  auto.

    (* Second layer: conditional of original program. *)
    apply hoare_if.  apply hoare_if.
    eapply hoare_consequence_pre.
      apply hoare_asgn.
      unfold assert_implies.  intros.  unfold assn_sub.  simpl.  unfold t_update.  simpl.  
      destruct H.  destruct H.  destruct H.  destruct H.  destruct H.  split.  auto.  auto.
    eapply hoare_consequence_pre.
      apply hoare_asgn.
      unfold assert_implies.  intros.  destruct H.  destruct H.  destruct H.  destruct H.  destruct H.
      unfold bassn in H0.  unfold beval in H0.  unfold aeval in H0.  rewrite beq_nat_true_iff in H0.
      rewrite H in H0.  contradiction H0.  auto.

    (* Third layer: proceed to if branch of original program. *)
    apply hoare_if.  eapply hoare_seq.  apply hoare_asgn.
    eapply hoare_consequence_pre.  apply hoare_skip.
    unfold assert_implies.  intros.  destruct H.  destruct H.  destruct H.  destruct H.  destruct H.
    unfold assn_sub.  unfold aeval.  unfold t_update.  simpl.  split.  auto.  auto.
  
    (* Fourth layer: (don't) proceed to else branch of original program. *)
    apply hoare_if.  eapply hoare_seq.  apply hoare_asgn.
    eapply hoare_consequence_pre.  apply hoare_asgn.
    unfold assert_implies.  intros.
    destruct H.  destruct H.  destruct H.  destruct H.  destruct H.  destruct H.
    unfold bassn in H0.  unfold beval in H0.  unfold aeval in H0.  rewrite beq_nat_true_iff in H0.
    rewrite H0 in H5.  contradiction H5.  auto.

    (* Fifth layer: footer. *)
    apply hoare_if.  eapply hoare_seq.  apply hoare_asgn.
    eapply hoare_consequence_pre.  apply hoare_skip.
    unfold assert_implies.  intros.  unfold assn_sub.  unfold t_update.  simpl.
    destruct H.  destruct H.  destruct H.  destruct H.  destruct H.  destruct H.  destruct H.
    split.  auto.  auto.

    eapply hoare_consequence_pre.  apply hoare_skip.
    unfold assert_implies.  intros.  
    destruct H.  destruct H.  destruct H.  destruct H.  destruct H.  destruct H.  destruct H.
    split.  auto.  auto.
  Qed.

(* Input nonzero => output 1 *)


Example WorldEater_hoare_nonzero: forall n : nat, n <> 0 ->
  {{ as_x n }} WorldEater {{ as_x 1 }}.
  Proof.
    intros.  unfold as_x, WorldEater.
    apply hoare_if.
    - eapply hoare_consequence_pre.  apply hoare_skip.  unfold assert_implies.  
      intros.  destruct H0.  unfold bassn in H1.  unfold beval in H1.  unfold aeval in H1.
      rewrite H0 in H1.  rewrite beq_nat_true_iff in H1.  rewrite <- H1 in H.  contradiction H.  auto.
    - eapply hoare_consequence_pre.
      + apply hoare_asgn.
      + unfold assert_implies.  intros.
        unfold assn_sub.  unfold t_update.  simpl.  auto.
  Qed.

Example TransWorldEater_hoare_nonzero: forall n : nat, n <> 0 ->
  {{ as_x n }} TransWorldEater {{ as_x 1 }}.
  Proof.
    intros.  unfold as_x, TransWorldEater.  unfold TransformationCFG.  rewrite WorldEaterHasIf.

    (* Initialization of break and switch variables.  *)
    eapply hoare_seq.
    2: apply hoare_consequence_pre with ((fun st : state => ~ (st X = 0) /\ st BREAK = 0) [BREAK |-> 0]).
    2: apply hoare_asgn.
    2: { unfold assert_implies.  intros.  unfold assn_sub.  unfold aeval.  unfold t_update.  simpl.
         split.  rewrite H0.  auto.  auto. }
    eapply hoare_seq.
    2: apply hoare_consequence_pre with ((fun st : state => ~ (st X = 0) /\ st BREAK = 0 /\ st SWITCH = 0)
       [SWITCH |-> 0]).
    2: apply hoare_asgn.
    2: { unfold assert_implies.  intros.  unfold assn_sub.  destruct H0.  auto. }

    (* Loop invariant is more complicated this time, since we enter with X != 0 and need to exit with X = 1.
       The invariant is (X != 0 /\ (SWITCH < 2 \/ SWITCH = 3) /\ BREAK = 0) \/ (X = 1 /\ SWITCH = 4), representing the state
       of X along with other necessary conditions before and after the reassignment takes place.             *)
    unfold GetHeader, GetBranchCondition, GetIfBranch, GetElseBranch, GetFooter, GetFirstIf, WorldEater.
    simpl.  apply hoare_consequence_post with 
      (fun st : state => ((( ~ (st X = 0) /\ ( st SWITCH < 2 \/ st SWITCH = 3) /\ st BREAK = 0) \/ 
        (st X = 1 /\ st SWITCH = 4)) /\ ~ bassn (BREAK = 0) st)).
    2: { unfold assert_implies.  intros.  destruct H0.  elim H0.
         - intros.  destruct H2.  destruct H3.  unfold bassn in H1.  unfold beval in H1.  unfold aeval in H1.
           rewrite beq_nat_true_iff in H1.  rewrite H4 in H1.  contradiction H1.  auto.
         - intros.  destruct H2.  auto. }
    apply hoare_consequence_pre with
      (fun st : state => ((( ~ (st X = 0) /\ ( st SWITCH < 2 \/ st SWITCH = 3) /\ st BREAK = 0) \/ 
        (st X = 1 /\ st SWITCH = 4)))).
    2: { unfold assert_implies.  intros.  destruct H0.  destruct H1.  left.
         split.  auto.  split.  rewrite H2.  auto.  auto. }

    apply hoare_while.

    (* Into the while loop proper: nested if statements simulate switch behaviour. *)

    (* First layer: header. *)
    apply hoare_if.  eapply hoare_seq.  apply hoare_asgn.
    eapply hoare_consequence_pre.
      apply hoare_skip.
    unfold assert_implies.  intros.  unfold assn_sub.  simpl.  destruct H0.  destruct H0.  elim H0.
      { intros.  unfold t_update.  simpl.  left.  destruct H3.  destruct H4.
        split.  auto.  split.  auto.  auto. }
      { intros.  destruct H3.  unfold bassn in H1.  unfold beval in H1.  unfold aeval in H1.
        rewrite beq_nat_true_iff in H1.  rewrite H1 in H4.  inversion H4. }

    (* Second layer: conditional of original program. *)
    apply hoare_if.  apply hoare_if.
    { eapply hoare_consequence_pre.
      apply hoare_asgn.
      unfold assert_implies.  intros.  unfold assn_sub.  simpl.  unfold t_update.  simpl.  left.  
      destruct H0.  destruct H0.  destruct H0.  destruct H0.  elim H0.
      { intros.  destruct H5.  destruct H6.  unfold bassn in H1.  unfold beval in H1.  unfold aeval in H1.
        rewrite beq_nat_true_iff in H1.  rewrite H1 in H5.  contradiction H5.  auto. }
      { intros.  destruct H5.  unfold bassn in H2.  unfold beval in H2.  unfold aeval in H2.
        rewrite beq_nat_true_iff in H2.  rewrite H2 in H6.  inversion H6. } 
    }
    { eapply hoare_consequence_pre.
      apply hoare_asgn.
      unfold assert_implies.  intros.  destruct H0.  destruct H0.  destruct H0.  destruct H0.  elim H0.
      { intros.  unfold assn_sub.  unfold t_update.  simpl.  left.  destruct H5.  destruct H6.
        auto. }
      { intros.  destruct H5.  unfold bassn in H2.  unfold beval in H2.  unfold aeval in H2.
        rewrite beq_nat_true_iff in H2.  rewrite H2 in H6.  inversion H6. }
    }

    (* Third layer: (don't) proceed to if branch of original program. *)
    apply hoare_if.  eapply hoare_seq.  apply hoare_asgn.
    eapply hoare_consequence_pre.  apply hoare_skip.
    unfold assert_implies.  intros.  destruct H0.  destruct H0.  destruct H0.  destruct H0.  elim H0.
    { intros.  destruct H5.  destruct H6.  elim H6.
      { intros.  unfold bassn in H1.  unfold beval in H1.  unfold aeval in H1.  rewrite beq_nat_true_iff in H1.
        rewrite H1 in H8.  inversion H8.  inversion H10.  inversion H12. }
      { intros.  unfold bassn in H1.  unfold beval in H1.  unfold aeval in H1.  rewrite beq_nat_true_iff in H1.
        rewrite H1 in H8.  inversion H8. }
    }
    { intros.  destruct H5.   unfold bassn in H1.  unfold beval in H1.  unfold aeval in H1.  
      rewrite beq_nat_true_iff in H1.  rewrite H1 in H6.  inversion H6. }
  
    (* Fourth layer: proceed to else branch of original program. *)
    apply hoare_if.  eapply hoare_seq.  apply hoare_asgn.
    eapply hoare_consequence_pre.  apply hoare_asgn.
    unfold assert_implies.  intros.
    destruct H0.  destruct H0.  destruct H0.  destruct H0.  destruct H0.  elim H0.
    { intros.  destruct H6.  destruct H7.  unfold assn_sub.  unfold t_update.  simpl.
      right.  auto. }
    { intros.  destruct H6.   unfold bassn in H1.  unfold beval in H1.  unfold aeval in H1.  
      rewrite beq_nat_true_iff in H1.  rewrite H1 in H7.  inversion H7. }

    (* Fifth layer: footer. *)
    apply hoare_if.  eapply hoare_seq.  apply hoare_asgn.
    eapply hoare_consequence_pre.  apply hoare_skip.
    unfold assert_implies.  intros.  unfold assn_sub.  unfold t_update.  simpl.
    destruct H0.  destruct H0.  destruct H0.  destruct H0.  destruct H0.  destruct H0.  elim H0.
    { intros.  destruct H7.  destruct H8.  elim H8.
      { intros.  unfold bassn in H1.  unfold beval in H1.  unfold aeval in H1.  
        rewrite beq_nat_true_iff in H1.  rewrite H1 in H10.  inversion H10.  inversion H12.  inversion H14. }
      { intros.  unfold bassn in H1.  unfold beval in H1.  unfold aeval in H1.  
        rewrite beq_nat_true_iff in H1.  rewrite H1 in H10.  inversion H10. }
    }
    { intros.  right.  auto. }

    eapply hoare_consequence_pre.  apply hoare_skip.
    unfold assert_implies.  intros.  
    destruct H0.  destruct H0.  destruct H0.  destruct H0.  destruct H0.  destruct H0.  elim H0.
    { intros.  unfold bassn in *.  unfold beval in *.  unfold aeval in *.  rewrite beq_nat_true_iff in *.
      destruct H7.  destruct H8.  elim H8.
      { intros.  inversion H10.  rewrite H12 in H4.  contradiction H4.  auto.  inversion H12.
        rewrite H14 in H5.  contradiction H5.  auto.  inversion H14. }
      { intros.  rewrite H10 in H2.  contradiction H2.  auto. }
    }
    { intros.  unfold bassn in *.  unfold beval in *.  unfold aeval in *.  rewrite beq_nat_true_iff in *.
      destruct H7.  rewrite H8 in H1.  contradiction H1.  auto. }  
  Qed.

End HoareEquivalenceCFG_EX1.

(* ----------------------------------------------------------------------------------------------------------------- *)

Section HoareEquivalenceCFG_EX2.

(* Apply opaque_trans to the factorial program from the previous section (the version with assignments, so we have a
   nontrivial header in this example).  Then hit it with CFG flattening.  It's still factorial. *)

Example factorial_all_hoare_opaque_CFG : forall x xo c2,
  {{ as_x xo }} TransformationCFG (opaque_trans' x fact_program c2) {{ as_y (fact xo) }}.
  Proof.
    intros.  unfold TransformationCFG, opaque_trans', fact_program, as_x.  simpl.

    eapply hoare_seq.
    2: apply hoare_consequence_pre with ((fun st : state => st X = xo /\ st BREAK = 0) [BREAK |-> 0]).
    2: apply hoare_asgn.  2: hoareImplies.

    eapply hoare_seq.
    2: apply hoare_consequence_pre with ((fun st : state => st X = xo /\ st BREAK = 0 /\ st SWITCH = 0)
       [SWITCH |-> 0]).  2: apply hoare_asgn.  2: { hoareImplies.  destruct H.  auto. }

    (* Outer loop invariant; massage pre and post condition to match while loop rule *)
    apply hoare_consequence_post with 
      (fun st : state => ((st X = xo /\ ((st SWITCH = 0 /\ st BREAK = 0) \/ ( (st SWITCH = 1 \/ st SWITCH = 2) /\ st X' = x /\
         st Z' = st X' * st X' + st X' + st X' + 1 /\ st Z'' = (st X' + 1) * (st X' + 1) /\ 
         st BREAK = 0) \/ (st SWITCH = 4 /\ st Y = fact xo))) /\ ~ bassn (BREAK = 0) st)).

    2: { bassnEval.  hoareImplies.  destruct H.  rewrite beq_nat_true_iff in H0.  destruct H.  elim H1.
         - intros.  destruct H2.  rewrite H3 in H0.  contradiction H0.  auto.
         - intros.  elim H2.
           + intros.  destruct H3.  destruct H4.  destruct H5.  destruct H6.  rewrite H7 in H0.  
             contradiction H0.  auto.
           + intros.  destruct H3.  unfold as_y.  auto. }

    apply hoare_consequence_pre with
      (fun st : state => (st X = xo /\ ((st SWITCH = 0 /\ st BREAK = 0) \/ ((st SWITCH = 1 \/ st SWITCH = 2) /\ st X' = x /\
         st Z' = st X' * st X' + st X' + st X' + 1 /\ st Z'' = (st X' + 1) * (st X' + 1) /\ 
         st BREAK = 0) \/ (st SWITCH = 4 /\ st Y = fact xo)))).

    2: { hoareImplies.  destruct H.  destruct H0.  split.  auto.  left.  split.  rewrite H1.  auto.  auto. }

    (* Outer while loop proper *)
    apply hoare_while.

    (* First layer: header *)
    apply hoare_if.
    { eapply hoare_seq.  apply hoare_asgn.  eapply hoare_seq.  eapply hoare_seq.  eapply hoare_seq.
      apply hoare_skip.  apply hoare_asgn.  apply hoare_asgn.
      apply hoare_consequence_pre with 
      (((((fun st : state => st X = xo /\ (
        st SWITCH = 0 /\ st BREAK = 0 \/ (st SWITCH = 1 \/ st SWITCH = 2) /\
        st X' = x /\ st Z' = st X' * st X' + st X' + st X' + 1 /\ st Z'' = (st X' + 1) * (st X' + 1) /\ st BREAK = 0 \/
        st SWITCH = 4 /\ st Y = fact xo)) [SWITCH |-> 1]) [Z'' |-> (X' + 1) * (X' + 1)]) [Z' |-> X' * X' + X' + X' + 1])
        [X' |-> x]).  
        apply hoare_asgn.  hoareImplies.  unfold t_update.  simpl.  destruct H.  destruct H.  elim H.
        - intros.  split; auto.  right.  left.  split.  left; auto.  split.  auto.  split.  auto.  split.  auto.  
          destruct H3.  destruct H3.  auto.  bassnEvalh H1.  rewrite beq_nat_true_iff in H1.  auto.
    }

    (* Second layer: conditional of original program *)
    apply hoare_if.  apply hoare_if.
    { eapply hoare_consequence_pre.  apply hoare_asgn.  hoareImplies.  unfold t_update.  simpl.  split.
      destruct H.  destruct H.  destruct H.  destruct H.  destruct H.  auto.  destruct H.  destruct H.
      destruct H.  destruct H.  destruct H.  elim H4.
      - intros.  destruct H5.  bassnEvalh H1.  rewrite beq_nat_true_iff in H1.  rewrite H1 in H5.  inversion H5.
      - intros.  elim H5.
        + intros.  destruct H6.  auto.
        + intros.  bassnEvalh H1.  rewrite beq_nat_true_iff in H1.  destruct H6.  rewrite H1 in H6.  inversion H6.
    }
    { eapply hoare_consequence_pre.  apply hoare_asgn.  hoareImplies.  destruct H.  destruct H.  destruct H.
      destruct H.  destruct H.  bassnEvalh H0.  rewrite beq_nat_true_iff in H0.  contradiction H0.  elim H4.
      - intros.  bassnEvalh H1.  rewrite beq_nat_true_iff in H1.  destruct H4.  rewrite H1 in H4.  inversion H4.
        inversion H6.  destruct H5.  rewrite H1 in H5.  inversion H5.
      - intros.  elim H5.
        + intros.  destruct H6.  elim H6.
          * intros.  destruct H7.  destruct H9.  destruct H10.  rewrite H9; rewrite H10.  rewrite opaque_taut.  auto.
          * intros.  bassnEvalh H1.  rewrite beq_nat_true_iff in H1.  rewrite H1 in H8.  inversion H8.
        + intros.  destruct H6.  bassnEvalh H1.  rewrite beq_nat_true_iff in H1.  rewrite H1 in H6.  inversion H6.
    }

    (* Third layer: run original program *)
    apply hoare_if.
    { eapply hoare_seq.  apply hoare_asgn.  eapply hoare_seq.  eapply hoare_seq.  
      apply hoare_consequence_post with
       (* Inner loop invariant, lifted from Hoare logic section *)
       (fun st : state => (fun st0 : state => st0 Y = fact (st0 Z) /\ st0 X = xo) st /\ ~ bassn (! (Z = X)) st).
       apply hoare_while.
      - eapply hoare_seq.  apply hoare_asgn.  eapply hoare_consequence_pre.  apply hoare_asgn. 
        hoareImplies.  unfold t_update.  simpl.  destruct H.  destruct H.  split.  2: auto.  rewrite H.
        rewrite fact_dist.  auto.
      - hoareImplies.  unfold t_update.  simpl.  destruct H.  destruct H.  split.  auto.  right.  right.  split.
        auto.  bassnEvalh H0.  rewrite negb_true_iff in H0.  rewrite not_false_iff_true in H0.
        rewrite beq_nat_true_iff in H0.  rewrite H.  rewrite H0.  rewrite H1.  auto.
      - apply hoare_asgn.
      - eapply hoare_consequence_pre.  apply hoare_asgn.  hoareImplies.  unfold t_update.  simpl.  split.  auto.
        destruct H.  destruct H.  destruct H.  destruct H.  destruct H.  auto.
    }

    (* Fourth layer: else branch never triggers *)
    apply hoare_if.
    { eapply hoare_seq.  apply hoare_asgn.  unfold hoare_triple.  intros.  destruct H0.  destruct H0.
      destruct H0.  destruct H0.  destruct H0.  destruct H0.  elim H6.
      - intros.  destruct H7.  bassnEvalh H1.  rewrite beq_nat_true_iff in H1.  rewrite H1 in H7.  inversion H7.
      - intros.  elim H7.
        + intros.  destruct H8.  elim H8.
          * intros.  bassnEvalh H1.  rewrite beq_nat_true_iff in H1.  rewrite H1 in H10.  inversion H10.
          * intros.  bassnEvalh H1.  rewrite beq_nat_true_iff in H1.  rewrite H1 in H10.  inversion H10.
        + intros.  destruct H8.  bassnEvalh H1.  rewrite beq_nat_true_iff in H1.  rewrite H1 in H8.  inversion H8.
    }

    (* Fifth later: (still empty) footer *)
    apply hoare_if.
    { eapply hoare_seq.  apply hoare_asgn.  eapply hoare_consequence_pre.  apply hoare_skip.  hoareImplies.
      unfold t_update.  simpl.  destruct H.  destruct H.  destruct H.  destruct H.  destruct H.  destruct H.
      destruct H.  elim H6.  bassnEvalh H0.  rewrite beq_nat_true_iff in H0.
      - intros.  destruct H7.  rewrite H0 in H7.  inversion H7.
      - intros.  elim H7.
        + intros.  destruct H8.  elim H8.
          * intros.  bassnEvalh H0.  rewrite beq_nat_true_iff in H0.  rewrite H0 in H10.  inversion H10.
          * intros.  bassnEvalh H0.  rewrite beq_nat_true_iff in H0.  rewrite H0 in H10.  inversion H10.
        + intros.  destruct H8.  split.  auto.  right.  right.  split.  auto.  auto.
    }

    eapply hoare_consequence_pre.  apply hoare_skip.  hoareImplies.  destruct H.  destruct H.  destruct H.
    destruct H.  destruct H.  destruct H.  destruct H.  split.  auto.  auto.
  Qed.

End HoareEquivalenceCFG_EX2.

(* ----------------------------------------------------------------------------------------------------------------- *)


Section GeneralCFG.

(* Prove a general pre- and post-condition preservance theorem of the same form as the example. *)

Definition Hoare_fidelity_xx c1 c2 := forall xo xi,
  hoare_triple (as_x xo) c1 (as_x xi) -> hoare_triple (as_x xo) c2 (as_x xi).

(*
Lemma reconstructPieces : forall c,
  (ExistsIf c) = true -> exists header condition ifbranch elsebranch footer,
  c = (header ;; IFB (condition) THEN ifbranch ELSE elsebranch FI ;; footer).
  Proof.
    intros.  
    exists (GetHeader c).  exists (GetBranchCondition c).  exists (GetIfBranch c).
    exists (GetElseBranch c).  exists (GetFooter c).
    unfold GetHeader.  simpl.
    Abort.
*)

Lemma pre_existsIf : forall a b, ExistsIf b = true -> ExistsIf (a ;; b) = true.
  Proof.
    intros.  unfold ExistsIf.  destruct a; auto.  rewrite orb_true_iff.  rewrite orb_true_iff.
    right.  auto.
  Qed.

Theorem CFGtrans_hoare_fidelity_xx : forall header cond c1 c2 footer, ExistsIf header = false ->
  Hoare_fidelity_xx (header ;; IFB (cond) THEN c1 ELSE c2 FI ;; footer) 
    (TransformationCFG (header ;; IFB (cond) THEN c1 ELSE c2 FI ;; footer)).
  Proof.
    unfold Hoare_fidelity_xx, TransformationCFG.  intros.
    assert (eIf : ExistsIf (IFB (cond) THEN c1 ELSE c2 FI ;; footer) = true).  auto.
    assert (eIf2 : ExistsIf (header ;; IFB (cond) THEN c1 ELSE c2 FI ;; footer) = true).
      apply pre_existsIf.  auto.  rewrite eIf2.  

    (* Unfolding... lots of cases *)

    unfold GetHeader.  destruct header eqn:headerForm. 
    (* Uh oh... combinatorial explosion if we keep going like this... *)
    - unfold ExistsIf in H.
    
    3: {  destruct c1.

    (* If the program didn't have an If statement, this is trivially true. *)
    case (ExistsIf c) eqn:HasIf.  2: auto.

    (* Condition on whether 

    (* If the program did have an If statement, we do induction, then most of the base cases contradict the
       assumption that an If statement exists. *)
    induction c; inversion HasIf.
    unfold GetHeader, GetBranchCondition, GetIfBranch, GetElseBranch, GetFooter, GetFirstIf.  
  

Theorem CFGtrans_hoare_fidelity_xy : forall c,
  Hoare_fidelity_xy c (TransformationCFG c).
Proof.
  Admitted.

Corollary CFGtrans_opaque_hoare_fidelity_xy : forall c1 c2 x,
  Hoare_fidelity_xy c1 (TransformationCFG (opaque_trans' x c1 c2)).
Proof.
  Admitted.

End GeneralCFG.
*)