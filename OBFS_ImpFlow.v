Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Import ListNotations.

Require Import SF_Maps.
Require Import SF_Imp.

Require Import OBFS_opaque_predicate.

(* ----------------------------------------------------------------------------------------------------------------- *)

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

Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k ; l --> m ; n --> o ; p --> q ; r --> s ; t2 --> t3 ; t4 --> t5 }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k ; l --> m ; n --> o ; p --> q ; r --> s ; t2 --> t3 }) t4 t5) (at level 0).

Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k ; l --> m ; n --> o ; p --> q ; r --> s ; t2 --> t3 ; t4 --> t5 ; t6 --> t7 }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k ; l --> m ; n --> o ; p --> q ; r --> s ; t2 --> t3 ; t4 --> t5}) t6 t7) (at level 0).

Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k ; l --> m ; n --> o ; p --> q ; r --> s ; t2 --> t3 ; t4 --> t5 ; t6 --> t7 ; t8 --> t9 }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> i ; j --> k ; l --> m ; n --> o ; p --> q ; r --> s ; t2 --> t3 ; t4 --> t5 ; t6 --> t7}) t8 t9) (at level 0).

(* ----------------------------------------------------------------------------------------------------------------- *)

(* A comBlock consists of a command together with an instruction of how to find the next block, via string/map pointers.

   It can Jump, by taking another string which will index into a blockDict and find the next block.

   It can Conditional (jump), by evaluating a bexp, and then it has an if string and an else string that index into a
   blockDict and find the next block.

   It can be a Switch, which takes a switching variable (a string) and a function nat->string which maps values of the
   switching variable to a pointer into comDict to find the next block.

   Finally, it can simply end.

   To write/evaluate an ImpFlow+ program, then, is to be given an initial comBlock together with a blockDict that contains
   the data of all other blocks necessary for the program.

   Note that this means you can't effectively do a goto from or into a branching statement or a while loop.  This is fine
   for our purposes, and may avoid some weird behaviour. *)

Inductive comBlock : Type :=
  | bJump : com -> string -> comBlock
  | bConditional : com -> bexp -> string -> string -> comBlock
  | bSwitch : com -> string -> (nat -> string) -> comBlock
  | bEnd : com -> comBlock.

Definition blockDict : Type := total_map comBlock.


(* To evaluate a single block, given a blockDict and comDict and initial state, is to find the final state after executing 
   the commands and then finding the (option, since we could terminate) next block to go to. *)


Inductive blockEval : comBlock -> blockDict -> state -> state -> option comBlock -> Prop :=
  | BE_Jump : forall c blockD st st' next nextBlock,
                ceval c st st' ->
                (blockD next) = nextBlock ->
                (blockEval (bJump c next) blockD st st' (Some nextBlock))
  | BE_CondTrue : forall c blockD st st' condition nextIf nextBlock nextElse,
                    ceval c st st' ->
                    (blockD nextIf = nextBlock) ->
                    (beval st' condition) = true ->
                    (blockEval (bConditional c condition nextIf nextElse) 
                     blockD st st' (Some nextBlock))
  | BE_CondFalse : forall c blockD st st' condition nextIf nextBlock nextElse,
                     ceval c st st' ->
                     (blockD nextElse = nextBlock) ->
                     (beval st' condition) = false ->
                     (blockEval (bConditional c condition nextIf nextElse) 
                      blockD st st' (Some nextBlock))
  | BE_Switch : forall c blockD st st' swVar swMap n nextPos nextBlock,
                  ceval c st st' ->
                  aeval st' (AId swVar) = n ->
                  swMap n = nextPos ->
                  blockD nextPos = nextBlock ->
                  (blockEval (bSwitch c swVar swMap) blockD st st' 
                   (Some nextBlock))
  | BE_End : forall c blockD st st',
               ceval c st st' ->
               (blockEval (bEnd c) blockD st st' None).

Notation "cmd '<<' blockD '/' st '\' stt '-->' nxt" :=
  (blockEval cmd blockD st stt nxt)
                  (at level 40, st at level 39).

(* Evaluating an entire program starts with the same data: an initial block that represents the start of the program, and
   the corresponding blockDict, except it will actually continue on to the next block until it hits an end
   block.  We have to inductively build this backwards: we need a rule for evaluating an end block, and then a rule for
   how to pre-pend a block to an existing chain. *)

Inductive progEval : comBlock -> blockDict -> state -> state -> Prop :=
  | PE_Terminal : forall c blockD st st',
                     (blockEval (bEnd c) blockD st st' None) ->
                     progEval (bEnd c) blockD st st'
  | PE_AddBlock : forall newBlock currentChain blockD st st' st'',
                     (progEval currentChain blockD st'' st') ->
                     (blockEval newBlock blockD st st'' (Some currentChain)) ->
                     (progEval newBlock blockD st st').

Notation "cmd '<<' blockD '/' st '\\\' stt" :=
  (progEval cmd blockD st stt)
                  (at level 40, st at level 39).

(* For usability, we can define a program to formally consist of a starting comBlock and a blockDict *)

Definition IFP : Type := comBlock * blockDict.

Definition IFPEval (program : IFP) st st' := progEval (fst program) (snd program) st st'.

Notation "prog '/' st '\\\' stt" :=
  (IFPEval prog st stt)
                  (at level 40, st at level 39).

(* ----------------------------------------------------------------------------------------------------------------- *)

Section CWExample.

(* On page 6 of Chenxi Wang, there are three versions of the same sample program.
    (i) High level constructs: we can do this with a single block.
    (ii) Dismantled high level constructs: blocks and flow but with the same logic of the original program.
    (iii) The flattened version of (ii). *)

Definition A : string := "A".
Definition B : string := "B".
Definition RETURN : string := "RETURN".
Definition SWITCH : string := "SWITCH".
Definition Blank : blockDict := { --> (bEnd SKIP) }.

(* (i) *)

Definition OriginalCommand : com :=
  WHILE (A <= 2) DO
    B ::= A + B ;;
    IFB (!(B <= 4)) THEN
      B ::= B - 1
    ELSE SKIP FI ;;
    A ::= A + 1
  END ;;
  RETURN ::= A * B.

Definition Main : comBlock :=
  bEnd OriginalCommand.

Definition OriginalDict : blockDict :=
  Blank & { "Main" --> Main }.

Definition OriginalProgram : IFP :=
  (Main, OriginalDict).

(* (ii) *)

Definition L1Com : com :=
  SKIP.

Definition L2Com : com :=
  A ::= A + 1.

Definition L3Com : com :=
  B ::= A + B.

Definition L4Com : com :=
  RETURN ::= A * B.

Definition L5Com : com :=
  B ::= B - 1.

Definition L1Blk : comBlock :=
  bConditional L1Com (!(A <= 2)) "L4" "L3".

Definition L2Blk : comBlock :=
  bJump L2Com "L1".

Definition L3Blk : comBlock :=
  bConditional L3Com (B <= 4) "L2" "L5".

Definition L4Blk : comBlock :=
  bEnd L4Com.

Definition L5Blk : comBlock :=
  bJump L5Com "L2".

Definition DismantledDict : blockDict :=
  Blank & { "L1" --> L1Blk ; "L2" --> L2Blk ; "L3" --> L3Blk ; "L4" --> L4Blk ; "L5" --> L5Blk }.

Definition DismantledProgram : IFP :=
  (L1Blk, DismantledDict).

(* (iii) *)

Definition InitCom : com :=
  SWITCH ::= 1.  

Definition SwitchCom : com :=
  SKIP.

Definition S1Com : com :=
  IFB (A <= 2) THEN
    SWITCH ::= 2
  ELSE
    SWITCH ::= 5
  FI.

Definition S2Com : com :=
  B ::= B + A ;;
  IFB (B <= 4) THEN
    SWITCH ::= 4
  ELSE
    SWITCH ::= 3
  FI.

Definition S3Com : com :=
  B ::= B - 1 ;;
  SWITCH ::= 4.

Definition S4Com : com :=
  A ::= A + 1 ;;
  SWITCH ::= 1.

Definition S5Com : com :=
  RETURN ::= A * B.

Definition SwitchMap (n : nat) : string :=
  match n with
  | 1 => "S1"
  | 2 => "S2"
  | 3 => "S3"
  | 4 => "S4"
  | 5 => "S5"
  | 6 => "S6"
  | _ => ""
  end.

Definition InitBlk : comBlock :=
  bJump InitCom "Switch".

Definition SwitchBlk : comBlock :=
  bSwitch SwitchCom SWITCH SwitchMap.

Definition S1Blk : comBlock :=
  bJump S1Com "Switch".

Definition S2Blk : comBlock :=
  bJump S2Com "Switch".

Definition S3Blk : comBlock :=
  bJump S3Com "Switch".

Definition S4Blk : comBlock :=
  bJump S4Com "Switch".

Definition S5Blk : comBlock :=
  bEnd S5Com.

Definition FlattenedDict : blockDict :=
  Blank & { "Init" --> InitBlk ; "Switch" --> SwitchBlk ; "S1" --> S1Blk ; "S2" --> S2Blk ; 
            "S3" --> S3Blk ; "S4" --> S4Blk ; "S5" --> S5Blk }.

Definition FlattenedProgram : IFP :=
  (InitBlk, FlattenedDict).

(* Now let's show the execution for each version *)

Example Original_Execution :
  OriginalProgram / { A --> 1 ; B --> 2 } \\\ { A --> 1 ; B --> 2 ; B --> 3 ; A --> 2 ; B --> 5 ; 
    B --> 4 ;  A --> 3 ; RETURN --> 12 }.
  Proof.
    unfold OriginalProgram.  unfold Main, OriginalDict.  unfold IFPEval.  simpl.  apply PE_Terminal.  
    apply BE_End.  unfold OriginalCommand.
    
    (* Now just on the level of IMP *)

    (* Break apart While iterations *)
    eapply E_Seq.  2: apply E_Ass.  2: auto.
    apply E_WhileTrue with { A --> 1 ; B --> 2 ; B --> 3 ; A --> 2 }.  auto.
    2: apply E_WhileTrue with { A --> 1 ; B --> 2 ; B --> 3 ; A --> 2 ; B --> 5 ; B --> 4 ; 
                                A --> 3 }.  2: auto.
    3: apply E_WhileFalse.  3: auto.

    (* Inside the loops *)
    - apply E_Seq with { A --> 1 ; B --> 2 ; B --> 3 }.  apply E_Ass.  auto.  
      eapply E_Seq.  2: { apply E_Ass.  auto. }  apply E_IfFalse.  auto.  apply E_Skip.
    - apply E_Seq with { A --> 1 ; B --> 2 ; B --> 3 ; A --> 2 ; B --> 5 }.  apply E_Ass.  auto.
      eapply E_Seq.  2: { apply E_Ass.  auto. }  apply E_IfTrue.  auto.  apply E_Ass.  auto.     
  Qed.

Example Dismantled_Execution :
  DismantledProgram / { A --> 1 ; B --> 2 } \\\ { A --> 1 ; B --> 2 ; B --> 3 ; A --> 2 ; B --> 5 ; 
    B --> 4 ; A --> 3 ; RETURN --> 12 }.
  Proof.
    unfold DismantledProgram.  unfold L1Blk, DismantledDict.  unfold IFPEval.  simpl.

    (* We'll figure out one block and its proof at a time. *)

    apply PE_AddBlock with L3Blk { A --> 1 ; B --> 2 }.
    2: { apply BE_CondFalse.  unfold L1Com.  apply E_Skip.  auto.  auto. }

    apply PE_AddBlock with L2Blk { A --> 1 ; B --> 2 ; B --> 3}.
    2: { apply BE_CondTrue.  unfold L3Com.  apply E_Ass.  auto.  auto.  auto. }

    apply PE_AddBlock with L1Blk { A --> 1 ; B --> 2 ; B --> 3 ; A --> 2 }.
    2: { apply BE_Jump.  unfold L2Com.  apply E_Ass.  auto.  auto. }

    apply PE_AddBlock with L3Blk { A --> 1 ; B --> 2 ; B --> 3 ; A --> 2 }.
    2 : { apply BE_CondFalse.  unfold L1Com.  apply E_Skip.  auto.  simpl.  auto. }

    apply PE_AddBlock with L5Blk { A --> 1 ; B --> 2 ; B --> 3 ; A --> 2 ; B --> 5 }.
    2 : { apply BE_CondFalse.  unfold L3Com.  apply E_Ass.  auto.  auto.  auto. }

    apply PE_AddBlock with L2Blk { A --> 1 ; B --> 2 ; B --> 3 ; A --> 2 ; B --> 5 ; B --> 4 }.
    2: { apply BE_Jump.  unfold L5Com.  apply E_Ass.  auto.  auto. }

    apply PE_AddBlock with L1Blk { A --> 1 ; B --> 2 ; B --> 3 ; A --> 2 ; B --> 5 ; B --> 4 ; A --> 3 }.
    2: { apply BE_Jump.  unfold L2Com.  apply E_Ass.  auto.  auto. }

    apply PE_AddBlock with L4Blk { A --> 1 ; B --> 2 ; B --> 3 ; A --> 2 ; B --> 5 ; B --> 4 ; A --> 3 }.
    2: { apply BE_CondTrue.  unfold L1Com.  apply E_Skip.  auto.  auto. }

    apply PE_Terminal.  apply BE_End.  unfold L4Com.  apply E_Ass.  auto.
  Qed.

Open Scope string_scope.

Example Flattened_Execution : 
  FlattenedProgram / { A --> 1 ; B --> 2 } \\\ { A --> 1 ; B --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; 
    B --> 3 ; SWITCH --> 4 ; A --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 5 ; SWITCH --> 3 ; 
    B --> 4 ; SWITCH --> 4 ; A --> 3 ; SWITCH --> 1 ; SWITCH --> 5 ; RETURN --> 12 }.
  Proof.
    unfold FlattenedProgram.  unfold InitBlk, FlattenedDict.  unfold IFPEval.  simpl.

    (* Again, figure out one block and its proof at a time. *)

    apply PE_AddBlock with SwitchBlk { A --> 1 ; B --> 2 ; SWITCH --> 1 }.
    2 : { apply BE_Jump.  unfold InitCom.  apply E_Ass.  auto.  auto. }

    apply PE_AddBlock with S1Blk { A --> 1 ; B --> 2 ; SWITCH --> 1 }.
    2 : { apply BE_Switch with 1 "S1".  unfold SwitchCom.  apply E_Skip.  auto.  auto.  auto. }

    apply PE_AddBlock with SwitchBlk { A --> 1 ; B --> 2 ; SWITCH --> 1 ; SWITCH --> 2 }.
    2 : { apply BE_Jump.  unfold S1Com.  apply E_IfTrue.  auto.  apply E_Ass.  auto.  auto. }

    apply PE_AddBlock with S2Blk { A --> 1 ; B --> 2 ; SWITCH --> 1 ; SWITCH --> 2 }.
    2 : { apply BE_Switch with 2 "S2".  unfold SwitchCom.  apply E_Skip.  auto.  auto.  auto. }

    apply PE_AddBlock with SwitchBlk { A --> 1 ; B --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 3 ; 
                                       SWITCH --> 4 }.
    2 : { apply BE_Jump.  unfold S2Com.  apply E_Seq with { A --> 1 ; B --> 2 ; SWITCH --> 1 ; 
          SWITCH --> 2 ; B --> 3 }.  
          apply E_Ass.  auto.  apply E_IfTrue.  auto.  apply E_Ass.  auto.  auto. }

    apply PE_AddBlock with S4Blk { A --> 1 ; B --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 3 ; 
                                   SWITCH --> 4 }.
    2 : { apply BE_Switch with 4 "S4".  unfold SwitchCom.  apply E_Skip.  auto.  auto.  auto. }

    apply PE_AddBlock with SwitchBlk { A --> 1 ; B --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 3 ;
                                       SWITCH --> 4 ; A --> 2 ; SWITCH --> 1 }.
    2 : { apply BE_Jump.  unfold S4Com.  eapply E_Seq.  apply E_Ass.  auto.  simpl.  apply E_Ass.
          auto.  auto. }

    apply PE_AddBlock with S1Blk { A --> 1 ; B --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 3 ; 
                                   SWITCH --> 4 ; A --> 2 ; SWITCH --> 1 }.
    2 : { apply BE_Switch with 1 "S1".  unfold SwitchCom.  apply E_Skip.  auto.  auto.  auto. }

    apply PE_AddBlock with SwitchBlk { A --> 1 ; B --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 3 ; 
                                       SWITCH --> 4 ; A --> 2 ; SWITCH --> 1 ; SWITCH --> 2}.
    2 : { apply BE_Jump.  unfold S1Com.  apply E_IfTrue.  auto.  apply E_Ass.  auto.  auto. }
  
    apply PE_AddBlock with S2Blk { A --> 1 ; B --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 3 ; 
                                   SWITCH --> 4 ; A --> 2 ; SWITCH --> 1 ; SWITCH --> 2}.
    2 : { apply BE_Switch with 2 "S2".  unfold SwitchCom.  apply E_Skip.  auto.  auto.  auto. }

    apply PE_AddBlock with SwitchBlk { A --> 1 ; B --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 3 ;
                                       SWITCH --> 4 ; A --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; 
                                       B --> 5 ; SWITCH --> 3 }.
    2 : { apply BE_Jump.  unfold S2Com.  eapply E_Seq with { A --> 1 ; B --> 2 ; SWITCH --> 1 ; 
          SWITCH --> 2 ; B --> 3 ;  SWITCH --> 4 ; A --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 5 }.  
          apply E_Ass.  auto.  apply E_IfFalse.  auto.  apply E_Ass.  auto.  auto. }

    apply PE_AddBlock with S3Blk { A --> 1 ; B --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 3 ; 
                                   SWITCH --> 4 ; A --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 5 ; 
                                   SWITCH --> 3 }.
    2 : { apply BE_Switch with 3 "S3".  unfold SwitchCom.  apply E_Skip.  auto.  auto.  auto. }

    apply PE_AddBlock with SwitchBlk { A --> 1 ; B --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ;
      B --> 3 ; SWITCH --> 4 ; A --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 5 ; SWITCH --> 3 ;
      B --> 4 ; SWITCH --> 4 }.
    2 : { apply BE_Jump.  unfold S3Com.  eapply E_Seq.  apply E_Ass.  auto.  simpl.  
          apply E_Ass.  auto.  auto. }

    apply PE_AddBlock with S4Blk { A --> 1 ; B --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 3 ; 
                                   SWITCH --> 4 ; A --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 5 ;
                                   SWITCH --> 3 ; B --> 4 ; SWITCH --> 4 }.
    2 : { apply BE_Switch with 4 "S4".  unfold SwitchCom.  apply E_Skip.  auto.  auto.  auto. }

    apply PE_AddBlock with SwitchBlk { A --> 1 ; B --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; 
      B --> 3 ; SWITCH --> 4 ; A --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 5 ; SWITCH --> 3 ;
      B --> 4 ; SWITCH --> 4 ; A --> 3 ; SWITCH --> 1 }.
    2 : { apply BE_Jump.  unfold S4Com.  eapply E_Seq.  apply E_Ass.  auto.  simpl.
          apply E_Ass.  auto.  auto. }

    apply PE_AddBlock with S1Blk { A --> 1 ; B --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 3 ; 
      SWITCH --> 4 ; A --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 5 ; SWITCH --> 3 ; B --> 4 ; 
      SWITCH --> 4 ; A --> 3 ; SWITCH --> 1 }.
    2 : { apply BE_Switch with 1 "S1".  unfold SwitchCom.  apply E_Skip.  auto.  auto.  auto. }

    apply PE_AddBlock with SwitchBlk { A --> 1 ; B --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; 
      B --> 3 ; SWITCH --> 4 ; A --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 5 ; SWITCH --> 3 ; 
      B --> 4 ; SWITCH --> 4 ; A --> 3 ; SWITCH --> 1 ; SWITCH --> 5}.
    2 : { apply BE_Jump.  unfold S1Com.  apply E_IfFalse.  auto.  apply E_Ass.  auto.  auto. }

    apply PE_AddBlock with S5Blk { A --> 1 ; B --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 3 ; 
      SWITCH --> 4 ; A --> 2 ; SWITCH --> 1 ; SWITCH --> 2 ; B --> 5 ; SWITCH --> 3 ; B --> 4 ; 
      SWITCH --> 4 ; A --> 3 ; SWITCH --> 1 ; SWITCH --> 5}.
    2 : { apply BE_Switch with 5 "S5".  unfold SwitchCom.  apply E_Skip.  auto.  auto.  auto. }

    apply PE_Terminal.  apply BE_End.  unfold S5Com.  apply E_Ass.  auto.
  Qed.

End CWExample.

