Require Import Basics.
Require Import List.

Require Import Listutils.
Require Import PsCore.

Definition termtrue_spec (t1 : term) : Prop :=
  forall (t2 t3 : term) (vs ps : stack),
    (t3 :: t2 :: vs, t1 :: ps) |=>* (t3 :: t2 :: vs, ps).

Definition termfalse_spec (t1 : term) : Prop :=
  forall (t2 t3 : term) (vs ps : stack),
    (t3 :: t2 :: vs, t1 :: ps) |=>* (t2 :: t3 :: vs, ps).

Definition termbool_spec (b : bool) (t : term) : Prop :=
  if b then termtrue_spec t else termfalse_spec t.

Definition termtrue := termnop.

Definition termfalse := termswap.

Lemma eval_termtrue : termtrue_spec termtrue.
  repeat intro ; evalauto.
Qed.

Lemma eval_termfalse : termfalse_spec termfalse.
  repeat intro ; evalauto.
Qed.

Lemma termtrue_proof : termbool_spec true termtrue.
  apply eval_termtrue.
Qed.

Lemma termfalse_proof : termbool_spec false termfalse.
  apply eval_termfalse.
Qed.

Definition termnot := termseq [ termpush ; termswap ; termcons ].

Lemma termnot_proof : forall (b : bool) (t1 : term) (vs ps : stack),
  termbool_spec b t1 ->
    exists t2 : term,
      termbool_spec (negb b) t2 /\
      (t1 :: vs, termnot :: ps) |=>* (t2 :: vs, ps).
  intros.
  eexists.
  destruct b ; eapply (flip (@conj _ _)).
  evalauto.
  repeat intro ; evalauto ; evalpartial H ; evalauto.
  evalauto.
  repeat intro ; evalauto ; evalpartial H ; evalauto.
Qed.

Definition termif := termseq [ termexec ; termpop ].

Lemma eval_termif : forall (b : bool) (t1 t2 t3 : term) (vs ps : stack),
  termbool_spec b t3 -> (t3 :: t2 :: t1 :: vs, termif :: ps) |=>*
    ((if b then t1 else t2) :: vs, ps).
  intros.
  destruct b ; evalauto ; evalpartial H ; evalauto.
Qed.

Definition termexecif := termseq [ termif ; termexec ].

Lemma eval_termexecif : forall (b : bool) (t1 t2 t3 : term) (vs ps : stack),
  termbool_spec b t3 -> (t3 :: t2 :: t1 :: vs, termexecif :: ps) |=>*
    (vs, (if b then t1 else t2) :: ps).
  intros.
  destruct b ; evalauto ; evalpartial H ; evalauto.
Qed.

Definition termxor := termseq [ termcons ; termnot ].

Lemma termxor_proof : forall (b1 b2 : bool) (t1 t2 : term) (vs ps : stack),
  termbool_spec b1 t1 -> termbool_spec b2 t2 ->
    exists t3 : term,
      termbool_spec (xorb b1 b2) t3 /\
      (t2 :: t1 :: vs, termxor :: ps) |=>* (t3 :: vs, ps).
  intros.
  destruct b1, b2 ; eexists ;
    (eapply (flip (@conj _ _)) ; [ evalauto |
      repeat intro ; evalauto ; evalpartial H ; evalpartial H0 ; evalauto ]).
Qed.
