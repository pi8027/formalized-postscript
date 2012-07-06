Require Import
  Arith.Even Arith.Wf_nat Arith.Euclid
  List Basics Relations Omega ArithRing.
Require Import Utils PsCore PsBool.

Definition instincr : inst := instseq
  [ instdup ; instquote ; instswap ; instquote ; instcons ;
    instswap ; instquote ; instcons ; instexec ;
    instsnoc ; instswap ].

Lemma eval_instincr : forall (i1 i2 : inst) (vs ps : stack),
  (i1 :: i2 :: vs, instincr :: ps) |=>* (i1 :: instpair i2 i1 :: vs, ps).
  intros ; evalauto.
Qed.

Lemma eval_instincr_replicate : forall (n : nat) (i1 i2 : inst) (vs ps : stack),
  (i1 :: i2 :: vs, replicate n instincr ++ ps) |=>*
    (i1 :: instseq' (replicate n i1) i2 :: vs, ps).
  induction n ; intros ; evalauto.
  evalpartial IHn ; evalauto.
Qed.

Definition instnatq (n : nat) : inst := instseq (replicate n instincr).

Lemma eval_instnatq : forall (n : nat) (i1 i2 : inst) (vs ps : stack),
  (i1 :: i2 :: vs, instnatq n :: ps) |=>*
    (i1 :: instseq' (replicate n i1) i2 :: vs, ps).
  intros.
  evalpartial evalseq.
  evalpartial eval_instincr_replicate.
  evalauto.
Qed.

Definition instnat_spec (n : nat) (i1 : inst) : Prop :=
  forall (i2 : inst) (vs ps : stack),
    (i2 :: vs, i1 :: ps) |=>* (vs, replicate n i2 ++ ps).

Definition instnat (n : nat) : inst := instseq
  [ instpush ; instnop ; instswap ; instnatq n ; instpop ; instexec ].

Lemma eval_instnat : forall (n : nat), instnat_spec n (instnat n).
  repeat intro.
  evalpartial evalseq ; evalauto.
  evalpartial eval_instnatq ; evalauto.
  apply evalseq.
Qed.

Definition instnat_quote : inst := instseq
  [ instpush ; instnop ; instquote ;
    instpush ; instincr ; instquote ; instcons ;
    instswap ; instquote ; instcons ; instexec ;
    instpush ; instincr ; instswap ; instexec ; instpop ].

Lemma eval_instnat_quote :
  forall (n : nat) (i : inst) (vs ps : stack), instnat_spec n i ->
    (i :: vs, instnat_quote :: ps) |=>* (instnatq n :: vs, ps).
  repeat intro.
  evalauto ; evalpartial H ; evalpartial eval_instincr_replicate ; evalauto.
Qed.

Opaque instnat_quote.

Definition instnat_unquote : inst := instseq
  [ instpush ; instnop ;
    instpush ; instpush ; instcons ;
    instpush ; instnop ; instcons ;
    instpush ; instswap ; instcons ;
    instsnoc ;
    instpush ; instpop ; instcons ;
    instpush ; instexec ; instcons ].

Definition eval_instnat_unquote : forall (n : nat) (vs ps : stack),
  (instnatq n :: vs, instnat_unquote :: ps) |=>* (instnat n :: vs, ps).
  repeat intro ; evalauto.
Qed.

Opaque instnat_unquote.

Lemma instnatq_eqmap : forall (n m : nat), instnatq n = instnatq m -> n = m.
  intro.
  induction n ; intros ; destruct m.
  auto.
  unfold instnatq, instseq, replicate at 1, instseq' at 1, fold_left in H.
  rewrite (instseq_replicate (S m) instincr instnop) in H.
  inversion H.
  unfold instnatq, instseq, replicate at 2, instseq' at 2, fold_left in H.
  rewrite (instseq_replicate (S n) instincr instnop) in H.
  inversion H.
  f_equal.
  apply IHn.
  unfold instnatq, instseq in *.
  repeat erewrite instseq_replicate in *.
  inversion H.
  auto.
Qed.

Lemma instnat_eqmap : forall (n m : nat) (i : inst),
  instnat_spec n i -> instnat_spec m i -> n = m.
  intros.
  assert
    (([], replicate n instpop) |=>*' ([], replicate m instpop) \/
     ([], replicate m instpop) |=>*' ([], replicate n instpop)).
    repeat erewrite <- evalrtc_is_evalrtc'.
    apply (evalrtc_confluence ([ instpop ], [ i ])).
    evalpartial H.
    erewrite app_nil_r.
    evalauto.
    evalpartial H0.
    erewrite app_nil_r.
    evalauto.
  assert (replicate n instpop = replicate m instpop).
    destruct H1 ; destruct n ; destruct m ; inversion H1 ;
      (auto || inversion H2 || simpl ; f_equal ; auto).
  clear H H0 H1.
  revert m H2 ; induction n ; intro ; destruct m ; simpl ; intros ;
    (auto || congruence || f_equal ; apply IHn ; congruence).
Qed.

Definition instnatq_succ : inst := instseq [ instpush ; instincr ; instcons ].

Lemma eval_instnatq_succ : forall (n : nat) (vs ps : stack),
  (instnatq n :: vs, instnatq_succ :: ps) |=>* (instnatq (S n) :: vs, ps).
  intros.
  evalauto.
  rtcrefl.
  unfold instnat, instnatq, instseq.
  erewrite instseq_replicate.
  simpl ; unfold flip ; f_equal.
  apply eq_sym, instseq_replicate.
Qed.

Opaque instnatq_succ.

Definition instnat_succ : inst :=
  instseq [ instnat_quote ; instnatq_succ ; instnat_unquote ].

Lemma eval_instnat_succ :
  forall (n : nat) (i : inst) (vs ps : stack), instnat_spec n i ->
    (i :: vs, instnat_succ :: ps) |=>* (instnat (S n) :: vs, ps).
  intros.
  evalauto.
  evalpartial eval_instnat_quote by eauto.
  evalpartial eval_instnatq_succ.
  eapply eval_instnat_unquote.
Qed.

Opaque instnat_succ.

Lemma instnat_succ_proof :
  forall (n : nat) (i1 : inst) (vs ps : stack), instnat_spec n i1 ->
    exists i2 : inst, instnat_spec (S n) i2 /\
    (i1 :: vs, instnat_succ :: ps) |=>* (i2 :: vs, ps).
  intros.
  evalpartial eval_instnat_succ by eauto.
  evalauto.
  apply (eval_instnat (S n)).
Qed.

Definition instnat_add : inst := instseq
  [ instswap ; instpush ; instnat_succ ; instswap ; instexec ].

Lemma instnat_add_proof : forall (n m : nat) (i1 i2 : inst) (vs ps : stack),
  instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (n + m) i3 /\
    (i2 :: i1 :: vs, instnat_add :: ps) |=>* (i3 :: vs, ps).
  intros.
  evalauto.
  evalpartial H.
  generalize m as m', i2 as i3, H0 ; clear H H0.
  induction n ; intros ; simpl.
  evalauto ; apply H0.
  edestruct (instnat_succ_proof _ _ _ _ H0) as [? [? ?]].
  evalpartial H1.
  replace (S (n + m')) with (n + S m') by omega.
  apply (IHn (S m') x H).
Qed.

Opaque instnat_add.

Definition instnatq_add : inst := instseq
  [ instnat_unquote ; instswap ; instnat_unquote ; instswap ;
    instnat_add ; instnat_quote ].

Lemma eval_instnatq_add : forall (n m : nat) (vs ps : stack),
  (instnatq m :: instnatq n :: vs, instnatq_add :: ps) |=>*
    (instnatq (n + m) :: vs, ps).
  intros.
  evalpartial evalseq.
  do 2 (evalpartial eval_instnat_unquote ; evalstep).
  edestruct (instnat_add_proof _ _ _ _ _ _
    (eval_instnat n) (eval_instnat m)) as [? [? ?]].
  evalpartial H0.
  apply (eval_instnat_quote (n + m) x vs ps H).
Qed.

Opaque instnatq_add.

Definition instnat_mult : inst := instseq
  [ instswap ; instquote ; instpush ; instnat_add ; instcons ; instquote ;
    instsnoc ; instpush ; instnat 0 ; instquote ; instsnoc ; instexec ].

Lemma instnat_mult_proof : forall (n m : nat) (i1 i2 : inst) (vs ps : stack),
  instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (m * n) i3 /\
    (i2 :: i1 :: vs, instnat_mult :: ps) |=>* (i3 :: vs, ps).
  intros.
  evalauto.
  evalpartial H0.
  clear H0.
  replace (m * n) with (m * n + 0) by omega.
  generalize 0 as o, (instnat 0) as i3, (eval_instnat 0).
  induction m ; intros ; simpl ; evalauto.
  apply H0.
  edestruct (instnat_add_proof _ _ _ _ _ _ H0 H) as [? [? ?]].
  evalpartial H2.
  replace (n + m * n + o) with (m * n + (o + n)) by omega ; auto.
Qed.

Opaque instnat_mult.

Definition instnatq_mult : inst := instseq
  [ instnat_unquote ; instswap ; instnat_unquote ; instswap ;
    instnat_mult ; instnat_quote ].

Lemma eval_instnatq_mult : forall (n m : nat) (vs ps : stack),
  (instnatq m :: instnatq n :: vs, instnatq_mult :: ps) |=>*
    (instnatq (m * n) :: vs, ps).
  intros.
  evalpartial evalseq.
  do 2 (evalpartial eval_instnat_unquote ; evalstep).
  edestruct (instnat_mult_proof _ _ _ _ _ _
    (eval_instnat n) (eval_instnat m)) as [? [? ?]].
  evalpartial H0.
  apply eval_instnat_quote ; auto.
Qed.

Opaque instnatq_mult.

Definition instnat_even : inst := instseq
  [ instpush ; instnot ; instquote ; instsnoc ;
    instpush ; insttrue ; instswap ; instexec ].

Lemma instnat_even_proof :
  forall (n : nat) (i1 : inst) (vs ps : stack), instnat_spec n i1 -> even n ->
    exists i2 : inst, insttrue_spec i2 /\
    (i1 :: vs, instnat_even :: ps) |=>* (i2 :: vs, ps).
  intros.
  evalauto.
  evalpartial H.
  generalize insttrue, H0, eval_insttrue.
  clear H.
  refine ((fix IHn (n : nat) :=
    match n with
      | 0 => _
      | S 0 => _
      | S (S n) => _
    end) n) ; intros.
  evalauto.
  apply H.
  inversion H1 ; inversion H3.
  evalauto.
  apply IHn.
  inversion H1 ; inversion H3 ; auto.
  repeat intro ; evalauto ; evalpartial H ; evalauto.
Qed.

Lemma instnat_even_proof' :
  forall (n : nat) (i1 : inst) (vs ps : stack), instnat_spec n i1 -> odd n ->
    exists i2 : inst, instfalse_spec i2 /\
    (i1 :: vs, instnat_even :: ps) |=>* (i2 :: vs, ps).
  intros.
  evalauto.
  evalpartial H.
  generalize insttrue, H0, eval_insttrue.
  clear H.
  refine ((fix IHn (n : nat) :=
    match n with
      | 0 => _
      | S 0 => _
      | S (S n) => _
    end) n) ; intros.
  inversion H1.
  evalauto.
  repeat intro ; evalauto ; evalpartial H ; evalauto.
  evalauto.
  apply IHn.
  inversion H1 ; inversion H3 ; auto.
  repeat intro ; evalauto ; evalpartial H ; evalauto.
Qed.

Opaque instnat_even.

Definition instnat_iszero : inst := instseq
  [ instpush ; instpop ; instpush ; instfalse ; instquote ;
    instcons ; instquote ; instsnoc ;
    instpush ; insttrue ; instswap ; instexec ].

Lemma instnat_iszero_proof :
  forall (n : nat) (i1 : inst) (vs ps : stack), instnat_spec n i1 ->
    exists i2 : inst,
      instbool_spec (match n with 0 => true | S _ => false end) i2 /\
      (i1 :: vs, instnat_iszero :: ps) |=>* (i2 :: vs, ps).
  intros.
  destruct n.
  evalauto.
  evalpartial H.
  evalauto.
  repeat intro ; evalauto.
  evalauto.
  evalpartial H.
  evalauto.
  clear H.
  induction n ; intros.
  evalauto.
  repeat intro ; evalauto.
  evalauto ; auto.
Qed.

Opaque instnat_iszero.

Definition instnat_pred : inst := instseq
  [ instpush ; instnat 0 ; instquote ; instdup ; instcons ;
    instpush ; instseq [ instpop ; instdup ; instnat_succ ; instswap ] ;
    instquote ; instcons ; instsnoc ; instexec ; instswap ; instpop ].

Lemma instnat_pred_proof :
  forall (n : nat) (i1 : inst) (vs ps : stack), instnat_spec n i1 ->
    exists i2 : inst, instnat_spec (n - 1) i2 /\
    (i1 :: vs, instnat_pred :: ps) |=>* (i2 :: vs, ps).
  intros.
  evalauto.
  evalpartial H.
  clear i1 H.
  replace (n - 1) with (n + 0 - 1) by omega.
  replace (instnat 0 :: instnat 0 :: vs)
    with (instnat (0 - 1) :: instnat 0 :: vs)
    by (f_equal ; omega).
  generalize (instnat (0 - 1)) as i1, (instnat 0) as i2,
    (eval_instnat (0 - 1)), (eval_instnat 0).
  generalize 0 at 1 3 4 as m.
  induction n ; intros ; simpl.
  evalauto ; auto.
  replace (n + m - 0) with (n + m) by omega.
  evalauto.
  edestruct (instnat_succ_proof m i2 _ _ H0) as [? [? ?]].
  evalpartial H2 ; clear H2.
  evalauto.
  replace (n + m) with (n + S m - 1) by omega.
  refine (IHn (S m) i2 x _ H1).
  replace (S m - 1) with m by omega ; auto.
Qed.

Opaque instnat_pred.

Definition instnat_sub : inst := instseq
  [ instpush ; instnat_pred ; instquote ; instsnoc ; instexec ].

Lemma instnat_sub_proof : forall (n m : nat) (i1 i2 : inst) (vs ps : stack),
  instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (n - m) i3 /\
    (i2 :: i1 :: vs, instnat_sub :: ps) |=>* (i3 :: vs, ps).
  intros.
  evalauto.
  evalpartial H0 ; clear H0 i2.
  revert n i1 H.
  induction m ; intros ; simpl.
  evalauto.
  replace (n - 0) with n by omega ; apply H.
  replace (n - S m) with (n - 1 - m) by omega.
  edestruct (instnat_pred_proof n i1 _ _ H) as [? [? ?]].
  evalpartial H1 ; auto.
Qed.

Opaque instnat_sub.

Definition instnat_le : inst := instpair instnat_sub instnat_iszero.

Lemma instnat_le_proof : forall (n m : nat) (i1 i2 : inst) (vs ps : stack),
  instnat_spec n i1 -> instnat_spec m i2 -> n <= m ->
    exists i3 : inst, insttrue_spec i3 /\
    (i2 :: i1 :: vs, instnat_le :: ps) |=>* (i3 :: vs, ps).
  intros.
  evalauto.
  edestruct (instnat_sub_proof n m i1 i2 _ _ H H0) as [? [? ?]].
  evalpartial H3.
  edestruct (instnat_iszero_proof (n - m) x _ _ H2) as [? [? ?]].
  evalpartial H5.
  evalauto.
  replace (n - m) with 0 in * by omega ; auto.
Qed.

Lemma instnat_le_proof' : forall (n m : nat) (i1 i2 : inst) (vs ps : stack),
  instnat_spec n i1 -> instnat_spec m i2 -> ~ (n <= m) ->
    exists i3 : inst, instfalse_spec i3 /\
    (i2 :: i1 :: vs, instnat_le :: ps) |=>* (i3 :: vs, ps).
  intros.
  evalauto.
  edestruct (instnat_sub_proof n m i1 i2 _ _ H H0) as [? [? ?]].
  evalpartial H3.
  edestruct (instnat_iszero_proof (n - m) x _ _ H2) as [? [? ?]].
  evalpartial H5.
  evalauto.
  replace (n - m) with (S (n - m - 1)) in * by omega ; auto.
Qed.

Opaque instnat_le.

Definition instnat_mod_iter : inst := instseq
  [ instquote ;
    instswap ; instquote ; instcons ;
    instswap ; instquote ; instcons ;
    instswap ; instquote ; instcons ; instexec ;
    instquote ; instdup ; instcons ; instswap ;
    instquote ; instcons ; instexec ;
    instquote ; instdup ; instcons ; instswap ;
    instquote ; instcons ; instexec ; instswap ;
    instswap ; instnat_le ;
    instpush ; instseq
      [ instquote ; instdup ; instcons ;
        instswap ; instquote ; instcons ; instexec ;
        instswap ; instnat_sub ;
        instquote ; instswap ; instquote ; instcons ;
        instswap ; instnat_succ ; instquote ; instcons ;
        instswap ; instquote ; instcons ; instexec ;
        instdup ; instexec ] ;
    instpush ; instseq
      [ instquote ;
        instswap ; instquote ; instsnoc ;
        instswap ; instquote ; instcons ;
        instswap ; instquote ; instcons ; instexec ;
        instpop ; instswap ; instpop ; instswap ] ;
    instexecif ].

Lemma instnat_mod_iter_proof :
  forall (n m q : nat) (i1 i2 i3 i4 : inst) (vs ps : stack),
  m <= n -> instnat_spec n i1 -> instnat_spec m i2 -> instnat_spec q i3 ->
    exists i1' : inst, instnat_spec (n - m) i1' /\
    exists i3' : inst, instnat_spec (S q) i3' /\
    (i4 :: i3 :: i2 :: i1 :: vs, instnat_mod_iter :: ps) |=>*
    (i4 :: i3' :: i2 :: i1' :: vs, i4 :: ps).
  intros.
  evalauto.
  edestruct (instnat_le_proof m n i2 i1 _ _ H1 H0 H) as [? [? ?]].
  evalpartial H4 ; clear H4.
  evalauto.
  evalpartial H3 ; clear x H3.
  evalauto.
  edestruct (instnat_sub_proof n m i1 i2 _ _ H0 H1) as [? [? ?]].
  evalpartial H4 ; clear H4.
  exists x ; split ; [ exact H3 | clear H3 ].
  evalauto.
  evalpartial (eval_instnat_succ q i3) by tauto.
  evalauto.
  apply (eval_instnat (S q)).
Qed.

Lemma instnat_mod_iter_proof' :
  forall (n m q : nat) (i1 i2 i3 i4 : inst) (vs ps : stack),
  ~ (m <= n) -> instnat_spec n i1 -> instnat_spec m i2 -> instnat_spec q i3 ->
    (i4 :: i3 :: i2 :: i1 :: vs, instnat_mod_iter :: ps) |=>*
    (i1 :: i3 :: vs, ps).
  intros.
  evalauto.
  edestruct (instnat_le_proof' m n i2 i1 _ _ H1 H0 H) as [? [? ?]].
  evalpartial H4 ; clear H4.
  evalauto.
  evalpartial H3 ; clear x H3.
  evalauto.
Qed.

Opaque instnat_mod_iter.

Definition instnat_mod : inst := instseq
  [ instpush ; instnat 0 ; instpush ; instnat_mod_iter ; instdup ; instexec ].

Lemma diveucl_uniqueness : forall (a b : nat) (e1 e2 : diveucl a b),
  match e1 with divex q r _ _ =>
  match e2 with divex q' r' _ _ =>
  q = q' /\ r = r'
  end end.
  intros.
  destruct e1, e2.
  revert b q q0 r r0 e e0 g g0.
  apply (gt_wf_rec a) ; intros.
  destruct (dec_le b n).
  destruct q. simpl in * ; omega.
  destruct q0. simpl in * ; omega.
  assert (q = q0 /\ r = r0).
    simpl in * ; refine (H (n - b) _ b q q0 r r0 _ _ _ _) ; omega.
  omega.
  destruct q.
  destruct q0.
  simpl in * ; omega.
  simpl in *. generalize (q0 * b), e0 ; intros ; omega.
  simpl in *. generalize (q * b), e ; intros ; omega.
Qed.

Lemma instnat_mod_proof :
  forall (n m : nat) (i1 i2 : inst) (vs ps : stack) (eucl : diveucl n m),
  instnat_spec n i1 -> instnat_spec m i2 ->
  match eucl with divex q r _ _ =>
    exists i3 : inst, instnat_spec q i3 /\
    exists i4 : inst, instnat_spec r i4 /\
    (i2 :: i1 :: vs, instnat_mod :: ps) |=>* (i4 :: i3 :: vs, ps)
  end.
  intros.
  destruct eucl.
  evalauto.
  assert (forall r' q' i1 i3,
    instnat_spec r' i1 -> instnat_spec q' i3 -> n = q' * m + r' ->
    exists i4 : inst, instnat_spec q i4 /\
    exists i5 : inst, instnat_spec r i5 /\
    (instnat_mod_iter :: i3 :: i2 :: i1 :: vs, instnat_mod_iter :: ps)
    |=>* (i5 :: i4 :: vs, ps)).
    clear H i1.
    intro.
    apply (gt_wf_rec r').
    intros.
    destruct (dec_le m n0).
    edestruct (instnat_mod_iter_proof n0 m q'
      i1 i2 i3 instnat_mod_iter _ _ H4 H1 H0 H2) as [? [? [? [? ?]]]].
    evalpartial H7 ; clear H7.
    refine (H (n0 - m) _ (S q') x x0 H5 H6 _).
    omega.
    simpl ; omega.
    evalpartial (instnat_mod_iter_proof' n0 m q'
      i1 i2 i3 instnat_mod_iter vs ps H4 H1 H0 H2).
    destruct (diveucl_uniqueness n m
        (divex n m q r g e) (divex n m q' n0 (not_le _ _ H4) H3)).
    evalauto.
    rewrite H5 ; auto.
    rewrite H6 ; auto.
  apply (H1 n 0 i1 (instnat 0) H (eval_instnat 0)).
  auto.
Qed.

Opaque instnat_mod.
