Require Import
  Arith.Even Arith.Wf_nat Arith.Euclid
  Lists.List Program.Basics Relations.Relations Omega ArithRing
  ssreflect Common PsCore PsBool.

(*
instincr:
  自然数を構成するための補助的な命令。
*)
Definition instincr : inst := instseq
  [ instcopy ; instquote ; instswap ; instquote ; instcons ;
    instswap ; instquote ; instcons ; instexec ;
    instsnoc ; instswap ].

Lemma eval_instincr : forall i1 i2 vs cs,
  (i1 :: i2 :: vs, instincr :: cs) |=>* (i1 :: instpair i2 i1 :: vs, cs).
Proof.
  intros ; evalauto.
Qed.

Lemma eval_instincr_replicate : forall n i1 i2 vs cs,
  (i1 :: i2 :: vs, replicate n instincr ++ cs) |=>*
    (i1 :: instseq' (replicate n i1) i2 :: vs, cs).
Proof.
  induction n ; intros ; evalauto.
  evalpartial IHn ; evalauto.
Qed.

(*
instnatq, instnat_spec:
  どちらも自然数の定義である。近い意味を持つが、違う形をしている。
  instnatq は、自然数 n を instincr を n 個並べた形で表現するものである。
  instnat は、自然数 n を実行することによって、値のスタックの先頭にある命令を n
  個継続のスタックにコピーする(つまり多くの場合においてはそれが n 回実行される)
  命令である。
*)
Definition instnatq (n : nat) : inst := instseq (replicate n instincr).

Lemma eval_instnatq : forall n i1 i2 vs cs,
  (i1 :: i2 :: vs, instnatq n :: cs) |=>*
    (i1 :: instseq' (replicate n i1) i2 :: vs, cs).
Proof.
  intros.
  evalpartial evalseq.
  evalpartial eval_instincr_replicate.
  evalauto.
Qed.

Definition instnat_spec (n : nat) (i1 : inst) : Prop :=
  forall i2 vs cs, (i2 :: vs, i1 :: cs) |=>* (vs, replicate n i2 ++ cs).

(*
instnat:
  任意の自然数に関して、自然数の仕様を満たす命令を構成する。
*)
Definition instnat (n : nat) : inst := instseq
  [ instpush instnop ; instswap ; instnatq n ; instpop ; instexec ].

Lemma eval_instnat : forall n, instnat_spec n (instnat n).
Proof.
  repeat intro.
  evalpartial evalseq ; evalauto.
  evalpartial eval_instnatq ; evalauto.
  apply evalseq.
Qed.

(*
instnat_quote, instnat_unquote:
  instnat, instnatq を相互に変換する命令。
*)
Definition instnat_quote : inst := instseq
  [ instpush (instseq
      [ instpush instnop ; instpush instincr ; instpush instincr ]) ;
    instswap ; instquote ; instcons ; instexec ; instexec ; instpop ].

Lemma eval_instnat_quote : forall n i vs cs, instnat_spec n i ->
  (i :: vs, instnat_quote :: cs) |=>* (instnatq n :: vs, cs).
Proof.
  repeat intro.
  evalauto ; evalpartial H ; evalpartial eval_instincr_replicate ; evalauto.
Qed.

Opaque instnat_quote.

Definition instnat_unquote : inst := instseq
  [ instpush (instseq [ instpush instnop ; instswap ]) ; instsnoc ;
    instpush instpop ; instcons ; instpush instexec ; instcons ].

Lemma eval_instnat_unquote : forall n vs cs,
  (instnatq n :: vs, instnat_unquote :: cs) |=>* (instnat n :: vs, cs).
Proof.
  repeat intro.
  evalauto.
Qed.

Opaque instnat_unquote.

(*
instnatq_eqmap:
  任意の自然数 n, m について、instnatq n = instnatq m であれば n = m。
  対偶を取ると n /= m であれば instnatq n /= instnatq m であり、表現する対象の自
  然数が違えば命令も必ず同値ではないことを表している。
*)
Lemma instnatq_eqmap : forall n m, instnatq n = instnatq m -> n = m.
Proof.
  elim => [ | n H ] ; elim.
  * done.
  * move=> n H H0.
    rewrite /instnatq /instseq (instseq_replicate (S n) instincr instnop) in H0.
    inversion H0.
  * move=> H0.
    rewrite /instnatq /instseq (instseq_replicate (S n) instincr instnop) in H0.
    inversion H0.
  * move=> m H0 H1 ; f_equal ; apply: H.
    move: H1 ; rewrite /instnatq /instseq !instseq_replicate.
    by move=> H ; inversion H.
Qed.

(*
instnat_eqmap:
  任意の自然数 n, m と任意の命令 i について、i が自然数 n, m としての仕様を同時
  に満たしていれば、必ず n = m である。
  よって、n /= m であればある命令が自然数 n, m としての仕様を同時に満たすことは
  ない。
*)
Lemma instnat_eqmap :
  forall n m i, instnat_spec n i -> instnat_spec m i -> n = m.
Proof.
  intros.
  have H1: (([], replicate n instpop) |=>* ([], replicate m instpop) \/
      ([], replicate m instpop) |=>* ([], replicate n instpop)).
    apply (eval_semi_uniqueness ([ instpop ], [ i ])).
    evalpartial H.
    erewrite app_nil_r.
    evalauto.
    evalpartial H0.
    erewrite app_nil_r.
    evalauto.
  have: (replicate n instpop = replicate m instpop).
    by destruct H1 ; destruct n ; destruct m ; inversion H1 ;
      (inversion H2 || simpl ; f_equal).
  clear.
  move: m ; induction n ; intro ; destruct m ; simpl ; intros ;
    (congruence || f_equal ; apply IHn ; congruence).
Qed.

(*
instnatq_succ, instnat_succ
  後者関数に相当する命令。
*)
Definition instnatq_succ : inst := instpair (instpush instincr) instcons.

Lemma eval_instnatq_succ : forall n vs cs,
  (instnatq n :: vs, instnatq_succ :: cs) |=>* (instnatq (S n) :: vs, cs).
Proof.
  intros.
  evalauto.
  rtcrefl.
  rewrite /instnatq /instseq.
  by repeat erewrite instseq_replicate.
Qed.

Opaque instnatq_succ.

Definition instnat_succ : inst :=
  instseq [ instnat_quote ; instnatq_succ ; instnat_unquote ].

Lemma eval_instnat_succ :
  forall n i vs cs, instnat_spec n i ->
    (i :: vs, instnat_succ :: cs) |=>* (instnat (S n) :: vs, cs).
Proof.
  intros.
  evalauto.
  evalpartial eval_instnat_quote.
  evalpartial eval_instnatq_succ.
  eapply eval_instnat_unquote.
Qed.

Opaque instnat_succ.

Lemma instnat_succ_proof :
  forall n i1 vs cs, instnat_spec n i1 ->
    exists i2 : inst, instnat_spec (S n) i2 /\
    (i1 :: vs, instnat_succ :: cs) |=>* (i2 :: vs, cs).
Proof.
  intros.
  evalpartial eval_instnat_succ.
  evalauto.
  apply (eval_instnat (S n)).
Qed.

(*
instnat_add:
  加算命令。
*)
Definition instnat_add : inst := instseq
  [ instswap ; instpush instnat_succ ; instswap ; instexec ].

Lemma instnat_add_proof : forall n m i1 i2 vs cs,
  instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (n + m) i3 /\
    (i2 :: i1 :: vs, instnat_add :: cs) |=>* (i3 :: vs, cs).
Proof.
  intros.
  evalauto.
  evalpartial H.
  move: m i2 H0 ; clear H.
  induction n ; intros ; simpl.
  evalauto ; apply H0.
  edestruct (instnat_succ_proof _ _ _ _ H0) as [? [? ?]].
  evalpartial H1.
  replace (S (n + m)) with (n + S m) by omega ; auto.
Qed.

Opaque instnat_add.

(*
instnat_mult:
  乗算命令。
*)
Definition instnat_mult : inst := instseq
  [ instquote ; instpush instnat_add ; instcons ; instquote ;
    instsnoc ; instpush (instpush (instnat 0)) ; instsnoc ; instexec ].

Lemma instnat_mult_proof : forall n m i1 i2 vs cs,
  instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (n * m) i3 /\
    (i2 :: i1 :: vs, instnat_mult :: cs) |=>* (i3 :: vs, cs).
Proof.
  intros.
  evalauto.
  evalpartial H.
  clear H.
  replace (n * m) with (n * m + 0) by omega.
  generalize 0 as o, (instnat 0) as i3, (eval_instnat 0).
  induction n ; intros ; simpl ; evalauto.
  done.
  edestruct (instnat_add_proof _ _ _ _ _ _ H H0) as [? [? ?]].
  evalpartial H2.
  replace (m + n * m + o) with (n * m + (o + m)) by omega ; auto.
Qed.

Opaque instnat_mult.

(*
instnat_even:
  偶奇判定の命令。
*)
Definition instnat_even : inst := instseq
  [ instpush insttrue ; instswap ; instpush instnot ; instswap ; instexec ].

Lemma instnat_even_proof :
  forall n i1 vs cs, instnat_spec n i1 ->
    exists i2 : inst,
    instbool_spec (if even_odd_dec n then true else false)%GEN_IF i2 /\
    (i1 :: vs, instnat_even :: cs) |=>* (i2 :: vs, cs).
Proof.
  intros.
  evalauto.
  evalpartial H.
  generalize insttrue, eval_insttrue.
  move=> i ; rewrite -/(instbool_spec true i) -/(negb true).
  clear H ; move: i true.
  induction n ; intros.
  by evalauto.
  simpl.
  edestruct (instnot_proof b i _ _ H) as [? [? ?]].
  evalpartial H1.
  destruct (even_odd_dec n) ; simpl in *.
  apply (IHn _ _ H0).
  destruct b ; apply (IHn _ _ H0).
Qed.

Opaque instnat_even.

(*
instnat_iszero:
  ゼロとの比較をする命令。
*)
Definition instnat_iszero : inst := instseq
  [ instpush insttrue ; instswap ;
    instpush (instpair instpop (instpush instfalse)) ; instswap ; instexec ].

Lemma instnat_iszero_proof :
  forall n i1 vs cs, instnat_spec n i1 ->
    exists i2 : inst,
      instbool_spec (match n with 0 => true | S _ => false end) i2 /\
      (i1 :: vs, instnat_iszero :: cs) |=>* (i2 :: vs, cs).
Proof.
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
  by evalauto.
Qed.

Opaque instnat_iszero.

(*
instnat_pred:
  自然数から1を引く命令。元の数が0であれば結果も0となる。
*)
Definition instnat_pred : inst := instseq
  [ instpush (instseq [ instpush (instnat 0) ; instpush (instnat 0) ;
      instpush (instseq [ instpop ; instcopy ; instnat_succ ; instswap ])]) ;
    instsnoc ; instexec ; instswap ; instpop].

Lemma instnat_pred_proof :
  forall n i1 vs cs, instnat_spec n i1 ->
    exists i2 : inst, instnat_spec (n - 1) i2 /\
    (i1 :: vs, instnat_pred :: cs) |=>* (i2 :: vs, cs).
Proof.
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
  by evalauto.
  replace (n + m - 0) with (n + m) by omega.
  evalauto.
  edestruct (instnat_succ_proof m i2 _ _ H0) as [? [? ?]].
  evalpartial H2 ; clear H2.
  evalauto.
  replace (n + m) with (n + S m - 1) by omega.
  refine (IHn (S m) i2 x _ H1).
  by replace (S m - 1) with m by omega.
Qed.

Opaque instnat_pred.

(*
instnat_sub:
  減算命令。
*)
Definition instnat_sub : inst := instseq
  [ instpush instnat_pred ; instswap ; instexec ].

Lemma instnat_sub_proof : forall n m i1 i2 vs cs,
  instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (n - m) i3 /\
    (i2 :: i1 :: vs, instnat_sub :: cs) |=>* (i3 :: vs, cs).
Proof.
  intros.
  evalauto.
  evalpartial H0 ; clear H0 i2.
  move: n i1 H.
  induction m ; intros ; simpl.
  evalauto.
  replace (n - 0) with n by omega ; apply H.
  replace (n - S m) with (n - 1 - m) by omega.
  edestruct (instnat_pred_proof n i1 _ _ H) as [? [? ?]].
  evalpartial H1 ; auto.
Qed.

Opaque instnat_sub.

(*
instnat_le:
  自然数 n, m に関して n <= m かそうでないかを判定する命令。
*)
Definition instnat_le : inst := instpair instnat_sub instnat_iszero.

Lemma instnat_le_proof : forall n m i1 i2 vs cs,
  instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst,
    instbool_spec (if le_dec n m then true else false)%GEN_IF i3 /\
    (i2 :: i1 :: vs, instnat_le :: cs) |=>* (i3 :: vs, cs).
Proof.
  intros.
  evalauto.
  edestruct (instnat_sub_proof n m i1 i2 _ _ H H0) as [? [? ?]].
  evalpartial H2.
  edestruct (instnat_iszero_proof (n - m) x _ _ H1) as [? [? ?]].
  evalpartial H4.
  evalauto.
  replace (match n - m with | 0 => true | S _ => false end)
    with (if le_dec n m then true else false)%GEN_IF in H3.
  auto.
  destruct (le_dec n m).
  by replace (n - m) with 0 by omega.
  by replace (n - m) with (S (n - m - 1)) by omega.
Qed.

Opaque instnat_le.

(*
instnat_eucl:
  割り算を行い、商と余りを計算する命令。
*)
Definition instnat_eucl_iter : inst := instseq
  [ instquote ;
    instswap ; instquote ; instcons ;
    instswap ; instquote ; instcons ;
    instswap ; instquote ; instcons ; instexec ;
    instquote ; instcopy ; instcons ; instswap ;
    instquote ; instcons ; instexec ;
    instquote ; instcopy ; instcons ; instswap ;
    instquote ; instcons ; instexec ; instnat_le ;
    instpush (instseq
      [ instquote ; instcopy ; instcons ;
        instswap ; instquote ; instcons ; instexec ;
        instswap ; instnat_sub ;
        instquote ; instswap ; instquote ; instcons ;
        instswap ; instnat_succ ; instquote ; instcons ;
        instswap ; instquote ; instcons ; instexec ;
        instcopy ; instexec ]) ;
    instpush (instseq
      [ instquote ;
        instswap ; instquote ; instsnoc ;
        instswap ; instquote ; instcons ;
        instswap ; instquote ; instcons ; instexec ;
        instpop ; instswap ; instpop ; instswap ]) ;
    instexecif ].

Lemma instnat_eucl_iter_proof : forall n m q i1 i2 i3 i4 vs cs,
  m <= n -> instnat_spec n i1 -> instnat_spec m i2 -> instnat_spec q i3 ->
    exists i1' : inst, instnat_spec (n - m) i1' /\
    exists i3' : inst, instnat_spec (S q) i3' /\
    (i4 :: i3 :: i2 :: i1 :: vs, instnat_eucl_iter :: cs) |=>*
    (i4 :: i3' :: i2 :: i1' :: vs, i4 :: cs).
Proof.
  intros.
  evalauto.
  edestruct (instnat_le_proof m n i2 i1 _ _ H1 H0) as [? [? ?]].
  destruct (le_dec m n).
  evalpartial H4 ; clear H4.
  evalauto.
  evalpartial H3 ; clear x H3.
  evalauto.
  edestruct (instnat_sub_proof n m i1 i2 _ _ H0 H1) as [? [? ?]].
  evalpartial H4 ; clear H4.
  exists x ; split ; [ exact H3 | clear H3 ].
  evalauto.
  evalpartial (eval_instnat_succ q i3).
  evalauto.
  apply (eval_instnat (S q)).
  apply False_ind ; omega.
Qed.

Lemma instnat_eucl_iter_proof' :
  forall n m q i1 i2 i3 i4 vs cs, ~ (m <= n) ->
  instnat_spec n i1 -> instnat_spec m i2 -> instnat_spec q i3 ->
    (i4 :: i3 :: i2 :: i1 :: vs, instnat_eucl_iter :: cs) |=>*
    (i1 :: i3 :: vs, cs).
Proof.
  intros.
  evalauto.
  edestruct (instnat_le_proof m n i2 i1 _ _ H1 H0) as [? [? ?]].
  destruct (le_dec m n).
  apply False_ind ; omega.
  evalpartial H4.
  evalauto.
  evalpartial H3.
  evalauto.
Qed.

Opaque instnat_eucl_iter.

Definition instnat_eucl : inst := instseq
  [ instpush (instnat 0) ; instpush instnat_eucl_iter ; instnat_eucl_iter ].

Lemma diveucl_uniqueness : forall (a b : nat) (e1 e2 : diveucl a b),
  match e1 with divex q r _ _ =>
  match e2 with divex q' r' _ _ =>
  q = q' /\ r = r'
  end end.
Proof.
  intros.
  destruct e1, e2.
  move: b q q0 r r0 e e0 g g0.
  apply (gt_wf_rec a) ; intros.
  destruct (dec_le b n).
  destruct q. simpl in * ; omega.
  destruct q0. simpl in * ; omega.
  have H1 : (q = q0 /\ r = r0).
    simpl in * ; refine (H (n - b) _ b q q0 r r0 _ _ _ _) ; omega.
  omega.
  destruct q.
  destruct q0.
  simpl in * ; omega.
  simpl in *. generalize (q0 * b), e0 ; intros ; omega.
  simpl in *. generalize (q * b), e ; intros ; omega.
Qed.

Lemma instnat_eucl_proof : forall (n m : nat) (eucl : diveucl n m) i1 i2 vs cs,
  instnat_spec n i1 -> instnat_spec m i2 ->
  match eucl with divex q r _ _ =>
    exists i3 : inst, instnat_spec q i3 /\
    exists i4 : inst, instnat_spec r i4 /\
    (i2 :: i1 :: vs, instnat_eucl :: cs) |=>* (i4 :: i3 :: vs, cs)
  end.
Proof.
  intros.
  destruct eucl.
  evalauto.
  have H1 : (forall r' q' i1 i3,
    instnat_spec r' i1 -> instnat_spec q' i3 -> n = q' * m + r' ->
    exists i4 : inst, instnat_spec q i4 /\
    exists i5 : inst, instnat_spec r i5 /\
    (instnat_eucl_iter :: i3 :: i2 :: i1 :: vs, instnat_eucl_iter :: cs)
    |=>* (i5 :: i4 :: vs, cs)).
    clear H i1.
    intro.
    apply (gt_wf_rec r').
    intros.
    destruct (dec_le m n0).
    edestruct (instnat_eucl_iter_proof n0 m q'
      i1 i2 i3 instnat_eucl_iter _ _ H4 H1 H0 H2) as [? [? [? [? ?]]]].
    evalpartial H7 ; clear H7.
    refine (H (n0 - m) _ (S q') x x0 H5 H6 _).
    omega.
    simpl ; omega.
    evalpartial (instnat_eucl_iter_proof' n0 m q'
      i1 i2 i3 instnat_eucl_iter vs cs H4 H1 H0 H2).
    destruct (diveucl_uniqueness n m
      (divex n m q r g e) (divex n m q' n0 (not_le _ _ H4) H3)).
    by rewrite H5 H6 ; evalauto.
  by apply (H1 n 0 i1 (instnat 0) H (eval_instnat 0)).
Qed.

Opaque instnat_eucl.
