Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool
  Ssreflect.ssrnat Ssreflect.seq Ssreflect.div
  FormalPS.stdlib_ext FormalPS.Core FormalPS.Template FormalPS.Bool.

Set Implicit Arguments.

(*
instnat_spec:
  自然数の仕様。
*)
Definition instnat_spec (n : nat) (i1 : inst) : Prop :=
  forall i2 vs cs, (i2 :: vs, i1 :: cs) |=>* (instseqc_nseq n i2 :: vs, cs).

(*
exists_instnat:
  自然数の仕様を満たす命令。
*)
Lemma exists_instnat : forall n, { i : inst | instnat_spec n i }.
Proof.
  elim => [| n [i H]]; eexists => i2 vs cs /=.
  - evalpartial' evalpop.
    evalpartial evalpush.
    evalauto.
  - evalpartial' evalcopy.
    evalpartial' H.
    apply evalsnoc.
Defined.

Notation instnat n := (proj1_sig (exists_instnat n)).
Notation eval_instnat n := (proj2_sig (exists_instnat n)).

Hint Resolve ((fun n => eval_instnat n) : forall n, instnat_spec n (instnat n)).

(*
instnat_repeat:
  繰り返しの命令。
*)
Lemma exists_instnat_repeat :
  { instnat_repeat : inst |
    forall n i1 i2 vs cs, instnat_spec n i2 ->
    (i1 :: vs, i2 :: instnat_repeat :: cs) |=>* (vs, nseq n i1 ++ cs) }.
Proof.
  eexists => n i1 i2 vs cs H.
  evalpartial H.
  evalpartial evalexec.
  apply evalseqc_nseq.
Defined.

Notation instnat_repeat := (proj1_sig exists_instnat_repeat).
Notation eval_instnat_repeat := (proj2_sig exists_instnat_repeat).

(*
instnat_eqmap:
  任意の自然数 n, m と任意の命令 i について、i が自然数 n, m としての仕様を同時
  に満たしていれば、必ず n = m である。
  よって、n /= m であればある命令が自然数 n, m としての仕様を同時に満たすことは
*)
Lemma instnat_eqmap :
  forall n m i, instnat_spec n i -> instnat_spec m i -> n = m.
Proof.
  move => n m i1 H0 H1.
  have: (([::], nseq n instpop) |=>* ([::], nseq m instpop) \/
      ([::], nseq m instpop) |=>* ([::], nseq n instpop)).
    apply (@eval_semi_uniqueness ([:: instpop], [:: i1; instexec])).
    - evalpartial (eval_instnat_repeat n).
      rtcrefl.
      apply cats0.
    - evalpartial (eval_instnat_repeat m).
      rtcrefl.
      apply cats0.
  clear => H.
  have: (nseq n instpop = nseq m instpop).
    by destruct H, n, m; inversion H => /=; (inversion H0 || f_equal).
  clear; move: n m; elim => [ | n IHn]; case => [ | m] H; inversion H; auto.
Qed.

(*
instnat_succ:
  後者関数。
*)
Lemma exists_instnat_succ :
  { instnat_succ : inst |
    forall n i1 vs cs, instnat_spec n i1 ->
    exists i2 : inst, instnat_spec n.+1 i2 /\
    (i1 :: vs, instnat_succ :: cs) |=>* (i2 :: vs, cs) }.
Proof.
  eexists => n i1 vs cs H; eexists; split.
  - move => i2 vs' cs'.
    evalpartial' evalcopy.
    evalpartial' H.
    apply evalsnoc.
  - evaltemplate 1
      [:: insttpair insttcopy
        (insttpair (instthole 0) (insttpair insttswap insttcons))]
      (Nil instt).
    evalauto.
Defined.

Notation instnat_succ := (proj1_sig exists_instnat_succ).
Notation instnat_succ_proof := (proj2_sig exists_instnat_succ).

(*
instnat_add:
  加算命令。
*)
Lemma exists_instnat_add_tail :
  { instnat_add_tail : inst |
    forall n m i1 i2 vs cs, instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (NatTrec.add n m) i3 /\
    (i2 :: i1 :: vs, instnat_add_tail :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  eexists => n m i1 i2 vs cs H H0.
  evalpartial' evalswap.
  evalpartial' evalpush.
  evalpartial' evalswap.
  evalpartial' evalexec.
  evalpartial (eval_instnat_repeat n).
  clear H i1; move: n m i2 H0; elim => [ | n IH] m i1 H /=.
  - by evalauto.
  - edestruct (instnat_succ_proof m i1) as [i2 [H1 H2]]; auto.
    evalpartial H2.
    auto.
Defined.

Notation instnat_add := (proj1_sig exists_instnat_add_tail).
Notation instnat_add_proof_tail := (proj2_sig exists_instnat_add_tail).

Lemma exists_instnat_add :
  { instnat_add : inst |
    forall n m i1 i2 vs cs, instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (n + m) i3 /\
    (i2 :: i1 :: vs, instnat_add :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  exists instnat_add => n m.
  rewrite -NatTrec.addE.
  apply instnat_add_proof_tail.
Defined.

Notation instnat_add_proof := (proj2_sig exists_instnat_add).

(*
instnat_mult:
  乗算命令。
*)
Lemma exists_instnat_mult_tail :
  { instnat_mult_tail : inst |
    forall n m i1 i2 vs cs, instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (NatTrec.add_mul n m 0) i3 /\
    (i2 :: i1 :: vs, instnat_mult_tail :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  move: (0) (instnat 0) (eval_instnat 0) => o i1 H.
  eexists => n m i2 i3 vs cs H0 H1.
  do 2 evalpartial' evalpush.
  evaltemplate' 4
    [:: insttpair (insttpush (instthole 2)) (instthole 1); instthole 0]
    [:: instthole 3].
  evalpartial (eval_instnat_repeat n).
  clear i2 H0.
  move: n o i1 i3 H H1; elim => [ | n IH] o i1 i2 H H0 /=.
  - evalauto.
    eauto.
  - evalauto.
    evalpartial' evalswap.
    edestruct (instnat_add_proof_tail m o i2 i1) as [i3 [H1 H2]]; auto.
    evalpartial H2.
    auto.
Defined.

Notation instnat_mult := (proj1_sig exists_instnat_mult_tail).
Notation instnat_mult_proof_tail := (proj2_sig exists_instnat_mult_tail).

Lemma exists_instnat_mult :
  { instnat_mult : inst |
    forall n m i1 i2 vs cs, instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (n * m) i3 /\
    (i2 :: i1 :: vs, instnat_mult :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  exists instnat_mult => n m.
  replace (n * m) with (NatTrec.add_mul n m 0) by ssromega.
  apply instnat_mult_proof_tail.
Defined.

Notation instnat_mult_proof := (proj2_sig exists_instnat_mult).

(*
instnat_even:
  偶奇判定の命令。
*)
Lemma exists_instnat_even_tail :
  { instnat_even_tail : inst |
    forall (b : bool) n i1 i2 vs cs, instbool_spec b i1 -> instnat_spec n i2 ->
    exists i3 : inst, instbool_spec (if odd n then ~~ b else b) i3 /\
    (i2 :: i1 :: vs, instnat_even_tail :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  eexists => b n i1 i2 vs cs H H0.
  evalpartial' evalpush.
  evalpartial' evalswap.
  evalpartial' evalexec.
  evalpartial (eval_instnat_repeat n).
  clear H0 i2.
  move: n b i1 H; elim => [ | n IH] b i1 H.
  - by evalauto.
  - edestruct (evalnot b i1) as [i2 [H0 H1]]; auto.
    evalpartial H1; clear i1 H H1.
    edestruct (IH (negb b) i2) as [i1 [H H1]]; auto.
    evalpartial H1; clear IH H0 H1.
    evalauto.
    move: H => //=.
    case: b; case: (odd n) => //=.
Defined.

Notation instnat_even_tail := (proj1_sig exists_instnat_even_tail).
Notation instnat_even_proof_tail := (proj2_sig exists_instnat_even_tail).

Lemma exists_instnat_even :
  { instnat_even : inst |
    forall n i1 vs cs, instnat_spec n i1 ->
    exists i2 : inst, instbool_spec (~~ odd n) i2 /\
    (i1 :: vs, instnat_even :: cs) |=>* (i2 :: vs, cs) }.
Proof.
  eexists => n i1 vs cs H.
  evalpartial' evalpush.
  evalpartial' evalswap.
  edestruct (instnat_even_proof_tail true n) as [i2 [H0 H1]]; eauto.
Defined.

Notation instnat_even := (proj1_sig exists_instnat_even).
Notation instnat_even_proof := (proj2_sig exists_instnat_even).

(*
instnat_iszero:
  ゼロとの比較をする命令。
*)
Lemma exists_instnat_iszero :
  { instnat_iszero : inst |
    forall n i1 vs cs, instnat_spec n i1 ->
    exists i2 : inst,
    instbool_spec (eqn 0 n) i2 /\
    (i1 :: vs, instnat_iszero :: cs) |=>* (i2 :: vs, cs) }.
Proof.
  eexists => n i1 vs cs H.
  exists (if eqn 0 n then insttrue else instfalse)%GEN_IF; split.
  - case (eqn 0 n); auto.
  - evalpartial' (evalpush insttrue).
    evalpartial' evalswap.
    evalpartial' evalpush.
    evalpartial' evalswap.
    evalpartial' evalexec.
    evalpartial (eval_instnat_repeat n).
    clear i1 H.
    move: n insttrue; elim => [| n IHn] i /=.
    - evalauto.
    - move: IHn (IHn instfalse) => _ IHn.
      evalpartial' evalpop.
      evalpartial evalpush.
      case (eqn 0 n) in IHn; apply IHn.
Defined.

Notation instnat_iszero := (proj1_sig exists_instnat_iszero).
Notation instnat_iszero_proof := (proj2_sig exists_instnat_iszero).

(*
instnat_pred:
  前者関数。ただし元の数が0である場合の結果は0である。
*)
Lemma exists_instnat_pred_tail :
  { instnat_pred_tail : inst |
    forall n m i1 i2 i3 vs cs,
    instnat_spec n i1 -> instnat_spec (n - 1) i2 -> instnat_spec m i3 ->
    exists i4 : inst, instnat_spec (n + m - 1) i4 /\
    (i3 :: i2 :: i1 :: vs, instnat_pred_tail :: cs) |=>* (i4 :: vs, cs) }.
Proof.
  eexists => n m i1 i2 i3 vs cs H H0 H1.
  evalpartial' evalpush.
  evalpartial' evalswap.
  evalpartial evalpair.
  evalpartial' evalexec.
  evalpartial (eval_instnat_repeat m).
  clear H1 i3.
  move: m n i1 i2 H H0; elim => [ | m IH] n i1 i2 H H0 /=.
  - evalpartial' evalswap.
    evalpartial evalpop.
    evalauto.
    by rewrite addn0.
  - evalpartial' evalpop; clear i2 H0.
    evalpartial' evalcopy.
    edestruct (instnat_succ_proof n i1) as [i2 [H0 H1]]; auto.
    evalpartial' H1; clear H1.
    evalpartial evalswap.
    replace (n + m.+1 - 1) with (n.+1 + m - 1) by ssromega.
    by apply IH; replace (n.+1 - 1) with n by ssromega.
Defined.

Notation instnat_pred_tail := (proj1_sig exists_instnat_pred_tail).
Notation instnat_pred_proof_tail := (proj2_sig exists_instnat_pred_tail).

Lemma exists_instnat_pred :
  { instnat_pred : inst |
    forall n i1 vs cs, instnat_spec n i1 ->
    exists i2 : inst, instnat_spec (n - 1) i2 /\
    (i1 :: vs, instnat_pred :: cs) |=>* (i2 :: vs, cs) }.
Proof.
  eexists => n i1 vs cs H.
  do 2 (evalpartial' evalpush; evalpartial' evalswap).
  edestruct (instnat_pred_proof_tail 0 n) as [i2 [H0 H1]]; eauto.
Defined.

Notation instnat_pred := (proj1_sig exists_instnat_pred).
Notation instnat_pred_proof := (proj2_sig exists_instnat_pred).

(*
instnat_sub:
  減算命令。
*)
Lemma exists_instnat_sub :
  { instnat_sub : inst |
    forall n m i1 i2 vs cs, instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (n - m) i3 /\
    (i2 :: i1 :: vs, instnat_sub :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  eexists => n m i1 i2 vs cs H H0.
  evalpartial' evalpush.
  evalpartial' evalswap.
  evalpartial' evalexec.
  evalpartial (eval_instnat_repeat m).
  clear i2 H0; move: m n i1 H; elim => [ | m IH] n i1 H /=.
  - evalauto.
    by rewrite subn0.
  - edestruct (instnat_pred_proof n i1) as [i2 [H1 H2]]; auto.
    evalpartial H2; clear H2.
    edestruct (IH (n - 1) i2) as [i3 [H2 H3]]; auto.
    evalpartial H3.
    evalauto.
    by rewrite (subnDA 1 n m).
Defined.

Notation instnat_sub := (proj1_sig exists_instnat_sub).
Notation instnat_sub_proof := (proj2_sig exists_instnat_sub).

(*
instnat_le:
  大小比較。
*)
Lemma exists_instnat_le :
  { instnat_le : inst |
    forall n m i1 i2 vs cs, instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instbool_spec (n <= m) i3 /\
    (i2 :: i1 :: vs, instnat_le :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  eexists => n m i1 i2 vs cs H H0.
  edestruct (instnat_sub_proof n m i1 i2) as [i3 [H1 H2]]; auto.
  evalpartial' H2; clear i1 i2 H H0 H2.
  edestruct (instnat_iszero_proof (n - m) i3) as [i1 [H H0]]; auto.
  evalpartial H0; clear i3 H0 H1.
  evalauto.
  by move: H; rewrite /leq; case: (n - m).
Defined.

Notation instnat_le := (proj1_sig exists_instnat_le).
Notation instnat_le_proof := (proj2_sig exists_instnat_le).

(*
instnat_divmod:
  割り算を行い、商と余りを計算する命令。
*)
Lemma exists_instnat_divmod_part :
  { instnat_divmod_part : inst |
    forall n m q i1 i2 i3 i4 vs cs,
    instnat_spec n i1 -> instnat_spec m.+1 i2 -> instnat_spec q i3 ->
    exists i1' : inst, instnat_spec (n - m.+1) i1' /\
    exists i3' : inst, instnat_spec q.+1 i3' /\
    (i4 :: i3 :: i2 :: i1 :: vs, instnat_divmod_part :: cs) |=>*
    (if m.+1 <= n
      then (i4 :: i3' :: i2 :: i1' :: vs, i4 :: cs)
      else (i1 :: i3 :: vs, cs))
  }.
Proof.
  eexists => n m q i1 i2 i3 i4 vs cs H H0 H1.
  evaltemplate' 4
    [:: instthole 3; instthole 2;
        instthole 0; instthole 1; instthole 2; instthole 3 ]
    (Nil instt).
  edestruct (instnat_le_proof m.+1 n i2 i1) as [i5 [H2 H3]]; auto.
  evalpartial' H3; clear H3.
  do 2 evalpartial' evalpush.
  evalpartial (evalexecif (m.+1 <= n) i5).
  clear i5 H2.
  case: (m < n).
  - evaltemplate' 4
      [:: instthole 2; instthole 3; instthole 0; instthole 1; instthole 2 ]
      (Nil instt).
    edestruct (instnat_sub_proof n m.+1 i1 i2) as [i1' [H2 H3]]; auto.
    evalpartial' H3; clear i1 H H0 H3.
    evaltemplate' 4
      [:: instthole 2; instthole 1; instthole 3; instthole 0 ]
      (Nil instt).
    edestruct (instnat_succ_proof q i3) as [i3' [H3 H4]]; auto.
    evalpartial' H4.
    clear i3 H1 H4.
    evalpartial' evalswap.
    evalpartial' evalcopy.
    evalpartial evalexec.
    by evalauto.
  - evalpartial' evalpop.
    evalpartial' evalswap.
    evalpartial' evalpop.
    evalpartial evalswap.
    evalauto; eauto.
Defined.

Lemma exists_instnat_divmod_tail :
  { instnat_divmod : inst |
    forall n m q i1 i2 i3 vs cs,
    instnat_spec n i1 -> instnat_spec m.+1 i2 -> instnat_spec q i3 ->
    exists i4 : inst, instnat_spec (q + n %/ m.+1) i4 /\
    exists i5 : inst, instnat_spec (n %% m.+1) i5 /\
    (i3 :: i2 :: i1 :: vs, instnat_divmod :: cs) |=>* (i5 :: i4 :: vs, cs) }.
Proof.
  eexists => n m q i1 i2 i3 vs cs H H0 H1.
  evalpartial' evalpush.
  evalpartial' evalcopy.
  evalpartial evalexec.
  move: n i1 H q i3 H1.
  refine (well_founded_ind well_founded_lt _ _).
  move => n IHn i1 H q i3 H1.
  edestruct (proj2_sig exists_instnat_divmod_part n m q i1 i2 i3)
    as [i4 [H2 [i5 [H3 H4]]]]; auto.
  evalpartial H4.
  clear H4.
  case: ifP => H4.
  - clear i1 i3 H H0 H1.
    have H5: (n > n - m.+1) by ssromega.
    edestruct (IHn (n - m.+1) H5 i4 H2 q.+1 i5 H3) as [i6 [H6 [i7 [H7 H8]]]].
    evalpartial H8.
    clear i2 i4 i5 H2 H3 H8 IHn.
    replace n with (1 * m.+1 + (n - m.+1)) by ssromega.
    evalauto.
    - by rewrite divnMDl // add1n -addSnnS.
    - by rewrite modnMDl.
  - clear i2 i4 i5 H0 H2 H3 IHn.
    evalauto.
    - rewrite leqNgt in H4.
      by rewrite (divn_small (negbFE H4)) addn0.
    - rewrite modn_small //; ssromega.
Defined.

Lemma exists_instnat_divmod :
  { instnat_divmod : inst |
    forall n m i1 i2 vs cs,
    instnat_spec n i1 -> instnat_spec m.+1 i2 ->
    exists i3 : inst, instnat_spec (n %/ m.+1) i3 /\
    exists i4 : inst, instnat_spec (n %% m.+1) i4 /\
    (i2 :: i1 :: vs, instnat_divmod :: cs) |=>* (i4 :: i3 :: vs, cs) }.
Proof.
  eexists => n m i1 i2 vs cs H H0.
  evalpartial' evalpush.
  edestruct (proj2_sig exists_instnat_divmod_tail n m 0 i1 i2)
    as [i3 [H1 [i4 [H2 H3]]]]; auto.
  evalpartial H3.
  by evalauto.
Defined.

Notation instnat_divmod := (proj1_sig exists_instnat_divmod).
Notation instnat_divmod_proof := (proj2_sig exists_instnat_divmod).

(*
instnat_gcd:
  ユークリッドの互除法によって最大公約数を計算する。
*)
Lemma exists_instnat_gcd_iter :
  { instnat_gcd_iter : inst |
    forall n m i1 i2 i3 vs cs,
    instnat_spec n i1 -> instnat_spec m i2 ->
    exists i4 : inst, instnat_spec (n %% m) i4 /\
    (i3 :: i2 :: i1 :: vs, instnat_gcd_iter :: cs) |=>*
    (if eqn 0 m then (i1 :: vs, cs) else (i3 :: i4 :: i2 :: vs, i3 :: cs)) }.
Proof.
  eexists => n m i1 i2 i3 vs cs H H0.
  evalpartial' evalswap.
  evalpartial' evalcopy.
  edestruct (instnat_iszero_proof m i2) as [i4 [H1 H2]]; auto.
  evalpartial' H2; clear H2.
  do 2 evalpartial' evalpush.
  evalpartial (evalexecif (eqn 0 m) i4).
  move: m i2 i4 H0 H1.
  case => /= [ | m] i2 _ H0 _.
  - evalpartial' evalpop.
    evalpartial evalpop.
    by evalauto.
  - evaltemplate' 3
      [:: instthole 0; instthole 2; instthole 0; instthole 1]
      (Nil instt).
    edestruct (instnat_divmod_proof n m i1 i2) as [i4 [H1 [i5 [H2 H3]]]]; auto.
    evalpartial' H3; clear H3.
    evaltemplate 4 [:: instthole 3; instthole 0; instthole 2] [:: instthole 3].
    by evalauto.
Defined.

Lemma exists_instnat_gcd :
  { instnat_gcd : inst |
    forall n m i1 i2 vs cs,
    instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (gcdn n m) i3 /\
    (i2 :: i1 :: vs, instnat_gcd :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  eexists => n m i1 i2 vs cs H H0.
  evalpartial' evalpush.
  evalpartial' evalcopy.
  evalpartial evalexec.
  move: i1 i2 vs cs H H0.
  set m' := m.
  rewrite -/(n, m).1 -/(n, m').2.
  subst m'.
  move: (n, m); clear.
  refine (well_founded_ind (well_founded_ltof
    (fun p => (if p.1 <= p.2 then 1 else 0) + p.1 + p.2)) _ _).
  rewrite /ltof.
  case => n m /= IH i1 i2 vs cs H H0.
  edestruct (proj2_sig exists_instnat_gcd_iter n m i1 i2) as [i3 [H1 H2]]; auto.
  evalpartial H2; clear H2.
  move: m IH H0 H1.
  rewrite (lock exists_instnat_gcd_iter); case => /=.
  - move => IH H0 H1.
    evalauto.
    by rewrite gcdn0.
  - move => m IH H0 H1.
    edestruct (IH (m.+1, n %% m.+1)) as [i4 [H2 H3]] => /=.
    - clear; case: ifP.
      - move: (ltn_pmod n (ltn0Sn m)) => H H0.
        ssromega.
      - case: ifP => H _.
        - rewrite add0n -addnA add1n -addSn -addnS (addnC n) leq_add2l.
          apply leq_mod.
        - rewrite leqNgt in H.
          move: (negbFE H) => H0.
          have H1: n = 1 * m.+1 + (n - m.+1) by ssromega.
          rewrite !add0n (addnC n) ltn_add2l {1}H1 modnMDl.
          apply (leq_ltn_trans (leq_mod (n - m.+1) m.+1)).
          ssromega.
    - apply H0.
    - apply H1.
    - evalpartial H3.
      evalauto.
      move: H2 => /=.
      by rewrite gcdn_modr gcdnC.
Defined.

Notation instnat_gcd := (proj1_sig exists_instnat_gcd).
Notation instnat_gcd_proof := (proj2_sig exists_instnat_gcd).
