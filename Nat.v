Require Import
  Coq.Program.Wf
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq MathComp.div
  FormalPS.stdlib_ext FormalPS.Core FormalPS.Template FormalPS.Bool.

Set Implicit Arguments.

Set Printing Width 51.

(*
instnat_spec:
  自然数の仕様。
*)
Definition instnat_spec (n : nat) (i1 : inst) : Prop :=
  forall i2 vs cs, (i2 :: vs, i1 :: cs) |=>* (instnseqc n i2 :: vs, cs).

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
inst_repeatn:
  繰り返しの命令。
*)
Lemma exists_inst_repeatn :
  { inst_repeatn : inst |
    forall n i1 i2 vs cs, instnat_spec n i2 ->
    (i1 :: vs, i2 :: inst_repeatn :: cs) |=>* (vs, nseq n i1 ++ cs) }.
Proof.
  eexists => n i1 i2 vs cs H.
  evalpartial H.
  evalpartial evalexec.
  apply evalnseqc.
Defined.

Notation inst_repeatn := (proj1_sig exists_inst_repeatn).
Notation eval_inst_repeatn := (proj2_sig exists_inst_repeatn).

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
  rewrite -(size_nseq n instpop) -(size_nseq m instpop); f_equal.
  have: (([::], nseq n instpop) |=>* ([::], nseq m instpop) \/
    ([::], nseq m instpop) |=>* ([::], nseq n instpop))
    by apply (@eval_semi_uniqueness ([:: instpop], [:: i1; instexec]));
      rewrite -[nseq _ _]cats0; apply eval_inst_repeatn.
  by case: n m {H0 H1} => [| n]; case => [| m]; case => H //=;
    inversion H; try inversion H0.
Qed.

(*
inst_succn:
  後者関数。
*)
Lemma exists_inst_succn :
  { inst_succn : inst |
    forall n i1 vs cs, instnat_spec n i1 ->
    exists i2 : inst, instnat_spec n.+1 i2 /\
    (i1 :: vs, inst_succn :: cs) |=>* (i2 :: vs, cs) }.
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

Notation inst_succn := (proj1_sig exists_inst_succn).
Notation inst_succn_proof := (proj2_sig exists_inst_succn).

(*
inst_addn:
  加算命令。
*)
Lemma exists_inst_addn :
  { inst_addn : inst |
    forall n m i1 i2 vs cs, instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (n + m) i3 /\
    (i2 :: i1 :: vs, inst_addn :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  eexists => n m i1 i2 vs cs H H0.
  evalpartial' evalswap.
  evalpartial' evalpush.
  evalpartial' evalswap.
  evalpartial' evalexec.
  evalpartial (eval_inst_repeatn n).
  elim: n m i2 H0 {i1 H} => [ | n IH] m i1 H /=.
  - by evalauto.
  - edestruct (inst_succn_proof m i1) as [i2 [H1 H2]]; auto.
    evalpartial H2.
    by rewrite addSnnS; apply IH.
Defined.

Notation inst_addn := (proj1_sig exists_inst_addn).
Notation inst_addn_proof := (proj2_sig exists_inst_addn).

(*
inst_muln:
  乗算命令。
*)

Lemma exists_inst_muln_tail :
  { inst_muln_tail : inst |
    forall n m i1 i2 vs cs, instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (NatTrec.add_mul n m 0) i3 /\
    (i2 :: i1 :: vs, inst_muln_tail :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  move: (0) (instnat 0) (eval_instnat 0) => o i1 H.
  eexists => n m i2 i3 vs cs H0 H1.
  do 2 evalpartial' evalpush.
  evaltemplate' 4
    [:: insttpair (insttpush (instthole 2)) (instthole 1); instthole 0]
    [:: instthole 3].
  evalpartial (eval_inst_repeatn n).
  elim: n o i1 i3 H H1 {i2 H0} => [ | n IH] o i1 i2 H H0 /=.
  - evalauto; apply H.
  - evalauto.
    evalpartial' evalswap.
    edestruct (@inst_addn_proof m o i2 i1) as [i3 [H1 H2]]; auto.
    evalpartial H2.
    rewrite NatTrec.addE.
    auto.
Defined.

Notation inst_muln := (proj1_sig exists_inst_muln_tail).
Notation inst_muln_proof_tail := (proj2_sig exists_inst_muln_tail).

Lemma inst_muln_proof :
  forall n m i1 i2 vs cs, instnat_spec n i1 -> instnat_spec m i2 ->
  exists i3 : inst, instnat_spec (n * m) i3 /\
  (i2 :: i1 :: vs, inst_muln :: cs) |=>* (i3 :: vs, cs).
Proof.
  move => n m.
  replace (n * m) with (NatTrec.add_mul n m 0) by ssromega.
  apply inst_muln_proof_tail.
Defined.

(*
inst_even:
  偶奇判定の命令。
*)
Lemma exists_inst_even_tail :
  { inst_even_tail : inst |
    forall (b : bool) n i1 i2 vs cs, instbool_spec b i1 -> instnat_spec n i2 ->
    exists i3 : inst, instbool_spec (if odd n then ~~ b else b) i3 /\
    (i2 :: i1 :: vs, inst_even_tail :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  eexists => b n i1 i2 vs cs H H0.
  evalpartial' evalpush.
  evalpartial' evalswap.
  evalpartial' evalexec.
  evalpartial (eval_inst_repeatn n).
  elim: n b i1 H {i2 H0} => [ | n IH] b i1 H.
  - by evalauto.
  - edestruct (evalnot b i1) as [i2 [H0 H1]]; auto.
    evalpartial H1; clear i1 H H1.
    edestruct (IH (negb b) i2) as [i1 [H H1]]; auto.
    evalpartial H1; clear IH H0 H1.
    evalauto.
    move: H => //=.
    case: b; case: (odd n) => //=.
Defined.

Notation inst_even_tail := (proj1_sig exists_inst_even_tail).
Notation inst_even_proof_tail := (proj2_sig exists_inst_even_tail).

Lemma exists_inst_even :
  { inst_even : inst |
    forall n i1 vs cs, instnat_spec n i1 ->
    exists i2 : inst, instbool_spec (~~ odd n) i2 /\
    (i1 :: vs, inst_even :: cs) |=>* (i2 :: vs, cs) }.
Proof.
  eexists => n i1 vs cs H.
  evalpartial' evalpush.
  evalpartial' evalswap.
  edestruct (inst_even_proof_tail true n) as [i2 [H0 H1]]; eauto.
Defined.

Notation inst_even := (proj1_sig exists_inst_even).
Notation inst_even_proof := (proj2_sig exists_inst_even).

(*
inst_iszero:
  ゼロとの比較をする命令。
*)
Lemma exists_inst_iszero :
  { inst_iszero : inst |
    forall n i1 vs cs, instnat_spec n i1 ->
    exists i2 : inst,
    instbool_spec (n == 0) i2 /\
    (i1 :: vs, inst_iszero :: cs) |=>* (i2 :: vs, cs) }.
Proof.
  eexists => n i1 vs cs H.
  exists (instbool (n == 0)); split.
  - case (n == 0); auto.
  - evalpartial' (evalpush (instbool true)).
    evalpartial' evalswap.
    evalpartial' evalpush.
    evalpartial' evalswap.
    evalpartial' evalexec.
    evalpartial (eval_inst_repeatn n).
    case: n {i1 H} => //=; first evalauto.
    move => n.
    evalpartial' evalpop.
    evalpartial (evalpush (instbool false)).
    elim: n => [| n IHn] /=; evalauto.
    apply IHn.
Defined.

Notation inst_iszero := (proj1_sig exists_inst_iszero).
Notation inst_iszero_proof := (proj2_sig exists_inst_iszero).

(*
inst_predn:
  前者関数。ただし元の数が0である場合の結果は0である。
*)
Lemma exists_inst_predn_tail :
  { inst_predn_tail : inst |
    forall n m i1 i2 i3 vs cs,
    instnat_spec n i1 -> instnat_spec (n - 1) i2 -> instnat_spec m i3 ->
    exists i4 : inst, instnat_spec (n + m - 1) i4 /\
    (i3 :: i2 :: i1 :: vs, inst_predn_tail :: cs) |=>* (i4 :: vs, cs) }.
Proof.
  eexists => n m i1 i2 i3 vs cs H H0 H1.
  evalpartial' evalpush.
  evalpartial' evalswap.
  evalpartial evalpair.
  evalpartial' evalexec.
  evalpartial (eval_inst_repeatn m).
  elim: m n i1 i2 H H0 {i3 H1} => [ | m IH] n i1 i2 H H0 /=.
  - evalpartial' evalswap.
    evalpartial evalpop.
    evalauto.
    by rewrite addn0.
  - evalpartial' evalpop; clear i2 H0.
    evalpartial' evalcopy.
    edestruct (inst_succn_proof n i1) as [i2 [H0 H1]]; auto.
    evalpartial' H1; clear H1.
    evalpartial evalswap.
    replace (n + m.+1 - 1) with (n.+1 + m - 1) by ssromega.
    by apply IH; replace (n.+1 - 1) with n by ssromega.
Defined.

Notation inst_predn_tail := (proj1_sig exists_inst_predn_tail).
Notation inst_predn_proof_tail := (proj2_sig exists_inst_predn_tail).

Lemma exists_inst_predn :
  { inst_predn : inst |
    forall n i1 vs cs, instnat_spec n i1 ->
    exists i2 : inst, instnat_spec (n - 1) i2 /\
    (i1 :: vs, inst_predn :: cs) |=>* (i2 :: vs, cs) }.
Proof.
  eexists => n i1 vs cs H.
  do 2 (evalpartial' evalpush; evalpartial' evalswap).
  edestruct (inst_predn_proof_tail 0 n) as [i2 [H0 H1]]; eauto.
Defined.

Notation inst_predn := (proj1_sig exists_inst_predn).
Notation inst_predn_proof := (proj2_sig exists_inst_predn).

(*
inst_subn:
  減算命令。
*)
Lemma exists_inst_subn :
  { inst_subn : inst |
    forall n m i1 i2 vs cs, instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (n - m) i3 /\
    (i2 :: i1 :: vs, inst_subn :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  eexists => n m i1 i2 vs cs H H0.
  evalpartial' evalpush.
  evalpartial' evalswap.
  evalpartial' evalexec.
  evalpartial (eval_inst_repeatn m).
  elim: m n i1 H {i2 H0} => [ | m IH] n i1 H /=.
  - evalauto.
    by rewrite subn0.
  - edestruct (inst_predn_proof n i1) as [i2 [H1 H2]]; auto.
    evalpartial H2; clear H2.
    edestruct (IH (n - 1) i2) as [i3 [H2 H3]]; auto.
    evalpartial H3.
    evalauto.
    by rewrite (subnDA 1 n m).
Defined.

Notation inst_subn := (proj1_sig exists_inst_subn).
Notation inst_subn_proof := (proj2_sig exists_inst_subn).

(*
inst_leqn:
  大小比較。
*)
Lemma exists_inst_leqn :
  { inst_leqn : inst |
    forall n m i1 i2 vs cs, instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instbool_spec (n <= m) i3 /\
    (i2 :: i1 :: vs, inst_leqn :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  eexists => n m i1 i2 vs cs H H0.
  edestruct (inst_subn_proof n m i1 i2) as [i3 [H1 H2]]; auto.
  evalpartial' H2; clear i1 i2 H H0 H2.
  edestruct (inst_iszero_proof (n - m) i3) as [i1 [H H0]]; auto.
  evalpartial H0; clear i3 H0 H1.
  evalauto.
  by move: H; rewrite /leq; case: (n - m).
Defined.

Notation inst_leqn := (proj1_sig exists_inst_leqn).
Notation inst_leqn_proof := (proj2_sig exists_inst_leqn).

(*
inst_divmodn:
  割り算を行い、商と余りを計算する命令。
*)
Lemma exists_inst_divmodn_part :
  { inst_divmodn_part : inst |
    forall n m q i1 i2 i3 i4 vs cs,
    instnat_spec n i1 -> instnat_spec m.+1 i2 -> instnat_spec q i3 ->
    exists i1' : inst, instnat_spec (n - m.+1) i1' /\
    exists i3' : inst, instnat_spec q.+1 i3' /\
    (i4 :: i3 :: i2 :: i1 :: vs, inst_divmodn_part :: cs) |=>*
    (if m < n
      then (i4 :: i3' :: i2 :: i1' :: vs, i4 :: cs)
      else (i1 :: i3 :: vs, cs))
  }.
Proof.
  eexists => n m q i1 i2 i3 i4 vs cs H H0 H1.
  evaltemplate' 4
    [:: instthole 3; instthole 2;
        instthole 0; instthole 1; instthole 2; instthole 3 ]
    (Nil instt).
  edestruct (inst_leqn_proof m.+1 n i2 i1) as [i5 [H2 H3]]; auto.
  evalpartial' H3; clear H3.
  do 2 evalpartial' evalpush.
  evalpartial (evalexecif (m.+1 <= n) i5).
  clear i5 H2.
  case: (m < n).
  - evaltemplate' 4
      [:: instthole 2; instthole 3; instthole 0; instthole 1; instthole 2 ]
      (Nil instt).
    edestruct (inst_subn_proof n m.+1 i1 i2) as [i1' [H2 H3]]; auto.
    evalpartial' H3; clear i1 H H0 H3.
    evaltemplate' 4
      [:: instthole 2; instthole 1; instthole 3; instthole 0 ]
      (Nil instt).
    edestruct (inst_succn_proof q i3) as [i3' [H3 H4]]; auto.
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

Lemma exists_inst_divmodn_tail :
  { inst_divmodn : inst |
    forall n m q i1 i2 i3 vs cs,
    instnat_spec n i1 -> instnat_spec m.+1 i2 -> instnat_spec q i3 ->
    exists i4 : inst, instnat_spec (q + n %/ m.+1) i4 /\
    exists i5 : inst, instnat_spec (n %% m.+1) i5 /\
    (i3 :: i2 :: i1 :: vs, inst_divmodn :: cs) |=>* (i5 :: i4 :: vs, cs) }.
Proof.
  eexists => n m q i1 i2 i3 vs cs H H0 H1.
  evalpartial' evalpush.
  evalpartial' evalcopy.
  evalpartial evalexec.
  move: n i1 H q i3 H1.
  refine (well_founded_ind well_founded_lt _ _).
  move => n IHn i1 H q i3 H1.
  edestruct (proj2_sig exists_inst_divmodn_part n m q i1 i2 i3)
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

Lemma exists_inst_divmodn :
  { inst_divmodn : inst |
    forall n m i1 i2 vs cs,
    instnat_spec n i1 -> instnat_spec m.+1 i2 ->
    exists i3 : inst, instnat_spec (n %/ m.+1) i3 /\
    exists i4 : inst, instnat_spec (n %% m.+1) i4 /\
    (i2 :: i1 :: vs, inst_divmodn :: cs) |=>* (i4 :: i3 :: vs, cs) }.
Proof.
  eexists => n m i1 i2 vs cs H H0.
  evalpartial' evalpush.
  edestruct (proj2_sig exists_inst_divmodn_tail n m 0 i1 i2)
    as [i3 [H1 [i4 [H2 H3]]]]; auto.
  evalpartial H3.
  by evalauto.
Defined.

Notation inst_divmodn := (proj1_sig exists_inst_divmodn).
Notation inst_divmodn_proof := (proj2_sig exists_inst_divmodn).

(*
inst_gcdn:
  ユークリッドの互除法によって最大公約数を計算する。
*)
Lemma exists_inst_gcdn_iter :
  { inst_gcdn_iter : inst |
    forall n m i1 i2 i3 vs cs,
    instnat_spec n i1 -> instnat_spec m i2 ->
    exists i4 : inst, instnat_spec (n %% m) i4 /\
    (i3 :: i2 :: i1 :: vs, inst_gcdn_iter :: cs) |=>*
    (if m == 0 then (i1 :: vs, cs) else (i3 :: i4 :: i2 :: vs, i3 :: cs)) }.
Proof.
  eexists => n m i1 i2 i3 vs cs H H0.
  evalpartial' evalswap.
  evalpartial' evalcopy.
  edestruct (inst_iszero_proof m i2) as [i4 [H1 H2]]; auto.
  evalpartial' H2; clear H2.
  do 2 evalpartial' evalpush.
  evalpartial (evalexecif (m == 0) i4).
  move: m i2 i4 H0 H1.
  case => /= [ | m] i2 _ H0 _.
  - evalpartial' evalpop.
    evalpartial evalpop.
    by evalauto.
  - evaltemplate' 3
      [:: instthole 0; instthole 2; instthole 0; instthole 1]
      (Nil instt).
    edestruct (inst_divmodn_proof n m i1 i2) as [i4 [H1 [i5 [H2 H3]]]]; auto.
    evalpartial' H3; clear H3.
    evaltemplate 4 [:: instthole 3; instthole 0; instthole 2] [:: instthole 3].
    by evalauto.
Defined.

Lemma exists_inst_gcdn :
  { inst_gcdn : inst |
    forall n m i1 i2 vs cs,
    instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (gcdn n m) i3 /\
    (i2 :: i1 :: vs, inst_gcdn :: cs) |=>* (i3 :: vs, cs) }.
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
  refine (well_founded_ind (measure_wf well_founded_lt
    (fun p => (if p.1 <= p.2 then 1 else 0) + p.1 + p.2)) _ _).
  rewrite /MR; case => n m /= IH i1 i2 vs cs H H0.
  edestruct (proj2_sig exists_inst_gcdn_iter n m i1 i2) as [i3 [H1 H2]]; auto.
  evalpartial H2; clear H2.
  move: m IH H0 H1.
  rewrite (lock exists_inst_gcdn_iter); case => /=.
  - move => IH H0 H1.
    evalauto.
    by rewrite gcdn0.
  - move => m IH H0 H1.
    edestruct (IH (m.+1, n %% m.+1)) as [i4 [H2 H3]] => /=; try eassumption.
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
    - evalpartial H3.
      evalauto.
      move: H2 => /=.
      by rewrite gcdn_modr gcdnC.
Defined.

Notation inst_gcdn := (proj1_sig exists_inst_gcdn).
Notation inst_gcdn_proof := (proj2_sig exists_inst_gcdn).
