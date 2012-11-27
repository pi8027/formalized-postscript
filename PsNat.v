Require Import
  Arith.Compare_dec Arith.Even Arith.Peano_dec
  Relations.Relations Lists.List Program.Basics Program.Syntax
  ssreflect Common PsCore PsTemplate PsBool.

(*
instnat_spec:
  自然数の仕様。
*)
Definition instnat_spec (n : nat) (i1 : inst) : Prop :=
  forall i2 vs cs,
  (i2 :: vs, i1 :: cs) |=>* (instseqc_replicate n i2 :: vs, cs).

(*
exists_instnat:
  自然数の仕様を満たす命令。
*)
Lemma exists_instnat : forall n, { i : inst | instnat_spec n i }.
Proof.
  elim=> [| n [i H]] ; eexists=> i2 vs cs.
  - simpl.
    evalpartial' evalpop.
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
    (i1 :: vs, i2 :: instnat_repeat :: cs) |=>* (vs, replicate n i1 ++ cs) }.
Proof.
  eexists=> n i1 i2 vs cs H.
  evalpartial H.
  evalpartial evalexec.
  apply evalseqc_replicate.
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
  move=> n m i1 H0 H1.
  have: (([], replicate n instpop) |=>* ([], replicate m instpop) \/
      ([], replicate m instpop) |=>* ([], replicate n instpop)).
    apply (eval_semi_uniqueness ([instpop], [i1 ; instexec])).
    - evalpartial (eval_instnat_repeat n).
      rtcrefl.
      apply app_nil_r.
    - evalpartial (eval_instnat_repeat m).
      rtcrefl.
      apply app_nil_r.
  clear=> H.
  have: (replicate n instpop = replicate m instpop).
    by destruct H, n, m ; inversion H ; (inversion H0 || simpl ; f_equal).
  clear ; move: n m ; elim=> [ | n IHn] ; case=> [ | m] H ; inversion H ; auto.
Qed.

(*
instnat_succ:
  後者関数。
*)
Lemma exists_instnat_succ :
  { instnat_succ : inst |
    forall n i1 vs cs, instnat_spec n i1 ->
    exists i2 : inst, instnat_spec (S n) i2 /\
    (i1 :: vs, instnat_succ :: cs) |=>* (i2 :: vs, cs) }.
Proof.
  eexists=> n i1 vs cs H ; eexists ; split.
  - move=> i2 vs' cs'.
    evalpartial' evalcopy.
    evalpartial' H.
    apply evalsnoc.
  - evaltemplate 1
      [insttpair insttcopy
        (insttpair (instthole 0) (insttpair insttswap insttcons))]
      (@nil instt).
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
    exists i3 : inst, instnat_spec (Plus.tail_plus n m) i3 /\
    (i2 :: i1 :: vs, instnat_add_tail :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  eexists=> n m i1 i2 vs cs H H0.
  evalpartial' evalswap.
  evalpartial' evalpush.
  evalpartial' evalswap.
  evalpartial' evalexec.
  evalpartial (eval_instnat_repeat n).
  clear H i1 ; move: n m i2 H0 ; elim=> [ | n IH] m i1 H ; simpl.
  - by evalauto.
  - edestruct (instnat_succ_proof m i1) as [i2 [H1 H2]] ; auto.
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
  rewrite Plus.plus_tail_plus.
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
    exists i3 : inst, instnat_spec (Mult.tail_mult n m) i3 /\
    (i2 :: i1 :: vs, instnat_mult_tail :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  rewrite /Mult.tail_mult.
  move: (0) (instnat 0) (eval_instnat 0) => o i1 H.
  eexists=> n m i2 i3 vs cs H0 H1.
  do 2 evalpartial' evalpush.
  evaltemplate' 4
    [insttpair (insttpush (instthole 2)) (instthole 1); instthole 0]
    [instthole 3].
  evalpartial (eval_instnat_repeat n).
  clear i2 H0.
  move: n o i1 i3 H H1 ; elim=> [ | n IH] o i1 i2 H H0 ; simpl.
  - evalauto.
    eauto.
  - evalauto.
    evalpartial' evalswap.
    edestruct (instnat_add_proof_tail m o i2 i1) as [i3 [H1 H2]] ; auto.
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
  rewrite Mult.mult_tail_mult.
  apply instnat_mult_proof_tail.
Defined.

Notation instnat_mult_proof := (proj2_sig exists_instnat_mult).

(*
instnat_even:
  偶奇判定の命令。
*)
Lemma exists_instnat_even_tail :
  { instnat_even_tail : inst |
    forall b n i1 i2 vs cs, instbool_spec b i1 -> instnat_spec n i2 ->
    exists i3 : inst,
    instbool_spec (if even_odd_dec n then b else negb b)%GEN_IF i3 /\
    (i2 :: i1 :: vs, instnat_even_tail :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  eexists=> b n i1 i2 vs cs H H0.
  evalpartial' evalpush.
  evalpartial' evalswap.
  evalpartial' evalexec.
  evalpartial (eval_instnat_repeat n).
  clear H0 i2.
  move: n b i1 H ; elim=> [ | n IH] b i1 H.
  - by evalauto.
  - edestruct (evalnot b i1) as [i2 [H0 H1]] ; auto.
    evalpartial H1 ; clear i1 H H1.
    edestruct (IH (negb b) i2) as [i1 [H H1]] ; auto.
    evalpartial H1 ; clear IH H0 H1.
    evalauto.
    rewrite -Bool.negb_involutive_reverse in H.
    destruct (even_odd_dec n), (even_odd_dec (S n)) ; auto.
    by inversion e0 ; apply False_ind, (not_even_and_odd n).
    by inversion o0 ; apply False_ind, (not_even_and_odd n).
Defined.

Notation instnat_even_tail := (proj1_sig exists_instnat_even_tail).
Notation instnat_even_proof_tail := (proj2_sig exists_instnat_even_tail).

Lemma exists_instnat_even :
  { instnat_even : inst |
    forall n i1 vs cs, instnat_spec n i1 ->
    exists i2 : inst,
    instbool_spec (if even_odd_dec n then true else false)%GEN_IF i2 /\
    (i1 :: vs, instnat_even :: cs) |=>* (i2 :: vs, cs) }.
Proof.
  eexists=> n i1 vs cs H.
  evalpartial' evalpush.
  evalpartial' evalswap.
  edestruct (instnat_even_proof_tail true n) as [i2 [H0 H1]] ; eauto.
Defined.

Notation instnat_even := (proj1_sig exists_instnat_even).
Notation instnat_even_proof := (proj2_sig exists_instnat_even).

(*
instnat_iszero:
  ゼロとの比較をする命令。
*)
Lemma exists_instnat_iszero_tail :
  { instnat_iszero_tail : inst |
    forall n i1 i2 vs cs, instnat_spec n i2 ->
    exists i3 : inst, instfalse_spec i3 /\
    (i2 :: i1 :: vs, instnat_iszero_tail :: cs) |=>*
    ((if eq_nat_dec 0 n then i1 else i3)%GEN_IF :: vs, cs) }.
Proof.
  eexists=> n i1 i2 vs cs H ; exists instfalse ; split.
  - auto.
  - evalpartial' evalpush.
    evalpartial' evalswap.
    evalpartial' evalexec.
    evalpartial (eval_instnat_repeat n).
    clear i2 H ; move: n i1 ; elim=> [ | n IH] i1.
    - evalauto.
    - simpl.
      evalpartial' evalpop.
      evalpartial evalpush.
      move: IH ; case (eq_nat_dec 0 n) ; auto.
Defined.

Notation instnat_iszero_tail := (proj1_sig exists_instnat_iszero_tail).
Notation instnat_iszero_proof_tail := (proj2_sig exists_instnat_iszero_tail).

Lemma exists_instnat_iszero :
  { instnat_iszero : inst |
    forall n i1 vs cs, instnat_spec n i1 ->
    exists i2 : inst,
    instbool_spec (if eq_nat_dec 0 n then true else false)%GEN_IF i2 /\
    (i1 :: vs, instnat_iszero :: cs) |=>* (i2 :: vs, cs) }.
Proof.
  eexists=> n i1 vs cs H.
  evalpartial' evalpush.
  evalpartial' evalswap.
  edestruct instnat_iszero_proof_tail as [i2 [H0 H1]] ; first apply H.
  evalpartial H1.
  case (eq_nat_dec 0 n) => H2 ; evalauto ; eauto.
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
  eexists=> n m i1 i2 i3 vs cs H H0 H1.
  evalpartial' evalpush.
  evalpartial' evalswap.
  evalpartial evalpair.
  evalpartial' evalexec.
  evalpartial (eval_instnat_repeat m).
  clear H1 i3.
  move: m n i1 i2 H H0 ; elim=> [ | m IH] n i1 i2 H H0.
  - evalpartial' evalswap.
    evalpartial evalpop.
    evalauto.
    by replace (n + 0 - 1) with (n - 1) by omega.
  - simpl.
    evalpartial' evalpop ; clear i2 H0.
    evalpartial' evalcopy.
    edestruct (instnat_succ_proof n i1) as [i2 [H0 H1]] ; auto.
    evalpartial' H1 ; clear H1.
    evalpartial evalswap.
    replace (n + S m - 1) with (S n + m - 1) by omega.
    by apply IH ; replace (S n - 1) with n by omega.
Defined.

Notation instnat_pred_tail := (proj1_sig exists_instnat_pred_tail).
Notation instnat_pred_proof_tail := (proj2_sig exists_instnat_pred_tail).

Lemma exists_instnat_pred :
  { instnat_pred : inst |
    forall n i1 vs cs, instnat_spec n i1 ->
    exists i2 : inst, instnat_spec (n - 1) i2 /\
    (i1 :: vs, instnat_pred :: cs) |=>* (i2 :: vs, cs) }.
Proof.
  eexists=> n i1 vs cs H.
  do 2 (evalpartial' evalpush ; evalpartial' evalswap).
  edestruct (instnat_pred_proof_tail 0 n) as [i2 [H0 H1]] ; eauto.
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
  eexists=> n m i1 i2 vs cs H H0.
  evalpartial' evalpush.
  evalpartial' evalswap.
  evalpartial' evalexec.
  evalpartial (eval_instnat_repeat m).
  clear i2 H0 ; move: m n i1 H ; elim=> [ | m IH] n i1 H.
  - evalauto.
    by replace (n - 0) with n by omega.
  - simpl.
    edestruct (instnat_pred_proof n i1) as [i2 [H1 H2]] ; auto.
    evalpartial H2 ; clear H2.
    edestruct (IH (n - 1) i2) as [i3 [H2 H3]] ; auto.
    evalpartial H3.
    evalauto.
    by replace (n - S m) with (n - 1 - m) by omega.
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
    exists i3 : inst,
    instbool_spec (if le_dec n m then true else false)%GEN_IF i3 /\
    (i2 :: i1 :: vs, instnat_le :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  eexists=> n m i1 i2 vs cs H H0.
  edestruct (instnat_sub_proof n m i1 i2) as [i3 [H1 H2]] ; auto.
  evalpartial' H2 ; clear i1 i2 H H0 H2.
  edestruct (instnat_iszero_proof (n - m) i3) as [i1 [H H0]] ; auto.
  evalpartial H0 ; clear i3 H0 H1.
  evalauto.
  move: H ; case (le_dec n m) => H.
  by replace (n - m) with 0 by omega.
  by replace (n - m) with (S (n - m - 1)) by omega.
Defined.

Notation instnat_le := (proj1_sig exists_instnat_le).
Notation instnat_le_proof := (proj2_sig exists_instnat_le).
