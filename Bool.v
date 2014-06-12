Require Import
  Coq.Bool.Sumbool Ssreflect.ssreflect Ssreflect.seq
  FormalPS.stdlib_ext FormalPS.Core.

Set Implicit Arguments.

(*
instfalse_spec, insttrue_spec, instbool_spec:
  ブール値の仕様。
  false は何もしない命令である。
  true は swap と同様の振舞いをする命令である。
*)
Definition instbool_spec (b : bool) (i1 : inst) : Prop :=
  forall i2 i3 vs cs,
    (i3 :: i2 :: vs, i1 :: cs) |=>*
    ((if b then [:: i2; i3] else [:: i3; i2]) ++ vs, cs).

(*
exists_false, exists_true:
  ブール値の仕様を満たす命令。
*)
Lemma exists_bool b : {instbool : inst | instbool_spec b instbool }.
Proof.
  case: b; eexists => i1 i2 vs cs /=.
  - evalpartial evalswap; evalauto.
  - evalpartial evalnop; evalauto.
Defined.

Notation instbool b := (proj1_sig (exists_bool b)).
Notation evalbool b := (proj2_sig (exists_bool b)).

Hint Resolve ((fun b => evalbool b) :
  forall b, instbool_spec b (instbool b)).

(*
instbool_eqmap:
*)
Lemma instbool_eqmap :
  forall b1 b2 i, instbool_spec b1 i -> instbool_spec b2 i -> b1 = b2.
Proof.
  move => b1 b2 i H H0.
  have: let f b := if b then [:: instpop; instcopy]
                        else [:: instcopy; instpop] in
        let s1 := (f b1, [::]) in
        let s2 := (f b2, [::]) in s1 |=>* s2 \/ s2 |=>* s1
    by apply (@eval_semi_uniqueness ([:: instcopy; instpop], [:: i]));
      [evalpartial H | evalpartial H0]; rewrite cats0; evalauto.
  by move: b1 b2 {H H0} => [] [] [] //= H; inversion H; inversion H0.
Qed.

(*
exists_not:
  not 命令。
*)
Lemma exists_not :
  { instnot : inst |
    forall (b : bool) i1 vs cs, instbool_spec b i1 ->
    exists i2 : inst, instbool_spec (negb b) i2 /\
    (i1 :: vs, instnot :: cs) |=>* (i2 :: vs, cs) }.
Proof.
  eexists => b i1 vs cs H.
  evalpartial' (evalpush instswap).
  evalpartial evalcons.
  evalauto.
  case: b H => H i2 i3 vs' cs'; evalauto; evalpartial H; evalauto.
Defined.

Notation instnot := (proj1_sig exists_not).
Notation evalnot := (proj2_sig exists_not).

(*
exists_if, exists_execif:
  ブール値による条件分岐の命令。
  exists_if は、ブール値によってスタックの先頭にある2つの値のうちどちらを残すか
  を切り替える。後者(exists_execif)は、exists_if によって選択される命令を実行す
  る。
*)
Lemma exists_if :
  { instif : inst |
    forall (b : bool) i1 i2 i3 vs cs, instbool_spec b i1 ->
    (i3 :: i2 :: i1 :: vs, instif :: cs) |=>*
    ((if b then i2 else i3) :: vs, cs) }.
Proof.
  eexists => b i1 i2 i3 vs cs H.
  evalpartial' evalquote.
  evalpartial' evalswap.
  evalpartial' evalquote.
  evalpartial' evalcons.
  evalpartial' evalsnoc.
  evalpartial' evalexec.
  evalauto.
  case: b H => H; evalpartial H => /=; evalpartial evalpop; evalauto.
Defined.

Notation instif := (proj1_sig exists_if).
Notation evalif := (proj2_sig exists_if).

Lemma exists_execif :
  { instexecif : inst |
    forall (b : bool) i1 i2 i3 vs cs, instbool_spec b i1 ->
    (i3 :: i2 :: i1 :: vs, instexecif :: cs) |=>*
    (vs, (if b then i2 else i3) :: cs) }.
Proof.
  eexists => b i1 i2 i3 vs cs H.
  evalpartial' (evalif b).
  evalpartial evalexec.
  evalauto.
Defined.

Notation instexecif := (proj1_sig exists_execif).
Notation evalexecif := (proj2_sig exists_execif).

(*
instxor:
  xor 命令。
*)
Definition instxor : inst := instcons.

Lemma evalxor :
  forall (b1 b2 : bool) i1 i2 vs cs,
  instbool_spec b1 i1 -> instbool_spec b2 i2 ->
  exists i3 : inst, instbool_spec (xorb b1 b2) i3 /\
  (i2 :: i1 :: vs, instxor :: cs) |=>* (i3 :: vs, cs).
Proof.
  (do 2 case) => i1 i2 vs cs H H0; evalauto => i3 i4 vs' cs';
    evalauto; evalpartial H; evalpartial H0; evalauto.
Qed.

(*
exists_and:
  and 命令。
*)
Lemma exists_and :
  { instand : inst |
    forall (b1 b2 : bool) i1 i2 vs cs,
    instbool_spec b1 i1 -> instbool_spec b2 i2 ->
    exists i3 : inst, instbool_spec (andb b1 b2) i3 /\
    (i2 :: i1 :: vs, instand :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  eexists => b1 b2 i1 i2 vs cs H H0.
  evalpartial' evalswap.
  do 2 evalpartial' evalpush.
  evalpartial (evalexecif b1).
  case b1 => /=.
  - evalpartial evalnop.
    by evalauto.
  - evalpartial' evalpop.
    evalpartial evalpush.
    by evalauto.
Defined.

Notation instand := (proj1_sig exists_and).
Notation evaland := (proj2_sig exists_and).

(*
exists_or:
  or 命令。
*)
Lemma exists_or :
  { instand : inst |
    forall (b1 b2 : bool) i1 i2 vs cs,
    instbool_spec b1 i1 -> instbool_spec b2 i2 ->
    exists i3 : inst, instbool_spec (orb b1 b2) i3 /\
    (i2 :: i1 :: vs, instand :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  eexists => b1 b2 i1 i2 vs cs H H0.
  evalpartial' evalswap.
  do 2 evalpartial' evalpush.
  evalpartial (evalexecif b1).
  case b1 => /=.
  - evalpartial' evalpop.
    evalpartial evalpush.
    by evalauto.
  - evalpartial evalnop.
    by evalauto.
Defined.

Notation instor := (proj1_sig exists_or).
Notation evalor := (proj2_sig exists_or).
