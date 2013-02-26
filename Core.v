Require Import
  Coq.Logic.Decidable Coq.Relations.Relations
  Coq.Strings.String Coq.Program.Basics Coq.Program.Equality
  Ssreflect.ssreflect Ssreflect.ssrnat Ssreflect.seq
  FormalPS.stdlib_ext.

Set Implicit Arguments.

(*
inst:
  命令の定義。命令は値も兼ねる。
*)
Inductive inst : Set :=
  | instpop | instcopy | instswap | instcons | instquote | instexec
  | instpush of inst
  | instpair of inst & inst.

(*
inst_to_pscode:
  inst 型の命令を PostScript のプログラムに変換する。
*)
Fixpoint pscode_of_inst (i : inst) : string :=
  match i with
    | instpop        => "pop"
    | instcopy       => "dup"
    | instswap       => "exch"
    | instcons       => "cons"
    | instquote      => "quote"
    | instexec       => "exec"
    | instpush i     => "{" ++ pscode_of_inst i ++ "}"
    | instpair i1 i2 => pscode_of_inst i1 ++ " " ++ pscode_of_inst i2
  end%string.

(*
inst_size:
  命令を構成するコンストラクタの数を計算する。
*)
Fixpoint inst_size i : nat :=
  match i with
    | instpush i => (inst_size i).+1
    | instpair i1 i2 => (inst_size i1 + inst_size i2).+1
    | _ => 1
  end.

(*
stack:
  スタックは命令のリスト。
*)
Notation stack := (seq inst).

(*
state:
  状態は2本のスタックの組。前者は値のスタック、後者は継続のスタックである。
*)
Notation state := (stack * stack)%type.

(*
eval:
  計算は状態上の二項関係(書換系)である。
  evalpop (instpop):
    値のスタックの先頭を捨てる。
  evalcopy (instcopy):
    値のスタックの先頭を複製する。
  evalswap (instswap):
    値のスタックの先頭の2つの値を入れ替える。
  evalcons (instcons):
    値のスタックの先頭の2つの値を取り出し、そのペアを instpair で作成し、値のス
    タックの先頭に積む。
  evalquote (instquote):
    値のスタックの先頭にある値を取り出し、クオートした値をスタックに積む。クオー
    トされた値は実行すると元の値が取り出せる。
  evalexec (instexec):
    値のスタックの先頭にある値を取り出し、継続のスタックの先頭に積む。
  evalpush (instpush):
    instpush のパラメータの値を値のスタックに積む。
  evalpair (instpair):
    instpair のパラメータの2つの命令を継続のスタックに積む。
*)
Inductive eval : relation state :=
  | evalpop   : forall i vs cs, eval (i :: vs, instpop :: cs) (vs, cs)
  | evalcopy  : forall i vs cs,
      eval (i :: vs, instcopy :: cs) (i :: i :: vs, cs)
  | evalswap  : forall i1 i2 vs cs,
      eval (i2 :: i1 :: vs, instswap :: cs) (i1 :: i2 :: vs, cs)
  | evalcons  : forall i1 i2 vs cs,
      eval (i2 :: i1 :: vs, instcons :: cs) (instpair i1 i2 :: vs, cs)
  | evalquote : forall i vs cs,
      eval (i :: vs, instquote :: cs) (instpush i :: vs, cs)
  | evalexec  : forall i vs cs, eval (i :: vs, instexec :: cs) (vs, i :: cs)
  | evalpush  : forall i vs cs, eval (vs, instpush i :: cs) (i :: vs, cs)
  | evalpair  : forall i1 i2 vs cs,
      eval (vs, instpair i1 i2 :: cs) (vs, i1 :: i2 :: cs).

(*
evalrtc:
  eval の反射推移閉包。
*)
Notation evalrtc := (clos_refl_trans_1n state eval).

(*
|=>, |=>*:
  eval, evalrtc の中置演算子。
*)
Infix "|=>" := eval (at level 50, no associativity).
Infix "|=>*" := evalrtc (at level 50, no associativity).

Lemma evalrtc_refl : forall s, s |=>* s.
Proof.
  constructor.
Qed.

Lemma evalrtc_refl' : forall s1 s2, s1 = s2 -> s1 |=>* s2.
Proof.
  move => s1 s2 H; rewrite H; constructor.
Qed.

Lemma evalrtc_step : forall s1 s2, s1 |=> s2 -> s1 |=>* s2.
Proof.
  do !econstructor; eauto.
Qed.

Lemma evalrtc_cons : forall s1 s2 s3, s1 |=> s2 -> s2 |=>* s3 -> s1 |=>* s3.
Proof.
  econstructor; eauto.
Qed.

Lemma evalrtc_trans : forall s1 s2 s3, s1 |=>* s2 -> s2 |=>* s3 -> s1 |=>* s3.
Proof.
  by apply rt1n_trans'.
Qed.

(*
decide_eval:
  状態 s1 から eval によって書き換えられる状態 s2 の有無を決定する。
*)
Theorem decide_eval : forall s1, decidable (exists s2 : state, s1 |=> s2).
Proof.
  elim => [vs [ | [ | | | | | | | ] ps]];
  [ |
   destruct vs |
   destruct vs |
   destruct vs as [ | ? [ | ? ?]] |
   destruct vs as [ | ? [ | ? ?]] |
   destruct vs |
   destruct vs |
    |
    ];
  (by right; intro; do 2 inversion 0) ||
  (by left; eexists; constructor).
Defined.

(*
eval_uniqueness:
  状態 s1 から eval によって書き換えられる状態 s2, s3 は同値である。
*)
Theorem eval_uniqueness : forall s1 s2 s3, s1 |=> s2 -> s1 |=> s3 -> s2 = s3.
Proof.
  destruct s1 as [[ | v vs] [ | [ | | | | | | | ] [ | p ps]]] => s2 s3 H H0;
    inversion H; inversion H0; congruence.
Qed.

(*
eval_semi_uniqueness:
  s1 |=>* s2 かつ s1 |=>* s3 ならば s2 |=>* s3 もしくは s3 |=>* s2 が成り立つ。
*)
Theorem eval_semi_uniqueness:
  forall s1 s2 s3, s1 |=>* s2 -> s1 |=>* s3 -> s2 |=>* s3 \/ s3 |=>* s2.
Proof.
  move => s1 s2 s3; elim.
  - auto.
  - move => x y z H H0 IH H1.
    inversion H1.
    right; rewrite -H2; econstructor; eauto.
    move: IH; rewrite (eval_uniqueness H H2); auto.
Qed.

(*
eval_apptail, evalrtc_apptail:
  ある計算が正しければ、その両辺の値スタックや継続スタックの末尾にリストを足した
  としても正しい計算となる。
*)
Lemma eval_apptail :
  forall vs ps vs' ps' vs'' ps'', (vs, ps) |=> (vs', ps') ->
  (vs ++ vs'', ps ++ ps'') |=> (vs' ++ vs'', ps' ++ ps'').
Proof.
  move => vs ps vs' ps' vs'' ps'' H.
  inversion H; constructor.
Qed.

Theorem evalrtc_apptail :
  forall vs ps vs' ps' vs'' ps'', (vs, ps) |=>* (vs', ps') ->
  (vs ++ vs'', ps ++ ps'') |=>* (vs' ++ vs'', ps' ++ ps'').
Proof.
  move => vs ps vs' ps' vs'' ps'' H.
  dependent induction H.
  constructor.
  destruct y.
  by apply evalrtc_cons with (l ++ vs'', l0 ++ ps'');
    [ apply eval_apptail | apply IHclos_refl_trans_1n].
Qed.

(*
evalstep:
  ゴールが s1 |=>* s2 の形である場合に、s1 から書き換え可能な状態 s3 を計算し、
  ゴールを s3 |=>* s2 で置き換えるタクティク。計算を自動的に1段階進める。
*)
Lemma exists_and_right_map :
  forall (P Q R : inst -> Prop), (forall i, Q i -> R i) ->
  (exists i : inst, P i /\ Q i) -> (exists i : inst, P i /\ R i).
Proof.
  by firstorder.
Qed.

Ltac evalstep_0 s1 s2 :=
  apply evalrtc_refl ||
  match eval hnf in (decide_eval s1) with
    | or_introl _ (ex_intro _ ?s3 ?p) => apply (@evalrtc_cons _ _ _ p)
  end.

Ltac evalstep_1 s1 s2 :=
  (eexists; split; last apply evalrtc_refl) ||
  match eval hnf in (decide_eval s1) with
    | or_introl _ (ex_intro _ ?s3 ?p) =>
      apply (@exists_and_right_map _ _ _ (fun _ => @evalrtc_cons _ _ _ p))
  end.

Ltac evalstep_2 s1 s2 :=
  (eexists; split; last (eexists; split; last apply evalrtc_refl)) ||
  match eval hnf in (decide_eval s1) with
    | or_introl _ (ex_intro _ ?s3 ?p) =>
      apply (@exists_and_right_map _ _ _ (fun _ =>
             @exists_and_right_map _ _ _ (fun _ => @evalrtc_cons _ _ _ p)))
  end.

Ltac evalstep :=
  match goal with
    | |- ?s1 |=>* ?s2 => evalstep_0 s1 s2
    | |- exists i1 : inst, _ /\ ?s1 |=>* ?s2 => evalstep_1 s1 s2
    | |- exists i1 : inst, _ /\ exists i2 : inst, _ /\ ?s1 |=>* ?s2 =>
      evalstep_2 s1 s2
  end.

(*
evalauto:
  evalstep を適用できなくなるまで繰り返す。
*)
Ltac evalauto := do !evalstep.

(*
evalpartial:
  指定した関数を適用することで計算を途中まで進める。
*)
Tactic Notation "evalpartial" constr(H) "by" tactic(tac) :=
  (
    apply: evalrtc_trans ||
    refine (@exists_and_right_map _ _ _ (fun _ => @evalrtc_trans _ _ _ _) _) ||
    refine (@exists_and_right_map _ _ _ (fun _ =>
            @exists_and_right_map _ _ _ (fun _ => @evalrtc_trans _ _ _ _)) _)
  ); [ by (apply evalrtc_step; eapply H) || eapply H; tac | ]; subst_evars.

Tactic Notation "evalpartial" constr(H) := evalpartial H by idtac.

Tactic Notation "evalpartial'" constr(H) "by" tactic(tac) :=
  evalpartial evalpair; evalpartial H by tac.

Tactic Notation "evalpartial'" constr(H) := evalpartial' H by idtac.

(*
rtcrefl:
  ゴール s1 |=>* s2 を s1 = s2 で置き換え、f_equal を繰り返し適用する。
*)
Ltac rtcrefl := apply evalrtc_refl'; do ?f_equal.

(*
exists_nop:
  何もしない(NOP)命令。
*)
Lemma exists_nop :
  { instnop : inst | forall vs cs, (vs, instnop :: cs) |=>* (vs, cs) }.
Proof.
  eexists => vs cs.
  evalpartial' (evalpush instpop).
  evalpartial evalpop.
  evalauto.
Defined.

Notation instnop := (proj1_sig exists_nop).
Notation evalnop := (proj2_sig exists_nop).

(*
exists_snoc:
  instswap, instcons を順番に実行する。パラメータの順番が反転した instcons。
*)
Lemma exists_snoc :
  { instsnoc : inst | forall i1 i2 vs cs,
    (i1 :: i2 :: vs, instsnoc :: cs) |=>* (instpair i1 i2 :: vs, cs) }.
Proof.
  eexists => i1 i2 vs cs.
  evalpartial' evalswap.
  evalpartial evalcons.
  evalauto.
Defined.

Notation instsnoc := (proj1_sig exists_snoc).
Notation evalsnoc := (proj2_sig exists_snoc).

(*
instseqc', instseqc:
  命令列を素直に記述するためのもの。命令のリストを instpair で畳み込むと、それが
  継続のスタックの先頭にあった場合に、元のリストの通りに展開される。
*)
Notation instseqc' := (foldl instpair).

Lemma evalseqc' :
  forall il i vs cs, (vs, instseqc' i il :: cs) |=>* (vs, i :: il ++ cs).
Proof.
  elim => [ | i il IH] i' vs cs.
  evalauto.
  evalpartial IH; evalauto.
Qed.

Notation instseqc := (instseqc' instnop).

Lemma evalseqc : forall il vs cs, (vs, instseqc il :: cs) |=>* (vs, il ++ cs).
Proof.
  move => il vs cs.
  evalpartial evalseqc'.
  evalauto.
Qed.

Lemma app_instseqc' :
  forall il1 il2 i, instseqc' i (il1 ++ il2) = instseqc' (instseqc' i il1) il2.
Proof.
  move => il1 il2 i; apply foldl_cat.
Qed.

Lemma app_instseqc :
  forall il1 il2, instseqc (il1 ++ il2) = instseqc' (instseqc il1) il2.
Proof.
  move => il1 il2; apply app_instseqc'.
Qed.

Notation instseqc_nseq' n i1 i2 := (foldr (flip instpair) i2 (nseq n i1)).

Notation instseqc_nseq n i := (instseqc_nseq' n i instnop).

Lemma instseqc_nseq_eq :
  forall n i1 i2, instseqc' i2 (nseq n i1) = instseqc_nseq' n i1 i2.
Proof.
  by move => n i1 i2; rewrite {1}nseq_rev_id foldl_rev.
Qed.

Lemma evalseqc_nseq' :
  forall n i1 i2 vs cs,
  (vs, instseqc_nseq' n i1 i2 :: cs) |=>* (vs, i2 :: nseq n i1 ++ cs).
Proof.
  move => n i1 i2; rewrite -instseqc_nseq_eq; apply evalseqc'.
Qed.

Lemma evalseqc_nseq :
  forall n i vs cs, (vs, instseqc_nseq n i :: cs) |=>* (vs, nseq n i ++ cs).
Proof.
  move => n i vs cs.
  evalpartial evalseqc_nseq'.
  evalauto.
Qed.

(*
instseqv', instseqv:
  スタックに展開される命令の並びを記述するためのもの。
*)
Notation instseqv' := (foldl (fun a b => instpair (instpush b) a)).

Lemma evalseqv' :
  forall il i vs cs, (vs, instseqv' i il :: cs) |=>* (il ++ vs, i :: cs).
Proof.
  elim => [ | i' il IH ] i vs cs.
  evalauto.
  evalpartial IH.
  evalauto.
Qed.

Notation instseqv := (instseqv' instnop).

Lemma evalseqv : forall il vs cs, (vs, instseqv il :: cs) |=>* (il ++ vs, cs).
Proof.
  move => il vs cs.
  evalpartial evalseqv'.
  evalauto.
Qed.

Lemma app_instseqv' :
  forall il1 il2 i, instseqv' i (il1 ++ il2) = instseqv' (instseqv' i il1) il2.
Proof.
  move => il1 il2 i; apply foldl_cat.
Qed.

Lemma app_instseqv :
  forall il1 il2, instseqv (il1 ++ il2) = instseqv' (instseqv il1) il2.
Proof.
  move => il1 il2; apply app_instseqv'.
Qed.
