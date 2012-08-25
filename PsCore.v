Require Import
  Logic.Decidable Relations.Relations Relations.Relation_Operators
  Lists.List Program.Basics Program.Equality
  ssreflect Common.

(*
inst:
  命令の定義。命令は値も兼ねる。
*)
Inductive inst : Set :=
  | instpop   : inst
  | instcopy  : inst
  | instswap  : inst
  | instcons  : inst
  | instquote : inst
  | instexec  : inst
  | instpush  : inst -> inst
  | instpair  : inst -> inst -> inst.

(*
inst_length:
  命令を構成するコンストラクタの数を計算する。
*)
Fixpoint inst_length i : nat :=
  match i with
    | instpush i => S (inst_length i)
    | instpair i1 i2 => S (inst_length i1 + inst_length i2)
    | _ => 1
  end.

(*
stack:
  スタックは命令のリスト。
*)
Definition stack : Set := list inst.

(*
environment:
  環境は2本のスタックの組。前者は値のスタック、後者は継続のスタックである。
*)
Definition environment : Set := (stack * stack)%type.

(*
eval:
  計算は環境上の二項関係(書換系)である。
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
Inductive eval : relation environment :=
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
Definition evalrtc : relation environment :=
  clos_refl_trans_1n environment eval.

(*
|=>, |=>*:
  eval, evalrtc の中置演算子。
*)
Infix "|=>" := eval (at level 50, no associativity).
Infix "|=>*" := evalrtc (at level 50, no associativity).

Lemma evalrtc_refl : forall e, e |=>* e.
Proof.
  constructor.
Qed.

Lemma evalrtc_refl' : forall e1 e2, e1 = e2 -> e1 |=>* e2.
Proof.
  move=> e1 e2 H ; rewrite H ; constructor.
Qed.

Lemma evalrtc_step : forall e1 e2, e1 |=> e2 -> e1 |=>* e2.
Proof.
  do !econstructor ; eauto.
Qed.

Lemma evalrtc_cons : forall e1 e2 e3, e1 |=> e2 -> e2 |=>* e3 -> e1 |=>* e3.
Proof.
  econstructor ; eauto.
Qed.

Lemma evalrtc_trans : forall e1 e2 e3, e1 |=>* e2 -> e2 |=>* e3 -> e1 |=>* e3.
Proof.
  by apply rt1n_trans'.
Qed.

(*
decide_eval:
  環境 e1 から eval によって書き換えられる環境 e2 の存在を決定する。
*)
Theorem decide_eval : forall e1, decidable (exists e2 : environment, e1 |=> e2).
Proof.
  elim=> [vs [ | [ | | | | | | | ] ps]] ;
  [ |
   destruct vs |
   destruct vs |
   destruct vs as [ | ? [ | ? ?]] |
   destruct vs as [ | ? [ | ? ?]] |
   destruct vs |
   destruct vs |
    |
    ] ;
  (by right ; intro ; do 2 inversion 0) ||
  (by left ; eexists ; constructor).
Defined.

(*
eval_uniqueness:
  環境 e1 から eval によって書き換えられる環境 e2, e3 は同値である。
*)
Theorem eval_uniqueness : forall e1 e2 e3, e1 |=> e2 -> e1 |=> e3 -> e2 = e3.
Proof.
  intros.
  destruct e1 as [[ | v vs] [ | [ | | | | | | | ] [ | p ps]]] ;
    inversion H ; inversion H0 ; congruence.
Qed.

(*
eval_semi_uniqueness:
  e1 |=>* e2 かつ e1 |=>* e3 ならば e2 |=>* e3 もしくは e3 |=>* e2 が成り立つ。
*)
Theorem eval_semi_uniqueness:
  forall e1 e2 e3, e1 |=>* e2 -> e1 |=>* e3 -> e2 |=>* e3 \/ e3 |=>* e2.
Proof.
  intros.
  induction H.
  auto.
  inversion H0.
  right ; rewrite <- H2 ; econstructor ; eauto.
  by apply IHclos_refl_trans_1n ; rewrite (eval_uniqueness _ _ _ H H2).
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
  intros.
  inversion H ; simpl ; constructor.
Qed.

Theorem evalrtc_apptail :
  forall vs ps vs' ps' vs'' ps'', (vs, ps) |=>* (vs', ps') ->
  (vs ++ vs'', ps ++ ps'') |=>* (vs' ++ vs'', ps' ++ ps'').
Proof.
  intros.
  dependent induction H.
  constructor.
  destruct y.
  by apply evalrtc_cons with (s ++ vs'', s0 ++ ps'') ;
    [ apply eval_apptail | apply IHclos_refl_trans_1n].
Qed.

(*
evalstep:
  ゴールが e1 |=>* e2 の形である場合に、e1 から書き換え可能な環境 e3 を計算し、
  ゴールを e3 |=>* e2 で置き換えるタクティク。計算を自動的に1段階進める。
*)
Lemma exists_and_right_map :
  forall (P Q R : inst -> Prop), (forall i, Q i -> R i) ->
  (exists i : inst, P i /\ Q i) -> (exists i : inst, P i /\ R i).
Proof.
  by firstorder.
Qed.

Ltac evalstep_0 e1 e2 :=
  apply evalrtc_refl ||
  match eval hnf in (decide_eval e1) with
    | or_introl _ (ex_intro _ ?e3 ?p) => apply (evalrtc_cons _ _ _ p)
  end.

Ltac evalstep_1 e1 e2 :=
  (eexists ; split ; last apply evalrtc_refl) ||
  match eval hnf in (decide_eval e1) with
    | or_introl _ (ex_intro _ ?e3 ?p) =>
      apply (exists_and_right_map _ _ _ (fun _ => evalrtc_cons _ _ _ p))
  end.

Ltac evalstep_2 e1 e2 :=
  (eexists ; split ; last (eexists ; split ; last apply evalrtc_refl)) ||
  match eval hnf in (decide_eval e1) with
    | or_introl _ (ex_intro _ ?e3 ?p) =>
      apply (exists_and_right_map _ _ _ (fun _ =>
             exists_and_right_map _ _ _ (fun _ => evalrtc_cons _ _ _ p)))
  end.

Ltac evalstep :=
  match goal with
    | |- ?e1 |=>* ?e2 => evalstep_0 e1 e2
    | |- exists i1 : inst, _ /\ ?e1 |=>* ?e2 => evalstep_1 e1 e2
    | |- exists i1 : inst, _ /\ exists i2 : inst, _ /\ ?e1 |=>* ?e2 =>
      evalstep_2 e1 e2
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
  (eapply evalrtc_trans ;
   [ by eapply H ; tac | ]) ||
  (refine (exists_and_right_map _ _ _ (fun _ => evalrtc_trans _ _ _ _) _) ;
   [ by eapply H ; tac | ]) ||
  (refine (exists_and_right_map _ _ _ (fun _ =>
           exists_and_right_map _ _ _ (fun _ => evalrtc_trans _ _ _ _)) _) ;
   [ by eapply H ; tac | ]).

Tactic Notation "evalpartial" constr(H) := evalpartial H by idtac.

(*
rtcrefl:
  ゴール e1 |=>* e2 を e1 = e2 で置き換え、f_equal を繰り返し適用する。
*)
Ltac rtcrefl := apply evalrtc_refl' ; repeat f_equal.

(*
instnop:
  何もしない(NOP)命令。
*)
Definition instnop : inst := instpair (instpush instpop) instpop.

Lemma evalnop : forall vs cs, (vs, instnop :: cs) |=>* (vs, cs).
Proof.
  intros ; evalauto.
Qed.

(*
instsnoc:
  instswap, instcons を順番に実行する。パラメータの順番が反転した instcons。
*)
Definition instsnoc : inst := instpair instswap instcons.

Lemma evalsnoc : forall i1 i2 vs cs,
  (i1 :: i2 :: vs, instsnoc :: cs) |=>* (instpair i1 i2 :: vs, cs).
Proof.
  intros ; evalauto.
Qed.

(*
instseq:
  命令列を素直に記述するためのもの。命令のリストを instpair で畳み込むと、それが
  継続のスタックの先頭にあった場合に、元のリストの通りに展開される。
*)
Definition instseq' : list inst -> inst -> inst := fold_left instpair.

Lemma evalseq' :
  forall il i vs cs, (vs, instseq' il i :: cs) |=>* (vs, i :: il ++ cs).
Proof.
  elim ; intros ; last evalpartial H ; evalauto.
Qed.

Definition instseq il : inst := instseq' il instnop.

Lemma evalseq : forall il vs cs, (vs, instseq il :: cs) |=>* (vs, il ++ cs).
Proof.
  intros.
  evalpartial evalseq'.
  evalauto.
Qed.

Lemma instseq_replicate : forall n i1 i2,
  instseq' (replicate n i1) i2 = fold_right (flip instpair) i2 (replicate n i1).
Proof.
  intros.
  rewrite {2} replicate_rev_id.
  apply eq_sym, fold_left_rev_right.
Qed.

Lemma app_instseq' :
  forall is1 is2 i, instseq' (is1 ++ is2) i = instseq' is2 (instseq' is1 i).
Proof.
  apply fold_left_app.
Qed.

Lemma app_instseq :
  forall is1 is2, instseq (is1 ++ is2) = instseq' is2 (instseq is1).
Proof.
  intros ; apply app_instseq'.
Qed.
