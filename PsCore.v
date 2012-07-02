Require Import Basics.
Require Import Relations.
Require Import Relation_Operators.
Require Import Logic.Decidable.
Require Import List.

Require Import Utils.

(*
inst:
  命令の定義。命令は値も兼ねる。
*)
Inductive inst : Set :=
  | instpop  : inst
  | instdup  : inst
  | instswap : inst
  | instcons : inst
  | instpush : inst
  | instexec : inst
  | instpair : inst -> inst -> inst.

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
  evaldup (instdup):
    値のスタックの先頭を複製する。
  evalswap (instswap):
    値のスタックの先頭の2つの値を入れ替える。
  evalcons (instcons):
    値のスタックの先頭の2つの値を取り出し、そのペアを instpair で作成し、値のス
    タックの先頭に積む。
  evalpush (instpush):
    継続のスタックの先頭にある evalpush 命令の直後の値を取り出し、値のスタックに
    積む。
  evalexec (instexec):
    値のスタックの先頭にある値を取り出し、継続のスタックの先頭に積む。
  evalpair (instpair):
    instpair のパラメータの2つの命令を継続のスタックに積む。
*)
Inductive eval : relation environment :=
  | evalpop  :
      forall (i : inst) (vs ps : stack),
      eval (i :: vs, instpop :: ps) (vs, ps)
  | evaldup  :
      forall (i : inst) (vs ps : stack),
      eval (i :: vs, instdup :: ps) (i :: i :: vs, ps)
  | evalswap :
      forall (i1 i2 : inst) (vs ps : stack),
      eval (i1 :: i2 :: vs, instswap :: ps) (i2 :: i1 :: vs, ps)
  | evalcons :
      forall (i1 i2 : inst) (vs ps : stack),
      eval (i1 :: i2 :: vs, instcons :: ps) (instpair i2 i1 :: vs, ps)
  | evalpush :
      forall (i : inst) (vs ps : stack),
      eval (vs, instpush :: i :: ps) (i :: vs, ps)
  | evalexec :
      forall (i : inst) (vs ps : stack),
      eval (i :: vs, instexec :: ps) (vs, i :: ps)
  | evalpair  :
      forall (i1 i2 : inst) (vs ps : stack),
      eval (vs, instpair i1 i2 :: ps) (vs, i1 :: i2 :: ps).

(*
evalrtc, evalrtc':
  eval の反射推移閉包。
  NOTE:
    clos_refl_trans と clos_refl_trans_1n はどちらも反射推移閉包であるが、定義が
    異なる。
*)
Definition evalrtc : relation environment := clos_refl_trans _ eval.
Definition evalrtc' : relation environment := clos_refl_trans_1n _ eval.

(*
|=>, |=>*, |=>*':
  eval, evalrtc, evalrtc' の中置演算子。
*)
Infix "|=>" := eval (at level 50, no associativity).
Infix "|=>*" := evalrtc (at level 50, no associativity).
Infix "|=>*'" := evalrtc' (at level 50, no associativity).

(*
evalrtc_is_evalrtc':
  evalrtc, evalrtc' の同値性の証明。
*)
Lemma evalrtc_is_evalrtc' :
  forall (e1 e2 : environment), e1 |=>* e2 <-> e1 |=>*' e2.
  intros ; split ; [ apply clos_rt_rt1n | apply clos_rt1n_rt ].
Qed.

(*
decide_eval:
  環境 e1 から eval によって書き換えられる環境 e2 の存在を決定する。
*)
Lemma decide_eval : forall (e1 : environment),
  decidable (exists e2 : environment, e1 |=> e2).
  intros.
  destruct e1.
  destruct s0.
  right ; intro.
  destruct H.
  inversion H.
  destruct i.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply evalpop.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply evaldup.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply evalswap.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply evalcons.
  destruct s0.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply evalpush.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply evalexec.
  left ; eexists ; apply evalpair.
Defined.

(*
uniqueness_of_eval:
  環境 e1 から eval によって書き換えられる環境 e2, e3 は同値である。
*)
Lemma uniqueness_of_eval :
  forall (e1 e2 e3 : environment), e1 |=> e2 -> e1 |=> e3 -> e2 = e3.
  intros.
  destruct e1, e2, e3.
  destruct s0.
  inversion H.
  destruct i.
  destruct s ; [ inversion H | inversion H ; inversion H0 ; congruence ].
  destruct s ; [ inversion H | inversion H ; inversion H0 ; congruence ].
  destruct s ; [ inversion H | inversion H ; inversion H0 ; congruence ].
  destruct s ; [ inversion H | inversion H ; inversion H0 ; congruence ].
  destruct s ; [ inversion H | inversion H ; inversion H0 ; congruence ].
  destruct s0 ; [ inversion H | inversion H ; inversion H0 ; congruence ].
  destruct s ; [ inversion H | inversion H ; inversion H0 ; congruence ].
  inversion H ; inversion H0 ; congruence.
Qed.

(*
evalrtc'_confluence:
  e1 |=>*' e2 かつ e1 |=>*' e3 ならば e2 |=>*' e3 もしくは e3 |=>*' e2 が成り立
  つ。
  NOTE:
    合流性より強い性質であるが、適切な名前を知らないので仮の名前として
    evalrtc'_confluence とした。
*)
Lemma evalrtc'_confluence : forall (e1 e2 e3 : environment),
  e1 |=>*' e2 -> e1 |=>*' e3 -> e2 |=>*' e3 \/ e3 |=>*' e2.
  intros.
  induction H ; auto.
  inversion H0.
  rewrite <- H2.
  right.
  eapply rt1n_trans ; [ apply H | apply H1 ].
  apply IHclos_refl_trans_1n.
  rewrite (uniqueness_of_eval _ _ _ H H2) ; auto.
Qed.

(*
evalrtc_confluence:
  e1 |=>* e2 かつ e1 |=>* e3 ならば e2 |=>* e3 もしくは e3 |=>* e2 が成り立つ。
*)
Lemma evalrtc_confluence : forall (e1 e2 e3 : environment),
  e1 |=>* e2 -> e1 |=>* e3 -> e2 |=>* e3 \/ e3 |=>* e2.
  do 3 intro.
  repeat erewrite evalrtc_is_evalrtc'.
  eapply evalrtc'_confluence.
Qed.

(*
evalstep:
  ゴールが e1 |=>* e2 の形である場合に、e1 から書き換え可能な環境 e3 を計算し、
  ゴールを e3 |=>* e2 で置き換えるタクティク。計算を自動的に1段階進める。
*)

Ltac evalstep' e1 e2 :=
  try apply rt_refl ;
  match eval hnf in (decide_eval e1) with
    | or_introl _ (ex_intro _ ?e3 ?p) =>
      apply (rt_trans _ _ _ _ _ (rt_step _ _ _ _ p))
    | _ => idtac
  end.

Ltac evalstep'' e1 e2 :=
  try (eexists ; split ; [ | apply rt_refl ; fail ]) ;
  match eval hnf in (decide_eval e1) with
    | or_introl _ (ex_intro _ ?e3 ?p) =>
      apply (exists_map _ _ _ (fun _ =>
        and_map_right _ _ _ (rt_trans _ _ _ _ _ (rt_step _ _ _ _ p))))
    | _ => idtac
  end.

Ltac evalstep :=
  match goal with
    | |- ?e1 |=>* ?e2 => evalstep' e1 e2
    | |- clos_refl_trans _ eval ?e1 ?e2 => evalstep' e1 e2
    | [ |- exists i : inst, ?P /\ ?e1 |=>* ?e2 ] =>
      evalstep'' e1 e2
    | [ |- exists i : inst, ?P /\ clos_refl_trans _ eval ?e1 ?e2 ] =>
      evalstep'' e1 e2
    | _ => fail "The goal is invalid."
  end.

(*
evalauto:
  evalstep を適用できなくなるまで繰り返す。
*)
Ltac evalauto := evalstep ; repeat evalstep.

(*
evalpartial, evalpartial':
  指定した関数を適用することで計算を途中まで進める。evalpartial は適用した結果と
  してサブゴールが残ることを許容しないが、evalpartial' ではそれを許容する。
*)
Ltac evalpartial H := eapply rt_trans ; [ apply H ; fail | ].

Ltac evalpartial' H := eapply rt_trans ; [ eapply H | ].

(*
rtcrefl:
  ゴール e1 |=>* e2 を e1 = e2 で置き換え、f_equal を繰り返し適用する。
*)
Ltac rtcrefl :=
  hnf ;
  match goal with
    | |- clos_refl_trans _ _ ?e1 ?e2 =>
      replace e1 with e2 ; [ apply rt_refl | repeat f_equal ]
    | _ => fail 2 "The goal is invalid."
  end.

(*
instnop:
  何もしない(NOP)命令。
*)
Definition instnop : inst := instpair (instpair instpush instpop) instpop.

Lemma evalnop : forall (vs ps : stack), (vs, instnop :: ps) |=>* (vs, ps).
  intros ; evalauto.
Qed.

(*
instseq:
  命令列を素直に記述するためのもの。命令のリストを instpair で畳み込むと、それが
  継続のスタックの先頭にあった場合に、元のリストの通りに展開される。
*)
Definition instseq' : list inst -> inst -> inst := fold_left instpair.

Lemma evalseq' : forall (is : list inst) (i : inst) (vs ps : stack),
  (vs, instseq' is i :: ps) |=>* (vs, i :: is ++ ps).
  induction is ; intros.
  evalauto.
  evalpartial IHis ; evalauto.
Qed.

Definition instseq (is : list inst) : inst := instseq' is instnop.

Lemma evalseq : forall (is : list inst) (vs ps : stack),
  (vs, instseq is :: ps) |=>* (vs, is ++ ps).
  intros.
  evalpartial evalseq'.
  evalauto.
Qed.

Lemma instseq_replicate : forall (n : nat) (i1 i2 : inst),
  instseq' (replicate n i1) i2 =
    fold_right (flip instpair) i2 (replicate n i1).
  intros.
  rewrite (replicate_rev_id n i1) at 2.
  apply (eq_sym (fold_left_rev_right (flip instpair) (replicate n i1) i2)).
Qed.

Lemma app_instseq' : forall (is1 is2 : list inst) (i : inst),
  instseq' (is1 ++ is2) i = instseq' is2 (instseq' is1 i).
  intros ; apply fold_left_app.
Qed.

Lemma app_instseq : forall (is1 is2 : list inst),
  instseq (is1 ++ is2) = instseq' is2 (instseq is1).
  intros ; apply app_instseq'.
Qed.

(*
instsnoc:
  instswap, instcons を順番に実行する。パラメータの順番が反転した instcons。
*)
Definition instsnoc : inst := instseq [ instswap ; instcons ].

Lemma evalsnoc : forall (i1 i2 : inst) (vs ps : stack),
  (i1 :: i2 :: vs, instsnoc :: ps) |=>* (instpair i1 i2 :: vs, ps).
  intros ; evalauto.
Qed.

(*
instquote:
  スタックの先頭にある値をクオートする。クオートされた値は、クオートされる前の値
  をスタックの先頭に積む命令である。
*)
Definition instquote : inst := instseq [instpush ; instpush ; instsnoc ].

Lemma evalquote : forall (i : inst) (vs ps : stack),
  (i :: vs, instquote :: ps) |=>* (instpair instpush i :: vs, ps).
  intros ; evalauto.
Qed.
