Require Import Basics Relations Relation_Operators Logic.Decidable List.
Require Import Utils.

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
inst_countcons:
  命令を構成するコンストラクタの数を計算する。
*)
Fixpoint inst_countcons (i : inst) : nat :=
  match i with
    | instpush i => S (inst_countcons i)
    | instpair i1 i2 => S (inst_countcons i1 + inst_countcons i2)
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
  Local Ltac decide_eval_solve :=
    (right ; intro ; do 2 inversion 0 ; fail) ||
    (left ; eexists ; constructor ; fail).
  destruct e1 as [vs [ | [ | | | | | | | ] ps]].
  decide_eval_solve.
  destruct vs ; decide_eval_solve.
  destruct vs ; decide_eval_solve.
  destruct vs as [ | ? [ | ? ?]] ; decide_eval_solve.
  destruct vs as [ | ? [ | ? ?]] ; decide_eval_solve.
  destruct vs ; decide_eval_solve.
  destruct vs ; decide_eval_solve.
  decide_eval_solve.
  decide_eval_solve.
Defined.

(*
uniqueness_of_eval:
  環境 e1 から eval によって書き換えられる環境 e2, e3 は同値である。
*)
Lemma uniqueness_of_eval :
  forall (e1 e2 e3 : environment), e1 |=> e2 -> e1 |=> e3 -> e2 = e3.
  intros.
  destruct e1 as [[ | v vs] [ | [ | | | | | | | ] [ | p ps]]] ;
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

Lemma exists_and_right_map : forall (P Q R : inst -> Prop),
  (forall (i : inst), Q i -> R i) ->
  (exists i : inst, P i /\ Q i) -> (exists i : inst, P i /\ R i).
  firstorder auto.
Qed.

Ltac evalstep' e1 e2 :=
  try apply rt_refl ;
  try (eexists ; split ; [ | apply rt_refl ]) ;
  try (eexists ; split ; [ | eexists ; split ; [ | apply rt_refl ] ]) ;
  match eval hnf in (decide_eval e1) with
    | or_introl _ (ex_intro _ ?e3 ?p) =>
      apply (rt_trans _ _ _ _ _ (rt_step _ _ _ _ p)) ||
      apply (exists_and_right_map _ _ _ (fun _ =>
             rt_trans _ _ _ _ _ (rt_step _ _ _ _ p))) ||
      apply (exists_and_right_map _ _ _ (fun _ =>
             exists_and_right_map _ _ _ (fun _ =>
             rt_trans _ _ _ _ _ (rt_step _ _ _ _ p))))
    | _ => idtac
  end.

Ltac evalstep :=
  match goal with
    | |- ?e1 |=>* ?e2 => evalstep' e1 e2
    | |- clos_refl_trans _ eval ?e1 ?e2 => evalstep' e1 e2
    | |- exists i1 : inst, _ /\
         ?e1 |=>* ?e2 => evalstep' e1 e2
    | |- exists i1 : inst, _ /\
         clos_refl_trans _ eval ?e1 ?e2 => evalstep' e1 e2
    | |- exists i1 : inst, _ /\
         exists i2 : inst, _ /\
         ?e1 |=>* ?e2 => evalstep' e1 e2
    | |- exists i1 : inst, _ /\
         exists i2 : inst, _ /\
         clos_refl_trans _ eval ?e1 ?e2 => evalstep' e1 e2
    | _ => fail "The goal is invalid."
  end.

(*
evalauto:
  evalstep を適用できなくなるまで繰り返す。
*)
Ltac evalauto := evalstep ; repeat evalstep.

(*
evalpartial:
  指定した関数を適用することで計算を途中まで進める。
*)

Tactic Notation "evalpartial" constr(H) "by" tactic(tac) :=
  (eapply  rt_trans ;
   [ eapply H ; tac ; fail | ]) ||
  (refine (exists_and_right_map _ _ _ (fun _ =>
           rt_trans _ _ _ _ _ _) _) ;
   [ eapply H ; tac ; fail | ]) ||
  (refine (exists_and_right_map _ _ _ (fun _ =>
           exists_and_right_map _ _ _ (fun _ =>
           rt_trans _ _ _ _ _ _)) _) ;
   [ eapply H ; tac ; fail | ]) ||
  fail.

Tactic Notation "evalpartial" constr(H) := evalpartial H by idtac.

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

Definition instnop : inst := instpair (instpush instpop) instpop.

Lemma evalnop : forall (vs cs : stack), (vs, instnop :: cs) |=>* (vs, cs).
  intros ; evalauto.
Qed.

(*
instseq:
  命令列を素直に記述するためのもの。命令のリストを instpair で畳み込むと、それが
  継続のスタックの先頭にあった場合に、元のリストの通りに展開される。
*)
Definition instseq' : list inst -> inst -> inst := fold_left instpair.

Lemma evalseq' : forall (is : list inst) (i : inst) (vs cs : stack),
  (vs, instseq' is i :: cs) |=>* (vs, i :: is ++ cs).
  induction is ; intros ; [ | evalpartial IHis ] ; evalauto.
Qed.

Definition instseq (is : list inst) : inst := instseq' is instnop.

Lemma evalseq : forall (is : list inst) (vs cs : stack),
  (vs, instseq is :: cs) |=>* (vs, is ++ cs).
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
  apply fold_left_app.
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

Lemma evalsnoc : forall (i1 i2 : inst) (vs cs : stack),
  (i1 :: i2 :: vs, instsnoc :: cs) |=>* (instpair i1 i2 :: vs, cs).
  intros ; evalauto.
Qed.
