Require Import
  Logic.Decidable Relations.Relations Relations.Relation_Operators
  Lists.List Strings.String Program.Basics Program.Equality
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
Notation stack := (list inst).

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
  状態 e1 から eval によって書き換えられる状態 e2 の存在を決定する。
*)
Theorem decide_eval : forall e1, decidable (exists e2 : state, e1 |=> e2).
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
  状態 e1 から eval によって書き換えられる状態 e2, e3 は同値である。
*)
Theorem eval_uniqueness : forall e1 e2 e3, e1 |=> e2 -> e1 |=> e3 -> e2 = e3.
Proof.
  destruct e1 as [[ | v vs] [ | [ | | | | | | | ] [ | p ps]]]=> e2 e3 H H0 ;
    inversion H ; inversion H0 ; congruence.
Qed.

(*
eval_semi_uniqueness:
  e1 |=>* e2 かつ e1 |=>* e3 ならば e2 |=>* e3 もしくは e3 |=>* e2 が成り立つ。
*)
Theorem eval_semi_uniqueness:
  forall e1 e2 e3, e1 |=>* e2 -> e1 |=>* e3 -> e2 |=>* e3 \/ e3 |=>* e2.
Proof.
  move=> e1 e2 e3 ; elim.
  - auto.
  - move=> x y z H H0 IH H1.
    inversion H1.
    right ; rewrite -H2 ; econstructor ; eauto.
    move: IH ; rewrite (eval_uniqueness _ _ _ H H2) ; auto.
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
  move=> vs ps vs' ps' vs'' ps'' H.
  inversion H ; constructor.
Qed.

Theorem evalrtc_apptail :
  forall vs ps vs' ps' vs'' ps'', (vs, ps) |=>* (vs', ps') ->
  (vs ++ vs'', ps ++ ps'') |=>* (vs' ++ vs'', ps' ++ ps'').
Proof.
  move=> vs ps vs' ps' vs'' ps'' H.
  dependent induction H.
  constructor.
  destruct y.
  by apply evalrtc_cons with (l ++ vs'', l0 ++ ps'') ;
    [ apply eval_apptail | apply IHclos_refl_trans_1n].
Qed.

(*
evalstep:
  ゴールが e1 |=>* e2 の形である場合に、e1 から書き換え可能な状態 e3 を計算し、
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
  (eapply evalrtc_cons ;
   [ by eapply H ; tac | ]) ||
  (eapply evalrtc_trans ;
   [ by eapply H ; tac | ]) ||
  (refine (exists_and_right_map _ _ _ (fun _ => evalrtc_cons _ _ _ _) _) ;
   [ by eapply H ; tac | ]) ||
  (refine (exists_and_right_map _ _ _ (fun _ => evalrtc_trans _ _ _ _) _) ;
   [ by eapply H ; tac | ]) ||
  (refine (exists_and_right_map _ _ _ (fun _ =>
           exists_and_right_map _ _ _ (fun _ => evalrtc_cons _ _ _ _)) _) ;
   [ by eapply H ; tac | ]) ||
  (refine (exists_and_right_map _ _ _ (fun _ =>
           exists_and_right_map _ _ _ (fun _ => evalrtc_trans _ _ _ _)) _) ;
   [ by eapply H ; tac | ]).

Tactic Notation "evalpartial" constr(H) := evalpartial H by idtac.

Tactic Notation "evalpartial'" constr(H) "by" tactic(tac) :=
  evalpartial evalpair ; evalpartial H by tac.

Tactic Notation "evalpartial'" constr(H) :=
  evalpartial evalpair ; evalpartial H.

(*
rtcrefl:
  ゴール e1 |=>* e2 を e1 = e2 で置き換え、f_equal を繰り返し適用する。
*)
Ltac rtcrefl := apply evalrtc_refl' ; do ?f_equal.

(*
exists_nop:
  何もしない(NOP)命令。
*)
Lemma exists_nop :
  { instnop : inst | forall vs cs, (vs, instnop :: cs) |=>* (vs, cs) }.
Proof.
  eexists=> vs cs.
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
  eexists=> i1 i2 vs cs.
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
Notation instseqc' := (fold_left instpair).

Lemma evalseqc' :
  forall il i vs cs, (vs, instseqc' il i :: cs) |=>* (vs, i :: il ++ cs).
Proof.
  elim=> [ | i il IH] i' vs cs.
  evalauto.
  evalpartial IH ; evalauto.
Qed.

Notation instseqc il := (instseqc' il instnop).

Lemma evalseqc : forall il vs cs, (vs, instseqc il :: cs) |=>* (vs, il ++ cs).
Proof.
  move=> il vs cs.
  evalpartial evalseqc'.
  evalauto.
Qed.

Lemma app_instseqc' :
  forall is1 is2 i, instseqc' (is1 ++ is2) i = instseqc' is2 (instseqc' is1 i).
Proof.
  apply fold_left_app.
Qed.

Lemma app_instseqc :
  forall is1 is2, instseqc (is1 ++ is2) = instseqc' is2 (instseqc is1).
Proof.
  move=> is1 is2 ; apply app_instseqc'.
Qed.

Notation instseqc_replicate' n i1 i2 :=
  (fold_right (flip instpair) i2 (replicate n i1)).

Notation instseqc_replicate n i := (instseqc_replicate' n i instnop).

Lemma instseqc_replicate_eq :
  forall n i1 i2, instseqc' (replicate n i1) i2 = instseqc_replicate' n i1 i2.
Proof.
  move=> n i1 i2.
  rewrite {2}replicate_rev_id.
  apply eq_sym, fold_left_rev_right.
Qed.

Lemma evalseqc_replicate' :
  forall n i1 i2 vs cs,
  (vs, instseqc_replicate' n i1 i2 :: cs) |=>* (vs, i2 :: replicate n i1 ++ cs).
Proof.
  move=> n i1 i2.
  rewrite -instseqc_replicate_eq ; apply evalseqc'.
Qed.

Lemma evalseqc_replicate :
  forall n i vs cs,
  (vs, instseqc_replicate n i :: cs) |=>* (vs, replicate n i ++ cs).
Proof.
  move=> n i vs cs.
  evalpartial evalseqc_replicate'.
  evalauto.
Qed.

(*
instseqv', instseqv:
  スタックに展開される命令の並びを記述するためのもの。
*)
Notation instseqv' := (fold_left (fun a b => instpair (instpush b) a)).

Lemma evalseqv' :
  forall il i vs cs, (vs, instseqv' il i :: cs) |=>* (il ++ vs, i :: cs).
Proof.
  elim=> [ | i' il IH ] i vs cs.
  evalauto.
  evalpartial IH.
  evalauto.
Qed.

Notation instseqv il := (instseqv' il instnop).

Lemma evalseqv : forall il vs cs, (vs, instseqv il :: cs) |=>* (il ++ vs, cs).
Proof.
  move=> il vs cs.
  evalpartial evalseqv'.
  evalauto.
Qed.

Lemma app_instseqv' :
  forall is1 is2 i, instseqv' (is1 ++ is2) i = instseqv' is2 (instseqv' is1 i).
Proof.
  apply fold_left_app.
Qed.

Lemma app_instseqv :
  forall is1 is2, instseqv (is1 ++ is2) = instseqv' is2 (instseqv is1).
Proof.
  move=> is1 is2 ; apply app_instseqv'.
Qed.
