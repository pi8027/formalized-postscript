Require Import
  Arith Lists.List Program.Syntax ssreflect Common PsCore.

Section ListIndex.

Variable A : Type.

Inductive listindex : list A -> nat -> A -> Prop :=
  | lizero : forall x xs, listindex (x :: xs) 0 x
  | lisucc : forall x' xs n x, listindex xs n x -> listindex (x' :: xs) (S n) x.

Lemma listindex_cond :
  forall xs n, length xs > n <-> exists a, listindex xs n a.
Proof.
  elim=> [n | x xs IH [ | n]] ; split=> H.
  - inversion H.
  - case: H => x H.
    inversion H.
  - exists x.
    apply lizero.
  - simpl ; omega.
  - have: (exists a, listindex xs n a).
      apply (proj1 (IH n)).
      simpl in H ; omega.
    by case=> x' H1 ; exists x' ; constructor.
  - have: length xs > n.
      case: H => x' H.
      inversion H.
      apply: (proj2 (IH n) (ex_intro _ x' H4)).
    simpl=> H1 ; omega.
Qed.

Theorem dec_listindex :
  forall xs n, sb_decidable (exists a, listindex xs n a).
Proof.
  move=> xs n.
  apply (iff_decidable _ _ (listindex_cond xs n) (gt_dec (length xs) n)).
Defined.

Theorem unique_listindex :
  forall xs n x y, listindex xs n x -> listindex xs n y -> x = y.
Proof.
  elim=> [n | a xs IH [ | n]] x y H H0.
  - inversion H.
  - inversion H.
    inversion H0.
    congruence.
  - apply (IH n x y).
    by inversion H.
    by inversion H0.
Qed.

Notation listindices xs := (Forall2 (listindex xs)).

Lemma listindices_cond :
  forall xs ns, Forall (gt (length xs)) ns <-> exists ys, listindices xs ns ys.
Proof.
  move=> xs ; elim => [ | n ns IH] ; split=> H.
  - eexists [] ; constructor.
  - constructor.
  - inversion H.
    case (proj1 (listindex_cond xs n) H2) => y H4.
    case (proj1 IH H3) => ys H5.
    exists (y :: ys) ; constructor ; auto.
  - case: H ; case => [ | y ys ] H.
    - inversion H.
    - inversion H.
      constructor.
      - rewrite (listindex_cond xs n).
        by exists y.
      - apply (proj2 IH).
        by exists ys.
Qed.

Theorem dec_listindices :
  forall xs ns, sb_decidable (exists ys, listindices xs ns ys).
Proof.
  move=> xs ns.
  apply (iff_decidable _ _ (listindices_cond xs ns)).
  elim: ns => [ | n ns [IH | IH]].
  - left ; constructor.
  - case (gt_dec (length xs) n) => H.
    - by left ; constructor.
    - by right=> H1 ; apply: H ; inversion H1.
  - by right=> H0 ; apply: IH ; inversion H0.
Defined.

Theorem unique_listindices :
  forall xs ns ys zs, listindices xs ns ys -> listindices xs ns zs -> ys = zs.
Proof.
  move=> xs ; elim=> [ | n ns IH ] ; case=> [ | y ys] ; case => [ | z zs] H H0 ;
    inversion H ; inversion H0.
  - auto.
  - f_equal.
    - apply: unique_listindex ; eauto.
    - auto.
Qed.

End ListIndex.

Notation listindices A xs := (Forall2 (listindex A xs)).

Inductive instt : Set :=
  | insttpop   : instt
  | insttcopy  : instt
  | insttswap  : instt
  | insttcons  : instt
  | insttquote : instt
  | insttexec  : instt
  | insttpush  : instt -> instt
  | insttpair  : instt -> instt -> instt
  | instthole  : nat -> instt.

Inductive fill_template : list inst -> instt -> inst -> Prop :=
  | fillpop   : forall l, fill_template l insttpop instpop
  | fillcopy  : forall l, fill_template l insttcopy instcopy
  | fillswap  : forall l, fill_template l insttswap instswap
  | fillcons  : forall l, fill_template l insttcons instcons
  | fillquote : forall l, fill_template l insttquote instquote
  | fillexec  : forall l, fill_template l insttexec instexec
  | fillpush  :
    forall l t i, fill_template l t i ->
    fill_template l (insttpush t) (instpush i)
  | fillpair  :
    forall l t1 t2 i1 i2, fill_template l t1 i1 -> fill_template l t2 i2 ->
    fill_template l (insttpair t1 t2) (instpair i1 i2)
  | fillhole  :
    forall l n i, listindex inst l n i -> fill_template l (instthole n) i.

Fixpoint holes_of_template (t : instt) : list nat :=
  match t with
    | insttpush i => holes_of_template i
    | insttpair i1 i2 => holes_of_template i1 ++ holes_of_template i2
    | instthole n => [n]
    | _ => []
  end.

Lemma fill_template_cond :
  forall l t,
  (exists ys, listindices inst l (holes_of_template t) ys) <->
  (exists i, fill_template l t i).
Proof.
  split.
  - elim: t ; try by eexists ; constructor.
    - move=> t IH H.
      case (IH H) => i H0.
      exists (instpush i).
      by constructor.
    - move=> t1 H t2 H0 [ys H1].
      case (Forall2_app_inv_l (holes_of_template t1) (holes_of_template t2) H1)
        => ysl [ysr [H2 [H3 _]]].
      clear ys H1.
      case (H (ex_intro _ ysl H2)) => il H4.
      case (H0 (ex_intro _ ysr H3)) => ir H5.
      exists (instpair il ir).
      by constructor.
    - move=> n [ys H].
      inversion H.
      exists y.
      by constructor.
  - elim: t ; try by move=> H ; eexists [] ; constructor.
    - move=> t IH [i H].
      apply IH.
      inversion H.
      by exists i0.
    - move=> t1 H t2 H0 [i H1].
      inversion H1.
      elim (H (ex_intro _ i1 H5)) => [ysl H8].
      elim (H0 (ex_intro _ i2 H7)) => [ysr H9].
      exists (ysl ++ ysr).
      by simpl ; apply Forall2_app.
    - move=> n [i H].
      inversion H.
      exists [i].
      by do !constructor.
Qed.

Theorem dec_fill_template :
  forall l t, sb_decidable (exists i, fill_template l t i).
Proof.
  move=> l t.
  apply (iff_decidable _ _ (fill_template_cond l t)), dec_listindices.
Defined.

Lemma proof_inst_listindex :
  forall n, { inst_listindex |
  forall xs x ys vs cs, listindex inst xs n x ->
  (instseqv ys :: xs ++ vs, inst_listindex :: cs) |=>*
  (x :: ys ++ xs ++ vs, cs) }.
Proof.
  elim=> [ | n [i IH]] ; eexists=> xs x ys vs cs H.
  - inversion H.
    simpl.
    evalpartial' evalquote.
    evalpartial' evalswap.
    evalpartial' evalquote.
    evalpartial' evalcopy.
    evalpartial' evalcons.
    evalpartial' evalsnoc.
    evalpartial' evalexec.
    evalauto.
    evalpartial' evalswap.
    evalpartial' evalquote.
    evalpartial' evalcons.
    evalpartial evalexec.
    evalauto.
    evalpartial evalseqv.
    evalauto.
  - inversion H.
    clear xs H n0 x0 H1 H0 H3.
    simpl.
    evalpartial' evalswap.
    evalpartial' evalquote.
    evalpartial' evalsnoc.
    rewrite -/(instseqv' [x'] (instseqv ys))
      -(app_instseqv ys [x']) -/([x'] ++ xs0 ++ vs) (app_assoc ys [x']).
    apply (IH xs0 x (ys ++ [x']) vs cs H2).
Defined.
