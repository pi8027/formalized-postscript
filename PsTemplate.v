Require Import
  Numbers.Natural.Peano.NPeano Lists.List Program.Syntax Omega
  ssreflect Common PsCore.

Section ListIndex.

Variable A : Type.

Inductive listindex : list A -> nat -> A -> Prop :=
  | lizero : forall x xs, listindex (x :: xs) 0 x
  | lisucc : forall x' xs n x, listindex xs n x -> listindex (x' :: xs) (S n) x.

Theorem lift_listindex :
  forall xs ys n a, listindex ys n a -> listindex (xs ++ ys) (length xs + n) a.
Proof.
  elim => [ | x xs IH ].
  auto.
  simpl ; constructor ; auto.
Qed.

Lemma listindex_eqprop :
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
  apply (iff_decidable _ _ (listindex_eqprop xs n) (gt_dec (length xs) n)).
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

Lemma listindices_eqprop :
  forall xs ns, Forall (gt (length xs)) ns <-> exists ys, listindices xs ns ys.
Proof.
  move=> xs ; elim => [ | n ns IH] ; split=> H.
  - eexists [] ; constructor.
  - constructor.
  - inversion H.
    case (proj1 (listindex_eqprop xs n) H2) => y H4.
    case (proj1 IH H3) => ys H5.
    exists (y :: ys) ; constructor ; auto.
  - case: H ; case => [ | y ys ] H.
    - inversion H.
    - inversion H.
      constructor.
      - rewrite (listindex_eqprop xs n).
        by exists y.
      - apply (proj2 IH).
        by exists ys.
Qed.

Theorem dec_listindices :
  forall xs ns, sb_decidable (exists ys, listindices xs ns ys).
Proof.
  move=> xs ns.
  apply (iff_decidable _ _ (listindices_eqprop xs ns)).
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

Fixpoint holes_of_template (t : instt) : list nat :=
  match t with
    | insttpush i => holes_of_template i
    | insttpair i1 i2 => holes_of_template i1 ++ holes_of_template i2
    | instthole n => [n]
    | _ => []
  end.

Fixpoint instt_length (t : instt) : nat :=
  match t with
    | insttpush t => S (instt_length t)
    | insttpair t1 t2 => S (instt_length t1 + instt_length t2)
    | _ => 1
  end.

Fixpoint lift_instt (n : nat) (t : instt) : instt :=
  match t with
    | insttpush t => insttpush (lift_instt n t)
    | insttpair t1 t2 => insttpair (lift_instt n t1) (lift_instt n t2)
    | instthole m => instthole (n + m)
    | _ => t
  end.

Theorem instt_length_lifted :
  forall n t, instt_length t = instt_length (lift_instt n t).
Proof.
  move=> n ; elim ; simpl ; f_equal ; auto.
Qed.

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

Theorem lift_fill_template :
  forall xs ys t i, fill_template ys t i ->
  fill_template (xs ++ ys) (lift_instt (length xs) t) i.
Proof.
  move=> xs ys ; elim ; try by move=> i H ; inversion H ; constructor.
  - move=> t IH i H.
    inversion H.
    simpl ; constructor ; auto.
  - move=> t1 IH1 t2 IH2 i H.
    inversion H.
    simpl ; constructor ; auto.
  - move=> n i H.
    inversion H.
    by simpl ; constructor ; apply lift_listindex.
Qed.

Lemma fill_template_eqprop :
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
  apply (iff_decidable _ _ (fill_template_eqprop l t)), dec_listindices.
Defined.

Theorem unique_fill_template :
  forall l t i1 i2, fill_template l t i1 -> fill_template l t i2 -> i1 = i2.
Proof.
  move=> l ; elim ; try by move=> i1 i2 H H0 ; inversion H ; inversion H0.
  - move=> t IH i1 i2 H H0.
    inversion H.
    inversion H0.
    f_equal ; auto.
  - move=> t1 IH1 t2 IH2 i1 i2 H H0.
    inversion H.
    inversion H0.
    f_equal ; auto.
  - move=> n i1 i2 H H0.
    inversion H.
    inversion H0.
    apply (unique_listindex _ l n) ; auto.
Qed.

Lemma exists_inst_listindex_iter :
  forall n, { inst_listindex |
  forall xs x ys, listindex inst xs n x -> forall vs cs,
  (instseqv ys :: xs ++ vs, inst_listindex :: cs) |=>*
  (x :: ys ++ xs ++ vs, cs) }.
Proof.
  elim=> [ | n [i IH]] ; eexists=> xs x ys H vs cs ; inversion H.
  - simpl.
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
  - clear xs H n0 x0 H1 H0 H3.
    simpl.
    evalpartial' evalswap.
    evalpartial' evalquote.
    evalpartial' evalsnoc.
    rewrite -/(instseqv' [x'] (instseqv ys))
      -(app_instseqv ys [x']) -/([x'] ++ xs0 ++ vs) app_assoc.
    apply (IH xs0 x (ys ++ [x']) H2).
Defined.

Theorem exists_inst_listindex :
  forall n, { inst_listindex |
  forall xs x, listindex inst xs n x -> forall vs cs,
  (xs ++ vs, inst_listindex :: cs) |=>* (x :: xs ++ vs, cs) }.
Proof.
  move=> n ; eexists=> xs x H vs cs.
  evalpartial' evalpush.
  evalpartial (proj2_sig (exists_inst_listindex_iter n) xs x [] H).
  evalauto.
Defined.

Theorem exists_inst_fill_template :
  forall len t, { inst_fill_template |
  forall l i, length l = len -> fill_template l t i -> forall vs cs,
  (l ++ vs, inst_fill_template :: cs) |=>* (i :: l ++ vs, cs) }.
Proof.
  move=> len t ; move: t len.
  refine (induction_gtof2 _ instt_length _ _).
  rewrite /gtof ; case ; try by move=> H len ;
    eexists=> l i H0 H1 vs cs ; inversion H1 ; evalpartial evalpush ; evalauto.
  - simpl=> t IH len ; eexists=> l i H H0 vs cs.
    inversion H0.
    evalpartial' (proj2_sig (IH t (le_n (S (instt_length t))) len) l i0 H H3).
    evalpartial evalquote.
    evalauto.
  - simpl=> t1 t2 IH len ; eexists=> l i H H0 vs cs.
    inversion H0.
    clear i l0 t0 t3 H0 H1 H2 H3 H5.
    evalpartial' (proj2_sig (IH t1 (le_n_S _ _ (le_plus_l _ _)) len) l i1 H H4).
    evalpartial' (proj2_sig (IH (lift_instt 1 t2)
      ((le_n_S _ _ (le_trans _ _ _
        (Nat.eq_le_incl _ _ (eq_sym (instt_length_lifted 1 t2)))
        (le_plus_r _ _))))
      (S len)) (i1 :: l) i2 (eq_S _ _ H) (lift_fill_template [i1] l t2 i2 H6)).
    simpl.
    evalpartial evalcons.
    evalauto.
  - simpl=> n _ len ; eexists=> l i H H0 vs cs.
    inversion H0.
    evalpartial (proj2_sig (exists_inst_listindex n) l i H3).
    evalauto.
Defined.
