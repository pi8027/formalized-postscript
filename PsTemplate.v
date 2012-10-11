Require Import
  Arith Arith.Min Lists.List Program.Syntax Omega ssreflect Common PsCore.

Section ListIndex.

Variable A : Type.

Inductive listindex : list A -> nat -> A -> Prop :=
  | lizero : forall x xs, listindex (x :: xs) 0 x
  | lisucc : forall x' xs n x, listindex xs n x -> listindex (x' :: xs) (S n) x.

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

Inductive fill_template' : list inst -> instt -> inst -> Prop :=
  | fillpop'   : fill_template' [] insttpop instpop
  | fillcopy'  : fill_template' [] insttcopy instcopy
  | fillswap'  : fill_template' [] insttswap instswap
  | fillcons'  : fill_template' [] insttcons instcons
  | fillquote' : fill_template' [] insttquote instquote
  | fillexec'  : fill_template' [] insttexec instexec
  | fillpush'  :
    forall l t i, fill_template' l t i ->
    fill_template' l (insttpush t) (instpush i)
  | fillpair'  :
    forall l1 l2 t1 t2 i1 i2,
    fill_template' l1 t1 i1 -> fill_template' l2 t2 i2 ->
    fill_template' (l1 ++ l2) (insttpair t1 t2) (instpair i1 i2)
  | fillhole'  : forall n i, fill_template' [i] (instthole n) i.

Lemma fill_template'_eqprop :
  forall l t,
  length l = length (holes_of_template t) <-> exists i, fill_template' l t i.
Proof.
  split.
  - move: t l ; elim ;
      try by simpl ; case=> [ | i l] H ;
        [apply: ex_intro ; constructor | inversion H].
    - move=> t IH l H.
      case (IH l H)=> i H0.
      by apply (ex_intro _ (instpush i)) ; constructor.
    - simpl=> t1 H1 t2 H2 l.
      rewrite app_length=> H.
      case (H2 (skipn (length (holes_of_template t1)) l)).
        rewrite skipn_length ; omega.
      case (H1 (firstn (length (holes_of_template t1)) l)).
        rewrite firstn_length.
        case (dec_le (length (holes_of_template t1)) (length l)) => H0.
        - by rewrite min_l.
        - omega.
      clear H H1 H2.
      move=> i1 H i2 H0.
      rewrite -(firstn_skipn (length (holes_of_template t1)) l).
      apply (ex_intro _ (instpair i1 i2)).
      by econstructor.
    - simpl.
      move=> n [ | i1 [ | i2 l]] H ; inversion H.
      apply (ex_intro _ i1) ; constructor.
  - move: t l ; elim ; try by move=> l [i H] ; inversion H.
    - move=> t IH l [i H].
      inversion H.
      by apply IH, (ex_intro _ i0).
    - move=> t1 H1 t2 H2 l [i H].
      inversion H.
      clear i H H0 H3 H4 H6.
      simpl ; rewrite !app_length ; f_equal.
      by apply H1, (ex_intro _ i1).
      by apply H2, (ex_intro _ i2).
    - move=> n l [i H].
      by inversion H.
Qed.

Lemma fill_template'_dec :
  forall l t, sb_decidable (exists i, fill_template' l t i).
Proof.
  move=> l t.
  apply (iff_decidable _ _ (fill_template'_eqprop l t)), eq_nat_dec.
Defined.

Theorem fill_template_eqprop2 :
  forall l t i,
    (exists l', listindices _ l (holes_of_template t) l' /\
      fill_template' l' t i) <->
    fill_template l t i.
Proof.
  split ; move:t i.
  - elim ; try by move=> i [l' [H H0]] ; inversion H0 ; constructor.
    - move=> t IH i [l' [H H0]].
      inversion H0.
      by apply fillpush, IH, (ex_intro _ l').
    - move=> t1 H t2 H0 i [l' []] ; simpl=> H2 H1 ; move: H2.
      inversion H1.
      clear i l' H1 H2 H3 H4 H6 => H1.
      case (Forall2_app_inv_l (holes_of_template t1) (holes_of_template t2) H1)
        => [l1' [l2' [H2 [H3 H4]]]].
      replace l1' with l1 in H2, H4.
      replace l2' with l2 in H3.
      - constructor.
        by apply H, (ex_intro _ l1).
        by apply H0, (ex_intro _ l2).
      - apply (app_inv_head _ _ _ H4).
      - apply eq_trans with (firstn (length (holes_of_template t1)) (l1 ++ l2)).
        - rewrite -(proj2 (fill_template'_eqprop l1 t1)
            (ex_intro (fill_template' l1 t1) i1 H5)).
          apply app_length_firstn.
        - rewrite H4.
          rewrite (Forall2_eq_length _ _ _ _ _ H2).
          apply eq_sym, app_length_firstn.
    - move=> n i [l' [H H0]].
      constructor.
      inversion H.
      inversion H0.
      replace i with y ; congruence.
  - elim ; try by move=> i H ; inversion H ; do !econstructor.
    - move=> t IH i H.
      inversion H.
      clear i H H0 H1 H3.
      case (IH i0 H2) => l' [H H0].
      exists l' ; split.
      - auto.
      - by constructor.
    - simpl.
      move=> t1 H t2 H0 i H1.
      inversion H1.
      clear i H1 H2 H3 H4 H6.
      case (H i1 H5) => ll [H1 H2].
      case (H0 i2 H7) => lr [H3 H4].
      clear l0 t0 t3 H H0 H5 H7.
      exists (ll ++ lr) ; split.
      by apply Forall2_app.
      by constructor.
    - simpl.
      move=> n i H.
      inversion H.
      exists [i] ; split ; by constructor.
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

Lemma exists_inst_listindices_iter :
  forall len ns, { inst_listindices |
  forall xs ys zs, length xs = len -> listindices inst xs ns ys -> forall vs cs,
  (instseqv zs :: xs ++ vs, inst_listindices :: cs) |=>*
  (instseqv (zs ++ ys) :: xs ++ vs, cs) }.
Proof.
  move=> len ; elim=> [ | n ns [i IH] ] ;
    eexists=> xs ys zs H H0 vs cs ; inversion H0.
  - evalpartial evalnop.
    by rtcrefl ; rewrite app_nil_r.
  - clear ys x l H0 H1 H2 H4.
    evalpartial' (proj2_sig (exists_inst_listindex (S n))
      (instseqv zs :: xs) y (lisucc _ _ _ _ _ H3)).
    simpl.
    evalpartial' evalquote.
    evalpartial' evalsnoc.
    rewrite -/(instseqv' [y] (instseqv zs))
      -(app_instseqv zs [y]) -/([y] ++ l') app_assoc.
    apply (IH xs l' (zs ++ [y]) H H5).
Defined.

Theorem exists_clear_used :
  forall len, { inst_clear_used |
  forall i vs1, length vs1 = len -> forall vs2 cs,
  (i :: vs1 ++ vs2, inst_clear_used :: cs) |=>* (i :: vs2, cs) }.
Proof.
  elim=> [ | n [i1 IH] ] ; eexists=> i2.
  - case=> [ | v vs1] H vs2 cs.
    - evalpartial evalnop.
      evalauto.
    - inversion H.
  - case=> [ | v vs1] H vs2 cs ; inversion H.
    simpl.
    evalpartial' evalswap.
    evalpartial' evalpop.
    apply (IH i2 vs1 H1).
Defined.

Theorem exists_inst_listindices :
  forall len ns, { inst_listindices |
  forall xs ys, length xs = len -> listindices inst xs ns ys -> forall vs cs,
  (xs ++ vs, inst_listindices :: cs) |=>* (ys ++ vs, cs) }.
Proof.
  move=> len ns ; eexists=> xs ys H H0 vs cs.
  evalpartial' evalpush.
  evalpartial' (proj2_sig (exists_inst_listindices_iter len ns) xs ys [] H H0).
  evalpartial' (proj2_sig (exists_clear_used len) (instseqv ys) xs H).
  evalpartial evalexec.
  apply evalseqv.
Defined.

Lemma exists_inst_fill_template'_iter :
  forall t, { inst_fill_template' |
  forall l i1, fill_template' l t i1 -> forall i2 vs cs,
  (i2 :: l ++ vs, inst_fill_template' :: cs) |=>* (i2 :: i1 :: vs, cs) }.
Proof.
  elim ;
    try by eexists=> l i1 H i2 vs cs ; inversion H ;
      evalpartial' evalpush ; evalpartial evalswap ; evalauto.
  - move=> t [i3 IH] ; eexists=> l i1 H i2 vs cs.
    inversion H.
    evalpartial' (IH l i H2).
    evalpartial' evalswap.
    evalpartial' evalquote.
    evalpartial evalswap.
    evalauto.
  - move=> t1 [i1 IH1] t2 [i2 IH2] ; eexists=> l i3 H i4 vs cs.
    inversion H.
    rewrite -app_assoc.
    evalpartial' (IH1 l1 i0 H3).
    evalpartial' evalquote.
    evalpartial' evalswap.
    evalpartial' evalquote.
    evalpartial' evalcons.
    evalpartial' (IH2 l2 i5 H5).
    evalpartial' evalswap.
    evalpartial' evalquote.
    evalpartial' evalcons.
    evalpartial' evalexec.
    evalauto.
    evalpartial' evalcons.
    evalpartial evalswap.
    evalauto.
  - move=> n ; eexists=> l i1 H i2 vs cs.
    inversion H.
    evalpartial evalnop.
    evalauto.
Defined.

Theorem exists_inst_fill_template' :
  forall t, { inst_fill_template' |
  forall l i, fill_template' l t i -> forall vs cs,
  (l ++ vs, inst_fill_template' :: cs) |=>* (i :: vs, cs) }.
Proof.
  move=> t ; eexists=> l i H vs cs.
  evalpartial' (evalpush instpop).
  evalpartial' (proj2_sig (exists_inst_fill_template'_iter t) l i H).
  evalpartial evalpop.
  evalauto.
Defined.

Theorem exists_inst_fill_template :
  forall len t, { inst_fill_template |
  forall l i, length l = len -> fill_template l t i -> forall vs cs,
  (l ++ vs, inst_fill_template :: cs) |=>* (i :: vs, cs) }.
Proof.
  move=> len t ; eexists=> l i.
  rewrite -fill_template_eqprop2.
  move=> H [l' [H0 H1]] vs cs.
  evalpartial'
    (proj2_sig (exists_inst_listindices len (holes_of_template t)) l l' H H0).
  evalpartial (proj2_sig (exists_inst_fill_template' t) l' i H1).
  evalauto.
Defined.
