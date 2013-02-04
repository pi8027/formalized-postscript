Require Import
  Coq.Numbers.Natural.Peano.NPeano Coq.Lists.List Omega
  Ssreflect.ssreflect Ssreflect.ssrnat Ssreflect.seq
  FormalPS.stdlib_ext FormalPS.Core.

Section ListIndex.

Variable A : Type.

Inductive listindex : list A -> nat -> A -> Prop :=
  | lizero : forall x xs, listindex (x :: xs) 0 x
  | lisucc : forall x' xs n x, listindex xs n x -> listindex (x' :: xs) n.+1 x.

Theorem lift_listindex :
  forall xs ys n a, listindex ys n a -> listindex (xs ++ ys) (length xs + n) a.
Proof.
  elim => [ | x xs IH ].
  auto.
  simpl; constructor; auto.
Qed.

Theorem dec_listindex :
  forall xs n, sb_decidable (exists a, listindex xs n a).
Proof.
  elim => [ | x xs IH] n.
  - right; case=> i H; inversion H.
  - case: n => [ | n].
    - left; exists x; constructor.
    - case (IH n) => H.
      - by left; case: H => i H; exists i; constructor.
      - by right => H0; apply: H; case: H0 => i H0; exists i; inversion H0.
Defined.

Theorem partial_listindex :
  forall xs n, option {a : A | listindex xs n a}.
Proof.
  elim => [ | x xs IH] n.
  - apply None.
  - case: n => [ | n].
    - apply Some; exists x; constructor.
    - case (IH n) => [[i H] | ].
      - by apply Some; exists i; constructor.
      - apply None.
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

End ListIndex.

Inductive instt : Set :=
  | insttpop | insttcopy | insttswap | insttcons | insttquote | insttexec
  | insttpush of instt
  | insttpair of instt & instt
  | instthole of nat.

Fixpoint holes_of_template (t : instt) : list nat :=
  match t with
    | insttpush i => holes_of_template i
    | insttpair i1 i2 => holes_of_template i1 ++ holes_of_template i2
    | instthole n => [:: n]
    | _ => [::]
  end.

Fixpoint instt_length (t : instt) : nat :=
  match t with
    | insttpush t => (instt_length t)
    | insttpair t1 t2 => (instt_length t1 + instt_length t2)
    | _ => 0
  end.+1.

Fixpoint lift_instt (n : nat) (t : instt) : instt :=
  match t with
    | insttpush t => insttpush (lift_instt n t)
    | insttpair t1 t2 => insttpair (lift_instt n t1) (lift_instt n t2)
    | instthole m => instthole (n + m)
    | _ => t
  end.

Fixpoint instt_of_inst (i : inst) : instt :=
  match i with
    | instpop => insttpop
    | instcopy => insttcopy
    | instswap => insttswap
    | instcons => insttcons
    | instquote => insttquote
    | instexec => insttexec
    | instpush i => insttpush (instt_of_inst i)
    | instpair i1 i2 => insttpair (instt_of_inst i1) (instt_of_inst i2)
  end.

Theorem instt_length_lifted :
  forall n t, instt_length t = instt_length (lift_instt n t).
Proof.
  move=> n; elim; simpl; f_equal; auto.
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
  move=> xs ys; elim; try by move=> i H; inversion H; constructor.
  - move=> t IH i H.
    inversion H.
    simpl; constructor; auto.
  - move=> t1 IH1 t2 IH2 i H.
    inversion H.
    simpl; constructor; auto.
  - move=> n i H.
    inversion H.
    by simpl; constructor; apply lift_listindex.
Qed.

Theorem dec_fill_template :
  forall l t, sb_decidable (exists i, fill_template l t i).
Proof.
  move=> l; elim; try by (left; eexists; econstructor).
  - move=> t; elim=> H.
    - by left; elim: H => i H; exists (instpush i); constructor.
    - right=> H0; apply: H; case: H0 => i H0; inversion H0.
      by exists i0.
  - move=> t1; elim=> H1.
    - move=> t2; elim=> H2.
      - left; elim: H1 => i1 H1; elim: H2 => i2 H2.
        by exists (instpair i1 i2); constructor.
      - right=> H3; apply: H2; case: H3 => i H3; inversion H3.
        by exists i2.
    - move=> t H2.
      right=> H3; apply: H1; case: H3 => i H3; inversion H3.
      by exists i1.
  - move=> n.
    case (dec_listindex _ l n) => H.
    - by left; case: H => i H; exists i; constructor.
    - by right => H0; apply H; case: H0 => i H0; exists i; inversion H0.
Defined.

Theorem partial_fill_template :
  forall l t, option {i : inst | fill_template l t i}.
Proof.
  move=> l; elim; try by (apply Some; eexists; econstructor).
  - move=> t [[i H] | ].
    - by apply Some; exists (instpush i); constructor.
    - apply None.
  - move=> t1 [[i1 H1] | ].
    - move=> t2 [[i2 H2] | ].
      - by apply Some; exists (instpair i1 i2); constructor.
      - apply None.
    - move=> t2 H2; apply None.
  - move=> n.
    case (partial_listindex _ l n) => [[i H] | ].
    - by apply Some; exists i; constructor.
    - apply None.
Defined.

Theorem partial_fill_template' :
  forall l tl, option {il : list inst | Forall2 (fill_template l) tl il}.
Proof.
  move=> l; elim.
  - by apply Some; apply: (exist _ [::]).
  - move=> t tl; case => [[il H] | ].
    - case (partial_fill_template l t) => [[i H0] | ].
      - by apply Some; exists (i :: il); constructor.
      - apply None.
    - apply None.
Defined.

Theorem unique_fill_template :
  forall l t i1 i2, fill_template l t i1 -> fill_template l t i2 -> i1 = i2.
Proof.
  move=> l; elim; try by move=> i1 i2 H H0; inversion H; inversion H0.
  - move=> t IH i1 i2 H H0.
    inversion H.
    inversion H0.
    f_equal; auto.
  - move=> t1 IH1 t2 IH2 i1 i2 H H0.
    inversion H.
    inversion H0.
    f_equal; auto.
  - move=> n i1 i2 H H0.
    inversion H.
    inversion H0.
    apply (unique_listindex _ l n); auto.
Qed.

Lemma exists_inst_listindex_iter :
  forall n, { inst_listindex |
  forall xs x ys, listindex inst xs n x -> forall vs cs,
  (instseqv ys :: xs ++ vs, inst_listindex :: cs) |=>*
  (x :: ys ++ xs ++ vs, cs) }.
Proof.
  elim=> [ | n [i IH]]; eexists=> xs x ys H vs cs; inversion H.
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
    rewrite -/(instseqv' (instseqv ys) [:: x'])
      -(app_instseqv ys [:: x']) -/([:: x'] ++ xs0 ++ vs) catA.
    apply (IH xs0 x (ys ++ [:: x']) H2).
Defined.

Theorem exists_inst_listindex :
  forall n, { inst_listindex |
  forall xs x, listindex inst xs n x -> forall vs cs,
  (xs ++ vs, inst_listindex :: cs) |=>* (x :: xs ++ vs, cs) }.
Proof.
  move=> n; eexists=> xs x H vs cs.
  evalpartial' evalpush.
  evalpartial (proj2_sig (exists_inst_listindex_iter n) xs x [::] H).
  evalauto.
Defined.

Lemma exists_inst_fill_template_iter :
  forall len t, { inst_fill_template |
  forall l i, length l = len -> fill_template l t i -> forall vs cs,
  (l ++ vs, inst_fill_template :: cs) |=>* (i :: l ++ vs, cs) }.
Proof.
  move=> len t; move: t len.
  refine (induction_gtof2 _ instt_length _ _).
  rewrite /gtof; case; try by move=> H len;
    eexists=> l i H0 H1 vs cs; inversion H1; evalpartial evalpush; evalauto.
  - simpl=> t IH len; eexists=> l i H H0 vs cs.
    inversion H0.
    clear i l0 t0 H0 H1 H2 H4.
    evalpartial' (proj2_sig (IH t (le_n (instt_length t).+1) len) l i0 H H3).
    evalpartial evalquote.
    evalauto.
  - simpl=> t1 t2 IH len; eexists=> l i H H0 vs cs.
    inversion H0.
    clear i l0 t0 t3 H0 H1 H2 H3 H5.
    evalpartial' (proj2_sig (IH t1 (le_n_S _ _ (le_plus_l _ _)) len) l i1 H H4).
    evalpartial' (proj2_sig (IH (lift_instt 1 t2)
      ((le_n_S _ _ (le_trans _ _ _
        (Nat.eq_le_incl _ _ (eq_sym (instt_length_lifted 1 t2)))
        (le_plus_r _ _)))) len.+1)
      (i1 :: l) i2 (eq_S _ _ H) (lift_fill_template [:: i1] l t2 i2 H6)).
    simpl.
    evalpartial evalcons.
    evalauto.
  - simpl=> n _ len; eexists=> l i H H0 vs cs.
    inversion H0.
    evalpartial (proj2_sig (exists_inst_listindex n) l i H3).
    evalauto.
Defined.

Theorem exists_clear_used :
  forall len, { inst_clear_used |
  forall i vs1, length vs1 = len -> forall vs2 cs,
  (i :: vs1 ++ vs2, inst_clear_used :: cs) |=>* (i :: vs2, cs) }.
Proof.
  elim=> [ | n [i1 IH] ]; eexists=> i2.
  - case=> [ | v vs1] H vs2 cs.
    - evalpartial evalnop.
      evalauto.
    - inversion H.
  - case=> [ | v vs1] H vs2 cs; inversion H.
    simpl.
    evalpartial' evalswap.
    evalpartial' evalpop.
    apply (IH i2 vs1 H1).
Defined.

Theorem exists_inst_fill_template' :
  forall len t, { inst_fill_template |
  forall l i, length l = len -> fill_template l t i -> forall vs cs,
  (l ++ vs, inst_fill_template :: cs) |=>* (i :: vs, cs) }.
Proof.
  move=> len t; eexists=> l i H H0 vs cs.
  evalpartial' (proj2_sig (exists_inst_fill_template_iter len t) l i H H0).
  apply (proj2_sig (exists_clear_used len) i l H).
Defined.

Theorem exists_inst_fill_template :
  forall len tvs tcs, { inst_fill_template |
    forall l vs' cs', length l = len ->
    Forall2 (fill_template l) tvs vs' ->
    Forall2 (fill_template l) tcs cs' -> forall vs cs,
    (l ++ vs, inst_fill_template :: cs) |=>* (vs' ++ vs, cs' ++ cs) }.
Proof.
  move=> len tvs tcs; eexists=> l vs' cs' H H0 H1.
  have: fill_template l
    (fold_left (fun a b => insttpair (insttpush b) a) tvs
      (fold_left insttpair tcs (instt_of_inst instnop)))
    (instseqv' (instseqc cs') vs').
    clear len H.
    have: fill_template l
      (fold_left insttpair tcs (instt_of_inst instnop)) (instseqc cs').
      clear tvs vs' H0.
      have: fill_template l (instt_of_inst instnop) instnop.
        do !constructor.
      move: {+} instnop (instt_of_inst instnop).
      move: tcs cs' H1; elim.
      - by move=> cs' H; inversion H.
      - move=> tc tcs IH cs' H i t H0.
        inversion H; simpl; apply IH; auto.
        by constructor.
    move: {+} (fold_left insttpair tcs (instt_of_inst instnop)) (instseqc cs').
    clear tcs cs' H1; move: tvs vs' H0; elim.
    - by move=> vs' H t i H0; inversion H.
    - move=> tv tvs IH vs' H t i H0.
      inversion H; simpl; apply IH; auto.
      by do! constructor.
  move=> H2 vs cs.
  evalpartial' (proj2_sig (exists_inst_fill_template' len _) l _ H H2).
  evalpartial evalexec.
  evalpartial evalseqv'.
  apply evalseqc.
Defined.

Tactic Notation "evaltemplate_eapply"
    constr(vs) constr(n) constr(tvs) constr(tcs) :=
  match eval hnf in (eq_nat_dec n (length (firstn n vs))) with
    | left ?H1 =>
      match eval compute in (partial_fill_template' (firstn n vs) tvs) with
        | Some (exist _ ?vs' ?H2) =>
          match eval compute in (partial_fill_template' (firstn n vs) tcs) with
            | Some (exist _ ?cs' ?H3) =>
              eapply (proj2_sig (exists_inst_fill_template n tvs tcs)
                      (firstn n vs) vs' cs' H1 H2 H3)
          end
        end
  end.

Tactic Notation "evaltemplate_evalpartial'"
    constr(vs) constr(n) constr(tvs) constr(tcs) :=
  match eval hnf in (eq_nat_dec n (length (firstn n vs))) with
    | left ?H1 =>
      match eval compute in (partial_fill_template' (firstn n vs) tvs) with
        | Some (exist _ ?vs' ?H2) =>
          match eval compute in (partial_fill_template' (firstn n vs) tcs) with
            | Some (exist _ ?cs' ?H3) =>
              evalpartial' (proj2_sig (exists_inst_fill_template n tvs tcs)
                            (firstn n vs) vs' cs' H1 H2 H3)
          end
        end
  end.

Tactic Notation "evaltemplate" constr(n) constr(tvs) constr(tcs) :=
  match goal with
    | |- (?vs, _) |=>* _ =>
      evaltemplate_eapply vs n tvs tcs
    | |- exists _, _ /\ (?vs, _) |=>* _ =>
      evaltemplate_eapply vs n tvs tcs
  end.

Tactic Notation "evaltemplate'" constr(n) constr(tvs) constr(tcs) :=
  match goal with
    | |- (?vs, _) |=>* _ =>
      evaltemplate_evalpartial' vs n tvs tcs
    | |- exists _, _ /\ (?vs, _) |=>* _ =>
      evaltemplate_evalpartial' vs n tvs tcs
  end; subst_evars; simpl.
