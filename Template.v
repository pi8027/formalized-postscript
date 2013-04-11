Require Import
  Coq.Lists.List Coq.Program.Wf
  Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.seq
  FormalPS.stdlib_ext FormalPS.Core.

Set Implicit Arguments.

Section ListIndex.

Variable A : Type.

Fixpoint listindex (xs : seq A) n x :=
  if xs is x' :: xs
    then (if n is n.+1 then listindex xs n x else x = x')
    else False.

Theorem lift_listindex :
  forall xs ys n a, listindex ys n a -> listindex (xs ++ ys) (size xs + n) a.
Proof.
  by elim.
Qed.

Theorem dec_listindex :
  forall xs n, { a | listindex xs n a } + ({ a | listindex xs n a } -> False).
Proof.
  elim => [| x xs IH] /=.
  - by right; case.
  - by case => //; left; exists x.
Defined.

Theorem unique_listindex :
  forall xs n x y, listindex xs n x -> listindex xs n y -> x = y.
Proof.
  elim => // x xs IHxs; case => //= x' y H H0; congruence.
Qed.

End ListIndex.

Inductive instt : Set :=
  | insttpop | insttcopy | insttswap | insttcons | insttquote | insttexec
  | insttpush of instt
  | insttpair of instt & instt
  | instthole of nat.

Fixpoint holes_of_template (t : instt) : seq nat :=
  match t with
    | insttpush i => holes_of_template i
    | insttpair i1 i2 => holes_of_template i1 ++ holes_of_template i2
    | instthole n => [:: n]
    | _ => [::]
  end.

Fixpoint instt_size (t : instt) : nat :=
  match t with
    | insttpush t => (instt_size t)
    | insttpair t1 t2 => (instt_size t1 + instt_size t2)
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

Theorem instt_size_lifted :
  forall n t, instt_size t = instt_size (lift_instt n t).
Proof.
  move => n; elim => //=; f_equal; auto.
Qed.

Inductive fill_template : seq inst -> instt -> inst -> Prop :=
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
    forall l n i, listindex l n i -> fill_template l (instthole n) i.

Theorem fill_instt_of_inst : forall xs i, fill_template xs (instt_of_inst i) i.
Proof.
  by move => xs; elim; constructor.
Qed.

Theorem lift_fill_template :
  forall xs ys t i, fill_template ys t i ->
  fill_template (xs ++ ys) (lift_instt (size xs) t) i.
Proof.
  move => xs.
  apply fill_template_ind; constructor => //.
  by apply lift_listindex.
Qed.

Theorem dec_fill_template :
  forall l t, {i | fill_template l t i} + ({i | fill_template l t i} -> False).
Proof.
  move => l; elim; try by (left; eexists; econstructor).
  - move => t; elim => H.
    - by left; elim: H => i H; exists (instpush i); constructor.
    - right => H0; apply: H; case: H0;
        case => [||||||i|il ir] H; try by apply False_rec; inversion H.
      by exists i; inversion H.
  - move => t1; elim => H1.
    - move => t2; elim => H2.
      - left; elim: H1 => i1 H1; elim: H2 => i2 H2.
        by exists (instpair i1 i2); constructor.
      - right => H3; apply: H2; case: H3;
          case => [||||||i|il ir] H; try by apply False_rec; inversion H.
        by exists ir; inversion H.
    - move => t H2.
      right => H3; apply: H1; case: H3;
        case => [||||||i|il ir] H; try by apply False_rec; inversion H.
      by exists il; inversion H.
  - move => n; case (dec_listindex l n).
    - by case => i; left; eexists i; constructor.
    - by move => H; right; case => i H0 ; apply: H; exists i; inversion H0.
Defined.

Theorem dec_fill_template' :
  forall l tl,
    {il | Forall2 (fill_template l) tl il} +
    ({il | Forall2 (fill_template l) tl il} -> False).
Proof.
  move => l; elim.
  - by left; exists [::].
  - move => t tl; case => [[il H] | H].
    - case (dec_fill_template l t) => [[i H0] | H0].
      - by left; exists (i :: il); constructor.
      - right; case; case.
        - move => H1; inversion H1.
        - move => i il'; move => H1; apply H0.
          by exists i; inversion H1.
    - right; case => l' H1; inversion H1; apply: H.
      by exists l'0.
Defined.

Theorem unique_fill_template :
  forall l t i1 i2, fill_template l t i1 -> fill_template l t i2 -> i1 = i2.
Proof.
  move => l; elim; try by move => i1 i2 H H0; inversion H; inversion H0.
  - move => t IH i1 i2 H H0.
    inversion H.
    inversion H0.
    f_equal; auto.
  - move => t1 IH1 t2 IH2 i1 i2 H H0.
    inversion H.
    inversion H0.
    f_equal; auto.
  - move => n i1 i2 H H0.
    inversion H.
    inversion H0.
    by apply (unique_listindex l n).
Qed.

Lemma exists_inst_listindex_iter :
  forall n, { inst_listindex |
  forall xs x ys, listindex xs n x -> forall vs cs,
  (instseqv ys :: xs ++ vs, inst_listindex :: cs) |=>*
  (x :: ys ++ xs ++ vs, cs) }.
Proof.
  elim => [| n [i IH]]; eexists; case => //= x xs x' ys H vs cs.
  - subst.
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
  - evalpartial' evalswap.
    evalpartial' evalquote.
    evalpartial' evalsnoc.
    rewrite -/(instseqv' (instseqv ys) [:: x])
      -(app_instseqv ys [:: x]) -/([:: x] ++ xs ++ vs) catA.
    by apply IH.
Defined.

Theorem exists_inst_listindex :
  forall n, { inst_listindex |
  forall xs x, listindex xs n x -> forall vs cs,
  (xs ++ vs, inst_listindex :: cs) |=>* (x :: xs ++ vs, cs) }.
Proof.
  move => n; eexists => xs x H vs cs.
  evalpartial' evalpush.
  apply (proj2_sig (exists_inst_listindex_iter n) xs x [::] H).
Defined.

Lemma exists_inst_fill_template_iter :
  forall len t, { inst_fill_template |
  forall l i, size l = len -> fill_template l t i -> forall vs cs,
  (l ++ vs, inst_fill_template :: cs) |=>* (i :: l ++ vs, cs) }.
Proof.
  have Heq1: forall n m, n < (n + m).+1 by move => n m; rewrite ltnS leq_addr.
  have Heq2: forall n t1 t2,
    instt_size (lift_instt n t1) < (instt_size t2 + instt_size t1).+1
    by move => n t1 t2; rewrite ltnS -instt_size_lifted leq_addl.
  move => len t; move: t len.
  refine (well_founded_induction (measure_wf well_founded_lt instt_size) _ _).
  rewrite /MR; case; try by move => H len;
    eexists => l i H0 H1 vs cs; inversion H1; evalpartial evalpush; evalauto.
  - move => /= t IH len; eexists => l i H H0 vs cs.
    inversion H0; move => {i l0 t0 H0 H1 H2 H4}.
    evalpartial' (proj2_sig (IH t (ltnSn (instt_size t)) len) l i0 H H3).
    apply evalrtc_step, evalquote.
  - move => /= t1 t2 IH len; eexists => l i H H0 vs cs.
    inversion H0; move => {i l0 t0 t3 H0 H1 H2 H3 H5}.
    evalpartial' (proj2_sig (IH t1 (Heq1 _ _) len) l i1 H H4).
    evalpartial' (proj2_sig (IH (lift_instt 1 t2) (Heq2 1 t2 t1) len.+1)
      (i1 :: l) i2 (eq_S _ _ H) (@lift_fill_template [:: i1] l t2 i2 H6)) => /=.
    apply evalrtc_step, evalcons.
  - move => /= n _ len; eexists => l i H H0 vs cs.
    inversion H0.
    apply (proj2_sig (exists_inst_listindex n) l i H3).
Defined.

Theorem exists_clear_used :
  forall len, { inst_clear_used |
  forall i vs1, size vs1 = len -> forall vs2 cs,
  (i :: vs1 ++ vs2, inst_clear_used :: cs) |=>* (i :: vs2, cs) }.
Proof.
  elim => [| n [i1 IH]]; eexists => i2.
  - case => [| v vs1] H vs2 cs.
    - apply evalnop.
    - inversion H.
  - case => [| v vs1] H vs2 cs; inversion H => /=.
    evalpartial' evalswap.
    evalpartial' evalpop.
    apply (IH i2 vs1 H1).
Defined.

Theorem exists_inst_fill_template :
  forall len tvs tcs, { inst_fill_template |
    forall l vs' cs', size l = len ->
    Forall2 (fill_template l) tvs vs' ->
    Forall2 (fill_template l) tcs cs' -> forall vs cs,
    (l ++ vs, inst_fill_template :: cs) |=>* (vs' ++ vs, cs' ++ cs) }.
Proof.
  move => len tvs tcs; eexists => l vs' cs' H H0 H1.
  have: fill_template l
    (foldl (fun a b => insttpair (insttpush b) a)
      (foldl insttpair (instt_of_inst instnop) tcs) tvs)
    (instseqv' (instseqc cs') vs').
    move: tcs cs' H1 instnop
      (instt_of_inst instnop) (fill_instt_of_inst l instnop) {len H}.
    refine (Forall2_ind _ _ _) => //.
    - move: tvs vs' H0;
        refine (Forall2_ind _ _ _) => //= t i tl il H H0 H1 i' t' H2.
      by apply H1; do! constructor.
    - move => t i tl il H H1 H2 t' i' H3.
      by apply H2; constructor.
  move => H2 vs cs.
  evalpartial' (proj2_sig (exists_inst_fill_template_iter len _) l _ H H2).
  evalpartial' (proj2_sig (exists_clear_used len)).
  evalpartial evalexec.
  evalpartial evalseqv'.
  apply evalseqc.
Defined.

Tactic Notation "evaltemplate_evalpartial"
    constr(vs) constr(n) constr(tvs) constr(tcs) :=
  match eval compute in (Peano_dec.eq_nat_dec (size (firstn n vs)) n) with
    | left ?H1 =>
      match eval compute in (dec_fill_template' (firstn n vs) tvs) with
        | inl (exist _ ?vs' ?H2) =>
          match eval compute in (dec_fill_template' (firstn n vs) tcs) with
            | inl (exist _ ?cs' ?H3) =>
              evalpartial (proj2_sig (exists_inst_fill_template n tvs tcs)
                           (firstn n vs) vs' cs' H1 H2 H3)
          end
      end
  end.

Tactic Notation "evaltemplate_evalpartial'"
    constr(vs) constr(n) constr(tvs) constr(tcs) :=
  match eval compute in (Peano_dec.eq_nat_dec (size (firstn n vs)) n) with
    | left ?H1 =>
      match eval compute in (dec_fill_template' (firstn n vs) tvs) with
        | inl (exist _ ?vs' ?H2) =>
          match eval compute in (dec_fill_template' (firstn n vs) tcs) with
            | inl (exist _ ?cs' ?H3) =>
              evalpartial' (proj2_sig (exists_inst_fill_template n tvs tcs)
                            (firstn n vs) vs' cs' H1 H2 H3)
          end
      end
  end.

Tactic Notation "evaltemplate" constr(n) constr(tvs) constr(tcs) :=
  match goal with
    | |- (?vs, _) |=>* _ =>
      evaltemplate_evalpartial vs n tvs tcs
    | |- exists _, _ /\ (?vs, _) |=>* _ =>
      evaltemplate_evalpartial vs n tvs tcs
    | |- exists _, _ /\ exists _, _ /\ (?vs, _) |=>* _ =>
      evaltemplate_evalpartial vs n tvs tcs
  end; simpl.

Tactic Notation "evaltemplate'" constr(n) constr(tvs) constr(tcs) :=
  match goal with
    | |- (?vs, _) |=>* _ =>
      evaltemplate_evalpartial' vs n tvs tcs
    | |- exists _, _ /\ (?vs, _) |=>* _ =>
      evaltemplate_evalpartial' vs n tvs tcs
    | |- exists _, _ /\ exists _, _ /\ (?vs, _) |=>* _ =>
      evaltemplate_evalpartial' vs n tvs tcs
  end; simpl.
