Require Export ch2o.abstract_c.architectures.
Require Export ch2o.axiomatic.assertions.
Require Export ch2o.axiomatic.axiomatic_statements.
Require Export ch2o.axiomatic.axiomatic_expressions.
Require Export ch2o.axiomatic.axiomatic_adequate.

Definition A: architecture := {|
  arch_sizes := architectures.lp64;
  arch_big_endian := false;
  arch_char_signedness := Signed;
  arch_alloc_can_fail := false
|}.
Notation K := (arch_rank A).

Definition store := list (option Z).

Inductive eval `{Env K}: store -> expr K -> Z -> Prop :=
| eval_lit st z:
  int_typed z sintT ->
  eval st (# intV{sintT} z) z
| eval_load_var st i z:
  st !! i = Some (Some z) ->
  eval st (load (var i)) z
.

Definition points_to i mv: assert K :=
  match mv with
    None =>
    var i ↦{false, perm_full} - : sintT%BT
  | Some z =>
    var i ↦{false, perm_full} (# intV{sintT} z) : sintT%BT
  end.

Fixpoint assert_stack(st: store): assert K :=
  match st with
    [] => emp
  | mv::st =>
    points_to 0 mv ★ assert_stack st ↑
  end.

Lemma assert_stack_load (Γ: env K) δ st i z:
  st !! i = Some (Some z) ->
  assert_stack st ⊆{Γ,δ} (load (var i) ⇓ inr (intV{sintT} z))%A.
revert i.
induction st.
- discriminate.
- destruct i.
  + simpl; intros.
    injection H; clear H; intros; subst.
    rewrite <- assert_memext_l with (P:=(load (var 0) ⇓ inr (intV{sintT} z))%A) (Q:=(assert_stack st↑)%A).
    * apply assert_sep_preserving; try reflexivity.
      apply assert_singleton_eval.
      reflexivity.
    * auto with typeclass_instances.
  + simpl; intros.
    rewrite <- assert_memext_r with (Q:=points_to 0 a) (P:=(load (var (S i)) ⇓ inr (intV{sintT} z))%A); [|auto with typeclass_instances].
    apply assert_sep_preserving; [reflexivity|].
    rewrite IHst with (2:=H).
    rewrite assert_lift_expr.
    reflexivity.
Qed.

Lemma eval_sound (Γ: env K) δ st e z:
  eval st e z ->
  (assert_stack st ⊆{Γ,δ} e ⇓ inr (intV{sintT} z))%A.
induction 1.
- apply assert_int_typed_eval; assumption.
- apply assert_stack_load with (1:=H).
Qed.

Inductive outcome := onormal(s: store) | oreturn(z: Z).

Inductive exec `{Env K}: store -> stmt K -> outcome -> Prop :=
| exec_local_normal st s mv st':
  exec (None::st) s (onormal (mv::st')) ->
  exec st (local{sintT%BT} s) (onormal st')
| exec_local_return st s z:
  exec (None::st) s (oreturn z) ->
  exec st (local{sintT%BT} s) (oreturn z)
| exec_assign st i e z:
  i < length st ->
  eval st e z ->
  exec st (var i ::= cast{sintT%BT} e) (onormal (<[i:=Some z]>st))
| exec_seq st s1 st' s2 O:
  exec st s1 (onormal st') ->
  exec st' s2 O ->
  exec st (s1 ;; s2) O
| exec_ret st e z:
  eval st e z ->
  exec st (ret (cast{sintT%BT} e)) (oreturn z)
.

Definition R (st: store) (O: outcome): val K -> assert K :=
  λ v,
  (∃st',
   assert_stack st' ★
   ⌜length st' = length st /\
    ∃z, O = oreturn z /\ v = intV{sintT} z⌝)%A.

Definition J: labelname -> assert K := (λ _, False%A).
Definition T: nat -> assert K := (λ _, False%A).
Definition C: option Z -> assert K := (λ _, False%A).

Lemma exec_sound_lemma (Γ: env K) δ st s O:
  exec st s O ->
  Γ\ δ\ R st O\ J\ T\ C ⊨ₛ
  {{ assert_stack st }} s {{ ∃st', assert_stack st' ★ ⌜O = onormal st'⌝ }}.
induction 1.
- (* exec_local_normal *)
  apply ax_local.
  apply ax_stmt_weaken with (8:=IHexec); intros.
  + unfold R.
    apply assert_exist_elim; intro st'0.
    apply assert_Prop_intro_r.
    intros.
    destruct H0.
    destruct H1.
    destruct H1.
    discriminate.
  + unfold J.
    apply assert_False_elim.
  + unfold J.
    rewrite stack_indep.
    apply @RightAbsorb_instance_2.
  + unfold T.
    apply assert_False_elim.
  + unfold C.
    rewrite stack_indep.
    apply @RightAbsorb_instance_2.
  + simpl.
    reflexivity.
  + apply assert_exist_elim. intro st'0.
    apply assert_Prop_intro_r. intro HO.
    injection HO; clear HO; intros; subst.
    simpl.
    apply assert_sep_preserving.
    * destruct mv.
      -- eapply assert_exist_intro.
         unfold points_to.
         reflexivity.
      -- reflexivity.
    * rewrite assert_lift_exists.
      eapply assert_exist_intro.
      rewrite assert_lift_sep.
      rewrite stack_indep.
      rewrite assert_Prop_r. 2:reflexivity.
      reflexivity.
- apply ax_local.
  apply ax_stmt_weaken with (8:=IHexec); intros.
  + unfold R.
    apply assert_exist_elim; intro st'.
    apply assert_Prop_intro_r.
    intros.
    destruct H0.
    destruct H1.
    destruct H1.
    injection H1; clear H1; intros; subst.
    destruct st' as [|mv st']; [discriminate|].
    simpl.
    apply assert_sep_preserving.
    * destruct mv.
      -- eapply assert_exist_intro.
         unfold points_to.
         reflexivity.
      -- reflexivity.
    * rewrite assert_lift_exists.
      apply assert_exist_intro with (x0:=st').
      rewrite assert_lift_sep.
      rewrite stack_indep.
      rewrite assert_Prop_r.
      -- reflexivity.
      -- split.
         ++ simpl in H0; congruence.
         ++ eexists; tauto.
  + unfold J.
    apply assert_False_elim.
  + unfold J.
    rewrite stack_indep.
    apply @RightAbsorb_instance_2.
  + unfold T.
    apply assert_False_elim.
  + unfold C.
    rewrite stack_indep.
    apply @RightAbsorb_instance_2.
  + simpl.
    reflexivity.
  + apply assert_exist_elim. intro st'0.
    apply assert_Prop_intro_r. intro HO.
    discriminate.

Theorem exec_sound Γ δ (s: stmt K) z S f:
  ✓ Γ ->
  exec [] s (oreturn z) ->
  is_final_state S ->
  Γ\ δ\ [] ⊢ₛ State [CParams f []] (Stmt ↘ s) ∅ ⇒* S ->
  exists m,
  Γ\ δ\ [] ⊢ₛ State [CParams f []] (Stmt (⇈ (intV{sintT} z)) s) m ⇒* S.
intros.
apply exec_sound_lemma with (1:=H) (2:=H1) (3:=H0) (4:=H2).
- split.
  + apply cmap_empty_valid.
    simpl.
    rewrite fmap_empty.
    apply memenv_empty_valid.
  + rewrite cmap_erase_empty.
    apply stack_mem_empty.
    * assumption.
    * simpl. rewrite fmap_empty.
      apply memenv_empty_valid.
- intros.
  inv_rcsteps H5. elim H1. inv_rcstep.
- intros.
  injection H3; clear H3; intros; subst.
  eexists; eassumption.
Qed.
