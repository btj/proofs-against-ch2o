Require Export ch2o.abstract_c.architectures.
Require Export ch2o.axiomatic.assertions.
Require Export ch2o.axiomatic.axiomatic_statements.
Require Export ch2o.axiomatic.axiomatic_expressions.
Require Export ch2o.axiomatic.axiomatic_adequate.

Lemma emp_dup `{EnvSpec K} (P: assert K) (Γ: env K) δ:
  ((P ∧ emp)%A ⊆{Γ,δ} ((P ∧ emp) ★ (P ∧ emp)))%A.
unfold subseteqE.
unfold assert_entails.
intros.
unfold assert_and in *.
unfold assert_sep in *.
simpl in *.
destruct H7.
destruct H8.
subst.
exists ∅. exists ∅.
split.
- rewrite sep_right_id.
  + reflexivity.
  + apply sep_empty_valid.
- split.
  + rewrite sep_disjoint_list_double.
    apply sep_disjoint_empty_l.
    apply sep_empty_valid.
  + tauto.
Qed.

Lemma assert_lift_unlock `{EnvSpec K} (Γ: env K) δ P:
  (P ◊ ↑ ⊆{Γ,δ} P ↑ ◊)%A.
unfold subseteqE.
unfold assert_entails.
unfold assert_unlock.
unfold assert_lift.
simpl.
intros.
assumption.
Qed.

Lemma assert_lift_eval `{EnvSpec K} (Γ: env K) δ e ν:
  (e↑ ⇓ ν ⊆{Γ,δ} (e ⇓ ν)↑)%A.
unfold subseteqE.
unfold assert_entails.
unfold assert_expr.
unfold assert_lift.
simpl.
intros.
destruct H7 as [τlr [Ht He]].
rewrite expr_eval_lift in He.
apply expr_typed_lift in Ht.
exists τlr.
split; [|assumption].
destruct ρ; assumption.
Qed.

Lemma assert_eval_functional `{EnvSpec K} (Γ: env K) δ e ν1 ν2:
  (((e ⇓ ν1 ∧ emp) ★ (e ⇓ ν2 ∧ emp)) ⊆{Γ,δ} ⌜ν1 = ν2⌝)%A.
unfold subseteqE.
unfold assert_entails.
unfold assert_sep.
unfold assert_and.
unfold assert_expr.
unfold assert_Prop.
intros.
simpl in *.
destruct H7 as [m1 [m2 [Hm [Hdisj [[[τlr1 [Ht1 He1]] [_ Hm1]] [[τlr2 [Ht2 He2]] [_ Hm2]]]]]]].
subst.
split.
- congruence.
- rewrite sep_left_id.
  reflexivity.
  apply sep_empty_valid.
Qed.

Lemma assert_eval_functional' `{EnvSpec K} (Γ: env K) δ e ν1 ν2:
  (((e ⇓ ν1 ∧ emp) ★ (e ⇓ ν2 ∧ emp)) ⊆{Γ,δ} (⌜ν1 = ν2⌝ ★ (e ⇓ ν1 ∧ emp)))%A.
rewrite emp_dup at 1.
rewrite (commutative (★)%A).
rewrite (associative (★)%A).
apply assert_sep_preserving; [|reflexivity].
rewrite (commutative (★)%A).
apply assert_eval_functional.
Qed.

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

Definition points_to' a mv: assert K :=
  match mv with
    None =>
    % a ↦{false, perm_full} - : sintT%BT
  | Some z =>
    % a ↦{false, perm_full} (# intV{sintT} z) : sintT%BT
  end.

Fixpoint assert_stack'(ρ: list (ptr K))(st: store): assert K :=
  match ρ, st with
    [], [] => emp
  | a::ρ, mv::st =>
    (var 0 ⇓ inl a ∧ emp) ★ points_to' a mv ★
    assert_stack' ρ st ↑
  | _, _ => False
  end.

Lemma points_to'_intro (Γ: env K) δ mv:
  points_to 0 mv ⊆{Γ,δ}
  (∃a, (var 0 ⇓ inl a ∧ emp) ★ points_to' a mv)%A.
destruct mv.
- apply assert_singleton_l.
- apply assert_singleton_l_.
Qed.

Lemma assert_stack'_intro (Γ: env K) δ st:
  (assert_stack st ⊆{Γ,δ} ∃ρ, assert_stack' ρ st)%A.
induction st; simpl.
- apply assert_exist_intro with (x:=[]).
  reflexivity.
- rename a into mv.
  rewrite points_to'_intro.
  rewrite assert_exist_sep.
  apply assert_exist_elim; intro a.
  rewrite IHst.
  rewrite assert_lift_exists.
  rewrite (commutative (★)%A).
  rewrite assert_exist_sep.
  apply assert_exist_elim; intro ρ.
  apply assert_exist_intro with (x:=a::ρ).
  simpl.
  rewrite (commutative (★)%A).
  rewrite (associative (★)%A).
  reflexivity.
Qed.

Lemma assert_stack'_var (Γ: env K) δ ρ st i:
  i < length st ->
  (assert_stack' ρ st ⊆{Γ,δ}
   ∃a, (var i ⇓ inl a ∧ emp) ★ assert_stack' ρ st
   ★ ⌜ρ !! i = Some a⌝)%A.
revert ρ i.
induction st.
- simpl; intros; lia.
- simpl; intros.
  rename a into mv.
  destruct ρ as [|a ρ]; simpl.
  + apply assert_False_elim.
  + destruct i; simpl.
    * apply assert_exist_intro with (x:=a).
      rewrite assert_Prop_r; [|reflexivity].
      assert (forall A B C: assert K,
        A ⊆{Γ,δ} (A ★ A)%A ->
        (A ★ B ★ C)%A ⊆{Γ,δ}
        (A ★ A ★ B ★ C)%A). {
        intros.
        rewrite H0 at 1.
        rewrite (associative (★)%A).
        rewrite (associative (★)%A).
        rewrite (associative (★)%A).
        reflexivity.
      }
      apply H0; clear H0.
      apply emp_dup.
    * assert (i < length st). lia. clear H.
      rewrite IHst with (3:=H0).
      rewrite (associative (★)%A).
      rewrite (commutative (★)%A).
      rewrite assert_lift_exists.
      rewrite assert_exist_sep.
      apply assert_exist_elim. intro a0.
      apply assert_exist_intro with (x:=a0).
      rewrite assert_lift_sep.
      rewrite assert_lift_sep.
      rewrite assert_lift_and.
      rewrite assert_lift_expr.
      rewrite stack_indep.
      simpl.
      rewrite <- (associative (★)%A).
      apply assert_sep_preserving; [reflexivity|].
      rewrite (commutative (★)%A).
      rewrite (associative (★)%A).
      rewrite stack_indep.
      apply assert_sep_preserving; [|reflexivity].
      rewrite (associative (★)%A).
      reflexivity.
Qed.

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

Lemma points_to_unlock_indep (Γ: env K) δ i mv:
  (points_to i mv ⊆{Γ,δ} points_to i mv ◊)%A.
destruct mv; unfold points_to.
* simpl.
  apply assert_singleton_unlock_indep.
  reflexivity.
* apply assert_exist_elim; intro v.
  rewrite assert_unlock_exists.
  apply assert_exist_intro with (x:=v).
  apply assert_singleton_unlock_indep.
  reflexivity.
Qed.

Lemma assert_stack_unlock_indep (Γ: env K) δ st:
  (assert_stack st↑)%A ⊆{Γ,δ} ((assert_stack st↑) ◊)%A.
revert Γ δ.
induction st; simpl; intros.
- rewrite stack_indep.
  rewrite <- unlock_indep.
  reflexivity.
- rewrite assert_lift_sep.
  rewrite <- assert_unlock_sep.
  apply assert_sep_preserving.
  + rename a into mv.
    destruct mv; unfold points_to.
    * rewrite assert_lift_singleton.
      simpl.
      apply assert_singleton_unlock_indep.
      reflexivity.
    * rewrite assert_lift_exists.
      apply assert_exist_elim; intro v.
      rewrite assert_unlock_exists.
      apply assert_exist_intro with (x:=v).
      rewrite assert_lift_singleton.
      apply assert_singleton_unlock_indep.
      reflexivity.
  + assert (UnlockIndep (assert_stack st↑)%A). exact IHst.
    apply unlock_indep.
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
- eapply ax_stmt_weaken_post with (Q:=(assert_stack (<[i:=Some z]>st))%A). {
    apply assert_exist_intro with (x:=(<[i:=Some z]> st)).
    rewrite assert_Prop_r; reflexivity.
  }
  eapply ax_stmt_weaken_pre with (P:=(emp ★ assert_stack st)%A). {
    rewrite (left_id _ (★)%A).
    reflexivity.
  }
  apply ax_do.
  apply ax_assign with
    (Q1:=λ ν, (var i ⇓ ν ∧ emp)%A)
    (Q2:=λ ν, (⌜ν = inr (intV{sintT} z)⌝ ★ assert_stack st)%A)
    (μ:=false)
    (γ:=perm_full)
    (τ:=sintT%T).
  + reflexivity.
  + intros.
    rewrite (commutative (★)%A).
    rewrite <- (associative (★)%A).
    apply assert_Prop_intro_l. intros.
    injection H1; clear H1; intros; subst.
    rewrite (commutative (★)%A).
    apply assert_exist_intro with (x:=intV{sintT} z).
    apply assert_exist_intro with (x:=intV{sintT} z).
    apply assert_and_intro.
    * clear H0.
      revert st i H.
      induction st.
      -- simpl; intros; lia.
      -- Opaque perm_full.
         rename a into mv.
         simpl; intros.
         destruct i.
         ++ clear IHst H.
            simpl.
            assert (points_to 0 mv ⊆{Γ,δ} var 0 ↦{false,perm_full} - : sintT%BT)%A. {
              destruct mv.
              - eapply assert_exist_intro.
                simpl. reflexivity.
              - reflexivity.
            }
            rewrite H.
            rewrite assert_singleton_l_.
            rewrite (commutative (★)%A).
            rewrite <- (associative (★)%A).
            rewrite assert_exist_sep.
            apply assert_exist_elim; intro p'.
            rewrite (associative (★)%A).
            rewrite (commutative (★)%A).
            rewrite <- (associative (★)%A).
            rewrite (associative (★)%A).
            rewrite assert_eval_functional'.
            rewrite <- (associative (★)%A).
            apply assert_Prop_intro_l. intro Hp'. injection Hp'; clear Hp'; intros; subst p'.
            rewrite (associative (★)%A).
            rewrite (commutative (★)%A).
            rewrite (associative (★)%A).
            rewrite (commutative (★)%A).
            apply assert_sep_preserving; [reflexivity|].
            rewrite (commutative (★)%A).
            apply assert_wand_intro.
            rewrite (commutative (★)%A).
            rewrite (associative (★)%A).
            rewrite <- assert_unlock_sep.
            apply assert_sep_preserving.
            ** rewrite (commutative (★)%A).
               rewrite assert_singleton_l_2.
               apply assert_unlock_singleton.
               reflexivity.
            ** apply assert_stack_unlock_indep.
         ++ simpl.
            rewrite <- assert_unlock_sep.
Lemma assert_wand_sep (Γ: env K) δ P Q R:
  ((P ★ (Q -★ R)) ⊆{Γ,δ} (Q -★ (P ★ R)))%A.
apply assert_wand_intro.
rewrite <- (associative (★)%A).
apply assert_sep_preserving; [reflexivity|].
apply assert_wand_elim.
Qed.
            rewrite <- assert_wand_sep.
            rewrite (commutative (★)%A).
            rewrite <- (associative (★)%A).
            rewrite (commutative (★)%A) with (x:=(% p ↦{false,perm_full} - : sintT%BT)%A).
            rewrite <- (associative (★)%A).
            apply assert_sep_preserving; [apply points_to_unlock_indep|].
            rewrite (commutative (★)%A).
            rewrite (commutative (★)%A) with (y:=(% p ↦{false,perm_full} - : sintT%BT)%A).
            assert (
              ((var (S i) ⇓ inl p ∧ emp) ★ assert_stack st↑)%A ⊆{Γ,δ}
              (((var i ⇓ inl p ∧ emp) ★ assert_stack st)↑)%A). {
              rewrite assert_lift_sep.
              rewrite assert_lift_and.
              rewrite stack_indep.
              apply assert_sep_preserving; [|reflexivity].
              apply assert_and_intro.
              - apply assert_and_elim_l.
                rewrite <- assert_lift_eval.
                reflexivity.
              - apply assert_and_elim_r; reflexivity.
            }
            rewrite H0.
            rewrite IHst.
            ** rewrite assert_lift_sep.
               rewrite assert_lift_wand.
               rewrite assert_lift_unlock.
               rewrite assert_lift_singleton.
               rewrite assert_lift_singleton_.
               reflexivity.
            ** lia.
    * 
 
  apply ax_stmt_exist_pre. intro ρ.
  eapply ax_stmt_weaken_pre. {
    apply assert_stack'_var with (1:=H).
  }
  assert (Inhabited (ptr K)). {
    constructor.
    apply NULL.
    constructor.
    apply (sintT%T).
  }
  apply ax_stmt_exist_pre. intro a.
  rewrite (associative (★)%A).
  rewrite (commutative (★)%A).
  apply ax_stmt_Prop_pre. {
    intros.
    unfold J.
    apply assert_False_elim.
  } {
    intros.
    unfold C.
    apply assert_False_elim.
  }
  intros.
  apply ax_stmt_weaken_pre with (P:=((var i ⇓ inl a ∧ emp) ★ emp ★ assert_stack' ρ st)%A). {
    rewrite (left_id _ (★)%A).
    reflexivity.
  }
  apply ax_do.
  eapply ax_expr_weaken_post with (Q':=fun _ => (emp ★ assert_stack (<[i:=Some z]> st) ◊)%A). {
    intros.
    rewrite (left_id _ (★)%A).
    reflexivity.
  }
  eapply ax_expr_weaken_post with (Q':=fun _ => ((var i ⇓ inl a ∧ emp) ★ assert_stack (<[i:=Some z]> st) ◊)%A). {
    intros.
    apply assert_sep_preserving; [|reflexivity].
    apply assert_and_r.
  }
  apply ax_expr_invariant_l.
  rewrite (right_id _ (★)%A).
  apply ax_assign with
    (Q1:=fun ν => ⌜ν = inl a⌝)
    (Q2:=fun ν => ⌜ν = inr (intV{sintT} z⌝ ★ assert_stack' ρ st.
  
  
  

  
  
    
  
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
