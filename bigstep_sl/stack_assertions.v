Require Export stores.
Require Export assertions_lemmas.

Definition points_to `{EnvSpec K} i mv: assert K :=
  match mv with
    None =>
    var i ↦{false, perm_full} - : sintT%BT
  | Some z =>
    var i ↦{false, perm_full} (# intV{sintT} z) : sintT%BT
  end.

Fixpoint assert_stack `{EnvSpec K} (st: store): assert K :=
  match st with
    [] => emp
  | mv::st =>
    points_to 0 mv ★ assert_stack st ↑
  end.

Lemma assert_stack_var `{EnvSpec K} (Γ: env K) δ st i:
  i < length st ->
  assert_stack st ⊆{Γ,δ}
  ((∃p, var i ⇓ inl p ∧ emp) ★ assert_stack st)%A.
revert i.
induction st; simpl; intros.
- lia.
- destruct i.
  + rewrite (associative (★)%A).
    apply assert_sep_preserving; [|reflexivity].
    rename a into mv.
    destruct mv.
    * simpl.
      rewrite assert_singleton_l at 1.
      apply assert_exist_elim; intro p.
      rewrite assert_exist_sep.
      apply assert_exist_intro with (x:=p).
      rewrite emp_dup at 1.
      rewrite <- (associative (★)%A).
      apply assert_sep_preserving; [reflexivity|].
      rewrite assert_singleton_l_2.
      reflexivity.
    * simpl.
      rewrite assert_singleton_l_ at 1.
      apply assert_exist_elim; intro p.
      rewrite assert_exist_sep.
      apply assert_exist_intro with (x:=p).
      rewrite emp_dup at 1.
      rewrite <- (associative (★)%A).
      apply assert_sep_preserving; [reflexivity|].
      rewrite assert_singleton_l_2_.
      reflexivity.
  + rewrite (commutative (★)%A).
    rewrite (associative (★)%A).
    apply assert_sep_preserving; [|reflexivity].
    rewrite IHst with (i:=i) at 1; [|lia].
    rewrite assert_lift_sep.
    rewrite assert_lift_exists.
    apply assert_sep_preserving; [|reflexivity].
    apply assert_exist_elim; intro p.
    apply assert_exist_intro with (x:=p).
    rewrite assert_lift_and.
    rewrite stack_indep.
    apply assert_and_intro.
    * apply assert_and_elim_l.
      rewrite <- assert_lift_eval at 1.
      reflexivity.
    * apply assert_and_elim_r; reflexivity.
Qed.

Lemma assert_stack_load {K} {HK: Env K} {HK': EnvSpec K} (Γ: env K) δ st i z:
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
    rewrite IHst with (1:=H).
    rewrite assert_lift_expr.
    reflexivity.
Qed.

Lemma points_to_unlock_indep `{EnvSpec K} (Γ: env K) δ i mv:
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

Lemma assert_stack_unlock_indep' `{EnvSpec K} (Γ: env K) δ st:
  assert_stack st ⊆{Γ,δ} (assert_stack st ◊)%A.
revert Γ δ.
induction st; simpl; intros.
- rewrite <- unlock_indep.
  reflexivity.
- rewrite <- assert_unlock_sep.
  apply assert_sep_preserving.
  + rename a into mv.
    destruct mv; unfold points_to.
    * simpl.
      apply assert_singleton_unlock_indep.
      reflexivity.
    * apply assert_exist_elim; intro v.
      rewrite assert_unlock_exists.
      apply assert_exist_intro with (x:=v).
      apply assert_singleton_unlock_indep.
      reflexivity.
  + assert (UnlockIndep (assert_stack st)%A). exact IHst.
    apply unlock_indep.
Qed.

Lemma assert_stack_unlock_indep `{EnvSpec K} (Γ: env K) δ st:
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