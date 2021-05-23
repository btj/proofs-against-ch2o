Require Export ZArith.
Require Export ch2o.core_c.expressions.
Require Export ch2o.memory_separation.memory_singleton.
Require Export ch2o.separation.permissions.
Require Export ch2o.core_c.expressions.
Require Export ch2o.core_c.expression_eval.
Require Export ch2o.core_c.restricted_smallstep.

Notation store := (list (option Z)).

Inductive mem_stack `{Env K} (Γ : env K) (Δ : memenv K): stack K -> store -> mem K -> Prop :=
| mem_stack_empty m:
  ✓ Γ ->
  ✓{Γ} Δ ->
  ✓{Γ, Δ} m ->
  mem_stack Γ Δ [] [] m
| mem_stack_alloc o mv m ρ st m':
  ✓ Γ ->
  ✓{Γ} Δ ->
  index_alive Δ o ->
  mem_singleton Γ Δ (addr_top o sintT%T) false perm_full
    (match mv with None => indetV sintT%BT | Some z => intV{sintT} z end)
    sintT%T m ->
  mem_stack Γ Δ ρ st m' ->
  ⊥[m; m'] ->
  mem_stack Γ Δ ((o, sintT%T)::ρ) (mv::st) (m ∪ m')
.

Lemma mem_stack_valid `{EnvSpec K} Γ Δ ρ st m:
  mem_stack Γ Δ ρ st m ->
  ✓{Γ, Δ} m.
induction 1.
- assumption.
- apply cmap_union_valid_2.
  * apply sep_disjoint_list_double; assumption.
  * apply mem_singleton_valid with (4:=H4); try assumption.
    discriminate.
  * assumption.
Qed.

Lemma mem_stack_lookup_stack `{Env K} Γ Δ ρ st m i mv:
  mem_stack Γ Δ ρ st m ->
  st !! i = Some mv ->
  exists o, ρ !! i = Some (o, sintT%T).
intro.
revert i mv.
induction H0.
- intros.
  discriminate.
- intros.
  destruct i.
  + exists o. reflexivity.
  + simpl in H6.
    simpl.
    apply IHmem_stack with (1:=H6).
Qed.

Lemma mem_stack_lookup_mem `{EnvSpec K} Γ Δ ρ st m i v o:
  mem_stack Γ Δ ρ st m ->
  st !! i = Some (Some v) ->
  ρ !! i = Some (o, sintT%T) ->
  m !!{Γ} addr_top o sintT%T = Some (intV{sintT} v).
intro.
revert i v o.
induction H1; intros. {
  discriminate.
}
destruct i; simpl in *.
- injection H7; clear H7; intros; subst.
  injection H8; clear H8; intros; subst.
  eapply mem_lookup_subseteq with (m1:=m).
  + assumption.
  + apply mem_singleton_valid with (4:=H4).
    * assumption.
    * assumption.
    * discriminate.
    * apply H3.
  + apply sep_union_subseteq_l.
    assumption.
  + apply mem_lookup_singleton with (3:=H4).
    * assumption.
    * rewrite perm_kind_full.
      reflexivity.
- eapply mem_lookup_subseteq with (m1:=m').
  + assumption.
  + apply mem_stack_valid with (1:=H5).
  + apply sep_union_subseteq_r.
    assumption.
  + apply IHmem_stack with (1:=H7) (2:=H8).
Qed.

Lemma mem_stack_forced `{EnvSpec K} Γ Δ ρ st m i v o:
  mem_stack Γ Δ ρ st m ->
  st !! i = Some (Some v) ->
  ρ !! i = Some (o, sintT%T) ->
  mem_forced Γ (addr_top o sintT%T) m.
intro.
revert i v o.
induction H1; intros. {
  discriminate.
}
destruct i; simpl in *.
- injection H7; clear H7; intros; subst.
  injection H8; clear H8; intros; subst.
  eapply mem_forced_subseteq with (m1:=m); try eassumption.
  + apply mem_singleton_valid with (4:=H4); try assumption.
    discriminate.
  + apply sep_union_subseteq_l. assumption.
  + apply mem_singleton_forced with (3:=H4).
    * assumption.
    * rewrite perm_kind_full.
      reflexivity.
  + rewrite mem_lookup_singleton with (3:=H4).
    * unfold is_Some.
      eexists. reflexivity.
    * assumption.
    * rewrite perm_kind_full. reflexivity.
- eapply mem_forced_subseteq with (m1:=m').
  + assumption.
  + apply mem_stack_valid with (1:=H5).
  + apply sep_union_subseteq_r.
    assumption.
  + eapply IHmem_stack; eassumption.
  + rewrite mem_stack_lookup_mem with (1:=H5) (2:=H7) (3:=H8).
    eexists; reflexivity.
Qed.

Inductive eval `{Env K}: store -> expr K -> Z -> Prop :=
| eval_lit st z:
  eval st (# intV{sintT} z) z
| eval_load_var st i z:
  st !! i = Some (Some z) ->
  eval st (load (var i)) z
.

Lemma eval_sound `{EnvSpec K} (Γ: env K) st e z ρ m:
  eval st e z ->
  mem_stack Γ '{m} ρ st m ->
  ⟦ e ⟧ Γ ρ m = Some (inr (intV{sintT} z)).
intros.
destruct H1.
- (* eval_lit *)
  reflexivity.
- (* eval_load_var *)
  simpl.
  pose proof (mem_stack_lookup_stack _ _ _ _ _ _ _ H2 H1).
  destruct H3 as [o Ho].
  rewrite Ho.
  simpl.
  rewrite option_guard_True.
  + rewrite mem_stack_lookup_mem with (1:=H2) (2:=H1) (3:=Ho).
    reflexivity.
  + apply mem_stack_forced with (1:=H2) (2:=H1) (3:=Ho).
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
  eval st e z ->
  exec st (var i ::= cast{sintT%BT} e) (onormal (<[i:=Some z]>st))
| exec_seq st s1 st' s2 O:
  exec st s1 (onormal st') ->
  exec st s2 O ->
  exec st (s1 ;; s2) O
| exec_ret st e z:
  eval st e z ->
  exec st (ret (cast{sintT%BT} e)) (oreturn z)
.

Definition is_final_state `{Env K} S := forall Γ δ S', ~ Γ\ δ\ [] ⊢ₛ S ⇒ S'.

Lemma bigstep_sound_lemma `{Env K} st s O (P: Prop):
  exec st s O ->
  forall Γ δ k m S,
  is_final_state S ->
  Γ\ δ\ [] ⊢ₛ State k (Stmt ↘ s) m ⇒* S ->
  mem_stack Γ '{m} (rlocals [] k) st m ->
  (forall st' m',
   O = onormal st' ->
   mem_stack Γ '{m'} (rlocals [] k) st' m' ->
   Γ\ δ\ [] ⊢ₛ State k (Stmt ↗ s) m' ⇒* S ->
   P) ->
  (forall z st' m',
   O = oreturn z ->
   mem_stack Γ '{m'} (rlocals [] k) st' m' ->
   Γ\ δ\ [] ⊢ₛ State k (Stmt (⇈ intV{sintT} z) s) m' ⇒* S ->
   P) ->
  P.
Admitted.

Theorem bigstep_sound `{Env K} s z:
  exec [] s (oreturn z) ->
  forall Γ δ S,
  Γ\ δ\ [] ⊢ₛ State [] (Stmt ↘ s) ∅ ⇒* S ->
  exists m,
  Γ\ δ\ [] ⊢ₛ S ⇒* State [] (Stmt (⇈ (intV{sintT} z)) s) m.
Admitted.
