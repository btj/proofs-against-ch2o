Require Export ZArith.
Require Export ch2o.core_c.expressions.
Require Export ch2o.memory_separation.memory_singleton.
Require Export ch2o.separation.permissions.
Require Export ch2o.core_c.expressions.
Require Export ch2o.core_c.expression_eval.
Require Export ch2o.core_c.restricted_smallstep.
Require Export ch2o.core_c.expression_eval_smallstep.
Require Export ch2o.abstract_c.natural_type_environment.
Require Export ch2o.abstract_c.architecture_spec.
Require Export ch2o.abstract_c.architectures.

Notation store := (list (option Z)).

Inductive stack_mem `{Env K} (Γ : env K) (Δ : memenv K): stack K -> store -> mem K -> Prop :=
| stack_mem_empty:
  ✓ Γ ->
  ✓{Γ} Δ ->
  stack_mem Γ Δ [] [] ∅
| stack_mem_alloc o mv m ρ st m':
  ✓ Γ ->
  ✓{Γ} Δ ->
  ✓{Γ, Δ} (m ∪ m') ->
  mem_singleton Γ Δ (addr_top o sintT%T) false perm_full
    (match mv with None => indetV sintT%BT | Some z => intV{sintT} z end)
    sintT%T m ->
  stack_mem Γ Δ ρ st m' ->
  ⊥[m; m'] ->
  stack_mem Γ Δ ((o, sintT%T)::ρ) (mv::st) (m ∪ m')
.

Lemma stack_mem_erase `{EnvSpec K} Γ Δ ρ st m:
  stack_mem Γ Δ ρ st m ->
  cmap_erase m = m.
induction 1.
- apply cmap_erase_empty.
- rewrite cmap_erase_union.
  rewrite mem_erase_singleton with (1:=H4).
  rewrite IHstack_mem.
  reflexivity.
Qed.

Definition stack_mem' `{Env K} Γ ρ st m :=
  ✓{Γ} m /\ stack_mem Γ '{m} ρ st (cmap_erase m).

Lemma stack_mem_valid `{EnvSpec K} Γ Δ ρ st m:
  stack_mem Γ Δ ρ st m ->
  ✓{Γ, Δ} m.
induction 1.
- apply cmap_empty_valid.
  assumption.
- assumption.
Qed.

Lemma stack_mem_lookup_stack `{Env K} Γ Δ ρ st m i mv:
  stack_mem Γ Δ ρ st m ->
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
    apply IHstack_mem with (1:=H6).
Qed.

Lemma stack_mem_lookup_mem `{EnvSpec K} Γ Δ ρ st m i v o:
  stack_mem Γ Δ ρ st m ->
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
  + apply cmap_valid_subseteq with (2:=H3).
    * assumption.
    * apply sep_union_subseteq_l.
      assumption.
  + apply sep_union_subseteq_l.
    assumption.
  + apply mem_lookup_singleton with (3:=H4).
    * assumption.
    * rewrite perm_kind_full.
      reflexivity.
- eapply mem_lookup_subseteq with (m1:=m').
  + assumption.
  + apply stack_mem_valid with (1:=H5).
  + apply sep_union_subseteq_r.
    assumption.
  + apply IHstack_mem with (1:=H7) (2:=H8).
Qed.

Lemma stack_mem_weaken_memenv `{EnvSpec K} Γ Δ ρ st m Δ':
  stack_mem Γ Δ ρ st m ->
  ✓{Γ} Δ' ->
  Δ ⊆ Δ' ->
  stack_mem Γ Δ' ρ st m.
induction 1; intros.
- apply stack_mem_empty; try assumption.
- apply stack_mem_alloc; try assumption.
  + apply cmap_valid_weaken with (2:=H3); trivial.
  + apply mem_singleton_weaken with (4:=H4); try assumption.
    * reflexivity.
    * apply memenv_subseteq_forward.
      assumption.
  + apply IHstack_mem; assumption.
Qed.

Lemma stack_mem_forced `{EnvSpec K} Γ Δ ρ st m i v o:
  stack_mem Γ Δ ρ st m ->
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
  + apply cmap_valid_subseteq with (2:=H3).
    * assumption.
    * apply sep_union_subseteq_l.
      assumption.
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
  + apply stack_mem_valid with (1:=H5).
  + apply sep_union_subseteq_r.
    assumption.
  + eapply IHstack_mem; eassumption.
  + rewrite stack_mem_lookup_mem with (1:=H5) (2:=H7) (3:=H8).
    eexists; reflexivity.
Qed.

Lemma stack_mem_free `{EnvSpec K} Γ Δ ρ st m Δ':
  stack_mem Γ Δ ρ st m ->
  memenv_forward Δ Δ' ->
  ✓{Γ, Δ'} m ->
  stack_mem Γ Δ' ρ st m.
induction 1; intros.
- apply stack_mem_empty.
  + assumption.
  + apply cmap_valid_memenv_valid with (1:=H4).
- apply stack_mem_alloc.
  + assumption.
  + apply cmap_valid_memenv_valid with (1:=H8).
  + assumption.
  + apply mem_singleton_weaken with (4:=H4); try assumption.
    * reflexivity.
  + apply IHstack_mem; try assumption.
    * apply cmap_valid_subseteq with (2:=H8).
      -- assumption.
      -- apply sep_union_subseteq_r.
         assumption.
  + assumption.
Qed.

Lemma stack_mem_typed `{EnvSpec K} Γ Δ ρ st m i o:
  stack_mem Γ Δ ρ st m ->
  ρ !! i = Some (o, sintT%T) ->
  (Γ, Δ) ⊢ addr_top o sintT%BT : sintT%PT.
intro.
revert i.
induction H1; intros.
- discriminate.
- destruct i.
  + simpl in *.
    injection H7; clear H7; intros; subst.
    apply mem_singleton_typed_addr_typed with (1:=H4).
  + simpl in H7.
    apply IHstack_mem with (1:=H7).
Qed.

Lemma stack_mem_writable `{EnvSpec K} Γ Δ ρ st m i o:
  stack_mem Γ Δ ρ st m ->
  ρ !! i = Some (o, sintT%T) ->
  mem_writable Γ (addr_top o sintT%BT) m.
intro.
revert i.
induction H1; intros.
- discriminate.
- destruct i; simpl in H7.
  + injection H7; clear H7; intros; subst.
    eapply mem_writable_subseteq.
    * assumption.
    * apply cmap_valid_subseteq with (2:=H3).
      -- assumption.
      -- apply sep_union_subseteq_l.
         assumption.
    * apply sep_union_subseteq_l; assumption.
    * apply mem_writable_singleton with (3:=H4).
      -- assumption.
      -- reflexivity.
  + eapply mem_writable_subseteq.
    * assumption.
    * apply cmap_valid_subseteq with (2:=H3).
      -- assumption.
      -- apply sep_union_subseteq_r.
         assumption.
    * apply sep_union_subseteq_r; assumption.
    * apply IHstack_mem with (1:=H7).
Qed.

Lemma stack_mem_insert `{EnvSpec K} Γ Δ ρ st m i o z:
  stack_mem Γ Δ ρ st m ->
  ρ !! i = Some (o, sintT%T) ->
  int_typed z sintT ->
  cmap_valid (Γ, Δ) (<[addr_top o sintT%BT:=intV{sintT} z]{Γ}> m) ->
  stack_mem Γ Δ ρ (<[i:=Some z]> st)
    (<[addr_top o sintT%BT:=intV{sintT} z]{Γ}> m).
intro.
revert i.
induction H1; intros.
- discriminate.
- destruct i.
  + simpl in H7.
    injection H7; clear H7; intros; subst.
    assert (<[addr_top o sintT%BT:=intV{sintT} z]{Γ}> m ⊥ m'). {
            apply mem_insert_disjoint with (Δ1:=Δ) (τ1:=sintT%T).
            ** assumption.
            ** apply cmap_valid_subseteq with (2:=H3).
               --- assumption.
               --- apply sep_union_subseteq_l; assumption.
            ** rewrite sep_disjoint_list_double in H6.
               assumption.
            ** apply mem_singleton_typed_addr_typed with (1:=H4).
            ** apply mem_writable_singleton with (3:=H4).
               --- assumption.
               --- reflexivity.
            ** constructor.
               constructor.
               assumption.
    }
    assert (Hunion: <[addr_top o sintT%BT:=intV{sintT} z]{Γ}> (m ∪ m') = <[addr_top o sintT%BT:=intV{sintT} z]{Γ}> m ∪ m'). {
      apply mem_insert_union with (Δ1:=Δ) (τ1:=sintT%T).
         ++ assumption.
         ++ apply cmap_valid_subseteq with (2:=H3).
            +++ assumption.
            +++ apply sep_union_subseteq_l; assumption.
         ++ rewrite sep_disjoint_list_double in H6; assumption.
         ++ apply mem_singleton_typed_addr_typed with (1:=H4).
         ++ apply mem_writable_singleton with (3:=H4).
                   +++ assumption.
                   +++ reflexivity.
         ++ constructor; constructor; assumption.
    }
    rewrite Hunion.
    * apply stack_mem_alloc.
      -- assumption.
      -- assumption.
      -- rewrite Hunion in H9; assumption.
      -- assert (Hz: intV{sintT} z = freeze true (intV{sintT} z)). reflexivity.
         rewrite Hz at 1.
         apply mem_insert_singleton with (3:=H4).
         ++ assumption.
         ++ reflexivity.
         ++ constructor; constructor; assumption.
      -- assumption.
      -- rewrite sep_disjoint_list_double; assumption.
  + simpl in H7.
    assert (Hdisjoint: ⊥ [<[addr_top o sintT%BT:=intV{sintT} z]{Γ}> m'; m]). {
      apply sep_disjoint_list_double.
      apply mem_insert_disjoint with (Δ1:=Δ) (τ1:=sintT%T).
      - assumption.
      - apply cmap_valid_subseteq with (2:=H3).
            +++ assumption.
            +++ apply sep_union_subseteq_r; assumption.
      - apply symmetry.
        rewrite sep_disjoint_list_double in H6; assumption.
      - apply stack_mem_typed with (1:=H5) (2:=H7).
      - apply stack_mem_writable with (1:=H5) (2:=H7).
      - constructor; constructor; assumption.
    }
    assert (Hunion: <[addr_top o sintT%BT:=intV{sintT} z]{Γ}> (m ∪ m') = m ∪ <[addr_top o sintT%BT:=intV{sintT} z]{Γ}> m'). {
      rewrite sep_commutative. 2:assumption.
      rewrite mem_insert_union with (Δ1:=Δ) (τ1:=sintT%T).
         ++ apply sep_commutative. assumption.
         ++ assumption.
         ++ apply cmap_valid_subseteq with (2:=H3).
            +++ assumption.
            +++ apply sep_union_subseteq_r; assumption.
         ++ apply symmetry; rewrite sep_disjoint_list_double in H6; assumption.
         ++ apply stack_mem_typed with (1:=H5) (2:=H7).
         ++ apply stack_mem_writable with (1:=H5) (2:=H7).
         ++ constructor; constructor; assumption.
    }
    rewrite Hunion.
    * apply stack_mem_alloc.
      -- assumption.
      -- assumption.
      -- rewrite Hunion in H9; assumption.
      -- assumption.
      -- apply IHstack_mem; try assumption.
         apply cmap_valid_subseteq with (2:=H9); try assumption.
         rewrite Hunion.
         apply sep_union_subseteq_r.
         rewrite sep_disjoint_list_double.
         rewrite sep_disjoint_list_double in Hdisjoint.
         apply symmetry; assumption.
      -- rewrite sep_disjoint_list_double.
         rewrite sep_disjoint_list_double in Hdisjoint.
         apply symmetry; assumption.
Qed.
