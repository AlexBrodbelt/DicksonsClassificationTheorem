import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_A_MaximalAbelianSubgroup

open MaximalAbelianSubgroup Subgroup MulAction MulAut Pointwise Function SpecialSubgroups SpecialMatrices

open scoped MatrixGroups

#check A_subgroupOf_normalizer_MulEquiv_conj_A_subgroupOf_conj_quot_eq

#check normalizer_inf_le_eq_normalizer_subgroupOf

lemma Nonempty_normalizer_A'_inf_G_diff_A' {F : Type*} [Field F] (A' G' : Subgroup SL(2,F)) (hA' : A' ∈ MaximalAbelianSubgroupsOf G')
  (A'_le_D : A' ≤ D F) : Set.Nonempty ((A'.normalizer ⊓ G').carrier \ A') := by
  by_contra! h
  rw [Set.diff_eq_empty] at h
  have : A'.normalizer ⊓ G' ≤ D F := by
    rw [normalizer_subgroup_D_eq_DW sorry sorry]
    sorry


  sorry
/-
Theorem 2.3 (iv b) Furthermore, if [NG (A) : A] = 2,
then there is an element y of NG (A)\A such that, yxy⁻¹ = x⁻¹  for all x ∈ A.
 -/
theorem of_index_normalizer_eq_two {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  {p : ℕ} [Fact (Nat.Prime p)] [CharP F p] (p_ne_two : p ≠ 2) (A G : Subgroup SL(2,F))
  [Finite G] (hA : A ∈ MaximalAbelianSubgroupsOf G) (center_le_G : center SL(2,F) ≤ G)
  (hA' : Nat.Coprime (Nat.card A) p)
  (hNA : relIndex (A.subgroupOf G) (A.subgroupOf G).normalizer = 2) (x : A) :
    ∃ y ∈ (A.normalizer ⊓ G).carrier \ A, y * x * y⁻¹ = x⁻¹ := by
  have two_lt_card_A : 2 < Nat.card A := by
    have key := card_normalizer_inf_G_eq_one_of_card_le_two p_ne_two A G center_le_G hA
    contrapose! key
    constructor
    · exact key
    · rw [hNA]
      norm_num
  have G_ne_center : G ≠ center SL(2,F) := G_ne_center_of_two_lt_card A G hA two_lt_card_A

  rcases IsCyclic_and_card_coprime_CharP_or_eq_Q_join_Z_of_center_ne p G A hA
      center_le_G G_ne_center with (⟨⟨c, A', Finite_A', A'_le_D, A_eq_conj_A'⟩, -⟩ | h)
  · let G' := conj c⁻¹ • G
    have G_eq_conj_G' : G = conj c • G' := by simp [G']
    have hA' : A' ∈ MaximalAbelianSubgroupsOf G' := by
      rw [iff_conj_MaximalAbelianSubgroupsOf_conj A' G' c, ← A_eq_conj_A', ← G_eq_conj_G']
      exact hA
    rw [relIndex,
      ← relIndex_MaximalAbelianSubgroupOf_normalizer_eq_relIndex_conj_MaxAbelianSubgroupOf
      A_eq_conj_A' G_eq_conj_G'] at hNA
    have two_lt_card_A' : 2 < Nat.card A' := by rwa [card_conj_eq_card A_eq_conj_A']
    have A'_eq_G'_inf_D : A' = G' ⊓ D F := A_eq_G_inf_D A' G' A'_le_D hA'

    let f := A_subgroupOf_G_MonoidHom_ZMod_two A' G' A'_le_D hA'.right two_lt_card_A' A'_eq_G'_inf_D
    have Injective_f : Injective f :=
      injective_A_subgroupOf_G_MonoidHom_ZMod_two
        A' G' A'_le_D hA'.right two_lt_card_A' A'_eq_G'_inf_D
    -- let := Equiv.ofInjective
    --   (A_subgroupOf_G_MonoidHom_ZMod_two A' G' A'_le_D hA'.right two_lt_card_A' A'_eq_G'_inf_D)
    --   (injective_A_subgroupOf_G_MonoidHom_ZMod_two A' G' A'_le_D hA'.right two_lt_card_A' A'_eq_G'_inf_D)

    have card_multiplicative_ZMod_two_eq_two : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative]; rfl
    -- let := Equiv.mulEquiv (Equiv.ofInjective
    --   (A_subgroupOf_G_MonoidHom_ZMod_two A' G' A'_le_D hA'.right two_lt_card_A' A'_eq_G'_inf_D)
    --   (injective_A_subgroupOf_G_MonoidHom_ZMod_two A' G' A'_le_D hA'.right two_lt_card_A' A'_eq_G'_inf_D))

    rw [index] at hNA
    have key := ((Nat.bijective_iff_injective_and_card f).mpr
      ⟨Injective_f, by rwa [card_multiplicative_ZMod_two_eq_two]⟩).2

    dsimp [f, A_subgroupOf_G_MonoidHom_ZMod_two] at key
    rw [← comp_assoc] at key
    -- want surjectivity of the second map on the left in the composition

    have surjective : Bijective ((monoidHom_normalizer_D_quot_D A' G')) := by
      sorry



    have normalizer_A'_inf_G'_sup_D_eq_normalizer_D :
      (A'.normalizer ⊓ G' ⊔ D F) = (D F).normalizer := by
      apply le_antisymm
      · apply sup_le
        · rw [A'_eq_G'_inf_D]

          apply inf_le_of_left_le
          -- for a suitable characteristic this should follow easily,
          -- or should generalise the result for the case when card D₀ ≤ 2
          rw [normalizer_subgroup_D_eq_DW (by sorry) inf_le_right,
            normalizer_D_eq_DW]
        · exact le_normalizer
      · sorry

    suffices ∃ δ : Fˣ, (d δ * w) ∈ (A'.normalizer ⊓ G').carrier \ A' by
      obtain ⟨δ, mem_normalizer_A'_inf_G', not_mem_A'⟩ := this
      use conj c • (d δ * w)
      constructor
      · refine ⟨?mem_normalizer_inf_G, ?not_mem_A'⟩
        · rw [normalizer_inf_le_eq_normalizer_subgroupOf hA.right]
          sorry
        · intro contr
          rw [← Set.mem_inv_smul_set_iff, ← map_inv, A_eq_conj_A',
            map_inv, coe_pointwise_smul, inv_smul_smul, SetLike.mem_coe] at contr
          contradiction
      · have conj_x_mem_A' : conj c⁻¹ • x.val ∈ A' := by
          rw [← mem_inv_pointwise_smul_iff, map_inv, inv_inv, ← A_eq_conj_A']
          exact x.prop
        have conj_x_mem_D := A'_le_D conj_x_mem_A'
        obtain ⟨δ', hδ'⟩ := conj_x_mem_D
        symm at hδ'
        rw [smul_eq_iff_eq_inv_smul, map_inv, inv_inv] at hδ'
        simp only [smul_mul', MulAut.smul_def, conj_apply, conj_mul, hδ', mul_inv_rev, inv_inv,
          inv_w_eq_neg_w, inv_d_eq_d_inv, neg_mul, w_mul_d_eq_d_inv_w, neg_d_mul_w, InvMemClass.coe_inv]
        group
        simp only [Int.reduceNeg, zpow_neg, zpow_one, mul_left_inj]
        rw [← neg_d_eq_d_neg, show (c * d δ * w * d δ') * -d δ * w = (c * d δ * w * d δ') * d δ * -w by simp [- neg_d_eq_d_neg],
          ← inv_w_eq_neg_w, show c * d δ * w * d δ' * d δ * w⁻¹ = c * d δ * w * (d δ' * d δ) * w⁻¹ by group, d_mul_d_eq_d_mul,
          show c * d δ * w * d (δ' * δ) * w⁻¹ = c * d δ * (w * d (δ' * δ) * w⁻¹) by group, w_mul_d_mul_inv_w_eq_inv_d,  ← d_mul_d_eq_d_mul,
          show c * d δ * (d δ' * d δ)⁻¹ = c * (d δ * (d δ' * d δ)⁻¹) by group]
        congr
        simp
    sorry
  sorry

  --   use x
  --   constructor
  --   · constructor
  --     · rw [mem_carrier, ← mem_inv_pointwise_smul_iff,
  --         normalizer_inf_le_eq_normalizer_subgroupOf hA.right,
  --         map_inv, inv_inv, conj_A_subgroupOf_G_eq_A'_subgroupOf_G A_eq_conj_A' G_eq_conj_G',
  --         ← normalizer_inf_le_eq_normalizer_subgroupOf hA'.right]




-- tactic which uses associativity before rewriting






  --       -- rw [pointwise_smul_def, map_map]

  --       -- relationship between conj c • A.normalizer vs (conj c • A).normalizer
  --       sorry
  --     · intro contr
  --       rw [SetLike.mem_coe, ← mem_inv_pointwise_smul_iff,
  --         A_eq_conj_A', smul_smul] at contr

  --       sorry
  --   · sorry

  -- sorry

/-
Theorem 2.3 (v a) Let Q be a Sylow p-subgroup of G.
If Q = { I_G }, then there is a cyclic subgroup K of G such that N_G (Q) = Q K.
-/
theorem exists_IsCyclic_K_normalizer_eq_Q_join_K {F : Type*} [Field F] { p : ℕ }
  (hp : Nat.Prime p)
  (G : Subgroup SL(2,F))
  (Q : Sylow p G)
  (h : Q.toSubgroup ≠ ⊥) :
  ∃ K : Subgroup G, IsCyclic K ∧ normalizer Q.toSubgroup = Q.toSubgroup ⊔ K := by
  sorry

/-
Theorem 2.3 (v b)If |K| > |Z|, then K ∈ M.
-/
theorem K_mem_MaximalAbelianSubgroups_of_center_lt_card_K {F : Type*} [Field F] { p : ℕ } [hp' : Fact (Nat.Prime p)] (G : Subgroup SL(2,F))
  (Q : Sylow p G) (h : Q.toSubgroup ≠ ⊥) (K : Subgroup G)(hK : IsCyclic K)
  (hNG : normalizer Q.toSubgroup = Q.toSubgroup ⊔ K) (h : Nat.card K > Nat.card (center SL(2,F))) :
  map G.subtype K ∈ MaximalAbelianSubgroupsOf G := by
  sorry



#min_imports
