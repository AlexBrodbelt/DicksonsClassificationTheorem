import ClassificationOfSubgroups.Ch5_PropertiesOfSLOverAlgClosedField.S1_SpecialMatrices
import Mathlib.Algebra.Category.Grp.Images
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Order.CompletePartialOrder
import Mathlib.GroupTheory.Sylow

set_option linter.style.longLine true
set_option maxHeartbeats 0

open Matrix MatrixGroups Subgroup Pointwise SpecialMatrices

universe u

variable
  {F : Type u} [Field F]
  (n : Type u) [Fintype n]
  {R : Type u} [CommRing R]
  {G : Type u} [Group G]

namespace MatrixShapes

def IsDiagonal (x : Matrix (Fin 2) (Fin 2) F) : Prop := x 0 1 = 0 ∧ x 1 0 = 0
def IsLowerTriangular (x : Matrix (Fin 2) (Fin 2) F) : Prop := x 0 1 = 0
def IsUpperTriangular (x : Matrix (Fin 2) (Fin 2) F) : Prop := x 1 0 = 0

/-
A 2x2 matrix is lower triangular if and only the top right entry is zero.
-/
lemma lower_triangular_iff {M : Matrix (Fin 2) (Fin 2) F} :
  IsLowerTriangular M ↔ (∃ a c d, !![a, 0; c, d] = M) := by
  constructor
  · intro h
    unfold IsLowerTriangular at h
    use M 0 0, M 1 0, M 1 1
    simp_rw [← h]
    ext <;> rfl
  · intro h
    unfold IsLowerTriangular
    obtain ⟨a, c, d, hM⟩ := h
    simp [← hM]

/-
A 2x2 matrix is upper triangular if and only if the bottom left entry is zero.
-/
lemma upper_triangular_iff {M : Matrix (Fin 2) (Fin 2) F} :
  IsUpperTriangular M ↔ (∃ a b d, !![a, b; 0, d] = M) := by
  constructor
  · intro h
    unfold IsUpperTriangular at h
    use M 0 0, M 0 1, M 1 1
    simp_rw [← h]
    ext <;> rfl
  · intro h
    unfold IsUpperTriangular
    obtain ⟨a, b, d, hM⟩ := h
    simp [← hM]

lemma diagonal_iff {M : Matrix (Fin 2) (Fin 2) F} :
  IsDiagonal M ↔ (∃ a d, !![a, 0; 0, d] = M) := by
  constructor
  · intro h
    obtain ⟨h01, h10⟩ := h
    use M 0 0, M 1 1
    ext <;> simp [h01, h10]
  · intro h
    unfold IsDiagonal
    obtain ⟨a, d, hM⟩ := h
    simp [← hM]

lemma diagonal_iff_upper_and_lower {M: Matrix (Fin 2) (Fin 2) F} :
  IsDiagonal M ↔ IsUpperTriangular M ∧ IsLowerTriangular M := by
  constructor
  · intro h
    rw [diagonal_iff] at h
    obtain ⟨h01, h10, h⟩ := h
    rw [upper_triangular_iff, lower_triangular_iff]
    constructor
    . use h01, 0, h10
    . use h01, 0, h10
  · intro h
    obtain ⟨h_upper, h_lower⟩ := h
    rw [diagonal_iff]
    rw [upper_triangular_iff] at h_upper
    rw [lower_triangular_iff] at h_lower
    obtain ⟨a, b, d, hM_upper⟩ := h_upper
    obtain ⟨a', c, d', hM_lower⟩ := h_lower
    use a, d
    ext <;> simp [← hM_upper]
    have : b = M 0 1 := by rw [← hM_upper]; rfl
    rw [this]
    rw [← hM_lower]
    simp

end MatrixShapes

namespace SpecialSubgroups
section Diagonal

/- Lemma 1.2.1.1 -/
def D (F : Type*) [Field F] : Subgroup SL(2,F) where
  carrier := { d δ | δ : Fˣ }
  mul_mem' := by rintro S Q ⟨δS, hδS⟩ ⟨δQ, hδQ⟩
                 use δS * δQ; simp [← hδS, ← hδQ]
  one_mem' := ⟨1, d_one_eq_one⟩
  inv_mem' := by rintro S ⟨δ, hS⟩
                 use δ⁻¹; simp [← hS]

/- Lemma 1.2.1.3 -/
def D_iso_units (F : Type*) [Field F] : SpecialSubgroups.D F ≃* Fˣ where
  toFun d := ⟨
              d.val 0 0,
              d.val 1 1,
              by obtain ⟨δ, hδ⟩ := d.property; rw [← hδ]; simp [SpecialMatrices.d],
              by obtain ⟨δ, hδ⟩ := d.property; rw [← hδ]; simp [SpecialMatrices.d]
              ⟩
  invFun δ := ⟨d δ, by use δ⟩
  left_inv A := by
                obtain ⟨δ, hδ⟩ := A.property
                rw [← Subtype.coe_inj, ← hδ]
                ext <;> simp [SpecialMatrices.d, ← hδ]
  right_inv a := by ext; rfl
  map_mul' X Y := by
                obtain ⟨δ₁, hδ₁⟩ := X.property
                obtain ⟨δ₂, hδ₂⟩ := Y.property
                simp [Subgroup.coe_mul, Fin.isValue, SpecialLinearGroup.coe_mul]
                congr
                repeat'
                  simp_rw [← hδ₁, ← hδ₂]
                  simp [SpecialMatrices.d, mul_comm]
@[simp]
lemma d_mem_D {F : Type*} [Field F] {δ : Fˣ} : d δ ∈ D F := by
  use δ


end Diagonal
section Shear

/--
  Lemma 1.2.1.2
  This is T in the notes.
-/
def S (F : Type*) [Field F] : Subgroup SL(2,F) where
  carrier := { s σ | σ : F }
  mul_mem' := by rintro S Q ⟨σS, hσS⟩ ⟨σQ, hσQ⟩
                 use σS + σQ; simp [← hσS, ← hσQ]
  one_mem' := ⟨0, s_zero_eq_one⟩
  inv_mem' := by rintro S ⟨σ, hσ⟩
                 use (-σ); simp [← hσ]

/- Lemma 1.2.1.4 { T σ } ≃* F -/
def S_iso_F (F : Type*) [Field F]: S F ≃* (Multiplicative F) where
  toFun T := T.val 1 0
  invFun σ := ⟨s σ, by use σ⟩
  left_inv T := by
    obtain ⟨σ, hσ⟩ := T.property
    rw [← Subtype.coe_inj, ← hσ]
    ext <;> simp [s, ← hσ]
  right_inv σ := by simp [s]
  map_mul' X Y := by
    obtain ⟨σ₁, hσ₁⟩ := X.property
    obtain ⟨σ₂, hσ₂⟩ := Y.property
    simp only [Subgroup.coe_mul, Fin.isValue, SpecialLinearGroup.coe_mul]
    simp_rw [← hσ₁, ← hσ₂]
    simp [s]
    rfl

end Shear

lemma D_meet_S_eq_bot (F : Type*) [Field F] : D F ⊓ S F = ⊥ := by
  ext x
  constructor
  · rintro ⟨x_mem_D, x_mem_T⟩
    obtain ⟨δ, hδ⟩ := x_mem_D
    obtain ⟨σ, hσ⟩ := x_mem_T
    rw [← hσ] at hδ
    rw [s_eq_d_iff] at hδ
    obtain ⟨-, rfl⟩ := hδ
    simp [← hσ]
  · intro h
    simp at h
    constructor
    · simp [h]
    · simp [h]
/--
  This is H in the notes.
-/
def L (F : Type*) [Field F] : Subgroup SL(2,F) where
  carrier := { d δ * s σ | (δ : Fˣ) (σ : F) }
  mul_mem' := by
              rintro A₁ A₂ ⟨δ₁, σ₁, h₁⟩ ⟨δ₂, σ₂, h₂⟩
              use (δ₁ * δ₂), (σ₁*δ₂*δ₂ + σ₂)
              rw [← h₁, ← h₂]
              ext
              · simp [d, s]
              · simp [d, s]
              · simp [d, s]; field_simp
              · simp [d, s, mul_comm]
  one_mem' := ⟨1, 0, by simp⟩
  inv_mem' := by
              rintro A ⟨δ, σ, h⟩
              use δ⁻¹, -σ * δ⁻¹ * δ⁻¹
              rw [← h]
              simp [d_mul_s_eq_ds, Matrix.SpecialLinearGroup.SL2_inv_expl]
              ext <;> simp [ds]

/-
For every lower triangular matrix, l,
there exists a representation of l as an element of L
-/
lemma mem_L_iff_lower_triangular [DecidableEq F] {x : SL(2,F)} :
  x ∈ L F ↔ MatrixShapes.IsLowerTriangular x.val := by
  constructor
  · intro hx
    rw [MatrixShapes.lower_triangular_iff]
    obtain ⟨δ, σ, h⟩ := hx
    use δ, σ * δ⁻¹, δ⁻¹
    rw [← h]
    ext <;> simp [d, s, mul_comm]
  · rw [MatrixShapes.lower_triangular_iff]
    rintro ⟨a, c, d, hx⟩
    have had : det (x : Matrix (Fin 2) (Fin 2) F) = 1 := by simp
    simp [← hx] at had
    have a_is_unit : IsUnit a := isUnit_of_mul_eq_one a d had
    have a_inv_eq_d : a⁻¹ = d := DivisionMonoid.inv_eq_of_mul a d had
    use a_is_unit.unit, c * a_is_unit.unit
    simp [SpecialMatrices.d, SpecialMatrices.s]
    ext <;>
    simp [← a_inv_eq_d, ← hx]
    rw [← mul_assoc]
    have a_ne_zero : a ≠ 0 := left_ne_zero_of_mul_eq_one had
    field_simp [a_ne_zero]

lemma S_le_L : S F ≤ L F := by
  rintro x ⟨σ, rfl⟩
  rw [L, mem_mk]
  use 1, σ
  rw [d_one_eq_one, one_mul]

/- Lemma 1.2.2.1 T is a normal subgroup of H = D T -/
lemma normal_S_subgroupOf_L {F : Type*} [Field F] : ((S F).subgroupOf (L F)).Normal := by
  rw [← normalizer_eq_top_iff]
  ext x
  constructor
  · intro _hx
    exact mem_top _
  · intro hx
    rw [← subgroupOf_self] at hx
    rw [mem_subgroupOf] at hx
    obtain ⟨δ, σ, hx⟩ := hx
    rw [mem_normalizer_iff'']
    intro t'
    constructor
    · rintro ⟨σ', hσ'⟩
      rw [mem_subgroupOf]
      dsimp at hσ' ⊢
      rw [← hx, ← hσ', _root_.mul_inv_rev, s_inv,
        inv_d_eq_d_inv, mul_assoc, mul_assoc (s (-σ)), ← mul_assoc (s σ'),
        ← mul_assoc (d δ⁻¹), ← mul_assoc (d δ⁻¹), d_eq_inv_d_inv δ,
        d_mul_s_mul_d_inv_eq_s, s_mul_s_eq_s_add, s_mul_s_eq_s_add]
      rw [S, inv_inv, neg_add_cancel_comm_assoc, mem_mk]
      use σ' * (δ : F) * (δ : F)
    · rintro ⟨σ', hσ'⟩
      rw [mem_subgroupOf]
      dsimp at hσ' ⊢
      have hσ : (t' : SL(2,F)) = (x : SL(2,F)) * s σ' * (x : SL(2,F))⁻¹ := by rw [hσ']; group
      rw [hσ, ← hx]
      rw [_root_.mul_inv_rev, s_inv, inv_d_eq_d_inv, mul_assoc (d δ), s_mul_s_eq_s_add,
         mul_assoc (d δ), ← mul_assoc (s (σ + σ')), s_mul_s_eq_s_add, ← mul_assoc,
         ← inv_d_eq_d_inv, d_mul_s_mul_d_inv_eq_s, add_neg_cancel_comm, Units.val_inv_eq_inv_val]
      use σ' * (δ : F)⁻¹ * (δ :F)⁻¹

def prod_monoidHom_join {G : Type*} [Group G] (H K : Subgroup G) [hH : Normal H] [hK : Normal K]
  (hHK : Disjoint H K) : H × K →* (H ⊔ K :) where
  toFun h_k := ⟨h_k.1 * h_k.2, mul_mem_sup h_k.1.property h_k.2.property⟩
  map_one' := by simp
  map_mul' := by
    rintro ⟨⟨h₁, hh₁⟩, ⟨k₁, hk₁⟩⟩ ⟨⟨h₂, hh₂⟩, ⟨k₂, hk₂⟩⟩
    simp
    rw [mul_assoc, mul_assoc, ← mul_assoc k₁,
      (Commute.eq (commute_of_normal_of_disjoint K H hK hH (Disjoint.symm hHK) k₁ h₂ hk₁ hh₂))]
    group

open Function

lemma Bijective_prod_monoidHom_join {G : Type*} [Group G] (H K : Subgroup G) [hH : Normal H]
  [hK : Normal K] (hHK : Disjoint H K) : Bijective (prod_monoidHom_join H K hHK) :=  by
  refine ⟨?injective, ?surjective⟩
  case injective =>
    rintro ⟨⟨h₁, h₁_in_H⟩, k₁, k₁_in_K⟩ ⟨⟨h₂, h₂_in_H⟩, k₂, k₂_in_K⟩ h
    simp [prod_monoidHom_join] at h
    have : h₁⁻¹ * h₂ * k₂ * k₁⁻¹ = 1 := by
      rw [mul_assoc, mul_assoc, ← mul_assoc h₂, ← h]
      group
    -- show h₁ * h₂⁻¹  = 1 and k₁ * k₂⁻¹ = 1
    have H₁ : k₂ * k₁⁻¹ = (k₁ * k₂⁻¹)⁻¹ := by
      group
    have key₁ : h₁⁻¹ * h₂ = k₁ * k₂⁻¹ := by
      rw [mul_assoc] at this
      rw [H₁, mul_inv_eq_one] at this
      exact this
    have mul_in_H : k₁ * k₂⁻¹ ∈ H := key₁.symm ▸ mul_mem (inv_mem h₁_in_H) h₂_in_H
    have mul_in_K : k₁ * k₂⁻¹ ∈ K := mul_mem k₁_in_K (inv_mem k₂_in_K)
    rw [disjoint_iff_inf_le] at hHK
    have key₂ : k₁ * k₂⁻¹ = 1 := by
      rw [← mem_bot]
      apply hHK
      refine mem_inf.mpr ⟨mul_in_H, mul_in_K⟩
    rw [key₂] at key₁
    rw [inv_mul_eq_one] at key₁
    rw [mul_inv_eq_one] at key₂
    ext <;> simp [key₁, key₂]
  case surjective =>
    rintro ⟨x, hx⟩
    rw [← SetLike.mem_coe, mul_normal] at hx
    obtain ⟨h, h_in_H, k, k_in_K, hh⟩ := hx
    use ⟨⟨h, h_in_H⟩, ⟨k, k_in_K⟩⟩
    simp [prod_monoidHom_join, hh]

noncomputable def prod_mulEquiv_join_of_disjoint_of_normal {G : Type*} [Group G] (H K : Subgroup G)
  (hHK : Disjoint H K) [hH : Normal H] [hK : Normal K] : H × K ≃* (H ⊔ K :) :=
  MulEquiv.ofBijective (prod_monoidHom_join H K hHK) (Bijective_prod_monoidHom_join H K hHK)


lemma D_mul_S_le_L (F : Type*) [Field F] : ((D F) : Set SL(2,F)) * (S F) ⊆ (L F) := by
  rintro x ⟨d, ⟨δ, rfl⟩, s, ⟨σ, rfl⟩, rfl⟩
  simp [L]

lemma D_join_S_eq_L (F : Type*) [Field F]: D F ⊔ S F = L F := by
  ext x
  constructor
  · intro hx
    rw [sup_eq_closure_mul, mem_closure] at hx
    exact hx (L F) (D_mul_S_le_L F)
  · rintro ⟨δ, σ, rfl⟩
    rw [sup_eq_closure_mul, mem_closure]
    intro K hK
    apply hK
    rw [Set.mem_mul]
    use d δ
    split_ands
    · use δ
    use s σ
    split_ands
    · use σ
    rfl





-- second isomorphism theorem!!!!
#check QuotientGroup.quotientInfEquivProdNormalQuotient

def D_subgroupOf_L_mulEquiv_D : (D F).subgroupOf (L F) ≃* D F := by
  refine subgroupOfEquivOfLe ?_
  rintro d ⟨δ, rfl⟩
  simp [L]
  use δ, 0
  simp

def S_subgroupOf_L_mulEquiv_S : (S F).subgroupOf (L F) ≃* S F := by
  refine subgroupOfEquivOfLe ?_
  rintro s ⟨σ, rfl⟩
  simp [L]
  use 1, σ
  simp

instance group_L_quot_S_subgroupOf_L :
  Group ((L F) ⧸ (S F).subgroupOf (L F)) :=
    @QuotientGroup.Quotient.group (L F) _ ((S F).subgroupOf (L F)) (normal_S_subgroupOf_L)

instance : ((S F).subgroupOf (D F ⊔ S F :)).Normal := by
  rw [D_join_S_eq_L]
  exact normal_S_subgroupOf_L

lemma left_subgroupOf_join_right_subgroupOf_join_eq_join_subgroupOf_join {G : Type*}
  [Group G] (H K : Subgroup G) :
  H.subgroupOf (H ⊔ K) ⊔ K.subgroupOf (H ⊔ K) = ⊤ := by
  rw [← comap_subtype, ← comap_subtype]
  let f := (H ⊔ K).subtype
  have hH : H ≤ f.range := by simp [f]
  have hK : K ≤ f.range := by simp [f]
  rw [comap_sup_eq_of_le_range f hH hK]
  simp [f]

lemma simplify₁ : ((D F).subgroupOf (D F ⊔ S F) ⊔ (S F).subgroupOf (D F ⊔ S F)) = ⊤ :=
  left_subgroupOf_join_right_subgroupOf_join_eq_join_subgroupOf_join (D F) (S F)

/- D and S have trivial interesection, so the following holds -/
lemma simplify₂ : ((S F).subgroupOf (D F ⊔ S F)).subgroupOf ((D F).subgroupOf (D F ⊔ S F)) = ⊥ := by
  simp
  rw [disjoint_iff, ← comap_subtype, ← comap_subtype, ← comap_inf, inf_comm, D_meet_S_eq_bot]
  simp

/- The second isomorphism theorem -/
noncomputable def D_join_S_quot_S_subgroupOf_D_join_S_mulEquiv_D_subgroupOf_D_join_S
  (F : Type*) [Field F] :=
  (QuotientGroup.quotientInfEquivProdNormalQuotient
    (H := (D F).subgroupOf (D F ⊔ S F:)) (N := (S F).subgroupOf (D F ⊔ S F :))).symm

#check D_join_S_quot_S_subgroupOf_D_join_S_mulEquiv_D_subgroupOf_D_join_S

def LHS (F : Type*) [Field F] :=
  @QuotientGroup.equivQuotientSubgroupOfOfEq



#check QuotientGroup.quotientBot

#check MulEquiv.trans

#check QuotientGroup.equivQuotientSubgroupOfOfEq

#check QuotientGroup.quotientMulEquivOfEq

def RHS (F : Type*) [Field F] :=
  @QuotientGroup.equivQuotientSubgroupOfOfEq ((D F).subgroupOf (D F ⊔ S F) :) _
    (A' := ((S F).subgroupOf (D F ⊔ S F)).subgroupOf ((D F).subgroupOf (D F ⊔ S F)))
    -- below were ⊤ : (D F).subgroupOf (D F ⊔ S F)
    (A := ⊤)--((D F).subgroupOf (D F ⊔ S F)).subgroupOf ((D F).subgroupOf (D F ⊔ S F)))
    (B' := ⊥)
    (B := ⊤)--((D F).subgroupOf (D F ⊔ S F)).subgroupOf ((D F).subgroupOf (D F ⊔ S F)))
    (hAN := normal_subgroupOf)
    (hBN := normal_subgroupOf)
    (h' := simplify₂)
    (h := Eq.refl _)

#check RHS


-- def RHS' (F : Type*) [Field F] :
--   ↥(⊤ : Subgroup ↥((D F).subgroupOf (D F ⊔ S F))) ⧸ (⊥ : Subgroup ((D F).subgroupOf (D F ⊔ S F))).subgroupOf (⊤ : Subgroup ↥((D F).subgroupOf (D F ⊔ S F)))
--   ≃*
--   ↥(⊤ : Subgroup ↥((D F).subgroupOf (D F ⊔ S F))) :=
--   @QuotientGroup.quotientBot (((D F).subgroupOf (D F ⊔ S F)) :) _

-- Conclusion to reach is
instance : ((S F).subgroupOf (L F)).Normal := normal_S_subgroupOf_L

noncomputable def L_quot_S_subgroupOf_L_mulEquiv_D_subgroupOf_L :=
    QuotientGroup.quotientInfEquivProdNormalQuotient
      (H := (L F).subgroupOf (L F)) (N := (S F).subgroupOf (L F :))


#check L_quot_S_subgroupOf_L_mulEquiv_D_subgroupOf_L

-- lemma foo : ((S F).subgroupOf (L F)).subgroupOf ((L F).subgroupOf (L F)) = (S F).subgroupOf (L F) := by sorry

#check D_join_S_quot_S_subgroupOf_D_join_S_mulEquiv_D_subgroupOf_D_join_S

#check L_quot_S_subgroupOf_L_mulEquiv_D_subgroupOf_L

#check ((S F).subgroupOf (L F)).subgroupOf ((L F).subgroupOf (L F) ⊔ (S F).subgroupOf (L F))

  --@QuotientGroup.Quotient.group (L F) _ ((S F).subgroupOf (L F)) (normal_S_subgroupOf_L)

def D_join_S_monoidHom_D : (D F × S F :) →* D F where
  toFun d_s := d_s.1
  map_one' := by simp
  map_mul' := by simp

def DW (F : Type*) [Field F] : Subgroup SL(2,F) where
  carrier := { d δ | δ : Fˣ} ∪ { d δ * w | δ : Fˣ}
  mul_mem' := by
    rintro x y (⟨δ₁, rfl⟩ | ⟨δ₁, rfl⟩) (⟨δ₂, rfl⟩ | ⟨δ₂, rfl⟩)
    · rw [d_mul_d_eq_d_mul]
      left
      use δ₁ * δ₂
    · rw [← mul_assoc, d_mul_d_eq_d_mul]
      right
      use δ₁ * δ₂
    · rw [mul_assoc, w_mul_d_eq_d_inv_w, inv_d_eq_d_inv, ← mul_assoc, d_mul_d_eq_d_mul]
      right
      use δ₁ * δ₂⁻¹
    · rw [mul_assoc, ← mul_assoc w, w_mul_d_eq_d_inv_w, mul_assoc _ w, w_mul_w_eq_neg_one,
       inv_d_eq_d_inv, ← mul_assoc, d_mul_d_eq_d_mul, mul_neg_one, neg_d_eq_d_neg]
      left
      use -(δ₁ * δ₂⁻¹)
  one_mem' := by left; rw [← d_one_eq_one]; use 1
  inv_mem' := by
    intro x h
    simp at h
    rcases h with (⟨δ, rfl⟩ | ⟨δ, rfl⟩)
    · simp
    · simp

lemma D_le_DW : D F ≤ DW F := by
  rintro x ⟨δ, rfl⟩
  rw [DW, mem_mk]
  left
  apply exists_apply_eq_apply


lemma Dw_le_DW : (D F : Set SL(2,F)) * ({w} : Set SL(2,F)) ⊆ (DW F :  Set SL(2,F)) := by
  rintro x ⟨d', hd', w, hw, rfl⟩
  obtain ⟨δ, rfl⟩ := hd'
  rw [DW, coe_set_mk]
  right
  use δ
  rw [Set.mem_singleton_iff] at hw
  rw [hw]

@[simp]
lemma w_not_mem_D {F : Type*} [Field F] : w ∉ D F := by
  intro contr
  obtain ⟨δ, hδ⟩ := contr
  simp [SpecialLinearGroup.fin_two_ext_iff, w, d] at hδ

@[simp]
lemma neg_mem_D_iff_mem_D {F : Type*} [Field F] {x : SL(2,F)} : -x ∈ D F  ↔ x ∈ D F  := by
  constructor
  · rintro ⟨δ, hδ⟩
    rw [← neg_eq_iff_eq_neg] at hδ
    subst hδ
    simp
  · rintro ⟨δ, rfl⟩
    simp

lemma D_sup_closure_w_eq_DW {F : Type*} [Field F] : DW F = (D F) ⊔ Subgroup.closure {w} := by
  rw [sup_eq_closure_mul]
  apply le_antisymm
  · rintro x (⟨δ, rfl⟩ | ⟨δ, rfl⟩) <;> rw [mem_closure] <;> intro K hK <;>
    apply hK <;> rw [Set.mem_mul] <;> use d δ <;> simp
  · intro x hx
    rw [mem_closure] at hx
    apply hx; rintro y ⟨_, ⟨δ, rfl⟩, w', hw', rfl⟩
    rw [← zpowers_eq_closure] at hw'
    rcases mem_zpowers_iff.mp hw' with ⟨k, rfl⟩
    have hw4 : (w : SL(2,F)) ^ (4 : ℤ) = 1 := by
      show w ^ (4 : ℕ) = 1
      simp [pow_succ, pow_zero, w_mul_w_eq_neg_one]
    have hk : (w : SL(2,F)) ^ k = w ^ (k % 4) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 4]
      rw [zpow_add, zpow_mul, hw4, one_zpow, mul_one]
    have : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases this with (h | h | h | h) <;> simp only [h, hk]
    · simp; left; use δ
    · simp; right; use δ
    · rw [zpow_two, w_mul_w_eq_neg_one]; left; use -δ; simp
    · rw [show (3 : ℤ) = 2 + 1 by norm_num, zpow_add, zpow_two, zpow_one, w_mul_w_eq_neg_one]
      right; use -δ; simp


section Center

def Z (R : Type*) [CommRing R] : Subgroup SL(2,R) := closure {(-1 : SL(2,R))}

lemma get_entries (x : SL(2,F)) : ∃ α β γ δ,
  α = x.1 0 0 ∧ β = x.1 0 1 ∧ γ = x.1 1 0 ∧ δ = x.1 1 1 ∧
  (x : Matrix (Fin 2) (Fin 2) F) = !![α, β; γ, δ] := by
  use x.1 0 0, x.1 0 1, x.1 1 0, x.1 1 1
  split_ands
  repeat' rfl
  ext <;> rfl

lemma neg_one_mem_Z : (-1 : SL(2,F)) ∈ Z F := by simp [Z]


lemma Odd.neg_one_zpow {α : Type*} [Group α] [HasDistribNeg α] {n : ℤ} (h : Odd n) :
  (-1 : α) ^ n = -1 := by
  rw [← neg_eq_iff_eq_neg, ← neg_one_mul, Commute.neg_one_left, mul_zpow_self]
  exact Even.neg_one_zpow <| Odd.add_one h


lemma closure_neg_one_eq : (closure {(-1 : SL(2,R))} : Set SL(2,R)) = {1, -1} := by
  ext x
  constructor
  · intro hx
    rw [← zpowers_eq_closure, SetLike.mem_coe, mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases hk : Even k
    · left
      apply Even.neg_one_zpow hk
    · right;
      rw [Int.not_even_iff_odd] at hk
      exact Odd.neg_one_zpow hk
  · intro hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with (rfl | rfl)
    · rw [SetLike.mem_coe, mem_closure_singleton]
      use 2
      apply Even.neg_one_zpow (by norm_num)
    · rw [SetLike.mem_coe]
      exact mem_closure_singleton_self (-1)


@[simp]
lemma neg_one_neq_one_of_two_ne_zero [NeZero (2 : F)] : (1 : SL(2,F)) ≠ (-1 : SL(2,F)) := by
  intro h
  have neg_one_eq_one : (1 : SL(2,F)).1 0 0 = (-1 : SL(2,F)).1 0 0 := by nth_rewrite 1 [h]; rfl
  simp at neg_one_eq_one
  symm at neg_one_eq_one
  let inst : Nontrivial F := CommGroupWithZero.toNontrivial
  rw [neg_one_eq_one_iff] at neg_one_eq_one
  let inst : CharP F 2 := ringChar.eq_iff.mp neg_one_eq_one
  have two_eq_zero : (2 : F) = 0 := CharTwo.two_eq_zero
  have two_ne_zero : (2 : F) ≠ 0 := two_ne_zero
  contradiction

lemma Field.one_eq_neg_one_of_two_eq_zero (two_eq_zero : (2 : F) = 0) : 1 = (-1 : F) := by
  rw [← one_add_one_eq_two, add_eq_zero_iff_neg_eq'] at two_eq_zero
  exact two_eq_zero.symm


lemma SpecialLinearGroup.neg_one_eq_one_of_two_eq_zero (two_eq_zero : (2 : F) = 0) :
  1 = (-1 : SL(2,F)) := by
  ext
  <;> simpa using Field.one_eq_neg_one_of_two_eq_zero two_eq_zero



@[simp]
lemma set_Z_eq : (Z R : Set SL(2,R)) = {1, -1} := by
  dsimp [Z]
  rw [closure_neg_one_eq]

@[simp]
lemma Z_carrier_eq : (Z R).carrier = {1, -1} := by
  rw [← set_Z_eq]
  rfl

@[simp]
lemma mem_Z_iff {x : SL(2,R)}: x ∈ Z R ↔ x = 1 ∨ x = -1 := by
  rw [← mem_carrier, Z_carrier_eq, Set.mem_insert_iff, Set.mem_singleton_iff]

instance : Finite (Z F) := by
  simp only [mem_Z_iff]
  exact Finite.Set.finite_insert 1 {-1}

lemma center_SL2_eq_Z (R : Type*)  [CommRing R] [NoZeroDivisors R]: center SL(2,R) = Z R := by
  ext x
  constructor
  · intro hx
    rw [SpecialLinearGroup.mem_center_iff] at hx
    obtain ⟨z, z_pow_two_eq_one, hz⟩ := hx
    simp at z_pow_two_eq_one hz ⊢
    rcases z_pow_two_eq_one with (rfl | rfl)
    · left
      ext <;> simp [← hz]
    · right
      ext <;> simp [← hz]
  · simp
    rintro (rfl | rfl) <;> simp [mem_center_iff]

instance : Finite (center SL(2,F)) := by
  rw [center_SL2_eq_Z F]
  infer_instance


lemma card_Z_eq_two_of_two_ne_zero [NeZero (2 : F)]: Nat.card (Z F) = 2 := by
  rw [Nat.card_eq_two_iff]
  use 1, ⟨-1, neg_one_mem_Z⟩
  split_ands
  · intro h
    rw [Subtype.ext_iff] at h
    -- -1 ≠ 1 for characteristic different to 2
    simp at h
  · rw [Set.eq_univ_iff_forall]
    rintro ⟨z, hz⟩
    simp at hz
    rcases hz with (rfl | rfl) <;> simp

lemma card_Z_eq_one_of_two_eq_zero (two_eq_zero : (2 : F) = 0) : Nat.card (Z F) = 1 := by
  rw [card_eq_one]
  ext x
  simp [(SpecialLinearGroup.neg_one_eq_one_of_two_eq_zero two_eq_zero).symm]

lemma card_Z_le_two : Nat.card (Z F) ≤ 2 := by
  by_cases h : (2 : F) = 0
  · rw [card_Z_eq_one_of_two_eq_zero h]
    linarith
  · let inst : NeZero (2 : F) := { out := h }
    rw [card_Z_eq_two_of_two_ne_zero]


lemma orderOf_neg_one_eq_two [NeZero (2 : F)]: orderOf (-1 : SL(2,F)) = 2 := by
  have order_dvd_two : (orderOf (-1 : SL(2,F))) ∣ 2 ∧ 2 ≠ 0 := by
    split_ands
    rw [orderOf_dvd_iff_pow_eq_one ]; simp
    simp
  have order_neq_one : (orderOf (-1 : SL(2,F))) ≠ 1 := by
    simp only [ne_eq, orderOf_eq_one_iff]
    rw [← ne_eq]
    symm
    apply neg_one_neq_one_of_two_ne_zero
  rw [← Nat.mem_divisors, Nat.Prime.divisors Nat.prime_two, Finset.mem_insert] at order_dvd_two
  rcases order_dvd_two with (order_eq_one | order_eq_two)
  · contradiction
  · rw [Finset.mem_singleton] at order_eq_two
    exact order_eq_two

-- Lemma 1.4 If p ≠ 2, then SL(2,F) contains a unique element of order 2.
lemma exists_unique_orderOf_eq_two [NeZero (2 : F)] : ∃! x : SL(2,F), orderOf x = 2 := by
  use -1
  split_ands
  · exact orderOf_neg_one_eq_two
  -- Now we show it is the unique element of order two
  intro x hx
  rcases get_entries x with ⟨α, β, γ, _δ, _x_eq⟩
  simp [propext (orderOf_eq_iff (Nat.le.step Nat.le.refl))] at hx
  obtain ⟨hx₁, hx₂⟩ := hx
  rw [sq, mul_eq_one_iff_eq_inv'] at hx₁
  rw [SpecialLinearGroup.fin_two_ext_iff] at hx₁
  simp [adjugate_fin_two] at hx₁
  obtain ⟨α_eq_δ, β_eq_neg_β, γ_eq_neg_γ, -⟩ := hx₁
  rw [eq_neg_iff_add_eq_zero, ← two_mul] at β_eq_neg_β γ_eq_neg_γ
  have β_eq_zero : x.1 0 1 = 0 := eq_zero_of_ne_zero_of_mul_left_eq_zero two_ne_zero β_eq_neg_β
  have γ_eq_zero : x.1 1 0 = 0 := eq_zero_of_ne_zero_of_mul_left_eq_zero two_ne_zero γ_eq_neg_γ
  have det_x_eq_one : det (x : Matrix (Fin 2) (Fin 2) F) = 1 :=  by simp
  rw [det_fin_two, β_eq_zero, zero_mul, sub_zero, α_eq_δ, mul_self_eq_one_iff] at det_x_eq_one
  rcases det_x_eq_one with (δ_eq_one | δ_eq_neg_one )
  have α_eq_δ := α_eq_δ
  · rw [δ_eq_one] at α_eq_δ
    have x_eq_one : x = 1 := by ext <;> simp [α_eq_δ, β_eq_zero, γ_eq_zero, δ_eq_one]
    specialize hx₂ 1 (by norm_num) (by norm_num)
    rw [pow_one] at hx₂
    contradiction
  · rw [δ_eq_neg_one] at α_eq_δ
    ext <;> simp [α_eq_δ, β_eq_zero, γ_eq_zero, δ_eq_neg_one]

instance IsCyclic_Z : IsCyclic (Z F) := by
  apply isCyclic_iff_exists_orderOf_eq_natCard.mpr ?_
  by_cases h : NeZero (2 : F)
  · rw [card_Z_eq_two_of_two_ne_zero]
    use ⟨-1, neg_one_mem_Z ⟩
    simp
    exact orderOf_neg_one_eq_two
  · have two_eq_zero : (2 : F) = 0 := by exact not_neZero.mp h
    rw [card_Z_eq_one_of_two_eq_zero two_eq_zero]
    simp only [orderOf_eq_one_iff, exists_eq]

instance IsCommutative_Z : IsMulCommutative (Z F) := inferInstance


namespace IsPGroup


/- Lemma 2.1. If G is a finite group of order pm where p is prime and m > 0,
then p divides |Z(G)|.-/
lemma p_dvd_card_center {H : Type*} {p : ℕ} (hp:  Nat.Prime p) [Group H] [Finite H] [Nontrivial H]
  (hH : IsPGroup p H) : p ∣ Nat.card (center H) := by
  let inst : Fact (Nat.Prime p) := by exact { out := hp }
  have card_H_eq_pow_prime : ∃ n > 0, Nat.card H = p ^ n := by rwa [← hH.nontrivial_iff_card]
  suffices ∃ k > 0, Nat.card (center H) = p ^ k by
    obtain ⟨k, kpos, hk⟩ := this
    use p^(k-1)
    rw [hk, ← Nat.pow_add_one', Nat.sub_add_cancel]
    linarith
  obtain ⟨n, npos, hn⟩ := card_H_eq_pow_prime
  exact IsPGroup.card_center_eq_prime_pow hn npos

end IsPGroup

end Center

def SZ (F : Type*) [Field F] : Subgroup SL(2,F) where
  carrier := { s σ | σ : F } ∪ { - s σ | σ : F }
  mul_mem' := by
    rintro x y (⟨σ₁, rfl⟩ | ⟨σ₁, rfl⟩) (⟨σ₂, rfl⟩ | ⟨σ₂, rfl⟩)
    repeat' simp
  one_mem' := by
    rw [← s_zero_eq_one]; left; use 0
  inv_mem' :=  by
    rintro x (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
    repeat' simp


def SZ' (F : Type*) [Field F] : Subgroup SL(2,F) where
  carrier := S F * Z F
  mul_mem' := by
    rintro a b ⟨s₁, hs₁, ⟨z₁, hz₁, rfl⟩⟩ ⟨s₂, hs₂, ⟨z₂, hz₂, rfl⟩⟩
    simp only [SetLike.mem_coe] at hs₁ hs₂ hz₁ hz₂ ⊢
    group
    have hz₁' := hz₁
    simp only [← center_SL2_eq_Z] at hz₁'
    rw [mul_assoc s₁, (mem_center_iff.mp hz₁' s₂).symm]
    group
    use s₁ * s₂
    constructor
    · exact Subgroup.mul_mem _ hs₁ hs₂
    use z₁ * z₂
    constructor
    · exact Subgroup.mul_mem _ hz₁ hz₂
    group
  one_mem' := by
    use 1
    constructor
    · use 0, s_zero_eq_one
    use 1
    constructor
    · simp
    group
  inv_mem' := by
    rintro x ⟨s, hs, ⟨z, hz, rfl⟩⟩
    simp at hs
    have hz' := hz
    simp [← center_SL2_eq_Z] at hz
    simp only [_root_.mul_inv_rev,
       (mem_center_iff.mp ((Subgroup.inv_mem_iff (center SL(2, F))).mpr hz) s⁻¹).symm]
    use s⁻¹
    constructor
    · simp [hs]
    use z⁻¹
    constructor
    · exact (Subgroup.inv_mem_iff (Z F)).mpr hz'
    group

lemma SZ_eq_SZ' {F : Type*} [Field F] : SZ' F = SZ F := by
  ext x
  constructor
  · rintro ⟨t, ht, z, hz, rfl⟩
    simp at hz ht
    obtain ⟨σ, rfl⟩ := ht
    -- z = 1 or z = -1
    rcases hz with (rfl | rfl)
    · left
      use σ
      simp
    · right
      use σ
      simp
  · intro hx
    rcases hx with (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
    · use s σ
      constructor
      · use σ
      use 1
      constructor
      · simp
      · simp
    · use s σ
      constructor
      · use σ
      use -1
      constructor
      · simp
      · simp


lemma S_mul_Z_subset_SZ :
  ((S F) : Set SL(2,F)) * ((Z F) : Set SL(2,F)) ⊆ ((SZ F) : Set SL(2,F)) := by
  rintro x ⟨t', ht', z, hz, hσ, h⟩
  obtain ⟨σ, rfl⟩ := ht'
  dsimp [Z] at hz
  dsimp
  rw [closure_neg_one_eq] at hz
  simp [SZ]
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with (rfl | rfl)
  left
  use σ
  rw [mul_one]
  right
  use σ
  simp

-- ordering propositions so when proving it can be done more efficiently
#check Set.mem_mul


section CommutativeSubgroups

lemma IsMulCommutative_iff {G : Type*} [Group G] {H : Subgroup G} :
  IsMulCommutative H ↔ ∀ x y : H, x * y = y * x := by
  constructor
  · intro h x y
    have := @mul_comm_of_mem_isMulCommutative G _ H h x y (by simp) (by simp)
    exact SetLike.coe_eq_coe.mp this
  · intro h
    rw [← le_centralizer_iff_isMulCommutative]
    intro y hy
    rw [mem_centralizer_iff]
    intro x hx
    simp only [SetLike.mem_coe] at hx
    specialize h ⟨x, hx⟩ ⟨y, hy⟩
    simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq] at h
    exact h

instance IsMulCommutative_D : IsMulCommutative (D F) := by
  rw [IsMulCommutative_iff]
  rintro ⟨x, ⟨δ₁, hδ₁⟩⟩ ⟨y, ⟨δ₂, hδ₂⟩⟩
  simp [← hδ₁, ← hδ₂, mul_comm]

instance IsMulCommutative_S (F : Type*) [Field F] : IsMulCommutative (S F) := by
  rw [IsMulCommutative_iff]
  rintro ⟨x, ⟨σ₁, hσ₁⟩⟩ ⟨y, ⟨σ₂, hσ₂⟩⟩
  simp [Subtype.ext_iff]
  rw [← hσ₁, ← hσ₂]
  simp [add_comm]

instance IsMulCommutative_SZ (F : Type*) [Field F] : IsMulCommutative (SZ F) := by
  refine le_centralizer_iff_isMulCommutative.mp ?_
  rintro x (⟨σ₁, rfl⟩ | ⟨σ₁, rfl⟩)
  repeat
  rw [mem_centralizer_iff]
  rintro y (⟨σ₂, rfl⟩ | ⟨σ₂, rfl⟩)
  repeat' simp [add_comm]

end CommutativeSubgroups

theorem val_eq_neg_one {a : Fˣ} : (a : F) = -1 ↔ a = (-1 : Fˣ) := by
  rw [Units.ext_iff, Units.coe_neg_one];


lemma ex_of_card_D_gt_two {D₀ : Subgroup SL(2,F) }(hD₀ : 2 < Nat.card D₀) (D₀_leq_D : D₀ ≤ D F) :
  ∃ δ : Fˣ, (δ : F) ≠ 1 ∧ (δ : F) ≠ -1 ∧ d δ ∈ D₀ := by
  by_contra! h
  have D₀_le_Z : D₀.carrier ≤ Z F := by
    simp
    intro x hx
    obtain ⟨δ, rfl⟩ := D₀_leq_D hx
    rw [Set.mem_insert_iff]
    by_cases h₀ : (δ : F) = 1
    · left;
      rw [Units.val_eq_one] at h₀
      rw [h₀, d_one_eq_one]
    · by_cases h₁ : (δ : F) = -1
      · right
        rw [val_eq_neg_one] at h₁
        rw [h₁, d_neg_one_eq_neg_one, Set.mem_singleton_iff]
      · rw [← ne_eq] at h₀ h₁
        specialize h δ h₀ h₁
        contradiction
  have card_D₀_leq_two : Nat.card D₀ ≤ 2 :=
    le_trans (Subgroup.card_le_of_le D₀_le_Z) card_Z_le_two
  linarith


lemma mem_D_iff {x : SL(2,F)} : x ∈ D F ↔ ∃ δ : Fˣ, d δ = x := by rfl


lemma mem_D_w_iff {x : SL(2,F)} : x ∈ (D F : Set SL(2,F)) * {w} ↔ ∃ δ : Fˣ, d δ * w = x := by
  constructor
  · rintro ⟨d', ⟨δ, rfl⟩, w, ⟨rfl⟩, rfl⟩
    use δ
  · rintro ⟨δ, rfl⟩
    simp [D]
    use δ
    rw [mul_assoc, w_mul_w_eq_neg_one, mul_neg, mul_one, neg_neg]

lemma S_join_Z_eq_SZ : S F ⊔ Z F = SZ F := by
  ext x
  constructor
  · intro hx
    rw [sup_eq_closure_mul, mem_closure] at hx
    exact hx (SZ F) (S_mul_Z_subset_SZ)
  · rintro (⟨σ, rfl⟩ | ⟨σ, rfl⟩) <;> rw [sup_eq_closure_mul]
    · have mem_Z_mul_S : s σ ∈ ((S F) : Set SL(2,F)) * (Z F) := by
        rw [Set.mem_mul]
        use s σ
        split_ands
        simp only [SetLike.mem_coe]
        use σ
        simp
      apply Subgroup.subset_closure mem_Z_mul_S
    · have mem_Z_mul_T : -s σ ∈ ((S F) : Set SL(2,F)) * (Z F) := by
        rw [Set.mem_mul]
        use s σ
        split_ands
        simp only [SetLike.mem_coe]
        use σ
        simp
      apply Subgroup.subset_closure mem_Z_mul_T


end SpecialSubgroups

#min_imports
