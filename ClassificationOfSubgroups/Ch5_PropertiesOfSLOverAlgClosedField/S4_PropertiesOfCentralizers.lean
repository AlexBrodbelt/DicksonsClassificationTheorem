import ClassificationOfSubgroups.Ch5_PropertiesOfSLOverAlgClosedField.S3_JordanNormalFormOfSL

set_option autoImplicit false
set_option linter.style.longLine true

open Matrix MatrixGroups Subgroup Pointwise

open SpecialMatrices SpecialSubgroups

universe u

variable
  {F : Type u} [Field F]
  (n : Type u) [Fintype n]
  (R : Type u) [CommRing R]
  {G : Type u} [Group G]

/- Proposition 1.6.ii C_L(± s σ) = T × Z where σ ≠ 0 -/
theorem centralizer_s_eq_SZ {σ : F} (hσ : σ ≠ 0) : centralizer { s σ } = SZ F := by
  ext x
  constructor
  · intro hx
    simp [mem_centralizer_iff] at hx
    rw [SpecialLinearGroup.fin_two_ext_iff] at hx
    simp [s] at hx
    obtain ⟨top_right, -, bottom_left, -⟩ := hx
    rcases get_entries x with ⟨α, β, γ, δ, hα, hβ, -, hδ, x_eq⟩
    simp [x_eq, hσ] at top_right bottom_left
    rw [add_comm γ] at bottom_left
    have α_eq_δ : σ * α = σ * δ := by rw [mul_comm σ δ, eq_iff_eq_of_add_eq_add bottom_left]
    rw [mul_eq_mul_left_iff, or_iff_not_imp_right] at α_eq_δ
    specialize α_eq_δ hσ
    simp [SZ]
    -- is a shear matrix if diagonal entries are equal and top right entry is zero
    rw [← SpecialLinearGroup.fin_two_shear_iff]
    constructor
    -- diagonal entries are equal
    · rw [← hα, ← hδ, α_eq_δ]
    -- top right entry is zero
    · rw [← hβ, top_right]
  · rintro (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
    repeat
    rw [mem_centralizer_iff]
    intro y hy
    simp at hy
    rw [hy]
    simp [add_comm]


lemma Field.self_eq_inv_iff (x : F) (x_ne_zero : x ≠ 0) : x = x⁻¹ ↔ x = 1 ∨ x = - 1 := by
  rw [← sq_eq_one_iff, sq, (mul_eq_one_iff_eq_inv₀ x_ne_zero)]

lemma Units.val_neg_one : ((-1 : Fˣ) : F) = -1 := by simp only [Units.val_neg, val_one]

lemma Units.val_eq_neg_one (x : Fˣ) : (x : F) = -1 ↔ x = (-1 : Fˣ) := by
  rw [← Units.val_neg_one, val_inj]

lemma centralizer_d_eq_D (δ : Fˣ) (δ_ne_one : δ ≠ 1) (δ_ne_neg_one : δ ≠ -1) :
  centralizer {d δ} = D F := by
  ext x
  constructor
  · intro hx
    simp [mem_centralizer_iff] at hx
    rcases get_entries x with ⟨a, b, c, d, _ha, hb', hc', _hd, x_eq⟩
    simp [SpecialLinearGroup.fin_two_ext_iff, SpecialMatrices.d, x_eq] at hx
    obtain ⟨-, hb, hc, -⟩ := hx
    have δ_ne_zero : (δ : F) ≠ 0 := Units.ne_zero δ
    have δ_ne_δ_inv : (δ : F) ≠ δ⁻¹ := by
      intro h
      rw [Units.val_inj] at h
      rw [← mul_eq_one_iff_eq_inv] at h
      suffices δ = 1 ∨ δ = -1 by
        rcases this <;> contradiction
      refine Units.eq_or_eq_neg_of_sq_eq_sq δ 1 ?_
      rwa [one_pow, sq]
    rw [mul_comm, mul_eq_mul_left_iff] at hb hc
    -- rw [ne_eq] at δ_ne_δ_inv
    have not_eq_inv : ¬ (δ : F)⁻¹ = (δ : F) := by
      norm_cast
      exact fun a ↦ δ_ne_δ_inv (congrArg Units.val (id (Eq.symm a)))
    replace hb : b = 0 := Or.resolve_left hb (Ne.symm not_eq_inv)
    replace hc : c = 0 := Or.resolve_left hc not_eq_inv
    rw [mem_D_iff, ← SpecialLinearGroup.fin_two_diagonal_iff]
    simp [hb, hc, ← hb', ← hc']
  · rintro ⟨δ', rfl⟩
    simp [mem_centralizer_iff, mul_comm]

lemma centralizer_d_eq_D' (δ : Fˣ) (hd: d δ ∉ center SL(2,F)) : centralizer {d δ} = D F := by
  simp [center_SL2_eq_Z, ← ne_eq] at hd
  apply centralizer_d_eq_D δ
  · rintro rfl
    simp at hd
  · rintro rfl
    simp at hd

open MulAction MulAut

lemma centralizer_neg_eq_centralizer {x : SL(2,F)} : centralizer {x} = centralizer {-x} := by
  ext; constructor <;> simp [mem_centralizer_iff_commutator_eq_one]

/-
Proposition 1.8.
Let a and b be conjugate elements in a group G. Then ∃ x ∈ G such that x C_G(a) x⁻¹ = C_G (b).
-/
lemma conjugate_centralizers_of_IsConj  (a b : G) (hab : IsConj a b) :
  ∃ x : G, conj x • (centralizer { a }) = centralizer { b } := by
  rw [isConj_iff] at hab
  obtain ⟨x, hc⟩ := hab
  use x
  ext y
  simp [centralizer, MulAut.conj]
  constructor
  · rintro ⟨y', y'_in_cen, hy'⟩
    simp at hy' y'_in_cen ⊢
    rw [Set.mem_centralizer_iff]
    rintro m ⟨rfl⟩
    have : a * y' = y' * a := by exact y'_in_cen a rfl
    rw [← hy', ← hc]
    group
    rw [mul_assoc x a, this]
    group
  · intro hy
    simp [Set.mem_centralizer_iff] at hy
    have : y = b * y * b⁻¹ := by rw [hy]; group
    simp [← hc] at this hy
    use a * x⁻¹ * y * x * a⁻¹
    split_ands
    · simp
      rw [Set.mem_centralizer_iff]
      simp_rw [Set.mem_singleton_iff, forall_eq, inv_mul_cancel_right]
      nth_rewrite 1 [← mul_one a, ← inv_mul_cancel x]
      have helper: a * (x⁻¹ * x) * (a * x⁻¹ * y * x * a⁻¹) =
        a * x⁻¹ * (x * a * x⁻¹ * y * x * a⁻¹) := by group
      rw [helper, hy]
      group
    · simp
      group at hy ⊢
      rw [hy]
      group

lemma MulAut.conj_smul_symm {G : Type*} [Group G] (H K : Subgroup G) (c : G)
 (h : conj c • H = K) : ∃ c' : G, conj c' • K = H := ⟨c⁻¹, by simp [← h]⟩

/-
Corollary 1.9.
The centraliser of an element x in L is abelian unless x belongs to the centre of L.
-/
lemma IsMulCommutative_centralizer_of_not_mem_center [IsAlgClosed F] [DecidableEq F](x : SL(2,F))
  (hx : x ∉ center SL(2,F)) : IsMulCommutative (centralizer { x }) := by
  rcases SL2_IsConj_d_or_IsConj_s_or_IsConj_neg_s_of_AlgClosed x with
    (⟨δ, x_IsConj_d⟩ | ⟨σ, x_IsConj_s⟩ | ⟨σ, x_IsConj_neg_s⟩ )
  · obtain ⟨x, centralizer_x_eq⟩ := conjugate_centralizers_of_IsConj (d δ) x x_IsConj_d
    have δ_ne_one : δ ≠ 1 := by
      rintro rfl
      simp at x_IsConj_d
      rw [← x_IsConj_d, center_SL2_eq_Z] at hx
      simp at hx
    have δ_ne_neg_one : δ ≠ -1 := by
      rintro rfl
      simp at x_IsConj_d
      rw [← x_IsConj_d, center_SL2_eq_Z] at hx
      simp at hx
    rw [← centralizer_x_eq, centralizer_d_eq_D _ δ_ne_one δ_ne_neg_one]
    exact map_isMulCommutative _ _
  · obtain ⟨x, centralizer_S_eq⟩ := conjugate_centralizers_of_IsConj (s σ) x x_IsConj_s
    have σ_ne_zero : σ ≠ 0 := by
      rintro rfl
      simp at x_IsConj_s
      rw [← x_IsConj_s, center_SL2_eq_Z] at hx
      simp at hx
    rw [← centralizer_S_eq, centralizer_s_eq_SZ σ_ne_zero]
    exact map_isMulCommutative _ _
  · obtain ⟨x, centralizer_S_eq⟩ := conjugate_centralizers_of_IsConj (-s σ) x x_IsConj_neg_s
    have σ_ne_zero : σ ≠ 0 := by
      rintro rfl
      simp at x_IsConj_neg_s
      rw [← x_IsConj_neg_s, center_SL2_eq_Z] at hx
      simp at hx
    rw [← centralizer_S_eq,  ← centralizer_neg_eq_centralizer, centralizer_s_eq_SZ σ_ne_zero]
    exact map_isMulCommutative _ _

#min_imports
