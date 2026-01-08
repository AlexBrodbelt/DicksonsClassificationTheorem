import ClassificationOfSubgroups.Ch5_PropertiesOfSLOverAlgClosedField.S2_SpecialSubgroups
import Mathlib.Algebra.GroupWithZero.Conj
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleRing.Principal

set_option autoImplicit false
set_option linter.style.longLine true

open Matrix MatrixGroups Subgroup Pointwise

open SpecialMatrices SpecialSubgroups MatrixShapes

universe u

variable
  {F : Type u} [Field F]
  (n : Type u) [Fintype n]
  {R : Type u} [CommRing R]
  {G : Type u} [Group G]

@[simp]
lemma SpecialLinearGroup.coe_coe {n : ℕ} {S : SL(n, F)} :
  ((S : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = (S : Matrix (Fin n) (Fin n) F) :=  by rfl

@[simp]
lemma GeneralLinearGroup.coe_mk' {R : Type*} [CommRing R] {M : Matrix (Fin 2) (Fin 2) R}
  (hM : Invertible (det M) ) : (GeneralLinearGroup.mk' M hM) = M := by rfl

@[simp]
lemma GeneralLinearGroup.coe_mk'_inv {R : Type*} [CommRing R] {M : Matrix (Fin 2) (Fin 2) R}
  {hM : Invertible (det M) } : (GeneralLinearGroup.mk' M hM)⁻¹ = M⁻¹ := by simp only [coe_units_inv,
    coe_mk']

lemma GL_eq_iff_Matrix_eq {n R : Type* } [Fintype n] [DecidableEq n] [CommRing R] {A B : GL n R}
  (h : (A : Matrix n n R) = (B : Matrix n n R) ) : A = B := by
  apply Matrix.GeneralLinearGroup.ext
  rw [← Matrix.ext_iff] at h
  exact h

lemma det_GL_coe_is_unit {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] (G : GL n R) :
  IsUnit (det (G : Matrix n n R)) := by
  have det_G_is_unit : IsUnit (GeneralLinearGroup.det G) := Group.isUnit (GeneralLinearGroup.det G)
  exact ⟨det_G_is_unit.unit, by simp only [IsUnit.unit_spec, GeneralLinearGroup.val_det_apply]⟩

open Polynomial

lemma associated_of_dvd_mul_irreducibles {k : Type*} [Field k] {q p₁ p₂: k[X]}
  (hp₁ : Irreducible p₁) (hp₂ : Irreducible p₂) (hpq : q ∣ p₁ * p₂) :
  (Associated q 1) ∨ Associated q p₁ ∨ Associated q p₂ ∨ Associated q (p₁ * p₂) := by
  rw [dvd_mul] at hpq
  obtain ⟨d₁, d₂, hd₁, hd₂, q_eq⟩ := hpq
  rw [irreducible_iff] at hp₁ hp₂
  rcases hp₁ with ⟨-, hp₁⟩
  rcases hp₂ with ⟨-, hp₂⟩
  rcases hd₁ with ⟨k₁, hk₁⟩
  rcases hd₂ with ⟨k₂, hk₂⟩
  specialize hp₁ hk₁
  specialize hp₂ hk₂
  rcases hp₁ with (h₁ | h₁)
  · rcases hp₂ with (h₂ | h₂)
    · left
      rw [associated_one_iff_isUnit, q_eq]
      exact (IsUnit.mul h₁ h₂)
    · right; right; left
      rw [q_eq, hk₂, associated_mul_isUnit_right_iff h₂, mul_comm,
          associated_mul_isUnit_left_iff h₁]
  · rcases hp₂ with (h₂ | h₂)
    · right; left
      rw [q_eq, hk₁, associated_mul_isUnit_left_iff h₂, associated_mul_isUnit_right_iff h₁]
    · right; right; right
      rw [q_eq, hk₁, hk₂, mul_assoc, ← mul_assoc k₁, mul_comm k₁, mul_assoc, ← mul_assoc,
      associated_mul_isUnit_right_iff (IsUnit.mul h₁ h₂)]


lemma minpoly_eq_X_sub_C_implies_matrix_is_diagonal { n R : Type*} [Fintype n] [DecidableEq n]
     [ CommRing R ] [NoZeroDivisors R] {M : Matrix n n R} {a : R}
    (hM : minpoly R M = (X - C a)) : M = diagonal (fun _ ↦ a) := by
    -- The minimal polynomial evaluated at M must be 0
    have M_eq_diagonal : aeval (M : Matrix n n R) (minpoly R M) = 0 := minpoly.aeval _ _
    simp [hM, algebraMap, sub_eq_zero] at M_eq_diagonal
    -- This shows M is diagonal
    exact M_eq_diagonal


/-
The product of the top left entry and the bottom right entry equals one
if the bottom left entry is zero.
-/
lemma det_eq_mul_diag_of_upper_triangular (S : SL(2,F)) (hγ : IsUpperTriangular S.val) :
  S 0 0 * S 1 1 = 1 := by
  rw [IsUpperTriangular] at hγ
  have det_eq_one : det (S.val) = 1 := by simp
  simp only [det_fin_two, hγ, mul_zero, sub_zero] at det_eq_one
  exact det_eq_one

/-
The product of the top left entry and the bottom right entry equals one
if the top right entry is zero.
-/
lemma det_eq_mul_diag_of_lower_triangular (S : SL(2,F)) (hβ : IsLowerTriangular S.val) :
  S 0 0 * S 1 1 = 1 := by
  rw [IsLowerTriangular] at hβ
  have det_eq_one : det (S.val) = 1 := by simp
  simp only [det_fin_two, hβ, zero_mul, sub_zero] at det_eq_one
  exact det_eq_one

/-
A 2x2 matrix of the special linear group is diagonal, and can be written as `d δ` for some `δ ∈ Fˣ`
if and only if the bottom left and top right entries are zero.
-/
lemma SpecialLinearGroup.fin_two_diagonal_iff (x : SL(2,F)) :
  x 0 1 = 0 ∧ x 1 0 = 0 ↔ ∃ δ : Fˣ, d δ = x := by
  constructor
  · rintro ⟨hβ, hγ⟩
    rcases get_entries x with ⟨α, β, γ, δ, hα, -, -, hδ, -⟩
    have det_eq_mul_diagonal := det_eq_mul_diag_of_lower_triangular x hβ
    have α_is_unit : IsUnit α := isUnit_of_mul_eq_one α δ (hα ▸ hδ ▸ det_eq_mul_diagonal)
    have δ_is_unit : IsUnit δ := isUnit_of_mul_eq_one_right α δ (hα ▸ hδ ▸ det_eq_mul_diagonal)
    have δ_ne_zero : x.1 1 1 ≠ 0 := by exact IsUnit.ne_zero <| hδ.symm ▸ δ_is_unit
    use α_is_unit.unit
    rw [mul_eq_one_iff_eq_inv₀ δ_ne_zero] at det_eq_mul_diagonal
    ext <;> simp [d, hα, hβ, hγ, det_eq_mul_diagonal]
  · rintro ⟨δ, h⟩
    rw [SpecialLinearGroup.fin_two_ext_iff] at h
    rcases h with ⟨-, h₁, h₂, -⟩
    split_ands <;> simp [d, ← h₁, ← h₂]

/-
A 2x2 matrix of the special linear group is antidiagonal, and can be written as
`d δ * w` for some `δ ∈ Fˣ` if and only if the top left and bottom right entries are zero.
-/
lemma SpecialLinearGroup.fin_two_antidiagonal_iff (x : SL(2,F)) :
  x 0 0 = 0 ∧ x 1 1 = 0 ↔ ∃ δ : Fˣ, (d δ) * w = x := by
  constructor
  · rintro ⟨hα, hδ⟩
    have det_eq_one : det (x : Matrix (Fin 2) (Fin 2) F) = 1 := by rw [SpecialLinearGroup.det_coe]
    rw [det_fin_two, hα, hδ, zero_mul, zero_sub, ← neg_mul, neg_mul_comm] at det_eq_one
    have β_is_unit : IsUnit (x 0 1) := by exact isUnit_of_mul_eq_one (x 0 1) (-x 1 0) det_eq_one
    rw [← neg_mul_comm] at det_eq_one
    have neg_β_inv_eq : -(x 0 1)⁻¹ = x 1 0 := by
      rw [neg_inv]
      refine inv_eq_of_mul_eq_one_right det_eq_one
    use β_is_unit.unit
    ext <;>
    simp [d, w, hα, hδ, neg_β_inv_eq]
  · rintro ⟨δ, rfl⟩
    split_ands  <;>
    simp [d, w]

/-
A matrix `x` of `SL(2,F)` is a shear matrix if and only if either
`x = s σ` or `x = -s σ` for some `σ ∈ F`.
-/
lemma SpecialLinearGroup.fin_two_shear_iff (x : SL(2,F)) :
  x 0 0 = x 1 1 ∧ x 0 1 = 0 ↔ (∃ σ, s σ = x) ∨ ∃ σ, -s σ = x := by
  constructor
  · rintro ⟨α_eq_δ, β_eq_zero⟩
    have α_eq_one_or_neg_one := α_eq_δ.symm ▸ det_eq_mul_diag_of_lower_triangular x β_eq_zero
    rw [← sq, sq_eq_one_iff] at α_eq_one_or_neg_one
    rcases α_eq_one_or_neg_one with (α_eq_one | α_eq_neg_one)
    · left
      use x.1 1 0
      ext <;> simp [s, α_eq_one, β_eq_zero, α_eq_δ ▸ α_eq_one]
    · right
      use - x.1 1 0
      ext <;> simp [s, α_eq_neg_one, β_eq_zero, α_eq_δ ▸ α_eq_neg_one]
  · rintro (⟨σ,h⟩ | ⟨σ, h⟩)
    repeat' rw [SpecialLinearGroup.fin_two_ext_iff] at h; rcases h with ⟨hα, hβ, -, hδ⟩
    · simp [← hα, ← hδ, ← hβ, s]
    · simp [← hα, ← hδ, ← hβ, s]

@[simp]
lemma Matrix.special_inv_eq {x : F} :
  !![1, 0; x, 1]⁻¹ = !![1, 0; - x, 1] := by simp [inv_def]

lemma exists_root_of_special_poly [IsAlgClosed F] (a b c d : F) (hb : b ≠ 0):
  ∃ x : F, -b * x * x + (a - d) * x + c = 0 := by
  let P := C (-b) * X^2 + C (a - d) * X + C c
  have deg_P_eq_two : degree P = 2 := by
    dsimp [P]
    rw [Polynomial.degree_quadratic]
    simp [hb]
  have exists_root_of_P := by apply IsAlgClosed.exists_root P (by simp [deg_P_eq_two])
  obtain ⟨x, hx⟩ := exists_root_of_P
  use x
  simp [P] at hx
  ring_nf at hx ⊢
  exact hx

lemma Matrix.conj_s_eq {x : F} {a b c d : F} :
  s x * !![a, b; c, d] * s (-x) =
  !![-b * x + a, b; (-b) * x * x + (a -d) * x + c, b*x + d] := by
  simp [s]
  ring_nf
  trivial

def SpecialLinearGroup.mk' {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (h : det M = 1) : SL(n, F) :=
  ⟨M, h⟩

-- Note: I do not use IsConj as the the matrix which acts by conjugation has determinant 1
theorem isTriangularizable_of_algClosed [DecidableEq F] [IsAlgClosed F]
  (M : Matrix (Fin 2) (Fin 2) F) :
  ∃ (C : SL(2,F)), IsUpperTriangular (C * M * C⁻¹ : Matrix (Fin 2) (Fin 2) F) := by
  let α := M 0 0
  let β := M 0 1
  let γ := M 1 0
  let δ := M 1 1
  have M_coe_eq : M = !![α, β; γ, δ] := by ext <;> rfl
  -- If β ≠ 0 then we solve the quadratic to force the bottom left entry to be 0
  by_cases hβ : β ≠ 0
  · obtain ⟨σ, hσ⟩ := exists_root_of_special_poly α β γ δ hβ
    use s σ
    simp [M_coe_eq, s]
    ring_nf at hσ ⊢
    exact hσ
  simp at hβ
  · use w
    rw [upper_triangular_iff]
    simp [M_coe_eq, w, hβ]

/-
A 2x2 upper triangular matrix is conjugate to a diagonal matrix if `a ≠ d`
-/
lemma upper_triangular_isConj_diagonal_of_nonzero_det  [DecidableEq F]
  {a b d : F} (had : a - d ≠ 0) : ∃ C : SL(2,F), C * !![a, b; 0, d] * C⁻¹ = !![a, 0; 0, d] := by
  use ⟨!![1, b / (a - d); 0, 1], by simp⟩
  simp
  repeat'
  field_simp
  ring_nf

/-
A 2x2 upper triangular matrix is conjugate to a jordan block if `b ≠ 0`
-/
lemma upper_triangular_isConj_jordan {a b : F} (hb : b ≠ 0) :
  IsConj !![a, b; 0, a] !![a, 1; 0, a] := by
  use GeneralLinearGroup.mk' !![1 / b, 0; 0, 1]
    (by simp; apply invertibleOfNonzero <| inv_ne_zero hb)
  ext <;> simp <;> field_simp

/-
A 2x2 lower triangular matrix is conjugate to an upper triangular matrix
-/
lemma lower_triangular_isConj_upper_triangular {a b : F} :
  ∃ C : SL(2,F), C * !![a, 0; -b, a] * C⁻¹ = !![a, b; 0, a] := by
  use w
  simp [w]

/-
If M is semiconjugate to N by a unit in a monoid if and only if M is conjugate to N by a unit
-/
lemma mul_left_eq_mul_right_iff {α : Type*} [Monoid α]{N M : α}(c : αˣ) :
  ((c : α) * M = N * (c : α)) ↔ M = c⁻¹ * N * c := by
  constructor
  · intro h
    rw [mul_assoc, ← h, ← mul_assoc, Units.inv_mul, one_mul]
  · intro h
    rw [h, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]

-- Note: [isConj_iff] can be strengthened for monoids
lemma det_eq_det_IsConj {n : ℕ} {M N : Matrix (Fin n) (Fin n) R} (h : IsConj N M) :
  det N = det M := by
  rw [isConj_comm, IsConj] at h
  obtain ⟨c, hc⟩ := h
  rw [SemiconjBy, mul_left_eq_mul_right_iff] at hc
  rw [hc, Matrix.coe_units_inv, det_conj' c.isUnit N]

/-
If the underlying matrices are the same then the matrices
as subtypes of the special linear group are also the same
-/
lemma SpecialLinearGroup.eq_of {S L : SL(2,F) } (h : (S : Matrix (Fin 2) (Fin 2) F) = L) :
  S = L := by ext <;> simp [h]

lemma IsConj_coe {M N : Matrix (Fin 2) (Fin 2) F} (hM : det M = 1) (hN : det N = 1)
  (h : ∃ C : SL(2, F), C * M * C⁻¹ = N) : ∃ C : SL(2,F), C * ⟨M, hM⟩ * C⁻¹ = ⟨N, hN⟩ := by
  obtain ⟨C, hC⟩ := h
  use C
  apply SpecialLinearGroup.eq_of
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, hC]


/-
Lemma 1.5.
Each element of SL(2,F) is conjugate to either
`D δ` for some `δ ∈ Fˣ`, or to  `± s σ` for some `σ ∈ F` if
`F` is algebraically closed.
-/
theorem SL2_IsConj_d_or_IsConj_s_or_IsConj_neg_s_of_AlgClosed [DecidableEq F] [IsAlgClosed F]
  (S : SL(2, F)) :
  (∃ δ : Fˣ, IsConj (d δ) S)
  ∨
  (∃ σ : F, IsConj (s σ) S)
  ∨
  (∃ σ : F, IsConj (- s σ) S) := by
  -- S is conjugate to an upper triangular matrix
  have S_IsConj_upper_triangular :=
    isTriangularizable_of_algClosed (S : Matrix (Fin 2) (Fin 2) F)
  have det_coe_S_eq_one : det (S : Matrix (Fin 2) (Fin 2) F ) = 1 := by simp
  obtain ⟨C, h⟩ := S_IsConj_upper_triangular
  rw [upper_triangular_iff] at h
  obtain ⟨a, b, d, h⟩ := h
  -- Because !![a, b; 0, d] is conjugate to S it also has determinant 1
  have det_eq_one : det !![a, b; 0, d] = 1 := by
    rw [← det_coe_S_eq_one, h]
    simp only [det_mul, SpecialLinearGroup.det_coe, mul_one]
  have had := det_eq_one
  -- The determinant being equal to 1 implies a * d = 1
  simp at had
  -- so the inverse of a is equal to d
  have d_eq_inv_a : d = a⁻¹ := Eq.symm (DivisionMonoid.inv_eq_of_mul a d had)
  -- Therefore a is a unit
  have a_is_unit : IsUnit a := by exact isUnit_of_mul_eq_one a d had
  -- Furthermore, a is nonzero
  have a_ne_zero : a ≠ 0 := by exact left_ne_zero_of_mul_eq_one had
  have det_eq_one' : det !![a, 0; 0, d] = 1 := by simp [d_eq_inv_a]; rw [mul_inv_cancel₀ a_ne_zero]
  obtain rfl | had' := eq_or_ne a d
  · right
    simp [← sq] at det_eq_one'
    rcases det_eq_one' with (a_eq_one | a_eq_neg_one)
    · left
      rw [a_eq_one] at h
      have det_eq_one'' : det !![1, b; 0, 1] = 1 := by norm_num
      use -b
      have isConj₁ : ∃ C : SL(2,F), C * (s (-b)) * C⁻¹ = ⟨!![1, b; 0, 1], det_eq_one''⟩ := by
        apply IsConj_coe
        exact lower_triangular_isConj_upper_triangular
      have isConj₂ : ∃ C : SL(2,F), C * S * C⁻¹ = ⟨!![1, b; 0, 1], det_eq_one''⟩ := by
        use C
        apply SpecialLinearGroup.eq_of
        simp only [SpecialLinearGroup.coe_mul, h]
      rw [← isConj_iff] at isConj₁ isConj₂
      apply IsConj.trans isConj₁ isConj₂.symm
    · right
      rw [a_eq_neg_one] at h
      have det_eq_one'' : det !![-1, b; 0, -1] = 1 := by norm_num
      have S_eq : - s b = !![-1, 0; -b, -1] := by simp [s]
      use b
      have isConj₁ : ∃ C : SL(2,F), C * (-s b) * C⁻¹ = ⟨!![-1, b; 0, -1], det_eq_one''⟩ := by
        apply IsConj_coe
        simp only [S_eq]
        exact lower_triangular_isConj_upper_triangular
      have isConj₂ : ∃ C : SL(2,F), C * S * C⁻¹ = ⟨!![-1, b; 0, -1], det_eq_one''⟩ := by
        use C
        apply SpecialLinearGroup.eq_of
        simp only [SpecialLinearGroup.coe_mul, h]
      rw [← isConj_iff] at isConj₁ isConj₂
      -- conjugation is transitive
      apply IsConj.trans isConj₁ isConj₂.symm
  · left
    use a_is_unit.unit
    have isConj₁ : ∃ C : SL(2,F), C * S * C⁻¹ =  ⟨!![a, b ; 0, d], det_eq_one⟩ := by
      use C
      apply SpecialLinearGroup.eq_of
      simp only [SpecialLinearGroup.coe_mul]
      rw [h]
    have isConj₂ :
      ∃ C : SL(2,F), C * ⟨!![a, b; 0,d], det_eq_one⟩ * C⁻¹ = ⟨!![a,0;0,d], det_eq_one'⟩ := by
      apply IsConj_coe
      refine upper_triangular_isConj_diagonal_of_nonzero_det ?a_ne_d
      intro h
      rw [sub_eq_zero] at h
      contradiction
    simp_rw [← isConj_iff, d_eq_inv_a] at isConj₁ isConj₂
    simp only [SpecialMatrices.d, IsUnit.unit_spec]
    -- conjugation is transitive
    apply IsConj.trans isConj₂.symm isConj₁.symm


#min_imports
