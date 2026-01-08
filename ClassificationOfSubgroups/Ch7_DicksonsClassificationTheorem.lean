import ClassificationOfSubgroups.Ch4_PGLIsoPSLOverAlgClosedField.ProjectiveGeneralLinearGroup
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_A_MaximalAbelianSubgroup
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

set_option linter.style.longLine true
set_option maxHeartbeats 0

open Matrix Subgroup LinearMap

open scoped MatrixGroups


/- Lemma 3.1 -/
lemma IsPGroup.not_le_normalizer {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)]
  [CharP F p] (G : Subgroup SL(2,F)) (H K : Subgroup G) (hK : IsPGroup p K )
  (H_lt_K : H < K) : ¬ H ≤ Subgroup.normalizer K := by sorry

open MaximalAbelianSubgroup


/- Lemma 3.2 -/
lemma Sylow.not_normal_subgroup_of_G {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)]
  [CharP F p] (G K : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G)
  (hK : K ∈ MaximalAbelianSubgroupsOf G)
  (hQK : map G.subtype (normalizer Q.toSubgroup) = (map G.subtype Q.toSubgroup) ⊔ K) :
  ¬ Normal Q.toSubgroup := by
  sorry

/- Lemma 3.3 -/
def R (F : Type*) [Field F] (p : ℕ) [Fact (Nat.Prime p)] [CharP F p](k : ℕ+) :=
  { x : F | x^p^(k : ℕ) - x = 0 }


instance field_R {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)]
  [CharP F p] {k : ℕ+} : Field (R F p k) := by sorry

/- Lemma 3.4 -/
noncomputable instance Fintype_GL {F : Type*} {n : ℕ} [Field F] [Fintype F] :
    Fintype (GL (Fin n) F) := by
  exact Fintype.ofFinite (GL (Fin n) F)

theorem GL_card {q : ℕ} {F : Type*} [Field F] [Fintype F] (hq : Fintype.card F = q) :
    Fintype.card (GL (Fin 2) F)= (q ^ 2 - 1) * (q ^ 2 - q) := by
  rw [← Nat.card_eq_fintype_card]
  rw [Matrix.card_GL_field]
  simp [hq]

-- Matrix.card_SL_field seems to be missing from mathlib
lemma card_SL_field {𝔽 : Type u} [Field 𝔽] [Fintype 𝔽] (n : ℕ):
  Nat.card (SL (Fin n) 𝔽) = Nat.card (GL (Fin n) 𝔽) / (Fintype.card 𝔽 - 1) := by
  sorry

noncomputable instance Fintype_SL {F : Type*} {n : ℕ} [Field F] [Fintype F] :
    Fintype (SL (Fin n) F) := by
  exact Fintype.ofFinite (SL(n, F))

theorem SL_card {q : ℕ} {F : Type*} [Field F] [Fintype F]
    (hq : Fintype.card F = q) (hqone: q > 1): Fintype.card SL(2, F) = (q ^ 2 - 1) * q := by
  rw [← Nat.card_eq_fintype_card]
  rw [card_SL_field]
  simp [hq]
  rw [GL_card hq]
  have : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, pow_two]
    simp
  rw [this]
  ring_nf
  apply Nat.mul_div_left (q * (q ^ 2 - 1)) (by exact Nat.zero_lt_sub_of_lt hqone)

/- Lemma 3.5. Correspondence theorem -/
#check QuotientGroup.comapMk'OrderIso

def Isomorphic (G H : Type*) [Group G] [Group H] :=
  Nonempty (G ≃* H)

/-
When $s = 1$ and $t = 0$
-/
lemma case_I {F : Type*} {p : ℕ} [Field F] [CharP F p ] (G : Subgroup SL(2,F)) [Finite G]
  (Q : Sylow p G) (Q_ne_G : (⊤ : Subgroup G) ≠ Q.toSubgroup)
  (hQ : IsElementaryAbelian p Q.toSubgroup) [Normal Q.toSubgroup] :
  IsCyclic (G ⧸ Q.toSubgroup) ∧ Nat.Coprime p (Nat.card (G ⧸ Q.toSubgroup)) := by sorry

/-
When $s = t = 1$
-/
lemma case_II {F : Type*} {p : ℕ} [Field F] [CharP F p ]
  (G : Subgroup SL(2,F)) [Finite G] (hG : Nat.Coprime p (Nat.card G)) :
  Isomorphic G SL(2, ZMod 3) ∨ ∃ n, Odd n ∧ Isomorphic G (DihedralGroup (4*n)) := by sorry

/-
When $s = t = 0$
-/
lemma case_III {F : Type*} {p : ℕ} [Field F] [CharP F p ]
  (G : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G) :
  Isomorphic G ((Subgroup.map G.subtype Q.toSubgroup) ⊔ (center SL(2,F)) :) := by sorry

/-
When $s = 0$ and $t = 1$
-/
lemma case_IV {F : Type*} {p : ℕ} [Field F] [CharP F p] (G : Subgroup SL(2,F)) [Finite G] :
 (p = 2 ∧ (∃ n, Odd n ∧ Isomorphic G (DihedralGroup (2*n))))
 ∨
 (p = 3) ∧ Isomorphic G (SL(2, ZMod 3)) := by sorry


-- We first need to define the homomorphism of
-- SL(2, GaloisField p k) into SL(2, GaloisField p (2*k))

open Polynomial

/- Embed GF(p^k) into GF(p^m) where k ∣ m -/
variable {p : ℕ} [hp : Fact (Nat.Prime p)] {n m : ℕ+}


noncomputable
abbrev GaloisField.polynomial (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ+) :
  (ZMod p)[X] := X ^ p ^ n.val - X


lemma GaloisField.polynomial_ne_zero : GaloisField.polynomial p n ≠ 0 := by
  rw [GaloisField.polynomial]
  exact FiniteField.X_pow_card_pow_sub_X_ne_zero (ZMod p) n.ne_zero hp.out.one_lt

lemma GaloisField.splits_of_dvd (hn : n ∣ m) :
    Splits (algebraMap (ZMod p) (GaloisField p m)) (GaloisField.polynomial p n) := by
  have hsk : Splits (algebraMap (ZMod p) (GaloisField p m)) (GaloisField.polynomial p m) :=
    IsSplittingField.splits (GaloisField p m) (GaloisField.polynomial p m)
  have hsk' : Splits (algebraMap (ZMod p) (GaloisField p m)) (X ^ (p ^ m.val - 1) - 1) := by
    refine splits_of_splits_of_dvd _ polynomial_ne_zero hsk ⟨X, ?_⟩
    suffices (X : (ZMod p)[X]) ^ p ^ m.val = X ^ (p ^ m.val - 1 + 1) by
      simpa [GaloisField.polynomial, sub_mul, ← pow_succ]
    rw [tsub_add_cancel_of_le]
    exact Nat.pow_pos (Nat.Prime.pos Fact.out)
  obtain ⟨k, rfl⟩ := hn
  have hd : (p ^ n.val - 1) ∣ (p ^ (n.val * k) - 1) := by
    refine Nat.pow_sub_one_dvd_pow_sub_one p ?_
    apply dvd_mul_right
    -- nat_pow_one_sub_dvd_pow_mul_sub_one p ↑n ↑k
  have hdx : (X : (ZMod p)[X]) ^ (p ^ n.val - 1) - 1 ∣ X ^ (p ^ (n.val * k) - 1) - 1 := by
    let  Y : (ZMod p)[X] := X ^ (p ^ n.val - 1)
    obtain ⟨m, hm⟩ := hd
    simp_rw [hm, pow_mul]
    suffices Y - 1 ∣ Y^m -1 by
      simp [Y] at this
      exact this
    exact sub_one_dvd_pow_sub_one Y m
  have hs' : Splits (algebraMap (ZMod p) (GaloisField p (n * k))) (X ^ (p ^ n.val - 1) - 1) := by
    -- if g | f and f splits then g splits
    refine splits_of_splits_of_dvd _ ?_ hsk' hdx
    refine Monic.ne_zero_of_ne (zero_ne_one' (ZMod p)) ?_
    refine monic_X_pow_sub ?_
    simp [hp.out.one_lt]
  have hs : Splits (algebraMap (ZMod p) (GaloisField p (n * k))) (GaloisField.polynomial p n) := by
    rw [GaloisField.polynomial]
    suffices Splits (algebraMap (ZMod p) (GaloisField p (n * k))) (X * (X ^ (p ^ n.val - 1) - 1)) by
      convert this using 1
      simp only [mul_sub, mul_one, sub_left_inj]
      nth_rewrite 2 [← pow_one X]
      rw [← pow_add, Nat.one_add, Nat.sub_one, Nat.succ_pred]
      exact Ne.symm (NeZero.ne' (p ^ n.val))
    -- product of X * (X^(p^n - 1) - 1) splits if each term in the product splits
    rw [splits_mul_iff]
    exact ⟨splits_X _, hs'⟩
    exact X_ne_zero
    refine Monic.ne_zero_of_ne (zero_ne_one' (ZMod p)) ?_
    refine monic_X_pow_sub ?_
    simp [hp.out.one_lt]
  exact hs


noncomputable
def GaloisField.algHom_of_dvd (hn : n ∣ m) : GaloisField p n →ₐ[ZMod p] GaloisField p m :=
  Polynomial.SplittingField.lift _ (splits_of_dvd hn)


-- (x) The group hSL(2, Fq ), dπ i, where SL(2, Fq ) C hSL(2, Fq ), dπ i.
noncomputable def GaloisField_ringHom (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ+) :=
  (@GaloisField.algHom_of_dvd p _ k (2*k) (dvd_mul_left k 2)).toRingHom


noncomputable def SL2_monoidHom_SL2  {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ+} :
  SL(2, GaloisField p k.val) →* SL(2, GaloisField p (2* k.val)) :=
    Matrix.SpecialLinearGroup.map
      (@GaloisField.algHom_of_dvd p _ k (2*k) (dvd_mul_left k 2)).toRingHom

open SpecialMatrices

noncomputable def SL2_join_d (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ+) (π : (GaloisField p (2* k.val))ˣ ) :=
 (Subgroup.map (@SL2_monoidHom_SL2 p _ k) (⊤ : Subgroup SL(2, GaloisField p k.val)))
  ⊔
  Subgroup.closure { d π }


lemma case_V {F : Type*} {p : ℕ} [Fact (Nat.Prime p)] [Field F] [CharP F p]
  (G : Subgroup SL(2,F)) [Finite G] :
  ∃ k : ℕ+, Isomorphic G SL(2, GaloisField p k.val)
  ∨
  ∃ k : ℕ+, ∃ π : (GaloisField p (2 * k.val))ˣ, Isomorphic G (SL2_join_d p k π)
  ∨
  Isomorphic G SL(2, ZMod 5) := by sorry

inductive Symbols
 | x
 | y

open FreeGroup Symbols PresentedGroup

/-
Relations for the group presentation ⟨x, y | x^n = y^2, y * x * y⁻¹ = x⁻¹ ⟩
-/
def Relations (n : ℕ) : Set (FreeGroup (Symbols)) :=
  {.of x ^ n * (.of y)⁻¹ * (.of y)⁻¹ } ∪
  {.of y * .of x * (.of y)⁻¹ * .of x }

abbrev D (n : ℕ) :=
  PresentedGroup <| Relations n

lemma case_VI {F : Type*} {p : ℕ} [Fact (Nat.Prime p)] [Field F] [CharP F p]
  (G : Subgroup SL(2,F)) [Finite G] :
  ∃ n, Even n ∧ Isomorphic G (D n)
  ∨
  Isomorphic G (GL (Fin 2) (ZMod 5))
  ∨
  Isomorphic G SL(2, ZMod 5) := by sorry


 -- (v) Ŝ₄ , the representation group of S4 in which the transpositions correspond to
-- the elements of order 4.

instance five_prime : Fact (Nat.Prime 5) := { out := by decide }

/- Theorem 3.6 -/
theorem dicksons_classification_theorem_class_I {F : Type*} [Field F] [IsAlgClosed F]
  {p : ℕ} [CharP F p] (hp : Prime p) (hp' : p = 0 ∨ Nat.Coprime (Nat.card G) p)
  (G : Subgroup (SL(2,F)))  [Finite G] :
  IsCyclic G ∨
  Isomorphic G (DihedralGroup n)
  ∨
  Isomorphic G SL(2, ZMod 3)
  ∨
  Isomorphic G SL(2, ZMod 5)
  ∨
  Isomorphic G (GL (Fin 2) (ZMod 3))
  := by sorry

-- Ŝ₄ is isomorphic to GL₂(F₃)

lemma card_GaloisField_dvd_card_GaloisField (p : ℕ) [Fact (Nat.Prime p)] {m n : ℕ+}
  (m_dvd_n : m ∣ n) :  Nat.card (GaloisField p m.val) ∣ Nat.card (GaloisField p n.val) := by
  rw [GaloisField.card p m m.ne_zero, GaloisField.card p n n.ne_zero]
  apply pow_dvd_pow
  suffices m.val ∣ n.val by exact Nat.le_of_dvd n.prop this
  exact PNat.dvd_iff.mp m_dvd_n

theorem dicksons_classification_theorem_class_II {F : Type*} [Field F] [IsAlgClosed F]{p : ℕ}
  [Fact (Nat.Prime p)] [CharP F p] (G : Subgroup (SL(2,F))) [Finite G] (hp : p ∣ Nat.card G)  :
  ∃ Q : Subgroup SL(2,F), IsElementaryAbelian p Q ∧ Normal Q ∧ Isomorphic G Q
  ∨
  (p = 2 ∧ ∃ n : ℕ, Odd n ∧ Isomorphic G (DihedralGroup n))
  ∨
  Isomorphic G SL(2, ZMod 5)
  ∨
  ∃ k : ℕ+, Isomorphic G SL(2, GaloisField p k)
  ∨
  ∃ k : ℕ+, ∃ x : GaloisField p (2* k), orderOf x^2 = p^(k : ℕ) ∧
    ∃ φ : G ≃* SL(2, GaloisField p k), True
  := by sorry



#check ZMod

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

open Matrix LinearMap Subgroup

open scoped MatrixGroups


/-- A projective general linear group is the quotient of a special linear group by its center. -/
abbrev ProjectiveGeneralLinearGroup' : Type _ :=
    GL n R ⧸ center (GL n R)



theorem FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod {p : ℕ} [Fact (Nat.Prime p)] (𝕂 : Type*)
  [Field 𝕂] [CharP 𝕂 p] [Finite 𝕂]
  (G : Subgroup (PGL (Fin 2) (AlgebraicClosure (ZMod p)))) [hG : Finite G] :
  IsCyclic G
  ∨
  ∃ n, Isomorphic G (DihedralGroup n)
  ∨
  Isomorphic G (alternatingGroup (Fin 4))
  ∨
  Isomorphic G (Equiv.Perm (Fin 5))
  ∨
  Isomorphic G (alternatingGroup (Fin 5))
  ∨
  Isomorphic G (PSL (Fin 2) (𝕂))
  ∨
  Isomorphic G (PGL (Fin 2) (𝕂)) := by
    sorry

#min_imports
