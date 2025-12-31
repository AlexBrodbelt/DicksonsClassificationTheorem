import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_A_MaximalAbelianSubgroup
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_B_MaximalAbelianSubgroup

import Mathlib

set_option linter.style.longLine true
set_option autoImplicit false
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0


universe u


open Matrix MatrixGroups Subgroup MulAut MaximalAbelianSubgroup Pointwise SpecialSubgroups


/-- The non-central part of a subgroup as a set. -/
def Subgroup.noncenter {G : Type*} [Group G] (H : Subgroup G) : Set G :=
  H.carrier \ center G


theorem Subgroup.mem_noncenter {G : Type*} [Group G] {H : Subgroup G} {x : G} :
  x ∈ H.noncenter ↔ x ∈ H ∧ x ∉ center G := by
  simp [Subgroup.noncenter, Set.mem_diff, SetLike.mem_coe]

/-
Definition. The set $\mathcal{C}(A) = Cl(A) = \{x A x^{-1} \; | \; x ∈ G \}$
is called the conjugacy class of $A \in \mathcal{M}$.
-/
def ConjClassOf {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) :=
  { conj x • A.val | x ∈ G }

/- let M∗ be the set of all Aᵢ* and let Cᵢ* be the conjugacy class of Aᵢ* .-/
def noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F] (G : Subgroup SL(2,F)) :=
  { noncenter (K : Subgroup SL(2,F)) | K ∈ MaximalAbelianSubgroupsOf G }

def noncenter_ConjClassOf {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : noncenter_MaximalAbelianSubgroupsOf G)  :=
  { conj x • A.val | x ∈ G }


noncomputable def card_noncenter_ConjClassOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) : noncenter_MaximalAbelianSubgroupsOf G → ℕ :=
  fun A => Nat.card (noncenter_ConjClassOf G A)

section noncenter_MaximalAbelianSubgroupsOf


lemma noncenter_mem_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) : A.val.noncenter ∈ noncenter_MaximalAbelianSubgroupsOf G := by
  use A, A.prop

#check noncenter_MaximalAbelianSubgroupsOf

/-
Define the equivalence relation $\sim$ on $\mathcal{M}^*$ by
$A_i \sim A_j$ if and only if $A_i = x A_j x^{-1}$ for some $x \in G$.
 -/
instance lift_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F] (G : Subgroup SL(2,F)) :
  Setoid (noncenter_MaximalAbelianSubgroupsOf G) where
  r A B := ∃ x ∈ G, conj x • A.val = B.val
  iseqv := {
    refl := by rintro A
               exact ⟨1, Subgroup.one_mem G, by simp⟩
    symm := by
      rintro A B ⟨x, x_in_G, hx⟩
      use x⁻¹
      simp at hx ⊢
      rw [inv_smul_eq_iff]
      exact ⟨x_in_G, hx.symm⟩
    trans := by
      rintro A B C ⟨x, x_in_G,  hx⟩ ⟨y, y_in_G, hy⟩
      use y * x
      rw [← hy, ← hx, smul_smul, MonoidHom.map_mul]
      exact ⟨Subgroup.mul_mem G y_in_G x_in_G, rfl⟩
  }

def Partition_lift_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F] (G : Subgroup SL(2,F)) :=
  (lift_noncenter_MaximalAbelianSubgroupsOf G).classes

#check Partition_lift_noncenter_MaximalAbelianSubgroupsOf

#check Setoid.IsPartition.sUnion_eq_univ

#check sUnion_memPartition

#check Set
/-
Define $C (A)^* = \bicup_{x \in G} x A^*  x^{-1}$
-/
def union_conj_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :
  noncenter_MaximalAbelianSubgroupsOf G → Set SL(2,F) :=
    fun A => ⋃ x ∈ G, conj x • A.val


lemma union_conj_noncenter_eq_of_related {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G] :
 (∀ (A B : (noncenter_MaximalAbelianSubgroupsOf G)),
  A ≈ B → union_conj_noncenter_MaximalAbelianSubgroupsOf G A =
     union_conj_noncenter_MaximalAbelianSubgroupsOf G B) := by
  intro A B ArB
  obtain ⟨r, r_in_G, hr⟩ := ArB
  simp [union_conj_noncenter_MaximalAbelianSubgroupsOf]
  ext y
  constructor
  <;> intro hy
  <;> simp only [Set.mem_iUnion, exists_prop] at hy ⊢
  <;> obtain ⟨g, g_in_G, y_in_conj⟩ := hy
  · simp only [← hr]
    use g * r⁻¹
    split_ands
    · exact Subgroup.mul_mem G g_in_G (inv_mem r_in_G)
    · simp only [_root_.map_mul, map_inv, ← MulAction.mul_smul, inv_mul_cancel_right]
      exact y_in_conj
  · simp only [←  hr] at y_in_conj
    use g * r
    split_ands
    · exact Subgroup.mul_mem G g_in_G r_in_G
    rw [_root_.map_mul, MulAction.mul_smul]
    exact y_in_conj

def lift_union_conj_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :=
  @Quotient.lift _ _ (s := lift_noncenter_MaximalAbelianSubgroupsOf G)
    (f := union_conj_noncenter_MaximalAbelianSubgroupsOf G) (union_conj_noncenter_eq_of_related G)




end noncenter_MaximalAbelianSubgroupsOf

section MaximalAbelianSubgroupsOf
/-
We define the equivalence relation on the set of Maximal Abelian Subgroups of `G`, a finite
group of `SL(2,F)`
-/
instance lift_MaximalAbelianSubgroupsOf {F : Type*} [Field F] (G : Subgroup SL(2,F)) :
  Setoid (MaximalAbelianSubgroupsOf G) where
  r A B := ∃ x ∈ G, conj x • A.val = B.val
  iseqv := {
    refl A := ⟨1, Subgroup.one_mem _ , by simp⟩
    symm := by
      rintro ⟨A, hA⟩  ⟨B, hB⟩ ⟨x, hx⟩
      use x⁻¹
      simp at hx ⊢
      rw [inv_smul_eq_iff]
      exact ⟨hx.left, hx.right.symm⟩
    trans := by
      rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨C, hC⟩ ⟨x, hx⟩ ⟨y, hy⟩
      use y * x
      split_ands
      apply Subgroup.mul_mem G hy.left hx.left
      rw [← hy.right, ← hx.right, smul_smul, MonoidHom.map_mul]
  }

-- noncomputable def card_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
--   (G : Subgroup SL(2,F)) [Finite G] : MaximalAbelianSubgroupsOf G → ℕ :=
--   fun A => Nat.card ((A.val.carrier \ (center SL(2,F)).carrier) :)

-- /-
-- The function which computes the cardinality of the noncentral part of a maximal abelian subgroup,
-- respects the equivalence relation on the setoid of maximal abelian subgroups of `G`.
-- -/
-- lemma card_eq_of_related_noncenter_subgroups {F : Type*} [Field F] (G : Subgroup SL(2,F))
--   (center_le_G : center SL(2,F) ≤ G)[ hG : Finite G] :
--   ∀ (A B : (MaximalAbelianSubgroupsOf G)),
--     A ≈ B → card_noncenter_MaximalAbelianSubgroupsOf G A =
--       card_noncenter_MaximalAbelianSubgroupsOf G B := by
--   rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨x, x_in_G, rfl⟩
--   simp only [card_noncenter_MaximalAbelianSubgroupsOf, center_toSubmonoid,
--     Submonoid.center_toSubsemigroup, pointwise_smul_toSubmonoid, Set.Nat.card_coe_set_eq]
--   let center_finite : Finite (center SL(2, F)) := by
--     rw [center_SL2_eq_Z]
--     infer_instance
--   have center_le_A : (Subsemigroup.center SL(2, F)).carrier ⊆ A.carrier :=
--     @MaximalAbelianSubgroup.center_le SL(2,F) _ G A hA center_le_G
--   let center_coe_finite : Finite (Subsemigroup.center SL(2, F)).carrier := center_finite
--   have center_le_conj_A :
--     (Subsemigroup.center SL(2, F)).carrier ⊆ (conj x • A.toSubmonoid).carrier := by
--     intro z hz
--     rw [Submonoid.mem_carrier, Submonoid.mem_pointwise_smul_iff_inv_smul_mem]
--     have hz' := hz
--     rw [Subsemigroup.mem_carrier, Subsemigroup.mem_center_iff] at hz'
--     simp only [MulAut.smul_def, conj_inv_apply, mem_toSubmonoid]
--     rw [hz' x⁻¹]
--     group
--     exact center_le_A hz
--   rw [Set.ncard_diff center_le_A, Set.ncard_diff center_le_conj_A]
--   have key : (conj x • A.toSubmonoid).carrier.ncard = A.carrier.ncard := by
--     symm
--     refine Set.ncard_congr (fun a ha ↦ x * a * x⁻¹) ?closure ?injective ?surjective
--     case closure =>
--       intro a ha
--       simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
--         Submonoid.mem_pointwise_smul_iff_inv_smul_mem,
--         smul_mul', MulAut.smul_def, conj_inv_apply, inv_mul_cancel, one_mul, smul_inv',
--         mem_toSubmonoid]
--       group
--       exact ha
--     case injective =>
--       intro a b ha hb hab
--       simp only [mul_left_inj, mul_right_inj] at hab
--       exact hab
--     case surjective =>
--       rintro b ⟨y, hy, rfl⟩
--       use y, hy
--       congr
--   rw [key]

noncomputable def card_noncenter {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] : noncenter_MaximalAbelianSubgroupsOf G → ℕ :=
  fun A => Nat.card A.val

/-
The function which computes the cardinality of the noncentral part of a maximal abelian subgroup,
respects the equivalence relation on the setoid of maximal abelian subgroups of `G`.
-/
lemma card_noncenter_eq_of_related {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] :
  ∀ (A B : (noncenter_MaximalAbelianSubgroupsOf G)),
    A ≈ B → card_noncenter G A =
      card_noncenter G B := by
  rintro ⟨A_star, A, A_in_MaxAbSub, hA⟩ ⟨B_star, B, B_in_MaxAbSub, hB⟩ ⟨x, x_in_G, rfl⟩
  simp only [card_noncenter, Nat.card_coe_set_eq]
  let center_finite : Finite (center SL(2, F)) := by
    rw [center_SL2_eq_Z]
    infer_instance
  simp

/-
We lift the function which computes the cardinality of the noncentral part of a maximal subgroup
-/
noncomputable def lift_card_noncenter {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [Finite G] := @Quotient.lift _ _ (s := lift_noncenter_MaximalAbelianSubgroupsOf G)
    (f := card_noncenter G)
    (card_noncenter_eq_of_related G)


def toConjClassOfSet {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] : noncenter_MaximalAbelianSubgroupsOf G → Set (Set SL(2,F)) :=
  fun A => noncenter_ConjClassOf G A

lemma conj_noncenter_eq_noncenter_conj {F : Type*} [Field F] {G :Subgroup SL(2,F)}
  (A : MaximalAbelianSubgroupsOf G) (x : SL(2,F)) :
  (conj x • A.val).noncenter = conj x • A.val.noncenter := by
  ext y
  constructor
  · rintro ⟨⟨a, a_in_A, rfl⟩, conj_a_not_in_center⟩
    simp at conj_a_not_in_center ⊢
    simp only [Set.mem_smul_set_iff_inv_smul_mem, smul_mul', MulAut.smul_def, conj_inv_apply,
      inv_mul_cancel, one_mul, smul_inv']
    group
    have a_not_in_center : a ∉ center SL(2,F) := by
      intro a_in_center
      rw [mem_center_iff] at a_in_center
      have contr : x * a * x⁻¹ ∈ center SL(2,F) := by
        rw [mem_center_iff]
        rw [a_in_center x]
        group
        exact a_in_center
      contradiction
    exact ⟨a_in_A, a_not_in_center⟩
  · rintro ⟨a, ⟨a_in_A, a_not_in_center⟩, rfl⟩
    simp
    rw [noncenter, Set.mem_diff]
    split_ands
    · simp only [pointwise_smul_toSubmonoid, Subsemigroup.mem_carrier,
      Submonoid.mem_toSubsemigroup, Submonoid.mem_pointwise_smul_iff_inv_smul_mem, smul_mul',
      MulAut.smul_def, conj_inv_apply, inv_mul_cancel, one_mul, smul_inv', mem_toSubmonoid]
      group
      exact a_in_A
    · intro conj_in_center
      rw [SetLike.mem_coe, mem_center_iff] at conj_in_center
      have a_in_center : a ∈ center SL(2,F) := by
        rw [mem_center_iff]
        intro g
        specialize conj_in_center (x * g * x⁻¹)
        group at conj_in_center
        rw [mul_left_inj, mul_assoc, mul_assoc, mul_right_inj] at conj_in_center
        exact conj_in_center
      contradiction

lemma toConjClassOfSet_eq_of_related_noncenter_subgroups {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :
  (∀ (A B : noncenter_MaximalAbelianSubgroupsOf G),
    A ≈ B → toConjClassOfSet G A = toConjClassOfSet G B) := by
  intro A B ArB
  obtain ⟨x, x_in_G, hx⟩ := ArB
  simp [toConjClassOfSet, noncenter_ConjClassOf]
  ext s
  constructor
  · rintro ⟨y, y_in_G, rfl⟩
    simp only [← hx, Set.mem_setOf_eq]
    use y * x⁻¹
    rw [MonoidHom.map_mul, MulAction.mul_smul, smul_left_cancel_iff, map_inv, inv_smul_eq_iff]
    exact ⟨Subgroup.mul_mem G y_in_G (inv_mem x_in_G), rfl⟩
  · rintro ⟨y, y_in_G, rfl⟩
    simp only [← hx, Set.mem_setOf_eq]
    use y * x
    rw [MonoidHom.map_mul, MulAction.mul_smul, smul_left_cancel_iff]
    exact ⟨Subgroup.mul_mem G y_in_G x_in_G, rfl⟩


def lift_ConjClassOfSet {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G] :=
  @Quotient.lift _ _ (s := lift_noncenter_MaximalAbelianSubgroupsOf G) (f := toConjClassOfSet G)
    (toConjClassOfSet_eq_of_related_noncenter_subgroups G)


end MaximalAbelianSubgroupsOf

section Finite

open Function

lemma Injective_subroup_to_subset {L : Type*} [Group L] (G : Subgroup L) [Finite G] :
  Injective
    (fun (H : {K | (K : Subgroup L) ≤ G}) =>
      (⟨H.val.carrier, H.property⟩ : {K | K ⊆ G.carrier})) := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩ hAB
  simp at hAB ⊢
  refine toSubmonoid_inj.mp ?_
  ext x
  exact Eq.to_iff (congrFun hAB x)


instance finite_MaximalAbelianSubgroups {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] : Set.Finite (MaximalAbelianSubgroupsOf G) := by
  apply Set.Finite.subset (s := {K | (K : Subgroup SL(2,F)) ≤ G})
  · apply @Finite.of_injective _ _ ?set_finite _ (Injective_subroup_to_subset G)
    exact Set.Finite.finite_subsets hG
  · intro M hM
    exact hM.right

instance finite_MaximalAbelianSubgroups' {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] : Finite (MaximalAbelianSubgroupsOf G) :=
    Set.finite_coe_iff.mpr <| finite_MaximalAbelianSubgroups G

instance finite_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] : Finite (noncenter_MaximalAbelianSubgroupsOf G) := by
  dsimp [noncenter_MaximalAbelianSubgroupsOf]
  refine Finite.of_surjective (
    fun (A : MaximalAbelianSubgroupsOf G) =>
    (
      ⟨noncenter A.val,
      noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G A⟩ :
      noncenter_MaximalAbelianSubgroupsOf G
    )
    ) ?_
  rintro ⟨A_star, A, A_mem_MaximalAbelianSubgroupsOf, hA⟩
  use ⟨A, A_mem_MaximalAbelianSubgroupsOf⟩
  simp [hA]

instance finite_MaximalAbelianSubgroups_lift {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] : Finite (Quotient (lift_MaximalAbelianSubgroupsOf G)) := Quotient.finite _

instance finite_lift_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :
  Finite (Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G)) := Quotient.finite _

noncomputable instance fintype_lift_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [hG : Finite G] :
  Fintype (Quotient (lift_MaximalAbelianSubgroupsOf G)) := by
  apply fintypeOfNotInfinite
  rw [not_infinite_iff_finite]
  exact finite_MaximalAbelianSubgroups_lift G

noncomputable instance fintype_lift_noncenter_MaximalAbelianSubgroups {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [hG : Finite G] :
  Fintype (Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G)) := by
  apply fintypeOfNotInfinite
  rw [not_infinite_iff_finite]
  exact finite_lift_noncenter_MaximalAbelianSubgroupsOf G


end Finite

/-
Somehow need to lift this statement

⋃ A_star : lift_noncenter_MaximalAbelianSubgroupsOf G,
      lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G A_star

or

⋃ A_star : lift_noncenter_MaximalAbelianSubgroupsOf G,
      lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G A_star.exists_rep.choose


-/

lemma union_noncenter_C_eq_G_diff_center {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  (G : Subgroup SL(2,F)) [hG : Finite G] :
  G.carrier \ center SL(2,F) =
    ⋃ A_star : noncenter_MaximalAbelianSubgroupsOf G,
      union_conj_noncenter_MaximalAbelianSubgroupsOf G A_star := by
    ext x
    constructor
    · rintro hx
      rw [Set.mem_iUnion]
      use ⟨
        centralizer {x} ⊓ G \ center SL(2,F), by
        dsimp [noncenter_MaximalAbelianSubgroupsOf]
        use centralizer {x} ⊓ G
        constructor
        · exact centralizer_meet_G_in_MaximalAbelianSubgroups_of_noncentral G x hx
        · rw [Set.inter_diff_distrib_left]
          have center_le_centralizer : center SL(2,F) ≤ centralizer {x} := center_le_centralizer {x}
          rw [Set.inter_eq_self_of_subset_right center_le_centralizer]
          rfl⟩
      dsimp [union_conj_noncenter_MaximalAbelianSubgroupsOf]
      rw [@Set.mem_iUnion₂]
      use 1
      simp only [_root_.map_one, one_smul, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_diff,
        exists_and_left, exists_prop]
      split_ands
      · exact mem_centralizer_singleton_iff.mpr rfl
      · apply hx.left
      · exact Subgroup.one_mem G
      · apply hx.right
    · intro hx
      rw [@Set.mem_iUnion] at hx
      obtain ⟨A_star, hA⟩ := hx
      dsimp [union_conj_noncenter_MaximalAbelianSubgroupsOf] at hA
      simp [noncenter_MaximalAbelianSubgroupsOf] at A_star
      rw [Set.mem_iUnion₂] at hA
      obtain ⟨c, hc⟩ := hA
      simp only [exists_prop] at hc
      obtain ⟨c_mem_G, x_mem_conj_c⟩ := hc
      obtain ⟨A, A_MaximalAbelian, hA⟩ := A_star.prop
      simp [← hA, noncenter, Set.mem_smul_set_iff_inv_smul_mem] at x_mem_conj_c
      have A_subs_G := A_MaximalAbelian.right
      obtain ⟨x_mem_G, x_not_mem_center⟩ := x_mem_conj_c
      rw [← @conj_inv_apply, ← MulAut.smul_def, ← mem_carrier,
        ← Set.mem_smul_set_iff_inv_smul_mem] at x_mem_G x_not_mem_center
      simp only [Set.mem_diff, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
        mem_toSubmonoid, SetLike.mem_coe]
      split_ands
      · apply conj_smul_le_of_le A_subs_G ⟨c, c_mem_G⟩
        apply x_mem_G
      · have conj_center_eq_center : conj c • (center SL(2, F)) = (center SL(2,F)) := by
          exact Normal.conj_smul_eq_self c (center SL(2, F))
        have : conj c • (center SL(2,F)).carrier = (conj c • (center SL(2, F))).carrier := by rfl
        rw [(by rfl : conj c • (center SL(2,F)).carrier = (conj c • (center SL(2, F))).carrier),
          conj_center_eq_center] at x_not_mem_center
        exact x_not_mem_center

-- theorem key {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
--   (G : Subgroup SL(2,F)) [hG : Finite G]  : ⋃ A_star : noncenter_MaximalAbelianSubgroupsOf G,
--       union_conj_noncenter_MaximalAbelianSubgroupsOf G A_star =

/-
Theorem 2.4 i a)
The union of elements of the `Quotient` on the `Setoid`,
`lift_noncenter_MaximalAbelianSubgroups G` is equal to `G \ Z`
-/
lemma union_lift_union_conj_noncenter_MaximalAbelianSubgroupsOf_eq_G_diff_center {F : Type*}
  [Field F] [IsAlgClosed F] [DecidableEq F] (G : Subgroup SL(2,F)) [hG : Finite G] :
  G.carrier \ center SL(2,F) =
    ⋃ A_star : Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G),
      lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G A_star := by
    rw [union_noncenter_C_eq_G_diff_center]
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx ⊢
      obtain ⟨noncenter_M, hM⟩ := hx
      use Quotient.mk (lift_noncenter_MaximalAbelianSubgroupsOf G) noncenter_M
      exact hM
    · intro hx
      rw [Set.mem_iUnion] at hx ⊢
      obtain ⟨lift_noncenter_M, hM⟩ := hx
      obtain ⟨noncenter_M, hM'⟩ := Quot.exists_rep lift_noncenter_M
      use noncenter_M
      rw [← hM'] at hM
      exact hM

/-
use disjUnion
-/
-- lemma union_equiv_clasess_eq_union_lift {F : Type*}
--   [Field F] [IsAlgClosed F] [DecidableEq F] (G : Subgroup SL(2,F)) [hG : Finite G]  : ⋃ A_star : Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G),
--       lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G A_star = ⋃ A_star : (lift_noncenter_MaximalAbelianSubgroupsOf G).classes, union_conj_noncenter_MaximalAbelianSubgroupsOf G A_star := by sorry

def equivalence_classes {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) := Setoid.isPartition_classes <|lift_noncenter_MaximalAbelianSubgroupsOf G

#check Setoid.IsPartition.sUnion_eq_univ

/-
Theorem 2.4 i b)
Distinct elements in the `Quotient` of the `Setoid`,
`lift_noncenter_MaximalAbelianSubgroups G` map to disjoint subsets
when sent through `lift_noncenter_C`.
-/


section Subsets

def subsets_MaximalAbelianSubgroups {L : Type*} [Group L] (G : Subgroup L) :=
  { (K : Set L) | K ∈ MaximalAbelianSubgroupsOf G }

lemma mem_subsets_MaximalAbelianSubgroups {F : Type*} [Field F] {G : Subgroup SL(2,F)}
  (A : MaximalAbelianSubgroupsOf G) : A.val.carrier ∈ subsets_MaximalAbelianSubgroups G := by
  simp only [subsets_MaximalAbelianSubgroups, Set.mem_setOf_eq];
  use A.val
  simp only [Subtype.coe_prop, true_and]
  congr

noncomputable def finset_MaximalAbelianSubgroups {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :=
  (@Set.Finite.toFinset _ (s := MaximalAbelianSubgroupsOf G) )
  (h := finite_MaximalAbelianSubgroups G)

open Function

/-
Now we do the same but for MaximalAbelianSubgroups being a Set (Set SL(2,F))
-/
lemma Surjective_MaxAbSub_to_subsets_MaxAbSub {F : Type*} [Field F] (G : Subgroup SL(2,F)) :
  Surjective
    (fun (A : MaximalAbelianSubgroupsOf G) =>
      (⟨A.val.carrier, mem_subsets_MaximalAbelianSubgroups A⟩ :
        subsets_MaximalAbelianSubgroups G)) := by
    rintro ⟨A, ⟨M, hM₁, hM₂⟩⟩
    use ⟨M, hM₁⟩
    exact SetCoe.ext hM₂

lemma finite_subsets_MaximalAbelianSubgroups {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [ hG : Finite G] : Set.Finite (subsets_MaximalAbelianSubgroups G) := by
  let inst₀ : Set.Finite (MaximalAbelianSubgroupsOf G) := finite_MaximalAbelianSubgroups G
  let inst₁:  Finite ↑(MaximalAbelianSubgroupsOf G) := inst₀
  exact @Finite.of_surjective
    (α := (MaximalAbelianSubgroupsOf G)) _ _ _ (Surjective_MaxAbSub_to_subsets_MaxAbSub G)

noncomputable def finset_subsets_MaximalAbelianSubgroups {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [hG : Finite G] := @Set.Finite.toFinset _
    (s := subsets_MaximalAbelianSubgroups G) (h := finite_subsets_MaximalAbelianSubgroups G)

/-
Define the equivalence relation $\sim$ on $\mathcal{M}^*$ by
$A_i \sim A_j$ if and only if $A_i = x A_j x^{-1}$ for some $x \in G$.
 -/
instance finset_subsets_MaximalAbelianSubgroups_lift {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [Finite G] :  Setoid (finset_subsets_MaximalAbelianSubgroups G) where
  r A B := ∃ (x : SL(2,F)), conj x • A.val = B.val
  iseqv := {
    refl A := ⟨1, by simp⟩
    symm := by
      rintro A B ⟨x, hx⟩
      use x⁻¹
      simp at hx ⊢
      rw [inv_smul_eq_iff]
      exact hx.symm
    trans := by
      rintro A B C ⟨x, hx⟩ ⟨y, hy⟩
      use y * x
      rw [← hy, ← hx, smul_smul, MonoidHom.map_mul]
  }

open Setoid


def isPartition_MaximalAbelianSubgroups_lift {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :=
  isPartition_classes (finset_subsets_MaximalAbelianSubgroups_lift G)


noncomputable def finpartition_MaximalAbelianSubgroups {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] := @Setoid.IsPartition.finpartition SL(2,F)
    (c := finset_subsets_MaximalAbelianSubgroups G)
    --(hc := isPartition_classes (finset_subsets_MaximalAbelianSubgroups_lift G))



end Subsets


/-
Define $C(A) = \bigcup_{x \in G} xA x^{-1}$
-/
def C {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G]
  (A : MaximalAbelianSubgroupsOf G) := ⋃ x ∈ G, conj x • A.val.carrier



/-
We compute the cardinality of the noncenter conjugacy class
-/
-- noncomputable def card_noncenter_C {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G] :
--  noncenter_MaximalAbelianSubgroupsOf G → ℕ := fun A => Nat.card (noncenter_C G A)
/-
We have the relation $|C(A^*)| = |A^*| |\mathcal{C}(A^*)|$
-/
lemma card_noncenter_C_eq_noncenter_MaximalAbelianSubgroup_mul_noncenter_ConjClassOfSet
  {F : Type*} [hF : Field F] (G : Subgroup SL(2,F)) [hG : Finite G]
  (A : noncenter_MaximalAbelianSubgroupsOf G) :
  Nat.card (union_conj_noncenter_MaximalAbelianSubgroupsOf G A) =
    Nat.card A * card_noncenter_ConjClassOf G A := by
  dsimp [union_conj_noncenter_MaximalAbelianSubgroupsOf]
  have card_A_eq_card_conj_A (A : noncenter_MaximalAbelianSubgroupsOf G) (c : SL(2,F)) :
    Nat.card A.val = Nat.card (conj c • A.val :) := by simp
  -- rw [Set.Finite.ncard_biUnion]



  sorry

#check Group.nat_card_center_add_sum_card_noncenter_eq_card

#check Group.card_center_add_sum_card_noncenter_eq_card


-- lemma card_noncenter_C_eq_of_related {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G] :
--   ∀ (A B : noncenter_MaximalAbelianSubgroupsOf G),
--     A ≈ B → card_noncenter_C G A = card_noncenter_C G B := by
--   rintro A B ⟨y, y_in_G, conj_y_A_eq_B⟩
--   simp [card_noncenter_C, noncenter_C, ← conj_y_A_eq_B]
--   congr
--   ext z; constructor <;> rintro ⟨s, hs, z_in_s⟩
--   <;> obtain ⟨g, eq_s⟩ := hs
--   <;> rw [← eq_s] at z_in_s
--   <;> simp [Set.mem_iUnion] at z_in_s ⊢
--   <;> obtain ⟨g_in_G, z_in_conj_g_A⟩ := z_in_s
--   · use g * y⁻¹, Subgroup.mul_mem G g_in_G (inv_mem y_in_G)
--     simp only [_root_.map_mul, map_inv, smul_smul, inv_mul_cancel_right]
--     exact z_in_conj_g_A
--   · use g * y, Subgroup.mul_mem G g_in_G y_in_G
--     rw [_root_.map_mul, ← smul_smul]
--     exact z_in_conj_g_A



#check Setoid.isPartition_classes

#check Setoid.IsPartition.pairwiseDisjoint

#check Finset.card_disjiUnion

#check lift_noncenter_MaximalAbelianSubgroupsOf
/-
We have the relation $|C_i^*| = |A_i^*| |\mathcal{C}_i^*|$
-/
lemma card_noncenter_C_eq_card_A_mul_card_noncenter_ConjClass {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G]  (A : noncenter_MaximalAbelianSubgroupsOf G) :
  Nat.card (union_conj_noncenter_MaximalAbelianSubgroupsOf G A) =
    Nat.card A * card_noncenter_ConjClassOf G A := by
  sorry

/- $G \setminus Z(\textrm{SL}_2(F)) = \bigcup_{A \in \mathcal{M}} (C A)^*$ -/
lemma subgroup_sdiff_center_eq_union_noncenter_C {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [Finite G] : G.carrier \ center (SL(2,F)) =
    ⋃ A : noncenter_MaximalAbelianSubgroupsOf G, union_conj_noncenter_MaximalAbelianSubgroupsOf G A := by sorry



def ConjClassOf_to_noncenter_ConjClassOf {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) : (ConjClassOf G A) → (noncenter_ConjClassOf G (
      ⟨noncenter A, noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G A⟩)) :=
  fun conj_A => ⟨
    conj_A.val.noncenter,
    by
    obtain ⟨c, c_mem_G, conj_A_eq⟩ := conj_A.prop
    use c, c_mem_G
    rw [← conj_noncenter_eq_noncenter_conj, ← conj_A_eq]
  ⟩

open Function

#check Set.image_union
#check Set.union_diff_cancel

instance semiring {X : Type*} : Semiring (Set X) where
  add s t := Set.union s t
  add_assoc s t r := Set.union_assoc _ _ _
  zero := ⊥
  zero_add s := Set.empty_union _
  add_zero := Set.union_empty
  nsmul n s := sorry --⋃₀ i : Fin n, s
  add_comm := Set.union_comm
  mul s t := Set.inter s t
  left_distrib := Set.inter_union_distrib_left
  right_distrib := Set.union_inter_distrib_right
  zero_mul := Set.empty_inter
  mul_zero := Set.inter_empty
  mul_assoc := Set.inter_assoc
  one := ⊤
  one_mul := Set.univ_inter
  mul_one := Set.inter_univ
  nsmul_zero := sorry
  nsmul_succ := sorry


lemma conj_subgroup_eq_conj_center_union_conj_noncenter {G : Type*} [Group G] (H : Subgroup G)
  (c : G) : (conj c • H : Set G)
    = (conj c • H.noncenter : Set G) ∪ (conj c • (center G ⊓ H) : Set G) := by
  unfold noncenter
  rw [← Set.image_smul, ← Set.image_smul, ← Set.image_smul, ← Set.image_union,
  Set.union_comm]
  congr
  rw [← Set.diff_self_inter, Set.inter_comm, show H.carrier = (H : Set G) by rfl]
  simp only [coe_inf]
  rw [Set.union_diff_cancel (Set.inter_subset_right)]


lemma mem_coe_conj_iff_conj_coe {G : Type*} [Group G] (H : Subgroup G) (c x : G) :
    x ∈ conj c • H ↔ x ∈ (conj c • H : Set G) := by rfl

-- For Mathlib
instance instNormalCenterInf {G : Type*} [Group G] {H : Subgroup G} : Normal (center G ⊓ H) := by
  sorry

-- For Mathlib
lemma subset_of_union_eq_of_disjoint {G : Type*} (A B C : Set G) (hA : Disjoint A C)
  (h : A ∪ C = B ∪ C) : A ⊆ B := by
  intro a a_mem_A
  have a_mem_B_union_C : a ∈ B ∪ C := by
    rw [← h]
    exact Set.mem_union_left C a_mem_A
  suffices a ∉ C by
    rw [Set.mem_union] at a_mem_B_union_C
    grind
  have A_inter_C_eq_empty : A ∩ C = ∅ := Disjoint.inter_eq hA
  intro a_mem_C
  have contr : a ∈ (∅ : Set G) := by rw [← A_inter_C_eq_empty]; grind
  contradiction


-- For Mathlib
lemma eq_iff_union_eq_of_disjoint {G : Type*} (A B C: Set G) (hA : Disjoint A C)
  (hB : Disjoint B C) : A ∪ C = B ∪ C ↔ A = B := by
  constructor
  · intro h
    apply subset_antisymm
    · exact subset_of_union_eq_of_disjoint A B C hA h
    · exact subset_of_union_eq_of_disjoint B A C hB (id (Eq.symm h))
  · intro h
    rw [h]

theorem Disjoint_conj_noncenter_center {G : Type*} [inst : Group G]
  {c : G} (H : Subgroup G) (key : conj c • (center G ⊓ H) = center G ⊓ H)  :
  Disjoint (conj c • H.noncenter) ↑(center G ⊓ H) := by
  rw [disjoint_comm, disjoint_iff, eq_bot_iff, ← key]
  intro x ⟨x_mem_center, x_mem_conj⟩
  simp [Subgroup.noncenter] at x_mem_conj
  push_cast at x_mem_center
  rw [Set.mem_smul_set_iff_inv_smul_mem] at x_mem_conj x_mem_center
  rw [Set.mem_diff] at x_mem_conj
  suffices (conj c)⁻¹ • x ∈ center G by
    absurd x_mem_conj.right
    exact this
  apply Set.inter_subset_left
  apply x_mem_center


-- it is not clear whether I should be defining `Subgroup.noncenter`
-- or trying an alternative formalization
-- argument is symmetric, surely there must be a tactic for such cases
lemma conj_eq_conj_iff {G : Type*} [Group G] {c c' : G} (H : Subgroup G) :
    conj c • H.noncenter = conj c' • H.noncenter ↔ conj c • H = conj c' • H := by
  -- have :=  conj_subgroup_eq_conj_center_union_conj_noncenter H c
  suffices conj c • H.noncenter = conj c' • H.noncenter ↔ (conj c • H : Set G) = conj c' • H by
    simp [this]
    constructor <;> intro h <;> ext x
    · rw [mem_coe_conj_iff_conj_coe, mem_coe_conj_iff_conj_coe, h]
    · rw [← mem_coe_conj_iff_conj_coe, ← mem_coe_conj_iff_conj_coe, h]
  rw [conj_subgroup_eq_conj_center_union_conj_noncenter]
  have key₁ : conj c • (center G ⊓ H) = center G ⊓ H := Subgroup.Normal.conj_smul_eq_self c _
  norm_cast
  rw [key₁]
  push_cast
  rw [conj_subgroup_eq_conj_center_union_conj_noncenter]
  have key₂ : conj c' • (center G ⊓ H) = center G ⊓ H := Subgroup.Normal.conj_smul_eq_self c' _
  norm_cast
  rw [key₂]
  symm
  rw [eq_iff_union_eq_of_disjoint _ _]
  · exact Disjoint_conj_noncenter_center H key₁
  · exact Disjoint_conj_noncenter_center H key₂


lemma Bijective_ConjClassOf_to_noncenter_ConjClassOf {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) : Bijective (ConjClassOf_to_noncenter_ConjClassOf G A) := by
  refine ⟨?Injective, ?Surjective⟩
  · intro conj_A conj_B hAB
    obtain ⟨c, c_mem_G, conj_A_eq⟩ := conj_A.prop
    obtain ⟨c', c'_mem_G, conj_B_eq⟩ := conj_B.prop
    simp [ConjClassOf_to_noncenter_ConjClassOf] at hAB
    rw [← conj_A_eq, ← conj_B_eq, conj_noncenter_eq_noncenter_conj,
      conj_noncenter_eq_noncenter_conj] at hAB
    rw [conj_eq_conj_iff] at hAB
    apply Subtype.ext
    rw [← conj_A_eq, ← conj_B_eq, hAB]
  · intro ⟨A_noncenter, c, c_mem_G, conj_A_noncenter_eq⟩
    use ⟨conj c • A, by simp [ConjClassOf]; use c⟩
    simp [ConjClassOf_to_noncenter_ConjClassOf, ← conj_A_noncenter_eq]
    exact conj_noncenter_eq_noncenter_conj A c


#check Function.Bijective
/-
Theorem 2.4 ii)
$|\mathcal{C}_i| = |\mathcal{C}_i^*|$
-/
lemma card_noncenter_ConjClassOfSet_eq_card_ConjClassOfSet {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) (A : MaximalAbelianSubgroupsOf G) :
    Nat.card (ConjClassOf G A) =
    Nat.card (noncenter_ConjClassOf G (
      ⟨noncenter A, noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G A⟩
    )) := by
  exact Nat.card_eq_of_bijective _ (Bijective_ConjClassOf_to_noncenter_ConjClassOf G A)


noncomputable def conjClassOf_to_G {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) : ConjClassOf G A → G :=
  fun ⟨_, h⟩ => ⟨h.choose, h.choose_spec.left⟩

def G_to_ConjClassOf {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) : G → ConjClassOf G A :=
  fun ⟨c, hc⟩ => ⟨conj c • A.val, by use c⟩

-- For Mathlib
lemma conj_eq_of_mem {G : Type*} [Group G] {H : Subgroup G} {h : G} (hh : h ∈ H) :
    conj h • H = H := by
  apply le_antisymm (conj_smul_le_of_le (le_refl H) ⟨h, hh⟩)
  rw [subset_pointwise_smul_iff, ← map_inv]
  exact conj_smul_le_of_le (le_refl H) ⟨h⁻¹, H.inv_mem hh⟩

#check lift_MaximalAbelianSubgroupsOf

def G_to_ConjClassOf_lift  {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) : G ⧸ ((A.val.subgroupOf G).normalizer) → ConjClassOf G A :=
  Quot.lift (G_to_ConjClassOf G A)
  (by
  intro ⟨c, c_mem_G⟩ ⟨c', c'_mem_G⟩ h
  symm at h
  rw [QuotientGroup.leftRel_apply, mem_normalizer_iff] at h
  simp [G_to_ConjClassOf]
  rw [@conj_eq_iff_eq_conj_inv, smul_smul, ← map_mul]
  ext x; constructor
  · intro hx
    specialize h ⟨x, A.prop.right hx⟩
    simp [mem_subgroupOf] at h
    simp [mem_pointwise_smul_iff_inv_smul_mem]
    group at h ⊢
    apply h.mp hx
  · intro hx
    simp [mem_pointwise_smul_iff_inv_smul_mem] at hx
    have x_mem_G := A.prop.right hx
    rw [show c'⁻¹ * (c * x * c⁻¹) * c' = (conj (c⁻¹ * c'))⁻¹ • x by simp,
      ← mem_pointwise_smul_iff_inv_smul_mem] at x_mem_G
    suffices conj (c⁻¹ * c') • G = G by
      rw [this] at x_mem_G
      specialize h ⟨x, x_mem_G⟩
      simp [mem_subgroupOf] at h
      group at h hx
      apply h.mpr hx
    exact conj_eq_of_mem (G.mul_mem (G.inv_mem c_mem_G) c'_mem_G))


lemma Bijective_G_to_ConjClassOf_lift {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) : Bijective (G_to_ConjClassOf_lift G A) := by
  refine ⟨?Injective, ?Surjective⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp [G_to_ConjClassOf_lift] at hxy
    rw [Subtype.ext_iff] at hxy
    rw [Subtype.coe_eq_iff] at hxy
    obtain ⟨⟨c, c_mem_G, hc⟩, h⟩ := hxy
    simp_rw [← hc] at h
    rw [Quot.eq]
    sorry
  · dsimp [G_to_ConjClassOf_lift]
    rw [Quot.surjective_lift]
    intro ⟨conj_A, c, c_mem_G, conj_A_eq⟩
    use ⟨c, c_mem_G⟩
    simp [G_to_ConjClassOf, ← conj_A_eq]


-- noncomputable def conjClassOf_to_quot_normalizer {F : Type*} [Field F] (G : Subgroup SL(2,F))
--   (A : MaximalAbelianSubgroupsOf G) : ConjClassOf G A → G ⧸ ((A.val.subgroupOf G).normalizer) :=
--   fun conj_A => Quot.mk ⇑(QuotientGroup.leftRel ((A.val.subgroupOf G).normalizer)) ⟨_, conj_A.prop.choose_spec.left⟩



-- lemma Bijective_conjClassOf_to_quot_normalizer {F : Type*} [Field F] (G : Subgroup SL(2,F))
--   (A : MaximalAbelianSubgroupsOf G) : Bijective (conjClassOf_to_quot_normalizer G A) := by
--   refine ⟨?Injective, ?Surjective⟩
--   · intro conj_A conj_B h
--     simp [conjClassOf_to_quot_normalizer] at h
--     have ⟨c_mem_G, conj_A_eq⟩ := conj_A.prop.choose_spec
--     have ⟨c'_mem_G, conj_B_eq⟩ := conj_B.prop.choose_spec
--     set c := conj_A.prop.choose with hc
--     set c' := conj_B.prop.choose with hc'
--     simp_rw [← hc, ← hc'] at h
--     apply Subtype.ext
--     rw [← conj_A_eq, ← conj_B_eq]
--     symm at h
--     rw? at h
--     simp [Quot.eq, mem_normalizer_iff] at h
--     rw [conj_eq_iff_eq_conj_inv, smul_smul, ← map_mul]
--     ext x; constructor
--     · intro hx
--       simp [mem_pointwise_smul_iff_inv_smul_mem]
--       specialize h x (A.prop.right hx)
--       simp [mem_subgroupOf] at h
--       group at h ⊢
--       apply h.mp hx
--     · intro hx
--       simp [mem_pointwise_smul_iff_inv_smul_mem] at hx
--       have x_mem_G := A.prop.right hx
--       rw [show c'⁻¹ * (c * x * c⁻¹) * c' = (conj (c⁻¹ * c'))⁻¹ • x by simp,
--         ← mem_pointwise_smul_iff_inv_smul_mem] at x_mem_G
--       suffices conj (c⁻¹ * c') • G = G by
--         rw [this] at x_mem_G
--         specialize h x x_mem_G
--         simp [mem_subgroupOf] at h
--         group at h hx
--         apply h.mpr hx
--       exact conj_eq_of_mem (G.mul_mem (G.inv_mem c_mem_G) c'_mem_G)
--   · intro c_normalizer
--     obtain ⟨c, hc⟩ := c_normalizer
--     use ⟨conj c • A.val, by use c⟩
--     simp [conjClassOf_to_quot_normalizer]
--     let conj_A : ConjClassOf G A := ⟨conj c • A, by use c⟩
--     set c' := conj_A.prop.choose with hc'
--     simp_rw [← hc']





--     -- rw [QuotientGroup.eq]

--     -- rw [QuotientGroup.eq_iff_div_mem]


--     sorry

/-
Theorem 2.4 iii)
$|\mathcal{C}_i| = [G : N_G(A_i)]$
-/
lemma card_ConjClassOf_eq_index_normalizer {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) :
    Nat.card (ConjClassOf G A) = index (normalizer (A.val.subgroupOf G)) := by
  sorry

noncomputable instance {F : Type*} [Field F] {G : Subgroup SL(2,F)} [Finite G] :
  Fintype (Quotient (lift_MaximalAbelianSubgroupsOf G)) := by infer_instance


/-
the setNormalizer needs to be restricted to G
-/
-- noncomputable def lift_index_normalizer {F : Type*} [Field F] {G : Subgroup SL(2,F)} [Finite G] :=
--   @Quotient.lift _ _ (s := lift_noncenter_MaximalAbelianSubgroupsOf G)
--     (fun (A_star : noncenter_MaximalAbelianSubgroupsOf G) => index (setNormalizer (A_star.val)))

/-
Theorem 2.4 iv)
$|G \setminus Z| = \sum_{[A] \in \mathfrak{M} / \sim } |[A*]| |[C(A)*]|$
-/
theorem card_noncenter_fin_subgroup_eq_sum_card_noncenter_mul_index_normalizer {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G) :
  Nat.card (G.carrier \ (center SL(2,F)).carrier : Set SL(2,F)) =
  ∑ lift_A : Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G),
    lift_card_noncenter G lift_A * Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G lift_A) := by sorry

#check Sylow

-- inductive lift_noncenter_MaximalAbelianSubgroupsOfType {L : Type*} [Group L] (G : Subgroup L) extends lift_noncenter_MaximalAbelianSubgroupsOf G
--   | S
--   | T

#check MonoidHom

-- todo: probably somewhere in mathlib, but I can't find it.
lemma center_conj {G : Type*} [Group G] (x : G) (y: G) :
  x ∈ center G ↔ y * x * y⁻¹ ∈ center G := by
  simp only [mem_center_iff]
  constructor <;> intro h z
  · have := h (y⁻¹ * z * y)
    calc z * (y * x * y⁻¹)
        = y * (y⁻¹ * z * y * x) * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * z * y)) * y⁻¹ := by rw [this]
      _ = y * x * y⁻¹ * z := by group
  · have := h (y * z * y⁻¹)
    calc z * x
        = y⁻¹ * (y * z * y⁻¹ * (y * x * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * x * y⁻¹) * (y * z * y⁻¹)) * y := by rw [this]
      _ = x * z := by group

/-- Lemma 2.5 N_G(A) = N_G(A*)
Oddly it doesn't need any assumption about A being maximal or abelian.
-/
lemma normalizer_noncentral_eq {F : Type*} [Field F] (A G : Subgroup SL(2,F)) [Finite G]:
  normalizer (A.subgroupOf G) = setNormalizer (noncenter (A.subgroupOf G)) := by
  ext x
  constructor
  . intro h
    rw [mem_normalizer_iff] at h
    simp [setNormalizer]
    intro a ha
    specialize h ⟨a, ha⟩
    simp [Subgroup.mem_noncenter]
    rw [h]
    suffices ⟨a, ha⟩ ∈ center ↥G ↔ x * ⟨a, ha⟩ * x⁻¹ ∈ center ↥G by
      apply not_iff_not.mpr at this
      rw [this]
    rw [← center_conj]
  . intro h
    rw [mem_normalizer_iff]
    simp [setNormalizer] at h
    intro a
    specialize h a a.prop
    simp [Subgroup.mem_noncenter] at h
    by_cases hc: a ∈ center ↥G
    . have : x * a * x⁻¹ = a := by
        rw [mem_center_iff] at hc
        specialize hc x
        rw [hc]
        group
      rw [this]
    . simp [hc] at h
      rw [not_iff_not.mpr (center_conj a x)] at hc
      simp [hc] at h
      exact h

/- Lemma Let `Q` be a `p`-Sylow subgroup of `G` then $N_G(Q \sqcup Z) = N_G(Q)$-/
lemma normalizer_Sylow_join_center_eq_normalizer_Sylow {F : Type*} [Field F] {p : ℕ}
[Fact (Nat.Prime p)] [CharP F p] (G : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G) :
  normalizer (map G.subtype Q.toSubgroup ⊔ center SL(2,F)) =
    normalizer (map G.subtype Q.toSubgroup) := by
  sorry



#min_imports
