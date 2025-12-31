import Mathlib

variable (A B C : Type*) [MulOne A] [MulOne B] [MulOne C]

instance : Trans
  (@MonoidHom A B)
  (@MonoidHom B C)
  (@MonoidHom A C)
  where trans f g := g.comp f

instance : Trans
  (@MulEquiv A B)
  (@MulEquiv B C)
  (@MulEquiv A C)
  where trans f g := f.trans g

-- Having issues with this one
-- instance : Trans
--   (@MulEquiv A B)
--   (@MonoidHom B C)
--   (@MonoidHom A C)
--   where trans f g := g.comp f.toMonoidHom

noncomputable example : ℤ →* ℝ :=
  calc
  ℤ →* ℚ := MonoidHom.smulOneHom
  ℚ →* ℝ := MonoidHom.smulOneHom
  ℝ →* ℝ := {
    toFun := fun x => abs x
    map_one' := by simp
    map_mul' := by simp
  }




example : Multiplicative (ZMod 2) ≃* Multiplicative (ZMod 2) :=
  calc
  Multiplicative (ZMod 2) ≃* Multiplicative (ZMod 2) := sorry
  Multiplicative (ZMod 2) ≃* Multiplicative (ZMod 2) := sorry

-- if it is not possible, would it be possible to beed up calc?

-- if so, I would love to work on this.

def sum_of_first_n_odd_nat : ℕ → ℕ
| 0 => 0
| (Nat.succ n) => sum_of_first_n_odd_nat n + (2*n+1)


theorem closed_eq_sum_of_first_n_odd_nat (n : ℕ) : (sum_of_first_n_odd_nat n) = n * n := by
  induction n
  -- Prove the base case.
  case zero =>
    rw [mul_zero, sum_of_first_n_odd_nat]
  -- Prove the induction step.
  case succ m hm =>
    rewrite [sum_of_first_n_odd_nat]
    -- Apply the induction hypothesis
    rewrite [hm]
    -- Multiply out the square of sum
    rewrite [add_mul_self_eq]
    -- We finish it off by hand
    rewrite [mul_one, mul_one, add_assoc]
    rfl

#check add_mul_self_eq



#min_imports
