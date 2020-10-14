/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin, Patrick Massot
-/

import algebra.ordered_group
import algebra.group_with_zero
import algebra.group_with_zero_power

/-!
# Linearly ordered commutative groups with a zero element adjoined

This file sets up a special class of linearly ordered commutative monoids
that show up as the target of so-called “valuations” in algebraic number theory.

Usually, in the informal literature, these objects are constructed
by taking a linearly ordered commutative group Γ and formally adjoining a zero element: Γ ∪ {0}.

The disadvantage is that a type such as `nnreal` is not of that form,
whereas it is a very common target for valuations.
The solutions is to use a typeclass, and that is exactly what we do in this file.
-/

set_option old_structure_cmd true

/-- A linearly ordered commutative group with a zero element. -/
class linear_ordered_comm_group_with_zero (α : Type*)
  extends linear_order α, comm_group_with_zero α :=
(mul_le_mul_left : ∀ {a b : α}, a ≤ b → ∀ c : α, c * a ≤ c * b)
(zero_le_one : (0:α) ≤ 1)

variables {α : Type*} [linear_ordered_comm_group_with_zero α]
variables {a b c d x y z : α}

local attribute [instance] classical.prop_decidable

/-- Every linearly ordered commutative group with zero is an ordered commutative monoid.-/
@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_comm_group_with_zero.to_ordered_comm_monoid : ordered_comm_monoid α :=
{ lt_of_mul_lt_mul_left := λ a b c h, by { contrapose! h,
    exact linear_ordered_comm_group_with_zero.mul_le_mul_left h a }
  .. ‹linear_ordered_comm_group_with_zero α› }


section linear_ordered_comm_monoid
/-
The following facts are true more generally in a (linearly) ordered commutative monoid.
-/

lemma one_le_pow_of_one_le' {n : ℕ} (H : 1 ≤ x) : 1 ≤ x^n :=
begin
  induction n with n ih,
  { exact le_refl 1 },
  { exact one_le_mul H ih }
end

lemma pow_le_one_of_le_one {n : ℕ} (H : x ≤ 1) : x^n ≤ 1 :=
begin
  induction n with n ih,
  { exact le_refl 1 },
  { exact mul_le_one' H ih }
end

lemma eq_one_of_pow_eq_one {n : ℕ} (hn : n ≠ 0) (H : x ^ n = 1) : x = 1 :=
begin
  rcases nat.exists_eq_succ_of_ne_zero hn with ⟨n, rfl⟩, clear hn,
  induction n with n ih,
  { simpa using H },
  { cases le_total x 1 with h,
    all_goals
    { have h1 := mul_le_mul_right' h (x ^ (n + 1)),
      rw pow_succ at H,
      rw [H, one_mul] at h1 },
    { have h2 := pow_le_one_of_le_one h,
      exact ih (le_antisymm h2 h1) },
    { have h2 := one_le_pow_of_one_le' h,
      exact ih (le_antisymm h1 h2) } }
end

lemma pow_eq_one_iff {n : ℕ} (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 :=
⟨eq_one_of_pow_eq_one hn, by { rintro rfl, exact one_pow _ }⟩

lemma one_le_pow_iff {n : ℕ} (hn : n ≠ 0) : 1 ≤ x^n ↔ 1 ≤ x :=
begin
  refine ⟨_, one_le_pow_of_one_le'⟩,
  contrapose!,
  intro h, apply lt_of_le_of_ne (pow_le_one_of_le_one (le_of_lt h)),
  rw [ne.def, pow_eq_one_iff hn],
  exact ne_of_lt h,
end

lemma pow_le_one_iff {n : ℕ} (hn : n ≠ 0) : x^n ≤ 1 ↔ x ≤ 1 :=
begin
  refine ⟨_, pow_le_one_of_le_one⟩,
  contrapose!,
  intro h, apply lt_of_le_of_ne (one_le_pow_of_one_le' (le_of_lt h)),
  rw [ne.def, eq_comm, pow_eq_one_iff hn],
  exact ne_of_gt h,
end

end linear_ordered_comm_monoid

lemma zero_le_one' : (0 : α) ≤ 1 :=
linear_ordered_comm_group_with_zero.zero_le_one

lemma zero_lt_one' : (0 : α) < 1 :=
lt_of_le_of_ne zero_le_one' zero_ne_one

@[simp] lemma zero_le' : 0 ≤ a :=
by simpa only [mul_zero, mul_one] using mul_le_mul_left' (@zero_le_one' α _) a

@[simp] lemma not_lt_zero' : ¬a < 0 :=
not_lt_of_le zero_le'

@[simp] lemma le_zero_iff : a ≤ 0 ↔ a = 0 :=
⟨λ h, le_antisymm h zero_le', λ h, h ▸ le_refl _⟩

lemma zero_lt_iff : 0 < a ↔ a ≠ 0 :=
⟨ne_of_gt, λ h, lt_of_le_of_ne zero_le' h.symm⟩

lemma le_of_le_mul_right (h : c ≠ 0) (hab : a * c ≤ b * c) : a ≤ b :=
by simpa only [mul_inv_cancel_right' h] using (mul_le_mul_right' hab c⁻¹)

lemma le_mul_inv_of_mul_le (h : c ≠ 0) (hab : a * c ≤ b) : a ≤ b * c⁻¹ :=
le_of_le_mul_right h (by simpa [h] using hab)

lemma mul_inv_le_of_le_mul (h : c ≠ 0) (hab : a ≤ b * c) : a * c⁻¹ ≤ b :=
le_of_le_mul_right h (by simpa [h] using hab)

lemma div_le_div' (a b c d : α) (hb : b ≠ 0) (hd : d ≠ 0) :
  a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b :=
begin
  by_cases ha : a = 0, { simp [ha] },
  by_cases hc : c = 0, { simp [inv_ne_zero hb, hc, hd], },
  exact @div_le_div_iff' _ _ (units.mk0 a ha) (units.mk0 b hb) (units.mk0 c hc) (units.mk0 d hd)
end

lemma ne_zero_of_lt (h : b < a) : a ≠ 0 :=
λ h1, not_lt_zero' $ show b < 0, from h1 ▸ h

@[simp] lemma units.zero_lt (u : units α) : (0 : α) < u :=
zero_lt_iff.2 $ u.ne_zero

lemma mul_lt_mul'''' (hab : a < b) (hcd : c < d) : a * c < b * d :=
have hb : b ≠ 0 := ne_zero_of_lt hab,
have hd : d ≠ 0 := ne_zero_of_lt hcd,
if ha : a = 0 then by { rw [ha, zero_mul, zero_lt_iff], exact mul_ne_zero hb hd } else
if hc : c = 0 then by { rw [hc, mul_zero, zero_lt_iff], exact mul_ne_zero hb hd } else
@mul_lt_mul''' _ _ (units.mk0 a ha) (units.mk0 b hb) (units.mk0 c hc) (units.mk0 d hd) hab hcd

lemma mul_inv_lt_of_lt_mul' (h : x < y * z) : x * z⁻¹ < y :=
have hz : z ≠ 0 := (mul_ne_zero_iff.1 $ ne_zero_of_lt h).2,
by { contrapose! h, simpa only [inv_inv'] using mul_inv_le_of_le_mul (inv_ne_zero hz) h }

lemma mul_lt_right' (c : α) (h : a < b) (hc : c ≠ 0) : a * c < b * c :=
by { contrapose! h, exact le_of_le_mul_right hc h }

lemma inv_lt_inv'' (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ < b⁻¹ ↔ b < a :=
@inv_lt_inv_iff _ _ (units.mk0 a ha) (units.mk0 b hb)

lemma inv_le_inv'' (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
@inv_le_inv_iff _ _ (units.mk0 a ha) (units.mk0 b hb)
