/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import data.int.modeq
import data.nat.parity

/-!
# Properties of `even` and `odd` predicates on integer  numbers

The predicates `even` and `odd` are defined in `algebra/ring/parity` for any semiring. In this file
we prove various facts which are specific to integer numbers.

## Tags

parity, even, add, natural number
-/

namespace int

@[simp] theorem mod_two_ne_one {n : ℤ} : ¬ n % 2 = 1 ↔ n % 2 = 0 :=
by cases mod_two_eq_zero_or_one n with h h; simp [h]

local attribute [simp] -- euclidean_domain.mod_eq_zero uses (2 ∣ n) as normal form
theorem mod_two_ne_zero {n : ℤ} : ¬ n % 2 = 0 ↔ n % 2 = 1 :=
by cases mod_two_eq_zero_or_one n with h h; simp [h]

@[simp, norm_cast] theorem even_coe_nat (n : nat) : even (n : ℤ) ↔ even n :=
have ∀ m, 2 * to_nat m = to_nat (2 * m),
 from λ m, by cases m; refl,
⟨λ ⟨m, hm⟩, ⟨to_nat m, by rw [this, ←to_nat_coe_nat n, hm]⟩,
 λ ⟨m, hm⟩, ⟨m, by simp [hm]⟩⟩

theorem even_iff {n : ℤ} : even n ↔ n % 2 = 0 :=
⟨λ ⟨m, hm⟩, by simp [hm], λ h, ⟨n / 2, (mod_add_div n 2).symm.trans (by simp [h])⟩⟩

theorem odd_iff {n : ℤ} : odd n ↔ n % 2 = 1 :=
⟨λ ⟨m, hm⟩, by { rw [hm, add_mod], norm_num },
 λ h, ⟨n / 2, (mod_add_div n 2).symm.trans (by { rw h, abel })⟩⟩

lemma not_even_iff {n : ℤ} : ¬ even n ↔ n % 2 = 1 :=
by rw [even_iff, mod_two_ne_zero]

@[simp] lemma odd_iff_not_even {n : ℤ} : odd n ↔ ¬ even n :=
by rw [not_even_iff, odd_iff]

@[simp] theorem two_dvd_ne_zero {n : ℤ} : ¬ 2 ∣ n ↔ n % 2 = 1 :=
not_even_iff

instance decidable_pred_odd : decidable_pred (odd : ℤ → Prop) :=
λ n, decidable_of_decidable_of_iff (by apply_instance) odd_iff_not_even.symm

@[simp] theorem not_even_one : ¬ even (1 : ℤ) :=
by rw even_iff; apply one_ne_zero

@[parity_simps] theorem even_add {m n : ℤ} : even (m + n) ↔ (even m ↔ even n) :=
begin
  cases mod_two_eq_zero_or_one m with h₁ h₁; cases mod_two_eq_zero_or_one n with h₂ h₂;
    simp [even_iff, h₁, h₂, -euclidean_domain.mod_eq_zero],
  { exact @modeq.modeq_add _ _ 0 _ 0 h₁ h₂ },
  { exact @modeq.modeq_add _ _ 0 _ 1 h₁ h₂ },
  { exact @modeq.modeq_add _ _ 1 _ 0 h₁ h₂ },
  exact @modeq.modeq_add _ _ 1 _ 1 h₁ h₂
end

@[simp] theorem not_even_bit1 (n : ℤ) : ¬ even (bit1 n) :=
by simp [bit1] with parity_simps

@[parity_simps] theorem even_sub {m n : ℤ} : even (m - n) ↔ (even m ↔ even n) :=
by simp [sub_eq_add_neg] with parity_simps

@[parity_simps] theorem even_mul {m n : ℤ} : even (m * n) ↔ even m ∨ even n :=
begin
  cases mod_two_eq_zero_or_one m with h₁ h₁; cases mod_two_eq_zero_or_one n with h₂ h₂;
    simp [even_iff, h₁, h₂, -euclidean_domain.mod_eq_zero],
  { exact @modeq.modeq_mul _ _ 0 _ 0 h₁ h₂ },
  { exact @modeq.modeq_mul _ _ 0 _ 1 h₁ h₂ },
  { exact @modeq.modeq_mul _ _ 1 _ 0 h₁ h₂ },
  exact @modeq.modeq_mul _ _ 1 _ 1 h₁ h₂
end

@[parity_simps] theorem even_pow {m : ℤ} {n : ℕ} : even (m^n) ↔ even m ∧ n ≠ 0 :=
by { induction n with n ih; simp [*, even_mul, pow_succ], tauto }

-- Here are examples of how `parity_simps` can be used with `int`.

example (m n : ℤ) (h : even m) : ¬ even (n + 3) ↔ even (m^2 + m + n) :=
by simp [*, (dec_trivial : ¬ 2 = 0)] with parity_simps

example : ¬ even (25394535 : ℤ) :=
by simp

end int
