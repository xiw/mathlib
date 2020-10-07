/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot
-/
import algebra.ring.basic

/-!
# Parity in (semi)rings

In this file we define two predicates:

* `even a`: there exists `k` such that `a = 2 * k`;
* `odd a`: there exists `k` such that `a = 2 * k + 1`.

While they mostly make sense only in `ℕ` and `ℤ`, we define them in any semiring to have a unified
API. We prove simple lemmas that enable dot notation, e.g.,

* `even.add : even a → even b → even (a + b)`;
* `odd.add_even : odd a → even b → odd (a + b).

We also define induction principles `even.elim` and `odd.elim` that simplify unfolding of
assumptions like `h : even a` in term mode proofs. In tactic mode it's easier to use
`rcases h with ⟨k, rfl⟩`.

## Tags

parity, even, odd
-/

variables {R : Type*}

section semiring

variables [semiring R] {a b : R}

/-- An element `a` of a semiring is even if there exists `k` such `a = 2*k`. -/
def even (a : R) : Prop := ∃ k, a = 2*k

lemma even_iff_two_dvd : even a ↔ 2 ∣ a := iff.rfl

alias even_iff_two_dvd ↔ even.two_dvd has_dvd.dvd.even

@[elab_as_eliminator]
lemma even.elim {p : R → Prop} {a : R} (ha : even a) (hp : ∀ k, p (2 * k)) : p a :=
let ⟨k, hk⟩ := ha in hk.symm ▸ hp k

instance decidable_even [h : Π k : R, decidable (2 ∣ k)] : decidable_pred (even : R → Prop) :=
λ n, decidable_of_decidable_of_iff (h n)  even_iff_two_dvd.symm

/-- An element `a` of a semiring is odd if there exists `k` such `a = 2*k + 1`. -/
def odd (a : R) : Prop := ∃ k, a = 2*k + 1

@[elab_as_eliminator]
lemma odd.elim {p : R → Prop} {a : R} (ha : odd a) (hp : ∀ k, p (2 * k + 1)) : p a :=
let ⟨k, hk⟩ := ha in hk.symm ▸ hp k

@[simp] theorem even_zero : even (0 : R) := ⟨0, (mul_zero _).symm⟩

@[simp] lemma even_bit0 (a : R) : even (bit0 a) := ⟨a, (two_mul a).symm⟩

@[simp] lemma odd_bit1 (a : R) : odd (bit1 a) := ⟨a, by rw [bit1, bit0, two_mul]⟩

lemma even.add (ha : even a) (hb : even b) : even (a + b) :=
even.elim ha $ λ a, even.elim hb $ λ b, ⟨a + b, (mul_add _ _ _).symm⟩

lemma even.add_odd (ha : even a) (hb : odd b) : odd (a + b) :=
even.elim ha $ λ a, odd.elim hb $ λ b, ⟨a + b, by rw [mul_add, add_assoc]⟩

lemma odd.add_even (ha : odd a) (hb : even b) : odd (a + b) :=
add_comm b a ▸ hb.add_odd ha

lemma odd.add (ha : odd a) (hb : odd b) : even (a + b) :=
odd.elim ha $ λ a, odd.elim hb $ λ b,
  ⟨a + b + 1, by rw [add_assoc, add_left_comm (1 : R), ← two_mul, ← mul_add, ← mul_add, add_assoc]⟩

lemma even.mul_right (ha : even a) (b : R) : even (a * b) :=
dvd_mul_of_dvd_left ha b

lemma even.mul_left (ha : even a) (b : R) : even (b * a) :=
even.elim ha $ λ a, ⟨b * a, by rw [two_mul, two_mul, mul_add]⟩

@[nolint unused_argument] -- `hb` is unused
lemma even.mul_odd (ha : even a) (hb : odd b) : even (a * b) :=
ha.mul_right b

@[nolint unused_argument] -- `ha` is unused
lemma odd.mul_even (ha : odd a) (hb : even b) : even (a * b) :=
hb.mul_left a

lemma odd.mul (ha : odd a) (hb : odd b) : odd (a * b) :=
odd.elim ha $ λ a, odd.elim hb $ λ b, ⟨2 * a * b + a + b,
  by simp only [mul_add, add_mul, two_mul, mul_one, one_mul]; ac_refl⟩

end semiring

section ring

variables [ring R] {a b : R}

lemma even.neg (ha : even a) : even (-a) :=
even.elim ha $ λ a, ⟨-a, neg_mul_eq_mul_neg _ _⟩

lemma even.of_neg (ha : even (-a)) : even a := neg_neg a ▸ ha.neg

@[simp] lemma even_neg : even (-a) ↔ even a := ⟨even.of_neg, even.neg⟩

lemma odd.neg (ha : odd a) : odd (-a) :=
odd.elim ha $ λ a, ⟨-a-1, by simp [two_mul, add_assoc, sub_eq_add_neg]; ac_refl⟩

lemma odd.of_neg (ha : odd (-a)) : odd a := neg_neg a ▸ ha.neg

@[simp] lemma odd_neg : odd (-a) ↔ odd a := ⟨odd.of_neg, odd.neg⟩

lemma even.sub (ha : even a) (hb : even b) : even (a - b) :=
ha.add hb.neg

lemma even.sub_odd (ha : even a) (hb : odd b) : odd (a - b) :=
ha.add_odd hb.neg

lemma odd.sub_even (ha : odd a) (hb : even b) : odd (a - b) :=
ha.add_even hb.neg

lemma odd.sub (ha : odd a) (hb : odd b) : even (a - b) :=
ha.add hb.neg

end ring
