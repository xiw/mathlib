/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson
-/
import data.finset.gcd
import data.polynomial

/-!
# Gauss's Lemma, and GCD structures on polynomials

-/

variables {R : Type*} [integral_domain R]

namespace polynomial
section gcd_monoid
variable [gcd_monoid R]

def content (p : polynomial R) : R := (p.support).gcd p.coeff

lemma content_dvd_coeff {p : polynomial R} {n : ℕ} : p.content ∣ p.coeff n :=
begin
  by_cases h : n ∈ p.support,
  { apply finset.gcd_dvd h },
  rw [not_not, polynomial.mem_support_iff] at h,
end

/-- -/
def is_primitive (p : polynomial R) : Prop := (p.support).gcd p.coeff = 1

lemma add_erase (p : polynomial R) :
  monomial p.nat_degree p.leading_coeff + (finsupp.erase p.nat_degree p : polynomial R) = p :=
begin
  ext n,
  simp only [finsupp.erase, coeff_monomial, coeff_mk, coeff_add],
  by_cases h : n = p.nat_degree,
  { rw [if_pos h.symm, if_pos _, h, add_zero],
    { refl },
    apply h },
  { rw [if_neg, if_neg, zero_add],
    { refl },
    { apply h },
    { intro con, apply h con.symm } }
end

lemma is_primitive_mul {p q : polynomial R} (hp : p.is_primitive) (hq : q.is_primitive) :
  (p * q).is_primitive :=
begin
  have h : ∀ (n : ℕ) (p q : polynomial R), p.is_primitive → q.is_primitive → (p * q).nat_degree = n → (p * q).is_primitive,
  { clear hp hq p q,
    intro n,
    induction n with n hi,
    { intros p q hp hq hdeg,
      rw [eq_C_of_nat_degree_eq_zero hdeg, is_primitive],
      sorry,
    },
    intros p q hp hq hdeg,
    rw is_primitive,
    have h : (p * q).support.gcd (p * q).coeff ∣ p.leading_coeff * q.leading_coeff,
    { rw ← leading_coeff_mul p q, apply finset.gcd_dvd,
      rw [finsupp.mem_support_iff], },
    classical, by_contra hcon,
    have h := leading_coeff_mul p q,
    have h := hi (finsupp.erase p.nat_degree p) (finsupp.erase q.nat_degree q),
    sorry
  },
  apply h (p * q).nat_degree p q hp hq rfl,
end

@[elab_as_eliminator] protected lemma induction_on_degree {M : polynomial R → Prop} (p : polynomial R)
  (h_C : ∀ (a : R), M (C a))
  (h_add_monomial : ∀(n : ℕ) (a : R) (q : polynomial R), q.degree < n → M q → M (q + C a * X^n)) :
  M p :=
begin
  have h : ∀ n : ℕ, ∀ p : polynomial R, p.nat_degree = n → M p,
  { intros n,
    induction n using nat.strong_induction_on with n hi,
    intros p hn,
    cases n,
    { rw eq_C_of_nat_degree_eq_zero hn,
      apply h_C },
    have h := h_add_monomial p.nat_degree p.leading_coeff (p.erase p.nat_degree) _ _,
    { convert h, ext,
      by_cases h : n_1 = p.nat_degree,
      { simp [h, finsupp.erase, leading_coeff] },
      simp only [h, finsupp.erase, coeff_X_pow, add_zero, coeff_mk, coeff_C_mul,
        coeff_add, if_false, mul_zero],
      refl },
      { convert degree_erase_lt _, rw degree_eq_nat_degree _,
        iterate 2 { intro con,
          rw [con, nat_degree_zero] at hn,
          apply nat.succ_ne_zero _ hn.symm } },
      { apply hi (nat_degree (finsupp.erase p.nat_degree p)) _ _ rfl,
        rw ← hn,
        have h : p ≠ 0 := sorry,
        have h := degree_erase_lt h,
        rw [degree_eq_nat_degree, degree_eq_nat_degree, coe_lt_coe] at h,
        rw ← coe_lt_coe,
        rw ← degree_eq_nat_degree,
        convert degree_erase_lt _,
      } },
    apply h p.nat_degree, refl,
end

end gcd_monoid
end polynomial
