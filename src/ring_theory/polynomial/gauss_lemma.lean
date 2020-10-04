/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson
-/
import data.finset.gcd
import data.polynomial

/-!
# Gauss's Lemma, and GCD structures on polynomials

Gauss's Lemma is one of a few results pertaining to `gcd`s and irreducibility in polynomials over
GCD domains.

## Main Definitions
Let `p : polynomial R`.
 - `p.content` is the `gcd` of the coefficients of `p`.
 - `p.is_primitive` indicates that `p.content = 1`.

## Main Results
 - If `p q : polynomial R`, then `(p * q).content = p.content * q.content`.

-/

variables {R : Type*} [integral_domain R]

namespace polynomial
section gcd_monoid
variable [gcd_monoid R]

def content (p : polynomial R) : R := (p.support).gcd p.coeff

lemma content_dvd_coeff {p : polynomial R} (n : ℕ) : p.content ∣ p.coeff n :=
begin
  by_cases h : n ∈ p.support,
  { apply finset.gcd_dvd h },
  rw [mem_support_iff_coeff_ne_zero, not_not] at h,
  rw h,
  apply dvd_zero,
end

@[simp] lemma content_C {r : R} : (C r).content = normalize r :=
begin
  rw content,
  by_cases h0 : r = 0,
  { simp [h0] },
  have h : (C r).support = {0} := finsupp.support_single_ne_zero h0,
  simp [h],
end

@[simp] lemma content_zero : content (0 : polynomial R) = 0 :=
begin
  rw [← C_0, content_C],
  simp,
end

lemma content_eq_zero_iff {p : polynomial R} : content p = 0 ↔ p = 0 :=
begin
  rw [content, finset.gcd_eq_zero_iff],
  split; intro h,
  { ext n,
    by_cases h0 : n ∈ p.support,
    { rw [h n h0, coeff_zero], },
    { rw mem_support_iff_coeff_ne_zero at h0,
      push_neg at h0,
      simp [h0] } },
  { intros x h0,
    simp [h] }
end

@[simp] lemma normalize_content {p : polynomial R} : normalize p.content = p.content :=
finset.normalize_gcd

lemma content_eq_gcd_range_of_lt (p : polynomial R) (n : ℕ) (h : p.nat_degree < n) :
  p.content = (finset.range n).gcd p.coeff :=
begin
  apply dvd_antisymm_of_normalize_eq normalize_content finset.normalize_gcd,
  { rw finset.dvd_gcd_iff,
    intros i hi,
    apply content_dvd_coeff _ },
  { apply finset.gcd_mono,
    intro i,
    simp only [nat.lt_succ_iff, mem_support_iff_coeff_ne_zero, ne.def, finset.mem_range],
    contrapose!,
    intro h1,
    apply coeff_eq_zero_of_nat_degree_lt (lt_of_lt_of_le h h1), }
end

lemma content_eq_gcd_range_succ (p : polynomial R) :
  p.content = (finset.range p.nat_degree.succ).gcd p.coeff :=
content_eq_gcd_range_of_lt _ _ (nat.lt_succ_self _)

lemma content_eq_gcd_leading_coeff_content_sub (p : polynomial R) :
  p.content = gcd_monoid.gcd p.leading_coeff (p - C p.leading_coeff * X ^ p.nat_degree).content :=
begin
  rw [content_eq_gcd_range_succ, finset.range_succ, finset.gcd_insert, leading_coeff, content],
  refine congr rfl _,
  transitivity (finset.range p.nat_degree).gcd (p - C (p.coeff p.nat_degree) * X ^ p.nat_degree).coeff,
  { apply finset.gcd_congr rfl,
    intros a ha,
    rw finset.mem_range at ha,
    rw coeff_sub,
    symmetry,
    convert sub_zero (p.coeff a),
    rw [coeff_C_mul_X, if_neg (ne_of_lt ha)] },
  { classical,
    rw finset.gcd_eq_gcd_filter_ne_zero,
    refine congr (congr rfl _) rfl,
    ext,
    simp only [coeff_C_mul, and_iff_right_iff_imp, mem_support_iff_coeff_ne_zero, ne.def, finset.mem_filter,
      finset.mem_range, coeff_sub],
    contrapose!,
    intro h,
    cases eq_or_lt_of_le h with heq hlt,
    { simp [← heq], },
    rw [coeff_eq_zero_of_nat_degree_lt hlt, coeff_X_pow],
    simp [ne_of_gt hlt] }
end

lemma dvd_content_iff_C_dvd {p : polynomial R} {r : R} : r ∣ p.content ↔ C r ∣ p :=
begin
  rw C_dvd_iff_dvd_coeff,
  split,
  { intros h i,
    apply dvd_trans h (content_dvd_coeff _) },
  { intro h,
    rw [content, finset.dvd_gcd_iff],
    intros i hi,
    apply h i }
end

lemma C_content_dvd (p : polynomial R) : C p.content ∣ p :=
dvd_content_iff_C_dvd.1 (dvd_refl _)

/-- A polynomial over a GCD domain is primitive when the `gcd` of its coefficients is 1 -/
def is_primitive (p : polynomial R) : Prop := p.content = 1

@[simp]
lemma is_primitive_one : is_primitive (1 : polynomial R) :=
by rw [is_primitive, ← C_1, content_C, normalize_one]

lemma is_primitive.ne_zero {p : polynomial R} (hp : p.is_primitive) : p ≠ 0 :=
begin
  rintro rfl,
  rw [is_primitive, content_zero] at hp,
  apply zero_ne_one hp,
end

lemma is_primitive.content_eq_one {p : polynomial R} (hp : p.is_primitive) : p.content = 1 := hp

lemma is_primitive_iff_is_unit_of_C_dvd {p : polynomial R} :
  p.is_primitive ↔ ∀ (r : R), C r ∣ p → is_unit r :=
begin
  rw [is_primitive],
  split,
  { intros h r hdvd,
    rw [← dvd_content_iff_C_dvd, h] at hdvd,
    apply is_unit_of_dvd_one _ hdvd },
  { intro h,
    rw [← normalize_content, normalize_eq_one],
    apply h _ (C_content_dvd _) }
end

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

@[simp]
lemma content_C_mul (r : R) (p : polynomial R) : (C r * p).content = normalize r * p.content :=
begin
  by_cases h0 : r = 0, { simp [h0] },
  rw content, rw content, rw ← finset.gcd_mul_left,
  refine congr (congr rfl _) _; ext; simp [h0, mem_support_iff_coeff_ne_zero]
end

lemma eq_C_mul_primitive (p : polynomial R) :
  ∃ (r : R) (q : polynomial R), p = C r * q ∧ q.is_primitive ∧ p.nat_degree = q.nat_degree :=
begin
  by_cases h0 : p = 0,
  { use [0, 1],
    simp [h0] },
  rcases C_content_dvd p with ⟨q, h⟩,
  use [p.content, q],
  refine ⟨h, _, _⟩,
  { have h1 := content_C_mul p.content q,
    rw [← h, normalize_content, ← mul_one p.content, mul_assoc, one_mul] at h1,
    apply mul_left_cancel' _ h1.symm,
    rwa ← content_eq_zero_iff at h0 },
  { rw [h, mul_eq_zero] at h0,
    classical,
    rcases (decidable.not_or_iff_and_not _ _).1 h0,
    rw [h, nat_degree_mul left right, nat_degree_C, zero_add] }
end

lemma gcd_content_eq_of_dvd_sub {a : R} {p q : polynomial R} (h : C a ∣ p - q) :
  gcd_monoid.gcd a p.content = gcd_monoid.gcd a q.content :=
begin
  rw content_eq_gcd_range_of_lt p (max p.nat_degree q.nat_degree).succ
    (lt_of_le_of_lt (le_max_left _ _) (nat.lt_succ_self _)),
  rw content_eq_gcd_range_of_lt q (max p.nat_degree q.nat_degree).succ
    (lt_of_le_of_lt (le_max_right _ _) (nat.lt_succ_self _)),
  apply finset.gcd_eq_of_dvd_sub,
  intros x hx,
  cases h with w hw,
  use w.coeff x,
  rw [← coeff_sub, hw, coeff_C_mul]
end

lemma nat_degree_sub_leading_coeff_mul_X_pow_lt {p : polynomial R} (h : 0 < p.nat_degree) :
  (p - C p.leading_coeff * X ^ p.nat_degree).nat_degree < p.nat_degree :=
begin
  have hp : p ≠ 0,
  { rintro rfl,
    rw nat_degree_zero at h,
    apply lt_irrefl _ h },
  by_cases hp' : p - C p.leading_coeff * X ^ p.nat_degree = 0,
  { rw [hp', nat_degree_zero],
    apply h },
  rw [← with_bot.coe_lt_coe, ← degree_eq_nat_degree hp,
      ← degree_eq_nat_degree hp'],
  convert degree_erase_lt hp,
  apply polynomial.ext,
  intro a,
  by_cases ha : a = p.nat_degree,
  { simp only [ha, leading_coeff, coeff_X_pow_self, mul_one, coeff_C_mul, coeff_sub, sub_self],
    symmetry,
    apply finsupp.erase_same, },
  { rw [coeff_sub, coeff_C_mul, coeff_X_pow, if_neg ha, mul_zero, sub_zero],
    symmetry,
    apply finsupp.erase_ne ha, }
end

@[simp]
theorem content_mul {p q : polynomial R} : (p * q).content = p.content * q.content :=
begin
  have h : ∀ (n : ℕ) (p q : polynomial R), (p * q).nat_degree ≤ n → (p * q).content = p.content * q.content,
  { clear p q,
    intro n,
    induction n with n hi,
    { intros p q hdeg,
      by_cases hp : p = 0, { simp [hp] },
      by_cases hq : q = 0, { simp [hq] },
      rw nat_degree_mul hp hq at hdeg,
      cases nat.eq_zero_of_add_eq_zero (nat.eq_zero_of_le_zero hdeg) with pdeg qdeg,
      rw [eq_C_of_nat_degree_eq_zero pdeg, content_C_mul, content_C] },
    { intros p q hdeg,
      by_cases hpdeg : p.nat_degree = 0,
      { rw [eq_C_of_nat_degree_eq_zero hpdeg, content_C_mul, content_C] },
      by_cases hqdeg : q.nat_degree = 0,
      { rw [eq_C_of_nat_degree_eq_zero hqdeg, mul_comm, content_C_mul, content_C, mul_comm] },
      by_cases hdeg' : (p * q).nat_degree = n.succ,
      { rcases eq_C_mul_primitive p with ⟨cp, p1, rfl, p1_prim, p1_deg⟩,
        rw [mul_assoc, content_C_mul, content_C_mul],
        rcases eq_C_mul_primitive q with ⟨cq, q1, rfl, q1_prim, q1_deg⟩,
        rw [mul_comm p1 _, mul_assoc, content_C_mul, content_C_mul, mul_comm q1 _],
        suffices h : (p1 * q1).content = p1.content * q1.content,
        { rw h, ring },
        rw [nat_degree_mul, p1_deg, q1_deg] at hdeg',
        rw p1_deg at hpdeg,
        rw q1_deg at hqdeg,
        iterate 2 { swap, intro h0,
          apply nat.succ_ne_zero n,
          rw [← hdeg', h0],
          simp },
        clear hdeg p1_deg q1_deg,
        rw [p1_prim.content_eq_one, q1_prim.content_eq_one, mul_one,
            content_eq_gcd_leading_coeff_content_sub, leading_coeff_mul, ← normalize_gcd,
            normalize_eq_one, is_unit_iff_dvd_one, gcd_comm],
        transitivity,
        apply gcd_mul_dvd_mul_gcd,
        rw [← mul_one (1 : R), ← leading_coeff_mul], apply mul_dvd_mul,
        { have h := hi (p1 - C p1.leading_coeff * X ^ p1.nat_degree) q1 (nat.le_of_lt_succ _),
          { rw [q1_prim.content_eq_one, mul_one] at h,
            rw [← p1_prim.content_eq_one, content_eq_gcd_leading_coeff_content_sub p1, ← h, sub_mul,
                gcd_comm, gcd_content_eq_of_dvd_sub],
            rw [sub_sub, add_comm, sub_add, sub_sub_cancel,
                mul_assoc, leading_coeff_mul, ring_hom.map_mul, mul_assoc],
            apply dvd_sub (dvd.intro _ rfl) (dvd.intro _ rfl) },
          { by_cases h0 : (p1 - C p1.leading_coeff * X ^ p1.nat_degree) = 0,
            { simp [h0], },
            rw [← hdeg', nat_degree_mul h0 q1_prim.ne_zero],
            apply add_lt_add_right,
            apply nat_degree_sub_leading_coeff_mul_X_pow_lt (nat.pos_of_ne_zero hpdeg) } },
        { have h := hi (q1 - C q1.leading_coeff * X ^ q1.nat_degree) p1 (nat.le_of_lt_succ _),
          { rw [p1_prim.content_eq_one, mul_one] at h,
            rw [← q1_prim.content_eq_one, content_eq_gcd_leading_coeff_content_sub q1, ← h, sub_mul,
                gcd_comm, gcd_content_eq_of_dvd_sub],
            rw [sub_sub, add_comm, sub_add, mul_comm,
                sub_sub_cancel, mul_assoc, leading_coeff_mul, ring_hom.map_mul, mul_assoc],
            apply dvd_sub (dvd.intro _ rfl) (dvd.intro _ rfl) },
          { by_cases h0 : (q1 - C q1.leading_coeff * X ^ q1.nat_degree) = 0,
            { simp [h0], },
            rw [← hdeg', nat_degree_mul h0 p1_prim.ne_zero, add_comm],
            apply add_lt_add_left,
            apply nat_degree_sub_leading_coeff_mul_X_pow_lt (nat.pos_of_ne_zero hqdeg) } } },
      { apply hi p q (nat.le_of_lt_succ (lt_of_le_of_ne hdeg hdeg')) } } },
  apply h (p * q).nat_degree _ _  (le_refl _),
end

end gcd_monoid
end polynomial
