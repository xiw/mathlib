/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson.
-/

import number_theory.arithmetic_function
import number_theory.lucas_lehmer
import ring_theory.multiplicity

/-!
# Perfect Numbers

This file proves (currently one direction of)
  Theorem 70 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

The theorem characterizes even perfect numbers.

Euclid proved that if `2 ^ (k + 1) - 1` is prime (these primes are known as Mersenne primes),
  then `2 ^ k * 2 ^ (k + 1) - 1` is perfect.

Euler proved the converse, that if `n` is even and perfect, then there exists `k` such that
  `n = 2 ^ k * 2 ^ (k + 1) - 1` and `2 ^ (k + 1) - 1` is prime.

## References
https://en.wikipedia.org/wiki/Euclid%E2%80%93Euler_theorem
-/

@[simp]
lemma succ_mersenne (k : ℕ) : mersenne k + 1 = 2 ^ k :=
begin
  rw [mersenne, ← nat.succ_eq_add_one, ← nat.pred_eq_sub_one, nat.succ_pred_eq_of_pos],
  apply pow_pos,
  dec_trivial,
end

lemma odd_mersenne_succ (k : ℕ) : ¬ 2 ∣ mersenne (k + 1) :=
begin
  rw [← even_iff_two_dvd, ← nat.even_succ, nat.succ_eq_add_one, succ_mersenne,
    even_iff_two_dvd, pow_succ],
  apply dvd.intro _ rfl,
end

namespace nat
open arithmetic_function finset
open_locale arithmetic_function big_operators

lemma sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) :=
begin
  simp only [mersenne, prime_two, divisors_prime_pow, sum_map, function.embedding.coe_fn_mk,
    pow_one, sigma_apply],
  induction k,
  { simp },
  rw [pow_succ, sum_range_succ, two_mul, k_ih, nat.add_sub_assoc],
  rw nat.succ_le_iff,
  apply pow_pos,
  dec_trivial,
end

/-- Euclid's theorem that Mersenne primes induce perfect numbers -/
theorem perfect_two_pow_mul_mersenne_of_prime {k : ℕ} (pr : (mersenne (k + 1)).prime) :
  perfect ((2 ^ k) * mersenne (k + 1)) :=
begin
  rw [perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← pow_succ, ← sigma_one_apply, mul_comm,
    is_multiplicative_sigma.map_mul_of_coprime
        (nat.prime_two.coprime_pow_of_not_dvd (odd_mersenne_succ _)),
    sigma_two_pow_eq_mersenne_succ],
  simp [pr, nat.prime_two]
end

theorem even_two_pow_mul_mersenne_of_prime {k : ℕ} (pr : (mersenne (k + 1)).prime) :
  even ((2 ^ k) * mersenne (k + 1)) :=
begin
  simp only [true_and, even_zero, not_true, ne.def, not_false_iff] with parity_simps,
  left,
  rintro rfl,
  apply nat.not_prime_one,
  revert pr,
  simp [mersenne],
end

lemma eq_two_pow_mul_odd (n : ℕ) :
  ∃ {k m : ℕ}, n = 2 ^ k * m ∧ ¬ even m :=
begin
  sorry
end

lemma sum_proper_divisors_dvd {n : ℕ} (h : ∑ x in proper_divisors n, x ∣ n) :
  ∑ x in proper_divisors n, x = 1 ∨ ∑ x in proper_divisors n, x = n :=
begin
  by_cases h0 : n = 0,
  { right,
    simp [h0] },
  by_cases h1 : n = 1,
  { contrapose h,
    simp [h1] },
  rw or_iff_not_imp_right,
  intro sn,
  have hsub : ({1 , ∑ x in proper_divisors n, x } : finset ℕ) ⊆ proper_divisors n,
  { intro x,
    simp only [mem_insert, ne.def, mem_proper_divisors, mem_singleton],
    intro hor,
    rcases hor with rfl | rfl,
    { simp only [true_and, is_unit.dvd, nat.is_unit_iff],
      omega },
    { exact ⟨h, lt_of_le_of_ne (nat.le_of_dvd (nat.pos_of_ne_zero h0) h) sn⟩ } },
  have hle := not_le_of_gt (lt_succ_self (∑ (x : ℕ) in n.proper_divisors, x)),
  contrapose! hle,
  convert finset.sum_le_sum_of_subset hsub,
  rw [sum_insert, sum_singleton, add_comm],
  rw mem_singleton,
  apply hle.symm,
end

lemma foo {m n : ℕ} (h : m ∣ n) : m + n = σ 1 n → m = 1 ∨ m = n :=
begin
  by_cases h0 : n = 0,
  { intro hadd,
    right,
    revert hadd,
    simp [h0] },
  by_cases h1 : n = 1,
  { rw h1 at h,
    simp [nat.dvd_one.1 h], },
  have hsub : ({1 , m , n} : finset ℕ) ⊆ divisors n,
  { intro x,
    simp only [mem_insert, ne.def, mem_divisors, mem_singleton, h0, and_true, not_false_iff],
    intro hor,
    rcases hor with rfl | rfl | rfl;
    simp [h] },
  contrapose!,
  rintro ⟨m1, mn⟩,
  rw sigma_one_apply,
  apply ne_of_lt (lt_of_lt_of_le _ (finset.sum_le_sum_of_subset hsub)),
  rw [sum_insert, sum_insert, sum_singleton],
  { rw add_comm 1,
    apply nat.lt_succ_self },
  { rw mem_singleton,
    apply mn },
  { rw [mem_insert],
    push_neg,
    simp [m1.symm, ((ne.def _ _).mpr h1).symm] }
end

theorem eq_two_pow_mul_mersenne_prime_of_even_perfect {n : ℕ} (he : even n) (hp : perfect n) :
  ∃ (k : ℕ), prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) :=
begin
  rcases eq_two_pow_mul_odd n with ⟨k, m, rfl, m_odd⟩,
  use k,
  simp only [even_mul, m_odd, or_false, even_pow, even_bit0, true_and] at he,
  rw [perfect_iff_sum_divisors_eq_two_mul, ← sigma_one_apply, mul_comm,
    is_multiplicative_sigma.map_mul_of_coprime
        (nat.prime_two.coprime_pow_of_not_dvd m_odd),
    sigma_two_pow_eq_mersenne_succ, mul_comm 2, mul_assoc, ← pow_succ'] at hp,
  rcases nat.coprime.dvd_of_dvd_mul_right
    (nat.prime_two.coprime_pow_of_not_dvd (odd_mersenne_succ _)) (dvd.intro_left _ hp)
    with ⟨j, rfl⟩,
  suffices h : j = 1,
  { rw [h, mul_one, eq_self_iff_true, and_true],
    rw [h, mul_one, mul_comm, ← succ_mersenne] at hp,
    have hp' := mul_left_cancel' (ne_of_gt (mersenne_pos (nat.succ_pos k))) hp,
    sorry },
  rw [mul_comm, mul_assoc] at hp,
  have hj := mul_left_cancel' (ne_of_gt (mersenne_pos (nat.succ_pos _))) hp,
  rw [← succ_mersenne, mul_add, mul_one, add_comm _ j, mul_comm, sigma_one_apply,
    sum_divisors_eq_sum_proper_divisors_add_self] at hj,
  have hj1 := nat.add_right_cancel hj,
  rw sigma_one_apply at hj,
  cases foo _ hj.symm with j1 jmer,
  { exact j1 },
  { exfalso, rw [← mul_one j, mul_assoc, one_mul] at jmer,
    apply mul_left_cancel',},
end

theorem even_perfect_iff_two_pow_mul_mersenne_prime (n : ℕ) :
  (even n ∧ perfect n) ↔ ∃ (k : ℕ), (mersenne (k + 1)).prime ∧ n = (2 ^ k) * mersenne (k + 1) :=
begin
  split,
  { rintro ⟨he, hp⟩,
    exact eq_two_pow_mul_mersenne_prime_of_even_perfect he hp },
  { rintro ⟨k, ⟨hk, rfl⟩⟩,
    exact ⟨even_two_pow_mul_mersenne_of_prime hk, perfect_two_pow_mul_mersenne_of_prime hk⟩ }
end

end nat
