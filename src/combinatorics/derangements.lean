import data.equiv.basic
import combinatorics.generating_functions

open_locale big_operators
open_locale classical

noncomputable theory

variables {m : Type} [fintype m] [decidable_eq m]

def fixed_points (σ : equiv.perm m) : finset m :=
finset.filter (λ (x : m), σ x = x) finset.univ

def is_derangement (σ : equiv.perm m) : Prop :=
fixed_points σ = ∅

variable (m)
def derangements : finset (equiv.perm m) :=
finset.filter is_derangement finset.univ

def derangement_number : ℕ → ℕ :=
λ n : ℕ, (derangements (fin n)).card

theorem sum_derangements_eq_fact (n : ℕ) :
∑ p in finset.nat.antidiagonal n, (n.choose p.fst) * derangement_number (p.snd) = n.fact :=
begin
  sorry
end

theorem derangement_recurrence :
econvolve 1 ↑derangement_number = ↑nat.fact :=
begin
  ext,
  unfold econvolve,
  simp only [mul_one, pi.one_apply],
  change ∑ (p : ℕ × ℕ) in finset.nat.antidiagonal x,
    ↑(x.choose p.fst) * ↑(derangement_number p.snd) = ↑(nat.fact x),
  rw ← sum_derangements_eq_fact x, norm_cast,
end

theorem exp_mul_egf_derangement_eq_egf_fact :
formal_exp * egf ↑derangement_number = egf ↑nat.fact :=
begin
  rw formal_exp,
  rw egf_mul, rw derangement_recurrence
end

theorem derangement_eq_partial_sums_exp_inv :
derangement_number = partial_sums (λ n : ℕ, (-1) ^ n) :=
