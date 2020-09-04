import data.finsupp
import data.real.basic
import ring_theory.power_series

open_locale big_operators

noncomputable theory

section ogf

variable {R : Type}

def ogf [comm_semiring R] (a : ℕ → R) : power_series R := power_series.mk a

@[simp]
lemma ogf_coeff [comm_semiring R] {n : ℕ} {a : ℕ → R} :
(power_series.coeff R n) (ogf a) = a n := by { unfold ogf, simp }

def convolve [comm_semiring R] (a b : ℕ → R) : ℕ → R :=
λ (n : ℕ), ∑ (p : ℕ × ℕ) in (finset.nat.antidiagonal n), (a p.fst) * (b p.snd)

theorem ogf_mul [comm_semiring R] (a b : ℕ → R) :
(ogf a) * (ogf b) = ogf (convolve a b) :=
begin
  ext, unfold ogf, unfold convolve, rw power_series.coeff_mul, simp
end

end ogf

section partial_sums

def partial_sums (a : ℕ → ℝ) : ℕ → ℝ :=
λ (n : ℕ), (finset.range (n + 1)).sum a

theorem sum_ones_inv (R : Type*) [field R] :
(1 - power_series.X) * (ogf (1 : ℕ → R)) = 1 :=
begin
  rw sub_mul, rw one_mul, ext, simp only [add_monoid_hom.map_sub, pi.one_apply, power_series.coeff_one, ogf_coeff],
  cases n, rw if_pos rfl, simp,
  rw nat.succ_eq_add_one, rw mul_comm, simp
end

--Rule 5ish
theorem ogf_partial_sums (a : ℕ → ℝ) :
ogf (partial_sums a) = (ogf 1) * (ogf a) := sorry

end partial_sums

def div_by_fact (a : ℕ → ℝ) : ℕ → ℝ :=
λ n : ℕ, a n / nat.fact n

def egf (a : ℕ → ℝ) : power_series ℝ :=
ogf (div_by_fact a)

def formal_exp : power_series ℝ := egf 1

def econvolve (a b : ℕ → ℝ) : ℕ → ℝ :=
λ (n : ℕ), ∑ (p : ℕ × ℕ) in (finset.nat.antidiagonal n),
(nat.choose n p.fst) * (a p.fst) * (b p.snd)

lemma econvolve_to_convolve (a b : ℕ → ℝ) :
div_by_fact (econvolve a b) = convolve (div_by_fact a) (div_by_fact b) :=
begin
  unfold div_by_fact, unfold convolve, unfold econvolve,
  ext,
  symmetry,
  rw eq_div_iff_mul_eq, swap, rw nat.cast_ne_zero, apply nat.fact_ne_zero,
  rw finset.sum_mul,
  sorry,
end

--Rule 3'
theorem egf_mul (a b : ℕ → ℝ) :
(egf a) * (egf b) = egf (econvolve a b) :=
begin
  unfold egf, rw ogf_mul, rw econvolve_to_convolve
end

lemma formal_exp_inv :
formal_exp.inv = egf (λ n : ℕ, (-1) ^ n) := sorry

lemma egf_fact :
egf ↑nat.fact = ogf 1 :=
begin
  unfold egf, unfold div_by_fact, ext, simp only [pi.one_apply, ogf_coeff],
  symmetry, rw eq_div_iff_mul_eq, rw one_mul, refl,
  rw nat.cast_ne_zero, apply nat.fact_ne_zero
end
