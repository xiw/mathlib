import data.polynomial

universes u v

variables {R : Type v} {A : Type u} [semiring A] [comm_semiring R] [algebra R A]

lemma smul_pow (a : A) (r : R) (k : ℕ) : (r • a)^k = r^k • a^k :=
begin
  induction k with d hd, simp,
  rw [pow_succ, hd], rw algebra.smul_mul_assoc, simp, rw smul_smul, ring,
end
