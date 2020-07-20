/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson, Jalex Stark.
-/
import data.matrix.basic
import linear_algebra.matrix
import data.polynomial
import linear_algebra.determinant
import linear_algebra.basic

universes u v
variables {m : Type u} {R : Type v} [fintype m]

def sym_matrix (M : matrix m m R) : Prop :=
  M = M.transpose

lemma sym_matrix_apply {M : matrix m m R} (h : sym_matrix M) (i j : m):
  M i j = M j i :=
by { unfold sym_matrix at h, conv_rhs {rw h}, refl, }


section ugh

variables {A : Type u} [semiring A] [comm_semiring R] [algebra R A]

@[simp] lemma smul_pow (a : A) (r : R) (k : ℕ) : (r • a)^k = r^k • a^k :=
begin
  induction k with d hd, simp,
  rw [pow_succ, hd], rw algebra.smul_mul_assoc, simp, rw smul_smul, ring,
end

end ugh

variables [semiring R]

variables (m) (R)
def matrix_J : matrix m m R :=
  λ (i j : m), (1 : R)
variables {m} {R}

@[simp] lemma matrix_J_apply (i j : m) : (matrix_J m R) i j = (1 : R) := rfl

lemma trace_J (m:Type*) [fintype m] :
  matrix.trace m R R (matrix_J m R) = fintype.card m :=
by rw [matrix.trace, matrix_J, fintype.card]; simp
