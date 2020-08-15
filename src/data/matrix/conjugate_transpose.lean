import data.complex.basic
import data.fintype.basic
import data.matrix.basic
import linear_algebra.determinant
import linear_algebra.nonsingular_inverse
import tactic

-- TODO: rename conjugate_transpose to conjugate_transpose

noncomputable theory
open_locale classical
open_locale matrix
open_locale big_operators

universes u u'
variables {m n l : Type u} [fintype m] [fintype n] [fintype l]

local notation `Euc` := (n → ℂ)

namespace matrix
/-- Complex conjugate of a vector.-/
def conj (M : matrix m n ℂ) : matrix m n ℂ :=
λ i j, complex.conj (M i j)

@[simp]
lemma conj_val (M : matrix m n ℂ) (i j) : conj M i j = complex.conj (M i j) := rfl

def conjugate_transpose (M : matrix m n ℂ) : matrix n m ℂ :=
M.transpose.conj
end matrix

section conjugate_transpose
open complex matrix
/--
  Tell `simp` what the entries are in a transposed matrix.
-/
@[simp] lemma conjugate_transpose_val (M : matrix m n ℂ) (i j) : M.conjugate_transpose j i = complex.conj (M i j) := rfl

@[simp] lemma conjugate_transpose_transpose (M : matrix m n ℂ) :
  M.conjugate_transpose.conjugate_transpose = M :=
by ext; simp

@[simp] lemma conjugate_transpose_zero : (0 : matrix m n ℂ).conjugate_transpose = 0 :=
by ext; simp

@[simp] lemma conjugate_transpose_one [decidable_eq n] : (1 : matrix n n ℂ).conjugate_transpose = 1 :=
sorry
-- by ext; simp [matrix.one_val]; split_ifs; simp; cc

@[simp] lemma conjugate_transpose_add (M : matrix m n ℂ) (N : matrix m n ℂ) :
  (M + N).conjugate_transpose = M.conjugate_transpose + N.conjugate_transpose  :=
by ext; simp

@[simp] lemma conjugate_transpose_neg (M : matrix m n ℂ) :
  (- M).conjugate_transpose = - M.conjugate_transpose  :=
by ext; simp

@[simp] lemma conjugate_transpose_sub (M : matrix m n ℂ) (N : matrix m n ℂ) :
  (M - N).conjugate_transpose = M.conjugate_transpose - N.conjugate_transpose  :=
by ext; simp

@[simp] lemma conjugate_transpose_mul (M : matrix m n ℂ) (N : matrix n l ℂ) :
  (M ⬝ N).conjugate_transpose = N.conjugate_transpose ⬝ M.conjugate_transpose  :=
begin
  ext; simp, delta matrix.mul, delta matrix.dot_product, simp,
  -- rw add_monoid_hom.map_sum, -- I think this would work if re were a bundled hom
  {sorry},
  {sorry}
end

@[simp] lemma conjugate_transpose_smul (c : ℂ) (M : matrix m n ℂ) :
  (c • M).conjugate_transpose = complex.conj c • M.conjugate_transpose :=
by ext; simp

lemma det_complex_conj {M : matrix n n ℂ} :
  M.conj.det = M.det.conj :=
sorry

@[simp]
lemma det_conjugate_transpose {M : matrix n n ℂ} :
M.conjugate_transpose.det = complex.conj (M.det) :=
by {unfold matrix.conjugate_transpose, rw [det_complex_conj, matrix.det_transpose]}

end conjugate_transpose
