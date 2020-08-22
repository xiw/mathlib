import data.fintype.basic
import data.fin
import linear_algebra.basis
import linear_algebra.determinant
import linear_algebra.nonsingular_inverse
import data.matrix.conjugate_transpose
import data.matrix.dot_product
import tactic

noncomputable theory
open_locale classical
open_locale matrix

universes u u'
variables {m n l : Type*} [fintype m] [fintype n] [fintype l]
variables {k : ℕ}

section unitary

def matrix.unitary (A : matrix n n ℂ) :=
  A ⬝ (A.conjugate_transpose) = 1
open matrix

lemma unit_det_of_unitary {A : matrix n n ℂ} (hu : A.unitary) : is_unit A.det :=
begin
  have := matrix.det_mul A A.conjugate_transpose,
  unfold matrix.unitary at hu,
  rw [hu, matrix.det_one] at this,
  exact is_unit_of_mul_eq_one A.det A.conjugate_transpose.det (eq.symm this),
end

lemma unit_of_unitary {A : matrix n n ℂ} (hu : A.unitary) : is_unit A :=
  (matrix.is_unit_iff_is_unit_det A).mpr (unit_det_of_unitary hu)

lemma unitary_inv {A : matrix n n ℂ} (hu : A.unitary) : A⁻¹ = A.conjugate_transpose :=
begin
  unfold unitary at hu,
  calc A⁻¹ = A⁻¹ ⬝ 1 : by simp
  ... = A⁻¹ ⬝ (A ⬝ A.conjugate_transpose) : by rw ← hu
  ... = (A⁻¹ ⬝ A) ⬝ A.conjugate_transpose : by simp[matrix.mul_assoc]
  ... = 1 ⬝ A.conjugate_transpose : by rw ← nonsing_inv_mul A (unit_det_of_unitary hu)
  ... = A.conjugate_transpose : by simp,
end


lemma unitary_of_complex_transpose {A : matrix n n ℂ} (hu : A.unitary) : A.conjugate_transpose.unitary :=
begin
  calc A.conjugate_transpose ⬝ A.conjugate_transpose.conjugate_transpose = A.conjugate_transpose ⬝ A : by rw conjugate_transpose_transpose A
       ... = A⁻¹ ⬝ A : by rw unitary_inv hu
       ... = 1 : by rw ← nonsing_inv_mul A (unit_det_of_unitary hu),
  end


lemma unit_of_complex_transpose {A : matrix n n ℂ} (hu : A.unitary) : is_unit A.conjugate_transpose :=
begin
  exact unit_of_unitary (unitary_of_complex_transpose hu),
end

lemma unitary.has_mul {A B : matrix n n ℂ} (hA : A.unitary) (hB : B.unitary) :
  (A ⬝ B).unitary :=
begin
  unfold matrix.unitary at *,
  rw [conjugate_transpose_mul, matrix.mul_assoc, ← matrix.mul_assoc B], simp [hA, hB]
end

lemma unitary.has_one : (1 : matrix n n ℂ).unitary := by simp [matrix.unitary]
include n

instance unitary_group : group $ subtype $ unitary :=
{ mul := begin
  rintros ⟨A, hA⟩ ⟨B, hB⟩, refine ⟨A ⬝ B, _⟩, exact n, apply_instance, apply unitary.has_mul; assumption,
end,
  mul_assoc := sorry,
  one := ⟨1, unitary.has_one⟩,
  one_mul := sorry,
  mul_one := sorry,
  inv := sorry,
  mul_left_inv := sorry }

#check ite
theorem rows_of_unitary {A : matrix n n ℂ} :
  A.unitary ↔
  ∀ i j : n,
  (vector.complex_dot_product (A i) (A i) = 1) ∧
  (i ≠ j → (vector.complex_dot_product (A i) (A j) = 0))
:=
begin
  unfold matrix.unitary,
  rw ← ext_iff,
  unfold matrix.mul,
  unfold matrix.conjugate_transpose,
  unfold conj,
  unfold transpose,
  unfold vector.complex_dot_product,
  unfold vector.conj,
  split,
  intros hu i j,
  simp [hu],
  exact one_apply_ne, -- Why is this needed? This is already a simp lemma
  intros hu i j,
  specialize hu i j,
  cases hu with hp hq,
  by_cases h : i = j,
  rw ← h,
  rw one_apply_eq,
  simp [hp],
  rw one_apply_ne h,
  apply hq,
  exact h,
end

lemma extension_unitary_of_unitary {k : ℕ} (A : matrix (fin k) (fin k) ℂ) (a : ℝ):
  A.unitary → (A.extension a).unitary :=
sorry

theorem unitary_of_unit_vector [linear_order n] [has_zero n] (v : n → ℂ) :
  vector.complex_norm v = 1 →
  ∃ A : matrix n n ℂ,
  A.unitary ∧
  (A 0) = v :=
sorry

end unitary
