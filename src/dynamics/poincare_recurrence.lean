import measure_theory.measure_space

lemma equiv.perm.coe_pow {α : Type*} (e : equiv.perm α) : ∀ n : ℕ, ⇑(e ^ n) = (e^[n])
| 0 := rfl
| (n+1) := by { ext x, rw [nat.iterate_succ, pow_succ', equiv.perm.mul_apply, equiv.perm.coe_pow] }

lemma nat.iterate_mul {α : Sort*} (f : α → α) (m : ℕ) :
  ∀ n, f^[m * n] = (f^[m]^[n])
| 0 := by { ext x, simp }
| (n + 1) := by { ext x, simp [mul_add, nat.iterate_add, nat.iterate_mul n] }

lemma exists_imp_distrib' {α : Sort*} {p q : α → Prop} :
  (∃ x, p x → q x) ↔ ((∀ x, p x) → ∃ x, q x) :=
by classical; simp only [imp_iff_not_or, exists_or_distrib, not_forall]

lemma forall_imp_distrib_left {α : Sort*} {p : Prop} {q : α → Prop} [decidable p] :
  (∀ x, p → q x) ↔ (p → ∀ x, q x) :=
by simp only [imp_iff_not_or, forall_or_distrib_left]

noncomputable theory

open classical set filter measure_theory finset
open_locale classical topological_space

variables {ι : Type*} {α : Type*} {β : Type*} [measure_space α]

lemma sum_volume_le_volume_univ {s : finset ι} {t : ι → set α} (h : ∀ i ∈ s, is_measurable (t i))
  (H : pairwise_on ↑s (disjoint on t)) : s.sum (λ i, volume (t i)) ≤ volume (univ : set α) :=
volume_bUnion_finset H h ▸ volume_mono (subset_univ _)

lemma tsum_volume_le_volume_univ {s : ι → set α} (hs : ∀ i, is_measurable (s i))
  (H : pairwise (disjoint on s)) :
  (∑ i, volume (s i)) ≤ volume (univ : set α) :=
begin
  rw [ennreal.tsum_eq_supr_sum],
  exact supr_le (λ s, sum_volume_le_volume_univ (λ i hi, hs i) (λ i hi j hj hij, H i j hij))
end

/-- Pigeonhole principle for measure spaces: if `∑ i, μ (s i) > μ univ`, then
one of the intersections `s i ∩ s j` is not empty. -/
lemma exists_nonempty_inter_of_volume_univ_lt_tsum_volume {s : ι → set α}
  (hs : ∀ i, is_measurable (s i)) (H : volume (univ : set α) < ∑ i, volume (s i)) :
  ∃ i j (h : i ≠ j), (s i ∩ s j).nonempty :=
begin
  contrapose! H,
  apply tsum_volume_le_volume_univ hs,
  exact λ i j hij x hx, H i j hij ⟨x, hx⟩
end

/-- Pigeonhole principle for measure spaces: if `s` is a `finset` and
`s.sum (λ i, μ (t i)) > μ univ`, then one of the intersections `t i ∩ t j` is not empty. -/
lemma exists_nonempty_inter_of_volume_univ_lt_sum_volume {s : finset ι} {t : ι → set α}
  (h : ∀ i ∈ s, is_measurable (t i)) (H : volume (univ : set α) < s.sum (λ i, volume (t i))) :
  ∃ (i ∈ s) (j ∈ s) (h : i ≠ j), (t i ∩ t j).nonempty :=
begin
  contrapose! H,
  apply sum_volume_le_volume_univ h,
  exact λ i hi j hj hij x hx, H i hi j hj hij ⟨x, hx⟩
end

lemma measurable.iterate {f : α → α} (hf : measurable f) : ∀ n, measurable (f^[n])
| 0 := measurable_id
| (n+1) := (measurable.iterate n).comp hf

/-- A measurable self-map `f` is called `volume_preserving` if for any measurable `s`
we have `μ (f ⁻¹' s) = μ s`, or equivalently `μ.map f = μ`. -/
def volume_preserving (f : α → α) : Prop :=
measurable f ∧ ∀ ⦃s⦄, is_measurable s → volume (f ⁻¹' s) = volume s

namespace volume_preserving

variables (α) {f : α → α} {e : equiv.perm α}

protected lemma id : volume_preserving (@id α) := ⟨measurable_id, λ s hs, rfl⟩

variable {α}

protected lemma measurable (hf : volume_preserving f) : measurable f := hf.1

lemma map_volume_eq (hf : volume_preserving f) : measure_space.μ.map f = measure_space.μ :=
measure.ext $ λ s hs, by simpa only [measure.map_apply hf.measurable hs] using hf.2 hs

lemma volume_eq (hf : volume_preserving f) {s : set α} (hs : is_measurable s) :
  volume (f ⁻¹' s) = volume s :=
hf.2 hs

lemma comp (hf : volume_preserving f) {g : α → α} (hg : volume_preserving g) :
  volume_preserving (f ∘ g) :=
⟨hf.measurable.comp hg.measurable, λ s hs,
  by rw [preimage_comp, hg.volume_eq (hf.measurable s hs), hf.volume_eq hs]⟩

lemma iterate (hf : volume_preserving f) : ∀ n, volume_preserving (f^[n])
| 0 := volume_preserving.id α
| (n+1) := (iterate n).comp hf

lemma exists_mem_image_mem_of_volume_lt_mul_volume (hf : volume_preserving f) {s : set α}
  (hs : is_measurable s) {n : ℕ} (hvol : volume (univ : set α) < n * volume s) :
  ∃ (x ∈ s) (m ∈ Ioo 0 n), f^[m] x ∈ s :=
begin
  have A : ∀ m, is_measurable (f^[m] ⁻¹' s) := λ m, (hf.iterate m).measurable s hs,
  have B : ∀ m, volume (f^[m] ⁻¹' s) = volume s, from λ m, (hf.iterate m).volume_eq hs,
  have : volume (univ : set α) < (finset.range n).sum (λ m, volume (f^[m] ⁻¹' s)),
    by simpa [B, add_monoid.smul_eq_mul],
  rcases exists_nonempty_inter_of_volume_univ_lt_sum_volume (λ m hm, A m) this
    with ⟨i, hi, j, hj, hij, x, hxi, hxj⟩,
  wlog hlt : i < j := lt_or_gt_of_ne hij using [i j, j i],
  simp only [set.mem_preimage, finset.mem_range] at hi hj hxi hxj,
  refine ⟨f^[i] x, hxi, j - i, ⟨nat.sub_pos_of_lt hlt, lt_of_le_of_lt (j.sub_le i) hj⟩, _⟩,
  rwa [← nat.iterate_add, nat.sub_add_cancel (le_of_lt hlt)]
end

lemma exists_mem_image_mem (hf : volume_preserving f) {s : set α} (hs : is_measurable s)
  (hs' : volume s ≠ 0) (hvol : volume (univ : set α) ≠ ⊤) :
  ∃ (x ∈ s) (m > 0), f^[m] x ∈ s :=
begin
  rcases ennreal.exists_nat_mul_gt hs' hvol with ⟨N, hN⟩,
  rcases hf.exists_mem_image_mem_of_volume_lt_mul_volume hs hN with ⟨x, hx, m, hm, hmx⟩,
  exact ⟨x, hx, m, hm.1, hmx⟩
end

lemma is_measurable_not_recurrent (hf : measurable f) {s : set α} (hs : is_measurable s) (n : ℕ) :
  is_measurable (s ∩ ⋂ m ≥ n, f^[m] ⁻¹' -s) :=
hs.inter (is_measurable.Inter $ λ m, is_measurable.Inter_Prop $
      λ hm, (hf.iterate m).preimage hs.compl)

lemma volume_mem_forall_image_not_mem_eq_zero (hf : volume_preserving f) {s : set α}
  (hs : is_measurable s) (n : ℕ) (hvol :  volume (univ : set α) ≠ ⊤) :
  volume (s ∩ ⋂ m ≥ n, f^[m] ⁻¹' -s) = 0 :=
begin
  by_contradiction H,
  rcases exists_mem_image_mem (hf.iterate n)
    (is_measurable_not_recurrent hf.measurable hs n) H hvol
    with ⟨x, ⟨hxs, hxs'⟩, m, m0, ⟨hmx, hmx'⟩⟩,
  simp only [← nat.iterate_mul, set.mem_inter_iff, set.mem_Inter, set.mem_preimage] at hxs' hmx,
  exact hxs' (n * m) (nat.le_mul_of_pos_right m0) hmx
end

/-- Poincaré recurrence theorem: given a volume preserving map `f` and a measurable set `s`,
almost every point `x ∈ s`-/
lemma ae_set_recurrent (hf : volume_preserving f) {s : set α} (hs : is_measurable s)
  (hvol : volume (univ : set α) ≠ ⊤) :
  ∀ₘ x, x ∈ s → ∃ᶠ n in at_top, (f^[n] x) ∈ s :=
begin
  simp only [frequently_at_top, forall_imp_distrib_left.symm, all_ae_all_iff],
  intro n,
  have := volume_zero_iff_all_ae_nmem.1 (hf.volume_mem_forall_image_not_mem_eq_zero hs n hvol),
  refine this.mono (λ x, _),
  simp [not_forall]
end

end volume_preserving
