import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.Eilenberg
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.DistanceCoareaLower
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


/-!
# Measurability of Level-Set Hausdorff Measure

For a Lipschitz function `f : E n → ℝ` and a measurable bounded set `B`,
the function `s ↦ μHE[n-1](B ∩ f⁻¹{s})` is `AEMeasurable`.

## Proof route

1. **Compact case** (`levelSetMeasure_compact_measurable`): For compact `K`,
   the function is Borel measurable. This is a standard GMT fact
   (Federer §2.2.15; Mattila §6).

2. **Null set case** (`nullSet_levelSets_ae_zero`): If `volume N = 0`, then
   `μHE[n-1](N ∩ f⁻¹{s}) = 0` for a.e. `s`. Proof: approximate N from outside
   by open sets O_m with volume(O_m) → 0. Each open set is an increasing
   union of compact sets, so H_{O_m} is measurable (by the compact case).
   By Eilenberg, ∫ H_{O_m} ≤ C * volume(O_m) → 0. Fatou's lemma gives a
   measurable majorant g = liminf H_{O_m} with ∫ g = 0, hence g = 0 a.e.,
   and H_N ≤ g implies H_N = 0 a.e.

3. **Extension to measurable sets** (`levelSetMeasure_aemeasurable`):
   Approximate B from within by increasing compact sets K_m. H_{K_m} is
   measurable and H_{K_m} ↑ H_{B_∞}. The remainder B \ B_∞ has volume zero,
   so its level-set measure is zero a.e. (by step 2). Hence H_B = H_{B_∞}
   a.e., so H_B is AEMeasurable.

## Main result

- `levelSetMeasure_aemeasurable`
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ} [Nonempty (Fin n)]

/-- Every open set in `E n` is a countable union of an increasing sequence
of compact sets. -/
lemma open_compact_cover {O : Set (E n)} (hO : IsOpen O) :
    ∃ (K : ℕ → Set (E n)), (∀ j, IsCompact (K j)) ∧
      (∀ j, K j ⊆ K (j + 1)) ∧ (⋃ j, K j = O) ∧ (∀ j, K j ⊆ O) := by
  rcases hO.exists_iUnion_isClosed with ⟨F, hF_closed, hF_sub, hF_union, hF_mono⟩
  let K := fun j => F j ∩ closedBall (0 : E n) (j : ℝ)
  have hK_comp : ∀ j, IsCompact (K j) := by
    intro j
    have h2 : IsCompact (closedBall (0 : E n) (j : ℝ)) := ProperSpace.isCompact_closedBall (0 : E n) (j : ℝ)
    have h3 : IsCompact (closedBall (0 : E n) (j : ℝ) ∩ F j) := h2.inter_right (hF_closed j)
    have h4 : K j = closedBall (0 : E n) (j : ℝ) ∩ F j := by
      ext x; simp [K]; tauto
    rw [h4]; exact h3
  have hK_mono : ∀ j, K j ⊆ K (j + 1) := by
    intro j x hx
    have h3 : x ∈ F j := hx.1
    have h4 : x ∈ closedBall (0 : E n) (j : ℝ) := hx.2
    have h5 : x ∈ F (j + 1) := hF_mono (by linarith) h3
    have h4' : ‖x‖ ≤ (j : ℝ) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using h4
    have h6' : ‖x‖ ≤ ((j : ℝ) + 1) := by linarith
    have h6 : x ∈ closedBall (0 : E n) (↑(j + 1) : ℝ) := by
      have h_eq : (↑(j + 1) : ℝ) = (j : ℝ) + 1 := by simp
      rw [h_eq]
      simpa [Metric.mem_closedBall, dist_zero_right] using h6'
    exact ⟨h5, h6⟩
  have hK_sub : ∀ j, K j ⊆ O := by
    intro j x hx; exact hF_sub j hx.1
  have hK_union : ⋃ j, K j = O := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩; exact hK_sub j hj
    · intro hx
      have h1 : x ∈ ⋃ j, F j := by rw [hF_union]; exact hx
      rcases Set.mem_iUnion.mp h1 with ⟨j1, hj1⟩
      obtain ⟨j2, hj2⟩ := exists_nat_ge ‖x‖
      let j := max j1 j2
      have h3 : x ∈ F j := hF_mono (by exact le_max_left j1 j2) hj1
      have h_j2_le_j : (j2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast le_max_right j1 j2
      have h4 : x ∈ closedBall (0 : E n) (j : ℝ) := by
        simpa [Metric.mem_closedBall, dist_zero_right] using le_trans hj2 h_j2_le_j
      exact ⟨j, ⟨h3, h4⟩⟩
  exact ⟨K, hK_comp, hK_mono, hK_union, hK_sub⟩

/-- The set `{s | K ∩ f⁻¹{s} ⊆ U}` is open for compact `K`, continuous `f`,
and open `U`. -/
lemma levelSet_subset_open {n : ℕ} [Nonempty (Fin n)]
    {K : Set (E n)} (hK : IsCompact K)
    {f : E n → ℝ} (hf : Continuous f)
    {U : Set (E n)} (hU : IsOpen U) :
    IsOpen {s : ℝ | K ∩ f ⁻¹' {s} ⊆ U} := by
  have h1 : {s : ℝ | K ∩ f ⁻¹' {s} ⊆ U} = (f '' (K \ U))ᶜ := by
    ext s
    simp only [Set.mem_compl_iff, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro h
      intro h2
      rcases h2 with ⟨x, hx, rfl⟩
      have h3 : x ∈ K ∩ f ⁻¹' {f x} := ⟨hx.1, by simp⟩
      exact hx.2 (h h3)
    · intro h x hx
      by_contra h7
      have h8 : x ∈ K \ U := ⟨hx.1, h7⟩
      exact h ⟨x, h8, hx.2⟩
  rw [h1]
  have h2 : IsCompact (K \ U) := hK.diff hU
  have h3 : IsCompact (f '' (K \ U)) := h2.image hf
  exact h3.isClosed.isOpen_compl

/-- Enlarge a bounded set `E_set` to an open set `U` with controlled diameter and
`d`-th power of diameter. -/
lemma enlarge_set {n : ℕ} [Nonempty (Fin n)] {d : ℝ} (hd : 0 < d)
    {E_set : Set (E n)} (hE : ediam E_set ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ (U : Set (E n)), IsOpen U ∧ E_set ⊆ U ∧
      ediam U ≤ ediam E_set + ENNReal.ofReal ε ∧
      (ediam U)^d ≤ (ediam E_set)^d + ENNReal.ofReal ε := by
  by_cases hE_empty : E_set = ∅
  · rw [hE_empty]
    refine ⟨∅, isOpen_empty, by simp, ?_, ?_⟩
    · simp
    · simp [ENNReal.zero_rpow_of_pos hd] <;> exact bot_le
  have hE_nonempty : E_set.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
  let x : ℝ := (ediam E_set).toReal
  have hx : 0 ≤ x := by positivity
  have h_cont : ContinuousAt (fun t : ℝ => t ^ d) x :=
    (Real.continuous_rpow_const (by linarith)).continuousAt
  have h_nhds : ∀ᶠ (t : ℝ) in nhds x, t ^ d < x ^ d + ε := by
    have h1 : Set.Iio (x ^ d + ε) ∈ nhds (x ^ d) := Iio_mem_nhds (by linarith)
    have h2 : {t : ℝ | t ^ d < x ^ d + ε} ∈ nhds x := h_cont h1
    filter_upwards [h2] with t ht
    exact ht
  rcases Metric.mem_nhds_iff.mp h_nhds with ⟨δ', hδ'_pos, h2⟩
  let δ := min (δ' / 4) (ε / 4)
  have hδ_pos : 0 < δ := by positivity
  have h2δ_ltδ' : 2 * δ < δ' := by
    have h : δ ≤ δ' / 4 := min_le_left _ _
    linarith
  have h2δ_le_ε : 2 * δ ≤ ε := by
    have h : δ ≤ ε / 4 := min_le_right _ _
    linarith
  have h3 : (x + 2 * δ) ^ d < x ^ d + ε := by
    have h4 : dist (x + 2 * δ) x = 2 * δ := by
      rw [Real.dist_eq]
      have h5 : (x + 2 * δ) - x = 2 * δ := by ring
      rw [h5, abs_of_pos (by linarith)]
    have h5 : dist (x + 2 * δ) x < δ' := by rw [h4]; exact h2δ_ltδ'
    exact h2 h5
  let U : Set (E n) := Metric.thickening δ E_set
  have hU_open : IsOpen U := Metric.isOpen_thickening
  have hE_sub : E_set ⊆ U := by
    intro y hy
    exact Metric.mem_thickening_iff.mpr ⟨y, hy, by simp [hδ_pos]⟩
  have h_pair : ∀ (y z : E n), y ∈ U → z ∈ U →
      edist y z ≤ ediam E_set + ENNReal.ofReal (2 * δ) := by
    intro y z hy hz
    rcases Metric.mem_thickening_iff.mp hy with ⟨a, ha, hya_dist⟩
    rcases Metric.mem_thickening_iff.mp hz with ⟨b, hb, hzb_dist⟩
    have h6 : edist y a < ENNReal.ofReal δ := by
      rw [edist_dist]
      have h_iff : ENNReal.ofReal (dist y a) < ENNReal.ofReal δ ↔ dist y a < δ :=
        ENNReal.ofReal_lt_ofReal_iff hδ_pos
      exact h_iff.mpr hya_dist
    have h7 : edist z b < ENNReal.ofReal δ := by
      rw [edist_dist]
      have h_iff : ENNReal.ofReal (dist z b) < ENNReal.ofReal δ ↔ dist z b < δ :=
        ENNReal.ofReal_lt_ofReal_iff hδ_pos
      exact h_iff.mpr hzb_dist
    have h8 : edist a b ≤ ediam E_set := Metric.edist_le_ediam_of_mem ha hb
    have h9 : edist y z ≤ edist y a + edist a b + edist b z := by
      calc edist y z
        ≤ edist y a + edist a z := edist_triangle _ _ _
      _ ≤ edist y a + (edist a b + edist b z) := by gcongr <;> exact edist_triangle _ _ _
      _ = edist y a + edist a b + edist b z := by ring
    have h10 : edist y z ≤ ENNReal.ofReal δ + ediam E_set + ENNReal.ofReal δ := by
      calc edist y z
        ≤ edist y a + edist a b + edist b z := h9
      _ ≤ ENNReal.ofReal δ + ediam E_set + ENNReal.ofReal δ := by
        have h7' : edist b z ≤ ENNReal.ofReal δ := by rw [edist_comm]; exact h7.le
        exact add_le_add (add_le_add h6.le h8) h7'
    have h11 : ENNReal.ofReal δ + ediam E_set + ENNReal.ofReal δ = ediam E_set + ENNReal.ofReal (2 * δ) := by
      have h12 : ENNReal.ofReal δ + ENNReal.ofReal δ = ENNReal.ofReal (2 * δ) := by
        have h : ENNReal.ofReal δ + ENNReal.ofReal δ = ENNReal.ofReal (δ + δ) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        rw [h]
        have h2 : δ + δ = 2 * δ := by ring
        rw [h2]
      calc
        ENNReal.ofReal δ + ediam E_set + ENNReal.ofReal δ
          = ediam E_set + (ENNReal.ofReal δ + ENNReal.ofReal δ) := by abel
      _ = ediam E_set + ENNReal.ofReal (2 * δ) := by rw [h12]
    rw [h11] at h10
    exact h10
  have h_diam : ediam U ≤ ediam E_set + ENNReal.ofReal (2 * δ) := by
    have h_pair' : ∀ x ∈ U, ∀ y ∈ U, edist x y ≤ ediam E_set + ENNReal.ofReal (2 * δ) := by
      intro x hx y hy
      exact h_pair x y hx hy
    exact Metric.ediam_le h_pair'
  have h_diam2 : ediam U ≤ ediam E_set + ENNReal.ofReal ε := by
    calc ediam U
      ≤ ediam E_set + ENNReal.ofReal (2 * δ) := h_diam
    _ ≤ ediam E_set + ENNReal.ofReal ε := by gcongr <;> linarith
  have h_rpow_ofReal : ∀ (y : ℝ), 0 ≤ y → (ENNReal.ofReal y)^d = ENNReal.ofReal (y ^ d) := by
    intro y hy
    exact ENNReal.ofReal_rpow_of_nonneg hy (le_of_lt hd)
  have h_cost : (ediam U)^d ≤ (ediam E_set)^d + ENNReal.ofReal ε := by
    have h6 : ediam U ≤ ediam E_set + ENNReal.ofReal (2 * δ) := h_diam
    have h7 : (ediam U)^d ≤ (ediam E_set + ENNReal.ofReal (2 * δ))^d := by gcongr
    have h8 : ediam E_set + ENNReal.ofReal (2 * δ) = ENNReal.ofReal (x + 2 * δ) := by
      rw [← ENNReal.ofReal_toReal hE, ← ENNReal.ofReal_add (by positivity) (by positivity)] <;> ring
    rw [h8] at h7
    have h_nonneg : 0 ≤ x + 2 * δ := by linarith [hx, hδ_pos]
    have h9 : (ENNReal.ofReal (x + 2 * δ))^d = ENNReal.ofReal ((x + 2 * δ)^d) :=
      h_rpow_ofReal (x + 2 * δ) h_nonneg
    rw [h9] at h7
    have h10 : 0 ≤ (x + 2 * δ)^d := by positivity
    have h11 : 0 ≤ x ^ d + ε := by positivity
    have h12 : ENNReal.ofReal ((x + 2 * δ)^d) ≤ ENNReal.ofReal (x ^ d + ε) := by
      exact ENNReal.ofReal_le_ofReal h3.le
    have h13 : (ediam E_set)^d = ENNReal.ofReal (x ^ d) := by
      have h14 : ediam E_set = ENNReal.ofReal x := by rw [ENNReal.ofReal_toReal hE]
      rw [h14]
      exact h_rpow_ofReal x hx
    have h15 : ENNReal.ofReal (x ^ d + ε) = (ediam E_set)^d + ENNReal.ofReal ε := by
      rw [h13, ← ENNReal.ofReal_add (by positivity) (by positivity)] <;> ring
    rw [h15] at h12
    exact h7.trans h12
  exact ⟨U, hU_open, hE_sub, h_diam2, h_cost⟩

/-- **Compact-case level-set measurability.**

For compact `K` and continuous `f`, the function
`s ↦ μHE[n-1](K ∩ f⁻¹{s})` is Borel measurable.

Proof using countable basis approximation: the Hausdorff measure of a compact
set equals the supremum over scales of the infimum over finite covers by finite
unions of basis open sets. Since the family of such covers is countable and the
covering condition defines an open set in `s`, the resulting function is
Borel measurable.

References:
- Federer, *Geometric Measure Theory*, §2.2.15
- Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, §6
-/
lemma levelSetMeasure_compact_measurable (hn : 2 ≤ n)
    {K : Set (E n)} (hK : IsCompact K)
    {f : E n → ℝ} (hf : Continuous f) :
    Measurable fun s : ℝ => μHE[n - 1] (K ∩ f ⁻¹' {s}) := by
  let d : ℝ := ↑(n - 1)
  have h1 : 0 < n - 1 := by omega
  have hd_pos : 0 < d := by
    have h2 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h1
    simpa [d] using h2
  classical
  -- Countable basis
  have h_basis : ∃ (β : Set (Set (E n))), β.Countable ∧ TopologicalSpace.IsTopologicalBasis β := by
    have h_main : ∃ (b : Set (Set (E n))), b.Countable ∧ ∅ ∉ b ∧ TopologicalSpace.IsTopologicalBasis b :=
      TopologicalSpace.exists_countable_basis (E n)
    rcases h_main with ⟨β, hβ_count, _, hβ_basis⟩
    exact ⟨β, hβ_count, hβ_basis⟩
  rcases h_basis with ⟨β, hβ_count, hβ_basis⟩
  have hβ_nonempty : β.Nonempty := by
    have h_univ : ⋃₀ β = Set.univ := hβ_basis.sUnion_eq
    have h_ne : (⋃₀ β).Nonempty := by rw [h_univ]; exact Set.univ_nonempty
    rcases Set.nonempty_sUnion.mp h_ne with ⟨s, hs, _⟩
    exact ⟨s, hs⟩
  rcases hβ_count.exists_eq_range hβ_nonempty with ⟨eβ, hβ_range⟩
  have heβ_surj : ∀ i : ℕ, eβ i ∈ β := by
    intro i
    have h : eβ i ∈ Set.range eβ := Set.mem_range_self i
    exact hβ_range.symm ▸ h
  -- Choice function: for B ∈ β, pick idxβ B such that eβ (idxβ B) = B
  let idxβ : Set (E n) → ℕ := fun B =>
    if h : B ∈ β then Classical.choose (Set.mem_range.mp (hβ_range ▸ h)) else 0
  have h_idxβ : ∀ {B : Set (E n)}, B ∈ β → eβ (idxβ B) = B := by
    intro B hB
    simp [idxβ, hB]
    exact Classical.choose_spec (Set.mem_range.mp (hβ_range ▸ hB))
  -- ℱ = finite unions of basis elements, indexed by Finset ℕ
  let ℱ : Set (Set (E n)) := Set.range (fun (T : Finset ℕ) => ⋃ i ∈ T, eβ i)
  have hℱ_count : ℱ.Countable := Set.countable_range _
  have hℱ_union : ∀ F ∈ ℱ, ∃ (S : Finset (Set (E n))), (∀ B ∈ S, B ∈ β) ∧ F = ⋃ B ∈ S, B := by
    intro F hF
    rcases Set.mem_range.mp hF with ⟨T, rfl⟩
    let S : Finset (Set (E n)) := T.image eβ
    have hS_in : ∀ B ∈ S, B ∈ β := by
      intro B hB
      rcases Finset.mem_image.mp hB with ⟨i, _, rfl⟩
      exact heβ_surj i
    refine ⟨S, hS_in, ?_⟩
    ext x
    simp only [S, Set.mem_iUnion, Finset.mem_image]
    constructor
    · rintro ⟨i, hi, hx⟩
      exact ⟨eβ i, ⟨i, hi, rfl⟩, hx⟩
    · rintro ⟨B, ⟨i, hi, rfl⟩, hx⟩
      exact ⟨i, hi, hx⟩
  have hℱ_nonempty : ℱ.Nonempty := ⟨∅, by
    simp [ℱ]
    <;> exact ⟨∅, by simp⟩⟩
  rcases hℱ_count.exists_eq_range hℱ_nonempty with ⟨e, hℱ_range⟩
  have he_surj : ∀ {F : Set (E n)}, F ∈ ℱ → ∃ (n : ℕ), e n = F := by
    intro F hF
    have : F ∈ Set.range e := by
      exact hℱ_range ▸ hF
    exact Set.mem_range.mp this
  -- Define h_r(A): infimum over finite ℱ-covers with diam ≤ r
  let h : ENNReal → Set (E n) → ENNReal := fun r A =>
    ⨅ (T : Finset ℕ),
      let S := T.image e
      if (A ⊆ ⋃ F ∈ S, F) ∧ (∀ F ∈ S, ediam F ≤ r)
      then ∑ F ∈ S, (ediam F)^d else ⊤
  -- h_r(A) equals infimum over finite ℱ-covers
  have h_h_def : ∀ (r : ENNReal) (A : Set (E n)),
      h r A = ⨅ (S : Finset (Set (E n))) (_ : ∀ F ∈ S, F ∈ ℱ) (_ : A ⊆ ⋃ F ∈ S, F) (_ : ∀ F ∈ S, ediam F ≤ r),
        ∑ F ∈ S, (ediam F)^d := by
    intro r A
    simp only [h]
    let f : Finset ℕ → ENNReal := fun T =>
      let S := T.image e
      if (A ⊆ ⋃ F ∈ S, F) ∧ (∀ F ∈ S, ediam F ≤ r)
      then ∑ F ∈ S, (ediam F)^d else ⊤
    let g : Finset (Set (E n)) → ENNReal := fun S =>
      ⨅ (hS1 : ∀ F ∈ S, F ∈ ℱ) (hS2 : A ⊆ ⋃ F ∈ S, F) (hS3 : ∀ F ∈ S, ediam F ≤ r),
        ∑ F ∈ S, (ediam F)^d
    have h_main1 : (⨅ T, f T) ≤ (⨅ S, g S) := by
      apply le_iInf
      intro S
      apply le_iInf
      intro hS1
      apply le_iInf
      intro hS2
      apply le_iInf
      intro hS3
      choose n hn using fun (F : {x // x ∈ S}) => he_surj (hS1 F.val F.property)
      let T : Finset ℕ := Finset.image n S.attach
      have hT_eq : T.image e = S := by
        ext F
        simp only [T, Finset.mem_image, Finset.mem_attach, true_and]
        constructor
        · rintro ⟨i, ⟨F', rfl⟩, h_e⟩
          have h_eq : e (n F') = F'.val := hn F'
          rw [h_eq] at h_e
          exact h_e ▸ F'.property
        · intro hF
          let F' : {x // x ∈ S} := ⟨F, hF⟩
          have h2 : e (n F') = F := hn F'
          exact ⟨n F', ⟨F', rfl⟩, h2⟩
      have hcond : (A ⊆ ⋃ F ∈ T.image e, F) ∧ (∀ F ∈ T.image e, ediam F ≤ r) := by
        rw [hT_eq] <;> exact ⟨hS2, hS3⟩
      have h_fT : f T = ∑ F ∈ S, (ediam F)^d := by
        dsimp only [f]
        have h : (let S' := T.image e; if (A ⊆ ⋃ F ∈ S', F) ∧ (∀ F ∈ S', ediam F ≤ r) then ∑ F ∈ S', (ediam F)^d else ⊤) =
            ∑ F ∈ T.image e, (ediam F)^d := by
          dsimp only
          rw [if_pos hcond]
        rw [h, hT_eq]
      have h_iInf_le : (⨅ T, f T) ≤ f T := iInf_le _ T
      rw [h_fT] at h_iInf_le
      exact h_iInf_le
    have h_main2 : (⨅ S, g S) ≤ (⨅ T, f T) := by
      apply le_iInf
      intro T
      let S := T.image e
      have hS1 : ∀ F ∈ S, F ∈ ℱ := by
        intro F hF
        rcases Finset.mem_image.mp hF with ⟨n, _, rfl⟩
        have h : e n ∈ Set.range e := Set.mem_range_self n
        rw [←hℱ_range] at h
        exact h
      by_cases hcond : (A ⊆ ⋃ F ∈ S, F) ∧ (∀ F ∈ S, ediam F ≤ r)
      · have h_gS : g S ≤ ∑ F ∈ S, (ediam F)^d := by
          dsimp only [g]
          have h1 := iInf_le (fun (hS1 : ∀ F ∈ S, F ∈ ℱ) =>
            ⨅ (hS2 : A ⊆ ⋃ F ∈ S, F), ⨅ (hS3 : ∀ F ∈ S, ediam F ≤ r), ∑ F ∈ S, (ediam F)^d) hS1
          have h2 := iInf_le (fun (hS2 : A ⊆ ⋃ F ∈ S, F) =>
            ⨅ (hS3 : ∀ F ∈ S, ediam F ≤ r), ∑ F ∈ S, (ediam F)^d) hcond.1
          have h3 := iInf_le (fun (hS3 : ∀ F ∈ S, ediam F ≤ r) => ∑ F ∈ S, (ediam F)^d) hcond.2
          exact h1.trans h2 |>.trans h3
        have h_fT : f T = ∑ F ∈ S, (ediam F)^d := by
          dsimp only [f]
          rw [if_pos hcond]
        have h_iInf_le : (⨅ S, g S) ≤ g S := iInf_le _ S
        rw [h_fT]
        exact h_iInf_le.trans h_gS
      · have h_fT : f T = ⊤ := by
          dsimp only [f]
          rw [if_neg hcond]
        rw [h_fT]
        exact le_top
    exact le_antisymm h_main1 h_main2
  -- Monotonicity: h is decreasing in r (larger r = more covers = smaller infimum)
  have h_mono : ∀ (r1 r2 : ENNReal), r1 ≤ r2 → ∀ (A : Set (E n)), h r2 A ≤ h r1 A := by
    intro r1 r2 hle A
    simp only [h]
    apply iInf_mono
    intro T
    let S := T.image e
    by_cases hcond1 : (A ⊆ ⋃ F ∈ S, F) ∧ (∀ F ∈ S, ediam F ≤ r1)
    · have hcond2 : (A ⊆ ⋃ F ∈ S, F) ∧ (∀ F ∈ S, ediam F ≤ r2) := by
        exact ⟨hcond1.1, fun F hF => le_trans (hcond1.2 F hF) hle⟩
      rw [if_pos hcond2, if_pos hcond1]
    · rw [if_neg hcond1]
      by_cases hcond2 : (A ⊆ ⋃ F ∈ S, F) ∧ (∀ F ∈ S, ediam F ≤ r2)
      · rw [if_pos hcond2]; exact le_top
      · rw [if_neg hcond2]
  -- Step 1: h_r(A_s) is measurable in s
  have h1 : ∀ (r : ENNReal), Measurable (fun s : ℝ => h r (K ∩ f ⁻¹' {s})) := by
    intro r
    have h2 : ∀ (T : Finset ℕ), Measurable (fun s : ℝ =>
        let S := T.image e
        if (K ∩ f ⁻¹' {s} ⊆ ⋃ F ∈ S, F) ∧ (∀ F ∈ S, ediam F ≤ r)
        then ∑ F ∈ S, (ediam F)^d else ⊤) := by
      intro T
      let S := T.image e
      let U := ⋃ F ∈ S, F
      have hU_open : IsOpen U := by
        have h_all_open : ∀ F ∈ S, IsOpen F := by
          intro F hF
          have hF_in_ℱ : F ∈ ℱ := by
            rcases Finset.mem_image.mp hF with ⟨n, _, rfl⟩
            have h : e n ∈ Set.range e := Set.mem_range_self n
            rwa [hℱ_range]
          rcases hℱ_union F hF_in_ℱ with ⟨S', hS'_β, rfl⟩
          have hB_open : ∀ B ∈ S', IsOpen B := fun B hB => hβ_basis.isOpen (hS'_β B hB)
          exact isOpen_biUnion hB_open
        exact isOpen_biUnion h_all_open
      have h3 : IsOpen {s : ℝ | K ∩ f ⁻¹' {s} ⊆ U} :=
        levelSet_subset_open hK hf hU_open
      have h4 : MeasurableSet {s : ℝ | K ∩ f ⁻¹' {s} ⊆ U} := h3.measurableSet
      let c : ENNReal := ∑ F ∈ S, (ediam F)^d
      by_cases h5 : (∀ F ∈ S, ediam F ≤ r)
      · have h6 : (fun s : ℝ => (if (K ∩ f ⁻¹' {s} ⊆ U) ∧ (∀ F ∈ S, ediam F ≤ r) then c else ⊤)) =
            fun s : ℝ => if K ∩ f ⁻¹' {s} ⊆ U then c else ⊤ := by
          funext s
          by_cases h8 : K ∩ f ⁻¹' {s} ⊆ U
          · have h9 : (K ∩ f ⁻¹' {s} ⊆ U) ∧ (∀ F ∈ S, ediam F ≤ r) := ⟨h8, h5⟩
            rw [if_pos h9, if_pos h8]
          · have h10 : ¬((K ∩ f ⁻¹' {s} ⊆ U) ∧ (∀ F ∈ S, ediam F ≤ r)) := by
              intro h; exact h8 h.1
            rw [if_neg h10, if_neg h8]
        rw [h6]
        exact Measurable.ite h4 measurable_const measurable_const
      · have h6 : (fun s : ℝ => (if (K ∩ f ⁻¹' {s} ⊆ U) ∧ (∀ F ∈ S, ediam F ≤ r) then c else ⊤)) = fun _ => ⊤ := by
          funext s
          have h7 : ¬((K ∩ f ⁻¹' {s} ⊆ U) ∧ (∀ F ∈ S, ediam F ≤ r)) := by
            intro h
            exact h5 h.2
          rw [if_neg h7]
        rw [h6]
        exact measurable_const
    simpa [h] using Measurable.iInf h2
  -- Step 2: Hausdorff pre-measure ≤ h_r(A)
  let pre_m : ENNReal → Set (E n) → ENNReal := fun r A =>
    ⨅ (t : ℕ → Set (E n)) (_ : A ⊆ ⋃ (i : ℕ), t i) (_ : ∀ i, ediam (t i) ≤ r),
      ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ d
  have h_hausdorff : ∀ (A : Set (E n)), μH[d] A = ⨆ (r : ENNReal) (_ : 0 < r), pre_m r A :=
    MeasureTheory.Measure.hausdorffMeasure_apply d
  have h2 : ∀ (r : ENNReal) (A : Set (E n)), pre_m r A ≤ h r A := by
    intro r A
    rw [h_h_def r A]
    apply le_iInf
    intro S
    apply le_iInf
    intro hS1
    apply le_iInf
    intro hS2
    apply le_iInf
    intro hS3
    let e : Fin S.card ≃ {x // x ∈ S} := (Finset.equivFin (s := S)).symm
    let g : Fin S.card → Set (E n) := fun j => (e j : Set (E n))
    let t : ℕ → Set (E n) := fun n => if h : n < S.card then g ⟨n, h⟩ else ∅
    have hg_mem : ∀ (j : Fin S.card), g j ∈ S := fun j => (e j).property
    have hg_surj : ∀ (F : Set (E n)), F ∈ S → ∃ (j : Fin S.card), g j = F := by
      intro F hF
      let j : Fin S.card := e.symm ⟨F, hF⟩
      have h : g j = F := by
        dsimp only [g]
        have h2 : e j = ⟨F, hF⟩ := e.apply_symm_apply ⟨F, hF⟩
        rw [h2]
        <;> rfl
      exact ⟨j, h⟩
    have hg_inj : Function.Injective g := by
      intro j1 j2 h
      have h' : e j1 = e j2 := by
        apply Subtype.ext
        exact h
      exact e.injective h'
    have ht_cover : A ⊆ ⋃ (i : ℕ), t i := by
      intro x hx
      have h4 : x ∈ ⋃ F ∈ S, F := hS2 hx
      have h5 : ∃ F ∈ S, x ∈ F := by simpa [Finset.mem_biUnion] using h4
      rcases h5 with ⟨F, hF, hxF⟩
      rcases hg_surj F hF with ⟨j, hj⟩
      have h6 : t (j : ℕ) = F := by simp [t, g, hj, Fin.is_lt]
      exact Set.mem_iUnion.mpr ⟨(j : ℕ), by rw [h6] <;> exact hxF⟩
    have ht_diam : ∀ i, ediam (t i) ≤ r := by
      intro i
      by_cases h : i < S.card
      · have h4 : t i = g ⟨i, h⟩ := by simp [t, h]
        rw [h4]
        exact hS3 (g ⟨i, h⟩) (hg_mem ⟨i, h⟩)
      · simp [t, h] <;> exact bot_le
    have h_term_all : ∀ (i : ℕ), i < S.card →
        (⨆ _ : (t i).Nonempty, ediam (t i) ^ d) = (ediam (t i))^d := by
      intro i hi
      by_cases hne : (t i).Nonempty
      · simp [hne]
      · have h_empty : t i = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using hne
        rw [h_empty]
        simp [ENNReal.zero_rpow_of_pos hd_pos]
    have h_term_empty : ∀ (i : ℕ), i ≥ S.card →
        (⨆ _ : (t i).Nonempty, ediam (t i) ^ d) = 0 := by
      intro i hi
      have h4 : t i = ∅ := by simp [t, not_lt.mpr hi]
      rw [h4]
      simp
    let f : ℕ → ENNReal := fun i => ⨆ _ : (t i).Nonempty, ediam (t i) ^ d
    have h_support : ∀ i, i ∉ Finset.range S.card → f i = 0 := by
      intro i hi
      exact h_term_empty i (by simpa [Finset.mem_range] using hi)
    have h_tsum_eq : ∑' i, f i = ∑ i ∈ Finset.range S.card, f i := by
      have h_bdd : ∀ (s : Finset ℕ), ∑ i ∈ s, f i ≤ ∑ i ∈ Finset.range S.card, f i := by
        intro s
        have h_eq : ∑ i ∈ s, f i = ∑ i ∈ s.filter (· ∈ Finset.range S.card), f i := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i _
          by_cases h3 : i ∈ Finset.range S.card
          · simp [h3]
          · have h4 : f i = 0 := h_support i h3
            simp [h3, h4]
        rw [h_eq]
        have h_sub : s.filter (· ∈ Finset.range S.card) ⊆ Finset.range S.card := by
          intro i hi
          exact (Finset.mem_filter.mp hi).2
        have h_final : ∑ i ∈ s.filter (· ∈ Finset.range S.card), f i ≤ ∑ i ∈ Finset.range S.card, f i := by
          exact Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => by positivity)
        exact h_final
      have h1 : ∑' i, f i ≤ ∑ i ∈ Finset.range S.card, f i := by
        rw [ENNReal.tsum_eq_iSup_sum]
        apply iSup_le
        exact h_bdd
      have h2 : ∑ i ∈ Finset.range S.card, f i ≤ ∑' i, f i := ENNReal.sum_le_tsum (Finset.range S.card)
      exact le_antisymm h1 h2
    have h_cost : ∑' i, f i ≤ ∑ F ∈ S, (ediam F)^d := by
      rw [h_tsum_eq]
      have h6 : ∑ i ∈ Finset.range S.card, f i = ∑ i ∈ Finset.range S.card, (ediam (t i))^d := by
        apply Finset.sum_congr rfl
        intro i hi
        exact h_term_all i (Finset.mem_range.mp hi)
      rw [h6]
      have h7 : ∑ i ∈ Finset.range S.card, (ediam (t i))^d = ∑ j : Fin S.card, (ediam (g j))^d := by
        let val_emb : Fin S.card ↪ ℕ := ⟨fun j => j.val, fun j1 j2 h => Fin.ext h⟩
        have h_img_val : Finset.image val_emb Finset.univ = Finset.range S.card := by
          ext x
          simp only [Finset.mem_image, Finset.mem_univ, Finset.mem_range]
          constructor
          · rintro ⟨j, _, rfl⟩
            exact Fin.is_lt j
          · intro hx
            refine ⟨⟨x, hx⟩, by simp, rfl⟩
        have h_eq1 : ∑ j : Fin S.card, (ediam (g j))^d = ∑ i ∈ Finset.image val_emb Finset.univ, (ediam (t i))^d := by
          have h2 : ∑ j : Fin S.card, (ediam (g j))^d = ∑ j : Fin S.card, (ediam (t (val_emb j)))^d := by
            apply Finset.sum_congr rfl
            intro j _
            have hlt : j.val < S.card := Fin.is_lt j
            have h9 : t j.val = g j := by simp [t, hlt]
            have h10 : val_emb j = j.val := by rfl
            simp [h9, h10]
          rw [h2]
          let s : Finset (Fin S.card) := Finset.univ
          have h_inj : Set.InjOn val_emb (↑s : Set (Fin S.card)) := fun x _ y _ h => val_emb.inj' h
          let g' : ℕ → ENNReal := fun i => (ediam (t i))^d
          exact (Finset.sum_image h_inj : ∑ i ∈ Finset.image val_emb s, g' i = ∑ j ∈ s, g' (val_emb j)).symm
        rw [h_eq1, h_img_val]
      rw [h7]
      have h_img : Finset.image g Finset.univ = S := by
        ext F
        simp only [Finset.mem_image, Finset.mem_univ]
        constructor
        · rintro ⟨j, _, rfl⟩
          exact hg_mem j
        · intro hF
          rcases hg_surj F hF with ⟨j, hj⟩
          refine ⟨j, trivial, hj⟩
      have h8 : ∑ j : Fin S.card, (ediam (g j))^d = ∑ F ∈ S, (ediam F)^d := by
        have h10 : ∑ j : Fin S.card, (ediam (g j))^d = ∑ F ∈ Finset.image g Finset.univ, (ediam F)^d := by
          rw [Finset.sum_image] <;> exact fun x _ y _ hxy => hg_inj hxy
        rw [h10, h_img]
      rw [h8]
    have h_pre_le : pre_m r A ≤ ∑' i, f i := by
      simp only [pre_m]
      let f1 : (ℕ → Set (E n)) → ENNReal := fun t' =>
        ⨅ (_ : A ⊆ ⋃ (i : ℕ), t' i), ⨅ (_ : ∀ i, ediam (t' i) ≤ r), ∑' i, ⨆ _ : (t' i).Nonempty, ediam (t' i) ^ d
      have h1 : (⨅ t', f1 t') ≤ f1 t := iInf_le f1 t
      let f2 : (A ⊆ ⋃ (i : ℕ), t i) → ENNReal := fun _ =>
        ⨅ (_ : ∀ i, ediam (t i) ≤ r), ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ d
      have h2 : f1 t ≤ f2 ht_cover := iInf_le f2 ht_cover
      let f3 : (∀ i, ediam (t i) ≤ r) → ENNReal := fun _ => ∑' i, f i
      have h3 : f2 ht_cover ≤ f3 ht_diam := iInf_le f3 ht_diam
      exact h1.trans h2 |>.trans h3
    exact h_pre_le.trans h_cost
  -- Step 3: approximation: h_{r+ε}(B) ≤ pre_m r B + ε for compact B
  have h3 : ∀ (r : ENNReal), r ≠ ⊤ → ∀ (ε : ℝ), 0 < ε → ∀ (B : Set (E n)), IsCompact B →
      h (r + ENNReal.ofReal ε) B ≤ pre_m r B + ENNReal.ofReal ε := by
    intro r hr ε hε B hB
    by_cases h_top : pre_m r B = ⊤
    · rw [h_top]; simp
    · have h_pre_ne_top : pre_m r B ≠ ⊤ := h_top
      have h_pre_lt_top : pre_m r B < ⊤ := lt_of_le_of_ne le_top h_pre_ne_top
      have h_b_lt_top : pre_m r B + ENNReal.ofReal ε < ⊤ :=
        ENNReal.add_lt_top.mpr ⟨h_pre_lt_top, ENNReal.ofReal_lt_top⟩
      apply ENNReal.le_of_forall_pos_le_add
      intro δ hδ h_b_top
      let C : ENNReal := pre_m r B + ↑δ
      have hC_lt : pre_m r B < C := by
        have h_pos : (0 : ENNReal) < ↑δ := by exact_mod_cast hδ
        have h_ne_zero : (↑δ : ENNReal) ≠ 0 := ne_of_gt h_pos
        exact ENNReal.lt_add_right h_pre_ne_top h_ne_zero
      have h_exists_cover : ∃ (t : ℕ → Set (E n)), (B ⊆ ⋃ (i : ℕ), t i) ∧ (∀ i, ediam (t i) ≤ r) ∧
          (∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ d) < C := by
        have h : ∃ (t : ℕ → Set (E n)), (∀ i, ediam (t i) ≤ r) ∧ (B ⊆ ⋃ (i : ℕ), t i) ∧
            (∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ d) < C := by
          simpa [pre_m, iInf_lt_iff] using hC_lt
        rcases h with ⟨t, h1, h2, h3⟩
        exact ⟨t, h2, h1, h3⟩
      rcases h_exists_cover with ⟨t, ht_cover, ht_diam, ht_cost⟩
      -- Enlarge each nonempty t i with ε / 2^(i+1) additional cost
      have h_enlarge : ∀ i : ℕ, ∃ (U : Set (E n)), IsOpen U ∧ t i ⊆ U ∧
          ediam U ≤ ediam (t i) + ENNReal.ofReal ε ∧
          (ediam U)^d ≤ (ediam (t i))^d + ENNReal.ofReal (ε / 2 ^ (i + 1)) := by
        intro i
        by_cases h_empty : (t i).Nonempty
        · have h_ediam_ne_top : ediam (t i) ≠ ⊤ := by
            have h : ediam (t i) ≤ r := ht_diam i
            intro h2
            rw [h2] at h
            simp at h <;> tauto
          rcases enlarge_set hd_pos h_ediam_ne_top (show 0 < ε / 2 ^ (i + 1) by positivity)
            with ⟨U, hU_open, hU_sub, hU_diam1, hU_cost⟩
          have hU_diam2 : ediam U ≤ ediam (t i) + ENNReal.ofReal ε := by
            have h_le : ENNReal.ofReal (ε / 2 ^ (i + 1)) ≤ ENNReal.ofReal ε := by
              have h : ε / 2 ^ (i + 1) ≤ ε := by
                apply div_le_self (by linarith)
                have h2 : (1 : ℝ) ≤ 2 ^ (i + 1) := by
                  have h3 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
                  have h4 : (1 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ (i + 1) := by gcongr
                  have h5 : (1 : ℝ) ^ (i + 1) = (1 : ℝ) := by simp
                  rw [h5] at h4
                  exact h4
                exact h2
              gcongr
            calc ediam U
              ≤ ediam (t i) + ENNReal.ofReal (ε / 2 ^ (i + 1)) := hU_diam1
            _ ≤ ediam (t i) + ENNReal.ofReal ε := by gcongr
          exact ⟨U, hU_open, hU_sub, hU_diam2, hU_cost⟩
        · have h_ti_empty : t i = ∅ := by
            simpa [Set.not_nonempty_iff_eq_empty] using h_empty
          have h_ediam_zero : ediam (∅ : Set (E n)) = 0 := by simp
          have h_zero : (ediam (∅ : Set (E n)))^d = 0 := by
            rw [h_ediam_zero]
            exact ENNReal.zero_rpow_of_pos hd_pos
          refine ⟨∅, isOpen_empty, by simp [h_ti_empty], by simp, ?_⟩
          rw [h_ti_empty, h_zero]
          <;> exact le_add_right le_rfl
      choose U hU_open hU_sub hU_diam hU_cost using h_enlarge
      have hU_cover : B ⊆ ⋃ (i : ℕ), U i := by
        intro x hx
        rcases Set.mem_iUnion.mp (ht_cover hx) with ⟨i, hi⟩
        exact Set.mem_iUnion.mpr ⟨i, hU_sub i hi⟩
      -- Geometric series: ∑' i, ε / 2^(i+1) = ε
      have h_geom_real : ∑' i : ℕ, (ε / 2 ^ (i + 1)) = ε := by
        have h9 : (fun i : ℕ => ε / 2 ^ (i + 1)) = fun i : ℕ => ε / 2 / 2 ^ i := by
          funext i; ring
        rw [h9]
        exact tsum_geometric_two' ε
      have h_summable : Summable (fun i : ℕ => ε / 2 ^ (i + 1)) := by
        have h9 : (fun i : ℕ => ε / 2 ^ (i + 1)) = fun i : ℕ => ε / 2 / 2 ^ i := by
          funext i; ring
        rw [h9]
        exact summable_geometric_two' ε
      have h_geom_ennreal : ∑' i : ℕ, ENNReal.ofReal (ε / 2 ^ (i + 1)) = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) h_summable, h_geom_real]
      -- Cost bound for U i
      have h_sum_cost : ∑' i, (ediam (U i))^d ≤
          (∑' i, (ediam (t i))^d) + ENNReal.ofReal ε := by
        have h1 : ∑' i, (ediam (U i))^d ≤ ∑' i, ((ediam (t i))^d + ENNReal.ofReal (ε / 2 ^ (i + 1))) :=
          ENNReal.tsum_le_tsum hU_cost
        have h2 : ∑' i, ((ediam (t i))^d + ENNReal.ofReal (ε / 2 ^ (i + 1))) =
            (∑' i, (ediam (t i))^d) + ∑' i, ENNReal.ofReal (ε / 2 ^ (i + 1)) := by
          exact ENNReal.tsum_add
        calc ∑' i, (ediam (U i))^d
          ≤ ∑' i, ((ediam (t i))^d + ENNReal.ofReal (ε / 2 ^ (i + 1))) := h1
        _ = (∑' i, (ediam (t i))^d) + ∑' i, ENNReal.ofReal (ε / 2 ^ (i + 1)) := h2
        _ = (∑' i, (ediam (t i))^d) + ENNReal.ofReal ε := by rw [h_geom_ennreal]
      have h4 : ∑' i, (ediam (t i))^d = ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ d := by
        apply tsum_congr
        intro i
        by_cases h : (t i).Nonempty
        · simp [h]
        · have h_ti_empty : t i = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h
          have h5 : (⨆ _ : (t i).Nonempty, ediam (t i) ^ d) = 0 := by
            rw [h_ti_empty]
            simp
          have h6 : (ediam (t i))^d = 0 := by
            rw [h_ti_empty]
            have h_ediam_empty : ediam (∅ : Set (E n)) = 0 := by simp
            rw [h_ediam_empty]
            exact ENNReal.zero_rpow_of_pos hd_pos
          rw [h5, h6]
      rw [h4] at h_sum_cost
      have h7 : (∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ d) ≤ C := ht_cost.le
      have h_sum_cost2 : ∑' i, (ediam (U i))^d ≤ C + ENNReal.ofReal ε := by
        calc ∑' i, (ediam (U i))^d
          ≤ (∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ d) + ENNReal.ofReal ε := h_sum_cost
        _ ≤ C + ENNReal.ofReal ε := by gcongr
      -- Finite subcover
      rcases hB.elim_finite_subcover U hU_open hU_cover with ⟨I, hI_cover⟩
      -- For each x ∈ B, choose i ∈ I and basis Bx ⊆ U i containing x
      have h_choice : ∀ (x : E n), x ∈ B → ∃ (i : ℕ), i ∈ I ∧ ∃ (Bx : Set (E n)), Bx ∈ β ∧ x ∈ Bx ∧ Bx ⊆ U i := by
        intro x hx
        have h2 : x ∈ ⋃ i ∈ I, U i := hI_cover hx
        have h2' : ∃ i ∈ I, x ∈ U i := by simpa [Finset.mem_biUnion] using h2
        rcases h2' with ⟨i, hi, hxi⟩
        have h_nhds : U i ∈ nhds x := IsOpen.mem_nhds (hU_open i) hxi
        have h3 : ∃ (Bx : Set (E n)), Bx ∈ β ∧ x ∈ Bx ∧ Bx ⊆ U i :=
          hβ_basis.mem_nhds_iff.mp h_nhds
        exact ⟨i, hi, h3⟩
      choose idx hidx Bx hBx_in hBx_x hBx_sub using h_choice
      let B' : E n → Set (E n) := fun x => if h : x ∈ B then Bx x h else Set.univ
      have hB'_in : ∀ x ∈ B, B' x ∈ β := by
        intro x hx
        simpa [B', dif_pos hx] using hBx_in x hx
      have hB'_sub : ∀ (x : E n) (hx : x ∈ B), B' x ⊆ U (idx x hx) := by
        intro x hx
        simpa [B', dif_pos hx] using hBx_sub x hx
      have h_cover2 : B ⊆ ⋃ (y : {x // x ∈ B}), B' y.val := by
        intro x hx
        have hB'_eq : B' x = Bx x hx := by simp [B', hx]
        have h : x ∈ B' x := by
          rw [hB'_eq]
          exact hBx_x x hx
        exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, h⟩
      have hB'_open : ∀ (x : {x // x ∈ B}), IsOpen (B' x.val) := by
        intro x
        have h : B' x.val ∈ β := hB'_in x.val x.property
        exact hβ_basis.isOpen h
      rcases hB.elim_finite_subcover (fun x : {x // x ∈ B} => B' x.val) hB'_open h_cover2 with ⟨s, hs⟩
      -- For each i ∈ I, let F i = union of B' x where idx x = i
      let F : ℕ → Set (E n) := fun i =>
        ⋃ (x : {x // x ∈ B}) (_ : x ∈ s ∧ idx x.val x.property = i), B' x.val
      have hF_in_ℱ : ∀ i, F i ∈ ℱ := by
        intro i
        let S_i : Finset {x // x ∈ B} := s.filter (fun x => idx x.val x.property = i)
        let S_basis : Finset (Set (E n)) := S_i.image (fun x => B' x.val)
        have hS_basis_in_β : ∀ B ∈ S_basis, B ∈ β := by
          intro B hB
          rcases Finset.mem_image.mp hB with ⟨x, _, rfl⟩
          exact hB'_in x.val x.property
        let T : Finset ℕ := S_basis.image idxβ
        have hF_eq : F i = ⋃ B ∈ S_basis, B := by
          ext y
          constructor
          · intro hy
            rcases Set.mem_iUnion.mp hy with ⟨x, h2⟩
            have hP : x ∈ s ∧ idx x.val x.property = i := by
              by_cases h : x ∈ s ∧ idx x.val x.property = i
              · exact h
              · have h_empty : (⋃ (_ : x ∈ s ∧ idx x.val x.property = i), B' x.val) = ∅ := by simp [h]
                rw [h_empty] at h2; simpa using h2
            have h3 : y ∈ B' x.val := by simpa [hP] using h2
            have hx_in_Si : x ∈ S_i := by
              simp only [S_i, Finset.mem_filter] <;> exact hP
            have hB_in_Sbasis : B' x.val ∈ S_basis := Finset.mem_image.mpr ⟨x, hx_in_Si, rfl⟩
            simpa [Finset.mem_biUnion] using ⟨B' x.val, hB_in_Sbasis, h3⟩
          · intro hy
            have h : ∃ (B : Set (E n)), B ∈ S_basis ∧ y ∈ B := by
              simpa [Finset.mem_biUnion] using hy
            rcases h with ⟨B, hB_in_S, hyB⟩
            rcases Finset.mem_image.mp hB_in_S with ⟨x, hx_in_Si, rfl⟩
            have hP : x ∈ s ∧ idx x.val x.property = i := by
              simp only [S_i, Finset.mem_filter] at hx_in_Si <;> exact hx_in_Si
            have h4 : y ∈ (⋃ (_ : x ∈ s ∧ idx x.val x.property = i), B' x.val) := by
              simp [hP] <;> exact hyB
            exact Set.mem_iUnion.mpr ⟨x, h4⟩
        have h_main : (⋃ B ∈ S_basis, B) = ⋃ k ∈ T, eβ k := by
          ext y
          constructor
          · intro hy
            have h : ∃ (B : Set (E n)), B ∈ S_basis ∧ y ∈ B := by
              simpa [Finset.mem_biUnion] using hy
            rcases h with ⟨B, hB_in_S, hyB⟩
            have hB_in_β : B ∈ β := hS_basis_in_β B hB_in_S
            have h_k_in_T : idxβ B ∈ T := Finset.mem_image.mpr ⟨B, hB_in_S, rfl⟩
            have h_eq : eβ (idxβ B) = B := h_idxβ hB_in_β
            have h_y_in : y ∈ eβ (idxβ B) := by
              rw [h_eq]
              exact hyB
            simpa [Finset.mem_biUnion] using ⟨idxβ B, h_k_in_T, h_y_in⟩
          · intro hy
            have h : ∃ (k : ℕ), k ∈ T ∧ y ∈ eβ k := by
              simpa [Finset.mem_biUnion] using hy
            rcases h with ⟨k, hk_in_T, hyk⟩
            rcases Finset.mem_image.mp hk_in_T with ⟨B, hB_in_S, rfl⟩
            have hB_in_β : B ∈ β := hS_basis_in_β B hB_in_S
            have h_eq : eβ (idxβ B) = B := h_idxβ hB_in_β
            have hyk' : y ∈ B := by
              simpa [h_eq] using hyk
            simpa [Finset.mem_biUnion] using ⟨B, hB_in_S, hyk'⟩
        have h_final : F i = ⋃ k ∈ T, eβ k := by
          rw [hF_eq, h_main]
        exact ⟨T, h_final.symm⟩
      have hF_sub : ∀ i, F i ⊆ U i := by
        intro i y hy
        rcases Set.mem_iUnion.mp hy with ⟨x, h2⟩
        have hP : x ∈ s ∧ idx x.val x.property = i := by
          by_cases h : x ∈ s ∧ idx x.val x.property = i
          · exact h
          · have h_empty : (⋃ (_ : x ∈ s ∧ idx x.val x.property = i), B' x.val) = ∅ := by
              simp [h]
            rw [h_empty] at h2
            simpa using h2
        have h3 : y ∈ B' x.val := by
          simpa [hP] using h2
        have h4 : B' x.val ⊆ U i := by
          have h5 : B' x.val ⊆ U (idx x.val x.property) := hB'_sub x.val x.property
          have h6 : idx x.val x.property = i := hP.2
          rw [h6] at h5
          exact h5
        exact h4 h3
      have hF_cover : B ⊆ ⋃ i ∈ I, F i := by
        intro y hy
        have h7 : ∃ (x : {x // x ∈ B}), x ∈ s ∧ y ∈ B' x.val := by
          simpa [Finset.mem_biUnion] using hs hy
        rcases h7 with ⟨x, hx1, hyB⟩
        let i := idx x.val x.property
        have hi : i ∈ I := hidx x.val x.property
        have h_eq : idx x.val x.property = i := by rfl
        have hP : x ∈ s ∧ idx x.val x.property = i := ⟨hx1, h_eq⟩
        have h9 : y ∈ (⋃ (_ : x ∈ s ∧ idx x.val x.property = i), B' x.val) := by
          simp [hP] <;> exact hyB
        have h8 : y ∈ F i := Set.mem_iUnion.mpr ⟨x, h9⟩
        simpa using ⟨i, hi, h8⟩
      -- Cost and diameter bounds
      let S_F : Finset (Set (E n)) := I.image F
      have hS_F_in_ℱ : ∀ F' ∈ S_F, F' ∈ ℱ := by
        intro F' hF'
        rcases Finset.mem_image.mp hF' with ⟨i, hi, rfl⟩
        exact hF_in_ℱ i
      have hS_F_cover : B ⊆ ⋃ F' ∈ S_F, F' := by
        simpa [S_F] using hF_cover
      have hS_F_diam : ∀ F' ∈ S_F, ediam F' ≤ r + ENNReal.ofReal ε := by
        intro F' hF'
        rcases Finset.mem_image.mp hF' with ⟨i, hi, rfl⟩
        have h9 : ediam (F i) ≤ ediam (U i) := by
          gcongr <;> exact hF_sub i
        calc ediam (F i)
          ≤ ediam (U i) := h9
        _ ≤ ediam (t i) + ENNReal.ofReal ε := hU_diam i
        _ ≤ r + ENNReal.ofReal ε := by gcongr <;> exact ht_diam i
      have hS_F_cost : ∑ F' ∈ S_F, (ediam F')^d ≤ C + ENNReal.ofReal ε := by
        classical
        have h_choose : ∀ (y : Set (E n)), y ∈ S_F → ∃ (i : ℕ), i ∈ I ∧ F i = y := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
          exact ⟨i, hi, rfl⟩
        choose i hiI hiEq using h_choose
        let i' : Set (E n) → ℕ := fun y => if h : y ∈ S_F then i y h else 0
        have h_inj : Set.InjOn i' (S_F : Set (Set (E n))) := by
          intro y1 hy1 y2 hy2 h
          have h1 : i' y1 = i y1 hy1 := by
            dsimp only [i']
            split_ifs with h
            · rfl
            · contradiction
          have h2 : i' y2 = i y2 hy2 := by
            dsimp only [i']
            split_ifs with h
            · rfl
            · contradiction
          rw [h1, h2] at h
          have h3 : F (i y1 hy1) = y1 := hiEq y1 hy1
          have h4 : F (i y2 hy2) = y2 := hiEq y2 hy2
          rw [h] at h3
          rw [h3] at h4
          exact h4
        let S_i : Finset ℕ := S_F.image i'
        have hS_i_sub : S_i ⊆ I := by
          intro z hz
          rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
          have h_i'_eq : i' y = i y hy := by simp [i', hy]
          rw [h_i'_eq]
          exact hiI y hy
        have h_eq1 : ∑ y ∈ S_F, (ediam y)^d = ∑ z ∈ S_i, (ediam (F z))^d := by
          rw [Finset.sum_image h_inj]
          <;> apply Finset.sum_congr rfl
          intro y hy
          have h_i'_val : i' y = i y hy := by simp [i', hy]
          rw [h_i'_val]
          have h_eq_F : F (i y hy) = y := hiEq y hy
          exact congr_arg (fun x : Set (E n) => (ediam x)^d) h_eq_F.symm
        calc ∑ F' ∈ S_F, (ediam F')^d
          = ∑ z ∈ S_i, (ediam (F z))^d := h_eq1
        _ ≤ ∑ i ∈ I, (ediam (F i))^d := Finset.sum_le_sum_of_subset_of_nonneg hS_i_sub (fun _ _ _ => bot_le)
        _ ≤ ∑ i ∈ I, (ediam (U i))^d := by
          apply Finset.sum_le_sum
          intro i _
          have h10 : ediam (F i) ≤ ediam (U i) := by gcongr <;> exact hF_sub i
          have h11 : (ediam (F i))^d ≤ (ediam (U i))^d := by
            gcongr
          exact h11
        _ ≤ ∑' i, (ediam (U i))^d := by
          exact ENNReal.sum_le_tsum I
        _ ≤ C + ENNReal.ofReal ε := h_sum_cost2
      -- Therefore h (r + ε) B ≤ C + ε = pre_m r B + ε + δ
      have h_final : h (r + ENNReal.ofReal ε) B ≤ C + ENNReal.ofReal ε := by
        rw [h_h_def (r + ENNReal.ofReal ε) B]
        let g : Finset (Set (E n)) → ENNReal := fun S =>
          ⨅ (hS1 : ∀ F ∈ S, F ∈ ℱ) (hS2 : B ⊆ ⋃ F ∈ S, F) (hS3 : ∀ F ∈ S, ediam F ≤ r + ENNReal.ofReal ε),
            ∑ F ∈ S, (ediam F)^d
        have h1 : (⨅ S, g S) ≤ g S_F := iInf_le g S_F
        let g1 : (∀ F ∈ S_F, F ∈ ℱ) → ENNReal := fun hS1 =>
          ⨅ (hS2 : B ⊆ ⋃ F ∈ S_F, F) (hS3 : ∀ F ∈ S_F, ediam F ≤ r + ENNReal.ofReal ε),
            ∑ F ∈ S_F, (ediam F)^d
        have h2 : g S_F ≤ g1 hS_F_in_ℱ := iInf_le g1 hS_F_in_ℱ
        let g2 : (B ⊆ ⋃ F ∈ S_F, F) → ENNReal := fun hS2 =>
          ⨅ (hS3 : ∀ F ∈ S_F, ediam F ≤ r + ENNReal.ofReal ε), ∑ F ∈ S_F, (ediam F)^d
        have h3 : g1 hS_F_in_ℱ ≤ g2 hS_F_cover := iInf_le g2 hS_F_cover
        have h4 : g2 hS_F_cover ≤ ∑ F ∈ S_F, (ediam F)^d := iInf_le (fun hS3 => ∑ F ∈ S_F, (ediam F)^d) hS_F_diam
        exact h1.trans (h2.trans (h3.trans (h4.trans hS_F_cost)))
      have h_goal : C + ENNReal.ofReal ε = pre_m r B + ENNReal.ofReal ε + ↑δ := by
        simp [C, add_assoc] <;> abel
      rw [h_goal] at h_final
      exact h_final
  -- Step 4: equality μH[d](B) = ⨆ k, h_{1/(k+1)} B for compact B
  have h4 : ∀ (B : Set (E n)), IsCompact B →
      μH[d] B = ⨆ k : ℕ, h (ENNReal.ofReal (1 / (k + 1 : ℝ))) B := by
    intro B hB
    have h_hausdorff_B : μH[d] B = ⨆ (r : ENNReal) (_ : 0 < r), pre_m r B := h_hausdorff B
    -- Direction 1: μH[d] B ≤ ⨆ k, h_{1/(k+1)} B
    have h_dir1 : μH[d] B ≤ ⨆ k : ℕ, h (ENNReal.ofReal (1 / (k + 1 : ℝ))) B := by
      rw [h_hausdorff_B]
      apply iSup_le
      intro r
      by_cases hr : 0 < r
      · -- r > 0: show pre_m r B ≤ iSup
        have h_exists_k : ∃ (k : ℕ), ENNReal.ofReal (1 / (k + 1 : ℝ)) ≤ r := by
          by_cases h_r_top : r = ⊤
          · exact ⟨0, by simp [h_r_top]⟩
          · have h_r_pos : 0 < r.toReal := by
              have h : 0 < r := hr
              rw [← ENNReal.ofReal_toReal h_r_top] at h
              have h' : (0 : ENNReal) < ENNReal.ofReal r.toReal := h
              exact ENNReal.ofReal_pos.mp h'
            have h : ∃ k : ℕ, (1 / (k + 1 : ℝ)) ≤ r.toReal := by
              obtain ⟨k, hk⟩ := exists_nat_ge (1 / r.toReal - 1)
              refine ⟨k, ?_⟩
              have h2 : (1 : ℝ) / (k + 1 : ℝ) ≤ r.toReal := by
                have h3 : (k + 1 : ℝ) ≥ 1 / r.toReal := by linarith
                have h4 : 0 < r.toReal := h_r_pos
                calc 1 / (k + 1 : ℝ) ≤ 1 / (1 / r.toReal) := by gcongr
                     _ = r.toReal := by field_simp [h4.ne'] <;> ring
              exact h2
            rcases h with ⟨k, hk⟩
            refine ⟨k, ?_⟩
            rw [← ENNReal.ofReal_toReal h_r_top]
            gcongr
        rcases h_exists_k with ⟨k, hk⟩
        have h5 : pre_m r B ≤ h r B := h2 r B
        have h6 : h r B ≤ h (ENNReal.ofReal (1 / (k + 1 : ℝ))) B :=
          h_mono (ENNReal.ofReal (1 / (k + 1 : ℝ))) r hk B
        have h7 : h (ENNReal.ofReal (1 / (k + 1 : ℝ))) B ≤ ⨆ k : ℕ, h (ENNReal.ofReal (1 / (k + 1 : ℝ))) B :=
          le_iSup_of_le k le_rfl
        have h8 : (⨆ (_ : 0 < r), pre_m r B) = pre_m r B := by simp [hr]
        rw [h8]
        exact h5.trans (h6.trans h7)
      · -- r = 0
        have hr0 : r = 0 := by simpa using hr
        rw [hr0]
        simp
    -- Direction 2: ⨆ k, h_{1/(k+1)} B ≤ μH[d] B
    have h_dir2 : (⨆ k : ℕ, h (ENNReal.ofReal (1 / (k + 1 : ℝ))) B) ≤ μH[d] B := by
      apply iSup_le
      intro k
      let r_k := ENNReal.ofReal (1 / (k + 1 : ℝ))
      have h_r_k_pos : 0 < r_k := by positivity
      have h_r_k_ne_top : r_k ≠ ⊤ := by simp [r_k]
      have h_eps : ∀ (ε : ℝ), 0 < ε → h r_k B ≤ μH[d] B + ENNReal.ofReal ε := by
        intro ε hε
        by_cases h_big : ε ≥ 1 / (k + 1 : ℝ)
        · let ε' : ℝ := (1 / (k + 1 : ℝ)) / 2
          let r : ENNReal := ENNReal.ofReal ε'
          have hε'_pos : 0 < ε' := by positivity
          have hr_pos : 0 < r := by positivity
          have hr_ne_top : r ≠ ⊤ := by simp [r]
          have h_r_def : r = ENNReal.ofReal ε' := by rfl
          have h_r_plus : r + r = r_k := by
            rw [h_r_def]
            have h1 : ENNReal.ofReal ε' + ENNReal.ofReal ε' = ENNReal.ofReal (ε' + ε') := by
              rw [← ENNReal.ofReal_add hε'_pos.le hε'_pos.le]
            rw [h1]
            have h2 : ε' + ε' = (1 / (k + 1 : ℝ)) := by
              simp [ε'] <;> ring
            rw [h2] <;> rfl
          have h_approx : h (r + ENNReal.ofReal ε') B ≤ pre_m r B + ENNReal.ofReal ε' :=
            h3 r hr_ne_top ε' hε'_pos B hB
          rw [h_r_def] at h_approx
          rw [h_r_plus] at h_approx
          have h9 : pre_m r B ≤ μH[d] B := by
            rw [h_hausdorff_B]
            exact le_iSup_of_le r (le_iSup_of_le hr_pos le_rfl)
          have h10 : r ≤ ENNReal.ofReal ε := by
            rw [h_r_def]
            have h11 : ε' ≤ ε := by
              dsimp only [ε']
              linarith [h_big]
            gcongr
          calc h r_k B
            ≤ pre_m r B + r := h_approx
          _ ≤ μH[d] B + r := by gcongr
          _ ≤ μH[d] B + ENNReal.ofReal ε := by gcongr
        · have h_eps_lt : ENNReal.ofReal ε < r_k := by
            rw [ENNReal.ofReal_lt_ofReal_iff] <;> linarith
          let r := r_k - ENNReal.ofReal ε
          have h_le : ENNReal.ofReal ε ≤ r_k := h_eps_lt.le
          have hr_pos : 0 < r := by
            by_contra h
            have h' : r = 0 := by simpa using h
            have h_r_plus2 : r + ENNReal.ofReal ε = r_k :=
              tsub_add_cancel_of_le h_le
            rw [h'] at h_r_plus2
            have h_eq : ENNReal.ofReal ε = r_k := by simpa using h_r_plus2
            rw [h_eq] at h_eps_lt
            simp at h_eps_lt <;> tauto
          have hr_ne_top : r ≠ ⊤ := by
            have h_r_le : r ≤ r_k := by
              simp only [r]
              exact tsub_le_self
            exact ne_top_of_le_ne_top h_r_k_ne_top h_r_le
          have h_approx : h (r + ENNReal.ofReal ε) B ≤ pre_m r B + ENNReal.ofReal ε :=
            h3 r hr_ne_top ε hε B hB
          have h_r_plus : r + ENNReal.ofReal ε = r_k :=
            tsub_add_cancel_of_le h_le
          rw [h_r_plus] at h_approx
          have h9 : pre_m r B ≤ μH[d] B := by
            rw [h_hausdorff_B]
            exact le_iSup_of_le r (le_iSup_of_le hr_pos le_rfl)
          calc h r_k B
            ≤ pre_m r B + ENNReal.ofReal ε := h_approx
          _ ≤ μH[d] B + ENNReal.ofReal ε := by gcongr
      by_cases h_top : μH[d] B = ⊤
      · rw [h_top]; simp
      · have h : h r_k B ≤ μH[d] B := by
          apply ENNReal.le_of_forall_pos_le_add
          intro δ hδ hB_lt_top
          have hε' : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
          have h := h_eps (δ : ℝ) hε'
          simpa using h
        exact h
    exact le_antisymm h_dir1 h_dir2
  -- Step 5: transfer to μHE[d]
  let d' : ℕ := n - 1
  have h_d'_eq : (d' : ℝ) = d := by
    simp [d, d'] <;> omega
  have hμHE : (μHE[d'] : Measure (E n)) = (MeasureTheory.Measure.addHaarScalarFactor (volume : Measure (E d')) (μH[d'] : Measure (E d')) : ENNReal) • μH[d'] :=
    MeasureTheory.Measure.euclideanHausdorffMeasure_def (d := d')
  let c : ENNReal := ↑(MeasureTheory.Measure.addHaarScalarFactor (volume : Measure (E d')) (μH[d'] : Measure (E d')))
  have h_main_eq : ∀ (s : ℝ), μHE[d'] (K ∩ f ⁻¹' {s}) = c * μH[d] (K ∩ f ⁻¹' {s}) := by
    intro s
    have h1 : μHE[d'] (K ∩ f ⁻¹' {s}) = (c • μH[d']) (K ∩ f ⁻¹' {s}) := by
      rw [hμHE]
    rw [h1]
    simp [smul_apply, h_d'_eq]
    <;> rfl
  have hK_s_compact : ∀ (s : ℝ), IsCompact (K ∩ f ⁻¹' {s}) := by
    intro s
    have h1 : IsClosed (f ⁻¹' {s}) := isClosed_singleton.preimage hf
    exact hK.inter_right h1
  have h_meas_H : Measurable (fun s : ℝ => μH[d] (K ∩ f ⁻¹' {s})) := by
    have h_eq : (fun s : ℝ => μH[d] (K ∩ f ⁻¹' {s})) =
        fun s : ℝ => ⨆ k : ℕ, h (ENNReal.ofReal (1 / (k + 1 : ℝ))) (K ∩ f ⁻¹' {s}) := by
      funext s
      exact h4 (K ∩ f ⁻¹' {s}) (hK_s_compact s)
    rw [h_eq]
    exact Measurable.iSup (fun k => h1 _)
  have h_final : Measurable (fun s : ℝ => μHE[d'] (K ∩ f ⁻¹' {s})) := by
    have h_eq2 : (fun s : ℝ => μHE[d'] (K ∩ f ⁻¹' {s})) = fun s : ℝ => c * μH[d] (K ∩ f ⁻¹' {s}) := by
      funext s
      exact h_main_eq s
    rw [h_eq2]
    exact h_meas_H.const_mul c
  simpa [d'] using h_final

/-- If `volume N = 0`, then `μHE[n-1](N ∩ f⁻¹{s}) = 0` for a.e. `s`.

Proof: approximate N by open sets O_m from outside; each H_{O_m} is
measurable (open = increasing union of compact); Eilenberg gives
∫ H_{O_m} → 0; Fatou gives measurable g ≥ H_N with ∫ g = 0. -/
lemma nullSet_levelSets_ae_zero (hn : 2 ≤ n)
    {f : E n → ℝ} (hf : LipschitzWith 1 f)
    {N : Set (E n)} (hN_meas : MeasurableSet N) (hN : volume N = 0) :
    ∀ᵐ (s : ℝ), μHE[n - 1] (N ∩ f ⁻¹' {s}) = 0 := by
  rcases eilenberg_μHE hn (hf := hf) (by norm_num) with ⟨C, hC_ne_top, hC_pos, h_eilenberg⟩
  -- Outer regularity: open O_m ⊇ N with volume(O_m) < 1/(m+1)
  have h_outer : ∀ (m : ℕ), ∃ (O : Set (E n)), IsOpen O ∧ N ⊆ O ∧
      volume O < ENNReal.ofReal (1 / (m + 1 : ℝ)) := by
    intro m
    have hε : (0 : ENNReal) < ENNReal.ofReal (1 / (m + 1 : ℝ)) := by positivity
    have hN_top : volume N ≠ ⊤ := by rw [hN]; exact ENNReal.zero_ne_top
    rcases Set.exists_isOpen_lt_add N hN_top hε.ne' with ⟨O, hNO, hO_open, hO_lt⟩
    have hO_vol : volume O < ENNReal.ofReal (1 / (m + 1 : ℝ)) := by
      simpa [hN] using hO_lt
    exact ⟨O, hO_open, hNO, hO_vol⟩
  choose O hO_open hO_sub hO_vol using h_outer
  -- Increasing compact cover of each O_m
  have h_cover : ∀ m, ∃ (K : ℕ → Set (E n)), (∀ j, IsCompact (K j)) ∧
      (∀ j, K j ⊆ K (j + 1)) ∧ (⋃ j, K j = O m) := by
    intro m
    rcases open_compact_cover (hO_open m) with ⟨K, hK_comp, hK_mono, hK_union, _⟩
    exact ⟨K, hK_comp, hK_mono, hK_union⟩
  choose K hK_comp hK_mono hK_union using h_cover
  -- H_{K m j} measurable by compact lemma
  have h_meas_K : ∀ m j, Measurable fun s : ℝ => μHE[n - 1] (K m j ∩ f ⁻¹' {s}) := by
    intro m j
    exact levelSetMeasure_compact_measurable hn (hK_comp m j) hf.continuous
  -- H_{O_m} = sup_j H_{K m j} measurable
  let H_O := fun m => fun s : ℝ => μHE[n - 1] (O m ∩ f ⁻¹' {s})
  have h_H_O_eq : ∀ m, H_O m = fun s => ⨆ j, μHE[n - 1] (K m j ∩ f ⁻¹' {s}) := by
    intro m
    funext s
    have hK_mono_gen : ∀ j1 j2, j1 ≤ j2 → K m j1 ⊆ K m j2 := by
      intro j1 j2 h
      induction' h with j2 h ih
      · exact subset_refl _
      · exact ih.trans (hK_mono m j2)
    have h_mono : Monotone fun j => K m j ∩ f ⁻¹' {s} := by
      intro j1 j2 h x hx
      exact ⟨hK_mono_gen j1 j2 h hx.1, hx.2⟩
    have h1 : (⋃ j, K m j ∩ f ⁻¹' {s}) = O m ∩ f ⁻¹' {s} := by
      have h_iUnion_inter : (⋃ j, K m j ∩ f ⁻¹' {s}) = (⋃ j, K m j) ∩ f ⁻¹' {s} := by
        rw [Set.iUnion_inter]
      rw [h_iUnion_inter, hK_union m]
    have h_dir : DirectedOn (fun i j => (K m i ∩ f ⁻¹' {s}) ⊆ (K m j ∩ f ⁻¹' {s})) Set.univ := by
      intro i _ j _
      refine ⟨max i j, Set.mem_univ _, h_mono (le_max_left i j), h_mono (le_max_right i j)⟩
    have h_ms : ∀ j, MeasurableSet (K m j ∩ f ⁻¹' {s}) := by
      intro j
      exact (hK_comp m j).measurableSet.inter
        (isClosed_singleton.measurableSet.preimage hf.continuous.measurable)
    have h2 : μHE[n - 1] (⋃ j, K m j ∩ f ⁻¹' {s}) =
        ⨆ j, μHE[n - 1] (K m j ∩ f ⁻¹' {s}) := by
      have h := MeasureTheory.measure_biUnion_eq_iSup (μ := μHE[n - 1]) (Set.countable_univ) h_dir
      simpa using h
    have h_goal : H_O m s = ⨆ j, μHE[n - 1] (K m j ∩ f ⁻¹' {s}) := by
      dsimp only [H_O]
      rw [← h1]
      exact h2
    exact h_goal
  have h_meas_O : ∀ m, Measurable (H_O m) := by
    intro m
    rw [h_H_O_eq m]
    exact Measurable.iSup (h_meas_K m)
  -- Eilenberg bound
  have h_int : ∀ m, ∫⁻ (s : ℝ), H_O m s ≤ C * volume (O m) := by
    intro m
    simpa [H_O] using h_eilenberg (O m)
  have hC_pos' : 0 < C := lt_of_le_of_ne bot_le hC_pos.symm
  have h_int2 : ∀ (m : ℕ), ∫⁻ (s : ℝ), H_O m s < C * ENNReal.ofReal (1 / (m + 1 : ℝ)) := by
    intro m
    have h5 : C * volume (O m) < C * ENNReal.ofReal (1 / (m + 1 : ℝ)) := by
      exact ENNReal.mul_lt_mul_right hC_pos hC_ne_top (hO_vol m)
    exact (h_int m).trans_lt h5
  -- g = liminf H_{O_m}
  let g : ℝ → ENNReal := fun s => liminf (fun (m : ℕ) => H_O m s) Filter.atTop
  have hg_meas : Measurable g := Measurable.liminf h_meas_O
  -- H_N ≤ g
  have h1 : ∀ s, μHE[n - 1] (N ∩ f ⁻¹' {s}) ≤ g s := by
    intro s
    have h2 : ∀ m, μHE[n - 1] (N ∩ f ⁻¹' {s}) ≤ H_O m s := by
      intro m
      apply measure_mono
      intro x hx
      exact ⟨hO_sub m hx.1, hx.2⟩
    have h3 : ∀ᶠ m in Filter.atTop, μHE[n - 1] (N ∩ f ⁻¹' {s}) ≤ H_O m s :=
      Filter.univ_mem' h2
    exact Filter.le_liminf_of_le (h := h3)
  -- Fatou
  have h_fatou : ∫⁻ (s : ℝ), g s ≤ liminf (fun (m : ℕ) => ∫⁻ (s : ℝ), H_O m s) Filter.atTop :=
    lintegral_liminf_le h_meas_O
  letI h_bdd1 : IsCoboundedUnder (fun x1 x2 : ENNReal => x1 ≥ x2) Filter.atTop
      (fun (m : ℕ) => ∫⁻ (s : ℝ), H_O m s) := by
    refine' ⟨⊤, _⟩
    intro a h
    exact le_top
  letI h_bdd2 : IsCoboundedUnder (fun x1 x2 : ENNReal => x1 ≥ x2) Filter.atTop
      (fun (m : ℕ) => C * ENNReal.ofReal (1 / (m + 1 : ℝ))) := by
    refine' ⟨⊤, _⟩
    intro a h
    exact le_top
  have h3 : liminf (fun (m : ℕ) => ∫⁻ (s : ℝ), H_O m s) Filter.atTop ≤
      liminf (fun (m : ℕ) => C * ENNReal.ofReal (1 / (m + 1 : ℝ))) Filter.atTop :=
    Filter.liminf_le_liminf (by filter_upwards with m; exact le_of_lt (h_int2 m))
  have h4 : Tendsto (fun m : ℕ => C * ENNReal.ofReal (1 / (m + 1 : ℝ))) Filter.atTop (nhds 0) := by
    have h5 : Tendsto (fun m : ℕ => ENNReal.ofReal (1 / (m + 1 : ℝ))) Filter.atTop (nhds 0) := by
      have h6 : Continuous ENNReal.ofReal := ENNReal.continuous_ofReal
      have h7 : Tendsto (ENNReal.ofReal ∘ fun n : ℕ => (1 / (n + 1 : ℝ))) Filter.atTop (nhds (ENNReal.ofReal (0 : ℝ))) :=
        h6.tendsto 0 |>.comp tendsto_one_div_add_atTop_nhds_zero_nat
      have h8 : ENNReal.ofReal (0 : ℝ) = 0 := by simp
      have h9 : Tendsto (ENNReal.ofReal ∘ fun n : ℕ => (1 / (n + 1 : ℝ))) Filter.atTop (nhds 0) := by
        rw [h8] at h7; exact h7
      have h10 : (fun (m : ℕ) => ENNReal.ofReal (1 / (m + 1 : ℝ))) = (ENNReal.ofReal ∘ fun n : ℕ => (1 / (n + 1 : ℝ))) := by
        funext m; rfl
      rw [h10]; exact h9
    have h_cont : Continuous (fun x : ENNReal => C * x) := ENNReal.continuous_const_mul hC_ne_top
    have h := h_cont.tendsto 0 |>.comp h5
    have h' : Tendsto (fun (m : ℕ) => C * ENNReal.ofReal (1 / (m + 1 : ℝ))) Filter.atTop (nhds 0) := by
      convert h using 1
      · funext m; rfl
      · simp
    exact h'
  have h5 : liminf (fun (m : ℕ) => C * ENNReal.ofReal (1 / (m + 1 : ℝ))) Filter.atTop = 0 :=
    h4.liminf_eq
  have h6 : ∫⁻ (s : ℝ), g s ≤ 0 := by
    calc ∫⁻ (s : ℝ), g s
      ≤ liminf (fun (m : ℕ) => ∫⁻ (s : ℝ), H_O m s) Filter.atTop := h_fatou
    _ ≤ liminf (fun (m : ℕ) => C * ENNReal.ofReal (1 / (m + 1 : ℝ))) Filter.atTop := h3
    _ = 0 := h5
  have h7 : ∫⁻ (s : ℝ), g s = 0 := by simpa using h6
  have h8 : ∀ᵐ (s : ℝ), g s = 0 := (lintegral_eq_zero_iff' hg_meas.aemeasurable).mp h7
  have h9 : ∀ᵐ (s : ℝ), μHE[n - 1] (N ∩ f ⁻¹' {s}) = 0 := by
    filter_upwards [h8] with s hs
    have h10 : μHE[n - 1] (N ∩ f ⁻¹' {s}) ≤ g s := h1 s
    rw [hs] at h10
    simpa using h10
  exact h9

/-- **Main theorem: AEMeasurability of level-set Hausdorff measure.**

For a measurable bounded set `B` and a 1-Lipschitz function `f`,
`s ↦ μHE[n-1](B ∩ f⁻¹{s})` is `AEMeasurable` w.r.t. `volume.restrict (Set.Ioc a b)`. -/
lemma levelSetMeasure_aemeasurable (hn : 2 ≤ n)
    {f : E n → ℝ} (hf : LipschitzWith 1 f)
    {B : Set (E n)} (hB : MeasurableSet B) (hBdd : Bornology.IsBounded B)
    {a b : ℝ} (hab : a < b) :
    AEMeasurable (fun s : ℝ => μHE[n - 1] (B ∩ f ⁻¹' {s}))
      (volume.restrict (Set.Ioc a b)) := by
  -- Increasing compact approximations K'_m ⊆ B
  have h_exists : ∀ (m : ℕ), ∃ (K : Set (E n)), K ⊆ B ∧ IsCompact K ∧ IsClosed K ∧
      volume (B \ K) < ENNReal.ofReal (1 / (m + 1 : ℝ)) := by
    intro m
    have hfin : volume B ≠ ⊤ := hBdd.measure_lt_top.ne
    have hε : (0 : ENNReal) < ENNReal.ofReal (1 / (m + 1 : ℝ)) := by positivity
    exact hB.exists_isCompact_isClosed_sdiff_lt hfin hε.ne'
  choose K hK_sub hK_comp hK_closed hK_diff using h_exists
  let K' : ℕ → Set (E n) := fun m => ⋃ i ∈ Finset.range (m + 1), K i
  have hK'_comp : ∀ m, IsCompact (K' m) := by
    intro m
    induction m with
    | zero => simpa [K'] using hK_comp 0
    | succ m ih =>
      have h : K' (m + 1) = K' m ∪ K (m + 1) := by
        ext y
        simp only [K', Set.mem_iUnion, Set.mem_union, Finset.mem_range]
        constructor
        · rintro ⟨i, h_i_lt, hyi⟩
          by_cases h : i < m + 1
          · exact Or.inl ⟨i, h, hyi⟩
          · have h_eq : i = m + 1 := by omega
            rw [h_eq] at hyi
            exact Or.inr hyi
        · rintro (h | h)
          · rcases h with ⟨i, h_i_lt, hyi⟩
            exact ⟨i, by omega, hyi⟩
          · exact ⟨m + 1, by omega, h⟩
      rw [h]; exact IsCompact.union ih (hK_comp (m + 1))
  have hK'_sub : ∀ m, K' m ⊆ B := by
    intro m; intro x hx
    simp only [K', Set.mem_iUnion] at hx
    rcases hx with ⟨i, _, hxi⟩
    exact hK_sub i hxi
  have hK'_mono : ∀ m, K' m ⊆ K' (m + 1) := by
    intro m
    have h_range : (Finset.range (m + 1) : Set ℕ) ⊆ (Finset.range (m + 2) : Set ℕ) := by
      intro i hi
      have h1 : i < m + 1 := Finset.mem_range.mp hi
      have h2 : i < m + 2 := by linarith
      exact Finset.mem_range.mpr h2
    exact Set.biUnion_subset_biUnion_left h_range
  have hK'_diff : ∀ m, volume (B \ K' m) < ENNReal.ofReal (1 / (m + 1 : ℝ)) := by
    intro m
    have h1 : B \ K' m ⊆ B \ K m := by
      intro x hx
      have h2 : x ∉ K' m := hx.2
      have h3 : x ∉ K m := by
        intro h4
        have h5 : x ∈ K' m := by
          simp only [K', Set.mem_iUnion]
          exact ⟨m, by simp [Finset.mem_range], h4⟩
        exact h2 h5
      exact ⟨hx.1, h3⟩
    have h4 : volume (B \ K' m) ≤ volume (B \ K m) := measure_mono h1
    exact h4.trans_lt (hK_diff m)
  let B_union := ⋃ m, K' m
  have hB_union_sub : B_union ⊆ B := by
    intro x hx
    rcases mem_iUnion.mp hx with ⟨m, hm⟩
    exact hK'_sub m hm
  have hB_diff_null : volume (B \ B_union) = 0 := by
    let V := volume (B \ B_union)
    have h1 : ∀ (m : ℕ), V ≤ volume (B \ K' m) := by
      intro m
      apply measure_mono
      intro x hx
      exact ⟨hx.1, fun h2 => hx.2 (mem_iUnion.mpr ⟨m, h2⟩)⟩
    have h2 : ∀ (m : ℕ), V < ENNReal.ofReal (1 / (m + 1 : ℝ)) := by
      intro m
      exact (h1 m).trans_lt (hK'_diff m)
    by_contra h3
    have h4 : 0 < V := by
      have h_le : 0 ≤ V := bot_le
      have h_ne : (0 : ENNReal) ≠ V := by
        intro h
        exact h3 h.symm
      exact lt_of_le_of_ne h_le h_ne
    have hV_fin : V ≠ ⊤ := by
      have h : V ≤ volume B := measure_mono (show B \ B_union ⊆ B from diff_subset)
      exact ne_top_of_le_ne_top hBdd.measure_lt_top.ne h
    have hV_pos_real : 0 < V.toReal := toReal_pos h3 hV_fin
    have h5 : ∃ (m : ℕ), ENNReal.ofReal (1 / (m + 1 : ℝ)) < V := by
      have h6 : ∃ (m : ℕ), (1 / V.toReal - 1 : ℝ) < (m : ℝ) := exists_nat_gt (1 / V.toReal - 1)
      rcases h6 with ⟨m, hm⟩
      have h7' : (m + 1 : ℝ) > 1 / V.toReal := by linarith
      have h7 : 0 < V.toReal := hV_pos_real
      have h8 : 0 < (m + 1 : ℝ) := by positivity
      have h9 : 1 / (m + 1 : ℝ) < V.toReal := by
        calc 1 / (m + 1 : ℝ)
          < 1 / (1 / V.toReal) := by gcongr
          _ = V.toReal := by field_simp [h7.ne'] <;> ring
      have h10 : ENNReal.ofReal (1 / (m + 1 : ℝ)) < ENNReal.ofReal V.toReal := by
        exact (ENNReal.ofReal_lt_ofReal_iff hV_pos_real).mpr h9
      have h11 : ENNReal.ofReal V.toReal = V := ENNReal.ofReal_toReal hV_fin
      rw [h11] at h10
      exact ⟨m, h10⟩
    rcases h5 with ⟨m, hm⟩
    have h9 : V < ENNReal.ofReal (1 / (m + 1 : ℝ)) := h2 m
    exact lt_asymm h9 hm
  -- H_{K'_m} measurable
  have h_meas : ∀ m, Measurable fun s : ℝ => μHE[n - 1] (K' m ∩ f ⁻¹' {s}) := by
    intro m
    exact levelSetMeasure_compact_measurable hn (hK'_comp m) hf.continuous
  -- H_{B_∞} = sup H_{K'_m} measurable
  let H_Bunion := fun s : ℝ => μHE[n - 1] (B_union ∩ f ⁻¹' {s})
  have hH_Bunion_meas : Measurable H_Bunion := by
    have h : H_Bunion = fun s => ⨆ m, μHE[n - 1] (K' m ∩ f ⁻¹' {s}) := by
      funext s
      have hK'_mono' : ∀ m1 m2, m1 ≤ m2 → K' m1 ⊆ K' m2 := by
        intro m1 m2 h
        induction' h with m2 h ih
        · exact subset_refl _
        · exact ih.trans (hK'_mono m2)
      have h_mono : Monotone fun m => K' m ∩ f ⁻¹' {s} := by
        intro m1 m2 h x hx
        exact ⟨hK'_mono' m1 m2 h hx.1, hx.2⟩
      have h_union : (⋃ m, K' m ∩ f ⁻¹' {s}) = B_union ∩ f ⁻¹' {s} := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_inter_iff, B_union]
        constructor
        · rintro ⟨m, h1, h2⟩; exact ⟨⟨m, h1⟩, h2⟩
        · rintro ⟨h1, h2⟩; rcases h1 with ⟨m, hm⟩; exact ⟨m, hm, h2⟩
      have h_dir : DirectedOn (fun i j => (K' i ∩ f ⁻¹' {s}) ⊆ (K' j ∩ f ⁻¹' {s})) Set.univ := by
        intro i _ j _
        refine ⟨max i j, Set.mem_univ _, h_mono (le_max_left i j), h_mono (le_max_right i j)⟩
      have h_ms : ∀ m, MeasurableSet (K' m ∩ f ⁻¹' {s}) := by
        intro m
        exact (hK'_comp m).measurableSet.inter
          (isClosed_singleton.measurableSet.preimage hf.continuous.measurable)
      let A : ℕ → Set (E n) := fun m => K' m ∩ f ⁻¹' {s}
      have h_dir' : DirectedOn (fun i j => A i ⊆ A j) (Set.univ : Set ℕ) := h_dir
      have h_main : μHE[n - 1] (⋃ i ∈ (Set.univ : Set ℕ), A i) =
          ⨆ i ∈ (Set.univ : Set ℕ), μHE[n - 1] (A i) :=
        MeasureTheory.measure_biUnion_eq_iSup (Set.countable_univ) h_dir'
      have h1 : (⋃ i ∈ (Set.univ : Set ℕ), A i) = (⋃ i : ℕ, A i) := by ext x; simp
      have h2 : (⨆ i ∈ (Set.univ : Set ℕ), μHE[n - 1] (A i)) = (⨆ i : ℕ, μHE[n - 1] (A i)) := by
        simp
      have h_eq_measure : μHE[n - 1] (⋃ m : ℕ, A m) = ⨆ m : ℕ, μHE[n - 1] (A m) := by
        rw [← h1, ← h2]; exact h_main
      have h_goal : H_Bunion s = ⨆ m, μHE[n - 1] (K' m ∩ f ⁻¹' {s}) := by
        have h10 : H_Bunion s = μHE[n - 1] (B_union ∩ f ⁻¹' {s}) := by rfl
        have h11 : (⋃ m : ℕ, A m) = B_union ∩ f ⁻¹' {s} := by
          ext x; simp [A, h_union]
        have h12 : μHE[n - 1] (B_union ∩ f ⁻¹' {s}) = ⨆ m, μHE[n - 1] (A m) := by
          rw [← h11]
          exact h_eq_measure
        rw [h10, h12]
        <;> rfl
      exact h_goal
    rw [h]
    exact Measurable.iSup h_meas
  -- H_B = H_B∞ + H_{B\B∞}, and H_{B\B∞} = 0 a.e.
  have h_null : ∀ᵐ (s : ℝ), μHE[n - 1] ((B \ B_union) ∩ f ⁻¹' {s}) = 0 :=
    nullSet_levelSets_ae_zero hn (hf := hf)
      (hB.diff (MeasurableSet.iUnion (fun m => (hK'_comp m).measurableSet)))
      hB_diff_null
  have h_main : ∀ᵐ (s : ℝ), μHE[n - 1] (B ∩ f ⁻¹' {s}) = H_Bunion s := by
    filter_upwards [h_null] with s hs
    have h_disj : Disjoint (B_union ∩ f ⁻¹' {s}) ((B \ B_union) ∩ f ⁻¹' {s}) := by
      rw [Set.disjoint_left]; intro x h1 h2; exact h2.1.2 h1.1
    have h_union2 : B ∩ f ⁻¹' {s} = (B_union ∩ f ⁻¹' {s}) ∪ ((B \ B_union) ∩ f ⁻¹' {s}) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_diff]
      constructor
      · intro h
        by_cases h2 : x ∈ B_union
        · exact Or.inl ⟨h2, h.2⟩
        · exact Or.inr ⟨⟨h.1, h2⟩, h.2⟩
      · rintro (h | h)
        · exact ⟨hB_union_sub h.1, h.2⟩
        · exact ⟨h.1.1, h.2⟩
    let S1 := B_union ∩ f ⁻¹' {s}
    let S2 := (B \ B_union) ∩ f ⁻¹' {s}
    have hS2_meas : MeasurableSet S2 := by
      exact (hB.diff (MeasurableSet.iUnion (fun m => (hK'_comp m).measurableSet))).inter
        (isClosed_singleton.measurableSet.preimage hf.continuous.measurable)
    have h_eq : μHE[n - 1] (B ∩ f ⁻¹' {s}) =
        μHE[n - 1] S1 + μHE[n - 1] S2 := by
      rw [h_union2]
      exact measure_union h_disj hS2_meas
    rw [h_eq, hs, add_zero]
  have h_main' : H_Bunion =ᵐ[volume] (fun s : ℝ => μHE[n - 1] (B ∩ f ⁻¹' {s})) := by
    filter_upwards [h_main] with s hs
    exact hs.symm
  have h_ae : AEMeasurable (fun s : ℝ => μHE[n - 1] (B ∩ f ⁻¹' {s})) volume :=
    hH_Bunion_meas.aemeasurable.congr h_main'
  exact h_ae.restrict

/-- **`FunctionLevelMeasurable` for any 1-Lipschitz function.**

Extends `levelSetMeasure_aemeasurable` from bounded to arbitrary measurable
sets by exhausting with closed balls `B ∩ closedBall 0 k`. For each `s`,
the level sets form an increasing sequence whose Hausdorff measure converges
to the measure of the full level set, and `AEMeasurable.iSup` closes the
proof. -/
lemma functionLevelMeasurable_of_lipschitz (hn : 2 ≤ n)
    {f : E n → ℝ} (hf : LipschitzWith 1 f) :
    FunctionLevelMeasurable f := by
  intro B hB a b
  by_cases hab : a < b
  · -- Define B_k := B ∩ closedBall 0 k
    let Bk : ℕ → Set (E n) := fun k => B ∩ closedBall (0 : E n) k
    have hBk_meas : ∀ k, MeasurableSet (Bk k) := by
      intro k
      exact hB.inter isClosed_closedBall.measurableSet
    have hBk_bdd : ∀ k, Bornology.IsBounded (Bk k) := by
      intro k
      exact Metric.isBounded_closedBall.subset inter_subset_right
    have hBk_mono : ∀ (k1 k2 : ℕ), k1 ≤ k2 → Bk k1 ⊆ Bk k2 := by
      intro k1 k2 h
      intro x hx
      have h1 : x ∈ B := hx.1
      have h2 : x ∈ closedBall (0 : E n) k1 := hx.2
      have h3 : x ∈ closedBall (0 : E n) k2 :=
        closedBall_subset_closedBall (by exact_mod_cast h) h2
      exact ⟨h1, h3⟩
    have hBk_union : (⋃ k, Bk k) = B := by
      ext x
      simp only [Bk, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨k, h1, _⟩; exact h1
      · intro hx
        have h_exists : ∃ (k : ℕ), ‖x‖ ≤ (k : ℝ) := by
          exact ⟨Nat.ceil ‖x‖, by exact Nat.le_ceil ‖x‖⟩
        rcases h_exists with ⟨k, hk⟩
        have h_in_ball : x ∈ closedBall (0 : E n) k := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hk
        exact ⟨k, hx, h_in_ball⟩
    -- For each k, g_k(s) := μHE[n-1]{x ∈ Bk k | f x = s} is AEMeasurable
    let gk : ℕ → (ℝ → ENNReal) := fun k =>
      fun s => μHE[n - 1] {x ∈ Bk k | f x = s}
    have hgk_ae : ∀ k, AEMeasurable (gk k) (volume.restrict (Set.Ioc a b)) := by
      intro k
      have h_set_eq : ∀ (s : ℝ), {x ∈ Bk k | f x = s} = (Bk k) ∩ f ⁻¹' {s} := by
        intro s
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
        <;> aesop
      have h : AEMeasurable (fun s : ℝ => μHE[n - 1] ((Bk k) ∩ f ⁻¹' {s}))
          (volume.restrict (Set.Ioc a b)) :=
        levelSetMeasure_aemeasurable hn (hf := hf) (hB := hBk_meas k) (hBdd := hBk_bdd k) (hab := hab)
      have h2 : (gk k) = (fun s : ℝ => μHE[n - 1] ((Bk k) ∩ f ⁻¹' {s})) := by
        funext s
        dsimp only [gk]
        exact congr_arg (μHE[n - 1]) (h_set_eq s)
      rw [h2]
      exact h
    -- For each s, the level sets are increasing
    have h_level_mono : ∀ (s : ℝ) (k1 k2 : ℕ), k1 ≤ k2 →
        {x ∈ Bk k1 | f x = s} ⊆ {x ∈ Bk k2 | f x = s} := by
      intro s k1 k2 h x hx
      exact ⟨hBk_mono k1 k2 h hx.1, hx.2⟩
    -- For each s, union of level sets equals {x ∈ B | f x = s}
    have h_level_union : ∀ (s : ℝ), (⋃ k, {x ∈ Bk k | f x = s}) = {x ∈ B | f x = s} := by
      intro s
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · rintro ⟨k, h1, h2⟩; exact ⟨h1.1, h2⟩
      · rintro ⟨h1, h2⟩
        have h3 : x ∈ ⋃ k, Bk k := by rw [hBk_union]; exact h1
        rcases Set.mem_iUnion.mp h3 with ⟨k, hk⟩
        exact ⟨k, hk, h2⟩
    -- μHE of increasing union is iSup
    have h_measure_union : ∀ (s : ℝ),
        μHE[n - 1] (⋃ k, {x ∈ Bk k | f x = s}) =
        ⨆ k, μHE[n - 1] {x ∈ Bk k | f x = s} := by
      intro s
      let A : ℕ → Set (E n) := fun k => {x ∈ Bk k | f x = s}
      have hA_mono : ∀ k1 k2, k1 ≤ k2 → A k1 ⊆ A k2 := h_level_mono s
      have h_dir : DirectedOn (fun i j => A i ⊆ A j) Set.univ := by
        intro i _ j _
        refine ⟨max i j, Set.mem_univ _, hA_mono i (max i j) (le_max_left i j),
          hA_mono j (max i j) (le_max_right i j)⟩
      have h_main : μHE[n - 1] (⋃ i ∈ (Set.univ : Set ℕ), A i) =
          ⨆ i ∈ (Set.univ : Set ℕ), μHE[n - 1] (A i) :=
        MeasureTheory.measure_biUnion_eq_iSup (Set.countable_univ) h_dir
      have h1 : (⋃ i ∈ (Set.univ : Set ℕ), A i) = (⋃ i : ℕ, A i) := by ext x; simp
      have h2 : (⨆ i ∈ (Set.univ : Set ℕ), μHE[n - 1] (A i)) = (⨆ i : ℕ, μHE[n - 1] (A i)) := by simp
      rw [← h1, ← h2]
      exact h_main
    -- Therefore target function = iSup gk
    have h_g_eq : (fun s : ℝ => μHE[n - 1] {x ∈ B | f x = s}) =
        fun s : ℝ => ⨆ k, gk k s := by
      funext s
      have h1 : μHE[n - 1] {x ∈ B | f x = s} = μHE[n - 1] (⋃ k, {x ∈ Bk k | f x = s}) := by
        rw [h_level_union s]
      rw [h1, h_measure_union s]
      <;> rfl
    rw [h_g_eq]
    exact AEMeasurable.iSup hgk_ae
  · -- Case ¬(a < b), i.e. a ≥ b
    have h_Ioc_empty : Set.Ioc a b = ∅ := by
      ext x
      simp only [Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]
      intro h
      linarith
    have h : volume.restrict (Set.Ioc a b) = 0 := by
      rw [h_Ioc_empty] <;> simp
    rw [h] <;> simp

end Geometry
