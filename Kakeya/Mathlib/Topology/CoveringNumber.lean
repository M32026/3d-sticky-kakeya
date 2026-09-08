/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
We collect lemmas on covering numbers and packing numbers.

-/

@[expose] public section

open Metric MeasureTheory

/-- In a proper space (e.g. a finite-dimensional Euclidean space), the covering
number of a bounded set at any positive radius is finite. -/
theorem Bornology.IsBounded.coveringNumber_ne_top
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X] {s : Set X}
    (hs : Bornology.IsBounded s) {r : NNReal} (hr : 0 < r) :
    Metric.coveringNumber r s ≠ ⊤ := by
  have hs_tb : TotallyBounded s :=
    hs.isCompact_closure.totallyBounded.subset subset_closure
  obtain ⟨N, hNY, hNfin, hNcov⟩ :=
    Metric.exists_finite_isCover_of_totallyBounded hr.ne' hs_tb
  exact ne_top_of_le_ne_top hNfin.encard_lt_top.ne (hNcov.coveringNumber_le_encard hNY)

/-- In a proper space, the packing number of a bounded set at any positive radius is finite. -/
theorem Bornology.IsBounded.packingNumber_ne_top
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X] {s : Set X}
    (hs : Bornology.IsBounded s) {r : NNReal} (hr : 0 < r) :
    Metric.packingNumber r s ≠ ⊤ := by
  have h04 : 0 < r / 2 := by positivity
  have hb := hs.coveringNumber_ne_top (r := r / 2) h04
  exact ne_top_of_le_ne_top hb (by
    calc
      Metric.packingNumber r s = Metric.packingNumber (2 * (r / 2)) s := by
        congr 1
        ring
      _ ≤ Metric.externalCoveringNumber (r / 2) s :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber (r / 2) s
      _ ≤ Metric.coveringNumber (r / 2) s :=
        Metric.externalCoveringNumber_le_coveringNumber (r / 2) s)

/-- Finset version of `Metric.exists_set_encard_eq_coveringNumber`. -/
theorem Metric.exists_finset_card_eq_coveringNumber
    {X : Type*} [PseudoMetricSpace X] {r : NNReal} {s : Set X}
    (h : Metric.coveringNumber r s ≠ ⊤) :
    ∃ C : Finset X, (C : Set X) ⊆ s ∧ Metric.IsCover r s C ∧
      (C.card : ℕ∞) = Metric.coveringNumber r s := by
  obtain ⟨C, hCs, hCfin, hCcov, hCcard⟩ := Metric.exists_set_encard_eq_coveringNumber h
  lift C to Finset X using hCfin
  refine ⟨C, hCs, hCcov, ?_⟩
  rw [← hCcard, Set.encard_coe_eq_coe_finsetCard]

/-- Bounded-set variant: in a proper space, a bounded set has a finite covering
realised by an explicit `Finset`. -/
theorem Bornology.IsBounded.exists_finset_card_eq_coveringNumber
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X] {s : Set X}
    (hs : Bornology.IsBounded s) {r : NNReal} (hr : 0 < r) :
    ∃ C : Finset X, (C : Set X) ⊆ s ∧ Metric.IsCover r s C ∧
      (C.card : ℕ∞) = Metric.coveringNumber r s :=
  Metric.exists_finset_card_eq_coveringNumber (hs.coveringNumber_ne_top hr)

/-! # Boundedly overlapping ball covers

A maximal `w`-separated subset of a bounded set yields a cover of that set by the closed
`w`-balls around its points, with pointwise overlap at most `5 ^ finrank ℝ E`. The overlap constant
comes from `Besicovitch.card_le_of_separated` after rescaling. -/

section BoundedOverlap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A separated set inside a ball of twice its separation is small** (blueprint
`lem:step5SeparatedCardBound`): a `w`-separated finite set all of whose points lie within `2 * w`
of a common point `x` has at most `5 ^ finrank ℝ E` elements.

The radius `2 * w` is exactly the one for which `Besicovitch.card_le_of_separated` is stated. -/
theorem Metric.IsSeparated.card_le_pow_of_dist_le {w : NNReal} (hw : 0 < w) {T : Finset E}
    (hsep : Metric.IsSeparated (w : ENNReal) (T : Set E)) {x : E}
    (hT : ∀ c ∈ T, dist c x ≤ 2 * (w : ℝ)) :
    T.card ≤ 5 ^ Module.finrank ℝ E := by
  classical
  let φ : E → E := fun c => (w : ℝ)⁻¹ • (c - x)
  have hwne : (w : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hw)
  have hw_inv_pos : 0 < (w : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hw)
  have hw_inv_nonneg : 0 ≤ (w : ℝ)⁻¹ := le_of_lt hw_inv_pos
  have hw_inv_abs : ‖(w : ℝ)⁻¹‖ = (w : ℝ)⁻¹ := abs_eq_self.mpr hw_inv_nonneg
  have hφnorm : ∀ a b : E, ‖φ a - φ b‖ = (w : ℝ)⁻¹ * dist a b := by
    intro a b
    calc
      ‖φ a - φ b‖ = ‖(w : ℝ)⁻¹ • (a - b)‖ := by
        congr 1
        calc
          φ a - φ b = (w : ℝ)⁻¹ • (a - x) - (w : ℝ)⁻¹ • (b - x) := by simp [φ]
          _ = (w : ℝ)⁻¹ • ((a - x) - (b - x)) := by rw [← smul_sub]
          _ = (w : ℝ)⁻¹ • (a - b) := by congr 1; abel
      _ = (w : ℝ)⁻¹ * dist a b := by
        rw [norm_smul, hw_inv_abs]
        simp [dist_eq_norm]
  have hφ : Function.Injective φ := by
    intro a b hab
    have hnorm0 : ‖φ a - φ b‖ = 0 := by
      have : φ a - φ b = 0 := sub_eq_zero.mpr hab
      rw [this, norm_zero]
    have hprod : (w : ℝ)⁻¹ * dist a b = 0 := by
      rw [← hφnorm a b]
      exact hnorm0
    have hdist0 : dist a b = 0 := by
      rcases mul_eq_zero.mp hprod with hmul | hdist
      · exfalso
        exact (inv_ne_zero hwne) hmul
      · exact hdist
    exact dist_eq_zero.mp hdist0
  have hnorm_le : ∀ c ∈ T.image φ, ‖c‖ ≤ 2 := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨a, ha, rfl⟩
    calc
      ‖φ a‖ = ‖(w : ℝ)⁻¹ • (a - x)‖ := by simp [φ]
      _ = ‖(w : ℝ)⁻¹‖ * ‖a - x‖ := by rw [norm_smul]
      _ = (w : ℝ)⁻¹ * dist a x := by
        rw [hw_inv_abs]
        simp [dist_eq_norm]
      _ ≤ (w : ℝ)⁻¹ * (2 * (w : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (hT a ha) hw_inv_nonneg
      _ = 2 := by
        rw [show (w : ℝ)⁻¹ * (2 * (w : ℝ)) = 2 * ((w : ℝ)⁻¹ * (w : ℝ)) by ring]
        rw [inv_mul_cancel₀ hwne]
        norm_num
  have hsep_le : ∀ c ∈ T.image φ, ∀ d ∈ T.image φ, c ≠ d → 1 ≤ ‖c - d‖ := by
    intro c hc d hd hne
    rcases Finset.mem_image.mp hc with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hd with ⟨b, hb, rfl⟩
    have hab_ne : a ≠ b := by
      intro hab_eq
      apply hne
      rw [hab_eq]
    have hr_nn : 0 ≤ (w : ℝ) := w.coe_nonneg
    have hexy : (w : ENNReal) < edist a b :=
      hsep (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab_ne
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal (p := w)] at hexy
    have hdist_gt : (w : ℝ) < dist a b :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr_nn).mp hexy
    have hdist_lt : (w : ℝ)⁻¹ * (w : ℝ) < (w : ℝ)⁻¹ * dist a b :=
      mul_lt_mul_of_pos_left hdist_gt hw_inv_pos
    have hdist_div : 1 ≤ (w : ℝ)⁻¹ * dist a b := by
      rw [inv_mul_cancel₀ hwne] at hdist_lt
      exact le_of_lt hdist_lt
    rwa [hφnorm a b]
  have hcard : (T.image φ).card = T.card := Finset.card_image_of_injective T hφ
  rw [← hcard]
  exact Besicovitch.card_le_of_separated (T.image φ) hnorm_le hsep_le

open Classical in
/-- **Bounded overlap of the balls of a separated set** (blueprint `lem:step5OverlapBound`): the
closed `w`-balls around a `w`-separated finite set have pointwise overlap at most
`5 ^ finrank ℝ E`. -/
theorem Metric.IsSeparated.card_filter_mem_closedBall_le {w : NNReal} (hw : 0 < w) {T : Finset E}
    (hsep : Metric.IsSeparated (w : ENNReal) (T : Set E)) (x : E) :
    {c ∈ T | x ∈ Metric.closedBall c (w : ℝ)}.card ≤ 5 ^ Module.finrank ℝ E := by
  let S : Finset E := {c ∈ T | x ∈ Metric.closedBall c (w : ℝ)}
  have hS : (S : Set E) ⊆ (T : Set E) := by
    intro c hc
    exact (Finset.mem_filter.mp hc).1
  have hX : ∀ c ∈ S, dist c x ≤ 2 * (w : ℝ) := by
    intro c hc
    have hx : x ∈ Metric.closedBall c (w : ℝ) := (Finset.mem_filter.mp hc).2
    have hdist : dist c x ≤ (w : ℝ) := by
      simpa [Metric.mem_closedBall, dist_comm] using hx
    exact le_trans hdist (by nlinarith [show (0 : ℝ) ≤ (w : ℝ) from w.coe_nonneg])
  exact Metric.IsSeparated.card_le_pow_of_dist_le hw (hsep.subset hS) hX

open Classical in
/-- **Boundedly overlapping ball cover of a bounded set** (blueprint `lem:step5Cover`): a bounded
set in a finite-dimensional real normed space admits a finite `w`-separated subset whose closed
`w`-balls cover it with pointwise overlap at most `5 ^ finrank ℝ E`.

The witness is a maximal `w`-separated subset, `Metric.maximalSeparatedSet`. -/
theorem Bornology.IsBounded.exists_finset_isSeparated_isCover_closedBall {s : Set E}
    (hs : Bornology.IsBounded s) {w : NNReal} (hw : 0 < w) :
    ∃ T : Finset E, (T : Set E) ⊆ s ∧ Metric.IsSeparated (w : ENNReal) (T : Set E) ∧
      s ⊆ ⋃ c ∈ T, Metric.closedBall c (w : ℝ) ∧
      ∀ x : E, {c ∈ T | x ∈ Metric.closedBall c (w : ℝ)}.card ≤ 5 ^ Module.finrank ℝ E := by
  let A : Set E := Metric.maximalSeparatedSet w s
  have hpk : Metric.packingNumber w s ≠ ⊤ := hs.packingNumber_ne_top hw
  have hAencard_ne_top : A.encard ≠ ⊤ := by
    simpa [A] using (Metric.encard_maximalSeparatedSet (ε := w) (A := s) hpk).trans_ne hpk
  have hAfin : A.Finite := Set.encard_ne_top_iff.mp hAencard_ne_top
  let T : Finset E := hAfin.toFinset
  have hT_coe : (T : Set E) = A := by
    ext c
    simp [T]
  have hT_sub : (T : Set E) ⊆ s := by
    rw [hT_coe]
    exact Metric.maximalSeparatedSet_subset (ε := w) (A := s)
  have hT_sep : Metric.IsSeparated (w : ENNReal) (T : Set E) := by
    rw [hT_coe]
    exact Metric.isSeparated_maximalSeparatedSet (ε := w) (A := s)
  have hT_cover : s ⊆ ⋃ y ∈ (T : Set E), Metric.closedBall y (w : ℝ) := by
    rw [hT_coe]
    exact (Metric.isCover_iff_subset_iUnion_closedBall (ε := w) (N := A) (s := s)).mp
      (Metric.isCover_maximalSeparatedSet (ε := w) (A := s) hpk)
  exact ⟨T, hT_sub, hT_sep, hT_cover, by
    intro x
    exact Metric.IsSeparated.card_filter_mem_closedBall_le hw hT_sep x⟩

end BoundedOverlap

namespace Metric

/- # Covering number and volume. -/
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

 

/-- The multiplicative constant in `coveringNumber_mul_pow_le_volume_cthickening`
and in `packingNumber_mul_pow_le_volume_cthickening`. It depends only on the dimension. -/
@[nolint defsWithUnderscore]
noncomputable abbrev coveringNumber_mul_pow_le_volume_cthickening.C (n : ℕ) : NNReal :=
  ⟨(1 / 2) ^ n * (Real.sqrt Real.pi ^ n / Real.Gamma (n / 2 + 1)), by positivity⟩

theorem coveringNumber_mul_pow_le_volume_cthickening.C_pos (n : ℕ) :
    0 < coveringNumber_mul_pow_le_volume_cthickening.C n := by
  rw [← NNReal.coe_lt_coe]
  change (0 : ℝ) < (1 / 2) ^ n * (Real.sqrt Real.pi ^ n / Real.Gamma (n / 2 + 1))
  positivity

/-- The volume of the closed ball of radius `r/2` in a finite-dimensional inner product space,
expressed in terms of the constant `coveringNumber_mul_pow_le_volume_cthickening.C`. -/
theorem volume_closedBall_half (x : E) (r : NNReal) :
    volume (Metric.closedBall x ((r : ℝ) / 2)) =
      (coveringNumber_mul_pow_le_volume_cthickening.C (Module.finrank ℝ E) : ENNReal) *
        (r : ENNReal) ^ Module.finrank ℝ E := by
  set n := Module.finrank ℝ E
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  rw [InnerProductSpace.volume_closedBall x ((r : ℝ) / 2),
      show ((r : ℝ) / 2) = (1 / 2) * r by ring,
      ENNReal.ofReal_mul hhalf, mul_pow, ← ENNReal.ofReal_pow hhalf,
      ENNReal.ofReal_coe_nnreal,
      show (coveringNumber_mul_pow_le_volume_cthickening.C n : ENNReal) =
          ENNReal.ofReal ((1 / 2) ^ n) *
            ENNReal.ofReal (Real.sqrt Real.pi ^ n / Real.Gamma (n / 2 + 1)) by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact (ENNReal.ofReal_eq_coe_nnreal _).symm]
  ring

/-- **Volume of a centred ball, in terms of `C_cov`** (blueprint `lem:closedBallVolumeCcov`):
`|B̄(0, r)| = ofReal (2 ^ d · C_cov d · r ^ d)` with `d = dim E`, i.e. `ω_d = 2 ^ d · C_cov d` is
the volume of the unit ball.  This is `Metric.volume_closedBall_half` at `s = (2 r)₊`, rewritten
as a single `ENNReal.ofReal`. -/
theorem volume_closedBall_eq_ccov_mul_pow {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.closedBall (0 : E) r)
      = ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E
          * (coveringNumber_mul_pow_le_volume_cthickening.C (Module.finrank ℝ E) : ℝ)
          * r ^ Module.finrank ℝ E) := by
  set n := Module.finrank ℝ E
  let s : NNReal := ⟨2 * r, by positivity⟩
  have hs2 : (s : ℝ) = 2 * r := rfl
  have hsr : (s : ℝ) / 2 = r := by rw [hs2]; ring
  have h2r : (0 : ℝ) ≤ 2 * r := by positivity
  have hC0 : (0 : ℝ) ≤ (coveringNumber_mul_pow_le_volume_cthickening.C n : ℝ) :=
    (coveringNumber_mul_pow_le_volume_cthickening.C n).property
  conv_lhs => rw [← hsr]
  rw [volume_closedBall_half (0 : E) s, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_coe_nnreal, hs2, ← ENNReal.ofReal_pow h2r]
  have hmerge : ENNReal.ofReal ((coveringNumber_mul_pow_le_volume_cthickening.C n : ℝ) *
      (2 * r) ^ n) = ENNReal.ofReal (coveringNumber_mul_pow_le_volume_cthickening.C n : ℝ) *
        ENNReal.ofReal ((2 * r) ^ n) :=
    ENNReal.ofReal_mul
      (p := (coveringNumber_mul_pow_le_volume_cthickening.C n : ℝ))
      (q := (2 * r) ^ n) hC0
  rw [← hmerge]
  congr 1
  rw [mul_pow]
  ring

/-- For a finite `r`-separated subset `T` of `s`, the disjoint closed balls of radius `r/2`
around the points of `T` are contained in the closed `r`-thickening of `s`. -/
private theorem card_mul_volume_closedBall_half_le_volume_cthickening
    {r : NNReal} {s : Set E} {T : Finset E} (hTs : (T : Set E) ⊆ s)
    (hTsep : IsSeparated (r : ENNReal) (T : Set E)) :
    (T.card : ENNReal) * volume (Metric.closedBall (0 : E) ((r : ℝ) / 2)) ≤
      volume (Metric.cthickening (r : ℝ) s) := by
  have hr_nn : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
  have hdisj : (T : Set E).PairwiseDisjoint
      (fun x => Metric.closedBall x ((r : ℝ) / 2)) := by
    intro x hx y hy hxy
    have hexy : (r : ENNReal) < edist x y := hTsep hx hy hxy
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal (p := r)] at hexy
    exact Metric.closedBall_disjoint_closedBall <| by
      have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr_nn).mp hexy
      linarith
  have hsub : ∀ x ∈ T, Metric.closedBall x ((r : ℝ) / 2) ⊆ Metric.cthickening (r : ℝ) s :=
    fun x hx => (Metric.closedBall_subset_closedBall (by linarith)).trans
      (Metric.closedBall_subset_cthickening (hTs hx) (r : ℝ))
  calc (T.card : ENNReal) * volume (Metric.closedBall (0 : E) ((r : ℝ) / 2))
      = ∑ x ∈ T, volume (Metric.closedBall x ((r : ℝ) / 2)) := by
        simp [volume_closedBall_half, Finset.sum_const, nsmul_eq_mul]
    _ = volume (⋃ x ∈ T, Metric.closedBall x ((r : ℝ) / 2)) :=
        (MeasureTheory.measure_biUnion_finset hdisj
          (fun _ _ => measurableSet_closedBall)).symm
    _ ≤ volume (Metric.cthickening r s) := measure_mono (Set.iUnion₂_subset hsub)

/-- Volume lower bound on the closed `r`-thickening in terms of the packing number. -/
theorem packingNumber_mul_pow_le_volume_cthickening (r : NNReal) (s : Set E) :
    (coveringNumber_mul_pow_le_volume_cthickening.C (Module.finrank ℝ E) *
        packingNumber r s * r ^ (Module.finrank ℝ E) : ENNReal) ≤
      volume (cthickening r s) := by
  set n := Module.finrank ℝ E
  -- Rewrite LHS as `packingNumber * vol(closedBall(0, r/2))`.
  rw [show (coveringNumber_mul_pow_le_volume_cthickening.C n *
        packingNumber r s * r ^ n : ENNReal) =
      (packingNumber r s : ENNReal) *
        volume (closedBall (0 : E) (r / 2)) by
    rw [volume_closedBall_half (0 : E) r]; ring]
  -- Auxiliary: every separated subset `C ⊆ s` satisfies
  -- `C.encard * vol_ball ≤ vol_cthickening`.
  suffices key : ∀ C : Set E, C ⊆ s → IsSeparated (r : ENNReal) C →
      (C.encard : ENNReal) * volume (closedBall (0 : E) (r / 2)) ≤
        volume (cthickening r s) by
    -- Conclude via the iSup definition of `packingNumber`.
    rw [packingNumber, ENat.toENNReal_iSup, ENNReal.iSup_mul]
    refine iSup_le fun C => ?_
    rw [ENat.toENNReal_iSup, ENNReal.iSup_mul]
    refine iSup_le fun hCs => ?_
    rw [ENat.toENNReal_iSup, ENNReal.iSup_mul]
    exact iSup_le fun hCsep => key C hCs hCsep
  intro C hCs hCsep
  rcases Set.finite_or_infinite C with hCfin | hCinf
  · lift C to Finset E using hCfin
    rw [Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe]
    exact card_mul_volume_closedBall_half_le_volume_cthickening hCs hCsep
  · -- Infinite case: extract finite separated subsets of arbitrary size.
    rw [hCinf.encard_eq, ENat.toENNReal_top, ← ENNReal.iSup_natCast, ENNReal.iSup_mul]
    refine iSup_le fun N => ?_
    obtain ⟨T, hTC, hTcard⟩ := hCinf.exists_subset_card_eq N
    rw [show (N : ENNReal) = (T.card : ENNReal) from by exact_mod_cast hTcard.symm]
    exact card_mul_volume_closedBall_half_le_volume_cthickening (hTC.trans hCs)
      (hCsep.subset hTC)



/-- Lower bound on the volume of an `r`-thickening, dual to `volume_le_coveringNumber`.
Direct corollary of `packingNumber_mul_pow_le_volume_cthickening` via
`coveringNumber ≤ packingNumber`. -/
theorem coveringNumber_mul_pow_le_volume_cthickening (r : NNReal) (s : Set E) :
    (coveringNumber_mul_pow_le_volume_cthickening.C (Module.finrank ℝ E) *
        coveringNumber r s * r ^ (Module.finrank ℝ E) : ENNReal) ≤
      volume (Metric.cthickening r s) :=
  (packingNumber_mul_pow_le_volume_cthickening r s).trans' <| by
    gcongr; exact_mod_cast coveringNumber_le_packingNumber r s

/-- **Euclidean packing bound (multiplicative form).** A finite `r`-separated subset
`T` of a closed ball of radius `R` in an `n`-dimensional inner product space obeys
`T.card * r ^ n ≤ (2 * (R + r)) ^ n`, where `n = finrank ℝ E`. The dimensional volume
constant cancels, leaving an elementary bound: disjoint radius-`r/2` balls around the
points of `T` all lie in `closedBall x (R + r)`, and comparing volumes gives the count.
This is the packing estimate used to bound the number of essentially distinct slabs
through a point.
TODO rename in the `IsSeparated` namespace
-/
theorem card_mul_pow_le_of_isSeparated_subset_closedBall
    {r : NNReal} (hr : 0 < r) {x : E} {R : ℝ} (hR : 0 ≤ R) {T : Finset E}
    (hTsub : (T : Set E) ⊆ closedBall x R)
    (hTsep : IsSeparated (r : ENNReal) (T : Set E)) :
    (T.card : ℝ) * (r : ℝ) ^ Module.finrank ℝ E ≤
      (2 * (R + r)) ^ Module.finrank ℝ E := by
  set n := Module.finrank ℝ E with hn
  set κ : ℝ := Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1) with hκ
  have hκpos : 0 < κ := by
    have hΓ : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    have hnum : 0 < Real.sqrt Real.pi ^ n := by positivity
    exact div_pos hnum hΓ
  have hkey := card_mul_volume_closedBall_half_le_volume_cthickening hTsub hTsep
  have hvolL : volume (closedBall (0 : E) ((r : ℝ) / 2)) =
      ENNReal.ofReal ((r : ℝ) / 2) ^ n * ENNReal.ofReal κ :=
    InnerProductSpace.volume_closedBall 0 ((r : ℝ) / 2)
  have hvolR : volume (cthickening (r : ℝ) (closedBall x R)) =
      ENNReal.ofReal ((r : ℝ) + R) ^ n * ENNReal.ofReal κ := by
    rw [cthickening_closedBall r.coe_nonneg hR x]
    exact InnerProductSpace.volume_closedBall x ((r : ℝ) + R)
  rw [hvolL, hvolR,
    show (T.card : ENNReal) * (ENNReal.ofReal ((r : ℝ) / 2) ^ n * ENNReal.ofReal κ)
        = ENNReal.ofReal ((T.card : ℝ) * ((r : ℝ) / 2) ^ n * κ) from by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
      ring,
    show ENNReal.ofReal ((r : ℝ) + R) ^ n * ENNReal.ofReal κ
        = ENNReal.ofReal (((r : ℝ) + R) ^ n * κ) from by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]] at hkey
  have hreal : (T.card : ℝ) * ((r : ℝ) / 2) ^ n * κ ≤ ((r : ℝ) + R) ^ n * κ :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hkey
  have hr2 : (T.card : ℝ) * ((r : ℝ) / 2) ^ n ≤ ((r : ℝ) + R) ^ n :=
    le_of_mul_le_mul_right hreal hκpos
  calc (T.card : ℝ) * (r : ℝ) ^ n
      = ((T.card : ℝ) * ((r : ℝ) / 2) ^ n) * 2 ^ n := by
        rw [mul_assoc, ← mul_pow]; ring_nf
    _ ≤ ((r : ℝ) + R) ^ n * 2 ^ n := by gcongr
    _ = (2 * (R + r)) ^ n := by rw [← mul_pow]; ring_nf

/-- **Euclidean packing bound (cardinality form).** A finite `r`-separated subset of a
closed ball of radius `R` in an `n`-dimensional inner product space has at most
`(2 * (R + r) / r) ^ n` elements.
TODO: rename in the `IsSeparated` namespace
-/
theorem card_le_of_isSeparated_subset_closedBall
    {r : NNReal} (hr : 0 < r) {x : E} {R : ℝ} (hR : 0 ≤ R) {T : Finset E}
    (hTsub : (T : Set E) ⊆ closedBall x R)
    (hTsep : IsSeparated (r : ENNReal) (T : Set E)) :
    (T.card : ℝ) ≤ (2 * (R + r) / (r : ℝ)) ^ Module.finrank ℝ E := by
  have hrn : (0 : ℝ) < (r : ℝ) ^ Module.finrank ℝ E := by positivity
  rw [div_pow, le_div_iff₀ hrn]
  exact card_mul_pow_le_of_isSeparated_subset_closedBall hr hR hTsub hTsep

end Metric

/-! ### The degenerate case of a zero-dimensional space

`Metric.volume_closedBall_eq_ccov_mul_pow` — like every volume-of-balls lemma it rests on —
assumes `[Nontrivial E]`.  The three lemmas below cover the complementary case `dim G = 0`,
which is what `Tube.volume_closedBall_perpSpace` meets when the ambient dimension is `1`. -/

section ZeroDim

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]

/-- **The zero space has total volume one** (blueprint `lem:zeroSpaceVolumeUniv`): the standard
orthonormal basis of `G` is indexed by the empty type, so its parallelepiped is `{0}`, which is
all of `G`, and `OrthonormalBasis.volume_parallelepiped` gives it measure `1`. -/
theorem MeasureTheory.volume_univ_of_finrank_eq_zero (h : Module.finrank ℝ G = 0) :
    volume (Set.univ : Set G) = 1 := by
  let b : OrthonormalBasis (Fin 0) ℝ G := by
    rw [← h]
    exact stdOrthonormalBasis ℝ G
  let B : Module.Basis (Fin 0) ℝ G := b.toBasis
  have hpar : (parallelepiped B : Set G) = Set.univ := by
    rw [parallelepiped_basis_eq B]
    ext x
    simp
  calc
    volume (Set.univ : Set G) = volume (parallelepiped B : Set G) := by rw [hpar]
    _ = B.addHaar (parallelepiped B : Set G) := by
      rw [← OrthonormalBasis.addHaar_eq_volume b]
    _ = 1 := Module.Basis.addHaar_self B

/-- **In the zero space every ball is the whole space** (blueprint
`lem:zeroSpaceClosedBallEqUniv`). -/
theorem Metric.closedBall_eq_univ_of_finrank_eq_zero (h : Module.finrank ℝ G = 0) {r : ℝ}
    (hr : 0 ≤ r) : Metric.closedBall (0 : G) r = Set.univ := by
  haveI : Subsingleton G := Module.finrank_zero_iff.mp h
  refine Set.eq_univ_of_forall fun z => ?_
  rw [Metric.mem_closedBall]
  have hz : z = 0 := Subsingleton.elim z 0
  rw [hz, dist_self]
  exact hr

/-- **Every ball of the zero space has volume one** (blueprint `lem:zeroSpaceBallVolume`). -/
theorem Metric.volume_closedBall_of_finrank_eq_zero (h : Module.finrank ℝ G = 0) {r : ℝ}
    (hr : 0 ≤ r) : volume (Metric.closedBall (0 : G) r) = 1 := by
  rw [Metric.closedBall_eq_univ_of_finrank_eq_zero h hr]
  exact MeasureTheory.volume_univ_of_finrank_eq_zero h

end ZeroDim
