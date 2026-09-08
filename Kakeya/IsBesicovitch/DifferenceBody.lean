/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib

/-!
# A quantitative difference-body bound in dimension three

This file proves the elementary difference-body estimate used by the separated-direction
Katz--Tao argument.  The proof uses the covariogram of a convex compact set and a ten-shell
discretization.  Its constant is deliberately explicit.
-/

@[expose] public section

open MeasureTheory Set
open scoped Pointwise ENNReal

namespace Kakeya.IsBesicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The overlap whose translation parameter is a point of the difference body. -/
def differenceOverlap (K : Set E) (z : E) : Set E :=
  K ∩ (fun y ↦ z + y) ⁻¹' K

private lemma measurable_volume_differenceOverlap {K : Set E} (hK : MeasurableSet K) :
    Measurable fun z ↦ volume (differenceOverlap K z) := by
  let A : Set (E × E) := {p | p.2 ∈ K ∧ p.1 + p.2 ∈ K}
  have hA : MeasurableSet A := by
    exact (hK.preimage measurable_snd).inter
      (hK.preimage (measurable_fst.add measurable_snd))
  have hm := measurable_measure_prodMk_left (ν := volume) hA
  convert hm using 1
  funext z
  congr 1

/-- The integral of the overlap function is the square of the volume. -/
lemma lintegral_volume_differenceOverlap {K : Set E} (hK : MeasurableSet K) :
    ∫⁻ z, volume (differenceOverlap K z) = volume K * volume K := by
  let A : Set (E × E) := {p | p.2 ∈ K ∧ p.1 + p.2 ∈ K}
  have hA : MeasurableSet A := by
    exact (hK.preimage measurable_snd).inter
      (hK.preimage (measurable_fst.add measurable_snd))
  have hpre : (fun p : E × E ↦ (p.1 - p.2, p.2)) ⁻¹' A = K ×ˢ K := by
    ext p
    simp only [A, mem_preimage, mem_setOf_eq, mem_prod]
    constructor
    · rintro ⟨hp2, hp1⟩
      exact ⟨by simpa only [sub_add_cancel] using hp1, hp2⟩
    · rintro ⟨hp1, hp2⟩
      exact ⟨hp2, by simpa only [sub_add_cancel] using hp1⟩
  calc
    ∫⁻ z, volume (differenceOverlap K z)
        = (volume.prod volume) A := by
          rw [Measure.prod_apply hA]
          rfl
    _ = (volume.prod volume)
          ((fun p : E × E ↦ (p.1 - p.2, p.2)) ⁻¹' A) := by
            symm
            exact (measurePreserving_sub_prod volume volume).measure_preimage hA.nullMeasurableSet
    _ = (volume.prod volume) (K ×ˢ K) := by rw [hpre]
    _ = volume K * volume K := Measure.prod_prod K K

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A scalar copy of a convex set lies in the appropriate overlap. -/
lemma image_homothety_subset_differenceOverlap {K : Set E} (hK : Convex ℝ K)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {a b : E} (ha : a ∈ K) (hb : b ∈ K) :
    AffineMap.homothety b (1 - t) '' K ⊆ differenceOverlap K (t • (a - b)) := by
  rintro y ⟨x, hx, rfl⟩
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hsum : (1 - t) + t = 1 := by ring
  constructor
  · have hmem := hK hx hb h1t ht0 hsum
    have heq : AffineMap.homothety b (1 - t) x = (1 - t) • x + t • b := by
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
      module
    rw [heq]
    exact hmem
  · have hmem := hK hx ha h1t ht0 hsum
    have heq : t • (a - b) + AffineMap.homothety b (1 - t) x =
        (1 - t) • x + t • a := by
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
      module
    change t • (a - b) + AffineMap.homothety b (1 - t) x ∈ K
    rw [heq]
    exact hmem

/-- Points in a contracted difference body have a quantitatively large overlap. -/
lemma volume_differenceOverlap_lower {K : Set E} (hK : Convex ℝ K)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {z : E} (hz : z ∈ t • (K - K)) :
    ENNReal.ofReal ((1 - t) ^ Module.finrank ℝ E) * volume K
      ≤ volume (differenceOverlap K z) := by
  rw [mem_smul_set] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rcases hw with ⟨a, ha, b, hb, rfl⟩
  have hpow : 0 ≤ (1 - t) ^ Module.finrank ℝ E := pow_nonneg (sub_nonneg.mpr ht1) _
  calc
    ENNReal.ofReal ((1 - t) ^ Module.finrank ℝ E) * volume K
        = volume (AffineMap.homothety b (1 - t) '' K) := by
          rw [Measure.addHaar_image_homothety, abs_of_nonneg hpow]
    _ ≤ volume (differenceOverlap K (t • (a - b))) :=
      measure_mono (image_homothety_subset_differenceOverlap hK ht0 ht1 ha hb)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The difference body of a compact set is compact. -/
lemma IsCompact.difference {K : Set E} (hK : IsCompact K) : IsCompact (K - K) := by
  simpa only [sub_eq_add_neg] using hK.add hK.neg

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma smul_set_subset_smul_set_of_nonneg_of_le {D : Set E} (hD : Convex ℝ D)
    (hzero : (0 : E) ∈ D) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : 0 < s) :
    r • D ⊆ s • D := by
  intro x hx
  rw [mem_smul_set] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  have ht : r / s ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hr hs.le, (div_le_one hs).2 hrs⟩
  refine ⟨(r / s) • y, hD.smul_mem_of_zero_mem hzero hy ht, ?_⟩
  · rw [smul_smul]
    congr 1
    field_simp

private abbrev Euclidean3 := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th shell in the ten-shell discretization, for `0 ≤ i < 9`. -/
private def differenceShell (K : Set Euclidean3) (i : Fin 9) : Set Euclidean3 :=
  ((((i : ℕ) + 1 : ℕ) : ℝ) / 10) • (K - K) \
    ((((i : ℕ) : ℝ) / 10) • (K - K))

private lemma measurableSet_differenceShell {K : Set Euclidean3} (hK : IsCompact K) (i : Fin 9) :
    MeasurableSet (differenceShell K i) := by
  apply MeasurableSet.diff
  · exact ((IsCompact.difference hK).image (continuous_const_smul _)).measurableSet
  · exact ((IsCompact.difference hK).image (continuous_const_smul _)).measurableSet

private lemma pairwiseDisjoint_differenceShell {K : Set Euclidean3} (hK : Convex ℝ K)
    (hKne : K.Nonempty) : Set.PairwiseDisjoint (Set.univ : Set (Fin 9)) (differenceShell K) := by
  have hD : Convex ℝ (K - K) := hK.sub hK
  obtain ⟨x, hx⟩ := hKne
  have hzero : (0 : Euclidean3) ∈ K - K := ⟨x, hx, x, hx, sub_self x⟩
  intro i _ j _ hij
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h ↦ hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hij' | hji'
  · apply Set.disjoint_left.2
    intro z hzi hzj
    have hle_nat : (i : ℕ) + 1 ≤ (j : ℕ) := Nat.succ_le_iff.mpr hij'
    have hle_real : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hle_nat
    have hjpos : (0 : ℝ) < (j : ℕ) := by exact_mod_cast (Nat.zero_lt_of_lt hij')
    exact hzj.2 (smul_set_subset_smul_set_of_nonneg_of_le hD hzero
      (by positivity) (by norm_num; linarith) (by positivity) hzi.1)
  · apply Set.disjoint_left.2
    intro z hzi hzj
    have hle_nat : (j : ℕ) + 1 ≤ (i : ℕ) := Nat.succ_le_iff.mpr hji'
    have hle_real : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hle_nat
    have hipos : (0 : ℝ) < (i : ℕ) := by exact_mod_cast (Nat.zero_lt_of_lt hji')
    exact hzi.2 (smul_set_subset_smul_set_of_nonneg_of_le hD hzero
      (by positivity) (by norm_num; linarith) (by positivity) hzj.1)

private lemma volume_differenceShell {K : Set Euclidean3} (hK : IsCompact K)
    (hKconv : Convex ℝ K) (hKne : K.Nonempty) (i : Fin 9) :
    volume (differenceShell K i) =
      (ENNReal.ofReal (((((i : ℕ) + 1 : ℕ) : ℝ) / 10) ^ 3) -
        ENNReal.ofReal ((((i : ℕ) : ℝ) / 10) ^ 3)) * volume (K - K) := by
  have hDcompact : IsCompact (K - K) := IsCompact.difference hK
  have hinner_compact : IsCompact ((((i : ℕ) : ℝ) / 10) • (K - K)) :=
    hDcompact.image (continuous_const_smul _)
  have hsub : ((((i : ℕ) : ℝ) / 10) • (K - K)) ⊆
      ((((i : ℕ) + 1 : ℕ) : ℝ) / 10) • (K - K) := by
    obtain ⟨x, hx⟩ := hKne
    exact smul_set_subset_smul_set_of_nonneg_of_le (hKconv.sub hKconv)
      ⟨x, hx, x, hx, sub_self x⟩ (by positivity) (by norm_num; linarith) (by positivity)
  rw [differenceShell, measure_sdiff hsub hinner_compact.measurableSet.nullMeasurableSet
    hinner_compact.measure_ne_top]
  simp only [Measure.addHaar_smul, finrank_euclideanSpace_fin]
  have houter_nonneg : 0 ≤ (((((i : ℕ) + 1 : ℕ) : ℝ) / 10) ^ 3) := by positivity
  have hinner_nonneg : 0 ≤ ((((i : ℕ) : ℝ) / 10) ^ 3) := by positivity
  rw [abs_of_nonneg houter_nonneg, abs_of_nonneg hinner_nonneg]
  exact (ENNReal.sub_mul fun _ _ ↦ hDcompact.measure_ne_top).symm

private noncomputable def shellCoefficient (i : Fin 9) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - ((((i : ℕ) + 1 : ℕ) : ℝ) / 10)) ^ 3)

private lemma shellCoefficient_toReal (i : Fin 9) :
    (shellCoefficient i).toReal =
      (1 - ((((i : ℕ) + 1 : ℕ) : ℝ) / 10)) ^ 3 := by
  rw [shellCoefficient, ENNReal.toReal_ofReal]
  have hi : (i : ℕ) < 9 := i.isLt
  have hi' : (((i : ℕ) : ℝ) + 1) / 10 ≤ 1 := by
    apply (div_le_one (by norm_num : (0 : ℝ) < 10)).2
    have hn : (i : ℕ) + 1 ≤ 10 := by omega
    exact_mod_cast hn
  have hi'' : ((((i : ℕ) + 1 : ℕ) : ℝ) / 10) ≤ 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hi'
  exact pow_nonneg (sub_nonneg.mpr hi'') _

private lemma differenceOverlap_lower_on_shell {K : Set Euclidean3} (hK : Convex ℝ K)
    (i : Fin 9) {z : Euclidean3} (hz : z ∈ differenceShell K i) :
    shellCoefficient i * volume K ≤ volume (differenceOverlap K z) := by
  have h := volume_differenceOverlap_lower hK
    (t := ((((i : ℕ) + 1 : ℕ) : ℝ) / 10)) (by positivity) (by
      have hi : (i : ℕ) < 9 := i.isLt
      apply (div_le_one (by norm_num : (0 : ℝ) < 10)).2
      have hn : (i : ℕ) + 1 ≤ 10 := by omega
      exact_mod_cast hn)
    hz.1
  simpa only [shellCoefficient, finrank_euclideanSpace_fin] using h

private lemma lintegral_differenceOverlap_shell_lower {K : Set Euclidean3}
    (hKcompact : IsCompact K) (hKconv : Convex ℝ K) (i : Fin 9) :
    shellCoefficient i * volume K * volume (differenceShell K i) ≤
      ∫⁻ z in differenceShell K i, volume (differenceOverlap K z) := by
  rw [← setLIntegral_const]
  exact setLIntegral_mono (measurable_volume_differenceOverlap hKcompact.measurableSet)
    fun _ hz ↦ differenceOverlap_lower_on_shell hKconv i hz

private lemma volumeReal_differenceShell {K : Set Euclidean3} (hK : IsCompact K)
    (hKconv : Convex ℝ K) (hKne : K.Nonempty) (i : Fin 9) :
    volume.real (differenceShell K i) =
      ((((((i : ℕ) + 1 : ℕ) : ℝ) / 10) ^ 3) -
        ((((i : ℕ) : ℝ) / 10) ^ 3)) * volume.real (K - K) := by
  rw [Measure.real_def, volume_differenceShell hK hKconv hKne]
  rw [ENNReal.toReal_mul]
  have hle : ENNReal.ofReal ((((i : ℕ) : ℝ) / 10) ^ 3) ≤
      ENNReal.ofReal (((((i : ℕ) + 1 : ℕ) : ℝ) / 10) ^ 3) := by
    apply ENNReal.ofReal_le_ofReal
    gcongr
    norm_num
  rw [ENNReal.toReal_sub_of_le hle (by simp)]
  have houter : 0 ≤ (((((i : ℕ) + 1 : ℕ) : ℝ) / 10) ^ 3) := by positivity
  have hinner : 0 ≤ ((((i : ℕ) : ℝ) / 10) ^ 3) := by positivity
  rw [ENNReal.toReal_ofReal houter, ENNReal.toReal_ofReal hinner]
  rfl

private lemma real_shell_coefficient_sum (a b : ℝ) :
    (∑ i : Fin 9,
      (1 - ((((i : ℕ) + 1 : ℕ) : ℝ) / 10)) ^ 3 * a *
        (((((((i : ℕ) + 1 : ℕ) : ℝ) / 10) ^ 3) -
          ((((i : ℕ) : ℝ) / 10) ^ 3)) * b)) =
      (37269 / 1000000 : ℝ) * a * b := by
  norm_num [Fin.sum_univ_succ]
  ring

private lemma sum_shell_overlap_le {K : Set Euclidean3} (hKcompact : IsCompact K)
    (hKconv : Convex ℝ K) (hKne : K.Nonempty) :
    (∑ i : Fin 9, shellCoefficient i * volume K * volume (differenceShell K i)) ≤
      volume K * volume K := by
  calc
    (∑ i : Fin 9, shellCoefficient i * volume K * volume (differenceShell K i))
        ≤ ∑ i : Fin 9, ∫⁻ z in differenceShell K i,
            volume (differenceOverlap K z) := by
          exact Finset.sum_le_sum fun i _ ↦
            lintegral_differenceOverlap_shell_lower hKcompact hKconv i
    _ = ∫⁻ z in ⋃ i ∈ Finset.univ, differenceShell K i,
          volume (differenceOverlap K z) := by
          symm
          have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 9)))
              (differenceShell K) := by
            simpa using pairwiseDisjoint_differenceShell hKconv hKne
          simpa using lintegral_biUnion_finset
            (s := Finset.univ)
            hpair
            (fun i _ ↦ measurableSet_differenceShell hKcompact i)
            (fun z ↦ volume (differenceOverlap K z))
    _ ≤ ∫⁻ z, volume (differenceOverlap K z) := by
      exact setLIntegral_le_lintegral _ _
    _ = volume K * volume K :=
      lintegral_volume_differenceOverlap hKcompact.measurableSet

/-- The explicit ten-shell difference-body inequality in dimension three. -/
theorem volumeReal_difference_le_explicit
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hKcompact : IsCompact K)
    (hKconv : Convex ℝ K) (hKvol : volume K ≠ 0) :
    37269 * volume.real (K - K) ≤ 1000000 * volume.real K := by
  have hKne : K.Nonempty := by
    by_contra hKne
    have hKempty : K = ∅ := not_nonempty_iff_eq_empty.mp hKne
    apply hKvol
    rw [hKempty]
    simp
  have hKfinite : volume K ≠ ∞ := hKcompact.measure_ne_top
  have hDfinite : volume (K - K) ≠ ∞ := (IsCompact.difference hKcompact).measure_ne_top
  have hshellfinite (i : Fin 9) : volume (differenceShell K i) ≠ ∞ := by
    rw [volume_differenceShell hKcompact hKconv hKne]
    exact ENNReal.mul_ne_top (by simp) hDfinite
  have hsum := sum_shell_overlap_le hKcompact hKconv hKne
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hKfinite hKfinite) hsum
  rw [ENNReal.toReal_sum (fun i _ ↦ ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by simp [shellCoefficient]) hKfinite) (hshellfinite i))] at hreal
  simp_rw [ENNReal.toReal_mul, shellCoefficient_toReal,
    ← Measure.real_def, volumeReal_differenceShell hKcompact hKconv hKne] at hreal
  rw [real_shell_coefficient_sum] at hreal
  have hKreal_pos : 0 < volume.real K := ENNReal.toReal_pos hKvol hKfinite
  norm_num at hreal ⊢
  nlinarith

end Kakeya.IsBesicovitch
