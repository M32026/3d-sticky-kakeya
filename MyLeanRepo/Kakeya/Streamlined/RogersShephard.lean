import MyLeanRepo.Kakeya.Streamlined.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Convex.Measure
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Rogers-Shephard type inequality for convex sets in R^3

Main results:
- `rogers_shephard_3d`: `volume(K-L) * volume(K∩L) ≤ 64 * volume K * volume L`
- `convex_hull_intersection_bound`: `volume(conv(K∪L)) * volume(K∩L) ≤ 4096 * volume K * volume L`

The constants are not sharp but the proofs are elementary (no Brunn-Minkowski).
-/

noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace Kakeya.Streamlined

/-- Minkowski difference of two sets. -/
def minkowskiDiff (K L : Set Point3) : Set Point3 :=
  Set.image2 (· - ·) K L

/-- Translation of a set by a point. -/
def translateSet (z : Point3) (S : Set Point3) : Set Point3 :=
  (fun x => z + x) '' S

/-- Volume scaling under dilation in R^3. -/
lemma volume_dilateSet (c : ℝ) (hc : c ≠ 0) (S : Set Point3) :
    volume (c • S) = ENNReal.ofReal (|c|^3) * volume S := by
  have h1 := MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀ (d := 3) hc S
  have h2 : (μHE[3] : Measure Point3) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume 3
  rw [h2] at h1
  simpa [NNReal.coe_pow, abs_nonneg] using h1

/-- The Minkowski difference is convex when both K and L are. -/
lemma convex_minkowskiDiff {K L : Set Point3}
    (hK : Convex ℝ K) (hL : Convex ℝ L) :
    Convex ℝ (minkowskiDiff K L) := by
  intro z1 hz1 z2 hz2 a b ha hb hab
  rcases Set.mem_image2.mp hz1 with ⟨k1, hk1, l1, hl1, rfl⟩
  rcases Set.mem_image2.mp hz2 with ⟨k2, hk2, l2, hl2, rfl⟩
  let k := a • k1 + b • k2
  let l := a • l1 + b • l2
  have hk : k ∈ K := hK hk1 hk2 ha hb hab
  have hl : l ∈ L := hL hl1 hl2 ha hb hab
  have h5 : k - l = a • (k1 - l1) + b • (k2 - l2) := by
    simp only [k, l]
    rw [smul_sub, smul_sub] <;> abel
  exact Set.mem_image2.mpr ⟨k, hk, l, hl, h5⟩

/-- If `z ∈ minkowskiDiff K L`, then for `t ∈ [0,1]`:
`volume(K ∩ translateSet (t•z) L) ≥ (1 - t)^3 * volume(K ∩ L)`. -/
lemma convexity_intersection_inclusion {K L : Set Point3}
    (hK : Convex ℝ K) (hL : Convex ℝ L)
    {z : Point3} (hz : z ∈ minkowskiDiff K L) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (_h_inter_nonempty : (K ∩ L).Nonempty) :
    volume (K ∩ translateSet (t • z) L) ≥
      ENNReal.ofReal ((1 - t)^3) * volume (K ∩ L) := by
  rcases Set.mem_image2.mp hz with ⟨k, hk, l, hl, rfl⟩
  let a : Point3 := k
  have ha1 : a ∈ K := hk
  have ha2 : a - (k - l) ∈ L := by
    have h_eq : a - (k - l) = l := by simp [a]
    rw [h_eq]; exact hl
  let S : Set Point3 := (1 - t) • (K ∩ L)
  let T := translateSet (t • a) S
  have h1t_nonneg : 0 ≤ 1 - t := by linarith
  have h_sum : t + (1 - t) = 1 := by linarith
  have h_main_set : T ⊆ K ∩ translateSet (t • (k - l)) L := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases hx with ⟨u, hu, rfl⟩
    have hu1 : u ∈ K := hu.1
    have hu2 : u ∈ L := hu.2
    have h_in_K : t • a + (1 - t) • u ∈ K := hK ha1 hu1 ht h1t_nonneg h_sum
    have h_in_L_shift : t • a + (1 - t) • u - t • (k - l) ∈ L := by
      have h_eq2 : t • a + (1 - t) • u - t • (k - l) =
          t • (a - (k - l)) + (1 - t) • u := by
        simp [a, smul_sub, sub_smul] <;> abel
      rw [h_eq2]
      exact hL ha2 hu2 ht h1t_nonneg h_sum
    have h_in_trans : t • a + (1 - t) • u ∈ translateSet (t • (k - l)) L := by
      rw [translateSet, Set.mem_image]
      refine' ⟨t • a + (1 - t) • u - t • (k - l), h_in_L_shift, _⟩
      abel
    exact ⟨h_in_K, h_in_trans⟩
  have h_trans_iso : Isometry (fun y : Point3 => t • a + y) := by
    intro x y
    have h1 : dist (t • a + x) (t • a + y) = dist x y := by
      have h2 : (t • a + x) - (t • a + y) = x - y := by abel
      simp [dist_eq_norm, h2]
    simpa [edist_dist] using congr_arg ENNReal.ofReal h1
  have h_vol1 : volume T = volume S := by
    have h_T_def : T = (fun y : Point3 => t • a + y) '' S := by rfl
    rw [h_T_def]
    have h1 := Isometry.euclideanHausdorffMeasure_image (d := 3) h_trans_iso S
    have h2 : (μHE[3] : Measure Point3) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume 3
    rw [h2] at h1
    exact h1
  by_cases h_t1 : t = 1
  · rw [h_t1]; simp
  · have h_t_lt_one : t < 1 := lt_of_le_of_ne ht' h_t1
    have h_1t_pos : 0 < 1 - t := by linarith
    have h_1t_ne_zero : (1 - t) ≠ 0 := ne_of_gt h_1t_pos
    have h_dilation : volume S = ENNReal.ofReal ((1 - t)^3) * volume (K ∩ L) := by
      have h3 : |1 - t| = 1 - t := by
        rw [abs_of_pos h_1t_pos]
      have h := volume_dilateSet (1 - t) h_1t_ne_zero (K ∩ L)
      rw [h, h3]
    calc
      volume (K ∩ translateSet (t • (k - l)) L)
        ≥ volume T := volume.mono h_main_set
      _ = volume S := h_vol1
      _ = ENNReal.ofReal ((1 - t)^3) * volume (K ∩ L) := h_dilation

/-- Fubini identity for measurable sets. -/
lemma fubini_intersection_volume {K L : Set Point3}
    (hK_meas : MeasurableSet K) (hL_meas : MeasurableSet L) :
    ∫⁻ (z : Point3), volume (K ∩ translateSet z L) = volume K * volume L := by
  let g : Point3 → Point3 → ENNReal := fun x z =>
    Set.indicator K (fun _ => (1 : ENNReal)) x *
    Set.indicator L (fun _ => (1 : ENNReal)) (x - z)
  have g_meas : Measurable (fun p : Point3 × Point3 => g p.1 p.2) := by
    dsimp only [g]; fun_prop
  have h1 : ∀ (z : Point3), volume (K ∩ translateSet z L) = ∫⁻ (x : Point3), g x z := by
    intro z
    have h_set_eq : K ∩ translateSet z L = {x | x ∈ K ∧ x - z ∈ L} := by
      ext x
      simp only [translateSet, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hx, ⟨y, hy, rfl⟩⟩
        exact ⟨hx, by simpa using hy⟩
      · rintro ⟨hx, hxz⟩
        exact ⟨hx, x - z, hxz, by abel⟩
    have h_set_meas : MeasurableSet {x : Point3 | x ∈ K ∧ x - z ∈ L} :=
      hK_meas.inter (hL_meas.preimage (measurable_id.sub measurable_const))
    have h_indicator : (fun x : Point3 => g x z) =
        Set.indicator {x : Point3 | x ∈ K ∧ x - z ∈ L} (fun _ => (1 : ENNReal)) := by
      funext x
      dsimp only [g]
      by_cases hx : x ∈ K <;> by_cases hxz : x - z ∈ L <;>
        simp [Set.indicator_apply, hx, hxz] <;> ring
    have h_int : ∫⁻ (x : Point3), g x z = volume (K ∩ translateSet z L) := by
      rw [h_indicator, h_set_eq]
      rw [lintegral_indicator h_set_meas]
      simp
    exact h_int.symm
  have h_main1 : ∫⁻ (z : Point3), volume (K ∩ translateSet z L) =
      ∫⁻ (z : Point3), ∫⁻ (x : Point3), g x z := by
    congr with z; exact h1 z
  rw [h_main1]
  have h_fubini : ∫⁻ (z : Point3), ∫⁻ (x : Point3), g x z =
      ∫⁻ (x : Point3), ∫⁻ (z : Point3), g x z := by
    rw [← lintegral_prod (fun p : Point3 × Point3 => g p.1 p.2) g_meas.aemeasurable]
    rw [lintegral_prod_symm (fun p : Point3 × Point3 => g p.1 p.2) g_meas.aemeasurable]
  rw [h_fubini]
  have h_inner : ∀ (x : Point3), ∫⁻ (z : Point3), g x z =
      Set.indicator K (fun _ => (1 : ENNReal)) x * volume L := by
    intro x
    have h5 : ∫⁻ (z : Point3), g x z =
        Set.indicator K (fun _ => (1 : ENNReal)) x *
        ∫⁻ (z : Point3), Set.indicator L (fun _ => (1 : ENNReal)) (x - z) := by
      dsimp only [g]
      rw [lintegral_const_mul (Set.indicator K (fun _ => (1 : ENNReal)) x) (by fun_prop)]
    rw [h5]
    have h_mp : MeasurePreserving (fun z : Point3 => x - z) volume volume :=
      MeasureTheory.Measure.measurePreserving_sub_left volume x
    have h71 : ∫⁻ (z : Point3), Set.indicator L (fun _ => (1 : ENNReal)) (x - z) =
        ∫⁻ (y : Point3), Set.indicator L (fun _ => (1 : ENNReal)) y := by
      have h_eq : (fun z : Point3 => Set.indicator L (fun _ => (1 : ENNReal)) (x - z)) =
          (Set.indicator L (fun _ => (1 : ENNReal))) ∘ (fun z : Point3 => x - z) := by
        funext z; rfl
      rw [h_eq]
      exact h_mp.lintegral_comp (measurable_const.indicator hL_meas)
    rw [h71]
    have h8 : ∫⁻ (y : Point3), Set.indicator L (fun _ => (1 : ENNReal)) y = volume L := by
      rw [lintegral_indicator hL_meas]
      simp
    rw [h8] <;> ring
  have h_sum : ∫⁻ (x : Point3), ∫⁻ (z : Point3), g x z =
      ∫⁻ (x : Point3), Set.indicator K (fun _ => (1 : ENNReal)) x * volume L := by
    congr with x; exact h_inner x
  rw [h_sum]
  have h7 : ∫⁻ (x : Point3), Set.indicator K (fun _ => (1 : ENNReal)) x * volume L =
      volume L * ∫⁻ (x : Point3), Set.indicator K (fun _ => (1 : ENNReal)) x := by
    have h9 : ∫⁻ (x : Point3), Set.indicator K (fun _ => (1 : ENNReal)) x * volume L =
        ∫⁻ (x : Point3), volume L * Set.indicator K (fun _ => (1 : ENNReal)) x := by
      congr with x; ring
    rw [h9]
    rw [lintegral_const_mul (volume L) (measurable_const.indicator hK_meas)] <;> ring
  rw [h7]
  have h8 : ∫⁻ (x : Point3), Set.indicator K (fun _ => (1 : ENNReal)) x = volume K := by
    rw [lintegral_indicator hK_meas]
    simp
  rw [h8] <;> ring

/-- Lintegral of indicator of a null-measurable set equals its volume. -/
lemma lintegral_indicator_nullMeasurable {s : Set Point3}
    (hs : NullMeasurableSet s volume) :
    ∫⁻ (x : Point3), Set.indicator s (fun _ => (1 : ENNReal)) x = volume s := by
  let t := MeasureTheory.toMeasurable volume s
  have ht_meas : MeasurableSet t := MeasureTheory.measurableSet_toMeasurable volume s
  have h_ae : s =ᵐ[volume] t := hs.toMeasurable_ae_eq.symm
  have h_ind_ae : Set.indicator s (fun _ => (1 : ENNReal)) =ᵐ[volume]
      Set.indicator t (fun _ => (1 : ENNReal)) := by
    filter_upwards [h_ae] with x hx
    have h6 : x ∈ s ↔ x ∈ t := by
      have h7 : (x ∈ s) = (x ∈ t) := hx
      exact Iff.of_eq h7
    have h_eq : Set.indicator s (fun _ => (1 : ENNReal)) x = Set.indicator t (fun _ => (1 : ENNReal)) x := by
      by_cases h7 : x ∈ s
      · have h8 : x ∈ t := h6.mp h7
        simp [Set.indicator_apply, h7, h8]
      · have h8 : x ∉ t := by tauto
        simp [Set.indicator_apply, h7, h8]
    exact h_eq
  have hvt : volume t = volume s := MeasureTheory.measure_toMeasurable s
  have h : ∫⁻ (x : Point3), Set.indicator t (fun _ => (1 : ENNReal)) x = volume t := by
    rw [lintegral_indicator ht_meas]
    <;> simp
  rw [lintegral_congr_ae h_ind_ae, h]
  exact hvt

/-- Fubini identity for null-measurable sets. -/
lemma fubini_intersection_volume_general {K L : Set Point3}
    (hK : NullMeasurableSet K volume) (hL : NullMeasurableSet L volume) :
    ∫⁻ (z : Point3), volume (K ∩ translateSet z L) = volume K * volume L := by
  let K' := MeasureTheory.toMeasurable volume K
  let L' := MeasureTheory.toMeasurable volume L
  have hK'_meas : MeasurableSet K' := MeasureTheory.measurableSet_toMeasurable volume K
  have hL'_meas : MeasurableSet L' := MeasureTheory.measurableSet_toMeasurable volume L
  have hK_ae : K =ᵐ[volume] K' := hK.toMeasurable_ae_eq.symm
  have hL_ae : L =ᵐ[volume] L' := hL.toMeasurable_ae_eq.symm
  have hK_vol : volume K' = volume K := MeasureTheory.measure_toMeasurable K
  have hL_vol : volume L' = volume L := MeasureTheory.measure_toMeasurable L
  have h_main : ∀ (z : Point3), volume (K ∩ translateSet z L) =
      volume (K' ∩ translateSet z L') := by
    intro z
    have h_mp : MeasurePreserving (fun x : Point3 => x - z) volume volume :=
      MeasureTheory.measurePreserving_sub_right volume z
    have h_preimage : ∀ (S : Set Point3), translateSet z S = (fun x : Point3 => x - z) ⁻¹' S := by
      intro S
      ext x
      simp [translateSet, sub_eq_iff_eq_add]
      <;> abel
    have hL_trans : translateSet z L =ᵐ[volume] translateSet z L' := by
      rw [h_preimage L, h_preimage L']
      exact h_mp.quasiMeasurePreserving.preimage_ae_eq hL_ae
    have h_inter : Set.inter K (translateSet z L) =ᵐ[volume] Set.inter K' (translateSet z L') := by
      filter_upwards [hK_ae, hL_trans] with x hx1 hx2
      have h1 : K x ↔ K' x := Iff.of_eq hx1
      have h2 : translateSet z L x ↔ translateSet z L' x := Iff.of_eq hx2
      exact propext (Iff.and h1 h2)
    exact MeasureTheory.measure_congr h_inter
  have h_fubini := fubini_intersection_volume hK'_meas hL'_meas
  have h7 : ∫⁻ (z : Point3), volume (K ∩ translateSet z L) =
      ∫⁻ (z : Point3), volume (K' ∩ translateSet z L') := by
    congr with z; exact h_main z
  rw [h7, h_fubini, hK_vol, hL_vol]

/-- Rogers-Shephard inequality for convex sets in `Point3`.

`volume(minkowskiDiff K L) * volume(K ∩ L) ≤ 64 * volume K * volume L`.

No measurability or finiteness assumptions needed; convex sets are null-measurable. -/
theorem rogers_shephard_general {K L : Set Point3}
    (hK_conv : Convex ℝ K) (hL_conv : Convex ℝ L) :
    volume (minkowskiDiff K L) * volume (K ∩ L) ≤ 64 * volume K * volume L := by
  by_cases h_inter_zero : volume (K ∩ L) = 0
  · rw [h_inter_zero]; simp
  · have h_inter_nonempty : (K ∩ L).Nonempty := by
      by_contra h
      have h' : K ∩ L = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      rw [h'] at h_inter_zero; simp at h_inter_zero
    by_cases hK_top : volume K = ⊤
    · by_cases hL_zero : volume L = 0
      · have h_int_zero : volume (K ∩ L) = 0 := by
          have h_sub : K ∩ L ⊆ L := Set.inter_subset_right
          have h : volume (K ∩ L) ≤ volume L := measure_mono h_sub
          rw [hL_zero] at h
          simpa using h
        rw [h_int_zero]; simp
      · have hL_pos : 0 < volume L := Ne.bot_lt hL_zero
        rw [hK_top]
        have h : (64 : ENNReal) * (⊤ : ENNReal) * volume L = ⊤ := by
          have h2 : (64 : ENNReal) * (⊤ : ENNReal) = ⊤ := ENNReal.mul_top (by norm_num)
          rw [h2]
          exact ENNReal.top_mul hL_pos.ne'
        rw [h] <;> exact le_top
    by_cases hL_top : volume L = ⊤
    · by_cases hK_zero : volume K = 0
      · have h_int_zero : volume (K ∩ L) = 0 := by
          have h_sub : K ∩ L ⊆ K := Set.inter_subset_left
          have h : volume (K ∩ L) ≤ volume K := measure_mono h_sub
          rw [hK_zero] at h
          simpa using h
        rw [h_int_zero]; simp
      · have hK_pos : 0 < volume K := Ne.bot_lt hK_zero
        rw [hL_top]
        have h : (64 : ENNReal) * volume K * (⊤ : ENNReal) = ⊤ := by
          have h2 : (64 : ENNReal) * volume K ≠ 0 := mul_ne_zero (by norm_num) hK_pos.ne'
          exact ENNReal.mul_top h2
        rw [h] <;> exact le_top
    have hK_null : NullMeasurableSet K volume := hK_conv.nullMeasurableSet volume
    have hL_null : NullMeasurableSet L volume := hL_conv.nullMeasurableSet volume
    let D := minkowskiDiff K L
    have h0_in_diff : (0 : Point3) ∈ D := by
      rcases h_inter_nonempty with ⟨p, hp⟩
      exact Set.mem_image2.mpr ⟨p, hp.1, p, hp.2, by simp⟩
    have h_diff_conv : Convex ℝ D := convex_minkowskiDiff hK_conv hL_conv
    have hD_null : NullMeasurableSet D volume := h_diff_conv.nullMeasurableSet volume
    set t : ℝ := 1 / 2 with ht_def
    have ht_pos : 0 < t := by norm_num
    have ht_nonneg : 0 ≤ t := by norm_num
    have ht_le : t ≤ 1 := by norm_num
    have h1t_nonneg : 0 ≤ 1 - t := by norm_num
    have h_sum : t + (1 - t) = 1 := by norm_num
    have h_t_diff_sub : t • D ⊆ D := by
      intro w hw
      rcases hw with ⟨z, hz, rfl⟩
      have h : t • z + (1 - t) • (0 : Point3) ∈ D :=
        h_diff_conv hz h0_in_diff ht_nonneg h1t_nonneg h_sum
      simpa using h
    let f : Point3 → ENNReal := fun z => volume (K ∩ translateSet z L)
    set c : ENNReal := ENNReal.ofReal ((1 - t)^3) * volume (K ∩ L) with hc_def
    have h_pointwise : ∀ w ∈ t • D, f w ≥ c := by
      intro w hw
      rcases hw with ⟨z, hz, rfl⟩
      exact convexity_intersection_inclusion hK_conv hL_conv hz ht_nonneg ht_le h_inter_nonempty
    have h_tD_conv : Convex ℝ (t • D) := by
      intro x hx y hy a b ha hb hab
      rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      have h : a • x' + b • y' ∈ D := h_diff_conv hx' hy' ha hb hab
      have h2 : a • (t • x') + b • (t • y') = t • (a • x' + b • y') := by
        rw [smul_comm a t x', smul_comm b t y', ← smul_add]
        <;> rfl
      rw [h2]
      exact ⟨a • x' + b • y', h, rfl⟩
    have h_tD_null : NullMeasurableSet (t • D) volume :=
      h_tD_conv.nullMeasurableSet volume
    have h_indicator : ∀ (w : Point3), f w ≥ c * Set.indicator (t • D) (fun _ => (1 : ENNReal)) w := by
      intro w
      by_cases hw : w ∈ t • D
      · have h9 : Set.indicator (t • D) (fun _ => (1 : ENNReal)) w = 1 := by
          simp [Set.indicator_apply, hw]
        rw [h9]
        <;> simpa using h_pointwise w hw
      · have h9 : Set.indicator (t • D) (fun _ => (1 : ENNReal)) w = 0 := by
          simp [Set.indicator_apply, hw]
        rw [h9] <;> simp
    have h_lower : ∫⁻ (w : Point3), f w ≥ c * volume (t • D) := by
      have h_ind_ameas : AEMeasurable (Set.indicator (t • D) (fun _ => (1 : ENNReal))) volume :=
        (aemeasurable_indicator_const_iff 1).mpr h_tD_null
      have h : ∫⁻ (w : Point3), f w ≥
          ∫⁻ (w : Point3), c * Set.indicator (t • D) (fun _ => (1 : ENNReal)) w :=
        lintegral_mono (fun w => h_indicator w)
      have h3 : ∫⁻ (w : Point3), c * Set.indicator (t • D) (fun _ => (1 : ENNReal)) w =
          c * ∫⁻ (w : Point3), Set.indicator (t • D) (fun _ => (1 : ENNReal)) w :=
        lintegral_const_mul'' c h_ind_ameas
      rw [h3] at h
      rw [lintegral_indicator_nullMeasurable h_tD_null] at h
      exact h
    have h_dilation : volume (t • D) = ENNReal.ofReal (t^3) * volume D := by
      have h3 : |t| = t := by rw [abs_of_pos ht_pos]
      have h := volume_dilateSet t (by norm_num) D
      rw [h, h3]
    have h_fubini : ∫⁻ (z : Point3), f z = volume K * volume L :=
      fubini_intersection_volume_general hK_null hL_null
    have h14 : volume K * volume L ≥ c * volume (t • D) := by
      calc
        volume K * volume L = ∫⁻ (z : Point3), f z := h_fubini.symm
        _ ≥ c * volume (t • D) := h_lower
    rw [hc_def, h_dilation] at h14
    have h15 : volume K * volume L ≥
        (ENNReal.ofReal ((1 - t)^3) * volume (K ∩ L)) * (ENNReal.ofReal (t^3) * volume D) := h14
    have h16 : (ENNReal.ofReal ((1 - t)^3) * volume (K ∩ L)) * (ENNReal.ofReal (t^3) * volume D) =
        ENNReal.ofReal (((1 - t)^3 * t^3)) * (volume (K ∩ L) * volume D) := by
      have h17 : ENNReal.ofReal ((1 - t)^3) * ENNReal.ofReal (t^3) =
          ENNReal.ofReal (((1 - t)^3 * t^3)) := by
        rw [← ENNReal.ofReal_mul] <;> norm_num
      have h17' : (ENNReal.ofReal ((1 - t)^3) * volume (K ∩ L)) * (ENNReal.ofReal (t^3) * volume D) =
          (ENNReal.ofReal ((1 - t)^3) * ENNReal.ofReal (t^3)) * (volume (K ∩ L) * volume D) := by
        rw [mul_mul_mul_comm]
      rw [h17', h17]
    rw [h16] at h15
    have h18 : (1 - t)^3 * t^3 = 1 / 64 := by
      rw [ht_def] <;> norm_num
    rw [h18] at h15
    have h19' : ENNReal.ofReal (1 / 64 : ℝ) = (1 / 64 : ENNReal) := by
      have h20 : (1 / 64 : ℝ) = (64 : ℝ)⁻¹ := by norm_num
      rw [h20]
      have h21 : ENNReal.ofReal ((64 : ℝ)⁻¹) = (ENNReal.ofReal (64 : ℝ))⁻¹ :=
        ENNReal.ofReal_inv_of_pos (by norm_num)
      rw [h21]
      have h22 : ENNReal.ofReal (64 : ℝ) = (64 : ENNReal) := by
        simp
      rw [h22]
      have h23 : (1 / 64 : ENNReal) = (64 : ENNReal)⁻¹ := by
        simp [one_div]
      rw [h23]
    rw [h19'] at h15
    have h19 : volume K * volume L ≥ (1 / 64 : ENNReal) * (volume (K ∩ L) * volume D) := h15
    have h20 : (64 : ENNReal) * (volume K * volume L) ≥ volume (K ∩ L) * volume D := by
      have h21 : (64 : ENNReal) * (volume K * volume L) ≥
          (64 : ENNReal) * ((1 / 64 : ENNReal) * (volume (K ∩ L) * volume D)) := by gcongr
      have h22 : (64 : ENNReal) * ((1 / 64 : ENNReal) * (volume (K ∩ L) * volume D)) =
          volume (K ∩ L) * volume D := by
        have h23 : (64 : ENNReal) * (1 / 64 : ENNReal) = 1 := by
          have h24 : (1 / 64 : ENNReal) = (64 : ENNReal)⁻¹ := by simp [one_div]
          rw [h24]
          exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        rw [← mul_assoc, h23, one_mul]
      rw [h22] at h21
      exact h21
    have h24 : (64 : ENNReal) * (volume K * volume L) = 64 * volume K * volume L := by ring
    rw [h24] at h20
    have h25 : volume (K ∩ L) * volume D ≤ 64 * volume K * volume L := h20
    have h26 : volume D * volume (K ∩ L) = volume (K ∩ L) * volume D := by ring
    rw [h26]
    exact h25

/-- Rogers-Shephard inequality with the target signature. -/
lemma rogers_shephard_3d (K L : Set Point3) (hK : Convex ℝ K) (hL : Convex ℝ L)
    (h0 : (0 : Point3) ∈ K) (h0' : (0 : Point3) ∈ L) :
    volume (Set.image2 (·-·) K L) * volume (K ∩ L) ≤ 64 * volume K * volume L :=
  rogers_shephard_general hK hL

/-- Symmetric Rogers-Shephard overlap bound:
`volume(K-L) ≤ 64 * volume K * volume L / volume(K∩L)`.

This is the direct consequence of the two-body RS inequality, valid when
`K` has positive finite volume and `K ∩ L` has positive volume. -/
lemma rogers_shephard_overlap {K L : Set Point3}
    (hK : Convex ℝ K) (hL : Convex ℝ L)
    (hK_pos : 0 < volume K) (hK_finite : volume K ≠ ⊤)
    (h_inter_pos : 0 < volume (K ∩ L)) :
    volume (minkowskiDiff K L) ≤ 64 * volume K * volume L / volume (K ∩ L) := by
  have h_main : volume (minkowskiDiff K L) * volume (K ∩ L) ≤ 64 * volume K * volume L :=
    rogers_shephard_general hK hL
  have h_inter_ne_zero : volume (K ∩ L) ≠ 0 := ne_of_gt h_inter_pos
  have h_inter_finite : volume (K ∩ L) ≠ ⊤ := by
    have h : volume (K ∩ L) ≤ volume K := measure_mono (Set.inter_subset_left)
    exact ne_top_of_le_ne_top hK_finite h
  have h : volume (minkowskiDiff K L) * volume (K ∩ L) * (volume (K ∩ L))⁻¹ ≤
      (64 * volume K * volume L) * (volume (K ∩ L))⁻¹ := by gcongr
  have h2 : volume (K ∩ L) * (volume (K ∩ L))⁻¹ = 1 :=
    ENNReal.mul_inv_cancel h_inter_ne_zero h_inter_finite
  have h3 : volume (minkowskiDiff K L) * volume (K ∩ L) * (volume (K ∩ L))⁻¹ =
      volume (minkowskiDiff K L) := by
    rw [mul_assoc, h2, mul_one]
  rw [h3] at h
  simpa [div_eq_mul_inv] using h

/-- Single-body Rogers-Shephard: `volume(S-S) ≤ 64 * volume S` for positive finite volume. -/
lemma rogers_shephard_single_pos {S : Set Point3} (hS : Convex ℝ S)
    (hS_pos : 0 < volume S) (hS_finite : volume S ≠ ⊤) :
    volume (minkowskiDiff S S) ≤ 64 * volume S := by
  have h_main := rogers_shephard_general hS hS
  have h_inter : S ∩ S = S := by simp
  rw [h_inter] at h_main
  have hS_ne_zero : volume S ≠ 0 := ne_of_gt hS_pos
  have h : volume (minkowskiDiff S S) * volume S ≤ 64 * volume S * volume S := h_main
  have h' : volume (minkowskiDiff S S) ≤ 64 * volume S := by
    have h_inv : (volume S)⁻¹ * (volume (minkowskiDiff S S) * volume S) ≤
        (volume S)⁻¹ * (64 * volume S * volume S) := by gcongr
    have h_cancel1 : (volume S)⁻¹ * (volume (minkowskiDiff S S) * volume S) =
        volume (minkowskiDiff S S) := by
      have h_comm : volume (minkowskiDiff S S) * volume S = volume S * volume (minkowskiDiff S S) := by ring
      rw [h_comm]
      rw [ENNReal.inv_mul_cancel_left hS_ne_zero hS_finite]
    have h_cancel2 : (volume S)⁻¹ * (64 * volume S * volume S) = 64 * volume S := by
      have h9 : (volume S)⁻¹ * (64 * volume S * volume S) =
          64 * (((volume S)⁻¹ * volume S) * volume S) := by ring
      rw [h9]
      have h10 : (volume S)⁻¹ * volume S = 1 := by
        have h12 := ENNReal.inv_mul_cancel_left hS_ne_zero hS_finite (b := (1 : ENNReal))
        simpa using h12
      rw [h10] <;> ring
    rw [h_cancel1, h_cancel2] at h_inv
    exact h_inv
  exact h'

/-- Volume is preserved by translation. -/
lemma volume_translation (p : Point3) (S : Set Point3) :
    volume ((fun x : Point3 => -p + x) '' S) = volume S := by
  have h_edist : ∀ (x y : Point3), edist (-p + x) (-p + y) = edist x y := by
    intro x y
    have h1 : dist (-p + x) (-p + y) = dist x y := by
      have h2 : (-p + x) - (-p + y) = x - y := by abel
      simp [dist_eq_norm, h2]
    simpa [edist_dist] using congr_arg ENNReal.ofReal h1
  have h_iso : Isometry (fun x : Point3 => -p + x) := by
    intro x y
    exact h_edist x y
  have h := Isometry.euclideanHausdorffMeasure_image (d := 3) h_iso S
  have h2 : (μHE[3] : Measure Point3) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume 3
  rw [h2] at h
  exact h

/-- For convex `S` containing `0`, `conv(S ∪ -S) ⊆ S - S`. -/
lemma convex_hull_sym_diff_subset {S : Set Point3} (hS : Convex ℝ S) (h0 : (0 : Point3) ∈ S) :
    convexHull ℝ (S ∪ ((fun x : Point3 => -x) '' S)) ⊆ minkowskiDiff S S := by
  have h1 : Convex ℝ (minkowskiDiff S S) := convex_minkowskiDiff hS hS
  have h2 : S ∪ ((fun x : Point3 => -x) '' S) ⊆ minkowskiDiff S S := by
    intro x hx
    cases hx with
    | inl hx =>
      exact Set.mem_image2.mpr ⟨x, hx, 0, h0, by simp⟩
    | inr hx =>
      rcases hx with ⟨y, hy, rfl⟩
      exact Set.mem_image2.mpr ⟨0, h0, y, hy, by simp⟩
  exact convexHull_min h2 h1

/-- Convex hull intersection bound:
`volume(convexHull ℝ (K ∪ L)) * volume(K ∩ L) ≤ 4096 * volume K * volume L`. -/
lemma convex_hull_intersection_bound (K L : Set Point3) (hK : Convex ℝ K) (hL : Convex ℝ L)
    (h_nonempty : (K ∩ L).Nonempty) :
    volume (convexHull ℝ (K ∪ L)) * volume (K ∩ L) ≤ 4096 * volume K * volume L := by
  rcases h_nonempty with ⟨p, hp⟩
  let K' : Set Point3 := (fun x : Point3 => -p + x) '' K
  let L' : Set Point3 := (fun x : Point3 => -p + x) '' L
  have hK'_conv : Convex ℝ K' := by
    have h : Convex ℝ ((fun x : Point3 => -p + (1 : ℝ) • x) '' K) := hK.affinity (-p) (1 : ℝ)
    have h_eq : (fun x : Point3 => -p + (1 : ℝ) • x) '' K = K' := by
      ext z
      simp only [K', Set.mem_image]
      <;> constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, by simp [one_smul]⟩
    rw [h_eq] at h
    exact h
  have hL'_conv : Convex ℝ L' := by
    have h : Convex ℝ ((fun x : Point3 => -p + (1 : ℝ) • x) '' L) := hL.affinity (-p) (1 : ℝ)
    have h_eq : (fun x : Point3 => -p + (1 : ℝ) • x) '' L = L' := by
      ext z
      simp only [L', Set.mem_image]
      <;> constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, by simp [one_smul]⟩
    rw [h_eq] at h
    exact h
  have h0K' : (0 : Point3) ∈ K' := by
    exact ⟨p, hp.1, neg_add_cancel p⟩
  have h0L' : (0 : Point3) ∈ L' := by
    exact ⟨p, hp.2, neg_add_cancel p⟩
  have h_volK : volume K' = volume K := volume_translation p K
  have h_volL : volume L' = volume L := volume_translation p L
  have h_vol_inter : volume (K' ∩ L') = volume (K ∩ L) := by
    have h_eq : K' ∩ L' = (fun x : Point3 => -p + x) '' (K ∩ L) := by
      ext x
      simp only [K', L', Set.mem_inter_iff, Set.mem_image]
      constructor
      · rintro ⟨⟨y1, hy1, rfl⟩, ⟨y2, hy2, h_eq2⟩⟩
        have y_eq : y1 = y2 := by
          have h : -p + y1 = -p + y2 := h_eq2.symm
          simpa using h
        have hyK : y2 ∈ K := by
          rw [← y_eq]; exact hy1
        exact ⟨y2, ⟨hyK, hy2⟩, h_eq2⟩
      · rintro ⟨y, ⟨hyK, hyL⟩, rfl⟩
        exact ⟨⟨y, hyK, rfl⟩, ⟨y, hyL, rfl⟩⟩
    rw [h_eq]
    exact volume_translation p (K ∩ L)
  have h_hull_image : (fun x : Point3 => -p + x) '' (convexHull ℝ (K ∪ L)) =
      convexHull ℝ (K' ∪ L') := by
    have h1 : (fun x : Point3 => -p + x) '' (K ∪ L) = K' ∪ L' := by
      ext x
      simp only [K', L', Set.mem_image, Set.mem_union]
      constructor
      · rintro ⟨y, hy | hy, rfl⟩
        · exact Or.inl ⟨y, hy, rfl⟩
        · exact Or.inr ⟨y, hy, rfl⟩
      · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
        · exact ⟨y, Or.inl hy, rfl⟩
        · exact ⟨y, Or.inr hy, rfl⟩
    have h2 : convexHull ℝ ((-p : Point3) +ᵥ (K ∪ L)) =
        (-p : Point3) +ᵥ convexHull ℝ (K ∪ L) :=
      convexHull_vadd (𝕜 := ℝ) (-p : Point3) (K ∪ L)
    have h3 : (-p : Point3) +ᵥ (K ∪ L) = (fun x : Point3 => -p + x) '' (K ∪ L) := by rfl
    have h4 : (-p : Point3) +ᵥ convexHull ℝ (K ∪ L) = (fun x : Point3 => -p + x) '' (convexHull ℝ (K ∪ L)) := by rfl
    rw [h3, h4] at h2
    simpa [h1] using h2.symm
  have h_vol_hull : volume (convexHull ℝ (K' ∪ L')) = volume (convexHull ℝ (K ∪ L)) := by
    rw [← h_hull_image]
    exact volume_translation p (convexHull ℝ (K ∪ L))
  let D' := minkowskiDiff K' L'
  have hD'_conv : Convex ℝ D' := convex_minkowskiDiff hK'_conv hL'_conv
  let negD' : Set Point3 := (fun x : Point3 => -x) '' D'
  have h1 : convexHull ℝ (K' ∪ L') ⊆ minkowskiDiff D' D' := by
    have h2 : K' ∪ L' ⊆ D' ∪ negD' := by
      intro x hx
      cases hx with
      | inl hx =>
        exact Or.inl (Set.mem_image2.mpr ⟨x, hx, 0, h0L', sub_zero x⟩)
      | inr hx =>
        have h_neg_x_in_D' : -x ∈ D' := Set.mem_image2.mpr ⟨0, h0K', x, hx, zero_sub x⟩
        have h_x_in_negD' : x ∈ negD' := ⟨-x, h_neg_x_in_D', by simp⟩
        exact Or.inr h_x_in_negD'
    have h3 : convexHull ℝ (K' ∪ L') ⊆ convexHull ℝ (D' ∪ negD') :=
      convexHull_mono h2
    have h4 : convexHull ℝ (D' ∪ negD') ⊆ minkowskiDiff D' D' :=
      convex_hull_sym_diff_subset hD'_conv (by
        exact Set.mem_image2.mpr ⟨0, h0K', 0, h0L', sub_zero (0 : Point3)⟩)
    exact subset_trans h3 h4
  by_cases h_inter_zero : volume (K ∩ L) = 0
  · rw [h_inter_zero]; simp
  · have h_inter_pos : 0 < volume (K ∩ L) := Ne.bot_lt h_inter_zero
    have hD'_pos : 0 < volume D' := by
      have h5 : (0 : Point3) ∈ D' := Set.mem_image2.mpr ⟨0, h0K', 0, h0L', by simp⟩
      have h6 : K' ∩ L' ⊆ D' := by
        intro x hx
        exact Set.mem_image2.mpr ⟨x, hx.1, 0, h0L', by simp⟩
      have h7 : 0 < volume (K' ∩ L') := by
        rw [h_vol_inter]; exact h_inter_pos
      exact lt_of_lt_of_le h7 (volume.mono h6)
    by_cases hD'_top : volume D' = ⊤
    · -- If volume D' = ⊤, then volume K' = ⊤ or volume L' = ⊤ (since D' ⊆ K' + L'?)
      -- Actually, we don't know that. But if volume D' = ⊤, the RS inequality gives
      -- ⊤ * volume(K'∩L') ≤ 64 * volume K' * volume L', so RHS must be ⊤.
      -- Thus volume K' = ⊤ or volume L' = ⊤, so 4096 * volume K * volume L = ⊤.
      have h_rs := rogers_shephard_general hK'_conv hL'_conv
      rw [hD'_top] at h_rs
      have h9 : volume (K' ∩ L') ≠ 0 := by
        rw [h_vol_inter]; exact ne_of_gt h_inter_pos
      have h10 : (64 : ENNReal) * volume K' * volume L' = ⊤ := by
        simpa [h9, ENNReal.mul_eq_top] using h_rs
      have h11 : 64 * volume K * volume L = ⊤ := by
        simpa [h_volK, h_volL] using h10
      have h12 : (4096 : ENNReal) * volume K * volume L = ⊤ := by
        have h13 : (4096 : ENNReal) * volume K * volume L =
            (64 : ENNReal) * (64 * volume K * volume L) := by ring
        rw [h13, h11]
        <;> norm_num
      rw [h12]
      exact le_top
    · have h_single : volume (minkowskiDiff D' D') ≤ 64 * volume D' :=
        rogers_shephard_single_pos hD'_conv hD'_pos hD'_top
      have h_rs : volume D' * volume (K' ∩ L') ≤ 64 * volume K' * volume L' :=
        rogers_shephard_general hK'_conv hL'_conv
      have h_hull_vol : volume (convexHull ℝ (K' ∪ L')) ≤ volume (minkowskiDiff D' D') :=
        volume.mono h1
      calc
        volume (convexHull ℝ (K ∪ L)) * volume (K ∩ L)
          = volume (convexHull ℝ (K' ∪ L')) * volume (K' ∩ L') := by
            rw [h_vol_hull, h_vol_inter]
        _ ≤ volume (minkowskiDiff D' D') * volume (K' ∩ L') := by
          gcongr
        _ ≤ (64 * volume D') * volume (K' ∩ L') := by
          gcongr
        _ = 64 * (volume D' * volume (K' ∩ L')) := by ring
        _ ≤ 64 * (64 * volume K' * volume L') := by
          gcongr
        _ = 4096 * volume K * volume L := by
          rw [h_volK, h_volL] <;> ring

end Kakeya.Streamlined
