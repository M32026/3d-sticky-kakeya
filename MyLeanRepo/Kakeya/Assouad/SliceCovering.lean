import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.CoveringInfrastructure
import MyLeanRepo.Kakeya.Assouad.LargeSlope.GlobalADVolumeBound
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescalingGeometry
import MyLeanRepo.Kakeya.Assouad.WZLemma30ADUpper
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.ADThickening
import Mathlib.Tactic

/-!
# Slice-based covering lemma for Ahlfors-David regular sets

Provides `volume_near_AD_slices_local`: if each horizontal slice of a set `U`
is within `K*rho` of nearby slices of a set `B` whose slices are AD-regular,
and `B` has bounded-slope curves, then `volume U ≤ 32*(K+L+1)*C*rho^sigma`.

## Main results

- `IsADSet1.volume_cthickening_le`: 1D thickening volume bound for AD sets
- `volume_near_AD_slices_local`: the full 2D covering lemma

## Proof route

1. For each height `t`, `sliceAt U t ⊆ cthickening R (sliceAt B t)` where `R = (K+L+1)*rho`,
   using the curve property to shift nearby B-slices to height `t`.
2. If `R ≤ 1`, apply `IsADSet1.volume_cthickening_le` to bound each slice volume.
3. If `R > 1`, use the boundedness of AD slices to get a crude bound.
4. Apply Fubini (via the volume-preserving coordinate map Point2 → ℝ × ℝ) to integrate
   the slice bounds over `t ∈ Icc(-1,1)`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace Kakeya.Assouad

/-- Horizontal slice of a 2D set at height `t`. -/
def sliceAt (B : Set Point2) (t : ℝ) : Set ℝ :=
  (fun p : Point2 => p 0) '' {p ∈ B | p 1 = t}

/-- Construct a Point2 from horizontal and vertical coordinates. -/
private def mkPoint2 (x t : ℝ) : Point2 :=
  x • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
  t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

private lemma mkPoint2_coord (x t : ℝ) :
    (mkPoint2 x t) 0 = x ∧ (mkPoint2 x t) 1 = t := by
  have h0 : (mkPoint2 x t) 0 = x := by simp [mkPoint2]
  have h1 : (mkPoint2 x t) 1 = t := by simp [mkPoint2]
  exact ⟨h0, h1⟩

/--
If a set E in ℝ is covered by a finite family of R-balls, then the
R-thickening of E has volume at most the number of balls times 4R.
-/
private lemma volume_cthickening1D_le_finite_cover
    {E : Set ℝ} {R : ℝ} {centers : Finset ℝ}
    (hR : 0 ≤ R) (hcover : E ⊆ ⋃ c ∈ centers, closedBall c R) :
    volume (cthickening R E) ≤ (centers.card : ENNReal) * ENNReal.ofReal (4 * R) := by
  have h1 : cthickening R E ⊆ cthickening R (⋃ c ∈ centers, closedBall c R) :=
    cthickening_subset_of_subset R hcover
  have h2 : cthickening R (⋃ c ∈ centers, closedBall c R) ⊆
        ⋃ c ∈ centers, closedBall c (2 * R) :=
    cthickening_finite_balls_double hR centers
  have h5 : cthickening R E ⊆ ⋃ c ∈ centers, closedBall c (2 * R) := h1.trans h2
  have h6 : volume (cthickening R E) ≤ ∑ c ∈ centers, volume (closedBall c (2 * R)) :=
    (measure_mono h5).trans (measure_biUnion_finset_le centers _)
  have h9 : ∀ (c : ℝ), volume (closedBall c (2 * R)) = ENNReal.ofReal (4 * R) := by
    intro c
    rw [Real.volume_closedBall]; ring_nf
  have h9' : ∀ x ∈ centers, volume (closedBall x (2 * R)) = ENNReal.ofReal (4 * R) :=
    fun x _ => h9 x
  have h10 : ∑ c ∈ centers, volume (closedBall c (2 * R)) =
      (centers.card : ENNReal) * ENNReal.ofReal (4 * R) := by
    rw [Finset.sum_congr rfl h9']
    simp [Finset.sum_const]
  exact h6.trans (le_of_eq h10)

/--
An `IsADSet1 E delta (1-sigma) C` set has thickening volume at most
`16 * C * R^sigma` when `delta ≤ R ≤ 1`.
-/
lemma IsADSet1.volume_cthickening_le
    {E : Set ℝ} {delta sigma : ℝ} {C : ENNReal}
    (hAD : IsADSet1 E delta (1 - sigma) C)
    (hdelta : 0 < delta) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hCtop : C ≠ ⊤)
    {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hdelta_R : delta ≤ R) :
    volume (cthickening R E) ≤ 16 * C * Kakeya.realRpowENN R sigma := by
  rcases hAD with ⟨_, _, _, hC_one, hE_bounded, hAD_cover⟩
  let centers : Finset ℝ := {-3, -1, 1, 3}
  have hinterval_cover :
      Set.Icc (-4 : ℝ) 4 ⊆ ⋃ c ∈ centers, Metric.closedBall c 1 := by
    intro x hx
    by_cases hx₁ : x ≤ -2
    · exact Set.mem_iUnion₂.mpr ⟨-3, by simp [centers], by
        rw [Metric.mem_closedBall, Real.dist_eq]; apply abs_le.mpr <;> constructor <;> linarith [hx.1]⟩
    · by_cases hx₂ : x ≤ 0
      · exact Set.mem_iUnion₂.mpr ⟨-1, by simp [centers], by
          rw [Metric.mem_closedBall, Real.dist_eq]; apply abs_le.mpr <;> constructor <;> linarith⟩
      · by_cases hx₃ : x ≤ 2
        · exact Set.mem_iUnion₂.mpr ⟨1, by simp [centers], by
            rw [Metric.mem_closedBall, Real.dist_eq]; apply abs_le.mpr <;> constructor <;> linarith⟩
        · exact Set.mem_iUnion₂.mpr ⟨3, by simp [centers], by
            rw [Metric.mem_closedBall, Real.dist_eq]; apply abs_le.mpr <;> constructor <;> linarith [hx.2]⟩
  have hE_cover : E ⊆ ⋃ c ∈ centers, E ∩ Metric.closedBall c 1 := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (hinterval_cover (hE_bounded hx)) with ⟨c, hc, hxc⟩
    exact Set.mem_iUnion₂.mpr ⟨c, hc, hx, hxc⟩
  have h_union_distrib : ∀ (s : Finset ℝ),
      cthickening R (⋃ c ∈ s, E ∩ Metric.closedBall c 1) =
        ⋃ c ∈ s, cthickening R (E ∩ Metric.closedBall c 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      have h1 : (⋃ c ∈ (insert a s), E ∩ Metric.closedBall c 1) =
          (E ∩ Metric.closedBall a 1) ∪ (⋃ c ∈ s, E ∩ Metric.closedBall c 1) := by
        ext z; simp [Finset.mem_insert]
      rw [h1, cthickening_union, ih]
      ext z
      simp [Finset.mem_insert]
  have hthick_cover : cthickening R E ⊆ ⋃ c ∈ centers, cthickening R (E ∩ Metric.closedBall c 1) := by
    have h1 : cthickening R E ⊆ cthickening R (⋃ c ∈ centers, E ∩ Metric.closedBall c 1) :=
      cthickening_subset_of_subset R hE_cover
    rw [h_union_distrib centers] at h1
    exact h1
  have hpiece : ∀ c ∈ centers,
      volume (cthickening R (E ∩ Metric.closedBall c 1)) ≤
        4 * C * Kakeya.realRpowENN R sigma := by
    intro c _
    have hcover :
        (↑(Metric.externalCoveringNumber ⟨R, hR.le⟩
          (E ∩ Metric.closedBall c 1)) : ENNReal) ≤
          C * Kakeya.realRpowENN (1 / R) (1 - sigma) :=
      hAD_cover R hR.le hdelta_R hR1 c 1 (by linarith) le_rfl
    have hN_top : C * Kakeya.realRpowENN (1 / R) (1 - sigma) ≠ ⊤ :=
      ENNReal.mul_ne_top hCtop (by simp [Kakeya.realRpowENN])
    have h_fin : Metric.externalCoveringNumber ⟨R, hR.le⟩
        (E ∩ Metric.closedBall c 1) ≠ ⊤ := by
      intro htop
      rw [htop] at hcover
      exact hN_top (top_le_iff.mp hcover)
    obtain ⟨coverSet, hcoverSet_finite, hcoverSet_cover, hcoverSet_card⟩ :=
      exists_set_encard_eq_externalCoveringNumber h_fin
    let coverFinset : Finset ℝ := hcoverSet_finite.toFinset
    have hcover' : (E ∩ Metric.closedBall c 1) ⊆ ⋃ x ∈ coverFinset, closedBall x R := by
      intro y hy
      have hy_cover := hcoverSet_cover.subset_iUnion_closedBall hy
      simp only [Set.mem_iUnion] at hy_cover
      obtain ⟨x, hx_centers, hy_ball⟩ := hy_cover
      have hx_finset : x ∈ coverFinset := by
        have : x ∈ (coverFinset : Set ℝ) := by
          simpa [coverFinset, hcoverSet_finite.coe_toFinset] using hx_centers
        exact this
      have hy_dist : dist y x ≤ R := by exact_mod_cast hy_ball
      exact Set.mem_iUnion₂.mpr ⟨x, hx_finset, by simpa [Metric.mem_closedBall] using hy_dist⟩
    have hcard : (coverFinset.card : ENNReal) ≤ C * Kakeya.realRpowENN (1 / R) (1 - sigma) := by
      have hcard_enat : (↑coverFinset.card : ℕ∞) =
          Metric.externalCoveringNumber ⟨R, hR.le⟩ (E ∩ Metric.closedBall c 1) := by
        calc
          (↑coverFinset.card : ℕ∞)
            = coverSet.encard := by simpa [coverFinset] using hcoverSet_finite.encard_eq_coe_toFinset_card.symm
          _ = Metric.externalCoveringNumber ⟨R, hR.le⟩ (E ∩ Metric.closedBall c 1) := hcoverSet_card
      have h : (coverFinset.card : ENNReal) =
          (↑(Metric.externalCoveringNumber ⟨R, hR.le⟩ (E ∩ Metric.closedBall c 1)) : ENNReal) := by
        exact_mod_cast hcard_enat
      rw [h]
      exact hcover
    have hvol := volume_cthickening1D_le_finite_cover hR.le hcover'
    have hrpow : Kakeya.realRpowENN (1 / R) (1 - sigma) * ENNReal.ofReal (4 * R) =
        4 * Kakeya.realRpowENN R sigma := by
      simp only [Kakeya.realRpowENN]
      have hleft : Real.rpow (1 / R) (1 - sigma) * (4 * R) = 4 * Real.rpow R sigma := by
        have hinv : Real.rpow (1 / R) (1 - sigma) = (Real.rpow R (1 - sigma))⁻¹ := by
          rw [show (1 / R) = R⁻¹ by field_simp [hR.ne']]
          exact Real.inv_rpow hR.le (1 - sigma)
        rw [hinv]
        have hadd := Real.rpow_add hR (-(1 - sigma)) 1
        rw [Real.rpow_one] at hadd
        have hexp : -(1 - sigma) + 1 = sigma := by ring
        rw [hexp] at hadd
        have hneg : (Real.rpow R (1 - sigma))⁻¹ = Real.rpow R (-(1 - sigma)) :=
          (Real.rpow_neg hR.le (1 - sigma)).symm
        calc
          (Real.rpow R (1 - sigma))⁻¹ * (4 * R)
            = 4 * (Real.rpow R (-(1 - sigma)) * R) := by rw [hneg] <;> ring
          _ = 4 * Real.rpow R sigma := congrArg (fun x => 4 * x) hadd.symm
      have hnonneg : 0 ≤ Real.rpow (1 / R) (1 - sigma) := Real.rpow_nonneg (by positivity) _
      rw [← ENNReal.ofReal_mul hnonneg, hleft] <;> simp
    calc
      volume (cthickening R (E ∩ Metric.closedBall c 1))
        ≤ (coverFinset.card : ENNReal) * ENNReal.ofReal (4 * R) := hvol
      _ ≤ (C * Kakeya.realRpowENN (1 / R) (1 - sigma)) * ENNReal.ofReal (4 * R) := by gcongr
      _ = C * (Kakeya.realRpowENN (1 / R) (1 - sigma) * ENNReal.ofReal (4 * R)) := by
        rw [mul_assoc]
      _ = C * (4 * Kakeya.realRpowENN R sigma) := by rw [hrpow]
      _ = 4 * C * Kakeya.realRpowENN R sigma := by
        set X := Kakeya.realRpowENN R sigma with hX
        have h1 : C * (4 * X) = (C * (4 : ENNReal)) * X := by
          exact (mul_assoc C (4 : ENNReal) X).symm
        have h2 : (C * (4 : ENNReal)) * X = ((4 : ENNReal) * C) * X := by
          rw [mul_comm C (4 : ENNReal)]
        have h3 : ((4 : ENNReal) * C) * X = (4 : ENNReal) * C * X := by rfl
        rw [h1, h2, h3]
  calc
    volume (cthickening R E)
      ≤ ∑ c ∈ centers, volume (cthickening R (E ∩ Metric.closedBall c 1)) :=
        (measure_mono hthick_cover).trans (measure_biUnion_finset_le centers _)
    _ ≤ ∑ _c ∈ centers, (4 * C * Kakeya.realRpowENN R sigma) :=
        Finset.sum_le_sum fun c hc => hpiece c hc
    _ = (centers.card : ENNReal) * (4 * C * Kakeya.realRpowENN R sigma) := by simp
    _ = 16 * C * Kakeya.realRpowENN R sigma := by
        have hcard4 : centers.card = 4 := by norm_num [centers]
        rw [hcard4]
        set X := Kakeya.realRpowENN R sigma with hX
        have h : (4 : ENNReal) * (4 * C * X) = 16 * C * X := by
          have h1 : (4 : ENNReal) * (4 * C * X) = (4 : ENNReal) * ((4 : ENNReal) * C) * X := by
            rw [mul_assoc (4 : ENNReal) ((4 : ENNReal) * C) X]
            <;> rfl
          rw [h1]
          have h2 : (4 : ENNReal) * ((4 : ENNReal) * C) = (16 : ENNReal) * C := by
            calc
              (4 : ENNReal) * ((4 : ENNReal) * C)
                = (4 : ENNReal) * (4 : ENNReal) * C := by rw [mul_assoc]
              _ = (16 : ENNReal) * C := by norm_num
          rw [h2] <;> rfl
        exact h

/-- cthickening δ' (cthickening δ S) ⊆ cthickening (δ' + δ) S. -/
private lemma cthickening_cthickening_subset
    {X : Type*} [PseudoMetricSpace X] {δ' δ : ℝ} (hδ' : 0 ≤ δ') (hδ : 0 ≤ δ)
    {S : Set X} :
    cthickening δ' (cthickening δ S) ⊆ cthickening (δ' + δ) S := by
  intro x hx
  have h1 : infEDist x (cthickening δ S) ≤ ENNReal.ofReal δ' := by
    rwa [Metric.mem_cthickening_iff] at hx
  have h2 : infEDist x S ≤ infEDist x (cthickening δ S) + ENNReal.ofReal δ :=
    Metric.infEDist_le_infEDist_cthickening_add (δ := δ) (x := x) (s := S)
  have h3 : infEDist x S ≤ ENNReal.ofReal (δ' + δ) := by
    calc infEDist x S
      ≤ infEDist x (cthickening δ S) + ENNReal.ofReal δ := h2
    _ ≤ ENNReal.ofReal δ' + ENNReal.ofReal δ := by gcongr
    _ = ENNReal.ofReal (δ' + δ) := by rw [ENNReal.ofReal_add hδ' hδ]
  rw [Metric.mem_cthickening_iff]
  exact h3

/-- The coordinate map `p ↦ (p 0, p 1)` from Point2 to ℝ × ℝ preserves volume. -/
private lemma coordMap_volumePreserving :
    MeasurePreserving (fun p : Point2 => (p 0, p 1)) volume volume := by
  let e1 : Point2 → (Fin 2 → ℝ) := WithLp.ofLp
  have hpres1 : MeasurePreserving e1 volume volume :=
    PiLp.volume_preserving_ofLp (ι := Fin 2)
  let e2 : (Fin 2 → ℝ) → ℝ × ℝ := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hpres2 : MeasurePreserving e2 volume volume :=
    MeasureTheory.volume_preserving_piFinTwo (fun _ => ℝ)
  let e : Point2 → ℝ × ℝ := e2 ∘ e1
  have hpres : MeasurePreserving e volume volume := hpres2.comp hpres1
  have h_eq : e = (fun p : Point2 => (p 0, p 1)) := by
    funext p <;> rfl
  rw [h_eq] at hpres
  exact hpres

/--
Covering lemma: if each slice of U is within K*rho of nearby AD slices,
and the AD slices vary along curves of slope at most L (locally), then
volume(U) ≤ 32*(K+L+1)*C*rho^sigma.

The h_curves hypothesis is local: it only needs to hold when |p 1 - t'| ≤ rho.
Requires `U` measurable and vertically supported in `Icc(-1,1)`.
-/
lemma volume_near_AD_slices_local
    {U B : Set Point2} {delta rho sigma : ℝ} {C : ENNReal}
    (hdelta : 0 < delta) (hrho : 0 < rho) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hC : 1 ≤ C) (hCtop : C ≠ ⊤) (hdelta_rho : delta ≤ rho)
    (hB_AD : ∀ t ∈ Set.Icc (-1 : ℝ) 1, IsADSet1 (sliceAt B t) delta (1 - sigma) C)
    (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (h_main : ∀ (t : ℝ), t ∈ Set.Icc (-1 : ℝ) 1 →
      sliceAt U t ⊆ cthickening (K * rho)
        (⋃ (s : ℝ) (_ : s ∈ Set.Icc (t - rho) (t + rho)), sliceAt B s))
    (h_curves : ∀ (p : Point2), p ∈ B → ∀ (t' : ℝ),
      |p 1 - t'| ≤ rho → t' ∈ Set.Icc (-1 : ℝ) 1 →
      ∃ (p' : Point2), p' ∈ B ∧ p' 1 = t' ∧
        |p 0 - p' 0| ≤ L * |p 1 - t'| + delta)
    (hrho_one : rho ≤ 1)
    (hU_meas : MeasurableSet U)
    (hU_vertical : ∀ p ∈ U, (p 1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1) :
    volume U ≤ (32 : ENNReal) * ENNReal.ofReal (K + L + 1) * C * Kakeya.realRpowENN rho sigma := by
  set R : ℝ := (K + L + 1) * rho with hR_def
  have hR_pos : 0 < R := by positivity
  have hKpos : 0 ≤ K * rho := by positivity
  have hLpos : 0 ≤ (L + 1) * rho := by positivity
  have hR_sum : K * rho + (L + 1) * rho = R := by
    simp [hR_def] <;> ring
  have h_slice : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      sliceAt U t ⊆ cthickening R (sliceAt B t) := by
    intro t ht
    let S : Set ℝ := ⋃ (s : ℝ) (_ : s ∈ Set.Icc (t - rho) (t + rho)), sliceAt B s
    have h1 : sliceAt U t ⊆ cthickening (K * rho) S := h_main t ht
    have h2 : S ⊆ cthickening ((L + 1) * rho) (sliceAt B t) := by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨s, hs⟩
      rcases Set.mem_iUnion.mp hs with ⟨hs_in, hxs⟩
      have h31 : t - rho ≤ s := hs_in.1
      have h32 : s ≤ t + rho := hs_in.2
      have hst : |s - t| ≤ rho := by
        rw [abs_le]
        constructor <;> linarith
      have hxs' : ∃ (p : Point2), p ∈ {p ∈ B | p 1 = s} ∧ p 0 = x := by
        simpa [sliceAt, Set.mem_image] using hxs
      rcases hxs' with ⟨p, ⟨hpB, hp1s⟩, hp0x⟩
      have hpt : |p 1 - t| ≤ rho := by
        rw [hp1s] <;> exact hst
      have h4 : ∃ (p' : Point2), p' ∈ B ∧ p' 1 = t ∧ |p 0 - p' 0| ≤ L * |p 1 - t| + delta :=
        h_curves p hpB t hpt ht
      rcases h4 with ⟨p', hp'_in, hp'_t, hdist⟩
      have h5 : |p 0 - p' 0| ≤ (L + 1) * rho := by
        calc |p 0 - p' 0|
          ≤ L * |p 1 - t| + delta := hdist
        _ ≤ L * rho + rho := by
          have h : L * |p 1 - t| + delta ≤ L * rho + rho := by
            calc L * |p 1 - t| + delta ≤ L * rho + delta := by gcongr
              _ ≤ L * rho + rho := by linarith
          exact h
        _ = (L + 1) * rho := by ring
      have h6 : dist x (p' 0) ≤ (L + 1) * rho := by
        have h5' : |x - p' 0| ≤ (L + 1) * rho := by
          rw [← hp0x]
          exact h5
        have hdist_eq : dist x (p' 0) = |x - p' 0| := by
          rw [Real.dist_eq] <;> rfl
        rw [hdist_eq]
        exact h5'
      have h7 : p' 0 ∈ sliceAt B t := by
        exact ⟨p', ⟨hp'_in, hp'_t⟩, rfl⟩
      exact Metric.mem_cthickening_of_dist_le x (p' 0) ((L + 1) * rho) (sliceAt B t) h7 h6
    have h3 : cthickening (K * rho) S ⊆ cthickening R (sliceAt B t) := by
      have h4 : cthickening (K * rho) S ⊆
          cthickening (K * rho) (cthickening ((L + 1) * rho) (sliceAt B t)) :=
        cthickening_subset_of_subset (K * rho) h2
      have h5 : cthickening (K * rho) (cthickening ((L + 1) * rho) (sliceAt B t)) ⊆
          cthickening (K * rho + (L + 1) * rho) (sliceAt B t) :=
        cthickening_cthickening_subset hKpos hLpos
      rw [hR_sum] at h5
      exact h4.trans h5
    exact h1.trans h3
  let e : Point2 → ℝ × ℝ := fun p => (p 0, p 1)
  have he_meas : Measurable e := by fun_prop
  have hpres : MeasurePreserving e volume volume := coordMap_volumePreserving
  have hmap : Measure.map e volume = volume := hpres.2
  let imageU : Set (ℝ × ℝ) := e '' U
  have h_inj : Function.Injective e := by
    intro p q h
    have h1 : p 0 = q 0 := by simpa [e] using congr_arg Prod.fst h
    have h2 : p 1 = q 1 := by simpa [e] using congr_arg Prod.snd h
    ext i; fin_cases i <;> tauto
  have h_injOn : Set.InjOn e U := fun x _ y _ hxy => h_inj hxy
  have hU'_meas : MeasurableSet imageU :=
    MeasurableSet.image_of_measurable_injOn hU_meas he_meas h_injOn
  have h3 : e ⁻¹' imageU = U := by
    ext p
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨q, hq, heq⟩; exact h_inj heq ▸ hq
    · intro hp; exact ⟨p, hp, rfl⟩
  have hvol_eq : volume U = volume imageU := by
    have h : volume imageU = volume U := by
      calc volume imageU
        = (Measure.map e volume) imageU := by rw [hmap]
      _ = volume (e ⁻¹' imageU) := by rw [Measure.map_apply he_meas hU'_meas]
      _ = volume U := by rw [h3]
    exact h.symm
  have h_fubini : volume imageU =
      ∫⁻ (t : ℝ), volume {x : ℝ | (x, t) ∈ imageU} ∂volume := by
    have hvol_eq_prod : (volume : Measure (ℝ × ℝ)) = volume.prod volume :=
      MeasureTheory.Measure.volume_eq_prod ℝ ℝ
    rw [hvol_eq_prod]
    exact MeasureTheory.Measure.prod_apply_symm hU'_meas
  have h_slice_eq : ∀ (t : ℝ), {x : ℝ | (x, t) ∈ imageU} = sliceAt U t := by
    intro t
    ext x
    simp only [Set.mem_image, sliceAt, e]
    constructor
    · rintro ⟨p, hp, hpe⟩
      have hpt : p 1 = t := by simpa [e] using congr_arg Prod.snd hpe
      have hpx : p 0 = x := by simpa [e] using congr_arg Prod.fst hpe
      exact ⟨p, ⟨hp, hpt⟩, hpx⟩
    · rintro ⟨p, ⟨hp, hpt⟩, hpx⟩
      have hpe : e p = (x, t) := by
        simp [e, hpx, hpt] <;> rfl
      exact ⟨p, hp, hpe⟩
  have h_fubini_main : volume U = ∫⁻ (t : ℝ), volume (sliceAt U t) ∂volume := by
    calc volume U
      = volume imageU := hvol_eq
    _ = ∫⁻ (t : ℝ), volume {x : ℝ | (x, t) ∈ imageU} ∂volume := h_fubini
    _ = ∫⁻ (t : ℝ), volume (sliceAt U t) ∂volume := by
      congr with t; rw [h_slice_eq t]
  have h_support : ∀ (t : ℝ), t ∉ Set.Icc (-1 : ℝ) 1 →
      volume (sliceAt U t) = 0 := by
    intro t ht
    by_contra hne
    have h_nonempty : Set.Nonempty (sliceAt U t) := by
      by_contra h
      have h_empty : sliceAt U t = ∅ := by
        simpa [Set.not_nonempty_iff_eq_empty] using h
      rw [h_empty] at hne
      simp at hne
    obtain ⟨x, hx⟩ := h_nonempty
    obtain ⟨p, hp_in, hpx⟩ : ∃ (p : Point2), p ∈ {p ∈ U | p 1 = t} ∧ p 0 = x := by
      simpa [sliceAt, Set.mem_image] using hx
    have hp : p ∈ U := hp_in.1
    have hpt : p 1 = t := hp_in.2
    have hvt : p 1 ∈ Set.Icc (-1 : ℝ) 1 := hU_vertical p hp
    rw [hpt] at hvt
    exact ht hvt
  let g : ℝ → ENNReal := fun t => volume (sliceAt U t)
  have h_integral : ∫⁻ (t : ℝ), g t ∂volume =
      ∫⁻ (t : ℝ) in Set.Icc (-1 : ℝ) 1, g t ∂volume := by
    rw [← lintegral_add_compl g measurableSet_Icc]
    have h6 : ∫⁻ (t : ℝ) in (Set.Icc (-1 : ℝ) 1)ᶜ, g t ∂volume = 0 := by
      apply le_zero_iff.mp
      have h_ae : ∀ᵐ (t : ℝ) ∂(volume.restrict (Set.Icc (-1 : ℝ) 1)ᶜ), g t ≤ (0 : ENNReal) := by
        filter_upwards [self_mem_ae_restrict measurableSet_Icc.compl] with t ht
        have hgt : g t = 0 := h_support t ht
        rw [hgt] <;> simp
      have h_le : ∫⁻ (t : ℝ) in (Set.Icc (-1 : ℝ) 1)ᶜ, g t ∂volume ≤
          ∫⁻ (t : ℝ) in (Set.Icc (-1 : ℝ) 1)ᶜ, (0 : ENNReal) ∂volume :=
        lintegral_mono_ae h_ae
      simpa using h_le
    rw [h6, add_zero]
  rw [h_fubini_main, h_integral]
  by_cases hR1 : R ≤ 1
  · -- Case R ≤ 1: use AD covering bound
    have hdelta_R : delta ≤ R := by
      have h1 : 1 ≤ K + L + 1 := by linarith
      have h2 : rho ≤ (K + L + 1) * rho := by
        have h3 : 0 ≤ (K + L) * rho := by positivity
        linarith
      have h4 : R = (K + L + 1) * rho := by simp [R]
      linarith
    have h_bound : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
        volume (sliceAt U t) ≤ 16 * C * Kakeya.realRpowENN R sigma := by
      intro t ht
      have hAD_t : IsADSet1 (sliceAt B t) delta (1 - sigma) C := hB_AD t ht
      have h4 : sliceAt U t ⊆ cthickening R (sliceAt B t) := h_slice t ht
      have h5 : volume (cthickening R (sliceAt B t)) ≤
            16 * C * Kakeya.realRpowENN R sigma :=
        hAD_t.volume_cthickening_le hdelta hsigma hsigma1 hCtop hR_pos hR1 hdelta_R
      exact (measure_mono h4).trans h5
    let bval : ENNReal := 16 * C * Kakeya.realRpowENN R sigma
    have h_le_all : ∀ (t : ℝ), g t ≤ bval := by
      intro t
      by_cases h : t ∈ Set.Icc (-1 : ℝ) 1
      · exact h_bound t h
      · have hgt : g t = 0 := h_support t h
        rw [hgt] <;> exact bot_le
    have h6 : ∫⁻ (t : ℝ) in Set.Icc (-1 : ℝ) 1, g t ∂volume ≤
        ∫⁻ (t : ℝ) in Set.Icc (-1 : ℝ) 1, bval ∂volume :=
      lintegral_mono h_le_all
    have h7 : ∫⁻ (t : ℝ) in Set.Icc (-1 : ℝ) 1, bval ∂volume =
        bval * volume (Set.Icc (-1 : ℝ) 1) := by
      simp [lintegral_const]
      <;> rfl
    have h8 : volume (Set.Icc (-1 : ℝ) 1) = ENNReal.ofReal 2 := by
      rw [Real.volume_Icc] <;> norm_num
    set X := Kakeya.realRpowENN R sigma with hX
    have h9 : bval * volume (Set.Icc (-1 : ℝ) 1) =
        (32 : ENNReal) * C * Kakeya.realRpowENN R sigma := by
      rw [h8]
      dsimp only [bval]
      have h_mul : (16 : ENNReal) * ENNReal.ofReal 2 = (32 : ENNReal) := by norm_num
      have h1 : ((16 : ENNReal) * C * X) * ENNReal.ofReal 2 =
          (16 : ENNReal) * (C * X) * ENNReal.ofReal 2 := by
        rw [mul_assoc (16 : ENNReal) C X]
      have h2 : (16 : ENNReal) * (C * X) * ENNReal.ofReal 2 =
          (16 : ENNReal) * ENNReal.ofReal 2 * (C * X) := by
        exact mul_right_comm (16 : ENNReal) (C * X) (ENNReal.ofReal 2)
      have h3 : (16 : ENNReal) * ENNReal.ofReal 2 * (C * X) =
          (32 : ENNReal) * (C * X) := by
        rw [h_mul] <;> rfl
      have h4 : (32 : ENNReal) * (C * X) = (32 : ENNReal) * C * X := by
        rw [mul_assoc]
      rw [h1, h2, h3, h4]
    have h10 : Kakeya.realRpowENN R sigma ≤
        ENNReal.ofReal (K + L + 1) * Kakeya.realRpowENN rho sigma := by
      simp only [Kakeya.realRpowENN]
      have h11 : R = (K + L + 1) * rho := by simp [R]
      have h_pos1 : 0 ≤ K + L + 1 := by linarith
      have h12 : Real.rpow ((K + L + 1) * rho) sigma =
          Real.rpow (K + L + 1) sigma * Real.rpow rho sigma :=
        Real.mul_rpow h_pos1 (by linarith)
      have h13 : 1 ≤ K + L + 1 := by linarith
      have h14 : Real.rpow (K + L + 1) sigma ≤ K + L + 1 := by
        have h_sigma_le_one : sigma ≤ (1 : ℝ) := by linarith
        have h15 : Real.rpow (K + L + 1) sigma ≤ Real.rpow (K + L + 1) 1 :=
          Real.rpow_le_rpow_of_exponent_le h13 h_sigma_le_one
        have h16 : Real.rpow (K + L + 1) 1 = K + L + 1 := by simp
        rw [h16] at h15
        exact h15
      have h15 : 0 ≤ Real.rpow rho sigma := Real.rpow_nonneg (by linarith) _
      have h16 : Real.rpow R sigma ≤ (K + L + 1) * Real.rpow rho sigma := by
        rw [h11, h12]
        nlinarith
      have h17 : ENNReal.ofReal (Real.rpow R sigma) ≤
          ENNReal.ofReal ((K + L + 1) * Real.rpow rho sigma) :=
        ENNReal.ofReal_le_ofReal h16
      have h18 : ENNReal.ofReal ((K + L + 1) * Real.rpow rho sigma) =
          ENNReal.ofReal (K + L + 1) * ENNReal.ofReal (Real.rpow rho sigma) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      simpa [Kakeya.realRpowENN] using h17.trans (le_of_eq h18)
    calc
      ∫⁻ (t : ℝ) in Set.Icc (-1 : ℝ) 1, g t ∂volume
        ≤ ∫⁻ (t : ℝ) in Set.Icc (-1 : ℝ) 1, bval ∂volume := h6
      _ = bval * volume (Set.Icc (-1 : ℝ) 1) := h7
      _ = (32 : ENNReal) * C * Kakeya.realRpowENN R sigma := h9
      _ ≤ (32 : ENNReal) * C * (ENNReal.ofReal (K + L + 1) * Kakeya.realRpowENN rho sigma) := by gcongr
      _ = (32 : ENNReal) * ENNReal.ofReal (K + L + 1) * C * Kakeya.realRpowENN rho sigma := by
        simp [mul_assoc, mul_comm, mul_left_comm]
  · -- Case R > 1: use crude bounding box
    have hR_gt1 : 1 < R := by linarith
    have h_bound : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
        volume (sliceAt U t) ≤ ENNReal.ofReal (10 * R) := by
      intro t ht
      have hAD_t : IsADSet1 (sliceAt B t) delta (1 - sigma) C := hB_AD t ht
      rcases hAD_t with ⟨_, _, _, _, hB_bounded, _⟩
      have h4 : sliceAt U t ⊆ cthickening R (sliceAt B t) := h_slice t ht
      have h5 : cthickening R (sliceAt B t) ⊆ Set.Icc (-(4 + R)) (4 + R) := by
        have hB_ball : sliceAt B t ⊆ Metric.closedBall (0 : ℝ) 4 := by
          intro x hx
          have hx4 : x ∈ Set.Icc (-4 : ℝ) 4 := hB_bounded hx
          have h : |x| ≤ 4 := abs_le.mpr ⟨hx4.1, hx4.2⟩
          simpa [Metric.mem_closedBall, Real.dist_eq, dist_zero_right] using h
        have h_thick : cthickening R (sliceAt B t) ⊆ cthickening R (Metric.closedBall (0 : ℝ) 4) :=
          cthickening_subset_of_subset R hB_ball
        have h_main : ∀ ε : ℝ, 0 < ε → cthickening R (Metric.closedBall (0 : ℝ) 4) ⊆
            Metric.closedBall (0 : ℝ) (4 + R + ε) := by
          intro ε hε
          have hpos : 0 < R + ε := by linarith
          have hlt : R < R + ε := by linarith
          have h1 : cthickening R (Metric.closedBall (0 : ℝ) 4) ⊆
              ⋃ x ∈ Metric.closedBall (0 : ℝ) 4, Metric.closedBall x (R + ε) :=
            cthickening_subset_iUnion_closedBall_of_lt (Metric.closedBall (0 : ℝ) 4)
              (hδ₀ := hpos) (hδδ' := hlt)
          have h2 : (⋃ x ∈ Metric.closedBall (0 : ℝ) 4, Metric.closedBall x (R + ε)) ⊆
              Metric.closedBall (0 : ℝ) (4 + R + ε) := by
            intro y hy
            rcases Set.mem_iUnion₂.mp hy with ⟨x, hx, hy2⟩
            have h3 : dist y x ≤ R + ε := by simpa [Metric.mem_closedBall] using hy2
            have h4 : dist x (0 : ℝ) ≤ 4 := by simpa [Metric.mem_closedBall] using hx
            have h5 : dist y (0 : ℝ) ≤ dist y x + dist x (0 : ℝ) := dist_triangle y x (0 : ℝ)
            have h6 : dist y (0 : ℝ) ≤ 4 + R + ε := by
              calc dist y (0 : ℝ) ≤ dist y x + dist x (0 : ℝ) := h5
                _ ≤ (R + ε) + 4 := by gcongr
                _ = 4 + R + ε := by ring
            simpa [Metric.mem_closedBall] using h6
          exact h1.trans h2
        intro y hy
        have h_all : ∀ ε : ℝ, 0 < ε → y ∈ Metric.closedBall (0 : ℝ) (4 + R + ε) := by
          intro ε hε
          exact h_main ε hε (h_thick hy)
        have h13 : dist y (0 : ℝ) ≤ 4 + R := by
          by_contra h
          have h14 : dist y (0 : ℝ) > 4 + R := by linarith
          set ε : ℝ := (dist y (0 : ℝ) - (4 + R)) / 2 with hε_def
          have hε_pos : 0 < ε := by linarith
          have h15 : y ∈ Metric.closedBall (0 : ℝ) (4 + R + ε) := h_all ε hε_pos
          have h16 : dist y (0 : ℝ) ≤ 4 + R + ε := by simpa [Metric.mem_closedBall] using h15
          linarith
        have h17 : |y| ≤ 4 + R := by simpa [Real.dist_eq, dist_zero_right] using h13
        exact ⟨by linarith [abs_le.mp h17], by linarith [abs_le.mp h17]⟩
      have h9 : volume (sliceAt U t) ≤ volume (Set.Icc (-(4 + R)) (4 + R)) :=
        measure_mono (h4.trans h5)
      have h10 : volume (Set.Icc (-(4 + R)) (4 + R)) = ENNReal.ofReal (2 * (4 + R)) := by
        rw [Real.volume_Icc] <;> ring_nf
      have h11 : volume (sliceAt U t) ≤ ENNReal.ofReal (2 * (4 + R)) :=
        le_trans h9 (le_of_eq h10)
      have h12 : ENNReal.ofReal (2 * (4 + R)) ≤ ENNReal.ofReal (10 * R) := by
        apply ENNReal.ofReal_le_ofReal
        linarith
      exact le_trans h11 h12
    let bval2 : ENNReal := ENNReal.ofReal (10 * R)
    have h_le_all2 : ∀ (t : ℝ), g t ≤ bval2 := by
      intro t
      by_cases h : t ∈ Set.Icc (-1 : ℝ) 1
      · exact h_bound t h
      · have hgt : g t = 0 := h_support t h
        rw [hgt] <;> exact bot_le
    have h6 : ∫⁻ (t : ℝ) in Set.Icc (-1 : ℝ) 1, g t ∂volume ≤
        ∫⁻ (t : ℝ) in Set.Icc (-1 : ℝ) 1, bval2 ∂volume :=
      lintegral_mono h_le_all2
    have h7 : ∫⁻ (t : ℝ) in Set.Icc (-1 : ℝ) 1, bval2 ∂volume =
        bval2 * volume (Set.Icc (-1 : ℝ) 1) := by
      simp [lintegral_const] <;> rfl
    have h8 : volume (Set.Icc (-1 : ℝ) 1) = ENNReal.ofReal 2 := by
      rw [Real.volume_Icc] <;> norm_num
    have h_rho_le_rpow : rho ≤ rho ^ sigma := by
      have h_rho_pos : 0 < rho := hrho
      have h_log_nonpos : Real.log rho ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
      have h_mul : sigma * Real.log rho ≥ Real.log rho := by nlinarith
      have h_exp : Real.exp (sigma * Real.log rho) ≥ Real.exp (Real.log rho) :=
        Real.exp_monotone h_mul
      have h_rpow : rho ^ sigma = Real.exp (Real.log rho * sigma) :=
        Real.rpow_def_of_pos h_rho_pos sigma
      have h_log_rho : Real.exp (Real.log rho) = rho := Real.exp_log h_rho_pos
      rw [h_rpow, mul_comm (Real.log rho) sigma]
      rw [h_log_rho] at h_exp
      exact h_exp
    have h9 : ENNReal.ofReal (20 * R) ≤
        (32 : ENNReal) * ENNReal.ofReal (K + L + 1) * C * Kakeya.realRpowENN rho sigma := by
      have h10 : 20 * R = 20 * (K + L + 1) * rho := by
        simp [R] <;> ring
      rw [h10]
      have h14 : ENNReal.ofReal (20 * (K + L + 1) * rho) ≤
          ENNReal.ofReal (20 * (K + L + 1) * rho ^ sigma) := by
        apply ENNReal.ofReal_le_ofReal
        have h_pos : 0 ≤ 20 * (K + L + 1) := by positivity
        exact mul_le_mul_of_nonneg_left h_rho_le_rpow h_pos
      have h15 : ENNReal.ofReal (20 * (K + L + 1) * rho ^ sigma) ≤
          (32 : ENNReal) * ENNReal.ofReal (K + L + 1) * C * Kakeya.realRpowENN rho sigma := by
        have h_pos2 : 0 ≤ rho ^ sigma := by positivity
        have h_eq : ENNReal.ofReal ((20 * (K + L + 1)) * rho ^ sigma) =
            ENNReal.ofReal (20 * (K + L + 1)) * ENNReal.ofReal (rho ^ sigma) :=
          ENNReal.ofReal_mul (by positivity)
        rw [h_eq]
        have h16 : ENNReal.ofReal (20 * (K + L + 1)) ≤ (32 : ENNReal) * ENNReal.ofReal (K + L + 1) := by
          have h17 : (20 : ENNReal) * ENNReal.ofReal (K + L + 1) ≤ (32 : ENNReal) * ENNReal.ofReal (K + L + 1) := by
            gcongr <;> norm_num
          simpa using h17
        have h18 : (32 : ENNReal) * ENNReal.ofReal (K + L + 1) ≤ (32 : ENNReal) * ENNReal.ofReal (K + L + 1) * C := by
          have h19 : (1 : ENNReal) ≤ C := hC
          calc (32 : ENNReal) * ENNReal.ofReal (K + L + 1)
            = (32 : ENNReal) * ENNReal.ofReal (K + L + 1) * 1 := by simp
          _ ≤ (32 : ENNReal) * ENNReal.ofReal (K + L + 1) * C := by gcongr
        have h20 : ENNReal.ofReal (20 * (K + L + 1)) * ENNReal.ofReal (rho ^ sigma) ≤
            ((32 : ENNReal) * ENNReal.ofReal (K + L + 1) * C) * ENNReal.ofReal (rho ^ sigma) := by
          gcongr <;> exact h16.trans h18
        have h21 : ((32 : ENNReal) * ENNReal.ofReal (K + L + 1) * C) * ENNReal.ofReal (rho ^ sigma) =
            (32 : ENNReal) * ENNReal.ofReal (K + L + 1) * C * Kakeya.realRpowENN rho sigma := by
          simp [Kakeya.realRpowENN, mul_assoc, mul_comm, mul_left_comm]
        rw [h21] at h20
        exact h20
      exact h14.trans h15
    calc
      ∫⁻ (t : ℝ) in Set.Icc (-1 : ℝ) 1, g t ∂volume
        ≤ ∫⁻ (t : ℝ) in Set.Icc (-1 : ℝ) 1, bval2 ∂volume := h6
      _ = bval2 * volume (Set.Icc (-1 : ℝ) 1) := h7
      _ = ENNReal.ofReal 2 * bval2 := by
        rw [h8]
        exact mul_comm _ _
      _ = ENNReal.ofReal (20 * R) := by
        dsimp only [bval2]
        have h : ENNReal.ofReal 2 * ENNReal.ofReal (10 * R) = ENNReal.ofReal (2 * (10 * R)) := by
          rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
        rw [h]
        have h2 : 2 * (10 * R) = 20 * R := by ring
        rw [h2]
      _ ≤ (32 : ENNReal) * ENNReal.ofReal (K + L + 1) * C * Kakeya.realRpowENN rho sigma := h9

end Kakeya.Assouad

end
