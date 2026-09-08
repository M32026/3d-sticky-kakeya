/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Nets
public import Kakeya.KatzTao
public import Kakeya.Frostman
public import Kakeya.Mathlib.Finset

/-!
# The multiscale chain of GWZ Lemma 7.7(A)

`Tube.ParentBodyDensity.maxDensity_le_prod_of_uniform_at_scales` (GWZ Lemma 7.4) bounds the
leaf-level `maxDensity` of a family of `δ`-tubes by a product of per-level Katz–Tao constants,
but its hypotheses are an *abstract* multiscale chain package `(κ, tb, Q, proj, cover)`.

This file builds that package once and for all from a geometric grid of scales
`1 = σ 0 ≥ σ 1 ≥ … ≥ σ M = δ` with consecutive ratio at least `16`, and exports the single
specialized statement `maxDensity_le_prod_of_grid_cuts`, whose hypotheses are phrased purely
in terms of `fibreIndex` / `fibreBodies` / `ConvexSpaceBody.IsKatzTao`.  No later region needs
to see the chain.

## The chain

The chain nodes are *leaf indices used as representatives*: `κ k := ι` and
`tb k i := (T i).rescale (ρ k)`, where the Lemma 7.4 scale function is the grid inflated by a
factor `2` away from the finest level,
`ρ k = if k = Fin.last M then δ else 2 * σ k`.
The level-`k` representative set `Q k` is a maximal `σ k / 2`-separated subset of `s` in the
`L¹` endpoint metric (`exists_tube_net`), and `proj m` sends a node to its level-`m.castSucc`
representative.  Separation gives the level-`0` count `9 ^ (2n)`, which is exactly
`C_box * (R + 3) ^ (2n)` for `R = 6` and `C_box = 1`; closeness in the endpoint metric gives
both the chain containment `tb m.succ w ≤ tb m.castSucc (proj m w)` and the inclusion of the
`proj`-fibre into `fibreIndex`, which is what lets the assumed Katz–Tao hypothesis be
transported to the chain (`isKatzTao_rescale_le` absorbing the factor-`2` thickening).
-/

@[expose] public section

open MeasureTheory Real Metric

namespace Kakeya

namespace MultiScaleFac

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### A maximal separated subset of a `Finset` -/

/-! ### Endpoint closeness and rescale containment -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Both endpoints of a tube lie in its carrier. -/
theorem tube_endpoints_mem_carrier {δ : NNReal} (T : Tube δ E) :
    T.x ∈ T.carrier ∧ T.y ∈ T.carrier := by
  rw [T.carrier_eq_cthickening]
  exact ⟨Metric.self_subset_cthickening _ (left_mem_segment ℝ T.x T.y),
         Metric.self_subset_cthickening _ (right_mem_segment ℝ T.x T.y)⟩

/-! ### The per-scale representative net -/

/-- **Representative net at a scale.**  Given a finite family of `δ`-tubes in the unit ball and a
coarse scale `θ > 0`, there are a subfamily `s'` of representatives and a total assignment
`f : ι → ι` with `f i ∈ s'` such that the `θ'`-rescaling of `T (f i)` contains the `τ'`-rescaling of
`T i` whenever `τ' + θ / 2 ≤ θ'`, and `s'.card ≤ ((1 + θ/8) / (θ/8)) ^ (2n)`. -/
theorem exists_tube_net {ι : Type*} {δ : NNReal} (s : Finset ι) (hs : s.Nonempty)
    (T : ι → Tube δ E) (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {θ : NNReal} (hθ : 0 < θ) :
    ∃ (s' : Finset ι) (f : ι → ι), s' ⊆ s ∧ (∀ i ∈ s, f i ∈ s') ∧
      (∀ τ' θ' : NNReal, (τ' : ℝ) + (θ : ℝ) / 2 ≤ (θ' : ℝ) → ∀ i ∈ s,
        ((T i).rescale τ').toConvexSpaceBody ≤ ((T (f i)).rescale θ').toConvexSpaceBody) ∧
      (s'.card : ℝ) ≤ ((1 + (θ : ℝ) / 8) / ((θ : ℝ) / 8)) ^ (2 * Module.finrank ℝ E) := by
  classical
  let d : ι → ι → ℝ := fun i j => ‖(T i).x - (T j).x‖ + ‖(T i).y - (T j).y‖
  rcases Finset.exists_separated_net s d (ε := (θ : ℝ) / 2) (div_nonneg θ.coe_nonneg zero_le_two)
      (fun a => by simp only [d, sub_self, norm_zero, add_zero])
      (fun a b => by simp only [d, norm_sub_rev])
    with ⟨s', hs'sub, hsep, hdens⟩
  choose g hg₁ hg₂ using hdens
  obtain ⟨i₀, hi₀⟩ := hs
  let f : ι → ι := fun i => if hi : i ∈ s then g i hi else g i₀ hi₀
  have hf_mem : ∀ i ∈ s, f i ∈ s' := fun i hi => by
    simp only [f, dif_pos hi]; exact hg₁ i hi
  have hd_f : ∀ i ∈ s, ‖(T i).x - (T (f i)).x‖ + ‖(T i).y - (T (f i)).y‖ ≤ (θ : ℝ) / 2 :=
    fun i hi => by simp only [f, dif_pos hi]; exact hg₂ i hi
  have hx_ball : ∀ a ∈ s', ‖(T a).x - (0 : E)‖ ≤ 1 := fun a ha => by
    simpa only [Metric.mem_closedBall, dist_zero_right, sub_zero] using
      hball a (hs'sub ha) (tube_endpoints_mem_carrier (T a)).1
  have hy_ball : ∀ a ∈ s', ‖(T a).y - (0 : E)‖ ≤ 1 := fun a ha => by
    simpa only [Metric.mem_closedBall, dist_zero_right, sub_zero] using
      hball a (hs'sub ha) (tube_endpoints_mem_carrier (T a)).2
  refine ⟨s', f, hs'sub, hf_mem, fun τ' θ' hineq i hi =>
    Tube.rescale_le_rescale_of_endpoint_dist (T i) (T (f i)) (by linarith [hd_f i hi]), ?_⟩
  have hpack := Tube.card_le_of_L1_separated_in_box (E := E) s' (fun i => (T i).x)
    (fun i => (T i).y) (0 : E) (0 : E) (R := (1 : ℝ)) (r := (θ : ℝ) / 2)
    (div_pos (NNReal.coe_pos.mpr hθ) two_pos)
    (fun a ha b hb hne => (hsep a ha b hb hne).le) hx_ball hy_ball
  rwa [show ((1 : ℝ) + ((θ : ℝ) / 2) / 4) / (((θ : ℝ) / 2) / 4)
    = (1 + (θ : ℝ) / 8) / ((θ : ℝ) / 8) by ring] at hpack

/-! ### Katz–Tao under a bounded change of scale -/

/-- The dimensional price of moving the Katz–Tao constant of a family of rescaled tubes from
scale `τ` to a scale `τ' ≤ 2 * τ`: the ratio of the two-sided tube-volume bounds times
`2 ^ (n - 1)`. -/
noncomputable def katzTaoRescaleConst (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NNReal :=
  Tube.volume_le.C (Module.finrank ℝ E) * 2 ^ (Module.finrank ℝ E - 1)
    / Tube.le_volume.c (Module.finrank ℝ E)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The Katz–Tao rescaling cost is a positive constant. -/
theorem katzTaoRescaleConst_pos : 0 < katzTaoRescaleConst E := by
  have := Tube.le_volume.c_pos (Module.finrank ℝ E)
  unfold katzTaoRescaleConst Tube.volume_le.C
  positivity

/-- **Katz–Tao is stable under a bounded change of scale.**  If the `τ`-rescalings of a family
of tubes are `C`-Katz–Tao and `τ ≤ τ' ≤ 2 * τ` with `τ' ≤ 1`, then the `τ'`-rescalings are
`katzTaoRescaleConst E * C`-Katz–Tao: the index set shrinks (a `τ`-rescaling is contained in
the `τ'`-rescaling) while each body's volume grows by at most the dimensional factor. -/
theorem isKatzTao_rescale_le {ι : Type*} {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E)
    {τ τ' : NNReal} (hτ : 0 < τ) (hle : τ ≤ τ') (hτ' : τ' ≤ 2 * τ) (hτ'_one : τ' ≤ 1)
    {C : ENNReal}
    (h : ConvexSpaceBody.IsKatzTao s (fun i => ((T i).rescale τ).toConvexSpaceBody) C) :
    ConvexSpaceBody.IsKatzTao s (fun i => ((T i).rescale τ').toConvexSpaceBody)
      ((katzTaoRescaleConst E : ENNReal) * C) := by
  have _hτ := hτ
  rw [ConvexSpaceBody.isKatzTao_iff] at h ⊢
  intro K
  set n := Module.finrank ℝ E
  set A := (katzTaoRescaleConst E : ENNReal) with hA_def
  have hmulN : katzTaoRescaleConst E * Tube.le_volume.c n =
      Tube.volume_le.C n * 2 ^ (n - 1) := by
    unfold katzTaoRescaleConst
    exact div_mul_cancel₀ _ (Tube.le_volume.c_pos n).ne'
  have hmul : A * (Tube.le_volume.c n : ENNReal) =
      (Tube.volume_le.C n : ENNReal) * (2 : ENNReal) ^ (n - 1) := by
    rw [hA_def, ← ENNReal.coe_mul, hmulN]
    push_cast
    ring
  have h_vol_comp : ∀ i, volume ((T i).rescale τ').carrier ≤
      A * volume ((T i).rescale τ).carrier := fun i =>
    calc volume ((T i).rescale τ').carrier
        ≤ (Tube.volume_le.C n : ENNReal) * ((τ' : ENNReal) ^ (n - 1)) := by
          simpa only [ENNReal.coe_mul, ENNReal.coe_pow] using
            Tube.volume_le hτ'_one ((T i).rescale τ')
      _ ≤ (Tube.volume_le.C n : ENNReal) * (2 : ENNReal) ^ (n - 1) *
            ((τ : ENNReal) ^ (n - 1)) := by
          rw [mul_assoc, ← mul_pow]
          gcongr
          exact_mod_cast hτ'
      _ = A * ((Tube.le_volume.c n : ENNReal) * ((τ : ENNReal) ^ (n - 1))) := by
          rw [← mul_assoc, hmul]
      _ ≤ A * volume ((T i).rescale τ).carrier := by
          gcongr
          simpa only [ENNReal.coe_mul, ENNReal.coe_pow] using Tube.le_volume ((T i).rescale τ)
  have h_filter_subset : s.filter (fun i => ((T i).rescale τ').toConvexSpaceBody ≤ K) ⊆
      s.filter (fun i => ((T i).rescale τ).toConvexSpaceBody ≤ K) :=
    Finset.monotone_filter_right s fun i _ hi =>
      (Tube.rescale_le_rescale_of_radius_le (T i) hle).trans hi
  calc
    ∑ i ∈ s with ((T i).rescale τ').toConvexSpaceBody ≤ K, volume ((T i).rescale τ').carrier
        ≤ ∑ i ∈ s with ((T i).rescale τ').toConvexSpaceBody ≤ K,
            A * volume ((T i).rescale τ).carrier :=
      Finset.sum_le_sum fun i _ => h_vol_comp i
    _ = A * ∑ i ∈ s with ((T i).rescale τ').toConvexSpaceBody ≤ K,
        volume ((T i).rescale τ).carrier := Finset.mul_sum .. |>.symm
    _ ≤ A * ∑ i ∈ s with ((T i).rescale τ).toConvexSpaceBody ≤ K,
        volume ((T i).rescale τ).carrier :=
      mul_le_mul_right (Finset.sum_le_sum_of_subset h_filter_subset) _
    _ ≤ A * (C * volume K.carrier) := mul_le_mul_right (h K) _
    _ = (A * C) * volume K.carrier := (mul_assoc _ _ _).symm

/-! ### The inflated scale function -/

/-! ### The exported specialization of GWZ Lemma 7.4 -/

end MultiScaleFac

end Kakeya
