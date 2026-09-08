/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectCoveringBridge

/-!
# The covering bridge's two remaining rows: the anisotropic pull-back, and the grid

`Reduction/SpineDefectCoveringBridge.lean` transcribes `lem:defect-covering-bridge` (refined
l.5484–5672) and left exactly two rows open: `BridgeAnisotropicPullback` (the estimate
`eq:defect-pullback-line`, l.5573–5586) and `hgrid` (the location of `m` on the radius grid,
l.5590–5622).  This leaf closes both.

## The anisotropic pull-back — `exists_bridgeAnisotropicPullback`

`anisoInvLin ea ρ y = 8·(y_∥ + ρ y_⊥)` is the source's `L₀^{-1}` (l.5555), the **anisotropic**
inverse of the normalisation `L`.  This is precisely what the tree could not express: `Kakeya.ML2Reduction.carrier_subset_dilate_of_normaliseBody_subset_dilate` pulls back through
`normaliseBody`, whose contraction is the **isotropic** factor `8`, and lands in a dilated *tube*;
Mathlib's image lemmas for balls (`Metric.smul_image_closedBall`,
`LinearIsometryEquiv.image_closedBall`, `IsometryEquiv.image_closedBall`) cover only the isometric
and scalar cases.  A search of the whole tree for producers of `_ ⊆ lineNbhd _ _ _` returns only
`Conjunct6LineED.lean`'s core comparison and one negative statement.  So the estimate is built
here, from the inner-product geometry.

The proof follows the source line by line:

* `transverse_projection_norm_le` is l.5576–5578 — with `d_W·e_a ≥ 1/6`, the component of `e_a`
  normal to the pulled-back line has norm at most `6 ρ_a`.  The bound is sharp in the source's
  own constants: `‖·‖² = ρ_a²‖d_⊥‖²/(d₁² + ρ_a²‖d_⊥‖²) ≤ 36 ρ_a²`.
* `norm_sub_unitProj_le` is the elementary fact that projecting off a unit vector does not
  increase norms; it is used three times.
* `exists_bridgeAnisotropicPullback` is l.5578–5586: for `‖v‖ ≤ σ` the normal component of
  `L₀^{-1}v = 8(v_∥ + ρ_a v_⊥)` is at most `48 ρ_a σ + 8 ρ_a σ = 56 ρ_a σ`.  The longitudinal
  expansion is absorbed by the choice of the line parameter `s₀`, which is the Lean content of
  l.5587–5588 ("the pulled-back line itself absorbs it").

`hdir`, the cone `d_W · e_a ≥ 1/6` of `eq:defect-cover-direction` (l.5565–5566), is the source's
own *preceding* step — proved there from the geometry of the covered `b`-cell (l.5557–5567), not
from this estimate — and is carried here as a named hypothesis.

## The grid — `bridgeGrid`

`bridgeGrid M δ k` is `ρ_k = (1/40)δ^{k/M}` for `k < M` and `ρ_M = δ` (l.5487–5488).
`bridgeGrid_step` is the one-step ratio `q ρ_k ≤ ρ_{k+1} ≤ 40 q ρ_k` (l.5594); both ends are
equalities on this grid, the left for `k+1 < M` and the right at the last step.
`bridgeGrid_hgrid_of_maximal` is the bridge's `hgrid` itself (l.5600–5604, l.5621–5622);
`bridgeGrid_m_gt_a` and `bridgeGrid_m_lt_b` are the two location rows (l.5596–5600); and
`bridgeGrid_window_lower` / `bridgeGrid_window_upper` are the two window endpoints
(l.5606–5614), which are what put `m` in the range where `eq:defect-bridge-floor` is available.

Constants copied, never fitted: `1/40` and the grid exponent `k/M` (l.5487), `40` in the step
ratio (l.5594), `56` (l.5585), `1/6` (l.5566), `6ρ_a` (l.5578), `2` in `δ̃ = ρ_b/(2ρ_a)`
(l.5508).
-/

@[expose] public section

open Real RealInnerProductSpace

namespace Kakeya.ML2Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


/-- `x ↦ x − ⟪d,x⟫ d` is the orthogonal projection off a unit `d`; it does not increase norms. -/
theorem norm_sub_unitProj_le {d x : E} (hd : ‖d‖ = 1) : ‖x - ⟪d, x⟫ • d‖ ≤ ‖x‖ := by
  have hdd : ⟪d, d⟫ = (1:ℝ) := by rw [real_inner_self_eq_norm_sq, hd]; norm_num
  have hsq : ‖x - ⟪d, x⟫ • d‖ ^ 2 = ‖x‖ ^ 2 - ⟪d, x⟫ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hd,
      real_inner_comm x d, mul_one, sq_abs]
    ring
  nlinarith [norm_nonneg (x - ⟪d, x⟫ • d), norm_nonneg x, sq_nonneg ⟪d, x⟫, hsq]

/-- **The inverse linear part of the source's anisotropic normalisation**, refined l.5555:
`L₀⁻¹ y = 8 (y_∥ + ρ_a y_⊥)`, the parallel/perpendicular split taken against the unit core
direction `e_a` of the normalised cell.  This is `normaliseBody`'s **anisotropic** analogue: the
isotropic contraction `8` acts on the axis, and the transverse directions carry the extra
factor `ρ_a`, which is exactly what isotropic pull-back cannot express. -/
def anisoInvLin (ea : E) (ρ : ℝ) (y : E) : E :=
  (8 : ℝ) • (⟪ea, y⟫ • ea + ρ • (y - ⟪ea, y⟫ • ea))

theorem anisoInvLin_add (ea : E) (ρ : ℝ) (y z : E) :
    anisoInvLin ea ρ (y + z) = anisoInvLin ea ρ y + anisoInvLin ea ρ z := by
  simp only [anisoInvLin, inner_add_right]
  module

theorem anisoInvLin_smul (ea : E) (ρ : ℝ) (t : ℝ) (y : E) :
    anisoInvLin ea ρ (t • y) = t • anisoInvLin ea ρ y := by
  simp only [anisoInvLin, real_inner_smul_right]
  module

/-- Source l.5576-5578: the projection of `e_a` onto the normal plane of the pulled-back line
has norm at most `6 ρ_a`. -/
theorem transverse_projection_norm_le {ea dperp : E} {ρ d₁ : ℝ}
    (hea : ‖ea‖ = 1) (hperp : ⟪ea, dperp⟫ = 0) (hdp : ‖dperp‖ ≤ 1)
    (hρ0 : 0 < ρ) (hd1 : (1 : ℝ) / 6 ≤ d₁) :
    ‖ea - (⟪d₁ • ea + ρ • dperp, ea⟫ / ‖d₁ • ea + ρ • dperp‖ ^ 2) • (d₁ • ea + ρ • dperp)‖
      ≤ 6 * ρ := by
  set D : E := d₁ • ea + ρ • dperp with hD
  have hpc : ⟪dperp, ea⟫ = (0:ℝ) := by rw [real_inner_comm]; exact hperp
  have hee : ⟪ea, ea⟫ = (1:ℝ) := by rw [real_inner_self_eq_norm_sq, hea]; norm_num
  have hDe : ⟪D, ea⟫ = d₁ := by
    rw [hD, inner_add_left, real_inner_smul_left, real_inner_smul_left, hee, hpc]; ring
  have hdd : ⟪dperp, dperp⟫ = ‖dperp‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hDn : ‖D‖ ^ 2 = d₁ ^ 2 + ρ ^ 2 * ‖dperp‖ ^ 2 := by
    rw [hD, ← real_inner_self_eq_norm_sq, inner_add_add_self]
    simp only [real_inner_smul_left, real_inner_smul_right, hee, hperp, hpc, hdd]
    ring
  have hd10 : (0:ℝ) < d₁ := lt_of_lt_of_le (by norm_num) hd1
  have hq0 : (0:ℝ) ≤ ‖dperp‖ ^ 2 := sq_nonneg _
  have hN0 : (0:ℝ) < ‖D‖ ^ 2 := by rw [hDn]; nlinarith
  set N : ℝ := ‖D‖ ^ 2 with hNdef
  set q : ℝ := ‖dperp‖ ^ 2 with hqdef
  have hNq : N = d₁ ^ 2 + ρ ^ 2 * q := hDn
  set a : ℝ := ρ ^ 2 * q / N with ha
  set c : ℝ := -(d₁ * ρ / N) with hc
  have hvec : ea - (⟪D, ea⟫ / N) • D = a • ea + c • dperp := by
    rw [hDe, hD, ha, hc]
    have h1 : (1:ℝ) - d₁ ^ 2 / N = ρ ^ 2 * q / N := by
      field_simp [hN0.ne']
      linarith [hNq]
    have h2 : ea - (d₁ / N) • (d₁ • ea + ρ • dperp)
        = ((1:ℝ) - d₁ ^ 2 / N) • ea + (-(d₁ * ρ / N)) • dperp := by
      match_scalars <;> field_simp
    rw [h2, h1]
  have hsq : ‖a • ea + c • dperp‖ ^ 2 = a ^ 2 + c ^ 2 * q := by
    rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hperp,
      norm_smul, norm_smul, hea, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [hqdef]
    ring_nf
    rw [sq_abs, sq_abs]
  have hval : a ^ 2 + c ^ 2 * q = ρ ^ 2 * q / N := by
    rw [ha, hc]
    field_simp
    nlinarith [hNq]
  have hle : ρ ^ 2 * q / N ≤ 36 * ρ ^ 2 := by
    rw [div_le_iff₀ hN0]
    have hq1 : q ≤ 1 := by
      rw [hqdef]; nlinarith [norm_nonneg dperp]
    have h36 : (0:ℝ) ≤ 36 * d₁ ^ 2 - q := by nlinarith
    have hA : (0:ℝ) ≤ ρ ^ 2 * (36 * d₁ ^ 2 - q) := mul_nonneg (sq_nonneg ρ) h36
    have hB : (0:ℝ) ≤ 36 * (ρ ^ 2 * ρ ^ 2 * q) :=
      by positivity
    rw [hNq]; nlinarith [hA, hB]
  rw [hvec]
  nlinarith [norm_nonneg (a • ea + c • dperp), hsq, hval, hle, hρ0]

/-- The projection off a unit `d` is linear on the two-term combinations we need. -/
theorem unitProj_lin (d x y : E) (a b : ℝ) :
    (a • x + b • y) - ⟪d, a • x + b • y⟫ • d
      = a • (x - ⟪d, x⟫ • d) + b • (y - ⟪d, y⟫ • d) := by
  simp only [inner_add_right, real_inner_smul_right]
  module

/-- **`eq:defect-pullback-line`, refined l.5573–5586 — the open row of
`Kakeya.ML2Core.BridgeAnisotropicPullback`, now closed.**

Under the inverse `y ↦ m_a + L₀^{-1}y` of the source's anisotropic normalisation, the image of a
`σ`-tube `W` whose direction meets `e_a` in the cone `d_W · e_a ≥ 1/6` lies in the
`56 ρ_a σ`-neighbourhood of a single affine line.  Both constants are the source's: the `1/6` is
`eq:defect-cover-direction` (l.5565–5566) and the `56` is `48 + 8` (l.5578–5581), the transverse
part of `L₀^{-1}y = 8(y_∥ + ρ_a y_⊥)` against the `6ρ_a` tilt of `e_a` off the pulled-back line.

The longitudinal expansion is harmless "because the pulled-back line itself absorbs it"
(l.5587–5588): in the proof that is the choice of the line parameter `s₀`, which carries the
component of `L₀^{-1}v` along the line.

`hdir` is the source's own preceding step (l.5557–5567) and is carried as a hypothesis: it is
proved there from the geometry of the covered `b`-cell, not from this estimate. -/
theorem exists_bridgeAnisotropicPullback [ProperSpace E]
    {σ : NNReal} (Wt : Tube σ E) (ea ma : E) (ρ : ℝ)
    (hea : ‖ea‖ = 1) (hρ0 : 0 < ρ)
    (hdir : (1 : ℝ) / 6 ≤ ⟪ea, Wt.direction⟫) :
    ∃ p d : E, BridgeAnisotropicPullback (fun y ↦ ma + anisoInvLin ea ρ y) ρ Wt p d := by
  classical
  set dW : E := Wt.direction with hdWdef
  have hdWn : ‖dW‖ = 1 := Wt.norm_direction
  set d₁ : ℝ := ⟪ea, dW⟫ with hd1def
  set dperp : E := dW - d₁ • ea with hdperpdef
  have hee : ⟪ea, ea⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hea]; norm_num
  have hperp : ⟪ea, dperp⟫ = (0 : ℝ) := by
    rw [hdperpdef, inner_sub_right, real_inner_smul_right, hee, hd1def]; ring
  have hdp : ‖dperp‖ ≤ 1 := by
    have h := norm_sub_unitProj_le (d := ea) (x := dW) hea
    rw [hdWn] at h
    rw [hdperpdef, hd1def]
    exact h
  have hd10 : (0 : ℝ) < d₁ := lt_of_lt_of_le (by norm_num) hdir
  set D₀ : E := d₁ • ea + ρ • dperp with hD₀def
  have hpc : ⟪dperp, ea⟫ = (0 : ℝ) := by rw [real_inner_comm]; exact hperp
  have hdd : ⟪dperp, dperp⟫ = ‖dperp‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hD₀n2 : ‖D₀‖ ^ 2 = d₁ ^ 2 + ρ ^ 2 * ‖dperp‖ ^ 2 := by
    rw [hD₀def, ← real_inner_self_eq_norm_sq, inner_add_add_self]
    simp only [real_inner_smul_left, real_inner_smul_right, hee, hperp, hpc, hdd]
    ring
  have hD₀0 : (0 : ℝ) < ‖D₀‖ := by
    nlinarith [norm_nonneg D₀, hD₀n2, sq_nonneg (ρ * ‖dperp‖), sq_nonneg ρ, norm_nonneg dperp]
  set d : E := ‖D₀‖⁻¹ • D₀ with hddef
  have hdn : ‖d‖ = 1 := by
    rw [hddef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hD₀0)]
    field_simp
  have hproj_ea : ea - ⟪d, ea⟫ • d
      = ea - (⟪D₀, ea⟫ / ‖D₀‖ ^ 2) • D₀ := by
    rw [hddef, real_inner_smul_left, smul_smul]
    congr 2
    field_simp
  have h6 : ‖ea - ⟪d, ea⟫ • d‖ ≤ 6 * ρ := by
    rw [hproj_ea]
    exact transverse_projection_norm_le hea hperp hdp hρ0 hdir
  refine ⟨ma + anisoInvLin ea ρ Wt.x, d, hdn, ?_⟩
  rintro y ⟨w, hw, rfl⟩
  rw [Wt.carrier_eq] at hw
  obtain ⟨z, hz, hwz⟩ := Set.mem_iUnion₂.mp hw
  rw [segment_eq_image' ℝ Wt.x Wt.y] at hz
  obtain ⟨t, -, hzeq⟩ := hz
  have hzeq' : z = Wt.x + t • dW := by rw [← hzeq, hdWdef]
  set v : E := w - z with hvdef
  have hv : ‖v‖ ≤ (σ : ℝ) := by
    have : dist w z ≤ (σ : ℝ) := by simpa [Metric.mem_closedBall] using hwz
    rwa [dist_eq_norm] at this
  have hwsplit : w = z + v := by rw [hvdef]; abel
  set u : E := anisoInvLin ea ρ v with hudef
  have haD : anisoInvLin ea ρ dW = (8 : ℝ) • D₀ := by
    rw [anisoInvLin, hD₀def, hdperpdef, hd1def]
  have himg : anisoInvLin ea ρ w
      = anisoInvLin ea ρ Wt.x + (t * (8 * ‖D₀‖)) • d + u := by
    rw [hwsplit, anisoInvLin_add, hzeq', anisoInvLin_add, anisoInvLin_smul, haD, hddef, ← hudef]
    rw [smul_smul, smul_smul]
    congr 2
    field_simp
  refine Kakeya.VeryNotSticky.mem_lineNbhd_of_dist_le (t * (8 * ‖D₀‖) + ⟪d, u⟫) ?_
  have hvec : (ma + anisoInvLin ea ρ w)
      - ((ma + anisoInvLin ea ρ Wt.x) + (t * (8 * ‖D₀‖) + ⟪d, u⟫) • d)
      = u - ⟪d, u⟫ • d := by
    rw [himg, add_smul]
    abel
  rw [dist_eq_norm, hvec]
  -- split `u` into its axial and transverse parts and project off `d`
  set v₁ : ℝ := ⟪ea, v⟫ with hv1def
  set vperp : E := v - v₁ • ea with hvperpdef
  have hu : u = (8 * v₁) • ea + (8 * ρ) • vperp := by
    rw [hudef, anisoInvLin, hvperpdef, hv1def]
    module
  have hsplit : u - ⟪d, u⟫ • d
      = (8 * v₁) • (ea - ⟪d, ea⟫ • d) + (8 * ρ) • (vperp - ⟪d, vperp⟫ • d) := by
    rw [hu]; exact unitProj_lin d ea vperp (8 * v₁) (8 * ρ)
  have hv1 : |v₁| ≤ (σ : ℝ) := by
    have h := abs_real_inner_le_norm ea v
    rw [hea, one_mul] at h
    exact le_trans h hv
  have hvperp : ‖vperp - ⟪d, vperp⟫ • d‖ ≤ (σ : ℝ) := by
    refine le_trans (norm_sub_unitProj_le hdn) ?_
    refine le_trans ?_ hv
    have h := norm_sub_unitProj_le (d := ea) (x := v) hea
    rw [hvperpdef, hv1def]
    exact h
  have hσ0 : (0 : ℝ) ≤ (σ : ℝ) := σ.coe_nonneg
  calc ‖u - ⟪d, u⟫ • d‖
      ≤ ‖(8 * v₁) • (ea - ⟪d, ea⟫ • d)‖ + ‖(8 * ρ) • (vperp - ⟪d, vperp⟫ • d)‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ = |8 * v₁| * ‖ea - ⟪d, ea⟫ • d‖ + |8 * ρ| * ‖vperp - ⟪d, vperp⟫ • d‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (8 * (σ : ℝ)) * (6 * ρ) + (8 * ρ) * (σ : ℝ) := by
        have ha1 : |8 * v₁| ≤ 8 * (σ : ℝ) := by
          rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 8)]
          nlinarith [hv1, abs_nonneg v₁]
        have ha2 : |8 * ρ| = 8 * ρ := abs_of_pos (by linarith)
        have hne : (0:ℝ) ≤ ‖ea - ⟪d, ea⟫ • d‖ := norm_nonneg _
        rw [ha2]
        have hb1 : |8 * v₁| * ‖ea - ⟪d, ea⟫ • d‖ ≤ (8 * (σ:ℝ)) * (6 * ρ) :=
          mul_le_mul ha1 h6 hne (by linarith)
        have hb2 : (8 * ρ) * ‖vperp - ⟪d, vperp⟫ • d‖ ≤ (8 * ρ) * (σ : ℝ) :=
          mul_le_mul_of_nonneg_left hvperp (by linarith)
        linarith
    _ = 56 * ρ * (σ : ℝ) := by ring

section Grid


/-- **The source's radius grid**, refined l.5487–5488:
`ρ_k = (1/40)·δ^{k/M}` for `0 ≤ k < M`, and `ρ_M = δ`. -/
noncomputable def bridgeGrid (M : ℕ) (δ : ℝ) (k : ℕ) : ℝ :=
  if k < M then (1 / 40) * δ ^ ((k : ℝ) / (M : ℝ)) else δ

theorem bridgeGrid_pos {M : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (k : ℕ) : 0 < bridgeGrid M δ k := by
  unfold bridgeGrid
  split
  · positivity
  · exact hδ0

/-- **The one-step ratio**, refined l.5594: `q ρ_k ≤ ρ_{k+1} ≤ 40 q ρ_k` with `q = δ^{1/M}`.
Both ends are equalities on the grid: the left one for `k+1 < M`, the right one at the last
step `k+1 = M`, where `ρ_M = δ = 40 q ρ_{M-1}`. -/
theorem bridgeGrid_step {M : ℕ} {δ : ℝ} (hM : 0 < M) (hδ0 : 0 < δ) {k : ℕ} (hk : k < M) :
    δ ^ (1 / (M : ℝ)) * bridgeGrid M δ k ≤ bridgeGrid M δ (k + 1) ∧
      bridgeGrid M δ (k + 1) ≤ 40 * (δ ^ (1 / (M : ℝ)) * bridgeGrid M δ k) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hadd : δ ^ (1 / (M : ℝ)) * δ ^ ((k : ℝ) / (M : ℝ))
      = δ ^ (((k : ℝ) + 1) / (M : ℝ)) := by
    rw [← Real.rpow_add hδ0]
    congr 1
    field_simp
    ring
  have hkey : δ ^ (1 / (M : ℝ)) * ((1 / 40) * δ ^ ((k : ℝ) / (M : ℝ)))
      = (1 / 40) * δ ^ (((k : ℝ) + 1) / (M : ℝ)) := by
    calc δ ^ (1 / (M : ℝ)) * ((1 / 40) * δ ^ ((k : ℝ) / (M : ℝ)))
        = (1 / 40) * (δ ^ (1 / (M : ℝ)) * δ ^ ((k : ℝ) / (M : ℝ))) := by ring
      _ = (1 / 40) * δ ^ (((k : ℝ) + 1) / (M : ℝ)) := by rw [hadd]
  rcases lt_or_ge (k + 1) M with h | h
  · have h1 : bridgeGrid M δ k = (1 / 40) * δ ^ ((k : ℝ) / (M : ℝ)) := by
      unfold bridgeGrid; rw [if_pos hk]
    have h2 : bridgeGrid M δ (k + 1) = (1 / 40) * δ ^ ((((k : ℕ) + 1 : ℕ) : ℝ) / (M : ℝ)) := by
      unfold bridgeGrid; rw [if_pos h]
    rw [h1, h2, hkey]
    push_cast
    constructor
    · exact le_of_eq (by ring_nf)
    · nlinarith [Real.rpow_pos_of_pos hδ0 (((k : ℝ) + 1) / (M : ℝ))]
  · have hkM : k + 1 = M := le_antisymm hk h
    have h1 : bridgeGrid M δ k = (1 / 40) * δ ^ ((k : ℝ) / (M : ℝ)) := by
      unfold bridgeGrid; rw [if_pos hk]
    have h2 : bridgeGrid M δ (k + 1) = δ := by
      unfold bridgeGrid; rw [if_neg (by omega)]
    have h3 : δ ^ (1 / (M : ℝ)) * ((1 / 40) * δ ^ ((k : ℝ) / (M : ℝ))) = δ / 40 := by
      rw [hkey]
      have : ((k : ℝ) + 1) / (M : ℝ) = 1 := by
        have : ((k : ℝ) + 1) = (M : ℝ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hkM
        rw [this]; field_simp
      rw [this, Real.rpow_one]; ring
    rw [h1, h2, h3]
    constructor <;> linarith

/-- **`hgrid`, refined l.5600–5604 and l.5621–5622.**  If `m` is maximal with `ρ_m ≥ 56 ρ_a σ` —
so that the *next* radius already falls below the threshold — then the one-step ratio
`q ρ_m ≤ ρ_{m+1}` bounds `ρ_m` from above by `56 ρ_a σ / q`, which is the bridge's `hgrid`
`δ^{1/M}/(56 σ) ≤ ρ_a/ρ_m`.  Stated on the two radii alone: the grid enters only through
`hstep`. -/
theorem bridgeGrid_hgrid_of_maximal {q σ ρa ρm ρnext : ℝ}
    (_hq0 : 0 < q) (hσ0 : 0 < σ) (_hρa0 : 0 < ρa) (hρm0 : 0 < ρm)
    (hstep : q * ρm ≤ ρnext) (hmax : ρnext ≤ 56 * ρa * σ) :
    q / (56 * σ) ≤ ρa / ρm := by
  rw [div_le_div_iff₀ (by positivity) hρm0]
  nlinarith

/-- **`m` sits strictly above `a`**, refined l.5596–5598: the first scale test
`56 σ ≤ q x^ε` with `x ≤ 1` gives `56 ρ_a σ ≤ q ρ_a`, so the threshold is below the radius one
step down from `ρ_a`. -/
theorem bridgeGrid_m_gt_a {q σ ρa x ε : ℝ}
    (hq0 : 0 < q) (hρa0 : 0 < ρa) (hx0 : 0 < x) (hx1 : x ≤ 1) (hε0 : 0 ≤ ε)
    (htest : 56 * σ ≤ q * x ^ ε) :
    56 * ρa * σ ≤ q * ρa := by
  have hxe : x ^ ε ≤ 1 := Real.rpow_le_one hx0.le hx1 hε0
  have h1 : q * x ^ ε ≤ q := by nlinarith [hq0.le]
  have h2 : 56 * σ ≤ q := le_trans htest h1
  nlinarith [mul_le_mul_of_nonneg_left h2 hρa0.le]

/-- **`m` sits strictly below `b`**, refined l.5598–5600: `σ ≥ δ̃ = x/2` with `x = ρ_b/ρ_a`
gives `56 ρ_a σ ≥ 28 ρ_b > ρ_b`. -/
theorem bridgeGrid_m_lt_b {σ ρa ρb : ℝ}
    (hρa0 : 0 < ρa) (hρb0 : 0 < ρb) (hσ : ρb / (2 * ρa) ≤ σ) :
    ρb < 56 * ρa * σ := by
  rw [div_le_iff₀ (by positivity)] at hσ
  nlinarith

/-- **The lower window endpoint**, refined l.5606–5609: `ρ_b/ρ_m > q x/(56 σ) ≥ x^{1-ε}`, the
first scale test read as an endpoint. -/
theorem bridgeGrid_window_lower {q σ x ε : ℝ}
    (hq0 : 0 < q) (hσ0 : 0 < σ) (hx0 : 0 < x)
    (htest : 56 * σ ≤ q * x ^ ε) :
    x ^ (1 - ε) ≤ q * x / (56 * σ) := by
  rw [le_div_iff₀ (by positivity)]
  have hx : x ^ (1 - ε) * x ^ ε = x := by
    rw [← Real.rpow_add hx0]; simp
  nlinarith [Real.rpow_pos_of_pos hx0 (1 - ε), Real.rpow_pos_of_pos hx0 ε]

/-- **The upper window endpoint**, refined l.5611–5614: `σ ≥ δ̃^{1-ε_sc}` with `δ̃ = x/2` and
`ε ≤ ε_sc` give `x/(56 σ) ≤ x^ε`; "the fixed factor `2` is dominated by `56`". -/
theorem bridgeGrid_window_upper {σ x ε εsc : ℝ}
    (hσ0 : 0 < σ) (hx0 : 0 < x) (hx1 : x ≤ 1) (hεsc0 : 0 < εsc) (hεsc1 : εsc < 1)
    (hε : ε ≤ εsc)
    (hσlo : (x / 2) ^ (1 - εsc) ≤ σ) :
    x / (56 * σ) ≤ x ^ ε := by
  have hhalf : (x / 2) ^ (1 - εsc) = x ^ (1 - εsc) * (1 / 2 : ℝ) ^ (1 - εsc) := by
    rw [show x / 2 = x * (1 / 2 : ℝ) by ring, Real.mul_rpow hx0.le (by norm_num)]
  have hpow : (1 / 2 : ℝ) ^ (1 - εsc) ≥ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ (1 - εsc) ≥ (1 / 2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_one]
  have hx1e : x ^ (1 - εsc) * x ^ εsc = x := by rw [← Real.rpow_add hx0]; simp
  have hxe : x ^ εsc ≤ x ^ ε := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hε
  have h1 : x ^ (1 - εsc) * (1 / 2 : ℝ) ≤ σ := by
    refine le_trans ?_ hσlo
    rw [hhalf]
    have := Real.rpow_pos_of_pos hx0 (1 - εsc)
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Real.rpow_pos_of_pos hx0 (1 - εsc), Real.rpow_pos_of_pos hx0 εsc,
    Real.rpow_pos_of_pos hx0 ε]

end Grid

end Kakeya.ML2Core

end
