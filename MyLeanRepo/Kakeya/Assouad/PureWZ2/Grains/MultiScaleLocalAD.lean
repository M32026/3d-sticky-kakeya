import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.WZ1.ADScaleRefinement

/-!
# Pure WZ2 multi-scale local AD iteration

Adapts the WZ1 `EveryScaleLocalGrain` multi-scale argument to the PureWZ2
balanced-cover setting.  Replaces `UniformTubeStructure` + `WZ1ExtremalPair`
with sticky data (`PureWZ2PropStickyData`: balanced cover + coarse extremal).

## Proof structure

1. **One-scale lemma hypothesis** (`PureWZ2OneScaleLocalGrainConclusion`):
   given sticky data at coarse scale `rho`, produce a subshading with the
   1-σ `IsADSet1` bound at scale `rho`.

2. **Multi-scale iteration**: the N-scale grid
   `rho_k = δ^(1-k/N)`, `k ∈ [⌈N·midLoss⌉, ⌊N·(1-midLoss)⌋]`,
   applying the one-scale lemma at each scale and accumulating AD bounds
   on nested subshadings.

3. **Fine scales**: for `rho > rho_kmax`, the trivial bound `10/rho` is
   absorbed via `epsilon = outputLoss - 2·midLoss - 1/N > 0`.

4. **Plane map preserved** across iterations (restriction to smaller unions).
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Subshading relation for paper tube shadings. -/
abbrev PaperIsSubshading' {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Z Y : WZ1PaperTubeShading F) : Prop :=
  ∀ i, Z.carrier i ⊆ Y.carrier i

/-- If Z is a subshading of Y, then Z.union ⊆ Y.union. -/
lemma PaperIsSubshading'.union {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Z Y : WZ1PaperTubeShading F} (h : PaperIsSubshading' Z Y) :
    Z.union ⊆ Y.union := by
  rintro x ⟨i, hi⟩
  exact ⟨i, h i hi⟩

/-!
## One-scale output and conclusion type
-/

/--
One-scale local AD output for PureWZ2.

A subshading `Z` of `Y` on which the scalar projection has the 1-σ
`IsADSet1` bound at the selected scale `rho`.

The nesting iteration handles mass retention separately via the hereditary
sticky provision and polylog retention per step.
-/
structure PureWZ2OneScaleLocalGrainData
    {delta sigma outputLoss rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (planeMap : {point : Point3 // point ∈ Y.union} → Point3) where
  shading : WZ1PaperTubeShading F
  subshading : PaperIsSubshading' shading Y
  extremal : WZ2PaperCroppedIsExtremal sigma outputLoss F shading
  cwa : WZ2PaperConvexWolffBound F (Kakeya.realRpowENN delta (-outputLoss))
  local_ad :
    ∀ (p : Point3) (hp : p ∈ shading.union),
      IsADSet1
        (scalarProjection (planeMap ⟨p, subshading.union hp⟩)
          (shading.union ∩ Metric.closedBall p (Real.sqrt rho)))
        rho (1 - sigma)
        (Kakeya.realRpowENN delta (-outputLoss))

/--
Provision of sticky data at any requested scale for an extremal shading.
-/
def PureWZ2StickyAtScale : Prop :=
  ∀ (sigma outputLoss : ℝ),
    0 < sigma → sigma < 1 →
    0 < outputLoss →
      ∃ (inputLoss delta₀ : ℝ),
        0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
          ∀ (F : Kakeya.Streamlined.TubeFamily delta)
            (Y : WZ1PaperTubeShading F),
            WZ2PaperCroppedIsExtremal sigma inputLoss F Y →
            WZ2PaperConvexWolffBound F (Kakeya.realRpowENN delta (-inputLoss)) →
            ∀ (rho : WZ2PaperRequestedScale delta) (logExponent : ℕ),
              Nonempty (PureWZ2PropStickyData
                (sigma := sigma) (outputLoss := outputLoss)
                (sourceShading := Y) rho logExponent)

/--
Shading-specific provision of sticky data at any requested scale.

Fix C: This is the shading-specific version of `PureWZ2StickyAtScale`.
Instead of quantifying over all families/shadings, it is parameterized by
a specific `delta`, `F`, `Y`.

Node 3 provides this directly for the normalized shading.
-/
def PureWZ2StickyAtScaleFor
    (delta : ℝ) (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : WZ1PaperTubeShading F) : Prop :=
  ∀ (sigma outputLoss : ℝ),
    0 < sigma → sigma < 1 →
    0 < outputLoss →
      ∃ (inputLoss : ℝ),
        0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
          WZ2PaperCroppedIsExtremal sigma inputLoss F Y →
          WZ2PaperConvexWolffBound F (Kakeya.realRpowENN delta (-inputLoss)) →
          ∀ (rho : WZ2PaperRequestedScale delta) (logExponent : ℕ),
            Nonempty (PureWZ2PropStickyData
              (sigma := sigma) (outputLoss := outputLoss)
              (sourceShading := Y) rho logExponent)

/--
Shading-specific sticky provision with fixed `sigma` and `outputLoss`.

Simplified Fix C: This is the type passed to the plane map construction.
Unlike `PureWZ2StickyAtScale` (universal over all families/shadings) or
`PureWZ2StickyAtScaleFor` (which re-packages the `inputLoss` existential),
this type assumes `sigma`/`outputLoss` are already fixed and just provides
sticky data at any requested scale for the specific shading `Y`.

Node 3 (`PureWZ2CroppedPropStickyAt`) provides this directly for
`normalized.croppedRefined` within the scale range
`[delta^(1-outputLoss), delta^outputLoss]`.
-/
def PureWZ2StickyProvisionFor
    (delta : ℝ) (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : WZ1PaperTubeShading F)
    (sigma outputLoss : ℝ) : Prop :=
  ∀ (rho : WZ2PaperRequestedScale delta) (logExponent : ℕ),
    Nonempty (PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      (sourceShading := Y) rho logExponent)

/--
One-scale local AD conclusion (hypothesis of the multi-scale theorem).

Takes a sticky provision at all scales (not just one), enabling the multi-scale
Córdoba approach which needs balanced covers at both ρ and an intermediate τ.
-/
def PureWZ2OneScaleLocalGrainConclusion : Prop :=
  ∀ (sigma outputLoss : ℝ) (logExponent : ℕ),
    0 < sigma → sigma < 1 →
    0 < outputLoss →
      ∃ (inputLoss delta₀ : ℝ),
        0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
          ∀ (F : Kakeya.Streamlined.TubeFamily delta)
            (Y : WZ1PaperTubeShading F),
            WZ2PaperCroppedIsExtremal sigma inputLoss F Y →
            WZ2PaperConvexWolffBound F (Kakeya.realRpowENN delta (-inputLoss)) →
            ∀ (L : NNReal), (L : ℝ) ≤ Real.rpow delta (-inputLoss) →
              ∀ (planeMap : {point : Point3 // point ∈ Y.union} → Point3),
                LipschitzWith L planeMap →
                (∀ p, ‖planeMap p‖ = 1) →
                (∀ i p hp,
                  |inner ℝ (F.tube i).direction
                    (planeMap ⟨p, ⟨i, hp⟩⟩)| ≤ delta) →
                (h_sticky_provision :
                  ∀ (rho' : WZ2PaperRequestedScale delta),
                    Real.rpow delta (1 - outputLoss) ≤ rho'.1 →
                    rho'.1 ≤ Real.rpow delta outputLoss →
                    Nonempty (PureWZ2PropStickyData
                      (sigma := sigma) (outputLoss := outputLoss)
                      (sourceShading := Y) rho' logExponent)) →
                ∀ (rho : ℝ) (hrho1 : delta ≤ rho) (hrho2 : rho ≤ 1),
                  Nonempty (PureWZ2OneScaleLocalGrainData
                    (sigma := sigma) (outputLoss := outputLoss)
                    (rho := rho) (Y := Y) planeMap)

/-!
## Every-scale output and conclusion type
-/

/--
Every-scale local grain output for PureWZ2.
-/
structure PureWZ2EveryScaleLocalGrainData
    {delta sigma outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (planeMap : {point : Point3 // point ∈ Y.union} → Point3) where
  shading : WZ1PaperTubeShading F
  subshading : PaperIsSubshading' shading Y
  extremal : WZ2PaperCroppedIsExtremal sigma outputLoss F shading
  cwa : WZ2PaperConvexWolffBound F (Kakeya.realRpowENN delta (-outputLoss))
  localGrains :
    PureWZ2LocalGrainData shading sigma
      (Kakeya.realRpowENN delta (-outputLoss))

/--
Every-scale local grain conclusion for PureWZ2.
-/
def PureWZ2EveryScaleLocalGrainConclusion : Prop :=
  ∀ (sigma outputLoss : ℝ),
    0 < sigma → sigma < 1 →
    0 < outputLoss →
      ∃ (inputLoss delta₀ : ℝ),
        0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
          ∀ (F : Kakeya.Streamlined.TubeFamily delta)
            (Y : WZ1PaperTubeShading F),
            WZ2PaperCroppedIsExtremal sigma inputLoss F Y →
            WZ2PaperConvexWolffBound F (Kakeya.realRpowENN delta (-inputLoss)) →
            ∀ (planeMap : {point : Point3 // point ∈ Y.union} → Point3),
              LipschitzWith 1 planeMap →
              (∀ p, ‖planeMap p‖ = 1) →
              (∀ i p hp,
                |inner ℝ (F.tube i).direction
                  (planeMap ⟨p, ⟨i, hp⟩⟩)| ≤ delta) →
              Nonempty (PureWZ2EveryScaleLocalGrainData
                (sigma := sigma) (outputLoss := outputLoss)
                (Y := Y) planeMap)

/-!
## Plane-map restriction helpers
-/

/-- Restrict a plane map from `Y.union` to `Z.union`. -/
def restrictPlaneMap
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y Z : WZ1PaperTubeShading F}
    (hsub : PaperIsSubshading' Z Y)
    (planeMap : {point : Point3 // point ∈ Y.union} → Point3) :
    {point : Point3 // point ∈ Z.union} → Point3 :=
  fun p => planeMap ⟨p, hsub.union p.prop⟩

lemma restrictPlaneMap_lipschitz
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y Z : WZ1PaperTubeShading F}
    (hsub : PaperIsSubshading' Z Y)
    (planeMap : {point : Point3 // point ∈ Y.union} → Point3)
    (hlip : LipschitzWith 1 planeMap) :
    LipschitzWith 1 (restrictPlaneMap hsub planeMap) := by
  intro p q
  exact hlip ⟨p, hsub.union p.prop⟩ ⟨q, hsub.union q.prop⟩

lemma restrictPlaneMap_unit
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y Z : WZ1PaperTubeShading F}
    (hsub : PaperIsSubshading' Z Y)
    (planeMap : {point : Point3 // point ∈ Y.union} → Point3)
    (hunit : ∀ p, ‖planeMap p‖ = 1) :
    ∀ p, ‖restrictPlaneMap hsub planeMap p‖ = 1 := by
  intro p
  exact hunit ⟨p, hsub.union p.prop⟩

lemma restrictPlaneMap_incidence
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y Z : WZ1PaperTubeShading F}
    (hsub : PaperIsSubshading' Z Y)
    (planeMap : {point : Point3 // point ∈ Y.union} → Point3)
    (hinc : ∀ i p hp, |inner ℝ (F.tube i).direction (planeMap ⟨p, ⟨i, hp⟩⟩)| ≤ delta) :
    ∀ i p hp, |inner ℝ (F.tube i).direction
        (restrictPlaneMap hsub planeMap ⟨p, ⟨i, hp⟩⟩)| ≤ delta := by
  intro i p hp
  exact hinc i p (hsub i hp)

/-- Points in a paper tube shading lie in `axisBox 2 2 2`, hence have norm ≤ 3. -/
lemma paperShading_point_bounded
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Z : WZ1PaperTubeShading F} {x : Point3} (hx : x ∈ Z.union) :
    ‖x‖ ≤ 3 := by
  rcases hx with ⟨i, hi⟩
  have h2 : x ∈ ((wz1PaperBodyFamily F).body i).carrier := Z.subset_body i hi
  have h3 : x ∈ wz1PaperTubeCarrier (F.tube i) := by
    have h4 : ((wz1PaperBodyFamily F).body i).carrier = wz1PaperTubeCarrier (F.tube i) := by rfl
    rw [h4] at h2
    exact h2
  have h_in_box : x ∈ Kakeya.Streamlined.axisBox 2 2 2 := h3.2
  have h_coords : |x 0| ≤ 1 ∧ |x 1| ≤ 1 ∧ |x 2| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using h_in_box
  have h_norm_sq : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
    have h := EuclideanSpace.real_norm_sq_eq x
    simpa [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] using h
  have h4 : ‖x‖ ^ 2 ≤ 9 := by
    rw [h_norm_sq]
    have h5 : |x 0| ≤ 1 := h_coords.1
    have h6 : |x 1| ≤ 1 := h_coords.2.1
    have h7 : |x 2| ≤ 1 := h_coords.2.2
    have h8 : (x 0) ^ 2 ≤ 1 := by nlinarith [abs_le.mp h5]
    have h9 : (x 1) ^ 2 ≤ 1 := by nlinarith [abs_le.mp h6]
    have h10 : (x 2) ^ 2 ≤ 1 := by nlinarith [abs_le.mp h7]
    nlinarith
  have h11 : 0 ≤ ‖x‖ := by positivity
  nlinarith

/-- Scalar projection of paper shading points onto a unit vector lies in `[-4, 4]`. -/
lemma scalarProjection_bounded
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Z : WZ1PaperTubeShading F} {v : Point3} (hv : ‖v‖ = 1)
    (E : Set ℝ) (hE : E ⊆ scalarProjection v Z.union) :
    E ⊆ Set.Icc (-4 : ℝ) 4 := by
  intro y hy
  rcases hE hy with ⟨x, hx, rfl⟩
  have h_norm_x : ‖x‖ ≤ 3 := paperShading_point_bounded hx
  have h_abs : |inner ℝ x v| ≤ ‖x‖ * ‖v‖ := abs_real_inner_le_norm x v
  have h_bound : |inner ℝ x v| ≤ 4 := by
    calc |inner ℝ x v|
        ≤ ‖x‖ * ‖v‖ := h_abs
      _ = ‖x‖ := by rw [hv]; ring
      _ ≤ 3 := h_norm_x
      _ ≤ 4 := by norm_num
  exact abs_le.mp h_bound

/-- Helper: `ENNReal.ofReal x / 10 = ENNReal.ofReal (x / 10)` for `x ≥ 0`. -/
lemma ofReal_div10 {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal x / 10 = ENNReal.ofReal (x / 10) := by
  have h1 : ENNReal.ofReal (x * (1 / 10 : ℝ)) =
      ENNReal.ofReal x * ENNReal.ofReal (1 / 10 : ℝ) :=
    ENNReal.ofReal_mul hx
  have h2 : x / 10 = x * (1 / 10 : ℝ) := by ring
  have h3 : ENNReal.ofReal (1 / 10 : ℝ) = (1 / 10 : ENNReal) := by
    simp
  have h4 : ENNReal.ofReal x / 10 = ENNReal.ofReal x * (1 / 10 : ENNReal) := by
    simp [div_eq_mul_inv]
    <;> rfl
  rw [h4, ← h3, ← h1, h2]

/-!
## Multi-scale iteration theorem
-/

/--
Pure WZ2 every-scale local grain construction.

Takes the one-scale geometric lemma and sticky-data provision as hypotheses,
and produces the every-scale local AD bound via the N-scale grid iteration.
-/
theorem pure_wz2_every_scale_local_grain
    (h_one_scale : PureWZ2OneScaleLocalGrainConclusion)
    (h_sticky_at : PureWZ2StickyAtScale)
    (h_bridge : PureWZ2PaperADBridgeStatement) :
    PureWZ2EveryScaleLocalGrainConclusion := by
  intro sigma outputLoss hsigma_pos hsigma_lt_one houtput_loss_pos

  -- Loss budget and grid parameters
  let midLoss : ℝ := min (outputLoss / 3) (1 / 3)
  have hmid_pos : 0 < midLoss := by
    apply lt_min <;> positivity <;> norm_num
  have hmid_le_output : midLoss ≤ outputLoss := by
    have h : midLoss ≤ outputLoss / 3 := min_le_left _ _
    linarith
  have hmid_le_third : midLoss ≤ 1 / 3 := min_le_right _ _
  have hmid_lt_half : midLoss < 1 / 2 := by linarith
  have hgap_pos : 0 < outputLoss - midLoss := by
    have h1 : midLoss ≤ outputLoss / 3 := min_le_left _ _
    linarith
  let gap2 : ℝ := outputLoss - 2 * midLoss
  have hgap2_pos : 0 < gap2 := by
    have h1 : midLoss ≤ outputLoss / 3 := min_le_left _ _
    linarith
  let N : ℕ :=
    max 9
      (Nat.ceil
          (max (sigma / (outputLoss - midLoss)) (1 / gap2)) +
        1)
  have hN_ge_9 : N ≥ 9 := Nat.le_max_left _ _
  have hsigma_over_N_lt : sigma / (N : ℝ) < outputLoss - midLoss := by
    set x : ℝ := max (sigma / (outputLoss - midLoss)) (1 / gap2) with hx_def
    have h1 : N ≥ Nat.ceil x + 1 := Nat.le_max_right _ _
    have h2 : (N : ℝ) ≥ (Nat.ceil x : ℝ) + 1 := by exact_mod_cast h1
    have h3 : (Nat.ceil x : ℝ) ≥ x := Nat.le_ceil x
    have h4 : (N : ℝ) > x := by linarith
    have h5 : sigma / (outputLoss - midLoss) ≤ x := le_max_left _ _
    have h6 : sigma / (outputLoss - midLoss) < (N : ℝ) := lt_of_le_of_lt h5 h4
    have h7 : 0 < outputLoss - midLoss := hgap_pos
    have h8 : (N : ℝ) * (outputLoss - midLoss) > sigma := by
      calc (N : ℝ) * (outputLoss - midLoss)
          > (sigma / (outputLoss - midLoss)) * (outputLoss - midLoss) := by gcongr
        _ = sigma := by field_simp [h7.ne']
    have h9 : 0 < (N : ℝ) := by positivity
    calc sigma / (N : ℝ)
        < ((N : ℝ) * (outputLoss - midLoss)) / (N : ℝ) := by gcongr
      _ = outputLoss - midLoss := by field_simp [h9.ne']
  have hone_over_N_lt : 1 / (N : ℝ) < gap2 := by
    set x : ℝ := max (sigma / (outputLoss - midLoss)) (1 / gap2) with hx_def
    have h1 : N ≥ Nat.ceil x + 1 := Nat.le_max_right _ _
    have h2 : (N : ℝ) ≥ (Nat.ceil x : ℝ) + 1 := by exact_mod_cast h1
    have h3 : (Nat.ceil x : ℝ) ≥ x := Nat.le_ceil x
    have h4 : (N : ℝ) > x := by linarith
    have h5 : 1 / gap2 ≤ x := le_max_right _ _
    have h6 : 1 / gap2 < (N : ℝ) := lt_of_le_of_lt h5 h4
    have h7 : 0 < gap2 := hgap2_pos
    have h8 : (N : ℝ) * gap2 > 1 := by
      calc (N : ℝ) * gap2 > (1 / gap2) * gap2 := by gcongr
        _ = 1 := by field_simp [h7.ne']
    have h9 : 0 < (N : ℝ) := by positivity
    calc 1 / (N : ℝ)
        < ((N : ℝ) * gap2) / (N : ℝ) := by gcongr
      _ = gap2 := by field_simp [h9.ne']

  -- Obtain one-scale and sticky parameters
  rcases h_one_scale sigma midLoss 0 hsigma_pos hsigma_lt_one hmid_pos with
    ⟨inputLoss_one, delta₀_one, hinput_one_pos, hinput_one_le_mid,
      hdelta₀_one_pos, hdelta₀_one_one, h_step_one⟩
  rcases h_sticky_at sigma midLoss hsigma_pos hsigma_lt_one hmid_pos with
    ⟨inputLoss_sticky, delta₀_sticky, hinput_sticky_pos, hinput_sticky_le_mid,
      hdelta₀_sticky_pos, hdelta₀_sticky_one, h_sticky_inner⟩

  let inputLoss : ℝ := min inputLoss_one inputLoss_sticky
  have hinput_pos : 0 < inputLoss := by positivity
  have hinput_le_one : inputLoss ≤ inputLoss_one := min_le_left _ _
  have hinput_le_sticky : inputLoss ≤ inputLoss_sticky := min_le_right _ _

  let delta₀ : ℝ := min delta₀_one delta₀_sticky
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_one : delta₀ ≤ 1 :=
    (min_le_left _ _).trans hdelta₀_one_one

  -- Grid setup
  let k_min : ℕ := Nat.ceil ((N : ℝ) * midLoss)
  let k_max : ℕ := Nat.floor ((N : ℝ) * (1 - midLoss))
  have h1m_pos : 0 < 1 - midLoss := by linarith
  have h_nonneg : 0 ≤ (N : ℝ) * (1 - midLoss) := by positivity
  have hk_min_lower : (N : ℝ) * midLoss ≤ (k_min : ℝ) := Nat.le_ceil _
  have hk_max_upper : (k_max : ℝ) ≤ (N : ℝ) * (1 - midLoss) := Nat.floor_le h_nonneg
  have hk_max_lower : (k_max : ℝ) ≥ (N : ℝ) * (1 - midLoss) - 1 := by
    have h2 : (N : ℝ) * (1 - midLoss) < (k_max : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hk_min_le_k_max : k_min ≤ k_max := by
    have h1 : (k_min : ℝ) < (N : ℝ) * midLoss + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (N : ℝ) * (1 - midLoss) < (k_max : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : (N : ℝ) * midLoss + 1 ≤ (N : ℝ) * (1 - midLoss) := by
      have h4 : (N : ℝ) * (1 - 2 * midLoss) ≥ 1 := by
        have h5 : (N : ℝ) ≥ 9 := by exact_mod_cast hN_ge_9
        nlinarith
      linarith
    have h6 : (k_min : ℝ) < (k_max : ℝ) + 1 := by linarith
    have h7 : k_min < k_max + 1 := by exact_mod_cast h6
    omega
  let valid_ks : List ℕ := List.range' k_min (k_max - k_min + 1)
  have h_valid_ks_mem : ∀ k : ℕ, k ∈ valid_ks ↔ k_min ≤ k ∧ k ≤ k_max := by
    intro k
    simp only [valid_ks, List.mem_range']
    constructor
    · rintro ⟨j, hj_lt, rfl⟩ <;> constructor <;> omega
    · rintro ⟨h1, h2⟩
      refine ⟨k - k_min, by omega, by omega⟩
  let rho_val (delta : ℝ) (k : ℕ) : ℝ :=
    Real.rpow delta (1 - (k : ℝ) / (N : ℝ))
  have hrho_val_pos : ∀ delta : ℝ, 0 < delta → ∀ k : ℕ, 0 < rho_val delta k := by
    intro delta hdelta k
    apply Real.rpow_pos_of_pos hdelta
  have hrho_val_admissible :
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
        ∀ k ∈ valid_ks, delta ≤ rho_val delta k ∧ rho_val delta k ≤ 1 := by
    intro delta hdelta hdelta_one k hk
    have h1 : k_min ≤ k ∧ k ≤ k_max := (h_valid_ks_mem k).mp hk
    have h2 : (k : ℝ) / (N : ℝ) ≥ midLoss := by
      have h3 : (k_min : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1.1
      have h4 : (N : ℝ) * midLoss ≤ (k : ℝ) := hk_min_lower.trans h3
      have h5 : 0 < (N : ℝ) := by positivity
      calc (k : ℝ) / (N : ℝ) ≥ ((N : ℝ) * midLoss) / (N : ℝ) := by gcongr
        _ = midLoss := by field_simp [h5.ne']
    have h6 : (k : ℝ) / (N : ℝ) ≤ 1 - midLoss := by
      have h7 : (k : ℝ) ≤ (k_max : ℝ) := by exact_mod_cast h1.2
      have h8 : (k : ℝ) ≤ (N : ℝ) * (1 - midLoss) := h7.trans hk_max_upper
      have h9 : 0 < (N : ℝ) := by positivity
      calc (k : ℝ) / (N : ℝ) ≤ ((N : ℝ) * (1 - midLoss)) / (N : ℝ) := by gcongr
        _ = 1 - midLoss := by field_simp [h9.ne']
    have h10 : 0 ≤ 1 - (k : ℝ) / (N : ℝ) := by linarith
    have h11 : 1 - (k : ℝ) / (N : ℝ) ≤ 1 := by linarith
    have h12 : delta ≤ Real.rpow delta (1 - (k : ℝ) / (N : ℝ)) := by
      have h13 : Real.rpow delta 1 ≤ Real.rpow delta (1 - (k : ℝ) / (N : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one h11
      simpa using h13
    have h15 : Real.rpow delta (1 - (k : ℝ) / (N : ℝ)) ≤ 1 := by
      have h16 : Real.rpow delta (1 - (k : ℝ) / (N : ℝ)) ≤ Real.rpow delta 0 :=
        Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one h10
      simpa using h16
    exact ⟨h12, h15⟩

  -- Accumulation predicate
  let P : List ℕ → Prop := fun ks =>
    ∃ (loss : ℝ) (delta₀_P : ℝ),
      0 < loss ∧ loss ≤ midLoss ∧
      0 < delta₀_P ∧ delta₀_P ≤ 1 ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀_P →
        ∀ (F : Kakeya.Streamlined.TubeFamily delta)
          (Y : WZ1PaperTubeShading F),
          WZ2PaperCroppedIsExtremal sigma loss F Y →
          WZ2PaperConvexWolffBound F (Kakeya.realRpowENN delta (-loss)) →
          ∀ (planeMap : {point : Point3 // point ∈ Y.union} → Point3),
            LipschitzWith 1 planeMap →
            (∀ p, ‖planeMap p‖ = 1) →
            (∀ i p hp,
              |inner ℝ (F.tube i).direction
                (planeMap ⟨p, ⟨i, hp⟩⟩)| ≤ delta) →
            ∃ (Z : WZ1PaperTubeShading F) (hsub : PaperIsSubshading' Z Y),
              WZ2PaperCroppedIsExtremal sigma midLoss F Z ∧
              WZ2PaperConvexWolffBound F (Kakeya.realRpowENN delta (-midLoss)) ∧
              ∀ k ∈ ks, ∀ (p : Point3) (hp : p ∈ Z.union),
                IsADSet1
                  (scalarProjection
                    (planeMap ⟨p, hsub.union hp⟩)
                    (Z.union ∩ Metric.closedBall p (Real.sqrt (rho_val delta k))))
                  (rho_val delta k) (1 - sigma)
                  (Kakeya.realRpowENN delta (-midLoss))

  have h_base : P [] := by
    refine ⟨midLoss, 1, hmid_pos, le_refl midLoss, by positivity, by norm_num, ?_⟩
    intro delta hdelta_pos hdelta_one F Y hY_extremal hY_cwa planeMap hlip hunit hinc
    refine ⟨Y, (fun i => rfl.subset), ?_, ?_, ?_⟩
    · exact hY_extremal
    · exact hY_cwa
    · intro k hk
      simp only [List.mem_nil_iff] at hk

  have h_step :
      ∀ (k : ℕ), k ∈ valid_ks → ∀ (ks : List ℕ), P ks → P (k :: ks) := by
    intro k hk ks hPks
    rcases hPks with
      ⟨loss_ks, delta₀_ks, hloss_ks_pos, hloss_ks_le_mid,
        hdelta₀_ks_pos, hdelta₀_ks_one, hPks_inner⟩
    rcases h_one_scale sigma loss_ks 0 hsigma_pos hsigma_lt_one hloss_ks_pos with
      ⟨inputLoss_new, delta₀_new, hinput_new_pos, hinput_new_le_ks,
        hdelta₀_new_pos, hdelta₀_new_one, h_step_new⟩
    rcases h_sticky_at sigma loss_ks hsigma_pos hsigma_lt_one hloss_ks_pos with
      ⟨inputLoss_sticky, delta₀_sticky, hinput_sticky_pos, hinput_sticky_le_ks,
        hdelta₀_sticky_pos, hdelta₀_sticky_one, h_sticky_inner⟩
    let inputLoss' : ℝ := min inputLoss_new inputLoss_sticky
    have hinput'_pos : 0 < inputLoss' := by positivity
    have hinput'_le_ks : inputLoss' ≤ loss_ks := by
      exact le_trans (min_le_left _ _) hinput_new_le_ks
    let delta₀' : ℝ := min delta₀_new (min delta₀_sticky (min delta₀_ks delta₀))
    have hdelta₀'_pos : 0 < delta₀' := by positivity
    have hdelta₀'_one : delta₀' ≤ 1 :=
      (min_le_left _ _).trans hdelta₀_new_one
    refine
      ⟨inputLoss', delta₀', hinput'_pos,
        hinput'_le_ks.trans hloss_ks_le_mid,
        hdelta₀'_pos, hdelta₀'_one, ?_⟩
    intro delta hdelta_pos hdelta_le F Y hY_extremal hY_cwa planeMap hlip hunit hinc
    let rho_k : ℝ := rho_val delta k
    have hrho_k_adm : delta ≤ rho_k ∧ rho_k ≤ 1 :=
      hrho_val_admissible delta hdelta_pos
        (hdelta_le.trans hdelta₀'_one) k hk
    -- Weaken extremal/CWA from inputLoss' to inputLoss_new and inputLoss_sticky
    have hinput'_le_new : inputLoss' ≤ inputLoss_new := min_le_left _ _
    have hinput'_le_sticky : inputLoss' ≤ inputLoss_sticky := min_le_right _ _
    have hY_ext_new : WZ2PaperCroppedIsExtremal sigma inputLoss_new F Y :=
      hY_extremal.mono_loss hinput'_le_new
    have hY_ext_sticky : WZ2PaperCroppedIsExtremal sigma inputLoss_sticky F Y :=
      hY_extremal.mono_loss hinput'_le_sticky
    have hrpow_new : Kakeya.realRpowENN delta (-inputLoss') ≤
        Kakeya.realRpowENN delta (-inputLoss_new) := by
      simp only [Kakeya.realRpowENN]
      apply ENNReal.ofReal_mono
      have h : -inputLoss' ≥ -inputLoss_new := by linarith
      exact Real.rpow_le_rpow_of_exponent_ge
        hdelta_pos (hdelta_le.trans hdelta₀'_one) h
    have hY_cwa_new : WZ2PaperConvexWolffBound F
        (Kakeya.realRpowENN delta (-inputLoss_new)) := by
      intro convexSet hconv
      have h := hY_cwa convexSet hconv
      have h_mul : (Kakeya.realRpowENN delta (-inputLoss')) * volume convexSet * F.enncard ≤
          (Kakeya.realRpowENN delta (-inputLoss_new)) * volume convexSet * F.enncard := by
        gcongr
      exact h.trans h_mul
    have hrpow_sticky : Kakeya.realRpowENN delta (-inputLoss') ≤
        Kakeya.realRpowENN delta (-inputLoss_sticky) := by
      simp only [Kakeya.realRpowENN]
      apply ENNReal.ofReal_mono
      have h : -inputLoss' ≥ -inputLoss_sticky := by linarith
      exact Real.rpow_le_rpow_of_exponent_ge
        hdelta_pos (hdelta_le.trans hdelta₀'_one) h
    have hY_cwa_sticky : WZ2PaperConvexWolffBound F
        (Kakeya.realRpowENN delta (-inputLoss_sticky)) := by
      intro convexSet hconv
      have h := hY_cwa convexSet hconv
      have h_mul : (Kakeya.realRpowENN delta (-inputLoss')) * volume convexSet * F.enncard ≤
          (Kakeya.realRpowENN delta (-inputLoss_sticky)) * volume convexSet * F.enncard := by
        gcongr
      exact h.trans h_mul
    -- Construct universal sticky provision, then restrict to A2's needed range
    let h_sticky_universal : ∀ (rho' : WZ2PaperRequestedScale delta) (logExponent : ℕ),
        Nonempty (PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := loss_ks)
          (sourceShading := Y) rho' logExponent) :=
      h_sticky_inner delta hdelta_pos
        (hdelta_le.trans (min_le_right _ _ |>.trans (min_le_left _ _)))
        F Y hY_ext_sticky hY_cwa_sticky
    let h_sticky_provision :
        ∀ (rho' : WZ2PaperRequestedScale delta),
          Real.rpow delta (1 - loss_ks) ≤ rho'.1 →
          rho'.1 ≤ Real.rpow delta loss_ks →
          Nonempty (PureWZ2PropStickyData
            (sigma := sigma) (outputLoss := loss_ks)
            (sourceShading := Y) rho' 0) :=
      fun rho' _ _ => h_sticky_universal rho' 0
    -- Apply one-scale lemma with L=1 and sticky provision
    have h1_le_rpow : (1 : ℝ) ≤ Real.rpow delta (-inputLoss_new) := by
      have h : Real.rpow delta (-inputLoss_new) ≥ Real.rpow delta 0 :=
        Real.rpow_le_rpow_of_exponent_ge hdelta_pos
          (hdelta_le.trans hdelta₀'_one) (by linarith)
      simpa using h
    have h_one_at_k : Nonempty (PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := loss_ks)
        (rho := rho_k) (Y := Y) planeMap) :=
      h_step_new delta hdelta_pos
        (hdelta_le.trans (min_le_left _ _))
        F Y hY_ext_new hY_cwa_new
        (1 : NNReal) h1_le_rpow
        planeMap hlip hunit hinc
        h_sticky_provision
        rho_k hrho_k_adm.1 hrho_k_adm.2
    rcases h_one_at_k with ⟨data_k⟩
    let Z₁ := data_k.shading
    have hZ₁_sub : PaperIsSubshading' Z₁ Y := data_k.subshading
    have hZ₁_extremal : WZ2PaperCroppedIsExtremal sigma loss_ks F Z₁ :=
      data_k.extremal
    have hZ₁_cwa : WZ2PaperConvexWolffBound F
        (Kakeya.realRpowENN delta (-loss_ks)) := data_k.cwa
    let planeMap₁ := restrictPlaneMap hZ₁_sub planeMap
    have hplane₁_lip : LipschitzWith 1 planeMap₁ :=
      restrictPlaneMap_lipschitz hZ₁_sub planeMap hlip
    have hplane₁_unit : ∀ p, ‖planeMap₁ p‖ = 1 :=
      restrictPlaneMap_unit hZ₁_sub planeMap hunit
    have hplane₁_inc : ∀ i p hp,
        |inner ℝ (F.tube i).direction (planeMap₁ ⟨p, ⟨i, hp⟩⟩)| ≤ delta :=
      restrictPlaneMap_incidence hZ₁_sub planeMap hinc
    -- Apply previous accumulation to Z₁
    rcases hPks_inner delta hdelta_pos
        (hdelta_le.trans (min_le_right _ _ |>.trans (min_le_right _ _ |>.trans (min_le_left _ _))))
        F Z₁ hZ₁_extremal hZ₁_cwa planeMap₁ hplane₁_lip hplane₁_unit hplane₁_inc with
      ⟨Z₂, hZ₂_sub, hZ₂_extremal, hZ₂_cwa, hAD_ks⟩
    have hZ₂_sub_Y : PaperIsSubshading' Z₂ Y := by
      intro i p hp
      have h1 : p ∈ Z₁.carrier i := hZ₂_sub i hp
      exact hZ₁_sub i h1
    -- AD at scale k: transfer from Z₁ to Z₂
    have hAD_k : ∀ (p : Point3) (hp : p ∈ Z₂.union),
        IsADSet1
          (scalarProjection
            (planeMap ⟨p, hZ₂_sub_Y.union hp⟩)
            (Z₂.union ∩ Metric.closedBall p (Real.sqrt rho_k)))
          rho_k (1 - sigma)
          (Kakeya.realRpowENN delta (-midLoss)) := by
      intro p hp
      have hZ₂_sub_Z₁ : Z₂.union ⊆ Z₁.union := hZ₂_sub.union
      have hAD_Z₁ := data_k.local_ad p (hZ₂_sub_Z₁ hp)
      have h_plane_eq : planeMap ⟨p, hZ₁_sub.union (hZ₂_sub_Z₁ hp)⟩ =
          planeMap ⟨p, hZ₂_sub_Y.union hp⟩ := by rfl
      have h_inter_sub :
          Z₂.union ∩ Metric.closedBall p (Real.sqrt rho_k) ⊆
          Z₁.union ∩ Metric.closedBall p (Real.sqrt rho_k) :=
        Set.inter_subset_inter_left _ hZ₂_sub_Z₁
      have hset_sub :
          scalarProjection (planeMap ⟨p, hZ₂_sub_Y.union hp⟩)
            (Z₂.union ∩ Metric.closedBall p (Real.sqrt rho_k)) ⊆
          scalarProjection (planeMap ⟨p, hZ₁_sub.union (hZ₂_sub_Z₁ hp)⟩)
            (Z₁.union ∩ Metric.closedBall p (Real.sqrt rho_k)) := by
        rintro y ⟨x, hx, rfl⟩
        exact ⟨x, h_inter_sub hx, rfl⟩
      rw [h_plane_eq] at hAD_Z₁
      have h_const : Kakeya.realRpowENN delta (-loss_ks) ≤
          Kakeya.realRpowENN delta (-midLoss) := by
        simp only [Kakeya.realRpowENN]
        apply ENNReal.ofReal_mono
        exact Real.rpow_le_rpow_of_exponent_ge
          hdelta_pos (hdelta_le.trans hdelta₀'_one) (by linarith)
      exact (hAD_Z₁.mono hset_sub).mono_constant h_const
    have hAD_all :
        ∀ j ∈ k :: ks, ∀ (p : Point3) (hp : p ∈ Z₂.union),
          IsADSet1
            (scalarProjection
              (planeMap ⟨p, hZ₂_sub_Y.union hp⟩)
              (Z₂.union ∩ Metric.closedBall p (Real.sqrt (rho_val delta j))))
            (rho_val delta j) (1 - sigma)
            (Kakeya.realRpowENN delta (-midLoss)) := by
      intro j hj p hp
      rcases List.mem_cons.mp hj with (rfl | hj)
      · exact hAD_k p hp
      · exact hAD_ks j hj p hp
    exact ⟨Z₂, hZ₂_sub_Y, hZ₂_extremal, hZ₂_cwa, hAD_all⟩

  have h_general :
      ∀ (l : List ℕ), (∀ x ∈ l, x ∈ valid_ks) → P l := by
    intro l
    induction l with
    | nil => intro _; exact h_base
    | cons k ks ih =>
        intro hmem
        have hk : k ∈ valid_ks := hmem k (by simp)
        have hrest : ∀ x ∈ ks, x ∈ valid_ks := fun x hx => hmem x (by simp [hx])
        exact h_step k hk ks (ih hrest)

  rcases h_general valid_ks (fun x hx => hx) with
    ⟨loss, delta₀_P, hloss_pos, hloss_le_mid,
      hdelta₀_P_pos, hdelta₀_P_one, h_main_inner⟩

  -- Epsilon absorption margin
  let ε : ℝ := outputLoss - 2 * midLoss - 1 / (N : ℝ)
  have hε_pos : 0 < ε := by
    dsimp only [ε, gap2] at *
    linarith

  refine
    ⟨loss, min delta₀_P ((10 : ℝ) ^ (-2 / ε)),
      hloss_pos, hloss_le_mid.trans hmid_le_output,
      by positivity,
      (min_le_left _ _).trans hdelta₀_P_one, ?_⟩
  intro delta hdelta_pos hdelta_le F Y hY_extremal hY_cwa planeMap hlip hunit hinc

  have hdelta_small : delta ≤ (10 : ℝ) ^ (-2 / ε) :=
    hdelta_le.trans (min_le_right _ _)
  have hdelta_one : delta ≤ 1 :=
    (hdelta_le.trans (min_le_left _ _)).trans hdelta₀_P_one

  -- Epsilon absorption: 100 ≤ δ^(-ε) since δ ≤ 10^(-2/ε)
  have h100_le_delta_neg_eps : (100 : ℝ) ≤ Real.rpow delta (-ε) := by
    have h_eps_pos : 0 < ε := hε_pos
    have h_base_pos : (0 : ℝ) ≤ delta := by linarith
    have h1 : Real.rpow delta ε ≤ Real.rpow ((10 : ℝ) ^ (-2 / ε)) ε :=
      Real.rpow_le_rpow h_base_pos hdelta_small (by linarith)
    have h2 : Real.rpow ((10 : ℝ) ^ (-2 / ε)) ε = 1 / 100 := by
      have h_pos10 : (0 : ℝ) ≤ (10 : ℝ) := by norm_num
      have h3 : Real.rpow ((10 : ℝ) ^ (-2 / ε)) ε =
          Real.rpow (10 : ℝ) ((-2 / ε) * ε) := by
        exact (Real.rpow_mul (x := (10 : ℝ)) h_pos10 (-2 / ε) ε).symm
      rw [h3]
      have h4 : (-2 / ε) * ε = -2 := by
        field_simp [h_eps_pos.ne'] <;> ring
      rw [h4] <;> norm_num
    have h3 : Real.rpow delta ε ≤ 1 / 100 := h1.trans (by rw [h2])
    have h4 : Real.rpow delta (-ε) = (Real.rpow delta ε)⁻¹ :=
      Real.rpow_neg hdelta_pos.le ε
    have h5 : 0 < Real.rpow delta ε := Real.rpow_pos_of_pos hdelta_pos ε
    have h6 : (Real.rpow delta ε)⁻¹ ≥ 100 := by
      have h7 : (Real.rpow delta ε)⁻¹ ≥ (1 / 100 : ℝ)⁻¹ := by gcongr
      have h8 : (1 / 100 : ℝ)⁻¹ = 100 := by norm_num
      rw [h8] at h7
      exact h7
    rw [h4]
    exact h6

  have h_absorb_interp :
      (100 : ℝ) * Real.rpow delta (-2 * midLoss - 1 / (N : ℝ)) ≤
      Real.rpow delta (-outputLoss) := by
    have h2 : Real.rpow delta (-ε) * Real.rpow delta (-2 * midLoss - 1 / (N : ℝ)) =
        Real.rpow delta (-outputLoss) := by
      have h_add := Real.rpow_add hdelta_pos (-ε) (-2 * midLoss - 1 / (N : ℝ))
      have h3 : (-ε) + (-2 * midLoss - 1 / (N : ℝ)) = -outputLoss := by
        dsimp only [ε] <;> ring
      rw [h3] at h_add
      exact h_add.symm
    have h4 : (100 : ℝ) * Real.rpow delta (-2 * midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-ε) * Real.rpow delta (-2 * midLoss - 1 / (N : ℝ)) := by
      have h_pos : 0 ≤ Real.rpow delta (-2 * midLoss - 1 / (N : ℝ)) :=
        (Real.rpow_pos_of_pos hdelta_pos _).le
      exact mul_le_mul_of_nonneg_right h100_le_delta_neg_eps h_pos
    rw [h2] at h4
    exact h4

  have h_absorb_trivial :
      (100 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) ≤
      Real.rpow delta (-outputLoss) := by
    have h2 : Real.rpow delta (-midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-2 * midLoss - 1 / (N : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one
      linarith
    have h3 : (100 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) ≤
        (100 : ℝ) * Real.rpow delta (-2 * midLoss - 1 / (N : ℝ)) := by gcongr
    exact h3.trans h_absorb_interp

  rcases h_main_inner delta hdelta_pos
      (hdelta_le.trans (min_le_left _ _))
      F Y hY_extremal hY_cwa planeMap hlip hunit hinc with
    ⟨Z, hZ_sub, hZ_extremal, hZ_cwa, hAD_finite⟩

  have hZ_union_sub_Y : Z.union ⊆ Y.union := hZ_sub.union

  let planeMap_Z := restrictPlaneMap hZ_sub planeMap

  -- Final local AD for every rho ∈ [delta, 1], with constant C/10 for bridge conversion
  have h_local_ad_isad :
      ∀ (rho : ℝ), delta ≤ rho → rho ≤ 1 →
        ∀ (p : Point3) (hp : p ∈ Z.union),
          IsADSet1
            (scalarProjection (planeMap_Z ⟨p, hp⟩)
              (Z.union ∩ Metric.closedBall p (Real.sqrt rho)))
            rho (1 - sigma)
            (Kakeya.realRpowENN delta (-outputLoss) / 10) := by
    intro rho hdelta_le_rho hrho_le_one p hp
    let E_rho :=
      scalarProjection (planeMap_Z ⟨p, hp⟩)
        (Z.union ∩ Metric.closedBall p (Real.sqrt rho))
    have hE_sub : E_rho ⊆ scalarProjection (planeMap_Z ⟨p, hp⟩) Z.union := by
      rintro y ⟨x, hx, rfl⟩
      exact ⟨x, hx.1, rfl⟩
    have hE_bdd : E_rho ⊆ Set.Icc (-4 : ℝ) 4 := by
      let v := planeMap_Z ⟨p, hp⟩
      have hv : ‖v‖ = 1 := restrictPlaneMap_unit hZ_sub planeMap hunit ⟨p, hp⟩
      exact scalarProjection_bounded hv E_rho hE_sub
    by_cases h_case : rho ≤ rho_val delta k_max
    · -- Interpolation from nearest grid scale
      let S : Finset ℕ :=
        (Finset.Icc k_min k_max).filter (fun k => rho ≤ rho_val delta k)
      have hS_nonempty : S.Nonempty := by
        refine ⟨k_max, Finset.mem_filter.mpr ⟨?_, h_case⟩⟩
        simp [Finset.mem_Icc, hk_min_le_k_max]
      let k : ℕ := S.min' hS_nonempty
      have hk_in : k ∈ S := Finset.min'_mem S hS_nonempty
      have hk_range : k_min ≤ k ∧ k ≤ k_max := by
        simpa [Finset.mem_Icc] using (Finset.mem_filter.mp hk_in).1
      have hrho_le_k : rho ≤ rho_val delta k :=
        (Finset.mem_filter.mp hk_in).2
      have hk_valid : k ∈ valid_ks :=
        (h_valid_ks_mem k).mpr hk_range
      have hsqrt_mono : Real.sqrt rho ≤ Real.sqrt (rho_val delta k) :=
        Real.sqrt_le_sqrt hrho_le_k
      have hball_sub :
          Metric.closedBall p (Real.sqrt rho) ⊆
          Metric.closedBall p (Real.sqrt (rho_val delta k)) := by
        intro x hx
        exact hx.trans hsqrt_mono
      have hE_sub : E_rho ⊆
          scalarProjection (planeMap_Z ⟨p, hp⟩)
            (Z.union ∩ Metric.closedBall p (Real.sqrt (rho_val delta k))) := by
        rintro y ⟨x, hx, rfl⟩
        exact ⟨x, ⟨hx.1, hball_sub hx.2⟩, rfl⟩
      have hAD_sub :=
        (hAD_finite k hk_valid p hp).mono hE_sub
      have hrho_k_one : rho_val delta k ≤ 1 :=
        (hrho_val_admissible delta hdelta_pos hdelta_one k hk_valid).2
      have hAD_weaken :=
        hAD_sub.weaken_scale (by linarith) hrho_le_k hrho_k_one
      -- Factor bound: rho_k / rho ≤ δ^(-midLoss - 1/N)
      have h_rpow_div : ∀ (a b : ℝ), Real.rpow delta a / Real.rpow delta b = Real.rpow delta (a - b) := by
        intro a b
        have h_pos_b : 0 < Real.rpow delta b := Real.rpow_pos_of_pos hdelta_pos b
        have h_eq : Real.rpow delta (a - b) = Real.rpow delta a / Real.rpow delta b :=
          Real.rpow_sub hdelta_pos a b
        exact h_eq.symm
      have h_kmin_bound : (k_min : ℝ) / (N : ℝ) ≤ midLoss + 1 / (N : ℝ) := by
        have hN_pos : 0 < (N : ℝ) := by positivity
        have h4 : (k_min : ℝ) < (N : ℝ) * midLoss + 1 := Nat.ceil_lt_add_one (by positivity)
        have h5 : (k_min : ℝ) ≤ (N : ℝ) * midLoss + 1 := by linarith
        calc (k_min : ℝ) / (N : ℝ)
            ≤ ((N : ℝ) * midLoss + 1) / (N : ℝ) := by gcongr
          _ = midLoss + 1 / (N : ℝ) := by field_simp [hN_pos.ne'] <;> ring
      have h_factor_bound : (10 : ℝ) * rho_val delta k / rho ≤
          (10 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) := by
        by_cases h_k_min : k = k_min
        · -- Case k = k_min
          have h_rho_pos : 0 < rho := by linarith
          have h2 : rho_val delta k_min / rho ≤ rho_val delta k_min / delta := by
            apply div_le_div_of_nonneg_left
            · exact (hrho_val_pos delta hdelta_pos k_min).le
            · linarith
            · linarith
          have h3 : rho_val delta k_min / delta = Real.rpow delta (-(k_min : ℝ) / (N : ℝ)) := by
            dsimp only [rho_val]
            have h4 : Real.rpow delta (1 - (k_min : ℝ) / (N : ℝ)) / Real.rpow delta 1 =
                Real.rpow delta ((1 - (k_min : ℝ) / (N : ℝ)) - 1) := by
              rw [h_rpow_div]
            have h5 : Real.rpow delta 1 = delta := Real.rpow_one delta
            rw [h5] at h4
            have h6 : (1 - (k_min : ℝ) / (N : ℝ)) - 1 = -(k_min : ℝ) / (N : ℝ) := by ring
            rw [h6] at h4
            exact h4
          have h1 : rho_val delta k / rho ≤ Real.rpow delta (-(k_min : ℝ) / (N : ℝ)) := by
            rw [h_k_min]
            exact h2.trans h3.le
          have h5 : -(k_min : ℝ) / (N : ℝ) ≥ -midLoss - 1 / (N : ℝ) := by
            have h6 : (k_min : ℝ) / (N : ℝ) ≤ midLoss + 1 / (N : ℝ) := h_kmin_bound
            have h7 : -((k_min : ℝ) / (N : ℝ)) ≥ -(midLoss + 1 / (N : ℝ)) := by
              exact neg_le_neg h6
            have h8 : -((k_min : ℝ) / (N : ℝ)) = -(k_min : ℝ) / (N : ℝ) := by ring
            have h9 : -(midLoss + 1 / (N : ℝ)) = -midLoss - 1 / (N : ℝ) := by ring
            rw [h8, h9] at h7
            exact h7
          have h7 : Real.rpow delta (-(k_min : ℝ) / (N : ℝ)) ≤ Real.rpow delta (-midLoss - 1 / (N : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one h5
          calc (10 : ℝ) * rho_val delta k / rho
              = (10 : ℝ) * (rho_val delta k / rho) := by ring
            _ ≤ (10 : ℝ) * Real.rpow delta (-(k_min : ℝ) / (N : ℝ)) := by gcongr
            _ ≤ (10 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) := by gcongr
        · -- Case k > k_min
          have h_k_gt_min : k > k_min := by omega
          have h_k1_not_in_S : k - 1 ∉ S := by
            intro h
            have := Finset.min'_le S (k - 1) h
            omega
          have h_k1_in_Icc : k - 1 ∈ Finset.Icc k_min k_max := by
            simp [Finset.mem_Icc] <;> omega
          have h_rho_gt_k1 : rho > rho_val delta (k - 1) := by
            have h12 : ¬ rho ≤ rho_val delta (k - 1) := by
              intro h13
              exact h_k1_not_in_S (Finset.mem_filter.mpr ⟨h_k1_in_Icc, h13⟩)
            exact not_le.mp h12
          have h_rho_k1_pos : 0 < rho_val delta (k - 1) := hrho_val_pos delta hdelta_pos (k - 1)
          have h2 : rho_val delta k / rho < rho_val delta k / rho_val delta (k - 1) := by
            have h_pos_k : 0 < rho_val delta k := hrho_val_pos delta hdelta_pos k
            have h : rho_val delta (k - 1) < rho := h_rho_gt_k1
            have h1 : 1 / rho < 1 / rho_val delta (k - 1) := one_div_lt_one_div_of_lt h_rho_k1_pos h
            have h2 : rho_val delta k * (1 / rho) < rho_val delta k * (1 / rho_val delta (k - 1)) :=
              mul_lt_mul_of_pos_left h1 h_pos_k
            have h3 : rho_val delta k / rho = rho_val delta k * (1 / rho) := by ring
            have h4 : rho_val delta k / rho_val delta (k - 1) = rho_val delta k * (1 / rho_val delta (k - 1)) := by ring
            rw [h3, h4]
            exact h2
          have h3 : rho_val delta k / rho_val delta (k - 1) = Real.rpow delta (-(1 / (N : ℝ))) := by
            dsimp only [rho_val]
            have h41 : (1 - (k : ℝ) / (N : ℝ)) - (1 - ((k - 1 : ℕ) : ℝ) / (N : ℝ)) = -(1 / (N : ℝ)) := by
              simp [Nat.cast_sub (show k ≥ 1 by omega)] <;> field_simp <;> ring
            have h42 : Real.rpow delta (1 - (k : ℝ) / (N : ℝ)) / Real.rpow delta (1 - ((k - 1 : ℕ) : ℝ) / (N : ℝ)) =
                Real.rpow delta ((1 - (k : ℝ) / (N : ℝ)) - (1 - ((k - 1 : ℕ) : ℝ) / (N : ℝ))) := by
              rw [h_rpow_div]
            rw [h42, h41]
          have h1 : rho_val delta k / rho ≤ Real.rpow delta (-(1 / (N : ℝ))) := by
            have h1a : rho_val delta k / rho < rho_val delta k / rho_val delta (k - 1) := h2
            rw [h3] at h1a
            exact h1a.le
          have h8 : -(1 / (N : ℝ)) ≥ -midLoss - 1 / (N : ℝ) := by
            have h9 : 0 ≤ midLoss := by positivity
            linarith
          have h9 : Real.rpow delta (-(1 / (N : ℝ))) ≤ Real.rpow delta (-midLoss - 1 / (N : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one h8
          calc (10 : ℝ) * rho_val delta k / rho
              = (10 : ℝ) * (rho_val delta k / rho) := by ring
            _ ≤ (10 : ℝ) * Real.rpow delta (-(1 / (N : ℝ))) := by gcongr <;> exact h1
            _ ≤ (10 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) := by gcongr
      have h_rpow_add : Real.rpow delta (-midLoss) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) =
          Real.rpow delta (-2 * midLoss - 1 / (N : ℝ)) := by
        have h : Real.rpow delta ((-midLoss) + (-midLoss - 1 / (N : ℝ))) =
            Real.rpow delta (-midLoss) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) :=
          Real.rpow_add hdelta_pos (-midLoss) (-midLoss - 1 / (N : ℝ))
        have h9 : (-midLoss) + (-midLoss - 1 / (N : ℝ)) = -2 * midLoss - 1 / (N : ℝ) := by ring
        rw [h9] at h
        exact h.symm
      have h_factor2 : (10 : ℝ) * rho_val delta k / rho ≤ (10 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) :=
        h_factor_bound
      have h_rho_pos : 0 < rho := by linarith
      have h_rho_val_pos : 0 < rho_val delta k := hrho_val_pos delta hdelta_pos k
      have h_nonneg2 : 0 ≤ (10 : ℝ) * rho_val delta k / rho := by
        have h1 : 0 ≤ (10 : ℝ) * rho_val delta k := by
          exact mul_nonneg (by norm_num) h_rho_val_pos.le
        have h3 : 0 ≤ rho := h_rho_pos.le
        exact div_nonneg h1 h3
      have h_pos_rpow : 0 ≤ Real.rpow delta (-midLoss) :=
        (Real.rpow_pos_of_pos hdelta_pos _).le
      have h_mul_real : Real.rpow delta (-midLoss) * ((10 : ℝ) * rho_val delta k / rho) ≤
          Real.rpow delta (-outputLoss) / 10 := by
        have h_div10 : (100 : ℝ) * Real.rpow delta (-2 * midLoss - 1 / (N : ℝ)) ≤ Real.rpow delta (-outputLoss) :=
          h_absorb_interp
        have h_half : (10 : ℝ) * Real.rpow delta (-2 * midLoss - 1 / (N : ℝ)) ≤ Real.rpow delta (-outputLoss) / 10 := by
          have h : (100 : ℝ) * Real.rpow delta (-2 * midLoss - 1 / (N : ℝ)) ≤ Real.rpow delta (-outputLoss) := h_div10
          have h' : (10 : ℝ) * Real.rpow delta (-2 * midLoss - 1 / (N : ℝ)) = ((100 : ℝ) * Real.rpow delta (-2 * midLoss - 1 / (N : ℝ))) / 10 := by ring
          rw [h']
          exact div_le_div_of_nonneg_right h (by norm_num)
        calc Real.rpow delta (-midLoss) * ((10 : ℝ) * rho_val delta k / rho)
            ≤ Real.rpow delta (-midLoss) * ((10 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ))) := by
              exact mul_le_mul_of_nonneg_left h_factor2 h_pos_rpow
          _ = (10 : ℝ) * (Real.rpow delta (-midLoss) * Real.rpow delta (-midLoss - 1 / (N : ℝ))) := by ring
          _ = (10 : ℝ) * Real.rpow delta (-2 * midLoss - 1 / (N : ℝ)) := by rw [h_rpow_add] <;> ring
          _ ≤ Real.rpow delta (-outputLoss) / 10 := h_half
      have h_nonneg1 : 0 ≤ Real.rpow delta (-midLoss) := h_pos_rpow
      have h_nonneg : 0 ≤ Real.rpow delta (-midLoss) * ((10 : ℝ) * rho_val delta k / rho) :=
        mul_nonneg h_nonneg1 h_nonneg2
      have h_const : Kakeya.realRpowENN delta (-midLoss) *
          ENNReal.ofReal ((10 : ℝ) * rho_val delta k / rho) ≤
          Kakeya.realRpowENN delta (-outputLoss) / 10 := by
        simp only [Kakeya.realRpowENN]
        have h10 : ENNReal.ofReal (Real.rpow delta (-midLoss)) * ENNReal.ofReal ((10 : ℝ) * rho_val delta k / rho) =
            ENNReal.ofReal (Real.rpow delta (-midLoss) * ((10 : ℝ) * rho_val delta k / rho)) := by
          rw [← ENNReal.ofReal_mul h_nonneg1]
        rw [h10]
        have h11 : ENNReal.ofReal (Real.rpow delta (-outputLoss) / 10) =
            ENNReal.ofReal (Real.rpow delta (-outputLoss)) / 10 :=
          (ofReal_div10 (Real.rpow_nonneg hdelta_pos.le _)).symm
        rw [← h11]
        exact ENNReal.ofReal_le_ofReal h_mul_real
      exact hAD_weaken.mono_constant h_const
    · -- Fine scale: trivial bound absorbed via epsilon
      have h_rho_gt : rho > rho_val delta k_max := by linarith
      have h_trivial :
          IsADSet1 E_rho rho (1 - sigma)
            (ENNReal.ofReal (10 / rho)) :=
        IsADSet1.trivial_bound
          (α := 1 - sigma) hE_bdd
          (by linarith) hrho_le_one
          (by linarith) (by linarith)
      have h_rho_kmax_lower : rho_val delta k_max ≥ Real.rpow delta (midLoss + 1 / (N : ℝ)) := by
        dsimp only [rho_val]
        have hN_pos : 0 < (N : ℝ) := by positivity
        have h1 : (k_max : ℝ) / (N : ℝ) ≥ 1 - midLoss - 1 / (N : ℝ) := by
          calc (k_max : ℝ) / (N : ℝ)
              ≥ ((N : ℝ) * (1 - midLoss) - 1) / (N : ℝ) := by gcongr <;> exact hk_max_lower
            _ = 1 - midLoss - 1 / (N : ℝ) := by field_simp [hN_pos.ne'] <;> ring
        have h2 : midLoss + 1 / (N : ℝ) ≥ 1 - (k_max : ℝ) / (N : ℝ) := by linarith
        exact Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one h2
      have h1div : 1 / rho ≤ Real.rpow delta (-midLoss - 1 / (N : ℝ)) := by
        have h_pos1 : 0 < rho_val delta k_max := hrho_val_pos delta hdelta_pos k_max
        have h2 : 1 / rho < 1 / rho_val delta k_max := by
          apply one_div_lt_one_div_of_lt <;> linarith
        have h3 : 1 / rho_val delta k_max = Real.rpow delta (-(1 - (k_max : ℝ) / (N : ℝ))) := by
          dsimp only [rho_val]
          have h_pos : 0 < Real.rpow delta (1 - (k_max : ℝ) / (N : ℝ)) := Real.rpow_pos_of_pos hdelta_pos _
          have h_eq : (Real.rpow delta (1 - (k_max : ℝ) / (N : ℝ)))⁻¹ = Real.rpow delta (-(1 - (k_max : ℝ) / (N : ℝ))) := by
            exact (Real.rpow_neg hdelta_pos.le _).symm
          simpa using h_eq
        have hN_pos : 0 < (N : ℝ) := by positivity
        have h4 : (k_max : ℝ) / (N : ℝ) ≥ 1 - midLoss - 1 / (N : ℝ) := by
          calc (k_max : ℝ) / (N : ℝ)
              ≥ ((N : ℝ) * (1 - midLoss) - 1) / (N : ℝ) := by gcongr <;> exact hk_max_lower
            _ = 1 - midLoss - 1 / (N : ℝ) := by field_simp [hN_pos.ne'] <;> ring
        have h5 : -(1 - (k_max : ℝ) / (N : ℝ)) ≥ -midLoss - 1 / (N : ℝ) := by linarith
        have h6 : Real.rpow delta (-(1 - (k_max : ℝ) / (N : ℝ))) ≤ Real.rpow delta (-midLoss - 1 / (N : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one h5
        calc 1 / rho ≤ 1 / rho_val delta k_max := h2.le
          _ = Real.rpow delta (-(1 - (k_max : ℝ) / (N : ℝ))) := h3
          _ ≤ Real.rpow delta (-midLoss - 1 / (N : ℝ)) := h6
      have h2 : (10 : ℝ) / rho ≤ (10 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) := by
        calc (10 : ℝ) / rho = (10 : ℝ) * (1 / rho) := by ring
          _ ≤ (10 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) := by gcongr
      have h_half_triv : (10 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) ≤ Real.rpow delta (-outputLoss) / 10 := by
        have h : (100 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) ≤ Real.rpow delta (-outputLoss) := h_absorb_trivial
        have h' : (10 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) = ((100 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ))) / 10 := by ring
        rw [h']
        exact div_le_div_of_nonneg_right h (by norm_num)
      have h3 : ENNReal.ofReal ((10 : ℝ) / rho) ≤ Kakeya.realRpowENN delta (-outputLoss) / 10 := by
        simp only [Kakeya.realRpowENN]
        have h4 : ENNReal.ofReal (Real.rpow delta (-outputLoss) / 10) =
            ENNReal.ofReal (Real.rpow delta (-outputLoss)) / 10 :=
          (ofReal_div10 (Real.rpow_nonneg hdelta_pos.le _)).symm
        rw [← h4]
        exact ENNReal.ofReal_le_ofReal (h2.trans h_half_triv)
      exact h_trivial.mono_constant h3

  -- Build final output using bridge conversion
  let C : ENNReal := Kakeya.realRpowENN delta (-outputLoss)
  have hC_real : C = ENNReal.ofReal (Real.rpow delta (-outputLoss)) := by
    rfl
  have hC_ne_top : C ≠ ⊤ := by
    rw [hC_real]
    exact ENNReal.ofReal_ne_top
  have h_pos_out : 0 ≤ Real.rpow delta (-outputLoss) := (Real.rpow_pos_of_pos hdelta_pos _).le
  have hC_div10_eq : C / 10 = ENNReal.ofReal (Real.rpow delta (-outputLoss) / 10) := by
    rw [hC_real]
    exact ofReal_div10 h_pos_out
  have hC_div10_ne_top : C / 10 ≠ ⊤ := by
    rw [hC_div10_eq]
    exact ENNReal.ofReal_ne_top
  have h10_mul_div10 : 10 * (C / 10) = C := by
    rw [hC_div10_eq]
    let x : ℝ := Real.rpow delta (-outputLoss) / 10
    have hx_nonneg : 0 ≤ x := by positivity
    have h : (10 : ENNReal) * ENNReal.ofReal x = ENNReal.ofReal ((10 : ℝ) * x) := by
      have h1 : (10 : ENNReal) = ENNReal.ofReal (10 : ℝ) := by norm_cast
      calc
        (10 : ENNReal) * ENNReal.ofReal x
          = ENNReal.ofReal (10 : ℝ) * ENNReal.ofReal x := by rw [h1]
        _ = ENNReal.ofReal ((10 : ℝ) * x) := (ENNReal.ofReal_mul (by norm_num)).symm
    rw [h]
    have h2 : (10 : ℝ) * x = Real.rpow delta (-outputLoss) := by
      dsimp only [x] <;> ring
    rw [h2, hC_real]
  have h_bridge2 : ∀ (set : Set ℝ) (δ α : ℝ) (C' : ENNReal),
      0 < δ → δ ≤ 1 → C' ≠ ⊤ → IsADSet1 set δ α C' → PureWZ2PaperADSet1 set δ α (10 * C') :=
    h_bridge.2
  let localGrainsData : PureWZ2LocalGrainData Z sigma C :=
    { planeMap := planeMap_Z
      planeMap_lipschitz := restrictPlaneMap_lipschitz hZ_sub planeMap hlip
      planeMap_unit := restrictPlaneMap_unit hZ_sub planeMap hunit
      planeMap_incidence := restrictPlaneMap_incidence hZ_sub planeMap hinc
      local_ad := fun rho hdelta_le_rho hrho_le_one point =>
        let E_rho := scalarProjection (planeMap_Z point)
            (Z.union ∩ Metric.closedBall (point : Point3) (Real.sqrt rho))
        have h_isad : IsADSet1 E_rho rho (1 - sigma) (C / 10) :=
          h_local_ad_isad rho hdelta_le_rho hrho_le_one (point : Point3) point.prop
        have h_paper : PureWZ2PaperADSet1 E_rho rho (1 - sigma) (10 * (C / 10)) :=
          h_bridge2 E_rho rho (1 - sigma) (C / 10)
            (show 0 < rho from by linarith) hrho_le_one hC_div10_ne_top h_isad
        have h_final_const : 10 * (C / 10) = C := h10_mul_div10
        h_final_const ▸ h_paper }
  -- Weaken extremal from midLoss to outputLoss
  have hZ_extremal_output : WZ2PaperCroppedIsExtremal sigma outputLoss F Z :=
    hZ_extremal.mono_loss hmid_le_output
  -- Weaken CWA from δ^(-midLoss) to δ^(-outputLoss)
  have h_rpow_weaken : Kakeya.realRpowENN delta (-midLoss) ≤
      Kakeya.realRpowENN delta (-outputLoss) := by
    simp only [Kakeya.realRpowENN]
    apply ENNReal.ofReal_mono
    have h : -midLoss ≥ -outputLoss := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one h
  have hZ_cwa_output : WZ2PaperConvexWolffBound F
      (Kakeya.realRpowENN delta (-outputLoss)) := by
    intro convexSet hconv
    have h := hZ_cwa convexSet hconv
    have h_mul : (Kakeya.realRpowENN delta (-midLoss)) * volume convexSet * F.enncard ≤
        (Kakeya.realRpowENN delta (-outputLoss)) * volume convexSet * F.enncard := by
      gcongr
      <;> exact h_rpow_weaken
    exact h.trans h_mul
  have h_final : Nonempty (PureWZ2EveryScaleLocalGrainData
      (sigma := sigma) (outputLoss := outputLoss)
      (Y := Y) planeMap) :=
    ⟨{ shading := Z
       subshading := hZ_sub
       extremal := hZ_extremal_output
       cwa := hZ_cwa_output
       localGrains := localGrainsData }⟩
  exact h_final

end Kakeya.Assouad

end
