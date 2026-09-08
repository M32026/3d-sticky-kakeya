/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Analysis.AffineSubspace
public import Mathlib.Data.Int.Star
public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Orthogonal projections
-/

@[expose] public section

open MeasureTheory Metric

namespace EuclideanGeometry

section
variable
  {V E}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace E] [NormedAddTorsor V E]
-- set_option trace.profiler.useHeartbeats true
-- set_option trace.profiler true

theorem orthogonalProjection_vsub_orthogonalProjection_eq_orthogonalProjection
    {A : AffineSubspace ℝ E} [Nonempty A] [A.direction.HasOrthogonalProjection]
    (p q : E) :
    orthogonalProjection A p -ᵥ orthogonalProjection A q =
      A.direction.orthogonalProjectionOnto (p -ᵥ q) := by
  rw [← orthogonalProjection_contLinear (s := A), ContinuousAffineMap.contLinear_map_vsub]

/-- If `u` lies in the direction of an affine subspace `A`, then replacing the point `x` by its
orthogonal projection onto `A` does not change the inner product `⟪u, x -ᵥ c⟫`. -/
theorem inner_vsub_eq_inner_orthogonalProjection_vsub
    {A : AffineSubspace ℝ E} [Nonempty A] [A.direction.HasOrthogonalProjection]
    {u : V} (hu : u ∈ A.direction) (x c : E) :
    inner ℝ u (x -ᵥ c) = inner ℝ u ((orthogonalProjection A x : E) -ᵥ c) := by
  have h : x -ᵥ c =
      (x -ᵥ (orthogonalProjection A x : E)) + ((orthogonalProjection A x : E) -ᵥ c) :=
    (vsub_add_vsub_cancel _ _ _).symm
  rw [h, inner_add_right,
      Submodule.inner_right_of_mem_orthogonal hu
        (vsub_orthogonalProjection_mem_direction_orthogonal A x), zero_add]

/-- The orthogonal projection onto a nonempty affine subspace is `1`-Lipschitz. -/
theorem orthogonalProjection_lipschitzWith_one
    (A : AffineSubspace ℝ E) [Nonempty A] [A.direction.HasOrthogonalProjection] :
    LipschitzWith 1 ((orthogonalProjection A) : E → ↥A) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro p q
  simp only [NNReal.coe_one, one_mul]
  rw [dist_eq_norm_vsub, dist_eq_norm_vsub V p q]
  rw [orthogonalProjection_vsub_orthogonalProjection_eq_orthogonalProjection]
  exact Submodule.norm_orthogonalProjectionOnto_apply_le A.direction _

/-- The fibre of a set `s` over a point `x` of an affine subspace `A`: the intersection of
`s` with the affine subspace through `x` orthogonal to the direction of `A`. -/
def orthogonalFiber (A : AffineSubspace ℝ E) [Nonempty A] (s : Set E) (x : A) : Set E :=
  s ∩ (AffineSubspace.mk' x.val A.directionᗮ)

theorem orthogonalFiber_mono (A : AffineSubspace ℝ E) [Nonempty A] {s t : Set E}
    (h : s ⊆ t) (x : A) : orthogonalFiber A s x ⊆ orthogonalFiber A t x :=
  Set.inter_subset_inter_left _ h

theorem orthogonalFiber_preimage_eq_empty (A : AffineSubspace ℝ E)
    [Nonempty A] [A.direction.HasOrthogonalProjection]
    {t : Set A} {x : A} (h : x ∉ t) :
    orthogonalFiber A ((orthogonalProjection A) ⁻¹' t) x = ∅ := by
  ext y
  refine ⟨?_, False.elim⟩
  rintro ⟨h1, h2⟩
  refine h ((?_ : x = orthogonalProjection A y) ▸ h1)
  symm
  rwa [orthogonalProjection_eq_iff_mem, ← AffineSubspace.mem_mk']

private lemma preimage_cthickening_subset_closedBall {A : AffineSubspace ℝ E}
    [Nonempty A] [A.direction.HasOrthogonalProjection]
    (r : NNReal) (x : A) {f : ℝ → AffineSubspace.mk' x.val A.directionᗮ} (hf : Isometry f)
    (h : (f 0).val = x.val) :
    { t : ℝ | (f t).val ∈ cthickening r A } ⊆ closedBall 0 r := by
  intro t ht
  -- The orthogonal projection of `(f t).val` onto `A` is `x.val`.
  have hproj : (orthogonalProjection A (f t).val : E) = x.val := by
    rw [coe_orthogonalProjection_eq_iff_mem]
    exact ⟨x.2, by simpa using AffineSubspace.mem_mk'.mp (f t).2⟩
  -- Hence `dist (f t).val x.val = infDist (f t).val A`.
  have h_dist_eq : dist (f t).val x.val = Metric.infDist (f t).val A := by
    have key := dist_orthogonalProjection_eq_infDist A (f t).val
    rw [hproj] at key
    exact key
  -- Membership in `cthickening r A` gives `infDist ≤ r`.
  have h_inf_le : Metric.infDist (f t).val A ≤ (r : ℝ) := by
    have : Metric.infEDist (f t).val A ≤ ENNReal.ofReal r :=
      Metric.mem_cthickening_iff.mp ht
    rw [Metric.infDist, ← ENNReal.toReal_ofReal r.coe_nonneg]
    exact ENNReal.toReal_mono (by simp) this
  -- The isometry turns `dist (f t).val x.val` into `|t|`.
  have h_dist_t : dist (f t).val x.val = |t| :=
    calc dist (f t).val x.val
        = dist (f t).val (f 0).val := congrArg (dist (f t).val) h.symm
      _ = dist (f t) (f 0) := rfl
      _ = dist t 0 := hf.dist_eq t 0
      _ = |t| := by rw [Real.dist_eq, sub_zero]
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs, ← h_dist_t]
  exact h_dist_eq.trans_le h_inf_le

end

section

variable
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem AffineSubspace.volume_eq_lintegral (A : AffineSubspace ℝ E) [Nonempty A]
    {s : Set E} (hs : MeasurableSet s) :
    volume s = ∫⁻ (x : A),
      μHE[Module.finrank ℝ A.directionᗮ] (orthogonalFiber A s x)
        ∂μHE[Module.finrank ℝ ↥A.direction] := by
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      A.euclideanHausdorffMeasure_eq_lintegral hs]
  congr

theorem μHE_one_orthogonalFiber_cthickening {A : AffineSubspace ℝ E} [Nonempty ↥A]
    (h : Module.finrank ℝ E = Module.finrank ℝ A.direction + 1)
    (r : NNReal) (x : A) :
    μHE[Module.finrank ℝ ↥A.directionᗮ] (orthogonalFiber A (cthickening r A) x) ≤ 2 * r := by
  have hone : Module.finrank ℝ ↥A.directionᗮ = 1 :=
    Submodule.finrank_add_finrank_orthogonal' (by linarith [h])
  set L : AffineSubspace ℝ E := AffineSubspace.mk' x.val A.directionᗮ with hL_def
  have hLnonempty : Nonempty ↥L := ⟨⟨x.val, AffineSubspace.self_mem_mk' _ _⟩⟩
  have hdir : Module.finrank ℝ L.direction = 1 := by
    rw [hL_def, AffineSubspace.direction_mk']; exact hone
  let x' : ↥L := ⟨x.val, AffineSubspace.self_mem_mk' x.val A.directionᗮ⟩
  obtain ⟨f, hf0⟩ :=
    AffineSubspace.exists_isometryEquiv_real_of_direction_finrank_eq_one hdir x'
  let g : ℝ → E := fun t => (f t).val
  have hf_iso : Isometry f := f.isometry
  have hg_iso : Isometry g := L.subtypeₐᵢ.isometry.comp hf_iso
  have hf0' : (f 0).val = x.val := by rw [hf0]
  have hrange : Set.range g = (L : Set E) := by
    change Set.range ((Subtype.val : ↥L → E) ∘ f) = _
    rw [Set.range_comp, f.surjective.range_eq, Set.image_univ, Subtype.range_coe]
  have hfiber_eq : orthogonalFiber A (cthickening r A) x =
      cthickening r A ∩ Set.range g := by
    change cthickening r A ∩ (L : Set E) = _; rw [hrange]
  rw [hfiber_eq, ← hg_iso.euclideanHausdorffMeasure_preimage (cthickening r A)]
  have hsub : g ⁻¹' cthickening r A ⊆ closedBall (0 : ℝ) r :=
    fun t ht => preimage_cthickening_subset_closedBall r x hf_iso hf0' ht
  refine (measure_mono hsub).trans ?_
  have hone' : Module.finrank ℝ ↥A.directionᗮ = Module.finrank ℝ ℝ := by
    rw [hone, Module.finrank_self]
  rw [hone', InnerProductSpace.euclideanHausdorffMeasure_eq_volume, Real.volume_closedBall,
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  simp [ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]

/-- Codimension-one lower bound for a normal fibre: the fibre of the closed `ρ`-ball around `c`,
taken over the orthogonal projection of `c`, has measure at least `2ρ`, because it contains the
length-`2ρ` normal segment through `c`. -/
theorem two_mul_ofReal_le_μHE_orthogonalFiber_closedBall {A : AffineSubspace ℝ E} [Nonempty ↥A]
    (h : Module.finrank ℝ E = Module.finrank ℝ A.direction + 1) (c : E) {ρ : ℝ} (_hρ : 0 ≤ ρ) :
    2 * ENNReal.ofReal ρ ≤
      μHE[Module.finrank ℝ ↥A.directionᗮ]
        (orthogonalFiber A (closedBall c ρ) (orthogonalProjection A c)) := by
  have hone : Module.finrank ℝ ↥A.directionᗮ = 1 :=
    Submodule.finrank_add_finrank_orthogonal' (by linarith [h])
  set x₀ : ↥A := orthogonalProjection A c with hx₀
  set L : AffineSubspace ℝ E := AffineSubspace.mk' (x₀ : E) A.directionᗮ with hL_def
  have hc_mem : c ∈ (L : Set E) := by
    have hvec : c -ᵥ (x₀ : E) ∈ A.directionᗮ :=
      vsub_orthogonalProjection_mem_direction_orthogonal A c
    rw [hL_def]
    exact (AffineSubspace.mem_mk').mpr hvec
  have hLnonempty : Nonempty ↥L := ⟨⟨(x₀ : E), AffineSubspace.self_mem_mk' _ _⟩⟩
  have hdir : Module.finrank ℝ L.direction = 1 := by
    rw [hL_def, AffineSubspace.direction_mk']; exact hone
  let c' : ↥L := ⟨c, hc_mem⟩
  obtain ⟨f, hf0⟩ :=
    AffineSubspace.exists_isometryEquiv_real_of_direction_finrank_eq_one hdir c'
  let g : ℝ → E := fun t => (f t).val
  have hf_iso : Isometry f := f.isometry
  have hg_iso : Isometry g := L.subtypeₐᵢ.isometry.comp hf_iso
  have hg0 : g 0 = c := by
    calc
      g 0 = (f 0).val := rfl
      _ = c'.val := by rw [hf0]
      _ = c := rfl
  have hrange : Set.range g = (L : Set E) := by
    change Set.range ((Subtype.val : ↥L → E) ∘ f) = _
    rw [Set.range_comp, f.surjective.range_eq, Set.image_univ, Subtype.range_coe]
  have hfiber_eq : orthogonalFiber A (closedBall c ρ) x₀ = closedBall c ρ ∩ Set.range g := by
    change closedBall c ρ ∩ (L : Set E) = _; rw [hrange]
  rw [hfiber_eq, ← hg_iso.euclideanHausdorffMeasure_preimage (closedBall c ρ)]
  have hsub : closedBall (0 : ℝ) ρ ⊆ g ⁻¹' closedBall c ρ := by
    intro t ht
    have hdt : dist t 0 ≤ ρ := mem_closedBall.mp ht
    have hmem : dist (g t) c ≤ ρ := by
      calc
        dist (g t) c = dist (g t) (g 0) := by rw [hg0]
        _ = dist t 0 := hg_iso.dist_eq t 0
        _ ≤ ρ := hdt
    exact Set.mem_preimage.mpr (mem_closedBall.mpr hmem)
  have hball :
      μHE[Module.finrank ℝ ↥A.directionᗮ] (closedBall (0 : ℝ) ρ) = 2 * ENNReal.ofReal ρ := by
    have hone' : Module.finrank ℝ ↥A.directionᗮ = Module.finrank ℝ ℝ := by
      rw [hone, Module.finrank_self]
    rw [hone', InnerProductSpace.euclideanHausdorffMeasure_eq_volume, Real.volume_closedBall,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp [ENNReal.ofReal_ofNat]
  calc
    2 * ENNReal.ofReal ρ = μHE[Module.finrank ℝ ↥A.directionᗮ] (closedBall (0 : ℝ) ρ) := by
      rw [hball]
    _ ≤ μHE[Module.finrank ℝ ↥A.directionᗮ] (g ⁻¹' closedBall c ρ) := measure_mono hsub

/-- Codimension-one version of the volume bound for an arbitrary measurable "cylinder" of the form
`cthickening r A ∩ (orthogonalProjection A) ⁻¹' Y`. -/
theorem volume_cthickening_inter_preimage_orthogonalProjection_le
    {A : AffineSubspace ℝ E} [Nonempty ↥A]
    (h : Module.finrank ℝ E = Module.finrank ℝ A.direction + 1)
    (r : NNReal) {Y : Set A} (hY : MeasurableSet Y) :
    volume (cthickening (r : ℝ) A ∩ (orthogonalProjection A) ⁻¹' Y) ≤
      2 * r * μHE[Module.finrank ℝ A.direction] Y := by
  set d := Module.finrank ℝ A.direction
  set P : E → ↥A := fun x => orthogonalProjection A x
  set T : Set E := cthickening (r : ℝ) A ∩ P ⁻¹' Y
  have hT_meas : MeasurableSet T :=
    isClosed_cthickening.measurableSet.inter ((orthogonalProjection A).continuous.measurable hY)
  rw [AffineSubspace.volume_eq_lintegral A hT_meas]
  let f (x : A) := Set.indicator Y (fun _ => 2 * (r : ENNReal)) x
  have h_bound : ∀ x : A, μHE[Module.finrank ℝ A.directionᗮ] (orthogonalFiber A T x) ≤ f x := by
    intro x
    by_cases hx : x ∈ Y
    · apply (measure_mono (orthogonalFiber_mono A (Set.inter_subset_left) x)).trans
      simp only [f, Set.indicator_of_mem hx]
      apply μHE_one_orthogonalFiber_cthickening h
    · suffices orthogonalFiber A T x = ∅ by simp [this]
      apply Set.eq_empty_of_subset_empty
      apply (orthogonalFiber_mono A (Set.inter_subset_right) _).trans
      rw [orthogonalFiber_preimage_eq_empty A hx]
  calc
    _ ≤ ∫⁻ x : A, f x ∂(μHE[d]) :=
        lintegral_mono h_bound
    _ = 2 * (r : ENNReal) * μHE[d] Y := by
        rw [lintegral_indicator_const hY]

/-- Reverse of `volume_cthickening_inter_preimage_orthogonalProjection_le` (codimension one): the
cylinder `cthickening r A ∩ π⁻¹ Y` over a measurable set `Y` has volume at least `2r` times the
measure of `Y`. -/
theorem two_mul_le_volume_cthickening_inter_preimage_orthogonalProjection
    {A : AffineSubspace ℝ E} [Nonempty ↥A]
    (h : Module.finrank ℝ E = Module.finrank ℝ A.direction + 1)
    (r : NNReal) {Y : Set A} (hY : MeasurableSet Y) :
    2 * (r : ENNReal) * μHE[Module.finrank ℝ A.direction] Y ≤
      volume (cthickening (r : ℝ) A ∩ (orthogonalProjection A) ⁻¹' Y) := by
  set d := Module.finrank ℝ A.direction
  set P : E → ↥A := fun x => orthogonalProjection A x
  set T : Set E := cthickening (r : ℝ) A ∩ P ⁻¹' Y
  have hT_meas : MeasurableSet T :=
    isClosed_cthickening.measurableSet.inter ((orthogonalProjection A).continuous.measurable hY)
  let f (x : A) := Set.indicator Y (fun _ => 2 * (r : ENNReal)) x
  have h_bound : ∀ x : A, f x ≤ μHE[Module.finrank ℝ A.directionᗮ] (orthogonalFiber A T x) := by
    intro x
    by_cases hx : x ∈ Y
    · simp only [f, Set.indicator_of_mem hx]
      have hfib : orthogonalFiber A (closedBall (x : E) (r : ℝ)) x ⊆
          orthogonalFiber A T x := by
        intro p hp
        rcases hp with ⟨hp_ball, hp_fiber⟩
        refine ⟨?_, hp_fiber⟩
        -- Show p ∈ cthickening (r : ℝ) A
        have hx_mem : (x : E) ∈ A := x.2
        have h_dist : dist p (x : E) ≤ (r : ℝ) := mem_closedBall.mp hp_ball
        have h_infEDist : Metric.infEDist p A ≤ ENNReal.ofReal (r : ℝ) :=
          calc
            Metric.infEDist p A ≤ edist p (x : E) :=
              Metric.infEDist_le_edist_of_mem hx_mem
            _ = ENNReal.ofReal (dist p (x : E)) := by rw [edist_dist]
            _ ≤ ENNReal.ofReal (r : ℝ) := ENNReal.ofReal_le_ofReal h_dist
        have h_cthick : p ∈ cthickening (r : ℝ) A := by
          rw [Metric.mem_cthickening_iff]
          exact h_infEDist
        -- Show p ∈ P⁻¹' Y, i.e. orthogonalProjection A p ∈ Y
        have hproj : (orthogonalProjection A p : E) = (x : E) := by
          rw [coe_orthogonalProjection_eq_iff_mem]
          refine ⟨x.2, ?_⟩
          have hp_fiber' : p -ᵥ (x : E) ∈ A.directionᗮ :=
            (AffineSubspace.mem_mk' (p := x.val) (direction := A.directionᗮ)).mp hp_fiber
          exact hp_fiber'
        have hproj_sub : orthogonalProjection A p = x :=
          Subtype.ext hproj
        have hP : P p = x := hproj_sub
        have hP_mem : P p ∈ Y := by
          rw [hP]
          exact hx
        exact Set.mem_inter h_cthick (Set.mem_preimage.mpr hP_mem)
      have hproj_eq : (orthogonalProjection A (x : E) : A) = x := by
        apply Subtype.ext
        rw [coe_orthogonalProjection_eq_iff_mem]
        exact ⟨x.2, by simp⟩
      calc
        2 * (r : ENNReal) = 2 * ENNReal.ofReal (r : ℝ) := by
          simp [ENNReal.ofReal_coe_nnreal]
        _ ≤ μHE[Module.finrank ℝ A.directionᗮ]
            (orthogonalFiber A (closedBall (x : E) (r : ℝ))
              (orthogonalProjection A (x : E))) :=
          two_mul_ofReal_le_μHE_orthogonalFiber_closedBall h (x : E) r.coe_nonneg
        _ = μHE[Module.finrank ℝ A.directionᗮ]
            (orthogonalFiber A (closedBall (x : E) (r : ℝ)) x) := by
          simp [hproj_eq]
        _ ≤ μHE[Module.finrank ℝ A.directionᗮ] (orthogonalFiber A T x) :=
          measure_mono hfib
    · simp [f, Set.indicator_of_notMem hx]
  calc
    2 * (r : ENNReal) * μHE[d] Y = (∫⁻ x : A, f x ∂(μHE[d])) := by
      rw [← lintegral_indicator_const hY]
    _ ≤ ∫⁻ x : A, μHE[Module.finrank ℝ A.directionᗮ] (orthogonalFiber A T x) ∂(μHE[d]) :=
      lintegral_mono h_bound
    _ = volume T := by
      rw [AffineSubspace.volume_eq_lintegral A hT_meas]
    _ = volume (cthickening (r : ℝ) A ∩ (orthogonalProjection A) ⁻¹' Y) := rfl

/-- Volume bound for a set contained in the closed `r`-thickening of an affine hyperplane,
in terms of the Hausdorff measure of its orthogonal projection. -/
theorem volume_image_orthogonalProjection {A : AffineSubspace ℝ E} [Nonempty ↥A]
    (hcodim : Module.finrank ℝ E = Module.finrank ℝ A.direction + 1)
    {s : Set E} {r : NNReal} (h : s ⊆ cthickening r A) :
    volume s ≤ 2 * r * μHE[Module.finrank ℝ A.direction] ((orthogonalProjection A) '' s) := by
  set d := Module.finrank ℝ A.direction
  set P : E → ↥A := fun x => orthogonalProjection A x
  set X : Set ↥A := MeasureTheory.toMeasurable (μHE[d] : Measure ↥A) (P '' s)
  have hX_meas : MeasurableSet X := measurableSet_toMeasurable _ _
  have hX_sub : P '' s ⊆ X := subset_toMeasurable _ _
  have hX_meas_eq : μHE[d] X = μHE[d] (P '' s) := measure_toMeasurable _
  have hs : s ⊆ cthickening (r : ℝ) A ∩ P ⁻¹' X :=
    fun y hy => ⟨h hy, hX_sub ⟨y, hy, rfl⟩⟩
  calc volume s
      ≤ volume (cthickening (r : ℝ) A ∩ P ⁻¹' X) := measure_mono hs
    _ ≤ 2 * r * μHE[d] X :=
        volume_cthickening_inter_preimage_orthogonalProjection_le hcodim r hX_meas
    _ = 2 * r * μHE[d] (P '' s) := by rw [hX_meas_eq]

end

end EuclideanGeometry
