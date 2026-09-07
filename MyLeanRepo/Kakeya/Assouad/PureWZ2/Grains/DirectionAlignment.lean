import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Direction alignment from paper tube cover relation

Derives norm-distance bounds between paper directions from
`WZ1PaperTubeCovers`. The cover relation includes an angle bound `≤ rho/2`,
which translates to `‖paperDir_fine - paperDir_coarse‖ ≤ rho/2`.

This is the PureWZ2 analogue of `WZ1BalancedCoverData.direction_alignment`,
which gives `≤ 4 * rho`. Our bound is tighter (`rho/2`) because the paper
line-distance metric directly includes the angle.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set InnerProductGeometry

attribute [local instance] Classical.propDecidable

/-- Angle between unit vectors bounds their norm difference: `‖u - v‖ ≤ angle u v`.

Proof: `‖u - v‖ = 2 * sin(θ/2) ≤ 2 * (θ/2) = θ` for `θ ∈ [0, π]`. -/
lemma norm_sub_le_angle {u v : Point3}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u - v‖ ≤ InnerProductGeometry.angle u v := by
  set θ : ℝ := InnerProductGeometry.angle u v with hθ
  have hθ_nonneg : 0 ≤ θ := InnerProductGeometry.angle_nonneg u v
  have hθ_le_pi : θ ≤ Real.pi := InnerProductGeometry.angle_le_pi u v
  have h_inner : inner ℝ u v = Real.cos θ := by
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm u v
    rw [hu, hv] at h
    simpa using h.symm
  have h_norm_sq : ‖u - v‖ ^ 2 = 2 - 2 * Real.cos θ := by
    have h2 : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u v + ‖v‖ ^ 2 :=
      norm_sub_sq_real u v
    rw [h2, hu, hv, h_inner] <;> ring
  have h_sin_nonneg : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  have h_cos_double : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h : Real.cos (2 * (θ / 2)) = 2 * Real.cos (θ / 2) ^ 2 - 1 :=
      Real.cos_two_mul (θ / 2)
    have h2 : 2 * (θ / 2) = θ := by ring
    rw [h2] at h
    have h3 : Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 :=
      Real.cos_sq_add_sin_sq (θ / 2)
    nlinarith
  have h4 : ‖u - v‖ ^ 2 = (2 * Real.sin (θ / 2)) ^ 2 := by
    rw [h_norm_sq, h_cos_double] <;> ring
  have h5 : 0 ≤ ‖u - v‖ := by positivity
  have h6 : ‖u - v‖ = 2 * Real.sin (θ / 2) := by nlinarith
  rw [h6]
  have h7 : 0 ≤ θ / 2 := by linarith
  have h8 : Real.sin (θ / 2) ≤ θ / 2 := Real.sin_le h7
  linarith

/-- Direction alignment from the paper cover relation.

If `WZ1PaperTubeCovers fine coarse`, then
`‖wz1PaperDirection fine - wz1PaperDirection coarse‖ ≤ rho / 2`. -/
lemma paper_cover_direction_alignment
    {delta rho : ℝ}
    {fine : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    (hcover : WZ1PaperTubeCovers fine coarse) :
    ‖wz1PaperDirection fine - wz1PaperDirection coarse‖ ≤ rho / 2 := by
  have h1 : wz1PaperLineDistance fine coarse ≤ rho / 2 := hcover
  have h_angle : InnerProductGeometry.angle
      (wz1PaperDirection fine) (wz1PaperDirection coarse) ≤ rho / 2 := by
    have h_dist : 0 ≤ dist (wz1TubeAxisZeroPoint fine) (wz1TubeAxisZeroPoint coarse) :=
      by positivity
    have h_sum : dist (wz1TubeAxisZeroPoint fine) (wz1TubeAxisZeroPoint coarse) +
        InnerProductGeometry.angle (wz1PaperDirection fine) (wz1PaperDirection coarse) ≤
        rho / 2 := h1
    linarith
  have h_align : ‖wz1PaperDirection fine - wz1PaperDirection coarse‖ ≤
      InnerProductGeometry.angle (wz1PaperDirection fine) (wz1PaperDirection coarse) :=
    norm_sub_le_angle (wz1PaperDirection_norm fine) (wz1PaperDirection_norm coarse)
  exact h_align.trans h_angle

/-- Existence of a unit vector perpendicular to any nonzero vector in `Point3`.

Uses `OrthonormalBasis.fromOrthogonalSpanSingleton` to obtain an orthonormal
basis of the 2-dimensional orthogonal complement, then picks one vector. -/
lemma exists_unit_perpendicular (v : Point3) (hv : v ≠ 0) :
    ∃ (n : Point3), ‖n‖ = 1 ∧ inner ℝ v n = 0 := by
  let _i : Fact (Module.finrank ℝ Point3 = 3) := ⟨by simp⟩
  let basis : OrthonormalBasis (Fin 2) ℝ (ℝ ∙ v)ᗮ :=
    OrthonormalBasis.fromOrthogonalSpanSingleton (n := 2) hv
  let n : Point3 := (basis 0 : Point3)
  have hnorm : ‖n‖ = 1 := basis.orthonormal.1 0
  have hperp : inner ℝ v n = 0 := by
    have h1 : (n : Point3) ∈ (ℝ ∙ v)ᗮ := (basis 0).property
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp h1
  exact ⟨n, hnorm, hperp⟩

/-- The fiber over a coarse parent is near-planar.

All fine tubes in the full geometric fiber over `parent` have directions within
`rho / 2` of the parent direction. Choosing a unit normal `n` perpendicular to
the parent direction gives `|inner(fine_dir, n)| ≤ rho / 2`.

This is the key lemma showing "the fiber IS the direction bin": the cover
relation's angle bound directly implies near-planarity without any additional
pigeonholing or mass loss. -/
lemma fiber_near_planar
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (hrho_pos : 0 < rho) :
    ∃ (normal : Point3), ‖normal‖ = 1 ∧
      ∀ (source : Fin fine.card),
        WZ1PaperTubeCovers (fine.tube source) (coarse.tube parent) →
        |inner ℝ (fine.tube source).direction normal| ≤ rho / 2 := by
  let d_coarse := wz1PaperDirection (coarse.tube parent)
  have h_coarse_unit : ‖d_coarse‖ = 1 := wz1PaperDirection_norm (coarse.tube parent)
  have h_coarse_ne_zero : d_coarse ≠ 0 := by
    intro h
    rw [h] at h_coarse_unit
    simp at h_coarse_unit
  rcases exists_unit_perpendicular d_coarse h_coarse_ne_zero with ⟨normal, hnorm, hperp⟩
  refine ⟨normal, hnorm, fun source hcover => ?_⟩
  let d_fine := wz1PaperDirection (fine.tube source)
  have h_align : ‖d_fine - d_coarse‖ ≤ rho / 2 :=
    paper_cover_direction_alignment hcover
  have h1 : inner ℝ d_fine normal = inner ℝ (d_fine - d_coarse) normal := by
    have h2 : inner ℝ d_fine normal = inner ℝ (d_fine - d_coarse) normal + inner ℝ d_coarse normal := by
      simp [inner_sub_left]
      <;> ring
    rw [h2, hperp] <;> ring
  have h3 : |inner ℝ d_fine normal| ≤ ‖d_fine - d_coarse‖ * ‖normal‖ := by
    rw [h1]
    exact abs_real_inner_le_norm (d_fine - d_coarse) normal
  rw [hnorm] at h3
  have h4 : |inner ℝ d_fine normal| ≤ rho / 2 := h3.trans (by linarith)
  have h5 : |inner ℝ (fine.tube source).direction normal| = |inner ℝ d_fine normal| := by
    have h6 : d_fine = (fine.tube source).direction ∨ d_fine = -(fine.tube source).direction := by
      dsimp only [d_fine, wz1PaperDirection]
      split_ifs <;> tauto
    rcases h6 with (h6 | h6)
    · rw [h6]
    · rw [h6]
      have h7 : inner ℝ (-(fine.tube source).direction) normal = -inner ℝ (fine.tube source).direction normal := by
        rw [inner_neg_left]
      rw [h7]
      rw [abs_neg]
  rw [h5]
  exact h4

/-- Constant weak plane map from a single-coarse-parent fiber.

If every tube in a fine family is covered by the same coarse parent, then
`V(p) = orthogonalNormal(parent_dir)` is a constant unit-norm plane map with
incidence `≤ rho / 2` for every tube at every point.

This gives 100% mass retention: no subshading restriction is needed because
the incidence bound holds for all tubes uniformly. -/
lemma fiber_constant_weak_plane_map
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (S : WZ1PaperTubeShading fine)
    (hrho_pos : 0 < rho)
    (hcover_all : ∀ (i : Fin fine.card),
      WZ1PaperTubeCovers (fine.tube i) (coarse.tube parent)) :
    ∃ (V : {p : Point3 // p ∈ S.union} → Point3),
      (∀ p, ‖V p‖ = 1) ∧
      (∀ (i : Fin fine.card) (p : Point3) (hp : p ∈ S.carrier i),
        |inner ℝ (fine.tube i).direction (V ⟨p, ⟨i, hp⟩⟩)| ≤ rho / 2) := by
  rcases fiber_near_planar parent hrho_pos with ⟨normal, hnorm, hinc⟩
  let V : {p : Point3 // p ∈ S.union} → Point3 := fun _ => normal
  refine ⟨V, fun _ => hnorm, fun i p hp => ?_⟩
  exact hinc i (hcover_all i)

end Kakeya.Assouad

end
