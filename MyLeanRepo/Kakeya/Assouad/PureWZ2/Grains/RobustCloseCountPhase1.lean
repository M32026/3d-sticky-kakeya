import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.CrossPerturbation

/-!
# Phase 1: Direction alignment from cover relation

Key insight: `wz1PaperLineDistance` includes the angle, so
`WZ1PaperTubeCovers` directly gives direction alignment.

Provides:
- `selectParent`: functional parent from existential cover
- `crossBound_from_cover`: cross product norm ≤ rho/2
- `directionAlignment_from_cover`: projective norm difference ≤ rho/2
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Select a functional parent map from the existential cover. -/
def selectParent
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse) :
    Fin fine.card → Fin coarse.card :=
  fun i => Classical.choose (cover.covers i)

/-- The selected parent covers the fine tube. -/
lemma selectedParent_covers
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (i : Fin fine.card) :
    WZ1PaperTubeCovers (fine.tube i) (coarse.tube (selectParent cover i)) :=
  Classical.choose_spec (cover.covers i)

/-- Paper direction is either the raw direction or its negation. -/
lemma paperDirection_sign {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    ∃ (s : ℝ), (s = 1 ∨ s = -1) ∧ tube.direction = s • wz1PaperDirection tube := by
  unfold wz1PaperDirection
  by_cases h : 0 ≤ tube.direction (2 : Fin 3)
  · rw [if_pos h]
    exact ⟨1, Or.inl rfl, by simp⟩
  · rw [if_neg h]
    refine ⟨-1, Or.inr rfl, ?_⟩
    simp

/-- Angle bound from cover relation using paper directions. -/
lemma paperDirectionAngle_from_cover
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (i : Fin fine.card) :
    InnerProductGeometry.angle
      (wz1PaperDirection (fine.tube i))
      (wz1PaperDirection (coarse.tube (selectParent cover i))) ≤ rho / 2 := by
  let u := wz1PaperDirection (fine.tube i)
  let v := wz1PaperDirection (coarse.tube (selectParent cover i))
  have h : WZ1PaperTubeCovers (fine.tube i) (coarse.tube (selectParent cover i)) :=
    selectedParent_covers cover i
  have h_sum : dist (wz1TubeAxisZeroPoint (fine.tube i))
        (wz1TubeAxisZeroPoint (coarse.tube (selectParent cover i))) +
      InnerProductGeometry.angle u v ≤ rho / 2 := h
  have h_dist_nonneg : 0 ≤ dist (wz1TubeAxisZeroPoint (fine.tube i))
      (wz1TubeAxisZeroPoint (coarse.tube (selectParent cover i))) := by positivity
  have : InnerProductGeometry.angle u v ≤
      dist (wz1TubeAxisZeroPoint (fine.tube i))
        (wz1TubeAxisZeroPoint (coarse.tube (selectParent cover i))) +
      InnerProductGeometry.angle u v :=
    le_add_of_nonneg_left h_dist_nonneg
  exact le_trans this h_sum

/-- Cross product norm is invariant under sign flips of arguments. -/
lemma crossNorm_sign_invariant (u v : Point3) (s1 s2 : ℝ)
    (hs1 : s1 = 1 ∨ s1 = -1) (hs2 : s2 = 1 ∨ s2 = -1) :
    ‖wz1Cross (s1 • u) (s2 • v)‖ = ‖wz1Cross u v‖ := by
  have h1 : wz1Cross (s1 • u) (s2 • v) = s2 • wz1Cross (s1 • u) v :=
    wz1Cross_smul_right s2 (s1 • u) v
  have h2 : wz1Cross (s1 • u) v = s1 • wz1Cross u v :=
    wz1Cross_smul_left s1 u v
  have h_bilin : wz1Cross (s1 • u) (s2 • v) = (s1 * s2) • wz1Cross u v := by
    rw [h1, h2, smul_smul] <;> ring
  rw [h_bilin]
  have h_norm : ‖(s1 * s2) • wz1Cross u v‖ = ‖s1 * s2‖ * ‖wz1Cross u v‖ :=
    norm_smul (s1 * s2) (wz1Cross u v)
  rw [h_norm]
  have h_abs : ‖s1 * s2‖ = 1 := by
    rcases hs1 with (rfl | rfl) <;> rcases hs2 with (rfl | rfl) <;> norm_num
  rw [h_abs, one_mul]

/-- For unit vectors: `‖cross(u,v)‖ = sin(angle(u,v))`. -/
lemma crossNorm_eq_sin_angle {u v : Point3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖wz1Cross u v‖ = Real.sin (InnerProductGeometry.angle u v) := by
  have h1 : ‖wz1Cross u v‖ = ‖u‖ * ‖v‖ * Real.sin (InnerProductGeometry.angle u v) :=
    InnerProductGeometry.norm_toLp_symm_crossProduct (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
  rw [h1, hu, hv] <;> ring

/-- Cross product bound from direction alignment. -/
lemma crossBound_from_cover
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (hrho_pos : 0 < rho)
    (i : Fin fine.card) :
    ‖wz1Cross (fine.tube i).direction
        (coarse.tube (selectParent cover i)).direction‖ ≤ rho / 2 := by
  let u := wz1PaperDirection (fine.tube i)
  let v := wz1PaperDirection (coarse.tube (selectParent cover i))
  have h_angle : InnerProductGeometry.angle u v ≤ rho / 2 :=
    paperDirectionAngle_from_cover cover i
  have h_angle_nonneg : 0 ≤ InnerProductGeometry.angle u v :=
    InnerProductGeometry.angle_nonneg u v
  have h_hu : ‖u‖ = 1 := wz1PaperDirection_norm (fine.tube i)
  have h_hv : ‖v‖ = 1 := wz1PaperDirection_norm (coarse.tube (selectParent cover i))
  have hsin : ‖wz1Cross u v‖ = Real.sin (InnerProductGeometry.angle u v) :=
    crossNorm_eq_sin_angle h_hu h_hv
  have hsin_le : Real.sin (InnerProductGeometry.angle u v) ≤ InnerProductGeometry.angle u v :=
    Real.sin_le h_angle_nonneg
  have hcross_le : ‖wz1Cross u v‖ ≤ rho / 2 := by
    calc
      ‖wz1Cross u v‖ = Real.sin (InnerProductGeometry.angle u v) := hsin
      _ ≤ InnerProductGeometry.angle u v := hsin_le
      _ ≤ rho / 2 := h_angle
  rcases paperDirection_sign (fine.tube i) with ⟨s1, hs1, hdir1⟩
  rcases paperDirection_sign (coarse.tube (selectParent cover i)) with ⟨s2, hs2, hdir2⟩
  have h4 : ‖wz1Cross (fine.tube i).direction (coarse.tube (selectParent cover i)).direction‖ =
      ‖wz1Cross u v‖ := by
    rw [hdir1, hdir2]
    exact crossNorm_sign_invariant u v s1 s2 hs1 hs2
  rw [h4]
  exact hcross_le

/-- Norm difference bound for unit vectors: `‖u-v‖ ≤ angle(u,v)`. -/
lemma normDiff_le_angle {u v : Point3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u - v‖ ≤ InnerProductGeometry.angle u v := by
  set θ := InnerProductGeometry.angle u v with hθ
  have hθ_nonneg : 0 ≤ θ := InnerProductGeometry.angle_nonneg u v
  have hθ_le_pi : θ ≤ Real.pi := InnerProductGeometry.angle_le_pi u v
  have hcos : Real.cos θ = inner ℝ u v := by
    rw [InnerProductGeometry.cos_angle] <;> rw [hu, hv] <;> ring
  have h1 : ‖u - v‖ ^ 2 = 2 - 2 * inner ℝ u v := by
    have h := norm_sub_sq_real u v
    rw [h, hu, hv] <;> ring
  have h3 : inner ℝ u v = Real.cos θ := hcos.symm
  have h41 : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have h : Real.cos (2 * (θ / 2)) = 2 * Real.cos (θ / 2) ^ 2 - 1 := Real.cos_two_mul (θ / 2)
    have h5 : 2 * (θ / 2) = θ := by ring
    rw [h5] at h
    exact h
  have h42 : Real.cos (θ / 2) ^ 2 = 1 - Real.sin (θ / 2) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (θ / 2)
    linarith
  have h4 : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    rw [h41, h42] <;> ring
  have h2 : ‖u - v‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
    calc
      ‖u - v‖ ^ 2 = 2 - 2 * inner ℝ u v := h1
      _ = 2 - 2 * Real.cos θ := by rw [h3]
      _ = 2 - 2 * (1 - 2 * Real.sin (θ / 2) ^ 2) := by rw [h4]
      _ = 4 * Real.sin (θ / 2) ^ 2 := by ring
  have h5 : 0 ≤ ‖u - v‖ := by positivity
  have h6 : 0 ≤ Real.sin (θ / 2) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor
    · linarith
    · linarith [hθ_le_pi]
  have h7 : ‖u - v‖ = 2 * Real.sin (θ / 2) := by nlinarith
  rw [h7]
  have h8 : Real.sin (θ / 2) ≤ θ / 2 := Real.sin_le (by linarith)
  linarith

/-- Projective direction alignment from cover relation.

Given the cover relation, there exists a sign `s` such that
`‖coarse_dir - s • fine_dir‖ ≤ rho / 2`.
This is the form needed by `wz1Cross_projective_upper`. -/
lemma directionAlignment_from_cover
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (hrho_pos : 0 < rho)
    (i : Fin fine.card) :
    ∃ (s : ℝ), (s = 1 ∨ s = -1) ∧
      ‖(coarse.tube (selectParent cover i)).direction -
          s • (fine.tube i).direction‖ ≤ rho / 2 := by
  let u := wz1PaperDirection (fine.tube i)
  let v := wz1PaperDirection (coarse.tube (selectParent cover i))
  rcases paperDirection_sign (fine.tube i) with ⟨s1, hs1, hdir1⟩
  rcases paperDirection_sign (coarse.tube (selectParent cover i)) with ⟨s2, hs2, hdir2⟩
  let s : ℝ := s2 * s1
  have hs : s = 1 ∨ s = -1 := by
    rcases hs1 with (rfl | rfl) <;> rcases hs2 with (rfl | rfl) <;> norm_num <;> tauto
  have h_hu : ‖u‖ = 1 := wz1PaperDirection_norm (fine.tube i)
  have h_hv : ‖v‖ = 1 := wz1PaperDirection_norm (coarse.tube (selectParent cover i))
  have h_angle : InnerProductGeometry.angle u v ≤ rho / 2 :=
    paperDirectionAngle_from_cover cover i
  have h_normdiff : ‖v - u‖ ≤ rho / 2 := by
    have h : ‖v - u‖ ≤ InnerProductGeometry.angle v u := normDiff_le_angle h_hv h_hu
    have h_symm : InnerProductGeometry.angle v u = InnerProductGeometry.angle u v :=
      InnerProductGeometry.angle_comm v u
    rw [h_symm] at h
    linarith
  have hs1_mul : s1 * s1 = 1 := by
    rcases hs1 with (rfl | rfl) <;> norm_num
  have h_scalar : s2 * s1 * s1 = s2 := by
    rcases hs1 with (rfl | rfl) <;> norm_num
  have h_main : ‖(coarse.tube (selectParent cover i)).direction - s • (fine.tube i).direction‖ =
      ‖v - u‖ := by
    rw [hdir2, hdir1]
    have h9 : s2 • v - (s2 * s1) • (s1 • u) = s2 • (v - u) := by
      rw [smul_sub, smul_smul, h_scalar] <;> ring
    rw [h9]
    have h10 : ‖s2 • (v - u)‖ = ‖s2‖ * ‖v - u‖ := norm_smul s2 (v - u)
    rw [h10]
    have h11 : ‖s2‖ = 1 := by
      rcases hs2 with (rfl | rfl) <;> norm_num
    rw [h11, one_mul]
  refine' ⟨s, hs, _⟩
  rw [h_main]
  exact h_normdiff

end Kakeya.Assouad.PureWZ2
