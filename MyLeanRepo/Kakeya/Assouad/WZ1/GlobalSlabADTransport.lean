import MyLeanRepo.Kakeya.Assouad.WZ1.ADPerturbation
import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Global slab AD transport under slope perturbation

If two slopes are pointwise δ-close on `[-1,1]`, their global grain projections
of a set in the unit ball are δ-close in Hausdorff distance.  Applying the AD
perturbation lemma transports `IsADSet1` (and hence `HasGlobalSlabAD`) from one
slope to the other with constant factor 8.
-/

namespace Kakeya.Assouad

open Metric Set

/--
If two slopes are pointwise δ-close on `[-1,1]` and `E` lies in the unit ball
with heights in `[-1,1]`, then every point of the second projection is within
δ of some point of the first projection.
-/
lemma globalGrainProjection_close_by_delta
    {E : Set Point3} {s1 s2 : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (h_slopes : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |s1 z - s2 z| ≤ δ)
    (hE_height : ∀ p ∈ E, p (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1)
    (hE_unitBall : E ⊆ Metric.closedBall (0 : Point3) 1) :
    ∀ x ∈ globalGrainProjection s2 E,
      ∃ y ∈ globalGrainProjection s1 E, |x - y| ≤ δ := by
  intro x hx
  rcases hx with ⟨p, hp, rfl⟩
  let z := p (2 : Fin 3)
  have hz : z ∈ Set.Icc (-1 : ℝ) 1 := hE_height p hp
  have h_close_slopes : |s1 z - s2 z| ≤ δ := h_slopes z hz
  have h_close_slopes' : |s2 z - s1 z| ≤ δ := by
    have h : |s2 z - s1 z| = |s1 z - s2 z| := by rw [show s2 z - s1 z = -(s1 z - s2 z) by ring, abs_neg]
    rw [h]
    exact h_close_slopes
  have hp_unit : p ∈ Metric.closedBall (0 : Point3) 1 := hE_unitBall hp
  have h_norm : ‖p‖ ≤ 1 := by
    simpa [Metric.mem_closedBall] using hp_unit
  let e1 : Point3 := EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
  have h_inner_e1 : inner ℝ p e1 = p (1 : Fin 3) := by
    rw [EuclideanSpace.inner_single_right]
    <;> simp
  have h_p1_eq : p (1 : Fin 3) = inner ℝ p e1 := h_inner_e1.symm
  have h_cs : |inner ℝ p e1| ≤ ‖p‖ * ‖e1‖ := abs_real_inner_le_norm p e1
  have h_e1_norm : ‖e1‖ = 1 := by
    rw [PiLp.norm_single] <;> norm_num
  have h_p1 : |p (1 : Fin 3)| ≤ ‖p‖ := by
    rw [h_p1_eq]
    rw [h_e1_norm] at h_cs
    simpa using h_cs
  have h_p1_le_one : |p (1 : Fin 3)| ≤ 1 := by
    calc
      |p (1 : Fin 3)| ≤ ‖p‖ := h_p1
      _ ≤ 1 := h_norm
  let y := inner ℝ p (globalGrainDirection (s1 z))
  have hy : y ∈ globalGrainProjection s1 E := ⟨p, hp, rfl⟩
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  have h_inner_e0 : inner ℝ p e0 = p (0 : Fin 3) := by
    rw [EuclideanSpace.inner_single_right] <;> simp
  have h_proj2 : inner ℝ p (globalGrainDirection (s2 z)) =
      p (0 : Fin 3) + s2 z * p (1 : Fin 3) := by
    have h : globalGrainDirection (s2 z) = e0 + s2 z • e1 := by
      simp [globalGrainDirection, e0, e1]
    rw [h]
    rw [inner_add_right, inner_smul_right, h_inner_e0, h_inner_e1]
  have h_proj1 : y = p (0 : Fin 3) + s1 z * p (1 : Fin 3) := by
    have h : globalGrainDirection (s1 z) = e0 + s1 z • e1 := by
      simp [globalGrainDirection, e0, e1]
    simp only [y, h]
    rw [inner_add_right, inner_smul_right, h_inner_e0, h_inner_e1]
  have h_diff : inner ℝ p (globalGrainDirection (s2 z)) - y =
      (s2 z - s1 z) * p (1 : Fin 3) := by
    rw [h_proj2, h_proj1]
    <;> ring
  have h_abs : |inner ℝ p (globalGrainDirection (s2 z)) - y| ≤ δ := by
    rw [h_diff]
    calc
      |(s2 z - s1 z) * p (1 : Fin 3)|
        = |s2 z - s1 z| * |p (1 : Fin 3)| := by rw [abs_mul]
      _ ≤ δ * |p (1 : Fin 3)| := by gcongr
      _ ≤ δ * 1 := by gcongr
      _ = δ := by ring
  exact ⟨y, hy, h_abs⟩

/--
Transport `IsADSet1` from the first slope's projection to the second slope's
projection, assuming the slopes are δ-close and the second projection is
bounded in `[-4,4]`.
-/
lemma IsADSet1.transport_globalGrainProjection
    {E : Set Point3} {s1 s2 : ℝ → ℝ} {δ α : ℝ} {C : ENNReal}
    (hδ : 0 < δ)
    (h_slopes : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |s1 z - s2 z| ≤ δ)
    (hE_height : ∀ p ∈ E, p (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1)
    (hE_unitBall : E ⊆ Metric.closedBall (0 : Point3) 1)
    (hE2_bounded : globalGrainProjection s2 E ⊆ Set.Icc (-4 : ℝ) 4)
    (hAD : IsADSet1 (globalGrainProjection s1 E) δ α C) :
    IsADSet1 (globalGrainProjection s2 E) δ α (8 * C) :=
  hAD.perturb_by_delta
    (globalGrainProjection_close_by_delta hδ h_slopes hE_height hE_unitBall)
    hE2_bounded

/--
Transport `HasGlobalSlabAD` from slope `s1` to slope `s2` when they are
pointwise δ-close on `[-1,1]`, the shading union lies in the unit ball, and
the second slope's projection of every slab is bounded in `[-4,4]`.
-/
lemma HasGlobalSlabAD.transport
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Y : Kakeya.Streamlined.TubeShading F}
    {s1 s2 : ℝ → ℝ} {sigma : ℝ} {C : ENNReal}
    (hAD : HasGlobalSlabAD Y s1 sigma C)
    (hδ : 0 < δ)
    (h_slopes : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |s1 z - s2 z| ≤ δ)
    (h_unitBall : F.IsInUnitBall)
    (hE2_bounded : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      globalGrainProjection s2 (globalGrainSlab Y.union z δ) ⊆
        Set.Icc (-4 : ℝ) 4) :
    HasGlobalSlabAD Y s2 sigma (8 * C) := by
  intro z hz
  let E := globalGrainSlab Y.union z δ
  have hE_height : ∀ p ∈ E, p (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := by
    intro p hp
    exact hp.2
  have hE_unitBall : E ⊆ Metric.closedBall (0 : Point3) 1 := by
    intro p hp
    have h_p_in_union : p ∈ Y.union := hp.1.1
    rcases h_p_in_union with ⟨i, hi⟩
    have h1 : p ∈ (F.tube i).carrier := Y.subset_body i hi
    have h2 : (F.tube i).carrier ⊆ Metric.closedBall (0 : Point3) 1 := h_unitBall i
    exact h2 h1
  exact (hAD z hz).transport_globalGrainProjection
    hδ h_slopes hE_height hE_unitBall (hE2_bounded z hz)

end Kakeya.Assouad
