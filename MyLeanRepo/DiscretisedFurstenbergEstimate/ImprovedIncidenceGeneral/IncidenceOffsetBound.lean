module

/-
  Offset bound and tube family boundedness from incidence.

  Given p ∈ closedBall 0 1 and p ∈ cthickening(δ, ℓ), proves:
  1. ‖ℓ.offset‖ ≤ 2 (for δ ≤ 1)
  2. Any family of lines all δ-near a bounded point set is bounded in AffineLine metric.

  These are needed to satisfy the hypotheses of construct_nice_configuration
  and extract_finite_tube_sset.

  Whiteprint node: improved_incidence_general / incidence_offset_bound
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal


noncomputable section

namespace DirecretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open EuclideanGeometry

/-- If p is within distance δ of line ℓ and ‖p‖ ≤ 1, then ‖ℓ.offset‖ ≤ 1 + δ.
    The offset is the orthogonal projection of 0 onto ℓ, which minimizes
    distance to 0 among all points in ℓ. -/
lemma offset_norm_le_from_incidence {δ : ℝ} (hδ_pos : 0 < δ)
    {p : EuclideanPlane} (hp_norm : ‖p‖ ≤ 1)
    {ℓ : AffineLine} (h_inc : p ∈ Metric.cthickening δ ℓ.1) :
    ‖ℓ.offset‖ ≤ 1 + δ := by
  -- Use orthogonal projection of p onto ℓ to find a nearby point q ∈ ℓ
  let q : EuclideanPlane := orthogonalProjection ℓ.1 p
  have hq : q ∈ ℓ.1 := orthogonalProjection_mem p
  have hdist : dist p q ≤ δ := by
    -- q achieves the infimum distance, so edist p q = infEDist p ℓ.1
    have h_achieves : ∀ y ∈ ℓ.1, dist p q ≤ dist p y := by
      intro y hy
      have h : dist p q = Metric.infDist p ℓ.1 :=
        dist_orthogonalProjection_eq_infDist ℓ.1 p
      rw [h]
      exact Metric.infDist_le_dist_of_mem hy
    have h_edist_achieves : ∀ y ∈ ℓ.1, edist p q ≤ edist p y := by
      intro y hy
      have h : dist p q ≤ dist p y := h_achieves y hy
      have h' : edist p q ≤ edist p y := by
        have h1 : edist p q = ENNReal.ofReal (dist p q) := by simp [edist_dist]
        have h2 : edist p y = ENNReal.ofReal (dist p y) := by simp [edist_dist]
        rw [h1, h2]
        gcongr
      exact h'
    have h_inf_le : Metric.infEDist p ℓ.1 ≤ edist p q :=
      Metric.infEDist_le_edist_of_mem hq
    have h_q_le : edist p q ≤ Metric.infEDist p ℓ.1 :=
      Metric.le_infEDist.mpr h_edist_achieves
    have h_eq : edist p q = Metric.infEDist p ℓ.1 := le_antisymm h_q_le h_inf_le
    have h_edist_bound : Metric.infEDist p ℓ.1 ≤ ENNReal.ofReal δ := by
      simpa [Metric.mem_cthickening_iff] using h_inc
    have h_final : edist p q ≤ ENNReal.ofReal δ := by
      rw [h_eq] <;> exact h_edist_bound
    exact (edist_le_ofReal (by positivity)).mp h_final
  -- Offset minimizes distance from 0 to ℓ, so ‖offset‖ ≤ ‖q‖
  have h_inf : dist (0 : EuclideanPlane) ℓ.offset =
      Metric.infDist (0 : EuclideanPlane) ℓ.1 :=
    dist_orthogonalProjection_eq_infDist ℓ.1 0
  have h_le : Metric.infDist (0 : EuclideanPlane) ℓ.1 ≤ dist (0 : EuclideanPlane) q :=
    Metric.infDist_le_dist_of_mem hq
  have h_norm_offset : ‖ℓ.offset‖ = dist (0 : EuclideanPlane) ℓ.offset := by
    simp [dist_zero_right]
  have h_norm_q : ‖q‖ = dist (0 : EuclideanPlane) q := by
    simp [dist_zero_right]
  have h1 : ‖ℓ.offset‖ ≤ ‖q‖ := by
    rw [h_norm_offset, h_inf, h_norm_q]
    exact h_le
  have h2 : ‖q‖ ≤ ‖p‖ + dist p q := by
    have h_tri : ‖q‖ ≤ ‖p‖ + ‖q - p‖ := by
      calc ‖q‖
        = ‖p + (q - p)‖ := by abel_nf
      _ ≤ ‖p‖ + ‖q - p‖ := norm_add_le _ _
    have h_dist : ‖q - p‖ = dist p q := by
      simp [dist_eq_norm, norm_sub_rev]
    rw [h_dist] at h_tri
    exact h_tri
  linarith

/-- If p ∈ closedBall 0 1, p ∈ cthickening(δ, ℓ), and δ ≤ 1,
    then ℓ.offset ∈ closedBall 0 2. -/
lemma offset_bound_from_incidence {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    {p : EuclideanPlane} (hp : p ∈ Metric.closedBall 0 1)
    {ℓ : AffineLine} (h_inc : p ∈ Metric.cthickening δ ℓ.1) :
    ℓ.offset ∈ Metric.closedBall 0 2 := by
  have hp_norm : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp
  have h : ‖ℓ.offset‖ ≤ 1 + δ := offset_norm_le_from_incidence hδ_pos hp_norm h_inc
  have h' : ‖ℓ.offset‖ ≤ 2 := by linarith
  simpa [Metric.mem_closedBall] using h'

/-- A family of AffineLines, all of which are δ-near a point p with ‖p‖ ≤ 1,
    is bounded in the AffineLine metric. -/
lemma tube_family_bounded_from_incidence {δ : ℝ} (hδ_pos : 0 < δ)
    {p : EuclideanPlane} (hp_norm : ‖p‖ ≤ 1)
    {T : Set AffineLine} (hT_nonempty : T.Nonempty)
    (h_near : ∀ ℓ ∈ T, p ∈ Metric.cthickening δ ℓ.1) :
    Bornology.IsBounded T := by
  rcases hT_nonempty with ⟨ℓ₀, hℓ₀⟩
  have h_sp_norm : ∀ (ℓ : AffineLine), ‖ℓ.1.direction.starProjection‖ ≤ 1 :=
    fun ℓ => Submodule.starProjection_norm_le (K := ℓ.1.direction)
  have h_offset_bound : ∀ ℓ ∈ T, ‖ℓ.offset‖ ≤ 1 + δ := by
    intro ℓ hℓ
    exact offset_norm_le_from_incidence hδ_pos hp_norm (h_near ℓ hℓ)
  have h_main : ∀ ℓ ∈ T, dist ℓ ℓ₀ ≤ 4 + 2 * δ := by
    intro ℓ hℓ
    have h4 : ‖ℓ.1.direction.starProjection - ℓ₀.1.direction.starProjection‖ ≤
        ‖ℓ.1.direction.starProjection‖ + ‖ℓ₀.1.direction.starProjection‖ :=
      norm_sub_le _ _
    have h5 : ‖ℓ.offset - ℓ₀.offset‖ ≤ ‖ℓ.offset‖ + ‖ℓ₀.offset‖ := norm_sub_le _ _
    have h6 : ‖ℓ.1.direction.starProjection‖ ≤ 1 := h_sp_norm ℓ
    have h7 : ‖ℓ₀.1.direction.starProjection‖ ≤ 1 := h_sp_norm ℓ₀
    have h8 : ‖ℓ.offset‖ ≤ 1 + δ := h_offset_bound ℓ hℓ
    have h9 : ‖ℓ₀.offset‖ ≤ 1 + δ := h_offset_bound ℓ₀ hℓ₀
    have h10 : dist ℓ ℓ₀ =
        ‖ℓ.1.direction.starProjection - ℓ₀.1.direction.starProjection‖ +
        ‖ℓ.offset - ℓ₀.offset‖ := by
      rfl
    rw [h10]
    linarith
  have h : T ⊆ Metric.closedBall ℓ₀ (4 + 2 * δ) := by
    intro x hx
    simpa [Metric.mem_closedBall] using h_main x hx
  exact Metric.isBounded_iff_subset_ball ℓ₀ |>.mpr ⟨4 + 2 * δ + 1, by
    intro x hx
    have h' : x ∈ Metric.closedBall ℓ₀ (4 + 2 * δ) := h hx
    have h'' : dist x ℓ₀ ≤ 4 + 2 * δ := by simpa [Metric.mem_closedBall] using h'
    simpa [Metric.mem_ball] using lt_of_le_of_lt h'' (by linarith)⟩

end DirecretisedFurstenbergEstimate.ImprovedIncidenceGeneral
