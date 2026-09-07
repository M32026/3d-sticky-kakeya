import MyLeanRepo.Kakeya.AssertionD
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Base alignment from tube intersection

If a point lies in the intersection of two δ-tubes and their directions are
within `Cδ`, then the base of one tube lies within `(C+2)δ` of a signed
reparameterization of the other tube's axis.
-/

noncomputable section

open Kakeya MeasureTheory Set

namespace Kakeya.Assouad

/-- Decompose a point in a δ-tube carrier as `base + t • direction + e`
where `t ∈ [0,1]` and `‖e‖ ≤ δ`. -/
lemma tube_carrier_decomp {δ : ℝ} (hδ : 0 ≤ δ)
    (T : DeltaTube δ) (x : Point3) (hx : x ∈ T.carrier) :
    ∃ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ (e : Point3), ‖e‖ ≤ δ ∧ x = T.base + t • T.direction + e := by
  have hcarrier : T.carrier = Metric.cthickening δ (unitSegment T.base T.direction) := by
    simp [DeltaTube.carrier]
  rw [hcarrier] at hx
  have hcompact : IsCompact (unitSegment T.base T.direction) := by
    exact isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  rw [hcompact.cthickening_eq_biUnion_closedBall hδ] at hx
  rcases Set.mem_iUnion₂.mp hx with ⟨y, hy_seg, hy_ball⟩
  rcases hy_seg with ⟨t, ht, rfl⟩
  let e : Point3 := x - (T.base + t • T.direction)
  have he_norm : ‖e‖ ≤ δ := by
    simpa [e, dist_eq_norm] using hy_ball
  refine ⟨t, ht, e, he_norm, ?_⟩
  have h_eq : x = T.base + t • T.direction + e := by
    simp [e] <;> abel
  exact h_eq

/--
Base alignment when `sign = 1`: if `x` lies in both carriers and
`‖T.direction - U.direction‖ ≤ C * δ`, then there exists `s ∈ [-1,1]` such that
`‖T.base - (U.base + s • U.direction)‖ ≤ (C + 2) * δ`.
-/
lemma base_alignment_sign_pos {δ : ℝ} (hδ : 0 ≤ δ)
    (T U : DeltaTube δ) (C : ℝ)
    (hC : ‖T.direction - U.direction‖ ≤ C * δ)
    (x : Point3) (hx : x ∈ T.carrier ∩ U.carrier) :
    ∃ s ∈ Set.Icc (-1 : ℝ) 1,
      ‖T.base - (U.base + s • U.direction)‖ ≤ (C + 2) * δ := by
  rcases tube_carrier_decomp hδ T x hx.1 with ⟨t, ht, eT, heT, h_eqT⟩
  rcases tube_carrier_decomp hδ U x hx.2 with ⟨u, hu, eU, heU, h_eqU⟩
  have hT' : T.base = x - t • T.direction - eT := by
    rw [h_eqT] <;> abel
  have hU' : U.base = x - u • U.direction - eU := by
    rw [h_eqU] <;> abel
  set s : ℝ := u - t with hs_def
  have hs_range : s ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ⟨by linarith [ht.1, ht.2, hu.1, hu.2],
      by linarith [ht.1, ht.2, hu.1, hu.2]⟩
  have h_diff : T.base - U.base = u • U.direction - t • T.direction + (eU - eT) := by
    rw [hT', hU'] <;> abel
  have h_goal : T.base - (U.base + s • U.direction) =
      t • (U.direction - T.direction) + (eU - eT) := by
    have h1 : T.base - (U.base + s • U.direction) = T.base - U.base - s • U.direction := by
      abel
    rw [h1, h_diff, hs_def]
    rw [sub_smul, smul_sub] <;> abel
  refine' ⟨s, hs_range, _⟩
  rw [h_goal]
  have h_abs_t : |t| ≤ 1 := by
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h_norm_t : ‖t‖ = |t| := Real.norm_eq_abs t
  have h2 : ‖eU - eT‖ ≤ ‖eU‖ + ‖eT‖ := norm_sub_le _ _
  have h3 : |t| * ‖U.direction - T.direction‖ ≤ C * δ := by
    calc
      |t| * ‖U.direction - T.direction‖
        ≤ 1 * ‖U.direction - T.direction‖ := by gcongr <;> linarith
      _ = ‖U.direction - T.direction‖ := by ring
      _ ≤ C * δ := by
        have h_eq : ‖U.direction - T.direction‖ = ‖T.direction - U.direction‖ := by
          rw [show U.direction - T.direction = -(T.direction - U.direction) from by abel, norm_neg]
        rw [h_eq]
        exact hC
  have h4 : ‖eU‖ + ‖eT‖ ≤ δ + δ := by linarith [heT, heU]
  calc
    ‖t • (U.direction - T.direction) + (eU - eT)‖
      ≤ ‖t • (U.direction - T.direction)‖ + ‖eU - eT‖ := norm_add_le _ _
    _ = ‖t‖ * ‖U.direction - T.direction‖ + ‖eU - eT‖ := by rw [norm_smul]
    _ = |t| * ‖U.direction - T.direction‖ + ‖eU - eT‖ := by rw [h_norm_t]
    _ ≤ |t| * ‖U.direction - T.direction‖ + (‖eU‖ + ‖eT‖) := by gcongr
    _ ≤ C * δ + (δ + δ) := by linarith
    _ = (C + 2) * δ := by ring

/--
Base alignment when `sign = -1`: if `x` lies in both carriers and
`‖T.direction + U.direction‖ ≤ C * δ`, then there exists `s ∈ [-1,1]` such that
`‖T.base - ((U.base + U.direction) + s • (-U.direction))‖ ≤ (C + 2) * δ`.
-/
lemma base_alignment_sign_neg {δ : ℝ} (hδ : 0 ≤ δ)
    (T U : DeltaTube δ) (C : ℝ)
    (hC : ‖T.direction + U.direction‖ ≤ C * δ)
    (x : Point3) (hx : x ∈ T.carrier ∩ U.carrier) :
    ∃ s ∈ Set.Icc (-1 : ℝ) 1,
      ‖T.base - ((U.base + U.direction) + s • (-U.direction))‖ ≤ (C + 2) * δ := by
  rcases tube_carrier_decomp hδ T x hx.1 with ⟨t, ht, eT, heT, h_eqT⟩
  rcases tube_carrier_decomp hδ U x hx.2 with ⟨u, hu, eU, heU, h_eqU⟩
  have hT' : T.base = x - t • T.direction - eT := by
    rw [h_eqT] <;> abel
  have hU' : U.base = x - u • U.direction - eU := by
    rw [h_eqU] <;> abel
  set v : Point3 := -U.direction with hv_def
  have hC' : ‖T.direction - v‖ ≤ C * δ := by
    simpa [hv_def] using hC
  have h_diff : T.base - U.base = u • U.direction - t • T.direction + (eU - eT) := by
    rw [hT', hU'] <;> abel
  set s : ℝ := 1 - u - t with hs_def
  have hs_range : s ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ⟨by linarith [ht.1, ht.2, hu.1, hu.2],
      by linarith [ht.1, ht.2, hu.1, hu.2]⟩
  have h_goal : T.base - ((U.base + U.direction) + s • (-U.direction)) =
      t • (v - T.direction) + (eU - eT) := by
    have h1 : (U.base + U.direction) + s • (-U.direction) = U.base + (1 - s) • U.direction := by
      rw [hs_def]
      simp [smul_neg, sub_smul] <;> abel
    rw [h1]
    have h2 : T.base - (U.base + (1 - s) • U.direction) = T.base - U.base - (1 - s) • U.direction := by
      simp [sub_smul] <;> abel
    rw [h2, h_diff]
    have h3 : (1 - s) = u + t := by
      simp [hs_def] <;> ring
    rw [h3]
    have h4 : u • U.direction - t • T.direction + (eU - eT) - (u + t) • U.direction =
        t • (v - T.direction) + (eU - eT) := by
      rw [add_smul, smul_sub]
      simp [hv_def] <;> abel
    exact h4
  refine' ⟨s, hs_range, _⟩
  have h_goal' : T.base - ((U.base + U.direction) + s • v) =
      t • (v - T.direction) + (eU - eT) := by
    simpa [hv_def] using h_goal
  rw [h_goal']
  have h_abs_t : |t| ≤ 1 := by
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h_norm_t : ‖t‖ = |t| := Real.norm_eq_abs t
  have h2 : ‖eU - eT‖ ≤ ‖eU‖ + ‖eT‖ := norm_sub_le _ _
  have h3 : |t| * ‖v - T.direction‖ ≤ C * δ := by
    calc
      |t| * ‖v - T.direction‖
        ≤ 1 * ‖v - T.direction‖ := by gcongr <;> linarith
      _ = ‖v - T.direction‖ := by ring
      _ ≤ C * δ := by
        have h_eq : ‖v - T.direction‖ = ‖T.direction - v‖ := by
          rw [show v - T.direction = -(T.direction - v) from by abel, norm_neg]
        rw [h_eq]
        exact hC'
  have h4 : ‖eU‖ + ‖eT‖ ≤ δ + δ := by linarith [heT, heU]
  calc
    ‖t • (v - T.direction) + (eU - eT)‖
      ≤ ‖t • (v - T.direction)‖ + ‖eU - eT‖ := norm_add_le _ _
    _ = ‖t‖ * ‖v - T.direction‖ + ‖eU - eT‖ := by rw [norm_smul]
    _ = |t| * ‖v - T.direction‖ + ‖eU - eT‖ := by rw [h_norm_t]
    _ ≤ |t| * ‖v - T.direction‖ + (‖eU‖ + ‖eT‖) := by gcongr
    _ ≤ C * δ + (δ + δ) := by linarith
    _ = (C + 2) * δ := by ring

end Kakeya.Assouad
