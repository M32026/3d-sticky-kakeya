import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.Estimates
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Join
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Geometric lemmas for the tube density test net

This file develops the key geometric lemmas needed to construct a finite
polynomial-size test net of convex bodies for bounded δ-tube families.

## Main results

1. `volume_image_linearMap`: volume scaling under a linear map.
2. `frame_box_containment`: a framed box is contained in a slightly enlarged
   box under a small perturbation of the affine frame.
3. `density_reduction_to_ball`: for density extremization, any convex K can be
   replaced by its tube-convex-hull H ⊆ B(0,10) with density(H) ≥ density(K).
4. `deltaTube_nonempty_interior`: a δ-tube carrier has nonempty interior.
-/

noncomputable section

open MeasureTheory Metric

namespace Kakeya.Streamlined.RandomTranslation

open Kakeya.Streamlined

/-- Volume scaling under a continuous linear map. -/
theorem volume_image_linearMap (f : Point3 →L[ℝ] Point3) (s : Set Point3) :
    volume (f '' s) = ENNReal.ofReal |LinearMap.det (f : Point3 →ₗ[ℝ] Point3)| * volume s :=
  MeasureTheory.Measure.addHaar_image_continuousLinearMap volume f s


/--
If two affine isometry frames are close in both translation and linear part,
then the image of a box under the first frame is contained in the image of a
slightly enlarged box under the second frame.

Let `R_box` bound the norm of every point in the original box.
The enlargement margin is `2 * ε * (R_box + 1)`.
-/
theorem frame_box_containment
    (e e' : Point3 ≃ᵃⁱ[ℝ] Point3)
    (a b c : ℝ) (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c)
    (ε : ℝ) (hε : 0 ≤ ε)
    (h_trans : ‖e 0 - e' 0‖ ≤ ε)
    (h_lin : ‖(e.linearIsometryEquiv.toContinuousLinearMap -
                e'.linearIsometryEquiv.toContinuousLinearMap)‖ ≤ ε)
    (R_box : ℝ) (hR : ∀ x ∈ axisBox a b c, ‖x‖ ≤ R_box)
    (margin : ℝ) (hm : 2 * ε * (R_box + 1) ≤ margin) :
    e '' axisBox a b c ⊆ e' '' axisBox (a + margin) (b + margin) (c + margin) := by
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  let R_lin := e.linearIsometryEquiv
  let R'_lin := e'.linearIsometryEquiv
  let t := e 0
  let t' := e' 0
  let diff_clm : Point3 →L[ℝ] Point3 :=
    R_lin.toContinuousLinearMap - R'_lin.toContinuousLinearMap
  let z' : Point3 := e'.symm (e z)
  have h_ez' : e' z' = e z := e'.apply_symm_apply (e z)
  have h_frame_eq : ∀ (f : Point3 ≃ᵃⁱ[ℝ] Point3) (x : Point3),
      f x = f.linearIsometryEquiv x + f 0 := by
    intro f x
    have h := f.map_vadd (0 : Point3) x
    simpa using h
  have h1 : e z = R_lin z + t := h_frame_eq e z
  have h2 : z' = R'_lin.symm (e z - t') := by
    have h3 : e' z' = R'_lin z' + t' := h_frame_eq e' z'
    have h4 : e z = R'_lin z' + t' := by rw [←h_ez']; exact h3
    have h5 : R'_lin z' + t' = e z := h4.symm
    have h6 : R'_lin z' = e z - t' := by
      have h : R'_lin z' + t' = e z := h5
      calc R'_lin z'
        = R'_lin z' + t' - t' := by abel
      _ = e z - t' := by rw [h]
    have h7 : z' = R'_lin.symm (R'_lin z') := by
      exact (R'_lin.symm_apply_apply z').symm
    rw [h7, h6]
  have h_z_apply : R'_lin.symm (R'_lin z) = z := R'_lin.symm_apply_apply z
  have h_sub : z' - z = R'_lin.symm (e z - t') - z := by
    rw [h2] <;> rfl
  have h_diff1 : z' - z = R'_lin.symm ((e z - t') - R'_lin z) := by
    calc z' - z
      = R'_lin.symm (e z - t') - z := h_sub
    _ = R'_lin.symm (e z - t') - R'_lin.symm (R'_lin z) := by rw [h_z_apply]
    _ = R'_lin.symm ((e z - t') - R'_lin z) := by
      rw [← R'_lin.symm.map_sub] <;> rfl
  have h_eq : (e z - t') - R'_lin z = diff_clm z + (t - t') := by
    rw [h1]
    simp [diff_clm] <;> abel
  have h_diff : z' - z = R'_lin.symm (diff_clm z) + R'_lin.symm (t - t') := by
    rw [h_diff1, h_eq]
    rw [R'_lin.symm.map_add]
  have h_lin_bound : ‖diff_clm z‖ ≤ ε * ‖z‖ := by
    have h : ‖diff_clm z‖ ≤ ‖diff_clm‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
    exact h.trans (mul_le_mul_of_nonneg_right h_lin (norm_nonneg z))
  have h_norm_z : ‖z‖ ≤ R_box := hR z hz
  have h_orth : ‖z' - z‖ ≤ ε * (R_box + 1) := by
    have h7 : ‖z' - z‖ = ‖R'_lin.symm (diff_clm z) + R'_lin.symm (t - t')‖ := by
      rw [h_diff]
    rw [h7]
    have h8 : ‖R'_lin.symm (diff_clm z) + R'_lin.symm (t - t')‖ ≤
        ‖R'_lin.symm (diff_clm z)‖ + ‖R'_lin.symm (t - t')‖ :=
      norm_add_le _ _
    have h9 : ‖R'_lin.symm (diff_clm z)‖ = ‖diff_clm z‖ :=
      R'_lin.symm.norm_map _
    have h10 : ‖R'_lin.symm (t - t')‖ = ‖t - t'‖ := R'_lin.symm.norm_map _
    rw [h9, h10] at h8
    have h11 : ‖diff_clm z‖ + ‖t - t'‖ ≤ ε * ‖z‖ + ε := by gcongr
    have h12 : ε * ‖z‖ + ε ≤ ε * R_box + ε := by gcongr
    have h13 : ε * R_box + ε = ε * (R_box + 1) := by ring
    exact le_trans h8 (le_trans h11 (le_trans h12 (le_of_eq h13)))
  have h_coord_bound : ∀ (i : Fin 3), |(z' - z) i| ≤ ‖z' - z‖ := by
    intro i
    let e_i : Point3 := EuclideanSpace.single i 1
    have h1 : (z' - z) i = inner ℝ e_i (z' - z) := by
      simp [e_i, EuclideanSpace.inner_single_left]
    rw [h1]
    have h2 : |inner ℝ e_i (z' - z)| ≤ ‖e_i‖ * ‖z' - z‖ :=
      abs_real_inner_le_norm _ _
    have h3 : ‖e_i‖ = 1 := by
      simp [e_i]
    rw [h3] at h2
    simpa using h2
  have h_in_box : z' ∈ axisBox (a + margin) (b + margin) (c + margin) := by
    simp only [axisBox, Set.mem_setOf_eq]
    have h0 : |z 0| ≤ a / 2 := hz.1
    have h1 : |z 1| ≤ b / 2 := hz.2.1
    have h2 : |z 2| ≤ c / 2 := hz.2.2
    have h_margin2 : ε * (R_box + 1) ≤ margin / 2 := by linarith
    have h_abs : ∀ (i : Fin 3) (d : ℝ), |z i| ≤ d / 2 → |z' i| ≤ (d + margin) / 2 := by
      intro i d hdi
      have h_eq : z' i = z i + (z' - z) i := by simp
      rw [h_eq]
      have h : |z i + (z' - z) i| ≤ |z i| + |(z' - z) i| := by
        simpa [Real.norm_eq_abs] using norm_add_le (z i) ((z' - z) i)
      have h2 : |(z' - z) i| ≤ ‖z' - z‖ := h_coord_bound i
      calc |z i + (z' - z) i|
        ≤ |z i| + |(z' - z) i| := h
      _ ≤ d / 2 + ‖z' - z‖ := by gcongr
      _ ≤ d / 2 + ε * (R_box + 1) := by gcongr
      _ ≤ d / 2 + margin / 2 := by gcongr
      _ = (d + margin) / 2 := by ring
    have h0' : |z' 0| ≤ (a + margin) / 2 := h_abs 0 a hz.1
    have h1' : |z' 1| ≤ (b + margin) / 2 := h_abs 1 b hz.2.1
    have h2' : |z' 2| ≤ (c + margin) / 2 := h_abs 2 c hz.2.2
    exact ⟨h0', h1', h2'⟩
  exact ⟨z', h_in_box, h_ez'⟩


/-! ### Lemma 3: Convex hull compactness and replacement -/

/-- Set of all convex combinations `t • x + (1-t) • y` with `x ∈ A`, `y ∈ B`. -/
private def convexCombinations (A B : Set Point3) : Set Point3 :=
  {z | ∃ (x : Point3) (y : Point3) (t : ℝ), x ∈ A ∧ y ∈ B ∧ 0 ≤ t ∧ t ≤ 1 ∧ z = t • x + (1 - t) • y}

/-- The set of convex combinations of two compact sets is compact. -/
private lemma isCompact_convexCombinations {A B : Set Point3} (hA : IsCompact A) (hB : IsCompact B) :
    IsCompact (convexCombinations A B) := by
  let f : Point3 × Point3 × ℝ → Point3 := fun p => p.2.2 • p.1 + (1 - p.2.2) • p.2.1
  let K : Set (Point3 × Point3 × ℝ) := A ×ˢ B ×ˢ Set.Icc (0 : ℝ) 1
  have hK_compact : IsCompact K := hA.prod (hB.prod isCompact_Icc)
  have h_cont : Continuous f := by fun_prop
  have h_eq : convexCombinations A B = f '' K := by
    ext z
    simp only [convexCombinations, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨x, y, t, hx, hy, ht0, ht1, rfl⟩
      refine ⟨(x, (y, t)), ?_, rfl⟩
      simp only [K, Set.mem_prod, Set.mem_Icc] <;> exact ⟨hx, hy, ht0, ht1⟩
    · rintro ⟨p, hp, rfl⟩
      rcases p with ⟨x, y, t⟩
      simp only [K, Set.mem_prod, Set.mem_Icc] at hp
      rcases hp with ⟨hx, hy, ht0, ht1⟩
      exact ⟨x, y, t, hx, hy, ht0, ht1, rfl⟩
  rw [h_eq]
  exact hK_compact.image h_cont

/-- For nonempty convex A, B, `convexHull ℝ (A ∪ B)` equals the set of convex combinations. -/
private lemma convexHull_union_eq {A B : Set Point3} (hA_conv : Convex ℝ A) (hB_conv : Convex ℝ B)
    (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty) :
    convexHull ℝ (A ∪ B) = convexCombinations A B := by
  ext z
  simp only [convexCombinations, Set.mem_setOf_eq]
  constructor
  · intro hz
    have h1 : convexHull ℝ (A ∪ B) = convexJoin ℝ A B :=
      hA_conv.convexHull_union hB_conv hA_nonempty hB_nonempty
    rw [h1] at hz
    simp only [convexJoin, Set.mem_iUnion] at hz
    rcases hz with ⟨x, hx, y, hy, a, b, ha, hb, hab, rfl⟩
    refine ⟨x, y, a, hx, hy, ha, by linarith, ?_⟩
    have h_b : b = 1 - a := by linarith
    rw [h_b] <;> rfl
  · rintro ⟨x, y, t, hx, hy, ht0, ht1, rfl⟩
    have h1 : x ∈ convexHull ℝ (A ∪ B) := subset_convexHull ℝ (A ∪ B) (Or.inl hx)
    have h2 : y ∈ convexHull ℝ (A ∪ B) := subset_convexHull ℝ (A ∪ B) (Or.inr hy)
    exact (convex_convexHull ℝ (A ∪ B)) h1 h2 ht0 (by linarith) (by linarith)

/-- Convex hull of a finite union of compact convex sets is compact. -/
lemma isCompact_convexHull_finite_union {ι : Type*} (t : Finset ι) (A : ι → Set Point3)
    (hA : ∀ i ∈ t, IsCompact (A i) ∧ Convex ℝ (A i)) :
    IsCompact (convexHull ℝ (⋃ i ∈ t, A i)) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | @insert i t hi ih =>
    have h_biUnion : (⋃ j ∈ (insert i t), A j) = A i ∪ (⋃ j ∈ t, A j) := by
      ext x; simp [hi] <;> tauto
    rw [h_biUnion]
    by_cases hAi_empty : A i = ∅
    · rw [hAi_empty]
      simpa using ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
    · have hAi_nonempty : (A i).Nonempty := Set.nonempty_iff_ne_empty.mpr hAi_empty
      by_cases h_union_empty : (⋃ j ∈ t, A j) = ∅
      · rw [h_union_empty]
        simp
        have hAi_conv : Convex ℝ (A i) := (hA i (Finset.mem_insert_self i t)).2
        have h_eq : convexHull ℝ (A i) = A i := hAi_conv.convexHull_eq
        rw [h_eq]
        exact (hA i (Finset.mem_insert_self i t)).1
      · have h_union_nonempty : (⋃ j ∈ t, A j).Nonempty := Set.nonempty_iff_ne_empty.mpr h_union_empty
        have h_prev_compact : IsCompact (convexHull ℝ (⋃ j ∈ t, A j)) :=
          ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
        have h_prev_nonempty : (convexHull ℝ (⋃ j ∈ t, A j)).Nonempty :=
          h_union_nonempty.mono (subset_convexHull ℝ _)
        have hAi_conv : Convex ℝ (A i) := (hA i (Finset.mem_insert_self i t)).2
        have hAi_compact : IsCompact (A i) := (hA i (Finset.mem_insert_self i t)).1
        have h_prev_conv : Convex ℝ (convexHull ℝ (⋃ j ∈ t, A j)) := convex_convexHull ℝ _
        have h_eq1 : convexHull ℝ (A i ∪ (⋃ j ∈ t, A j)) =
            convexHull ℝ (A i ∪ convexHull ℝ (⋃ j ∈ t, A j)) := by
          let U := A i ∪ (⋃ j ∈ t, A j)
          let W := convexHull ℝ (⋃ j ∈ t, A j)
          let V := A i ∪ W
          have h1 : (⋃ j ∈ t, A j) ⊆ W := subset_convexHull ℝ _
          have hAi_sub_V : A i ⊆ V := by simp [V]
          have hUnion_sub_V : (⋃ j ∈ t, A j) ⊆ V := subset_trans h1 (by simp [V])
          have hUV : U ⊆ V := Set.union_subset hAi_sub_V hUnion_sub_V
          have hdir1 : convexHull ℝ U ⊆ convexHull ℝ V :=
            convexHull_min (subset_trans hUV (subset_convexHull ℝ V)) (convex_convexHull ℝ V)
          have hAi_sub_CHU : A i ⊆ convexHull ℝ U :=
            subset_trans (by simp [U]) (subset_convexHull ℝ U)
          have hUnion_sub_CHU : (⋃ j ∈ t, A j) ⊆ convexHull ℝ U :=
            subset_trans (by simp [U]) (subset_convexHull ℝ U)
          have hW_sub_CHU : W ⊆ convexHull ℝ U :=
            convexHull_min hUnion_sub_CHU (convex_convexHull ℝ U)
          have hV_sub_CHU : V ⊆ convexHull ℝ U := Set.union_subset hAi_sub_CHU hW_sub_CHU
          have hdir2 : convexHull ℝ V ⊆ convexHull ℝ U :=
            convexHull_min hV_sub_CHU (convex_convexHull ℝ U)
          exact Set.Subset.antisymm hdir1 hdir2
        rw [h_eq1]
        rw [convexHull_union_eq hAi_conv h_prev_conv hAi_nonempty h_prev_nonempty]
        exact isCompact_convexCombinations hAi_compact h_prev_compact

/-- Closed thickening of a compact convex set is convex. -/
lemma Convex.cthickening_of_compact {s : Set Point3} (hs : Convex ℝ s) (hsc : IsCompact s)
    {δ : ℝ} (hδ : 0 ≤ δ) : Convex ℝ (Metric.cthickening δ s) := by
  by_cases hse : s = ∅
  · rw [hse]
    have h_empty : Metric.cthickening δ (∅ : Set Point3) = ∅ := by
      ext x
      simp only [Metric.mem_cthickening_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      have h_top : Metric.infEDist x (∅ : Set Point3) = ⊤ := by simp
      rw [h_top] at h
      simpa using h
    rw [h_empty]
    exact convex_empty
  · have hne : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hse
    have h_mem_iff : ∀ (z : Point3), z ∈ Metric.cthickening δ s ↔ Metric.infDist z s ≤ δ := by
      intro z
      have h_ne_top : Metric.infEDist z s ≠ ⊤ := Metric.infEDist_ne_top hne
      have h_iff : Metric.infEDist z s ≤ ENNReal.ofReal δ ↔ Metric.infDist z s ≤ δ := by
        have h1 : (Metric.infEDist z s).toReal = Metric.infDist z s := by rfl
        have h2 : (ENNReal.ofReal δ).toReal = δ := ENNReal.toReal_ofReal hδ
        calc
          Metric.infEDist z s ≤ ENNReal.ofReal δ
            ↔ (Metric.infEDist z s).toReal ≤ (ENNReal.ofReal δ).toReal :=
              (ENNReal.toReal_le_toReal h_ne_top (by simp)).symm
          _ ↔ Metric.infDist z s ≤ δ := by rw [h1, h2]
      simpa [Metric.mem_cthickening_iff] using h_iff
    intro x hx y hy a b ha hb hab
    have h_x : Metric.infDist x s ≤ δ := (h_mem_iff x).mp hx
    have h_y : Metric.infDist y s ≤ δ := (h_mem_iff y).mp hy
    rcases hsc.exists_infDist_eq_dist hne x with ⟨p, hp, hxp⟩
    rcases hsc.exists_infDist_eq_dist hne y with ⟨q, hq, hyq⟩
    have h_xp : dist x p ≤ δ := by linarith [hxp]
    have h_yq : dist y q ≤ δ := by linarith [hyq]
    have h_pq : a • p + b • q ∈ s := hs hp hq ha hb hab
    have h_dist : dist (a • x + b • y) (a • p + b • q) ≤ a * dist x p + b * dist y q := by
      have h_add : ‖a • (x - p) + b • (y - q)‖ ≤ ‖a • (x - p)‖ + ‖b • (y - q)‖ := norm_add_le _ _
      have h_smul1 : ‖a • (x - p)‖ = a * ‖x - p‖ := by
        have h : ‖a • (x - p)‖ = |a| * ‖x - p‖ := norm_smul a (x - p)
        rw [h, abs_of_nonneg ha]
      have h_smul2 : ‖b • (y - q)‖ = b * ‖y - q‖ := by
        have h : ‖b • (y - q)‖ = |b| * ‖y - q‖ := norm_smul b (y - q)
        rw [h, abs_of_nonneg hb]
      have h_norm : ‖a • (x - p) + b • (y - q)‖ ≤ a * ‖x - p‖ + b * ‖y - q‖ := by
        rw [h_smul1, h_smul2] at h_add
        exact h_add
      have h_sub : (a • x + b • y) - (a • p + b • q) = a • (x - p) + b • (y - q) := by
        rw [smul_sub, smul_sub] <;> abel
      rw [dist_eq_norm, h_sub]
      exact h_norm
    have h_le : a * dist x p + b * dist y q ≤ δ := by
      have h1 : a * dist x p ≤ a * δ := by gcongr
      have h2 : b * dist y q ≤ b * δ := by gcongr
      have h3 : a * δ + b * δ = (a + b) * δ := by ring
      have h4 : (a + b) * δ = δ := by rw [hab]; ring
      linarith
    have h4 : Metric.infDist (a • x + b • y) s ≤ dist (a • x + b • y) (a • p + b • q) :=
      Metric.infDist_le_dist_of_mem h_pq
    have h5 : Metric.infDist (a • x + b • y) s ≤ δ := le_trans h4 (le_trans h_dist h_le)
    exact (h_mem_iff (a • x + b • y)).mpr h5

/--
For any convex K, let H be the convex hull of the union of all tube carriers
contained in K. Then H is convex, H ⊆ K, H ⊆ B(0,10), the same tubes are
contained in H and K, and volume(H) ≤ volume(K). Hence density(H) ≥ density(K).
-/
theorem density_reduction_to_ball {δ : ℝ} (G : TubeFamily δ)
    (h_support : ∀ i, (G.tube i).carrier ⊆ Metric.closedBall (0 : Point3) 10)
    (K : Set Point3) (hK : Convex ℝ K) :
    ∃ (H : Set Point3),
      Convex ℝ H ∧
      IsCompact H ∧
      H ⊆ Metric.closedBall (0 : Point3) 10 ∧
      H ⊆ K ∧
      (∀ i, (G.tube i).carrier ⊆ K ↔ (G.tube i).carrier ⊆ H) ∧
      G.toBodyFamily.containedMass H = G.toBodyFamily.containedMass K ∧
      volume H ≤ volume K := by
  let S : Set Point3 := {x | ∃ (i : Fin G.card), (G.tube i).carrier ⊆ K ∧ x ∈ (G.tube i).carrier}
  let H : Set Point3 := convexHull ℝ S
  have h_tube_compact_conv : ∀ i, IsCompact (G.tube i).carrier ∧ Convex ℝ (G.tube i).carrier := by
    intro i
    let seg := Kakeya.unitSegment (G.tube i).base (G.tube i).direction
    have h_seg_compact : IsCompact seg := by
      have h_cont : Continuous (fun t : ℝ => (G.tube i).base + t • (G.tube i).direction) := by fun_prop
      exact isCompact_Icc.image h_cont
    have h_seg_convex : Convex ℝ seg := by
      intro x hx y hy a b ha hb hab
      rcases hx with ⟨t1, ht1, rfl⟩
      rcases hy with ⟨t2, ht2, rfl⟩
      let base := (G.tube i).base
      let dir := (G.tube i).direction
      have ht : a * t1 + b * t2 ∈ Set.Icc (0 : ℝ) 1 :=
        convex_Icc (0 : ℝ) 1 ht1 ht2 ha hb hab
      have h1 : a • (base + t1 • dir) = a • base + (a * t1) • dir := by
        rw [smul_add, mul_smul]
      have h2 : b • (base + t2 • dir) = b • base + (b * t2) • dir := by
        rw [smul_add, mul_smul]
      have h_main : a • (base + t1 • dir) + b • (base + t2 • dir) =
          base + (a * t1 + b * t2) • dir := by
        rw [h1, h2]
        have h3 : a • base + (a * t1) • dir + (b • base + (b * t2) • dir) =
            (a + b) • base + (a * t1 + b * t2) • dir := by
          simp [add_smul, smul_add] <;> abel
        rw [h3, hab]
        <;> simp
      exact ⟨a * t1 + b * t2, ht, h_main.symm⟩
    have h_carrier_compact : IsCompact (G.tube i).carrier := h_seg_compact.cthickening (r := δ)
    have h_carrier_convex : Convex ℝ (G.tube i).carrier := h_seg_convex.cthickening δ
    exact ⟨h_carrier_compact, h_carrier_convex⟩
  let idx : Set (Fin G.card) := {i | (G.tube i).carrier ⊆ K}
  have h_idx_finite : Set.Finite idx := Set.toFinite _
  let idx' : Finset (Fin G.card) := h_idx_finite.toFinset
  have h_idx'_eq : (idx' : Set (Fin G.card)) = idx := h_idx_finite.coe_toFinset
  have hS_eq : S = ⋃ i ∈ idx', (G.tube i).carrier := by
    ext x; simp [S, idx, idx', h_idx'_eq] <;> tauto
  have hH_compact : IsCompact H := by
    rw [show H = convexHull ℝ S from rfl, hS_eq]
    exact isCompact_convexHull_finite_union idx' (fun i => (G.tube i).carrier)
      (fun i _ => h_tube_compact_conv i)
  have hS_sub_K : S ⊆ K := by
    intro x hx
    rcases hx with ⟨i, h_i_sub_K, hxi⟩
    exact h_i_sub_K hxi
  have hH_convex : Convex ℝ H := convex_convexHull ℝ S
  have hH_sub_K : H ⊆ K := convexHull_min hS_sub_K hK
  have hS_sub_ball : S ⊆ Metric.closedBall (0 : Point3) 10 := by
    intro x hx
    rcases hx with ⟨i, _h_i_sub_K, hxi⟩
    exact h_support i hxi
  have h_ball_convex : Convex ℝ (Metric.closedBall (0 : Point3) 10) := convex_closedBall (0 : Point3) 10
  have hH_sub_ball : H ⊆ Metric.closedBall (0 : Point3) 10 := convexHull_min hS_sub_ball h_ball_convex
  have h_tube_iff : ∀ i, (G.tube i).carrier ⊆ K ↔ (G.tube i).carrier ⊆ H := by
    intro i
    constructor
    · intro h
      have h_tube_sub_S : (G.tube i).carrier ⊆ S := by
        intro x hx
        exact ⟨i, h, hx⟩
      exact subset_trans h_tube_sub_S (subset_convexHull ℝ S)
    · intro h
      exact subset_trans h hH_sub_K
  have h_body_eq : ∀ i, (G.toBodyFamily.body i).carrier = (G.tube i).carrier := by
    intro i; rfl
  have h_idx_eq : G.toBodyFamily.containedIndices H = G.toBodyFamily.containedIndices K := by
    apply Finset.ext
    intro i
    classical
    have h7 : (G.toBodyFamily.body i).carrier = (G.tube i).carrier := h_body_eq i
    have h8 : ((G.toBodyFamily.body i).carrier ⊆ H) ↔ ((G.toBodyFamily.body i).carrier ⊆ K) := by
      constructor
      · intro h
        have h9 : (G.tube i).carrier ⊆ H := by exact h7 ▸ h
        have h10 : (G.tube i).carrier ⊆ K := (h_tube_iff i).mpr h9
        exact h7 ▸ h10
      · intro h
        have h9 : (G.tube i).carrier ⊆ K := by exact h7 ▸ h
        have h10 : (G.tube i).carrier ⊆ H := (h_tube_iff i).mp h9
        exact h7 ▸ h10
    simpa [BodyFamily.containedIndices, Finset.mem_filter] using h8
  have h_mass_eq : G.toBodyFamily.containedMass H = G.toBodyFamily.containedMass K := by
    rw [BodyFamily.containedMass, BodyFamily.containedMass, h_idx_eq]
  have h_vol_le : volume H ≤ volume K := measure_mono hH_sub_K
  exact ⟨H, hH_convex, hH_compact, hH_sub_ball, hH_sub_K, h_tube_iff, h_mass_eq, h_vol_le⟩

/-- A δ-tube (δ > 0) contains an open ball of radius δ around its base point,
so its carrier has nonempty interior. -/
theorem deltaTube_nonempty_interior {δ : ℝ} (hδ : 0 < δ)
    (T : Kakeya.DeltaTube δ) :
    Set.Nonempty (interior T.carrier) := by
  have h_base_in_seg : T.base ∈ Kakeya.unitSegment T.base T.direction := by
    refine ⟨0, by norm_num, ?_⟩
    simp
  have h_ball_sub : Metric.ball T.base δ ⊆ T.carrier := by
    intro x hx
    have h_dist : dist x T.base < δ := hx
    have h1 : Metric.infEDist x (Kakeya.unitSegment T.base T.direction) ≤
        edist x T.base := Metric.infEDist_le_edist_of_mem h_base_in_seg
    have h2 : edist x T.base = ENNReal.ofReal (dist x T.base) := by
      rw [edist_dist]
    rw [h2] at h1
    have h3 : ENNReal.ofReal (dist x T.base) ≤ ENNReal.ofReal δ := by
      gcongr
      <;> linarith
    exact h1.trans h3
  have h3 : Metric.ball T.base δ ⊆ interior T.carrier :=
    interior_maximal h_ball_sub isOpen_ball
  have h4 : (T.base : Point3) ∈ Metric.ball T.base δ := by
    simp [hδ]
  exact ⟨T.base, h3 h4⟩

end Kakeya.Streamlined.RandomTranslation
