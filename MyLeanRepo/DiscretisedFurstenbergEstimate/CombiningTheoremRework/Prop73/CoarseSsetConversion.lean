module

/-
  Coarse S-set conversion lemma.

  Converts IsDeltaSSet on the fine point set (at coarse scale δ_m) to
  IsFinsetDeltaSSet on the coarse DSquare corner set.

  DSquare metric is sup norm on ℝ×ℝ; Plane metric is Euclidean.
  Conversion factor: sup-norm ball of radius r → Euclidean ball of radius √2·r.

  C_coarse = 81 * K * C_between * (2*√2)^s

  Whiteprint node: combining_theorem_rework / coarse_sset_conversion
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GeometricIntersection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.B1_Sublemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction.GeometricAndExternal
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.GoodTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CleanSquareLemmas
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
open DiscretisedFurstenbergEstimate.InductionOnScales

attribute [local instance] Classical.propDecidable

/-- At most 9 DSquares in a δ-ball (sup norm on grid corners). -/
lemma dsquare_ball_at_most_9 {m : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_eq : δ = dyadicDelta m) (c : DSquare m) (S : Finset (DSquare m)) :
    (S.filter (fun q => dist q c ≤ δ)).card ≤ 9 := by
  let i0 := c.i
  let j0 := c.j
  let grid : Finset (DSquare m) :=
    (Finset.Icc (i0 - 1) (i0 + 1)).biUnion fun i =>
      (Finset.Icc (j0 - 1) (j0 + 1)).image (fun j => (⟨i, j⟩ : DSquare m))
  have h1 : S.filter (fun q => dist q c ≤ δ) ⊆ grid := by
    intro q hq
    have h2 : dist q c ≤ δ := (Finset.mem_filter.mp hq).2
    have h_def : dist q c = dist q.toPoint c.toPoint := by rfl
    have h_max : dist q.toPoint c.toPoint = max (dist q.toPoint.1 c.toPoint.1) (dist q.toPoint.2 c.toPoint.2) := by exact Prod.dist_eq
    have hδ_def : DiscretisedFurstenbergEstimate.δ m = dyadicDelta m := by
      simp [DiscretisedFurstenbergEstimate.δ, dyadicDelta, Real.rpow_neg] <;> field_simp <;> norm_cast
    have h21 : dist q.toPoint.1 c.toPoint.1 = |(q.i : ℝ) - (c.i : ℝ)| * δ := by
      have h : dist q.toPoint.1 c.toPoint.1 = |(q.i : ℝ) * dyadicDelta m - (c.i : ℝ) * dyadicDelta m| := by
        rw [Real.dist_eq]
        have h' : q.toPoint.1 = (q.i : ℝ) * DiscretisedFurstenbergEstimate.δ m := by
          simp [DSquare.toPoint] <;> rfl
        have h'' : c.toPoint.1 = (c.i : ℝ) * DiscretisedFurstenbergEstimate.δ m := by
          simp [DSquare.toPoint] <;> rfl
        rw [h', h'', hδ_def]
      rw [h]
      have h2 : (q.i : ℝ) * dyadicDelta m - (c.i : ℝ) * dyadicDelta m = ((q.i : ℝ) - (c.i : ℝ)) * δ := by
        rw [←hδ_eq] <;> ring
      rw [h2, abs_mul]
      have h3 : |((q.i : ℝ) - (c.i : ℝ))| * |δ| = |(q.i : ℝ) - (c.i : ℝ)| * δ := by
        rw [abs_of_pos hδ_pos] <;> ring
      exact h3
    have h22 : dist q.toPoint.2 c.toPoint.2 = |(q.j : ℝ) - (c.j : ℝ)| * δ := by
      have h : dist q.toPoint.2 c.toPoint.2 = |(q.j : ℝ) * dyadicDelta m - (c.j : ℝ) * dyadicDelta m| := by
        rw [Real.dist_eq]
        have h' : q.toPoint.2 = (q.j : ℝ) * DiscretisedFurstenbergEstimate.δ m := by
          simp [DSquare.toPoint] <;> rfl
        have h'' : c.toPoint.2 = (c.j : ℝ) * DiscretisedFurstenbergEstimate.δ m := by
          simp [DSquare.toPoint] <;> rfl
        rw [h', h'', hδ_def]
      rw [h]
      have h2 : (q.j : ℝ) * dyadicDelta m - (c.j : ℝ) * dyadicDelta m = ((q.j : ℝ) - (c.j : ℝ)) * δ := by
        rw [←hδ_eq] <;> ring
      rw [h2, abs_mul]
      have h3 : |((q.j : ℝ) - (c.j : ℝ))| * |δ| = |(q.j : ℝ) - (c.j : ℝ)| * δ := by
        rw [abs_of_pos hδ_pos] <;> ring
      exact h3
    have h_dist_eq : dist q c = max (|(q.i : ℝ) - (c.i : ℝ)| * δ) (|(q.j : ℝ) - (c.j : ℝ)| * δ) := by
      rw [h_def, h_max, h21, h22]
    rw [h_dist_eq] at h2
    have h7 : |(q.i : ℝ) - (c.i : ℝ)| ≤ 1 := by
      have h8 : |(q.i : ℝ) - (c.i : ℝ)| * δ ≤ max (|(q.i : ℝ) - (c.i : ℝ)| * δ) (|(q.j : ℝ) - (c.j : ℝ)| * δ) := le_max_left _ _
      have h9 : |(q.i : ℝ) - (c.i : ℝ)| * δ ≤ δ := by linarith
      nlinarith [abs_nonneg ((q.i : ℝ) - (c.i : ℝ))]
    have h9 : |(q.j : ℝ) - (c.j : ℝ)| ≤ 1 := by
      have h10 : |(q.j : ℝ) - (c.j : ℝ)| * δ ≤ max (|(q.i : ℝ) - (c.i : ℝ)| * δ) (|(q.j : ℝ) - (c.j : ℝ)| * δ) := le_max_right _ _
      have h11 : |(q.j : ℝ) - (c.j : ℝ)| * δ ≤ δ := by linarith
      nlinarith [abs_nonneg ((q.j : ℝ) - (c.j : ℝ))]
    have h14 : c.i - 1 ≤ q.i := by
      have h : (c.i : ℝ) - 1 ≤ (q.i : ℝ) := by linarith [abs_le.mp h7]
      exact_mod_cast h
    have h15 : q.i ≤ c.i + 1 := by
      have h : (q.i : ℝ) ≤ (c.i : ℝ) + 1 := by linarith [abs_le.mp h7]
      exact_mod_cast h
    have h16 : c.j - 1 ≤ q.j := by
      have h : (c.j : ℝ) - 1 ≤ (q.j : ℝ) := by linarith [abs_le.mp h9]
      exact_mod_cast h
    have h17 : q.j ≤ c.j + 1 := by
      have h : (q.j : ℝ) ≤ (c.j : ℝ) + 1 := by linarith [abs_le.mp h9]
      exact_mod_cast h
    have h18 : q.i ∈ Finset.Icc (i0 - 1) (i0 + 1) := by
      simp only [Finset.mem_Icc]; exact ⟨h14, h15⟩
    have h19 : q.j ∈ Finset.Icc (j0 - 1) (j0 + 1) := by
      simp only [Finset.mem_Icc]; exact ⟨h16, h17⟩
    exact Finset.mem_biUnion.mpr ⟨q.i, h18, Finset.mem_image.mpr ⟨q.j, h19, by cases q <;> simp <;> rfl⟩⟩
  have h_grid_card : grid.card ≤ 9 := by
    have h13 : grid.card ≤ ∑ i ∈ Finset.Icc (i0 - 1) (i0 + 1),
        ((Finset.Icc (j0 - 1) (j0 + 1)).image (fun j : ℤ => (⟨i, j⟩ : DSquare m))).card :=
      Finset.card_biUnion_le
    have h14 : ∀ i, ((Finset.Icc (j0 - 1) (j0 + 1)).image (fun j : ℤ => (⟨i, j⟩ : DSquare m))).card = 3 := by
      intro i
      have h_inj : Function.Injective (fun j : ℤ => (⟨i, j⟩ : DSquare m)) := by
        intro j1 j2 h
        simpa [DSquare.mk] using h
      rw [Finset.card_image_of_injective _ h_inj]
      simp [Finset.Icc_self]
      <;> omega
    have h15 : (Finset.Icc (i0 - 1) (i0 + 1)).card = 3 := by simp <;> omega
    calc grid.card
      ≤ ∑ i ∈ Finset.Icc (i0 - 1) (i0 + 1), _ := h13
    _ = ∑ i ∈ Finset.Icc (i0 - 1) (i0 + 1), 3 := by
        apply Finset.sum_congr rfl; intro i _; exact h14 i
    _ = 3 * 3 := by rw [Finset.sum_const, h15] <;> ring
    _ = 9 := by norm_num
  exact le_trans (Finset.card_le_card h1) h_grid_card

/-- Helper: for any finite cover C, |S| ≤ 9 * |C|. -/
lemma grid_packing_helper {m : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_eq : δ = dyadicDelta m) (S : Finset (DSquare m))
    (C : Finset (DSquare m))
    (hcover : (S : Set (DSquare m)) ⊆ ⋃ c ∈ C, Metric.closedBall c δ.toNNReal) :
    S.card ≤ 9 * C.card := by
  let S_c (c : DSquare m) : Finset (DSquare m) := S.filter (fun q => dist q c ≤ δ)
  have h3 : ∀ c ∈ C, (S_c c).card ≤ 9 := by
    intro c _
    exact dsquare_ball_at_most_9 hδ_pos hδ_eq c S
  have h4 : S ⊆ C.biUnion S_c := by
    intro q hq
    have h5 : q ∈ (S : Set (DSquare m)) := hq
    have h6 : q ∈ ⋃ c ∈ C, Metric.closedBall c δ.toNNReal := hcover h5
    rcases Set.mem_iUnion₂.mp h6 with ⟨c, hc, hball⟩
    have h7 : dist q c ≤ δ := by
      have hε : (δ.toNNReal : ℝ) = δ := by
        simp [NNReal.coe_mk, hδ_pos.le] <;> linarith
      have hdist : dist q c ≤ (δ.toNNReal : ℝ) := by exact dist_le_coe.mpr hball
      rw [hε] at hdist
      exact hdist
    have h8 : q ∈ S_c c := Finset.mem_filter.mpr ⟨hq, h7⟩
    exact Finset.mem_biUnion.mpr ⟨c, hc, h8⟩
  have h5 : S.card ≤ (C.biUnion S_c).card := Finset.card_le_card h4
  have h6 : (C.biUnion S_c).card ≤ ∑ c ∈ C, (S_c c).card := Finset.card_biUnion_le
  have h7 : ∑ c ∈ C, (S_c c).card ≤ ∑ c ∈ C, 9 := by
    apply Finset.sum_le_sum; intro c hc; exact h3 c hc
  have h8 : ∑ c ∈ C, (9 : ℕ) = 9 * C.card := by
    simp [Finset.sum_const] <;> ring
  rw [h8] at h7
  exact le_trans (le_trans h5 h6) h7

/-- Grid packing: |S| ≤ 9 * Ncover(δ, S) for any finset of DSquares. -/
lemma grid_packing_dsquare {m : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_eq : δ = dyadicDelta m) (S : Finset (DSquare m)) :
    (S.card : ENNReal) ≤ (9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal (S : Set (DSquare m)) := by
  let ε : NNReal := δ.toNNReal
  have h_main : ∀ (C : Set (DSquare m)), Metric.IsCover ε (S : Set (DSquare m)) C →
      (S.card : ENNReal) / 9 ≤ (C.encard : ENNReal) := by
    intro C hC
    by_cases hCfin : Set.Finite C
    · let Cfin := hCfin.toFinset
      have h2 : (Cfin : Set (DSquare m)) = C := Set.Finite.coe_toFinset _
      have h3 : (S : Set (DSquare m)) ⊆ ⋃ c ∈ Cfin, Metric.closedBall c ε := by
        have h4 := hC.subset_iUnion_closedBall
        rw [←h2] at h4
        exact h4
      have h4 : S.card ≤ 9 * Cfin.card := grid_packing_helper hδ_pos hδ_eq S Cfin h3
      have h5 : (S.card : ENNReal) ≤ (9 : ENNReal) * (Cfin.card : ENNReal) := by exact_mod_cast h4
      have h6 : (C.encard : ENNReal) = (Cfin.card : ENNReal) := by
        have h7 : C.encard = (Cfin.card : ENat) := by rw [←h2]; simp
        rw [h7] <;> norm_cast
      rw [h6]
      calc (S.card : ENNReal) / 9
        ≤ ((9 : ENNReal) * (Cfin.card : ENNReal)) / 9 := by gcongr
      _ = (Cfin.card : ENNReal) := by
        have h_comm : (9 : ENNReal) * (Cfin.card : ENNReal) = (Cfin.card : ENNReal) * (9 : ENNReal) := by ring
        rw [h_comm]
        exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
    · have h6 : C.encard = ⊤ := by rw [Set.encard_eq_top_iff]; exact hCfin
      rw [h6] <;> simp
  have h4 : (S.card : ENNReal) / 9 ≤ (Metric.externalCoveringNumber ε (S : Set (DSquare m)) : ENNReal) := by
    simpa [Metric.externalCoveringNumber] using le_iInf₂ h_main
  have h5 : ((S.card : ENNReal) / 9) * 9 ≤ (Metric.externalCoveringNumber ε (S : Set (DSquare m)) : ENNReal) * 9 := by
    gcongr
  have h6 : ((S.card : ENNReal) / 9) * 9 = (S.card : ENNReal) := by
    exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
  have h7 : (S.card : ENNReal) ≤ (9 : ENNReal) * (Metric.externalCoveringNumber ε (S : Set (DSquare m)) : ENNReal) := by
    have h8 : (Metric.externalCoveringNumber ε (S : Set (DSquare m)) : ENNReal) * 9 = (9 : ENNReal) * (Metric.externalCoveringNumber ε (S : Set (DSquare m)) : ENNReal) := by ring
    rw [h8] at h5
    rw [h6] at h5
    exact h5
  exact h7

/-- Local bound: number of coarse corners in sup-norm ball ≤ 9 * Ncover(pointSet ∩ enlarged Euclidean ball). -/
lemma local_corners_bound
    {k m : ℕ} (hnm : m ≤ k)
    {s C₁ C₂ : ℝ} {M MΔ : ℕ}
    (config : CombiningTheorem.NiceConfiguration k s C₁ M)
    (P : Finset (DyadicSquare k))
    (hP_sub : P ⊆ config.P₀)
    (coarseConfig : CombiningTheorem.NiceConfiguration m s C₂ MΔ)
    (hcoarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_eq : δ = dyadicDelta m)
    (p : DSquare m) (r : ℝ) (hr : δ ≤ r) :
    (((finsetDyadicToDSquare coarseConfig.P₀).filter (fun q => dist q p ≤ r)).card : ENNReal) ≤
      (9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal
        (config.pointSet ∩ Metric.closedBall (dSquareCorner δ p) (Real.sqrt 2 * (r + δ))) := by
  let S := finsetDyadicToDSquare coarseConfig.P₀
  let localS := S.filter (fun q => dist q p ≤ r)
  let x := dSquareCorner δ p
  let R := Real.sqrt 2 * (r + δ)
  let ε : NNReal := δ.toNNReal
  have h_main : ∀ (C : Set Plane), Metric.IsCover ε (config.pointSet ∩ Metric.closedBall x R) C →
      (localS.card : ENNReal) / 9 ≤ (C.encard : ENNReal) := by
    intro C hC
    by_cases hCfin : Set.Finite C
    · let Cfin := hCfin.toFinset
      have h2 : (Cfin : Set Plane) = C := Set.Finite.coe_toFinset _
      let Q_c (c : Plane) : Finset (DSquare m) :=
        localS.filter (fun q =>
          ((dSquareToDyadicSquare q).toSet : Set Plane) ∩ Metric.closedBall c δ ≠ ∅)
      have h3 : ∀ c ∈ Cfin, (Q_c c).card ≤ 9 := by
        intro c _
        rcases ball_intersects_at_most_9_squares c δ hδ_pos hδ_eq with ⟨I, hI9, hI_mem⟩
        let I' : Finset (DSquare m) := I.image dyadicSquareToDSquare
        have h4 : Q_c c ⊆ I' := by
          intro q hq
          have h6 : ((dSquareToDyadicSquare q).toSet : Set Plane) ∩ Metric.closedBall c δ ≠ ∅ :=
            (Finset.mem_filter.mp hq).2
          have h7 : dSquareToDyadicSquare q ∈ I := hI_mem (dSquareToDyadicSquare q) h6
          exact Finset.mem_image.mpr ⟨dSquareToDyadicSquare q, h7, rfl⟩
        have h5 : (Q_c c).card ≤ I'.card := Finset.card_le_card h4
        have h6 : I'.card ≤ I.card := Finset.card_image_le
        linarith
      have h4 : localS ⊆ Cfin.biUnion Q_c := by
        intro q hq
        have hq' : q ∈ S := (Finset.mem_filter.mp hq).1
        have hq_dist : dist q p ≤ r := (Finset.mem_filter.mp hq).2
        have hq_coarse : dSquareToDyadicSquare q ∈ coarseConfig.P₀ := by
          have h1 : q ∈ S := hq'
          rcases Finset.mem_image.mp h1 with ⟨Q_coarse, hQ_in, rfl⟩
          simpa [dSquareToDyadicSquare, dyadicSquareToDSquare] using hQ_in
        rcases Finset.mem_image.mp (by rw [hcoarse_P_eq] at hq_coarse; exact hq_coarse) with ⟨p_fine, hp_fine, h_eq⟩
        have h5 : p_fine ∈ P := hp_fine
        have h6 : p_fine ∈ config.P₀ := hP_sub h5
        have h7 : (p_fine.toSet : Set Plane) ⊆ config.pointSet := by
          intro z hz
          exact Set.mem_iUnion₂.mpr ⟨p_fine, h6, hz⟩
        have h8 : (p_fine.toSet : Set Plane).Nonempty := by
          let z0 : Plane := ep ((p_fine.i : ℝ) * dyadicDelta k) ((p_fine.j : ℝ) * dyadicDelta k)
          have hdk_pos : 0 < dyadicDelta k := dyadicDelta_pos k
          have hz0 : z0 ∈ (p_fine.toSet : Set Plane) := by
            simp only [DyadicSquare.toSet, Set.mem_setOf_eq]
            have h1 : (p_fine.i : ℝ) * dyadicDelta k ≤ z0 0 := by
              simp [z0, ep] <;> linarith
            have h2 : z0 0 < ((p_fine.i : ℝ) + 1) * dyadicDelta k := by
              simp [z0, ep] <;> linarith [hdk_pos]
            have h3 : (p_fine.j : ℝ) * dyadicDelta k ≤ z0 1 := by
              simp [z0, ep] <;> linarith
            have h4 : z0 1 < ((p_fine.j : ℝ) + 1) * dyadicDelta k := by
              simp [z0, ep] <;> linarith [hdk_pos]
            exact ⟨h1, h2, h3, h4⟩
          exact ⟨z0, hz0⟩
        have h10 : InductionConfigurations.containingSquare hnm p_fine = dSquareToDyadicSquare q := by
          simpa [dSquareToDyadicSquare, dyadicSquareToDSquare] using h_eq
        have h9 : (p_fine.toSet : Set Plane) ⊆ (InductionConfigurations.containingSquare hnm p_fine).toSet :=
          fine_square_subset_coarse hnm p_fine
        rw [h10] at h9
        rcases h8 with ⟨z, hz⟩
        have hz1 : z ∈ config.pointSet := h7 hz
        have hz2 : z ∈ (dSquareToDyadicSquare q).toSet := h9 hz
        let q_corner := dSquareCorner δ q
        have h10_dist : dist z q_corner ≤ Real.sqrt 2 * δ := by
          have h11 : z ∈ (dSquareToDyadicSquare q).toSet := hz2
          have h12 : 0 ≤ z 0 - (q.i : ℝ) * δ := by
            have h13 : ((dSquareToDyadicSquare q).i : ℝ) * dyadicDelta m ≤ z 0 := h11.1
            have h14 : (dSquareToDyadicSquare q).i = q.i := by simp [dSquareToDyadicSquare]
            rw [h14] at h13
            rw [←hδ_eq] at h13
            linarith
          have h13 : z 0 - (q.i : ℝ) * δ < δ := by
            have h14 : z 0 < ((dSquareToDyadicSquare q).i : ℝ) * dyadicDelta m + dyadicDelta m := by
              have h15 : z 0 < ((dSquareToDyadicSquare q).i + 1 : ℝ) * dyadicDelta m := h11.2.1
              have h16 : ((dSquareToDyadicSquare q).i + 1 : ℝ) * dyadicDelta m =
                  ((dSquareToDyadicSquare q).i : ℝ) * dyadicDelta m + dyadicDelta m := by ring
              rw [h16] at h15; exact h15
            have h17 : (dSquareToDyadicSquare q).i = q.i := by simp [dSquareToDyadicSquare]
            rw [h17] at h14
            rw [←hδ_eq] at h14
            linarith
          have h14 : 0 ≤ z 1 - (q.j : ℝ) * δ := by
            have h15 : ((dSquareToDyadicSquare q).j : ℝ) * dyadicDelta m ≤ z 1 := h11.2.2.1
            have h16 : (dSquareToDyadicSquare q).j = q.j := by simp [dSquareToDyadicSquare]
            rw [h16] at h15
            rw [←hδ_eq] at h15
            linarith
          have h15 : z 1 - (q.j : ℝ) * δ < δ := by
            have h16 : z 1 < ((dSquareToDyadicSquare q).j : ℝ) * dyadicDelta m + dyadicDelta m := by
              have h17 : z 1 < ((dSquareToDyadicSquare q).j + 1 : ℝ) * dyadicDelta m := h11.2.2.2
              have h18 : ((dSquareToDyadicSquare q).j + 1 : ℝ) * dyadicDelta m =
                  ((dSquareToDyadicSquare q).j : ℝ) * dyadicDelta m + dyadicDelta m := by ring
              rw [h18] at h17; exact h17
            have h19 : (dSquareToDyadicSquare q).j = q.j := by simp [dSquareToDyadicSquare]
            rw [h19] at h16
            rw [←hδ_eq] at h16
            linarith
          have h16 : (z 0 - (q.i : ℝ) * δ) ^ 2 ≤ δ ^ 2 := by nlinarith
          have h17 : (z 1 - (q.j : ℝ) * δ) ^ 2 ≤ δ ^ 2 := by nlinarith
          have h18 : dist z q_corner ^ 2 = (z 0 - (q.i : ℝ) * δ) ^ 2 + (z 1 - (q.j : ℝ) * δ) ^ 2 := by
            have h19 := EuclideanSpace.dist_sq_eq z q_corner
            rw [h19]
            simp [Fin.sum_univ_two, Real.dist_eq, q_corner, dSquareCorner, ep] <;> ring
          have h20 : dist z q_corner ^ 2 ≤ (Real.sqrt 2 * δ) ^ 2 := by
            rw [h18]
            have h21 : (Real.sqrt 2 * δ) ^ 2 = 2 * δ ^ 2 := by
              calc (Real.sqrt 2 * δ) ^ 2 = (Real.sqrt 2) ^ 2 * δ ^ 2 := by ring
                _ = 2 * δ ^ 2 := by rw [Real.sq_sqrt (by norm_num)] <;> ring
            rw [h21]
            linarith [h16, h17]
          have h22 : 0 ≤ dist z q_corner := by positivity
          have h23 : 0 ≤ Real.sqrt 2 * δ := by positivity
          have h24 : |dist z q_corner| ≤ |Real.sqrt 2 * δ| := sq_le_sq.mp h20
          rw [abs_of_nonneg h22, abs_of_nonneg h23] at h24
          exact h24
        have h11_dist : dist q_corner x ≤ Real.sqrt 2 * r := by
          have h_def : dist q p = dist q.toPoint p.toPoint := by rfl
          have h_max : dist q.toPoint p.toPoint = max (dist q.toPoint.1 p.toPoint.1) (dist q.toPoint.2 p.toPoint.2) := by exact Prod.dist_eq
          have hδ_def2 : DiscretisedFurstenbergEstimate.δ m = dyadicDelta m := by
            simp [DiscretisedFurstenbergEstimate.δ, dyadicDelta, Real.rpow_neg] <;> field_simp <;> norm_cast
          have h21 : dist q.toPoint.1 p.toPoint.1 = |(q.i : ℝ) - (p.i : ℝ)| * δ := by
            have h : dist q.toPoint.1 p.toPoint.1 = |(q.i : ℝ) * dyadicDelta m - (p.i : ℝ) * dyadicDelta m| := by
              rw [Real.dist_eq]
              have h' : q.toPoint.1 = (q.i : ℝ) * DiscretisedFurstenbergEstimate.δ m := by
                simp [DSquare.toPoint] <;> rfl
              have h'' : p.toPoint.1 = (p.i : ℝ) * DiscretisedFurstenbergEstimate.δ m := by
                simp [DSquare.toPoint] <;> rfl
              rw [h', h'', hδ_def2]
            rw [h]
            have h2 : (q.i : ℝ) * dyadicDelta m - (p.i : ℝ) * dyadicDelta m = ((q.i : ℝ) - (p.i : ℝ)) * δ := by
              rw [←hδ_eq] <;> ring
            rw [h2, abs_mul]
            have h3 : |((q.i : ℝ) - (p.i : ℝ))| * |δ| = |(q.i : ℝ) - (p.i : ℝ)| * δ := by
              rw [abs_of_pos hδ_pos] <;> ring
            exact h3
          have h22 : dist q.toPoint.2 p.toPoint.2 = |(q.j : ℝ) - (p.j : ℝ)| * δ := by
            have h : dist q.toPoint.2 p.toPoint.2 = |(q.j : ℝ) * dyadicDelta m - (p.j : ℝ) * dyadicDelta m| := by
              rw [Real.dist_eq]
              have h' : q.toPoint.2 = (q.j : ℝ) * DiscretisedFurstenbergEstimate.δ m := by
                simp [DSquare.toPoint] <;> rfl
              have h'' : p.toPoint.2 = (p.j : ℝ) * DiscretisedFurstenbergEstimate.δ m := by
                simp [DSquare.toPoint] <;> rfl
              rw [h', h'', hδ_def2]
            rw [h]
            have h2 : (q.j : ℝ) * dyadicDelta m - (p.j : ℝ) * dyadicDelta m = ((q.j : ℝ) - (p.j : ℝ)) * δ := by
              rw [←hδ_eq] <;> ring
            rw [h2, abs_mul]
            have h3 : |((q.j : ℝ) - (p.j : ℝ))| * |δ| = |(q.j : ℝ) - (p.j : ℝ)| * δ := by
              rw [abs_of_pos hδ_pos] <;> ring
            exact h3
          have h_dist_eq : dist q p = max (|(q.i : ℝ) - (p.i : ℝ)| * δ) (|(q.j : ℝ) - (p.j : ℝ)| * δ) := by
            rw [h_def, h_max, h21, h22]
          have h12 : |(q.i : ℝ) - (p.i : ℝ)| * δ ≤ dist q p := by
            rw [h_dist_eq]; exact le_max_left _ _
          have h13 : |(q.j : ℝ) - (p.j : ℝ)| * δ ≤ dist q p := by
            rw [h_dist_eq]; exact le_max_right _ _
          have h14 : |(q.i : ℝ) - (p.i : ℝ)| * δ ≤ r := by linarith
          have h15 : |(q.j : ℝ) - (p.j : ℝ)| * δ ≤ r := by linarith
          have h16 : ((q.i : ℝ) - (p.i : ℝ)) ^ 2 * δ ^ 2 = (|(q.i : ℝ) - (p.i : ℝ)| * δ) ^ 2 := by
            calc ((q.i : ℝ) - (p.i : ℝ)) ^ 2 * δ ^ 2
              = (|(q.i : ℝ) - (p.i : ℝ)|) ^ 2 * δ ^ 2 := by rw [sq_abs]
            _ = (|(q.i : ℝ) - (p.i : ℝ)| * δ) ^ 2 := by ring
          have h17 : ((q.j : ℝ) - (p.j : ℝ)) ^ 2 * δ ^ 2 = (|(q.j : ℝ) - (p.j : ℝ)| * δ) ^ 2 := by
            calc ((q.j : ℝ) - (p.j : ℝ)) ^ 2 * δ ^ 2
              = (|(q.j : ℝ) - (p.j : ℝ)|) ^ 2 * δ ^ 2 := by rw [sq_abs]
            _ = (|(q.j : ℝ) - (p.j : ℝ)| * δ) ^ 2 := by ring
          have h18 : ((q.i : ℝ) - (p.i : ℝ)) ^ 2 * δ ^ 2 ≤ r ^ 2 := by
            rw [h16]; gcongr
          have h19 : ((q.j : ℝ) - (p.j : ℝ)) ^ 2 * δ ^ 2 ≤ r ^ 2 := by
            rw [h17]; gcongr
          have hr_pos : 0 < r := by linarith [hδ_pos]
          have h20 : dist q_corner x ^ 2 = ((q.i : ℝ) - (p.i : ℝ)) ^ 2 * δ ^ 2 + ((q.j : ℝ) - (p.j : ℝ)) ^ 2 * δ ^ 2 := by
            have h21 := EuclideanSpace.dist_sq_eq q_corner x
            rw [h21]
            simp [Fin.sum_univ_two, Real.dist_eq, q_corner, x, dSquareCorner, ep] <;> ring
          have h22 : ((q.i : ℝ) - (p.i : ℝ)) ^ 2 * δ ^ 2 + ((q.j : ℝ) - (p.j : ℝ)) ^ 2 * δ ^ 2 ≤ 2 * r ^ 2 := by
            linarith [h18, h19]
          have h23 : dist q_corner x ^ 2 ≤ (Real.sqrt 2 * r) ^ 2 := by
            rw [h20]
            have h24 : (Real.sqrt 2 * r) ^ 2 = 2 * r ^ 2 := by
              calc (Real.sqrt 2 * r) ^ 2 = (Real.sqrt 2) ^ 2 * r ^ 2 := by ring
                _ = 2 * r ^ 2 := by rw [Real.sq_sqrt (by norm_num)] <;> ring
            rw [h24]
            exact h22
          have h25 : 0 ≤ dist q_corner x := by positivity
          have h26 : 0 ≤ Real.sqrt 2 * r := by positivity
          have h27 : |dist q_corner x| ≤ |Real.sqrt 2 * r| := sq_le_sq.mp h23
          rw [abs_of_nonneg h25, abs_of_nonneg h26] at h27
          exact h27
        have hz3 : dist z x ≤ R := by
          calc dist z x
            ≤ dist z q_corner + dist q_corner x := dist_triangle _ _ _
          _ ≤ Real.sqrt 2 * δ + Real.sqrt 2 * r := by linarith
          _ = Real.sqrt 2 * (r + δ) := by ring
          _ = R := by simp [R] <;> ring
        have hz4 : z ∈ config.pointSet ∩ Metric.closedBall x R := ⟨hz1, hz3⟩
        have h13 : z ∈ ⋃ c ∈ Cfin, Metric.closedBall c ε := by
          have h14 := hC.subset_iUnion_closedBall
          rw [←h2] at h14
          exact h14 hz4
        rcases Set.mem_iUnion₂.mp h13 with ⟨c, hc_in, hz_ball⟩
        have h15 : ((dSquareToDyadicSquare q).toSet : Set Plane) ∩ Metric.closedBall c δ ≠ ∅ := by
          have hε : (ε : ℝ) = δ := by simp [ε, hδ_pos.le] <;> linarith
          have hz_ball' : z ∈ Metric.closedBall c δ := by
            have h_set : Metric.closedBall c (↑ε : ℝ) = Metric.closedBall c δ := by rw [hε]
            rw [h_set] at hz_ball
            exact hz_ball
          have h_nonempty : (((dSquareToDyadicSquare q).toSet : Set Plane) ∩ Metric.closedBall c δ).Nonempty :=
            ⟨z, hz2, hz_ball'⟩
          exact Set.nonempty_iff_ne_empty.mp h_nonempty
        exact Finset.mem_biUnion.mpr ⟨c, hc_in, Finset.mem_filter.mpr ⟨hq, h15⟩⟩
      have h5 : localS.card ≤ (Cfin.biUnion Q_c).card := Finset.card_le_card h4
      have h6 : (Cfin.biUnion Q_c).card ≤ ∑ c ∈ Cfin, (Q_c c).card := Finset.card_biUnion_le
      have h7 : ∑ c ∈ Cfin, (Q_c c).card ≤ ∑ c ∈ Cfin, 9 := by
        apply Finset.sum_le_sum; intro c hc; exact h3 c hc
      have h8 : ∑ c ∈ Cfin, (9 : ℕ) = 9 * Cfin.card := by
        simp [Finset.sum_const] <;> ring
      rw [h8] at h7
      have h9 : (localS.card : ENNReal) ≤ (9 : ENNReal) * (Cfin.card : ENNReal) := by
        exact_mod_cast le_trans (le_trans h5 h6) h7
      have h10 : (C.encard : ENNReal) = (Cfin.card : ENNReal) := by
        have h11 : C.encard = (Cfin.card : ENat) := by rw [←h2]; simp
        rw [h11] <;> norm_cast
      rw [h10]
      calc (localS.card : ENNReal) / 9
        ≤ ((9 : ENNReal) * (Cfin.card : ENNReal)) / 9 := by gcongr
      _ = (Cfin.card : ENNReal) := by
        have h_comm : (9 : ENNReal) * (Cfin.card : ENNReal) = (Cfin.card : ENNReal) * (9 : ENNReal) := by ring
        rw [h_comm]
        exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
    · have h6 : C.encard = ⊤ := by rw [Set.encard_eq_top_iff]; exact hCfin
      rw [h6] <;> simp
  have h4 : (localS.card : ENNReal) / 9 ≤
      (Metric.externalCoveringNumber ε (config.pointSet ∩ Metric.closedBall x R) : ENNReal) := by
    simpa [Metric.externalCoveringNumber] using le_iInf₂ h_main
  have h5 : ((localS.card : ENNReal) / 9) * 9 ≤
      (Metric.externalCoveringNumber ε (config.pointSet ∩ Metric.closedBall x R) : ENNReal) * 9 := by
    gcongr
  have h6 : ((localS.card : ENNReal) / 9) * 9 = (localS.card : ENNReal) := by
    exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
  have h7 : (localS.card : ENNReal) ≤ (9 : ENNReal) * (Metric.externalCoveringNumber ε (config.pointSet ∩ Metric.closedBall x R) : ENNReal) := by
    have h8 : (Metric.externalCoveringNumber ε (config.pointSet ∩ Metric.closedBall x R) : ENNReal) * 9 = (9 : ENNReal) * (Metric.externalCoveringNumber ε (config.pointSet ∩ Metric.closedBall x R) : ENNReal) := by ring
    rw [h8] at h5
    rw [h6] at h5
    exact h5
  exact h7

/-- Main conversion: fine point-set S-set → coarse corner finset S-set.

    C_coarse = 81 * K * C_between * (2*√2)^s -/
lemma coarse_corners_sset_from_fine_pointset
    {k m : ℕ} (hnm : m ≤ k)
    {s_cfg u C_between C_cfg K C₁ : ℝ} {M MΔ : ℕ}
    (config : CombiningTheorem.NiceConfiguration k s_cfg C₁ M)
    (P : Finset (DyadicSquare k))
    (hP_sub : P ⊆ config.P₀)
    (coarseConfig : CombiningTheorem.NiceConfiguration m s_cfg C_cfg MΔ)
    (hcoarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (h_card_bound : (config.P₀.image (InductionConfigurations.containingSquare hnm)).card ≤ K * coarseConfig.P₀.card)
    (h_sset : IsDeltaSSet (dyadicDelta m) u C_between config.pointSet)
    (hu : 0 ≤ u) (hC_between_pos : 0 < C_between) (hK_pos : 0 < K)
    (hP_nonempty : P.Nonempty) :
    ∃ (C_coarse : ℝ), C_coarse = 81 * K * C_between * (2 * Real.sqrt 2) ^ u ∧
      0 < C_coarse ∧
      IsFinsetDeltaSSet (dyadicDelta m) u C_coarse (finsetDyadicToDSquare coarseConfig.P₀) := by
  set δ : ℝ := dyadicDelta m with hδ_def
  have hδ_pos : 0 < δ := dyadicDelta_pos m
  let ε : NNReal := δ.toNNReal
  let S_dsquare := finsetDyadicToDSquare coarseConfig.P₀
  have hS_nonempty : S_dsquare.Nonempty := by
    rcases hP_nonempty with ⟨p, hp⟩
    let Q := InductionConfigurations.containingSquare hnm p
    have hQ_in : Q ∈ coarseConfig.P₀ := by
      rw [hcoarse_P_eq]
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    exact ⟨dyadicSquareToDSquare Q, Finset.mem_image.mpr ⟨Q, hQ_in, rfl⟩⟩
  let C_coarse : ℝ := 81 * K * C_between * (2 * Real.sqrt 2) ^ u
  have hC_coarse_pos : 0 < C_coarse := by positivity

  have h_cover_pointSet : Metric.externalCoveringNumber ε config.pointSet ≤
      ((config.P₀.image (InductionConfigurations.containingSquare hnm)).card : ENat) :=
    pointSet_ncover_bound hnm config hδ_pos rfl

  have h_card_bound1 : ((config.P₀.image (InductionConfigurations.containingSquare hnm)).card : ℝ) ≤
      K * (coarseConfig.P₀.card : ℝ) := by exact_mod_cast h_card_bound

  have h_card_bound' : ((config.P₀.image (InductionConfigurations.containingSquare hnm)).card : ENNReal) ≤
      ENNReal.ofReal (K * (coarseConfig.P₀.card : ℝ)) := by
    have h2 : ENNReal.ofReal (((config.P₀.image (InductionConfigurations.containingSquare hnm)).card : ℝ)) ≤
        ENNReal.ofReal (K * (coarseConfig.P₀.card : ℝ)) := by
      gcongr
    simpa using h2

  have h_card_eq : (coarseConfig.P₀.card : ℝ) = (S_dsquare.card : ℝ) := by
    have h : (finsetDyadicToDSquare coarseConfig.P₀).card = coarseConfig.P₀.card :=
      card_dyadicToDSquare coarseConfig.P₀
    have h2 : (S_dsquare.card : ℝ) = (coarseConfig.P₀.card : ℝ) := by exact_mod_cast h
    exact h2.symm

  have h_grid : (S_dsquare.card : ENNReal) ≤
      (9 : ENNReal) * Metric.externalCoveringNumber ε (S_dsquare : Set (DSquare m)) :=
    grid_packing_dsquare hδ_pos rfl S_dsquare

  have h_main : IsDeltaSSet δ u C_coarse (S_dsquare : Set (DSquare m)) := by
    refine ⟨hS_nonempty, hδ_pos, hC_coarse_pos, hu, ?_⟩
    intro p r hr
    have hr_pos : 0 < r := by linarith [hδ_pos]
    let x : Plane := dSquareCorner δ p
    let R : ℝ := Real.sqrt 2 * (r + δ)
    have hR_geδ : δ ≤ R := by
      have h1 : 0 < Real.sqrt 2 := by positivity
      have h2 : r + δ ≥ 2 * δ := by linarith
      have h3 : Real.sqrt 2 * (r + δ) ≥ Real.sqrt 2 * (2 * δ) := by gcongr
      have h4 : Real.sqrt 2 * (2 * δ) > δ := by
        have h5 : 0 < δ := hδ_pos
        have h6 : 1 < Real.sqrt 2 := by
          rw [Real.lt_sqrt] <;> norm_num
        have h7 : 2 * Real.sqrt 2 > 1 := by linarith
        have h8 : 2 * Real.sqrt 2 * δ > δ := by
          have h9 : (2 * Real.sqrt 2) * δ > 1 * δ := mul_lt_mul_of_pos_right h7 h5
          linarith
        linarith
      have h6 : R = Real.sqrt 2 * (r + δ) := by simp [R]
      rw [h6]
      linarith
    have h_r_bound : R ≤ (2 * Real.sqrt 2) * r := by
      have h9 : δ ≤ r := hr
      have h10 : r + δ ≤ 2 * r := by linarith
      have h11 : Real.sqrt 2 * (r + δ) ≤ Real.sqrt 2 * (2 * r) := by gcongr
      have h12 : Real.sqrt 2 * (2 * r) = (2 * Real.sqrt 2) * r := by ring
      have h13 : R = Real.sqrt 2 * (r + δ) := by simp [R]
      rw [h13]
      linarith
    let localS := S_dsquare.filter (fun q => dist q p ≤ r)
    have h_localS_eq : (localS : Set (DSquare m)) = (S_dsquare : Set (DSquare m)) ∩ Metric.closedBall p r := by
      ext q
      simp [localS, Metric.mem_closedBall]
      <;> tauto

    have h_local_bound : (localS.card : ENNReal) ≤ (9 : ENNReal) *
        Metric.externalCoveringNumber ε (config.pointSet ∩ Metric.closedBall x R) :=
      local_corners_bound hnm config P hP_sub coarseConfig hcoarse_P_eq hδ_pos rfl p r hr

    have h_sset' := h_sset.2.2.2.2 x R hR_geδ

    have h1 : Metric.externalCoveringNumber ε (localS : Set (DSquare m)) ≤ (localS.card : ENNReal) := by
      have hcover : Metric.IsCover ε (localS : Set (DSquare m)) (localS : Set (DSquare m)) := by
        apply Metric.IsCover.of_subset_iUnion_closedBall
        intro y hy
        exact Set.mem_iUnion₂.mpr ⟨y, hy, Metric.mem_closedBall_self (by positivity)⟩
      have h2 : Metric.externalCoveringNumber ε (localS : Set (DSquare m)) ≤ (localS : Set (DSquare m)).encard :=
        hcover.externalCoveringNumber_le_encard
      have h3 : (localS : Set (DSquare m)).encard = (localS.card : ENat) := by simp
      rw [h3] at h2
      exact_mod_cast h2

    have h_cover_bound : Metric.externalCoveringNumber ε config.pointSet ≤
        ENNReal.ofReal (K * (coarseConfig.P₀.card : ℝ)) :=
      le_trans (by exact_mod_cast h_cover_pointSet) h_card_bound'

    have h_step1 : Metric.externalCoveringNumber ε (localS : Set (DSquare m)) ≤
        (9 : ENNReal) * Metric.externalCoveringNumber ε (config.pointSet ∩ Metric.closedBall x R) :=
      le_trans h1 h_local_bound

    have h_step2 : (9 : ENNReal) * Metric.externalCoveringNumber ε (config.pointSet ∩ Metric.closedBall x R) ≤
        (9 : ENNReal) * (ENNReal.ofReal C_between * (ENNReal.ofReal R) ^ u *
          Metric.externalCoveringNumber ε config.pointSet) := by
      gcongr
      <;> exact h_sset'

    have h_factor : (9 : ENNReal) * ENNReal.ofReal C_between * (ENNReal.ofReal R) ^ u ≠ 0 := by positivity
    have h_step3 : (9 : ENNReal) * ENNReal.ofReal C_between * (ENNReal.ofReal R) ^ u *
          Metric.externalCoveringNumber ε config.pointSet ≤
        (9 : ENNReal) * ENNReal.ofReal C_between * (ENNReal.ofReal R) ^ u *
          ENNReal.ofReal (K * (coarseConfig.P₀.card : ℝ)) := by
      apply mul_le_mul_of_nonneg_left h_cover_bound
      positivity

    have h_step4 : (9 : ENNReal) * ENNReal.ofReal C_between * (ENNReal.ofReal R) ^ u *
          ENNReal.ofReal (K * (coarseConfig.P₀.card : ℝ)) =
        (9 : ENNReal) * ENNReal.ofReal C_between * (ENNReal.ofReal R) ^ u *
          ENNReal.ofReal K * (S_dsquare.card : ENNReal) := by
      have h11 : ENNReal.ofReal (K * (coarseConfig.P₀.card : ℝ)) =
          ENNReal.ofReal K * ENNReal.ofReal ((coarseConfig.P₀.card : ℝ)) := by
        rw [ENNReal.ofReal_mul] <;> positivity
      have h12 : ENNReal.ofReal ((coarseConfig.P₀.card : ℝ)) = (S_dsquare.card : ENNReal) := by
        have h13 : (coarseConfig.P₀.card : ℝ) = (S_dsquare.card : ℝ) := h_card_eq
        rw [h13] <;> norm_cast
      rw [h11, h12] <;> ring

    have h_step5 : (9 : ENNReal) * ENNReal.ofReal C_between * (ENNReal.ofReal R) ^ u *
          ENNReal.ofReal K * (S_dsquare.card : ENNReal) ≤
        (9 : ENNReal) * ENNReal.ofReal C_between * (ENNReal.ofReal R) ^ u *
          ENNReal.ofReal K * ((9 : ENNReal) * Metric.externalCoveringNumber ε (S_dsquare : Set (DSquare m))) := by
      apply mul_le_mul_of_nonneg_left h_grid
      positivity

    have h_rpow_eq : (ENNReal.ofReal (2 * Real.sqrt 2)) ^ u = ENNReal.ofReal ((2 * Real.sqrt 2) ^ u) := by
      have hpos : 0 ≤ 2 * Real.sqrt 2 := by positivity
      exact ENNReal.ofReal_rpow_of_nonneg hpos hu

    have h_final : (9 : ENNReal) * ENNReal.ofReal C_between * (ENNReal.ofReal R) ^ u *
          ENNReal.ofReal K * ((9 : ENNReal) * Metric.externalCoveringNumber ε (S_dsquare : Set (DSquare m))) ≤
        ENNReal.ofReal C_coarse * (ENNReal.ofReal r) ^ u *
          Metric.externalCoveringNumber ε (S_dsquare : Set (DSquare m)) := by
      have h12 : ENNReal.ofReal C_coarse =
          (81 : ENNReal) * ENNReal.ofReal K * ENNReal.ofReal C_between *
            ENNReal.ofReal ((2 * Real.sqrt 2) ^ u) := by
        dsimp only [C_coarse]
        have h_all_pos : 0 < (81 : ℝ) * K * C_between * (2 * Real.sqrt 2) ^ u := by positivity
        have h_pos1 : 0 ≤ (81 : ℝ) * K * C_between := by positivity
        have h_pos2 : 0 ≤ (2 * Real.sqrt 2) ^ u := by positivity
        have h_mul1 : ENNReal.ofReal (((81 : ℝ) * K * C_between) * (2 * Real.sqrt 2) ^ u) =
            ENNReal.ofReal ((81 : ℝ) * K * C_between) * ENNReal.ofReal ((2 * Real.sqrt 2) ^ u) := by
          rw [ENNReal.ofReal_mul h_pos1]
        have h_pos3 : 0 ≤ (81 : ℝ) * K := by positivity
        have h_mul2 : ENNReal.ofReal ((81 : ℝ) * K * C_between) =
            ENNReal.ofReal ((81 : ℝ) * K) * ENNReal.ofReal C_between := by
          rw [ENNReal.ofReal_mul h_pos3]
        have h_mul3 : ENNReal.ofReal ((81 : ℝ) * K) =
            ENNReal.ofReal (81 : ℝ) * ENNReal.ofReal K := by
          rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ (81 : ℝ) by positivity)]
        have h_mul : ENNReal.ofReal ((81 : ℝ) * K * C_between * (2 * Real.sqrt 2) ^ u) =
            ENNReal.ofReal (81 : ℝ) * ENNReal.ofReal K * ENNReal.ofReal C_between * ENNReal.ofReal ((2 * Real.sqrt 2) ^ u) := by
          rw [show (81 : ℝ) * K * C_between * (2 * Real.sqrt 2) ^ u =
              ((81 : ℝ) * K * C_between) * (2 * Real.sqrt 2) ^ u by ring]
          rw [h_mul1, h_mul2, h_mul3] <;> ring
        rw [h_mul]
        <;> simp [ENNReal.ofReal_ofNat] <;> ring
      have h13 : (ENNReal.ofReal R) ^ u ≤ ENNReal.ofReal ((2 * Real.sqrt 2) ^ u) * (ENNReal.ofReal r) ^ u := by
        have h14 : R ≤ (2 * Real.sqrt 2) * r := h_r_bound
        have h15 : (ENNReal.ofReal R) ^ u ≤ (ENNReal.ofReal ((2 * Real.sqrt 2) * r)) ^ u := by gcongr
        have h16 : ENNReal.ofReal ((2 * Real.sqrt 2) * r) =
            ENNReal.ofReal (2 * Real.sqrt 2) * ENNReal.ofReal r := by
          rw [ENNReal.ofReal_mul] <;> positivity
        rw [h16] at h15
        have h17 : (ENNReal.ofReal (2 * Real.sqrt 2) * ENNReal.ofReal r) ^ u =
            (ENNReal.ofReal (2 * Real.sqrt 2)) ^ u * (ENNReal.ofReal r) ^ u := by
          exact ENNReal.mul_rpow_of_nonneg _ _ hu
        rw [h17] at h15
        rw [h_rpow_eq] at h15
        exact h15
      have h18 : (9 : ENNReal) * (9 : ENNReal) = (81 : ENNReal) := by norm_cast
      calc (9 : ENNReal) * ENNReal.ofReal C_between * (ENNReal.ofReal R) ^ u * ENNReal.ofReal K * ((9 : ENNReal) * Metric.externalCoveringNumber ε (S_dsquare : Set (DSquare m)))
        = (9 : ENNReal) * (9 : ENNReal) * ENNReal.ofReal C_between * ENNReal.ofReal K * (ENNReal.ofReal R) ^ u * Metric.externalCoveringNumber ε (S_dsquare : Set (DSquare m)) := by ring
      _ = (81 : ENNReal) * ENNReal.ofReal C_between * ENNReal.ofReal K * (ENNReal.ofReal R) ^ u * Metric.externalCoveringNumber ε (S_dsquare : Set (DSquare m)) := by rw [h18] <;> ring
      _ ≤ (81 : ENNReal) * ENNReal.ofReal C_between * ENNReal.ofReal K * (ENNReal.ofReal ((2 * Real.sqrt 2) ^ u) * (ENNReal.ofReal r) ^ u) * Metric.externalCoveringNumber ε (S_dsquare : Set (DSquare m)) := by gcongr
      _ = (81 : ENNReal) * ENNReal.ofReal K * ENNReal.ofReal C_between * ENNReal.ofReal ((2 * Real.sqrt 2) ^ u) * (ENNReal.ofReal r) ^ u * Metric.externalCoveringNumber ε (S_dsquare : Set (DSquare m)) := by ring
      _ = ENNReal.ofReal C_coarse * (ENNReal.ofReal r) ^ u * Metric.externalCoveringNumber ε (S_dsquare : Set (DSquare m)) := by
        rw [h12] <;> ring

    have h_assoc : (9 : ENNReal) * (ENNReal.ofReal C_between * (ENNReal.ofReal R) ^ u *
          Metric.externalCoveringNumber ε config.pointSet) =
        (9 : ENNReal) * ENNReal.ofReal C_between * (ENNReal.ofReal R) ^ u *
          Metric.externalCoveringNumber ε config.pointSet := by ring
    rw [←h_localS_eq]
    exact le_trans (le_trans (le_trans (le_trans h_step1 (h_assoc ▸ h_step2)) h_step3) h_step4.le) (le_trans h_step5 h_final)

  exact ⟨C_coarse, by rfl, hC_coarse_pos, h_main⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
