module

/-
  Fixed numerical packing bound for canonical dyadic affine lines.

  Given dyadic tubes with |slope| ≤ 1 and |intercept| ≤ 3, the number of
  distinct affine-line images in any ball of radius 64·δ_n is bounded by
  a fixed numerical constant C_pack = 5633^2 = 31730689.

  Proof:
  - toAffineLine is 22-co-Lipschitz (DyadicToAffineAdapters)
  - Two lines in a 64·δ_n ball are at most 128·δ_n apart
  - Hence parameter difference ≤ 22·128·δ_n = 2816·δ_n
  - Since slope = a·δ_n, intercept = b·δ_n for integers a,b:
    |a1-a2| ≤ 2816, |b1-b2| ≤ 2816
  - At most (2·2816+1)^2 = 5633^2 integer pairs
  - toAffineLine is injective, so image cardinality = tube cardinality

  Whiteprint node: fixed_packing_bound
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicToAffineAdapters
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FixedPackingBound

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DyadicCardToNcover (toAffineLine)
open DyadicToAffineAdapters (paramDistLinf toAffineLine_co_lipschitz)

/-- The packing constant: (2 * 2816 + 1)^2 = 5633^2. -/
def C_pack : ℕ := 5633 ^ 2

/-- `C_pack = 31730689`. -/
lemma C_pack_eq : C_pack = 31730689 := by
  rfl

/-! ========================================================================
   Injectivity of toAffineLine
   ======================================================================== -/

/-- `toAffineLine` is injective on tubes with bounded slope/intercept. -/
lemma toAffineLine_injective_on_bounded {n : ℕ} :
    Set.InjOn toAffineLine {T : DyadicTube n | |T.slope| ≤ 1 ∧ |T.intercept| ≤ 3} := by
  intro T1 h1 T2 h2 h_eq
  have h_dist : dist (toAffineLine T1) (toAffineLine T2) = 0 := by
    rw [h_eq] <;> simp
  have h_co_lip : paramDistLinf T1 T2 ≤ 22 * dist (toAffineLine T1) (toAffineLine T2) :=
    toAffineLine_co_lipschitz T1 T2 h1.1 h2.1 h2.2
  rw [h_dist] at h_co_lip
  have h_param0 : paramDistLinf T1 T2 = 0 := by
    have h_nonneg : 0 ≤ paramDistLinf T1 T2 := by positivity
    linarith
  have h_slope : |T1.slope - T2.slope| = 0 := by
    have h : |T1.slope - T2.slope| ≤ paramDistLinf T1 T2 := le_max_left _ _
    rw [h_param0] at h
    have h' : |T1.slope - T2.slope| ≤ 0 := h
    have h'' : 0 ≤ |T1.slope - T2.slope| := abs_nonneg _
    linarith
  have h_intercept : |T1.intercept - T2.intercept| = 0 := by
    have h : |T1.intercept - T2.intercept| ≤ paramDistLinf T1 T2 := le_max_right _ _
    rw [h_param0] at h
    have h' : |T1.intercept - T2.intercept| ≤ 0 := h
    have h'' : 0 ≤ |T1.intercept - T2.intercept| := abs_nonneg _
    linarith
  have hsl : T1.slope = T2.slope := by
    have h' : |T1.slope - T2.slope| = 0 := h_slope
    have h'' : T1.slope - T2.slope = 0 := abs_eq_zero.mp h'
    linarith
  have hin : T1.intercept = T2.intercept := by
    have h' : |T1.intercept - T2.intercept| = 0 := h_intercept
    have h'' : T1.intercept - T2.intercept = 0 := abs_eq_zero.mp h'
    linarith
  have ha : T1.a = T2.a := by
    have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
    have h : (T1.a : ℝ) * dyadicDelta n = (T2.a : ℝ) * dyadicDelta n := by
      simpa [DyadicTube.slope] using hsl
    have h' : (T1.a : ℝ) = (T2.a : ℝ) := by
      apply (mul_right_inj' hδ_pos.ne').mp
      ring_nf at h ⊢ <;> exact h
    exact_mod_cast h'
  have hb : T1.b = T2.b := by
    have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
    have h : (T1.b : ℝ) * dyadicDelta n = (T2.b : ℝ) * dyadicDelta n := by
      simpa [DyadicTube.intercept] using hin
    have h' : (T1.b : ℝ) = (T2.b : ℝ) := by
      apply (mul_right_inj' hδ_pos.ne').mp
      ring_nf at h ⊢ <;> exact h
    exact_mod_cast h'
  cases T1 <;> cases T2 <;> simp [ha, hb] <;> tauto

/-! ========================================================================
   Fixed packing bound
   ======================================================================== -/

/-- Fixed packing bound: for any dyadic tube set S with bounded slope/intercept,
    the intersection of `toAffineLine '' S` with any ball of radius `64·δ_n`
    has cardinality at most `C_pack`. -/
lemma fixed_packing_bound
    {n : ℕ} {S : Finset (DyadicTube n)}
    (hm : ∀ T ∈ S, |T.slope| ≤ 1)
    (hb : ∀ T ∈ S, |T.intercept| ≤ 3)
    (x : AffineLine) :
    ((toAffineLine '' (S : Set (DyadicTube n))) ∩
      Metric.closedBall x (64 * dyadicDelta n)).ncard ≤ C_pack := by
  set δ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  let TubesInBall : Finset (DyadicTube n) :=
    S.filter (fun T => dist (toAffineLine T) x ≤ 64 * δ)
  have h_image_eq : (toAffineLine '' (S : Set (DyadicTube n))) ∩
      Metric.closedBall x (64 * δ) =
      toAffineLine '' (TubesInBall : Set (DyadicTube n)) := by
    ext ℓ
    simp only [TubesInBall, Set.mem_inter_iff, Set.mem_image, Finset.mem_coe,
      Finset.mem_filter, Metric.mem_closedBall]
    constructor
    · rintro ⟨⟨T, hT, rfl⟩, hball⟩
      exact ⟨T, ⟨hT, hball⟩, rfl⟩
    · rintro ⟨T, ⟨hT, hball⟩, rfl⟩
      exact ⟨⟨T, hT, rfl⟩, hball⟩
  rw [h_image_eq]
  have h_bounded_set : ∀ T ∈ TubesInBall, |T.slope| ≤ 1 ∧ |T.intercept| ≤ 3 := by
    intro T hT
    have hT_in_S : T ∈ S := (Finset.mem_filter.mp hT).1
    exact ⟨hm T hT_in_S, hb T hT_in_S⟩
  have h_inj : Set.InjOn toAffineLine (TubesInBall : Set (DyadicTube n)) := by
    intro x hx y hy hxy
    have hx' : x ∈ {T : DyadicTube n | |T.slope| ≤ 1 ∧ |T.intercept| ≤ 3} := h_bounded_set x hx
    have hy' : y ∈ {T : DyadicTube n | |T.slope| ≤ 1 ∧ |T.intercept| ≤ 3} := h_bounded_set y hy
    exact toAffineLine_injective_on_bounded hx' hy' hxy
  have h_ncard : (toAffineLine '' (TubesInBall : Set (DyadicTube n))).ncard =
      TubesInBall.card := by
    rw [Set.ncard_image_of_injOn h_inj]
    <;> simp
  rw [h_ncard]
  -- Now bound TubesInBall.card
  by_cases h_empty : TubesInBall = ∅
  · rw [h_empty]
    <;> simp [C_pack] <;> norm_num
  · -- Pick a reference tube T0 in TubesInBall
    have h_nonempty : TubesInBall.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
    rcases h_nonempty with ⟨T0, hT0⟩
    have hT0_in_S : T0 ∈ S := (Finset.mem_filter.mp hT0).1
    have hT0_ball : dist (toAffineLine T0) x ≤ 64 * δ :=
      (Finset.mem_filter.mp hT0).2
    have hT0_slope : |T0.slope| ≤ 1 := hm T0 hT0_in_S
    have hT0_intercept : |T0.intercept| ≤ 3 := hb T0 hT0_in_S
    -- Every T in TubesInBall satisfies |T.a - T0.a| ≤ 2816 and |T.b - T0.b| ≤ 2816
    have h_grid : ∀ T ∈ TubesInBall,
        |(T.a : ℤ) - T0.a| ≤ 2816 ∧ |(T.b : ℤ) - T0.b| ≤ 2816 := by
      intro T hT
      have hT_in_S : T ∈ S := (Finset.mem_filter.mp hT).1
      have hT_ball : dist (toAffineLine T) x ≤ 64 * δ :=
        (Finset.mem_filter.mp hT).2
      have hT_slope : |T.slope| ≤ 1 := hm T hT_in_S
      have hT_intercept : |T.intercept| ≤ 3 := hb T hT_in_S
      have h_dist : dist (toAffineLine T) (toAffineLine T0) ≤ 128 * δ := by
        calc dist (toAffineLine T) (toAffineLine T0)
          ≤ dist (toAffineLine T) x + dist x (toAffineLine T0) := dist_triangle _ _ _
        _ = dist (toAffineLine T) x + dist (toAffineLine T0) x := by rw [dist_comm x (toAffineLine T0)]
        _ ≤ 64 * δ + 64 * δ := by gcongr
        _ = 128 * δ := by ring
      have h_co_lip : paramDistLinf T T0 ≤ 22 * dist (toAffineLine T) (toAffineLine T0) :=
        toAffineLine_co_lipschitz T T0 hT_slope hT0_slope hT0_intercept
      have h_param : paramDistLinf T T0 ≤ 22 * (128 * δ) := by
        calc paramDistLinf T T0
          ≤ 22 * dist (toAffineLine T) (toAffineLine T0) := h_co_lip
        _ ≤ 22 * (128 * δ) := by gcongr
      have h_slope_diff : |T.slope - T0.slope| ≤ 22 * (128 * δ) := by
        have h : |T.slope - T0.slope| ≤ paramDistLinf T T0 := le_max_left _ _
        linarith
      have h_int_diff : |T.intercept - T0.intercept| ≤ 22 * (128 * δ) := by
        have h : |T.intercept - T0.intercept| ≤ paramDistLinf T T0 := le_max_right _ _
        linarith
      have h_a_diff : |(T.a : ℝ) - (T0.a : ℝ)| ≤ 2816 := by
        have h1 : T.slope - T0.slope = ((T.a : ℝ) - (T0.a : ℝ)) * δ := by
          simp [DyadicTube.slope] <;> ring
        rw [h1] at h_slope_diff
        have h2 : |((T.a : ℝ) - (T0.a : ℝ)) * δ| ≤ 22 * (128 * δ) := h_slope_diff
        have h3 : |((T.a : ℝ) - (T0.a : ℝ))| * |δ| ≤ 22 * (128 * δ) := by
          rw [abs_mul] at h2 <;> exact h2
        have h4 : |δ| = δ := abs_of_pos hδ_pos
        rw [h4] at h3
        nlinarith [hδ_pos]
      have h_b_diff : |(T.b : ℝ) - (T0.b : ℝ)| ≤ 2816 := by
        have h1 : T.intercept - T0.intercept = ((T.b : ℝ) - (T0.b : ℝ)) * δ := by
          simp [DyadicTube.intercept] <;> ring
        rw [h1] at h_int_diff
        have h2 : |((T.b : ℝ) - (T0.b : ℝ)) * δ| ≤ 22 * (128 * δ) := h_int_diff
        have h3 : |((T.b : ℝ) - (T0.b : ℝ))| * |δ| ≤ 22 * (128 * δ) := by
          rw [abs_mul] at h2 <;> exact h2
        have h4 : |δ| = δ := abs_of_pos hδ_pos
        rw [h4] at h3
        nlinarith [hδ_pos]
      have h_a_int : |(T.a - T0.a : ℤ)| ≤ 2816 := by exact_mod_cast h_a_diff
      have h_b_int : |(T.b - T0.b : ℤ)| ≤ 2816 := by exact_mod_cast h_b_diff
      exact ⟨h_a_int, h_b_int⟩
    -- TubesInBall is contained in the grid
    let aGrid : Finset ℤ := Finset.Icc (T0.a - 2816) (T0.a + 2816)
    let bGrid : Finset ℤ := Finset.Icc (T0.b - 2816) (T0.b + 2816)
    have h_aGrid_card : aGrid.card = 5633 := by
      simp [aGrid] <;> norm_num <;> omega
    have h_bGrid_card : bGrid.card = 5633 := by
      simp [bGrid] <;> norm_num <;> omega
    let gridFilter : ℤ → ℤ → Finset (DyadicTube n) := fun a b =>
      S.filter (fun T => T.a = a ∧ T.b = b)
    have h_contained : TubesInBall ⊆ Finset.biUnion aGrid (fun a =>
        Finset.biUnion bGrid (gridFilter a)) := by
      intro T hT
      have hg := h_grid T hT
      have ha : T.a ∈ aGrid := by
        simp only [aGrid, Finset.mem_Icc]
        constructor <;> linarith [abs_le.mp hg.1]
      have hb : T.b ∈ bGrid := by
        simp only [bGrid, Finset.mem_Icc]
        constructor <;> linarith [abs_le.mp hg.2]
      have hT_in_S : T ∈ S := (Finset.mem_filter.mp hT).1
      have h_filter : T ∈ gridFilter T.a T.b := by
        simp only [gridFilter, Finset.mem_filter]
        <;> exact ⟨hT_in_S, by simp⟩
      exact Finset.mem_biUnion.mpr ⟨T.a, ha, Finset.mem_biUnion.mpr ⟨T.b, hb, h_filter⟩⟩
    have h_card : TubesInBall.card ≤
        (Finset.biUnion aGrid (fun a => Finset.biUnion bGrid (gridFilter a))).card :=
      Finset.card_le_card h_contained
    have h_biUnion_card : (Finset.biUnion aGrid (fun a => Finset.biUnion bGrid (gridFilter a))).card ≤
        aGrid.card * bGrid.card := by
      calc _
        ≤ ∑ a ∈ aGrid, (Finset.biUnion bGrid (gridFilter a)).card := Finset.card_biUnion_le
      _ ≤ ∑ a ∈ aGrid, ∑ b ∈ bGrid, (gridFilter a b).card := by
          gcongr with a ha
          exact Finset.card_biUnion_le
      _ ≤ ∑ a ∈ aGrid, ∑ b ∈ bGrid, 1 := by
          gcongr with a ha b hb
          have h_filter_card : (gridFilter a b).card ≤ 1 := by
            by_cases h : (gridFilter a b).Nonempty
            · rcases h with ⟨T, hT⟩
              have h_sub : gridFilter a b ⊆ ({T} : Finset (DyadicTube n)) := by
                intro U hU
                have h3 : U ∈ S ∧ (U.a = a ∧ U.b = b) := by
                  rw [Finset.mem_filter] at hU; exact hU
                have h4 : T ∈ S ∧ (T.a = a ∧ T.b = b) := by
                  rw [Finset.mem_filter] at hT; exact hT
                have ha : U.a = T.a := by rw [h3.2.1, h4.2.1]
                have hb : U.b = T.b := by rw [h3.2.2, h4.2.2]
                have h_eq : U = T := by
                  cases U <;> cases T <;> simp [ha, hb] <;> tauto
                simp [h_eq]
              calc (gridFilter a b).card
                ≤ ({T} : Finset (DyadicTube n)).card := Finset.card_le_card h_sub
              _ = 1 := by simp
            · rw [Finset.not_nonempty_iff_eq_empty] at h
              rw [h] <;> simp
          exact h_filter_card
      _ = aGrid.card * bGrid.card := by simp [Finset.sum_const] <;> ring
    calc TubesInBall.card
      ≤ (Finset.biUnion aGrid (fun a => Finset.biUnion bGrid (gridFilter a))).card := h_card
    _ ≤ aGrid.card * bGrid.card := h_biUnion_card
    _ = 5633 * 5633 := by rw [h_aGrid_card, h_bGrid_card]
    _ = C_pack := by simp [C_pack] <;> norm_num

end DirecretisedFurstenbergEstimate.FixedPackingBound

end
