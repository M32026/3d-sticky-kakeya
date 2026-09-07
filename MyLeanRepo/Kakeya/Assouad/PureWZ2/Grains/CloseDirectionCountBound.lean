import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalAD

/-!
# Close-direction count bound helper

Packages `pureWz2_close_direction_count_general` into a strict inequality
suitable for the `hclose` hypothesis of `weak_planiness_wiring`.

Both `paperCloseDirectionCount` and `PaperIsSubshading` are now defined in
the shared base module `Grains.lean`, so this file can be safely imported
alongside `TransversePairPaper` and `WeakPlaninessWiring`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Strict close-direction count bound from direction packing.

Given essentially distinct, line-class tubes at scale `L ≤ 1/10000`
and threshold `kappa = K * L` with `K * L ≤ 1/2`, the close-direction
count is strictly less than `(1600*K + 1)^5 + 1`.

This matches the `hclose` hypothesis of `weak_planiness_wiring` with
`R = (1600*K + 1)^5 + 1` and `kappa = K * L`. -/
lemma close_direction_count_bound
    {L : ℝ} {K : ℕ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (h_essentially_distinct : WZ1PaperIsEssentiallyDistinct coarse)
    (h_line_class : WZ1PaperIsLineClass coarse)
    (hL_pos : 0 < L)
    (hL_small : L ≤ 1 / 10000)
    (hK_one : 1 ≤ K)
    (hKL_small : (K : ℝ) * L ≤ 1 / 2) :
    ∀ (p : Point3), p ∈ coarseShading.union →
      ∀ (i : Fin coarse.card), p ∈ coarseShading.carrier i →
        paperCloseDirectionCount coarseShading p i ((K : ℝ) * L) <
          (1600 * K + 1)^5 + 1 := by
  intro p hp i hi
  have h1 : (paperCloseDirectionCount coarseShading p i ((K : ℝ) * L) : ENNReal) ≤
      ((1600 * K + 1)^5 : ENNReal) :=
    pureWz2_close_direction_count_general
      (delta := (0 : ℝ)) (sigma := (0 : ℝ))
      h_essentially_distinct h_line_class hL_pos hL_small hK_one hKL_small
      p hp i hi
  have h2 : paperCloseDirectionCount coarseShading p i ((K : ℝ) * L) ≤ (1600 * K + 1)^5 := by
    exact_mod_cast h1
  linarith

/-- Close-direction count transfers to a subshading.

Given `hsub : ∀ i, Z.carrier i ⊆ Y.carrier i`, the close-direction
count for `Z` is at most that for `Y`. -/
lemma close_direction_count_transfer
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Z Y : WZ1PaperTubeShading F}
    (hsub : ∀ i, Z.carrier i ⊆ Y.carrier i)
    (p : Point3) (i : Fin F.card) (kappa : ℝ) :
    paperCloseDirectionCount Z p i kappa ≤
    paperCloseDirectionCount Y p i kappa := by
  classical
  apply Finset.card_le_card
  intro j hj
  have h_mem : j ∈ (Finset.univ.filter fun j =>
      p ∈ Y.carrier j ∧ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < kappa) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hsub j hj.1, hj.2⟩
  exact h_mem

/-- Close-direction count is monotone in the threshold.

If `kappa1 ≤ kappa2`, then `count(kappa1) ≤ count(kappa2)`. -/
lemma close_direction_count_monotone_threshold
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (p : Point3) (i : Fin F.card) {kappa1 kappa2 : ℝ}
    (h : kappa1 ≤ kappa2) :
    paperCloseDirectionCount Y p i kappa1 ≤
      paperCloseDirectionCount Y p i kappa2 := by
  classical
  apply Finset.card_le_card
  intro j hj
  simp only [paperCloseDirectionCount, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact ⟨hj.1, lt_of_lt_of_le hj.2 h⟩

/-- Convert a finite ENNReal upper bound on the close-direction count to a
strict natural-number bound.

Given `(count : ENNReal) ≤ B` with `B ≠ ⊤`, there exists `R : ℕ` such that
`count < R`. This packages the close count for the `hclose` hypothesis of
`weak_planiness_wiring`. -/
lemma close_count_strict_of_ennreal
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F} {kappa : ℝ} {B : ENNReal}
    (hB_ne_top : B ≠ ⊤)
    (h_bound : ∀ (p : Point3), p ∈ Y.union →
      ∀ (i : Fin F.card), p ∈ Y.carrier i →
        (paperCloseDirectionCount Y p i kappa : ENNReal) ≤ B) :
    ∃ (R : ℕ), ∀ (p : Point3), p ∈ Y.union →
      ∀ (i : Fin F.card), p ∈ Y.carrier i →
        paperCloseDirectionCount Y p i kappa < R := by
  have h1 : ∃ (n : ℕ), B < (n : ENNReal) :=
    ENNReal.exists_nat_gt hB_ne_top
  rcases h1 with ⟨R, hR⟩
  refine ⟨R, fun p hp i hi => ?_⟩
  have h2 : (paperCloseDirectionCount Y p i kappa : ENNReal) ≤ B := h_bound p hp i hi
  have h3 : (paperCloseDirectionCount Y p i kappa : ENNReal) < (R : ENNReal) :=
    lt_of_le_of_lt h2 hR
  exact_mod_cast h3

/-- Combined close-count packaging: transfer to a subshading, relax the threshold,
and convert to a strict Nat bound.

Given a bound on `Y` at threshold `kappa2`, produce a strict bound on a subshading `Z`
at threshold `kappa1 ≤ kappa2`. -/
lemma close_count_packaged
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Z Y : WZ1PaperTubeShading F} {kappa1 kappa2 : ℝ} {B : ENNReal}
    (hsub : ∀ i, Z.carrier i ⊆ Y.carrier i)
    (hkappa_le : kappa1 ≤ kappa2)
    (hB_ne_top : B ≠ ⊤)
    (h_bound : ∀ (p : Point3), p ∈ Y.union →
      ∀ (i : Fin F.card), p ∈ Y.carrier i →
        (paperCloseDirectionCount Y p i kappa2 : ENNReal) ≤ B) :
    ∃ (R : ℕ), ∀ (p : Point3), p ∈ Z.union →
      ∀ (i : Fin F.card), p ∈ Z.carrier i →
        paperCloseDirectionCount Z p i kappa1 < R := by
  have hZ_sub_union : Z.union ⊆ Y.union := by
    intro x hx
    rcases hx with ⟨i, hi⟩
    exact ⟨i, hsub i hi⟩
  have h_bound' : ∀ (p : Point3), p ∈ Z.union →
      ∀ (i : Fin F.card), p ∈ Z.carrier i →
        (paperCloseDirectionCount Z p i kappa1 : ENNReal) ≤ B := by
    intro p hp i hi
    have h1 : paperCloseDirectionCount Z p i kappa1 ≤ paperCloseDirectionCount Z p i kappa2 :=
      close_direction_count_monotone_threshold p i hkappa_le
    have h2 : paperCloseDirectionCount Z p i kappa2 ≤ paperCloseDirectionCount Y p i kappa2 :=
      close_direction_count_transfer hsub p i kappa2
    have h3 : p ∈ Y.union := hZ_sub_union hp
    have h4 : (paperCloseDirectionCount Y p i kappa2 : ENNReal) ≤ B := h_bound p h3 i (hsub i hi)
    have h5 : (paperCloseDirectionCount Z p i kappa1 : ENNReal) ≤ (paperCloseDirectionCount Y p i kappa2 : ENNReal) := by
      exact_mod_cast le_trans h1 h2
    exact le_trans h5 h4
  exact close_count_strict_of_ennreal hB_ne_top h_bound'

end Kakeya.Assouad
