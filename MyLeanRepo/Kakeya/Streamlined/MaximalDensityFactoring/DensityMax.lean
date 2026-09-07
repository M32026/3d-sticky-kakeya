import MyLeanRepo.Kakeya.Streamlined.Basic

/-!
# Density maximization attainment lemma

For a finite `BodyFamily`, the supremum `deltaMax` over all convex sets
is attained at the convex hull of the union of some subfamily.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/--
The maximal density is attained.

For any convex `K`, let `S` be the indices of bodies contained in `K`.
The convex hull `W_S` of the union of those bodies satisfies `W_S ⊆ K`
and contains every body in `S`, so `density(F, W_S) ≥ density(F, K)`.
Since there are only finitely many subsets `S`, the supremum is a finite
maximum and is attained.
-/
lemma deltaMax_attained (F : BodyFamily) :
    ∃ (W : Set Point3), Convex ℝ W ∧ F.density W = F.deltaMax := by
  classical
  let candidates : Finset (Finset (Fin F.card)) :=
    Finset.powerset Finset.univ
  let unionBodies (S : Finset (Fin F.card)) : Set Point3 :=
    {x | ∃ (i : Fin F.card), i ∈ S ∧ x ∈ (F.body i).carrier}
  let hull (S : Finset (Fin F.card)) : Set Point3 :=
    convexHull ℝ (unionBodies S)
  let f (S : Finset (Fin F.card)) : ENNReal := F.density (hull S)
  let candVals : Finset ENNReal := Finset.image f candidates

  have h_hull_convex : ∀ S, Convex ℝ (hull S) := by
    intro S
    exact convex_convexHull ℝ _

  have h_main : ∀ (K : Set Point3), Convex ℝ K →
      ∃ S ∈ candidates, F.density K ≤ f S := by
    intro K hK
    let S : Finset (Fin F.card) :=
      Finset.univ.filter (fun i => (F.body i).carrier ⊆ K)
    have hS_cand : S ∈ candidates := by
      simp [candidates, S]
    let U : Set Point3 := unionBodies S
    have h1 : U ⊆ K := by
      intro x hx
      rcases hx with ⟨i, hi, hxi⟩
      have h2 : (F.body i).carrier ⊆ K := by
        have h3 : i ∈ S := hi
        simpa [S, Finset.mem_filter] using (Finset.mem_filter.mp h3).2
      exact h2 hxi
    have h2 : hull S ⊆ K := by
      exact convexHull_min h1 hK
    have h3 : ∀ i ∈ S, (F.body i).carrier ⊆ hull S := by
      intro i hi
      have h4 : (F.body i).carrier ⊆ U := by
        intro x hx
        exact ⟨i, hi, hx⟩
      exact subset_trans h4 (subset_convexHull ℝ U)
    have h4 : S ⊆ F.containedIndices (hull S) := by
      intro i hi
      simpa [BodyFamily.containedIndices, Finset.mem_filter] using h3 i hi
    have h5 : F.containedIndices K = S := by
      ext i
      simp [S, BodyFamily.containedIndices, Finset.mem_filter]
    have h6 : F.containedMass K ≤ F.containedMass (hull S) := by
      dsimp only [BodyFamily.containedMass]
      rw [h5]
      exact Finset.sum_le_sum_of_subset_of_nonneg h4 (fun _ _ _ => by simp)
    have h7 : MeasureTheory.volume (hull S) ≤ MeasureTheory.volume K := by
      exact measure_mono h2
    have h8 : F.density K ≤ F.density (hull S) := by
      dsimp only [BodyFamily.density]
      exact ENNReal.div_le_div h6 h7
    exact ⟨S, hS_cand, h8⟩

  have h_cand_nonempty : candidates.Nonempty := by
    exact ⟨∅, by simp [candidates]⟩

  have h_candVals_nonempty : candVals.Nonempty :=
    Finset.Nonempty.image h_cand_nonempty f

  let d : ENNReal := candVals.max' h_candVals_nonempty
  have hd : d ∈ candVals := Finset.max'_mem candVals h_candVals_nonempty
  have hmax : ∀ x ∈ candVals, x ≤ d := fun x hx => Finset.le_max' candVals x hx

  have h_bdd : BddAbove
      {d : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ d = F.density K} := by
    refine ⟨⊤, fun x _ => le_top⟩

  have h9 : ∀ (x : ENNReal), x ∈ candVals → x ≤ F.deltaMax := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨S, hS, rfl⟩
    have h10 : Convex ℝ (hull S) := h_hull_convex S
    have h11 : F.density (hull S) ∈
        {d : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ d = F.density K} := by
      exact ⟨hull S, h10, rfl⟩
    exact le_csSup h_bdd h11

  have h10 : candVals.sup id ≤ F.deltaMax := by
    apply Finset.sup_le
    intro x hx
    exact h9 x hx

  have hne : Set.Nonempty
      {d : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ d = F.density K} := by
    refine ⟨0, Set.univ, convex_univ, ?_⟩
    simp [BodyFamily.density]

  have h11 : ∀ (x : ENNReal),
      x ∈ {d : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ d = F.density K} →
      x ≤ d := by
    intro x hx
    rcases hx with ⟨K, hK, rfl⟩
    rcases h_main K hK with ⟨S, hS, hle⟩
    have h12 : f S ∈ candVals := Finset.mem_image.mpr ⟨S, hS, rfl⟩
    exact le_trans hle (hmax (f S) h12)

  have h12 : F.deltaMax ≤ d := by
    exact csSup_le hne h11

  have h13 : d ≤ candVals.sup id := by
    simpa using Finset.le_sup (f := id) hd
  have h14 : candVals.sup id ≤ d := Finset.sup_le hmax
  have h15 : candVals.sup id = d := le_antisymm h14 h13

  have h16 : F.deltaMax = d := le_antisymm h12 (le_trans h13 h10)

  rcases Finset.mem_image.mp hd with ⟨S, hS, hds⟩
  refine ⟨hull S, h_hull_convex S, ?_⟩
  rw [h16, ←hds]

end Kakeya.Streamlined
