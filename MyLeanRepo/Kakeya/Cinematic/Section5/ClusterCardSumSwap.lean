import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ClusterDefinitions

/-!
# Sum-swap lemma for cluster cardinalities

Swaps the order of summation in the overlap count:
`∑ c, #(F ∩ ball(c, 3t)) = ∑ f, #{c : f ∈ ball(c, 3t)}`.

This is the double-counting identity used in PYZ Section 5.1.1 to reduce the
bounded-overlap ambient ball sum to a per-point packing bound.
-/

namespace Kakeya.Cinematic

/-- Swaps the order of summation in the cluster-cardinality overlap sum. -/
lemma cluster_card_sum_swap
    {F : FiniteFunctionFamily} {centers : Finset C2Function} {t : ℝ} :
    ∑ c ∈ centers, ((F.cluster c (3 * t)).card : ℝ) =
    ∑ f ∈ F.toFinset, ((centers.filter (fun c => c2Distance f c ≤ 3 * t)).card : ℝ) := by
  have h_card_eq : ∀ (G : FiniteFunctionFamily), G.card = G.toFinset.card := by
    intro G
    exact Set.ncard_eq_toFinset_card G.carrier (hs := G.finite)
  have h1 : ∀ c : C2Function,
      (F.cluster c (3 * t)).toFinset =
      F.toFinset.filter (fun f => c2Distance f c ≤ 3 * t) := by
    intro c
    ext f
    simp only [FiniteFunctionFamily.toFinset, FiniteFunctionFamily.cluster,
      Finset.mem_filter, Set.Finite.mem_toFinset]
    ; simp [c2Ball]
  have h2 : ∀ c : C2Function,
      ((F.cluster c (3 * t)).card : ℝ) =
      ∑ f ∈ F.toFinset, if c2Distance f c ≤ 3 * t then (1 : ℝ) else 0 := by
    intro c
    have h_eq : (F.cluster c (3 * t)).toFinset =
        F.toFinset.filter (fun f => c2Distance f c ≤ 3 * t) := h1 c
    have h_card : (F.cluster c (3 * t)).card =
        (F.toFinset.filter (fun f => c2Distance f c ≤ 3 * t)).card := by
      have h3 : (F.cluster c (3 * t)).card = (F.cluster c (3 * t)).toFinset.card :=
        h_card_eq (F.cluster c (3 * t))
      rw [h3, h_eq]
    rw [h_card]
    rw [Finset.sum_ite]
    ; simp
  calc
    (∑ c ∈ centers, ((F.cluster c (3 * t)).card : ℝ))
      = ∑ c ∈ centers, ∑ f ∈ F.toFinset,
          (if c2Distance f c ≤ 3 * t then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro c _
        exact h2 c
    _ = ∑ f ∈ F.toFinset, ∑ c ∈ centers,
          (if c2Distance f c ≤ 3 * t then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ f ∈ F.toFinset, ((centers.filter (fun c => c2Distance f c ≤ 3 * t)).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro f _
        rw [Finset.sum_ite]
        ; simp

end Kakeya.Cinematic
