import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.SameAxisEnlargementConflictDegree
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.NonDistinctDilatedContainment
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.MidpointBound
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeRadius
import MyLeanRepo.Kakeya.Streamlined.IndependentCoverGeometry.DilatedTubeDimensions
import MyLeanRepo.Kakeya.Streamlined.TubePacking.Proof
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

namespace Kakeya.Streamlined

open GeometricLemmas IndependentCoverGeometry
open RandomTranslation.WithShading

theorem same_axis_enlargement_conflict_degree :
    SameAxisEnlargementConflictDegreeStatement := by
  classical
  rcases tube_packing_in_plank 3000 (by norm_num) with
    ⟨C, hC_pos, hC_bound⟩
  refine ⟨C, hC_pos, ?_⟩
  intro delta hdelta fine hF_ball U sigma rho hsigma_rho j
  let G := U.coarse sigma
  let G' := sameAxisEnlargedFamily (rho := rho.1) G
  let S : Finset (Fin G.card) :=
    Finset.univ.filter fun k =>
      k ≠ j ∧
        ¬(G'.tube j).EssentiallyDistinct (G'.tube k)
  have h_conflict_degree :
      tubeConflictDegree G' j = S.card := by
    simp [tubeConflictDegree, S]
    rfl
  have hsigma_pos : 0 < sigma.1 := by
    linarith [sigma.2.1]
  have hrho_pos : 0 < rho.1 := by
    linarith [rho.2.1]
  have hrho_one : rho.1 ≤ 1 := rho.2.2
  have h_midpoint_bound :
      ∀ k : Fin G.card, ‖tubeMidpoint (G'.tube k)‖ ≤ 3 := by
    intro k
    have h1 :
        tubeMidpoint (G'.tube k) =
          tubeMidpoint (G.tube k) := by
      simp [G', sameAxisEnlargedFamily_tube,
        withRadius_midpoint]
    rw [h1]
    exact coarse_tube_midpoint_bound
      (U.cover sigma) hF_ball
      (by linarith) (by linarith) k
  have h_dilated_containment :
      ∀ k ∈ S,
        (G'.tube k).carrier ⊆
          dilatedTubeCarrier 1000 (G'.tube j) := by
    intro k hk
    have h_filter :
        k ≠ j ∧
          ¬(G'.tube j).EssentiallyDistinct (G'.tube k) := by
      simpa [S, Finset.mem_filter] using hk
    have h_non_ed :
        ¬(G'.tube k).EssentiallyDistinct (G'.tube j) := by
      have h_symm :
          (G'.tube k).EssentiallyDistinct (G'.tube j) ↔
            (G'.tube j).EssentiallyDistinct (G'.tube k) :=
        essentiallyDistinct_symm
      exact h_symm.not.mpr h_filter.2
    exact non_distinct_dilated_containment
      hrho_pos hrho_one (G'.tube k) (G'.tube j)
      (h_midpoint_bound k) (h_midpoint_bound j) h_non_ed
  have h_original_contained :
      ∀ k ∈ S,
        (G.tube k).carrier ⊆
          dilatedTubeCarrier 1000 (G'.tube j) := by
    intro k hk
    have h1 :
        (G.tube k).carrier ⊆ (G'.tube k).carrier := by
      have h2 :
          G'.tube k = withRadius rho.1 (G.tube k) := by
        simp [G', sameAxisEnlargedFamily_tube]
      rw [h2]
      exact carrier_subset_withRadius hsigma_rho (G.tube k)
    exact h1.trans (h_dilated_containment k hk)
  rcases exists_dilatedTube_outer_plank_general
      (B := 1000) (by norm_num)
      hrho_pos hrho_one (G'.tube j) with
    ⟨plank, frame, hdim, hplank_contain⟩
  have hdim3000 :
      plank.HasDimensionsInFrame
        frame rho.1 rho.1 1 3000 := by
    convert hdim using 1
    all_goals norm_num
  have h_all_contained :
      ∀ k ∈ S, (G.tube k).carrier ⊆ plank.carrier := by
    intro k hk
    exact (h_original_contained k hk).trans hplank_contain
  let S_sub := TubeSubfamily.fromFinset G S
  have h_ed : S_sub.family.IsEssentiallyDistinct :=
    TubeSubfamily.isEssentiallyDistinct
      S_sub (U.coarse_distinct sigma)
  have h_sub_contain :
      ∀ i, (S_sub.family.tube i).carrier ⊆ plank.carrier := by
    intro i
    rw [S_sub.tube_eq i]
    have h2 : S_sub.embedding i ∈ S := by
      have h_emb :
          S_sub.embedding =
            (S.orderEmbOfFin rfl).toEmbedding := by
        rfl
      rw [h_emb]
      exact Finset.orderEmbOfFin_mem S rfl i
    exact h_all_contained (S_sub.embedding i) h2
  have h_pack_bound :
      S_sub.family.enncard ≤
        ENNReal.ofReal
          (C * (rho.1 * rho.1 / sigma.1 ^ 2) ^ 2) :=
    hC_bound sigma.1 rho.1 rho.1
      hsigma_pos hsigma_rho (by linarith) hrho_one
      plank frame hdim3000 S_sub.family h_ed h_sub_contain
  have h_algebra :
      (rho.1 * rho.1 / sigma.1 ^ 2) ^ 2 =
        (rho.1 / sigma.1) ^ 4 := by
    field_simp [hsigma_pos.ne']
  rw [h_algebra] at h_pack_bound
  have h_enncard :
      S_sub.family.enncard = (S.card : ENNReal) := by
    simp [S_sub, TubeSubfamily.fromFinset]
    rfl
  rw [h_enncard] at h_pack_bound
  have h_nonneg :
      0 ≤ C * (rho.1 / sigma.1) ^ 4 := by
    positivity
  have h_real :
      (S.card : ℝ) ≤ C * (rho.1 / sigma.1) ^ 4 := by
    have h7 :
        ENNReal.ofReal (S.card : ℝ) ≤
          ENNReal.ofReal
            (C * (rho.1 / sigma.1) ^ 4) := by
      simpa using h_pack_bound
    exact (ENNReal.ofReal_le_ofReal_iff h_nonneg).mp h7
  have h8 :
      (S.card : ℝ) ≤
        (Nat.ceil (C * (rho.1 / sigma.1) ^ 4) : ℝ) := by
    calc
      (S.card : ℝ)
          ≤ C * (rho.1 / sigma.1) ^ 4 := h_real
      _ ≤
          (Nat.ceil (C * (rho.1 / sigma.1) ^ 4) : ℝ) :=
        Nat.le_ceil (C * (rho.1 / sigma.1) ^ 4)
  have h_final :
      S.card ≤ Nat.ceil (C * (rho.1 / sigma.1) ^ 4) := by
    exact_mod_cast h8
  rw [h_conflict_degree]
  exact h_final

end Kakeya.Streamlined
