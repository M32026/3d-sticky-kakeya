import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.SameAxisEnlargementConflictDegree
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DeterministicHelpers
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.StrongNonDistinctDilatedContainment
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.MidpointBound
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeRadius
import MyLeanRepo.Kakeya.Streamlined.IndependentCoverGeometry.DilatedTubeDimensions
import MyLeanRepo.Kakeya.Streamlined.TubePacking.Proof
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Streamlined.CombinatorialLemmas.StrongEDExtraction
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.StrongConflictBasic

/-!
# K-strong ED conflict degree for coaxial enlargements

Generalizes `same_axis_enlargement_conflict_degree` from regular ED
(intersection ≤ V/2) to K-strong ED (intersection ≤ V/K).

The geometric input is a K-parameterized dilated containment:
if `vol(T1 ∩ T2) > V/K`, then `T1 ⊆ dilatedTubeCarrier (1000*K) T2`.
This follows from the same Rogers-Shephard argument as
`non_distinct_dilated_containment`, with the constant 128 replaced by 64*K.

The packing proof is otherwise identical: conflicting original σ-tubes are
ED (inherited from the UTS), contained in a plank of dimensions
ρ × ρ × 1 × 3000K around the enlarged reference tube, and packed to yield
the bound `C_K * (ρ/σ)^4`.

## Main result

- `strong_ed_enlargement_conflict_degree`: K-strong conflict degree bound.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Finset Kakeya.Streamlined
open Kakeya.Streamlined.GeometricLemmas
open Kakeya.Streamlined.IndependentCoverGeometry
open Kakeya.Streamlined.RandomTranslation
open Kakeya.Streamlined.RandomTranslation.WithShading

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/-- **K-strong ED conflict degree bound for coaxial enlargements**.

For a UTS coarse family at scale σ, enlarged to radius ρ, the number of
K-strong non-ED neighbors of any enlarged tube is at most
`Nat.ceil (C_K * (ρ/σ)^4)`, where `C_K` depends on K but not on δ, σ, ρ,
or the family.

Proof: identical to `same_axis_enlargement_conflict_degree`, using
`strong_non_distinct_dilated_containment_lemma` and a plank of dimensions
ρ × ρ × 1 × 3000K.
-/
lemma strong_ed_enlargement_conflict_degree
    (K : ℝ) (hK : 2 ≤ K) :
    ∃ C_K : ℝ, 0 < C_K ∧
      ∀ {δ : ℝ}, 0 < δ →
        ∀ (fine : TubeFamily δ), fine.IsInUnitBall →
          ∀ (U : UniformTubeStructure fine),
            ∀ (sigma rho : AdmissibleScale δ), sigma.1 ≤ rho.1 →
              ∀ (j : Fin (U.coarse sigma).card),
                tubeConflictDegreeStrong
                  (sameAxisEnlargedFamily (rho := rho.1) (U.coarse sigma))
                  (Kakeya.deltaTubeVolume rho.1) (ENNReal.ofReal K) j ≤
                  Nat.ceil (C_K * (rho.1 / sigma.1) ^ 4) := by
  classical
  let B : ℝ := 1000 * K
  have hB_one : 1 ≤ B := by
    have h1 : 0 < K := by linarith
    have h2 : 1000 * K ≥ 2000 := by nlinarith
    linarith
  let A_plank : ℝ := 3 * B
  have hA_one : 1 ≤ A_plank := by
    have h1 : 1 ≤ B := hB_one
    linarith
  rcases tube_packing_in_plank A_plank hA_one with
    ⟨C_K, hC_K_pos, hC_bound⟩
  refine ⟨C_K, hC_K_pos, ?_⟩
  intro δ hδ fine hF_ball U sigma rho hsigma_rho j
  let G := U.coarse sigma
  let G' := sameAxisEnlargedFamily (rho := rho.1) G
  let V_rho := Kakeya.deltaTubeVolume rho.1
  let K_enn := ENNReal.ofReal K
  let S : Finset (Fin G.card) :=
    Finset.univ.filter fun k =>
      k ≠ j ∧ volume ((G'.tube j).carrier ∩ (G'.tube k).carrier) > V_rho / K_enn
  have h_conflict_degree :
      tubeConflictDegreeStrong G' V_rho K_enn j = S.card := by
    simp [tubeConflictDegreeStrong, S] <;> rfl
  have hsigma_pos : 0 < sigma.1 := by linarith [sigma.2.1]
  have hrho_pos : 0 < rho.1 := by linarith [rho.2.1]
  have hrho_one : rho.1 ≤ 1 := rho.2.2
  have h_midpoint_bound :
      ∀ k : Fin G.card, ‖tubeMidpoint (G'.tube k)‖ ≤ 3 := by
    intro k
    have h1 : tubeMidpoint (G'.tube k) = tubeMidpoint (G.tube k) := by
      simp [G', sameAxisEnlargedFamily_tube, withRadius_midpoint]
    rw [h1]
    exact coarse_tube_midpoint_bound (U.cover sigma) hF_ball
      (by linarith) (by linarith) k
  have hV_j : (G'.tube j).volume = V_rho := by
    exact tube_volume_eq_deltaTubeVolume (G'.tube j)
  have h_dilated_containment :
      ∀ k ∈ S, (G'.tube k).carrier ⊆ dilatedTubeCarrier B (G'.tube j) := by
    intro k hk
    have h_filter : k ≠ j ∧
        volume ((G'.tube j).carrier ∩ (G'.tube k).carrier) > V_rho / K_enn := by
      simpa [S, Finset.mem_filter] using hk
    have hV_k : (G'.tube k).volume = V_rho :=
      tube_volume_eq_deltaTubeVolume (G'.tube k)
    have h_inter_symm : volume ((G'.tube k).carrier ∩ (G'.tube j).carrier) >
        V_rho / ENNReal.ofReal K := by
      have h_comm : (G'.tube k).carrier ∩ (G'.tube j).carrier =
          (G'.tube j).carrier ∩ (G'.tube k).carrier := by
        ext x; simp [and_comm]
      rw [h_comm]
      exact h_filter.2
    have h_overlap : volume ((G'.tube k).carrier ∩ (G'.tube j).carrier) >
        (G'.tube k).volume / ENNReal.ofReal K := by
      rw [hV_k]
      exact h_inter_symm
    exact strong_non_distinct_dilated_containment_lemma
        hrho_pos hrho_one (G'.tube k) (G'.tube j)
        (h_midpoint_bound k) (h_midpoint_bound j)
        (hK := hK) h_overlap
  have h_original_contained :
      ∀ k ∈ S, (G.tube k).carrier ⊆ dilatedTubeCarrier B (G'.tube j) := by
    intro k hk
    have h1 : (G.tube k).carrier ⊆ (G'.tube k).carrier := by
      have h2 : G'.tube k = withRadius rho.1 (G.tube k) := by
        simp [G', sameAxisEnlargedFamily_tube]
      rw [h2]
      exact carrier_subset_withRadius hsigma_rho (G.tube k)
    exact h1.trans (h_dilated_containment k hk)
  rcases exists_dilatedTube_outer_plank_general
      (B := B) hB_one hrho_pos hrho_one (G'.tube j) with
    ⟨plank, frame, hdim, hplank_contain⟩
  have hdim_A :
      plank.HasDimensionsInFrame frame rho.1 rho.1 1 A_plank := by
    convert hdim using 1 <;> simp [A_plank] <;> ring
  have h_all_contained :
      ∀ k ∈ S, (G.tube k).carrier ⊆ plank.carrier := by
    intro k hk
    exact (h_original_contained k hk).trans hplank_contain
  let S_sub := TubeSubfamily.fromFinset G S
  have h_ed : S_sub.family.IsEssentiallyDistinct :=
    TubeSubfamily.isEssentiallyDistinct S_sub (U.coarse_distinct sigma)
  have h_sub_contain :
      ∀ i, (S_sub.family.tube i).carrier ⊆ plank.carrier := by
    intro i
    rw [S_sub.tube_eq i]
    have h2 : S_sub.embedding i ∈ S := by
      have h_emb : S_sub.embedding = (S.orderEmbOfFin rfl).toEmbedding := by rfl
      rw [h_emb]
      exact Finset.orderEmbOfFin_mem S rfl i
    exact h_all_contained (S_sub.embedding i) h2
  have h_pack_bound :
      S_sub.family.enncard ≤
        ENNReal.ofReal (C_K * (rho.1 * rho.1 / sigma.1 ^ 2) ^ 2) :=
    hC_bound sigma.1 rho.1 rho.1
      hsigma_pos hsigma_rho (by linarith) hrho_one
      plank frame hdim_A S_sub.family h_ed h_sub_contain
  have h_algebra :
      (rho.1 * rho.1 / sigma.1 ^ 2) ^ 2 = (rho.1 / sigma.1) ^ 4 := by
    field_simp [hsigma_pos.ne'] <;> ring
  rw [h_algebra] at h_pack_bound
  have h_enncard : S_sub.family.enncard = (S.card : ENNReal) := by
    simp [S_sub, TubeSubfamily.fromFinset] <;> rfl
  rw [h_enncard] at h_pack_bound
  have h_nonneg : 0 ≤ C_K * (rho.1 / sigma.1) ^ 4 := by positivity
  have h_real : (S.card : ℝ) ≤ C_K * (rho.1 / sigma.1) ^ 4 := by
    have h7 : ENNReal.ofReal (S.card : ℝ) ≤
        ENNReal.ofReal (C_K * (rho.1 / sigma.1) ^ 4) := by
      simpa using h_pack_bound
    exact (ENNReal.ofReal_le_ofReal_iff h_nonneg).mp h7
  have h8 : (S.card : ℝ) ≤
      (Nat.ceil (C_K * (rho.1 / sigma.1) ^ 4) : ℝ) := by
    calc
      (S.card : ℝ) ≤ C_K * (rho.1 / sigma.1) ^ 4 := h_real
      _ ≤ (Nat.ceil (C_K * (rho.1 / sigma.1) ^ 4) : ℝ) :=
        Nat.le_ceil (C_K * (rho.1 / sigma.1) ^ 4)
  have h_final : S.card ≤ Nat.ceil (C_K * (rho.1 / sigma.1) ^ 4) := by
    exact_mod_cast h8
  rw [h_conflict_degree]
  exact h_final

end Kakeya.Streamlined.RandomTranslation.WithShading

end
