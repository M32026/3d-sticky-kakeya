import MyLeanRepo.Kakeya.Streamlined.TubePacking.Explicit
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.SupportFreeStrongEnlargementConflictDegree
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.KStrongDegreeFromDensity

/-!
# Explicit conflict-degree constant

Exposes the explicit constant from
`support_free_strong_enlargement_conflict_degree`, which is otherwise hidden
behind an existential.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Finset
open Kakeya.Streamlined.GeometricLemmas
open Kakeya.Streamlined.IndependentCoverGeometry
open Kakeya.Streamlined.RandomTranslation
open Kakeya.Streamlined.WithShading (strong_containment_via_translation)

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/-- Explicit conflict-degree constant: `3000 * 202^4 * (3000 * K)^7`. -/
def explicitConflictConstant (K : ℝ) : ℝ :=
  3000 * (202 : ℝ)^4 * (3000 * K)^7

theorem support_free_strong_enlargement_conflict_degree_explicit
    (K : ℝ) (hK : 2 ≤ K) :
    ∀ {sigma rho : ℝ}, 0 < sigma → sigma ≤ rho → rho ≤ 1 →
    ∀ G : TubeFamily sigma, G.IsEssentiallyDistinct →
    ∀ j : Fin G.card,
      tubeConflictDegreeStrong
        (sameAxisEnlargedFamily (rho := rho) G)
        (Kakeya.deltaTubeVolume rho)
        (ENNReal.ofReal K) j ≤
      Nat.ceil (explicitConflictConstant K * (rho / sigma) ^ 4) := by
  let B : ℝ := 1000 * K
  have hB_one : 1 ≤ B := by
    have h1 : 0 < K := by linarith
    have h2 : 2000 ≤ 1000 * K := by nlinarith
    linarith
  let A_plank : ℝ := 3 * B
  have hA_one : 1 ≤ A_plank := by
    have h1 : 1 ≤ B := hB_one
    linarith
  let C_K : ℝ := explicitConflictConstant K
  have hC_K_eq : C_K = 3000 * (202 : ℝ)^4 * A_plank^7 := by
    dsimp only [C_K, explicitConflictConstant, A_plank, B] <;> ring
  have hC_K_pos : 0 < C_K := by
    dsimp only [C_K, explicitConflictConstant] <;> positivity
  have hC_bound := tube_packing_in_plank_explicit A_plank hA_one
  intro sigma rho hsigma_pos hsigma_le_rho hrho_one G hG_ed j
  let G' := sameAxisEnlargedFamily (rho := rho) G
  let V_rho := Kakeya.deltaTubeVolume rho
  let K_enn := ENNReal.ofReal K
  let S : Finset (Fin G.card) :=
    Finset.univ.filter fun k =>
      k ≠ j ∧
        volume ((G'.tube j).carrier ∩ (G'.tube k).carrier) >
          V_rho / K_enn
  have h_conflict_degree :
      tubeConflictDegreeStrong G' V_rho K_enn j = S.card := by
    simp [tubeConflictDegreeStrong, S] <;> rfl
  have hrho_pos : 0 < rho := by linarith
  have h_dilated_containment :
      ∀ k ∈ S,
        (G'.tube k).carrier ⊆ dilatedTubeCarrier B (G'.tube j) := by
    intro k hk
    have h_filter : k ≠ j ∧ volume ((G'.tube j).carrier ∩ (G'.tube k).carrier) > V_rho / K_enn := by
      simpa [S, Finset.mem_filter] using hk
    have hV_k : (G'.tube k).volume = V_rho := tube_volume_eq_deltaTubeVolume (G'.tube k)
    have h_inter_symm : volume ((G'.tube k).carrier ∩ (G'.tube j).carrier) > V_rho / ENNReal.ofReal K := by
      have h_comm : (G'.tube k).carrier ∩ (G'.tube j).carrier = (G'.tube j).carrier ∩ (G'.tube k).carrier := by
        ext x; simp [and_comm]
      rw [h_comm]; exact h_filter.2
    have h_overlap : volume ((G'.tube k).carrier ∩ (G'.tube j).carrier) > (G'.tube k).volume / ENNReal.ofReal K := by
      rw [hV_k]; exact h_inter_symm
    exact strong_containment_via_translation hrho_pos hrho_one (hK := hK) h_overlap
  have h_original_contained :
      ∀ k ∈ S, (G.tube k).carrier ⊆ dilatedTubeCarrier B (G'.tube j) := by
    intro k hk
    have h1 : (G.tube k).carrier ⊆ (G'.tube k).carrier := by
      have h2 : G'.tube k = withRadius rho (G.tube k) := by
        simp [G', sameAxisEnlargedFamily_tube]
      rw [h2]; exact carrier_subset_withRadius hsigma_le_rho (G.tube k)
    exact h1.trans (h_dilated_containment k hk)
  rcases exists_dilatedTube_outer_plank_general (B := B) hB_one hrho_pos hrho_one (G'.tube j) with
    ⟨plank, frame, hdim, hplank_contain⟩
  have hdim_A : plank.HasDimensionsInFrame frame rho rho 1 A_plank := by
    convert hdim using 1 <;> simp [A_plank] <;> ring
  have h_all_contained : ∀ k ∈ S, (G.tube k).carrier ⊆ plank.carrier := by
    intro k hk
    exact (h_original_contained k hk).trans hplank_contain
  let S_sub := TubeSubfamily.fromFinset G S
  have h_ed : S_sub.family.IsEssentiallyDistinct := TubeSubfamily.isEssentiallyDistinct S_sub hG_ed
  have h_sub_contain : ∀ i, (S_sub.family.tube i).carrier ⊆ plank.carrier := by
    intro i
    rw [S_sub.tube_eq i]
    have h2 : S_sub.embedding i ∈ S := by
      have h_emb : S_sub.embedding = (S.orderEmbOfFin rfl).toEmbedding := by rfl
      rw [h_emb]; exact Finset.orderEmbOfFin_mem S rfl i
    exact h_all_contained (S_sub.embedding i) h2
  have h_pack_bound : S_sub.family.enncard ≤ ENNReal.ofReal (C_K * (rho * rho / sigma ^ 2) ^ 2) := by
    have h := hC_bound sigma rho rho hsigma_pos hsigma_le_rho (by linarith) hrho_one plank frame hdim_A S_sub.family h_ed h_sub_contain
    simpa [hC_K_eq] using h
  have h_algebra : (rho * rho / sigma ^ 2) ^ 2 = (rho / sigma) ^ 4 := by
    field_simp [hsigma_pos.ne'] <;> ring
  rw [h_algebra] at h_pack_bound
  have h_enncard : S_sub.family.enncard = (S.card : ENNReal) := by
    simp [S_sub, TubeSubfamily.fromFinset] <;> rfl
  rw [h_enncard] at h_pack_bound
  have h_nonneg : 0 ≤ C_K * (rho / sigma) ^ 4 := by positivity
  have h_real : (S.card : ℝ) ≤ C_K * (rho / sigma) ^ 4 := by
    have h7 : ENNReal.ofReal (S.card : ℝ) ≤ ENNReal.ofReal (C_K * (rho / sigma) ^ 4) := by
      simpa using h_pack_bound
    exact (ENNReal.ofReal_le_ofReal_iff h_nonneg).mp h7
  have h8 : (S.card : ℝ) ≤ (Nat.ceil (C_K * (rho / sigma) ^ 4) : ℝ) := by
    calc (S.card : ℝ) ≤ C_K * (rho / sigma) ^ 4 := h_real
      _ ≤ (Nat.ceil (C_K * (rho / sigma) ^ 4) : ℝ) := Nat.le_ceil (C_K * (rho / sigma) ^ 4)
  have h_final : S.card ≤ Nat.ceil (C_K * (rho / sigma) ^ 4) := by exact_mod_cast h8
  rw [h_conflict_degree]
  exact h_final

end Kakeya.Streamlined.RandomTranslation.WithShading
