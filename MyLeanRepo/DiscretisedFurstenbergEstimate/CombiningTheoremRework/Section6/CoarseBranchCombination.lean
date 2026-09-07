module

/-
  Coarse Branch Combination — Assembly + Provenance Transfer

  Combines:
  1. Coarse branch assembly (ratio data + B1 product + loss ledger)
  2. Provenance transfer via S0_line (FixedPackingBound + ProvenanceRadiusAddition)
  3. Absorption of C_pack and scale/exponent differences

  Chain:
    coarse_branch_assembly_dyadic → N₀ ≥ δn^{-(2s+netGain)}
    N₀ = card(fineTubes)  [fineTubes = B1-retained family]
    provenance transfer → card ≤ C_pack * Ncover(δ, originalFamily)
    Therefore: Ncover ≥ δn^{-(2s+netGain)} / C_pack
    Absorption hypothesis → Ncover ≥ δ^{-(2s+εInc)}

  IMPORTANT: fineTubes must be the SAME B1-retained family used to construct
  both CoarseRatioData (coarse count NΔ) and FineCor25Data (fine count NQ).
  The B1 product inequality K*N₀*MΔ*MQ ≥ NΔ*NQ*M relates these counts.

  Whiteprint node: coarse_branch_combination
  Status: PRODUCTION
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section6.Types
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CoarseBranchAssemblyClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.FixedPackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.ProvenanceRadiusAddition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.Gap1Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section6

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence (S0_line S0_line_lipschitz)
open DyadicCardToNcover (toAffineLine)
open FixedPackingBound (C_pack)

abbrev Ncover' {X : Type*} [PseudoMetricSpace X] (δ : ℝ) (E : Set X) : ENNReal :=
  Metric.externalCoveringNumber δ.toNNReal E

/-- ENNReal division cancellation: (a * b) / a = b for finite nonzero a. -/
private lemma ennreal_mul_div_cancel {a b : ENNReal} (ha_ne_zero : a ≠ 0) (ha_ne_top : a ≠ ⊤) :
    (a * b) / a = b := by
  have h1 : a * a⁻¹ = 1 := ENNReal.mul_inv_cancel ha_ne_zero ha_ne_top
  have h2 : (a * b) / a = (a * b) * a⁻¹ := by rfl
  rw [h2]
  have h3 : (a * b) * a⁻¹ = a * (b * a⁻¹) := by rw [mul_assoc]
  rw [h3]
  have h4 : b * a⁻¹ = a⁻¹ * b := by rw [mul_comm]
  rw [h4]
  have h5 : a * (a⁻¹ * b) = (a * a⁻¹) * b := by rw [mul_assoc]
  rw [h5, h1, one_mul]

/-- Coarse branch combination: from ratio data + B1 product + loss ledger +
    provenance data, prove the original family Ncover lower bound.

    All scale-dependent data is at `δn = dyadicDelta n`.

    1. `coarse_branch_assembly_dyadic` → N₀ ≥ δn^{-(2s+netGain)}
    2. S0 provenance transfer → N₀ ≤ C_pack * Ncover(δ, originalFamily)
    3. Absorption hypothesis bridges to final δ^{-(2s+εInc)}
-/
lemma coarse_branch_combination
    {n : ℕ} {s εInc : ℝ}
    (hn_pos : 0 < n)
    (hs_pos : 0 < s)
    (hεInc_pos : 0 < εInc)
    -- Scale parameter δ (original family scale); δn = dyadicDelta n is implicit
    {δ : ℝ}
    (hδ_pos : 0 < δ)
    {originalFamily : Set AffineLine}
    -- Coarse branch assembly inputs (all at dyadicDelta n)
    (coarseData : CoarseRatioData (DiscretisedFurstenbergEstimate.dyadicDelta n) s)
    (fineData : FineCor25Data (DiscretisedFurstenbergEstimate.dyadicDelta n) s)
    (pkg : B1ProductPackage (DiscretisedFurstenbergEstimate.dyadicDelta n) s)
    (h_product : (pkg.K : ℝ) * (pkg.N₀ : ℝ) *
        coarseData.coarseMultiplicity * fineData.localMultiplicity ≥
      coarseData.coarseCount * fineData.localCount * (pkg.M : ℝ))
    (ledger : LossLedger coarseData.coarseGain fineData.localLoss pkg)
    -- B1-retained tube family (e.g. fineTubesOfData data) — used for provenance
    (fineTubes : Finset (DiscretisedFurstenbergEstimate.DyadicTube n))
    (h_card_eq : fineTubes.card = pkg.N₀)
    (hm : ∀ T ∈ fineTubes, |T.slope| ≤ 1)
    (hb : ∀ T ∈ fineTubes, |T.intercept| ≤ 3)
    -- Provenance / scale data
    (h_scale : DiscretisedFurstenbergEstimate.dyadicDelta n ≤ δ / 4)
    (h_scale2 : δ / 4 < 4 * DiscretisedFurstenbergEstimate.dyadicDelta n)
    (h_thick : ∀ (T : DiscretisedFurstenbergEstimate.DyadicTube n), T ∈ fineTubes →
        ∃ (ℓ : AffineLine), ℓ ∈ originalFamily ∧
          dist (toAffineLine T) (S0_line ℓ) ≤ (15 / 2 : ℝ) * (δ / 4))
    -- Absorption: bridges δn^{-(2s+netGain)} / C_pack ≥ δ^{-(2s+εInc)}
    (h_absorb : ENNReal.ofReal (δ ^ (-(2 * s + εInc))) ≤
        ENNReal.ofReal ((DiscretisedFurstenbergEstimate.dyadicDelta n) ^ (-(2 * s + ledger.netGain))) / (C_pack : ENNReal)) :
    ENNReal.ofReal (δ ^ (-(2 * s + εInc))) ≤ Ncover' δ originalFamily := by
  let δn : ℝ := DiscretisedFurstenbergEstimate.dyadicDelta n
  let δ' : ℝ := δ / 4
  have hδn_pos : 0 < δn := by
    exact DiscretisedFurstenbergEstimate.dyadicDelta_pos n
  have hδ'_pos : 0 < δ' := by positivity
  let A : Set AffineLine := toAffineLine '' (fineTubes : Set (DiscretisedFurstenbergEstimate.DyadicTube n))

  -- Step 1: Coarse branch assembly → N₀ ≥ δn^{-(2s+netGain)}
  have h_N0_lower : (pkg.N₀ : ENNReal) ≥ ENNReal.ofReal (δn ^ (-(2 * s + ledger.netGain))) :=
    coarse_branch_assembly_dyadic
      (hn_pos := hn_pos)
      (coarseData := coarseData)
      (fineData := fineData)
      (pkg := pkg)
      (h_product := h_product)
      (ledger := ledger)

  -- Step 2: card(fineTubes) = N₀
  have h_card_lower : (fineTubes.card : ENNReal) ≥ ENNReal.ofReal (δn ^ (-(2 * s + ledger.netGain))) := by
    have h1 : (fineTubes.card : ENNReal) = (pkg.N₀ : ENNReal) := by
      rw [h_card_eq]
    rw [h1]
    exact h_N0_lower

  -- Step 3: Provenance transfer → card ≤ C_pack * Ncover
  have hA_fin : A.Finite := Set.Finite.image _ (Finset.finite_toSet _)
  have h_packing : ∀ (x : AffineLine), (A ∩ Metric.closedBall x (64 * δn)).ncard ≤ C_pack := by
    intro x
    simpa [A] using FixedPackingBound.fixed_packing_bound hm hb x
  have h_thick' : ∀ (a : AffineLine), a ∈ A →
      ∃ (b : AffineLine), b ∈ S0_line '' originalFamily ∧ dist a b ≤ (15 / 2 : ℝ) * δ' := by
    intro a ha
    rcases ha with ⟨T, hT, rfl⟩
    rcases h_thick T hT with ⟨ℓ, hℓ, hdist⟩
    exact ⟨S0_line ℓ, Set.mem_image_of_mem S0_line hℓ, hdist⟩
  have hLipschitz : ∀ (x y : AffineLine), dist (S0_line x) (S0_line y) ≤ 2 * dist x y := by
    intro x y
    exact S0_line_lipschitz.dist_le_mul x y
  have h_prov_ncard : A.ncard ≤ (C_pack : ENNReal) * Ncover' δ originalFamily :=
    ProvenanceRadiusAddition.provenance_radius_addition_transfer
      (hA_fin := hA_fin)
      (hδn_pos := hδn_pos)
      (hδ'_pos := hδ'_pos)
      (hδ_pos := hδ_pos)
      (h_scale2 := h_scale2)
      (hδ'_eq := by rfl)
      (h_thick := h_thick')
      (hLipschitz := hLipschitz)
      (h_packing := h_packing)
  have h_inj : Set.InjOn toAffineLine (fineTubes : Set (DiscretisedFurstenbergEstimate.DyadicTube n)) := by
    intro T1 hT1 T2 hT2 h_eq
    exact FixedPackingBound.toAffineLine_injective_on_bounded
      ⟨hm T1 hT1, hb T1 hT1⟩ ⟨hm T2 hT2, hb T2 hT2⟩ h_eq
  have h_ncard : A.ncard = (fineTubes.card : ENNReal) := by
    rw [Set.ncard_image_of_injOn h_inj] <;> simp [A]
  have h_prov : (fineTubes.card : ENNReal) ≤ (C_pack : ENNReal) * Ncover' δ originalFamily := by
    rw [← h_ncard]
    exact h_prov_ncard

  -- Step 4: Combine: δn^{-(2s+netGain)} ≤ C_pack * Ncover
  have h_main : ENNReal.ofReal (δn ^ (-(2 * s + ledger.netGain))) ≤
      (C_pack : ENNReal) * Ncover' δ originalFamily := by
    calc ENNReal.ofReal (δn ^ (-(2 * s + ledger.netGain)))
      ≤ (fineTubes.card : ENNReal) := h_card_lower
    _ ≤ (C_pack : ENNReal) * Ncover' δ originalFamily := h_prov

  -- Step 5: Divide by C_pack
  have h_Cpack_ne_zero : (C_pack : ENNReal) ≠ 0 := by
    simp [C_pack] <;> norm_num
  have h_Cpack_ne_top : (C_pack : ENNReal) ≠ ⊤ := by
    simp [C_pack] <;> norm_num
  have h_div : ENNReal.ofReal (δn ^ (-(2 * s + ledger.netGain))) / (C_pack : ENNReal) ≤
      Ncover' δ originalFamily := by
    have h2 : ENNReal.ofReal (δn ^ (-(2 * s + ledger.netGain))) / (C_pack : ENNReal) ≤
        ((C_pack : ENNReal) * Ncover' δ originalFamily) / (C_pack : ENNReal) := by
      gcongr
    rw [ennreal_mul_div_cancel h_Cpack_ne_zero h_Cpack_ne_top] at h2
    exact h2

  -- Step 6: Apply absorption hypothesis
  exact le_trans h_absorb h_div

end DirecretisedFurstenbergEstimate.Section6

end
