module

/-
  Continuous-to-finite extraction theorem for AffineLine fibers.

  Given potentially-infinite fibers of AffineLines that are (δ,s,C_T)-sets,
  extract finite δ-separated sub-fibers preserving:
  - S-set property (with constant max 1 (K_pack * C_T))
  - Near property (each tube passes within δ of its point)
  - Boundedness (offset within closed ball of radius 2)
  - Cardinality lower bound: |Fp| ≥ (C_T * δ^s)⁻¹

  Uses extract_finite_tube_sset_with_card and sset_ncover_lower_bound.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.CardinalityLowerBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
open DirecretisedFurstenbergEstimate ImprovedIncidenceAssembly

noncomputable section

namespace ContinuousExtraction

/-- Extract finite δ-separated sub-fibers from continuous (potentially infinite)
    S-set fibers of AffineLines, preserving near property, boundedness, and
    giving a cardinality lower bound. -/
theorem continuous_to_finite_extraction
    {δ s C_T : ℝ}
    {P : Set EuclideanPlane}
    (Tp : ∀ (p : EuclideanPlane), p ∈ P → Set AffineLine)
    (hTp_sset : ∀ p hp, IsDeltaSSet δ s C_T (Tp p hp))
    (hTp_bdd : ∀ p hp, Bornology.IsBounded (Tp p hp))
    (hTp_near : ∀ p hp, ∀ ℓ ∈ Tp p hp, p ∈ Metric.cthickening δ ℓ.1)
    (hTp_offset : ∀ p hp, ∀ ℓ ∈ Tp p hp, ℓ.offset ∈ Metric.closedBall 0 2) :
    ∃ (Fp : ∀ (p : EuclideanPlane), p ∈ P → Finset AffineLine),
      (∀ p hp, (Fp p hp : Set AffineLine) ⊆ Tp p hp) ∧
      (∀ p hp, (Fp p hp).Nonempty) ∧
      (∀ p hp, Set.Pairwise (Fp p hp : Set AffineLine) (fun x y => δ ≤ dist x y)) ∧
      (∀ p hp, IsDeltaSSet δ s
        (max 1 (MainAppendix.affineLine_packing_constant * C_T))
        (Fp p hp : Set AffineLine)) ∧
      (∀ p hp, (Fp p hp).card ≥ (C_T * δ^s)⁻¹) ∧
      (∀ p hp, ∀ ℓ ∈ Fp p hp, p ∈ Metric.cthickening δ ℓ.1) ∧
      (∀ p hp, ∀ ℓ ∈ Fp p hp, ℓ.offset ∈ Metric.closedBall 0 2) := by
  choose F hF_sub hF_nonempty hF_sep hF_sset hF_card using
    fun (p : EuclideanPlane) (hp : p ∈ P) =>
      extract_finite_tube_sset_with_card (hTp_sset p hp) (hTp_bdd p hp)
  let Fp : ∀ (p : EuclideanPlane), p ∈ P → Finset AffineLine := F
  have h_card_lower : ∀ (p : EuclideanPlane) (hp : p ∈ P),
      (Fp p hp).card ≥ (C_T * δ^s)⁻¹ := by
    intro p hp
    have h1 : ENNReal.ofReal ((C_T * δ^s)⁻¹) ≤
        (Metric.externalCoveringNumber δ.toNNReal (Tp p hp) : ENNReal) :=
      ImprovedIncidenceAssembly.sset_ncover_lower_bound (hTp_sset p hp)
    have h2 : (Metric.externalCoveringNumber δ.toNNReal (Tp p hp) : ENNReal) ≤
        (Fp p hp).card := hF_card p hp
    have h3 : ENNReal.ofReal ((C_T * δ^s)⁻¹) ≤ (Fp p hp).card :=
      le_trans h1 h2
    have h_pos : 0 ≤ (C_T * δ^s)⁻¹ := by
      have hC_pos : 0 < C_T := (hTp_sset p hp).2.2.1
      have hδ_pos : 0 < δ := (hTp_sset p hp).2.1
      have hs_nonneg : 0 ≤ s := (hTp_sset p hp).2.2.2.1
      have h : 0 < C_T * δ^s := by positivity
      exact inv_nonneg.mpr h.le
    exact_mod_cast h3
  exact ⟨Fp,
    hF_sub,
    hF_nonempty,
    hF_sep,
    hF_sset,
    h_card_lower,
    fun p hp ℓ hℓ => hTp_near p hp ℓ (hF_sub p hp hℓ),
    fun p hp ℓ hℓ => hTp_offset p hp ℓ (hF_sub p hp hℓ)⟩

end ContinuousExtraction
