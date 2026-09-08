/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceRetainedTerminalBridges
public import Kakeya.DimensionThree.Plank.Prop66BClose

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

open ML2Assembly ML2Reduction VeryNotSticky

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- The corrected four factors retain the actual factor-shading construction.
The old protected SourceZeroFourFactors is a different conditional object. -/
structure SourceRetainedFourFactors (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (a p b : Nat) (beta fineCharge parentCharge outerCharge middleGain : Real)
    (loss : ENNReal) where
  lambda : NNReal
  seam : SourceQMiddleSeam Q Z a p b lambda loss
  three : SourceQThreeFactorBounds Q seam beta fineCharge parentCharge outerCharge
  middle : ShadedBody.multiplicity seam.middle (fun i => (seam.middleShade i).toShadedBody) <=
    (delta : ENNReal) ^ middleGain * (seam.middle.card : ENNReal) ^ beta

/-- A same-seam VNS construction includes the real all-radius input, R4 output,
downstairs count and literal Lemma91At. These are produced together. -/
structure SourceRetainedMiddleAnalysis (Q : SourceThreadedTower S T M C)
    {Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
    {a p b : Nat} {lambda : NNReal} {loss : ENNReal}
    (X : SourceQMiddleSeam Q Z a p b lambda loss)
    (beta varpi zeta v etaD nuMid e : Real) where
  rho : NNReal
  R : Real
  etaC : Real
  q : Real
  gamma : Real
  R_pos : 0 < R
  rho_pos : 0 < rho
  rho_le_one : rho <= 1
  q_pos : 0 < q
  gamma_pos : 0 < gamma
  gamma_le_q : gamma <= q
  density_budget : 3 * q <= etaD
  gain_budget : nuMid + 3 * q <= v
  scale_gain : (rho : Real) <= (delta : Real) ^ (e / 2)
  cover_parameters : SourceQCoverParameters M sourceBottomED sourceLevelED C e varpi zeta etaC R
  cover_input : SourceQCoverInput Q a p b X.jp X.middle X.middleShade rho e zeta etaC
  situation : Tube.IsRescalingSituation (sourceTowerRadius delta M p)
    (sourceTowerRadius delta M b) rho R 3
  normalized : SourceQNormalizedRows situation R_pos (Q.tube p X.jp) X.middle X.middleShade
  D : Finset iota
  E : Finset iota
  U0 : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))
  U1 : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))
  retention : SourceMiddleActualRetention situation R_pos (Q.tube p X.jp)
    (varpi * zeta / 16) q gamma gamma gamma etaD varpi zeta X.middle D E X.middleShade U0 U1
  downstairs : SourceMiddleDownstairsCount situation R_pos (Q.tube p X.jp) varpi zeta E X.middleShade
  raw_vns : Lemma91At.{u} beta varpi zeta v etaD rho
  uniformity_budget : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) <=
    (rho : ENNReal) ^ (-etaD)

/-- Every non-analytic premise of the proved GWZ 6.6(B), on actual finite
normalized tubes. The branching floor and volumetric ED are not source-line ED. -/
structure SourceRetainedPlankApplication (n : Nat) (sigma : NNReal) (eta eps2 : Real) where
  family : Finset (Fin n)
  tubes : Fin n -> ShadedTube sigma (EuclideanSpace Real (Fin 3))
  sigma_pos : 0 < sigma
  family_nonempty : family.Nonempty
  centred : forall i, i ∈ family -> (tubes i).carrier <= Metric.closedBall 0 1
  essentially_distinct : (family : Set (Fin n)).Pairwise
    (fun i j => _root_.IsEssentiallyDistinct (tubes i).carrier (tubes j).carrier)
  Cu : NNReal
  uniformity : ShadedTube.ShadedUniformTubeSet family tubes (Tube.ssfGridLen sigma) Cu
  Cu_budget : Cu <= sigma ^ (-eta)
  fullness : sigma ^ eta <= ShadedBody.fullness family (fun i => (tubes i).toShadedBody)
  rho : NNReal
  short : NNReal
  middle : NNReal
  Cw : NNReal
  Cpar : NNReal
  Czero : NNReal
  short_le_middle : short <= middle
  middle_le_one : middle <= 1
  width_budget : Cw <= sigma ^ (-eta)
  parent_budget : Cpar <= sigma ^ (-eta)
  factor_budget : Czero <= sigma ^ (-eta)
  coarse_lower : sigma ^ (1 - eps2) <= rho
  rho_le_short : rho <= short
  parents : Tube.IsUniformAtScale family (fun i => (tubes i).toTube) rho Cpar
  branching_floor : (max 1 Cpar) ^ 2 <= parents.branchingN
  parent_centred : forall j, j ∈ parents.parent ->
    (parents.parentTube j).carrier <= Metric.closedBall 0 1
  factors : Kakeya.GlobalPlankFactorization Cw short middle short_le_middle middle_le_one
    parents.parent (fun j => (parents.parentTube j).toConvexSpaceBody) Czero

/-- A conditional good-branch normalization records original tags, affine shade
images and the complete leaves before paid ED/SSF extraction. The dimensions are
compared through an explicit constant; equality with a John axis is absent. -/
structure SourceRetainedPlankNormalization (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {a m : Nat} {etaParent bias : Real} {D aw bw cw : NNReal}
    (E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw)
    (eta eps2 : Real) (sigma0 : NNReal) (comparison : NNReal) where
  coarse : iota
  coarse_mem : coarse ∈ Q.indexSet a
  selectedNodes : Finset iota
  selectedParts : Finset (Finset iota)
  parts_subset : selectedParts <= (E.factor coarse coarse_mem).parts
  nodes_eq : selectedNodes = selectedParts.sup id
  completeLeaves : Finset iota
  complete_leaves_eq : completeLeaves = S.filter (fun i => Q.place m i ∈ selectedNodes)
  leaves : Finset iota
  leaves_subset : leaves <= completeLeaves
  leaves_nonempty : leaves.Nonempty
  leaves_in_cell : leaves <= Q.cell a coarse
  n : Nat
  enumerate : Fin n ≃ {i // i ∈ leaves}
  sigma : NNReal
  application : SourceRetainedPlankApplication n sigma eta eps2
  sigma_small : sigma <= sigma0
  all_fine : application.family = Finset.univ
  affine : EuclideanSpace Real (Fin 3) ≃ᵃ[Real] EuclideanSpace Real (Fin 3)
  fineShade : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))
  fine_tubes : forall i, (fineShade i).toTube = T i
  fine_subshade : forall i, (fineShade i).shade <= (Z i).shade
  extractionLoss : NNReal
  extraction_loss_one : 1 <= extractionLoss
  fine_refinement : ShadedBody.IsCRefinement leaves (fun i => (fineShade i).toShadedBody)
    completeLeaves (fun i => (Z i).toShadedBody) extractionLoss⁻¹
  shade_images : forall j, (application.tubes j).shade = affine '' (fineShade (enumerate j)).shade
  carrier_images : forall j, affine '' (T (enumerate j)).carrier <= (application.tubes j).carrier
  jacobian_positive : 0 < affineJacobian affine
  jacobian_finite : affineJacobian affine < (⊤ : ENNReal)
  mass_image : (∑ j ∈ application.family, volume (application.tubes j).shade) =
    affineJacobian affine * ∑ i ∈ leaves, volume (fineShade i).shade
  union_image : volume (⋃ j ∈ application.family, (application.tubes j).shade) =
    affineJacobian affine * volume (⋃ i ∈ leaves, (fineShade i).shade)
  parent_origin : Fin n -> iota
  parent_origin_mem : forall j, j ∈ application.parents.parent -> parent_origin j ∈ selectedNodes
  parent_factor_origin : forall part, part ∈ application.factors.parts ->
    exists originalPart, originalPart ∈ selectedParts /\
      forall j, j ∈ part -> parent_origin j ∈ originalPart
  source_parent_containment : forall j, j ∈ application.parents.parent ->
    affine '' (Q.tube m (parent_origin j)).carrier <= (application.parents.parentTube j).carrier
  comparison_one : 1 <= comparison
  scale_lower : delta / (comparison * sourceTowerRadius delta M a) <= sigma
  scale_upper : sigma <= comparison * delta / sourceTowerRadius delta M a
  aspect_comparison : application.short / application.middle <= comparison * (aw / bw)

theorem source_retained_fourFactor_ledger (Q : SourceThreadedTower S T M C)
    {Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
    {a p b : Nat} {beta f pCharge c g : Real} {loss : ENNReal}
    (hdelta : 0 < delta) (hbeta : 0 <= beta)
    (F : SourceRetainedFourFactors Q Z a p b beta f pCharge c g loss) :
    ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
      loss * (16 : ENNReal) ^ beta * (delta : ENNReal) ^ (g - f - pCharge - c) *
        (S.card : ENNReal) ^ beta := by
  have hd0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast hdelta.ne'
  have hdt : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc
    ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
        loss * ShadedBody.multiplicity (Q.cell b F.seam.jb)
          (fun i => (F.seam.fineShade i).toShadedBody) *
          ShadedBody.multiplicity F.seam.middle (fun i => (F.seam.middleShade i).toShadedBody) *
          ShadedBody.multiplicity F.seam.parents (fun i => (F.seam.parentShade i).toShadedBody) *
          ShadedBody.multiplicity F.seam.coarse (fun i => (F.seam.outerShade i).toShadedBody) :=
      F.seam.split
    _ <= loss * ((delta : ENNReal) ^ (-f) * ((Q.cell b F.seam.jb).card : ENNReal) ^ beta) *
          ((delta : ENNReal) ^ g * (F.seam.middle.card : ENNReal) ^ beta) *
          ((delta : ENNReal) ^ (-pCharge) * (F.seam.parents.card : ENNReal) ^ beta) *
          ((delta : ENNReal) ^ (-c) * (F.seam.coarse.card : ENNReal) ^ beta) :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl F.three.fine)
        F.middle) F.three.parent) F.three.outer
    _ = loss * (delta : ENNReal) ^ (g - f - pCharge - c) *
          (((Q.cell b F.seam.jb).card : ENNReal) * F.seam.middle.card *
            F.seam.parents.card * F.seam.coarse.card) ^ beta := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hbeta, ENNReal.mul_rpow_of_nonneg _ _ hbeta,
        ENNReal.mul_rpow_of_nonneg _ _ hbeta]
      rw [show g - f - pCharge - c = ((-f + g) + -pCharge) + -c by ring]
      rw [ENNReal.rpow_add _ _ hd0 hdt, ENNReal.rpow_add _ _ hd0 hdt,
        ENNReal.rpow_add _ _ hd0 hdt]
      ring
    _ <= loss * (delta : ENNReal) ^ (g - f - pCharge - c) *
          (16 * (S.card : ENNReal)) ^ beta :=
      mul_le_mul' le_rfl (ENNReal.rpow_le_rpow F.seam.card_product hbeta)
    _ = loss * (16 : ENNReal) ^ beta * (delta : ENNReal) ^ (g - f - pCharge - c) *
          (S.card : ENNReal) ^ beta := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hbeta]
      ring

/-- The exact proved 6.6(B) application, kept separate from constructing it. -/
theorem source_exists_retained_plank_application_accuracy {beta eps2 : Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1)
    (hKT : KatzTaoEstimate (EuclideanSpace Real (Fin 3)) beta)
    (hF : FrostmanEstimate (EuclideanSpace Real (Fin 3)) beta)
    (heps2 : 0 < eps2) (heps21 : eps2 <= 1) (eps : Real) (heps : 0 < eps) :
    exists eta : Real, 0 < eta /\ exists sigma0 : NNReal, 0 < sigma0 /\
      forall (n : Nat) (sigma : NNReal), sigma <= sigma0 ->
      forall A : SourceRetainedPlankApplication n sigma eta eps2,
        ShadedBody.multiplicity A.family (fun i => (A.tubes i).toShadedBody) <=
          (sigma : ENNReal) ^ (-eps) *
            Kakeya.maxDensity A.family (fun i => (A.tubes i).toConvexSpaceBody) ^ (1 - beta) *
            ((A.short : ENNReal) / (A.middle : ENNReal)) ^ beta *
            (A.family.card : ENNReal) ^ beta := by
  obtain ⟨eta, heta, sigma0, hsigma0, happ⟩ :=
    Kakeya.tubeMultiplicityOfGlobalPlankFactorisation hbeta0 hbeta1 hKT hF
      heps2 heps21 eps heps
  refine ⟨eta, heta, sigma0, hsigma0, ?_⟩
  intro n sigma hsigma A
  exact happ A.family A.sigma_pos A.tubes hsigma A.centred A.essentially_distinct
    ⟨A.Cu, A.Cu_budget, ⟨A.uniformity⟩⟩ A.fullness A.rho A.short A.middle
    A.short_le_middle A.middle_le_one A.Cw A.Cpar A.Czero A.width_budget
    A.parent_budget A.factor_budget A.coarse_lower A.rho_le_short A.parents
    A.branching_floor A.parent_centred (by
      convert A.factors using 1)

end Kakeya.ML2Core
