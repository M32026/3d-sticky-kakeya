import MyLeanRepo.Kakeya.Streamlined.IndependentCoverGeometry.DilatedTubeDimensions
import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverGeometry
import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverContainmentFibers
import MyLeanRepo.Kakeya.Streamlined.TubePacking.Proof

/-!
# Packing related parents in dilated paper-grid covers

The validated Section 2 refinement supplies independent dilated covers only
on the distinguished paper grid.  For a fixed coarser parent, the related
finer parents are essentially distinct and lie in one framed outer plank.
The phase-space packing theorem therefore gives the expected fourth-power
relation-fiber bound.
-/

noncomputable section

namespace Kakeya.Streamlined

open IndependentCoverGeometry

/--
For each fixed cover dilation `A`, every relation fiber between distinguished
paper-grid covers has cardinality
`O_A((sigma / rho)^4)`.
-/
def IndependentDilatedCoverRelatedPackingStatement (A : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ delta : ℝ, 0 < delta →
      ∀ hdelta_le_one : delta ≤ 1,
      ∀ fine : TubeFamily delta,
        fine.IsInUnitBall →
        ∀ U : DilatedDiscreteUniformTubeStructure
            (A := A) fine hdelta_le_one,
        ∀ r s : UniformScaleIndex delta,
          (uniformScale delta hdelta_le_one r).1 ≤
              (uniformScale delta hdelta_le_one s).1 →
          ∀ k : Fin (U.coarse s).card,
            ((U.relatedIndices r s k).card : ℝ) ≤
              C *
                ((uniformScale delta hdelta_le_one s).1 /
                  (uniformScale delta hdelta_le_one r).1) ^ 4

/--
The same fourth-power packing bound for the full containment fiber, not only
the parents selected by a common-child parent assignment.
-/
def IndependentDilatedCoverContainmentPackingStatement (A : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ delta : ℝ, 0 < delta →
      ∀ hdelta_le_one : delta ≤ 1,
      ∀ fine : TubeFamily delta,
        ∀ U : DilatedDiscreteUniformTubeStructure
            (A := A) fine hdelta_le_one,
        ∀ r s : UniformScaleIndex delta,
          (uniformScale delta hdelta_le_one r).1 ≤
              (uniformScale delta hdelta_le_one s).1 →
          ∀ k : Fin (U.coarse s).card,
            ((U.containedParentIndices r s k).card : ℝ) ≤
              C *
                ((uniformScale delta hdelta_le_one s).1 /
                  (uniformScale delta hdelta_le_one r).1) ^ 4

namespace DilatedDiscreteUniformTubeStructure

theorem related_parent_packing
    (A : ℝ) (hA : 1 ≤ A) :
    IndependentDilatedCoverRelatedPackingStatement A := by
  let D := independentCoverParentDilation A
  have hD : 1 ≤ D := by
    dsimp only [D, independentCoverParentDilation]
    nlinarith [sq_nonneg A]
  have h3D : 1 ≤ 3 * D := by
    nlinarith
  rcases tube_packing_in_plank (3 * D) h3D with
    ⟨C, hC, hpacking⟩
  refine ⟨C, hC, ?_⟩
  intro delta hdelta hdelta_le_one fine hfine U r s hrs k
  let rho := (uniformScale delta hdelta_le_one r).1
  let sigma := (uniformScale delta hdelta_le_one s).1
  have hrho_pos : 0 < rho :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1
  have hsigma_pos : 0 < sigma :=
    lt_of_lt_of_le hrho_pos hrs
  have hsigma_one : sigma ≤ 1 :=
    (uniformScale delta hdelta_le_one s).property.2
  rcases exists_dilatedTube_outer_plank_general
      hD hsigma_pos hsigma_one ((U.coarse s).tube k) with
    ⟨plank, frame, hdimensions, hdilated⟩
  let S := U.relatedSubfamily r s k
  have hdistinct : S.family.IsEssentiallyDistinct :=
    U.relatedSubfamily_essentiallyDistinct r s k
  have hcontain :
      ∀ i : Fin S.family.card,
        (S.family.tube i).carrier ⊆ plank.carrier := by
    intro i
    let j : Fin (U.coarse r).card := S.embedding i
    have hj : j ∈ U.relatedIndices r s k := by
      exact Finset.orderEmbOfFin_mem
        (U.relatedIndices r s k) rfl i
    have hrelation : U.ParentRelation r s j k :=
      (U.mem_relatedIndices_iff r s k j).mp hj
    have hparent :
        ((U.coarse r).tube j).carrier ⊆
          dilatedTubeCarrier D ((U.coarse s).tube k) := by
      simpa [D] using
        U.related_parent_containment hA hdelta hfine r s
          hrs j k hrelation
    rw [S.tube_eq i]
    exact hparent.trans hdilated
  have hpacking_ennreal :
      S.family.enncard ≤
        ENNReal.ofReal
          (C * (sigma * sigma / rho ^ 2) ^ 2) :=
    hpacking rho sigma sigma
      hrho_pos hrs le_rfl hsigma_one
      plank frame hdimensions S.family hdistinct hcontain
  have hleft_top : S.family.enncard ≠ ⊤ := by
    simp [TubeFamily.enncard]
  have hright_top :
      ENNReal.ofReal
          (C * (sigma * sigma / rho ^ 2) ^ 2) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hreal :
      S.family.enncard.toReal ≤
        (ENNReal.ofReal
          (C * (sigma * sigma / rho ^ 2) ^ 2)).toReal :=
    (ENNReal.toReal_le_toReal hleft_top hright_top).mpr
      hpacking_ennreal
  have hexpr_nonneg :
      0 ≤ C * (sigma * sigma / rho ^ 2) ^ 2 := by
    positivity
  have hleft :
      S.family.enncard.toReal =
        ((U.relatedIndices r s k).card : ℝ) := by
    simp [S,
      DilatedDiscreteUniformTubeStructure.relatedSubfamily,
      TubeSubfamily.fromFinset, TubeFamily.enncard]
  have hright :
      (ENNReal.ofReal
          (C * (sigma * sigma / rho ^ 2) ^ 2)).toReal =
        C * (sigma / rho) ^ 4 := by
    rw [ENNReal.toReal_ofReal hexpr_nonneg]
    field_simp [hrho_pos.ne']
    <;> ring
  rw [hleft, hright] at hreal
  exact hreal

theorem contained_parent_packing
    (A : ℝ) (hA : 1 ≤ A) :
    IndependentDilatedCoverContainmentPackingStatement A := by
  let D := independentCoverParentDilation A
  have hD : 1 ≤ D := by
    dsimp only [D, independentCoverParentDilation]
    nlinarith [sq_nonneg A]
  have h3D : 1 ≤ 3 * D := by
    nlinarith
  rcases tube_packing_in_plank (3 * D) h3D with
    ⟨C, hC, hpacking⟩
  refine ⟨C, hC, ?_⟩
  intro delta hdelta hdelta_le_one fine U r s hrs k
  let rho := (uniformScale delta hdelta_le_one r).1
  let sigma := (uniformScale delta hdelta_le_one s).1
  have hrho_pos : 0 < rho :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1
  have hsigma_pos : 0 < sigma :=
    lt_of_lt_of_le hrho_pos hrs
  have hsigma_one : sigma ≤ 1 :=
    (uniformScale delta hdelta_le_one s).property.2
  rcases exists_dilatedTube_outer_plank_general
      hD hsigma_pos hsigma_one ((U.coarse s).tube k) with
    ⟨plank, frame, hdimensions, hdilated⟩
  let S := U.containedParentSubfamily r s k
  have hdistinct : S.family.IsEssentiallyDistinct :=
    U.containedParentSubfamily_essentiallyDistinct r s k
  have hcontain :
      ∀ i : Fin S.family.card,
        (S.family.tube i).carrier ⊆ plank.carrier := by
    intro i
    let j : Fin (U.coarse r).card := S.embedding i
    have hj : j ∈ U.containedParentIndices r s k :=
      Finset.orderEmbOfFin_mem
        (U.containedParentIndices r s k) rfl i
    have hparent :
        ((U.coarse r).tube j).carrier ⊆
          dilatedTubeCarrier D ((U.coarse s).tube k) := by
      simpa [D] using
        (U.mem_containedParentIndices_iff r s k j).mp hj
    rw [S.tube_eq i]
    exact hparent.trans hdilated
  have hpacking_ennreal :
      S.family.enncard ≤
        ENNReal.ofReal
          (C * (sigma * sigma / rho ^ 2) ^ 2) :=
    hpacking rho sigma sigma
      hrho_pos hrs le_rfl hsigma_one
      plank frame hdimensions S.family hdistinct hcontain
  have hleft_top : S.family.enncard ≠ ⊤ := by
    simp [TubeFamily.enncard]
  have hright_top :
      ENNReal.ofReal
          (C * (sigma * sigma / rho ^ 2) ^ 2) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hreal :
      S.family.enncard.toReal ≤
        (ENNReal.ofReal
          (C * (sigma * sigma / rho ^ 2) ^ 2)).toReal :=
    (ENNReal.toReal_le_toReal hleft_top hright_top).mpr
      hpacking_ennreal
  have hexpr_nonneg :
      0 ≤ C * (sigma * sigma / rho ^ 2) ^ 2 := by
    positivity
  have hleft :
      S.family.enncard.toReal =
        ((U.containedParentIndices r s k).card : ℝ) := by
    simp [S,
      DilatedDiscreteUniformTubeStructure.containedParentSubfamily,
      TubeSubfamily.fromFinset, TubeFamily.enncard]
  have hright :
      (ENNReal.ofReal
          (C * (sigma * sigma / rho ^ 2) ^ 2)).toReal =
        C * (sigma / rho) ^ 4 := by
    rw [ENNReal.toReal_ofReal hexpr_nonneg]
    field_simp [hrho_pos.ne']
    <;> ring
  rw [hleft, hright] at hreal
  exact hreal

end DilatedDiscreteUniformTubeStructure

end Kakeya.Streamlined
