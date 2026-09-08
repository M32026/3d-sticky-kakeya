import MyLeanRepo.Kakeya.Streamlined.DividingScales.DiscreteKatzTaoProof.KatzTaoProfiles
import MyLeanRepo.Kakeya.Streamlined.DividingScales.BranchProductHelpers
import MyLeanRepo.Kakeya.Streamlined.ProfileUniformRefinement.FactorLocalTwoProfileCommonSelection

/-!
# Exact profile identity for a represented conditional relation

Every represented relation family is a nonempty equal-radius tube family
contained in the universal dilation of its endpoint parent.  Its maximal
density is therefore exactly its Frostman constant in that parent dilation
times its reference density there.

This identity is the local algebraic input used to convert localized
Katz--Tao composition into localized Frostman composition.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

namespace FrostmanConditionalFactorScope

/-- Reference container of one represented conditional relation. -/
def representedRelationContainer
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (s : UniformScaleIndex delta) :
    Set Point3 :=
  dilatedTubeCarrier (independentCoverParentDilation A)
    ((U.coarse s).tube ((U.cover s).parent i))

/-- Reference density of one represented relation family. -/
def representedRelationReferenceDensity
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) : ENNReal :=
  (P.relationSubfamily i r s).family.toBodyFamily.density
    (P.representedRelationContainer i s)

/-- Cardinality of one represented conditional relation family. -/
def representedRelationCard
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) : ENNReal :=
  (P.relationIndices i r s).card

/--
The scale-only factor in every represented relation reference density.

It is independent of the historical cell and of the represented endpoint
parent.  The denominator is the exact volume of the universal parent
dilation at scale `s`.
-/
def relationReferenceScaleFactor
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (r s : UniformScaleIndex delta) : ENNReal :=
  Kakeya.deltaTubeVolume (uniformScale delta hdelta_le_one r).1 /
    (ENNReal.ofReal (|independentCoverParentDilation A| ^ 3) *
      Kakeya.deltaTubeVolume (uniformScale delta hdelta_le_one s).1)

/-- Every represented relation tube lies in its reference endpoint parent. -/
lemma representedRelation_all_contained
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (hA : 1 ≤ A)
    (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1) :
    ∀ localIndex,
      ((P.relationSubfamily i r s).family.tube localIndex).carrier ⊆
        P.representedRelationContainer i s := by
  intro localIndex
  rw [(P.relationSubfamily i r s).tube_eq localIndex]
  have hmember :
      (P.relationSubfamily i r s).embedding localIndex ∈
        P.relationIndices i r s :=
    Finset.orderEmbOfFin_mem (P.relationIndices i r s) rfl localIndex
  rcases (P.mem_relationIndices_iff i r s _).mp hmember with
    ⟨original, _hhistory, hs, hr⟩
  have hrelation :
      U.toLocalDilatedDiscreteUniformTubeStructure.toDilated.ParentRelation
        r s
        ((U.cover r).parent original)
        ((U.cover s).parent original) :=
    ⟨original, rfl, rfl⟩
  have hcontain :=
    U.toLocalDilatedDiscreteUniformTubeStructure.toDilated
      |>.related_parent_containment
        hA hdelta hF_ball r s hrs
          ((U.cover r).parent original)
          ((U.cover s).parent original) hrelation
  change
    ((U.coarse r).tube ((U.cover r).parent original)).carrier ⊆
      dilatedTubeCarrier (independentCoverParentDilation A)
        ((U.coarse s).tube ((U.cover s).parent original)) at hcontain
  rw [hr, hs] at hcontain
  simpa [representedRelationContainer] using hcontain

/--
Exact cardinality formula for a represented relation reference density.

This is the reusable reduction from the measure-theoretic density telescope
to the genuinely combinatorial descendant-cardinality telescope required of
the coherent v5 hierarchy.
-/
theorem representedRelationReferenceDensity_eq_card_mul_scaleFactor
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (hA : 1 ≤ A)
    (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1) :
    P.representedRelationReferenceDensity i r s =
      P.representedRelationCard i r s *
        P.relationReferenceScaleFactor r s := by
  let relation := (P.relationSubfamily i r s).family
  let container := P.representedRelationContainer i s
  have hcontained :
      ∀ localIndex, (relation.tube localIndex).carrier ⊆ container :=
    P.representedRelation_all_contained
      hA hdelta hF_ball i r s hrs
  have hmass :
      relation.toBodyFamily.containedMass container =
        P.representedRelationCard i r s *
          Kakeya.deltaTubeVolume
            (uniformScale delta hdelta_le_one r).1 := by
    rw [BodyFamily.containedMass_eq_mass_of_all_contained
      relation.toBodyFamily container hcontained]
    rw [relation.bodyMass_eq_nominalMass]
    rfl
  have hD :
      independentCoverParentDilation A ≠ 0 := by
    dsimp only [independentCoverParentDilation]
    nlinarith [sq_nonneg A]
  have hvolume :
      volume container =
        ENNReal.ofReal (|independentCoverParentDilation A| ^ 3) *
          Kakeya.deltaTubeVolume
            (uniformScale delta hdelta_le_one s).1 := by
    exact volume_dilatedTubeCarrier hD
      ((U.coarse s).tube ((U.cover s).parent i))
  rw [show P.representedRelationReferenceDensity i r s =
      relation.toBodyFamily.containedMass container / volume container by
        rfl]
  rw [hmass, hvolume]
  simp only [representedRelationCard, relationReferenceScaleFactor]
  rw [mul_div_assoc]

/-- Exact `deltaMax = C_F * referenceDensity` identity on one represented
conditional relation family. -/
theorem representedRelationDeltaMax_eq_frostman_mul_referenceDensity
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (hA : 1 ≤ A)
    (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1) :
    P.representedRelationDeltaMax i r s =
      P.representedRelationFrostmanConstant i r s *
        P.representedRelationReferenceDensity i r s := by
  let relation := (P.relationSubfamily i r s).family
  let container := P.representedRelationContainer i s
  have hcontained :
      ∀ localIndex, (relation.tube localIndex).carrier ⊆ container :=
    P.representedRelation_all_contained
      hA hdelta hF_ball i r s hrs
  have hrelationNonempty : relation.Nonempty := by
    change 0 < (P.relationIndices i r s).card
    exact (P.relationIndices_nonempty i r s).card_pos
  have hrho :
      0 < (uniformScale delta hdelta_le_one r).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1
  have hsigma :
      0 < (uniformScale delta hdelta_le_one s).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one s).property.1
  have hD :
      1 ≤ independentCoverParentDilation A := by
    dsimp only [independentCoverParentDilation]
    nlinarith [sq_nonneg A]
  have hmassPos :
      0 < relation.toBodyFamily.containedMass container :=
    TubeFamily.containedMass_pos_of_nonempty_of_all_contained
      relation hrho hrelationNonempty hcontained
  have hmassTop :
      relation.toBodyFamily.containedMass container ≠ ⊤ :=
    TubeFamily.containedMass_ne_top_of_all_contained
      relation hcontained
  have hidentity :=
    BodyFamily.deltaMax_eq_frostmanConstantIn_mul_density_of_contained
      relation.toBodyFamily container
      (GeometricLemmas.dilatedTubeCarrier_convex
        ((U.coarse s).tube ((U.cover s).parent i)))
      hcontained
      hmassPos hmassTop
      (GeometricLemmas.dilatedTubeCarrier_volume_pos
        hsigma hD ((U.coarse s).tube ((U.cover s).parent i)))
      (GeometricLemmas.dilatedTubeCarrier_volume_ne_top
        hsigma hD ((U.coarse s).tube ((U.cover s).parent i)))
  exact hidentity

/-- Maximum represented relation reference density on one historical cell. -/
def relationReferenceDensityMax
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (r s : UniformScaleIndex delta) : ENNReal :=
  Finset.univ.sup' (by
    let i : Fin F.card := ⟨0, hF⟩
    exact ⟨i, Finset.mem_univ i⟩)
    fun i => P.representedRelationReferenceDensity i r s

/-- Minimum represented relation reference density on one historical cell. -/
def relationReferenceDensityMin
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (r s : UniformScaleIndex delta) : ENNReal :=
  Finset.univ.inf' (by
    let i : Fin F.card := ⟨0, hF⟩
    exact ⟨i, Finset.mem_univ i⟩)
    fun i => P.representedRelationReferenceDensity i r s

/-- Maximum represented relation cardinality on one historical cell. -/
def relationCardMax
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (r s : UniformScaleIndex delta) : ENNReal :=
  Finset.univ.sup' (by
    let i : Fin F.card := ⟨0, hF⟩
    exact ⟨i, Finset.mem_univ i⟩)
    fun i => P.representedRelationCard i r s

/-- Minimum represented relation cardinality on one historical cell. -/
def relationCardMin
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (r s : UniformScaleIndex delta) : ENNReal :=
  Finset.univ.inf' (by
    let i : Fin F.card := ⟨0, hF⟩
    exact ⟨i, Finset.mem_univ i⟩)
    fun i => P.representedRelationCard i r s

lemma representedRelationReferenceDensity_le_max
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    P.representedRelationReferenceDensity i r s ≤
      P.relationReferenceDensityMax hF r s :=
  Finset.le_sup'
    (fun current : Fin F.card =>
      P.representedRelationReferenceDensity current r s)
    (Finset.mem_univ i)

lemma relationReferenceDensityMin_le_represented
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    P.relationReferenceDensityMin hF r s ≤
      P.representedRelationReferenceDensity i r s :=
  Finset.inf'_le _ (Finset.mem_univ i)

/-- Every represented relation cardinality is bounded by the cell maximum. -/
lemma representedRelationCard_le_max
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    P.representedRelationCard i r s ≤
      P.relationCardMax hF r s :=
  Finset.le_sup'
    (fun current : Fin F.card =>
      P.representedRelationCard current r s)
    (Finset.mem_univ i)

/-- The cell minimum is bounded by every represented relation cardinality. -/
lemma relationCardMin_le_represented
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    P.relationCardMin hF r s ≤
      P.representedRelationCard i r s :=
  Finset.inf'_le _ (Finset.mem_univ i)

/-- The maximum reference density is controlled by the maximum relation
cardinality times the common scale factor. -/
lemma relationReferenceDensityMax_le_cardMax_mul_scaleFactor
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (hA : 1 ≤ A)
    (hdelta : 0 < delta)
    (hF : F.Nonempty)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1) :
    P.relationReferenceDensityMax hF r s ≤
      P.relationCardMax hF r s *
        P.relationReferenceScaleFactor r s := by
  exact Finset.sup'_le _ _ fun i _ => by
    rw [P.representedRelationReferenceDensity_eq_card_mul_scaleFactor
      hA hdelta hF_ball i r s hrs]
    gcongr
    exact P.representedRelationCard_le_max hF i r s

/-- The minimum relation cardinality times the common scale factor is
controlled by the minimum reference density. -/
lemma cardMin_mul_scaleFactor_le_relationReferenceDensityMin
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (hA : 1 ≤ A)
    (hdelta : 0 < delta)
    (hF : F.Nonempty)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1) :
    P.relationCardMin hF r s *
        P.relationReferenceScaleFactor r s ≤
      P.relationReferenceDensityMin hF r s := by
  exact Finset.le_inf' _ _ fun i _ => by
    rw [P.representedRelationReferenceDensity_eq_card_mul_scaleFactor
      hA hdelta hF_ball i r s hrs]
    gcongr
    exact P.relationCardMin_le_represented hF i r s

/-- The maximum Frostman profile times the minimum reference density is
bounded by the maximum `deltaMax` profile. -/
lemma relationFrostmanMax_mul_referenceDensityMin_le_relationDeltaMax
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (hA : 1 ≤ A)
    (hdelta : 0 < delta)
    (hF : F.Nonempty)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1) :
    P.relationFrostmanMax hF r s *
        P.relationReferenceDensityMin hF r s ≤
      P.relationDeltaMax hF r s := by
  let indices : Finset (Fin F.card) := Finset.univ
  have hindices : indices.Nonempty := by
    let i : Fin F.card := ⟨0, hF⟩
    exact ⟨i, Finset.mem_univ i⟩
  rcases
      Finset.exists_mem_eq_sup' hindices
        (fun i => P.representedRelationFrostmanConstant i r s) with
    ⟨imax, _himax, himax⟩
  have himax' :
      P.relationFrostmanMax hF r s =
        P.representedRelationFrostmanConstant imax r s := by
    simpa [relationFrostmanMax, indices] using himax
  have hdensity :
      P.relationReferenceDensityMin hF r s ≤
        P.representedRelationReferenceDensity imax r s :=
    P.relationReferenceDensityMin_le_represented hF imax r s
  have hidentity :=
    P.representedRelationDeltaMax_eq_frostman_mul_referenceDensity
      hA hdelta hF_ball imax r s hrs
  calc
    P.relationFrostmanMax hF r s *
          P.relationReferenceDensityMin hF r s
        =
      P.representedRelationFrostmanConstant imax r s *
          P.relationReferenceDensityMin hF r s := by
            rw [himax']
    _ ≤
      P.representedRelationFrostmanConstant imax r s *
        P.representedRelationReferenceDensity imax r s := by
          gcongr
    _ = P.representedRelationDeltaMax imax r s :=
      hidentity.symm
    _ ≤ P.relationDeltaMax hF r s :=
      P.representedRelationDeltaMax_le_max hF imax r s

/-- The maximum `deltaMax` profile is bounded by the maximum Frostman profile
times the maximum reference density. -/
lemma relationDeltaMax_le_relationFrostmanMax_mul_referenceDensityMax
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (hA : 1 ≤ A)
    (hdelta : 0 < delta)
    (hF : F.Nonempty)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1) :
    P.relationDeltaMax hF r s ≤
      P.relationFrostmanMax hF r s *
        P.relationReferenceDensityMax hF r s := by
  rw [P.relationDeltaMax_le_iff hF r s]
  intro i
  rw [P.representedRelationDeltaMax_eq_frostman_mul_referenceDensity
    hA hdelta hF_ball i r s hrs]
  exact mul_le_mul
    (P.representedRelationFrostmanConstant_le_max hF i r s)
    (P.representedRelationReferenceDensity_le_max hF i r s)
    (by positivity) (by positivity)

end FrostmanConditionalFactorScope

end Kakeya.Streamlined
