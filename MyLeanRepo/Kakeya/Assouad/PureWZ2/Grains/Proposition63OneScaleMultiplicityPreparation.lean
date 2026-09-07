import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ConstantMultiplicityRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ExtremalCWATransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiScaleLocalAD

/-!
# Constant-multiplicity preparation for one-scale local grains

Before the cellwise full-grain/Fubini step, the paper passes to a genuine
constant-multiplicity refinement.  This module performs that refinement on
the exact shading carried by a one-scale local-AD output.  It transfers
extremality with an explicit loss/slack hypothesis, weakens the CWA constant,
and restricts the local AD estimates without changing the plane map.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

/-- The analytic state needed to run a geometric refinement before local AD
has been assembled.  Unlike `PureWZ2OneScaleLocalGrainData`, this package
does not assume the conclusion of the inner Lemma 4.11 iteration. -/
structure Proposition63ExtremalShadingData
    {delta sigma outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family) where
  shading : WZ1PaperTubeShading family
  subshading : PaperIsSubshading shading source
  extremal : WZ2PaperCroppedIsExtremal sigma outputLoss family shading
  cwa : WZ2PaperConvexWolffBound family
    (Kakeya.realRpowENN delta (-outputLoss))

/-- Forget local AD while retaining the complete state needed by the next
shading refinement. -/
def PureWZ2OneScaleLocalGrainData.toExtremalShadingData
    {delta sigma outputLoss rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    (data : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := outputLoss) (rho := rho)
      (Y := source) (fun point => planeMap point)) :
    Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := outputLoss) source where
  shading := data.shading
  subshading := data.subshading
  extremal := data.extremal
  cwa := data.cwa

/-- Constant-multiplicity refinement of an extremal/CWA shading, without
assuming a local AD estimate. -/
structure Proposition63ConstantMultiplicityShadingData
    {delta sigma firstLoss secondLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (original : Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := firstLoss) source) where
  level : ℕ
  refined : Proposition63ExtremalShadingData
    (sigma := sigma) (outputLoss := secondLoss) source
  subshading_original : PaperIsSubshading refined.shading original.shading
  multiplicity_lower :
    ∀ point ∈ refined.shading.union,
      (2 ^ level : ENNReal) ≤
        (refined.shading.pointMultiplicity point : ENNReal)
  multiplicity_upper :
    ∀ point ∈ refined.shading.union,
      (refined.shading.pointMultiplicity point : ENNReal) <
        2 * (2 ^ level : ENNReal)
  preparationLoss : ENNReal
  preparationLoss_pos : 0 < preparationLoss
  preparationLoss_ne_top : preparationLoss ≠ ⊤
  mass_retention :
    original.shading.mass ≤ preparationLoss * refined.shading.mass

/-- Run the dyadic constant-multiplicity preparation before local AD exists. -/
theorem proposition63_prepare_extremalShading_constantMultiplicity_with_loss
    {delta sigma firstLoss secondLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (original : Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := firstLoss) source)
    (hloss : firstLoss ≤ secondLoss)
    (hsecondLoss : 0 < secondLoss)
    (hslack :
      (((Nat.log 2 family.card + 1 : ℕ) : ENNReal) *
          Kakeya.realRpowENN delta secondLoss) ≤
        Kakeya.realRpowENN delta firstLoss) :
    ∃ prepared : Proposition63ConstantMultiplicityShadingData
        (secondLoss := secondLoss) original,
      prepared.preparationLoss =
        ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) := by
  rcases Kakeya.Assouad.constant_multiplicity_refinement
      original.extremal.cubical with
    ⟨level, shading, hsub, hcubical, hlower, hupper, hmass⟩
  let lossFactor : ENNReal :=
    ((Nat.log 2 family.card + 1 : ℕ) : ENNReal)
  have hlossFactorPos : 0 < lossFactor := by simp [lossFactor]
  have hlossFactorTop : lossFactor ≠ ⊤ := by simp [lossFactor]
  have hextremal : WZ2PaperCroppedIsExtremal
      sigma secondLoss family shading :=
    Kakeya.Assouad.transfer_cropped_extremal_to_subshading
      lossFactor hlossFactorPos hlossFactorTop original.extremal hsub
      (by simpa [lossFactor, div_eq_mul_inv, mul_comm] using hmass) hcubical
      hloss (by simpa [lossFactor] using hslack)
      original.extremal.delta_pos original.extremal.delta_le_one
      hsecondLoss
  have hcwa : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-secondLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := original.shading) (_shading2 := shading)
      original.cwa hloss original.extremal.delta_pos
      original.extremal.delta_le_one
  let refined : Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := secondLoss) source :=
    { shading := shading
      subshading := fun index point hpoint =>
        original.subshading index (hsub index hpoint)
      extremal := hextremal
      cwa := hcwa }
  refine ⟨{
    level := level
    refined := refined
    subshading_original := hsub
    multiplicity_lower := hlower
    multiplicity_upper := hupper
    preparationLoss := lossFactor
    preparationLoss_pos := hlossFactorPos
    preparationLoss_ne_top := hlossFactorTop
    mass_retention := ?_
  }, rfl⟩
  have hconverted : original.shading.mass ≤
      shading.mass * lossFactor :=
    (ENNReal.div_le_iff
      (by simp [lossFactor] : lossFactor ≠ 0)
      (by simp [lossFactor] : lossFactor ≠ ⊤)).mp
        (by simpa only using hmass)
  simpa [refined, mul_comm] using hconverted

/-- A constant-multiplicity refinement of a one-scale local-grain output. -/
structure Proposition63OneScaleConstantMultiplicityData
    {delta sigma firstLoss secondLoss rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := rho) (Y := source) (fun point => planeMap point)) where
  level : ℕ
  refined : PureWZ2OneScaleLocalGrainData
    (sigma := sigma) (outputLoss := secondLoss)
    (rho := rho) (Y := source) (fun point => planeMap point)
  subshading_original : PaperIsSubshading' refined.shading original.shading
  multiplicity_lower :
    ∀ point ∈ refined.shading.union,
      (2 ^ level : ENNReal) ≤
        (refined.shading.pointMultiplicity point : ENNReal)
  multiplicity_upper :
    ∀ point ∈ refined.shading.union,
      (refined.shading.pointMultiplicity point : ENNReal) <
        2 * (2 ^ level : ENNReal)
  preparationLoss : ENNReal
  preparationLoss_pos : 0 < preparationLoss
  preparationLoss_ne_top : preparationLoss ≠ ⊤
  mass_retention :
    original.shading.mass ≤ preparationLoss * refined.shading.mass

/-- Insert the paper's dyadic constant-multiplicity refinement into a
one-scale local-grain output.  The caller supplies exactly the loss slack
needed to transfer cropped extremality. -/
theorem proposition63_prepare_oneScale_constantMultiplicity_with_loss
    {delta sigma firstLoss secondLoss rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := rho) (Y := source) (fun point => planeMap point))
    (hloss : firstLoss ≤ secondLoss)
    (hsecondLoss : 0 < secondLoss)
    (hslack :
      (((Nat.log 2 family.card + 1 : ℕ) : ENNReal) *
          Kakeya.realRpowENN delta secondLoss) ≤
        Kakeya.realRpowENN delta firstLoss) :
    ∃ prepared : Proposition63OneScaleConstantMultiplicityData
        (secondLoss := secondLoss) planeMap original,
      prepared.preparationLoss =
        ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) := by
  rcases Kakeya.Assouad.constant_multiplicity_refinement
      original.extremal.cubical with
    ⟨level, shading, hsub, hcubical, hlower, hupper, hmass⟩
  let lossFactor : ENNReal :=
    ((Nat.log 2 family.card + 1 : ℕ) : ENNReal)
  have hlossFactorPos : 0 < lossFactor := by
    simp [lossFactor]
  have hlossFactorTop : lossFactor ≠ ⊤ := by
    simp [lossFactor]
  have hextremal :
      WZ2PaperCroppedIsExtremal sigma secondLoss family shading :=
    Kakeya.Assouad.transfer_cropped_extremal_to_subshading
      lossFactor hlossFactorPos hlossFactorTop original.extremal hsub
      (by simpa [lossFactor, div_eq_mul_inv, mul_comm] using hmass) hcubical
      hloss (by simpa [lossFactor] using hslack)
      original.extremal.delta_pos original.extremal.delta_le_one
      hsecondLoss
  have hcwa : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-secondLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := original.shading) (_shading2 := shading)
      original.cwa hloss original.extremal.delta_pos
      original.extremal.delta_le_one
  have hsubSource : PaperIsSubshading' shading source :=
    fun index point hpoint => original.subshading index (hsub index hpoint)
  have hunionSubset : shading.union ⊆ original.shading.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, hsub index hpoint⟩
  have hlocal : ∀ point ∈ shading.union,
      IsADSet1
        (scalarProjection (planeMap point)
          (shading.union ∩ Metric.closedBall point (Real.sqrt rho)))
        rho (1 - sigma)
        (Kakeya.realRpowENN delta (-secondLoss)) := by
    intro point hpoint
    have hpointOriginal : point ∈ original.shading.union :=
      hunionSubset hpoint
    have hsetSubset :
        scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall point (Real.sqrt rho)) ⊆
          scalarProjection (planeMap point)
            (original.shading.union ∩
              Metric.closedBall point (Real.sqrt rho)) := by
      rintro value ⟨other, hother, rfl⟩
      exact ⟨other, ⟨hunionSubset hother.1, hother.2⟩, rfl⟩
    have hrestricted :=
      (original.local_ad point hpointOriginal).mono hsetSubset
    have hconstant : Kakeya.realRpowENN delta (-firstLoss) ≤
        Kakeya.realRpowENN delta (-secondLoss) := by
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge
        original.extremal.delta_pos original.extremal.delta_le_one
        (by linarith)
    exact hrestricted.mono_constant hconstant
  let refined : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := secondLoss)
      (rho := rho) (Y := source) (fun point => planeMap point) :=
    { shading := shading
      subshading := hsubSource
      extremal := hextremal
      cwa := hcwa
      local_ad := hlocal }
  refine ⟨{
    level := level
    refined := refined
    subshading_original := hsub
    multiplicity_lower := hlower
    multiplicity_upper := hupper
    preparationLoss :=
      ((Nat.log 2 family.card + 1 : ℕ) : ENNReal)
    preparationLoss_pos := by simp
    preparationLoss_ne_top := by simp
    mass_retention := by
      have hconverted : original.shading.mass ≤
          refined.shading.mass *
            ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) :=
        (ENNReal.div_le_iff
          (by simp : ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) ≠ 0)
          (by simp : ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) ≠ ⊤)).mp
            (by simpa only [refined] using hmass)
      simpa [mul_comm] using hconverted
  }, rfl⟩

/-- Compatibility wrapper retaining the original existence-only interface. -/
theorem proposition63_prepare_oneScale_constantMultiplicity
    {delta sigma firstLoss secondLoss rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := rho) (Y := source) (fun point => planeMap point))
    (hloss : firstLoss ≤ secondLoss)
    (hsecondLoss : 0 < secondLoss)
    (hslack :
      (((Nat.log 2 family.card + 1 : ℕ) : ENNReal) *
          Kakeya.realRpowENN delta secondLoss) ≤
        Kakeya.realRpowENN delta firstLoss) :
    Nonempty
      (Proposition63OneScaleConstantMultiplicityData
        (secondLoss := secondLoss) planeMap original) := by
  rcases proposition63_prepare_oneScale_constantMultiplicity_with_loss
      planeMap original hloss hsecondLoss hslack with ⟨prepared, _⟩
  exact ⟨prepared⟩

end Kakeya.Assouad.PureWZ2

end
