import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.QuantitativeConfiguration
import MyLeanRepo.Kakeya.Assouad.WZ1.ADPerturbation
import MyLeanRepo.Kakeya.Assouad.WZ1.TransportNormalizeAD

/-!
# Same-configuration refinements for the pure C2-grain argument

The Corollary-26 popularity iteration repeatedly replaces a cropped paper
shading by a whole-cell subshading on the *same* tube family.  This file
records the hereditary parts of the pure Node-4 package.  Extremality and
density are deliberately not inferred from mere containment: callers must
prove the retained extremality separately.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2PaperADSet1

/-- The paper-literal interval AD condition is invariant under translation. -/
theorem translate
    {source : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (data : PureWZ2PaperADSet1 source delta alpha C)
    (shift : ℝ) :
    PureWZ2PaperADSet1
      ((fun value : ℝ => value + shift) '' source) delta alpha C := by
  rcases data with
    ⟨hdelta, halpha, halphaOne, hC, hCtop, hcover⟩
  refine ⟨hdelta, halpha, halphaOne, hC, hCtop, ?_⟩
  intro rho hrho hdeltaRho left length hrhoLength
  let translation : ℝ → ℝ := fun value => value + shift
  have hisometry : Isometry translation := isometry_add_right shift
  have hsurjective : Function.Surjective translation := by
    intro value
    exact ⟨value - shift, by simp [translation]⟩
  have hintersection :
      ((fun value : ℝ => value + shift) '' source) ∩
          Set.Icc left (left + length) =
        translation ''
          (source ∩ Set.Icc (left - shift) (left - shift + length)) := by
    ext value
    constructor
    · rintro ⟨⟨sourceValue, hsourceValue, rfl⟩, hinterval⟩
      refine ⟨sourceValue, ⟨hsourceValue, ?_⟩, rfl⟩
      constructor <;> linarith [hinterval.1, hinterval.2]
    · rintro ⟨sourceValue, ⟨hsourceValue, hinterval⟩, rfl⟩
      refine ⟨⟨sourceValue, hsourceValue, rfl⟩, ?_⟩
      constructor <;> linarith [hinterval.1, hinterval.2]
  rw [hintersection]
  have hnumber := Isometry.externalCoveringNumber_image
    hisometry hsurjective
    (A := source ∩ Set.Icc (left - shift) (left - shift + length))
    (ε := ⟨rho, hrho⟩)
  rw [hnumber]
  exact hcover rho hrho hdeltaRho (left - shift) length hrhoLength

/-- The paper-literal interval AD condition is stable under a one-sided
`delta` perturbation.  Unlike the legacy bounded predicate, no artificial
`[-4,4]` range assumption is needed. -/
theorem perturb_by_delta
    {source target : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (data : PureWZ2PaperADSet1 source delta alpha C)
    (hclose : ∀ value ∈ target,
      ∃ sourceValue ∈ source, |value - sourceValue| ≤ delta) :
    PureWZ2PaperADSet1 target delta alpha (6 * C) := by
  rcases data with
    ⟨hdelta, halpha, halphaOne, hC, hCtop, hcover⟩
  refine
    ⟨hdelta, halpha, halphaOne,
      hC.trans (le_mul_of_one_le_left' (by norm_num)),
      ENNReal.mul_ne_top (by norm_num) hCtop, ?_⟩
  intro rho hrho hdeltaRho left length hrhoLength
  have hrhoPos : 0 < rho := lt_of_lt_of_le hdelta hdeltaRho
  let expandedLeft := left - delta
  let expandedLength := length + 2 * delta
  let sourcePart :=
    source ∩ Set.Icc expandedLeft (expandedLeft + expandedLength)
  let targetPart := target ∩ Set.Icc left (left + length)
  have hpartClose : ∀ value ∈ targetPart,
      ∃ sourceValue ∈ sourcePart,
        |value - sourceValue| ≤ delta := by
    intro value hvalue
    rcases hclose value hvalue.1 with
      ⟨sourceValue, hsourceValue, hdistance⟩
    refine ⟨sourceValue, ⟨hsourceValue, ?_⟩, hdistance⟩
    have hdistanceBounds := abs_le.mp hdistance
    rcases hvalue.2 with ⟨hvalueLower, hvalueUpper⟩
    dsimp only [expandedLeft, expandedLength]
    constructor <;> linarith
  have hcovering :
      (Metric.externalCoveringNumber ⟨rho, hrho⟩ targetPart : ENNReal) ≤
        2 *
          (Metric.externalCoveringNumber
            ⟨rho, hrho⟩ sourcePart : ENNReal) := by
    exact_mod_cast
      externalCoveringNumber_thickening_two_mul_real
        hrhoPos hdelta.le hdeltaRho hpartClose
  have hrhoExpanded : rho ≤ expandedLength := by
    dsimp only [expandedLength]
    linarith
  have hsourceCover :
      (Metric.externalCoveringNumber ⟨rho, hrho⟩ sourcePart : ENNReal) ≤
        C * Kakeya.realRpowENN (expandedLength / rho) alpha := by
    simpa [sourcePart, expandedLeft, expandedLength] using
      hcover rho hrho hdeltaRho (left - delta)
        (length + 2 * delta) hrhoExpanded
  have hlengthPos : 0 < length := lt_of_lt_of_le hrhoPos hrhoLength
  have hratioOne : 1 ≤ length / rho := by
    exact (le_div_iff₀ hrhoPos).2 (by simpa using hrhoLength)
  have hexpandedRatio :
      expandedLength / rho ≤ 3 * (length / rho) := by
    dsimp only [expandedLength]
    have hdeltaLength : delta ≤ length := hdeltaRho.trans hrhoLength
    calc
      (length + 2 * delta) / rho ≤ (3 * length) / rho := by
        exact div_le_div_of_nonneg_right (by linarith) hrhoPos.le
      _ = 3 * (length / rho) := by ring
  have hthreePower : Real.rpow 3 alpha ≤ 3 := by
    simpa using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        halphaOne
  have hpower :
      Kakeya.realRpowENN (expandedLength / rho) alpha ≤
        3 * Kakeya.realRpowENN (length / rho) alpha := by
    have hratioPos : 0 < length / rho := div_pos hlengthPos hrhoPos
    have hexpandedNonneg : 0 ≤ expandedLength / rho := by
      positivity
    have hmono :
        Real.rpow (expandedLength / rho) alpha ≤
          Real.rpow (3 * (length / rho)) alpha :=
      Real.rpow_le_rpow hexpandedNonneg hexpandedRatio halpha.le
    have hmul :
        Real.rpow (3 * (length / rho)) alpha =
          Real.rpow 3 alpha * Real.rpow (length / rho) alpha := by
      exact Real.mul_rpow (by norm_num) hratioPos.le
    have hratioPower : 0 ≤ Real.rpow (length / rho) alpha :=
      Real.rpow_nonneg hratioPos.le _
    unfold Kakeya.realRpowENN
    calc
      ENNReal.ofReal (Real.rpow (expandedLength / rho) alpha) ≤
          ENNReal.ofReal (Real.rpow (3 * (length / rho)) alpha) :=
        ENNReal.ofReal_mono hmono
      _ = ENNReal.ofReal
          (Real.rpow 3 alpha * Real.rpow (length / rho) alpha) := by
        rw [hmul]
      _ ≤ ENNReal.ofReal
          (3 * Real.rpow (length / rho) alpha) :=
        ENNReal.ofReal_mono
          (mul_le_mul_of_nonneg_right hthreePower hratioPower)
      _ = 3 * ENNReal.ofReal (Real.rpow (length / rho) alpha) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
  change
    (Metric.externalCoveringNumber ⟨rho, hrho⟩ targetPart : ENNReal) ≤
      (6 * C) * Kakeya.realRpowENN (length / rho) alpha
  calc
    (Metric.externalCoveringNumber ⟨rho, hrho⟩ targetPart : ENNReal) ≤
        2 *
          (Metric.externalCoveringNumber
            ⟨rho, hrho⟩ sourcePart : ENNReal) := hcovering
    _ ≤ 2 * (C * Kakeya.realRpowENN (expandedLength / rho) alpha) := by
      gcongr
    _ ≤ 2 * (C *
        (3 * Kakeya.realRpowENN (length / rho) alpha)) := by
      gcongr
    _ = (6 * C) * Kakeya.realRpowENN (length / rho) alpha := by ring

/-- Positive dilation of a paper-literal AD set, with its base scale dilated
by the same factor. -/
theorem image_mul
    {set : Set ℝ} {delta alpha scale : ℝ} {C : ENNReal}
    (data : PureWZ2PaperADSet1 set delta alpha C)
    (hscale : 0 < scale) :
    PureWZ2PaperADSet1
      ((fun value : ℝ => scale * value) '' set)
      (scale * delta) alpha C := by
  rcases data with
    ⟨hdelta, halpha, halphaOne, hC, hCtop, hcover⟩
  refine
    ⟨mul_pos hscale hdelta, halpha, halphaOne, hC, hCtop, ?_⟩
  intro rho hrho hscaleDeltaRho left length hrhoLength
  let sourceRho := rho / scale
  let sourceLeft := left / scale
  let sourceLength := length / scale
  have hsourceRho : 0 ≤ sourceRho := div_nonneg hrho hscale.le
  have hdeltaRho : delta ≤ sourceRho := by
    exact (le_div_iff₀ hscale).2 (by simpa [mul_comm] using hscaleDeltaRho)
  have hsourceLength : sourceRho ≤ sourceLength := by
    exact div_le_div_of_nonneg_right hrhoLength hscale.le
  have hset :
      ((fun value : ℝ => scale * value) '' set) ∩
          Set.Icc left (left + length) =
        (fun value : ℝ => scale * value) ''
          (set ∩ Set.Icc sourceLeft (sourceLeft + sourceLength)) := by
    ext value
    constructor
    · rintro ⟨⟨sourceValue, hsourceValue, rfl⟩,
          hvalueLower, hvalueUpper⟩
      refine ⟨sourceValue, ⟨hsourceValue, ?_⟩, rfl⟩
      dsimp only [sourceLeft, sourceLength]
      constructor
      · exact (div_le_iff₀ hscale).2 (by
          simpa [mul_comm] using hvalueLower)
      · have htarget : sourceValue ≤ (left + length) / scale :=
          (le_div_iff₀ hscale).2 (by
            simpa [mul_comm] using hvalueUpper)
        have heq : (left + length) / scale =
            left / scale + length / scale := by ring
        exact htarget.trans_eq heq
    · rintro ⟨sourceValue, ⟨hsourceValue,
          hsourceLower, hsourceUpper⟩, rfl⟩
      refine ⟨⟨sourceValue, hsourceValue, rfl⟩, ?_, ?_⟩
      · dsimp only [sourceLeft] at hsourceLower
        simpa [mul_comm] using (div_le_iff₀ hscale).1 hsourceLower
      · dsimp only [sourceLeft, sourceLength] at hsourceUpper
        have := (mul_le_mul_of_nonneg_left hsourceUpper hscale.le)
        field_simp [hscale.ne'] at this
        linarith
  rw [hset]
  have hcoverSource :=
    hcover sourceRho hsourceRho hdeltaRho sourceLeft sourceLength
      hsourceLength
  have hcovering :
      Metric.externalCoveringNumber ⟨rho, hrho⟩
          ((fun value : ℝ => scale * value) ''
            (set ∩ Set.Icc sourceLeft (sourceLeft + sourceLength))) =
        Metric.externalCoveringNumber ⟨sourceRho, hsourceRho⟩
          (set ∩ Set.Icc sourceLeft (sourceLeft + sourceLength)) := by
    let sourceRhoNN : NNReal := ⟨sourceRho, hsourceRho⟩
    let dilatedRho : NNReal :=
      ⟨scale * (sourceRhoNN : ℝ), by positivity⟩
    have hdilated : dilatedRho = (⟨rho, hrho⟩ : NNReal) := by
      apply NNReal.coe_injective
      change scale * (rho / scale) = rho
      field_simp [hscale.ne']
    rw [← hdilated]
    simpa only [dilatedRho] using
      (externalCoveringNumber_dilation_eq
        (a := scale) hscale
        (ε := sourceRhoNN)
        (A := set ∩ Set.Icc sourceLeft (sourceLeft + sourceLength)))
  rw [hcovering]
  have hratio : sourceLength / sourceRho = length / rho := by
    dsimp only [sourceLength, sourceRho]
    have hrhoPos : 0 < rho := lt_of_lt_of_le
      (mul_pos hscale hdelta) hscaleDeltaRho
    field_simp [hscale.ne', hrhoPos.ne']
  rwa [hratio] at hcoverSource

/-- The paper-literal upper AD condition is inherited by subsets. -/
theorem mono
    {set subset : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (hset : PureWZ2PaperADSet1 set delta alpha C)
    (hsubset : subset ⊆ set) :
    PureWZ2PaperADSet1 subset delta alpha C := by
  rcases hset with
    ⟨hdelta, halpha, halpha_one, hC_one, hC_top, hcover⟩
  refine ⟨hdelta, halpha, halpha_one, hC_one, hC_top, ?_⟩
  intro rho hrho hdelta_rho left length hrho_length
  have hmono :
      Metric.externalCoveringNumber ⟨rho, hrho⟩
          (subset ∩ Set.Icc left (left + length)) ≤
        Metric.externalCoveringNumber ⟨rho, hrho⟩
          (set ∩ Set.Icc left (left + length)) :=
    Metric.externalCoveringNumber_mono_set
      (Set.inter_subset_inter hsubset Set.Subset.rfl)
  have hmono' :
      (↑(Metric.externalCoveringNumber ⟨rho, hrho⟩
        (subset ∩ Set.Icc left (left + length))) : ENNReal) ≤
      (↑(Metric.externalCoveringNumber ⟨rho, hrho⟩
        (set ∩ Set.Icc left (left + length))) : ENNReal) := by
    exact_mod_cast hmono
  exact hmono'.trans
    (hcover rho hrho hdelta_rho left length hrho_length)

/-- Increasing the finite upper constant preserves paper-literal AD control. -/
theorem mono_constant
    {set : Set ℝ} {delta alpha : ℝ} {C C' : ENNReal}
    (hset : PureWZ2PaperADSet1 set delta alpha C)
    (hconstant : C ≤ C') (hC'_top : C' ≠ ⊤) :
    PureWZ2PaperADSet1 set delta alpha C' := by
  rcases hset with
    ⟨hdelta, halpha, halpha_one, hC_one, _hC_top, hcover⟩
  refine
    ⟨hdelta, halpha, halpha_one, hC_one.trans hconstant, hC'_top, ?_⟩
  intro rho hrho hdelta_rho left length hrho_length
  exact
    (hcover rho hrho hdelta_rho left length hrho_length).trans
      (mul_le_mul_right' hconstant
        (Kakeya.realRpowENN (length / rho) alpha))

/-- Raising the minimum covering scale preserves paper-literal AD control. -/
theorem coarsen_scale
    {set : Set ℝ} {delta delta' alpha : ℝ} {C : ENNReal}
    (hset : PureWZ2PaperADSet1 set delta alpha C)
    (hdelta' : 0 < delta') (hscale : delta ≤ delta') :
    PureWZ2PaperADSet1 set delta' alpha C := by
  rcases hset with
    ⟨_hdelta, halpha, halpha_one, hC_one, hC_top, hcover⟩
  refine ⟨hdelta', halpha, halpha_one, hC_one, hC_top, ?_⟩
  intro rho hrho hdelta'_rho left length hrho_length
  exact hcover rho hrho (hscale.trans hdelta'_rho) left length hrho_length

end PureWZ2PaperADSet1

namespace PureWZ2PaperIsSubshading

theorem union_subset
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {refined source : WZ1PaperTubeShading family}
    (hsub : PureWZ2PaperIsSubshading refined source) :
    refined.union ⊆ source.union := by
  rintro point ⟨index, hpoint⟩
  exact ⟨index, hsub index hpoint⟩

theorem cubical
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {refined source : WZ1PaperTubeShading family}
    (hsource : WZ1PaperIsCubicalShading source)
    (hwhole : ∀ index point, point ∈ refined.carrier index →
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        refined.carrier index) :
    WZ1PaperIsCubicalShading refined := by
  intro index point hpoint
  exact hwhole index point hpoint

end PureWZ2PaperIsSubshading

/-- Restrict local grains to a retained shading and weaken their AD constant. -/
noncomputable def PureWZ2LocalGrainData.restrictWithConstant
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source refined : WZ1PaperTubeShading family}
    {C C' : ENNReal}
    (data : PureWZ2LocalGrainData source sigma C)
    (hsub : PureWZ2PaperIsSubshading refined source)
    (hconstant : C ≤ C') (hC'_top : C' ≠ ⊤) :
    PureWZ2LocalGrainData refined sigma C' where
  planeMap point :=
    data.planeMap ⟨point, hsub.union_subset point.property⟩
  planeMap_lipschitz := by
    intro first second
    exact data.planeMap_lipschitz
      ⟨first, hsub.union_subset first.property⟩
      ⟨second, hsub.union_subset second.property⟩
  planeMap_unit point :=
    data.planeMap_unit ⟨point, hsub.union_subset point.property⟩
  planeMap_incidence index point hpoint := by
    exact data.planeMap_incidence index point (hsub index hpoint)
  local_ad rho hdelta_rho hrho_one point := by
    have hsource := data.local_ad rho hdelta_rho hrho_one
      ⟨point, hsub.union_subset point.property⟩
    apply (hsource.mono ?_).mono_constant hconstant hC'_top
    rintro value ⟨p, hp, rfl⟩
    exact ⟨p, ⟨hsub.union_subset hp.1, hp.2⟩, rfl⟩

/-- Restrict Lipschitz global grains to a retained shading. -/
noncomputable def PureWZ2LipschitzGlobalGrainData.restrict
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source refined : WZ1PaperTubeShading family}
    {C C' : ENNReal}
    (data : PureWZ2LipschitzGlobalGrainData source sigma C)
    (hsub : PureWZ2PaperIsSubshading refined source)
    (hconstant : C ≤ C') (hC'_top : C' ≠ ⊤) :
    PureWZ2LipschitzGlobalGrainData refined sigma C' where
  f := data.f
  lipschitz := data.lipschitz
  paper_ad z := by
    apply ((data.paper_ad z).mono ?_).mono_constant hconstant hC'_top
    rintro value ⟨p, hp, rfl⟩
    exact ⟨p, ⟨hsub.union_subset hp.1, hp.2⟩, rfl⟩

/-- Restrict a bounded global grain while retaining the chart bound on the
same literal slope.  The public parent is weakened through the ordinary
restriction lemma; the private bound is then copied definitionally. -/
noncomputable def PureWZ2BoundedLipschitzGlobalGrainData.restrict
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source refined : WZ1PaperTubeShading family}
    {C C' : ENNReal}
    (data : PureWZ2BoundedLipschitzGlobalGrainData source sigma C)
    (hsub : PureWZ2PaperIsSubshading refined source)
    (hconstant : C ≤ C') (hC'_top : C' ≠ ⊤) :
    PureWZ2BoundedLipschitzGlobalGrainData refined sigma C' where
  toPureWZ2LipschitzGlobalGrainData :=
    data.toPureWZ2LipschitzGlobalGrainData.restrict
      hsub hconstant hC'_top
  f_bound := data.f_bound

/-- Restrict normalized C2 global grains to a retained shading. -/
noncomputable def PureWZ2C2GlobalGrainData.restrict
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source refined : WZ1PaperTubeShading family}
    {C C' : ENNReal}
    (data : PureWZ2C2GlobalGrainData source sigma C)
    (hsub : PureWZ2PaperIsSubshading refined source)
    (hconstant : C ≤ C') (hC'_top : C' ≠ ⊤) :
    PureWZ2C2GlobalGrainData refined sigma C' where
  f := data.f
  normalized := data.normalized
  global_ad z := by
    apply ((data.global_ad z).mono ?_).mono_constant hconstant hC'_top
    rintro value ⟨p, hp, rfl⟩
    exact ⟨p, ⟨hsub.union_subset hp.1, hp.2⟩, rfl⟩

/-- Loss weakening for the power constant used by pure grain structures. -/
theorem pureWZ2_grain_constant_mono
    {delta firstLoss secondLoss : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hloss : firstLoss ≤ secondLoss) :
    Kakeya.realRpowENN delta (-firstLoss) ≤
      Kakeya.realRpowENN delta (-secondLoss) := by
  apply ENNReal.ofReal_mono
  exact Real.rpow_le_rpow_of_exponent_ge
    hdelta hdelta_one (by linarith)

/--
Extend the subtype-valued pure plane map to ambient space with the fixed
finite-dimensional extension constant supplied by Mathlib.

Only equality on the shaded union is asserted.  In particular, this does not
claim that the ambient extension is unit-valued away from the shading.
-/
theorem PureWZ2LocalGrainData.exists_ambient_extension
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (data : PureWZ2LocalGrainData shading sigma C) :
    ∃ extension : Point3 → Point3,
      LipschitzWith (lipschitzExtensionConstant Point3) extension ∧
      ∀ point : {point : Point3 // point ∈ shading.union},
        extension (point : Point3) = data.planeMap point := by
  classical
  let partialMap : Point3 → Point3 := fun point =>
    if hpoint : point ∈ shading.union then
      data.planeMap ⟨point, hpoint⟩
    else 0
  have hpartial :
      LipschitzOnWith 1 partialMap shading.union := by
    intro first hfirst second hsecond
    simpa [partialMap, hfirst, hsecond] using
      data.planeMap_lipschitz
        ⟨first, hfirst⟩ ⟨second, hsecond⟩
  rcases hpartial.extend_finite_dimension with
    ⟨extension, hextension, heq⟩
  refine ⟨extension, by simpa using hextension, ?_⟩
  intro point
  have h := heq point.property
  simpa [partialMap, point.property] using h.symm

/-- Forget normalized `C²` regularity while retaining the same configuration. -/
noncomputable def PureWZ2C2GrainConfiguration.toGrainConfiguration
    {sigma loss delta : ℝ}
    (configuration :
      PureWZ2C2GrainConfiguration sigma loss delta) :
    PureWZ2GrainConfiguration sigma loss delta := by
  let extension : ℝ → ℝ :=
    Classical.choose configuration.globalGrains.normalized
  have extension_spec :=
    Classical.choose_spec configuration.globalGrains.normalized
  let globalGrains :
      PureWZ2LipschitzGlobalGrainData
        configuration.shading sigma
        (Kakeya.realRpowENN delta (-loss)) :=
    { f := configuration.globalGrains.f
      lipschitz := by
        have hlipschitzOpen :
            LipschitzOnWith 1 extension (Set.Ioo (-1 : ℝ) 1) := by
          apply (convex_Ioo (-1 : ℝ) 1).lipschitzOnWith_of_nnnorm_deriv_le
          · intro z hz
            exact
              ((extension_spec.1.differentiableOn (by norm_num) z
                (Set.Ioo_subset_Icc_self hz)).mono
                  Set.Ioo_subset_Icc_self).differentiableAt
                    (isOpen_Ioo.mem_nhds hz)
          · intro z hz
            apply NNReal.coe_le_coe.mp
            simpa [extension, Real.norm_eq_abs] using
              (extension_spec.2.2 ⟨z, Set.Ioo_subset_Icc_self hz⟩).2.1
        have hcontinuousClosure :
            ContinuousOn extension (closure (Set.Ioo (-1 : ℝ) 1)) := by
          rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
          simpa [extension] using extension_spec.1.continuousOn
        have hclosed := hlipschitzOpen.closure hcontinuousClosure
        intro first second
        have hfirst : first.1 ∈ closure (Set.Ioo (-1 : ℝ) 1) := by
          rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
          exact first.2
        have hsecond : second.1 ∈ closure (Set.Ioo (-1 : ℝ) 1) := by
          rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
          exact second.2
        have h := hclosed hfirst hsecond
        have hfirstEq : extension first.1 = configuration.globalGrains.f first :=
          extension_spec.2.1 first
        have hsecondEq : extension second.1 = configuration.globalGrains.f second :=
          extension_spec.2.1 second
        rw [hfirstEq, hsecondEq] at h
        change edist (configuration.globalGrains.f first)
            (configuration.globalGrains.f second) ≤
          (1 : ENNReal) * edist first.1 second.1
        exact h
      paper_ad := by
        intro z
        exact configuration.globalGrains.global_ad z }
  exact
    { family := configuration.family
      shading := configuration.shading
      line_class := configuration.line_class
      cubical := configuration.cubical
      extremal := configuration.extremal
      top_level_cwa := configuration.top_level_cwa
      globalGrains := globalGrains
      localGrains := configuration.localGrains }

end Kakeya.Assouad
