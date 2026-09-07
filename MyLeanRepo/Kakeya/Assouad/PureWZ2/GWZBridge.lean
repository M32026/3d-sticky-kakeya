import MyLeanRepo.Kakeya.Assouad.PureWZ2.Theorem5_2

/-!
# Rigorous GWZ-to-WZ2 comparison remark

The GWZ hypothesis is not definitionally WZ2 Definition 2.12.  This module
freezes a branch-independent semantic projection of the GWZ socket, the
mass-retaining conversion, and the resulting volume theorem as separate
statements.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Support in a fixed ball, kept separate from full-fiber structure. -/
def PureWZ2FixedBallSupport
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (radius : ℝ) : Prop :=
  ∀ index,
    (family.tube index).carrier ⊆
      Metric.closedBall (0 : Point3) radius

/--
The exact-scale full-containment data used by the GWZ sticky socket, stated
without GWZ's auxiliary assigned parent.
-/
structure PureWZ2GWZScaleData
    {delta A : ℝ}
    (source : Kakeya.Streamlined.TubeFamily delta)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (C : ENNReal) where
  coarse : Kakeya.Streamlined.TubeFamily rho.1
  coarse_distinct : coarse.IsEssentiallyDistinct
  fullFiberIndices :
    Fin coarse.card → Finset (Fin source.card)
  fullFiberIndices_eq :
    ∀ parent,
      fullFiberIndices parent =
        Finset.univ.filter fun index =>
          (source.tube index).carrier ⊆
            wz2PaperCenteredDilatedCarrier A
              (coarse.tube parent)
  full_fiber_nonempty :
    ∀ parent, (fullFiberIndices parent).Nonempty
  full_fibers_cover :
    ∀ index : Fin source.card,
      ∃ parent : Fin coarse.card,
        index ∈ fullFiberIndices parent
  full_fiber_uniform :
    ∀ first second,
      ((fullFiberIndices first).card : ENNReal) ≤
        C * ((fullFiberIndices second).card : ENNReal)
  full_fiber_frostman :
    ∀ parent,
      let fiber :=
        Kakeya.Streamlined.TubeSubfamily.fromFinset
          source (fullFiberIndices parent)
      ∀ convexSet : Set Point3,
        Convex ℝ convexSet →
        convexSet ⊆
            wz2PaperCenteredDilatedCarrier A
              (coarse.tube parent) →
          fiber.family.toBodyFamily.containedMass convexSet *
                volume
                  (wz2PaperCenteredDilatedCarrier A
                    (coarse.tube parent)) ≤
            C * fiber.family.toBodyFamily.mass *
              volume convexSet

/-- Branch-independent semantic projection of the GWZ exact-scale input. -/
structure PureWZ2GWZFullFiberStructure
    {delta A : ℝ}
    (source : Kakeya.Streamlined.TubeFamily delta)
    (C : ENNReal) : Prop where
  finite_constant : 1 ≤ C ∧ C ≠ ⊤
  scale :
    ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
      Nonempty
        (PureWZ2GWZScaleData
          (A := A) source rho C)

/-- The fixed-support volume theorem consumed by one GWZ assembly. -/
def PureWZ2FixedSupportDilatedStickyContract
    (A R : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ source : Kakeya.Streamlined.TubeFamily delta,
          source.Nonempty →
          PureWZ2FixedBallSupport source R →
          source.IsEssentiallyDistinct →
          ∀ fullFiberData :
              PureWZ2GWZFullFiberStructure (A := A) source
                (Kakeya.realRpowENN delta (-eta)),
            ∀ shading :
                Kakeya.Streamlined.TubeShading source,
              shading.IsLambdaDense
                  (Kakeya.realRpowENN delta eta) →
                Kakeya.realRpowENN delta epsilon ≤
                  volume shading.union

/--
One literal-WZ2 configuration obtained by localized coaxial reanchoring of a
GWZ fixed-dilation configuration.

The output family is not a geometric subfamily of `source`: its unit segments
may be translated along their own coaxial lines.  The source-index embedding
and the unchanged subshading retain the exact provenance needed to transfer a
volume lower bound back to the source shading.
-/
structure PureWZ2GWZReanchoredConversionData
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : Kakeya.Streamlined.TubeShading source)
    (C : ENNReal)
    (logExponent : ℕ) where
  reanchored : Kakeya.Streamlined.TubeFamily delta
  sourceIndex : Fin reanchored.card ↪ Fin source.card
  axialShift : Fin reanchored.card → ℝ
  direction_eq :
    ∀ index,
      (reanchored.tube index).direction =
        (source.tube (sourceIndex index)).direction
  source_base_eq :
    ∀ index,
      (source.tube (sourceIndex index)).base =
        (reanchored.tube index).base +
          axialShift index • (reanchored.tube index).direction
  axialShift_bound :
    ∀ index, |axialShift index| ≤ 1
  shading :
    Kakeya.Streamlined.TubeShading reanchored
  subshading :
    ∀ index,
      shading.carrier index ⊆
        sourceShading.carrier (sourceIndex index)
  retained_mass :
    wz2PaperPureRefinementFraction delta logExponent *
        sourceShading.mass ≤
      shading.mass
  reanchored_paper_distinct :
    WZ2PaperOrdinaryIsEssentiallyDistinct reanchored
  literal_cwa :
    WZ2PaperPureCWAAtNearbyScales reanchored C

/--
The corrected mathematical content of the GWZ comparison remark.

For every requested WZ2 loss, sufficiently strong GWZ full-fiber uniformity
and full-fiber Frostman control yield a mass-retaining localized shading on a
new coaxially reanchored family satisfying literal WZ2 Definition 2.12.

Allowing bounded axial reanchoring is essential in the ordinary unit-segment
model.  Bare fixed-dilation containment does not control source and parent
segment endpoints at scale `rho`, so the corresponding unchanged-carrier
subfamily statement is false.
-/
def PureWZ2GWZReanchoredConversionStatement : Prop :=
  ∀ A R : ℝ,
    1 ≤ A →
    1 ≤ R →
      ∀ outputLoss : ℝ,
        0 < outputLoss →
        ∃ logExponent : ℕ,
        ∃ inputLoss delta₀ : ℝ,
          0 < inputLoss ∧
          0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ source : Kakeya.Streamlined.TubeFamily delta,
              source.Nonempty →
              PureWZ2FixedBallSupport source R →
              source.IsEssentiallyDistinct →
              ∀ fullFiberData :
                  PureWZ2GWZFullFiberStructure (A := A) source
                    (Kakeya.realRpowENN delta (-inputLoss)),
                ∀ sourceShading :
                    Kakeya.Streamlined.TubeShading source,
                  sourceShading.IsLambdaDense
                      (Kakeya.realRpowENN delta inputLoss) →
                    ∃ data :
                        PureWZ2GWZReanchoredConversionData
                          sourceShading
                          (Kakeya.realRpowENN delta (-outputLoss))
                          logExponent,
                      data.reanchored.Nonempty ∧
                      data.shading.IsLambdaDense
                        (Kakeya.realRpowENN delta outputLoss)

/-- The direct pure-WZ2-to-GWZ implication after the corrected remark. -/
def PureWZ2ToFixedSupportDilatedStickyStatement : Prop :=
  PureWZ2GWZReanchoredConversionStatement →
    ∀ A R : ℝ,
      1 ≤ A →
      1 ≤ R →
      PureWZ2Theorem5_2Statement →
        PureWZ2FixedSupportDilatedStickyContract A R

/--
The pure WZ2 theorem and the corrected GWZ remark imply the fixed-support
semantic contract.

The loss supplied to the public WZ2 theorem is used as the output loss in the
GWZ conversion.  The conversion chooses the stronger input loss demanded of
the concrete GWZ structure.  The reanchored shading is unchanged as a subset
of the source shading, so its volume lower bound transfers back to the source
union even though the output tube carriers are new.
-/
theorem pure_wz2_to_fixed_support_dilated_sticky :
    PureWZ2ToFixedSupportDilatedStickyStatement := by
  intro conversion A R hA hR pureTheorem
  intro epsilon hepsilon
  rcases pureTheorem epsilon hepsilon with
    ⟨outputLoss, theoremDelta₀, houtputLoss,
      htheoremDelta₀, htheoremDelta₀One, htheorem⟩
  rcases conversion A R hA hR outputLoss houtputLoss with
    ⟨logExponent, inputLoss, conversionDelta₀,
      hinputLoss, hconversionDelta₀,
      hconversionDelta₀One, hconversion⟩
  let delta₀ := min theoremDelta₀ conversionDelta₀
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans htheoremDelta₀One
  refine ⟨inputLoss, delta₀, hinputLoss, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaSmall source
    hsourceNonempty hsourceSupport hsourceDistinct
    fullFiberData sourceShading hsourceDense
  have hdeltaTheorem : delta ≤ theoremDelta₀ :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaConversion : delta ≤ conversionDelta₀ :=
    hdeltaSmall.trans (min_le_right _ _)
  rcases hconversion delta hdelta hdeltaConversion
      source hsourceNonempty hsourceSupport hsourceDistinct
      fullFiberData sourceShading hsourceDense with
    ⟨data, hreanchoredNonempty, hreanchoredDense⟩
  have hreanchoredLower :
      Kakeya.realRpowENN delta epsilon ≤
        volume data.shading.union :=
    htheorem delta hdelta hdeltaTheorem
      data.reanchored hreanchoredNonempty
      data.literal_cwa data.shading hreanchoredDense
  have hunionSubset :
      data.shading.union ⊆ sourceShading.union := by
    rintro point ⟨index, hpoint⟩
    exact
      ⟨data.sourceIndex index,
        data.subshading index hpoint⟩
  exact hreanchoredLower.trans (measure_mono hunionSubset)

/--
Node 9: the corrected mathematical content of the GWZ comparison remark.

The remark converts exact-scale, fixed-dilation complete-full-fiber
uniformity and Frostman data into literal WZ2 Definition 2.12 after localized
coaxial reanchoring and mass-retaining selection.  It is mathematically
independent of the proof of Theorem 5.2 and may therefore be proved in
parallel with Nodes 1--8.
-/
def PureWZ2GWZRemarkStatement : Prop :=
  PureWZ2GWZReanchoredConversionStatement

/--
Post-Node-9 semantic assembly.

This combines the pure WZ2 theorem with the rigorous GWZ remark and supplies
the fixed `A = 7998000`, `R = 10` semantic volume contract.  It is deliberately
separate from Node 9 so that the GWZ remark remains one independent proof
obligation.
-/
def PureWZ2SemanticSocketAssemblyStatement : Prop :=
  PureWZ2Theorem5_2Statement →
    PureWZ2GWZRemarkStatement →
      PureWZ2FixedSupportDilatedStickyContract 7998000 10

/-- The post-node semantic socket assembly is already closed. -/
theorem pure_wz2_semantic_socket_assembly :
    PureWZ2SemanticSocketAssemblyStatement := by
  intro pureTheorem remark
  exact
    pure_wz2_to_fixed_support_dilated_sticky
      remark 7998000 10 (by norm_num) (by norm_num) pureTheorem

/--
Provisional alias for the semantic socket assembly.

After the seven frozen GWZ interface files are synchronized, a separate
concrete ABI node must project `DilatedUniformTubeStructure` to
`PureWZ2GWZFullFiberStructure` and conclude the actual
`GWZStickyVolumeSocket`.
-/
def PureWZ2ToGWZBridgeStatement : Prop :=
  PureWZ2SemanticSocketAssemblyStatement

end Kakeya.Assouad

end
