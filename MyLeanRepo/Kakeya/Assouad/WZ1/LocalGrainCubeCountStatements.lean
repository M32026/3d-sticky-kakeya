import MyLeanRepo.Kakeya.Assouad.WZ1.Statements

/-!
# Paper-level leaves for WZ1 Lemma 17

These interfaces split the hard branch of the local-grain cube count at the
three genuine mathematical boundaries in the paper:

1. a same-configuration refinement carrying both balanced scales, two
   property-(P) shadings, constant multiplicity, and transverse witnesses;
2. the Córdoba argument that turns those witnesses into a full grain inside
   the appropriate scalar-projection slab;
3. the second balanced cover's local volume upper bound.

None of the three statements imports an open target.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/--
Fixed loss in the fine pullback mass argument: factor `8 * 10^6` from the
coarse cell-volume comparison, factor `4` from the fine parent-cell mass
band, and factor `2` from `restore_extremality_from_mass`.
-/
def wz1Lemma17FinePullbackAbsorptionConstant : ENNReal :=
  64000000

/-- The plane normal attached to the balanced spatial cell containing `p`. -/
def wz1Lemma17CellNormal
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (first :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (plane : WZ1PlaneMapData Y) (p : Point3) : Point3 :=
  plane.planeMap (first.representative (first.cell p))

/--
The dependent refinement produced before the Córdoba estimate in WZ1
Lemma 17.

`propertyOne` and `propertyThree` are the paper's first and second
property-(P) refinements.  The intermediate `constantShading` carries the
constant point multiplicity.  The `tau` cover and robust cover are nested
rather than chosen on unrelated configurations.  Finally `fineShading`
records the induced refinement on the original `delta`-tube family, so the
eventual Lemma 17 conclusion remains on the input family.
-/
structure WZ1Lemma17RefinementData
    {delta sigma epsilon₁ epsilon₂ epsilon₃ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (first :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon₁) U Y rho)
    (plane : WZ1PlaneMapData Y)
    (tau : Kakeya.Streamlined.AdmissibleScale delta)
    (tauAtRho : Kakeya.Streamlined.AdmissibleScale rho.1)
    (tauCover :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon₂)
        first.coarseUniform first.coarseShading tauAtRho)
    (robustScale : Kakeya.Streamlined.AdmissibleScale rho.1)
    (robustCover :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon₁)
        first.coarseUniform tauCover.refined robustScale) where
  propertyOne :
    Kakeya.Streamlined.TubeShading (U.coarse rho)
  propertyOne_sub_robust :
    IsSubshading propertyOne robustCover.refined
  propertyOne_sub_tau :
    IsSubshading propertyOne tauCover.refined
  propertyOne_extremal :
    WZ1ExtremalPair sigma epsilon₂
      (U.coarse rho) first.coarseUniform propertyOne
  constantShading :
    Kakeya.Streamlined.TubeShading (U.coarse rho)
  constant_subshading :
    IsSubshading constantShading propertyOne
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  constant_multiplicity :
    constantShading.HasConstantMultiplicity
      multiplicity (2 * multiplicity)
  multiplicity_lower :
    Kakeya.realRpowENN rho.1 (-sigma + epsilon₁) ≤
      (2 * multiplicity : ENNReal)
  propertyThree :
    Kakeya.Streamlined.TubeShading (U.coarse rho)
  propertyThree_subshading :
    IsSubshading propertyThree constantShading
  propertyThree_extremal :
    WZ1ExtremalPair sigma epsilon₂
      (U.coarse rho) first.coarseUniform propertyThree
  propertyOne_full :
    ∀ j p, p ∈ propertyOne.carrier j →
      Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
          ENNReal.ofReal tau.1 ≤
        volume
          (propertyOne.carrier j ∩ Metric.closedBall p tau.1)
  propertyThree_full :
    ∀ j p, p ∈ propertyThree.carrier j →
      Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
          ENNReal.ofReal tau.1 ≤
        volume
          (propertyThree.carrier j ∩ Metric.closedBall p tau.1)
  transverse :
    ∀ p ∈ propertyThree.union,
      ∀ i, p ∈ propertyThree.carrier i →
        ∃ j,
          p ∈ propertyOne.carrier j ∧
          Real.rpow rho.1 epsilon₃ ≤
            ‖wz1Cross
              ((U.coarse rho).tube i).direction
              ((U.coarse rho).tube j).direction‖
  fineShading : Kakeya.Streamlined.TubeShading F
  fine_subshading : IsSubshading fineShading first.refined
  fine_extremal :
    WZ1ExtremalPair sigma epsilon₂ F U fineShading
  fine_supported_on_propertyThree_cell :
    ∀ i p, p ∈ fineShading.carrier i →
      ∃ q,
        q ∈ propertyThree.carrier ((U.cover rho).parent i) ∧
          first.cell q = first.cell p

/--
The cell-level pullback puts every retained fine point within `2 * rho` of
the retained coarse Property-(P) shading for its own parent.
-/
lemma WZ1Lemma17RefinementData.fine_near_propertyThree
    {delta sigma epsilon₁ epsilon₂ epsilon₃ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {first :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon₁) U Y rho}
    {plane : WZ1PlaneMapData Y}
    {tau : Kakeya.Streamlined.AdmissibleScale delta}
    {tauAtRho : Kakeya.Streamlined.AdmissibleScale rho.1}
    {tauCover :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon₂)
        first.coarseUniform first.coarseShading tauAtRho}
    {robustScale : Kakeya.Streamlined.AdmissibleScale rho.1}
    {robustCover :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon₁)
        first.coarseUniform tauCover.refined robustScale}
    (data :
      WZ1Lemma17RefinementData
        (epsilon₃ := epsilon₃)
        first plane tau tauAtRho tauCover robustScale robustCover) :
    ∀ i p, p ∈ data.fineShading.carrier i →
      ∃ q,
        q ∈ data.propertyThree.carrier ((U.cover rho).parent i) ∧
          dist p q ≤ 2 * rho.1 := by
  intro i p hp
  rcases data.fine_supported_on_propertyThree_cell i p hp with
    ⟨q, hq, hcell⟩
  have hpFine : p ∈ first.refined.carrier i :=
    data.fine_subshading i hp
  have hpCoarse :
      p ∈ first.coarseShading.carrier ((U.cover rho).parent i) :=
    first.point_compatibility i p hpFine
  have hqPropertyOne :
      q ∈ data.propertyOne.carrier ((U.cover rho).parent i) :=
    data.constant_subshading _
      (data.propertyThree_subshading _ hq)
  have hqTau :
      q ∈ tauCover.refined.carrier ((U.cover rho).parent i) :=
    data.propertyOne_sub_tau _ hqPropertyOne
  have hqCoarse :
      q ∈ first.coarseShading.carrier ((U.cover rho).parent i) :=
    tauCover.subshading _ hqTau
  refine ⟨q, hq, ?_⟩
  exact
    first.cell_diameter p
      ⟨(U.cover rho).parent i, hpCoarse⟩ q
      ⟨(U.cover rho).parent i, hqCoarse⟩ hcell.symm

/--
WZ1 Lemma 17, dependent refinement leaf.

The two Proposition 5 outputs are explicit dependent inputs: the robust cover
is built on the refinement returned by the `tau` cover.  The close-direction
estimate and its numerical absorption are also explicit.  The target performs
the remaining Property-(P), constant-multiplicity, second Property-(P), and
fine-family pullback refinements on this one configuration.
-/
def WZ1Lemma17SameConfigurationRefinementStatement : Prop :=
  ∀ epsilon₁ epsilon₂ epsilon₃ : ℝ,
    0 < epsilon₁ →
    0 < epsilon₂ →
    0 < epsilon₃ →
    epsilon₁ < epsilon₂ →
    epsilon₂ < epsilon₃ →
    epsilon₁ + epsilon₃ < 1 →
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 / 1000 ∧
      ∀ {delta sigma : ℝ},
        ∀ {F : Kakeya.Streamlined.TubeFamily delta},
          ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
            ∀ {Y : Kakeya.Streamlined.TubeShading F},
              ∀ {rho : Kakeya.Streamlined.AdmissibleScale delta},
                ∀ (first :
                    WZ1BalancedCoverData
                      (sigma := sigma) (epsilon := epsilon₁)
                      U Y rho),
                  ∀ (plane : WZ1PlaneMapData Y),
                    ∀ (tau : Kakeya.Streamlined.AdmissibleScale delta),
                      ∀ (tauAtRho :
                          Kakeya.Streamlined.AdmissibleScale rho.1),
                        ∀ (tauCover :
                            WZ1BalancedCoverData
                              (sigma := sigma) (epsilon := epsilon₂)
                              first.coarseUniform first.coarseShading
                                tauAtRho),
                          ∀ (robustScale :
                              Kakeya.Streamlined.AdmissibleScale rho.1),
                            ∀ (robustCover :
                                WZ1BalancedCoverData
                                  (sigma := sigma) (epsilon := epsilon₁)
                                  first.coarseUniform tauCover.refined
                                    robustScale),
                              0 < sigma → sigma < 1 →
                              0 < rho.1 → rho.1 ≤ rho₀ →
                              wz1Lemma17FinePullbackAbsorptionConstant *
                                  Kakeya.realRpowENN delta
                                    (epsilon₂ - epsilon₁) ≤
                                Kakeya.realRpowENN rho.1 epsilon₂ →
                              tauAtRho.1 = tau.1 →
                              robustScale.1 =
                                Real.rpow rho.1 epsilon₃ →
                              rho.1 ≤ tau.1 →
                              tau.1 ≤ 1 →
                              ∀ D : ℕ, 0 < D →
                                (∀ p ∈ robustCover.refined.union,
                                  ∀ i,
                                    p ∈ robustCover.refined.carrier i →
                                      (wz1CloseDirectionCount
                                          robustCover.refined p i
                                            robustScale.1 : ENNReal) ≤
                                        (D : ENNReal) *
                                          Kakeya.realRpowENN
                                            (rho.1 / robustScale.1)
                                            (-sigma - epsilon₁)) →
                                2 * (D : ENNReal) *
                                    Kakeya.realRpowENN
                                      (rho.1 / robustScale.1)
                                      (-sigma - epsilon₁) <
                                  Kakeya.realRpowENN
                                    rho.1 (-sigma + epsilon₁) →
                                  Nonempty
                                    (WZ1Lemma17RefinementData
                                      (epsilon₃ := epsilon₃)
                                      first plane tau tauAtRho tauCover
                                        robustScale robustCover)

/--
WZ1 Lemma 17, Córdoba full-grain leaf.

For every projected point of the final property-(P) shading, the first
property-(P) shading occupies a quantitatively full slab.  The normal is the
one attached to the same balanced cell.  The factor
`20 * L * rho` absorbs the cell diameter, the coarse tube radius, and the
Lipschitz variation of the original plane map.
-/
def WZ1Lemma17CordobaSlabLowerStatement : Prop :=
  ∀ epsilon₁ epsilon₂ epsilon₃ : ℝ,
    0 < epsilon₁ →
    0 < epsilon₂ →
    0 < epsilon₃ →
    epsilon₁ < epsilon₂ →
    epsilon₂ < epsilon₃ →
    epsilon₁ + epsilon₃ < 1 →
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 / 1000 ∧
    ∀ {delta sigma : ℝ},
      ∀ {F : Kakeya.Streamlined.TubeFamily delta},
      ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
        ∀ {Y : Kakeya.Streamlined.TubeShading F},
          ∀ {rho : Kakeya.Streamlined.AdmissibleScale delta},
            ∀ (first :
                WZ1BalancedCoverData
                  (sigma := sigma) (epsilon := epsilon₁)
                  U Y rho),
              ∀ (plane : WZ1PlaneMapData Y),
                ∀ (tau :
                    Kakeya.Streamlined.AdmissibleScale delta),
                  ∀ (tauAtRho :
                      Kakeya.Streamlined.AdmissibleScale rho.1),
                    ∀ (tauCover :
                        WZ1BalancedCoverData
                          (sigma := sigma) (epsilon := epsilon₂)
                          first.coarseUniform first.coarseShading
                            tauAtRho),
                      ∀ (robustScale :
                          Kakeya.Streamlined.AdmissibleScale rho.1),
                        ∀ (robustCover :
                            WZ1BalancedCoverData
                              (sigma := sigma) (epsilon := epsilon₁)
                              first.coarseUniform tauCover.refined
                                robustScale),
                          ∀ data :
                              WZ1Lemma17RefinementData
                                (epsilon₃ := epsilon₃)
                                first plane tau tauAtRho tauCover
                                  robustScale robustCover,
                            0 < rho.1 →
                            rho.1 ≤ rho₀ →
                            rho.1 ≤ tau.1 →
                            tau.1 ^ 2 ≤ 4 * rho.1 →
                            tau.1 ≤ 1 →
                            tauAtRho.1 = tau.1 →
                            ∀ q ∈ data.propertyThree.union,
                              ∀ t ∈
                                  scalarProjection
                                    (wz1Lemma17CellNormal first plane q)
                                    (data.propertyThree.union ∩
                                      Metric.closedBall q tau.1),
                                Kakeya.realRpowENN rho.1
                                      (1 + 7 * epsilon₁ + epsilon₃) *
                                    ENNReal.ofReal
                                      (tau.1 ^ 2 / 200) ≤
                                  volume
                                    (data.propertyOne.union ∩
                                      Metric.closedBall q (3 * tau.1) ∩
                                      {x |
                                        |inner ℝ x
                                              (wz1Lemma17CellNormal
                                                first plane q) - t| ≤
                                          20 *
                                            max 1
                                              (plane.lipschitzConstant : ℝ) *
                                              rho.1})

/--
WZ1 Lemma 17, local upper-volume leaf.

This is the upper estimate supplied by the dependent `tau`-scale balanced
cover.  It is stated on the same `propertyOne` shading used by the Córdoba
lower bound, preventing an invalid comparison between unrelated
refinements.  The explicit constant records the factors from the abstract
balanced-cover API: the upper half of `cell_balance`, the finite cover of a
radius-`5 * tau` ball, `neighborBound_le`, and the volume bound for one
diameter-`2 * tau` cell.
-/
def wz1Lemma17LocalVolumeConstant : ℝ :=
  2 * 27 * 10000 * 8

def WZ1Lemma17LocalVolumeUpperStatement : Prop :=
  ∀ {delta sigma epsilon₁ epsilon₂ epsilon₃ : ℝ},
    ∀ {F : Kakeya.Streamlined.TubeFamily delta},
      ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
        ∀ {Y : Kakeya.Streamlined.TubeShading F},
          ∀ {rho : Kakeya.Streamlined.AdmissibleScale delta},
            ∀ (first :
                WZ1BalancedCoverData
                  (sigma := sigma) (epsilon := epsilon₁)
                  U Y rho),
              ∀ (plane : WZ1PlaneMapData Y),
                ∀ (tau :
                    Kakeya.Streamlined.AdmissibleScale delta),
                  ∀ (tauAtRho :
                      Kakeya.Streamlined.AdmissibleScale rho.1),
                    ∀ (tauCover :
                        WZ1BalancedCoverData
                          (sigma := sigma) (epsilon := epsilon₂)
                          first.coarseUniform first.coarseShading
                            tauAtRho),
                      ∀ (robustScale :
                          Kakeya.Streamlined.AdmissibleScale rho.1),
                        ∀ (robustCover :
                            WZ1BalancedCoverData
                              (sigma := sigma) (epsilon := epsilon₁)
                              first.coarseUniform tauCover.refined
                                robustScale),
                          ∀ data :
                              WZ1Lemma17RefinementData
                                (epsilon₃ := epsilon₃)
                                first plane tau tauAtRho tauCover
                                  robustScale robustCover,
                            0 < rho.1 →
                            rho.1 ≤ tau.1 →
                            tau.1 ≤ 1 →
                            tauAtRho.1 = tau.1 →
                            ∀ q : Point3,
                              volume
                                  (data.propertyOne.union ∩
                                    Metric.closedBall q (3 * tau.1)) ≤
                                ENNReal.ofReal
                                  (wz1Lemma17LocalVolumeConstant *
                                    Real.rpow rho.1
                                      (sigma - epsilon₁) *
                                    Real.rpow tau.1
                                      (3 - sigma - epsilon₂))

end Kakeya.Assouad
