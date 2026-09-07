import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RootNormalization

/-!
# Root input for the Proposition 6.3 four-call iteration

This companion keeps the strict ordinary axial `1 / 8` certificate attached
to the exact root normalization used by the four-call iteration.  Its concrete
producer consumes Node 3's synchronized realization: the root and the axial
certificate therefore come from the same `normalized` field.  In particular,
no `1 / 8` conclusion is inferred from the normalization record's weaker
`1 / 4` field.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The root normalization together with the strict ordinary axial window
needed by the four-call M5 path. -/
structure Proposition63FourCallRootInput
    {sigma inputLoss normalizationLoss densityLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss) : Prop where
  ordinaryAxialWindowEighth :
    ∀ index point,
      point ∈ root.normalization.frame ''
          root.normalization.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8

/-- Build the four-call root input from one synchronized Node 3 realization.
The resulting root is definitionally built from `realization.normalized`, so
the strict axial certificate and every root-normalization field refer to the
same source, frame, ordinary shading, and cropped family. -/
theorem Proposition63FourCallRootInput.ofPropStickyRealization
    {sigma outputLoss scaleCeiling densityLoss : ℝ}
    {normalizationExponent logExponent : ℕ}
    (realization : PureWZ2PropStickyRealizationData
      (sigma := sigma) (outputLoss := outputLoss)
      (scaleCeiling := scaleCeiling) normalizationExponent logExponent)
    (density_absorb :
      Kakeya.realRpowENN realization.delta densityLoss ≤
        Kakeya.realRpowENN realization.delta realization.sourceLoss / 2) :
    Proposition63FourCallRootInput
      (_root_.Kakeya.Assouad.PureWZ2.Proposition63RootNormalizationData.ofNormalization
        (normalized := realization.normalized)
        (density_absorb := density_absorb)) := by
  let root : Proposition63RootNormalizationData
      (outputLoss := realization.normalizationLoss) realization.source
        normalizationExponent densityLoss :=
    _root_.Kakeya.Assouad.PureWZ2.Proposition63RootNormalizationData.ofNormalization
      (normalized := realization.normalized)
      (density_absorb := density_absorb)
  change Proposition63FourCallRootInput root
  refine ⟨?_⟩
  simpa [root, Proposition63RootNormalizationData.ofNormalization] using
    realization.normalized_ordinary_axial_window_eighth

/-- Loss-only weakening preserves the strict axial certificate because the
frame and ordinary shading of the normalization are unchanged definitionally. -/
theorem Proposition63FourCallRootInput.weaken
    {sigma oldInputLoss newInputLoss oldNormalizationLoss
      newNormalizationLoss densityLoss delta : ℝ}
    {normalizationExponent : ℕ}
    {source : PureWZ2ExtremalConfiguration sigma oldInputLoss delta}
    {root : Proposition63RootNormalizationData
      (outputLoss := oldNormalizationLoss) source normalizationExponent
        densityLoss}
    (input : Proposition63FourCallRootInput root)
    (inputLoss_le : oldInputLoss ≤ newInputLoss)
    (normalizationLoss_le : oldNormalizationLoss ≤ newNormalizationLoss)
    (newInputLoss_pos : 0 < newInputLoss)
    (newNormalizationLoss_pos : 0 < newNormalizationLoss)
    (delta_pos : 0 < delta)
    (delta_le_one : delta ≤ 1)
    (input_le_half : newInputLoss ≤ newNormalizationLoss / 2) :
    Proposition63FourCallRootInput
      (root.weaken inputLoss_le normalizationLoss_le newInputLoss_pos
        newNormalizationLoss_pos delta_pos delta_le_one input_le_half) where
  ordinaryAxialWindowEighth := by
    intro index point point_mem
    exact input.ordinaryAxialWindowEighth index point point_mem

end Kakeya.Assouad.PureWZ2

end
