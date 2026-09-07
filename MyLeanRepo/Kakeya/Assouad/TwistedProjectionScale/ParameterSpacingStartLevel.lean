import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingSelectedProfile

/-!
# Fixed initial level for the spacing profile

The paper begins its scale decomposition at a small positive normalized
scale.  We use the fixed grid level `12`; sufficiently small `delta` makes the
terminal depth large enough that this level is both available and early in
normalized logarithmic scale.
-/

noncomputable section

namespace Kakeya.Assouad

def parameterSpacingStartIndex : ℕ := 12

structure ParameterSpacingStartLevelData
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (tree :
      ParameterSpacingUniformTreeData
        clustered epsilon) where
  level : Fin tree.levels
  level_val :
    level.val = parameterSpacingStartIndex
  normalized_small :
    scaleWeight tree.levels level.castSucc ≤
      epsilon ^ 2 / 100

theorem parameter_spacing_start_level
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (tree :
      ParameterSpacingUniformTreeData
        clustered epsilon)
    (hlevel_available :
      parameterSpacingStartIndex < tree.levels)
    (hnormalized :
      (parameterSpacingStartIndex : ℝ) /
          (tree.levels : ℝ) ≤
        epsilon ^ 2 / 100) :
    Nonempty (ParameterSpacingStartLevelData tree) := by
  let level : Fin tree.levels :=
    ⟨parameterSpacingStartIndex, hlevel_available⟩
  exact ⟨{
    level := level
    level_val := rfl
    normalized_small := by
      simpa [level, scaleWeight] using hnormalized
  }⟩

end Kakeya.Assouad
