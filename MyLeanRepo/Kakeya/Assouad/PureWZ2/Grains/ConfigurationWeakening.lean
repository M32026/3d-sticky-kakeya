import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADTransport

/-! Loss weakening for a completed pure WZ2 grain configuration. -/

noncomputable section

namespace Kakeya.Assouad

open ENNReal

lemma WZ2PaperConvexWolffBound.weaken_constant
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {C C' : ENNReal}
    (hCWA : WZ2PaperConvexWolffBound family C)
    (hC_le : C ≤ C') :
    WZ2PaperConvexWolffBound family C' := by
  intro convexSet hconv
  exact (hCWA convexSet hconv).trans (by gcongr)

def PureWZ2LocalGrainData.weaken_constant
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {sigma : ℝ} {C C' : ENNReal}
    (data : PureWZ2LocalGrainData shading sigma C)
    (hC_le : C ≤ C') (hC'_top : C' ≠ ⊤) :
    PureWZ2LocalGrainData shading sigma C' := by
  refine ⟨data.planeMap, data.planeMap_lipschitz, data.planeMap_unit,
    data.planeMap_incidence, ?_⟩
  intro rho hdelta_rho hrho_one point
  exact (data.local_ad rho hdelta_rho hrho_one point).mono_const
    hC_le hC'_top

def PureWZ2LipschitzGlobalGrainData.weaken_constant
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {sigma : ℝ} {C C' : ENNReal}
    (data : PureWZ2LipschitzGlobalGrainData shading sigma C)
    (hC_le : C ≤ C') (hC'_top : C' ≠ ⊤) :
    PureWZ2LipschitzGlobalGrainData shading sigma C' := by
  refine ⟨data.f, data.lipschitz, ?_⟩
  intro z
  exact (data.paper_ad z).mono_const hC_le hC'_top

def PureWZ2GrainConfiguration.mono_loss
    {sigma firstLoss secondLoss delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hfirstLoss : 0 ≤ firstLoss)
    (hloss : firstLoss ≤ secondLoss)
    (cfg : PureWZ2GrainConfiguration sigma firstLoss delta) :
    PureWZ2GrainConfiguration sigma secondLoss delta := by
  let C1 := Kakeya.realRpowENN delta (-firstLoss)
  let C2 := Kakeya.realRpowENN delta (-secondLoss)
  have hC_le : C1 ≤ C2 := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)
  have hsecondLoss_nonneg : 0 ≤ secondLoss := hfirstLoss.trans hloss
  have hC2_one : 1 ≤ C2 := by
    dsimp only [C2]
    rw [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
    have h := Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne
      (show -secondLoss ≤ 0 by linarith)
    simpa using h
  have hC2_top : C2 ≠ ⊤ := by
    simp [C2, Kakeya.realRpowENN]
  exact
    { family := cfg.family
      shading := cfg.shading
      line_class := cfg.line_class
      cubical := cfg.cubical
      extremal := cfg.extremal.mono_loss hloss
      top_level_cwa := cfg.top_level_cwa.weaken_constant hC_le
      globalGrains := cfg.globalGrains.weaken_constant hC_le hC2_top
      localGrains := cfg.localGrains.weaken_constant hC_le hC2_top }

end Kakeya.Assouad

end
