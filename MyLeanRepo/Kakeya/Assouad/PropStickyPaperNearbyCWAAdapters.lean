import MyLeanRepo.Kakeya.Assouad.PropStickyWeakening

/-!
# Adapters for nearby-scale paper CWA

The complete nearby-scale predicate differs from the raw hereditary-cover
predicate only by top-level essential distinctness.
-/

noncomputable section

namespace Kakeya.Assouad

theorem WZ2PaperCWACoversAtNearbyScales.withEssentiallyDistinct
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (covers : WZ2PaperCWACoversAtNearbyScales family C)
    (distinct : WZ1PaperIsEssentiallyDistinct family) :
    WZ2PaperCWAAtNearbyScales family C :=
  ⟨covers.1, covers.2.1, distinct, covers.2.2⟩

@[simp] theorem
    WZ2PaperCWAAtNearbyScales.toCoversAtNearbyScales_withEssentiallyDistinct
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperCWAAtNearbyScales family C) :
    data.toCoversAtNearbyScales.withEssentiallyDistinct data.2.2.1 =
      data := by
  rfl

end Kakeya.Assouad

end
