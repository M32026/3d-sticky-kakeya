import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperNearbyTopLevelPowerCWA

/-!
# Top-level Convex-Wolff recovery from nearby-scale CWA

This compatibility module exposes the paper-specific power-form consequence
proved in `Prop62PaperNearbyTopLevelPowerCWA`.

The former proof requested the top scale `1` and incorrectly treated the raw
actual scale as an `AdmissibleScale`, thereby manufacturing an upper bound
`rho ≤ 1` and then `rho = 1`.  Assouad Definition 2.12 only gives

`requested ≤ rho < C * requested`

with `rho > 0`.  The safe theorem instead requests the subunit scale
`delta ^ loss`; the nearby window then gives the upper bound needed by the
historical-rescaling argument.  Its honest conclusion has the cubic power
loss `D * delta ^ (-3 * loss)`.
-/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_nearby_top_level_convex_wolff :
    ∃ dimensionConstant : ℕ, 0 < dimensionConstant ∧
      ∀ {delta loss : ℝ},
        0 < delta →
        delta ≤ 1 / 100 →
        0 < loss →
        ∀ {family : Kakeya.Streamlined.TubeFamily delta},
          WZ2PaperCWAAtNearbyScales family
              (Kakeya.realRpowENN delta (-loss)) →
            WZ2PaperConvexWolffBound family
              ((dimensionConstant : ENNReal) *
                Kakeya.realRpowENN delta (-3 * loss)) := by
  refine
    ⟨1715072373, by norm_num, ?_⟩
  intro delta loss hdelta hdeltaSmall hloss family hNearby
  exact
    wz2_paper_nearby_top_level_power_cwa
      hdelta hdeltaSmall hloss hNearby

noncomputable def wz2PaperNearbyTopLevelDimensionConstant : ℕ :=
  Classical.choose wz2_paper_nearby_top_level_convex_wolff

theorem wz2PaperNearbyTopLevelDimensionConstant_pos :
    0 < wz2PaperNearbyTopLevelDimensionConstant :=
  (Classical.choose_spec
    wz2_paper_nearby_top_level_convex_wolff).1

theorem wz2_paper_nearby_top_level_convex_wolff_canonical
    {delta loss : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 100)
    (hloss : 0 < loss)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hcwa :
      WZ2PaperCWAAtNearbyScales family
        (Kakeya.realRpowENN delta (-loss))) :
    WZ2PaperConvexWolffBound family
      ((wz2PaperNearbyTopLevelDimensionConstant : ENNReal) *
        Kakeya.realRpowENN delta (-3 * loss)) :=
  (Classical.choose_spec
    wz2_paper_nearby_top_level_convex_wolff).2
      hdelta hdeltaSmall hloss hcwa

end Kakeya.Assouad

end
