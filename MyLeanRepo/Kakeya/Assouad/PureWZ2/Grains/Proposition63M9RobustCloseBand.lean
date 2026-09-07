import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PaperLemma43Prepared

/-!
# Robust close-count transfer to a whole-cell dyadic band

This file isolates the arithmetic and provenance needed to transfer a robust
close-count bound from a source shading to a common whole-cell dyadic band.
The common-carrier identity, rather than subshading alone, preserves point
multiplicity on every point of the band.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set Finset

attribute [local instance] Classical.propDecidable

/-- On a common whole-cell restriction, point multiplicity agrees with the
source multiplicity at every point retained by the band. -/
lemma paper_pointMultiplicity_eq_of_common_carrier
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source band : WZ1PaperTubeShading family}
    (hbandCommon : ∀ index, band.carrier index =
      source.carrier index ∩ band.union)
    {point : Point3} (hpoint : point ∈ band.union) :
    band.pointMultiplicity point = source.pointMultiplicity point := by
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  apply Finset.filter_congr
  intro index _
  rw [hbandCommon index]
  simp only [Set.mem_inter_iff, hpoint, and_true]

/-- A robust source close-count bound transfers strictly below one twenty-fourth
of a dyadic band's lower multiplicity scale.  The factor `96` is what makes the
conclusion strict under only the dyadic upper bound `multiplicity < 2 * m`. -/
theorem paper_closeDirectionCount_lt_dyadic_div_twentyFour_of_robust_floor
    {delta kappa : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source band : WZ1PaperTubeShading family}
    {floor mu level : ℕ} {D : ENNReal}
    (hbandCommon : ∀ index, band.carrier index =
      source.carrier index ∩ band.union)
    (hbandSub : PaperIsSubshading band source)
    (hsourceFloor : ∀ point ∈ source.union,
      floor * mu ≤ source.pointMultiplicity point)
    (hsourceClose : ∀ point ∈ source.union, ∀ index,
      point ∈ source.carrier index →
        (paperCloseDirectionCount source point index kappa : ENNReal) ≤
          D * (mu : ENNReal))
    (_hbandLower : ∀ point ∈ band.union,
      2 ^ level ≤ band.pointMultiplicity point)
    (hbandUpper : ∀ point ∈ band.union,
      band.pointMultiplicity point < 2 * 2 ^ level)
    (hm : 24 ≤ 2 ^ level)
    (hfloor : (96 : ENNReal) * D ≤ (floor : ENNReal)) :
    ∀ point ∈ band.union, ∀ index, point ∈ band.carrier index →
      paperCloseDirectionCount band point index kappa < (2 ^ level) / 24 := by
  intro point hpoint index hindex
  have hpointSource : point ∈ source.union :=
    ⟨index, hbandSub index hindex⟩
  have hsourceIndex : point ∈ source.carrier index := hbandSub index hindex
  have hcloseMono :
      paperCloseDirectionCount band point index kappa ≤
        paperCloseDirectionCount source point index kappa := by
    unfold paperCloseDirectionCount
    apply Finset.card_le_card
    intro other hother
    simp only [Finset.mem_filter] at hother ⊢
    exact ⟨hother.1, hbandSub other hother.2.1, hother.2.2⟩
  have hclose : (paperCloseDirectionCount band point index kappa : ENNReal) ≤
      D * (mu : ENNReal) :=
    (Nat.cast_le.mpr hcloseMono).trans
      (hsourceClose point hpointSource index hsourceIndex)
  have hmultEq : band.pointMultiplicity point = source.pointMultiplicity point :=
    paper_pointMultiplicity_eq_of_common_carrier hbandCommon hpoint
  have hfloorBound : floor * mu < 2 * 2 ^ level := by
    exact (hsourceFloor point hpointSource).trans_lt <| by
      rw [← hmultEq]
      exact hbandUpper point hpoint
  have hscaled : 96 * paperCloseDirectionCount band point index kappa <
      2 * 2 ^ level := by
    exact_mod_cast
      (calc
        (96 : ENNReal) *
              (paperCloseDirectionCount band point index kappa : ENNReal) ≤
            96 * (D * (mu : ENNReal)) := by gcongr
        _ = ((96 : ENNReal) * D) * (mu : ENNReal) := by ring
        _ ≤ (floor : ENNReal) * (mu : ENNReal) := by gcongr
        _ = ((floor * mu : ℕ) : ENNReal) := by norm_num
        _ < ((2 * 2 ^ level : ℕ) : ENNReal) := by exact_mod_cast hfloorBound)
  have hfortyEight :
      48 * paperCloseDirectionCount band point index kappa < 2 ^ level := by
    omega
  omega

end Kakeya.Assouad.PureWZ2

end
