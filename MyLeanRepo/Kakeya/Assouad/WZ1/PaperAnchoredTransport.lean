import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADScaleGeneral
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperADScaleRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.TransportNormalizeAD

/-!
# Paper AD transport under an anchored rescaling

This is the paper-predicate analogue of the normalized transport lemmas.  It
uses the exact inverse-transpose pairing, then translates and positively
rescales the one-dimensional projection.  Unlike the internal bounded AD
predicate, `PureWZ2PaperADSet1` needs no artificial ambient-ball hypothesis.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- Paper AD is stable under an affine coordinate change whose linear factor
has absolute value between `1/4` and `4`. -/
lemma PureWZ2PaperADSet1.affine
    {S : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 S delta alpha C)
    (a b : ℝ) (haLower : 1 / 4 ≤ |a|) (haUpper : |a| ≤ 4)
    (hdeltaOne : delta ≤ 1) :
    PureWZ2PaperADSet1 ((fun value : ℝ => a * value + b) '' S)
      delta alpha (100 * C) := by
  have haNe : a ≠ 0 := by
    intro ha
    rw [ha, abs_zero] at haLower
    norm_num at haLower
  by_cases haNonnegative : 0 ≤ a
  · have haPositive : 0 < a := lt_of_le_of_ne haNonnegative haNe.symm
    have htranslated := (hAD.scale a haPositive
      (by simpa [abs_of_pos haPositive] using haLower)
      (by simpa [abs_of_pos haPositive] using haUpper) hdeltaOne).translate b
    have himage :
        (fun value : ℝ => a * value + b) '' S =
          (fun value : ℝ => value + b) ''
            ((fun value : ℝ => a * value) '' S) := by
      ext value
      simp only [Set.mem_image]
      constructor
      · rintro ⟨source, hsource, rfl⟩
        exact ⟨a * source, ⟨source, hsource, rfl⟩, rfl⟩
      · rintro ⟨scaled, ⟨source, hsource, rfl⟩, rfl⟩
        exact ⟨source, hsource, rfl⟩
    rw [himage]
    exact htranslated
  · let c : ℝ := -a
    have hcPositive : 0 < c := by dsimp only [c]; linarith
    have hcAbs : |a| = c := by
      dsimp only [c]
      rw [abs_of_neg (lt_of_not_ge haNonnegative)]
    have hscaled := hAD.scale c hcPositive
      (by simpa [hcAbs] using haLower)
      (by simpa [hcAbs] using haUpper) hdeltaOne
    have hnegative := hscaled.negate
    have himage :
        (fun value : ℝ => a * value + b) '' S =
          (fun value : ℝ => value + b) ''
            ((fun value : ℝ => -value) ''
              ((fun value : ℝ => c * value) '' S)) := by
      ext value
      simp only [Set.mem_image]
      constructor
      · rintro ⟨source, hsource, rfl⟩
        exact ⟨a * source, ⟨c * source, ⟨source, hsource, rfl⟩, by
          dsimp only [c]
          ring⟩, rfl⟩
      · rintro ⟨shifted, ⟨scaled, ⟨source, hsource, rfl⟩, rfl⟩, rfl⟩
        exact ⟨source, hsource, by dsimp only [c]; ring⟩
    rw [himage]
    exact hnegative.translate b

lemma paper_transport_and_normalize_ad
    {E : Set Point3} {v : Point3}
    {rho sourceDelta sourceScale targetScale alpha : ℝ} {C : ENNReal}
    (hrho : 0 < rho)
    (anchor : Kakeya.DeltaTube sourceDelta)
    (hAD : PureWZ2PaperADSet1
      (scalarProjection v E) sourceScale alpha C)
    (hNv_pos :
      0 < ‖wz1AnchoredUnitRescalingNormalLinear anchor rho v‖)
    (hscale :
      (1 / ‖wz1AnchoredUnitRescalingNormalLinear anchor rho v‖) *
          sourceScale ≤ targetScale) :
    PureWZ2PaperADSet1
      (scalarProjection
        ((1 / ‖wz1AnchoredUnitRescalingNormalLinear anchor rho v‖) •
          wz1AnchoredUnitRescalingNormalLinear anchor rho v)
        (wz1AnchoredUnitRescalingMap anchor rho hrho '' E))
      targetScale alpha C := by
  let Nv := wz1AnchoredUnitRescalingNormalLinear anchor rho v
  let a : ℝ := 1 / ‖Nv‖
  let center : Point3 :=
    anchor.base + (1 / 2 : ℝ) • anchor.direction
  let sourceProjection := scalarProjection v E
  let rawProjection := scalarProjection Nv
    (wz1AnchoredUnitRescalingMap anchor rho hrho '' E)
  have hraw : rawProjection =
      (fun value : ℝ => value - inner ℝ center v) '' sourceProjection := by
    exact scalarProjection_anchored_transport
      (anchor := anchor) (rho := rho) (hrho := hrho)
      (E := E) (v := v)
  have htranslated : PureWZ2PaperADSet1 rawProjection
      sourceScale alpha C := by
    rw [hraw]
    exact hAD.translate (-inner ℝ center v)
  have ha : 0 < a := by positivity
  have hscaled : PureWZ2PaperADSet1
      ((fun value : ℝ => a * value) '' rawProjection)
      (a * sourceScale) alpha C :=
    htranslated.scale_general a ha
  have hprojection :
      scalarProjection (a • Nv)
          (wz1AnchoredUnitRescalingMap anchor rho hrho '' E) =
        (fun value : ℝ => a * value) '' rawProjection := by
    exact scalarProjection_scale a ha Nv
      (wz1AnchoredUnitRescalingMap anchor rho hrho '' E)
  rw [hprojection]
  exact PureWZ2.paper_ad_coarsen_minimum_scale hscaled hscale

end Kakeya.Assouad

end
