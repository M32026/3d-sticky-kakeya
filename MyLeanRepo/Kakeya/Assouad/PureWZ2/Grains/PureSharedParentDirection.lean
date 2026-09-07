import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureCarrierDirectionAlignment

/-! # Direction distance inside one pure strict full fiber -/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- Two fine tubes contained in the same ordinary parent have positively
oriented paper directions within `8 * rho`. -/
lemma paper_directions_close_of_shared_carrier_parent
    {delta rho : ℝ}
    {first second : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (hdelta : 0 ≤ delta) (hrho : 0 < rho) (hrhoSmall : rho < 1 / 8)
    (hfirstLine : WZ1PaperTubeInLineClass first)
    (hsecondLine : WZ1PaperTubeInLineClass second)
    (hfirst : first.carrier ⊆ parent.carrier)
    (hsecond : second.carrier ⊆ parent.carrier) :
    ‖wz1PaperDirection first - wz1PaperDirection second‖ ≤ 8 * rho := by
  have hfirstAlign :
      ‖wz1PaperDirection first - wz1PaperDirection parent‖ ≤ 4 * rho :=
    paper_direction_alignment_of_carrier_subset
      (fine := first) (parent := parent)
      hdelta hrho hrhoSmall hfirstLine hfirst
  have hsecondAlign :
      ‖wz1PaperDirection second - wz1PaperDirection parent‖ ≤ 4 * rho :=
    paper_direction_alignment_of_carrier_subset
      (fine := second) (parent := parent)
      hdelta hrho hrhoSmall hsecondLine hsecond
  have hdecomp :
      wz1PaperDirection first - wz1PaperDirection second =
        (wz1PaperDirection first - wz1PaperDirection parent) +
          (wz1PaperDirection parent - wz1PaperDirection second) := by
    abel
  calc
    ‖wz1PaperDirection first - wz1PaperDirection second‖ =
        ‖(wz1PaperDirection first - wz1PaperDirection parent) +
          (wz1PaperDirection parent - wz1PaperDirection second)‖ := by
      rw [hdecomp]
    _ ≤
        ‖wz1PaperDirection first - wz1PaperDirection parent‖ +
          ‖wz1PaperDirection parent - wz1PaperDirection second‖ :=
      norm_add_le _ _
    _ ≤ 4 * rho + 4 * rho := by
      exact add_le_add hfirstAlign (by
        simpa [norm_sub_rev] using hsecondAlign)
    _ = 8 * rho := by ring

end Kakeya.Assouad.PureWZ2

end
