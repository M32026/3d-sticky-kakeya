import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement

/-!
WZ2 Section 7: select the positive or negative vertical half-window carrying
at least half of the shaded mass.
-/

namespace Kakeya.Assouad

theorem half_window_mass_selection :
    HalfWindowMassSelectionStatement := by
  intro delta F Y hY
  set Zpos : Kakeya.Streamlined.TubeShading F :=
    slabRestriction Y 0 1 with hZpos_def
  set Zneg : Kakeya.Streamlined.TubeShading F :=
    slabRestriction Y (-1) 0 with hZneg_def
  have h_cover :
      ∀ i : Fin F.card,
        Y.carrier i ⊆
          (Y.carrier i ∩ horizontalSlab (-1) 0) ∪
            (Y.carrier i ∩ horizontalSlab 0 1) := by
    intro i p hp
    have hwindow : p ∈ horizontalSlab (-1) 1 :=
      hY ⟨i, hp⟩
    by_cases hz : p (2 : Fin 3) ≤ 0
    · exact Or.inl ⟨hp, hwindow.1, hz⟩
    · exact Or.inr ⟨hp, by linarith, hwindow.2⟩
  have hpiece :
      ∀ i : Fin F.card,
        MeasureTheory.volume (Y.carrier i) ≤
          MeasureTheory.volume
              (Y.carrier i ∩ horizontalSlab (-1) 0) +
            MeasureTheory.volume
              (Y.carrier i ∩ horizontalSlab 0 1) := by
    intro i
    exact (MeasureTheory.measure_mono (h_cover i)).trans
      (MeasureTheory.measure_union_le _ _)
  have h_mass_split : Y.mass ≤ Zneg.mass + Zpos.mass := by
    calc
      Y.mass
          = ∑ i : Fin F.card,
              MeasureTheory.volume (Y.carrier i) := rfl
      _ ≤ ∑ i : Fin F.card,
            (MeasureTheory.volume
                (Y.carrier i ∩ horizontalSlab (-1) 0) +
              MeasureTheory.volume
                (Y.carrier i ∩ horizontalSlab 0 1)) :=
          Finset.sum_le_sum fun i _ => hpiece i
      _ = (∑ i : Fin F.card,
              MeasureTheory.volume
                (Y.carrier i ∩ horizontalSlab (-1) 0)) +
            (∑ i : Fin F.card,
              MeasureTheory.volume
                (Y.carrier i ∩ horizontalSlab 0 1)) := by
          rw [Finset.sum_add_distrib]
      _ = Zneg.mass + Zpos.mass := by
          rfl
  have hpigeon :
      (1 / 2 : ENNReal) * Y.mass ≤ Zneg.mass ∨
        (1 / 2 : ENNReal) * Y.mass ≤ Zpos.mass := by
    by_cases htop : Y.mass = ⊤
    · have hsum : Zneg.mass + Zpos.mass = ⊤ := by
        rw [htop] at h_mass_split
        exact top_le_iff.mp h_mass_split
      rcases ENNReal.add_eq_top.mp hsum with hneg | hpos
      · exact Or.inl (by rw [htop, hneg]; simp)
      · exact Or.inr (by rw [htop, hpos]; simp)
    · by_cases hneg : (1 / 2 : ENNReal) * Y.mass ≤ Zneg.mass
      · exact Or.inl hneg
      · right
        by_contra hpos
        have hneg' : Zneg.mass < (1 / 2 : ENNReal) * Y.mass :=
          lt_of_not_ge hneg
        have hpos' : Zpos.mass < (1 / 2 : ENNReal) * Y.mass :=
          lt_of_not_ge hpos
        have hsum :
            Zneg.mass + Zpos.mass <
              (1 / 2 : ENNReal) * Y.mass +
                (1 / 2 : ENNReal) * Y.mass :=
          ENNReal.add_lt_add hneg' hpos'
        have hhalf :
            (1 / 2 : ENNReal) * Y.mass +
                (1 / 2 : ENNReal) * Y.mass =
              Y.mass := by
          rw [← add_mul]
          have hcoeff :
              (1 / 2 : ENNReal) + (1 / 2 : ENNReal) = 1 := by
            have htwo : (2 : ENNReal) ≠ 0 := by norm_num
            have htwo_top : (2 : ENNReal) ≠ ⊤ := by norm_num
            calc
              (1 / 2 : ENNReal) + (1 / 2 : ENNReal)
                  = (2 : ENNReal) * (1 / 2 : ENNReal) := by ring
              _ = 1 := by
                simpa [one_div] using ENNReal.mul_inv_cancel htwo htwo_top
          rw [hcoeff, one_mul]
        rw [hhalf] at hsum
        exact (not_lt_of_ge h_mass_split) hsum
  rcases hpigeon with hneg | hpos
  · refine ⟨-1, Or.inr rfl, Zneg, ?_⟩
    refine ⟨?_, hneg, ?_⟩
    · intro i
      simp [Zneg, slabRestriction]
    · intro p hp
      rcases hp with ⟨i, hi⟩
      have hsign : (-1 : ℝ) ≠ 1 := by norm_num
      simpa [hsign] using hi.2
  · refine ⟨1, Or.inl rfl, Zpos, ?_⟩
    refine ⟨?_, hpos, ?_⟩
    · intro i
      simp [Zpos, slabRestriction]
    · intro p hp
      rcases hp with ⟨i, hi⟩
      simpa using hi.2

end Kakeya.Assouad
