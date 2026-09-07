import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.Statements

/-!
# WZ1 counted-broad pruning

Closed proof of the counted-broad deletion step in WZ1 Lemma 11.
-/

namespace Kakeya.Assouad

theorem wz1_narrow_pruning :
    WZ1NarrowPruningStatement := by
  intro delta tau Q F Y hB h_mass
  let B := wz1CountedBroadSet Y tau Q
  let shading : Kakeya.Streamlined.TubeShading F :=
    { carrier := fun i => Y.carrier i \ B
      measurable_carrier := fun i =>
        (Y.measurable_carrier i).diff hB
      subset_body := fun i =>
        Set.Subset.trans (fun p hp => hp.1) (Y.subset_body i) }
  have h_sub : IsSubshading shading Y := by
    intro i
    exact fun p hp => hp.1
  have h_carrier_eq : ∀ i, shading.carrier i = Y.carrier i \ B := by
    intro i
    rfl
  let broadMass : ENNReal := ∫⁻ p in B, (Y.pointMultiplicity p : ENNReal)
  have h_fubini :
      (∑ i : Fin F.card, MeasureTheory.volume (Y.carrier i ∩ B)) = broadMass :=
    sum_volume_inter_eq_setLIntegral_pointMultiplicity Y hB
  have h_mass_decomp : Y.mass = shading.mass + broadMass := by
    have h1 : ∀ i : Fin F.card,
        MeasureTheory.volume (Y.carrier i) =
          MeasureTheory.volume (shading.carrier i) + MeasureTheory.volume (Y.carrier i ∩ B) := by
      intro i
      have h2 : MeasureTheory.volume (Y.carrier i ∩ B) + MeasureTheory.volume (Y.carrier i \ B) =
            MeasureTheory.volume (Y.carrier i) :=
        MeasureTheory.measure_inter_add_sdiff₀ (Y.carrier i) hB.nullMeasurableSet
      simpa [shading, add_comm] using h2.symm
    calc
      Y.mass
        = ∑ i : Fin F.card, MeasureTheory.volume (Y.carrier i) := rfl
      _ = ∑ i : Fin F.card, (MeasureTheory.volume (shading.carrier i) + MeasureTheory.volume (Y.carrier i ∩ B)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact h1 i
      _ = shading.mass + ∑ i : Fin F.card, MeasureTheory.volume (Y.carrier i ∩ B) := by
          rw [Finset.sum_add_distrib]
          ; rfl
      _ = shading.mass + broadMass := by rw [h_fubini]
  have hY_finite : Y.mass ≠ ⊤ := by
    simp only [Kakeya.Streamlined.Shading.mass, ENNReal.sum_ne_top]
    intro i _
    have hsegment :
        IsCompact (Kakeya.unitSegment (F.tube i).base (F.tube i).direction) :=
      isCompact_Icc.image
        (continuous_const.add (continuous_id.smul continuous_const))
    have htube : IsCompact (F.tube i).carrier := by
      simpa [Kakeya.DeltaTube.carrier] using hsegment.cthickening
    have hle :
        MeasureTheory.volume (Y.carrier i) ≤
          MeasureTheory.volume (F.tube i).carrier :=
      MeasureTheory.measure_mono (Y.subset_body i)
    exact (hle.trans_lt htube.measure_lt_top).ne
  have h_broad_finite : broadMass ≠ ⊤ := by
    by_contra h
    have h' : 2 * broadMass = ⊤ := by
      rw [h] ; simp
    rw [h'] at h_mass
    exact hY_finite (top_le_iff.mp h_mass)
  have h_broad_le_shading : broadMass ≤ shading.mass := by
    have h3 : 2 * broadMass ≤ shading.mass + broadMass := by
      rw [← h_mass_decomp]
      exact h_mass
    have h4 : broadMass + broadMass ≤ shading.mass + broadMass := by
      simpa [two_mul] using h3
    exact (WithTop.add_le_add_iff_right h_broad_finite).mp h4
  have h5 : Y.mass ≤ 2 * shading.mass := by
    calc
      Y.mass = shading.mass + broadMass := h_mass_decomp
      _ ≤ shading.mass + shading.mass := by gcongr
      _ = 2 * shading.mass := by
        simp [two_mul]
  have h_half : (1 / 2 : ENNReal) * Y.mass ≤ shading.mass := by
    have h6 : (1 / 2 : ENNReal) * Y.mass ≤ (1 / 2 : ENNReal) * (2 * shading.mass) :=
      mul_le_mul_right h5 (1 / 2 : ENNReal)
    have h7 : (1 / 2 : ENNReal) * (2 * shading.mass) = shading.mass := by
      simpa [div_eq_mul_inv] using
        ENNReal.inv_mul_cancel_left (show (2 : ENNReal) ≠ 0 by norm_num)
          (show (2 : ENNReal) ≠ ⊤ by norm_num)
    rw [h7] at h6
    exact h6
  have h_count_mono : ∀ p, wz1LargeTripleCount shading p tau ≤ wz1LargeTripleCount Y p tau := by
    intro p
    classical
    apply Finset.card_le_card
    intro ijk h
    simp only [Finset.mem_filter] at h ⊢
    exact ⟨h.1,
      h_sub ijk.1 h.2.1,
      h_sub ijk.2.1 h.2.2.1,
      h_sub ijk.2.2 h.2.2.2.1,
      h.2.2.2.2⟩
  have h_lt : ∀ p ∈ shading.union, wz1LargeTripleCount shading p tau < Q := by
    intro p hp
    have h_in_Y : p ∈ Y.union := h_sub.union_subset hp
    have h_not_B : p ∉ B := by
      rcases hp with ⟨i, hi⟩
      exact hi.2
    have h_count_lt_Q : wz1LargeTripleCount Y p tau < Q := by
      by_contra h
      have h' : Q ≤ wz1LargeTripleCount Y p tau := by linarith
      exact h_not_B ⟨h_in_Y, h'⟩
    exact (h_count_mono p).trans_lt h_count_lt_Q
  exact ⟨shading, h_sub, h_carrier_eq, h_half, h_lt⟩

end Kakeya.Assouad
