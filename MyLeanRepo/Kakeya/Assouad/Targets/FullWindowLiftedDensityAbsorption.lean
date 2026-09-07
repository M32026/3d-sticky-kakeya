import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FullWindowLiftedDensityAbsorptionStatement
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.VerticalTubeTopBoundaryVolumeProof

/-!
# Full-window lifted density absorption

Generalizes `SelectedLiftedWindowDensityAbsorption` from a positive source
window `[0,1]` to the full slope window `[-1,1]`.  A rho-thickening may exit
through both boundary slabs `[-1-rho,-1]` and `[1,1+rho]`.  Each per-tube cap
is bounded by `100*rho^3` using `tube_slab_volume_upper_general`, summing to
`200*rho^3`, and absorbed under the budget `ofReal(400*rho)*L ≤ lambda`.
-/

namespace Kakeya.Assouad

theorem full_window_lifted_density_absorption :
    FullWindowLiftedDensityAbsorptionStatement := by
  intro delta rho hrho hrho_le fine Y hY lifted hvert Z hthick
        lambda L hlambda_top hL_zero hL_top h_density h_budget
  let W : Kakeya.Streamlined.TubeShading lifted := slabRestriction Z (-1) 1

  have h_sub : IsSubshading W Z := by
    intro i
    simp [W, slabRestriction] <;> exact Set.inter_subset_left _ _

  have h_window : IsInSlopeWindow W := by
    intro p hp
    rcases hp with ⟨i, hi⟩
    have h : p ∈ horizontalSlab (-1) 1 := by
      simpa [W, slabRestriction] using hi.2
    exact h

  have h_thick' : W.union ⊆ Metric.cthickening rho Y.union := by
    have h1 : W.union ⊆ Z.union := by
      intro p hp
      rcases hp with ⟨i, hi⟩
      exact ⟨i, h_sub i hi⟩
    exact h1.trans hthick

  by_cases hYempty : Y.union = ∅
  · have h_cthick_empty : Metric.cthickening rho Y.union = ∅ := by
      rw [hYempty]
      ext x
      simp only [Metric.mem_cthickening_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      have h_top : Metric.infEDist x (∅ : Set Point3) = ⊤ := by
        rw [Metric.infEDist_eq_top_iff] <;> rfl
      rw [h_top] at h <;> simpa [hrho] using h
    have hZempty : Z.union = ∅ := by
      rw [h_cthick_empty] at hthick <;> simpa using hthick
    have hZcar_empty : ∀ i, Z.carrier i = ∅ := by
      intro i
      have h : Z.carrier i ⊆ Z.union := fun p hp => ⟨i, hp⟩
      rw [hZempty] at h <;> simpa using h
    have h_mass : Z.mass = 0 := by
      simp [Kakeya.Streamlined.Shading.mass, hZcar_empty]
    have hW_mass : W.mass = 0 := by
      have h : W.mass ≤ Z.mass := by
        exact Finset.sum_le_sum fun i _ => MeasureTheory.measure_mono (h_sub i)
      rw [h_mass] at h <;> simpa using h
    have h_density0 : lambda * lifted.toBodyFamily.mass = 0 := by
      have h : lambda * lifted.toBodyFamily.mass ≤ L * Z.mass := h_density
      rw [h_mass] at h <;> simpa using h
    have h_goal : ((2 * L)⁻¹ * lambda) * lifted.toBodyFamily.mass ≤ W.mass := by
      have h9 : ((2 * L)⁻¹ * lambda) * lifted.toBodyFamily.mass =
          (2 * L)⁻¹ * (lambda * lifted.toBodyFamily.mass) := by ring
      rw [h9, h_density0, hW_mass] <;> simp
    exact ⟨h_sub, h_window, h_goal, h_thick'⟩

  · have hYne : Y.union.Nonempty := Set.nonempty_iff_ne_empty.mpr hYempty

    have h_coord : ∀ (p y : Point3), |p (2 : Fin 3) - y (2 : Fin 3)| ≤ dist p y := by
      intro p y
      have h : ‖(p - y) (2 : Fin 3)‖ ≤ ‖p - y‖ := PiLp.norm_apply_le (p - y) 2
      simpa [dist_eq_norm] using h

    have h_geom : ∀ (i : Fin lifted.card),
        Z.carrier i \ horizontalSlab (-1) 1 ⊆
          ((lifted.tube i).carrier ∩ horizontalSlab (-1 - rho) (-1)) ∪
          ((lifted.tube i).carrier ∩ horizontalSlab 1 (1 + rho)) := by
      intro i p hp
      have hpin : p ∈ Z.carrier i := hp.1
      have hnot : p ∉ horizontalSlab (-1) 1 := hp.2
      have hbody : p ∈ (lifted.tube i).carrier := Z.subset_body i hpin
      have hzin : p ∈ Z.union := ⟨i, hpin⟩
      have hct : p ∈ Metric.cthickening rho Y.union := hthick hzin
      have h_infEDist : Metric.infEDist p Y.union ≤ ENNReal.ofReal rho := by
        rw [Metric.mem_cthickening_iff] at hct <;> exact hct
      have h_ne_top : Metric.infEDist p Y.union ≠ ⊤ := Metric.infEDist_ne_top hYne
      have h_eq : Metric.infEDist p Y.union = ENNReal.ofReal (Metric.infDist p Y.union) := by
        have h : Metric.infDist p Y.union = (Metric.infEDist p Y.union).toReal := by rfl
        rw [h]
        exact (ENNReal.ofReal_toReal h_ne_top).symm
      have h_infDist : Metric.infDist p Y.union ≤ rho := by
        rw [h_eq] at h_infEDist
        exact ENNReal.ofReal_le_ofReal_iff (by linarith) |>.mp h_infEDist

      have h_lower : p (2 : Fin 3) ≥ -1 - rho := by
        by_contra h
        have h' : p (2 : Fin 3) < -1 - rho := by linarith
        have h_ge : ∀ y ∈ Y.union, dist p y ≥ -1 - p (2 : Fin 3) := by
          intro y hy
          have hyslab : y ∈ horizontalSlab (-1) 1 := hY hy
          have h0 : -1 ≤ y (2 : Fin 3) := hyslab.1
          have h1 : |p (2 : Fin 3) - y (2 : Fin 3)| ≥ y (2 : Fin 3) - p (2 : Fin 3) := by
            have h2 : y (2 : Fin 3) - p (2 : Fin 3) ≤ |y (2 : Fin 3) - p (2 : Fin 3)| := le_abs_self _
            have h3 : |y (2 : Fin 3) - p (2 : Fin 3)| = |p (2 : Fin 3) - y (2 : Fin 3)| := by
              rw [show y (2 : Fin 3) - p (2 : Fin 3) = -(p (2 : Fin 3) - y (2 : Fin 3)) by ring]
              rw [abs_neg]
            rw [h3] at h2 <;> exact h2
          have h4 : dist p y ≥ |p (2 : Fin 3) - y (2 : Fin 3)| := h_coord p y
          linarith
        have h_inf_ge : Metric.infDist p Y.union ≥ -1 - p (2 : Fin 3) :=
          (Metric.le_infDist hYne).mpr h_ge
        linarith

      have h_upper : p (2 : Fin 3) ≤ 1 + rho := by
        by_contra h
        have h' : p (2 : Fin 3) > 1 + rho := by linarith
        have h_ge : ∀ y ∈ Y.union, dist p y ≥ p (2 : Fin 3) - 1 := by
          intro y hy
          have hyslab : y ∈ horizontalSlab (-1) 1 := hY hy
          have h1 : y (2 : Fin 3) ≤ 1 := hyslab.2
          have h2 : |p (2 : Fin 3) - y (2 : Fin 3)| ≥ p (2 : Fin 3) - y (2 : Fin 3) := le_abs_self _
          have h4 : dist p y ≥ |p (2 : Fin 3) - y (2 : Fin 3)| := h_coord p y
          linarith
        have h_inf_ge : Metric.infDist p Y.union ≥ p (2 : Fin 3) - 1 :=
          (Metric.le_infDist hYne).mpr h_ge
        linarith

      have h_cases : p (2 : Fin 3) < -1 ∨ p (2 : Fin 3) > 1 := by
        have h9 : p (2 : Fin 3) ∉ Set.Icc (-1 : ℝ) 1 := hnot
        have h10 : ¬(-1 ≤ p (2 : Fin 3) ∧ p (2 : Fin 3) ≤ 1) := by
          simpa [Set.mem_Icc] using h9
        by_cases h11 : p (2 : Fin 3) < -1
        · exact Or.inl h11
        · have h12 : -1 ≤ p (2 : Fin 3) := by linarith
          have h13 : p (2 : Fin 3) > 1 := by
            by_contra h14
            have h15 : p (2 : Fin 3) ≤ 1 := by linarith
            exact h10 ⟨h12, h15⟩
          exact Or.inr h13
      rcases h_cases with (h_lt | h_gt)
      · exact Or.inl ⟨hbody, ⟨by linarith, by linarith⟩⟩
      · exact Or.inr ⟨hbody, ⟨by linarith, h_upper⟩⟩

    have h_slab_bound : ∀ (i : Fin lifted.card) (a b : ℝ), b - a = rho →
        MeasureTheory.volume ((lifted.tube i).carrier ∩ horizontalSlab a b) ≤
          ENNReal.ofReal (100 * rho ^ 3) := by
      intro i a b hwidth
      have hab : a < b := by linarith
      have h1 := tube_slab_volume_upper_general hrho hab (hvert i)
      have h_formula : Real.pi * rho^2 * (2 * (b - a) + 6 * rho) = 8 * Real.pi * rho^3 := by
        rw [hwidth] <;> ring
      rw [h_formula] at h1
      have hpi : Real.pi ≤ 4 := Real.pi_le_four
      have h3 : 8 * Real.pi * rho^3 ≤ 100 * rho^3 := by
        have h4 : 0 ≤ rho^3 := by positivity
        nlinarith [Real.pi_nonneg]
      exact h1.trans (ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr h3)

    have h_per_tube : ∀ (i : Fin lifted.card),
        MeasureTheory.volume (Z.carrier i) ≤
          MeasureTheory.volume (W.carrier i) + ENNReal.ofReal (200 * rho ^ 3) := by
      intro i
      have hWcar : W.carrier i = Z.carrier i ∩ horizontalSlab (-1) 1 := by rfl
      let A := Z.carrier i ∩ horizontalSlab (-1) 1
      let B := Z.carrier i \ horizontalSlab (-1) 1
      have h_decomp : A ∪ B = Z.carrier i := by
        ext x
        by_cases h : x ∈ horizontalSlab (-1) 1 <;>
          simp [A, B, h, Set.mem_sdiff] <;> tauto
      have h_vol : MeasureTheory.volume (Z.carrier i) ≤
          MeasureTheory.volume A + MeasureTheory.volume B := by
        rw [←h_decomp]
        exact MeasureTheory.measure_union_le A B
      let S1 := (lifted.tube i).carrier ∩ horizontalSlab (-1 - rho) (-1)
      let S2 := (lifted.tube i).carrier ∩ horizontalSlab 1 (1 + rho)
      have hB_sub : B ⊆ S1 ∪ S2 := h_geom i
      have hB_vol : MeasureTheory.volume B ≤ ENNReal.ofReal (200 * rho ^ 3) := by
        calc
          MeasureTheory.volume B
              ≤ MeasureTheory.volume (S1 ∪ S2) := MeasureTheory.measure_mono hB_sub
          _ ≤ MeasureTheory.volume S1 + MeasureTheory.volume S2 := MeasureTheory.measure_union_le S1 S2
          _ ≤ ENNReal.ofReal (100 * rho ^ 3) + ENNReal.ofReal (100 * rho ^ 3) := by
              exact add_le_add
                (h_slab_bound i (-1 - rho) (-1) (by ring))
                (h_slab_bound i 1 (1 + rho) (by ring))
          _ = ENNReal.ofReal (200 * rho ^ 3) := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)] <;> ring_nf
      calc
        MeasureTheory.volume (Z.carrier i)
            ≤ MeasureTheory.volume A + MeasureTheory.volume B := h_vol
        _ = MeasureTheory.volume (W.carrier i) + MeasureTheory.volume B := by rw [hWcar]
        _ ≤ MeasureTheory.volume (W.carrier i) + ENNReal.ofReal (200 * rho ^ 3) := by
            exact add_le_add_right hB_vol _

    have h_sum_const : ∑ i : Fin lifted.card, ENNReal.ofReal (200 * rho ^ 3) =
        lifted.enncard * ENNReal.ofReal (200 * rho ^ 3) := by
      have h1 : ∑ i : Fin lifted.card, ENNReal.ofReal (200 * rho ^ 3) =
          (Finset.card (Finset.univ : Finset (Fin lifted.card))) * ENNReal.ofReal (200 * rho ^ 3) := by
        rw [Finset.sum_const] <;> ring
      rw [h1]
      have h2 : Finset.card (Finset.univ : Finset (Fin lifted.card)) = lifted.card := by simp
      rw [h2] <;> rfl

    have h_mass_clip :
        Z.mass ≤ W.mass + lifted.enncard * ENNReal.ofReal (200 * rho ^ 3) := by
      calc
        Z.mass = ∑ i : Fin lifted.card, MeasureTheory.volume (Z.carrier i) := rfl
        _ ≤ ∑ i : Fin lifted.card, (MeasureTheory.volume (W.carrier i) + ENNReal.ofReal (200 * rho ^ 3)) :=
            Finset.sum_le_sum fun i _ => h_per_tube i
        _ = (∑ i : Fin lifted.card, MeasureTheory.volume (W.carrier i)) +
              ∑ i : Fin lifted.card, ENNReal.ofReal (200 * rho ^ 3) := by
            rw [Finset.sum_add_distrib]
        _ = W.mass + lifted.enncard * ENNReal.ofReal (200 * rho ^ 3) := by
            rw [h_sum_const] <;> rfl

    set A : ENNReal := lifted.enncard * ENNReal.ofReal (200 * rho ^ 3) with hA_def

    have hA_ne_top : A ≠ ⊤ := by
      rw [hA_def]
      apply ENNReal.mul_ne_top
      · exact ENNReal.natCast_ne_top _
      · exact ENNReal.ofReal_ne_top

    have h_vol_lower : ENNReal.ofReal (rho ^ 2) ≤ Kakeya.deltaTubeVolume rho :=
      canonical_volume_lower hrho

    have h_mass_eq :
        lifted.toBodyFamily.mass = lifted.enncard * Kakeya.deltaTubeVolume rho :=
      tubeFamily_mass_eq_nominal lifted

    have h1 : lifted.enncard * ENNReal.ofReal (rho ^ 2) ≤ lifted.toBodyFamily.mass := by
      rw [h_mass_eq]
      exact mul_le_mul_of_nonneg_left h_vol_lower (by positivity)

    have h2 : ENNReal.ofReal (400 * rho) * ENNReal.ofReal (rho ^ 2) =
        ENNReal.ofReal (400 * rho ^ 3) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> ring_nf

    have h3 : ENNReal.ofReal (400 * rho) * lifted.toBodyFamily.mass ≤ Z.mass := by
      have h31 : (ENNReal.ofReal (400 * rho) * L) * lifted.toBodyFamily.mass ≤
          lambda * lifted.toBodyFamily.mass :=
        mul_le_mul_of_nonneg_right h_budget (by positivity)
      have h32 : (ENNReal.ofReal (400 * rho) * L) * lifted.toBodyFamily.mass =
          L * (ENNReal.ofReal (400 * rho) * lifted.toBodyFamily.mass) := by ring
      rw [h32] at h31
      have h33 : L * (ENNReal.ofReal (400 * rho) * lifted.toBodyFamily.mass) ≤ L * Z.mass :=
        h31.trans h_density
      have h_iff : L * (ENNReal.ofReal (400 * rho) * lifted.toBodyFamily.mass) ≤ L * Z.mass ↔
          ENNReal.ofReal (400 * rho) * lifted.toBodyFamily.mass ≤ Z.mass :=
        ENNReal.mul_le_mul_iff_right hL_zero hL_top
      exact h_iff.mp h33

    have h41 : ENNReal.ofReal (400 * rho) * (lifted.enncard * ENNReal.ofReal (rho ^ 2)) ≤
        ENNReal.ofReal (400 * rho) * lifted.toBodyFamily.mass := by
      exact mul_le_mul_of_nonneg_left h1 (by positivity)

    have h42 : ENNReal.ofReal (400 * rho) * (lifted.enncard * ENNReal.ofReal (rho ^ 2)) =
        lifted.enncard * ENNReal.ofReal (400 * rho ^ 3) := by
      calc
        ENNReal.ofReal (400 * rho) * (lifted.enncard * ENNReal.ofReal (rho ^ 2))
          = lifted.enncard * (ENNReal.ofReal (400 * rho) * ENNReal.ofReal (rho ^ 2)) := by ring
        _ = lifted.enncard * ENNReal.ofReal (400 * rho ^ 3) := by rw [h2]

    have h43 : lifted.enncard * ENNReal.ofReal (400 * rho ^ 3) ≤ Z.mass := by
      rw [←h42]
      exact h41.trans h3

    have h44 : ENNReal.ofReal (400 * rho ^ 3) = 2 * ENNReal.ofReal (200 * rho ^ 3) := by
      have hpos : 0 ≤ 200 * rho ^ 3 := by positivity
      calc
        ENNReal.ofReal (400 * rho ^ 3)
          = ENNReal.ofReal (2 * (200 * rho ^ 3)) := by ring_nf
        _ = 2 * ENNReal.ofReal (200 * rho ^ 3) := by
          rw [ENNReal.ofReal_mul (by positivity)] <;> norm_num

    have h4 : 2 * A ≤ Z.mass := by
      calc
        2 * A
          = 2 * (lifted.enncard * ENNReal.ofReal (200 * rho ^ 3)) := by rw [hA_def]
        _ = lifted.enncard * (2 * ENNReal.ofReal (200 * rho ^ 3)) := by ring
        _ = lifted.enncard * ENNReal.ofReal (400 * rho ^ 3) := by rw [h44]
        _ ≤ Z.mass := h43

    have h51 : A + A ≤ W.mass + A := by
      have h : 2 * A = A + A := by ring
      rw [h] at h4
      exact h4.trans h_mass_clip

    have h5 : A ≤ W.mass := by
      have h_iff : A + A ≤ W.mass + A ↔ A ≤ W.mass :=
        ENNReal.add_le_add_iff_right hA_ne_top
      exact h_iff.mp h51

    have h6 : Z.mass ≤ 2 * W.mass := by
      calc
        Z.mass ≤ W.mass + A := h_mass_clip
        _ ≤ W.mass + W.mass := by gcongr
        _ = 2 * W.mass := by ring

    have h7 : lambda * lifted.toBodyFamily.mass ≤ (2 * L) * W.mass := by
      calc
        lambda * lifted.toBodyFamily.mass ≤ L * Z.mass := h_density
        _ ≤ L * (2 * W.mass) := by gcongr
        _ = (2 * L) * W.mass := by ring

    have h2L_ne_zero : (2 * L) ≠ 0 := by
      simpa [mul_eq_zero] using hL_zero
    have h2L_ne_top : (2 * L) ≠ ⊤ := by
      simpa [ENNReal.mul_eq_top] using hL_top

    have h8 : ((2 * L)⁻¹ * lambda) * lifted.toBodyFamily.mass ≤ W.mass := by
      have h_iff : ((2 * L)⁻¹ * lambda) * lifted.toBodyFamily.mass ≤ W.mass ↔
          lambda * lifted.toBodyFamily.mass ≤ (2 * L) * W.mass := by
        calc
          ((2 * L)⁻¹ * lambda) * lifted.toBodyFamily.mass ≤ W.mass
              ↔ (2 * L)⁻¹ * (lambda * lifted.toBodyFamily.mass) ≤ W.mass := by rw [mul_assoc]
          _ ↔ lambda * lifted.toBodyFamily.mass ≤ (2 * L) * W.mass :=
            ENNReal.inv_mul_le_iff h2L_ne_zero h2L_ne_top
      exact h_iff.mpr h7

    exact ⟨h_sub, h_window, h8, h_thick'⟩

end Kakeya.Assouad
