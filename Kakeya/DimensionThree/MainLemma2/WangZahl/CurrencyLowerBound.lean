/-
The elementary *lower* size bound on the Wang--Zahl currency
`X = (#T) |T|^{1/2}`, i.e. Obligation 1 of
`Kakeya.DimensionThree.MainLemma2.WangZahl.SourcePropositions`.

Source: `blueprint/src/WZ2/250224e_K3.tex`, the observation recorded
immediately after Definition `defnCDE` (Section 1.3): a slab of thickness
`|T|^{1/2}` containing one tube of the family forces `FS(T) (#T) |T|^{1/2} >= 1`,
so with the Frostman hypothesis `FS(T) <= delta^{-eta}` one gets
`X >= C⁻¹ delta^{eta}`.

The two geometric pieces are `exists_slabTestSet_containing` and
`volume_slabTestSet_le`, both in
`Kakeya.DimensionThree.MainLemma2.WangZahl.SlabGeometry`.
-/
module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.SigmaCalculus
public import Kakeya.DimensionThree.MainLemma2.WangZahl.SlabGeometry

@[expose] public section

open MeasureTheory Metric EuclideanGeometry Module

namespace Kakeya.WangZahl

noncomputable section

universe u

/-! ### Two elementary auxiliaries -/

theorem inv_le_of_one_le_mul' {a C : ENNReal} (h : 1 ≤ C * a) : a⁻¹ ≤ C := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp only [mul_zero, nonpos_iff_eq_zero] at h
    exact one_ne_zero h
  have hC0 : C ≠ 0 := by
    rintro rfl
    simp only [zero_mul, nonpos_iff_eq_zero] at h
    exact one_ne_zero h
  rw [ENNReal.inv_le_iff_le_mul (fun _ => ha0) (fun _ => hC0)]
  rwa [mul_comm]

/-! ### The Frostman step -/

/-- One tube of the family inside a slab `W` forces `1 <= FS(T) |W| (#T)`. -/
theorem inv_le_frostmanSlabWolffConstant {δ : NNReal} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) (W : SlabTestSet)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hsub : (T i₀).carrier ⊆ W.carrier) :
    (volume W.carrier * (s.card : ENNReal))⁻¹ ≤ frostmanSlabWolffConstant s T := by
  rw [frostmanSlabWolffConstant]
  refine le_sInf ?_
  rintro C ⟨-, hC⟩
  have h := hC W
  have h1 : (1 : ENNReal) ≤
      ((@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s).card : ENNReal) := by
    have hmem : i₀ ∈ (@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s) := by
      simp only [Finset.mem_filter]
      exact ⟨hi₀, hsub⟩
    have hpos : 0 < (@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s).card := Finset.card_pos.mpr ⟨i₀, hmem⟩
    exact_mod_cast hpos
  have h2 : (1 : ENNReal) ≤ C * (volume W.carrier * (s.card : ENNReal)) := by
    rw [← mul_assoc]
    exact h1.trans h
  exact inv_le_of_one_le_mul' h2

/-! ### Obligation 1 -/

/-- The lower currency bound of Section 1.3 of the source. -/
theorem exists_currencyLowerBound_aux :
    ∃ C : NNReal, 1 ≤ C ∧ CurrencyLowerBound.{u} C := by
  have hc0 : (0 : NNReal) < Tube.le_volume.c 3 := Tube.le_volume.c_pos 3
  set cs : ENNReal := ((Tube.le_volume.c 3 : NNReal) : ENNReal) ^ (1 / 2 : ℝ) with hcs
  have hcs0 : cs ≠ 0 := by
    rw [hcs]; exact (ENNReal.rpow_pos (by exact_mod_cast hc0) ENNReal.coe_ne_top).ne'
  have hcstop : cs ≠ ⊤ := by
    rw [hcs]
    exact ENNReal.rpow_ne_top_of_ne_zero (by exact_mod_cast hc0.ne') ENNReal.coe_ne_top
  set B : ENNReal := volume (closedBall (0 : Space3) 2) with hB
  have hB0 : B ≠ 0 := (measure_closedBall_pos volume (0 : Space3) (by norm_num)).ne'
  have hBtop : B ≠ ⊤ := measure_closedBall_lt_top.ne
  set K : ENNReal := cs⁻¹ * B with hK
  have hKtop : K ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hcs0) hBtop
  refine ⟨max 1 K.toNNReal, le_max_left _ _, ?_⟩
  have hKle : K ≤ ((max 1 K.toNNReal : NNReal) : ENNReal) := by
    have h : (K.toNNReal : ENNReal) = K := ENNReal.coe_toNNReal hKtop
    rw [← h]
    exact_mod_cast le_max_right (1 : NNReal) K.toNNReal
  have hCinv : ((max 1 K.toNNReal : NNReal) : ENNReal)⁻¹ ≤ cs * B⁻¹ := by
    refine (ENNReal.inv_le_inv.mpr hKle).trans (le_of_eq ?_)
    rw [hK, ENNReal.mul_inv (Or.inr hBtop) (Or.inr hB0), inv_inv]
  intro δ hδ hδ1 η hη ι s T hs hfamily _hm hell
  obtain ⟨i₀, hi₀⟩ := hs
  obtain ⟨W, hWt, hWsub⟩ := exists_slabTestSet_containing (T i₀) (hfamily.1 i₀ hi₀)
  have hstep : (δ : ENNReal) ^ η ≤ volume W.carrier * (s.card : ENNReal) := by
    have h := (inv_le_frostmanSlabWolffConstant s T W hi₀ hWsub).trans hell
    have h2 := ENNReal.inv_le_inv.mpr h
    rwa [inv_inv, ENNReal.rpow_neg, inv_inv] at h2
  have hWvol : volume W.carrier ≤ (δ : ENNReal) * B := by
    have h := volume_slabTestSet_le W
    rwa [hWt] at h
  have hstep2 : (δ : ENNReal) ^ η ≤ B * ((δ : ENNReal) * (s.card : ENNReal)) := by
    refine hstep.trans ?_
    calc volume W.carrier * (s.card : ENNReal)
        ≤ ((δ : ENNReal) * B) * (s.card : ENNReal) := by gcongr
      _ = B * ((δ : ENNReal) * (s.card : ENNReal)) := by ring
  have hstep3 : B⁻¹ * (δ : ENNReal) ^ η ≤ (δ : ENNReal) * (s.card : ENNReal) := by
    calc B⁻¹ * (δ : ENNReal) ^ η ≤ B⁻¹ * (B * ((δ : ENNReal) * (s.card : ENNReal))) := by
          gcongr
      _ = (B⁻¹ * B) * ((δ : ENNReal) * (s.card : ENNReal)) := by ring
      _ = (δ : ENNReal) * (s.card : ENNReal) := by
          rw [ENNReal.inv_mul_cancel hB0 hBtop, one_mul]
  calc ((max 1 K.toNNReal : NNReal) : ENNReal)⁻¹ * (δ : ENNReal) ^ η
      ≤ (cs * B⁻¹) * (δ : ENNReal) ^ η := by gcongr
    _ = cs * (B⁻¹ * (δ : ENNReal) ^ η) := by ring
    _ ≤ cs * ((δ : ENNReal) * (s.card : ENNReal)) := by gcongr
    _ = (cs * (δ : ENNReal)) * (s.card : ENNReal) := by ring
    _ ≤ (tubeVolume δ) ^ (1 / 2 : ℝ) * (s.card : ENNReal) := by
        gcongr
        exact sqrt_tubeVolume_ge
    _ = wzCurrency δ s.card := by rw [wzCurrency]; ring

end

end Kakeya.WangZahl
