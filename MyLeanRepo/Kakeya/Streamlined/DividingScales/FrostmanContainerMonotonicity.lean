import MyLeanRepo.Kakeya.Streamlined.DividingScales.FrostmanInequalities

/-!
# Frostman monotonicity between full-family containers

When every body lies in both containers, enlarging the container volume can
only increase the reference denominator and therefore cannot decrease the
relative Frostman constant.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

namespace BodyFamily

/--
If all bodies lie in both convex containers and `volume U ≤ volume V`, then
the Frostman constant relative to `U` is at most the one relative to `V`.
-/
lemma frostmanConstantIn_mono_of_all_contained
    (F : BodyFamily) {U V : Set Point3}
    (hU_conv : Convex ℝ U) (hV_conv : Convex ℝ V)
    (h_all_U : ∀ i, (F.body i).carrier ⊆ U)
    (h_all_V : ∀ i, (F.body i).carrier ⊆ V)
    (h_vol : volume U ≤ volume V)
    (hU_zero : volume U ≠ 0) (hU_top : volume U ≠ ⊤)
    (hV_zero : volume V ≠ 0) (hV_top : volume V ≠ ⊤)
    (hMass_zero : F.mass ≠ 0) (hMass_top : F.mass ≠ ⊤) :
    F.frostmanConstantIn U ≤ F.frostmanConstantIn V := by
  have hcmU : F.containedMass U = F.mass := by
    have h : F.containedIndices U = Finset.univ := by
      ext i
      simp [BodyFamily.mem_containedIndices_iff, h_all_U]
    rw [BodyFamily.containedMass, h]
    rfl
  have hcmV : F.containedMass V = F.mass := by
    have h : F.containedIndices V = Finset.univ := by
      ext i
      simp [BodyFamily.mem_containedIndices_iff, h_all_V]
    rw [BodyFamily.containedMass, h]
    rfl
  have h_densU_zero : F.density U ≠ 0 := by
    rw [BodyFamily.density, hcmU]
    exact ENNReal.div_ne_zero.mpr ⟨hMass_zero, hU_top⟩
  have h_densU_top : F.density U ≠ ⊤ := by
    rw [BodyFamily.density, hcmU]
    exact ENNReal.div_ne_top hMass_top hU_zero
  have h_densV_zero : F.density V ≠ 0 := by
    rw [BodyFamily.density, hcmV]
    exact ENNReal.div_ne_zero.mpr ⟨hMass_zero, hV_top⟩
  have h_densV_top : F.density V ≠ ⊤ := by
    rw [BodyFamily.density, hcmV]
    exact ENNReal.div_ne_top hMass_top hV_zero
  have h_densU_ge : F.density V ≤ F.density U := by
    simp only [BodyFamily.density, hcmU, hcmV]
    exact ENNReal.div_le_div le_rfl h_vol
  apply F.frostmanConstantIn_le_of_density_le_mul h_densU_zero h_densU_top
  intro K hK hKU
  let L := K ∩ V
  have hL_conv : Convex ℝ L := hK.inter hV_conv
  have hL_subV : L ⊆ V := Set.inter_subset_right
  have h_indices : F.containedIndices K = F.containedIndices L := by
    ext i
    simp only [BodyFamily.containedIndices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hi x hx
      exact ⟨hi hx, h_all_V i hx⟩
    · intro hi
      exact hi.trans Set.inter_subset_left
  have h_mass : F.containedMass K = F.containedMass L := by
    dsimp only [BodyFamily.containedMass]
    rw [h_indices]
  have h_volL : volume L ≤ volume K :=
    measure_mono Set.inter_subset_left
  have h_densK_le : F.density K ≤ F.density L := by
    dsimp only [BodyFamily.density]
    rw [h_mass]
    exact ENNReal.div_le_div le_rfl h_volL
  have h_main :
      F.density K / F.density U ≤
        F.density L / F.density V := by
    calc
      F.density K / F.density U
        ≤ F.density L / F.density U := by gcongr
      _ ≤ F.density L / F.density V := by gcongr
  have h_bound :
      F.density L / F.density V ≤
        F.frostmanConstantIn V :=
    F.density_div_density_le_frostmanConstantIn hL_conv hL_subV
  have h :
      F.density K / F.density U ≤
        F.frostmanConstantIn V :=
    h_main.trans h_bound
  exact (ENNReal.div_le_iff h_densU_zero h_densU_top).mp h

/-- Compare the Frostman constants of one family in two unrelated convex
containers which both contain every body.  Only the displayed volume loss is
paid; no set-theoretic containment between the two containers is needed. -/
lemma frostmanConstantIn_le_mul_of_all_contained
    (F : BodyFamily) {U V : Set Point3} {q : ENNReal}
    (hU_conv : Convex ℝ U) (hV_conv : Convex ℝ V)
    (h_all_U : ∀ i, (F.body i).carrier ⊆ U)
    (h_all_V : ∀ i, (F.body i).carrier ⊆ V)
    (h_vol : volume V ≤ q * volume U)
    (hU_zero : volume U ≠ 0) (hU_top : volume U ≠ ⊤)
    (hV_zero : volume V ≠ 0) (hV_top : volume V ≠ ⊤)
    (hMass_zero : F.mass ≠ 0) (hMass_top : F.mass ≠ ⊤) :
    F.frostmanConstantIn V ≤ q * F.frostmanConstantIn U := by
  have hMassU : F.containedMass U = F.mass := by
    have h : F.containedIndices U = Finset.univ := by
      ext i
      simp [BodyFamily.mem_containedIndices_iff, h_all_U i]
    rw [BodyFamily.containedMass, h]
    rfl
  have hMassV : F.containedMass V = F.mass := by
    have h : F.containedIndices V = Finset.univ := by
      ext i
      simp [BodyFamily.mem_containedIndices_iff, h_all_V i]
    rw [BodyFamily.containedMass, h]
    rfl
  apply F.frostmanConstantIn_le_of_containedMass_mul_volume_le
    hV_zero hV_top
    (by simpa [hMassV] using hMass_zero)
    (by simpa [hMassV] using hMass_top)
  intro K hK _hKV
  let L := K ∩ U
  have hL_conv : Convex ℝ L := hK.inter hU_conv
  have hL_U : L ⊆ U := Set.inter_subset_right
  have hindices : F.containedIndices K = F.containedIndices L := by
    ext i
    simp only [BodyFamily.containedIndices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hi x hx
      exact ⟨hi hx, h_all_U i hx⟩
    · intro hi
      exact hi.trans Set.inter_subset_left
  have hmass : F.containedMass K = F.containedMass L := by
    dsimp only [BodyFamily.containedMass]
    rw [hindices]
  have hsmall :=
    F.containedMass_mul_volume_le_of_frostmanConstantIn_le
      hU_zero hU_top
      (by simpa [hMassU] using hMass_zero)
      (by simpa [hMassU] using hMass_top)
      le_rfl hL_conv hL_U
  have hL_volume : volume L ≤ volume K :=
    measure_mono Set.inter_subset_left
  rw [hmass]
  calc
    F.containedMass L * volume V
        ≤ F.containedMass L * (q * volume U) := by gcongr
    _ = q * (F.containedMass L * volume U) := by ring
    _ ≤ q * (F.frostmanConstantIn U * F.containedMass U * volume L) := by
      gcongr
    _ ≤ q * (F.frostmanConstantIn U * F.containedMass U * volume K) := by
      gcongr
    _ = (q * F.frostmanConstantIn U) *
        F.containedMass V * volume K := by
      rw [hMassU, hMassV]
      ring

end BodyFamily

end Kakeya.Streamlined
