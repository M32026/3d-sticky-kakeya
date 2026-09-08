import MyLeanRepo.Kakeya.Streamlined.Basic
import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.Estimates
import MyLeanRepo.Kakeya.Streamlined.DividingScales.FrostmanInequalities
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.ThickenedParent
import Mathlib.Tactic

/-!
# Frostman constant preservation under thickening and subfamily restriction

## Subfamily Frostman bound

For a subfamily `S` of `G` with all bodies in `U`,
`C_F(S,U) ≤ (G.mass / S.mass) * C_F(G,U)`.

## Thickening preserves Frostman

If `G_i` is a thickening of `P_i` with `P_i ⊆ G_i` and `vol(G_i) ≤ C_vol * vol(P_i)`,
then `C_F(G,U) ≤ C_vol * C_F(P,U)`.
-/

noncomputable section

open MeasureTheory Metric Set Finset Classical

namespace Kakeya.Streamlined

/-- Subfamily Frostman upper bound: if `S` is a subfamily of `G` and all bodies
of both are contained in `U`, then
`C_F(S,U) ≤ (G.mass / S.mass) * C_F(G,U)`. -/
lemma subfamily_frostman_upper_bound
    {G S : BodyFamily} {embed : Fin S.card → Fin G.card}
    (hinj : Function.Injective embed)
    (hcarrier : ∀ i, (S.body i).carrier = (G.body (embed i)).carrier)
    {U : Set Point3}
    (hG_in_U : ∀ i, (G.body i).carrier ⊆ U)
    (hGU_zero : G.density U ≠ 0)
    (hGU_top : G.density U ≠ ⊤)
    (hSU_zero : S.density U ≠ 0)
    (hSU_top : S.density U ≠ ⊤)
    (hS_mass_pos : S.mass ≠ 0)
    (hS_mass_top : S.mass ≠ ⊤)
    (hG_mass_pos : G.mass ≠ 0)
    (hG_mass_top : G.mass ≠ ⊤) :
    S.frostmanConstantIn U ≤ (G.mass / S.mass) * G.frostmanConstantIn U := by
  let m : ENNReal := S.mass / G.mass
  have hm_zero : m ≠ 0 := by
    simp [m, hS_mass_pos] <;> tauto
  have hm_top : m ≠ ⊤ :=
    ENNReal.div_ne_top hS_mass_top hG_mass_pos
  have hG_mass_U : G.containedMass U = G.mass := by
    have h : G.containedIndices U = Finset.univ := by
      ext i; simp [BodyFamily.mem_containedIndices_iff, hG_in_U]
    rw [BodyFamily.containedMass, h] <;> rfl
  have hS_mass_U : S.containedMass U = S.mass := by
    have h : S.containedIndices U = Finset.univ := by
      ext i
      simp [BodyFamily.mem_containedIndices_iff, hcarrier, hG_in_U]
      <;> tauto
    rw [BodyFamily.containedMass, h] <;> rfl
  have hmass : m * G.containedMass U ≤ S.containedMass U := by
    rw [hG_mass_U, hS_mass_U]
    dsimp only [m]
    have h : (S.mass / G.mass) * G.mass = S.mass :=
      ENNReal.div_mul_cancel hG_mass_pos hG_mass_top
    rw [h]
  have h_main : S.frostmanConstantIn U ≤ G.frostmanConstantIn U / m :=
    BodyFamily.subfamily_frostmanConstantIn_le_div
      hinj hcarrier hm_zero hm_top hGU_zero hGU_top hSU_zero hSU_top hmass
  have h2 : G.frostmanConstantIn U / m = (G.mass / S.mass) * G.frostmanConstantIn U := by
    dsimp only [m]
    have h3 : (S.mass / G.mass)⁻¹ = G.mass / S.mass :=
      ENNReal.inv_div (Or.inl hG_mass_top) (Or.inl hG_mass_pos)
    rw [div_eq_mul_inv, h3] <;> ring
  rw [h2] at h_main
  exact h_main

/-- Thickening preserves Frostman constant up to a volume-ratio constant.

If each thickened body has volume at most `C_vol` times the original volume,
then `C_F(F.thicken r, U) ≤ C_vol * C_F(F, U)`. -/
lemma thickening_preserves_frostman
    (F : BodyFamily) (r : ℝ) {U : Set Point3} {C_vol : ENNReal}
    (hC_vol_top : C_vol ≠ ⊤)
    (h_sub : ∀ i, (F.body i).carrier ⊆ ((F.thicken r).body i).carrier)
    (h_vol : ∀ i, ((F.thicken r).body i).volume ≤ C_vol * (F.body i).volume)
    (hG_in_U : ∀ i, ((F.thicken r).body i).carrier ⊆ U)
    (hF_density_zero : F.density U ≠ 0)
    (hF_density_top : F.density U ≠ ⊤)
    (hG_density_zero : (F.thicken r).density U ≠ 0)
    (hG_density_top : (F.thicken r).density U ≠ ⊤) :
    (F.thicken r).frostmanConstantIn U ≤ C_vol * F.frostmanConstantIn U := by
  let G := F.thicken r
  have hF_in_U : ∀ i, (F.body i).carrier ⊆ U := by
    intro i
    exact subset_trans (h_sub i) (hG_in_U i)
  have h_mass_ge : G.mass ≥ F.mass := by
    dsimp only [BodyFamily.mass]
    apply Finset.sum_le_sum
    intro i _
    exact measure_mono (h_sub i)
  have hF_mass_U : F.containedMass U = F.mass := by
    have h : F.containedIndices U = Finset.univ := by
      ext i; simp [BodyFamily.mem_containedIndices_iff, hF_in_U]
    rw [BodyFamily.containedMass, h] <;> rfl
  have hG_mass_U : G.containedMass U = G.mass := by
    have h : G.containedIndices U = Finset.univ := by
      ext i
      have h_i : (G.body i).carrier ⊆ U := by
        exact hG_in_U i
      simp [BodyFamily.mem_containedIndices_iff, h_i]
    rw [BodyFamily.containedMass, h] <;> rfl
  have h_contained_ge : F.containedMass U ≤ G.containedMass U := by
    rw [hF_mass_U, hG_mass_U]
    exact h_mass_ge
  have h_density_ge : F.density U ≤ G.density U := by
    dsimp only [BodyFamily.density]
    exact ENNReal.div_le_div h_contained_ge le_rfl
  apply G.frostmanConstantIn_le_of_density_le_mul
    hG_density_zero hG_density_top
  intro K hK_conv hK_sub
  have h1 : G.containedMass K ≤ C_vol * F.containedMass K := by
    dsimp only [BodyFamily.containedMass]
    have h2 : ∀ i ∈ G.containedIndices K, (F.body i).carrier ⊆ K := by
      intro i hi
      have h3 : (G.body i).carrier ⊆ K :=
        BodyFamily.mem_containedIndices_iff.mp hi
      exact subset_trans (h_sub i) h3
    have h4 : G.containedIndices K ⊆ F.containedIndices K := by
      intro i hi
      exact BodyFamily.mem_containedIndices_iff.mpr (h2 i hi)
    have h5 : ∑ i ∈ G.containedIndices K, (G.body i).volume ≤
        ∑ i ∈ G.containedIndices K, C_vol * (F.body i).volume :=
      Finset.sum_le_sum (fun i _ => h_vol i)
    have h6 : ∑ i ∈ G.containedIndices K, C_vol * (F.body i).volume =
        C_vol * ∑ i ∈ G.containedIndices K, (F.body i).volume := by
      rw [Finset.mul_sum]
    have h7 : ∑ i ∈ G.containedIndices K, (F.body i).volume ≤
        ∑ i ∈ F.containedIndices K, (F.body i).volume :=
      Finset.sum_le_sum_of_subset_of_nonneg h4 (fun _ _ _ => bot_le)
    calc
      ∑ i ∈ G.containedIndices K, (G.body i).volume
        ≤ ∑ i ∈ G.containedIndices K, C_vol * (F.body i).volume := h5
      _ = C_vol * ∑ i ∈ G.containedIndices K, (F.body i).volume := h6
      _ ≤ C_vol * ∑ i ∈ F.containedIndices K, (F.body i).volume := by gcongr
  have h3 : G.density K ≤ C_vol * F.density K := by
    dsimp only [BodyFamily.density]
    have hvol : (MeasureTheory.volume K : ENNReal) = (MeasureTheory.volume K : ENNReal) := rfl
    have h : G.containedMass K / (MeasureTheory.volume K : ENNReal) ≤
        (C_vol * F.containedMass K) / (MeasureTheory.volume K : ENNReal) :=
      ENNReal.div_le_div h1 le_rfl
    have h2 : (C_vol * F.containedMass K) / (MeasureTheory.volume K : ENNReal) =
        C_vol * (F.containedMass K / (MeasureTheory.volume K : ENNReal)) := by
      simp [div_eq_mul_inv, mul_assoc]
      <;> ring
    rw [h2] at h
    exact h
  have h4 : F.density K ≤ F.frostmanConstantIn U * F.density U :=
    F.density_le_mul_of_frostmanConstantIn_le
      hF_density_zero hF_density_top le_rfl hK_conv hK_sub
  calc G.density K
    ≤ C_vol * F.density K := h3
  _ ≤ C_vol * (F.frostmanConstantIn U * F.density U) := by gcongr
  _ ≤ C_vol * (F.frostmanConstantIn U * G.density U) := by gcongr
  _ = (C_vol * F.frostmanConstantIn U) * G.density U := by ring

end Kakeya.Streamlined
