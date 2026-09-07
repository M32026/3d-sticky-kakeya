import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Hairbrush.RawBTransferLemmas
import MyLeanRepo.Kakeya.Hairbrush.PlaneCovering.Multiplicity
import MyLeanRepo.Kakeya.Hairbrush.PerBinCordoba
import MyLeanRepo.Kakeya.Hairbrush.IntersectionSumBound

/-!
# Asymmetric fixed-stem Córdoba hairbrush

This is (B.25)--(B.27) of the self-contained Appendix-B proof after the stem,
the hairs, and their far-cylinder shading have already been supplied.

Reuse the validated plane covering, per-bin Córdoba estimate, intersection
sum bound, and bounded-overlap summation from `HairbrushOrientedRawB`.  This
target does not select a stem, prove a degree lower bound, run a two-ends
reduction, or absorb the final exponent budget.
-/

noncomputable section

open MeasureTheory Metric Set Finset Real
open scoped Classical

namespace Kakeya.Assouad

theorem hairbrush_asymmetric_fixed_stem_cordoba :
    HairbrushAsymmetricFixedStemCordobaStatement := by
  intro δ sigma farRadius katzTaoConstant
    hδ hδ1000 hsigma hsigma1 hfarRadius hCKT_nonneg
    H Z _hH_nonempty hED hKT stem hAngle hInter hFar density hdensity_ne_top
    h_density_per hV_lower

  set V := Kakeya.deltaTubeVolume δ with hV_def
  set C_KT : ℝ := katzTaoConstant with hCKT_def
  set C : ENNReal := ENNReal.ofReal (2000 * (3 : ℝ) * C_KT * 32 * Real.pi) with hC_def
  set L : ENNReal := ENNReal.ofReal (Real.log (1 / δ)) with hL_def
  set D : ENNReal := 1 + C * L with hD_def
  set M : ENNReal := ENNReal.ofReal (100 * (sigma / farRadius + 1)) with hM_def

  have hδ1 : δ ≤ 1 := by linarith
  have hlog_pos : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    have h : 1 < 1 / δ := by
      apply one_lt_one_div hδ
      linarith
    exact h
  have hV_ne_top : V ≠ ⊤ := by
    have hvol : TubeVolumeScalingStatement := tube_volume_scaling
    have h_fin : 0 < V ∧ V ≠ ⊤ := hvol.2.1 δ hδ hδ1
    exact h_fin.2
  have hD_top : D ≠ ⊤ := by
    rw [hD_def]
    have h1 : (1 : ENNReal) ≠ ⊤ := by simp
    have h2 : C * L ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    exact ENNReal.add_ne_top.mpr ⟨h1, h2⟩

  -- Plane covering
  rcases plane_covering_with_multiplicity hδ hδ1 hsigma hsigma1 stem H
      hAngle hInter farRadius hfarRadius
    with ⟨K, bins, h_bins_sub, h_bins_cover, h_bins_normal, h_bins_mult⟩

  -- Per-bin Córdoba
  have h_cordoba : ∀ (k : Fin K),
      volume (⋃ U ∈ bins k, Z.carrier U) ≥
        density ^ 2 * (bins k).enncard * V / D := by
    intro k
    rcases h_bins_normal k with ⟨n, hn1, hn2⟩
    let G := bins k
    have hG : G ⊆ H := h_bins_sub k
    have hKT_G : Kakeya.KatzTaoConvexWolffBound G C_KT := rawB_KT_subset hKT hG
    have hED_G : G.IsEssentiallyDistinct := rawB_ED_subset hED hG
    have hV_all : ∀ T ∈ G, T.volume ≤ V := by
      intro T _
      have h_eq : T.volume = V := rawB_volume_eq T
      rw [h_eq]
    have h_plane : Kakeya.Hairbrush.LiesInTwoPlaneNeighborhood G n 2 :=
      ⟨hn1, fun U hU => hn2 U hU⟩
    have h_density : density * G.enncard * V ≤
        ∑ T ∈ G, volume (Z.carrier T) := by
      have h_sum : ∑ T ∈ G, density * V =
          density * G.enncard * V := by
        simp [Finset.sum_const, TubeFamily.enncard] <;> ring
      rw [←h_sum]
      apply Finset.sum_le_sum
      intro T hT
      have h_eq : T.volume = V := rawB_volume_eq T
      have h : density * T.volume ≤ volume (Z.carrier T) :=
        h_density_per T (hG hT)
      rw [h_eq] at h
      exact h
    have h_inter_sum : ∀ T ∈ G,
        ∑ U ∈ G.erase T, volume (Z.carrier T ∩ Z.carrier U) ≤
          C * V * L := by
      intro T hT
      let Z_G : Kakeya.Shading G :=
        Kakeya.Hairbrush.restrictShading (Y := Z) G hG
      have h2 := Kakeya.Hairbrush.intersection_sum_bound (Y := Z_G)
        hδ hδ1000 h_plane hKT_G hED_G T hT
        V (by norm_num) hCKT_nonneg hV_all hV_lower
      have h_eq : C * V * L =
          ENNReal.ofReal (2000 * (2 + 1) * C_KT * 32 * Real.pi) * V * L := by
        have h3 : (2000 * (2 + 1) * C_KT * 32 * Real.pi) =
            (2000 * (3 : ℝ) * C_KT * 32 * Real.pi) := by ring
        rw [h3] <;> rfl
      rw [h_eq]
      exact h2
    exact Kakeya.Hairbrush.per_bin_cordoba_bound (F := H) (Y := Z)
      hδ hδ1 G hG density V C
      hV_all hV_ne_top h_density hlog_pos h_inter_sum

  -- Sum over bins
  let A : Fin K → Set Point3 := fun k => ⋃ U ∈ bins k, Z.carrier U
  let union_all : Set Point3 := ⋃ k : Fin K, A k

  have hA_meas : ∀ k : Fin K, MeasurableSet (A k) := by
    intro k
    apply MeasurableSet.biUnion (bins k).finite_toSet.countable
    intro U hU
    exact Z.measurable_carrier (h_bins_sub k hU)

  have h_sum_lower : ∑ k : Fin K, volume (A k) ≥
      density ^ 2 * V / D * H.enncard := by
    have h1 : ∑ k : Fin K, volume (A k) ≥
        ∑ k : Fin K, (density ^ 2 * (bins k).enncard * V / D) :=
      Finset.sum_le_sum fun k _ => h_cordoba k
    have h2 : ∑ k : Fin K, (density ^ 2 * (bins k).enncard * V / D) =
        density ^ 2 * V / D * ∑ k : Fin K, (bins k).enncard := by
      have h21 : ∀ k, density ^ 2 * (bins k).enncard * V / D =
          (density ^ 2 * V / D) * (bins k).enncard := by
        intro k
        simp only [div_eq_mul_inv]
        <;> simp [mul_assoc, mul_comm, mul_left_comm]
      rw [Finset.sum_congr rfl (fun k _ => h21 k), Finset.mul_sum]
    have h3 : H.enncard ≤ ∑ k : Fin K, (bins k).enncard :=
      rawB_bins_sum_card h_bins_sub h_bins_cover
    rw [h2] at h1
    calc
      _ ≥ density ^ 2 * V / D * ∑ k : Fin K, (bins k).enncard := h1
      _ ≥ density ^ 2 * V / D * H.enncard := by gcongr

  -- Multiplicity upper bound
  have h_mult_pointwise : ∀ x,
      (Finset.filter (fun k : Fin K => x ∈ A k) Finset.univ).card ≤ M := by
    intro x
    by_cases hx : x ∈ union_all
    · have h_x_far : farRadius ≤ ‖perpProj stem.direction (x - stem.base)‖ := by
        rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
        rcases Set.mem_iUnion₂.mp hk with ⟨U, hU, hxU⟩
        have hU_H : U ∈ H := h_bins_sub k hU
        have h6 : Z.carrier U ⊆ {x | farRadius ≤ ‖perpProj stem.direction (x - stem.base)‖} :=
          hFar U hU_H
        exact h6 hxU
      have h4 : (Finset.filter (fun k : Fin K => x ∈ A k) Finset.univ).card ≤
          (Finset.filter (fun k : Fin K => ∃ U ∈ bins k, x ∈ U.carrier) Finset.univ).card := by
        apply Finset.card_le_card
        intro k hk
        simp only [Finset.mem_filter] at hk ⊢
        have h5 : x ∈ A k := hk.2
        rcases Set.mem_iUnion₂.mp h5 with ⟨U, hU, hxU⟩
        have hxU' : x ∈ U.carrier := Z.subset_tube (h_bins_sub k hU) hxU
        exact ⟨hk.1, ⟨U, hU, hxU'⟩⟩
      exact le_trans (Nat.cast_le.mpr h4) (h_bins_mult x h_x_far)
    · have h_none : ∀ k : Fin K, x ∉ A k := by
        intro k hk
        have h : x ∈ union_all := Set.mem_iUnion.mpr ⟨k, hk⟩
        exact hx h
      have h_filter_empty : Finset.filter (fun k : Fin K => x ∈ A k) Finset.univ = ∅ := by
        ext k; simp [h_none]
      rw [h_filter_empty]; simp

  have h_sum_upper : ∑ k : Fin K, volume (A k) ≤ M * volume union_all :=
    rawB_multiplicity_sum hA_meas h_mult_pointwise

  -- Combine: volume(union_all) ≥ lower_sum / M
  have h_main_bound : volume union_all ≥
      density ^ 2 * V / D * H.enncard / M := by
    have h : density ^ 2 * V / D * H.enncard ≤
        M * volume union_all := le_trans h_sum_lower h_sum_upper
    have h' : density ^ 2 * V / D * H.enncard ≤ volume union_all * M := by
      rw [mul_comm (M : ENNReal)] at h
      exact h
    exact ENNReal.div_le_of_le_mul h'

  -- union_all = Z.union
  have h_union_eq : union_all = Z.union := by
    ext x
    simp only [union_all, A, Set.mem_iUnion, Set.mem_iUnion₂]
    constructor
    · rintro ⟨k, U, hU, hxU⟩
      have hU_H : U ∈ H := h_bins_sub k hU
      exact ⟨U, hU_H, hxU⟩
    · rintro ⟨U, hU_H, hxU⟩
      rcases h_bins_cover U hU_H with ⟨k, hk⟩
      exact ⟨k, U, hk, hxU⟩

  rw [h_union_eq] at h_main_bound

  have hM_ne_top : M ≠ ⊤ := ENNReal.ofReal_ne_top
  have hM_pos : 0 < M := by
    rw [hM_def]
    apply ENNReal.ofReal_pos.mpr
    positivity
  have hD_pos : 0 < D := by
    rw [hD_def] <;> positivity
  have h_inv : (D * M)⁻¹ = D⁻¹ * M⁻¹ := by
    rw [ENNReal.mul_inv]
    <;> simp [hD_top, hM_ne_top]

  have hD_eq : D = hairbrushFixedStemCordobaDenominator δ katzTaoConstant := by
    simp [hD_def, hC_def, hL_def, hairbrushFixedStemCordobaDenominator]
    <;> rfl

  have h_alg : density ^ 2 * V / D * H.enncard / M =
      density ^ 2 * H.enncard * V / (D * M) := by
    simp only [div_eq_mul_inv]
    rw [h_inv]
    <;> simp [mul_assoc, mul_comm, mul_left_comm]
    <;> ring

  have h_final : density ^ 2 * H.enncard * V /
        (hairbrushFixedStemCordobaDenominator δ katzTaoConstant * M) ≤
      volume Z.union := by
    have h_main2 : density ^ 2 * V / D * H.enncard / M ≤ volume Z.union := h_main_bound
    rw [h_alg] at h_main2
    rw [hD_eq] at h_main2
    exact h_main2
  exact h_final

end Kakeya.Assouad
