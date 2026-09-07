import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Hairbrush.OverlapLemmas
import MyLeanRepo.Kakeya.Hairbrush.CylinderTubeIntersection
import MyLeanRepo.Kakeya.Assouad.Hairbrush.TransverseMultiplicity
import MyLeanRepo.Kakeya.Assouad.Hairbrush.UniformIntersectionBound
import MyLeanRepo.Kakeya.Assouad.Hairbrush.StemAveraging
import MyLeanRepo.Kakeya.Assouad.EssentiallyDistinctCardBound

/-!
# Ambient-stem selection

This is (B.22)--(B.24) of the self-contained Appendix-B proof.
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- `↑((mu + 1) / 2) ≥ (mu : ENNReal) / 2`. -/
lemma half_mu_lower {mu : ℕ} :
    (↑((mu + 1) / 2) : ENNReal) ≥ (mu : ENNReal) / 2 := by
  let k : ℕ := (mu + 1) / 2
  have h_nat : 2 * k ≥ mu := by omega
  have h' : (2 : ENNReal) * (k : ENNReal) ≥ (mu : ENNReal) := by
    exact_mod_cast h_nat
  have h_eq : (2 : ENNReal) * (k : ENNReal) / 2 = (k : ENNReal) := by
    have h2 : (2 : ENNReal) ≠ 0 := by norm_num
    have h3 : (2 : ENNReal) ≠ ⊤ := by norm_num
    have h_comm : (2 : ENNReal) * (k : ENNReal) = (k : ENNReal) * (2 : ENNReal) := by ring
    rw [h_comm]
    exact ENNReal.mul_div_cancel_right h2 h3
  calc
    (k : ENNReal)
      = (2 : ENNReal) * (k : ENNReal) / 2 := h_eq.symm
    _ ≥ (mu : ENNReal) / 2 := ENNReal.div_le_div_right h' 2

/-- `16 ≤ 1000 * π` as ENNReal. -/
lemma sixteen_le_thousand_pi :
    (16 : ENNReal) ≤ ENNReal.ofReal (1000 * Real.pi) := by
  have h : (16 : ℝ) ≤ 1000 * Real.pi := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    linarith
  have h' : (16 : ENNReal) = ENNReal.ofReal (16 : ℝ) := by norm_cast
  rw [h']
  exact ENNReal.ofReal_le_ofReal h

/-- `x / 2 / 8 = x / 16` for `x : ENNReal. -/
lemma div_two_div_eight {x : ENNReal} : x / 2 / 8 = x / 16 := by
  have h1 : x / 2 / 8 = x * (2 : ENNReal)⁻¹ * (8 : ENNReal)⁻¹ := by
    simp [div_eq_mul_inv]
  rw [h1]
  have h2 : (2 : ENNReal)⁻¹ * (8 : ENNReal)⁻¹ = (16 : ENNReal)⁻¹ := by
    rw [← ENNReal.mul_inv] <;> norm_num
  have h3 : x * (2 : ENNReal)⁻¹ * (8 : ENNReal)⁻¹ = x * ((2 : ENNReal)⁻¹ * (8 : ENNReal)⁻¹) := by
    simp [mul_assoc]
  rw [h3, h2]
  have h4 : x * (16 : ENNReal)⁻¹ = x / 16 := by
    simp [div_eq_mul_inv]
  exact h4

/-- Key constant: `↑((mu+1)/2) / 8 ≥ mu / (1000*π)` in ENNReal. -/
lemma constant_margin {mu : ℕ} :
    (↑((mu + 1) / 2) : ENNReal) / 8 ≥
    (mu : ENNReal) / ENNReal.ofReal (1000 * Real.pi) := by
  let k : ENNReal := ↑((mu + 1) / 2)
  have h1 : k ≥ (mu : ENNReal) / 2 := half_mu_lower
  have h2 : k / 8 ≥ ((mu : ENNReal) / 2) / 8 := ENNReal.div_le_div_right h1 8
  have h3 : ((mu : ENNReal) / 2) / 8 = (mu : ENNReal) / 16 := div_two_div_eight
  have h4 : (mu : ENNReal) / 16 ≥ (mu : ENNReal) / ENNReal.ofReal (1000 * Real.pi) :=
    ENNReal.div_le_div_left sixteen_le_thousand_pi (mu : ENNReal)
  calc
    k / 8
      ≥ ((mu : ENNReal) / 2) / 8 := h2
    _ = (mu : ENNReal) / 16 := h3
    _ ≥ (mu : ENNReal) / ENNReal.ofReal (1000 * Real.pi) := h4

/-- `ofReal a / ofReal b = ofReal (a / b)` for `a ≥ 0`, `b > 0`. -/
lemma ofReal_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    ENNReal.ofReal a / ENNReal.ofReal b = ENNReal.ofReal (a / b) := by
  have h1 : ENNReal.ofReal a / ENNReal.ofReal b =
      ENNReal.ofReal a * (ENNReal.ofReal b)⁻¹ := by
    simp [div_eq_mul_inv]
  rw [h1]
  have h2 : (ENNReal.ofReal b)⁻¹ = ENNReal.ofReal (b⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hb]
  rw [h2]
  have h3 : ENNReal.ofReal a * ENNReal.ofReal (b⁻¹) = ENNReal.ofReal (a * b⁻¹) := by
    rw [← ENNReal.ofReal_mul ha]
    <;> ring
  rw [h3]
  have h4 : a * b⁻¹ = a / b := by
    field_simp [hb.ne'] <;> ring
  rw [h4]

/--
Core ambient-stem selection with explicit `δ ≤ 1/1000` instead of an
existential `delta₀`.  This is the uniform-delta₀ form consumed by the
self-contained assembly.
-/
lemma hairbrush_ambient_stem_selection_core
    {eta theta angleScale δ : ℝ}
    {F : Kakeya.TubeFamily δ}
    {layer : Kakeya.Shading F}
    {mu : ℕ}
    {H : Kakeya.TubeFamily δ}
    {hairShading : Kakeya.Shading H}
    {hairDensity : ℝ}
    (heta : 0 < eta)
    (htheta_pos : 0 < theta)
    (htheta_le_one : theta ≤ 1)
    (h_angleScale_pos : 0 < angleScale)
    (h_two_angleScale : 2 * angleScale ≤ theta)
    (h_rpow : Real.rpow (2 * angleScale / theta) eta ≤ 1 / 4)
    (hδ : 0 < δ)
    (hδ_le : δ ≤ 1 / 1000)
    (hδ_le_angleScale : δ ≤ angleScale)
    (hF_nonempty : F.Nonempty)
    (hmu_pos : 0 < mu)
    (h_mult : ∀ x ∈ layer.union, mu ≤ (F.filter fun T => x ∈ layer.carrier T).card)
    (h_two_broad : IsTwoBroadAtScale layer theta eta)
    (hH_nonempty : H.Nonempty)
    (hHinF : H ⊆ F)
    (h_sub : ∀ T ∈ H, hairShading.carrier T ⊆ layer.carrier T)
    (hhairDensity_pos : 0 < hairDensity)
    (h_density : ∀ T ∈ H, ENNReal.ofReal hairDensity * T.volume ≤ volume (hairShading.carrier T)) :
    Nonempty (HairbrushAmbientStemSelectionData
      (angleScale := angleScale) (hairDensity := hairDensity) layer mu hairShading) := by

  have hδ1 : δ ≤ 1 / 1000 := hδ_le
  have h_angleScale_le_one : angleScale ≤ 1 := by linarith

  let k : ℕ := (mu + 1) / 2

  -- For each hair T, define the transverse family F_T
  let F_T : Kakeya.DeltaTube δ → Finset (Kakeya.DeltaTube δ) := fun T =>
    F.filter fun S => angleScale ≤ hairbrushAcuteAngle T S

  -- For each hair T, define stems with nonzero intersection
  let stems_T : Kakeya.DeltaTube δ → Finset (Kakeya.DeltaTube δ) := fun T =>
    (F_T T).filter fun S =>
      volume (hairShading.carrier T ∩ layer.carrier S) ≠ 0

  have h_stems_subset : ∀ T ∈ H, stems_T T ⊆ F := by
    intro T hT
    exact Finset.Subset.trans (Finset.filter_subset _ _) (Finset.filter_subset _ _)

  -- Per-hair: transverse multiplicity lower bound via bounded_overlap_lower
  have h_per_hair_integral : ∀ T ∈ H,
      (k : ENNReal) * volume (hairShading.carrier T) ≤
      ∑ S ∈ F_T T, volume (layer.carrier S ∩ hairShading.carrier T) := by
    intro T hT
    have hB : MeasurableSet (hairShading.carrier T) :=
      hairShading.measurable_carrier hT
    have hA : ∀ S ∈ F_T T, MeasurableSet (layer.carrier S) := by
      intro S hS
      have hS_F : S ∈ F := (Finset.mem_filter.mp hS).1
      exact layer.measurable_carrier hS_F
    have h_pointwise : ∀ x ∈ hairShading.carrier T,
        k ≤ ((F_T T).filter fun S => x ∈ layer.carrier S).card := by
      intro x hx
      have h_tm : (F.filter fun U => x ∈ layer.carrier U ∧ angleScale ≤ hairbrushAcuteAngle T U).card ≥ k :=
        transverse_multiplicity_lower
          heta htheta_pos h_angleScale_pos h_two_angleScale h_rpow
          mu hmu_pos h_mult h_two_broad hHinF hairShading h_sub hδ_le_angleScale T hT x hx
      have h_filter_eq : (F_T T).filter (fun S => x ∈ layer.carrier S) =
          F.filter (fun U => x ∈ layer.carrier U ∧ angleScale ≤ hairbrushAcuteAngle T U) := by
        ext S
        simp only [F_T, Finset.mem_filter, Finset.mem_filter]
        <;> tauto
      rw [h_filter_eq]
      exact h_tm
    exact bounded_overlap_lower (F_T T) (fun S => layer.carrier S)
      (hairShading.carrier T) k hB hA h_pointwise

  -- Per-hair: density + tube volume lower bound
  have h_per_hair_density : ∀ T ∈ H,
      (k : ENNReal) * ENNReal.ofReal hairDensity * ENNReal.ofReal (Real.pi * δ^2) ≤
      ∑ S ∈ F_T T, volume (layer.carrier S ∩ hairShading.carrier T) := by
    intro T hT
    have h_vol : ENNReal.ofReal hairDensity * T.volume ≤ volume (hairShading.carrier T) :=
      h_density T hT
    have h_tube_vol : ENNReal.ofReal (Real.pi * δ^2) ≤ T.volume :=
      tube_volume_lower_pi hδ T
    have h1 : (k : ENNReal) * ENNReal.ofReal hairDensity * ENNReal.ofReal (Real.pi * δ^2) ≤
        (k : ENNReal) * volume (hairShading.carrier T) := by
      calc
        (k : ENNReal) * ENNReal.ofReal hairDensity * ENNReal.ofReal (Real.pi * δ^2)
          ≤ (k : ENNReal) * ENNReal.ofReal hairDensity * T.volume := by gcongr
        _ = (k : ENNReal) * (ENNReal.ofReal hairDensity * T.volume) := by ring
        _ ≤ (k : ENNReal) * volume (hairShading.carrier T) := by gcongr
    exact le_trans h1 (h_per_hair_integral T hT)

  -- Per-hair: upper bound on each intersection volume
  have h_inter_bound : ∀ T ∈ H, ∀ S ∈ F_T T,
      volume (layer.carrier S ∩ hairShading.carrier T) ≤
      ENNReal.ofReal (8 * Real.pi * δ^3 / angleScale) := by
    intro T hT S hS
    have h_angle : angleScale ≤ hairbrushAcuteAngle T S :=
      (Finset.mem_filter.mp hS).2
    have h1 : volume (layer.carrier S ∩ hairShading.carrier T) ≤
        volume (S.carrier ∩ T.carrier) := by
      have h2 : layer.carrier S ∩ hairShading.carrier T ⊆ S.carrier ∩ T.carrier := by
        intro x hx
        exact ⟨layer.subset_tube (Finset.mem_filter.mp hS).1 hx.1,
          hairShading.subset_tube hT hx.2⟩
      exact measure_mono h2
    have h3 : volume (T.carrier ∩ S.carrier) ≤
        ENNReal.ofReal (8 * Real.pi * δ^3 / angleScale) :=
      uniform_intersection_volume_bound hδ hδ1 h_angleScale_pos h_angleScale_le_one T S h_angle
    have h4 : volume (S.carrier ∩ T.carrier) = volume (T.carrier ∩ S.carrier) := by
      rw [Set.inter_comm]
    rw [h4] at h1
    exact le_trans h1 h3

  -- Sum over F_T equals sum over stems_T (zero terms vanish)
  have h_sum_eq : ∀ T ∈ H,
      ∑ S ∈ F_T T, volume (layer.carrier S ∩ hairShading.carrier T) =
      ∑ S ∈ stems_T T, volume (layer.carrier S ∩ hairShading.carrier T) := by
    intro T hT
    have hsub : stems_T T ⊆ F_T T := Finset.filter_subset _ _
    have h : ∀ S ∈ F_T T, S ∉ stems_T T →
        volume (layer.carrier S ∩ hairShading.carrier T) = 0 := by
      intro S hS hS_not
      have h_vol_zero : volume (hairShading.carrier T ∩ layer.carrier S) = 0 := by
        simpa [stems_T, Finset.mem_filter, hS] using hS_not
      have h_comm : volume (layer.carrier S ∩ hairShading.carrier T) =
          volume (hairShading.carrier T ∩ layer.carrier S) := by
        rw [Set.inter_comm]
      rw [h_comm]
      exact h_vol_zero
    have h_eq : ∑ S ∈ stems_T T, volume (layer.carrier S ∩ hairShading.carrier T) =
        ∑ S ∈ F_T T, volume (layer.carrier S ∩ hairShading.carrier T) :=
      Finset.sum_subset hsub h
    exact h_eq.symm

  -- Per-hair: count nonzero intersections and derive lower bound
  have h_per_hair_count : ∀ T ∈ H,
      (k : ENNReal) * ENNReal.ofReal hairDensity * ENNReal.ofReal (Real.pi * δ^2) ≤
      (↑(stems_T T).card : ENNReal) * ENNReal.ofReal (8 * Real.pi * δ^3 / angleScale) := by
    intro T hT
    have h_sum : ∑ S ∈ stems_T T, volume (layer.carrier S ∩ hairShading.carrier T) ≤
        (↑(stems_T T).card : ENNReal) * ENNReal.ofReal (8 * Real.pi * δ^3 / angleScale) := by
      calc
        ∑ S ∈ stems_T T, volume (layer.carrier S ∩ hairShading.carrier T)
          ≤ ∑ S ∈ stems_T T, ENNReal.ofReal (8 * Real.pi * δ^3 / angleScale) := by
            apply Finset.sum_le_sum
            intro S hS
            have hS' : S ∈ F_T T := (Finset.mem_filter.mp hS).1
            exact h_inter_bound T hT S hS'
        _ = (↑(stems_T T).card : ENNReal) * ENNReal.ofReal (8 * Real.pi * δ^3 / angleScale) := by
            simp [Finset.sum_const, mul_comm]
    have h_main : (k : ENNReal) * ENNReal.ofReal hairDensity * ENNReal.ofReal (Real.pi * δ^2) ≤
        ∑ S ∈ stems_T T, volume (layer.carrier S ∩ hairShading.carrier T) := by
      rw [← h_sum_eq T hT]
      exact h_per_hair_density T hT
    exact le_trans h_main h_sum

  -- Define L as ofReal to simplify arithmetic
  let L_real : ℝ := (k : ℝ) * hairDensity * angleScale / (8 * δ)
  let L : ENNReal := ENNReal.ofReal L_real

  have hL_real_nonneg : 0 ≤ L_real := by positivity
  have hδ_pos' : 0 < δ := hδ

  -- Per-hair: stems_T T.card ≥ L
  have hL : ∀ T ∈ H, L ≤ (↑(stems_T T).card : ENNReal) := by
    intro T hT
    set Vbound : ENNReal := ENNReal.ofReal (8 * Real.pi * δ^3 / angleScale) with hVbound
    have h_pos1 : 0 < 8 * Real.pi * δ^3 / angleScale := by positivity
    have hV_ne_zero : Vbound ≠ 0 := by
      rw [hVbound]
      simpa [ENNReal.ofReal_pos] using h_pos1
    have hV_ne_top : Vbound ≠ ⊤ := by simp [hVbound]
    have h5 : (k : ENNReal) * ENNReal.ofReal hairDensity * ENNReal.ofReal (Real.pi * δ^2) ≤
        (↑(stems_T T).card : ENNReal) * Vbound := h_per_hair_count T hT
    have h_real_eq : L_real * (8 * Real.pi * δ^3 / angleScale) =
        (k : ℝ) * hairDensity * (Real.pi * δ^2) := by
      dsimp only [L_real]
      field_simp [hδ.ne', h_angleScale_pos.ne'] <;> ring
    have h_k_hd_pi2 : (k : ENNReal) * ENNReal.ofReal hairDensity * ENNReal.ofReal (Real.pi * δ^2) =
        ENNReal.ofReal ((k : ℝ) * hairDensity * (Real.pi * δ^2)) := by
      have h1 : (k : ENNReal) = ENNReal.ofReal (k : ℝ) := by norm_cast
      rw [h1]
      have h2 : ENNReal.ofReal (k : ℝ) * ENNReal.ofReal hairDensity =
          ENNReal.ofReal ((k : ℝ) * hairDensity) := by
        rw [← ENNReal.ofReal_mul (by positivity)] <;> norm_cast
      rw [h2]
      rw [← ENNReal.ofReal_mul (by positivity)] <;> norm_cast
    have hL_Vbound : L * Vbound =
        (k : ENNReal) * ENNReal.ofReal hairDensity * ENNReal.ofReal (Real.pi * δ^2) := by
      rw [show L = ENNReal.ofReal L_real from rfl, hVbound]
      rw [← ENNReal.ofReal_mul hL_real_nonneg]
      rw [h_real_eq]
      exact h_k_hd_pi2.symm
    have h6 : L * Vbound ≤ (↑(stems_T T).card : ENNReal) * Vbound := by
      rw [hL_Vbound]
      exact h5
    have h7 : L ≤ (↑(stems_T T).card : ENNReal) := by
      have h6' : L * Vbound ≤ (↑(stems_T T).card : ENNReal) * Vbound := by
        rw [hL_Vbound]
        exact h5
      have h_cancel : L * Vbound ≤ (↑(stems_T T).card : ENNReal) * Vbound ↔
          L ≤ (↑(stems_T T).card : ENNReal) :=
        ENNReal.mul_le_mul_iff_left hV_ne_zero hV_ne_top
      exact h_cancel.mp h6'
    exact h7

  -- Stem averaging
  have h_avg := stem_averaging_general hF_nonempty stems_T h_stems_subset L hL
  rcases h_avg with ⟨stem, hstem_mem, hstem_count⟩

  -- Define brush
  let brush : Kakeya.TubeFamily δ :=
    H.filter fun T => angleScale ≤ hairbrushAcuteAngle T stem ∧
      volume (hairShading.carrier T ∩ layer.carrier stem) ≠ 0

  have h_brush_eq : brush = H.filter fun T => stem ∈ stems_T T := by
    ext T
    simp only [brush, stems_T, F_T, Finset.mem_filter]
    <;> constructor <;> intro h <;> simp_all <;> tauto

  have h_brush_count : (brush.enncard : ENNReal) ≥ L * H.enncard / F.enncard := by
    rw [h_brush_eq]
    simpa [Kakeya.TubeFamily.enncard] using hstem_count

  -- Final cardinality bound
  have h_final : brush.enncard ≥
      ENNReal.ofReal angleScale * (mu : ENNReal) * ENNReal.ofReal hairDensity * H.enncard /
        (ENNReal.ofReal (1000 * Real.pi) * ENNReal.ofReal δ * F.enncard) := by
    let target_real : ℝ := (mu : ℝ) * hairDensity * angleScale / ((1000 * Real.pi) * δ)
    have htarget_nonneg : 0 ≤ target_real := by positivity
    have h_real_ineq : L_real ≥ target_real := by
      dsimp only [L_real, target_real]
      have h1 : 2 * k ≥ mu := by omega
      have h1' : (2 : ℝ) * (k : ℝ) ≥ (mu : ℝ) := by exact_mod_cast h1
      have h1'' : (k : ℝ) ≥ (mu : ℝ) / 2 := by linarith
      have h2 : (k : ℝ) / 8 ≥ (mu : ℝ) / 16 := by linarith
      have h3 : (16 : ℝ) ≤ 1000 * Real.pi := by
        have h4 : (3 : ℝ) < Real.pi := Real.pi_gt_three
        linarith
      have h5 : (mu : ℝ) / 16 ≥ (mu : ℝ) / (1000 * Real.pi) := by
        gcongr
        <;> linarith
      have h6 : (k : ℝ) / 8 ≥ (mu : ℝ) / (1000 * Real.pi) := by linarith
      have hpos1 : 0 < hairDensity := hhairDensity_pos
      have hpos2 : 0 < angleScale := h_angleScale_pos
      have hpos3 : 0 < δ := hδ
      have h7 : ((k : ℝ) / 8) * (hairDensity * angleScale / δ) ≥
          ((mu : ℝ) / (1000 * Real.pi)) * (hairDensity * angleScale / δ) := by
        gcongr
        <;> linarith
      have h10 : (k : ℝ) * hairDensity * angleScale / (8 * δ) =
          ((k : ℝ) / 8) * (hairDensity * angleScale / δ) := by ring
      have h11 : (mu : ℝ) * hairDensity * angleScale / ((1000 * Real.pi) * δ) =
          ((mu : ℝ) / (1000 * Real.pi)) * (hairDensity * angleScale / δ) := by ring
      rw [h10, h11]
      exact h7
    have hL_ge_target : L ≥ ENNReal.ofReal target_real := by
      exact ENNReal.ofReal_le_ofReal h_real_ineq
    have hRHS : ENNReal.ofReal angleScale * (mu : ENNReal) * ENNReal.ofReal hairDensity * H.enncard /
        (ENNReal.ofReal (1000 * Real.pi) * ENNReal.ofReal δ * F.enncard) =
        ENNReal.ofReal target_real * H.enncard / F.enncard := by
      have hmu : (mu : ENNReal) = ENNReal.ofReal (mu : ℝ) := by norm_cast
      have h_mul1 : ENNReal.ofReal angleScale * ENNReal.ofReal (mu : ℝ) * ENNReal.ofReal hairDensity =
          ENNReal.ofReal ((mu : ℝ) * hairDensity * angleScale) := by
        have h_a : ENNReal.ofReal angleScale * ENNReal.ofReal (mu : ℝ) =
            ENNReal.ofReal (angleScale * (mu : ℝ)) := by
          rw [← ENNReal.ofReal_mul (by positivity)] <;> norm_cast
        rw [h_a]
        have h_b : ENNReal.ofReal (angleScale * (mu : ℝ)) * ENNReal.ofReal hairDensity =
            ENNReal.ofReal ((angleScale * (mu : ℝ)) * hairDensity) := by
          rw [← ENNReal.ofReal_mul (by positivity)] <;> norm_cast
        rw [h_b]
        have h_c : (angleScale * (mu : ℝ)) * hairDensity = (mu : ℝ) * hairDensity * angleScale := by ring
        rw [h_c]
      have h_mul2 : ENNReal.ofReal (1000 * Real.pi) * ENNReal.ofReal δ =
          ENNReal.ofReal ((1000 * Real.pi) * δ) := by
        rw [← ENNReal.ofReal_mul (by positivity)] <;> norm_cast
      have h_div : ENNReal.ofReal ((mu : ℝ) * hairDensity * angleScale) /
          ENNReal.ofReal ((1000 * Real.pi) * δ) =
          ENNReal.ofReal (((mu : ℝ) * hairDensity * angleScale) / ((1000 * Real.pi) * δ)) := by
        exact ofReal_div (by positivity) (by positivity)
      calc
        ENNReal.ofReal angleScale * (mu : ENNReal) * ENNReal.ofReal hairDensity * H.enncard /
            (ENNReal.ofReal (1000 * Real.pi) * ENNReal.ofReal δ * F.enncard)
          = (ENNReal.ofReal angleScale * ENNReal.ofReal (mu : ℝ) * ENNReal.ofReal hairDensity) * H.enncard /
              (ENNReal.ofReal (1000 * Real.pi) * ENNReal.ofReal δ * F.enncard) := by
            rw [hmu] <;> ring
        _ = ENNReal.ofReal ((mu : ℝ) * hairDensity * angleScale) * H.enncard /
              (ENNReal.ofReal ((1000 * Real.pi) * δ) * F.enncard) := by
            rw [h_mul1, h_mul2] <;> ring
        _ = (ENNReal.ofReal ((mu : ℝ) * hairDensity * angleScale) / ENNReal.ofReal ((1000 * Real.pi) * δ)) * H.enncard / F.enncard := by
            have h_alg : ∀ (a b c d : ENNReal), b ≠ 0 → b ≠ ⊤ → d ≠ 0 → d ≠ ⊤ →
                a * c / (b * d) = (a / b) * c / d := by
              intro a b c d hb0 hbt hd0 hdt
              have h1 : (b * d)⁻¹ = b⁻¹ * d⁻¹ := by
                rw [ENNReal.mul_inv] <;> tauto
              simp [div_eq_mul_inv, h1, mul_assoc, mul_comm, mul_left_comm]
            have hb0 : ENNReal.ofReal ((1000 * Real.pi) * δ) ≠ 0 := by positivity
            have hbt : ENNReal.ofReal ((1000 * Real.pi) * δ) ≠ ⊤ := by simp
            have hd0 : F.enncard ≠ 0 := by
              simpa [Kakeya.TubeFamily.enncard, Finset.nonempty_iff_ne_empty] using hF_nonempty
            have hdt : F.enncard ≠ ⊤ := by
              simp [Kakeya.TubeFamily.enncard]
            exact h_alg _ _ _ _ hb0 hbt hd0 hdt
        _ = ENNReal.ofReal target_real * H.enncard / F.enncard := by
            rw [h_div] <;> simp [target_real]
    rw [hRHS]
    have h : L * H.enncard / F.enncard ≥ ENNReal.ofReal target_real * H.enncard / F.enncard := by
      gcongr
      <;> exact hL_ge_target
    exact le_trans h h_brush_count

  refine ⟨stem, hstem_mem, brush, ?_, ?_, ?_⟩
  · -- brush_subset
    exact Finset.filter_subset _ _
  · -- transverse_overlap
    intro T hT
    have h1 : angleScale ≤ hairbrushAcuteAngle T stem ∧
        volume (hairShading.carrier T ∩ layer.carrier stem) ≠ 0 :=
      (Finset.mem_filter.mp hT).2
    exact h1
  · -- brush_cardinality_lower
    exact h_final

/--
Frozen statement form of ambient-stem selection.

The existential witness is always `1 / 1000`; the core lemma
`hairbrush_ambient_stem_selection_core` exposes this uniform bound directly
for assembly use.
-/
theorem hairbrush_ambient_stem_selection :
    HairbrushAmbientStemSelectionStatement := by
  intro eta theta angleScale heta htheta_pos htheta_le_one h_angleScale_pos
    h_two_angleScale h_rpow
  refine ⟨1 / 1000, by norm_num, by norm_num,
    fun δ hδ hδ_le hδ_le_angleScale F layer hF_nonempty mu hmu_pos h_mult h_two_broad
      H hH_nonempty hHinF hairShading h_sub hairDensity hhairDensity_pos h_density =>
    hairbrush_ambient_stem_selection_core
      heta htheta_pos htheta_le_one h_angleScale_pos h_two_angleScale h_rpow
      hδ hδ_le hδ_le_angleScale hF_nonempty hmu_pos h_mult h_two_broad
      hH_nonempty hHinF h_sub hhairDensity_pos h_density⟩

end Kakeya.Assouad
