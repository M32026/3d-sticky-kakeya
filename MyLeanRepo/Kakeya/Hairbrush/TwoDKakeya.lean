import MyLeanRepo.Kakeya.AssertionD
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# 2D Kakeya / Córdoba L² bound

Córdoba L² argument (Wolff 1995 Lemma 2.2) for shaded δ-tubes in a 2-plane.
-/

noncomputable section

open MeasureTheory Set Finset

namespace Kakeya.Hairbrush

variable {δ : ℝ} {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}

local instance : DecidableEq (Kakeya.DeltaTube δ) := Classical.decEq _

/-- The multiplicity function as a sum of indicators. -/
def multFun (Y : Kakeya.Shading F) : Point3 → ENNReal :=
  fun x => ∑ T ∈ F, Set.indicator (Y.carrier T) (fun _ => (1 : ENNReal)) x

/-- Measurability of a finite sum of measurable functions. -/
private lemma measurable_finset_sum {α : Type*} [DecidableEq α]
    {f : α → Point3 → ENNReal} {s : Finset α}
    (h : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun x : Point3 => ∑ i ∈ s, f i x) := by
  have h_main : ∀ (t : Finset α), (∀ i ∈ t, Measurable (f i)) →
      Measurable (fun x : Point3 => ∑ i ∈ t, f i x) := by
    intro t
    exact Finset.induction_on t
      (fun _ => by simpa using measurable_const)
      (fun a t ha ih h2 => by
        have h_fun : (fun x : Point3 => ∑ i ∈ (insert a t), f i x) =
            fun x => f a x + ∑ i ∈ t, f i x := by
          funext x
          rw [Finset.sum_insert ha] <;> rfl
        rw [h_fun]
        have h_a : Measurable (f a) := h2 a (Finset.mem_insert_self a t)
        have h_t : ∀ i ∈ t, Measurable (f i) := fun i hi => h2 i (Finset.mem_insert_of_mem hi)
        exact h_a.add (ih h_t))
  exact h_main s h

/-- Measurability of a finite sum of measurable indicators. -/
private lemma finset_indicator_sum_measurable
    {s : Finset (Kakeya.DeltaTube δ)} (hs : s ⊆ F) :
    Measurable (fun x : Point3 =>
      ∑ T ∈ s, Set.indicator (Y.carrier T) (fun _ => (1 : ENNReal)) x) := by
  exact measurable_finset_sum (fun T hT =>
    measurable_const.indicator (Y.measurable_carrier (hs hT)))

/-- `multFun` is measurable. -/
private lemma multFun_measurable : Measurable (multFun Y) :=
  finset_indicator_sum_measurable (Finset.Subset.refl F)

/-- `∫ multFun = Y.mass`. -/
lemma lintegral_multFun :
    (∫⁻ x, multFun Y x) = Y.mass := by
  have h_unfold : (fun x : Point3 => multFun Y x) =
      fun x => ∑ T ∈ F, Set.indicator (Y.carrier T) (fun _ => (1 : ENNReal)) x := by
    funext x; rfl
  rw [h_unfold]
  rw [MeasureTheory.lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro T hT
    exact MeasureTheory.lintegral_indicator_one (Y.measurable_carrier hT)
  · intro T hT
    exact measurable_const.indicator (Y.measurable_carrier hT)

/-- `∫ (multFun)² = ∑_{T,U} |Y(T) ∩ Y(U)|`. -/
lemma lintegral_multFun_sq :
    (∫⁻ x, (multFun Y x)^(2 : ℝ)) =
      ∑ T ∈ F, ∑ U ∈ F,
        MeasureTheory.volume (Y.carrier T ∩ Y.carrier U) := by
  have h_sq : ∀ x, (multFun Y x)^(2 : ℝ) =
      ∑ T ∈ F, ∑ U ∈ F,
        Set.indicator (Y.carrier T ∩ Y.carrier U) (fun _ => (1 : ENNReal)) x := by
    intro x
    have h1 : (multFun Y x)^(2 : ℝ) = (multFun Y x)^2 := by
      exact ENNReal.rpow_two (multFun Y x)
    rw [h1]
    have h_sum_sq : (multFun Y x)^2 = ∑ T ∈ F, ∑ U ∈ F,
        (Set.indicator (Y.carrier T) (fun _ => (1 : ENNReal)) x *
         Set.indicator (Y.carrier U) (fun _ => (1 : ENNReal)) x) := by
      simp only [multFun, pow_two]
      rw [Finset.sum_mul_sum] <;> rfl
    rw [h_sum_sq]
    apply Finset.sum_congr rfl
    intro T _
    apply Finset.sum_congr rfl
    intro U _
    have h_ind : Set.indicator (Y.carrier T) (fun _ => (1 : ENNReal)) x *
        Set.indicator (Y.carrier U) (fun _ => (1 : ENNReal)) x =
      Set.indicator (Y.carrier T ∩ Y.carrier U) (fun _ => (1 : ENNReal)) x := by
      by_cases hT : x ∈ Y.carrier T <;> by_cases hU : x ∈ Y.carrier U <;>
        simp [hT, hU]
    exact h_ind
  rw [MeasureTheory.lintegral_congr h_sq]
  rw [MeasureTheory.lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro T hT
    rw [MeasureTheory.lintegral_finsetSum]
    · apply Finset.sum_congr rfl
      intro U hU
      exact MeasureTheory.lintegral_indicator_one
        ((Y.measurable_carrier hT).inter (Y.measurable_carrier hU))
    · intro U hU
      exact measurable_const.indicator
        ((Y.measurable_carrier hT).inter (Y.measurable_carrier hU))
  · intro T hT
    exact measurable_finset_sum (fun U hU =>
      measurable_const.indicator
        ((Y.measurable_carrier hT).inter (Y.measurable_carrier hU)))

/-- The shaded union is measurable. -/
private lemma union_measurable : MeasurableSet Y.union := by
  have h : Y.union = ⋃ T ∈ F, Y.carrier T := by
    ext x
    simp [Kakeya.Shading.union]
  rw [h]
  exact MeasurableSet.biUnion (Finset.countable_toSet F)
    (fun T hT => Y.measurable_carrier (Finset.mem_coe.mp hT))

/-- Squaring Hölder p=q=2 gives Cauchy–Schwarz (real-power version). -/
private lemma holder_square {f g : Point3 → ENNReal}
    (hf : AEMeasurable f MeasureTheory.volume)
    (hg : AEMeasurable g MeasureTheory.volume) :
    (∫⁻ x, f x * g x)^2 ≤
      (∫⁻ x, (f x)^(2 : ℝ)) * (∫⁻ x, (g x)^(2 : ℝ)) := by
  have h_hc : Real.HolderConjugate 2 2 := Real.HolderConjugate.two_two
  set B := ∫⁻ x, (f x)^(2 : ℝ) with hB
  set C := ∫⁻ x, (g x)^(2 : ℝ) with hC
  have h1 : (∫⁻ x, f x * g x) ≤ B^(1 / 2 : ℝ) * C^(1 / 2 : ℝ) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := MeasureTheory.volume) h_hc hf hg
  have h2 : (∫⁻ x, f x * g x)^2 ≤ (B^(1 / 2 : ℝ) * C^(1 / 2 : ℝ))^2 := by gcongr
  have h4 : (B^(1 / 2 : ℝ))^2 = B := by
    have h41 : (B^(1 / 2 : ℝ))^2 = (B^(1 / 2 : ℝ))^(2 : ℝ) := by
      exact (ENNReal.rpow_two (B ^ (1 / 2))).symm
    rw [h41]
    have h42 : (B^(1 / 2 : ℝ))^(2 : ℝ) = B^((1 / 2 : ℝ) * (2 : ℝ)) :=
      (ENNReal.rpow_mul B (1 / 2 : ℝ) (2 : ℝ)).symm
    rw [h42]
    have h43 : (1 / 2 : ℝ) * (2 : ℝ) = 1 := by norm_num
    rw [h43]
    exact ENNReal.rpow_one B
  have h5 : (C^(1 / 2 : ℝ))^2 = C := by
    have h51 : (C^(1 / 2 : ℝ))^2 = (C^(1 / 2 : ℝ))^(2 : ℝ) := by
      exact (ENNReal.rpow_two (C ^ (1 / 2))).symm
    rw [h51]
    have h52 : (C^(1 / 2 : ℝ))^(2 : ℝ) = C^((1 / 2 : ℝ) * (2 : ℝ)) :=
      (ENNReal.rpow_mul C (1 / 2 : ℝ) (2 : ℝ)).symm
    rw [h52]
    have h53 : (1 / 2 : ℝ) * (2 : ℝ) = 1 := by norm_num
    rw [h53]
    exact ENNReal.rpow_one C
  have h3 : (B^(1 / 2 : ℝ) * C^(1 / 2 : ℝ))^2 = B * C := by
    rw [mul_pow, h4, h5]
  rw [h3] at h2
  exact h2

/-- Córdoba Cauchy–Schwarz: `Y.mass² ≤ |Y.union| · ∫ multFun²`. -/
lemma cordoba_cauchy_schwarz :
    Y.mass^2 ≤ MeasureTheory.volume Y.union *
        (∫⁻ x, (multFun Y x)^(2 : ℝ)) := by
  let indU : Point3 → ENNReal := Set.indicator Y.union (fun _ => (1 : ENNReal))
  have h_meas_indU : Measurable indU :=
    measurable_const.indicator union_measurable
  have h_mult_ind : ∀ x, multFun Y x * indU x = multFun Y x := by
    intro x
    by_cases hx : x ∈ Y.union
    · simp [indU, hx]
    · have h_all : ∀ T ∈ F, x ∉ Y.carrier T := by
        intro T hT
        intro h_in
        exact hx ⟨T, hT, h_in⟩
      have h4 : multFun Y x = 0 := by
        have h_sum : ∑ T ∈ F, Set.indicator (Y.carrier T) (fun _ => (1 : ENNReal)) x = 0 := by
          apply Finset.sum_eq_zero
          intro T hT
          have h5 : x ∉ Y.carrier T := h_all T hT
          simp [h5]
        exact h_sum
      rw [h4]
      <;> simp [indU, hx]
  have h1 : (∫⁻ x, multFun Y x * indU x) = Y.mass := by
    have h2 : (∫⁻ x, multFun Y x) = Y.mass := lintegral_multFun
    have h3 : (∫⁻ x, multFun Y x * indU x) = ∫⁻ x, multFun Y x :=
      MeasureTheory.lintegral_congr h_mult_ind
    rw [h3, h2]
  have h_indU_sq : ∀ x, (indU x)^(2 : ℝ) = indU x := by
    intro x
    by_cases hx : x ∈ Y.union
    · simp [indU, hx] <;> norm_num
    · simp [indU, hx] <;> norm_num
  have h5 : (∫⁻ x, (indU x)^(2 : ℝ)) = MeasureTheory.volume Y.union := by
    rw [MeasureTheory.lintegral_congr h_indU_sq]
    exact MeasureTheory.lintegral_indicator_one union_measurable
  have hmm : Measurable (multFun Y) := multFun_measurable (Y := Y)
  have h_cs := holder_square hmm.aemeasurable h_meas_indU.aemeasurable
  rw [h1] at h_cs
  rw [h5] at h_cs
  have h_comm : (∫⁻ x, (multFun Y x)^(2 : ℝ)) * MeasureTheory.volume Y.union =
      MeasureTheory.volume Y.union * (∫⁻ x, (multFun Y x)^(2 : ℝ)) := by ring
  rw [h_comm] at h_cs
  exact h_cs

/--
Conditional 2D Kakeya volume lower bound (Córdoba argument).
-/
theorem two_d_kakeya_volume_bound (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (lambda V C : ENNReal)
    (hV : ∀ T ∈ F, T.volume ≤ V)
    (hY_dense : Y.IsLambdaDense lambda)
    (hlog_pos : 0 < Real.log (1 / δ))
    (h_inter_sum : ∀ T ∈ F,
        ∑ U ∈ F.erase T,
          MeasureTheory.volume (Y.carrier T ∩ Y.carrier U) ≤
        C * V * ENNReal.ofReal (Real.log (1 / δ))) :
    MeasureTheory.volume Y.union ≥
      lambda^2 * F.mass^2 /
        (F.enncard * V * (1 + C * ENNReal.ofReal (Real.log (1 / δ)))) := by
  let D : ENNReal := F.enncard * V * (1 + C * ENNReal.ofReal (Real.log (1 / δ)))
  have hY_mass_le : Y.mass ≤ F.enncard * V := by
    calc
      Y.mass = ∑ T ∈ F, MeasureTheory.volume (Y.carrier T) := by rfl
      _ ≤ ∑ T ∈ F, T.volume := Finset.sum_le_sum fun T hT =>
        MeasureTheory.measure_mono (Y.subset_tube hT)
      _ ≤ ∑ T ∈ F, V := Finset.sum_le_sum fun T hT => hV T hT
      _ = F.enncard * V := by
        simp [Finset.sum_const, Kakeya.TubeFamily.enncard] <;> ring
  have hL2 : (∫⁻ x, (multFun Y x)^(2 : ℝ)) ≤
      Y.mass + F.enncard * C * V * ENNReal.ofReal (Real.log (1 / δ)) := by
    rw [lintegral_multFun_sq]
    have h_offdiag : ∑ T ∈ F, ∑ U ∈ F.erase T,
          MeasureTheory.volume (Y.carrier T ∩ Y.carrier U) ≤
        F.enncard * C * V * ENNReal.ofReal (Real.log (1 / δ)) := by
      calc
        ∑ T ∈ F, ∑ U ∈ F.erase T, _ ≤
          ∑ T ∈ F, (C * V * ENNReal.ofReal (Real.log (1 / δ))) :=
            Finset.sum_le_sum fun T hT => h_inter_sum T hT
        _ = F.enncard * C * V * ENNReal.ofReal (Real.log (1 / δ)) := by
          simp [Finset.sum_const, Kakeya.TubeFamily.enncard] <;> ring
    have h_diag : ∑ T ∈ F, MeasureTheory.volume (Y.carrier T ∩ Y.carrier T) = Y.mass := by
      apply Finset.sum_congr rfl
      intro T hT
      have h4 : Y.carrier T ∩ Y.carrier T = Y.carrier T := by ext x; simp
      rw [h4]
    have h_sum_eq : ∑ T ∈ F, ∑ U ∈ F,
          MeasureTheory.volume (Y.carrier T ∩ Y.carrier U) =
        Y.mass + ∑ T ∈ F, ∑ U ∈ F.erase T,
          MeasureTheory.volume (Y.carrier T ∩ Y.carrier U) := by
      have h_per_T : ∀ T ∈ F, ∑ U ∈ F,
            MeasureTheory.volume (Y.carrier T ∩ Y.carrier U) =
          MeasureTheory.volume (Y.carrier T ∩ Y.carrier T) +
          ∑ U ∈ F.erase T,
            MeasureTheory.volume (Y.carrier T ∩ Y.carrier U) := by
        intro T hT
        let f : Kakeya.DeltaTube δ → ENNReal := fun U =>
          MeasureTheory.volume (Y.carrier T ∩ Y.carrier U)
        have h_F_eq : F = insert T (F.erase T) := by
          rw [Finset.insert_erase hT]
        have h_notin : T ∉ F.erase T := by simp
        have h_erase : (insert T (F.erase T)).erase T = F.erase T := by
          rw [Finset.erase_insert h_notin]
        have h_sum : ∑ U ∈ F, f U = f T + ∑ U ∈ F.erase T, f U := by
          rw [h_F_eq]
          rw [Finset.sum_insert h_notin]
          rw [h_erase]
          <;> rfl
        exact h_sum
      calc
        ∑ T ∈ F, ∑ U ∈ F, _
          = ∑ T ∈ F, (MeasureTheory.volume (Y.carrier T ∩ Y.carrier T) +
              ∑ U ∈ F.erase T, _) := Finset.sum_congr rfl h_per_T
        _ = (∑ T ∈ F, MeasureTheory.volume (Y.carrier T ∩ Y.carrier T)) +
              ∑ T ∈ F, ∑ U ∈ F.erase T, _ := by
          rw [Finset.sum_add_distrib]
        _ = Y.mass + ∑ T ∈ F, ∑ U ∈ F.erase T, _ := by rw [h_diag]
    rw [h_sum_eq] <;> gcongr
  have h_denom_bound : Y.mass + F.enncard * C * V * ENNReal.ofReal (Real.log (1 / δ)) ≤ D := by
    dsimp only [D]
    calc
      Y.mass + F.enncard * C * V * ENNReal.ofReal (Real.log (1 / δ))
        ≤ F.enncard * V + F.enncard * C * V * ENNReal.ofReal (Real.log (1 / δ)) := by gcongr
      _ = F.enncard * V * (1 + C * ENNReal.ofReal (Real.log (1 / δ))) := by ring
  have h_cs := cordoba_cauchy_schwarz (Y := Y)
  have h_mass : lambda * F.mass ≤ Y.mass := hY_dense
  have h6 : (lambda * F.mass)^2 ≤ Y.mass^2 := by
    exact ENNReal.pow_le_pow_left hY_dense
  have h7 : (lambda * F.mass)^2 = lambda^2 * F.mass^2 := by
    rw [mul_pow]
  have h_main : lambda^2 * F.mass^2 ≤ MeasureTheory.volume Y.union * D := by
    calc
      lambda^2 * F.mass^2
        = (lambda * F.mass)^2 := by rw [h7]
      _ ≤ Y.mass^2 := h6
      _ ≤ MeasureTheory.volume Y.union *
            (Y.mass + F.enncard * C * V * ENNReal.ofReal (Real.log (1 / δ))) :=
          h_cs.trans (mul_le_mul_right hL2 _)
      _ ≤ MeasureTheory.volume Y.union * D := mul_le_mul_right h_denom_bound _
  exact ENNReal.div_le_of_le_mul h_main

end Kakeya.Hairbrush
