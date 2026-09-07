import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-!
# Layer-Cake Symdiff Identity

For a function `u : E n → [0,1]` and a set `S ⊆ K`, the integral over
levels `s ∈ (0,1]` of the volume of the symmetric difference
`{u > s} Δ S` equals the `L¹` distance `∫_K |u - 1_S|`.

This is the standard layer-cake / Fubini identity used to bound
volume error in the mollification level-selection argument.
-/

open MeasureTheory ENNReal Set Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ}

/-- Pointwise identity: for fixed x, the s-measure of {s ∈ Ioc(0,1] | x ∈ symmDiff {u > s} S}
equals |u x - 1_S x|. -/
private lemma pointwise_layer_cake
    {u : E n → ℝ} (x : E n) (hx0 : 0 ≤ u x) (hx1 : u x ≤ 1)
    {S : Set (E n)} (hS : MeasurableSet S) :
    ∫⁻ (s : ℝ) in Set.Ioc (0 : ℝ) 1,
      Set.indicator (symmDiff {y | u y > s} S) (fun _ => (1 : ENNReal)) x =
    ENNReal.ofReal |u x - Set.indicator S (fun _ => (1 : ℝ)) x| := by
  set a : ℝ := u x with ha_def
  have ha0 : 0 ≤ a := hx0
  have ha1 : a ≤ 1 := hx1
  let Q : Set ℝ := {s | x ∈ symmDiff {y | u y > s} S}
  have h_Q_meas : MeasurableSet Q := by
    by_cases hxS : x ∈ S
    · have hQ : Q = Set.Ici a := by
        ext s
        simp only [Q, mem_setOf_eq, mem_Ici]
        have h : x ∈ symmDiff {y | u y > s} S ↔ ¬(u x > s) := by
          simp [symmDiff, hxS] <;> tauto
        rw [h] <;> simp [ha_def] <;> exact ⟨fun h => by linarith, fun h => by linarith⟩
      rw [hQ] <;> exact measurableSet_Ici
    · have hQ : Q = Set.Iio a := by
        ext s
        simp only [Q, mem_setOf_eq, mem_Iio]
        have h : x ∈ symmDiff {y | u y > s} S ↔ u x > s := by
          simp [symmDiff, hxS] <;> tauto
        rw [h] <;> simp [ha_def]
      rw [hQ] <;> exact measurableSet_Iio
  have h_eq1 : ∫⁻ (s : ℝ) in Set.Ioc (0 : ℝ) 1,
      Set.indicator (symmDiff {y | u y > s} S) (fun _ => (1 : ENNReal)) x =
      volume (Set.Ioc (0 : ℝ) 1 ∩ Q) := by
    have h1 : ∫⁻ (s : ℝ) in Set.Ioc (0 : ℝ) 1,
        Set.indicator (symmDiff {y | u y > s} S) (fun _ => (1 : ENNReal)) x =
        ∫⁻ (s : ℝ) in Set.Ioc (0 : ℝ) 1, Set.indicator Q (fun _ => (1 : ENNReal)) s := by
      congr with s
      <;> simp [Q, Set.indicator_apply] <;> aesop
    rw [h1, setLIntegral_indicator h_Q_meas]
    <;> simp [inter_comm]
    <;> rfl
  rw [h_eq1]
  by_cases hxS : x ∈ S
  · -- Case x ∈ S
    have hQ : Q = Set.Ici a := by
      ext s
      simp only [Q, mem_setOf_eq, mem_Ici]
      have h : x ∈ symmDiff {y | u y > s} S ↔ ¬(u x > s) := by
        simp [symmDiff, hxS] <;> tauto
      rw [h] <;> simp [ha_def] <;> exact ⟨fun h => by linarith, fun h => by linarith⟩
    rw [hQ]
    have h_vol : volume (Set.Ioc (0 : ℝ) 1 ∩ Set.Ici a) = ENNReal.ofReal (1 - a) := by
      by_cases ha_pos : 0 < a
      · have h_set : Set.Ioc (0 : ℝ) 1 ∩ Set.Ici a = Set.Icc a 1 := by
          ext s
          simp only [mem_inter, mem_Ioc, mem_Ici, mem_Icc]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩
            exact ⟨h3, h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨⟨by linarith, h2⟩, h1⟩
        rw [h_set, Real.volume_Icc]
        <;> simp [max_eq_right ha0] <;> ring_nf <;> norm_num <;> linarith
      · have ha0' : a = 0 := by linarith
        rw [ha0']
        have h_set : Set.Ioc (0 : ℝ) 1 ∩ Set.Ici (0 : ℝ) = Set.Ioc (0 : ℝ) 1 := by
          apply inter_eq_left.mpr
          intro s hs
          have h : 0 < s := hs.1
          exact le_of_lt h
        rw [h_set, Real.volume_Ioc]
        <;> simp <;> norm_num
    rw [h_vol]
    have h2 : Set.indicator S (fun _ => (1 : ℝ)) x = 1 := by
      simp [Set.indicator_apply, hxS]
    rw [h2, ha_def]
    have h_abs : |a - 1| = 1 - a := by rw [abs_of_nonpos] <;> linarith
    rw [h_abs]
  · -- Case x ∉ S
    have hQ : Q = Set.Iio a := by
      ext s
      simp only [Q, mem_setOf_eq, mem_Iio]
      have h : x ∈ symmDiff {y | u y > s} S ↔ u x > s := by
        simp [symmDiff, hxS] <;> tauto
      rw [h] <;> simp [ha_def]
    rw [hQ]
    have h_vol : volume (Set.Ioc (0 : ℝ) 1 ∩ Set.Iio a) = ENNReal.ofReal a := by
      have h_set : Set.Ioc (0 : ℝ) 1 ∩ Set.Iio a = Set.Ioo 0 a := by
        ext s
        simp only [mem_inter, mem_Ioc, mem_Iio, mem_Ioo]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, by linarith⟩, h2⟩
      rw [h_set, Real.volume_Ioo]
      <;> simp [max_eq_right ha0] <;> ring_nf <;> norm_num <;> linarith
    rw [h_vol]
    have h2 : Set.indicator S (fun _ => (1 : ℝ)) x = 0 := by
      simp [Set.indicator_apply, hxS]
    rw [h2, ha_def]
    have h_abs : |a - 0| = a := by rw [abs_of_nonneg] <;> linarith
    rw [h_abs] <;> ring

/-- **Layer-cake symdiff identity**.

For `u : E n → [0,1]` and `S ⊆ K`,
`∫₀¹ volume({u > s} Δ S) ds = ∫_K |u - 1_S|`. -/
lemma layer_cake_symdiff
    {u : E n → ℝ} (hu_meas : Measurable u)
    (h0 : ∀ x, 0 ≤ u x) (h1 : ∀ x, u x ≤ 1)
    {S : Set (E n)} (hS : MeasurableSet S)
    (K : Set (E n)) (hK : MeasurableSet K)
    (h_supp : ∀ x ∉ K, u x = 0) (hS_sub : S ⊆ K) :
    ∫⁻ s in Set.Ioc (0 : ℝ) 1, volume (symmDiff {x | u x > s} S) =
    ∫⁻ x in K, ENNReal.ofReal |u x - Set.indicator S (fun _ => (1 : ℝ)) x| := by
  let f : E n → ℝ → ENNReal := fun x s =>
    Set.indicator (symmDiff {y | u y > s} S) (fun _ => (1 : ENNReal)) x
  let g : ℝ → E n → ENNReal := fun s x => f x s
  -- Measurability of the uncurried function
  let A : Set (E n × ℝ) := {p | u p.1 > p.2}
  have hA_meas : MeasurableSet A := by
    have h1 : Measurable fun (p : E n × ℝ) => u p.1 := hu_meas.comp measurable_fst
    have h2 : Measurable fun (p : E n × ℝ) => p.2 := measurable_snd
    have h3 : MeasurableSet {p : E n × ℝ | p.2 < u p.1} := by exact measurableSet_lt h2 h1
    have hA : A = {p : E n × ℝ | p.2 < u p.1} := by
      ext p
      simp only [A, mem_setOf_eq]
      <;> rfl
    rw [hA]; exact h3
  let S' : Set (E n × ℝ) := S ×ˢ Set.univ
  have hS'_meas : MeasurableSet S' := MeasurableSet.prod hS MeasurableSet.univ
  let D : Set (E n × ℝ) := (A ∩ S'ᶜ) ∪ (Aᶜ ∩ S')
  have hD_meas : MeasurableSet D :=
    hA_meas.inter hS'_meas.compl |>.union (hA_meas.compl.inter hS'_meas)
  have hD_eq : D = {p : E n × ℝ | p.1 ∈ symmDiff {y | u y > p.2} S} := by
    ext ⟨x, s⟩
    simp only [D, A, S', mem_inter, mem_compl_iff, mem_union, mem_setOf_eq, mem_prod, mem_univ, true_and]
    simp [symmDiff]
    <;> tauto
  let A' : Set (ℝ × E n) := {p | u p.2 > p.1}
  have hA'_meas : MeasurableSet A' := by
    have h1 : Measurable fun (p : ℝ × E n) => u p.2 := hu_meas.comp measurable_snd
    have h2 : Measurable fun (p : ℝ × E n) => p.1 := measurable_fst
    have h3 : MeasurableSet {p : ℝ × E n | p.1 < u p.2} := by exact measurableSet_lt h2 h1
    have hA' : A' = {p : ℝ × E n | p.1 < u p.2} := by
      ext p
      simp only [A', mem_setOf_eq]
      <;> rfl
    rw [hA']; exact h3
  let S'' : Set (ℝ × E n) := {p | p.2 ∈ S}
  have hS''_meas : MeasurableSet S'' := by
    have h : Measurable fun (p : ℝ × E n) => p.2 := measurable_snd
    exact h hS
  let D' : Set (ℝ × E n) := (A' ∩ S''ᶜ) ∪ (A'ᶜ ∩ S'')
  have hD'_meas : MeasurableSet D' :=
    hA'_meas.inter hS''_meas.compl |>.union (hA'_meas.compl.inter hS''_meas)
  have hD'_eq : D' = {p : ℝ × E n | p.2 ∈ symmDiff {y | u y > p.1} S} := by
    ext ⟨s, x⟩
    simp only [D', A', S'', mem_inter, mem_compl_iff, mem_union, mem_setOf_eq]
    simp [symmDiff]
    <;> tauto
  let μ_s : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have h_main_set : MeasurableSet {p : ℝ × E n | p.2 ∈ symmDiff {y | u y > p.1} S} := by
    rw [←hD'_eq]
    exact hD'_meas
  have h_eq1 : (Function.uncurry g) = Set.indicator {p : ℝ × E n | p.2 ∈ symmDiff {y | u y > p.1} S} (fun _ => (1 : ENNReal)) := by
    funext p
    simp [g, f, Set.indicator_apply]
    <;> aesop
  have h_f_meas : AEMeasurable (Function.uncurry g) (Measure.prod μ_s volume) := by
    rw [h_eq1]
    have h_const : Measurable (fun (_ : ℝ × E n) => (1 : ENNReal)) := measurable_const
    have h_ind : Measurable (Set.indicator {p : ℝ × E n | p.2 ∈ symmDiff {y | u y > p.1} S} (fun (_ : ℝ × E n) => (1 : ENNReal))) :=
      Measurable.indicator h_const h_main_set
    exact h_ind.aemeasurable
  have h_tonelli : ∫⁻ (s : ℝ), (∫⁻ (x : E n), g s x) ∂μ_s =
      ∫⁻ (x : E n), (∫⁻ (s : ℝ), g s x ∂μ_s) := by
    exact lintegral_lintegral_swap h_f_meas
  have h_volume_eq : ∀ (s : ℝ), volume (symmDiff {x | u x > s} S) = ∫⁻ (x : E n), g s x := by
    intro s
    have h_meas : MeasurableSet (symmDiff {x | u x > s} S) := by
      have hIoi : MeasurableSet (Set.Ioi s) := isOpen_Ioi.measurableSet
      have h1 : MeasurableSet {x | u x > s} := hu_meas hIoi
      exact h1.symmDiff hS
    have h_g_eq : (g s) = Set.indicator (symmDiff {x | u x > s} S) (fun _ => (1 : ENNReal)) := by
      funext x
      simp [g, f, Set.indicator_apply]
      <;> aesop
    rw [h_g_eq]
    have h3 : ∫⁻ (x : E n), Set.indicator (symmDiff {x | u x > s} S) (fun _ => (1 : ENNReal)) x =
        volume (symmDiff {x | u x > s} S) := by
      have h5 : ∫⁻ (x : E n), Set.indicator (symmDiff {x | u x > s} S) (fun _ => (1 : ENNReal)) x =
          ∫⁻ (x : E n) in (symmDiff {x | u x > s} S), (1 : ENNReal) := by
        exact lintegral_indicator h_meas fun x => 1
      rw [h5]
      exact setLIntegral_one (symmDiff {x | u x > s} S)
    exact h3.symm
  have h_lhs : (∫⁻ (s : ℝ), volume (symmDiff {x | u x > s} S) ∂μ_s) =
      ∫⁻ (x : E n), (∫⁻ (s : ℝ), g s x ∂μ_s) := by
    calc
      (∫⁻ (s : ℝ), volume (symmDiff {x | u x > s} S) ∂μ_s)
        = ∫⁻ (s : ℝ), (∫⁻ (x : E n), g s x) ∂μ_s := by
          congr with s
          exact h_volume_eq s
      _ = ∫⁻ (x : E n), (∫⁻ (s : ℝ), g s x ∂μ_s) := h_tonelli
  have h_pointwise : ∀ (x : E n),
      (∫⁻ (s : ℝ), g s x ∂μ_s) =
      ENNReal.ofReal |u x - Set.indicator S (fun _ => (1 : ℝ)) x| := by
    intro x
    simpa [μ_s, g, f] using pointwise_layer_cake x (h0 x) (h1 x) hS
  have h_rhs_all : ∫⁻ (x : E n), (∫⁻ (s : ℝ), g s x ∂μ_s) =
      ∫⁻ (x : E n), ENNReal.ofReal |u x - Set.indicator S (fun _ => (1 : ℝ)) x| := by
    congr with x
    exact h_pointwise x
  let G : E n → ENNReal := fun x => ENNReal.ofReal |u x - Set.indicator S (fun _ => (1 : ℝ)) x|
  have h_zero_outside : ∀ x ∉ K, G x = 0 := by
    intro x hxK
    have hux : u x = 0 := h_supp x hxK
    have hxS : x ∉ S := by
      intro h
      exact hxK (hS_sub h)
    simp [G, hux, hxS, Set.indicator_apply]
    <;> norm_num
  have h_restrict_eq : ∫⁻ (x : E n), G x = ∫⁻ (x : E n) in K, G x := by
    have h1 : ∫⁻ (x : E n), G x = ∫⁻ (x : E n), Set.indicator K G x := by
      congr with x
      by_cases h : x ∈ K <;> simp [h, Set.indicator_apply, h_zero_outside] <;> tauto
    rw [h1]
    have h2 : ∫⁻ (x : E n), Set.indicator K G x = ∫⁻ (x : E n) in K, G x := by
      exact lintegral_indicator hK G
    exact h2
  have h_goal : ∫⁻ s in Set.Ioc (0 : ℝ) 1, volume (symmDiff {x | u x > s} S) =
      ∫⁻ x in K, ENNReal.ofReal |u x - Set.indicator S (fun _ => (1 : ℝ)) x| := by
    calc
      ∫⁻ s in Set.Ioc (0 : ℝ) 1, volume (symmDiff {x | u x > s} S)
        = ∫⁻ (s : ℝ), volume (symmDiff {x | u x > s} S) ∂μ_s := by rfl
      _ = ∫⁻ (x : E n), (∫⁻ (s : ℝ), g s x ∂μ_s) := h_lhs
      _ = ∫⁻ (x : E n), G x := h_rhs_all
      _ = ∫⁻ (x : E n) in K, G x := h_restrict_eq
      _ = ∫⁻ (x : E n) in K, ENNReal.ofReal |u x - Set.indicator S (fun _ => (1 : ℝ)) x| := by
        have h_eq : (fun x => G x) = (fun x => ENNReal.ofReal |u x - Set.indicator S (fun _ => (1 : ℝ)) x|) := by
          funext x; rfl
        rw [h_eq]
  exact h_goal

end Geometry
