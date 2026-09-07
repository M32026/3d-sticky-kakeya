import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Tactic

/-!
# Coordinate equivalences between EuclideanSpace and product types

Provides measure-preserving equivalences and the twisted-projection
diagram commutativity lemma needed by compact_tube_twisted_projection_area.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

def coordEquiv2 (p : Point2) : ℝ × ℝ := (p 0, p 1)

lemma measurePreserving_coordEquiv2 :
    MeasurePreserving coordEquiv2 volume volume := by
  let ofLp : Point2 → (Fin 2 → ℝ) := WithLp.ofLp
  have h1 : MeasurePreserving ofLp volume volume :=
    PiLp.volume_preserving_ofLp (Fin 2)
  let finTwo : (Fin 2 → ℝ) → ℝ × ℝ :=
    MeasurableEquiv.finTwoArrow (α := ℝ)
  have h2 : MeasurePreserving finTwo volume volume :=
    volume_preserving_finTwoArrow ℝ
  have h3 : coordEquiv2 = finTwo ∘ ofLp := by
    funext p
    rfl
  rw [h3]
  exact h2.comp h1

@[fun_prop]
lemma continuous_coordEquiv2 : Continuous coordEquiv2 := by
  have h1 : Continuous (fun p : Point2 => p (0 : Fin 2)) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)
  have h2 : Continuous (fun p : Point2 => p (1 : Fin 2)) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2)
  exact Continuous.prodMk h1 h2

lemma injective_coordEquiv2 : Function.Injective coordEquiv2 := by
  intro a b h
  have h4 : a 0 = b 0 ∧ a 1 = b 1 := by
    simpa [coordEquiv2, Prod.ext_iff] using h
  ext i
  fin_cases i <;> tauto

def coordEquiv3 (p : Point3) : ℝ × (ℝ × ℝ) :=
  (p 2, (p 0, p 1))

lemma measurePreserving_coordEquiv3 :
    MeasurePreserving coordEquiv3 volume volume := by
  let ofLp : Point3 → (Fin 3 → ℝ) := WithLp.ofLp
  have h1 : MeasurePreserving ofLp volume volume :=
    PiLp.volume_preserving_ofLp (Fin 3)
  let split : (Fin 3 → ℝ) → ℝ × (Fin 2 → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  have h2 : MeasurePreserving split volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  let finTwo : (Fin 2 → ℝ) → ℝ × ℝ :=
    MeasurableEquiv.finTwoArrow (α := ℝ)
  have h3 : MeasurePreserving finTwo volume volume :=
    volume_preserving_finTwoArrow ℝ
  let second : ℝ × (Fin 2 → ℝ) → ℝ × (ℝ × ℝ) :=
    Prod.map id finTwo
  have h4 : MeasurePreserving second volume volume :=
    (MeasurePreserving.id volume).prod h3
  have h5 : coordEquiv3 = second ∘ split ∘ ofLp := by
    funext p
    have h_ofLp : ∀ i : Fin 3, (ofLp p) i = p i := by
      intro i
      rfl
    let g : Fin 2 → ℝ :=
      fun j : Fin 2 => (ofLp p) (Fin.succAbove (2 : Fin 3) j)
    have hg0 : g 0 = (ofLp p) 0 := by
      simp [g, Fin.succAbove] <;> decide
    have hg1 : g 1 = (ofLp p) 1 := by
      simp [g, Fin.succAbove] <;> decide
    have h_main :
        (second ∘ split ∘ ofLp) p = coordEquiv3 p := by
      dsimp only [Function.comp_apply]
      have hs : split (ofLp p) = ((ofLp p) 2, g) := by
        rfl
      rw [hs]
      have hsecond :
          second ((ofLp p) 2, g) =
            ((ofLp p) 2, (g 0, g 1)) := by
        simp [second, MeasurableEquiv.finTwoArrow] <;> rfl
      rw [hsecond, hg0, hg1]
      simp [coordEquiv3, h_ofLp]
    exact h_main.symm
  rw [h5]
  exact h4.comp (h2.comp h1)

@[fun_prop]
lemma continuous_coordEquiv3 : Continuous coordEquiv3 := by
  have h1 : Continuous (fun p : Point3 => p (2 : Fin 3)) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  have h2 : Continuous (fun p : Point3 => p (0 : Fin 3)) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)
  have h3 : Continuous (fun p : Point3 => p (1 : Fin 3)) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3)
  exact Continuous.prodMk h1 (Continuous.prodMk h2 h3)

lemma injective_coordEquiv3 : Function.Injective coordEquiv3 := by
  intro a b h
  have h4 : a 2 = b 2 ∧ a 0 = b 0 ∧ a 1 = b 1 := by
    simpa [coordEquiv3, Prod.ext_iff] using h
  ext i
  fin_cases i <;> tauto

lemma twistedProjection_coordEquiv_diagram
    (f : SlopeFunction) (p : Point3) :
    coordEquiv2 (twistedProjection f p) =
      ((coordEquiv3 p).2.1 +
          f (coordEquiv3 p).1 * (coordEquiv3 p).2.2,
        (coordEquiv3 p).1) := by
  simp [coordEquiv2, coordEquiv3, twistedProjection]
  <;> rfl

lemma volume_image_of_injective_measurePreserving
    {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β]
    [T2Space α] [T2Space β]
    [MeasureSpace α] [MeasureSpace β]
    [BorelSpace α] [BorelSpace β]
    {f : α → β}
    (hcont : Continuous f)
    (hmp : MeasurePreserving f volume volume)
    (hinj : Function.Injective f)
    {A : Set α} (hA : IsCompact A) :
    volume (f '' A) = volume A := by
  have h_img_compact : IsCompact (f '' A) := hA.image hcont
  have h_img_meas : MeasurableSet (f '' A) :=
    h_img_compact.measurableSet
  have h1 : Measure.map f volume = volume := hmp.map_eq
  have h2 :
      volume (f '' A) = Measure.map f volume (f '' A) := by
    rw [h1]
  rw [h2, Measure.map_apply hmp.measurable h_img_meas]
  rw [hinj.preimage_image]

end Kakeya.Assouad
