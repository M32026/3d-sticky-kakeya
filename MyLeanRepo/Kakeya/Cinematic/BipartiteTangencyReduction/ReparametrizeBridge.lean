import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.Reparametrize
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Lenses

/-!
# Bridge from reparametrized families to graph pseudo-circle families

Lifts the "at most two intersections" and "all intersections transverse"
properties from a family on `I.carrier` to the reparametrized family on
`UnitPoint`.

The map `phiMap I : UnitPoint → I.carrier` is a strictly increasing bijection
when `0 < I.length`, so intersection and transversality properties transfer
via `reparam_intersection_iff` and `reparam_transverse_iff`.
-/

noncomputable section

namespace Kakeya.Cinematic

open C2Function

local instance instDecidableEqC2FunctionReparamBridge : DecidableEq C2Function :=
  Classical.decEq _

/-- `phiMap I x` always lands in `I.carrier`. -/
lemma phiMap_mem_carrier (I : ParameterInterval) (x : UnitPoint) :
    phiMap I x ∈ I.carrier := by
  have h1 : 0 ≤ (x : ℝ) := x.property.1
  have h2 : (x : ℝ) ≤ 1 := x.property.2
  have h3 : 0 ≤ I.length := I.length_nonneg
  have h4 : I.left ≤ I.left + (x : ℝ) * I.length := by
    have h5 : 0 ≤ (x : ℝ) * I.length := by positivity
    linarith
  have h6 : I.left + (x : ℝ) * I.length ≤ I.right := by
    have h7 : (x : ℝ) * I.length ≤ I.length := by
      nlinarith
    have h8 : I.left + (x : ℝ) * I.length ≤ I.left + I.length := by gcongr
    have h9 : I.left + I.length = I.right := by
      simp [ParameterInterval.length] <;> ring
    rw [h9] at h8
    exact h8
  exact ⟨h4, h6⟩

/-- `phiMap I` is strictly increasing when `I.length > 0`. -/
lemma phiMap_strictMono (I : ParameterInterval) (hI : 0 < I.length) :
    StrictMono (fun x : UnitPoint => (phiMap I x : ℝ)) := by
  intro x y hxy
  have h : (x : ℝ) < (y : ℝ) := hxy
  dsimp only [phiMap]
  have h' : I.left + (x : ℝ) * I.length < I.left + (y : ℝ) * I.length := by
    have hmul : (x : ℝ) * I.length < (y : ℝ) * I.length := by
      exact mul_lt_mul_of_pos_right h hI
    linarith
  exact h'

/--
A finite family with at most two intersections and all transverse intersections
on `I.carrier` becomes a graph pseudo-circle family after reparametrization
over `I`.
-/
lemma reparametrized_is_pseudo_circle
    {family : Finset C2Function} {I : ParameterInterval} (hI : 0 < I.length)
    (h_at_most_two : ∀ f ∈ family, ∀ g ∈ family, f ≠ g →
      ∀ y₁ y₂ y₃ : UnitPoint, y₁ ∈ I.carrier → y₂ ∈ I.carrier → y₃ ∈ I.carrier →
        (y₁ : ℝ) < (y₂ : ℝ) → (y₂ : ℝ) < (y₃ : ℝ) →
        f y₁ = g y₁ → f y₂ = g y₂ → f y₃ = g y₃ → False)
    (h_transverse : ∀ f ∈ family, ∀ g ∈ family, f ≠ g →
      ∀ y ∈ I.carrier, f y = g y → f.firstDeriv y ≠ g.firstDeriv y) :
    IsGraphPseudoCircleFamily (family.image (fun f => f.reparam I)) := by
  classical
  have h_phi_in_carrier : ∀ (x : UnitPoint), phiMap I x ∈ I.carrier :=
    phiMap_mem_carrier I
  have h_phi_mono : StrictMono (fun x : UnitPoint => (phiMap I x : ℝ)) :=
    phiMap_strictMono I hI

  constructor
  · -- At most two intersections
    intro F' hF' G' hG' hne
    intro x₁ x₂ x₃ h12 h23 eq1 eq2 eq3
    rcases Finset.mem_image.mp hF' with ⟨f, hf, rfl⟩
    rcases Finset.mem_image.mp hG' with ⟨g, hg, rfl⟩
    have hfg : f ≠ g := by
      intro h
      rw [h] at hne
      exact hne rfl
    let y1 := phiMap I x₁
    let y2 := phiMap I x₂
    let y3 := phiMap I x₃
    have hy1 : y1 ∈ I.carrier := h_phi_in_carrier x₁
    have hy2 : y2 ∈ I.carrier := h_phi_in_carrier x₂
    have hy3 : y3 ∈ I.carrier := h_phi_in_carrier x₃
    have h_y12 : (y1 : ℝ) < (y2 : ℝ) := h_phi_mono h12
    have h_y23 : (y2 : ℝ) < (y3 : ℝ) := h_phi_mono h23
    have eq1' : f y1 = g y1 := (reparam_intersection_iff f g I x₁).mp eq1
    have eq2' : f y2 = g y2 := (reparam_intersection_iff f g I x₂).mp eq2
    have eq3' : f y3 = g y3 := (reparam_intersection_iff f g I x₃).mp eq3
    exact h_at_most_two f hf g hg hfg y1 y2 y3 hy1 hy2 hy3 h_y12 h_y23 eq1' eq2' eq3'
  · -- All intersections transverse
    intro F' hF' G' hG' hne x h_eq
    rcases Finset.mem_image.mp hF' with ⟨f, hf, rfl⟩
    rcases Finset.mem_image.mp hG' with ⟨g, hg, rfl⟩
    have hfg : f ≠ g := by
      intro h
      rw [h] at hne
      exact hne rfl
    let y := phiMap I x
    have hy : y ∈ I.carrier := h_phi_in_carrier x
    have h_eq' : f y = g y := (reparam_intersection_iff f g I x).mp h_eq
    have h_trans : f.firstDeriv y ≠ g.firstDeriv y :=
      h_transverse f hf g hg hfg y hy h_eq'
    exact (reparam_transverse_iff f g I hI x).mpr h_trans

end Kakeya.Cinematic

end
