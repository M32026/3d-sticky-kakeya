import MyLeanRepo.Kakeya.Cinematic.WZ2Input
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Translation invariance of cinematic structures

Vertical translation `f ↦ f + c` preserves cinematic family conditions,
δ-separation, Frostman bounds, and shifts the multiplicity function in y.
-/

noncomputable section

open Kakeya.Cinematic MeasureTheory Set

namespace Kakeya.Cinematic

namespace C2Function

/-- Translate a C2Function vertically by `c`. -/
def translate (f : C2Function) (c : ℝ) : C2Function :=
  let value' : C(UnitPoint, ℝ) := ⟨fun x => f x + c, by continuity⟩
  let firstDeriv' : C(UnitPoint, ℝ) := f.firstDeriv
  let secondDeriv' : C(UnitPoint, ℝ) := f.secondDeriv
  let ext : ℝ → ℝ := f.extension
  let ext' : ℝ → ℝ := fun x => ext x + c
  have hdiff : ContDiff ℝ 2 ext := f.extension_contDiff
  have h_const : ContDiff ℝ 2 (fun (_ : ℝ) => c) := contDiff_const
  have hdiff' : ContDiff ℝ 2 ext' := by
    have h : ContDiff ℝ 2 (fun x : ℝ => ext x + c) := hdiff.add h_const
    simpa [ext'] using h
  have hdiff_diff : Differentiable ℝ ext :=
    ContDiff.differentiable hdiff (by norm_num)
  have hder : ∀ (x : ℝ), DifferentiableAt ℝ ext x :=
    fun x => hdiff_diff.differentiableAt
  have hval' : ∀ (x : UnitPoint), ext' x = value' x := by
    intro x
    dsimp only [ext', value']
    have h1 : ext x = f x := f.extension_eq_value x
    have h2 : ext x + c = f x + c := by rw [h1]
    exact h2
  have hderiv' : ∀ (x : UnitPoint), deriv ext' x = firstDeriv' x := by
    intro x
    let y : ℝ := x
    have h_has : HasDerivAt ext (deriv ext y) y := (hder y).hasDerivAt
    have h' : HasDerivAt ext' (deriv ext y) y :=
      (hasDerivAt_add_const_iff c).mpr h_has
    have h_eq : deriv ext' y = deriv ext y := h'.deriv
    rw [h_eq, f.deriv_extension_eq_firstDeriv x]
  have hderiv2' : ∀ (x : UnitPoint), deriv (deriv ext') x = secondDeriv' x := by
    intro x
    let y : ℝ := x
    have h1 : deriv ext' = deriv ext := by
      funext z
      have h_has : HasDerivAt ext (deriv ext z) z := (hder z).hasDerivAt
      have h' : HasDerivAt ext' (deriv ext z) z :=
        (hasDerivAt_add_const_iff c).mpr h_has
      exact h'.deriv
    rw [h1, f.secondDeriv_extension_eq_secondDeriv x]
  { value := value', firstDeriv := firstDeriv', secondDeriv := secondDeriv',
    hasExtension := ⟨ext', hdiff', hval', hderiv', hderiv2'⟩ }

@[simp]
theorem translate_apply (f : C2Function) (c : ℝ) (x : UnitPoint) :
    (f.translate c) x = f x + c := by
  rfl

@[simp]
theorem translate_firstDeriv (f : C2Function) (c : ℝ) :
    (f.translate c).firstDeriv = f.firstDeriv := by
  rfl

@[simp]
theorem translate_secondDeriv (f : C2Function) (c : ℝ) :
    (f.translate c).secondDeriv = f.secondDeriv := by
  rfl

theorem translate_injective (c : ℝ) :
    Function.Injective (fun f : C2Function => f.translate c) := by
  intro f g h
  have h_val : (f.translate c).value = (g.translate c).value :=
    congr_arg (fun x : C2Function => x.value) h
  have h_fd : (f.translate c).firstDeriv = (g.translate c).firstDeriv :=
    congr_arg (fun x : C2Function => x.firstDeriv) h
  have h_sd : (f.translate c).secondDeriv = (g.translate c).secondDeriv :=
    congr_arg (fun x : C2Function => x.secondDeriv) h
  have h5 : ∀ (x : UnitPoint), f.value x = g.value x := by
    intro x
    have h6 : (f.translate c).value x = (g.translate c).value x := by
      rw [h_val]
    have h7 : f.value x + c = g.value x + c := by
      simpa [translate_apply] using h6
    exact add_right_cancel h7
  have h3 : f.value = g.value := ContinuousMap.ext h5
  have h_jet : C2Function.toJet f = C2Function.toJet g := by
    dsimp only [C2Function.toJet]
    apply Prod.ext
    · exact h3
    · apply Prod.ext
      · exact h_fd
      · exact h_sd
  exact C2Function.toJet_injective h_jet

theorem translate_dist (f g : C2Function) (c : ℝ) :
    dist (f.translate c) (g.translate c) = dist f g := by
  have h_val : dist (f.translate c).value (g.translate c).value = dist f.value g.value := by
    have h_eq : ∀ (x : UnitPoint), dist ((f.translate c).value x) ((g.translate c).value x) = dist (f.value x) (g.value x) := by
      intro x
      simp [translate_apply, Real.dist_eq]
    rw [ContinuousMap.dist_eq_iSup, ContinuousMap.dist_eq_iSup]
    congr with x
    exact h_eq x
  have h_fd : dist (f.translate c).firstDeriv (g.translate c).firstDeriv = dist f.firstDeriv g.firstDeriv := by
    rfl
  have h_sd : dist (f.translate c).secondDeriv (g.translate c).secondDeriv = dist f.secondDeriv g.secondDeriv := by
    rfl
  have h_main : dist (C2Function.toJet (f.translate c)) (C2Function.toJet (g.translate c)) =
      dist (C2Function.toJet f) (C2Function.toJet g) := by
    simp [C2Function.toJet, Prod.dist_eq, h_val]
  exact h_main

theorem translate_c2Distance (f g : C2Function) (c : ℝ) :
    c2Distance (f.translate c) (g.translate c) = c2Distance f g :=
  translate_dist f g c

theorem translate_jetGap (f g : C2Function) (c : ℝ) (x : UnitPoint) :
    jetGap (f.translate c) (g.translate c) x = jetGap f g x := by
  simp [jetGap, translate_apply]

/-- Translation by `-c` is the inverse of translation by `c`. -/
theorem translate_neg_cancel (f : C2Function) (c : ℝ) :
    (f.translate c).translate (-c) = f := by
  apply C2Function.toJet_injective
  dsimp only [C2Function.toJet]
  apply Prod.ext
  · ext x
    simp [C2Function.translate_apply]
  · apply Prod.ext
    · rfl
    · rfl

end C2Function

/-- The image of a set under vertical translation. -/
def translateSet (family : Set C2Function) (c : ℝ) : Set C2Function :=
  (fun f => f.translate c) '' family

/-- Translating a cinematic family vertically preserves the property. -/
theorem IsCinematicFamily.translate {family : Set C2Function} {K D : ℝ}
    (h : IsCinematicFamily family K D) (c : ℝ) :
    IsCinematicFamily (translateSet family c) K D := by
  have h1 : ∀ ⦃f' : C2Function⦄, f' ∈ translateSet family c →
      ∀ ⦃g' : C2Function⦄, g' ∈ translateSet family c →
        c2Distance f' g' ≤ K := by
    intro f' hf' g' hg'
    rcases hf' with ⟨f, hf, rfl⟩
    rcases hg' with ⟨g, hg, rfl⟩
    have h := h.1 hf hg
    rwa [C2Function.translate_c2Distance]
  have h2 : ∀ ⦃f' : C2Function⦄, f' ∈ translateSet family c →
      ∀ r : ℝ, 0 < r →
        ∃ centers : Set C2Function, centers.Finite ∧ centers ⊆ translateSet family c ∧
          (centers.ncard : ℝ) ≤ D ∧
          ∀ ⦃g' : C2Function⦄, g' ∈ translateSet family c →
            c2Distance f' g' ≤ r →
            ∃ h' ∈ centers, c2Distance h' g' ≤ r / 2 := by
    intro f' hf' r hr
    rcases hf' with ⟨f, hf, rfl⟩
    rcases h.2.1 hf r hr with ⟨centers, hfin, hsub, hcard, hcover⟩
    let centers' := (fun g : C2Function => g.translate c) '' centers
    have hsub' : centers' ⊆ translateSet family c := by
      intro z hz
      rcases hz with ⟨h, hh, rfl⟩
      exact ⟨h, hsub hh, rfl⟩
    refine' ⟨centers', hfin.image _, hsub', _, _⟩
    · have hcard' : centers'.ncard = centers.ncard :=
        Set.ncard_image_of_injective centers (C2Function.translate_injective c)
      rw [hcard']
      exact hcard
    · intro g' hg' hd
      rcases hg' with ⟨g, hg, rfl⟩
      have hdist : c2Distance f g ≤ r := by
        rwa [C2Function.translate_c2Distance] at hd
      rcases hcover hg hdist with ⟨h, hh, hle⟩
      have h_in : h.translate c ∈ centers' := ⟨h, hh, rfl⟩
      exact ⟨h.translate c, h_in, by rwa [C2Function.translate_c2Distance]⟩
  have h3 : ∀ ⦃f' : C2Function⦄, f' ∈ translateSet family c →
      ∀ ⦃g' : C2Function⦄, g' ∈ translateSet family c →
        ∀ x : UnitPoint, K⁻¹ * c2Distance f' g' ≤ jetGap f' g' x := by
    intro f' hf' g' hg' x
    rcases hf' with ⟨f, hf, rfl⟩
    rcases hg' with ⟨g, hg, rfl⟩
    have h := h.2.2 hf hg x
    rwa [C2Function.translate_c2Distance, C2Function.translate_jetGap]
  exact ⟨h1, h2, h3⟩

namespace FiniteFunctionFamily

/-- Translate a finite function family vertically. -/
def translate (F : FiniteFunctionFamily) (c : ℝ) : FiniteFunctionFamily :=
  { carrier := (fun f => f.translate c) '' F.carrier,
    finite := F.finite.image _ }

theorem translate_card (F : FiniteFunctionFamily) (c : ℝ) :
    (F.translate c).card = F.card := by
  dsimp only [translate, card]
  rw [Set.ncard_image_of_injective _ (C2Function.translate_injective c)]

end FiniteFunctionFamily

/-- δ-separation is preserved under vertical translation. -/
theorem IsDeltaSeparated_translate {F : FiniteFunctionFamily} {δ : ℝ}
    (h : F.IsDeltaSeparated δ) (c : ℝ) :
    (F.translate c).IsDeltaSeparated δ := by
  intro f' hf' g' hg' hne
  rcases hf' with ⟨f, hf, rfl⟩
  rcases hg' with ⟨g, hg, rfl⟩
  have hfg : f ≠ g := by
    intro h_eq
    have h : f.translate c = g.translate c := by rw [h_eq]
    exact hne h
  have h := h hf hg hfg
  rwa [C2Function.translate_dist]

/-- Frostman bound is preserved under vertical translation. -/
theorem HasFrostmanBound_translate {F : FiniteFunctionFamily} {δ ε ζ : ℝ}
    (h : HasFrostmanBound F δ ε ζ) (c : ℝ) :
    HasFrostmanBound (F.translate c) δ ε ζ := by
  intro center' r hr
  let center := center'.translate (-c)
  have h_center' : center'.translate (-c) = center := rfl
  have h_center : center.translate c = center' := by
    apply C2Function.toJet_injective
    dsimp only [C2Function.toJet, center]
    apply Prod.ext
    · ext x
      simp [C2Function.translate_apply]
    · apply Prod.ext <;> rfl
  have h_bij : (fun f : C2Function => f.translate c) '' (F.carrier ∩ c2Ball center r) =
      (F.translate c).carrier ∩ c2Ball center' r := by
    ext g'
    simp only [Set.mem_image, Set.mem_inter_iff]
    constructor
    · rintro ⟨g, ⟨hg1, hg2⟩, rfl⟩
      have hg2' : dist g center ≤ r := by rwa [mem_c2Ball] at hg2
      have h_eq : dist (g.translate c) center' = dist g center := by
        rw [←h_center]
        exact C2Function.translate_c2Distance g center c
      have h_goal : dist (g.translate c) center' ≤ r := by
        rw [h_eq]
        exact hg2'
      exact ⟨⟨g, hg1, rfl⟩, by rwa [mem_c2Ball]⟩
    · rintro ⟨⟨g, hg1, rfl⟩, hg2⟩
      have hg2' : dist (g.translate c) center' ≤ r := by rwa [mem_c2Ball] at hg2
      have h_eq : dist (g.translate c) center' = dist g center := by
        rw [←h_center]
        exact C2Function.translate_c2Distance g center c
      have h_goal : dist g center ≤ r := by
        rw [←h_eq]
        exact hg2'
      refine' ⟨g, ⟨hg1, by rwa [mem_c2Ball]⟩, rfl⟩
  have h_equiv : ((F.translate c).carrier ∩ c2Ball center' r).ncard =
      (F.carrier ∩ c2Ball center r).ncard := by
    rw [←h_bij]
    rw [Set.ncard_image_of_injective _ (C2Function.translate_injective c)]
  rw [h_equiv]
  exact h center r hr

/-- A fixed Katz--Tao bound is preserved under vertical translation. -/
theorem HasKatzTaoBound_translate {F : FiniteFunctionFamily} {δ C : ℝ}
    (h : F.HasKatzTaoBound δ C) (c : ℝ) :
    (F.translate c).HasKatzTaoBound δ C := by
  constructor
  · rw [FiniteFunctionFamily.translate_card]
    exact h.1
  · intro center' r hδr hr1
    let center := center'.translate (-c)
    have h_center : center.translate c = center' := by
      apply C2Function.toJet_injective
      dsimp only [C2Function.toJet, center]
      apply Prod.ext
      · ext x
        simp [C2Function.translate_apply]
      · apply Prod.ext <;> rfl
    have h_bij : (fun f : C2Function => f.translate c) ''
        (F.carrier ∩ c2Ball center r) =
        (F.translate c).carrier ∩ c2Ball center' r := by
      ext g'
      simp only [Set.mem_image, Set.mem_inter_iff]
      constructor
      · rintro ⟨g, ⟨hg1, hg2⟩, rfl⟩
        refine ⟨⟨g, hg1, rfl⟩, ?_⟩
        rw [mem_c2Ball, ← h_center, C2Function.translate_c2Distance]
        rwa [mem_c2Ball] at hg2
      · rintro ⟨⟨g, hg1, rfl⟩, hg2⟩
        refine ⟨g, ⟨hg1, ?_⟩, rfl⟩
        rw [mem_c2Ball]
        rw [mem_c2Ball, ← h_center, C2Function.translate_c2Distance] at hg2
        exact hg2
    have h_equiv : ((F.translate c).carrier ∩ c2Ball center' r).ncard =
        (F.carrier ∩ c2Ball center r).ncard := by
      rw [← h_bij, Set.ncard_image_of_injective _ (C2Function.translate_injective c)]
    rw [h_equiv]
    exact h.2 center r hδr hr1

end Kakeya.Cinematic
