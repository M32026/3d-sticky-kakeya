import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.CoefficientBockstein
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Bockstein Short Exact Sequence

Proves that the chain complex sequence
0 → C_*(X;ℤ) --×2→ C_*(X;ℤ) → C_*(X;Z/2) → 0
is short exact, using AB4 (coproducts are exact in AddCommGrpCat).

## Main result
- `bocksteinShortExact X`: the Bockstein short complex of chain complexes is short exact.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial Preadditive
open TopCat (toSSet)
open BorsukUlam.BackupRoute

namespace BorsukUlam.BackupRoute

universe u

/-!
## Coefficient short exact sequence
-/

/-- The coefficient short exact sequence 0 → ℤ --×2→ ℤ → Z/2 → 0. -/
def coeffShortComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (2 • 𝟙 (AddCommGrpCat.of ℤ)) coeffReductionMap (by
    ext
    simp [coeffReductionMap, AddCommGrpCat.ofHom] <;> decide)

lemma mono_coeffShortComplex_f : Mono coeffShortComplex.f := by
  dsimp only [coeffShortComplex]
  refine' ConcreteCategory.mono_iff_injective_of_preservesPullback (2 • 𝟙 (AddCommGrpCat.of ℤ)) |>.mpr _
  intro a b h
  have h' : (2 : ℤ) * (a : ℤ) = (2 : ℤ) * (b : ℤ) := by
    simpa [smul_eq_mul] using h
  exact mul_left_cancel₀ (show (2 : ℤ) ≠ 0 from by decide) h'

lemma epi_coeffShortComplex_g : Epi coeffShortComplex.g := by
  dsimp only [coeffShortComplex]
  refine' (AddCommGrpCat.epi_iff_surjective coeffReductionMap).mpr _
  intro y
  have h_surj : Function.Surjective (fun (n : ℤ) => (n : ZMod 2)) := ZMod.intCast_surjective
  rcases h_surj y with ⟨z, hz⟩
  refine' ⟨z, _⟩
  simpa [coeffReductionMap, AddCommGrpCat.ofHom] using hz

lemma exact_coeffShortComplex : coeffShortComplex.Exact := by
  dsimp only [coeffShortComplex]
  have h_main : ∀ (x : AddCommGrpCat.of ℤ), coeffReductionMap x = 0 →
      ∃ (y : AddCommGrpCat.of ℤ), (2 • 𝟙 (AddCommGrpCat.of ℤ)) y = x := by
    intro x hx
    have h2 : ((x : ℤ) : ZMod 2) = 0 := by
      simpa [coeffReductionMap, AddCommGrpCat.ofHom] using hx
    have h3 : (2 : ℤ) ∣ (x : ℤ) := by
      have h4 : ((x : ℤ) : ZMod 2) = 0 ↔ (2 : ℤ) ∣ (x : ℤ) :=
        ZMod.intCast_zmod_eq_zero_iff_dvd (x : ℤ) 2
      exact h4.mp h2
    refine' ⟨(x : ℤ) / 2, _⟩
    have h5 : (2 : ℤ) * ((x : ℤ) / 2) = (x : ℤ) := Int.mul_ediv_cancel' h3
    have h6 : (2 • 𝟙 (AddCommGrpCat.of ℤ)) (((x : ℤ) / 2 : ℤ) : AddCommGrpCat.of ℤ) = x := by
      have h7 : ((2 • 𝟙 (AddCommGrpCat.of ℤ)) (((x : ℤ) / 2 : ℤ) : AddCommGrpCat.of ℤ) : AddCommGrpCat.of ℤ) = (x : AddCommGrpCat.of ℤ) := by
        simp [smul_eq_mul, h5]
      exact h7
    exact h6
  exact (ShortComplex.ab_exact_iff (S := coeffShortComplex)).mpr h_main

/-- The coefficient sequence is short exact. -/
lemma coeffShortExact : coeffShortComplex.ShortExact :=
  { exact := exact_coeffShortComplex
    mono_f := mono_coeffShortComplex_f
    epi_g := epi_coeffShortComplex_g }

/-!
## Copower functor exactness (AB4)
-/

/-- The copower functor by type `I`: `R ↦ ∐_{_:I} R`. -/
noncomputable def copowerFunctor (I : Type u) : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  Functor.const (Discrete I) ⋙ colim

instance copowerPreservesFiniteColimits (I : Type u) :
    PreservesFiniteColimits (copowerFunctor I) := by
  dsimp only [copowerFunctor]
  infer_instance

instance copowerPreservesFiniteLimits (I : Type u) :
    PreservesFiniteLimits (copowerFunctor I) := by
  dsimp only [copowerFunctor]
  letI : PreservesFiniteLimits (colim (J := Discrete I) (C := AddCommGrpCat.{u})) :=
    HasExactColimitsOfShape.preservesFiniteLimits (J := Discrete I)
  exact comp_preservesFiniteLimits (Functor.const (Discrete I)) colim

instance (I : Type u) : (copowerFunctor I).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_comp (Functor.const (Discrete I)) colim

instance copowerAdditive (I : Type u) : (copowerFunctor I).Additive := by
  apply Functor.additive_of_preserves_binary_products

/-- The copower functor maps scalar multiplication to scalar multiplication. -/
lemma copower_map_smul (I : Type u) (R : AddCommGrpCat) :
    (copowerFunctor I).map (2 • 𝟙 R) = 2 • 𝟙 ((copowerFunctor I).obj R) := by
  calc
    (copowerFunctor I).map (2 • 𝟙 R) = 2 • (copowerFunctor I).map (𝟙 R) :=
      Functor.map_nsmul (copowerFunctor I)
    _ = 2 • 𝟙 ((copowerFunctor I).obj R) :=
      congrArg (fun f => 2 • f) ((copowerFunctor I).map_id R)

/-!
## Bockstein short exact sequence of chain complexes
-/

variable (X : TopCat)

/-- Abbreviation for the singular simplicial set of X. -/
abbrev SSetX : SSet := TopCat.toSSet.obj X

/-- For each degree n, the evaluation of the Bockstein short complex
    at degree n is short exact. -/
lemma bocksteinDegreewiseShortExact (n : ℕ) :
    ((bocksteinShortComplex X).map (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) n)).ShortExact := by
  let I := (SSetX X) _⦋n⦌
  let F := copowerFunctor I
  let eval_n := HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) n
  let S_eval := (bocksteinShortComplex X).map eval_n
  let S_copower := coeffShortComplex.map F
  have h : S_copower.ShortExact :=
    CategoryTheory.ShortComplex.ShortExact.map_of_exact coeffShortExact F

  have hf : S_eval.f = S_copower.f := by
    change 2 • 𝟙 (F.obj (AddCommGrpCat.of ℤ)) =
      F.map (2 • 𝟙 (AddCommGrpCat.of ℤ))
    exact (copower_map_smul I (AddCommGrpCat.of ℤ)).symm

  have hg : S_eval.g = S_copower.g := by
    change (coeffReduction X).f n = F.map coeffReductionMap
    rfl

  have h_mono : Mono S_eval.f := by
    have h' : Mono S_copower.f := h.mono_f
    rw [hf] at * <;> exact h'

  have h_epi : Epi S_eval.g := by
    have h' : Epi S_copower.g := h.epi_g
    rw [hg] at * <;> exact h'

  have h_exact : S_eval.Exact := by
    have h' : S_copower.Exact := h.exact
    rw [ShortComplex.ab_exact_iff] at h' ⊢
    intro x hx
    have h_main : ∀ (x₂ : S_copower.X₂), (ConcreteCategory.hom S_copower.g) x₂ = 0 →
        ∃ (x₁ : S_copower.X₁), (ConcreteCategory.hom S_copower.f) x₁ = x₂ := h'
    have h_x : (ConcreteCategory.hom S_copower.g) x = 0 := by
      have h_temp : (ConcreteCategory.hom S_eval.g) x = 0 := hx
      exact h_temp
    rcases h_main x h_x with ⟨y, hy⟩
    refine' ⟨y, _⟩
    have h_eqf : S_eval.f = S_copower.f := hf
    rw [h_eqf]
    exact hy

  exact { exact := h_exact, mono_f := h_mono, epi_g := h_epi }

/-- The Bockstein short complex of singular chain complexes is short exact:
    0 → C_*(X;ℤ) --×2→ C_*(X;ℤ) → C_*(X;Z/2) → 0. -/
theorem bocksteinShortExact (X : TopCat) :
    (bocksteinShortComplex X).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact
    (bocksteinShortComplex X)
    (bocksteinDegreewiseShortExact X)

end BorsukUlam.BackupRoute
