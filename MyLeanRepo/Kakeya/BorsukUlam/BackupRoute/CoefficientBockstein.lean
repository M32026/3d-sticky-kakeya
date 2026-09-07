module

public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace.StdSphereHomology
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace.TopSphereHomology
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Coefficient Bockstein Sequence for Singular Homology

Constructs the short exact sequence of singular chain complexes:
  0 → C_*(X; ℤ) --2→ C_*(X; ℤ) → C_*(X; Z/2) → 0

## Main Definitions
- `coeffReductionMap`: ℤ → Z/2
- `coeffReduction`: C_*(X;ℤ) → C_*(X;Z/2)
- `multTwo`: multiplication by 2 on C_*(X;ℤ)
- `bocksteinShortComplex`: the short complex of chain complexes
- `coeffSES_shortExact`: coefficient SES is short exact

## Whiteprint Node
- `bockstein_short_exact`
-/

@[expose] public section
noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial Preadditive
open TopCat (toSSet)

namespace BorsukUlam.BackupRoute

/-- The coefficient ring Z/2 as an object of AddCommGrpCat. -/
abbrev R2 : AddCommGrpCat := AddCommGrpCat.of (ZMod 2)

variable (X : TopCat)

/-- The coefficient reduction map ℤ → Z/2 as a morphism in AddCommGrpCat. -/
def coeffReductionMap : AddCommGrpCat.of ℤ ⟶ R2 :=
  AddCommGrpCat.ofHom
    { toFun := fun n : ℤ => (n : ZMod 2)
      map_zero' := by simp
      map_add' := by intro a b; simp [add_comm] }

/-- Multiplication by 2 on ℤ as a morphism in AddCommGrpCat. -/
def multTwoMap : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ :=
  AddCommGrpCat.ofHom
    { toFun := fun n : ℤ => 2 * n
      map_zero' := by simp
      map_add' := by intro a b; simp [mul_add] <;> ring }

lemma multTwoMap_comp_coeffReductionMap : multTwoMap ≫ coeffReductionMap = 0 := by
  have h : ∀ (z : ℤ), (multTwoMap ≫ coeffReductionMap) z = 0 := by
    intro z
    have h6 : (2 * z : ZMod 2) = 0 := by
      have h7 : (2 : ZMod 2) = 0 := by decide
      rw [show (2 * z : ZMod 2) = (2 : ZMod 2) * (z : ZMod 2) from by simp]
      rw [h7, zero_mul]
    simpa [multTwoMap, coeffReductionMap] using h6
  exact AddCommGrpCat.ext h

/-- The coefficient short complex 0 → ℤ --2→ ℤ → Z/2 → 0. -/
def coeffSES : ShortComplex AddCommGrpCat :=
  ShortComplex.mk multTwoMap coeffReductionMap multTwoMap_comp_coeffReductionMap

lemma coeffSES_mono : Mono multTwoMap := by
  have h : Function.Injective multTwoMap := by
    intro x y h
    simpa [multTwoMap] using mul_left_cancel₀ (show (2 : ℤ) ≠ 0 from by norm_num) h
  exact (AddCommGrpCat.mono_iff_injective multTwoMap).mpr h

lemma coeffSES_epi : Epi coeffReductionMap := by
  have h : Function.Surjective coeffReductionMap := by
    intro y
    have h2 : y = 0 ∨ y = 1 := by fin_cases y <;> tauto
    rcases h2 with (h2 | h2)
    · exact ⟨0, by simp [coeffReductionMap, h2]⟩
    · exact ⟨1, by simp [coeffReductionMap, h2]⟩
  exact (AddCommGrpCat.epi_iff_surjective coeffReductionMap).mpr h

lemma coeffSES_exact : coeffSES.Exact := by
  rw [CategoryTheory.ShortComplex.ab_exact_iff_ker_le_range]
  intro (x : ℤ) hx
  have h1 : (x : ZMod 2) = 0 := by
    have h2 : coeffReductionMap.hom x = 0 := hx
    simpa [coeffReductionMap] using h2
  have h3 : (2 : ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mp h1
  rcases h3 with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  have h4 : multTwoMap.hom y = 2 * y := by rfl
  have h5 : multTwoMap.hom y = x := by
    rw [h4]
    exact hy.symm
  exact h5

/-- The coefficient SES is short exact. -/
lemma coeffSES_shortExact : coeffSES.ShortExact :=
  CategoryTheory.ShortComplex.ShortExact.mk' coeffSES_exact coeffSES_mono coeffSES_epi

/-- The coefficient reduction chain map C_*(X; ℤ) → C_*(X; Z/2). -/
noncomputable def coeffReduction (X : TopCat) :
    singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) X ⟶
    singularChainComplex' AddCommGrpCat R2 X :=
  ((SSet.chainComplexFunctor AddCommGrpCat).map coeffReductionMap).app (TopCat.toSSet.obj X)

/-- Multiplication by 2 on C_*(X; ℤ). -/
noncomputable def multTwo (X : TopCat) :
    singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) X ⟶
    singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) X :=
  2 • 𝟙 _

/-- Proof that multiplication by 2 followed by coefficient reduction is zero. -/
lemma multTwo_comp_coeffReduction (X : TopCat) :
    multTwo X ≫ coeffReduction X = 0 := by
  let F := SSet.chainComplexFunctor AddCommGrpCat
  let f : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ := 2 • 𝟙 _
  let g : AddCommGrpCat.of ℤ ⟶ R2 := coeffReductionMap
  have hfg : f ≫ g = 0 := by
    have h : ∀ (z : ℤ), (f ≫ g) z = 0 := by
      intro z
      have h6 : (2 * z : ZMod 2) = 0 := by
        have h7 : (2 : ZMod 2) = 0 := by decide
        rw [show (2 * z : ZMod 2) = (2 : ZMod 2) * (z : ZMod 2) from by simp]
        rw [h7, zero_mul]
      simpa [f, g, coeffReductionMap] using h6
    exact AddCommGrpCat.ext h
  have h1 : F.map f ≫ F.map g = 0 := by
    calc
      F.map f ≫ F.map g = F.map (f ≫ g) := by rw [←F.map_comp]
      _ = F.map 0 := by rw [hfg]
      _ = 0 := by simp
  have h2 : (F.map f ≫ F.map g).app (TopCat.toSSet.obj X) = 0 := by
    rw [h1] <;> simp
  have h31 : F.map f = 2 • 𝟙 (F.obj (AddCommGrpCat.of ℤ)) := by
    dsimp only [f]
    rw [Functor.map_smul] <;> simp
  have h3 : (F.map f).app (TopCat.toSSet.obj X) = multTwo X := by
    rw [h31] <;> simp [multTwo] <;> rfl
  have h4 : (F.map g).app (TopCat.toSSet.obj X) = coeffReduction X := by rfl
  have h5 : (F.map f ≫ F.map g).app (TopCat.toSSet.obj X) =
      (F.map f).app (TopCat.toSSet.obj X) ≫ (F.map g).app (TopCat.toSSet.obj X) := by rfl
  rw [h5, h3, h4] at h2
  exact h2

/-- The short complex C_*(X; ℤ) --2→ C_*(X; ℤ) → C_*(X; Z/2). -/
noncomputable def bocksteinShortComplex (X : TopCat) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (multTwo X) (coeffReduction X) (multTwo_comp_coeffReduction X)

end BorsukUlam.BackupRoute

end
