/-
# H_1(D(S^1)) ≅ Z/2 — Base Case

Proves H_1(D(S^1)) ≅ Z/2 using the quotient map to RP^1.

## Proof

1. The quotient chain map q : C(S^1) → C(RP^1) has kernel D = im(1 + a_#)
   and is surjective (lifting property).
2. The transfer corestriction p : C(S^1) → D also has kernel D and is surjective.
3. Since both are epi cokernels of the inclusion D → C(S^1), their
   codomains are isomorphic: D ≅ C(RP^1) as chain complexes.
4. RP^1 ≅ S^1 via the squaring map through the complex unit circle.
5. Therefore H_1(D) ≅ H_1(RP^1) ≅ H_1(S^1) ≅ Z/2.

## Whiteprint Node
- istar_ne_zero_base
-/

import MyLeanRepo.Kakeya.BorsukUlam.QuotientSES
import MyLeanRepo.Kakeya.BorsukUlam.QuotientKernel
import MyLeanRepo.Kakeya.BorsukUlam.TransferFull
import MyLeanRepo.Kakeya.BorsukUlam.TransferInstantiation
import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.RealProjectiveSpace
import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.CategoryBridge
import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.SphereHomologyZ2Bockstein
import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.Degree.SphereOneCircle
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial Preadditive
open Vendored.AlgebraicTopology.Degree
open AlgebraicTopology.StdSphereHomology
open BorsukUlamBackup
open BorsukUlam.BackupRoute
open BorsukUlam.QuotientSES

namespace BorsukUlam.BaseCaseH1

variable {n : ℕ}

/-! ### Surjectivity of quotient chain map -/

/-- The quotient chain map is epi in every degree.

Proof: every singular simplex of RP^n lifts to S^n, so every coproduct
injection into C_k(RP^n) factors through the quotient map. Since the
injections are jointly epi (`SSet.chainComplex_hom_ext`), the quotient
map is epi. -/
lemma quotientChainMap_epi (n k : ℕ) :
    Epi ((quotientChainMap n).f k) := by
  let X_S := sphereSSet n
  let X_RP := BorsukUlam.QuotientKernel.rpSSet n
  let ι_S := SingularSimplices n k
  let ι_RP := BorsukUlam.QuotientKernel.RPSingularSimplices n k
  let R2 := ModuleCat.of (ZMod 2) (ZMod 2)
  let π_simplex : ι_S → ι_RP := BorsukUlam.QuotientKernel.quotientSimplexMap n k
  let π_set : X_S ⟶ X_RP := TopCat.toSSet.map (TopCat.ofHom quotientCmap)
  let Q' : (X_S.chainComplex R2).X k ⟶ (X_RP.chainComplex R2).X k :=
    (SSet.chainComplexMap π_set R2).f k

  have h_Q_basis : ∀ (σ : ι_S),
      X_S.ιChainComplex (R := R2) σ ≫ Q' =
      X_RP.ιChainComplex (R := R2) (π_simplex σ) := by
    intro σ
    exact SSet.ι_chainComplexMap_f (R := R2) (f := π_set) (x := σ)

  have h_surj_simplex : ∀ (τ : ι_RP), ∃ (σ : ι_S), π_simplex σ = τ :=
    BorsukUlam.QuotientKernel.quotientSimplexMap_surjective n k

  have h_cancel : ∀ {Y : ModuleCat (ZMod 2)} {g h : (X_RP.chainComplex R2).X k ⟶ Y},
      Q' ≫ g = Q' ≫ h → g = h := by
    intro Y g h h_eq
    apply SSet.chainComplex_hom_ext (X := X_RP) (R := R2) (n := k)
    intro τ
    rcases h_surj_simplex τ with ⟨σ, hσ⟩
    have h_fact : X_RP.ιChainComplex (R := R2) τ =
        X_S.ιChainComplex (R := R2) σ ≫ Q' := by
      rw [h_Q_basis σ, hσ]
    have h_goal : X_RP.ιChainComplex (R := R2) τ ≫ g =
        X_RP.ιChainComplex (R := R2) τ ≫ h := by
      rw [h_fact]
      have h6 : (X_S.ιChainComplex (R := R2) σ ≫ Q') ≫ g =
          X_S.ιChainComplex (R := R2) σ ≫ (Q' ≫ g) := by rw [Category.assoc]
      have h7 : (X_S.ιChainComplex (R := R2) σ ≫ Q') ≫ h =
          X_S.ιChainComplex (R := R2) σ ≫ (Q' ≫ h) := by rw [Category.assoc]
      rw [h6, h7, h_eq]
    exact h_goal
  have h_eq : Q' = (quotientChainMap n).f k := by rfl
  have h_epi : Epi Q' := by
    letI : Epi Q' := ⟨fun {Z} g h hgh => @h_cancel Z g h hgh⟩
    exact inferInstance
  have h_main : Epi ((quotientChainMap n).f k) := by
    rw [h_eq] at h_epi
    exact h_epi
  exact h_main 

/-! ### Quotient short exact sequence -/

/-- The quotient short complex: 0 → D → C(S^n) → C(RP^n) → 0. -/
def quotientShortComplex (n : ℕ) :
    CategoryTheory.ShortComplex (ChainComplex (ModuleCat (ZMod 2)) ℕ) :=
  { X₁ := timageSubcomplex (pHash2 n)
    X₂ := ChainSphere2 n
    X₃ := ChainRP2 n
    f := tinclusionMap (pHash2 n)
    g := quotientChainMap n
    zero := by
      ext i x
      have h_ker : (tinclusionMap (pHash2 n)).f i x ∈
          LinearMap.ker ((quotientChainMap n).f i).hom := by
        rw [BorsukUlam.QuotientKernel.quotientChainMap_ker_eq_D n i]
        exact x.prop
      exact h_ker }

/-- Degreewise short exactness of the quotient sequence. -/
lemma quotientDegreewiseShortExact (n i : ℕ) :
    ((quotientShortComplex n).map
      (HomologicalComplex.eval (ModuleCat (ZMod 2)) (ComplexShape.down ℕ) i)).ShortExact := by
  let S_i := (quotientShortComplex n).map
      (HomologicalComplex.eval (ModuleCat (ZMod 2)) (ComplexShape.down ℕ) i)
  have h_mono : Mono S_i.f := by
    rw [ModuleCat.mono_iff_injective]
    intro a b h
    exact Subtype.ext h
  have h_epi : Epi S_i.g := quotientChainMap_epi n i
  have h_exact : S_i.Exact := by
    have h_iff : S_i.Exact ↔ ∀ (x₂ : (ChainSphere2 n).X i),
        S_i.g x₂ = 0 → ∃ (x₁ : (timageSubcomplex (pHash2 n)).X i), S_i.f x₁ = x₂ := by
      exact CategoryTheory.ShortComplex.moduleCat_exact_iff S_i
    rw [h_iff]
    intro x₂ hx₂
    have h9 : x₂ ∈ LinearMap.ker ((quotientChainMap n).f i).hom := by
      exact LinearMap.mem_ker.mpr hx₂
    have h10 : x₂ ∈ LinearMap.range ((pHash2 n).f i).hom := by
      rw [BorsukUlam.QuotientKernel.quotientChainMap_ker_eq_D n i] at h9
      exact h9
    refine ⟨⟨x₂, h10⟩, ?_⟩
    have h_goal : (S_i.f).hom ⟨x₂, h10⟩ = x₂ := by
      dsimp [S_i, quotientShortComplex, tinclusionMap]
      <;> rfl
    exact h_goal
  exact CategoryTheory.ShortComplex.ShortExact.mk' h_exact h_mono h_epi

/-- The quotient short complex is short exact. -/
theorem quotientShortExact (n : ℕ) :
    (quotientShortComplex n).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact
    (quotientShortComplex n)
    (quotientDegreewiseShortExact n)

/-! ### Chain complex isomorphism D ≅ C(RP^n) -/

/-- Chain complex isomorphism D ≅ C(RP^n).

Both the transfer corestriction and the quotient map are cokernels
of the inclusion D → C(S^n), so their codomains are isomorphic. -/
noncomputable def dIsoChainRP (n : ℕ) :
    timageSubcomplex (pHash2 n) ≅ ChainRP2 n := by
  let S_trans := ttransferShortComplex (pHash2 n) (pHash2_rangePi_eq_ker n)
  let S_quot := quotientShortComplex n
  have hS_trans : S_trans.ShortExact :=
    ttransferShortExact (pHash2 n) (pHash2_rangePi_eq_ker n)
  have hS_quot : S_quot.ShortExact := quotientShortExact n
  have h_zero_trans : S_trans.f ≫ S_trans.g = 0 := S_trans.zero
  have h_zero_quot : S_quot.f ≫ S_quot.g = 0 := S_quot.zero
  let fork_trans := CokernelCofork.ofπ S_trans.g h_zero_trans
  let fork_quot := CokernelCofork.ofπ S_quot.g h_zero_quot
  have h1 : IsColimit fork_trans := hS_trans.gIsCokernel
  have h2 : IsColimit fork_quot := hS_quot.gIsCokernel
  exact h1.coconePointUniqueUpToIso h2

/-! ### RP^1 ≅ S^1 via squaring map through Circle -/

/-- The squaring map on S^1, via the complex unit circle. -/
def squareSphere (x : SphereType 1) : SphereType 1 :=
  sphereOneCircleHomeomorph.symm ((sphereOneCircleHomeomorph x)^2)

lemma squareSphere_continuous : Continuous squareSphere := by
  have h : Continuous (fun x : SphereType 1 =>
      sphereOneCircleHomeomorph.symm ((sphereOneCircleHomeomorph x)^2)) := by fun_prop
  exact h

lemma squareSphere_antipodal (x : SphereType 1) :
    squareSphere (antipodal 1 x) = squareSphere x := by
  have h_antipodal : sphereOneCircleHomeomorph (antipodal 1 x) =
      -sphereOneCircleHomeomorph x := by
    apply Subtype.ext
    simp [sphereOneCircleHomeomorph, antipodal, complexToEuclideanLinearIsometryEquiv]
  have h : (sphereOneCircleHomeomorph (antipodal 1 x))^2 =
      (sphereOneCircleHomeomorph x)^2 := by
    rw [h_antipodal]
    simp [pow_two]
  have h_main : squareSphere (antipodal 1 x) = squareSphere x := by
    dsimp only [squareSphere]
    rw [h]
  exact h_main

/-- The squaring map descends to RP^1 → S^1. -/
def rp1ToS1 (x : RPType 1) : SphereType 1 :=
  Quotient.lift squareSphere (fun x y h => by
    rcases h with (rfl | h')
    · rfl
    · have h'' : x = antipodal 1 y := h'
      rw [h'']
      exact squareSphere_antipodal y) x

lemma rp1ToS1_continuous : Continuous rp1ToS1 := by
  have h : Continuous (squareSphere : SphereType 1 → SphereType 1) :=
    squareSphere_continuous
  exact continuous_coinduced_dom.mpr h

/-- The squaring map on Circle is surjective. -/
lemma circle_square_surjective : Function.Surjective (fun (z : Circle) => z^2) := by
  intro z
  have h_surj : Function.Surjective (Circle.exp : ℝ → Circle) := Circle.exp_surjective
  rcases h_surj z with ⟨t, ht⟩
  let w : Circle := Circle.exp (t / 2)
  have hw : w^2 = z := by
    have h1 : w^2 = w * w := by
      simp [pow_two]
    rw [h1]
    have h2 : w * w = Circle.exp (t / 2) * Circle.exp (t / 2) := by rfl
    rw [h2]
    have h3 : Circle.exp (t / 2) * Circle.exp (t / 2) = Circle.exp (t / 2 + t / 2) := by
      have h4 := Circle.exp_add (t / 2) (t / 2)
      exact h4.symm
    rw [h3]
    have h5 : t / 2 + t / 2 = t := by ring
    rw [h5, ht]
  exact ⟨w, hw⟩

lemma rp1ToS1_surjective : Function.Surjective rp1ToS1 := by
  intro y
  let z : Circle := sphereOneCircleHomeomorph y
  rcases circle_square_surjective z with ⟨w, hw⟩
  let x : SphereType 1 := sphereOneCircleHomeomorph.symm w
  have h2 : rp1ToS1 (quotientMap 1 x) = y := by
    have h3 : rp1ToS1 (quotientMap 1 x) = squareSphere x := by rfl
    rw [h3]
    dsimp only [squareSphere]
    have h4 : sphereOneCircleHomeomorph x = w := by
      simp [x]
    have hz : z = sphereOneCircleHomeomorph y := by rfl
    have h5 : sphereOneCircleHomeomorph.symm (w ^ 2) = y := by
      have h6 : w ^ 2 = z := hw
      have h7 : sphereOneCircleHomeomorph.symm (w ^ 2) = sphereOneCircleHomeomorph.symm z := by
        exact congr_arg sphereOneCircleHomeomorph.symm h6
      rw [h7, hz]
      exact Homeomorph.symm_apply_apply sphereOneCircleHomeomorph y
    have h8 : sphereOneCircleHomeomorph.symm ((sphereOneCircleHomeomorph x) ^ 2) =
        sphereOneCircleHomeomorph.symm (w ^ 2) := by
      rw [h4]
    rw [h8]
    exact h5
  exact ⟨quotientMap 1 x, h2⟩

lemma rp1ToS1_injective : Function.Injective rp1ToS1 := by
  intro a b h
  rcases Quotient.exists_rep a with ⟨x, rfl⟩
  rcases Quotient.exists_rep b with ⟨y, rfl⟩
  have h_eq : squareSphere x = squareSphere y := h
  let zx : Circle := sphereOneCircleHomeomorph x
  let zy : Circle := sphereOneCircleHomeomorph y
  have h2 : (zx : ℂ)^2 = (zy : ℂ)^2 := by
    have h2a : zx^2 = zy^2 := by
      simpa [squareSphere] using congr_arg sphereOneCircleHomeomorph h_eq
    exact_mod_cast h2a
  have h3 : (zx : ℂ) = (zy : ℂ) ∨ (zx : ℂ) = -(zy : ℂ) := by
    have h4 : ((zx : ℂ) - (zy : ℂ)) * ((zx : ℂ) + (zy : ℂ)) = 0 := by
      calc
        ((zx : ℂ) - (zy : ℂ)) * ((zx : ℂ) + (zy : ℂ))
          = (zx : ℂ)^2 - (zy : ℂ)^2 := by ring
        _ = 0 := by rw [h2] <;> ring
    have h5 : ((zx : ℂ) - (zy : ℂ)) = 0 ∨ ((zx : ℂ) + (zy : ℂ)) = 0 :=
      eq_zero_or_eq_zero_of_mul_eq_zero h4
    rcases h5 with (h5 | h5)
    · left
      have h6 : (zx : ℂ) - (zy : ℂ) = 0 := h5
      have h7 : (zx : ℂ) = (zy : ℂ) := by
        simpa [sub_eq_zero] using h6
      exact_mod_cast h7
    · right
      have h6 : (zx : ℂ) + (zy : ℂ) = 0 := h5
      have h7 : (zx : ℂ) = -(zy : ℂ) := by
        simpa [add_eq_zero_iff_eq_neg] using h6
      exact h7
  rcases h3 with (h3 | h3)
  · have hxy : x = y := by
      have h6 : zx = zy := by exact_mod_cast h3
      exact sphereOneCircleHomeomorph.injective h6
    exact congr_arg (quotientMap 1) hxy
  · have h_antipodal : sphereOneCircleHomeomorph (antipodal 1 y) = -zy := by
      apply Subtype.ext
      simp [sphereOneCircleHomeomorph, antipodal, complexToEuclideanLinearIsometryEquiv]
      exact Complex.ext rfl rfl
    have h7 : zx = sphereOneCircleHomeomorph (antipodal 1 y) := by
      have h8 : (zx : ℂ) = (-(zy : ℂ)) := h3
      have h9 : (zx : ℂ) = ↑(sphereOneCircleHomeomorph (antipodal 1 y)) := by
        rw [h_antipodal] <;> exact_mod_cast h8
      exact_mod_cast h9
    have hxy : x = antipodal 1 y := sphereOneCircleHomeomorph.injective h7
    exact Quotient.sound (Or.inr hxy)

/-- RP^1 ≅ S^1 via the squaring map.

Uses the fact that RP^1 is compact (quotient of compact S^1) and S^1 is
Hausdorff, so a continuous bijection is a homeomorphism. -/
noncomputable def rp1HomeoS1 : RPType 1 ≃ₜ SphereType 1 := by
  let e : RPType 1 ≃ SphereType 1 :=
    { toFun := rp1ToS1
      invFun := fun y => Classical.choose (rp1ToS1_surjective y)
      left_inv := fun x => rp1ToS1_injective (Classical.choose_spec (rp1ToS1_surjective (rp1ToS1 x)))
      right_inv := fun y => Classical.choose_spec (rp1ToS1_surjective y) }
  have h_cont : Continuous e := rp1ToS1_continuous
  have h_sphere_compact : CompactSpace (SphereType 1) := by
    exact Metric.sphere.compactSpace 0 1
  have h_surj : Function.Surjective (quotientMap 1) := Quotient.mk_surjective
  have h_qcont : Continuous (quotientMap 1) := continuous_quotientMap
  have h_compact : CompactSpace (RPType 1) := by
    exact Function.Surjective.compactSpace h_qcont h_surj
  have h_haus : T2Space (SphereType 1) := by
    exact instT2SpaceSubtype
  exact Continuous.homeoOfEquivCompactToT2 (f := e) h_cont

/-! ### H_1(D(S^1)) ≅ Z/2 in AddCommGrpCat -/

/-- Chain complex isomorphism D ≅ C(RP^1) in AddCommGrpCat. -/
noncomputable def dIsoChainRP_Add :
    forgetZ2Chain.obj (timageSubcomplex (pHash2 1)) ≅
    forgetZ2Chain.obj (ChainRP2 1) :=
  forgetZ2Chain.mapIso (dIsoChainRP 1)

/-- TopCat isomorphism from RP^1 to S^1. -/
noncomputable def rp1ToS1Iso :
    TopCat.of (RPType 1) ≅ TopCat.of (SphereType 1) :=
  { hom := TopCat.ofHom ⟨rp1HomeoS1, rp1HomeoS1.continuous_toFun⟩
    inv := TopCat.ofHom ⟨rp1HomeoS1.symm, rp1HomeoS1.continuous_invFun⟩
    hom_inv_id := by
      apply TopCat.ext
      intro x
      exact rp1HomeoS1.left_inv x
    inv_hom_id := by
      apply TopCat.ext
      intro x
      exact rp1HomeoS1.right_inv x }

/-- Chain complex isomorphism C(RP^1) ≅ C(S^1) in AddCommGrpCat. -/
noncomputable def chainRP1IsoChainS1_Add :
    forgetZ2Chain.obj (ChainRP2 1) ≅
    forgetZ2Chain.obj (ChainSphere2 1) :=
  forgetZ2Chain.mapIso (chainFunctor2.mapIso rp1ToS1Iso)

/-- H_1(D(S^1)) ≅ Z/2 in AddCommGrpCat.

This is the theorem needed by FCId.lean for the base case n=1. -/
noncomputable def h1D_S1_iso_Z2 :
    (forgetZ2Chain.obj (timageSubcomplex (pHash2 1))).homology 1 ≅ R2 := by
  let e1 := dIsoChainRP_Add
  let e2 := chainRP1IsoChainS1_Add
  let e3 : (forgetZ2Chain.obj (ChainSphere2 1)).homology 1 ≅
      singularHomology' AddCommGrpCat R2 1 (TopCat.of (Sphere 1)) :=
    HomologicalComplex.homologyMapIso (chainSphere2ForgetIso 1) 1
  let e4 := BorsukUlam.BackupRoute.topSphereHomologyIsoZ2 1 (by norm_num)
  exact (HomologicalComplex.homologyMapIso e1 1) ≪≫
    (HomologicalComplex.homologyMapIso e2 1) ≪≫ e3 ≪≫ e4

end BorsukUlam.BaseCaseH1
