/-
# Sphere Homology with Z/2 Coefficients (via Bockstein LES)

Computes H_k(S^n; Z/2) using the Bockstein long exact sequence
and known integer homology of spheres.

## Main Results
- `h0SphereIsoZ2`: H_0(S^n; Z/2) ≅ Z/2 for n ≥ 1
- `stdSphereVanishingZ2`: H_i(S^n; Z/2) = 0 for 0 < i < n
- `topSphereHomologyIsoZ2`: H_n(S^n; Z/2) ≅ Z/2 for n ≥ 1

## Proof Route
1. Bockstein SES 0 → C_*(;ℤ) --2→ C_*(;ℤ) → C_*(;Z/2) → 0 is short exact
2. LES gives H_i(;ℤ) --2→ H_i(;ℤ) → H_i(;Z/2) → H_{i-1}(;ℤ)
3. Known integer homology of spheres + cokernel of ×2 gives Z/2 homology

## Whiteprint Node
- `degree_route/sphere_homology_z2`
-/

import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.BocksteinDirect
import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace.StdSphereHomology
import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace.TopSphereHomology
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial Preadditive
open AlgebraicTopology.StdSphereHomology
open Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace

namespace BorsukUlam.BackupRoute

variable {n : ℕ}

abbrev RZ : AddCommGrpCat := AddCommGrpCat.of ℤ

/-- The homology map induced by multiplication by 2 on chains is multiplication by 2 on homology. -/
lemma homologyMap_multTwo {C : ChainComplex AddCommGrpCat ℕ} {i : ℕ} :
    HomologicalComplex.homologyMap (2 • 𝟙 C) i = 2 • 𝟙 (C.homology i) := by
  have h1 : (2 • 𝟙 C) = 𝟙 C + 𝟙 C := by
    ext n
    simp [two_smul] <;> abel
  rw [h1, HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_id]
  <;> simp [two_smul] <;> abel

/-- H₀(Sⁿ; Z/2) ≅ Z/2 for n ≥ 1 (path-connected sphere). -/
noncomputable def h0SphereIsoZ2 (n : ℕ) (hn : 1 ≤ n) :
    singularHomology' AddCommGrpCat R2 0 (TopCat.of (SphereType n)) ≅ R2 := by
  have h_finrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := by simp
  have h_rank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
    Module.lt_rank_of_lt_finrank (by omega)
  letI : PathConnectedSpace (SphereType n) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere h_rank 0 (by norm_num))
  let ε : singularHomology' AddCommGrpCat R2 0 (TopCat.of (SphereType n)) ⟶ R2 :=
    (TopCat.of (SphereType n)).singularHomology₀ε R2
  haveI : IsIso ε := by
    letI : PathConnectedSpace (TopCat.of (SphereType n)) := by
      exact isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere h_rank 0 (by norm_num))
    exact TopCat.instIsIsoSingularHomology₀εOfPathConnectedSpaceCarrier
      (TopCat.of (SphereType n)) R2
  exact asIso ε

/-- Multiplication by 2 on H₀(Sⁿ; ℤ) is mono for n ≥ 1. -/
lemma h0Sphere_multTwo_mono (n : ℕ) (hn : 1 ≤ n) :
    Mono (2 • 𝟙 (singularHomology' AddCommGrpCat RZ 0 (TopCat.of (SphereType n)))) := by
  let H0 := singularHomology' AddCommGrpCat RZ 0 (TopCat.of (SphereType n))
  have h_finrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := by simp
  have h_rank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
    Module.lt_rank_of_lt_finrank (by omega)
  letI : PathConnectedSpace (SphereType n) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere h_rank 0 (by norm_num))
  let ε : H0 ⟶ RZ := (TopCat.of (SphereType n)).singularHomology₀ε RZ
  haveI : IsIso ε := by
    exact TopCat.instIsIsoSingularHomology₀εOfPathConnectedSpaceCarrier (TopCat.of (SphereType n)) RZ
  let e : H0 ≅ RZ := asIso ε
  have h_mono_z : Mono (2 • 𝟙 RZ) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b h
    have h' : a + a = b + b := by simpa [two_smul] using h
    linarith
  have h_comm : (2 • 𝟙 H0) ≫ e.hom = e.hom ≫ (2 • 𝟙 RZ) := by
    simp [two_smul] <;> abel
  have h_eq : (2 • 𝟙 H0) = e.hom ≫ (2 • 𝟙 RZ) ≫ e.inv := by
    calc
      (2 • 𝟙 H0)
        = (2 • 𝟙 H0) ≫ 𝟙 H0 := by rw [Category.comp_id]
      _ = (2 • 𝟙 H0) ≫ (e.hom ≫ e.inv) := by rw [Iso.hom_inv_id]
      _ = ((2 • 𝟙 H0) ≫ e.hom) ≫ e.inv := by rw [Category.assoc]
      _ = (e.hom ≫ (2 • 𝟙 RZ)) ≫ e.inv := by rw [h_comm]
      _ = e.hom ≫ (2 • 𝟙 RZ) ≫ e.inv := by rw [Category.assoc]
  rw [h_eq]
  exact mono_comp e.hom ((2 • 𝟙 RZ) ≫ e.inv)

/-- Multiplication by 2 on an object isomorphic to ℤ is mono. -/
lemma multTwo_mono {A : AddCommGrpCat} (e : A ≅ RZ) : Mono (2 • 𝟙 A) := by
  have h_comm : (2 • 𝟙 A) ≫ e.hom = e.hom ≫ (2 • 𝟙 RZ) := by
    simp [two_smul] <;> abel
  have h_eq : (2 • 𝟙 A) = e.hom ≫ (2 • 𝟙 RZ) ≫ e.inv := by
    calc
      (2 • 𝟙 A)
        = (2 • 𝟙 A) ≫ 𝟙 A := by rw [Category.comp_id]
      _ = (2 • 𝟙 A) ≫ (e.hom ≫ e.inv) := by rw [Iso.hom_inv_id]
      _ = ((2 • 𝟙 A) ≫ e.hom) ≫ e.inv := by rw [Category.assoc]
      _ = (e.hom ≫ (2 • 𝟙 RZ)) ≫ e.inv := by rw [h_comm]
      _ = e.hom ≫ (2 • 𝟙 RZ) ≫ e.inv := by rw [Category.assoc]
  rw [h_eq]
  have h_mono_z : Mono (2 • 𝟙 RZ) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b h
    have h' : a + a = b + b := by simpa [two_smul] using h
    linarith
  exact mono_comp e.hom ((2 • 𝟙 RZ) ≫ e.inv)

/-- Vanishing below top degree (Z/2): H_i(Sⁿ; Z/2) = 0 for 0 < i < n. -/
theorem stdSphereVanishingZ2 :
    ∀ (n : ℕ) (i : ℕ), 0 < i → i < n →
      IsZero (singularHomology' AddCommGrpCat R2 i (TopCat.of (SphereType n))) := by
  intro n i hi_pos hi_lt
  let X := TopCat.of (SphereType n)
  let hS := BorsukUlam.BackupRoute.bocksteinShortExact X
  let S := bocksteinShortComplex X
  have h_int_vanish_i : IsZero (singularHomology' AddCommGrpCat RZ i X) :=
    stdSphere_vanishing n i hi_pos hi_lt
  by_cases h_i1 : i = 1
  · -- Case i = 1
    subst h_i1
    have h_n_ge2 : 2 ≤ n := by omega
    have hij : (ComplexShape.down ℕ).Rel 1 0 := by simp [ComplexShape.down_Rel]
    let H0Z := singularHomology' AddCommGrpCat RZ 0 X
    let H1Z2 := singularHomology' AddCommGrpCat R2 1 X
    let δ : H1Z2 ⟶ H0Z := hS.δ 1 0 hij
    let f0 : H0Z ⟶ H0Z := HomologicalComplex.homologyMap S.f 0
    have h_f0_eq : f0 = 2 • 𝟙 H0Z := homologyMap_multTwo
    have h_mono_f0 : Mono f0 := by
      rw [h_f0_eq]
      exact h0Sphere_multTwo_mono n (by omega)
    have h_exact1 := hS.homology_exact₁ 1 0 hij
    have hδ_eq_zero : δ = 0 := (h_exact1.mono_g_iff).mp h_mono_f0
    let g1 : singularHomology' AddCommGrpCat RZ 1 X ⟶ H1Z2 :=
      HomologicalComplex.homologyMap S.g 1
    have h_g1_eq_zero : g1 = 0 := IsZero.eq_zero_of_src h_int_vanish_i g1
    have h_exact3 := hS.homology_exact₃ 1 0 hij
    exact h_exact3.isZero_of_both_zeros h_g1_eq_zero hδ_eq_zero
  · -- Case i ≥ 2
    have h_i_ge2 : 2 ≤ i := by omega
    have h_i_minus1_pos : 0 < i - 1 := by omega
    have h_i_minus1_lt : i - 1 < n := by omega
    have h_int_vanish_j : IsZero (singularHomology' AddCommGrpCat RZ (i - 1) X) :=
      stdSphere_vanishing n (i - 1) h_i_minus1_pos h_i_minus1_lt
    let j := i - 1
    have hij : (ComplexShape.down ℕ).Rel i j := by
      simp [ComplexShape.down_Rel, j] <;> omega
    let HiZ2 := singularHomology' AddCommGrpCat R2 i X
    let δ : HiZ2 ⟶ singularHomology' AddCommGrpCat RZ j X := hS.δ i j hij
    let gi : singularHomology' AddCommGrpCat RZ i X ⟶ HiZ2 :=
      HomologicalComplex.homologyMap S.g i
    have h_gi_eq_zero : gi = 0 := IsZero.eq_zero_of_src h_int_vanish_i gi
    have hδ_eq_zero : δ = 0 := IsZero.eq_zero_of_tgt h_int_vanish_j δ
    have h_exact3 := hS.homology_exact₃ i j hij
    exact h_exact3.isZero_of_both_zeros h_gi_eq_zero hδ_eq_zero

/-- Cokernel of multiplication by 2 on ℤ is Z/2. -/
private noncomputable def cokerMultTwoIsoZ2 :
    Limits.cokernel (2 • 𝟙 RZ) ≅ R2 := by
  let hS : coeffShortComplex.ShortExact := coeffShortExact
  let h_cok : IsColimit (CokernelCofork.ofπ coeffShortComplex.g coeffShortComplex.zero) :=
    hS.gIsCokernel
  exact IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h_cok

/-- Top homology H_n(Sⁿ; Z/2) ≅ Z/2 for n ≥ 1. -/
noncomputable def topSphereHomologyIsoZ2 (n : ℕ) (hn : 1 ≤ n) :
    singularHomology' AddCommGrpCat R2 n (TopCat.of (SphereType n)) ≅ R2 := by
  let X := TopCat.of (SphereType n)
  let hS := BorsukUlam.BackupRoute.bocksteinShortExact X
  let S := bocksteinShortComplex X
  let HnZ := singularHomology' AddCommGrpCat RZ n X
  let HnZ2 := singularHomology' AddCommGrpCat R2 n X
  let f : HnZ ⟶ HnZ := HomologicalComplex.homologyMap S.f n
  let g : HnZ ⟶ HnZ2 := HomologicalComplex.homologyMap S.g n
  have h_fn_eq : f = 2 • 𝟙 HnZ := homologyMap_multTwo
  have h_top_int : HnZ ≅ RZ := topSphereHomologyIsoInt n hn
  have h_mono_f : Mono f := by
    rw [h_fn_eq]
    exact multTwo_mono h_top_int
  -- Choose j = n - 1 and show δ = 0
  let j := n - 1
  have hij : (ComplexShape.down ℕ).Rel n j := by
    simp [ComplexShape.down_Rel, j] <;> omega
  let δ := hS.δ n j hij
  have hδ : δ = 0 := by
    by_cases h_n1 : n = 1
    · subst h_n1
      let f0 := HomologicalComplex.homologyMap S.f 0
      have h_f0_eq : f0 = 2 • 𝟙 _ := homologyMap_multTwo
      have h_mono_f0 : Mono f0 := by
        rw [h_f0_eq]
        exact h0Sphere_multTwo_mono 1 (by norm_num)
      have h_exact1 := hS.homology_exact₁ 1 0 (by simp [ComplexShape.down_Rel])
      exact (h_exact1.mono_g_iff).mp h_mono_f0
    · have h_j_pos : 0 < j := by omega
      have h_j_lt : j < n := by omega
      have h_int : IsZero (singularHomology' AddCommGrpCat RZ j X) :=
        stdSphere_vanishing n j h_j_pos h_j_lt
      exact IsZero.eq_zero_of_tgt h_int δ
  -- gn is epi (from exact₃ and δ = 0)
  have h_exact3 := hS.homology_exact₃ n j hij
  have h_epi_g : Epi g := h_exact3.epi_f hδ
  -- Short exact at degree n: f and g form a short exact sequence
  have hfg : f ≫ g = 0 := by
    have h : (HomologicalComplex.homologyMap S.f n) ≫ (HomologicalComplex.homologyMap S.g n) = 0 := by
      rw [← HomologicalComplex.homologyMap_comp, S.zero, HomologicalComplex.homologyMap_zero]
    exact h
  let sc : ShortComplex AddCommGrpCat :=
    ShortComplex.mk f g hfg
  have h_sc_exact : sc.Exact := hS.homology_exact₂ n
  have h_sc_shortExact : sc.ShortExact :=
    ShortComplex.ShortExact.mk' h_sc_exact h_mono_f h_epi_g
  -- HnZ2 is cokernel of f
  let h_cok : IsColimit (CokernelCofork.ofπ g hfg) :=
    h_sc_shortExact.gIsCokernel
  let e1 : Limits.cokernel f ≅ HnZ2 :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h_cok
  -- cokernel f ≅ cokernel (2 • 𝟙 RZ) via h_top_int
  have h_comm : f ≫ h_top_int.hom = h_top_int.hom ≫ (2 • 𝟙 RZ) := by
    rw [h_fn_eq]
    simp [two_smul] <;> abel
  let e2 : Limits.cokernel f ≅ Limits.cokernel (2 • 𝟙 RZ) :=
    Limits.cokernel.mapIso f (2 • 𝟙 RZ) h_top_int h_top_int h_comm
  exact e1.symm ≪≫ e2 ≪≫ cokerMultTwoIsoZ2

/-! ### Vanishing above top degree -/

/-- The sphere in 1D Euclidean space is finite (helper for S^0 base case). -/
private lemma sphere0_set_finite : Set.Finite (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) := by
  let v1 : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 (1 : ℝ)
  let v2 : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 (-1 : ℝ)
  have h_norm_sq : ∀ (x : EuclideanSpace ℝ (Fin 1)), ‖x‖ ^ 2 = (x 0) ^ 2 := by
    intro x
    have h_sum : (∑ i : Fin 1, (x i) ^ 2) = (x 0) ^ 2 := by
      simp [Finset.sum_singleton] <;> rfl
    have h1 : ‖x‖ = Real.sqrt ((x 0) ^ 2) := by
      simp [EuclideanSpace.norm_eq, h_sum]
    rw [h1]
    have h2 : 0 ≤ (x 0) ^ 2 := by positivity
    rw [Real.sq_sqrt h2]
  have h_main : ∀ (x : EuclideanSpace ℝ (Fin 1)), x ∈ Metric.sphere (0 : _) 1 → x = v1 ∨ x = v2 := by
    intro x hx
    have h2 : ‖x‖ = 1 := by simpa [Metric.mem_sphere] using hx
    have h3 : (x 0) ^ 2 = 1 := by
      have h4 : ‖x‖ ^ 2 = (x 0) ^ 2 := h_norm_sq x
      rw [h2] at h4
      have h5 : (1 : ℝ) ^ 2 = (x 0) ^ 2 := h4
      have h6 : (x 0) ^ 2 = 1 := by rw [←h5] <;> norm_num
      exact h6
    have h6 : x 0 = 1 ∨ x 0 = -1 := by
      have h7 : (x 0 - 1) * (x 0 + 1) = 0 := by linarith
      have h8 : x 0 - 1 = 0 ∨ x 0 + 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h7
      rcases h8 with (h8 | h8)
      · left; linarith
      · right; linarith
    rcases h6 with (h6 | h6)
    · left
      have h10 : x = v1 := by
        ext i
        have h_i0 : i = 0 := by fin_cases i <;> rfl
        rw [h_i0]
        simp [v1, h6, PiLp.single_eq_same]
      exact h10
    · right
      have h10 : x = v2 := by
        ext i
        have h_i0 : i = 0 := by fin_cases i <;> rfl
        rw [h_i0]
        simp [v2, h6, PiLp.single_eq_same]
      exact h10
  have h_sub : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) ⊆ {v1, v2} := by
    intro x hx
    have h5 := h_main x hx
    rcases h5 with (h5 | h5) <;> simp [h5]
  have h_finite : Set.Finite ({v1, v2} : Set (EuclideanSpace ℝ (Fin 1))) := by simp
  exact Set.Finite.subset h_finite h_sub

/-- Integer homology H_i(S^n; Z) = 0 for i > n. -/
theorem stdSphereVanishingAboveInt (n i : ℕ) (hi : n < i) :
    IsZero (singularHomology' AddCommGrpCat RZ i (TopCat.of (SphereType n))) := by
  have h_main : ∀ n : ℕ, ∀ i : ℕ, n < i →
      IsZero (singularHomology' AddCommGrpCat RZ i (TopCat.of (SphereType n))) := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have h_i_pos : 0 < i := by omega
      have h_i_ne_zero : i ≠ 0 := by omega
      have h_finite : Set.Finite (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) := sphere0_set_finite
      haveI : Finite (SphereType 0) := by
        exact Set.finite_coe_iff.mpr h_finite
      haveI : DiscreteTopology (SphereType 0) := by
        exact Finite.instDiscreteTopology
      exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
        AddCommGrpCat i RZ (TopCat.of (SphereType 0)) h_i_ne_zero
    | succ n ih =>
      intro i hi
      have h_i_ge2 : 2 ≤ i := by omega
      let j := i - 1
      have h_j_pos : 0 < j := by omega
      have h_j_gt : n < j := by omega
      let p : SphereType (n + 1) := Classical.arbitrary _
      have h_iso : singularHomology' AddCommGrpCat RZ i (TopCat.of (SphereType (n + 1))) ≅
          singularHomology' AddCommGrpCat RZ j (TopCat.of (SphereType n)) := by
        have h_i' : i = j + 1 := by omega
        rw [h_i']
        exact sphere_homology_shift n p j h_j_pos
      exact IsZero.of_iso (ih j h_j_gt) h_iso
  exact h_main n i hi

/-- Vanishing above top degree (Z/2): H_i(S^n; Z/2) = 0 for i > n. -/
theorem stdSphereVanishingAboveZ2 (n i : ℕ) (hi : n < i) :
    IsZero (singularHomology' AddCommGrpCat R2 i (TopCat.of (SphereType n))) := by
  by_cases h_n0 : n = 0
  · -- n = 0: S^0 is totally disconnected
    subst h_n0
    have h_i_pos : 0 < i := by omega
    have h_i_ne_zero : i ≠ 0 := by omega
    have h_finite : Set.Finite (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) := sphere0_set_finite
    haveI : Finite (SphereType 0) := by
      exact Set.finite_coe_iff.mpr h_finite
    haveI : DiscreteTopology (SphereType 0) := by
      exact Finite.instDiscreteTopology
    exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      AddCommGrpCat i R2 (TopCat.of (SphereType 0)) h_i_ne_zero
  · -- n ≥ 1: use Bockstein LES
    have hn : 1 ≤ n := by omega
    let X := TopCat.of (SphereType n)
    let hS := BorsukUlam.BackupRoute.bocksteinShortExact X
    let S := bocksteinShortComplex X
    have h_i_ge2 : 2 ≤ i := by omega
    let j := i - 1
    have h_j_pos : 0 < j := by omega
    have hij : (ComplexShape.down ℕ).Rel i j := by
      simp [ComplexShape.down_Rel, j] <;> omega
    let δ : singularHomology' AddCommGrpCat R2 i X ⟶ singularHomology' AddCommGrpCat RZ j X :=
      hS.δ i j hij
    let g : singularHomology' AddCommGrpCat RZ i X ⟶ singularHomology' AddCommGrpCat R2 i X :=
      HomologicalComplex.homologyMap S.g i
    have h_above_int_i : IsZero (singularHomology' AddCommGrpCat RZ i X) :=
      stdSphereVanishingAboveInt n i hi
    have h_g_zero : g = 0 := IsZero.eq_zero_of_src h_above_int_i g
    by_cases h_jn : j = n
    · -- j = n (i = n + 1): use ×2 mono on H_n(Z)
      let f_j := HomologicalComplex.homologyMap S.f j
      have h_fj_eq : f_j = 2 • 𝟙 _ := homologyMap_multTwo
      have h_iso : singularHomology' AddCommGrpCat RZ j X ≅ RZ := by
        rw [show j = n from h_jn]
        exact topSphereHomologyIsoInt n hn
      have h_fj_mono : Mono f_j := by
        rw [h_fj_eq]
        exact multTwo_mono h_iso
      have h_exact1 : (ShortComplex.mk δ f_j _).Exact := hS.homology_exact₁ i j hij
      have hδ_zero : δ = 0 := h_exact1.mono_g_iff.mp h_fj_mono
      have h_exact3 : (ShortComplex.mk g δ _).Exact := hS.homology_exact₃ i j hij
      have hδ_mono : Mono δ := h_exact3.mono_g_iff.mpr h_g_zero
      have h_eq : (𝟙 (singularHomology' AddCommGrpCat R2 i X)) ≫ δ = (0 : _) ≫ δ := by
        rw [hδ_zero] <;> simp
      have h_id_zero : 𝟙 (singularHomology' AddCommGrpCat R2 i X) = 0 :=
        (cancel_mono δ).mp h_eq
      exact (IsZero.iff_id_eq_zero _).mpr h_id_zero
    · -- j > n: H_j(Z) = 0, so δ = 0 directly
      have h_j_gt_n : n < j := by omega
      have h_above_int_j : IsZero (singularHomology' AddCommGrpCat RZ j X) :=
        stdSphereVanishingAboveInt n j h_j_gt_n
      have hδ_zero : δ = 0 := IsZero.eq_zero_of_tgt h_above_int_j δ
      have h_exact3 : (ShortComplex.mk g δ _).Exact := hS.homology_exact₃ i j hij
      have hδ_mono : Mono δ := h_exact3.mono_g_iff.mpr h_g_zero
      have h_eq : (𝟙 (singularHomology' AddCommGrpCat R2 i X)) ≫ δ = (0 : _) ≫ δ := by
        rw [hδ_zero] <;> simp
      have h_id_zero : 𝟙 (singularHomology' AddCommGrpCat R2 i X) = 0 :=
        (cancel_mono δ).mp h_eq
      exact (IsZero.iff_id_eq_zero _).mpr h_id_zero

end BorsukUlam.BackupRoute

end
