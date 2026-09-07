/-
Generic transfer sequence for a chain map p with im(p) = ker(p).

Constructs the image subcomplex D = im(p) and the short exact sequence
0 → D → C → D → 0.

Given p² = 0 and im(p) = ker(p) at each degree.
-/
import Mathlib.Tactic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace BorsukUlamBackup

variable {C : ChainComplex (ModuleCat (ZMod 2)) ℕ}
variable (p : C ⟶ C)

/-- The underlying linear map of `p.f i`. -/
abbrev tLin (i : ℕ) : (C.X i) →ₗ[ZMod 2] (C.X i) :=
  ModuleCat.Hom.hom (p.f i)

/-- The underlying linear map of `C.d i j`. -/
abbrev tdLin (i j : ℕ) : (C.X i) →ₗ[ZMod 2] (C.X j) :=
  ModuleCat.Hom.hom (C.d i j)

/-- The image of `p.f i` as a submodule of `C.X i`. -/
def trangePi (i : ℕ) : Submodule (ZMod 2) (C.X i) :=
  LinearMap.range (tLin p i)

/-- Chain map commutativity at the linear map level. -/
lemma tp_comm_lin (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    tdLin i j ∘ₗ tLin p i = tLin p j ∘ₗ tdLin i j := by
  have h_comm : p.f i ≫ C.d i j = C.d i j ≫ p.f j := by
    exact Hom.comm p i j
  have h1 : ModuleCat.Hom.hom (p.f i ≫ C.d i j) = tdLin i j ∘ₗ tLin p i := by
    rw [ModuleCat.hom_comp] <;> rfl
  have h2 : ModuleCat.Hom.hom (C.d i j ≫ p.f j) = tLin p j ∘ₗ tdLin i j := by
    rw [ModuleCat.hom_comp] <;> rfl
  rw [←h1, ←h2, h_comm]

/-- The differential of C restricts to the image subcomplex. -/
lemma td_restricts_to_image (i j : ℕ) (x : C.X i)
    (hx : x ∈ trangePi p i) : tdLin i j x ∈ trangePi p j := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · rcases LinearMap.mem_range.mp hx with ⟨y, rfl⟩
    have h_eq := tp_comm_lin p i j hij
    have h4 : (tdLin i j ∘ₗ tLin p i) y = (tLin p j ∘ₗ tdLin i j) y := by rw [h_eq]
    have h5 : tdLin i j (tLin p i y) = tLin p j (tdLin i j y) := by
      simpa [LinearMap.comp_apply] using h4
    rw [h5]
    exact LinearMap.mem_range.mpr ⟨tdLin i j y, rfl⟩
  · have h : C.d i j = 0 := C.shape i j hij
    have h' : tdLin i j = (0 : (C.X i) →ₗ[ZMod 2] (C.X j)) := by
      simpa [tdLin, h] using rfl
    rw [h']
    simp

/-- Restricted differential from trangePi i to trangePi j. -/
def tdRestricted (i j : ℕ) :
    (trangePi p i) →ₗ[ZMod 2] (trangePi p j) :=
  { toFun := fun (x : trangePi p i) =>
      ⟨tdLin i j (x : C.X i), td_restricts_to_image p i j (x : C.X i) x.prop⟩
    map_add' := by intro a b; ext; simp
    map_smul' := by intro c a; ext; simp }

/-- The image subcomplex D = im(p) of a chain map p : C → C. -/
def timageSubcomplex : ChainComplex (ModuleCat (ZMod 2)) ℕ :=
  { X := fun i => ModuleCat.of (ZMod 2) (trangePi p i)
    d := fun i j => ModuleCat.ofHom (tdRestricted p i j)
    shape := by
      intro i j hnj
      have h : C.d i j = 0 := C.shape i j hnj
      have h' : (tdLin i j : (C.X i) →ₗ[ZMod 2] (C.X j)) = 0 := by
        simpa [tdLin, h] using rfl
      ext x
      have h_goal : (tdRestricted p i j x : C.X j) = (0 : C.X j) := by
        dsimp [tdRestricted]
        rw [h'] <;> simp
      simpa [ModuleCat.ofHom] using h_goal
    d_comp_d' := by
      intro i j k hij hjk
      ext x
      have h2 : (tdLin j k ∘ₗ tdLin i j : (C.X i) →ₗ[ZMod 2] (C.X k)) = 0 := by
        have h3 : ModuleCat.Hom.hom (C.d i j ≫ C.d j k) =
            (tdLin j k ∘ₗ tdLin i j : (C.X i) →ₗ[ZMod 2] (C.X k)) := by
          rw [ModuleCat.hom_comp] <;> rfl
        have h4 : C.d i j ≫ C.d j k = 0 := C.d_comp_d i j k
        rw [←h3, h4] <;> rfl
      have h5 : (tdLin j k ∘ₗ tdLin i j) (x : C.X i) = 0 := by
        rw [h2] <;> simp
      simpa [ModuleCat.hom_ofHom, tdRestricted, LinearMap.comp_apply] using h5 }

/-- Inclusion map from the image subcomplex D into C. -/
def tinclusionMap : timageSubcomplex p ⟶ C :=
  { f := fun i => ModuleCat.ofHom (Submodule.subtype (trangePi p i))
    comm' := by
      intro i j hij
      ext x
      <;> rfl }

/-- Corestriction map from C to the image subcomplex D. -/
def tcorestrictionMap
    (h_eq : ∀ i, trangePi p i = LinearMap.ker (tLin p i)) :
    C ⟶ timageSubcomplex p :=
  { f := fun i =>
      ModuleCat.ofHom <|
        { toFun := fun (x : C.X i) =>
            ⟨tLin p i x, LinearMap.mem_range.mpr ⟨x, rfl⟩⟩
          map_add' := by intro a b; ext; simp
          map_smul' := by intro c a; ext; simp }
    comm' := by
      intro i j hij
      ext x
      dsimp
      have h_eq2 := tp_comm_lin p i j hij
      have h4 : (tdLin i j ∘ₗ tLin p i) x = (tLin p j ∘ₗ tdLin i j) x := by rw [h_eq2]
      have h5 : tdLin i j (tLin p i x) = tLin p j (tdLin i j x) := by
        simpa [LinearMap.comp_apply] using h4
      exact Subtype.ext h5 }

/-- The short complex 0 → D → C → D → 0 where D = im(p). -/
def ttransferShortComplex
    (h_eq : ∀ i, trangePi p i = LinearMap.ker (tLin p i)) :
    CategoryTheory.ShortComplex (ChainComplex (ModuleCat (ZMod 2)) ℕ) :=
  let iMap := tinclusionMap p
  let qMap := tcorestrictionMap p h_eq
  { X₁ := timageSubcomplex p
    X₂ := C
    X₃ := timageSubcomplex p
    f := iMap
    g := qMap
    zero := by
      ext i x
      dsimp only [iMap, qMap]
      let x' : C.X i := Submodule.subtype (trangePi p i) x
      have h_x_in : x' ∈ trangePi p i := x.prop
      have h_x_ker : x' ∈ LinearMap.ker (tLin p i) := by
        rw [←h_eq i] <;> exact h_x_in
      have h_px : tLin p i x' = 0 := LinearMap.mem_ker.mp h_x_ker
      exact Subtype.ext h_px }

/-- Degreewise short exactness of the transfer sequence. -/
lemma tdegreewise_shortExact
    (h_eq : ∀ i, trangePi p i = LinearMap.ker (tLin p i)) (i : ℕ) :
    ((ttransferShortComplex p h_eq).map
      (HomologicalComplex.eval (ModuleCat (ZMod 2)) (ComplexShape.down ℕ) i)).ShortExact := by
  let S_i := (ttransferShortComplex p h_eq).map
      (HomologicalComplex.eval (ModuleCat (ZMod 2)) (ComplexShape.down ℕ) i)
  have h_mono : Mono S_i.f := by
    rw [ModuleCat.mono_iff_injective]
    intro a b h
    exact Subtype.ext h
  have h_epi : Epi S_i.g := by
    rw [ModuleCat.epi_iff_surjective]
    intro y
    rcases y with ⟨z, hz⟩
    rcases LinearMap.mem_range.mp hz with ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    dsimp only [S_i, ttransferShortComplex, tcorestrictionMap]
    <;> rfl
  have h_exact : S_i.Exact := by
    rw [CategoryTheory.ShortComplex.moduleCat_exact_iff S_i]
    intro (x₂ : C.X i) hx₂
    have h9 : tLin p i x₂ = 0 := by
      dsimp only [S_i, ttransferShortComplex, tcorestrictionMap] at hx₂
      exact congr_arg Subtype.val hx₂
    have h_ker : x₂ ∈ LinearMap.ker (tLin p i) := LinearMap.mem_ker.mpr h9
    have h_x_in : x₂ ∈ trangePi p i := by
      have h_eq_i : trangePi p i = LinearMap.ker (tLin p i) := h_eq i
      exact h_eq_i ▸ h_ker
    refine ⟨(⟨x₂, h_x_in⟩ : trangePi p i), ?_⟩
    simp [S_i, ttransferShortComplex, tinclusionMap] <;> rfl
  exact CategoryTheory.ShortComplex.ShortExact.mk' h_exact h_mono h_epi

/-- The transfer short complex is short exact. -/
lemma ttransferShortExact
    (h_eq : ∀ i, trangePi p i = LinearMap.ker (tLin p i)) :
    (ttransferShortComplex p h_eq).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact
    (ttransferShortComplex p h_eq)
    (tdegreewise_shortExact p h_eq)

end BorsukUlamBackup
