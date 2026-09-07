/-
# Kernel and Surjectivity of the Quotient Chain Map

Proves that the kernel of the quotient chain map C(S^n) → C(RP^n)
is exactly D = im(1 + a_#), and that the quotient chain map is surjective.

## Main Results
- `ker_mapDomain_eq_range_pMap`: general algebraic lemma for free involutions
- `quotientChainMap_ker_eq_D`: degreewise kernel equality
- `quotientChainMap_surjective`: degreewise surjectivity

## Whiteprint Node
- `degree_route/quotient_kernel`
-/

import MyLeanRepo.Kakeya.BorsukUlam.QuotientSES
import MyLeanRepo.Kakeya.BorsukUlam.TransferFull

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial Preadditive
open Vendored.AlgebraicTopology.Degree
open AlgebraicTopology.StdSphereHomology
open BorsukUlamBackup
open BorsukUlam.BackupRoute
open BorsukUlam.QuotientSES

variable {n : ℕ}

namespace BorsukUlam.QuotientKernel

/-! ### General algebraic lemma -/

/-- `Finsupp.mapDomain` as a linear map over Z/2. -/
def mapDomainLin {α β : Type*} [DecidableEq α] [DecidableEq β] (π : α → β) :
    (α →₀ ZMod 2) →ₗ[ZMod 2] (β →₀ ZMod 2) :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) π

/-- General lemma: for a free involution on α and a quotient map π : α → β
whose fibers are exactly the orbits, we have ker(mapDomain π) = im(1 + a)
over Z/2. -/
lemma ker_mapDomain_eq_range_pMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (h : FreeInvolution α) (π : α → β)
    (hπ : ∀ x, π (h.a x) = π x)
    (hfiber : ∀ x y, π x = π y → x = y ∨ x = h.a y)
    (hsurj : Function.Surjective π) :
    LinearMap.ker (mapDomainLin π) =
    LinearMap.range (pMap h) := by
  have h_a2 : ∀ x, h.a (h.a x) = x := by
    intro x
    simpa [Equiv.trans_apply] using congr_fun (congr_arg Equiv.toFun h.sq) x
  have h_key : ∀ (f : α →₀ ZMod 2) (x : α),
      (mapDomainLin π f) (π x) = (pMap h f) x := by
    intro f x
    have h_x_ne : x ≠ h.a x := (h.free x).symm
    have h_fiber_iff : ∀ (z : α), π z = π x ↔ z = x ∨ z = h.a x := by
      intro z
      constructor
      · exact hfiber z x
      · rintro (rfl | rfl) <;> [rfl; exact hπ x]
    have h_eval1 : (mapDomainLin π f) (π x) = f x + f (h.a x) := by
      have h_sum : (mapDomainLin π f) (π x) =
          ∑ z ∈ f.support.filter (fun z => π z = π x), f z := by
        simpa [mapDomainLin, Finsupp.lmapDomain_apply] using
          Finsupp.mapDomain_apply_eq_sum π f (a := x)
      rw [h_sum]
      have h_filter : f.support.filter (fun z => π z = π x) =
          f.support.filter (fun z => z = x ∨ z = h.a x) := by
        apply Finset.ext
        intro z
        simp only [Finset.mem_filter]
        <;> rw [h_fiber_iff z] <;> tauto
      rw [h_filter]
      have h_sum2 : ∑ z ∈ f.support.filter (fun z => z = x ∨ z = h.a x), f z =
          f x + f (h.a x) := by
        have h_disj : Disjoint (f.support.filter (fun z => z = x))
            (f.support.filter (fun z => z = h.a x)) := by
          rw [Finset.disjoint_left]
          intro z hz1 hz2
          have h4 : z = x := (Finset.mem_filter.mp hz1).2
          have h5 : z = h.a x := (Finset.mem_filter.mp hz2).2
          rw [h4] at h5
          exact h_x_ne h5
        have h_union : f.support.filter (fun z => z = x ∨ z = h.a x) =
            f.support.filter (fun z => z = x) ∪
            f.support.filter (fun z => z = h.a x) := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_union]
          <;> constructor
          · rintro ⟨hmem, h | h⟩
            · exact Or.inl ⟨hmem, h⟩
            · exact Or.inr ⟨hmem, h⟩
          · rintro (⟨hmem, h⟩ | ⟨hmem, h⟩)
            · exact ⟨hmem, Or.inl h⟩
            · exact ⟨hmem, Or.inr h⟩
        rw [h_union, Finset.sum_union h_disj]
        have h1 : ∑ z ∈ f.support.filter (fun z => z = x), f z = f x := by
          have h_filter : f.support.filter (fun z => z = x) = if x ∈ f.support then {x} else ∅ := by
            exact Finset.filter_eq' f.support x
          rw [h_filter]
          split_ifs with hx
          · rw [Finset.sum_singleton]
          · rw [Finset.sum_empty]
            have h_fx_zero : f x = 0 := by simpa [Finsupp.mem_support_iff] using hx
            rw [h_fx_zero]
        have h2 : ∑ z ∈ f.support.filter (fun z => z = h.a x), f z = f (h.a x) := by
          have h_filter : f.support.filter (fun z => z = h.a x) = if h.a x ∈ f.support then {h.a x} else ∅ := by
            exact Finset.filter_eq' f.support (h.a x)
          rw [h_filter]
          split_ifs with hax
          · rw [Finset.sum_singleton]
          · rw [Finset.sum_empty]
            have h_fax_zero : f (h.a x) = 0 := by simpa [Finsupp.mem_support_iff] using hax
            rw [h_fax_zero]
        rw [h1, h2] <;> rfl
      exact h_sum2
    have h_eval2 : (pMap h f) x = f x + f (h.a x) := by
      simp [pMap, involutionAction_eval h]
      <;> rfl
    rw [h_eval1, h_eval2]
  have h1 : LinearMap.ker (mapDomainLin π) = LinearMap.ker (pMap h) := by
    ext f
    simp only [LinearMap.mem_ker]
    constructor
    · intro hf
      apply Finsupp.ext
      intro x
      have h2 : (mapDomainLin π f) (π x) = 0 := by
        rw [hf] <;> simp
      rw [h_key f x] at h2
      exact h2
    · intro hf
      apply Finsupp.ext
      intro y
      rcases hsurj y with ⟨x, rfl⟩
      have h3 : (pMap h f) x = 0 := by
        rw [hf] <;> simp
      rw [h_key f x]
      exact h3
  rw [h1]
  exact (range_pMap_eq_ker h).symm

/-! ### Two-lifts-only lemma for RP^n -/

/-- If two continuous maps σ, τ from a connected space to S^n have the same
    image in RP^n, then τ = σ or τ = antipodal ∘ σ. -/
lemma two_lifts_only_RP {α : Type*} [TopologicalSpace α] [ConnectedSpace α]
    {σ τ : α → Sphere n} (hσ : Continuous σ) (hτ : Continuous τ)
    (h : ∀ x, quotientMap n (σ x) = quotientMap n (τ x)) :
    τ = σ ∨ τ = fun x => ap (σ x) := by
  let U : Set α := {x | τ x = σ x}
  let V : Set α := {x | τ x = ap (σ x)}
  have h1 : ∀ x, x ∈ U ∨ x ∈ V := by
    intro x
    have h2 : quotientMap n (σ x) = quotientMap n (τ x) := h x
    have h3 : antipodalRel (σ x) (τ x) := Quotient.exact h2
    rcases h3 with (h3 | h3)
    · exact Or.inl h3.symm
    · have h4 : τ x = ap (σ x) := by
        have h5 : σ x = ap (τ x) := h3
        have h6 : ap (σ x) = ap (ap (τ x)) := by rw [h5]
        have h7 : ap (ap (τ x)) = τ x := ap_invol (τ x)
        rw [h6, h7] at *
        <;> exact h6.symm
      exact Or.inr h4
  have hUV : U ∪ V = Set.univ := by
    ext x; simp only [Set.mem_union, Set.mem_univ, iff_true]; exact h1 x
  have h_disj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    have h4 : τ x = σ x := hxU
    have h5 : τ x = ap (σ x) := hxV
    have h6 : ap (σ x) = σ x := h5.symm.trans h4
    exact ap_no_fixed_points (σ x) h6
  have hU_closed : IsClosed U := isClosed_eq hτ hσ
  have hV_closed : IsClosed V :=
    isClosed_eq hτ (continuous_antipodal.comp hσ)
  have hU_open : IsOpen U := by
    have h_eq : U = Vᶜ := by
      ext x
      simp only [U, V, Set.mem_compl_iff]
      have h_cov : x ∈ U ∨ x ∈ V := h1 x
      rcases h_cov with (h_cov | h_cov)
      · constructor
        · intro h_eq2; intro h_contra
          have h7 : antipodal n (σ x) = σ x := h_contra.symm.trans h_eq2
          exact antipodal_ne_self n (σ x) h7
        · intro _; exact h_cov
      · have h_notU : x ∉ U := by
          intro hU; exact Set.disjoint_left.mp h_disj hU h_cov
        constructor
        · intro h_eq2; exfalso; exact h_notU h_eq2
        · intro h_notV; exfalso; exact h_notV h_cov
    rw [h_eq]; exact hV_closed.isOpen_compl
  have hU_clopen : IsClopen U := ⟨hU_closed, hU_open⟩
  have h_main : U = Set.univ ∨ U = ∅ := by
    by_cases hU : U.Nonempty
    · exact Or.inl (hU_clopen.eq_univ hU)
    · exact Or.inr (Set.not_nonempty_iff_eq_empty.mp hU)
  rcases h_main with (hU | hU_empty)
  · have h_goal : τ = σ := by
      funext x
      have h4 : x ∈ U := by
        rw [hU]
        <;> exact Set.mem_univ x
      exact h4
    exact Or.inl h_goal
  · have hV_univ : V = Set.univ := by
      have h : U ∪ V = Set.univ := hUV
      rw [hU_empty] at h; simpa using h
    have h_goal : τ = fun x => ap (σ x) := by
      funext x
      have h4 : x ∈ V := by
        rw [hV_univ] <;> exact Set.mem_univ x
      exact h4
    exact Or.inr h_goal

/-! ### Kernel of quotient chain map equals D -/

/-- The singular simplicial set of RP^n. -/
abbrev rpSSet (n : ℕ) := TopCat.toSSet.obj (TopCat.of (RPType n))

/-- The type of singular k-simplices of RP^n. -/
abbrev RPSingularSimplices (n k : ℕ) := rpSSet n _⦋k⦌

/-- The map on singular simplices induced by the quotient map. -/
def quotientSimplexMap (n k : ℕ) : SingularSimplices n k → RPSingularSimplices n k :=
  let π_set : sphereSSet n ⟶ rpSSet n := TopCat.toSSet.map (TopCat.ofHom quotientCmap)
  π_set.app _

/-- The quotient map on simplices commutes with the antipodal action. -/
lemma quotientSimplexMap_antipodal (n k : ℕ) :
    ∀ (σ : SingularSimplices n k),
      quotientSimplexMap n k (antipodalSimplexAction n k σ) =
      quotientSimplexMap n k σ := by
  intro σ
  let π_set : sphereSSet n ⟶ rpSSet n := TopCat.toSSet.map (TopCat.ofHom quotientCmap)
  let a_set : sphereSSet n ⟶ sphereSSet n := TopCat.toSSet.map (TopCat.ofHom apCmap)
  have h_comp : a_set ≫ π_set = π_set := by
    have h1 : (quotientCmap.comp apCmap : C(Sphere n, RPType n)) = quotientCmap := by
      apply ContinuousMap.ext; intro x
      have h2 : quotientMap n (ap x) = quotientMap n x := by
        apply Quotient.sound
        exact Or.inr rfl
      have h3 : (quotientCmap.comp apCmap) x = quotientMap n (ap x) := by rfl
      have h4 : quotientCmap x = quotientMap n x := by rfl
      rw [h3, h4, h2]
    have h2 : (TopCat.ofHom apCmap ≫ TopCat.ofHom quotientCmap : TopCat.of (Sphere n) ⟶ TopCat.of (RPType n)) =
        TopCat.ofHom quotientCmap := by
      simpa [TopCat.ofHom_comp] using congr_arg TopCat.ofHom h1
    exact congr_arg (TopCat.toSSet.map) h2
  simpa [quotientSimplexMap, antipodalSimplexAction] using congr_arg (fun (f : sphereSSet n ⟶ rpSSet n) => f.app _ σ) h_comp

/-- The quotient map on simplices has orbit fibers. -/
lemma quotientSimplexMap_fiber (n k : ℕ) :
    ∀ (σ τ : SingularSimplices n k),
      quotientSimplexMap n k σ = quotientSimplexMap n k τ →
      τ = σ ∨ τ = antipodalSimplexAction n k σ := by
  intro σ τ h
  let Δk := stdSimplex ℝ (Fin (k + 1))
  let eS : SingularSimplices n k ≃ C(Δk, Sphere n) :=
    TopCat.toSSetObjEquiv (TopCat.of (Sphere n)) (Opposite.op ⦋k⦌)
  let eRP : RPSingularSimplices n k ≃ C(Δk, RPType n) :=
    TopCat.toSSetObjEquiv (TopCat.of (RPType n)) (Opposite.op ⦋k⦌)
  let σ' : C(Δk, Sphere n) := eS σ
  let τ' : C(Δk, Sphere n) := eS τ
  have h_nat : eRP (quotientSimplexMap n k σ) = quotientCmap.comp σ' := by
    exact (Equiv.apply_eq_iff_eq_symm_apply eRP).mpr rfl
  have h_nat2 : eRP (quotientSimplexMap n k τ) = quotientCmap.comp τ' := by
    exact (Equiv.apply_eq_iff_eq_symm_apply eRP).mpr rfl
  have h_eq : quotientCmap.comp σ' = quotientCmap.comp τ' := by
    rw [←h_nat, ←h_nat2, h]
  have h_pointwise : ∀ (x : Δk), quotientMap n (σ' x) = quotientMap n (τ' x) := by
    intro x
    have h9 := congr_fun (congr_arg ContinuousMap.toFun h_eq) x
    exact h9
  have h_main : ⇑τ' = ⇑σ' ∨ ⇑τ' = fun x => ap (σ' x) :=
    two_lifts_only_RP (hσ := σ'.continuous) (hτ := τ'.continuous) h_pointwise
  rcases h_main with (h_eq1 | h_eq2)
  · have h_eq1' : τ' = σ' := by
      apply ContinuousMap.ext
      exact congr_fun h_eq1
    have h_τσ : τ = σ := by
      apply eS.injective
      exact h_eq1'
    exact Or.inl h_τσ
  · have h_eq2' : τ' = apCmap.comp σ' := by
      apply ContinuousMap.ext
      intro x
      exact congr_fun h_eq2 x
    have h9 : eS (antipodalSimplexAction n k σ) = apCmap.comp σ' := by
      exact (Equiv.apply_eq_iff_eq_symm_apply eS).mpr rfl
    have h10 : eS τ = eS (antipodalSimplexAction n k σ) := by
      calc
        eS τ = τ' := by rfl
        _ = apCmap.comp σ' := h_eq2'
        _ = eS (antipodalSimplexAction n k σ) := h9.symm
    have h_τaσ : τ = antipodalSimplexAction n k σ := eS.injective h10
    exact Or.inr h_τaσ

/-- The quotient map on simplices is surjective. -/
lemma quotientSimplexMap_surjective (n k : ℕ) :
    Function.Surjective (quotientSimplexMap n k) := by
  intro τ
  let Δk := stdSimplex ℝ (Fin (k + 1))
  let eRP : RPSingularSimplices n k ≃ C(Δk, RPType n) :=
    TopCat.toSSetObjEquiv (TopCat.of (RPType n)) (Opposite.op ⦋k⦌)
  let τ' : C(Δk, RPType n) := eRP τ
  have h_lift : ∃ (σ' : C(Δk, Sphere n)), quotientCmap.comp σ' = τ' :=
    lift_simplex k τ'
  rcases h_lift with ⟨σ', hσ'⟩
  let eS : SingularSimplices n k ≃ C(Δk, Sphere n) :=
    TopCat.toSSetObjEquiv (TopCat.of (Sphere n)) (Opposite.op ⦋k⦌)
  let σ : SingularSimplices n k := eS.symm σ'
  have h_nat : eRP (quotientSimplexMap n k σ) = quotientCmap.comp σ' := by
    exact (Equiv.apply_eq_iff_eq_symm_apply eRP).mpr rfl
  have h_main : eRP (quotientSimplexMap n k σ) = eRP τ := by
    rw [h_nat, hσ']
  exact ⟨σ, eRP.injective h_main⟩

/-- Commutativity: pHash2 corresponds to pMap under the finsupp equivalence. -/
lemma pHash2_finsupp_comm (n k : ℕ) :
    ∃ (e : (ChainSphere2 n).X k ≃ₗ[ZMod 2] (SingularSimplices n k →₀ ZMod 2)),
      e.toLinearMap.comp ((pHash2 n).f k).hom =
      (pMap {
        a := antipodalSimplexAction n k
        sq := by ext x; exact (antipodalSimplexAction n k).left_inv x
        free := antipodalSimplexAction_free n k }).comp e.toLinearMap := by
  classical
  let X := sphereSSet n
  let ι := SingularSimplices n k
  let R2 := ModuleCat.of (ZMod 2) (ZMod 2)
  let Z : ι → ModuleCat (ZMod 2) := fun _ => R2
  let a_simplex : ι ≃ ι := antipodalSimplexAction n k
  let h_free : FreeInvolution ι :=
    { a := a_simplex
      sq := by ext x; exact a_simplex.left_inv x
      free := antipodalSimplexAction_free n k }
  let Ck := (ChainSphere2 n).X k
  let e1 : Ck ≅ ModuleCat.of (ZMod 2) (DirectSum ι (fun i => ↑(Z i))) :=
    ModuleCat.coprodIsoDirectSum Z
  let e2 : (ι →₀ ZMod 2) ≃ₗ[ZMod 2] DirectSum ι (fun i => ↑(Z i)) :=
    finsuppLequivDFinsupp (ZMod 2)
  let e : Ck ≃ₗ[ZMod 2] (ι →₀ ZMod 2) :=
    e1.toLinearEquiv.trans e2.symm
  let A : Ck →ₗ[ZMod 2] Ck := ((aHash2 n).f k).hom
  let P : Ck →ₗ[ZMod 2] Ck := ((pHash2 n).f k).hom
  let P' : (ι →₀ ZMod 2) →ₗ[ZMod 2] (ι →₀ ZMod 2) := pMap h_free
  let a_set : X ⟶ X := TopCat.toSSet.map (TopCat.ofHom apCmap)
  let T := ModuleCat.of (ZMod 2) (ι →₀ ZMod 2)
  let ι_inc (σ : ι) : R2 ⟶ Ck := X.ιChainComplex (R := R2) σ
  have h_basis : ∀ (σ : ι), e.toLinearMap ((ι_inc σ).hom 1) = Finsupp.single σ 1 := by
    intro σ
    have h_iso : (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ)) ≫ e1.inv = ι_inc σ :=
      ModuleCat.lof_coprodIsoDirectSum_inv Z σ
    have h2 : ι_inc σ ≫ e1.hom =
        ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ) := by
      calc
        ι_inc σ ≫ e1.hom
          = ((ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ)) ≫ e1.inv) ≫ e1.hom := by rw [h_iso]
        _ = (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ)) ≫ (e1.inv ≫ e1.hom) := by rw [Category.assoc]
        _ = (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ)) ≫ 𝟙 _ := by rw [e1.inv_hom_id]
        _ = (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ)) := by simp
    have h1 : e1.toLinearEquiv ((ι_inc σ).hom 1) =
        (DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ) 1 := by
      exact congr_arg (fun (f : R2 ⟶ _) => f.hom 1) h2
    have h5 : DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ 1 =
        DFinsupp.single σ 1 := by
      exact Eq.symm (DirectSum.ext (fun i => ZMod 2) (congrFun rfl))
    have h6 : e2.symm (DFinsupp.single σ 1) = Finsupp.single σ 1 := by
      have h_e2 : (e2.symm : DirectSum ι (fun i : ι => ZMod 2) → (ι →₀ ZMod 2)) = DFinsupp.toFinsupp := by
        exact finsuppLequivDFinsupp_symm_apply (R := ZMod 2)
      rw [h_e2]
      have h_toFinsupp : DFinsupp.toFinsupp (DFinsupp.single σ (1 : ZMod 2)) = Finsupp.single σ (1 : ZMod 2) := by
        ext x; simp [DFinsupp.toFinsupp] <;> aesop
      exact h_toFinsupp
    calc
      e.toLinearMap ((ι_inc σ).hom 1)
        = e2.symm (e1.toLinearEquiv ((ι_inc σ).hom 1)) := by rfl
      _ = e2.symm (DirectSum.lof (ZMod 2) ι (fun i : ι => ZMod 2) σ 1) := by rw [h1]
      _ = Finsupp.single σ 1 := by rw [h5] <;> exact h6
  have h_A_basis : ∀ (σ : ι), A ((ι_inc σ).hom 1) = (ι_inc (a_simplex σ)).hom 1 := by
    intro σ
    have h1 : ι_inc σ ≫ (aHash2 n).f k = ι_inc (a_simplex σ) := by
      have h_map := SSet.ι_chainComplexMap_f (R := R2) (f := a_set) (x := σ)
      exact h_map
    exact congr_arg (fun (f : R2 ⟶ Ck) => f.hom 1) h1
  let f_cat : Ck ⟶ T := ModuleCat.ofHom (e.toLinearMap.comp A)
  let g_cat : Ck ⟶ T := ModuleCat.ofHom ((involutionAction h_free).comp e.toLinearMap)
  have h_eq : f_cat = g_cat := by
    apply SSet.chainComplex_hom_ext (R := R2)
    intro σ
    have h_hom : (ι_inc σ ≫ f_cat).hom = (ι_inc σ ≫ g_cat).hom := by
      apply LinearMap.ext
      intro z
      have h_z : z = 0 ∨ z = 1 := by fin_cases z <;> tauto
      rcases h_z with (h0 | h1)
      · rw [h0]; simp
      · subst h1
        have h_left : e.toLinearMap (A ((ι_inc σ).hom 1)) =
            Finsupp.single (a_simplex σ) 1 := by
          rw [h_A_basis σ, h_basis (a_simplex σ)]
        have h_right : involutionAction h_free (e.toLinearMap ((ι_inc σ).hom 1)) =
            Finsupp.single (a_simplex σ) 1 := by
          rw [h_basis σ]
          simp [involutionAction, Finsupp.mapDomain_single] <;> rfl
        have h_goal1 : (ι_inc σ ≫ f_cat).hom 1 = e.toLinearMap (A ((ι_inc σ).hom 1)) := by rfl
        have h_goal2 : (ι_inc σ ≫ g_cat).hom 1 = involutionAction h_free (e.toLinearMap ((ι_inc σ).hom 1)) := by rfl
        rw [h_goal1, h_goal2, h_left, h_right]
    have h_morph : (ι_inc σ ≫ f_cat) = (ι_inc σ ≫ g_cat) := by
      have h : (ι_inc σ ≫ f_cat).hom = (ι_inc σ ≫ g_cat).hom := h_hom
      exact ModuleCat.hom_ext h
    exact h_morph
  have h_comm_A : e.toLinearMap.comp A = (involutionAction h_free).comp e.toLinearMap := by
    have h : f_cat.hom = g_cat.hom := by rw [h_eq]
    exact h
  have h_comm_P : e.toLinearMap.comp P = P'.comp e.toLinearMap := by
    have hP : P = LinearMap.id + A := by rfl
    rw [hP]
    simp [LinearMap.add_comp, LinearMap.comp_add, h_comm_A] <;> rfl
  exact ⟨e, h_comm_P⟩

/-- Degreewise: the kernel of the quotient chain map equals D = im(pHash2). -/
theorem quotientChainMap_ker_eq_D (n k : ℕ) :
    LinearMap.ker ((quotientChainMap n).f k).hom =
    LinearMap.range ((pHash2 n).f k).hom := by
  classical
  let X_S := sphereSSet n
  let X_RP := rpSSet n
  let ι_S := SingularSimplices n k
  let ι_RP := RPSingularSimplices n k
  let R2 := ModuleCat.of (ZMod 2) (ZMod 2)
  let Z_S : ι_S → ModuleCat (ZMod 2) := fun _ => R2
  let Z_RP : ι_RP → ModuleCat (ZMod 2) := fun _ => R2
  let a_simplex : ι_S ≃ ι_S := antipodalSimplexAction n k
  let h_free : FreeInvolution ι_S :=
    { a := a_simplex
      sq := by ext x; exact a_simplex.left_inv x
      free := antipodalSimplexAction_free n k }
  let π_simplex : ι_S → ι_RP := quotientSimplexMap n k
  let Ck_S := (ChainSphere2 n).X k
  let Ck_RP := (ChainRP2 n).X k
  let e1_S : Ck_S ≅ ModuleCat.of (ZMod 2) (DirectSum ι_S (fun i => ↑(Z_S i))) :=
    ModuleCat.coprodIsoDirectSum Z_S
  let e2_S : (ι_S →₀ ZMod 2) ≃ₗ[ZMod 2] DirectSum ι_S (fun i => ↑(Z_S i)) :=
    finsuppLequivDFinsupp (ZMod 2)
  let e_S : Ck_S ≃ₗ[ZMod 2] (ι_S →₀ ZMod 2) :=
    e1_S.toLinearEquiv.trans e2_S.symm
  let e1_RP : Ck_RP ≅ ModuleCat.of (ZMod 2) (DirectSum ι_RP (fun i => ↑(Z_RP i))) :=
    ModuleCat.coprodIsoDirectSum Z_RP
  let e2_RP : (ι_RP →₀ ZMod 2) ≃ₗ[ZMod 2] DirectSum ι_RP (fun i => ↑(Z_RP i)) :=
    finsuppLequivDFinsupp (ZMod 2)
  let e_RP : Ck_RP ≃ₗ[ZMod 2] (ι_RP →₀ ZMod 2) :=
    e1_RP.toLinearEquiv.trans e2_RP.symm
  let Q : Ck_S →ₗ[ZMod 2] Ck_RP := ((quotientChainMap n).f k).hom
  let Q' : (ι_S →₀ ZMod 2) →ₗ[ZMod 2] (ι_RP →₀ ZMod 2) :=
    mapDomainLin π_simplex
  let P : Ck_S →ₗ[ZMod 2] Ck_S := ((pHash2 n).f k).hom
  let P' : (ι_S →₀ ZMod 2) →ₗ[ZMod 2] (ι_S →₀ ZMod 2) := pMap h_free
  let π_set : X_S ⟶ X_RP := TopCat.toSSet.map (TopCat.ofHom quotientCmap)
  let ι_inc_S (σ : ι_S) : R2 ⟶ Ck_S := X_S.ιChainComplex (R := R2) σ
  let ι_inc_RP (τ : ι_RP) : R2 ⟶ Ck_RP := X_RP.ιChainComplex (R := R2) τ
  have h_basis_S : ∀ (σ : ι_S), e_S.toLinearMap ((ι_inc_S σ).hom 1) = Finsupp.single σ 1 := by
    intro σ
    have h_iso : (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_S (fun i : ι_S => ZMod 2) σ)) ≫ e1_S.inv = ι_inc_S σ :=
      ModuleCat.lof_coprodIsoDirectSum_inv Z_S σ
    have h2 : ι_inc_S σ ≫ e1_S.hom =
        ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_S (fun i : ι_S => ZMod 2) σ) := by
      calc
        ι_inc_S σ ≫ e1_S.hom
          = ((ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_S (fun i : ι_S => ZMod 2) σ)) ≫ e1_S.inv) ≫ e1_S.hom := by rw [h_iso]
        _ = (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_S (fun i : ι_S => ZMod 2) σ)) ≫ (e1_S.inv ≫ e1_S.hom) := by rw [Category.assoc]
        _ = (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_S (fun i : ι_S => ZMod 2) σ)) ≫ 𝟙 _ := by rw [e1_S.inv_hom_id]
        _ = (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_S (fun i : ι_S => ZMod 2) σ)) := by simp
    have h1 : e1_S.toLinearEquiv ((ι_inc_S σ).hom 1) =
        (DirectSum.lof (ZMod 2) ι_S (fun i : ι_S => ZMod 2) σ) 1 := by
      exact congr_arg (fun (f : R2 ⟶ _) => f.hom 1) h2
    have h5 : DirectSum.lof (ZMod 2) ι_S (fun i : ι_S => ZMod 2) σ 1 =
        DFinsupp.single σ 1 := by
      exact Eq.symm (DirectSum.ext (fun i => ZMod 2) (congrFun rfl))
    have h6 : e2_S.symm (DFinsupp.single σ 1) = Finsupp.single σ 1 := by
      have h_e2 : (e2_S.symm : DirectSum ι_S (fun i : ι_S => ZMod 2) → (ι_S →₀ ZMod 2)) = DFinsupp.toFinsupp := by
        exact finsuppLequivDFinsupp_symm_apply (R := ZMod 2)
      rw [h_e2]
      have h_toFinsupp : DFinsupp.toFinsupp (DFinsupp.single σ (1 : ZMod 2)) = Finsupp.single σ (1 : ZMod 2) := by
        ext x; simp [DFinsupp.toFinsupp] <;> aesop
      exact h_toFinsupp
    calc
      e_S.toLinearMap ((ι_inc_S σ).hom 1)
        = e2_S.symm (e1_S.toLinearEquiv ((ι_inc_S σ).hom 1)) := by rfl
      _ = e2_S.symm (DirectSum.lof (ZMod 2) ι_S (fun i : ι_S => ZMod 2) σ 1) := by rw [h1]
      _ = Finsupp.single σ 1 := by rw [h5] <;> exact h6
  have h_basis_RP : ∀ (τ : ι_RP), e_RP.toLinearMap ((ι_inc_RP τ).hom 1) = Finsupp.single τ 1 := by
    intro τ
    have h_iso : (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ)) ≫ e1_RP.inv = ι_inc_RP τ :=
      ModuleCat.lof_coprodIsoDirectSum_inv Z_RP τ
    have h2 : ι_inc_RP τ ≫ e1_RP.hom =
        ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ) := by
      calc
        ι_inc_RP τ ≫ e1_RP.hom
          = ((ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ)) ≫ e1_RP.inv) ≫ e1_RP.hom := by rw [h_iso]
        _ = (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ)) ≫ (e1_RP.inv ≫ e1_RP.hom) := by rw [Category.assoc]
        _ = (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ)) ≫ 𝟙 _ := by rw [e1_RP.inv_hom_id]
        _ = (ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ)) := by simp
    have h1 : e1_RP.toLinearEquiv ((ι_inc_RP τ).hom 1) =
        (DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ) 1 := by
      exact congr_arg (fun (f : R2 ⟶ _) => f.hom 1) h2
    have h5 : DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ 1 =
        DFinsupp.single τ 1 := by
      exact Eq.symm (DirectSum.ext (fun i => ZMod 2) (congrFun rfl))
    have h6 : e2_RP.symm (DFinsupp.single τ 1) = Finsupp.single τ 1 := by
      have h_e2 : (e2_RP.symm : DirectSum ι_RP (fun i : ι_RP => ZMod 2) → (ι_RP →₀ ZMod 2)) = DFinsupp.toFinsupp := by
        exact finsuppLequivDFinsupp_symm_apply (R := ZMod 2)
      rw [h_e2]
      have h_toFinsupp : DFinsupp.toFinsupp (DFinsupp.single τ (1 : ZMod 2)) = Finsupp.single τ (1 : ZMod 2) := by
        ext x; simp [DFinsupp.toFinsupp] <;> aesop
      exact h_toFinsupp
    calc
      e_RP.toLinearMap ((ι_inc_RP τ).hom 1)
        = e2_RP.symm (e1_RP.toLinearEquiv ((ι_inc_RP τ).hom 1)) := by rfl
      _ = e2_RP.symm (DirectSum.lof (ZMod 2) ι_RP (fun i : ι_RP => ZMod 2) τ 1) := by rw [h1]
      _ = Finsupp.single τ 1 := by rw [h5] <;> exact h6
  have h_Q_basis : ∀ (σ : ι_S),
      Q ((ι_inc_S σ).hom 1) = (ι_inc_RP (π_simplex σ)).hom 1 := by
    intro σ
    have h1 : ι_inc_S σ ≫ (quotientChainMap n).f k = ι_inc_RP (π_simplex σ) := by
      have h_map := SSet.ι_chainComplexMap_f (R := R2) (f := π_set) (x := σ)
      exact h_map
    exact congr_arg (fun (f : R2 ⟶ Ck_RP) => f.hom 1) h1
  let T_RP := ModuleCat.of (ZMod 2) (ι_RP →₀ ZMod 2)
  let f_cat : Ck_S ⟶ T_RP := ModuleCat.ofHom (e_RP.toLinearMap.comp Q)
  let g_cat : Ck_S ⟶ T_RP := ModuleCat.ofHom (Q'.comp e_S.toLinearMap)
  have h_eq : f_cat = g_cat := by
    apply SSet.chainComplex_hom_ext (R := R2)
    intro σ
    have h_hom : (ι_inc_S σ ≫ f_cat).hom = (ι_inc_S σ ≫ g_cat).hom := by
      apply LinearMap.ext
      intro z
      have h_z : z = 0 ∨ z = 1 := by fin_cases z <;> tauto
      rcases h_z with (h0 | h1)
      · rw [h0]; simp
      · have h_goal1 : (ι_inc_S σ ≫ f_cat).hom 1 = e_RP.toLinearMap (Q ((ι_inc_S σ).hom 1)) := by rfl
        have h_goal2 : (ι_inc_S σ ≫ g_cat).hom 1 = Q' (e_S.toLinearMap ((ι_inc_S σ).hom 1)) := by rfl
        have h_left : e_RP.toLinearMap (Q ((ι_inc_S σ).hom 1)) =
            Finsupp.single (π_simplex σ) 1 := by
          rw [h_Q_basis σ, h_basis_RP (π_simplex σ)]
        have h_right : Q' (e_S.toLinearMap ((ι_inc_S σ).hom 1)) =
            Finsupp.single (π_simplex σ) 1 := by
          rw [h_basis_S σ]
          simpa [Q', mapDomainLin, Finsupp.mapDomain_single] using rfl
        have h_z1 : z = 1 := h1
        rw [h_z1, h_goal1, h_goal2, h_left, h_right]
    have h_morph : (ι_inc_S σ ≫ f_cat) = (ι_inc_S σ ≫ g_cat) := by
      have h : (ι_inc_S σ ≫ f_cat).hom = (ι_inc_S σ ≫ g_cat).hom := h_hom
      exact ModuleCat.hom_ext h
    exact h_morph
  have h_comm_Q : e_RP.toLinearMap.comp Q = Q'.comp e_S.toLinearMap := by
    have h : f_cat.hom = g_cat.hom := by rw [h_eq]
    exact h
  have h_fiber' : ∀ (σ τ : ι_S), π_simplex σ = π_simplex τ → σ = τ ∨ σ = h_free.a τ := by
    intro σ τ h
    have h_orig : τ = σ ∨ τ = h_free.a σ := quotientSimplexMap_fiber n k σ τ h
    rcases h_orig with (h_eq | h_ant)
    · exact Or.inl h_eq.symm
    · have h_a2 : h_free.a (h_free.a σ) = σ := by
        simpa [Equiv.trans_apply] using congr_fun (congr_arg Equiv.toFun h_free.sq) σ
      have h_ant2 : σ = h_free.a τ := by
        have h3 : h_free.a τ = h_free.a (h_free.a σ) := by rw [h_ant]
        rw [h3, h_a2]
      exact Or.inr h_ant2
  have h_alg : LinearMap.ker Q' = LinearMap.range P' :=
    ker_mapDomain_eq_range_pMap h_free π_simplex
      (quotientSimplexMap_antipodal n k)
      h_fiber'
      (quotientSimplexMap_surjective n k)
  -- Commutativity of pHash2 with finsupp equivalence (inline proof)
  let a_set2 : X_S ⟶ X_S := TopCat.toSSet.map (TopCat.ofHom apCmap)
  let A2 : Ck_S →ₗ[ZMod 2] Ck_S := ((aHash2 n).f k).hom
  let T_S2 := ModuleCat.of (ZMod 2) (ι_S →₀ ZMod 2)
  let fA2 : Ck_S ⟶ T_S2 := ModuleCat.ofHom (e_S.toLinearMap.comp A2)
  let gA2 : Ck_S ⟶ T_S2 := ModuleCat.ofHom ((involutionAction h_free).comp e_S.toLinearMap)
  have h_eq_A2 : fA2 = gA2 := by
    apply SSet.chainComplex_hom_ext (R := R2)
    intro σ
    have h_hom : (ι_inc_S σ ≫ fA2).hom = (ι_inc_S σ ≫ gA2).hom := by
      apply LinearMap.ext
      intro z
      have h_z : z = 0 ∨ z = 1 := by fin_cases z <;> tauto
      rcases h_z with (h0 | h1)
      · rw [h0]; simp
      · subst h1
        have h_A_basis2 : A2 ((ι_inc_S σ).hom 1) = (ι_inc_S (a_simplex σ)).hom 1 := by
          have h1 : ι_inc_S σ ≫ (aHash2 n).f k = ι_inc_S (a_simplex σ) := by
            have h_map := SSet.ι_chainComplexMap_f (R := R2) (f := a_set2) (x := σ)
            exact h_map
          exact congr_arg (fun (f : R2 ⟶ Ck_S) => f.hom 1) h1
        have h_goal1 : (ι_inc_S σ ≫ fA2).hom 1 = e_S.toLinearMap (A2 ((ι_inc_S σ).hom 1)) := by rfl
        have h_goal2 : (ι_inc_S σ ≫ gA2).hom 1 = involutionAction h_free (e_S.toLinearMap ((ι_inc_S σ).hom 1)) := by rfl
        have h_left : e_S.toLinearMap (A2 ((ι_inc_S σ).hom 1)) = Finsupp.single (a_simplex σ) 1 := by
          rw [h_A_basis2, h_basis_S (a_simplex σ)]
        have h_right : involutionAction h_free (e_S.toLinearMap ((ι_inc_S σ).hom 1)) = Finsupp.single (a_simplex σ) 1 := by
          rw [h_basis_S σ]
          simp [involutionAction, Finsupp.mapDomain_single] <;> rfl
        rw [h_goal1, h_goal2, h_left, h_right]
    have h_morph : (ι_inc_S σ ≫ fA2) = (ι_inc_S σ ≫ gA2) := by
      have h : (ι_inc_S σ ≫ fA2).hom = (ι_inc_S σ ≫ gA2).hom := h_hom
      exact ModuleCat.hom_ext h
    exact h_morph
  have h_comm_A2 : e_S.toLinearMap.comp A2 = (involutionAction h_free).comp e_S.toLinearMap := by
    have h : fA2.hom = gA2.hom := by rw [h_eq_A2]
    exact h
  have h_comm_P : e_S.toLinearMap.comp P = P'.comp e_S.toLinearMap := by
    have hP : P = LinearMap.id + A2 := by rfl
    rw [hP]
    simp [LinearMap.add_comp, LinearMap.comp_add, h_comm_A2] <;> rfl
  have h_ker_Q : LinearMap.ker Q = LinearMap.range P := by
    ext x
    have hQ_eq : ∀ (y : Ck_S), e_RP.toLinearMap (Q y) = Q' (e_S.toLinearMap y) := by
      intro y
      have h := congr_arg (fun (f : Ck_S →ₗ[ZMod 2] (ι_RP →₀ ZMod 2)) => f y) h_comm_Q
      exact h
    have hP_eq : ∀ (y : Ck_S), e_S.toLinearMap (P y) = P' (e_S.toLinearMap y) := by
      intro y
      have h := congr_arg (fun (f : Ck_S →ₗ[ZMod 2] (ι_S →₀ ZMod 2)) => f y) h_comm_P
      exact h
    have h1 : x ∈ LinearMap.ker Q ↔ e_S.toLinearMap x ∈ LinearMap.ker Q' := by
      constructor
      · intro hx
        have h2 : Q x = 0 := hx
        have h3 : Q' (e_S.toLinearMap x) = e_RP.toLinearMap (Q x) := (hQ_eq x).symm
        have h4 : Q' (e_S.toLinearMap x) = 0 := by
          rw [h3, h2] <;> simp
        simpa [LinearMap.mem_ker] using h4
      · intro hx
        have h2 : Q' (e_S.toLinearMap x) = 0 := by
          simpa [LinearMap.mem_ker] using hx
        have h3 : e_RP.toLinearMap (Q x) = Q' (e_S.toLinearMap x) := hQ_eq x
        have h4 : e_RP.toLinearMap (Q x) = 0 := by
          rw [h3, h2] <;> simp
        have h5 : e_RP.toLinearMap (Q x) = e_RP.toLinearMap 0 := by
          rw [h4] <;> simp
        have h6 : Q x = 0 := e_RP.injective h5
        exact h6
    have h2 : e_S.toLinearMap x ∈ LinearMap.ker Q' ↔ e_S.toLinearMap x ∈ LinearMap.range P' := by
      rw [h_alg]
    have h3 : e_S.toLinearMap x ∈ LinearMap.range P' ↔ x ∈ LinearMap.range P := by
      constructor
      · rintro ⟨z, hz⟩
        let y := e_S.symm z
        have h4 : e_S.toLinearMap (P y) = P' (e_S.toLinearMap y) := hP_eq y
        have h5 : e_S.toLinearMap y = z := by simp [y]
        have h6 : e_S.toLinearMap (P y) = e_S.toLinearMap x := by
          rw [h4, h5, hz]
        have h7 : P y = x := e_S.injective h6
        exact ⟨y, h7⟩
      · rintro ⟨y, rfl⟩
        refine ⟨e_S.toLinearMap y, ?_⟩
        have h4 : e_S.toLinearMap (P y) = P' (e_S.toLinearMap y) := hP_eq y
        exact h4.symm
    rw [h1, h2, h3]
  exact h_ker_Q

/-- The quotient chain map is degreewise surjective.

Since every singular simplex of RP^n lifts to S^n (`quotientSimplexMap_surjective`),
the induced map on free modules is surjective via `Finsupp.mapDomain_surjective`. -/
lemma quotientChainMap_surjective (n k : ℕ) :
    Function.Surjective ((quotientChainMap n).f k).hom := by
  classical
  let X_S := sphereSSet n
  let X_RP := rpSSet n
  let ι_S := SingularSimplices n k
  let ι_RP := RPSingularSimplices n k
  let R2 := ModuleCat.of (ZMod 2) (ZMod 2)
  let Z_S : ι_S → ModuleCat (ZMod 2) := fun _ => R2
  let Z_RP : ι_RP → ModuleCat (ZMod 2) := fun _ => R2
  let π : ι_S → ι_RP := quotientSimplexMap n k
  have hπ : Function.Surjective π := quotientSimplexMap_surjective n k
  let Ck_S := (ChainSphere2 n).X k
  let Ck_RP := (ChainRP2 n).X k
  let Q : Ck_S →ₗ[ZMod 2] Ck_RP := ((quotientChainMap n).f k).hom
  let e1_S := ModuleCat.coprodIsoDirectSum Z_S
  let e2_S : (ι_S →₀ ZMod 2) ≃ₗ[ZMod 2] DirectSum ι_S (fun i => ↑(Z_S i)) :=
    finsuppLequivDFinsupp (ι := ι_S) (ZMod 2)
  let e_S : Ck_S ≃ₗ[ZMod 2] (ι_S →₀ ZMod 2) := e1_S.toLinearEquiv.trans e2_S.symm
  let e1_RP := ModuleCat.coprodIsoDirectSum Z_RP
  let e2_RP : (ι_RP →₀ ZMod 2) ≃ₗ[ZMod 2] DirectSum ι_RP (fun i => ↑(Z_RP i)) :=
    finsuppLequivDFinsupp (ι := ι_RP) (ZMod 2)
  let e_RP : Ck_RP ≃ₗ[ZMod 2] (ι_RP →₀ ZMod 2) := e1_RP.toLinearEquiv.trans e2_RP.symm
  let Q' : (ι_S →₀ ZMod 2) →ₗ[ZMod 2] (ι_RP →₀ ZMod 2) := mapDomainLin π
  let π_set : X_S ⟶ X_RP := TopCat.toSSet.map (TopCat.ofHom quotientCmap)
  let ι_inc_S (σ : ι_S) : R2 ⟶ Ck_S := X_S.ιChainComplex (R := R2) σ
  let ι_inc_RP (τ : ι_RP) : R2 ⟶ Ck_RP := X_RP.ιChainComplex (R := R2) τ

  have h_iso_S : ∀ σ, ι_inc_S σ ≫ e1_S.hom =
      ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_S (fun _ => ZMod 2) σ) :=
    fun σ => ModuleCat.ι_coprodIsoDirectSum_hom Z_S σ
  have h_iso_RP : ∀ τ, ι_inc_RP τ ≫ e1_RP.hom =
      ModuleCat.ofHom (DirectSum.lof (ZMod 2) ι_RP (fun _ => ZMod 2) τ) :=
    fun τ => ModuleCat.ι_coprodIsoDirectSum_hom Z_RP τ

  have h_basis_S : ∀ (σ : ι_S), e_S.toLinearMap ((ι_inc_S σ).hom 1) = Finsupp.single σ 1 := by
    intro σ
    have h1 : e1_S.toLinearEquiv ((ι_inc_S σ).hom 1) =
        (DirectSum.lof (ZMod 2) ι_S (fun _ => ZMod 2) σ) 1 :=
      congr_arg (fun (f : R2 ⟶ _) => f.hom 1) (h_iso_S σ)
    have h2 : (DirectSum.lof (ZMod 2) ι_S (fun _ => ZMod 2) σ) 1 =
        DFinsupp.single σ 1 := by
      exact Eq.symm (DirectSum.ext (fun i => ZMod 2) (congrFun rfl))
    have h3 : e2_S.symm (DFinsupp.single σ 1) = Finsupp.single σ 1 := by
      have h_e2 : (e2_S.symm : DirectSum ι_S (fun _ => ZMod 2) → (ι_S →₀ ZMod 2)) = DFinsupp.toFinsupp :=
        finsuppLequivDFinsupp_symm_apply (R := ZMod 2)
      rw [h_e2]
      ext x; simp [DFinsupp.toFinsupp] <;> aesop
    calc
      e_S.toLinearMap ((ι_inc_S σ).hom 1)
        = e2_S.symm (e1_S.toLinearEquiv ((ι_inc_S σ).hom 1)) := by rfl
      _ = e2_S.symm ((DirectSum.lof (ZMod 2) ι_S (fun _ => ZMod 2) σ) 1) := by rw [h1]
      _ = e2_S.symm (DFinsupp.single σ 1) := by rw [h2]
      _ = Finsupp.single σ 1 := h3

  have h_basis_RP : ∀ (τ : ι_RP), e_RP.toLinearMap ((ι_inc_RP τ).hom 1) = Finsupp.single τ 1 := by
    intro τ
    have h1 : e1_RP.toLinearEquiv ((ι_inc_RP τ).hom 1) =
        (DirectSum.lof (ZMod 2) ι_RP (fun _ => ZMod 2) τ) 1 :=
      congr_arg (fun (f : R2 ⟶ _) => f.hom 1) (h_iso_RP τ)
    have h2 : (DirectSum.lof (ZMod 2) ι_RP (fun _ => ZMod 2) τ) 1 =
        DFinsupp.single τ 1 := by
      exact Eq.symm (DirectSum.ext (fun i => ZMod 2) (congrFun rfl))
    have h3 : e2_RP.symm (DFinsupp.single τ 1) = Finsupp.single τ 1 := by
      have h_e2 : (e2_RP.symm : DirectSum ι_RP (fun _ => ZMod 2) → (ι_RP →₀ ZMod 2)) = DFinsupp.toFinsupp :=
        finsuppLequivDFinsupp_symm_apply (R := ZMod 2)
      rw [h_e2]
      ext x; simp [DFinsupp.toFinsupp] <;> aesop
    calc
      e_RP.toLinearMap ((ι_inc_RP τ).hom 1)
        = e2_RP.symm (e1_RP.toLinearEquiv ((ι_inc_RP τ).hom 1)) := by rfl
      _ = e2_RP.symm ((DirectSum.lof (ZMod 2) ι_RP (fun _ => ZMod 2) τ) 1) := by rw [h1]
      _ = e2_RP.symm (DFinsupp.single τ 1) := by rw [h2]
      _ = Finsupp.single τ 1 := h3

  have h_Q_basis : ∀ (σ : ι_S),
      Q ((ι_inc_S σ).hom 1) = (ι_inc_RP (π σ)).hom 1 := by
    intro σ
    have h1 : ι_inc_S σ ≫ (quotientChainMap n).f k = ι_inc_RP (π σ) := by
      have h_map := SSet.ι_chainComplexMap_f (R := R2) (f := π_set) (x := σ)
      exact h_map
    exact congr_arg (fun (f : R2 ⟶ Ck_RP) => f.hom 1) h1

  have h_comm : e_RP.toLinearMap.comp Q = Q'.comp e_S.toLinearMap := by
    let T_RP := ModuleCat.of (ZMod 2) (ι_RP →₀ ZMod 2)
    let f_cat : Ck_S ⟶ T_RP := ModuleCat.ofHom (e_RP.toLinearMap.comp Q)
    let g_cat : Ck_S ⟶ T_RP := ModuleCat.ofHom (Q'.comp e_S.toLinearMap)
    have h_eq : f_cat = g_cat := by
      apply SSet.chainComplex_hom_ext (R := R2)
      intro σ
      have h_hom : (ι_inc_S σ ≫ f_cat).hom = (ι_inc_S σ ≫ g_cat).hom := by
        apply LinearMap.ext
        intro z
        have h_z : z = 0 ∨ z = 1 := by fin_cases z <;> tauto
        rcases h_z with (h0 | h1)
        · rw [h0]; simp
        · have h_goal1 : (ι_inc_S σ ≫ f_cat).hom 1 = e_RP.toLinearMap (Q ((ι_inc_S σ).hom 1)) := by rfl
          have h_goal2 : (ι_inc_S σ ≫ g_cat).hom 1 = Q' (e_S.toLinearMap ((ι_inc_S σ).hom 1)) := by rfl
          have h_left : e_RP.toLinearMap (Q ((ι_inc_S σ).hom 1)) = Finsupp.single (π σ) 1 := by
            rw [h_Q_basis σ, h_basis_RP (π σ)]
          have h_right : Q' (e_S.toLinearMap ((ι_inc_S σ).hom 1)) = Finsupp.single (π σ) 1 := by
            rw [h_basis_S σ]
            simpa [Q', mapDomainLin, Finsupp.mapDomain_single] using rfl
          rw [h1, h_goal1, h_goal2, h_left, h_right]
      have h_morph : (ι_inc_S σ ≫ f_cat) = (ι_inc_S σ ≫ g_cat) := by
        exact ModuleCat.hom_ext h_hom
      exact h_morph
    exact congr_arg (fun (f : Ck_S ⟶ T_RP) => f.hom) h_eq

  have hQ'_surj : Function.Surjective Q' := Finsupp.mapDomain_surjective hπ

  intro y
  let y' := e_RP.toLinearMap y
  rcases hQ'_surj y' with ⟨x', hx'⟩
  let x : Ck_S := e_S.symm x'
  have h1 : e_RP.toLinearMap (Q x) = Q' (e_S.toLinearMap x) := by
    exact congr_arg (fun f => f x) h_comm
  have h2 : e_S.toLinearMap x = x' := by
    simp [x]
  have h3 : e_RP.toLinearMap (Q x) = e_RP.toLinearMap y := by
    rw [h1, h2, hx'] <;> rfl
  have h4 : Q x = y := e_RP.injective h3
  exact ⟨x, h4⟩

end BorsukUlam.QuotientKernel
