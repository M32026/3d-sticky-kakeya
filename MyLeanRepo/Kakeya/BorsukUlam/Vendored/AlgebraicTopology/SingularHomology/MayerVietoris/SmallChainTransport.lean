module

public import Mathlib.Topology.Homeomorph.Lemmas
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.MayerVietoris.BarycentricSubdivision
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.MayerVietoris.SmallChains

@[expose] public section

/-!
# Small Chain Theorem: TwoSubspaces version

We prove the small chain theorem for the TwoSubspaces framework,
by transporting from the cover-based version.

The key step: the TwoSubspaces small subcomplex equals the cover-based
small subcomplex when the cover is {range(jU), range(jV)}.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Simplicial SSet HomologicalComplex
open TopCat (toSSet)

universe w v u

namespace AlgebraicTopology
namespace TwoSubspaces

variable {ts : TwoSubspaces.{w}}

/-- The cover of X by U and V. -/
def coverBySubspaces (ts : TwoSubspaces.{w}) : Bool → Set ts.X :=
  fun b => if b then Set.range ts.jU else Set.range ts.jV

/-!
### Helper: how toSSet.map acts on simplices
-/

/-- `toSSet.map f` acts by postcomposition with f, modulo the equivalence. -/
lemma toSSet_map_comp {X Y : TopCat.{w}} (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ}
    (τ : (toSSet.obj X).obj n) :
    TopCat.toSSetObjEquiv Y n ((toSSet.map f).app n τ) =
      f ∘ (TopCat.toSSetObjEquiv X n τ) := by
  have h : ∀ (x : stdSimplex ℝ (Fin (n.unop.len + 1))),
      (TopCat.toSSetObjEquiv Y n ((toSSet.map f).app n τ)) x =
      (f ∘ (TopCat.toSSetObjEquiv X n τ)) x := by
    intro x
    rfl
  ext x
  exact h x

/-!
### Equivalence of smallness notions

A simplex is "small" (factors through U or V) iff its image is contained
in U or in V (i.e., it's 𝒰-small for the cover {U, V}).
-/

/-- If a simplex factors through U, its range is contained in range(jU). -/
lemma range_of_factorU {n : SimplexCategoryᵒᵖ} {σ : (toSSet.obj ts.X).obj n}
    (h : ∃ (τ : (toSSet.obj ts.U).obj n), (toSSet.map ts.jU).app n τ = σ) :
    Set.range (TopCat.toSSetObjEquiv ts.X n σ) ⊆ Set.range ts.jU := by
  rcases h with ⟨τ, rfl⟩
  have h1 : TopCat.toSSetObjEquiv ts.X n ((toSSet.map ts.jU).app n τ) =
      ts.jU ∘ (TopCat.toSSetObjEquiv ts.U n τ) :=
    toSSet_map_comp ts.jU τ
  rw [h1]
  simp [Set.range_comp]

/-- If a simplex factors through V, its range is contained in range(jV). -/
lemma range_of_factorV {n : SimplexCategoryᵒᵖ} {σ : (toSSet.obj ts.X).obj n}
    (h : ∃ (τ : (toSSet.obj ts.V).obj n), (toSSet.map ts.jV).app n τ = σ) :
    Set.range (TopCat.toSSetObjEquiv ts.X n σ) ⊆ Set.range ts.jV := by
  rcases h with ⟨τ, rfl⟩
  have h1 : TopCat.toSSetObjEquiv ts.X n ((toSSet.map ts.jV).app n τ) =
      ts.jV ∘ (TopCat.toSSetObjEquiv ts.V n τ) :=
    toSSet_map_comp ts.jV τ
  rw [h1]
  simp [Set.range_comp]

/-- If jU is an embedding and range(σ) ⊆ range(jU), then σ factors through U. -/
lemma factorU_of_range_subset
    (h_jU_emb : Topology.IsEmbedding ts.jU)
    {n : SimplexCategoryᵒᵖ} {σ : (toSSet.obj ts.X).obj n}
    (h : Set.range (TopCat.toSSetObjEquiv ts.X n σ) ⊆ Set.range ts.jU) :
    ∃ (τ : (toSSet.obj ts.U).obj n), (toSSet.map ts.jU).app n τ = σ := by
  let eX : (toSSet.obj ts.X).obj n ≃ C(stdSimplex ℝ (Fin (n.unop.len + 1)), ts.X) :=
    TopCat.toSSetObjEquiv ts.X n
  let eU : (toSSet.obj ts.U).obj n ≃ C(stdSimplex ℝ (Fin (n.unop.len + 1)), ts.U) :=
    TopCat.toSSetObjEquiv ts.U n
  let σ' : C(stdSimplex ℝ (Fin (n.unop.len + 1)), ts.X) := eX σ
  have h' : Set.range σ' ⊆ Set.range ts.jU := h
  let e_homeo : ts.U ≃ₜ (Set.range ts.jU : Set ts.X) :=
    Topology.IsEmbedding.toHomeomorph h_jU_emb
  let g : stdSimplex ℝ (Fin (n.unop.len + 1)) → (Set.range ts.jU : Set ts.X) :=
    fun x => ⟨σ' x, h' (Set.mem_range_self x)⟩
  have hg_cont : Continuous g := σ'.continuous.subtype_mk _
  let τ_val : stdSimplex ℝ (Fin (n.unop.len + 1)) → ts.U := e_homeo.symm ∘ g
  have hτ_cont : Continuous τ_val := (e_homeo.symm).continuous.comp hg_cont
  let τ' : C(stdSimplex ℝ (Fin (n.unop.len + 1)), ts.U) := ⟨τ_val, hτ_cont⟩
  let τ : (toSSet.obj ts.U).obj n := eU.symm τ'
  refine ⟨τ, ?_⟩
  have h1 : eX ((toSSet.map ts.jU).app n τ) = ts.jU ∘ τ' :=
    toSSet_map_comp ts.jU τ
  have h_key : ∀ (y : Set.range ts.jU), ts.jU (e_homeo.symm y) = (y : ts.X) := by
    intro y
    have h5 : e_homeo (e_homeo.symm y) = y := e_homeo.apply_symm_apply y
    have h_apply : ∀ (z : ts.U), (e_homeo z : ts.X) = ts.jU z := by
      intro z
      simp [e_homeo, Topology.IsEmbedding.toHomeomorph]
    have h6 : (e_homeo (e_homeo.symm y) : ts.X) = ts.jU (e_homeo.symm y) := h_apply (e_homeo.symm y)
    have h7 : (e_homeo (e_homeo.symm y) : ts.X) = (y : ts.X) := by
      rw [h5]
    rw [←h6, h7]
  have h3 : eX ((toSSet.map ts.jU).app n τ) = eX σ := by
    apply ContinuousMap.ext
    intro x
    have h4 : (eX ((toSSet.map ts.jU).app n τ)) x = (ts.jU ∘ τ') x := by
      exact congr_fun h1 x
    rw [h4]
    dsimp only [Function.comp_apply, τ', τ_val, g]
    have h7 : ts.jU (e_homeo.symm ⟨σ' x, h' (Set.mem_range_self x)⟩) = σ' x := by
      rw [h_key ⟨σ' x, h' (Set.mem_range_self x)⟩]
    exact h7
  exact eX.injective h3

/-- If jV is an embedding and range(σ) ⊆ range(jV), then σ factors through V. -/
lemma factorV_of_range_subset
    (h_jV_emb : Topology.IsEmbedding ts.jV)
    {n : SimplexCategoryᵒᵖ} {σ : (toSSet.obj ts.X).obj n}
    (h : Set.range (TopCat.toSSetObjEquiv ts.X n σ) ⊆ Set.range ts.jV) :
    ∃ (τ : (toSSet.obj ts.V).obj n), (toSSet.map ts.jV).app n τ = σ := by
  let eX : (toSSet.obj ts.X).obj n ≃ C(stdSimplex ℝ (Fin (n.unop.len + 1)), ts.X) :=
    TopCat.toSSetObjEquiv ts.X n
  let eV : (toSSet.obj ts.V).obj n ≃ C(stdSimplex ℝ (Fin (n.unop.len + 1)), ts.V) :=
    TopCat.toSSetObjEquiv ts.V n
  let σ' : C(stdSimplex ℝ (Fin (n.unop.len + 1)), ts.X) := eX σ
  have h' : Set.range σ' ⊆ Set.range ts.jV := h
  let e_homeo : ts.V ≃ₜ (Set.range ts.jV : Set ts.X) :=
    Topology.IsEmbedding.toHomeomorph h_jV_emb
  let g : stdSimplex ℝ (Fin (n.unop.len + 1)) → (Set.range ts.jV : Set ts.X) :=
    fun x => ⟨σ' x, h' (Set.mem_range_self x)⟩
  have hg_cont : Continuous g := σ'.continuous.subtype_mk _
  let τ_val : stdSimplex ℝ (Fin (n.unop.len + 1)) → ts.V := e_homeo.symm ∘ g
  have hτ_cont : Continuous τ_val := (e_homeo.symm).continuous.comp hg_cont
  let τ' : C(stdSimplex ℝ (Fin (n.unop.len + 1)), ts.V) := ⟨τ_val, hτ_cont⟩
  let τ : (toSSet.obj ts.V).obj n := eV.symm τ'
  refine ⟨τ, ?_⟩
  have h1 : eX ((toSSet.map ts.jV).app n τ) = ts.jV ∘ τ' :=
    toSSet_map_comp ts.jV τ
  have h_key : ∀ (y : Set.range ts.jV), ts.jV (e_homeo.symm y) = (y : ts.X) := by
    intro y
    have h5 : e_homeo (e_homeo.symm y) = y := e_homeo.apply_symm_apply y
    have h_apply : ∀ (z : ts.V), (e_homeo z : ts.X) = ts.jV z := by
      intro z
      simp [e_homeo, Topology.IsEmbedding.toHomeomorph]
    have h6 : (e_homeo (e_homeo.symm y) : ts.X) = ts.jV (e_homeo.symm y) := h_apply (e_homeo.symm y)
    have h7 : (e_homeo (e_homeo.symm y) : ts.X) = (y : ts.X) := by
      rw [h5]
    rw [←h6, h7]
  have h3 : eX ((toSSet.map ts.jV).app n τ) = eX σ := by
    apply ContinuousMap.ext
    intro x
    have h4 : (eX ((toSSet.map ts.jV).app n τ)) x = (ts.jV ∘ τ') x := by
      exact congr_fun h1 x
    rw [h4]
    dsimp only [Function.comp_apply, τ', τ_val, g]
    have h7 : ts.jV (e_homeo.symm ⟨σ' x, h' (Set.mem_range_self x)⟩) = σ' x := by
      rw [h_key ⟨σ' x, h' (Set.mem_range_self x)⟩]
    exact h7
  exact eX.injective h3

/-- **Equivalence of smallness notions.**

    Assuming jU and jV are embeddings, a singular simplex is "small"
    (factors through U or V) iff it is 𝒰-small for the cover {range(jU), range(jV)}. -/
theorem isSmallSimplex_iff_cover_small
    (h_jU_emb : Topology.IsEmbedding ts.jU)
    (h_jV_emb : Topology.IsEmbedding ts.jV)
    {n : SimplexCategoryᵒᵖ} {σ : (toSSet.obj ts.X).obj n} :
    isSmallSimplex ts σ ↔
    (∃ (i : Bool), Set.range (TopCat.toSSetObjEquiv ts.X n σ) ⊆ coverBySubspaces ts i) := by
  constructor
  · -- Forward direction: isSmallSimplex → 𝒰-small
    intro h
    rcases h with (hU | hV)
    · -- factors through U
      refine ⟨true, ?_⟩
      simpa [coverBySubspaces] using range_of_factorU hU
    · -- factors through V
      refine ⟨false, ?_⟩
      simpa [coverBySubspaces] using range_of_factorV hV
  · -- Backward direction: 𝒰-small → isSmallSimplex
    rintro ⟨i, h⟩
    cases i
    · -- i = false (V)
      right
      exact factorV_of_range_subset h_jV_emb (by simpa [coverBySubspaces] using h)
    · -- i = true (U)
      left
      exact factorU_of_range_subset h_jU_emb (by simpa [coverBySubspaces] using h)

/-!
### Small chain theorem for two open subspaces

Given two open subspaces of a metric space `X` that cover `X`,
the inclusion of small chains (those contained in U or V) into full
chains is a quasi-isomorphism (induces isomorphisms on homology).

This is the TwoSubspaces version of the small chain theorem,
proved by reduction to the cover-based version.
-/

section TwoOpenSubspaces

open SingularChain

variable {X : Type} [PseudoMetricSpace X]

/-- The cover of X by U and V (for the cover-based small chain theorem). -/
def coverUV (U V : Set X) : Bool → Set X :=
  fun b => if b then U else V

/-- Openness of the cover sets. -/
lemma coverUV_open {U V : Set X} (hU_open : IsOpen U) (hV_open : IsOpen V) :
    ∀ (i : Bool), IsOpen (coverUV U V i) := by
  intro i
  cases i <;> simp [coverUV, hU_open, hV_open]

omit [PseudoMetricSpace X] in
/-- The cover covers X. -/
lemma coverUV_covers {U V : Set X} (hcover : (Set.univ : Set X) ⊆ U ∪ V) :
    (Set.univ : Set X) ⊆ ⋃ (i : Bool), coverUV U V i := by
  intro x _
  have h : x ∈ U ∪ V := hcover (Set.mem_univ x)
  rcases h with (hU | hV)
  · have h' : x ∈ coverUV U V true := by
      simpa [coverUV] using hU
    exact Set.mem_iUnion.mpr ⟨true, h'⟩
  · have h' : x ∈ coverUV U V false := by
      simpa [coverUV] using hV
    exact Set.mem_iUnion.mpr ⟨false, h'⟩

/-- **Small chain theorem for two open subspaces (cover version).**

    Given open sets U, V that cover a pseudometric space X, the inclusion of
    small chains (those entirely contained in U or in V) into full chains
    induces an isomorphism on homology in all degrees ≥ 1. -/
theorem smallChainTheorem_twoOpenSubspaces {U V : Set X}
    (hU_open : IsOpen U) (hV_open : IsOpen V)
    (hcover : (Set.univ : Set X) ⊆ U ∪ V) :
    ∀ (n : ℕ), IsIso (HomologicalComplex.homologyMap (smallChainInclusion_cover (coverUV U V)) (n + 1)) :=
  smallChainTheorem_cover (coverUV U V) (coverUV_open hU_open hV_open) (coverUV_covers hcover)

/-- **Small chain theorem for TwoSubspaces (pseudometric spaces).**

    Given a TwoSubspaces structure where the total space is `TopCat.of X`
    for some pseudometric space `X`, and jU, jV are embeddings with open
    images that cover X, the inclusion of small chains into full chains
    induces an isomorphism on homology in degrees ≥ 1. -/
theorem smallChainTheorem_TwoSubspaces_pseudoMetric
    {X : Type} [PseudoMetricSpace X]
    (ts : TwoSubspaces)
    (hX : ts.X = TopCat.of X)
    (h_jU_emb : Topology.IsEmbedding ts.jU)
    (h_jV_emb : Topology.IsEmbedding ts.jV)
    (hU_open : IsOpen (Set.range ts.jU))
    (hV_open : IsOpen (Set.range ts.jV))
    (hcover : (Set.univ : Set ts.X) ⊆ Set.range ts.jU ∪ Set.range ts.jV) :
    ∀ (n : ℕ), IsIso (HomologicalComplex.homologyMap (smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts) (n + 1)) := by
  induction ts with
  | mk X_ts U_ts V_ts UV_ts jU_ts jV_ts iU_ts iV_ts comm_ts =>
    have hX' : X_ts = TopCat.of X := hX
    subst hX'
    let 𝒰 : Bool → Set X := fun b => if b then Set.range jU_ts else Set.range jV_ts
    have hU_open' : ∀ (i : Bool), IsOpen (𝒰 i) := by
      intro i
      cases i <;> simp [𝒰, hU_open, hV_open]
    have hcover' : (Set.univ : Set X) ⊆ ⋃ (i : Bool), 𝒰 i := by
      intro x _
      have h : x ∈ Set.range jU_ts ∪ Set.range jV_ts := hcover (Set.mem_univ x)
      rcases h with (h1 | h2)
      · exact Set.mem_iUnion.mpr ⟨true, by simpa [𝒰] using h1⟩
      · exact Set.mem_iUnion.mpr ⟨false, by simpa [𝒰] using h2⟩
    have h_cover_thm : ∀ (n : ℕ), IsIso (HomologicalComplex.homologyMap (smallChainInclusion_cover 𝒰) (n + 1)) :=
      smallChainTheorem_cover 𝒰 hU_open' hcover'
    let ts' : TwoSubspaces :=
      { X := TopCat.of X, U := U_ts, V := V_ts, UV := UV_ts,
        jU := jU_ts, jV := jV_ts, iU := iU_ts, iV := iV_ts, comm := comm_ts }
    have h_jU_emb' : Topology.IsEmbedding ts'.jU := h_jU_emb
    have h_jV_emb' : Topology.IsEmbedding ts'.jV := h_jV_emb
    have h_pred_eq : ∀ (n : SimplexCategoryᵒᵖ) (σ : (toSSet.obj (TopCat.of X)).obj n),
        isSmallSimplex ts' σ ↔ isSmallSimplex_cover 𝒰 σ := by
      intro n σ
      have h_iff : isSmallSimplex ts' σ ↔ ∃ (i : Bool), Set.range (ts'.X.toSSetObjEquiv n σ) ⊆ ts'.coverBySubspaces i :=
        isSmallSimplex_iff_cover_small h_jU_emb' h_jV_emb'
      have h_bool : (∃ (i : Bool), Set.range (ts'.X.toSSetObjEquiv n σ) ⊆ ts'.coverBySubspaces i) ↔
          (Set.range (ts'.X.toSSetObjEquiv n σ) ⊆ ts'.coverBySubspaces false ∨
           Set.range (ts'.X.toSSetObjEquiv n σ) ⊆ ts'.coverBySubspaces true) := by
        constructor
        · rintro ⟨i, hi⟩
          cases i <;> tauto
        · rintro (h | h)
          · exact ⟨false, h⟩
          · exact ⟨true, h⟩
      have h1 : ts'.coverBySubspaces false = Set.range jV_ts := by
        simp [ts'] ; rfl
      have h2 : ts'.coverBySubspaces true = Set.range jU_ts := by
        simp [ts'] ; rfl
      rw [h_iff, h_bool, h1, h2]
      ; simp [isSmallSimplex_cover, 𝒰, ts']
    have h_obj_eq : ∀ (n : SimplexCategoryᵒᵖ),
        (smallSubcomplex ts').obj n = (smallSubcomplex_cover 𝒰).obj n := by
      intro n
      ext σ
      simp only [smallSubcomplex, smallSubcomplex_cover, Set.mem_setOf_eq]
      exact h_pred_eq n σ
    have h_eq_sc : smallSubcomplex ts' = smallSubcomplex_cover 𝒰 := by
      ext n x
      exact Set.ext_iff.mp (h_obj_eq n) x
    let h_eq_sset_iso : (smallSSet ts' : SSet) ≅ smallSSet_cover 𝒰 :=
      SSet.Subcomplex.eqToIso h_eq_sc
    have h_comm : h_eq_sset_iso.hom ≫ smallι_cover 𝒰 = smallι ts' := by
      have h : ∀ (S1 S2 : (singularSSet X).Subcomplex) (h : S1 = S2),
          (SSet.Subcomplex.eqToIso h).hom ≫ S2.ι = S1.ι := by
        intro S1 S2 h
        induction h
        ; simp [SSet.Subcomplex.eqToIso]
      exact h (smallSubcomplex ts') (smallSubcomplex_cover 𝒰) h_eq_sc
    let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
    have h_comm' :
        F.map h_eq_sset_iso.hom ≫ smallChainInclusion_cover 𝒰 =
        smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts' := by
      have h2 : F.map h_eq_sset_iso.hom ≫ smallChainInclusion_cover 𝒰 =
          F.map h_eq_sset_iso.hom ≫ F.map (smallι_cover 𝒰) := by rfl
      have h3 : F.map h_eq_sset_iso.hom ≫ F.map (smallι_cover 𝒰) =
          F.map (h_eq_sset_iso.hom ≫ smallι_cover 𝒰) := by
        exact Eq.symm (F.map_comp h_eq_sset_iso.hom (smallι_cover 𝒰))
      have h41 : (h_eq_sset_iso.hom ≫ smallι_cover 𝒰) = smallι ts' := h_comm
      have h4 : F.map (h_eq_sset_iso.hom ≫ smallι_cover 𝒰) = F.map (smallι ts') := by
        rw [h41] ; rfl
      have h5 : F.map (smallι ts') = smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts' := by rfl
      rw [h2, h3, h4, h5]
    intro n
    have h_iso_f : IsIso (F.map h_eq_sset_iso.hom) := by infer_instance
    have h_iso_g : IsIso (HomologicalComplex.homologyMap (smallChainInclusion_cover 𝒰) (n + 1)) := h_cover_thm n
    -- Since f is an iso of chain complexes, homologyMap f (n+1) is also an iso
    let f := F.map h_eq_sset_iso.hom
    let K := F.obj (smallSSet ts')
    let L := F.obj (smallSSet_cover 𝒰)
    have h_homology_comp :
        HomologicalComplex.homologyMap (f ≫ smallChainInclusion_cover 𝒰) (n + 1) =
        HomologicalComplex.homologyMap f (n + 1) ≫ HomologicalComplex.homologyMap (smallChainInclusion_cover 𝒰) (n + 1) :=
      HomologicalComplex.homologyMap_comp _ _ _
    have h_iso_hom_f : IsIso (HomologicalComplex.homologyMap f (n + 1)) := by
      let g := inv f
      have h1 : f ≫ g = 𝟙 K := IsIso.hom_inv_id f
      have h2 : g ≫ f = 𝟙 L := IsIso.inv_hom_id f
      have h3 : HomologicalComplex.homologyMap f (n + 1) ≫ HomologicalComplex.homologyMap g (n + 1) = 𝟙 _ := by
        have h4 : HomologicalComplex.homologyMap (f ≫ g) (n + 1) =
            HomologicalComplex.homologyMap f (n + 1) ≫ HomologicalComplex.homologyMap g (n + 1) :=
          HomologicalComplex.homologyMap_comp _ _ _
        rw [←h4, h1, HomologicalComplex.homologyMap_id]
      have h5 : HomologicalComplex.homologyMap g (n + 1) ≫ HomologicalComplex.homologyMap f (n + 1) = 𝟙 _ := by
        have h6 : HomologicalComplex.homologyMap (g ≫ f) (n + 1) =
            HomologicalComplex.homologyMap g (n + 1) ≫ HomologicalComplex.homologyMap f (n + 1) :=
          HomologicalComplex.homologyMap_comp _ _ _
        rw [←h6, h2, HomologicalComplex.homologyMap_id]
      exact ⟨⟨HomologicalComplex.homologyMap g (n + 1), h3, h5⟩⟩
    have h_iso_hom_comp : IsIso (HomologicalComplex.homologyMap (f ≫ smallChainInclusion_cover 𝒰) (n + 1)) := by
      rw [h_homology_comp]
      haveI h_f'_iso : IsIso (HomologicalComplex.homologyMap f (n + 1)) := h_iso_hom_f
      haveI h_g'_iso : IsIso (HomologicalComplex.homologyMap (smallChainInclusion_cover 𝒰) (n + 1)) := h_iso_g
      exact CategoryTheory.IsIso.comp_isIso' h_f'_iso h_g'_iso
    have h_final : IsIso (HomologicalComplex.homologyMap (smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts') (n + 1)) := by
      have h_eq : HomologicalComplex.homologyMap (smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts') (n + 1) =
          HomologicalComplex.homologyMap (f ≫ smallChainInclusion_cover 𝒰) (n + 1) := by
        congr
        exact h_comm'.symm
      rw [h_eq]
      exact h_iso_hom_comp
    exact h_final

/-- **Degree-0 small chain theorem for TwoSubspaces.**

    The inclusion of small chains into full chains induces an isomorphism on H₀. -/
theorem smallChainTheorem_TwoSubspaces_pseudoMetric_degree0
    {X : Type} [PseudoMetricSpace X]
    (ts : TwoSubspaces)
    (hX : ts.X = TopCat.of X)
    (h_jU_emb : Topology.IsEmbedding ts.jU)
    (h_jV_emb : Topology.IsEmbedding ts.jV)
    (hU_open : IsOpen (Set.range ts.jU))
    (hV_open : IsOpen (Set.range ts.jV))
    (hcover : (Set.univ : Set ts.X) ⊆ Set.range ts.jU ∪ Set.range ts.jV) :
    IsIso (HomologicalComplex.homologyMap (smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts) 0) := by
  induction ts with
  | mk X_ts U_ts V_ts UV_ts jU_ts jV_ts iU_ts iV_ts comm_ts =>
    have hX' : X_ts = TopCat.of X := hX
    subst hX'
    let 𝒰 : Bool → Set X := fun b => if b then Set.range jU_ts else Set.range jV_ts
    have hU_open' : ∀ (i : Bool), IsOpen (𝒰 i) := by
      intro i
      cases i <;> simp [𝒰, hU_open, hV_open]
    have hcover' : (Set.univ : Set X) ⊆ ⋃ (i : Bool), 𝒰 i := by
      intro x _
      have h : x ∈ Set.range jU_ts ∪ Set.range jV_ts := hcover (Set.mem_univ x)
      rcases h with (h1 | h2)
      · exact Set.mem_iUnion.mpr ⟨true, by simpa [𝒰] using h1⟩
      · exact Set.mem_iUnion.mpr ⟨false, by simpa [𝒰] using h2⟩
    have h_cover_thm : IsIso (HomologicalComplex.homologyMap (smallChainInclusion_cover 𝒰) 0) :=
      smallChainTheorem_cover_degree0 𝒰 hU_open' hcover'
    let ts' : TwoSubspaces :=
      { X := TopCat.of X, U := U_ts, V := V_ts, UV := UV_ts,
        jU := jU_ts, jV := jV_ts, iU := iU_ts, iV := iV_ts, comm := comm_ts }
    have h_jU_emb' : Topology.IsEmbedding ts'.jU := h_jU_emb
    have h_jV_emb' : Topology.IsEmbedding ts'.jV := h_jV_emb
    have h_pred_eq : ∀ (n : SimplexCategoryᵒᵖ) (σ : (toSSet.obj (TopCat.of X)).obj n),
        isSmallSimplex ts' σ ↔ isSmallSimplex_cover 𝒰 σ := by
      intro n σ
      have h_iff : isSmallSimplex ts' σ ↔ ∃ (i : Bool), Set.range (ts'.X.toSSetObjEquiv n σ) ⊆ ts'.coverBySubspaces i :=
        isSmallSimplex_iff_cover_small h_jU_emb' h_jV_emb'
      have h_bool : (∃ (i : Bool), Set.range (ts'.X.toSSetObjEquiv n σ) ⊆ ts'.coverBySubspaces i) ↔
          (Set.range (ts'.X.toSSetObjEquiv n σ) ⊆ ts'.coverBySubspaces false ∨
           Set.range (ts'.X.toSSetObjEquiv n σ) ⊆ ts'.coverBySubspaces true) := by
        constructor
        · rintro ⟨i, hi⟩
          cases i <;> tauto
        · rintro (h | h)
          · exact ⟨false, h⟩
          · exact ⟨true, h⟩
      have h1 : ts'.coverBySubspaces false = Set.range jV_ts := by
        simp [ts'] ; rfl
      have h2 : ts'.coverBySubspaces true = Set.range jU_ts := by
        simp [ts'] ; rfl
      rw [h_iff, h_bool, h1, h2]
      ; simp [isSmallSimplex_cover, 𝒰, ts']
    have h_obj_eq : ∀ (n : SimplexCategoryᵒᵖ),
        (smallSubcomplex ts').obj n = (smallSubcomplex_cover 𝒰).obj n := by
      intro n
      ext σ
      simp only [smallSubcomplex, smallSubcomplex_cover, Set.mem_setOf_eq]
      exact h_pred_eq n σ
    have h_eq_sc : smallSubcomplex ts' = smallSubcomplex_cover 𝒰 := by
      ext n x
      exact Set.ext_iff.mp (h_obj_eq n) x
    let h_eq_sset_iso : (smallSSet ts' : SSet) ≅ smallSSet_cover 𝒰 :=
      SSet.Subcomplex.eqToIso h_eq_sc
    have h_comm : h_eq_sset_iso.hom ≫ smallι_cover 𝒰 = smallι ts' := by
      have h : ∀ (S1 S2 : (singularSSet X).Subcomplex) (h : S1 = S2),
          (SSet.Subcomplex.eqToIso h).hom ≫ S2.ι = S1.ι := by
        intro S1 S2 h
        induction h
        ; simp [SSet.Subcomplex.eqToIso]
      exact h (smallSubcomplex ts') (smallSubcomplex_cover 𝒰) h_eq_sc
    let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
    have h_comm' :
        F.map h_eq_sset_iso.hom ≫ smallChainInclusion_cover 𝒰 =
        smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts' := by
      have h2 : F.map h_eq_sset_iso.hom ≫ smallChainInclusion_cover 𝒰 =
          F.map h_eq_sset_iso.hom ≫ F.map (smallι_cover 𝒰) := by rfl
      have h3 : F.map h_eq_sset_iso.hom ≫ F.map (smallι_cover 𝒰) =
          F.map (h_eq_sset_iso.hom ≫ smallι_cover 𝒰) := by
        exact Eq.symm (F.map_comp h_eq_sset_iso.hom (smallι_cover 𝒰))
      have h41 : (h_eq_sset_iso.hom ≫ smallι_cover 𝒰) = smallι ts' := h_comm
      have h4 : F.map (h_eq_sset_iso.hom ≫ smallι_cover 𝒰) = F.map (smallι ts') := by
        rw [h41] ; rfl
      have h5 : F.map (smallι ts') = smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts' := by rfl
      rw [h2, h3, h4, h5]
    have h_iso_f : IsIso (F.map h_eq_sset_iso.hom) := by infer_instance
    let f := F.map h_eq_sset_iso.hom
    let K := F.obj (smallSSet ts')
    let L := F.obj (smallSSet_cover 𝒰)
    have h_homology_comp :
        HomologicalComplex.homologyMap (f ≫ smallChainInclusion_cover 𝒰) 0 =
        HomologicalComplex.homologyMap f 0 ≫ HomologicalComplex.homologyMap (smallChainInclusion_cover 𝒰) 0 :=
      HomologicalComplex.homologyMap_comp _ _ _
    have h_iso_hom_f : IsIso (HomologicalComplex.homologyMap f 0) := by
      let g := inv f
      have h1 : f ≫ g = 𝟙 K := IsIso.hom_inv_id f
      have h2 : g ≫ f = 𝟙 L := IsIso.inv_hom_id f
      have h3 : HomologicalComplex.homologyMap f 0 ≫ HomologicalComplex.homologyMap g 0 = 𝟙 _ := by
        have h4 : HomologicalComplex.homologyMap (f ≫ g) 0 =
            HomologicalComplex.homologyMap f 0 ≫ HomologicalComplex.homologyMap g 0 :=
          HomologicalComplex.homologyMap_comp _ _ _
        rw [←h4, h1, HomologicalComplex.homologyMap_id]
      have h5 : HomologicalComplex.homologyMap g 0 ≫ HomologicalComplex.homologyMap f 0 = 𝟙 _ := by
        have h6 : HomologicalComplex.homologyMap (g ≫ f) 0 =
            HomologicalComplex.homologyMap g 0 ≫ HomologicalComplex.homologyMap f 0 :=
          HomologicalComplex.homologyMap_comp _ _ _
        rw [←h6, h2, HomologicalComplex.homologyMap_id]
      exact ⟨⟨HomologicalComplex.homologyMap g 0, h3, h5⟩⟩
    have h_iso_hom_comp : IsIso (HomologicalComplex.homologyMap (f ≫ smallChainInclusion_cover 𝒰) 0) := by
      rw [h_homology_comp]
      haveI h_f'_iso : IsIso (HomologicalComplex.homologyMap f 0) := h_iso_hom_f
      haveI h_g'_iso : IsIso (HomologicalComplex.homologyMap (smallChainInclusion_cover 𝒰) 0) := h_cover_thm
      exact CategoryTheory.IsIso.comp_isIso' h_f'_iso h_g'_iso
    have h_final : IsIso (HomologicalComplex.homologyMap (smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts') 0) := by
      have h_eq : HomologicalComplex.homologyMap (smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts') 0 =
          HomologicalComplex.homologyMap (f ≫ smallChainInclusion_cover 𝒰) 0 := by
        congr
        exact h_comm'.symm
      rw [h_eq]
      exact h_iso_hom_comp
    exact h_final

end TwoOpenSubspaces

end TwoSubspaces
end AlgebraicTopology

end
