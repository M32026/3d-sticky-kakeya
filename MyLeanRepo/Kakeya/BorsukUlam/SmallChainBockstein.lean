/-
# Small Chain Bockstein Bridge

Proves that the small chain inclusion is a quasi-isomorphism with Z/2 coefficients,
using the Bockstein long exact sequence and the five lemma.

## Main results
- `ssetBocksteinShortExact S`: Bockstein SES for any simplicial set S
-/

import MyLeanRepo.Kakeya.BorsukUlam.BocksteinShortExact
import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallChains
import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallChainTransport
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial SSet Preadditive
open BorsukUlam.BackupRoute

universe u

namespace BorsukUlam.SmallChainBockstein

variable (S : SSet)

/-!
## Generic Bockstein SES for any simplicial set
-/

/-- Multiplication by 2 on C_*(S; ℤ). -/
noncomputable def ssetMultTwo :
    ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj S ⟶
    ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj S :=
  2 • 𝟙 _

/-- Coefficient reduction C_*(S; ℤ) → C_*(S; Z/2). -/
noncomputable def ssetCoeffReduction :
    ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj S ⟶
    ((SSet.chainComplexFunctor AddCommGrpCat).obj R2).obj S :=
  ((SSet.chainComplexFunctor AddCommGrpCat).map coeffReductionMap).app S

/-- Proof that multiplication by 2 followed by coefficient reduction is zero. -/
lemma ssetMultTwo_comp_ssetCoeffReduction :
    ssetMultTwo S ≫ ssetCoeffReduction S = 0 := by
  let F := SSet.chainComplexFunctor AddCommGrpCat
  let f : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ := 2 • 𝟙 _
  let g : AddCommGrpCat.of ℤ ⟶ R2 := coeffReductionMap
  have hfg : f ≫ g = 0 := by
    have h : ∀ (z : ℤ), (f ≫ g) z = 0 := by
      intro z
      have h7 : (2 : ZMod 2) = 0 := by decide
      have h6 : (2 * z : ZMod 2) = 0 := by
        rw [show (2 * z : ZMod 2) = (2 : ZMod 2) * (z : ZMod 2) from by simp]
        rw [h7, zero_mul]
      simpa [f, g, coeffReductionMap] using h6
    exact AddCommGrpCat.ext h
  have h1 : F.map f ≫ F.map g = 0 := by
    calc
      F.map f ≫ F.map g = F.map (f ≫ g) := by rw [←F.map_comp]
      _ = F.map 0 := by rw [hfg]
      _ = 0 := by simp
  have h2 : (F.map f ≫ F.map g).app S = 0 := by
    rw [h1] <;> simp
  have h31 : F.map f = 2 • 𝟙 (F.obj (AddCommGrpCat.of ℤ)) := by
    dsimp only [f]
    rw [Functor.map_smul] <;> simp
  have h3 : (F.map f).app S = ssetMultTwo S := by
    rw [h31] <;> simp [ssetMultTwo] <;> rfl
  have h4 : (F.map g).app S = ssetCoeffReduction S := by rfl
  have h5 : (F.map f ≫ F.map g).app S =
      (F.map f).app S ≫ (F.map g).app S := by rfl
  rw [h5, h3, h4] at h2
  exact h2

/-- The Bockstein short complex for a generic simplicial set S:
    0 → C_*(S;ℤ) --×2→ C_*(S;ℤ) → C_*(S;Z/2) → 0. -/
noncomputable def ssetBocksteinShortComplex :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (ssetMultTwo S) (ssetCoeffReduction S)
    (ssetMultTwo_comp_ssetCoeffReduction S)

/-- For each degree n, the evaluation of the SSet Bockstein short complex is short exact. -/
lemma ssetBocksteinDegreewiseShortExact (n : ℕ) :
    ((ssetBocksteinShortComplex S).map
      (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) n)).ShortExact := by
  let I := S _⦋n⦌
  let F_copower := BorsukUlam.BackupRoute.copowerFunctor I
  let eval_n := HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) n
  let S_eval := (ssetBocksteinShortComplex S).map eval_n
  let S_copower := coeffShortComplex.map F_copower
  have h : S_copower.ShortExact :=
    CategoryTheory.ShortComplex.ShortExact.map_of_exact coeffShortExact F_copower

  have hf : S_eval.f = S_copower.f := by
    change 2 • 𝟙 (F_copower.obj (AddCommGrpCat.of ℤ)) =
      F_copower.map (2 • 𝟙 (AddCommGrpCat.of ℤ))
    exact (copower_map_smul I (AddCommGrpCat.of ℤ)).symm

  have hg : S_eval.g = S_copower.g := by
    dsimp only [ssetBocksteinShortComplex, ssetCoeffReduction, S_eval, S_copower, eval_n]
    <;> rfl

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
    have h_main : ∀ (x₂ : S_copower.X₂),
        (ConcreteCategory.hom S_copower.g) x₂ = 0 →
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

/-- The Bockstein short complex for any SSet is short exact. -/
theorem ssetBocksteinShortExact :
    (ssetBocksteinShortComplex S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact
    (ssetBocksteinShortComplex S)
    (ssetBocksteinDegreewiseShortExact S)

/-!
## Bockstein bridge: ℤ quasi-iso implies Z/2 quasi-iso

Given a map of simplicial sets `f : S₁ ⟶ S₂`, the induced chain maps
for ℤ and Z/2 coefficients form a map of Bockstein short exact sequences.
If the ℤ chain map is a quasi-isomorphism, then so is the Z/2 chain map.
-/

variable {S₁ S₂ : SSet} (f : S₁ ⟶ S₂)

/-- The chain map induced by f with coefficient R. -/
noncomputable def chainMapFor (R : AddCommGrpCat) :
    ((SSet.chainComplexFunctor AddCommGrpCat).obj R).obj S₁ ⟶
    ((SSet.chainComplexFunctor AddCommGrpCat).obj R).obj S₂ :=
  ((SSet.chainComplexFunctor AddCommGrpCat).obj R).map f

/-- The map of Bockstein short complexes induced by a map of simplicial sets. -/
noncomputable def bocksteinShortComplexMap :
    ssetBocksteinShortComplex S₁ ⟶ ssetBocksteinShortComplex S₂ where
  τ₁ := chainMapFor f (AddCommGrpCat.of ℤ)
  τ₂ := chainMapFor f (AddCommGrpCat.of ℤ)
  τ₃ := chainMapFor f R2
  comm₁₂ := by
    dsimp only [ssetBocksteinShortComplex, ssetMultTwo, chainMapFor]
    <;> simp
    <;> rfl
  comm₂₃ := by
    dsimp only [ssetBocksteinShortComplex, ssetCoeffReduction, chainMapFor]
    let F := SSet.chainComplexFunctor AddCommGrpCat
    have h : (F.obj (AddCommGrpCat.of ℤ)).map f ≫ (F.map coeffReductionMap).app S₂ =
        (F.map coeffReductionMap).app S₁ ≫ (F.obj R2).map f := by
      exact (F.map coeffReductionMap).naturality f
    exact h

/-- **Bockstein bridge**: If a map of simplicial sets induces a quasi-isomorphism
    on chain complexes with ℤ coefficients, then it also induces a quasi-isomorphism
    with Z/2 coefficients. -/
theorem bocksteinBridge [h_quasi : QuasiIso (chainMapFor f (AddCommGrpCat.of ℤ))] :
    QuasiIso (chainMapFor f R2) := by
  let φ := bocksteinShortComplexMap f
  have hS₁ : (ssetBocksteinShortComplex S₁).ShortExact :=
    ssetBocksteinShortExact S₁
  have hS₂ : (ssetBocksteinShortComplex S₂).ShortExact :=
    ssetBocksteinShortExact S₂
  have h_def1 : φ.τ₁ = chainMapFor f (AddCommGrpCat.of ℤ) := by rfl
  have h_def2 : φ.τ₂ = chainMapFor f (AddCommGrpCat.of ℤ) := by rfl
  rw [h_def1] at *
  rw [h_def2] at *
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hS₁ hS₂ h_quasi h_quasi

/-!
## Z/2 small chain theorem

Applies the Bockstein bridge to the existing ℤ small chain theorem
to obtain the Z/2 version.
-/

open AlgebraicTopology.TwoSubspaces

/-- The Z/2 small chain theorem: the small chain inclusion is a quasi-isomorphism
    with Z/2 coefficients, derived from the ℤ version via the Bockstein bridge. -/
theorem smallChainTheorem_z2
    {X : Type} [PseudoMetricSpace X]
    (ts : TwoSubspaces)
    (hX : ts.X = TopCat.of X)
    (h_jU_emb : Topology.IsEmbedding ts.jU)
    (h_jV_emb : Topology.IsEmbedding ts.jV)
    (hU_open : IsOpen (Set.range ts.jU))
    (hV_open : IsOpen (Set.range ts.jV))
    (hcover : (Set.univ : Set ts.X) ⊆ Set.range ts.jU ∪ Set.range ts.jV) :
    QuasiIso (smallChainInclusion AddCommGrpCat R2 ts) := by
  have h_int_succ : ∀ (n : ℕ),
      IsIso (HomologicalComplex.homologyMap
        (smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts) (n + 1)) :=
    smallChainTheorem_TwoSubspaces_pseudoMetric ts hX h_jU_emb h_jV_emb
      hU_open hV_open hcover
  have h_int0 : IsIso (HomologicalComplex.homologyMap
      (smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts) 0) :=
    smallChainTheorem_TwoSubspaces_pseudoMetric_degree0 ts hX h_jU_emb h_jV_emb
      hU_open hV_open hcover
  let f_int := smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts
  have h_all : ∀ (k : ℕ), IsIso (HomologicalComplex.homologyMap f_int k) := by
    intro k
    cases k with
    | zero => exact h_int0
    | succ n => exact h_int_succ n
  letI h_quasi_int : QuasiIso f_int := by
    refine' ⟨fun k => _⟩
    have h_iff : QuasiIsoAt f_int k ↔ IsIso (HomologicalComplex.homologyMap f_int k) :=
      quasiIsoAt_iff_isIso_homologyMap f_int k
    exact h_iff.mpr (h_all k)
  have h_eq : chainMapFor (smallι ts) (AddCommGrpCat.of ℤ) = f_int := by
    dsimp only [chainMapFor, smallChainInclusion] <;> rfl
  haveI : QuasiIso (chainMapFor (smallι ts) (AddCommGrpCat.of ℤ)) := by
    exact show QuasiIso f_int from h_quasi_int
  exact bocksteinBridge (smallι ts)

/-- The small chain inclusion is an isomorphism on H_k with Z/2 coefficients, for any k.

    This is the degree-specific form of `smallChainTheorem_z2`. -/
theorem smallChainInclusion_z2_iso
    {X : Type} [PseudoMetricSpace X]
    (ts : TwoSubspaces)
    (hX : ts.X = TopCat.of X)
    (h_jU_emb : Topology.IsEmbedding ts.jU)
    (h_jV_emb : Topology.IsEmbedding ts.jV)
    (hU_open : IsOpen (Set.range ts.jU))
    (hV_open : IsOpen (Set.range ts.jV))
    (hcover : (Set.univ : Set ts.X) ⊆ Set.range ts.jU ∪ Set.range ts.jV)
    (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (smallChainInclusion AddCommGrpCat R2 ts) k) := by
  have h_quasi : QuasiIso (smallChainInclusion AddCommGrpCat R2 ts) :=
    smallChainTheorem_z2 ts hX h_jU_emb h_jV_emb hU_open hV_open hcover
  have h_at : QuasiIsoAt (smallChainInclusion AddCommGrpCat R2 ts) k :=
    h_quasi.quasiIsoAt k
  exact instIsIsoHomologyMapOfQuasiIsoAt (smallChainInclusion AddCommGrpCat R2 ts) k

/-!
## Z/2 Mayer-Vietoris boundary isomorphism

A Z/2-specific version of the Mayer-Vietoris boundary isomorphism,
using the Z/2 small chain theorem.
-/

open AlgebraicTopology.TwoSubspaces

/-- Z/2 Mayer-Vietoris boundary isomorphism: given an open cover U ∪ V = X
    with H_n(U;Z/2) = H_n(V;Z/2) = H_{n+1}(U;Z/2) = H_{n+1}(V;Z/2) = 0,
    we have H_{n+1}(X;Z/2) ≅ H_n(U ∩ V;Z/2). -/
noncomputable def mayerVietoris_boundaryIso_openCover_z2
    {X : Type} [PseudoMetricSpace X]
    (U V : Set X)
    (hU_open : IsOpen U) (hV_open : IsOpen V)
    (hcover : (Set.univ : Set X) ⊆ U ∪ V)
    (n : ℕ)
    (hU_n : IsZero (singularHomology' AddCommGrpCat R2 n
      (twoSubspacesOfOpens U V).U))
    (hV_n : IsZero (singularHomology' AddCommGrpCat R2 n
      (twoSubspacesOfOpens U V).V))
    (hU_succ : IsZero (singularHomology' AddCommGrpCat R2 (n + 1)
      (twoSubspacesOfOpens U V).U))
    (hV_succ : IsZero (singularHomology' AddCommGrpCat R2 (n + 1)
      (twoSubspacesOfOpens U V).V)) :
    singularHomology' AddCommGrpCat R2 (n + 1)
      (twoSubspacesOfOpens U V).X ≅
    singularHomology' AddCommGrpCat R2 n
      (twoSubspacesOfOpens U V).UV := by
  let ts := twoSubspacesOfOpens U V
  have h_jU_emb : Topology.IsEmbedding ts.jU :=
    twoSubspacesOfOpens_jU_emb U V
  have h_jV_emb : Topology.IsEmbedding ts.jV :=
    twoSubspacesOfOpens_jV_emb U V
  have h_pullback : IsPullback ts.iU ts.iV ts.jU ts.jV :=
    twoSubspacesOfOpens_isPullback U V
  have h_range_jU : Set.range ts.jU = U := by
    dsimp only [ts, twoSubspacesOfOpens]
    ext x
    constructor
    · rintro ⟨y, hy⟩
      have h_y : y.val ∈ U := y.prop
      have h_eq : (ts.jU y) = x := hy
      have h_x_in_U : x ∈ U := by
        have h1 : (ts.jU y) = y.val := by simp [ts] ; rfl
        have h2 : x = y.val := h_eq.symm.trans h1
        rw [h2] ; exact h_y
      exact h_x_in_U
    · intro hx
      have h_y : ∃ (y : {x // x ∈ U}), (ts.jU y) = x := by
        refine' ⟨⟨x, hx⟩, _⟩ ; simp [ts] ; rfl
      rcases h_y with ⟨y, hy⟩
      exact ⟨y, hy⟩
  have h_range_jV : Set.range ts.jV = V := by
    dsimp only [ts, twoSubspacesOfOpens]
    ext x
    constructor
    · rintro ⟨y, hy⟩
      have h_y : y.val ∈ V := y.prop
      have h_eq : (ts.jV y) = x := hy
      have h_x_in_V : x ∈ V := by
        have h1 : (ts.jV y) = y.val := by simp [ts] ; rfl
        have h2 : x = y.val := h_eq.symm.trans h1
        rw [h2] ; exact h_y
      exact h_x_in_V
    · intro hx
      have h_y : ∃ (y : {x // x ∈ V}), (ts.jV y) = x := by
        refine' ⟨⟨x, hx⟩, _⟩ ; simp [ts] ; rfl
      rcases h_y with ⟨y, hy⟩
      exact ⟨y, hy⟩
  have h_small_chain_succ :
      IsIso (HomologicalComplex.homologyMap
        (smallChainInclusion AddCommGrpCat R2 ts) (n + 1)) :=
    smallChainInclusion_z2_iso ts rfl h_jU_emb h_jV_emb
      (by rw [h_range_jU]; exact hU_open)
      (by rw [h_range_jV]; exact hV_open)
      (by rw [h_range_jU, h_range_jV]; exact hcover) (n + 1)
  haveI hMono_jU : Mono ts.jU := by
    rw [TopCat.mono_iff_injective ts.jU]
    exact h_jU_emb.injective
  haveI hMono_jV : Mono ts.jV := by
    rw [TopCat.mono_iff_injective ts.jV]
    exact h_jV_emb.injective
  have h_iU_emb : Topology.IsEmbedding ts.iU := by
    have h1 : ∀ (x : ts.UV), ts.iU x = (⟨x.val, x.prop.1⟩ : ts.U) := by
      intro x ; simp [ts, twoSubspacesOfOpens, TopCat.ofHom] ; rfl
    let iU_fun : ts.UV → ts.U := fun x => ts.iU x
    have h_iff : Topology.IsEmbedding ts.iU ↔ Topology.IsEmbedding iU_fun := by exact TopCat.isEmbedding_iff ts.iU
    rw [h_iff]
    have h_sub : (U ∩ V : Set X) ⊆ U := by simp
    have h2 : iU_fun = Set.inclusion h_sub := by
      funext x ; simpa [iU_fun, Set.inclusion] using h1 x
    rw [h2]
    exact Topology.IsEmbedding.inclusion _
  haveI hMono_iU : Mono ts.iU := by
    rw [TopCat.mono_iff_injective ts.iU]
    exact h_iU_emb.injective
  have h_small_succ_iso :
      (smallChainComplex AddCommGrpCat R2 ts).homology (n + 1) ≅
      singularHomology' AddCommGrpCat R2 (n + 1) ts.X := by
    let f := HomologicalComplex.homologyMap (smallChainInclusion AddCommGrpCat R2 ts) (n + 1)
    have h : IsIso f := h_small_chain_succ
    have h_out : ∃ (g : singularHomology' AddCommGrpCat R2 (n + 1) ts.X ⟶
        (smallChainComplex AddCommGrpCat R2 ts).homology (n + 1)),
        f ≫ g = 𝟙 _ ∧ g ≫ f = 𝟙 _ := h.out
    let g := Classical.choose h_out
    have hg : f ≫ g = 𝟙 _ ∧ g ≫ f = 𝟙 _ := Classical.choose_spec h_out
    exact ⟨f, g, hg.1, hg.2⟩
  have h_dw_pullback : DegreewisePullbackAssumption ts :=
    degreewisePullback_of_isPullback_of_embeddings ts h_pullback h_jU_emb h_jV_emb
  have hS : (mvShortComplex AddCommGrpCat R2 ts).ShortExact :=
    mvSES_shortExact' AddCommGrpCat R2 ts h_dw_pullback
  have h_mid_succ : IsZero ((mvShortComplex AddCommGrpCat R2 ts).X₂.homology (n + 1)) := by
    exact isZero_biprod_homology (K := singularChainComplex' AddCommGrpCat R2 ts.U)
      (L := singularChainComplex' AddCommGrpCat R2 ts.V) (n := n + 1) hU_succ hV_succ
  have h_mid_n : IsZero ((mvShortComplex AddCommGrpCat R2 ts).X₂.homology n) := by
    exact isZero_biprod_homology (K := singularChainComplex' AddCommGrpCat R2 ts.U)
      (L := singularChainComplex' AddCommGrpCat R2 ts.V) (n := n) hU_n hV_n
  have h_boundary :
      (mvShortComplex AddCommGrpCat R2 ts).X₃.homology (n + 1) ≅
      (mvShortComplex AddCommGrpCat R2 ts).X₁.homology n :=
    mv_boundaryIso_small R2 ts n hS h_mid_succ h_mid_n
  have h_uv : (mvShortComplex AddCommGrpCat R2 ts).X₁.homology n ≅
      singularHomology' AddCommGrpCat R2 n ts.UV := by
    refine' Iso.refl _
  have h_small_hom : (mvShortComplex AddCommGrpCat R2 ts).X₃.homology (n + 1) ≅
      (smallChainComplex AddCommGrpCat R2 ts).homology (n + 1) := by
    refine' Iso.refl _
  exact h_small_succ_iso.symm ≪≫ h_small_hom.symm ≪≫ h_boundary ≪≫ h_uv

end BorsukUlam.SmallChainBockstein
