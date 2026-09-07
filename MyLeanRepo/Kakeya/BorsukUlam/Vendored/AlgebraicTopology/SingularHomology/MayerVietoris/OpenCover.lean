module

public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.MayerVietoris.Sequence
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.MayerVietoris.SmallChainTransport

@[expose] public section

/-!
# Mayer-Vietoris boundary isomorphism for two open subspaces

Specialization of the Mayer-Vietoris boundary isomorphism to the case
of two open subspaces of a pseudometric space, using the small chain
theorem proved via barycentric subdivision.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Simplicial SSet HomologicalComplex
open TopCat (toSSet)

universe w v u

namespace AlgebraicTopology
namespace TwoSubspaces

section TwoOpenSubspacesMV

variable {X : Type} [PseudoMetricSpace X]

/-- The `TwoSubspaces` structure built from two subsets of `X`. -/
def twoSubspacesOfOpens (U V : Set X) : TwoSubspaces :=
  let jU : TopCat.of U ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let jV : TopCat.of V ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let iU : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of U :=
    TopCat.ofHom ⟨fun x : (U ∩ V : Set X) => ⟨x.val, x.prop.1⟩, by continuity⟩
  let iV : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of V :=
    TopCat.ofHom ⟨fun x : (U ∩ V : Set X) => ⟨x.val, x.prop.2⟩, by continuity⟩
  { X := TopCat.of X,
    U := TopCat.of U,
    V := TopCat.of V,
    UV := TopCat.of (U ∩ V : Set X),
    jU := jU,
    jV := jV,
    iU := iU,
    iV := iV,
    comm := by
      ext x
      ; simp [jU, jV, iU, iV, TopCat.ofHom]  }

/-- jU is an embedding. -/
lemma twoSubspacesOfOpens_jU_emb (U V : Set X)
    : Topology.IsEmbedding (twoSubspacesOfOpens U V).jU := by
  let jU := (twoSubspacesOfOpens U V).jU
  have h1 : ∀ (x : _), jU x = x.val := by
    intro x
    simp [jU, twoSubspacesOfOpens, TopCat.ofHom] ; rfl
  have h_iff : Topology.IsEmbedding jU ↔ Topology.IsEmbedding (fun x : _ => jU x) := by exact TopCat.isEmbedding_iff jU
  rw [h_iff]
  have h2 : (fun x : _ => jU x) = Subtype.val := funext h1
  rw [h2]
  exact Topology.IsEmbedding.subtypeVal

/-- jV is an embedding. -/
lemma twoSubspacesOfOpens_jV_emb (U V : Set X)
    : Topology.IsEmbedding (twoSubspacesOfOpens U V).jV := by
  let jV := (twoSubspacesOfOpens U V).jV
  have h1 : ∀ (x : _), jV x = x.val := by
    intro x
    simp [jV, twoSubspacesOfOpens, TopCat.ofHom] ; rfl
  have h_iff : Topology.IsEmbedding jV ↔ Topology.IsEmbedding (fun x : _ => jV x) := by exact TopCat.isEmbedding_iff jV
  rw [h_iff]
  have h2 : (fun x : _ => jV x) = Subtype.val := funext h1
  rw [h2]
  exact Topology.IsEmbedding.subtypeVal

/-- The intersection square is a pullback in TopCat. -/
lemma twoSubspacesOfOpens_isPullback (U V : Set X)
    : IsPullback
      (twoSubspacesOfOpens U V).iU
      (twoSubspacesOfOpens U V).iV
      (twoSubspacesOfOpens U V).jU
      (twoSubspacesOfOpens U V).jV := by
  let ts := twoSubspacesOfOpens U V
  have h_comm : ts.iU ≫ ts.jU = ts.iV ≫ ts.jV := ts.comm
  have h_uniq : ∀ ⦃T : TopCat⦄ ⦃φ φ' : T ⟶ ts.UV⦄,
      φ ≫ ts.iU = φ' ≫ ts.iU → φ ≫ ts.iV = φ' ≫ ts.iV → φ = φ' := by
    intro T φ φ' h1 _
    have h_mono : Mono ts.iU := by
      rw [TopCat.mono_iff_injective ts.iU]
      intro x y h
      have h_val : (ts.iU x).val = (ts.iU y).val := by
        exact congr_arg Subtype.val h
      have h_x : (ts.iU x).val = x.val := by
        simp [ts] ; rfl
      have h_y : (ts.iU y).val = y.val := by
        simp [ts] ; rfl
      have h_eq : x.val = y.val := by
        rw [←h_x, ←h_y, h_val]
      exact Subtype.ext h_eq
    exact (cancel_mono ts.iU).mp h1
  have h_exists : ∀ ⦃T : TopCat⦄ (a : T ⟶ ts.U) (b : T ⟶ ts.V),
      a ≫ ts.jU = b ≫ ts.jV → ∃ (l : T ⟶ ts.UV), l ≫ ts.iU = a ∧ l ≫ ts.iV = b := by
    intro T a b hfg
    have h_eq : ∀ (w : T), ts.jU (a w) = ts.jV (b w) := by
      intro w
      have h : ((a ≫ ts.jU) w) = ((b ≫ ts.jV) w) := by rw [hfg]
      exact h
    let f : T → X := fun w => (a ≫ ts.jU) w
    have h_f_cont : Continuous f := by
      have h1 : f = fun w : T => ts.jU (a w) := by funext w; rfl
      rw [h1]
      continuity
    have h1 : ∀ (w : T), f w ∈ U := fun w => (a w).prop
    have h2 : ∀ (w : T), f w ∈ V := by
      intro w
      have h : f w = ts.jV (b w) := h_eq w
      rw [h]
      exact (b w).prop
    have h3 : ∀ (w : T), f w ∈ U ∩ V := fun w => ⟨h1 w, h2 w⟩
    let l_val : T → ts.UV := fun w => ⟨f w, h3 w⟩
    have h_l_cont : Continuous l_val := by
      exact h_f_cont.subtype_mk _
    let l : T ⟶ ts.UV := TopCat.ofHom ⟨l_val, h_l_cont⟩
    refine' ⟨l, _⟩
    constructor
    · ext w
      ; simp [l, l_val, f, TopCat.ofHom] ; rfl
    · ext w
      ; simp [l, l_val, f, TopCat.ofHom] ; exact Subtype.ext (h_eq w)
  exact IsPullback.mk' h_comm h_uniq h_exists

/-- **Mayer-Vietoris boundary isomorphism for two open subspaces.**

    Given two open subspaces U, V of a pseudometric space X with U ∪ V = X,
    and given that H_n(U) = H_n(V) = H_{n+1}(U) = H_{n+1}(V) = 0,
    we have H_{n+1}(X) ≅ H_n(U ∩ V).

    Uses the small chain theorem (barycentric subdivision) for degree n+1 ≥ 1. -/
noncomputable def mayerVietoris_boundaryIso_openCover
    (U V : Set X)
    (hU_open : IsOpen U) (hV_open : IsOpen V)
    (hcover : (Set.univ : Set X) ⊆ U ∪ V)
    (n : ℕ)
    (hU_n : IsZero (singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) n
      (twoSubspacesOfOpens U V).U))
    (hV_n : IsZero (singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) n
      (twoSubspacesOfOpens U V).V))
    (hU_succ : IsZero (singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) (n + 1)
      (twoSubspacesOfOpens U V).U))
    (hV_succ : IsZero (singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) (n + 1)
      (twoSubspacesOfOpens U V).V)) :
    singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) (n + 1)
      (twoSubspacesOfOpens U V).X ≅
    singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) n
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
        rw [h2]
        exact h_y
      exact h_x_in_U
    · intro hx
      have h_y : ∃ (y : {x // x ∈ U}), (ts.jU y) = x := by
        refine' ⟨⟨x, hx⟩, _⟩
        ; simp [ts] ; rfl
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
        rw [h2]
        exact h_y
      exact h_x_in_V
    · intro hx
      have h_y : ∃ (y : {x // x ∈ V}), (ts.jV y) = x := by
        refine' ⟨⟨x, hx⟩, _⟩
        ; simp [ts] ; rfl
      rcases h_y with ⟨y, hy⟩
      exact ⟨y, hy⟩
  have h_small_chain_succ :
      IsIso (HomologicalComplex.homologyMap (smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts) (n + 1)) :=
    smallChainTheorem_TwoSubspaces_pseudoMetric ts rfl h_jU_emb h_jV_emb
      (by rw [h_range_jU]; exact hU_open)
      (by rw [h_range_jV]; exact hV_open)
      (by rw [h_range_jU, h_range_jV]; exact hcover) n
  -- Now apply mayerVietoris_boundaryIso'
  -- We need h_small_chain : ∀ k, IsIso (... k), but we only have it for n+1
  -- However, the proof only uses it at n+1, so we can use a modified proof
  haveI hMono_jU : Mono ts.jU := by
    rw [TopCat.mono_iff_injective ts.jU]
    exact h_jU_emb.injective
  haveI hMono_jV : Mono ts.jV := by
    rw [TopCat.mono_iff_injective ts.jV]
    exact h_jV_emb.injective
  have h_iU_emb : Topology.IsEmbedding ts.iU := by
    have h1 : ∀ (x : ts.UV), ts.iU x = (⟨x.val, x.prop.1⟩ : ts.U) := by
      intro x
      simp [ts, twoSubspacesOfOpens, TopCat.ofHom] ; rfl
    let iU_fun : ts.UV → ts.U := fun x => ts.iU x
    have h_iff : Topology.IsEmbedding ts.iU ↔ Topology.IsEmbedding iU_fun := by exact TopCat.isEmbedding_iff ts.iU
    rw [h_iff]
    have h_sub : (U ∩ V : Set X) ⊆ U := by simp
    have h2 : iU_fun = Set.inclusion h_sub := by
      funext x
      simpa [iU_fun, Set.inclusion] using h1 x
    rw [h2]
    exact Topology.IsEmbedding.inclusion _
  haveI hMono_iU : Mono ts.iU := by
    rw [TopCat.mono_iff_injective ts.iU]
    exact h_iU_emb.injective
  have h_small_succ_iso :
      (smallChainComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).homology (n + 1) ≅
      singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) (n + 1) ts.X := by
    let f := HomologicalComplex.homologyMap (smallChainInclusion AddCommGrpCat (AddCommGrpCat.of ℤ) ts) (n + 1)
    have h : IsIso f := h_small_chain_succ
    have h_out : ∃ (g : singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) (n + 1) ts.X ⟶
        (smallChainComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).homology (n + 1)),
        f ≫ g = 𝟙 _ ∧ g ≫ f = 𝟙 _ := h.out
    let g := Classical.choose h_out
    have hg : f ≫ g = 𝟙 _ ∧ g ≫ f = 𝟙 _ := Classical.choose_spec h_out
    exact ⟨f, g, hg.1, hg.2⟩
  have h_dw_pullback : DegreewisePullbackAssumption ts :=
    degreewisePullback_of_isPullback_of_embeddings ts h_pullback h_jU_emb h_jV_emb
  have hS : (mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).ShortExact :=
    mvSES_shortExact' AddCommGrpCat (AddCommGrpCat.of ℤ) ts h_dw_pullback
  have h_mid_succ : IsZero ((mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).X₂.homology (n + 1)) := by
    exact isZero_biprod_homology (K := singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) ts.U)
      (L := singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) ts.V) (n := n + 1) hU_succ hV_succ
  have h_mid_n : IsZero ((mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).X₂.homology n) := by
    exact isZero_biprod_homology (K := singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) ts.U)
      (L := singularChainComplex' AddCommGrpCat (AddCommGrpCat.of ℤ) ts.V) (n := n) hU_n hV_n
  have h_boundary :
      (mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).X₃.homology (n + 1) ≅
      (mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).X₁.homology n :=
    mv_boundaryIso_small (AddCommGrpCat.of ℤ) ts n hS h_mid_succ h_mid_n
  have h_uv : (mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).X₁.homology n ≅
      singularHomology' AddCommGrpCat (AddCommGrpCat.of ℤ) n ts.UV := by
    refine' Iso.refl _
  have h_small_hom : (mvShortComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).X₃.homology (n + 1) ≅
      (smallChainComplex AddCommGrpCat (AddCommGrpCat.of ℤ) ts).homology (n + 1) := by
    refine' Iso.refl _
  exact h_small_succ_iso.symm ≪≫ h_small_hom.symm ≪≫ h_boundary ≪≫ h_uv

end TwoOpenSubspacesMV

end TwoSubspaces
end AlgebraicTopology

end
