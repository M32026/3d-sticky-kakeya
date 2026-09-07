module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Connected.PathConnected

@[expose] public section

namespace AlgebraicTopology

noncomputable section

open CategoryTheory Simplicial TopCat SSet Opposite

universe u

variable (X : TopCat.{u})

/-- The face map δ i on the singular simplicial set corresponds to
    precomposition with stdSimplex.map (δ i). -/
lemma toSSet_face_naturality (i : Fin 2) (e : (toSSet.obj X) _⦋1⦌) :
    (toSSetObjEquiv X (op ⦋0⦌)) ((toSSet.obj X).δ i e) =
      (toSSetObjEquiv X (op ⦋1⦌)) e ∘ (_root_.stdSimplex.map (SimplexCategory.δ i)) := by
  simp [toSSetObjEquiv]
  ; rfl

/-- Forward direction: an edge gives a path. -/
lemma edge_implies_joined {x₀ x₁ : (toSSet.obj X) _⦋0⦌}
    (e : (toSSet.obj X).Edge x₀ x₁) :
    Joined (toSSetObj₀Equiv x₀) (toSSetObj₀Equiv x₁) := by
  let f : C(_root_.stdSimplex ℝ (Fin 2), X) := (toSSetObjEquiv X (op ⦋1⦌)) e.edge
  have h1 : (toSSet.obj X).δ 1 e.edge = x₀ := e.src_eq
  have h0 : (toSSet.obj X).δ 0 e.edge = x₁ := e.tgt_eq
  have h_eq1 : (toSSetObjEquiv X (op ⦋0⦌)) x₀ = f ∘ (_root_.stdSimplex.map (SimplexCategory.δ 1)) := by
    rw [← h1, toSSet_face_naturality X 1 e.edge]
  have h_eq0 : (toSSetObjEquiv X (op ⦋0⦌)) x₁ = f ∘ (_root_.stdSimplex.map (SimplexCategory.δ 0)) := by
    rw [← h0, toSSet_face_naturality X 0 e.edge]
  let dflt : _root_.stdSimplex ℝ (Fin 1) := default
  have h_subsingleton : Subsingleton (_root_.stdSimplex ℝ (Fin 1)) := by exact stdSimplex.instSubsingletonElemForall
  have h_dflt_eq_v0 : dflt = _root_.stdSimplex.vertex (0 : Fin 1) :=
    Subsingleton.elim dflt (_root_.stdSimplex.vertex (0 : Fin 1))
  have hδ1 : (SimplexCategory.δ (1 : Fin 2) : Fin 1 → Fin 2) = fun _ => 0 := by
    funext i
    fin_cases i ; rfl
  have hδ0 : (SimplexCategory.δ (0 : Fin 2) : Fin 1 → Fin 2) = fun _ => 1 := by
    funext i
    fin_cases i ; rfl
  have h_map1 : _root_.stdSimplex.map (SimplexCategory.δ 1) dflt = _root_.stdSimplex.vertex (0 : Fin 2) := by
    rw [h_dflt_eq_v0, _root_.stdSimplex.map_vertex, hδ1]
  have h_map0 : _root_.stdSimplex.map (SimplexCategory.δ 0) dflt = _root_.stdSimplex.vertex (1 : Fin 2) := by
    rw [h_dflt_eq_v0, _root_.stdSimplex.map_vertex, hδ0]
  have h_val1 : toSSetObj₀Equiv x₀ = f (_root_.stdSimplex.vertex (0 : Fin 2)) := by
    have h : toSSetObj₀Equiv x₀ = ((toSSetObjEquiv X (op ⦋0⦌)) x₀) dflt := by rfl
    rw [h, h_eq1]
    exact congr_arg f h_map1
  have h_val0 : toSSetObj₀Equiv x₁ = f (_root_.stdSimplex.vertex (1 : Fin 2)) := by
    have h : toSSetObj₀Equiv x₁ = ((toSSetObjEquiv X (op ⦋0⦌)) x₁) dflt := by rfl
    rw [h, h_eq0]
    exact congr_arg f h_map0
  have h_symm0 : stdSimplexHomeomorphUnitInterval.symm (0 : _root_.unitInterval) = _root_.stdSimplex.vertex (0 : Fin 2) := by
    have h : stdSimplexHomeomorphUnitInterval (_root_.stdSimplex.vertex (0 : Fin 2)) = (0 : _root_.unitInterval) :=
      stdSimplexHomeomorphUnitInterval_zero
    exact ((stdSimplexHomeomorphUnitInterval.symm_apply_apply (_root_.stdSimplex.vertex (0 : Fin 2))).symm.trans (congr_arg stdSimplexHomeomorphUnitInterval.symm h)).symm
  have h_symm1 : stdSimplexHomeomorphUnitInterval.symm (1 : _root_.unitInterval) = _root_.stdSimplex.vertex (1 : Fin 2) := by
    have h : stdSimplexHomeomorphUnitInterval (_root_.stdSimplex.vertex (1 : Fin 2)) = (1 : _root_.unitInterval) :=
      stdSimplexHomeomorphUnitInterval_one
    exact ((stdSimplexHomeomorphUnitInterval.symm_apply_apply (_root_.stdSimplex.vertex (1 : Fin 2))).symm.trans (congr_arg stdSimplexHomeomorphUnitInterval.symm h)).symm
  let γ : C(_root_.unitInterval, X) :=
    ⟨fun t => f (stdSimplexHomeomorphUnitInterval.symm t), by continuity⟩
  have hγ0 : γ 0 = toSSetObj₀Equiv x₀ := by
    have h : γ 0 = f (stdSimplexHomeomorphUnitInterval.symm (0 : _root_.unitInterval)) := by rfl
    rw [h, h_symm0, h_val1]
  have hγ1 : γ 1 = toSSetObj₀Equiv x₁ := by
    have h : γ 1 = f (stdSimplexHomeomorphUnitInterval.symm (1 : _root_.unitInterval)) := by rfl
    rw [h, h_symm1, h_val0]
  exact ⟨γ, hγ0, hγ1⟩

/-- Backward direction: a path gives an edge. -/
lemma joined_implies_edge {x y : X} (h : Joined x y) :
    π₀Rel (x₀ := toSSetObj₀Equiv.symm x)
      (x₁ := toSSetObj₀Equiv.symm y) := by
  let γ : Path x y := h.somePath
  let f : C(_root_.stdSimplex ℝ (Fin 2), X) :=
    ⟨fun s => γ (stdSimplexHomeomorphUnitInterval s), by continuity⟩
  let e : (toSSet.obj X) _⦋1⦌ := (toSSetObjEquiv X (op ⦋1⦌)).symm f
  have h_f_e : (toSSetObjEquiv X (op ⦋1⦌)) e = f :=
    (toSSetObjEquiv X (op ⦋1⦌)).apply_symm_apply f
  have hδ1 : (SimplexCategory.δ (1 : Fin 2) : Fin 1 → Fin 2) = fun _ => 0 := by
    funext i
    fin_cases i ; rfl
  have hδ0 : (SimplexCategory.δ (0 : Fin 2) : Fin 1 → Fin 2) = fun _ => 1 := by
    funext i
    fin_cases i ; rfl
  let dflt : _root_.stdSimplex ℝ (Fin 1) := default
  have h_subsingleton : Subsingleton (_root_.stdSimplex ℝ (Fin 1)) := by exact stdSimplex.instSubsingletonElemForall
  have h_dflt_eq_v0 : dflt = _root_.stdSimplex.vertex (0 : Fin 1) :=
    Subsingleton.elim dflt (_root_.stdSimplex.vertex (0 : Fin 1))
  have h_map1 : _root_.stdSimplex.map (SimplexCategory.δ 1) dflt = _root_.stdSimplex.vertex (0 : Fin 2) := by
    rw [h_dflt_eq_v0, _root_.stdSimplex.map_vertex, hδ1]
  have h_map0 : _root_.stdSimplex.map (SimplexCategory.δ 0) dflt = _root_.stdSimplex.vertex (1 : Fin 2) := by
    rw [h_dflt_eq_v0, _root_.stdSimplex.map_vertex, hδ0]
  have h_fv0 : f (_root_.stdSimplex.vertex (0 : Fin 2)) = x := by
    simp [f, stdSimplexHomeomorphUnitInterval_zero]
  have h_fv1 : f (_root_.stdSimplex.vertex (1 : Fin 2)) = y := by
    simp [f, stdSimplexHomeomorphUnitInterval_one]
  have h_src : (toSSet.obj X).δ 1 e = toSSetObj₀Equiv.symm x := by
    apply (toSSetObjEquiv X (op ⦋0⦌)).injective
    apply ContinuousMap.ext
    intro z
    have h_z : z = dflt := Subsingleton.elim z dflt
    rw [h_z]
    have h1 : ((toSSetObjEquiv X (op ⦋0⦌)) ((toSSet.obj X).δ 1 e)) dflt =
        ((toSSetObjEquiv X (op ⦋1⦌)) e) (_root_.stdSimplex.map (SimplexCategory.δ 1) dflt) := by
      have h_face := toSSet_face_naturality X 1 e
      exact congr_fun h_face dflt
    rw [h1, h_f_e, h_map1, h_fv0]
    simp [toSSetObj₀Equiv_symm_apply]
  have h_tgt : (toSSet.obj X).δ 0 e = toSSetObj₀Equiv.symm y := by
    apply (toSSetObjEquiv X (op ⦋0⦌)).injective
    apply ContinuousMap.ext
    intro z
    have h_z : z = dflt := Subsingleton.elim z dflt
    rw [h_z]
    have h1 : ((toSSetObjEquiv X (op ⦋0⦌)) ((toSSet.obj X).δ 0 e)) dflt =
        ((toSSetObjEquiv X (op ⦋1⦌)) e) (_root_.stdSimplex.map (SimplexCategory.δ 0) dflt) := by
      have h_face := toSSet_face_naturality X 0 e
      exact congr_fun h_face dflt
    rw [h1, h_f_e, h_map0, h_fv1]
    simp [toSSetObj₀Equiv_symm_apply]
  let e' : (toSSet.obj X).Edge (toSSetObj₀Equiv.symm x) (toSSetObj₀Equiv.symm y) :=
    ⟨e, h_src, h_tgt⟩
  exact ⟨e'⟩

/-- Forward map: π₀ of the singular simplicial set → ZerothHomotopy X. -/
noncomputable def singularPiZeroToZerothHomotopy :
    SSet.π₀ (toSSet.obj X) → ZerothHomotopy X :=
  SSet.π₀.lift (fun x => Quotient.mk'' (toSSetObj₀Equiv x))
    (fun {_ _} e => Quotient.sound (edge_implies_joined X e))

/-- Backward map: ZerothHomotopy X → π₀ of the singular simplicial set. -/
noncomputable def zerothHomotopyToSingularPiZero :
    ZerothHomotopy X → SSet.π₀ (toSSet.obj X) :=
  Quotient.lift (fun x : X => SSet.π₀.mk (toSSetObj₀Equiv.symm x))
    (fun {x y} h => by
      have h' : π₀Rel (x₀ := toSSetObj₀Equiv.symm x) (x₁ := toSSetObj₀Equiv.symm y) :=
        joined_implies_edge X h
      rcases h' with ⟨e⟩
      exact SSet.π₀.sound e)

/-- The equivalence between π₀ of the singular simplicial set and ZerothHomotopy. -/
noncomputable def singularPiZeroEquivZerothHomotopy :
    SSet.π₀ (toSSet.obj X) ≃ ZerothHomotopy X := by
  refine' {
    toFun := singularPiZeroToZerothHomotopy X,
    invFun := zerothHomotopyToSingularPiZero X,
    left_inv := _,
    right_inv := _
  }
  · -- left inverse
    intro z
    induction z using SSet.π₀.rec with
    | mk x =>
      have h1 : singularPiZeroToZerothHomotopy X (SSet.π₀.mk x) =
          Quotient.mk'' (toSSetObj₀Equiv x) := by
        exact SSet.π₀.lift_mk _ _ _
      have h2 : zerothHomotopyToSingularPiZero X (Quotient.mk'' (toSSetObj₀Equiv x)) =
          SSet.π₀.mk (toSSetObj₀Equiv.symm (toSSetObj₀Equiv x)) := by
        rfl
      have h3 : toSSetObj₀Equiv.symm (toSSetObj₀Equiv x) = x :=
        toSSetObj₀Equiv.symm_apply_apply x
      rw [h1, h2, h3]
  · -- right inverse
    intro z
    induction z using Quotient.inductionOn' with
    | h x =>
      have h1 : zerothHomotopyToSingularPiZero X (Quotient.mk'' x) =
          SSet.π₀.mk (toSSetObj₀Equiv.symm x) := by rfl
      have h2 : singularPiZeroToZerothHomotopy X (SSet.π₀.mk (toSSetObj₀Equiv.symm x)) =
          Quotient.mk'' (toSSetObj₀Equiv (toSSetObj₀Equiv.symm x)) := by
        exact SSet.π₀.lift_mk _ _ _
      have h3 : toSSetObj₀Equiv (toSSetObj₀Equiv.symm x) = x :=
        toSSetObj₀Equiv.apply_symm_apply x
      rw [h1, h2, h3]

end

end AlgebraicTopology
