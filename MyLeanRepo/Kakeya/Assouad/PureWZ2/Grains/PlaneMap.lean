import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.CrossNormal
import MyLeanRepo.Kakeya.Assouad.WZ1.CombinatorialPigeonhole
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowPruning
import MyLeanRepo.Kakeya.Assouad.WZ1.WeakPlaninessFromNarrow
import MyLeanRepo.Kakeya.Assouad.WZ1.FiniteScaleLipschitz
import MyLeanRepo.Kakeya.Assouad.WZ1.FinestCellPlaneMap
import MyLeanRepo.Kakeya.Assouad.WZ1.GreedyColoring
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BaseConfig
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TransversePairPaper
import Mathlib.Geometry.Euclidean.Basic

/-!
# Pure WZ2 plane-map infrastructure

UTS-free combinatorial and geometric building blocks for constructing a
1-Lipschitz unit-norm plane map with controlled incidence on a cropped
cubical shading.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

namespace PureWZ2PlaneMap

attribute [local instance] Classical.propDecidable

/-!
## Cross-product plane map geometry
-/

/-- The inner product of `u` with `cross(u,v)` is zero. -/
lemma inner_cross_self_left (u v : Point3) :
    inner ℝ u (wz1Cross u v) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  have hstar : star (u : Fin 3 → ℝ) = (u : Fin 3 → ℝ) := by
    ext i; simp
  rw [hstar, dotProduct_comm]
  exact dot_self_cross (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)

/-- The inner product of `v` with `cross(u,v)` is zero. -/
lemma inner_cross_self_right (u v : Point3) :
    inner ℝ v (wz1Cross u v) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  have hstar : star (v : Fin 3 → ℝ) = (v : Fin 3 → ℝ) := by
    ext i; simp
  rw [hstar, dotProduct_comm]
  exact dot_cross_self (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)

/--
The scalar triple product identity:
`inner(w, cross(u,v)) = wz1TripleProduct u v w`.
-/
lemma inner_cross_triple_product (u v w : Point3) :
    inner ℝ w (wz1Cross u v) = wz1TripleProduct u v w := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  have hstar : star (w : Fin 3 → ℝ) = (w : Fin 3 → ℝ) := by
    ext i; simp
  rw [hstar, dotProduct_comm]
  have hperm :
      (w : Fin 3 → ℝ) ⬝ᵥ (wz1Cross u v : Fin 3 → ℝ) =
      (u : Fin 3 → ℝ) ⬝ᵥ (wz1Cross v w : Fin 3 → ℝ) :=
    triple_product_permutation
      (w : Fin 3 → ℝ) (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
  rw [hperm]
  exact triple_product_eq_det
    (u : Fin 3 → ℝ) (v : Fin 3 → ℝ) (w : Fin 3 → ℝ)

/--
Normalized cross product incidence formula.
-/
lemma normalized_cross_incidence (u v w : Point3)
    (hpos : 0 < ‖wz1Cross u v‖) :
    |inner ℝ w ((‖wz1Cross u v‖)⁻¹ • wz1Cross u v)| =
      |wz1TripleProduct u v w| / ‖wz1Cross u v‖ := by
  have hinner : inner ℝ w ((‖wz1Cross u v‖)⁻¹ • wz1Cross u v) =
      (‖wz1Cross u v‖)⁻¹ * inner ℝ w (wz1Cross u v) := by
    rw [inner_smul_right]
  rw [hinner, inner_cross_triple_product u v w]
  rw [abs_mul, abs_inv, abs_of_pos hpos]
  ring

/-- The normalized cross product has unit norm. -/
lemma normalized_cross_unit (u v : Point3)
    (hpos : 0 < ‖wz1Cross u v‖) :
    ‖(‖wz1Cross u v‖)⁻¹ • wz1Cross u v‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
  field_simp [hpos.ne']

/-!
## Subtype-domain finite-scale Lipschitz wrapper

Direct proof adapted from WZ1 `wz1_finite_scale_lipschitz`, but the domain
is a subtype `{p // p ∈ E}` rather than a set with membership arguments.
-/

/--
Subtype-domain finite-scale Lipschitz.

Given unit norm, constancy at `s^N`, and one-scale bounds `2*s^k`,
conclude `LipschitzWith (2/s)` on the subtype.
-/
theorem finite_scale_lipschitz_subtype
    {E : Set Point3}
    (N : ℕ) (hN : 1 ≤ N)
    (s : ℝ) (hs_pos : 0 < s) (_hs_le_one : s ≤ 1)
    (V : {p : Point3 // p ∈ E} → Point3)
    (hunit : ∀ (x : {p // p ∈ E}), ‖V x‖ = 1)
    (hconst : ∀ (x y : {p // p ∈ E}),
      dist (x : Point3) (y : Point3) ≤ s ^ N → V x = V y)
    (honeScale : ∀ (k : ℕ), 1 ≤ k → k < N →
      ∀ (x y : {p // p ∈ E}),
        dist (x : Point3) (y : Point3) ≤ s ^ k →
          dist (V x) (V y) ≤ 2 * s ^ k) :
    LipschitzWith (Real.toNNReal (2 / s)) V := by
  let C : NNReal := Real.toNNReal (2 / s)
  have hC_pos : 0 < 2 / s := by positivity
  have hC_nonneg : 0 ≤ (C : ℝ) := by positivity
  have hcoe : (C : ℝ) = 2 / s := by
    simp [C, hC_pos.le]
  have hmain : ∀ (x y : {p // p ∈ E}),
      dist (V x) (V y) ≤ (C : ℝ) * dist (x : Point3) (y : Point3) := by
    intro x y
    set d : ℝ := dist (x : Point3) (y : Point3) with hd
    have hgoal : dist (V x) (V y) ≤ (2 / s) * d := by
      by_cases h1 : d ≤ s ^ N
      · -- Constancy case
        have heq : V x = V y := hconst x y h1
        rw [heq]
        simp [hd] <;> positivity
      · -- d > s^N
        have h1' : s ^ N < d := by linarith
        by_cases h2 : d ≤ s
        · -- s^N < d ≤ s, find largest k < N with d ≤ s^k
          have hN2 : 2 ≤ N := by
            by_contra h
            have hlt : N < 2 := by linarith
            have hN1 : N = 1 := by omega
            rw [hN1] at h1' <;> linarith
          let S : Finset ℕ := Finset.filter (fun k => d ≤ s ^ k) (Finset.range N)
          have hS1 : 1 ∈ Finset.range N := by
            simp only [Finset.mem_range] <;> linarith
          have hS2 : d ≤ s ^ 1 := by simpa [pow_one] using h2
          have h1in : 1 ∈ S := by
            rw [Finset.mem_filter] <;> exact ⟨hS1, hS2⟩
          have hSnonempty : S.Nonempty := ⟨1, h1in⟩
          let k := S.max' hSnonempty
          have hkin : k ∈ S := Finset.max'_mem S hSnonempty
          have hkin' : k ∈ Finset.range N ∧ d ≤ s ^ k := by
            rwa [Finset.mem_filter] at hkin
          have hk_lt_N : k < N := Finset.mem_range.mp hkin'.1
          have hdk : d ≤ s ^ k := hkin'.2
          have hk_ge1 : 1 ≤ k := Finset.le_max' S 1 h1in
          have hdk1 : s ^ (k + 1) < d := by
            by_cases h : k + 1 < N
            · have hnot : k + 1 ∉ S := by
                intro hmem
                have hle : k + 1 ≤ k := Finset.le_max' S (k + 1) hmem
                linarith
              have hr : k + 1 ∈ Finset.range N := by
                simp only [Finset.mem_range] <;> linarith
              have hiff : (k + 1 ∈ S) ↔ d ≤ s ^ (k + 1) := by
                constructor
                · intro hmem
                  exact (Finset.mem_filter.mp hmem).2
                · intro hle
                  exact Finset.mem_filter.mpr ⟨hr, hle⟩
              have h' : ¬(d ≤ s ^ (k + 1)) := mt hiff.mpr hnot
              exact lt_of_not_ge h'
            · have hkN : k + 1 = N := by omega
              rw [hkN] <;> exact h1'
          have h9 : s * s ^ k < d := by
            simpa [pow_succ'] using hdk1
          have hdiv : (s * s ^ k) / s = s ^ k := by
            field_simp [hs_pos.ne'] <;> ring
          have hsk : s ^ k < d / s := by
            calc s ^ k
              = (s * s ^ k) / s := hdiv.symm
            _ < d / s := by gcongr
          have hbound : dist (V x) (V y) ≤ 2 * s ^ k :=
            honeScale k hk_ge1 hk_lt_N x y hdk
          calc dist (V x) (V y)
            ≤ 2 * s ^ k := hbound
          _ ≤ 2 * (d / s) := by gcongr
          _ = (2 / s) * d := by
            ring
        · -- d > s, unit norms give dist ≤ 2 < (2/s)*d
          have h2' : s < d := by linarith
          have h3 : dist (V x) (V y) ≤ ‖V x‖ + ‖V y‖ := by
            calc dist (V x) (V y)
              = ‖V x - V y‖ := by rw [dist_eq_norm]
            _ ≤ ‖V x‖ + ‖V y‖ := norm_sub_le (V x) (V y)
          have h4 : ‖V x‖ = 1 := hunit x
          have h5 : ‖V y‖ = 1 := hunit y
          have h6 : dist (V x) (V y) ≤ 2 := by
            calc dist (V x) (V y)
              ≤ ‖V x‖ + ‖V y‖ := h3
            _ = 1 + 1 := by rw [h4, h5]
            _ = 2 := by norm_num
          have h7 : (2 : ℝ) < (2 / s) * d := by
            have h8 : (2 / s) * s = 2 := by
              field_simp [hs_pos.ne']
            nlinarith
          linarith
    rw [hcoe]
    exact hgoal
  -- Convert dist bound to edist bound for LipschitzWith
  have hfinal : ∀ (x y : {p // p ∈ E}),
      edist (V x) (V y) ≤ (C : ENNReal) * edist x y := by
    intro x y
    have hdist : dist (V x) (V y) ≤ (C : ℝ) * dist (x : Point3) (y : Point3) :=
      hmain x y
    have h1 : edist (V x) (V y) = ENNReal.ofReal (dist (V x) (V y)) :=
      edist_dist (V x) (V y)
    have h2 : edist x y = ENNReal.ofReal (dist (x : Point3) (y : Point3)) :=
      edist_dist x y
    rw [h1, h2]
    have h3 : ENNReal.ofReal (dist (V x) (V y)) ≤
        ENNReal.ofReal ((C : ℝ) * dist (x : Point3) (y : Point3)) :=
      ENNReal.ofReal_le_ofReal hdist
    have hCnonneg : 0 ≤ (C : ℝ) := by positivity
    have h41 : ENNReal.ofReal ((C : ℝ) * dist (x : Point3) (y : Point3)) =
        ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (dist (x : Point3) (y : Point3)) :=
      ENNReal.ofReal_mul hCnonneg
    have h42 : ENNReal.ofReal (C : ℝ) = (C : ENNReal) := by simp
    rw [h41, h42] at h3
    exact h3
  exact hfinal

/-!
## Re-exported UTS-free WZ1 infrastructure
-/

/-- Combinatorial pigeonhole (reused from WZ1). -/
alias pureWZ2_combinatorial_pigeonhole := combinatorial_pigeonhole

/-- Counted-broad pruning (reused from WZ1). -/
alias pureWZ2_narrow_pruning := wz1_narrow_pruning

/-- Cross-product normal construction (reused from WZ1). -/
alias pureWZ2_cross_normal := wz1_cross_normal

/-- Finite-scale Lipschitz combinator (reused from WZ1). -/
alias pureWZ2_finite_scale_lipschitz := wz1_finite_scale_lipschitz

/-- Greedy graph coloring (reused from WZ1/Mathlib). -/
alias pureWZ2_colorable_of_max_degree := SimpleGraph.colorable_of_forall_degree_le

/-- Weak planiness from narrow refinement (reused from WZ1). -/
alias pureWZ2_weak_planiness_from_narrow := wz1_weak_planiness_from_narrow

/-!
## Incidence weakening and plane-map assembly
-/

/-- Weaken the incidence scale of a weak plane map. -/
def weaken_weak_plane_map_incidence
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {s t : ℝ} (hst : s ≤ t)
    (data : WZ1WeakPlaneMapData Y s) :
    WZ1WeakPlaneMapData Y t :=
  { planeMap := data.planeMap
    measurable := data.measurable
    unit := data.unit
    incidence := fun i p hp =>
      (data.incidence i p hp).trans hst }

/--
Assemble a weak plane map from a counted-narrow refinement and counting bounds.

This is a thin wrapper around `wz1_weak_planiness_from_narrow` that extracts
the selected shading and plane map from the package.

Given:
- A counted-narrow shading (from narrow pruning)
- Close-direction count bound `R`
- Multiplicity growth condition

Produces a selected subshading retaining ≥ 1/4 of the narrow mass, with a
weak plane map of incidence `tau / kappa`.
-/
theorem plane_map_from_narrow
    {delta kappa tau : ℝ} {Q R : ℕ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hkappa_pos : 0 < kappa)
    (hF : F.Nonempty)
    (narrow : WZ1NarrowRefinementData Y tau Q)
    (hclose : ∀ p ∈ narrow.shading.union, ∀ i,
      p ∈ narrow.shading.carrier i →
        wz1CloseDirectionCount narrow.shading p i kappa < R)
    (hmult : ∀ p ∈ narrow.shading.union,
      let mu := narrow.shading.pointMultiplicity p
      4 * (Q + 3 * R * mu ^ 2) ≤ 3 * mu ^ 3) :
    ∃ (selected : Kakeya.Streamlined.TubeShading F)
      (planeMap : WZ1WeakPlaneMapData selected (tau / kappa)),
      IsSubshading selected narrow.shading ∧
      (1 / 4 : ENNReal) * narrow.shading.mass ≤ selected.mass := by
  have h_main : ∃ (package : WZ1WeakPlaninessPackage Y tau Q kappa),
      package.narrow = narrow :=
    wz1_weak_planiness_from_narrow
      delta kappa tau Q R hkappa_pos F hF Y narrow hclose hmult
  rcases h_main with ⟨package, rfl⟩
  exact ⟨package.selected, package.planeMap,
    package.selected_subshading, package.selected_mass_lower⟩

/--
Version of `plane_map_from_narrow` with incidence weakened to `6 * delta`.

Use when `tau / kappa ≤ 6 * delta`.
-/
theorem plane_map_from_narrow_six_delta
    {delta kappa tau : ℝ} {Q R : ℕ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hkappa_pos : 0 < kappa)
    (hF : F.Nonempty)
    (narrow : WZ1NarrowRefinementData Y tau Q)
    (hclose : ∀ p ∈ narrow.shading.union, ∀ i,
      p ∈ narrow.shading.carrier i →
        wz1CloseDirectionCount narrow.shading p i kappa < R)
    (hmult : ∀ p ∈ narrow.shading.union,
      let mu := narrow.shading.pointMultiplicity p
      4 * (Q + 3 * R * mu ^ 2) ≤ 3 * mu ^ 3)
    (hincidence : tau / kappa ≤ 6 * delta) :
    ∃ (selected : Kakeya.Streamlined.TubeShading F)
      (planeMap : WZ1WeakPlaneMapData selected (6 * delta)),
      IsSubshading selected narrow.shading ∧
      (1 / 4 : ENNReal) * narrow.shading.mass ≤ selected.mass := by
  have h := plane_map_from_narrow hkappa_pos hF narrow hclose hmult
  rcases h with ⟨selected, planeMap, hsub, hmass⟩
  let planeMap' := weaken_weak_plane_map_incidence hincidence planeMap
  exact ⟨selected, planeMap', hsub, hmass⟩

/-!
## Finest-cell constancy and Lipschitz refinement
-/

/-- Finest-cell plane-map refinement (reused from WZ1). -/
alias pureWZ2_finest_cell_plane_map := wz1_finest_cell_plane_map

/--
Extract constancy-at-delta from a finest-cell plane-map data.

If two points in the selected shading are within distance `delta`, they lie in
the same cell and therefore have the same representative plane-map value.
-/
lemma finest_cell_constancy
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {cellCount : ℕ} {cell : Point3 → Fin cellCount}
    {planeMap : Point3 → Point3} {capCount : ℕ}
    (data : WZ1FinestCellPlaneMapData Y cell planeMap capCount) :
    ∀ (p : Point3), p ∈ data.shading.union →
      ∀ (q : Point3), q ∈ data.shading.union →
        dist p q ≤ delta →
          data.representativeMap p = data.representativeMap q := by
  intro p hp q hq hdist
  have hsame : cell p = cell q := data.nearby_same_cell p hp q hq hdist
  exact data.constant_on_cells p hp q hq hsame

/--
Generalized finite-scale Lipschitz on a subtype, with one-scale coefficient `C`.

Given unit norm, constancy at `s^N`, and one-scale bounds `C * s^k`,
conclude `LipschitzWith (C / s)` on the subtype.
-/
theorem finite_scale_lipschitz_subtype_general
    {E : Set Point3}
    (N : ℕ) (hN : 1 ≤ N)
    (s : ℝ) (hs_pos : 0 < s) (_hs_le_one : s ≤ 1)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC_two : 2 ≤ C)
    (V : {p : Point3 // p ∈ E} → Point3)
    (hunit : ∀ (x : {p // p ∈ E}), ‖V x‖ = 1)
    (hconst : ∀ (x y : {p // p ∈ E}),
      dist (x : Point3) (y : Point3) ≤ s ^ N → V x = V y)
    (honeScale : ∀ (k : ℕ), 1 ≤ k → k < N →
      ∀ (x y : {p // p ∈ E}),
        dist (x : Point3) (y : Point3) ≤ s ^ k →
          dist (V x) (V y) ≤ C * s ^ k) :
    LipschitzWith (Real.toNNReal (C / s)) V := by
  let K : NNReal := Real.toNNReal (C / s)
  have hK_pos : 0 ≤ C / s := by positivity
  have hcoe : (K : ℝ) = C / s := by
    simp [K, hK_pos]
  have hmain : ∀ (x y : {p // p ∈ E}),
      dist (V x) (V y) ≤ (K : ℝ) * dist (x : Point3) (y : Point3) := by
    intro x y
    set d : ℝ := dist (x : Point3) (y : Point3) with hd
    have hgoal : dist (V x) (V y) ≤ (C / s) * d := by
      by_cases h1 : d ≤ s ^ N
      · have heq : V x = V y := hconst x y h1
        rw [heq]
        simp [hd] <;> positivity
      · have h1' : s ^ N < d := by linarith
        by_cases h2 : d ≤ s
        · have hN2 : 2 ≤ N := by
            by_contra h
            have hlt : N < 2 := by linarith
            have hN1 : N = 1 := by omega
            rw [hN1] at h1' <;> linarith
          let S : Finset ℕ := Finset.filter (fun k => d ≤ s ^ k) (Finset.range N)
          have hS1 : 1 ∈ Finset.range N := by
            simp only [Finset.mem_range] <;> linarith
          have hS2 : d ≤ s ^ 1 := by simpa [pow_one] using h2
          have h1in : 1 ∈ S := by
            rw [Finset.mem_filter] <;> exact ⟨hS1, hS2⟩
          have hSnonempty : S.Nonempty := ⟨1, h1in⟩
          let k := S.max' hSnonempty
          have hkin : k ∈ S := Finset.max'_mem S hSnonempty
          have hkin' : k ∈ Finset.range N ∧ d ≤ s ^ k := by
            rwa [Finset.mem_filter] at hkin
          have hk_lt_N : k < N := Finset.mem_range.mp hkin'.1
          have hdk : d ≤ s ^ k := hkin'.2
          have hk_ge1 : 1 ≤ k := Finset.le_max' S 1 h1in
          have hdk1 : s ^ (k + 1) < d := by
            by_cases h : k + 1 < N
            · have hnot : k + 1 ∉ S := by
                intro hmem
                have hle : k + 1 ≤ k := Finset.le_max' S (k + 1) hmem
                linarith
              have hr : k + 1 ∈ Finset.range N := by
                simp only [Finset.mem_range] <;> linarith
              have hiff : (k + 1 ∈ S) ↔ d ≤ s ^ (k + 1) := by
                constructor
                · intro hmem
                  exact (Finset.mem_filter.mp hmem).2
                · intro hle
                  exact Finset.mem_filter.mpr ⟨hr, hle⟩
              have h' : ¬(d ≤ s ^ (k + 1)) := mt hiff.mpr hnot
              exact lt_of_not_ge h'
            · have hkN : k + 1 = N := by omega
              rw [hkN] <;> exact h1'
          have h9 : s * s ^ k < d := by simpa [pow_succ'] using hdk1
          have hdiv : (s * s ^ k) / s = s ^ k := by
            field_simp [hs_pos.ne'] <;> ring
          have hsk : s ^ k < d / s := by
            calc s ^ k
              = (s * s ^ k) / s := hdiv.symm
            _ < d / s := by gcongr
          have hbound : dist (V x) (V y) ≤ C * s ^ k :=
            honeScale k hk_ge1 hk_lt_N x y hdk
          calc dist (V x) (V y)
            ≤ C * s ^ k := hbound
          _ ≤ C * (d / s) := by gcongr
          _ = (C / s) * d := by ring
        · have h2' : s < d := by linarith
          have h3 : dist (V x) (V y) ≤ ‖V x‖ + ‖V y‖ := by
            calc dist (V x) (V y)
              = ‖V x - V y‖ := by rw [dist_eq_norm]
            _ ≤ ‖V x‖ + ‖V y‖ := norm_sub_le (V x) (V y)
          have h4 : ‖V x‖ = 1 := hunit x
          have h5 : ‖V y‖ = 1 := hunit y
          have h6 : dist (V x) (V y) ≤ 2 := by
            calc dist (V x) (V y)
              ≤ ‖V x‖ + ‖V y‖ := h3
            _ = 1 + 1 := by rw [h4, h5]
            _ = 2 := by norm_num
          have h7 : (2 : ℝ) ≤ (C / s) * d := by
            have h8 : (C / s) * s = C := by
              field_simp [hs_pos.ne'] <;> ring
            have h9 : C ≤ (C / s) * d := by
              calc C
                = (C / s) * s := h8.symm
              _ ≤ (C / s) * d := by gcongr
            linarith
          linarith
    rw [hcoe]
    exact hgoal
  have hfinal : ∀ (x y : {p // p ∈ E}),
      edist (V x) (V y) ≤ (K : ENNReal) * edist x y := by
    intro x y
    have hdist : dist (V x) (V y) ≤ (K : ℝ) * dist (x : Point3) (y : Point3) :=
      hmain x y
    have h1 : edist (V x) (V y) = ENNReal.ofReal (dist (V x) (V y)) :=
      edist_dist (V x) (V y)
    have h2 : edist x y = ENNReal.ofReal (dist (x : Point3) (y : Point3)) :=
      edist_dist x y
    rw [h1, h2]
    have h3 : ENNReal.ofReal (dist (V x) (V y)) ≤
        ENNReal.ofReal ((K : ℝ) * dist (x : Point3) (y : Point3)) :=
      ENNReal.ofReal_le_ofReal hdist
    have hKnonneg : 0 ≤ (K : ℝ) := by positivity
    have h41 : ENNReal.ofReal ((K : ℝ) * dist (x : Point3) (y : Point3)) =
        ENNReal.ofReal (K : ℝ) * ENNReal.ofReal (dist (x : Point3) (y : Point3)) :=
      ENNReal.ofReal_mul hKnonneg
    have h42 : ENNReal.ofReal (K : ℝ) = (K : ENNReal) := by simp
    rw [h41, h42] at h3
    exact h3
  exact hfinal

/--
One-scale plane-map variation bound (statement).

Given a plane map that is constant on cubical cells of side `s^k` and has
incidence bound `rho`, the variation between points in nearby cells is bounded
by `C * s^k`, where `C` depends on the direction-control bound.

This lemma takes the direction-control hypothesis explicitly so it can be
instantiated once cobalt's broad-set bound is available.
-/
theorem one_scale_variation_bound
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (planeMap : Point3 → Point3)
    (hunit : ∀ p ∈ Y.union, ‖planeMap p‖ = 1)
    (s : ℝ) (hs_pos : 0 < s)
    (k : ℕ)
    (cell : Point3 → ℕ)
    (hconst_on_cells : ∀ p ∈ Y.union, ∀ q ∈ Y.union,
      cell p = cell q → planeMap p = planeMap q)
    (hcell_diam : ∀ p ∈ Y.union, ∀ q ∈ Y.union,
      dist p q ≤ s ^ k → cell p = cell q)
    (hdirection_control : ∀ p ∈ Y.union, ∀ q ∈ Y.union,
      cell p ≠ cell q → dist p q ≤ 2 * s ^ k →
        dist (planeMap p) (planeMap q) ≤ 2 * s ^ k) :
    ∀ (p : Point3), p ∈ Y.union → ∀ (q : Point3), q ∈ Y.union →
      dist p q ≤ s ^ k → dist (planeMap p) (planeMap q) ≤ 2 * s ^ k := by
  intro p hp q hq hdist
  by_cases hsame : cell p = cell q
  · have heq : planeMap p = planeMap q := hconst_on_cells p hp q hq hsame
    rw [heq]
    simp <;> positivity
  · have hdist' : dist p q ≤ 2 * s ^ k := by
      have h10 : 0 < s ^ k := pow_pos hs_pos k
      linarith
    exact hdirection_control p hp q hq hsame hdist'

/--
Assemble a Lipschitz plane map on the shading-union subtype.

Given:
- A finest-cell refinement giving constancy at `delta`
- One-scale variation bounds at intermediate scales
- Unit norm

Produce a `LipschitzWith` plane map on `{p // p ∈ shading.union}`.

The Lipschitz constant is `C / s` where `C ≥ 2` is the one-scale coefficient
and `s ≤ 1` is the scale base.  For `C = 2, s = 2`, this gives `LipschitzWith 1`
(but `s ≤ 1` is required, so normalization/dilation is needed to reach 1).
-/
theorem assemble_lipschitz_plane_map
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (planeMap : Point3 → Point3)
    (hunit : ∀ p ∈ Y.union, ‖planeMap p‖ = 1)
    (N : ℕ) (hN : 1 ≤ N)
    (s : ℝ) (hs_pos : 0 < s) (hs_le_one : s ≤ 1)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC_two : 2 ≤ C)
    (hconst : ∀ (x y : {p // p ∈ Y.union}),
      dist (x : Point3) (y : Point3) ≤ s ^ N → planeMap x = planeMap y)
    (honeScale : ∀ (k : ℕ), 1 ≤ k → k < N →
      ∀ (x y : {p // p ∈ Y.union}),
        dist (x : Point3) (y : Point3) ≤ s ^ k →
          dist (planeMap x) (planeMap y) ≤ C * s ^ k) :
    LipschitzWith (Real.toNNReal (C / s))
      (fun (x : {p // p ∈ Y.union}) => planeMap (x : Point3)) :=
  finite_scale_lipschitz_subtype_general
    N hN s hs_pos hs_le_one C hC_nonneg hC_two
    (fun x => planeMap (x : Point3))
    (fun x => hunit x x.prop)
    hconst honeScale

/-!
## UTS-free cell separation (greedy coloring)

Reuses the WZ1 `nearby_cell_graph_degree_le` helper and greedy coloring to
select a color class of pairwise-separated active cells.
-/

/--
UTS-free nearby-cell separation.

Given active cells with representatives and a neighbor bound, color the
nearby-cell graph (edges when representatives are within `6*rho`) and select
the heaviest color class.  Selected cells are pairwise separated by more than
`6*rho`, and the selected class retains at least `1/(neighborBound+1)` of the
total mass.
-/
theorem pureWZ2_cell_separation
    {cellCount : ℕ} {α : Type*} [PseudoMetricSpace α]
    (active : Fin cellCount → Prop) [DecidablePred active]
    (representative : Fin cellCount → α)
    (rho : ℝ)
    (neighborBound : ℕ) (hnb_pos : 0 < neighborBound)
    (h_count : ∀ c, active c →
      (Finset.univ.filter fun d : Fin cellCount =>
        active d ∧ dist (representative c) (representative d) ≤ 6 * rho).card ≤
          neighborBound)
    (mass : Fin cellCount → ENNReal) :
    ∃ (selectedCells : Finset (Fin cellCount)),
      (∀ c ∈ selectedCells, active c) ∧
      (∀ c ∈ selectedCells, ∀ d ∈ selectedCells, c ≠ d →
        dist (representative c) (representative d) > 6 * rho) ∧
      (∑ c ∈ Finset.univ.filter active, mass c) ≤
        ((neighborBound + 1 : ℕ) : ENNReal) *
          (∑ c ∈ selectedCells, mass c) := by
  classical
  let adj (c d : Fin cellCount) : Prop :=
    c ≠ d ∧ active c ∧ active d ∧
      dist (representative c) (representative d) ≤ 6 * rho
  let G : SimpleGraph (Fin cellCount) :=
    { Adj := adj
      symm := ⟨fun {a b} h =>
        ⟨h.1.symm, h.2.2.1, h.2.1, by
          rw [dist_comm]; exact h.2.2.2⟩⟩
      loopless := ⟨fun v h => h.1 rfl⟩ }
  have hG : ∀ c d, G.Adj c d ↔ adj c d := by
    intro c d; rfl
  have h_deg : ∀ c : Fin cellCount, G.degree c ≤ neighborBound := by
    intro c
    have h_eq : G.degree c = (G.neighborFinset c).card :=
      SimpleGraph.card_neighborFinset_eq_degree G c
    rw [h_eq]
    exact nearby_cell_graph_degree_le
      active representative rho G hG neighborBound h_count c
  have h_colorable : G.Colorable (neighborBound + 1) :=
    SimpleGraph.colorable_of_forall_degree_le h_deg
  rcases h_colorable with ⟨color⟩
  have h_proper : ∀ c d, G.Adj c d → color c ≠ color d :=
    fun c d h => color.valid h
  let activeCells := Finset.univ.filter active
  let colorClass : Fin (neighborBound + 1) → Finset (Fin cellCount) :=
    fun k => activeCells.filter (fun c => color c = k)
  have h_disj : Set.Pairwise ( (Finset.univ : Finset (Fin (neighborBound + 1))) : Set (Fin (neighborBound + 1)))
      (fun k l => Disjoint (colorClass k) (colorClass l)) := by
    intro k _ l _ hkl
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    have h1 : color c = k := (Finset.mem_filter.mp hc1).2
    have h2 : color c = l := (Finset.mem_filter.mp hc2).2
    rw [h1] at h2
    exact hkl h2
  let f : Fin (neighborBound + 1) → ENNReal :=
    fun k => ∑ c ∈ colorClass k, mass c
  have h_union : activeCells = Finset.biUnion (Finset.univ : Finset (Fin (neighborBound + 1))) colorClass := by
    ext c
    simp [activeCells, colorClass, Finset.mem_biUnion]
    <;> tauto
  have h_sum : (∑ c ∈ activeCells, mass c) = ∑ k : Fin (neighborBound + 1), f k := by
    rw [h_union, Finset.sum_biUnion h_disj]
    <;> rfl
  have h_max : ∃ (k : Fin (neighborBound + 1)),
      k ∈ (Finset.univ : Finset (Fin (neighborBound + 1))) ∧
      ∀ (l : Fin (neighborBound + 1)), l ∈ (Finset.univ : Finset (Fin (neighborBound + 1))) → f l ≤ f k :=
    Finset.exists_max_image (Finset.univ) f (by simp)
  rcases h_max with ⟨k, _, hk⟩
  have hk' : ∀ (l : Fin (neighborBound + 1)), f l ≤ f k := by
    intro l; exact hk l (by simp)
  have h_main : (∑ c ∈ activeCells, mass c) ≤
      ((neighborBound + 1 : ℕ) : ENNReal) * (∑ c ∈ colorClass k, mass c) := by
    rw [h_sum]
    calc
      (∑ l : Fin (neighborBound + 1), f l)
        ≤ ∑ l : Fin (neighborBound + 1), f k :=
          Finset.sum_le_sum (fun i _ => hk' i)
      _ = ((neighborBound + 1 : ℕ) : ENNReal) * f k := by
        simp [Finset.sum_const, Fintype.card_fin]
        <;> ring
  have h_active : ∀ c, c ∈ colorClass k → active c := by
    intro c hc
    have h_ac : c ∈ activeCells := (Finset.mem_filter.mp hc).1
    simpa [activeCells] using h_ac
  refine ⟨colorClass k, h_active, ?_, h_main⟩
  · intro c hc d hd hne
    by_contra hdist
    have h_adj : G.Adj c d := by
      rw [hG]
      exact ⟨hne, h_active c hc, h_active d hd, by linarith⟩
    have h_color_ne : color c ≠ color d := h_proper c d h_adj
    have hc1 : color c = k := (Finset.mem_filter.mp hc).2
    have hd1 : color d = k := (Finset.mem_filter.mp hd).2
    rw [hc1] at h_color_ne
    exact h_color_ne hd1.symm

/-!
## Direct Lipschitz from constancy at a fixed scale

Simpler N=1 version of the finite-scale Lipschitz combinator. If a unit-norm
map is constant at scale `s` on a subtype, it is LipschitzWith `2/s`.
-/

/--
Direct Lipschitz from constancy at scale `s`.

If `‖V x‖ = 1` for all `x`, and `dist x y ≤ s` implies `V x = V y`, then
`LipschitzWith (2/s) V`. For `s = 1/3`, this gives `LipschitzWith 6`.
-/
lemma direct_lipschitz_from_constancy
    {E : Set Point3}
    (s : ℝ) (hs_pos : 0 < s)
    (V : {p : Point3 // p ∈ E} → Point3)
    (hunit : ∀ (x : {p // p ∈ E}), ‖V x‖ = 1)
    (hconst : ∀ (x y : {p // p ∈ E}),
      dist (x : Point3) (y : Point3) ≤ s → V x = V y) :
    LipschitzWith (Real.toNNReal (2 / s)) V := by
  let K : NNReal := Real.toNNReal (2 / s)
  have hK_pos : 0 < 2 / s := by positivity
  have hcoe : (K : ℝ) = 2 / s := by
    simp [K, hK_pos.le]
  have hmain : ∀ (x y : {p // p ∈ E}),
      dist (V x) (V y) ≤ (K : ℝ) * dist (x : Point3) (y : Point3) := by
    intro x y
    set d : ℝ := dist (x : Point3) (y : Point3) with hd
    by_cases h1 : d ≤ s
    · have heq : V x = V y := hconst x y h1
      rw [heq]
      simp [hd] <;> positivity
    · have h2 : s < d := by linarith
      have h3 : dist (V x) (V y) ≤ ‖V x‖ + ‖V y‖ := by
        calc dist (V x) (V y)
          = ‖V x - V y‖ := by rw [dist_eq_norm]
        _ ≤ ‖V x‖ + ‖V y‖ := norm_sub_le (V x) (V y)
      have h4 : ‖V x‖ = 1 := hunit x
      have h5 : ‖V y‖ = 1 := hunit y
      have h6 : dist (V x) (V y) ≤ 2 := by
        rw [h4, h5] at h3 <;> linarith
      have h7 : (2 : ℝ) < (2 / s) * d := by
        have h8 : (2 / s) * s = 2 := by
          field_simp [hs_pos.ne'] <;> ring
        have h9 : (2 / s) * d > (2 / s) * s := by
          gcongr
          <;> linarith
        rw [h8] at h9
        exact h9
      have h_goal : dist (V x) (V y) ≤ (K : ℝ) * d := by
        have h10 : dist (V x) (V y) ≤ 2 := h6
        have h11 : (2 : ℝ) < (2 / s) * d := h7
        have h12 : (2 / s) * d = (K : ℝ) * d := by
          rw [hcoe] <;> rfl
        rw [h12] at h11
        exact h10.trans h11.le
      exact h_goal
  have hfinal : ∀ x y, edist (V x) (V y) ≤ (K : ENNReal) * edist x y := by
    intro x y
    have hdist : dist (V x) (V y) ≤ (K : ℝ) * dist (x : Point3) (y : Point3) := hmain x y
    have h1 : edist (V x) (V y) = ENNReal.ofReal (dist (V x) (V y)) := edist_dist (V x) (V y)
    have h2 : edist x y = ENNReal.ofReal (dist (x : Point3) (y : Point3)) := edist_dist x y
    rw [h1, h2]
    have h3 := ENNReal.ofReal_le_ofReal hdist
    have h4 : ENNReal.ofReal ((K : ℝ) * dist (x : Point3) (y : Point3)) =
        (K : ENNReal) * ENNReal.ofReal (dist (x : Point3) (y : Point3)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      <;> simp
    rw [h4] at h3
    exact h3
  exact hfinal

/--
Cap + cell separation construction for paper shadings.

Given a weak plane map `V` on a paper shading `S` with incidence `I`, construct
a cell-constant plane map `W` on a pruned subshading `S'` with:
- Unit norm
- Incidence ≤ `I + epsilon` (absorbed into `6 * delta'`)
- Constancy at scale `1/3`
- `LipschitzWith 6`
- Mass retention `1 / (capCount * (neighborBound + 1))`

The construction follows the WZ1 finest-cell plane map pipeline:
1. Cover the unit sphere with caps of radius `epsilon`.
2. For each physical cell, select the heaviest cap.
3. Color cells so selected cells are pairwise `> 6*rho` apart.
4. Prune to selected cells ∩ selected caps.
5. `direct_lipschitz_from_constancy` gives `LipschitzWith 6`.
-/
lemma paper_cap_cell_lipschitz_general
    {delta' I epsilon rho cellDiam I_target : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta'}
    {S : WZ1PaperTubeShading F}
    (V : Point3 → Point3)
    (hV_meas : Measurable V)
    (hV_unit : ∀ p ∈ S.union, ‖V p‖ = 1)
    (hV_inc : ∀ i p, p ∈ S.carrier i →
      |inner ℝ (F.tube i).direction (V p)| ≤ I)
    (hI_eps : I + epsilon ≤ I_target)
    (hepsilon_pos : 0 < epsilon)
    (hrho_pos : 0 < rho)
    (hcellDiam_pos : 0 < cellDiam)
    (hconstancy : 0 < 6 * rho - 2 * cellDiam)
    {cellCount : ℕ}
    (cell : Point3 → Fin cellCount)
    (hcell_meas : Measurable cell)
    (representative : Fin cellCount → Point3)
    (hrep : ∀ p ∈ S.union, dist p (representative (cell p)) ≤ cellDiam)
    (neighborBound : ℕ)
    (hnb_pos : 0 < neighborBound)
    (hnearby : ∀ c,
      (∃ p ∈ S.union, cell p = c) →
      (Finset.univ.filter fun d : Fin cellCount =>
        (∃ p ∈ S.union, cell p = d) ∧
        dist (representative c) (representative d) ≤ 6 * rho).card ≤ neighborBound)
    {capCount : ℕ}
    (hcapCount_pos : 0 < capCount)
    (capCenter : Fin capCount → Point3)
    (hcapCenter_norm : ∀ k, ‖capCenter k‖ = 1)
    (hsphere_cover : ∀ x, ‖x‖ = 1 →
      ∃ k : Fin capCount, dist x (capCenter k) ≤ epsilon) :
    ∃ (S' : WZ1PaperTubeShading F)
      (W : {p : Point3 // p ∈ S'.union} → Point3),
      PaperIsSubshading S' S ∧
      LipschitzWith (Real.toNNReal (2 / (6 * rho - 2 * cellDiam))) W ∧
      (∀ x, ‖W x‖ = 1) ∧
      (∀ i p (hp : p ∈ S'.carrier i),
        |inner ℝ (F.tube i).direction (W ⟨p, ⟨i, hp⟩⟩)| ≤ I_target) ∧
      S.mass ≤ (capCount : ENNReal) * ((neighborBound + 1 : ℕ) : ENNReal) * S'.mass := by
  classical
  letI : Nonempty (Fin capCount) := ⟨⟨0, hcapCount_pos⟩⟩

  -- Step 1: Cap sets
  let capSet (c : Fin cellCount) (k : Fin capCount) : Set Point3 :=
    {p | cell p = c ∧ p ∈ S.union ∧ dist (V p) (capCenter k) ≤ epsilon}

  have hcapSet_meas : ∀ c k, MeasurableSet (capSet c k) := by
    intro c k
    have h1 : MeasurableSet {p : Point3 | cell p = c} :=
      hcell_meas (measurableSet_singleton c)
    have h2 : MeasurableSet {p | dist (V p) (capCenter k) ≤ epsilon} := by
      have h : Measurable (fun p : Point3 => dist (V p) (capCenter k)) := by fun_prop
      exact measurableSet_le h measurable_const
    have hYunion_meas : MeasurableSet S.union := by
      have h : S.union = ⋃ i : Fin F.card, S.carrier i := by
        ext x; simp [Kakeya.Streamlined.Shading.union] <;> tauto
      rw [h]
      exact MeasurableSet.iUnion (fun i => S.measurable_carrier i)
    have h4 : capSet c k =
        {p | cell p = c} ∩ S.union ∩ {p | dist (V p) (capCenter k) ≤ epsilon} := by
      ext x; simp [capSet] <;> tauto
    rw [h4]
    exact h1.inter hYunion_meas |>.inter h2

  -- Step 2: Cap sets cover each cell's intersection with S.union
  have hcap_cover : ∀ c,
      {p : Point3 | cell p = c ∧ p ∈ S.union} ⊆ ⋃ k : Fin capCount, capSet c k := by
    intro c p hp
    have hcell_p : cell p = c := hp.1
    have hY_p : p ∈ S.union := hp.2
    have hunit_p : ‖V p‖ = 1 := hV_unit p hY_p
    rcases hsphere_cover (V p) hunit_p with ⟨k, hk⟩
    have hmem : p ∈ capSet c k := ⟨hcell_p, hY_p, hk⟩
    exact Set.mem_iUnion.mpr ⟨k, hmem⟩

  -- Step 3: Mass definitions
  let cellSlice (c : Fin cellCount) : Set Point3 := {p | cell p = c}
  let massCell (c : Fin cellCount) : ENNReal :=
    ∑ i : Fin F.card, MeasureTheory.volume (S.carrier i ∩ cellSlice c)
  let massCellCap (c : Fin cellCount) (k : Fin capCount) : ENNReal :=
    ∑ i : Fin F.card, MeasureTheory.volume (S.carrier i ∩ capSet c k)

  have hcellSlice_meas : ∀ c, MeasurableSet (cellSlice c) := by
    intro c
    exact hcell_meas (measurableSet_singleton c)

  have hsub : ∀ (i : Fin F.card) (c : Fin cellCount),
      MeasureTheory.volume (S.carrier i ∩ cellSlice c) ≤
        ∑ k : Fin capCount, MeasureTheory.volume (S.carrier i ∩ capSet c k) := by
    intro i c
    have hYsub : S.carrier i ⊆ S.union := by
      intro x hx; exact ⟨i, hx⟩
    have hcover : S.carrier i ∩ cellSlice c ⊆
        ⋃ k : Fin capCount, S.carrier i ∩ capSet c k := by
      intro x hx
      have hxi : x ∈ S.carrier i := hx.1
      have hxcell : x ∈ cellSlice c := hx.2
      have h3 : x ∈ S.union := hYsub hxi
      have h4 : x ∈ {p : Point3 | cell p = c ∧ p ∈ S.union} := ⟨hxcell, h3⟩
      have h5 : x ∈ ⋃ k : Fin capCount, capSet c k := hcap_cover c h4
      rcases Set.mem_iUnion.mp h5 with ⟨k, h6⟩
      exact Set.mem_iUnion.mpr ⟨k, ⟨hxi, h6⟩⟩
    have h_mono : MeasureTheory.volume (S.carrier i ∩ cellSlice c) ≤
        MeasureTheory.volume (⋃ k : Fin capCount, S.carrier i ∩ capSet c k) :=
      MeasureTheory.measure_mono hcover
    have h_subadd : MeasureTheory.volume (⋃ k : Fin capCount, S.carrier i ∩ capSet c k) ≤
        ∑ k : Fin capCount, MeasureTheory.volume (S.carrier i ∩ capSet c k) := by
      have h_tsum : MeasureTheory.volume (⋃ k : Fin capCount, S.carrier i ∩ capSet c k) ≤
          ∑' k : Fin capCount, MeasureTheory.volume (S.carrier i ∩ capSet c k) :=
        MeasureTheory.measure_iUnion_le _
      simpa using h_tsum
    exact h_mono.trans h_subadd

  have hmass_cell_le : ∀ c, massCell c ≤ ∑ k : Fin capCount, massCellCap c k := by
    intro c
    dsimp only [massCell, massCellCap]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i _
    exact hsub i c

  -- Step 4: Select heaviest cap per cell
  choose selectedCap h_selectedCap using
    fun c : Fin cellCount => exists_ge_average (f := fun k : Fin capCount => massCellCap c k)

  have hpigeon : ∀ c,
      massCell c ≤ (capCount : ENNReal) * massCellCap c (selectedCap c) := by
    intro c
    have h : (Fintype.card (Fin capCount) : ENNReal) * massCellCap c (selectedCap c) ≥
        ∑ k : Fin capCount, massCellCap c k := h_selectedCap c
    have hcard : Fintype.card (Fin capCount) = capCount := by
      simp
    rw [hcard] at h
    have h' : massCell c ≤ ∑ k : Fin capCount, massCellCap c k := hmass_cell_le c
    exact h'.trans h

  -- Step 5: selectedSet1 and shading1
  let selectedSet1 : Set Point3 := ⋃ c : Fin cellCount, capSet c (selectedCap c)

  have hselectedSet1_meas : MeasurableSet selectedSet1 :=
    MeasurableSet.iUnion (fun c => hcapSet_meas c (selectedCap c))

  let shading1 : WZ1PaperTubeShading F :=
    { carrier := fun i => S.carrier i ∩ selectedSet1
      measurable_carrier := fun i =>
        (S.measurable_carrier i).inter hselectedSet1_meas
      subset_body := fun i =>
        Set.inter_subset_left.trans (S.subset_body i) }

  -- Step 6: Mass retention for cap selection
  have hcells_disjoint : ∀ c1 c2 : Fin cellCount,
      c1 ≠ c2 → Disjoint (cellSlice c1) (cellSlice c2) := by
    intro c1 c2 hne
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have h1 : cell x = c1 := hx1
    have h2 : cell x = c2 := hx2
    rw [h1] at h2
    exact hne h2

  have hmass1_shading : ∀ i,
      MeasureTheory.volume (shading1.carrier i) =
        ∑ c : Fin cellCount, MeasureTheory.volume (S.carrier i ∩ capSet c (selectedCap c)) := by
    intro i
    have h2 : shading1.carrier i =
        ⋃ c : Fin cellCount, S.carrier i ∩ capSet c (selectedCap c) := by
      ext x
      simp [shading1, selectedSet1, Set.mem_iUnion] <;> tauto
    rw [h2]
    have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin cellCount))
        (fun c => S.carrier i ∩ capSet c (selectedCap c)) := by
      intro c1 _ c2 _ hne
      have h4 : Disjoint (capSet c1 (selectedCap c1)) (capSet c2 (selectedCap c2)) :=
        (hcells_disjoint c1 c2 hne).mono
          (fun p hp => hp.1) (fun p hp => hp.1)
      exact h4.mono Set.inter_subset_right Set.inter_subset_right
    have hmeas : ∀ c ∈ (Finset.univ : Finset (Fin cellCount)),
        MeasurableSet (S.carrier i ∩ capSet c (selectedCap c)) := by
      intro c _
      exact (S.measurable_carrier i).inter (hcapSet_meas c (selectedCap c))
    have h_eq : MeasureTheory.volume (⋃ c ∈ (Finset.univ : Finset (Fin cellCount)),
          S.carrier i ∩ capSet c (selectedCap c)) =
        ∑ c ∈ (Finset.univ : Finset (Fin cellCount)),
          MeasureTheory.volume (S.carrier i ∩ capSet c (selectedCap c)) :=
      MeasureTheory.measure_biUnion_finset hdisj hmeas
    simpa [Set.biUnion_univ] using h_eq

  have hmass2 : shading1.mass = ∑ c : Fin cellCount, massCellCap c (selectedCap c) := by
    dsimp only [Kakeya.Streamlined.Shading.mass, massCellCap]
    calc
      ∑ i : Fin F.card, MeasureTheory.volume (shading1.carrier i)
        = ∑ i : Fin F.card, ∑ c : Fin cellCount,
            MeasureTheory.volume (S.carrier i ∩ capSet c (selectedCap c)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hmass1_shading i
      _ = ∑ c : Fin cellCount, ∑ i : Fin F.card,
            MeasureTheory.volume (S.carrier i ∩ capSet c (selectedCap c)) := by
          rw [Finset.sum_comm]
      _ = ∑ c : Fin cellCount, massCellCap c (selectedCap c) := by rfl

  have htotal_mass : ∑ c : Fin cellCount, massCell c = S.mass := by
    dsimp only [massCell, Kakeya.Streamlined.Shading.mass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    let pieces : Fin cellCount → Set Point3 := fun c => S.carrier i ∩ cellSlice c
    have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin cellCount)) pieces := by
      intro c1 _ c2 _ hne
      exact (hcells_disjoint c1 c2 hne).mono Set.inter_subset_right Set.inter_subset_right
    have hmeas : ∀ c ∈ (Finset.univ : Finset (Fin cellCount)), MeasurableSet (pieces c) := by
      intro c _
      exact (S.measurable_carrier i).inter (hcellSlice_meas c)
    have hcover : S.carrier i = ⋃ c : Fin cellCount, pieces c := by
      ext x
      simp only [pieces, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hxi
        exact ⟨cell x, hxi, rfl⟩
      · rintro ⟨c, hxi, _⟩
        exact hxi
    have h_univ_eq : (⋃ c : Fin cellCount, pieces c) =
        (⋃ c ∈ (Finset.univ : Finset (Fin cellCount)), pieces c) := by
      ext x; simp
    have h_eq : MeasureTheory.volume (⋃ c ∈ (Finset.univ : Finset (Fin cellCount)), pieces c) =
        ∑ c ∈ (Finset.univ : Finset (Fin cellCount)), MeasureTheory.volume (pieces c) :=
      MeasureTheory.measure_biUnion_finset hdisj hmeas
    have h1 : MeasureTheory.volume (S.carrier i) =
        MeasureTheory.volume (⋃ c : Fin cellCount, pieces c) :=
      congr_arg MeasureTheory.volume hcover
    have h2 : MeasureTheory.volume (⋃ c : Fin cellCount, pieces c) =
        MeasureTheory.volume (⋃ c ∈ (Finset.univ : Finset (Fin cellCount)), pieces c) :=
      congr_arg MeasureTheory.volume h_univ_eq
    have h3 : MeasureTheory.volume (S.carrier i) =
        ∑ c : Fin cellCount, MeasureTheory.volume (pieces c) := by
      rw [h1, h2, h_eq]
      <;> simp
    exact h3.symm

  have hmass_lower1 : S.mass ≤ (capCount : ENNReal) * shading1.mass := by
    rw [htotal_mass.symm, hmass2]
    calc
      ∑ c : Fin cellCount, massCell c
        ≤ ∑ c : Fin cellCount, (capCount : ENNReal) * massCellCap c (selectedCap c) := by
          apply Finset.sum_le_sum
          intro c _
          exact hpigeon c
      _ = (capCount : ENNReal) * ∑ c : Fin cellCount, massCellCap c (selectedCap c) := by
          rw [Finset.mul_sum]

  -- Step 7: Cell separation
  let active : Fin cellCount → Prop := fun c => (S.union ∩ cellSlice c).Nonempty
  have hactive_iff : ∀ c, active c ↔ (∃ p ∈ S.union, cell p = c) := by
    intro c
    simp only [active, cellSlice]
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨p, hp.1, hp.2⟩
    · rintro ⟨p, hp1, hp2⟩
      exact ⟨p, hp1, hp2⟩

  let mass : Fin cellCount → ENNReal := fun c => massCellCap c (selectedCap c)

  have hnearby' : ∀ c, active c →
      (Finset.univ.filter fun d : Fin cellCount =>
        active d ∧ dist (representative c) (representative d) ≤ 6 * rho).card ≤ neighborBound := by
    intro c hc
    have hc' : ∃ p ∈ S.union, cell p = c := (hactive_iff c).mp hc
    have h : (Finset.univ.filter fun d : Fin cellCount =>
            active d ∧ dist (representative c) (representative d) ≤ 6 * rho) =
          Finset.univ.filter fun d : Fin cellCount =>
            (∃ p ∈ S.union, cell p = d) ∧
            dist (representative c) (representative d) ≤ 6 * rho := by
      apply Finset.ext
      intro d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hactive_iff d]
    rw [h]
    exact hnearby c hc'

  rcases pureWZ2_cell_separation active representative rho neighborBound hnb_pos hnearby' mass
    with ⟨selectedCells, hsel_active, hsel_sep, hmass_lower2⟩

  -- Step 8: Final selectedSet and S'
  let selectedSet : Set Point3 := ⋃ c ∈ selectedCells, capSet c (selectedCap c)

  have hselectedSet_meas : MeasurableSet selectedSet := by
    have h : selectedSet = ⋃ c : Fin cellCount, if c ∈ selectedCells then capSet c (selectedCap c) else (∅ : Set Point3) := by
      ext x
      simp [selectedSet, Set.mem_iUnion]
      <;> tauto
    rw [h]
    apply MeasurableSet.iUnion
    intro c
    by_cases hc : c ∈ selectedCells
    · simpa [hc] using hcapSet_meas c (selectedCap c)
    · simp [hc]
      <;> exact MeasurableSet.empty

  let S' : WZ1PaperTubeShading F :=
    { carrier := fun i => S.carrier i ∩ selectedSet
      measurable_carrier := fun i =>
        (S.measurable_carrier i).inter hselectedSet_meas
      subset_body := fun i =>
        Set.inter_subset_left.trans (S.subset_body i) }

  have hsubshading : PaperIsSubshading S' S := by
    intro i
    exact Set.inter_subset_left

  -- Step 9: Mass retention total
  have hmass3 : shading1.mass ≤ ((neighborBound + 1 : ℕ) : ENNReal) * S'.mass := by
    have h_sum1 : ∑ c ∈ Finset.univ.filter active, mass c = shading1.mass := by
      have h_inactive_zero : ∀ c, ¬active c → mass c = 0 := by
        intro c hc
        have h_empty : capSet c (selectedCap c) = ∅ := by
          ext p
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hp
          have h_active : active c := by
            exact ⟨p, hp.2.1, hp.1⟩
          exact hc h_active
        dsimp only [mass, massCellCap]
        have h : ∀ i : Fin F.card, MeasureTheory.volume (S.carrier i ∩ capSet c (selectedCap c)) = 0 := by
          intro i
          rw [h_empty]
          <;> simp
        have hsum : ∑ i : Fin F.card, MeasureTheory.volume (S.carrier i ∩ capSet c (selectedCap c)) = 0 := by
          rw [Finset.sum_congr rfl (fun i _ => h i)]
          <;> simp
        exact hsum
      have h1 : ∑ c ∈ Finset.univ.filter active, mass c = ∑ c : Fin cellCount, mass c := by
        have h_sub : (Finset.univ.filter active) ⊆ (Finset.univ : Finset (Fin cellCount)) := Finset.filter_subset _ _
        rw [Finset.sum_subset h_sub]
        intro c _ hnc
        have h_inact : ¬active c := by simpa [Finset.mem_filter] using hnc
        exact h_inactive_zero c h_inact
      rw [h1]
      exact hmass2.symm
    rw [h_sum1] at hmass_lower2
    have h2 : S'.mass = ∑ c ∈ selectedCells, mass c := by
      dsimp only [Kakeya.Streamlined.Shading.mass, mass]
      calc
        ∑ i : Fin F.card, MeasureTheory.volume (S'.carrier i)
          = ∑ i : Fin F.card, ∑ c ∈ selectedCells,
              MeasureTheory.volume (S.carrier i ∩ capSet c (selectedCap c)) := by
            apply Finset.sum_congr rfl
            intro i _
            have hcover : S'.carrier i = ⋃ c ∈ selectedCells, S.carrier i ∩ capSet c (selectedCap c) := by
              ext x
              simp [S', selectedSet, Set.mem_iUnion] <;> tauto
            rw [hcover]
            have hdisj : Set.PairwiseDisjoint selectedCells
                (fun c => S.carrier i ∩ capSet c (selectedCap c)) := by
              intro c1 _ c2 _ hne
              have h41 : capSet c1 (selectedCap c1) ⊆ cellSlice c1 := fun p hp => hp.1
              have h42 : capSet c2 (selectedCap c2) ⊆ cellSlice c2 := fun p hp => hp.1
              have h4 : Disjoint (capSet c1 (selectedCap c1)) (capSet c2 (selectedCap c2)) :=
                (hcells_disjoint c1 c2 hne).mono h41 h42
              exact h4.mono Set.inter_subset_right Set.inter_subset_right
            have hmeas : ∀ c ∈ selectedCells, MeasurableSet (S.carrier i ∩ capSet c (selectedCap c)) := by
              intro c _
              exact (S.measurable_carrier i).inter (hcapSet_meas c (selectedCap c))
            have h_eq : MeasureTheory.volume (⋃ c ∈ selectedCells, S.carrier i ∩ capSet c (selectedCap c)) =
                ∑ c ∈ selectedCells, MeasureTheory.volume (S.carrier i ∩ capSet c (selectedCap c)) :=
              MeasureTheory.measure_biUnion_finset hdisj hmeas
            have h_final : MeasureTheory.volume (S'.carrier i) =
                ∑ c ∈ selectedCells, MeasureTheory.volume (S.carrier i ∩ capSet c (selectedCap c)) := by
              have hcov : S'.carrier i = ⋃ c ∈ selectedCells, S.carrier i ∩ capSet c (selectedCap c) := hcover
              rw [hcov]
              exact h_eq
            exact h_eq
        _ = ∑ c ∈ selectedCells, ∑ i : Fin F.card,
              MeasureTheory.volume (S.carrier i ∩ capSet c (selectedCap c)) := by
            rw [Finset.sum_comm]
        _ = ∑ c ∈ selectedCells, massCellCap c (selectedCap c) := by rfl
    have h3 : shading1.mass ≤ ((neighborBound + 1 : ℕ) : ENNReal) * S'.mass := by
      rw [h2]
      exact hmass_lower2
    exact h3

  have hmass_total : S.mass ≤ (capCount : ENNReal) * ((neighborBound + 1 : ℕ) : ENNReal) * S'.mass := by
    have h1 : S.mass ≤ (capCount : ENNReal) * shading1.mass := hmass_lower1
    have h2 : shading1.mass ≤ ((neighborBound + 1 : ℕ) : ENNReal) * S'.mass := hmass3
    have h3 : S.mass ≤ (capCount : ENNReal) * (((neighborBound + 1 : ℕ) : ENNReal) * S'.mass) := by
      calc
        S.mass ≤ (capCount : ENNReal) * shading1.mass := h1
        _ ≤ (capCount : ENNReal) * (((neighborBound + 1 : ℕ) : ENNReal) * S'.mass) := by gcongr
    have h4 : (capCount : ENNReal) * (((neighborBound + 1 : ℕ) : ENNReal) * S'.mass) =
        (capCount : ENNReal) * ((neighborBound + 1 : ℕ) : ENNReal) * S'.mass := by
      rw [mul_assoc]
    rw [h4] at h3
    exact h3

  -- Step 10: Define W
  let W : {p : Point3 // p ∈ S'.union} → Point3 :=
    fun x => capCenter (selectedCap (cell (x : Point3)))

  -- Step 11: Unit norm
  have hunit : ∀ x, ‖W x‖ = 1 := by
    intro x
    exact hcapCenter_norm (selectedCap (cell (x : Point3)))

  -- Step 12: Incidence
  have hinc : ∀ i p (hp : p ∈ S'.carrier i),
      |inner ℝ (F.tube i).direction (W ⟨p, ⟨i, hp⟩⟩)| ≤ I_target := by
    intro i p hp
    have hpi : p ∈ S.carrier i := hp.1
    have hpsel : p ∈ selectedSet := hp.2
    have h_exists : ∃ (c : Fin cellCount), c ∈ selectedCells ∧ p ∈ capSet c (selectedCap c) := by
      simpa [selectedSet, Set.mem_biUnion] using hpsel
    rcases h_exists with ⟨c, hc, hcap⟩
    have hcell_p : cell p = c := hcap.1
    have hdist : dist (V p) (capCenter (selectedCap c)) ≤ epsilon := hcap.2.2
    have hW : W ⟨p, ⟨i, hp⟩⟩ = capCenter (selectedCap c) := by
      dsimp only [W]
      rw [hcell_p] <;> rfl
    rw [hW]
    set u := (F.tube i).direction with hu
    set v := V p with hv
    set w := capCenter (selectedCap c) with hw
    have hdir_unit : ‖u‖ = 1 := (F.tube i).direction_unit
    have h_eq1 : v + (w - v) = w := by
      ext j; simp
    have h_abs : |inner ℝ u w| ≤ |inner ℝ u v| + |inner ℝ u (w - v)| := by
      have h_eq2 : inner ℝ u w = inner ℝ u v + inner ℝ u (w - v) := by
        have h3 : inner ℝ u (v + (w - v)) = inner ℝ u v + inner ℝ u (w - v) := by
          rw [inner_add_right]
        rw [h_eq1] at *
        <;> tauto
      rw [h_eq2]
      exact abs_add_le (inner ℝ u v) (inner ℝ u (w - v))
    have h_cs : |inner ℝ u (w - v)| ≤ ‖u‖ * ‖w - v‖ := abs_real_inner_le_norm u (w - v)
    have h_norm : ‖w - v‖ = dist v w := by
      rw [dist_eq_norm, norm_sub_rev]
    rw [hdir_unit, h_norm] at h_cs
    have h6 : |inner ℝ u v| ≤ I := hV_inc i p hpi
    have h7 : ‖w - v‖ ≤ epsilon := by
      rw [h_norm] <;> exact hdist
    have h5 : |inner ℝ u w| ≤ I + epsilon := by
      calc |inner ℝ u w|
        ≤ |inner ℝ u v| + ‖w - v‖ := by linarith [h_abs, h_cs]
      _ ≤ I + epsilon := by linarith
    exact h5.trans hI_eps

  -- Step 13: Constancy at scale s = 6*rho - 2*cellDiam
  let s : ℝ := 6 * rho - 2 * cellDiam
  have hs_pos : 0 < s := hconstancy

  have h_selected_cell : ∀ (x : {p : Point3 // p ∈ S'.union}),
      ∃ (c : Fin cellCount), c ∈ selectedCells ∧ cell (x : Point3) = c := by
    intro x
    have hx : (x : Point3) ∈ S'.union := x.prop
    rcases hx with ⟨i, hi⟩
    have hpsel : (x : Point3) ∈ selectedSet := hi.2
    have h_exists : ∃ (c : Fin cellCount), c ∈ selectedCells ∧ (x : Point3) ∈ capSet c (selectedCap c) := by
      simpa [selectedSet, Set.mem_biUnion] using hpsel
    rcases h_exists with ⟨c, hc, hcap⟩
    exact ⟨c, hc, hcap.1⟩

  have hconst : ∀ (x y : {p : Point3 // p ∈ S'.union}),
      dist (x : Point3) (y : Point3) ≤ s → W x = W y := by
    intro x y hdist
    rcases h_selected_cell x with ⟨c, hc, hcell_x⟩
    rcases h_selected_cell y with ⟨d, hd, hcell_y⟩
    by_cases hne : c ≠ d
    · have hsep : dist (representative c) (representative d) > 6 * rho :=
        hsel_sep c hc d hd hne
      have hx_S : (x : Point3) ∈ S.union := by
        rcases x.prop with ⟨i, hi⟩
        exact ⟨i, hi.1⟩
      have hy_S : (y : Point3) ∈ S.union := by
        rcases y.prop with ⟨i, hi⟩
        exact ⟨i, hi.1⟩
      have hrep_x : dist (x : Point3) (representative (cell (x : Point3))) ≤ cellDiam :=
        hrep (x : Point3) hx_S
      have hrep_y : dist (y : Point3) (representative (cell (y : Point3))) ≤ cellDiam :=
        hrep (y : Point3) hy_S
      rw [hcell_x] at hrep_x
      rw [hcell_y] at hrep_y
      have h1 : dist (representative c) (representative d) ≤
          dist (representative c) (x : Point3) + dist (x : Point3) (representative d) :=
        dist_triangle _ _ _
      have h2 : dist (x : Point3) (representative d) ≤
          dist (x : Point3) (y : Point3) + dist (y : Point3) (representative d) :=
        dist_triangle _ _ _
      have hgt : dist (x : Point3) (y : Point3) > s := by
        have h3 : dist (representative c) (representative d) ≤
            dist (x : Point3) (representative c) + dist (x : Point3) (y : Point3) + dist (y : Point3) (representative d) := by
          calc
            dist (representative c) (representative d)
              ≤ dist (representative c) (x : Point3) + dist (x : Point3) (representative d) := h1
            _ = dist (x : Point3) (representative c) + dist (x : Point3) (representative d) := by rw [dist_comm]
            _ ≤ dist (x : Point3) (representative c) + (dist (x : Point3) (y : Point3) + dist (y : Point3) (representative d)) := by gcongr
            _ = dist (x : Point3) (representative c) + dist (x : Point3) (y : Point3) + dist (y : Point3) (representative d) := by ring
        have h4 : dist (representative c) (representative d) > 6 * rho := hsep
        linarith [hrep_x, hrep_y]
      linarith
    · have hcd : c = d := by tauto
      have hcell_eq : cell (x : Point3) = cell (y : Point3) := by
        rw [hcell_x, hcell_y, hcd]
      dsimp only [W]
      rw [hcell_eq]

  -- Step 14: Lipschitz
  have hlipschitz : LipschitzWith (Real.toNNReal (2 / s)) W :=
    direct_lipschitz_from_constancy s hs_pos W hunit hconst

  exact ⟨S', W, hsubshading, hlipschitz, hunit, hinc, hmass_total⟩

/-- Backward-compatible wrapper: 6-Lipschitz, incidence ≤ 6·delta'. -/
lemma paper_cap_cell_lipschitz
    {delta' I epsilon rho cellDiam : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta'}
    {S : WZ1PaperTubeShading F}
    (V : Point3 → Point3)
    (hV_meas : Measurable V)
    (hV_unit : ∀ p ∈ S.union, ‖V p‖ = 1)
    (hV_inc : ∀ i p, p ∈ S.carrier i →
      |inner ℝ (F.tube i).direction (V p)| ≤ I)
    (hI_eps : I + epsilon ≤ 6 * delta')
    (hepsilon_pos : 0 < epsilon)
    (hrho_pos : 0 < rho)
    (hcellDiam_pos : 0 < cellDiam)
    (hconstancy : 1 / 3 ≤ 6 * rho - 2 * cellDiam)
    {cellCount : ℕ}
    (cell : Point3 → Fin cellCount)
    (hcell_meas : Measurable cell)
    (representative : Fin cellCount → Point3)
    (hrep : ∀ p ∈ S.union, dist p (representative (cell p)) ≤ cellDiam)
    (neighborBound : ℕ)
    (hnb_pos : 0 < neighborBound)
    (hnearby : ∀ c,
      (∃ p ∈ S.union, cell p = c) →
      (Finset.univ.filter fun d : Fin cellCount =>
        (∃ p ∈ S.union, cell p = d) ∧
        dist (representative c) (representative d) ≤ 6 * rho).card ≤ neighborBound)
    {capCount : ℕ}
    (hcapCount_pos : 0 < capCount)
    (capCenter : Fin capCount → Point3)
    (hcapCenter_norm : ∀ k, ‖capCenter k‖ = 1)
    (hsphere_cover : ∀ x, ‖x‖ = 1 →
      ∃ k : Fin capCount, dist x (capCenter k) ≤ epsilon) :
    ∃ (S' : WZ1PaperTubeShading F)
      (W : {p : Point3 // p ∈ S'.union} → Point3),
      PaperIsSubshading S' S ∧
      LipschitzWith 6 W ∧
      (∀ x, ‖W x‖ = 1) ∧
      (∀ i p (hp : p ∈ S'.carrier i),
        |inner ℝ (F.tube i).direction (W ⟨p, ⟨i, hp⟩⟩)| ≤ 6 * delta') ∧
      S.mass ≤ (capCount : ENNReal) * ((neighborBound + 1 : ℕ) : ENNReal) * S'.mass := by
  have hconstancy_pos : 0 < 6 * rho - 2 * cellDiam := by linarith
  rcases paper_cap_cell_lipschitz_general
    (I_target := 6 * delta')
    V hV_meas hV_unit hV_inc hI_eps hepsilon_pos hrho_pos hcellDiam_pos hconstancy_pos
    cell hcell_meas representative hrep neighborBound hnb_pos hnearby
    hcapCount_pos capCenter hcapCenter_norm hsphere_cover
    with ⟨S', W, hsub, hlip, hunit, hinc, hmass⟩
  let s : ℝ := 6 * rho - 2 * cellDiam
  have hs : 1 / 3 ≤ s := hconstancy
  have hK_le : (Real.toNNReal (2 / s) : NNReal) ≤ (6 : NNReal) := by
    apply NNReal.coe_le_coe.mp
    have h1 : 2 / s ≤ 6 := by
      have h2 : 0 < s := by linarith
      calc 2 / s ≤ 2 / (1 / 3 : ℝ) := by gcongr
        _ = 6 := by norm_num
    simpa [Real.toNNReal_of_nonneg (show 0 ≤ 2 / s by positivity)] using h1
  have hlip6 : LipschitzWith 6 W := hlip.weaken hK_le
  exact ⟨S', W, hsub, hlip6, hunit, hinc, hmass⟩

end PureWZ2PlaneMap

/-!
## Pure WZ2 grain plane-map theorem

Constructs a 6-Lipschitz unit-norm plane map with incidence ≤ 6·delta' on the
genuine shaded union of a cropped grain base configuration.

### Proof approach (WZ1 cubical plane-map adaptation)

The construction follows the WZ1 cubical plane-map pipeline (Lemma 12–15),
adapted to the Pure WZ2 balanced-cover setting:

1. **Transverse pair per cell**: Apply `transverse_pair_plane_map_paper` to the
   base shading to obtain a weak plane map `V` with unit norm and incidence
   ≤ 6·delta' on a selected subshading retaining ≥ 1/4 of the narrow mass.

2. **Coarse cell decomposition**: Use the cubical property to decompose the
   box into coarse grid cells. In each active cell, select a cap on the unit
   sphere containing the heaviest subset of `V`-values; the cap center becomes
   the cell's plane-map value. Cap radius ε is chosen so that incidence remains
   ≤ 6·delta' after perturbation.

3. **Cell coloring**: Apply `pureWZ2_cell_separation` to color the nearby-cell
   graph and retain one color class. Selected cells are pairwise separated by
   more than the constancy scale, so the plane map is exactly constant at that
   scale on the retained set.

4. **Lipschitz assembly**: Points within the constancy scale have identical
   plane-map values; points farther apart satisfy the unit-norm bound dist ≤ 2.
   A direct case split gives `LipschitzWith 6` without needing the full
   finite-scale multi-scale iteration.

### Open sub-goals

The cap-based incidence preservation and mass-retention argument are the core
remaining geometric obligations. The theorem skeleton below is `sorry` until
these are filled in.
-/

/--
Construct a 6-Lipschitz unit-norm plane map with incidence ≤ 6·delta' on a
pruned subshading of a cropped grain base configuration.

The output shading `S'` is a subshading of `base.shading` on which the plane
map is well-defined and satisfies all properties. This pruning is inherent to
the cap + cell-separation construction and matches the WZ1 cubical plane-map
pattern.

This is the Pure WZ2 analogue of the WZ1 cubical plane-map assembly
(`wz1_cubical_plane_map`), adapted to the balanced-cover setting without
`UniformTubeStructure`.
-/
theorem pure_wz2_grain_plane_map
    {delta' I : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta'}
    (S : WZ1PaperTubeShading F)
    (V : Point3 → Point3)
    (hV_meas : Measurable V)
    (hV_unit : ∀ p ∈ S.union, ‖V p‖ = 1)
    (hV_inc : ∀ i p, p ∈ S.carrier i →
        |inner ℝ (F.tube i).direction (V p)| ≤ I)
    (hI_lt : I < 6 * delta') :
    ∃ (S' : WZ1PaperTubeShading F)
      (planeMap : {point : Point3 // point ∈ S'.union} → Point3),
      PaperIsSubshading S' S ∧
      LipschitzWith 6 planeMap ∧
      (∀ point, ‖planeMap point‖ = 1) ∧
      (∀ index point (hpoint : point ∈ S'.carrier index),
        |inner ℝ (F.tube index).direction
            (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ 6 * delta') ∧
      S.mass ≤ (2 : ENNReal) *
        (Fintype.card (Fin 3 → Fin (Nat.ceil (2 * Real.sqrt 3 / ((6 * delta' - I) / 2)))) : ENNReal) *
        S'.mass := by
  classical
  set epsilon : ℝ := (6 * delta' - I) / 2 with hepsilon_def
  have hepsilon_pos : 0 < epsilon := by
    rw [hepsilon_def]
    have h : 0 < 6 * delta' - I := by linarith
    linarith
  have hI_eps : I + epsilon ≤ 6 * delta' := by
    rw [hepsilon_def] <;> linarith

  -- Choose N for grid covering of unit ball
  let N : ℕ := Nat.ceil (2 * Real.sqrt 3 / epsilon)
  have hN_pos : 0 < N := by
    apply Nat.ceil_pos.mpr
    have h1 : 0 < 2 * Real.sqrt 3 / epsilon := by positivity
    linarith
  have hN1 : 1 ≤ N := by exact_mod_cast hN_pos
  have hdiam : Real.sqrt 3 * (2 * (1 : ℝ) / N) ≤ epsilon := by
    have h1 : (N : ℝ) ≥ 2 * Real.sqrt 3 / epsilon := Nat.le_ceil _
    have h2 : 0 < epsilon := hepsilon_pos
    have h_pos1 : 0 < 2 * Real.sqrt 3 := by positivity
    have h_den : 0 < 2 * Real.sqrt 3 / epsilon := by positivity
    have h_step : 2 * Real.sqrt 3 / (N : ℝ) ≤ 2 * Real.sqrt 3 / (2 * Real.sqrt 3 / epsilon) := by
      apply div_le_div_of_nonneg_left h_pos1.le
      <;> linarith
    have h_final : 2 * Real.sqrt 3 / (N : ℝ) ≤ epsilon := by
      calc
        2 * Real.sqrt 3 / (N : ℝ)
          ≤ 2 * Real.sqrt 3 / (2 * Real.sqrt 3 / epsilon) := h_step
        _ = epsilon := by field_simp [h2.ne'] <;> ring
    have h_eq : Real.sqrt 3 * (2 * (1 : ℝ) / N) = 2 * Real.sqrt 3 / (N : ℝ) := by ring
    rw [h_eq]
    exact h_final

  obtain ⟨C, hC_meas, hC_cover, hC_diam⟩ :=
    grid_covering_cover (0 : Point3) 1 epsilon (by norm_num) N hN1 (by positivity) hdiam

  let Idx := Fin 3 → Fin N
  let defaultUnit : Point3 :=
    WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)
  have hdefaultUnit_norm : ‖defaultUnit‖ = 1 := by
    simp [defaultUnit, PiLp.norm_eq_of_L2, Fin.sum_univ_succ] <;> norm_num

  let v (k : Idx) : Point3 :=
    if h : (C k ∩ Metric.sphere 0 1).Nonempty then
      Classical.choose h
    else
      defaultUnit
  have hv_norm : ∀ k : Idx, ‖v k‖ = 1 := by
    intro k
    dsimp only [v]
    by_cases h : (C k ∩ Metric.sphere 0 1).Nonempty
    · rw [dif_pos h]
      have h2 : Classical.choose h ∈ C k ∩ Metric.sphere 0 1 :=
        Classical.choose_spec h
      have h3 : Classical.choose h ∈ Metric.sphere 0 1 := h2.2
      simpa [Metric.mem_sphere] using h3
    · rw [dif_neg h]
      exact hdefaultUnit_norm

  let capCount := Fintype.card Idx
  have hcapCount_pos : 0 < capCount := by
    simp [capCount, Idx, hN_pos] <;> omega

  let e : Idx ≃ Fin capCount := Fintype.equivFin Idx
  let capCenter : Fin capCount → Point3 := fun k => v (e.symm k)
  have hcapCenter_norm : ∀ k : Fin capCount, ‖capCenter k‖ = 1 := by
    intro k
    exact hv_norm (e.symm k)

  have hsphere_cover : ∀ (x : Point3), ‖x‖ = 1 →
      ∃ k : Fin capCount, dist x (capCenter k) ≤ epsilon := by
    intro x hx
    have hdist0 : dist x (0 : Point3) ≤ 1 := by
      have h1 : dist x (0 : Point3) = ‖x‖ := by simp [dist_eq_norm]
      rw [h1, hx] <;> norm_num
    rcases hC_cover x hdist0 with ⟨k, hk⟩
    have h_inter : (C k ∩ Metric.sphere 0 1).Nonempty := by
      refine ⟨x, hk, ?_⟩
      simpa [Metric.mem_sphere] using hx
    have h_v_in : v k ∈ C k ∩ Metric.sphere 0 1 := by
      dsimp only [v]
      rw [dif_pos h_inter]
      exact Classical.choose_spec h_inter
    have h_v_in_C : v k ∈ C k := h_v_in.1
    have h_dist : dist x (v k) ≤ epsilon := hC_diam k x (v k) hk h_v_in_C
    refine ⟨e k, ?_⟩
    simpa [capCenter] using h_dist

  -- Trivial 1-cell decomposition
  let cell : Point3 → Fin 1 := fun _ => 0
  have hcell_meas : Measurable cell := by fun_prop
  let representative : Fin 1 → Point3 := fun _ => 0
  let cellDiam : ℝ := 2
  let rho : ℝ := 13 / 18
  let neighborBound : ℕ := 1
  have hnb_pos : 0 < neighborBound := by norm_num
  have hcellDiam_pos : 0 < cellDiam := by norm_num
  have hrho_pos : 0 < rho := by norm_num
  have hconstancy : 1 / 3 ≤ 6 * rho - 2 * cellDiam := by
    norm_num [rho, cellDiam]

  have hrep : ∀ p ∈ S.union, dist p (representative (cell p)) ≤ cellDiam := by
    intro p hp
    have h1 : p ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
      rcases hp with ⟨i, hi⟩
      have h2 : S.carrier i ⊆ wz1PaperTubeCarrier (F.tube i) :=
        S.subset_body i
      have h3 : p ∈ wz1PaperTubeCarrier (F.tube i) := h2 hi
      exact h3.2
    have h4 : ∀ j : Fin 3, |p j| ≤ 1 := by
      have h1' : |p 0| ≤ (2 : ℝ) / 2 ∧ |p 1| ≤ (2 : ℝ) / 2 ∧ |p 2| ≤ (2 : ℝ) / 2 := by
        simpa [Kakeya.Streamlined.axisBox] using h1
      have h1'' : |p 0| ≤ 1 ∧ |p 1| ≤ 1 ∧ |p 2| ≤ 1 := by
        norm_num at h1' ⊢ <;> exact h1'
      intro j
      fin_cases j <;> tauto
    have h5 : ‖p‖ ≤ Real.sqrt 3 := by
      have h_sum : ∑ i : Fin 3, (p i) ^ 2 ≤ 3 := by
        have h7 : ∀ i : Fin 3, (p i) ^ 2 ≤ 1 := by
          intro i
          have h8 : |p i| ≤ 1 := h4 i
          nlinarith [abs_le.mp h8]
        have h12 : ∑ i : Fin 3, (p i) ^ 2 ≤ ∑ i : Fin 3, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          exact h7 i
        simpa using h12
      have h_norm2 : ‖p‖ ^ 2 = ∑ i : Fin 3, (p i) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq p
      have h13 : ‖p‖ ^ 2 ≤ 3 := by
        rw [h_norm2]
        exact h_sum
      have h14 : 0 ≤ ‖p‖ := by positivity
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h6 : dist p (representative (cell p)) = ‖p‖ := by
      simp [cell, representative, dist_eq_norm]
    rw [h6]
    have h7 : Real.sqrt 3 < 2 := Real.sqrt_lt' (by norm_num) |>.mpr (by norm_num)
    linarith

  have hnearby : ∀ (c : Fin 1),
      (∃ p ∈ S.union, cell p = c) →
      (Finset.univ.filter fun d : Fin 1 =>
        (∃ p ∈ S.union, cell p = d) ∧
        dist (representative c) (representative d) ≤ 6 * rho).card ≤ neighborBound := by
    intro c _
    have h2 : (Finset.univ.filter fun d : Fin 1 =>
        (∃ p ∈ S.union, cell p = d) ∧
        dist (representative c) (representative d) ≤ 6 * rho).card ≤
        (Finset.univ : Finset (Fin 1)).card := Finset.card_filter_le _ _
    have h3 : (Finset.univ : Finset (Fin 1)).card = 1 := by simp
    rw [h3] at h2
    simpa [neighborBound] using h2

  have h_result := PureWZ2PlaneMap.paper_cap_cell_lipschitz
    (S := S)
    V hV_meas hV_unit hV_inc hI_eps hepsilon_pos hrho_pos hcellDiam_pos hconstancy
    cell hcell_meas representative hrep neighborBound hnb_pos hnearby
    hcapCount_pos capCenter hcapCenter_norm hsphere_cover
  rcases h_result with ⟨S', W, hsub, hlip, hunit, hinc, hmass⟩
  have hmass' : S.mass ≤ (2 : ENNReal) * (capCount : ENNReal) * S'.mass := by
    have h : S.mass ≤ (capCount : ENNReal) * ((neighborBound + 1 : ℕ) : ENNReal) * S'.mass := hmass
    have hnb : ((neighborBound + 1 : ℕ) : ENNReal) = (2 : ENNReal) := by
      simp [neighborBound] <;> norm_cast
    have h2 : S.mass ≤ (capCount : ENNReal) * (2 : ENNReal) * S'.mass := by
      convert h using 2
      <;> rw [hnb]
    have h_comm : (capCount : ENNReal) * (2 : ENNReal) * S'.mass = (2 : ENNReal) * (capCount : ENNReal) * S'.mass := by ring
    rw [h_comm] at h2
    exact h2
  exact ⟨S', W, hsub, hlip, hunit, hinc, hmass'⟩

/--
Construct a 1-Lipschitz unit-norm plane map with configurable incidence bound on a
pruned subshading, using the no-dilation 1-cell decomposition.

With `rho = 1`, `cellDiam = 2`, the constancy scale is `6*1 - 2*2 = 2`, giving
`LipschitzWith (2/2) = 1`. The incidence bound `I_target` is configurable; the
weak plane map must satisfy `I < I_target` to leave room for cap perturbation.

This is the no-dilation analogue of `pure_wz2_grain_plane_map`: it preserves the
original line class, cubical shading, extremality, and CWA because it does not
rescale the family.
-/
theorem pure_wz2_grain_plane_map_tight
    {delta' I I_target : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta'}
    (S : WZ1PaperTubeShading F)
    (V : Point3 → Point3)
    (hV_meas : Measurable V)
    (hV_unit : ∀ p ∈ S.union, ‖V p‖ = 1)
    (hV_inc : ∀ i p, p ∈ S.carrier i →
        |inner ℝ (F.tube i).direction (V p)| ≤ I)
    (hI_lt : I < I_target) :
    ∃ (S' : WZ1PaperTubeShading F)
      (planeMap : {point : Point3 // point ∈ S'.union} → Point3),
      PaperIsSubshading S' S ∧
      LipschitzWith 1 planeMap ∧
      (∀ point, ‖planeMap point‖ = 1) ∧
      (∀ index point (hpoint : point ∈ S'.carrier index),
        |inner ℝ (F.tube index).direction
            (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ I_target) ∧
      S.mass ≤ (2 : ENNReal) *
        (Fintype.card (Fin 3 → Fin (Nat.ceil (2 * Real.sqrt 3 / ((I_target - I) / 2)))) : ENNReal) *
        S'.mass := by
  classical
  set epsilon : ℝ := (I_target - I) / 2 with hepsilon_def
  have hepsilon_pos : 0 < epsilon := by
    rw [hepsilon_def]
    have h : 0 < I_target - I := by linarith
    linarith
  have hI_eps : I + epsilon ≤ I_target := by
    rw [hepsilon_def] <;> linarith

  -- Choose N for grid covering of unit ball
  let N : ℕ := Nat.ceil (2 * Real.sqrt 3 / epsilon)
  have hN_pos : 0 < N := by
    apply Nat.ceil_pos.mpr
    have h1 : 0 < 2 * Real.sqrt 3 / epsilon := by positivity
    linarith
  have hN1 : 1 ≤ N := by exact_mod_cast hN_pos
  have hdiam : Real.sqrt 3 * (2 * (1 : ℝ) / N) ≤ epsilon := by
    have h1 : (N : ℝ) ≥ 2 * Real.sqrt 3 / epsilon := Nat.le_ceil _
    have h2 : 0 < epsilon := hepsilon_pos
    have h_pos1 : 0 < 2 * Real.sqrt 3 := by positivity
    have h_step : 2 * Real.sqrt 3 / (N : ℝ) ≤ 2 * Real.sqrt 3 / (2 * Real.sqrt 3 / epsilon) := by
      gcongr
      <;> linarith
    have h_final : 2 * Real.sqrt 3 / (N : ℝ) ≤ epsilon := by
      calc
        2 * Real.sqrt 3 / (N : ℝ)
          ≤ 2 * Real.sqrt 3 / (2 * Real.sqrt 3 / epsilon) := h_step
        _ = epsilon := by field_simp [h2.ne'] <;> ring
    have h_eq : Real.sqrt 3 * (2 * (1 : ℝ) / N) = 2 * Real.sqrt 3 / (N : ℝ) := by ring
    rw [h_eq]
    exact h_final

  obtain ⟨C, hC_meas, hC_cover, hC_diam⟩ :=
    grid_covering_cover (0 : Point3) 1 epsilon (by norm_num) N hN1 (by positivity) hdiam

  let Idx := Fin 3 → Fin N
  let defaultUnit : Point3 :=
    WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)
  have hdefaultUnit_norm : ‖defaultUnit‖ = 1 := by
    simp [defaultUnit, PiLp.norm_eq_of_L2, Fin.sum_univ_succ] <;> norm_num

  let v (k : Idx) : Point3 :=
    if h : (C k ∩ Metric.sphere 0 1).Nonempty then
      Classical.choose h
    else
      defaultUnit
  have hv_norm : ∀ k : Idx, ‖v k‖ = 1 := by
    intro k
    dsimp only [v]
    by_cases h : (C k ∩ Metric.sphere 0 1).Nonempty
    · rw [dif_pos h]
      have h2 : Classical.choose h ∈ C k ∩ Metric.sphere 0 1 :=
        Classical.choose_spec h
      have h3 : Classical.choose h ∈ Metric.sphere 0 1 := h2.2
      simpa [Metric.mem_sphere] using h3
    · rw [dif_neg h]
      exact hdefaultUnit_norm

  let capCount := Fintype.card Idx
  have hcapCount_pos : 0 < capCount := by
    simp [capCount, Idx, hN_pos] <;> omega

  let e : Idx ≃ Fin capCount := Fintype.equivFin Idx
  let capCenter : Fin capCount → Point3 := fun k => v (e.symm k)
  have hcapCenter_norm : ∀ k : Fin capCount, ‖capCenter k‖ = 1 := by
    intro k
    exact hv_norm (e.symm k)

  have hsphere_cover : ∀ (x : Point3), ‖x‖ = 1 →
      ∃ k : Fin capCount, dist x (capCenter k) ≤ epsilon := by
    intro x hx
    have hdist0 : dist x (0 : Point3) ≤ 1 := by
      have h1 : dist x (0 : Point3) = ‖x‖ := by simp [dist_eq_norm]
      rw [h1, hx] <;> norm_num
    rcases hC_cover x hdist0 with ⟨k, hk⟩
    have h_inter : (C k ∩ Metric.sphere 0 1).Nonempty := by
      refine ⟨x, hk, ?_⟩
      simpa [Metric.mem_sphere] using hx
    have h_v_in : v k ∈ C k ∩ Metric.sphere 0 1 := by
      dsimp only [v]
      rw [dif_pos h_inter]
      exact Classical.choose_spec h_inter
    have h_v_in_C : v k ∈ C k := h_v_in.1
    have h_dist : dist x (v k) ≤ epsilon := hC_diam k x (v k) hk h_v_in_C
    refine ⟨e k, ?_⟩
    simpa [capCenter] using h_dist

  -- No-dilation 1-cell decomposition: rho=1, cellDiam=2 → constancy=2 → Lipschitz 1
  let cell : Point3 → Fin 1 := fun _ => 0
  have hcell_meas : Measurable cell := by fun_prop
  let representative : Fin 1 → Point3 := fun _ => 0
  let cellDiam : ℝ := 2
  let rho : ℝ := 1
  let neighborBound : ℕ := 1
  have hnb_pos : 0 < neighborBound := by norm_num
  have hcellDiam_pos : 0 < cellDiam := by norm_num
  have hrho_pos : 0 < rho := by norm_num
  have hconstancy_pos : 0 < 6 * rho - 2 * cellDiam := by
    norm_num [rho, cellDiam]

  have hrep : ∀ p ∈ S.union, dist p (representative (cell p)) ≤ cellDiam := by
    intro p hp
    have h1 : p ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
      rcases hp with ⟨i, hi⟩
      have h2 : S.carrier i ⊆ wz1PaperTubeCarrier (F.tube i) :=
        S.subset_body i
      have h3 : p ∈ wz1PaperTubeCarrier (F.tube i) := h2 hi
      exact h3.2
    have h4 : ∀ j : Fin 3, |p j| ≤ 1 := by
      have h1' : |p 0| ≤ (2 : ℝ) / 2 ∧ |p 1| ≤ (2 : ℝ) / 2 ∧ |p 2| ≤ (2 : ℝ) / 2 := by
        simpa [Kakeya.Streamlined.axisBox] using h1
      have h1'' : |p 0| ≤ 1 ∧ |p 1| ≤ 1 ∧ |p 2| ≤ 1 := by
        norm_num at h1' ⊢ <;> exact h1'
      intro j
      fin_cases j <;> tauto
    have h5 : ‖p‖ ≤ Real.sqrt 3 := by
      have h_sum : ∑ i : Fin 3, (p i) ^ 2 ≤ 3 := by
        have h7 : ∀ i : Fin 3, (p i) ^ 2 ≤ 1 := by
          intro i
          have h8 : |p i| ≤ 1 := h4 i
          nlinarith [abs_le.mp h8]
        have h12 : ∑ i : Fin 3, (p i) ^ 2 ≤ ∑ i : Fin 3, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          exact h7 i
        simpa using h12
      have h_norm2 : ‖p‖ ^ 2 = ∑ i : Fin 3, (p i) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq p
      have h13 : ‖p‖ ^ 2 ≤ 3 := by
        rw [h_norm2]
        exact h_sum
      have h14 : 0 ≤ ‖p‖ := by positivity
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h6 : dist p (representative (cell p)) = ‖p‖ := by
      simp [cell, representative, dist_eq_norm]
    rw [h6]
    have h7 : Real.sqrt 3 < 2 := Real.sqrt_lt' (by norm_num) |>.mpr (by norm_num)
    linarith

  have hnearby : ∀ (c : Fin 1),
      (∃ p ∈ S.union, cell p = c) →
      (Finset.univ.filter fun d : Fin 1 =>
        (∃ p ∈ S.union, cell p = d) ∧
        dist (representative c) (representative d) ≤ 6 * rho).card ≤ neighborBound := by
    intro c _
    have h2 : (Finset.univ.filter fun d : Fin 1 =>
        (∃ p ∈ S.union, cell p = d) ∧
        dist (representative c) (representative d) ≤ 6 * rho).card ≤
        (Finset.univ : Finset (Fin 1)).card := Finset.card_filter_le _ _
    have h3 : (Finset.univ : Finset (Fin 1)).card = 1 := by simp
    rw [h3] at h2
    simpa [neighborBound] using h2

  rcases PureWZ2PlaneMap.paper_cap_cell_lipschitz_general
    (I_target := I_target)
    (S := S)
    V hV_meas hV_unit hV_inc hI_eps hepsilon_pos hrho_pos hcellDiam_pos hconstancy_pos
    cell hcell_meas representative hrep neighborBound hnb_pos hnearby
    hcapCount_pos capCenter hcapCenter_norm hsphere_cover
    with ⟨S', W, hsub, hlip, hunit, hinc, hmass⟩

  -- Convert Lipschitz constant: 2 / (6*1 - 2*2) = 2 / 2 = 1
  have hK_eq : Real.toNNReal (2 / (6 * rho - 2 * cellDiam)) = (1 : NNReal) := by
    apply NNReal.coe_injective
    have h9 : (2 / (6 * rho - 2 * cellDiam)) = 1 := by
      simp [rho, cellDiam] <;> norm_num
    rw [h9]
    simp [Real.toNNReal] <;> norm_num
  rw [hK_eq] at hlip
  have hmass' : S.mass ≤ (2 : ENNReal) * (capCount : ENNReal) * S'.mass := by
    have h : S.mass ≤ (capCount : ENNReal) * (2 : ENNReal) * S'.mass := by
      simpa [neighborBound] using hmass
    have h_comm : (capCount : ENNReal) * (2 : ENNReal) * S'.mass = (2 : ENNReal) * (capCount : ENNReal) * S'.mass := by ring
    rw [h_comm] at h
    exact h
  exact ⟨S', W, hsub, hlip, hunit, hinc, hmass'⟩

/-!
## Wiring lemma: transverse pair preconditions → Lipschitz plane map

Assembles the chain:
  base shading → narrow pruning → weak planiness (V at tau/kappa) →
  cap+cell Lipschitz plane map (at 6·delta')

The key hypothesis `hmult_lower` is supplied by ember's multiplicity
dichotomy (HIGH case). The broad-set mass bound and close-direction count
are passed as hypotheses; they follow from PaperCV and direction packing
respectively.
-/

/--
Wiring lemma: from transverse-pair preconditions on a shading `S`, produce
a twice-pruned subshading `S'` with a 6-Lipschitz unit-norm plane map of
incidence ≤ 6·delta'.

The incidence gap is strict at the weak-plane-map stage (`tau/kappa < 6·delta'`),
which leaves room for the cap-covering perturbation in
`pure_wz2_grain_plane_map`.
-/
theorem pure_wz2_grain_plane_map_wiring
    {delta' kappa tau : ℝ} {Q R m : ℕ}
    {F : Kakeya.Streamlined.TubeFamily delta'}
    {S : WZ1PaperTubeShading F}
    (hkappa_pos : 0 < kappa)
    (hF : F.Nonempty)
    (hincidence_strict : tau / kappa < 6 * delta')
    (hmult_lower : ∀ p ∈ S.union, m ≤ S.pointMultiplicity p)
    (hQ : 4 * Q ≤ m ^ 3)
    (hR : 12 * R ≤ m)
    (hbroad_meas : MeasurableSet (paperCountedBroadSet S tau Q))
    (hbroad_small :
      2 * (∫⁻ p in paperCountedBroadSet S tau Q,
        (S.pointMultiplicity p : ENNReal)) ≤ S.mass)
    (hclose : ∀ p ∈ S.union, ∀ i,
      p ∈ S.carrier i →
        paperCloseDirectionCount S p i kappa < R) :
    ∃ (selected : WZ1PaperTubeShading F)
      (S' : WZ1PaperTubeShading F)
      (W : {point : Point3 // point ∈ S'.union} → Point3),
      PaperIsSubshading selected S ∧
      PaperIsSubshading S' selected ∧
      LipschitzWith 6 W ∧
      (∀ point, ‖W point‖ = 1) ∧
      (∀ index point (hpoint : point ∈ S'.carrier index),
        |inner ℝ (F.tube index).direction
            (W ⟨point, ⟨index, hpoint⟩⟩)| ≤ 6 * delta') ∧
      S.mass ≤ (16 : ENNReal) * (Fintype.card (Fin 3 → Fin (Nat.ceil (2 * Real.sqrt 3 / ((6 * delta' - tau / kappa) / 2))))) * S'.mass := by
  classical
  -- Step 1: Paper narrow pruning
  have h_narrow : Nonempty (PaperWZ1NarrowRefinementData S tau Q) :=
    paper_narrow_pruning hbroad_meas hbroad_small
  rcases h_narrow with ⟨narrow⟩
  -- Step 2: Multiplicity preservation on narrow shading
  have h_mult_eq : ∀ p ∈ narrow.shading.union,
      narrow.shading.pointMultiplicity p = S.pointMultiplicity p := by
    intro p hp
    have h_not_broad : p ∉ paperCountedBroadSet S tau Q := by
      rcases hp with ⟨i, hi⟩
      have h : p ∈ S.carrier i \ paperCountedBroadSet S tau Q := by
        rw [narrow.carrier_eq i] at hi <;> exact hi
      exact h.2
    have h1 : ∀ j : Fin F.card, p ∈ narrow.shading.carrier j ↔ p ∈ S.carrier j := by
      intro j
      rw [narrow.carrier_eq j]
      simp [h_not_broad]
    have h_le1 : narrow.shading.pointMultiplicity p ≤ S.pointMultiplicity p := by
      classical
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact (h1 j).mp hj
    have h_le2 : S.pointMultiplicity p ≤ narrow.shading.pointMultiplicity p := by
      classical
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact (h1 j).mpr hj
    exact le_antisymm h_le1 h_le2
  have hmult : ∀ p ∈ narrow.shading.union,
      let mu := narrow.shading.pointMultiplicity p
      4 * (Q + 3 * R * mu ^ 2) ≤ 3 * mu ^ 3 := by
    intro p hp
    let mu := narrow.shading.pointMultiplicity p
    have h_mu_eq : mu = S.pointMultiplicity p := h_mult_eq p hp
    have h_mu_lower : m ≤ mu := by
      rw [h_mu_eq]
      exact hmult_lower p (by
        rcases hp with ⟨i, hi⟩
        exact ⟨i, narrow.subshading i hi⟩)
    exact wz1_good_triple_budget m Q R mu h_mu_lower hQ hR
  -- Step 3: Close-direction count transfers to narrow shading
  have hclose_narrow : ∀ p ∈ narrow.shading.union, ∀ i,
      p ∈ narrow.shading.carrier i →
        paperCloseDirectionCount narrow.shading p i kappa < R := by
    intro p hp i hpi
    have h1 : p ∈ S.carrier i := narrow.subshading i hpi
    have h2 : p ∈ S.union := ⟨i, h1⟩
    have h3 : paperCloseDirectionCount narrow.shading p i kappa ≤
        paperCloseDirectionCount S p i kappa := by
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter] at hj ⊢
      exact ⟨hj.1, narrow.subshading j hj.2.1, hj.2.2⟩
    exact h3.trans_lt (hclose p h2 i h1)
  -- Step 4: Weak planiness from narrow (incidence = tau / kappa)
  have h_main := paper_weak_planiness_from_narrow
    hkappa_pos hF narrow hclose_narrow hmult
  rcases h_main with ⟨selection, selected, planeMap, hsub_selected, hmass⟩
  -- Step 5: selected is a subshading of S (via narrow)
  have hsub_selected_S : PaperIsSubshading selected S := by
    intro i
    exact Set.Subset.trans (hsub_selected i) (narrow.subshading i)
  -- Step 6: Apply cap+cell Lipschitz construction with strict gap
  have hI_lt : tau / kappa < 6 * delta' := hincidence_strict
  have h_result := pure_wz2_grain_plane_map
    (S := selected)
    planeMap.planeMap
    planeMap.measurable
    planeMap.unit
    planeMap.incidence
    hI_lt
  rcases h_result with ⟨S', W, hsub_S', hlip, hunit, hinc, hmass_cap⟩
  have hmass_narrow : (1 / 2 : ENNReal) * S.mass ≤ narrow.shading.mass := narrow.mass_lower
  have hmass_selected : (1 / 4 : ENNReal) * narrow.shading.mass ≤ selected.mass := hmass
  set epsilon : ℝ := (6 * delta' - tau / kappa) / 2 with hepsilon_def
  set N : ℕ := Nat.ceil (2 * Real.sqrt 3 / epsilon) with hN_def
  set capCount : ℕ := Fintype.card (Fin 3 → Fin N) with hcapCount_def
  have hmass_total : S.mass ≤ (16 : ENNReal) * (capCount : ENNReal) * S'.mass := by
    have h_mul2 : (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
      have h : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by simp [one_div]
      rw [h]
      exact ENNReal.mul_inv_cancel (by simp) (by simp)
    have h_mul4 : (4 : ENNReal) * (1 / 4 : ENNReal) = 1 := by
      have h : (1 / 4 : ENNReal) = (4 : ENNReal)⁻¹ := by simp [one_div]
      rw [h]
      exact ENNReal.mul_inv_cancel (by simp) (by simp)
    have h1 : S.mass ≤ (2 : ENNReal) * narrow.shading.mass := by
      have h2 : (2 : ENNReal) * ((1 / 2 : ENNReal) * S.mass) = S.mass := by
        rw [←mul_assoc, h_mul2, one_mul]
      have h3 : (2 : ENNReal) * ((1 / 2 : ENNReal) * S.mass) ≤ (2 : ENNReal) * narrow.shading.mass :=
        mul_le_mul_of_nonneg_left hmass_narrow (by positivity)
      rwa [h2] at h3
    have h3 : narrow.shading.mass ≤ (4 : ENNReal) * selected.mass := by
      have h4 : (4 : ENNReal) * ((1 / 4 : ENNReal) * narrow.shading.mass) = narrow.shading.mass := by
        rw [←mul_assoc, h_mul4, one_mul]
      have h5 : (4 : ENNReal) * ((1 / 4 : ENNReal) * narrow.shading.mass) ≤ (4 : ENNReal) * selected.mass :=
        mul_le_mul_of_nonneg_left hmass_selected (by positivity)
      rwa [h4] at h5
    have h5 : selected.mass ≤ (2 : ENNReal) * (capCount : ENNReal) * S'.mass := by
      simpa [capCount, N, epsilon] using hmass_cap
    calc
      S.mass ≤ (2 : ENNReal) * narrow.shading.mass := h1
      _ ≤ (2 : ENNReal) * ((4 : ENNReal) * selected.mass) := by gcongr
      _ = (8 : ENNReal) * selected.mass := by ring
      _ ≤ (8 : ENNReal) * ((2 : ENNReal) * (capCount : ENNReal) * S'.mass) := by gcongr
      _ = (16 : ENNReal) * (capCount : ENNReal) * S'.mass := by ring
  exact ⟨selected, S', W, hsub_selected_S, hsub_S', hlip, hunit, hinc, hmass_total⟩

/--
Tight wiring lemma: from transverse-pair preconditions on a shading `S`, produce
a twice-pruned subshading `S'` with a **1-Lipschitz** unit-norm plane map of
configurable incidence `≤ I_target`.

Uses the no-dilation 1-cell decomposition (`rho=1`, `cellDiam=2`) so the
Lipschitz constant is exactly 1. The incidence gap is strict at the weak-plane-map
stage (`tau/kappa < I_target`), leaving room for cap perturbation.

This preserves the original line class, cubical shading, extremality, and CWA
because no rescaling is performed.
-/
theorem pure_wz2_grain_plane_map_wiring_tight
    {delta' kappa tau I_target : ℝ} {Q R m : ℕ}
    {F : Kakeya.Streamlined.TubeFamily delta'}
    {S : WZ1PaperTubeShading F}
    (hkappa_pos : 0 < kappa)
    (hF : F.Nonempty)
    (hincidence_strict : tau / kappa < I_target)
    (hmult_lower : ∀ p ∈ S.union, m ≤ S.pointMultiplicity p)
    (hQ : 4 * Q ≤ m ^ 3)
    (hR : 12 * R ≤ m)
    (hbroad_meas : MeasurableSet (paperCountedBroadSet S tau Q))
    (hbroad_small :
      2 * (∫⁻ p in paperCountedBroadSet S tau Q,
        (S.pointMultiplicity p : ENNReal)) ≤ S.mass)
    (hclose : ∀ p ∈ S.union, ∀ i,
      p ∈ S.carrier i →
        paperCloseDirectionCount S p i kappa < R) :
    ∃ (selected : WZ1PaperTubeShading F)
      (S' : WZ1PaperTubeShading F)
      (W : {point : Point3 // point ∈ S'.union} → Point3),
      PaperIsSubshading selected S ∧
      PaperIsSubshading S' selected ∧
      LipschitzWith 1 W ∧
      (∀ point, ‖W point‖ = 1) ∧
      (∀ index point (hpoint : point ∈ S'.carrier index),
        |inner ℝ (F.tube index).direction
            (W ⟨point, ⟨index, hpoint⟩⟩)| ≤ I_target) ∧
      S.mass ≤ (16 : ENNReal) * (Fintype.card (Fin 3 → Fin (Nat.ceil (2 * Real.sqrt 3 / ((I_target - tau / kappa) / 2))))) * S'.mass := by
  classical
  -- Step 1: Paper narrow pruning
  have h_narrow : Nonempty (PaperWZ1NarrowRefinementData S tau Q) :=
    paper_narrow_pruning hbroad_meas hbroad_small
  rcases h_narrow with ⟨narrow⟩
  -- Step 2: Multiplicity preservation on narrow shading
  have h_mult_eq : ∀ p ∈ narrow.shading.union,
      narrow.shading.pointMultiplicity p = S.pointMultiplicity p := by
    intro p hp
    have h_not_broad : p ∉ paperCountedBroadSet S tau Q := by
      rcases hp with ⟨i, hi⟩
      have h : p ∈ S.carrier i \ paperCountedBroadSet S tau Q := by
        rw [narrow.carrier_eq i] at hi <;> exact hi
      exact h.2
    have h1 : ∀ j : Fin F.card, p ∈ narrow.shading.carrier j ↔ p ∈ S.carrier j := by
      intro j
      rw [narrow.carrier_eq j]
      simp [h_not_broad]
    have h_le1 : narrow.shading.pointMultiplicity p ≤ S.pointMultiplicity p := by
      classical
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact (h1 j).mp hj
    have h_le2 : S.pointMultiplicity p ≤ narrow.shading.pointMultiplicity p := by
      classical
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact (h1 j).mpr hj
    exact le_antisymm h_le1 h_le2
  have hmult : ∀ p ∈ narrow.shading.union,
      let mu := narrow.shading.pointMultiplicity p
      4 * (Q + 3 * R * mu ^ 2) ≤ 3 * mu ^ 3 := by
    intro p hp
    let mu := narrow.shading.pointMultiplicity p
    have h_mu_eq : mu = S.pointMultiplicity p := h_mult_eq p hp
    have h_mu_lower : m ≤ mu := by
      rw [h_mu_eq]
      exact hmult_lower p (by
        rcases hp with ⟨i, hi⟩
        exact ⟨i, narrow.subshading i hi⟩)
    exact wz1_good_triple_budget m Q R mu h_mu_lower hQ hR
  -- Step 3: Close-direction count transfers to narrow shading
  have hclose_narrow : ∀ p ∈ narrow.shading.union, ∀ i,
      p ∈ narrow.shading.carrier i →
        paperCloseDirectionCount narrow.shading p i kappa < R := by
    intro p hp i hpi
    have h1 : p ∈ S.carrier i := narrow.subshading i hpi
    have h2 : p ∈ S.union := ⟨i, h1⟩
    have h3 : paperCloseDirectionCount narrow.shading p i kappa ≤
        paperCloseDirectionCount S p i kappa := by
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter] at hj ⊢
      exact ⟨hj.1, narrow.subshading j hj.2.1, hj.2.2⟩
    exact h3.trans_lt (hclose p h2 i h1)
  -- Step 4: Weak planiness from narrow (incidence = tau / kappa)
  have h_main := paper_weak_planiness_from_narrow
    hkappa_pos hF narrow hclose_narrow hmult
  rcases h_main with ⟨selection, selected, planeMap, hsub_selected, hmass⟩
  -- Step 5: selected is a subshading of S (via narrow)
  have hsub_selected_S : PaperIsSubshading selected S := by
    intro i
    exact Set.Subset.trans (hsub_selected i) (narrow.subshading i)
  -- Step 6: Apply tight cap+cell Lipschitz construction with strict gap
  have hI_lt : tau / kappa < I_target := hincidence_strict
  have h_result := pure_wz2_grain_plane_map_tight
    (S := selected)
    planeMap.planeMap
    planeMap.measurable
    planeMap.unit
    planeMap.incidence
    hI_lt
  rcases h_result with ⟨S', W, hsub_S', hlip, hunit, hinc, hmass_cap⟩
  have hmass_narrow : (1 / 2 : ENNReal) * S.mass ≤ narrow.shading.mass := narrow.mass_lower
  have hmass_selected : (1 / 4 : ENNReal) * narrow.shading.mass ≤ selected.mass := hmass
  set epsilon : ℝ := (I_target - tau / kappa) / 2 with hepsilon_def
  set N : ℕ := Nat.ceil (2 * Real.sqrt 3 / epsilon) with hN_def
  set capCount : ℕ := Fintype.card (Fin 3 → Fin N) with hcapCount_def
  have h_nat_mul_inv : ∀ (n : ℕ), n ≠ 0 → (n : ENNReal) * (1 / (n : ENNReal)) = 1 := by
    intro n hn
    have h1 : (n : ENNReal) ≠ 0 := by exact_mod_cast hn
    have h2 : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
    have h3 : (1 / (n : ENNReal)) = (n : ENNReal)⁻¹ := by simp [one_div]
    rw [h3]
    exact ENNReal.mul_inv_cancel h1 h2
  have h_mul2 : (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
    exact_mod_cast h_nat_mul_inv 2 (by norm_num)
  have h_mul4 : (4 : ENNReal) * (1 / 4 : ENNReal) = 1 := by
    exact_mod_cast h_nat_mul_inv 4 (by norm_num)
  have hmass_total : S.mass ≤ (16 : ENNReal) * (capCount : ENNReal) * S'.mass := by
    have h1 : S.mass ≤ (2 : ENNReal) * narrow.shading.mass := by
      have h2 : (2 : ENNReal) * ((1 / 2 : ENNReal) * S.mass) = S.mass := by
        rw [←mul_assoc, h_mul2, one_mul]
      have h3 : (2 : ENNReal) * ((1 / 2 : ENNReal) * S.mass) ≤ (2 : ENNReal) * narrow.shading.mass :=
        mul_le_mul_of_nonneg_left hmass_narrow (by positivity)
      rwa [h2] at h3
    have h3 : narrow.shading.mass ≤ (4 : ENNReal) * selected.mass := by
      have h4 : (4 : ENNReal) * ((1 / 4 : ENNReal) * narrow.shading.mass) = narrow.shading.mass := by
        rw [←mul_assoc, h_mul4, one_mul]
      have h5 : (4 : ENNReal) * ((1 / 4 : ENNReal) * narrow.shading.mass) ≤ (4 : ENNReal) * selected.mass :=
        mul_le_mul_of_nonneg_left hmass_selected (by positivity)
      rwa [h4] at h5
    have h5 : selected.mass ≤ (2 : ENNReal) * (capCount : ENNReal) * S'.mass := by
      simpa [capCount, N, epsilon] using hmass_cap
    calc
      S.mass ≤ (2 : ENNReal) * narrow.shading.mass := h1
      _ ≤ (2 : ENNReal) * ((4 : ENNReal) * selected.mass) := by gcongr
      _ = (8 : ENNReal) * selected.mass := by ring
      _ ≤ (8 : ENNReal) * ((2 : ENNReal) * (capCount : ENNReal) * S'.mass) := by gcongr
      _ = (16 : ENNReal) * (capCount : ENNReal) * S'.mass := by ring
  exact ⟨selected, S', W, hsub_selected_S, hsub_S', hlip, hunit, hinc, hmass_total⟩

end Kakeya.Assouad

end
