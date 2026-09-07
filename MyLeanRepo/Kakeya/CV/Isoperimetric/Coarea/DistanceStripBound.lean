import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.GraphArea
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.GraphAreaSmooth
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic

/-!
# C¹ Graph Distance Strip Bound

For a C¹ function `g : E m → ℝ` and a bounded measurable `A ⊆ E m`,
the one-sided distance strip of thickness `t` over `A` has volume
`≤ (H^m(graph g ∩ cylinder A) + ε) * t` for sufficiently small `t`.

## Proof approach

1. **Pointwise fiber bound**: for each `x ∈ A`, the vertical fiber of the
   distance strip at `x` has length `≤ t * (√(1+‖fderiv g x‖²) + η)`, using:
   - Existence of a nearby graph point (`infDist < t`)
   - C¹ local approximation (error `η * ‖u‖`)
   - 2D Cauchy-Schwarz: `v + ‖a‖‖u‖ ≤ √(1+‖a‖²) · √(v²+‖u‖²)`

2. **Fubini**: `volume(strip) = ∫_A volume(fiber_x) dx`
   `≤ ∫_A t · (√(1+‖fderiv g x‖²) + η) dx`
   `= t · (graph area + η · volume A)`
   `≤ t · (graph area + ε)` for small `η`.

3. **Uniform C¹ approximation** on bounded `A` follows from uniform continuity
   of `fderiv g` on a compact neighborhood.
-/

open MeasureTheory Metric Set ENNReal LinearMap Filter
open scoped MeasureTheory Pointwise Classical
open GraphAreaFormula

namespace Geometry.Isoperimetric

variable {m : ℕ} [Nonempty (Fin m)]

-- `E n` is `Geometry.E` from Basic.lean

-- ============================================================================
-- Distance strip definition
-- ============================================================================

/-- One-sided distance strip over A: points above the graph with
distance to graph in `(0, t)`. -/
def distanceStrip (g : E m → ℝ) (A : Set (E m)) (t : ℝ) : Set (E (m + 1)) :=
  {p | proj p ∈ A ∧ 0 < infDist p (graph g) ∧ infDist p (graph g) < t ∧
       p (Fin.last m) > g (proj p)}

/-- Lower distance strip over A: points below the graph with
distance to graph in `(0, t)`. -/
def lowerStrip (g : E m → ℝ) (A : Set (E m)) (t : ℝ) : Set (E (m + 1)) :=
  {p | proj p ∈ A ∧ 0 < infDist p (graph g) ∧ infDist p (graph g) < t ∧
       p (Fin.last m) < g (proj p)}

-- ============================================================================
-- Coordinate equivalence E(m+1) ≃ᵐ E(m) × ℝ
-- ============================================================================

noncomputable def eSplit : E (m + 1) ≃ᵐ E m × ℝ :=
  let e1 : E (m + 1) ≃ᵐ (Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm
  let e2 : (Fin (m + 1) → ℝ) ≃ᵐ (ℝ × (Fin m → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last m)
  let e3 : (ℝ × (Fin m → ℝ)) ≃ᵐ ((Fin m → ℝ) × ℝ) :=
    MeasurableEquiv.prodComm
  let e4 : (Fin m → ℝ) ≃ᵐ E m :=
    MeasurableEquiv.toLp 2 (Fin m → ℝ)
  let e4' : ((Fin m → ℝ) × ℝ) ≃ᵐ (E m × ℝ) :=
    e4.prodCongr (MeasurableEquiv.refl ℝ)
  e1.trans e2 |>.trans e3 |>.trans e4'

lemma eSplit_apply (p : E (m + 1)) :
    eSplit p = (GraphAreaFormula.proj p, p (Fin.last m)) := by
  have h1 : (eSplit p).1 = GraphAreaFormula.proj p := by
    ext j
    have h_eq1 : (eSplit p).1 j = p (Fin.castSucc j) := by
      simp [eSplit, MeasurableEquiv.toLp, MeasurableEquiv.piFinSuccAbove,
        MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr]
      <;> rfl
    have h_eq2 : (GraphAreaFormula.proj p) j = p (Fin.castSucc j) :=
      GraphAreaFormula.proj_apply p j
    rw [h_eq1, h_eq2]
  have h2 : (eSplit p).2 = p (Fin.last m) := by
    simp [eSplit, MeasurableEquiv.toLp, MeasurableEquiv.piFinSuccAbove,
      MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr]
    <;> rfl
  exact Prod.ext h1 h2

lemma eSplit_measurePreserving : MeasurePreserving (eSplit : E (m + 1) ≃ᵐ E m × ℝ) volume volume := by
  let e1 : E (m + 1) ≃ᵐ (Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm
  let e2 : (Fin (m + 1) → ℝ) ≃ᵐ (ℝ × (Fin m → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last m)
  let e3 : (ℝ × (Fin m → ℝ)) ≃ᵐ ((Fin m → ℝ) × ℝ) :=
    MeasurableEquiv.prodComm
  let e4 : (Fin m → ℝ) ≃ᵐ E m :=
    MeasurableEquiv.toLp 2 (Fin m → ℝ)
  let e4' : ((Fin m → ℝ) × ℝ) ≃ᵐ (E m × ℝ) :=
    e4.prodCongr (MeasurableEquiv.refl ℝ)
  have h1 : MeasurePreserving e1 volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (ι := Fin (m + 1))
  have h2 : MeasurePreserving e2 volume volume :=
    volume_preserving_piFinSuccAbove (fun _ => ℝ) (Fin.last m)
  have h3 : MeasurePreserving e3 volume volume := by
    have hv1 : (volume : Measure (ℝ × (Fin m → ℝ))) = volume.prod volume :=
      Measure.volume_eq_prod ℝ (Fin m → ℝ)
    have hv2 : (volume : Measure ((Fin m → ℝ) × ℝ)) = volume.prod volume :=
      Measure.volume_eq_prod (Fin m → ℝ) ℝ
    refine' ⟨e3.measurable_toFun, _⟩
    rw [hv1, hv2]
    exact Measure.measurePreserving_swap.map_eq
  have h4 : MeasurePreserving e4' volume volume := by
    have h41 : MeasurePreserving e4 volume volume :=
      PiLp.volume_preserving_toLp (ι := Fin m)
    have h42 : MeasurePreserving (MeasurableEquiv.refl ℝ) volume volume :=
      MeasurePreserving.id volume
    have hprod : MeasurePreserving e4' (volume.prod volume) (volume.prod volume) :=
      MeasurePreserving.prod h41 h42
    have hv1 : (volume : Measure ((Fin m → ℝ) × ℝ)) = volume.prod volume :=
      Measure.volume_eq_prod (Fin m → ℝ) ℝ
    have hv2 : (volume : Measure (E m × ℝ)) = volume.prod volume :=
      Measure.volume_eq_prod (E m) ℝ
    refine' ⟨e4'.measurable_toFun, _⟩
    rw [hv1, hv2]
    exact hprod.map_eq
  exact h4.comp (h3.comp (h2.comp h1))

-- ============================================================================
-- Measurability of distance strip
-- ============================================================================

lemma distanceStrip_measurable (g : E m → ℝ) (hg : Continuous g)
    (A : Set (E m)) (hA : MeasurableSet A) (t : ℝ) :
    MeasurableSet (distanceStrip g A t) := by
  have h1 : Measurable (fun p : E (m + 1) => GraphAreaFormula.proj p) := by
    have h_cont : Continuous (fun p : E (m + 1) => GraphAreaFormula.proj p) := by
      have h11 : Continuous (fun p : E (m + 1) => (fun i : Fin m => p (Fin.castSucc i))) := by
        fun_prop
      have h12 : Continuous ((EuclideanSpace.equiv (Fin m) ℝ).symm : (Fin m → ℝ) → E m) :=
        (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous
      exact h12.comp h11
    exact h_cont.measurable
  have h2 : Measurable (fun p : E (m + 1) => infDist p (graph g)) :=
    (Metric.continuous_infDist_pt (graph g)).measurable
  have h3 : Measurable (fun p : E (m + 1) => p (Fin.last m) - g (GraphAreaFormula.proj p)) := by fun_prop
  have hs1 : MeasurableSet {p : E (m + 1) | GraphAreaFormula.proj p ∈ A} :=
    hA.preimage h1
  have hs2 : MeasurableSet {p : E (m + 1) | 0 < infDist p (graph g)} :=
    measurableSet_Ioi.preimage h2
  have hs3 : MeasurableSet {p : E (m + 1) | infDist p (graph g) < t} :=
    measurableSet_Iio.preimage h2
  have h_last : Measurable (fun p : E (m + 1) => p (Fin.last m)) := by fun_prop
  have h_g : Measurable (fun p : E (m + 1) => g (GraphAreaFormula.proj p)) := by fun_prop
  have h4 : Measurable (fun p : E (m + 1) => p (Fin.last m) - g (GraphAreaFormula.proj p)) :=
    h_last.sub h_g
  have hs4 : MeasurableSet {p : E (m + 1) | p (Fin.last m) > g (GraphAreaFormula.proj p)} := by
    have h_eq : {p : E (m + 1) | p (Fin.last m) > g (GraphAreaFormula.proj p)} =
        {p : E (m + 1) | p (Fin.last m) - g (GraphAreaFormula.proj p) > 0} := by
      ext p; simp [sub_pos]
    rw [h_eq]
    exact measurableSet_Ioi.preimage h4
  exact hs1.inter (hs2.inter (hs3.inter hs4))

-- ============================================================================
-- 2D Cauchy-Schwarz lemma
-- ============================================================================

/-- `v + a u ≤ √(1+‖a‖²) · √(v²+‖u‖²)` via operator norm bound + algebra. -/
lemma cauchy_schwarz_2d (v : ℝ) (u : E m) (a : E m →L[ℝ] ℝ) :
    v + a u ≤ Real.sqrt (1 + ‖a‖ ^ 2) * Real.sqrt (v ^ 2 + ‖u‖ ^ 2) := by
  have h1 : a u ≤ ‖a u‖ := le_abs_self (a u)
  have h2 : ‖a u‖ ≤ ‖a‖ * ‖u‖ := a.le_opNorm u
  have h3 : a u ≤ ‖a‖ * ‖u‖ := by linarith
  have h4 : v + a u ≤ v + ‖a‖ * ‖u‖ := by linarith
  have h3 : (v + ‖a‖ * ‖u‖) ^ 2 ≤ (1 + ‖a‖ ^ 2) * (v ^ 2 + ‖u‖ ^ 2) := by
    nlinarith [sq_nonneg (‖u‖ - ‖a‖ * v)]
  have h4 : 0 ≤ Real.sqrt (1 + ‖a‖ ^ 2) * Real.sqrt (v ^ 2 + ‖u‖ ^ 2) := by positivity
  nlinarith [Real.sq_sqrt (show 0 ≤ 1 + ‖a‖ ^ 2 by positivity),
    Real.sq_sqrt (show 0 ≤ v ^ 2 + ‖u‖ ^ 2 by positivity)]

-- ============================================================================
-- Distance squared helper
-- ============================================================================

lemma dist_point_graphMap_sq (x : E m) (y : ℝ) (z : E m) (g : E m → ℝ)
    (p : E (m + 1)) (hp_proj : GraphAreaFormula.proj p = x) (hp_last : p (Fin.last m) = y) :
    ‖p - graphMap g z‖ ^ 2 = ‖x - z‖ ^ 2 + (y - g z) ^ 2 := by
  have h_main : ∀ (q : E (m + 1)), ‖q‖ ^ 2 = ‖GraphAreaFormula.proj q‖ ^ 2 + (q (Fin.last m)) ^ 2 := by
    intro q
    rw [EuclideanSpace.real_norm_sq_eq q, Fin.sum_univ_castSucc]
    have h1 : ∑ j : Fin m, (q (Fin.castSucc j)) ^ 2 = ‖GraphAreaFormula.proj q‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq (GraphAreaFormula.proj q)]
      apply Finset.sum_congr rfl
      intro j _
      have h2 : (GraphAreaFormula.proj q) j = q (Fin.castSucc j) := GraphAreaFormula.proj_apply q j
      rw [h2]
    rw [h1] <;> ring
  have h := h_main (p - graphMap g z)
  have hproj : GraphAreaFormula.proj (p - graphMap g z) = x - z := by
    have h3 : ∀ (q1 q2 : E (m + 1)), GraphAreaFormula.proj (q1 - q2) = GraphAreaFormula.proj q1 - GraphAreaFormula.proj q2 := by
      intro q1 q2
      ext j
      simp [GraphAreaFormula.proj_apply] <;> rfl
    rw [h3 p (graphMap g z)]
    have h4 : GraphAreaFormula.proj (graphMap g z) = z := GraphAreaFormula.graphMap_proj g z
    rw [hp_proj, h4]
  have hlast : (p - graphMap g z) (Fin.last m) = y - g z := by
    have h5 : (graphMap g z) (Fin.last m) = g z := GraphAreaFormula.graphMap_apply_last g z
    simp [hp_last, h5] <;> ring
  rw [h, hproj, hlast]

-- ============================================================================
-- Existence lemma for points close to infDist
-- ============================================================================

lemma exists_dist_lt_of_infDist_lt {α : Type _} [MetricSpace α] {S : Set α} {x : α} {d : ℝ}
    (h : infDist x S < d) (hne : S.Nonempty) :
    ∃ y ∈ S, dist x y < d := by
  by_contra h2
  push Not at h2
  have h3 : ∀ z ∈ S, d ≤ dist x z := h2
  have h4 : d ≤ infDist x S := (le_infDist hne).mpr h3
  linarith

-- ============================================================================
-- Fiber bound lemma
-- ============================================================================

/-- For a point `p` above the graph with `infDist p (graph g) < t`,
the vertical excess `y - g(x)` is bounded by `t · (√(1+‖a‖²) + η)`. -/
lemma fiber_bound (g : E m → ℝ) (x : E m) (a : E m →L[ℝ] ℝ)
    (y : ℝ) (r η t : ℝ) (hr : 0 < r) (hη : 0 ≤ η) (ht : 0 < t) (htr : t < r)
    (h_approx : ∀ z ∈ closedBall x r, |g z - (g x + a (z - x))| ≤ η * ‖z - x‖)
    (p : E (m + 1)) (hp_proj : GraphAreaFormula.proj p = x) (hp_last : p (Fin.last m) = y)
    (hy_above : y > g x)
    (h_infDist_lt : infDist p (GraphAreaFormula.graph g) < t) :
    y - g x ≤ t * (Real.sqrt (1 + ‖a‖ ^ 2) + η) := by
  have h_graph_nonempty : (GraphAreaFormula.graph g).Nonempty := by
    refine ⟨graphMap g 0, ?_⟩
    have h : (graphMap g 0) (Fin.last m) = g (GraphAreaFormula.proj (graphMap g 0)) := by
      rw [GraphAreaFormula.graphMap_apply_last g 0, GraphAreaFormula.graphMap_proj g 0]
    simpa [GraphAreaFormula.graph, Set.mem_setOf_eq] using h
  have h_exists : ∃ (q : E (m + 1)), q ∈ GraphAreaFormula.graph g ∧ dist p q < t :=
    exists_dist_lt_of_infDist_lt h_infDist_lt h_graph_nonempty
  rcases h_exists with ⟨q, hq_graph, hq_dist⟩
  let z : E m := GraphAreaFormula.proj q
  have hq_eq : q = graphMap g z := by
    ext i
    by_cases h : i.val < m
    · let j : Fin m := ⟨i.val, h⟩
      have hi : i = Fin.castSucc j := by apply Fin.ext <;> simp [j]
      rw [hi]
      have h1 : q (Fin.castSucc j) = (GraphAreaFormula.proj q) j := by
        rw [GraphAreaFormula.proj_apply q j]
      rw [h1]
      have h2 : (GraphAreaFormula.proj q) j = z j := by rfl
      rw [h2, GraphAreaFormula.graphMap_apply_castSucc g z j]
    · have hi : i = Fin.last m := by
        apply Fin.ext; simp [h] <;> omega
      rw [hi]
      have h1 : q (Fin.last m) = g (GraphAreaFormula.proj q) := by
        simpa [GraphAreaFormula.graph, Set.mem_setOf_eq] using hq_graph
      rw [h1]
      have h2 : (GraphAreaFormula.proj q) = z := by rfl
      rw [h2, GraphAreaFormula.graphMap_apply_last g z]
  have h_dist_sq : ‖x - z‖ ^ 2 + (y - g z) ^ 2 < t ^ 2 := by
    have h2 : ‖p - q‖ ^ 2 = ‖x - z‖ ^ 2 + (y - g z) ^ 2 := by
      simpa [hq_eq] using dist_point_graphMap_sq x y z g p hp_proj hp_last
    have h3 : ‖p - q‖ < t := by
      have h4 : dist p q = ‖p - q‖ := by rw [dist_eq_norm]
      rw [← h4]
      exact hq_dist
    have h5 : 0 ≤ ‖p - q‖ := by positivity
    have h6 : ‖p - q‖ ^ 2 < t ^ 2 := by
      have h7 : 0 < t := ht
      gcongr
      <;> linarith
    rw [h2] at h6
    exact h6
  have h_uz : ‖x - z‖ < t := by
    have h_nonneg : 0 ≤ ‖x - z‖ := by positivity
    have h : ‖x - z‖ ^ 2 < t ^ 2 := by nlinarith [sq_nonneg (y - g z)]
    nlinarith
  have h_z_closed : z ∈ closedBall x r := by
    simp only [mem_closedBall, dist_eq_norm]
    have h6 : ‖z - x‖ ≤ t := by
      have h7 : ‖z - x‖ = ‖x - z‖ := by rw [norm_sub_rev]
      rw [h7] <;> linarith
    linarith
  set u : E m := z - x with hu_def
  set v : ℝ := y - g z with hv_def
  have h_norm_sq : ‖u‖ ^ 2 + v ^ 2 < t ^ 2 := by
    have h9 : ‖u‖ = ‖x - z‖ := by
      simp [hu_def, norm_sub_rev]
    rw [h9]
    exact h_dist_sq
  have h_approx_z : |g z - (g x + a u)| ≤ η * ‖u‖ := by
    simpa [hu_def] using h_approx z h_z_closed
  let e : ℝ := g z - g x - a u
  have he_abs : |e| ≤ η * ‖u‖ := by
    have h_eq : g z - (g x + a u) = g z - g x - a u := by ring
    rw [h_eq] at h_approx_z
    simpa [e] using h_approx_z
  have h_y_diff : y - g x = v + a u + e := by
    simp [e, hv_def, hu_def] <;> ring
  have h_cs : v + a u ≤ Real.sqrt (1 + ‖a‖ ^ 2) * Real.sqrt (v ^ 2 + ‖u‖ ^ 2) :=
    cauchy_schwarz_2d v u a
  have h_sqrt_lt : Real.sqrt (v ^ 2 + ‖u‖ ^ 2) < t := by
    have h10 : v ^ 2 + ‖u‖ ^ 2 < t ^ 2 := by linarith [h_norm_sq]
    have h11 : 0 ≤ v ^ 2 + ‖u‖ ^ 2 := by positivity
    rw [Real.sqrt_lt] <;> nlinarith
  have h12 : v + a u < Real.sqrt (1 + ‖a‖ ^ 2) * t := by
    calc v + a u
      ≤ Real.sqrt (1 + ‖a‖ ^ 2) * Real.sqrt (v ^ 2 + ‖u‖ ^ 2) := h_cs
    _ < Real.sqrt (1 + ‖a‖ ^ 2) * t := by
      gcongr <;> linarith [Real.sqrt_nonneg (1 + ‖a‖ ^ 2)]
  have h13 : e ≤ η * ‖u‖ := by
    have h14 : e ≤ |e| := le_abs_self e
    linarith [he_abs]
  have h14 : η * ‖u‖ ≤ η * t := by
    have h15 : 0 ≤ η := hη
    have h16 : ‖u‖ < t := by
      have h17 : ‖u‖ = ‖x - z‖ := by simp [hu_def, norm_sub_rev]
      rw [h17] <;> exact h_uz
    gcongr <;> linarith
  linarith [h_y_diff, h12, h13, h14]

-- ============================================================================
-- Uniform C¹ approximation
-- ============================================================================

/-- For C¹ `g` and bounded `A`, there exists `r > 0` such that for all
`x ∈ closure A` and `z ∈ closedBall x r`, the affine approximation error
is `≤ η · ‖z - x‖`. -/
lemma uniform_C1_approx (g : E m → ℝ) (hg : ContDiff ℝ 1 g)
    (A : Set (E m)) (hA : Bornology.IsBounded A)
    (η : ℝ) (hη : 0 < η) :
    ∃ (r : ℝ), 0 < r ∧ ∀ (x : E m), x ∈ closure A →
      ∀ (z : E m), z ∈ closedBall x r →
        |g z - g x - fderiv ℝ g x (z - x)| ≤ η * ‖z - x‖ := by
  have hK_bdd : Bornology.IsBounded (closure A) := hA.closure
  have h1 : ∃ (R : ℝ), 0 < R ∧ closure A ⊆ closedBall (0 : E m) R := by
    by_cases h_nonempty : (closure A).Nonempty
    · rcases h_nonempty with ⟨x0, hx0⟩
      have h_bdd2 : ∃ (C : ℝ), ∀ x ∈ closure A, dist x x0 ≤ C := by
        rcases Metric.isBounded_iff.mp hK_bdd with ⟨C, hC⟩
        refine ⟨C, fun x hx => hC hx hx0⟩
      rcases h_bdd2 with ⟨C, hC⟩
      have hC_nonneg : 0 ≤ C := by
        have h5 : dist x0 x0 ≤ C := hC x0 hx0
        simpa using h5
      refine ⟨C + ‖x0‖ + 1, ?_, fun y hy => ?_⟩
      · positivity
      · have h2 : dist y x0 ≤ C := hC y hy
        have h4 : ‖y - x0‖ ≤ C := by simpa [dist_eq_norm] using h2
        have h3 : ‖y‖ ≤ ‖y - x0‖ + ‖x0‖ := by
          have h4 : ‖y‖ = ‖(y - x0) + x0‖ := by rw [sub_add_cancel]
          rw [h4]
          exact norm_add_le _ _
        have h5 : ‖y‖ ≤ C + ‖x0‖ + 1 := by linarith
        simpa [mem_closedBall, dist_eq_norm] using h5
    · refine ⟨1, by norm_num, fun y hy => ?_⟩
      have h_empty : (closure A) = ∅ := by
        simpa [Set.not_nonempty_iff_eq_empty] using h_nonempty
      rw [h_empty] at hy
      simp at hy
  rcases h1 with ⟨R, hR_pos, hR_subset⟩
  let K' := closedBall (0 : E m) (R + 1)
  have hK'_compact : IsCompact K' := isCompact_closedBall 0 (R + 1)
  have h_cont : Continuous (fun z : E m => fderiv ℝ g z) :=
    hg.continuous_fderiv (by norm_num)
  have h_contOn : ContinuousOn (fun z : E m => fderiv ℝ g z) K' := h_cont.continuousOn
  have h_uc : UniformContinuousOn (fun z : E m => fderiv ℝ g z) K' :=
    hK'_compact.uniformContinuousOn_of_continuous h_contOn
  have h2 : ∃ (r : ℝ), 0 < r ∧ r < 1 ∧
      ∀ (y z : E m), y ∈ K' → z ∈ K' → dist y z < r → ‖fderiv ℝ g y - fderiv ℝ g z‖ < η := by
    have h3 := Metric.uniformContinuousOn_iff.mp h_uc η hη
    rcases h3 with ⟨r, hr_pos, h4⟩
    refine ⟨min r (1 / 2), by positivity, ?_, ?_⟩
    · have h5 : min r (1 / 2) ≤ 1 / 2 := min_le_right r (1 / 2)
      linarith
    · intro y z hy hz hdist
      have h6 : dist y z < r := by
        have h7 : dist y z < min r (1 / 2) := hdist
        have h8 : min r (1 / 2) ≤ r := min_le_left r (1 / 2)
        linarith
      have h16 : dist (fderiv ℝ g y) (fderiv ℝ g z) < η := h4 (x := y) (y := z) hy hz h6
      simpa [dist_eq_norm] using h16
  rcases h2 with ⟨r, hr_pos, hr_lt_one, h_deriv_bound⟩
  let r' := r / 2
  have hr'_pos : 0 < r' := by positivity
  have h_in_K' : ∀ (x : E m), x ∈ closure A → ∀ (y : E m), y ∈ closedBall x r' → y ∈ K' := by
    intro x hx y hy
    have hxK' : x ∈ K' := by
      have h6 : x ∈ closedBall (0 : E m) R := hR_subset hx
      simp only [K', mem_closedBall] at * <;> linarith
    have h7 : ‖y - x‖ ≤ r' := mem_closedBall.mp hy
    have h8 : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
      have h9 : ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
      rw [h9]
      exact norm_add_le _ _
    have h8' : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by linarith [h8]
    have h9 : ‖x‖ ≤ R := by
      have h10 : x ∈ closedBall (0 : E m) R := hR_subset hx
      simpa [mem_closedBall] using h10
    simp only [K', mem_closedBall]
    have h10 : ‖y‖ ≤ R + 1 := by
      calc ‖y‖ ≤ ‖y - x‖ + ‖x‖ := h8'
           _ ≤ r' + R := by gcongr <;> exact h9
           _ ≤ R + 1 := by
             have h11 : r' < 1 := by
               dsimp only [r']
               linarith [hr_lt_one]
             linarith
    simpa [dist_eq_norm] using h10
  have h_diff : Differentiable ℝ g := hg.differentiable (by norm_num)
  refine ⟨r', hr'_pos, fun x hx z hz => ?_⟩
  have h_bound : ∀ (y : E m), y ∈ closedBall x r' → ‖fderiv ℝ g y - fderiv ℝ g x‖ ≤ η := by
    intro y hy
    have hyK' : y ∈ K' := h_in_K' x hx y hy
    have hxK' : x ∈ K' := h_in_K' x hx x (mem_closedBall_self hr'_pos.le)
    have h10 : dist y x < r := by
      have h11 : ‖y - x‖ ≤ r' := mem_closedBall.mp hy
      have h12 : dist y x = ‖y - x‖ := by rw [dist_eq_norm]
      rw [h12]
      have h13 : ‖y - x‖ ≤ r / 2 := by simpa [r'] using h11
      linarith
    have h14 : ‖fderiv ℝ g y - fderiv ℝ g x‖ < η := h_deriv_bound y x hyK' hxK' h10
    exact h14.le
  have h_main : ‖g z - g x - fderiv ℝ g x (z - x)‖ ≤ η * ‖z - x‖ := by
    apply Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (s := closedBall x r') (f' := fun z => fderiv ℝ g z) (φ := fderiv ℝ g x)
    · intro y _
      exact (h_diff.differentiableAt).hasFDerivAt.hasFDerivWithinAt
    · exact h_bound
    · exact convex_closedBall x r'
    · exact mem_closedBall_self hr'_pos.le
    · exact hz
  have h_abs : ‖g z - g x - fderiv ℝ g x (z - x)‖ =
      |g z - g x - fderiv ℝ g x (z - x)| := by
    simp [Real.norm_eq_abs]
  rw [h_abs] at h_main
  exact h_main

-- ============================================================================
-- Main theorem: C¹ graph distance strip bound
-- ============================================================================

/-- **C¹ graph distance strip bound.**

For a C¹ function `g` over a bounded measurable `A`, and any `ε > 0`,
there exists `δ > 0` such that for all `0 < t < δ`:
`volume(distanceStrip g A t) ≤ (H^m(graph g ∩ cylinder A) + ε) * t`. -/
theorem C1_graph_distanceStrip_bound
    (g : E m → ℝ) (hg : ContDiff ℝ 1 g)
    (A : Set (E m)) (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ (δ : ℝ), 0 < δ ∧ ∀ (t : ℝ), 0 < t → t < δ →
      volume (distanceStrip g A t) ≤
        (μHE[m] (graph g ∩ cylinder A) + ε) * ENNReal.ofReal t := by
  -- Step 1: volume A < ⊤
  have h_vol_lt_top : volume A < ⊤ := by
    have h1 : ∃ (R : ℝ), A ⊆ closedBall (0 : E m) R := by
      rcases hA_bdd.subset_ball (0 : E m) with ⟨R, hR⟩
      refine ⟨R, fun y hy => ?_⟩
      have h2 : y ∈ ball (0 : E m) R := hR hy
      have h3 : dist y 0 < R := by simpa [ball] using h2
      simpa [mem_closedBall] using h3.le
    rcases h1 with ⟨R, hR⟩
    have h2 : volume A ≤ volume (closedBall (0 : E m) R) := measure_mono hR
    have h3 : volume (closedBall (0 : E m) R) < ⊤ :=
      MeasureTheory.measure_closedBall_lt_top
    exact lt_of_le_of_lt h2 h3
  let v : ℝ := (volume A).toReal
  have hv : volume A = ENNReal.ofReal v := by
    rw [ENNReal.ofReal_toReal h_vol_lt_top.ne]
  have hv_nonneg : 0 ≤ v := by positivity

  -- Step 2: choose e > 0 with ENNReal.ofReal e ≤ ε
  have h_exists_e : ∃ (e : ℝ), 0 < e ∧ ENNReal.ofReal e ≤ ε := by
    by_cases hε_top : ε = ⊤
    · refine ⟨1, by norm_num, ?_⟩
      rw [hε_top] <;> simp
    · have hε_lt_top : ε < ⊤ := lt_top_iff_ne_top.mpr hε_top
      have hε' : ∃ (ε' : ℝ), 0 < ε' ∧ ε = ENNReal.ofReal ε' := by
        refine ⟨ε.toReal, ?_, ?_⟩
        · have hpos : 0 < ε := hε
          have hlt : ε < ⊤ := hε_lt_top
          exact ENNReal.toReal_pos_iff.mpr ⟨hpos, hlt⟩
        · exact (ENNReal.ofReal_toReal hε_lt_top.ne).symm
      rcases hε' with ⟨ε', hε'_pos, rfl⟩
      refine ⟨ε' / 2, by linarith, ?_⟩
      have h : ENNReal.ofReal (ε' / 2) ≤ ENNReal.ofReal ε' := by
        gcongr <;> linarith
      exact h
  rcases h_exists_e with ⟨e, he_pos, he_le⟩

  -- Step 3: choose η > 0 such that ENNReal.ofReal η * volume A ≤ ε
  let η : ℝ := e / (v + 1)
  have hη_pos : 0 < η := by positivity
  have hη_vol : ENNReal.ofReal η * volume A ≤ ε := by
    have h1 : η * v ≤ e := by
      dsimp only [η]
      have h2 : 0 ≤ v := hv_nonneg
      have h3 : 0 < v + 1 := by linarith
      have h4 : v / (v + 1) ≤ 1 := by
        rw [div_le_one h3] <;> linarith
      have h5 : e / (v + 1) * v = e * (v / (v + 1)) := by ring
      rw [h5]
      have h6 : e * (v / (v + 1)) ≤ e * 1 := by
        gcongr
        <;> linarith
      linarith
    rw [hv]
    have h4 : ENNReal.ofReal η * ENNReal.ofReal v = ENNReal.ofReal (η * v) := by
      rw [← ENNReal.ofReal_mul] <;> linarith
    rw [h4]
    have h5 : ENNReal.ofReal (η * v) ≤ ENNReal.ofReal e := by
      gcongr <;> linarith
    exact h5.trans he_le

  -- Step 4: get uniform approximation radius r
  rcases uniform_C1_approx g hg A hA_bdd η hη_pos with ⟨r, hr_pos, h_approx⟩
  let δ := r / 2
  have hδ_pos : 0 < δ := by positivity

  -- Step 5: prove bound for all t ∈ (0, δ)
  refine ⟨δ, hδ_pos, fun t ht_pos ht_lt => ?_⟩
  have hδ_def : δ = r / 2 := by rfl
  have htr : t < r := by
    have h : t < δ := ht_lt
    rw [hδ_def] at h
    linarith
  set S : Set (E (m + 1)) := distanceStrip g A t with hS_def
  have hS_meas : MeasurableSet S :=
    distanceStrip_measurable g hg.continuous A hA t
  set S' : Set (E m × ℝ) := eSplit '' S with hS'_def
  have hS'_meas : MeasurableSet S' := eSplit.measurableSet_image.mpr hS_meas

  -- volume S = volume S' (eSplit is a measure-preserving equivalence)
  have h_vol_eq : volume S = volume S' := by
    have h_preimage : eSplit.symm ⁻¹' S = S' := by
      ext y
      simp only [S', Set.mem_preimage, Set.mem_image]
      constructor
      · intro hy
        refine ⟨eSplit.symm y, hy, ?_⟩
        exact eSplit.right_inv y
      · rintro ⟨x, hx, rfl⟩
        have h : eSplit.symm (eSplit x) = x := eSplit.left_inv x
        rw [h]
        exact hx
    have hS_null : NullMeasurableSet S volume := hS_meas.nullMeasurableSet
    have h : volume (eSplit.symm ⁻¹' S) = volume S :=
      eSplit_measurePreserving.symm.measure_preimage hS_null
    rw [h_preimage] at h
    exact h.symm

  -- Fubini: volume S' = ∫⁻ x, volume {y | (x, y) ∈ S'}
  have h_fub : volume S' = ∫⁻ (x : E m), volume {y : ℝ | (x, y) ∈ S'} := by
    rw [Measure.volume_eq_prod (E m) ℝ]
    exact Measure.prod_apply hS'_meas

  -- Step 6: pointwise fiber bound
  have hS_unfold : ∀ (p : E (m + 1)), p ∈ S →
      GraphAreaFormula.proj p ∈ A ∧
      0 < infDist p (GraphAreaFormula.graph g) ∧
      infDist p (GraphAreaFormula.graph g) < t ∧
      p (Fin.last m) > g (GraphAreaFormula.proj p) := by
    intro p hp
    simpa [S, distanceStrip] using hp

  have h_fiber : ∀ (x : E m), volume {y : ℝ | (x, y) ∈ S'} ≤
      Set.indicator A (fun x : E m =>
        ENNReal.ofReal (t * (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2) + η))) x := by
    intro x
    by_cases hxA : x ∈ A
    · -- x ∈ A: apply fiber bound
      have h_ind : Set.indicator A (fun x : E m =>
          ENNReal.ofReal (t * (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2) + η))) x =
          ENNReal.ofReal (t * (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2) + η)) := by
        rw [Set.indicator_of_mem hxA]
      rw [h_ind]
      let a : E m →L[ℝ] ℝ := fderiv ℝ g x
      have h_x_closure : x ∈ closure A := subset_closure hxA
      have h_approx' : ∀ z ∈ closedBall x r,
          |g z - (g x + a (z - x))| ≤ η * ‖z - x‖ := by
        intro z hz
        have h_orig := h_approx x h_x_closure z hz
        have h_eq : g z - g x - a (z - x) = g z - (g x + a (z - x)) := by ring
        rw [h_eq] at h_orig
        exact h_orig
      have h_bound1 : ∀ (y : ℝ), (x, y) ∈ S' →
          y - g x ≤ t * (Real.sqrt (1 + ‖a‖ ^ 2) + η) := by
        intro y hy
        let p : E (m + 1) := eSplit.symm (x, y)
        have hpe : eSplit p = (x, y) := eSplit.right_inv (x, y)
        have hp_in_S : p ∈ S := by
          have h5 : eSplit p ∈ S' := by rw [hpe] <;> exact hy
          rw [hS'_def] at h5
          rcases h5 with ⟨q, hq, h_eq⟩
          have hq_eq : q = p := eSplit.injective h_eq
          rw [hq_eq] at hq
          exact hq
        have hS_p := hS_unfold p hp_in_S
        have hp_proj : GraphAreaFormula.proj p = x := by
          have h6 : (eSplit p).1 = x := by rw [hpe] <;> rfl
          have h7 : (eSplit p).1 = GraphAreaFormula.proj p := by rw [eSplit_apply]
          exact h7.symm.trans h6
        have hp_last : p (Fin.last m) = y := by
          have h6 : (eSplit p).2 = y := by rw [hpe] <;> rfl
          have h7 : (eSplit p).2 = p (Fin.last m) := by rw [eSplit_apply]
          exact h7.symm.trans h6
        have hS4 : p (Fin.last m) > g (GraphAreaFormula.proj p) := hS_p.2.2.2
        have hy_above : y > g x := by
          rw [hp_last, hp_proj] at hS4 <;> exact hS4
        exact fiber_bound g x a y r η t hr_pos (by linarith) ht_pos htr h_approx'
          p hp_proj hp_last hy_above hS_p.2.2.1
      have h_fiber_subset : {y : ℝ | (x, y) ∈ S'} ⊆
          Set.Ioc (g x) (g x + t * (Real.sqrt (1 + ‖a‖ ^ 2) + η)) := by
        intro y hy
        have h_above : g x < y := by
          let p : E (m + 1) := eSplit.symm (x, y)
          have hpe : eSplit p = (x, y) := eSplit.right_inv (x, y)
          have hp_in_S : p ∈ S := by
            have h5 : eSplit p ∈ S' := by rw [hpe] <;> exact hy
            rw [hS'_def] at h5
            rcases h5 with ⟨q, hq, h_eq⟩
            have hq_eq : q = p := eSplit.injective h_eq
            rw [hq_eq] at hq
            exact hq
          have hS_p := hS_unfold p hp_in_S
          have hp_proj : GraphAreaFormula.proj p = x := by
            have h6 : (eSplit p).1 = x := by rw [hpe] <;> rfl
            have h7 : (eSplit p).1 = GraphAreaFormula.proj p := by rw [eSplit_apply]
            exact h7.symm.trans h6
          have hp_last : p (Fin.last m) = y := by
            have h6 : (eSplit p).2 = y := by rw [hpe] <;> rfl
            have h7 : (eSplit p).2 = p (Fin.last m) := by rw [eSplit_apply]
            exact h7.symm.trans h6
          have h4 : p (Fin.last m) > g (GraphAreaFormula.proj p) := hS_p.2.2.2
          rw [hp_last, hp_proj] at h4 <;> exact h4
        have h_le : y ≤ g x + t * (Real.sqrt (1 + ‖a‖ ^ 2) + η) := by
          linarith [h_bound1 y hy]
        exact ⟨h_above, h_le⟩
      have h_vol_fiber : volume {y : ℝ | (x, y) ∈ S'} ≤
          ENNReal.ofReal (t * (Real.sqrt (1 + ‖a‖ ^ 2) + η)) := by
        calc volume {y : ℝ | (x, y) ∈ S'}
          ≤ volume (Set.Ioc (g x) (g x + t * (Real.sqrt (1 + ‖a‖ ^ 2) + η))) :=
            measure_mono h_fiber_subset
        _ = ENNReal.ofReal (t * (Real.sqrt (1 + ‖a‖ ^ 2) + η)) := by
          rw [Real.volume_Ioc]
          have h_nonneg : 0 ≤ t * (Real.sqrt (1 + ‖a‖ ^ 2) + η) := by positivity
          simp [h_nonneg, max_eq_right h_nonneg] <;> ring
      exact h_vol_fiber
    · -- x ∉ A: fiber is empty
      have h_ind : Set.indicator A (fun x : E m =>
          ENNReal.ofReal (t * (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2) + η))) x = 0 := by
        classical
        rw [Set.indicator_apply, if_neg hxA]
        <;> simp
      rw [h_ind]
      have h_empty : {y : ℝ | (x, y) ∈ S'} = ∅ := by
        ext y
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hy
        let p : E (m + 1) := eSplit.symm (x, y)
        have hpe : eSplit p = (x, y) := eSplit.right_inv (x, y)
        have hp_in_S : p ∈ S := by
          have h5 : eSplit p ∈ S' := by rw [hpe] <;> exact hy
          rw [hS'_def] at h5
          rcases h5 with ⟨q, hq, h_eq⟩
          have hq_eq : q = p := eSplit.injective h_eq
          rw [hq_eq] at hq
          exact hq
        have hS_p := hS_unfold p hp_in_S
        have h1 : GraphAreaFormula.proj p ∈ A := hS_p.1
        have hp_proj : GraphAreaFormula.proj p = x := by
          have h6 : (eSplit p).1 = x := by rw [hpe] <;> rfl
          have h7 : (eSplit p).1 = GraphAreaFormula.proj p := by rw [eSplit_apply]
          exact h7.symm.trans h6
        rw [hp_proj] at h1
        exact hxA h1
      rw [h_empty]
      <;> simp

  -- Step 7: integrate
  have h_main : ∫⁻ (x : E m), volume {y : ℝ | (x, y) ∈ S'} ≤
      ∫⁻ (x : E m), Set.indicator A (fun x : E m =>
        ENNReal.ofReal (t * (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2) + η))) x := by
    apply lintegral_mono
    exact h_fiber

  -- Simplify integral
  have h_int : ∫⁻ (x : E m), Set.indicator A (fun x : E m =>
      ENNReal.ofReal (t * (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2) + η))) x =
      ∫⁻ x in A, ENNReal.ofReal (t * (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2) + η)) := by
    rw [lintegral_indicator hA]
    <;> rfl

  -- Split into graph area + error
  let f : E m → ENNReal := fun x =>
    ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2))
  have h_split : ∀ (x : E m),
      ENNReal.ofReal (t * (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2) + η)) =
      ENNReal.ofReal t * (f x + ENNReal.ofReal η) := by
    intro x
    have h_pos1 : 0 ≤ t := by linarith
    have h_pos2 : 0 ≤ Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2) + η := by positivity
    have h_eq1 : t * (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2) + η) =
        t * Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2) + t * η := by ring
    rw [h_eq1]
    have h : ENNReal.ofReal (t * Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2) + t * η) =
        ENNReal.ofReal (t * Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2)) + ENNReal.ofReal (t * η) := by
      rw [ENNReal.ofReal_add] <;> positivity
    rw [h]
    have h2 : ENNReal.ofReal (t * Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2)) =
        ENNReal.ofReal t * f x := by
      rw [← ENNReal.ofReal_mul h_pos1] <;> rfl
    have h3 : ENNReal.ofReal (t * η) = ENNReal.ofReal t * ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_mul h_pos1] <;> rfl
    rw [h2, h3] <;> ring

  have h_congr : ∫⁻ x in A, ENNReal.ofReal (t * (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2) + η)) =
      ∫⁻ x in A, ENNReal.ofReal t * (f x + ENNReal.ofReal η) :=
    MeasureTheory.setLIntegral_congr_fun hA (fun x hx => h_split x)

  have h_meas_f : Measurable f := by fun_prop
  have h_meas_eta : Measurable (fun x : E m => ENNReal.ofReal η) := by fun_prop
  have h_meas_sum : Measurable (fun x : E m => f x + ENNReal.ofReal η) :=
    h_meas_f.add h_meas_eta

  have h1 : ∫⁻ x in A, ENNReal.ofReal t * (f x + ENNReal.ofReal η) =
      ENNReal.ofReal t * ∫⁻ x in A, (f x + ENNReal.ofReal η) :=
    MeasureTheory.lintegral_const_mul (ENNReal.ofReal t) (hf := h_meas_sum)

  have h2 : ∫⁻ x in A, (f x + ENNReal.ofReal η) =
      (∫⁻ x in A, f x) + (∫⁻ x in A, ENNReal.ofReal η) :=
    MeasureTheory.lintegral_add_left h_meas_f (fun x => ENNReal.ofReal η)

  have h_lintegral_mul : ∫⁻ x in A, ENNReal.ofReal t * (f x + ENNReal.ofReal η) =
      ENNReal.ofReal t * ((∫⁻ x in A, f x) + (∫⁻ x in A, ENNReal.ofReal η)) := by
    rw [h1, h2]

  have h_area : μHE[m] (graph g ∩ cylinder A) = ∫⁻ x in A, f x :=
    GraphAreaFormula.graph_area_smooth g hg hg A hA

  have h_error : ∫⁻ x in A, ENNReal.ofReal η = ENNReal.ofReal η * volume A := by
    have h : ∫⁻ x in A, ENNReal.ofReal η = ENNReal.ofReal η * (volume.restrict A) Set.univ :=
      MeasureTheory.lintegral_const (ENNReal.ofReal η)
    rw [h]
    have h2 : (volume.restrict A) Set.univ = volume A := by
      simp [Measure.restrict_apply]
    rw [h2]

  have h_final : ENNReal.ofReal t * (μHE[m] (graph g ∩ cylinder A) + ENNReal.ofReal η * volume A) ≤
      ENNReal.ofReal t * (μHE[m] (graph g ∩ cylinder A) + ε) := by
    have h_add : μHE[m] (graph g ∩ cylinder A) + ENNReal.ofReal η * volume A ≤
        μHE[m] (graph g ∩ cylinder A) + ε :=
      add_le_add_right hη_vol _
    gcongr

  calc volume S
    = volume S' := h_vol_eq
    _ = ∫⁻ (x : E m), volume {y : ℝ | (x, y) ∈ S'} := h_fub
    _ ≤ ∫⁻ (x : E m), Set.indicator A (fun x : E m =>
          ENNReal.ofReal (t * (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2) + η))) x := h_main
    _ = ∫⁻ x in A, ENNReal.ofReal (t * (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2) + η)) := h_int
    _ = ∫⁻ x in A, ENNReal.ofReal t * (f x + ENNReal.ofReal η) := h_congr
    _ = ENNReal.ofReal t * ((∫⁻ x in A, f x) + (∫⁻ x in A, ENNReal.ofReal η)) := h_lintegral_mul
    _ = ENNReal.ofReal t * (μHE[m] (graph g ∩ cylinder A) + ENNReal.ofReal η * volume A) := by
        rw [←h_area, h_error] <;> rfl
    _ ≤ ENNReal.ofReal t * (μHE[m] (graph g ∩ cylinder A) + ε) := h_final
    _ = (μHE[m] (graph g ∩ cylinder A) + ε) * ENNReal.ofReal t := by
      rw [mul_comm]

end Geometry.Isoperimetric
