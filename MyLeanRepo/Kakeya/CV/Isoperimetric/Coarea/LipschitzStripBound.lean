import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.GraphArea
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.GraphAreaSmooth
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.DistanceStripBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.LipschitzGraphAreaLower
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.LocalCoareaInequality
import Mathlib.Tactic

open MeasureTheory Metric Set ENNReal LinearMap Filter
open scoped MeasureTheory Pointwise Classical
open GraphAreaFormula



/-!
# Lipschitz Graph Strip Bound

Sharp one-sided strip bound for Lipschitz graphs:

`volume(upperStrip g t A) ≤ (1+ε) · t · H^m(graph(g) ∩ cylinder(A))`

for any `ε > 0` and sufficiently small `t > 0`.

Proof: Rademacher a.e. differentiability → measurable differentiability sets D_k
→ fiber bound on D_k, crude Lipschitz bound on A\\D_k → Fubini → lower area formula.

Also includes the crude bound `(1+L)·t·volume A` and the small-L variant.
-/

open MeasureTheory Metric Set ENNReal LinearMap Filter
open scoped MeasureTheory Pointwise Classical
open GraphAreaFormula


namespace Geometry.Isoperimetric

variable {m : ℕ} [Nonempty (Fin m)]

-- `E n` is inherited from `DistanceStripBound` import.

-- ============================================================================
-- Utility lemmas
-- ============================================================================

/-- `proj` is 1-Lipschitz. -/
lemma proj_one_lip : LipschitzWith (1 : NNReal) (proj : E (m + 1) → E m) := by
  have h : ∀ (p q : E (m + 1)), ‖GraphAreaFormula.proj p - GraphAreaFormula.proj q‖ ≤ ‖p - q‖ := by
    intro p q
    have h1 : ‖GraphAreaFormula.proj p - GraphAreaFormula.proj q‖ ^ 2 ≤ ‖p - q‖ ^ 2 := by
      have h2 : ‖GraphAreaFormula.proj p - GraphAreaFormula.proj q‖ ^ 2 = ∑ i : Fin m, ((p - q) (Fin.castSucc i)) ^ 2 := by
        simp [EuclideanSpace.real_norm_sq_eq, GraphAreaFormula.proj_apply] <;> rfl
      rw [h2]
      have h3 : ∑ i : Fin m, ((p - q) (Fin.castSucc i)) ^ 2 ≤
          ∑ i : Fin (m + 1), ((p - q) i) ^ 2 := by
        rw [Fin.sum_univ_castSucc]
        <;> simp [sq_nonneg] <;> ring_nf <;> nlinarith
      have h4 : ‖p - q‖ ^ 2 = ∑ i : Fin (m + 1), ((p - q) i) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
      rw [h4]
      exact h3
    nlinarith [norm_nonneg (GraphAreaFormula.proj p - GraphAreaFormula.proj q), norm_nonneg (p - q)]
  exact LipschitzWith.of_dist_le_mul fun p q => by
    simpa [dist_eq_norm] using h p q

/-- Each coordinate is bounded by the norm. -/
lemma coord_le_norm {n : ℕ} (p : E n) (i : Fin n) : |p i| ≤ ‖p‖ := by
  have h1 : (p i) ^ 2 ≤ ‖p‖ ^ 2 := by
    have h2 : ‖p‖ ^ 2 = ∑ j : Fin n, (p j) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    rw [h2]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)
  have h3 : |p i| ^ 2 ≤ ‖p‖ ^ 2 := by
    simpa [sq_abs] using h1
  nlinarith [abs_nonneg (p i), norm_nonneg p]

-- ============================================================================
-- Sharp strip bound
-- ============================================================================

section LipschitzStrip

variable (g : E m → ℝ) {L : NNReal} (hg : LipschitzWith L g)

/-- Upper distance strip over A (one-sided, above graph). Alias for `distanceStrip`. -/
def upperStrip (t : ℝ) (A : Set (E m)) : Set (E (m + 1)) :=
  distanceStrip g A t

include hg

/-- Crude fiber bound: for Lipschitz g, the vertical fiber of upperStrip at x
has length at most `t * (1 + L)`. -/
lemma crude_fiber_bound {A : Set (E m)} (x : E m) (t : ℝ) (ht : 0 < t) (hx : x ∈ A) :
    volume {y : ℝ | eSplit.symm (x, y) ∈ upperStrip g t A} ≤
    ENNReal.ofReal (t * (1 + (L : ℝ))) := by
  let S := {y : ℝ | eSplit.symm (x, y) ∈ upperStrip g t A}
  have h1 : ∀ y ∈ S, g x < y ∧ y < g x + t * (1 + (L : ℝ)) := by
    intro y hy
    let p : E (m + 1) := eSplit.symm (x, y)
    have hp : p ∈ upperStrip g t A := hy
    have h_proj : GraphAreaFormula.proj p = x := by
      have h : (eSplit p).1 = x := by simp [p]
      have h' : (eSplit p).1 = GraphAreaFormula.proj p := by rw [eSplit_apply p]
      exact h'.symm.trans h
    have h_last : p (Fin.last m) = y := by
      have h : (eSplit p).2 = y := by simp [p]
      have h' : (eSplit p).2 = p (Fin.last m) := by rw [eSplit_apply p]
      exact h'.symm.trans h
    have h_above : y > g x := by
      have h5 : p (Fin.last m) > g (GraphAreaFormula.proj p) := hp.2.2.2
      rw [h_last, h_proj] at h5; exact h5
    have h_inf : infDist p (GraphAreaFormula.graph g) < t := hp.2.2.1
    have h_graph_nonempty : (graph g).Nonempty := by
      refine ⟨graphMap g 0, ?_⟩
      have h1 : (graphMap g 0) (Fin.last m) = g (GraphAreaFormula.proj (graphMap g 0)) := by
        rw [graphMap_apply_last, graphMap_proj]
      have h2 : graphMap g 0 ∈ GraphAreaFormula.graph g := by
        change (graphMap g 0) (Fin.last m) = g (GraphAreaFormula.proj (graphMap g 0))
        exact h1
      exact h2
    have h_exists : ∃ (q : E (m + 1)), q ∈ GraphAreaFormula.graph g ∧ dist p q < t :=
      (Metric.infDist_lt_iff h_graph_nonempty).mp h_inf
    rcases h_exists with ⟨q, hq, hdist⟩
    let z : E m := GraphAreaFormula.proj q
    have hz : graphMap g z = q := by
      have h1 : q (Fin.last m) = g z := by
        have hq' : q ∈ GraphAreaFormula.graph g := hq
        change q (Fin.last m) = g (GraphAreaFormula.proj q) at hq'
        simpa [z] using hq'
      ext i
      by_cases h : i = Fin.last m
      · rw [h]; simp [h1, graphMap_apply_last] <;> rfl
      · have h3 : i.val < m := by
          have h4 : i.val < m + 1 := i.is_lt
          have h5 : i.val ≠ m := by
            intro h6
            have h7 : i = Fin.last m := by apply Fin.ext; simp [h6]
            exact h h7
          omega
        let j : Fin m := ⟨i.val, h3⟩
        have h_eq : i = Fin.castSucc j := by apply Fin.ext; simp [j]
        rw [h_eq]
        simp [z, graphMap_apply_castSucc, GraphAreaFormula.proj_apply] <;> rfl
    have h_norm1 : ‖x - z‖ < t := by
      have h8 : ‖GraphAreaFormula.proj p - GraphAreaFormula.proj q‖ ≤ ‖p - q‖ := by
        have h9 : dist (GraphAreaFormula.proj p) (GraphAreaFormula.proj q) ≤ (1 : NNReal) * dist p q :=
          (lipschitzWith_iff_dist_le_mul.mp proj_one_lip) p q
        simpa [dist_eq_norm, NNReal.coe_one] using h9
      have h9 : GraphAreaFormula.proj p = x := h_proj
      have h10 : GraphAreaFormula.proj q = z := by
        rw [←hz]; exact graphMap_proj g z
      rw [h9, h10] at h8
      have h11 : ‖p - q‖ = dist p q := by rw [dist_eq_norm]
      have h12 : ‖p - q‖ < t := by rwa [h11]
      exact h8.trans_lt h12
    have h_norm2 : |y - g z| < t := by
      have h8 : |(p - q) (Fin.last m)| ≤ ‖p - q‖ := coord_le_norm (p - q) (Fin.last m)
      have h9 : (p - q) (Fin.last m) = y - g z := by
        rw [←hz]
        simp [h_last, graphMap_apply_last] <;> ring
      rw [h9] at h8
      have h10 : ‖p - q‖ = dist p q := by rw [dist_eq_norm]
      have h11 : ‖p - q‖ < t := by rwa [h10]
      exact h8.trans_lt h11
    have h_lip : |g z - g x| ≤ (L : ℝ) * ‖z - x‖ := by
      have h : dist (g z) (g x) ≤ (L : ℝ) * dist z x :=
        (lipschitzWith_iff_dist_le_mul.mp hg) z x
      simpa [dist_eq_norm, Real.dist_eq] using h
    have h_znorm : ‖z - x‖ < t := by
      have h_eq : ‖z - x‖ = ‖x - z‖ := by rw [norm_sub_rev]
      rw [h_eq]; exact h_norm1
    have h_main : y - g x < t * (1 + (L : ℝ)) := by
      have hL_nonneg : 0 ≤ (L : ℝ) := by exact_mod_cast L.prop
      calc y - g x
        = (y - g z) + (g z - g x) := by ring
      _ ≤ |y - g z| + |g z - g x| := by exact add_le_add (le_abs_self _) (le_abs_self _)
      _ < t + (L : ℝ) * ‖z - x‖ := add_lt_add_of_lt_of_le h_norm2 h_lip
      _ ≤ t + (L : ℝ) * t := by
        have h : (L : ℝ) * ‖z - x‖ ≤ (L : ℝ) * t := by
          gcongr
          <;> exact h_znorm.le
        have h' : t + (L : ℝ) * ‖z - x‖ ≤ t + (L : ℝ) * t := by
          rw [add_comm t ((L : ℝ) * ‖z - x‖), add_comm t ((L : ℝ) * t)]
          exact add_le_add_left h t
        exact h'
      _ = t * (1 + (L : ℝ)) := by ring
    exact ⟨h_above, by linarith⟩
  have h_sub : S ⊆ Set.Ioc (g x) (g x + t * (1 + (L : ℝ))) := by
    intro y hy
    have h := h1 y hy
    exact ⟨h.1, h.2.le⟩
  calc volume S
    ≤ volume (Set.Ioc (g x) (g x + t * (1 + (L : ℝ)))) := measure_mono h_sub
  _ = ENNReal.ofReal (t * (1 + (L : ℝ))) := by
    rw [Real.volume_Ioc]
    have h_nonneg : 0 ≤ t * (1 + (L : ℝ)) := by positivity
    simp [h_nonneg, max_eq_right h_nonneg] <;> ring

/-- **Lipschitz graph one-sided strip bound.**

For Lipschitz `g` and bounded measurable `A`, for every `ε > 0` there
exists `t₀ > 0` such that for all `0 < t < t₀`:
`volume(upperStrip g t A) ≤ (1+ε) · t · H^m(graph(g) ∩ cylinder(A))`

Proof: Rademacher a.e. differentiability → measurable differentiability
sets D_k → fiber bound on D_k, crude bound on A\D_k → Fubini →
lower area formula. -/
theorem LipschitzGraph_stripBound
    (A : Set (E m)) (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (t₀ : ℝ), 0 < t₀ ∧ ∀ (t : ℝ), 0 < t → t < t₀ →
      volume (upperStrip g t A) ≤
        ENNReal.ofReal (1 + ε) * ENNReal.ofReal t *
        μHE[m] (graphMap g '' A) := by
  let H : ENNReal := μHE[m] (graphMap g '' A)

  -- Case volume A = 0: strip volume = 0 by Fubini
  by_cases hA0 : volume A = 0
  · refine ⟨1, by norm_num, fun t ht_pos _ => ?_⟩
    let S := upperStrip g t A
    have hg_cont : Continuous g := hg.continuous
    have hS_meas : MeasurableSet S := distanceStrip_measurable g hg_cont A hA t
    let S' := eSplit '' S
    have hS'_meas : MeasurableSet S' := eSplit.measurableSet_image.mpr hS_meas
    have h_vol_eq : volume S = volume S' := by
        have h1 : eSplit ⁻¹' S' = S := by ext x; simp [S']
        have h2 : volume (eSplit ⁻¹' S') = volume S' :=
          eSplit_measurePreserving.measure_preimage hS'_meas.nullMeasurableSet
        rw [h1] at h2; exact h2
    have h_fub : volume S' = ∫⁻ (x : E m), volume {y : ℝ | (x, y) ∈ S'} := by
      rw [Measure.volume_eq_prod (E m) ℝ]
      exact Measure.prod_apply hS'_meas
    have h_fiber_empty : ∀ (x : E m), x ∉ A → {y : ℝ | (x, y) ∈ S'} = ∅ := by
      intro x hx
      ext y; simp only [Set.mem_empty_iff_false, iff_false]
      intro hy
      let p : E (m + 1) := eSplit.symm (x, y)
      have hp : p ∈ S := by
        have h5 : eSplit p = (x, y) := eSplit.apply_symm_apply (x, y)
        have h6 : eSplit p ∈ S' := by rw [h5]; exact hy
        rcases h6 with ⟨q, hq, h_eq⟩
        have hq_eq : q = p := eSplit.injective h_eq
        rw [hq_eq] at hq; exact hq
      have h1 : GraphAreaFormula.proj p ∈ A := hp.1
      have hp_proj : GraphAreaFormula.proj p = x := by
        have h6 : (eSplit p).1 = x := by simp [p]
        have h7 : (eSplit p).1 = GraphAreaFormula.proj p := by
          have h8 := eSplit_apply p
          rw [h8] <;> simp
        exact h7.symm.trans h6
      rw [hp_proj] at h1; exact hx h1
    have h_main : ∫⁻ (x : E m), volume {y : ℝ | (x, y) ∈ S'} = 0 := by
      have h_ae : ∀ᵐ (x : E m) ∂volume, x ∉ A := by
        rw [ae_iff]; simpa using hA0
      have h : ∀ᵐ (x : E m) ∂volume, volume {y : ℝ | (x, y) ∈ S'} = 0 := by
        filter_upwards [h_ae] with x hx
        rw [h_fiber_empty x hx] <;> simp
      have h_eq : ∫⁻ (x : E m), volume {y : ℝ | (x, y) ∈ S'} = ∫⁻ (x : E m), (0 : ENNReal) :=
        lintegral_congr_ae h
      rw [h_eq]; simp
    rw [h_vol_eq, h_fub, h_main] <;> simp

  -- Case volume A > 0
  have hA_pos : 0 < volume A := by
    rw [pos_iff_ne_zero]; exact hA0
  have hA_lt_top : volume A < ⊤ := hA_bdd.measure_lt_top

  -- H < ⊤ since graphMap is Lipschitz and A is bounded
  have hH_lt_top : H < ⊤ := by
    let K : NNReal := ⟨Real.sqrt (1 + (L : ℝ)^2), by positivity⟩
    have h1 : LipschitzWith K (graphMap g) := graphMap_lipschitz_global hg
    have h1_A : LipschitzOnWith K (graphMap g) A := h1.lipschitzOnWith.mono (Set.subset_univ A)
    have h4 : μHE[m] (graphMap g '' A) ≤ (K : ENNReal) ^ (m : ℝ) * μHE[m] A :=
      lipschitzOnWith_euclideanHausdorffMeasure_image_le h1_A
    have h5 : μHE[m] A = volume A := by
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume m]
    have h6 : volume A < ⊤ := hA_bdd.measure_lt_top
    have hK_ne_top : (K : ENNReal) ≠ ⊤ := by simp
    have hK_pos : 0 < (K : ENNReal) := by
      have h_nonneg : 0 ≤ (L : ℝ) := NNReal.coe_nonneg L
      have h2 : 0 < 1 + (L : ℝ)^2 := by nlinarith
      have h3 : 0 < (K : ℝ) := by
        dsimp only [K]
        exact Real.sqrt_pos.mpr h2
      exact_mod_cast h3
    have h7 : (K : ENNReal) ^ (m : ℝ) < ⊤ := by
      have h_eq : (K : ENNReal) ^ (m : ℝ) = (K : ENNReal) ^ m := by simp
      rw [h_eq]
      have h_ne : (K : ENNReal) ^ m ≠ ⊤ := pow_ne_top hK_ne_top
      exact h_ne.lt_top
    exact h4.trans_lt (mul_lt_top h7 (by rw [h5] <;> exact h6))

  -- H > 0 since projection is 1-Lipschitz: volume A ≤ H
  have hH_pos : 0 < H := by
    have h_proj_lip : LipschitzWith (1 : NNReal) (GraphAreaFormula.proj : E (m + 1) → E m) := proj_one_lip
    have h_proj_A : LipschitzOnWith (1 : NNReal) GraphAreaFormula.proj (graphMap g '' A) :=
      h_proj_lip.lipschitzOnWith.mono (Set.subset_univ _)
    have h3 : μHE[m] (GraphAreaFormula.proj '' (graphMap g '' A)) ≤ (1 : ENNReal)^(m : ℝ) * H :=
      lipschitzOnWith_euclideanHausdorffMeasure_image_le h_proj_A
    have h4 : GraphAreaFormula.proj '' (graphMap g '' A) = A := by
      ext z; simp [graphMap_proj, Set.ext_iff] <;> tauto
    rw [h4] at h3
    have h5 : (1 : ENNReal)^(m : ℝ) = 1 := by simp
    rw [h5] at h3
    have h6 : μHE[m] A = volume A := by
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume m]
    rw [h6] at h3
    have h7 : 1 * H = H := by simp
    rw [h7] at h3
    exact lt_of_lt_of_le hA_pos h3

  let h : ℝ := H.toReal
  have hH_eq : H = ENNReal.ofReal h := by
    rw [ENNReal.ofReal_toReal hH_lt_top.ne]
  have h_pos : 0 < h := ENNReal.toReal_pos_iff.mpr ⟨hH_pos, hH_lt_top⟩
  let δ : ℝ := ε * h
  have hδ_pos : 0 < δ := mul_pos hε h_pos

  -- Get countable dense subset Q
  rcases TopologicalSpace.exists_countable_dense (E m) with ⟨Q, hQ_count, hQ_dense⟩

  -- Choose η > 0
  let vA : ℝ := (volume A).toReal
  have hvA_lt_top : volume A < ⊤ := hA_lt_top
  have h_vA_eq : volume A = ENNReal.ofReal vA := by
    rw [ENNReal.ofReal_toReal hvA_lt_top.ne]
  let η : ℝ := δ / (2 * (vA + 1))
  have hη_pos : 0 < η := by positivity
  have hη_vol : ENNReal.ofReal η * volume A ≤ ENNReal.ofReal (δ / 2) := by
    have h1 : η * vA ≤ δ / 2 := by
      dsimp only [η]
      have h2 : 0 ≤ vA := by exact ENNReal.toReal_nonneg
      have h3 : vA / (vA + 1) ≤ 1 := by
        have h4 : 0 < vA + 1 := by linarith
        rw [div_le_one h4] <;> linarith
      have h5 : δ / (2 * (vA + 1)) * vA = (δ / 2) * (vA / (vA + 1)) := by
        field_simp
        <;> ring
      rw [h5]
      have h6 : (δ / 2) * (vA / (vA + 1)) ≤ (δ / 2) * 1 := by gcongr <;> linarith
      linarith
    rw [h_vA_eq]
    have h4 : ENNReal.ofReal η * ENNReal.ofReal vA = ENNReal.ofReal (η * vA) := by
      rw [← ENNReal.ofReal_mul] <;> linarith
    rw [h4]
    gcongr <;> linarith

  -- Define differentiability sets D_k
  let D : ℕ → Set (E m) := fun k =>
    A ∩ ⋂ q ∈ (Q ∩ closedBall 0 (1 / (k + 1 : ℝ))),
      {x : E m | abs (g (x + q) - g x - (fderiv ℝ g x) q) ≤ η * ‖q‖}

  have hg_meas : Measurable g := hg.continuous.measurable
  have hfderiv_meas : Measurable (fderiv ℝ g) := by fun_prop

  -- D_k is measurable
  have hD_meas : ∀ k, MeasurableSet (D k) := by
    intro k
    let S_k : Set (E m) := Q ∩ closedBall 0 (1 / (k + 1 : ℝ))
    have h_sub : S_k ⊆ Q := by intro x hx; exact hx.1
    have h_count : S_k.Countable := hQ_count.mono h_sub
    have h_main : MeasurableSet (⋂ q ∈ S_k, {x : E m | abs (g (x + q) - g x - (fderiv ℝ g x) q) ≤ η * ‖q‖}) :=
      MeasurableSet.biInter h_count fun q _ => by
        have h1 : Measurable fun x : E m => g (x + q) :=
          hg_meas.comp (measurable_id.add measurable_const)
        have heval : Continuous (fun (f : E m →L[ℝ] ℝ) => f q) :=
          (ContinuousLinearMap.apply ℝ ℝ q).continuous
        have h2 : Measurable fun x : E m => (fderiv ℝ g x) q :=
          heval.measurable.comp hfderiv_meas
        have h3 : Measurable fun x : E m => g x := hg_meas
        have h4 : Measurable fun x : E m => g (x + q) - g x - (fderiv ℝ g x) q :=
          (h1.sub h3).sub h2
        have h_meas : Measurable fun x : E m => abs (g (x + q) - g x - (fderiv ℝ g x) q) :=
          continuous_abs.measurable.comp h4
        have h_const : Measurable (fun (_ : E m) => η * ‖q‖) := by fun_prop
        have h_pair : Measurable (fun x : E m => (abs (g (x + q) - g x - (fderiv ℝ g x) q), η * ‖q‖)) :=
          h_meas.prod h_const
        have h_le_closed : IsClosed {p : ℝ × ℝ | p.1 ≤ p.2} :=
          isClosed_le continuous_fst continuous_snd
        exact h_pair h_le_closed.measurableSet
    exact hA.inter h_main

  -- D_k is increasing
  have hD_mono : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → D k₁ ⊆ D k₂ := by
    intro k₁ k₂ hle
    have h_r : (1 / (k₂ + 1 : ℝ)) ≤ (1 / (k₁ + 1 : ℝ)) := by
      have h1 : (k₁ + 1 : ℝ) ≤ (k₂ + 1 : ℝ) := by exact_mod_cast (add_le_add hle (by norm_num))
      have h2 : 0 < (k₁ + 1 : ℝ) := by positivity
      exact one_div_le_one_div_of_le h2 h1
    intro x hx
    have hxA : x ∈ A := hx.1
    have h_ball : Q ∩ closedBall 0 (1 / (k₂ + 1 : ℝ)) ⊆ Q ∩ closedBall 0 (1 / (k₁ + 1 : ℝ)) := by
      intro q hq
      exact ⟨hq.1, closedBall_subset_closedBall h_r hq.2⟩
    have hx_prop : ∀ q ∈ (Q ∩ closedBall 0 (1 / (k₁ + 1 : ℝ))),
        abs (g (x + q) - g x - (fderiv ℝ g x) q) ≤ η * ‖q‖ := by
      have h : x ∈ ⋂ q ∈ (Q ∩ closedBall 0 (1 / (k₁ + 1 : ℝ))),
          {x : E m | abs (g (x + q) - g x - (fderiv ℝ g x) q) ≤ η * ‖q‖} := hx.2
      simpa [Set.mem_biInter] using h
    have h5 : x ∈ ⋂ q ∈ (Q ∩ closedBall 0 (1 / (k₂ + 1 : ℝ))),
        {x : E m | abs (g (x + q) - g x - (fderiv ℝ g x) q) ≤ η * ‖q‖} := by
      simpa [Set.mem_biInter] using fun q hq => hx_prop q (h_ball hq)
    exact ⟨hxA, h5⟩

  -- Differentiability points are covered by ∪ D_k
  have hg_diff : ∀ᵐ (x : E m) ∂volume, DifferentiableAt ℝ g x :=
    hg.ae_differentiableAt_of_real
  have h_cover : volume (A \ ⋃ k, D k) = 0 := by
    have h1 : ∀ x, DifferentiableAt ℝ g x → x ∈ A → x ∈ ⋃ k, D k := by
      intro x hdiff hxA
      have h2 : ∃ (r : ℝ), 0 < r ∧ ∀ (w : E m), ‖w‖ ≤ r →
          abs (g (x + w) - g x - (fderiv ℝ g x) w) ≤ η * ‖w‖ := by
        have h3 : HasFDerivAt g (fderiv ℝ g x) x := hdiff.hasFDerivAt
        have h4 : (fun y : E m => g y - g x - (fderiv ℝ g x) (y - x)) =o[nhds x] (fun y : E m => y - x) :=
          hasFDerivAt_iff_isLittleO.mp h3
        have h5 : ∀ᶠ (y : E m) in nhds x, ‖g y - g x - (fderiv ℝ g x) (y - x)‖ ≤ η * ‖y - x‖ :=
          h4.def hη_pos
        rcases Metric.mem_nhds_iff.mp h5 with ⟨r, hr_pos, h6⟩
        let r' := r / 2
        have hr'_pos : 0 < r' := by positivity
        have hr'_lt_r : r' < r := by
          dsimp only [r']
          have h : r / 2 < r := by linarith [hr_pos]
          exact h
        refine ⟨r', hr'_pos, fun w hw => ?_⟩
        have h7 : x + w ∈ Metric.ball x r := by
          have h_dist : dist (x + w) x < r := by
            simpa [dist_eq_norm] using calc ‖w‖ ≤ r' := hw
              _ < r := hr'_lt_r
          exact h_dist
        have h8 := h6 h7
        simpa [Real.norm_eq_abs] using h8
      rcases h2 with ⟨r, hr_pos, h2⟩
      have h3 : ∃ (k : ℕ), (1 / (k + 1 : ℝ)) ≤ r := by
        refine ⟨Nat.ceil (1 / r - 1), ?_⟩
        have h4 : (1 / r - 1 : ℝ) ≤ Nat.ceil (1 / r - 1) := Nat.le_ceil _
        have h5 : (1 / (Nat.ceil (1 / r - 1) + 1 : ℝ)) ≤ r := by
          have h6 : 0 < r := hr_pos
          have h7 : (Nat.ceil (1 / r - 1) + 1 : ℝ) ≥ 1 / r := by linarith [Nat.le_ceil (1 / r - 1)]
          have h8 : 0 < (Nat.ceil (1 / r - 1) + 1 : ℝ) := by positivity
          calc
            1 / (Nat.ceil (1 / r - 1) + 1 : ℝ) ≤ 1 / (1 / r) := by gcongr
            _ = r := by
              field_simp [h6.ne'] <;> ring
        exact h5
      rcases h3 with ⟨k, hk⟩
      have h4 : x ∈ D k := by
        have h_prop : ∀ q ∈ (Q ∩ closedBall 0 (1 / (k + 1 : ℝ))),
            abs (g (x + q) - g x - (fderiv ℝ g x) q) ≤ η * ‖q‖ := by
          intro q hq
          have h51 : q ∈ closedBall 0 (1 / (k + 1 : ℝ)) := hq.2
          have h5 : ‖q‖ ≤ 1 / (k + 1 : ℝ) := by
            simpa [closedBall, dist_eq_norm] using h51
          have h6 : ‖q‖ ≤ r := by linarith
          exact h2 q h6
        have h5 : x ∈ ⋂ q ∈ (Q ∩ closedBall 0 (1 / (k + 1 : ℝ))),
            {x : E m | abs (g (x + q) - g x - (fderiv ℝ g x) q) ≤ η * ‖q‖} := by
          have h : ∀ (q : E m), q ∈ (Q ∩ closedBall 0 (1 / (k + 1 : ℝ))) →
              x ∈ {x : E m | abs (g (x + q) - g x - (fderiv ℝ g x) q) ≤ η * ‖q‖} := by
            intro q hq
            exact h_prop q hq
          exact Set.mem_biInter h
        exact ⟨hxA, h5⟩
      exact Set.mem_iUnion.mpr ⟨k, h4⟩
    have h2 : A ⊆ (⋃ k, D k) ∪ {x | ¬DifferentiableAt ℝ g x} := by
      intro x hx
      by_cases hdiff : DifferentiableAt ℝ g x
      · exact Or.inl (h1 x hdiff hx)
      · exact Or.inr hdiff
    have h3 : volume (A \ ⋃ k, D k) ≤ volume {x | ¬DifferentiableAt ℝ g x} := by
      have h4 : A \ ⋃ k, D k ⊆ {x | ¬DifferentiableAt ℝ g x} := by
        intro x hx
        have h5 : x ∈ A := hx.1
        exact (h2 h5).resolve_left hx.2
      exact measure_mono h4
    have h4 : volume {x | ¬DifferentiableAt ℝ g x} = 0 := by
      simpa [ae_iff] using hg_diff
    have h5 : volume (A \ ⋃ k, D k) ≤ 0 := by
      rw [h4] at h3; exact h3
    have h6 : 0 ≤ volume (A \ ⋃ k, D k) := by positivity
    exact le_antisymm h5 h6

  -- volume (A \ D k) → 0
  have h_tendsto : Filter.Tendsto (fun k : ℕ => volume (A \ D k)) Filter.atTop (nhds 0) := by
    have h1 : ∀ k, A \ D (k + 1) ⊆ A \ D k := by
      intro k
      have h2 : D k ⊆ D (k + 1) := hD_mono k (k + 1) (by linarith)
      exact Set.diff_subset_diff_right h2
    have h2 : (⋂ k, A \ D k) = A \ ⋃ k, D k := by
      ext x
      simp only [Set.mem_iInter, Set.mem_diff, Set.mem_iUnion]
      constructor
      · intro h
        have hA : x ∈ A := (h 0).1
        have hnot : ∀ k, x ∉ D k := fun k => (h k).2
        exact ⟨hA, fun ⟨k, hk⟩ => hnot k hk⟩
      · intro h
        have hA : x ∈ A := h.1
        have hnot : ∀ k, x ∉ D k := by
          intro k hk
          exact h.2 ⟨k, hk⟩
        intro k
        exact ⟨hA, hnot k⟩
    have h3 : ∀ k, MeasurableSet (A \ D k) := fun k => hA.diff (hD_meas k)
    have h4 : ∃ k, volume (A \ D k) ≠ ⊤ := by
      refine ⟨0, ?_⟩
      exact (measure_mono (show A \ D 0 ⊆ A from by simp)).trans_lt hA_lt_top |>.ne
    have h_tendsto' : Filter.Tendsto (fun k : ℕ => volume (A \ D k)) Filter.atTop
        (nhds (volume (⋂ k, A \ D k))) :=
      MeasureTheory.tendsto_measure_iInter_atTop (fun k => (h3 k).nullMeasurableSet)
        (fun i j hle => Set.diff_subset_diff_right (hD_mono i j hle)) h4
    have h_main : volume (⋂ k, A \ D k) = 0 := by
      rw [h2, h_cover]
    rw [h_main] at h_tendsto'
    exact h_tendsto'

  -- Choose k such that (1+L) * volume (A \ D k) ≤ δ / 2
  have h_exists_k : ∃ (k : ℕ),
      ENNReal.ofReal ((L : ℝ) + 1) * volume (A \ D k) ≤ ENNReal.ofReal (δ / 2) := by
    have h_pos2 : 0 < ENNReal.ofReal (δ / 2) := by positivity
    have h_tendsto2 : Filter.Tendsto (fun k : ℕ => ENNReal.ofReal ((L : ℝ) + 1) * volume (A \ D k))
        Filter.atTop (nhds 0) := by
      let c : ENNReal := ENNReal.ofReal ((L : ℝ) + 1)
      have hc_ne_top : c ≠ ⊤ := ENNReal.coe_lt_top.ne
      have h : Filter.Tendsto (fun k : ℕ => c * volume (A \ D k)) Filter.atTop (nhds (c * 0)) :=
        ENNReal.Tendsto.const_mul h_tendsto (Or.inr hc_ne_top)
      have h_c0 : c * (0 : ENNReal) = 0 := by simp
      rw [h_c0] at h
      exact h
    have h_event : ∀ᶠ k in Filter.atTop,
        ENNReal.ofReal ((L : ℝ) + 1) * volume (A \ D k) < ENNReal.ofReal (δ / 2) :=
      h_tendsto2.eventually (gt_mem_nhds h_pos2)
    rcases h_event.exists with ⟨k, hk⟩
    exact ⟨k, hk.le⟩

  rcases h_exists_k with ⟨k, hk⟩
  let r : ℝ := 1 / (k + 1 : ℝ)
  have hr_pos : 0 < r := by positivity

  -- For t < r, prove the bound
  refine ⟨r, hr_pos, fun t ht_pos ht_lt => ?_⟩
  let S := upperStrip g t A
  have hS_meas : MeasurableSet S := distanceStrip_measurable g hg.continuous A hA t
  let S' := eSplit '' S
  have hS'_meas : MeasurableSet S' := eSplit.measurableSet_image.mpr hS_meas
  have h_vol_eq : volume S = volume S' := by
      have h1 : eSplit ⁻¹' S' = S := by ext x; simp [S']
      have h2 : volume (eSplit ⁻¹' S') = volume S' :=
        eSplit_measurePreserving.measure_preimage hS'_meas.nullMeasurableSet
      rw [h1] at h2; exact h2
  have h_fub : volume S' = ∫⁻ (x : E m), volume {y : ℝ | (x, y) ∈ S'} := by
    rw [Measure.volume_eq_prod (E m) ℝ]
    exact Measure.prod_apply hS'_meas

  let a : E m → (E m →L[ℝ] ℝ) := fun x => fderiv ℝ g x

  -- On D k ∩ differentiability points, full approximation holds
  have h_approx_full : ∀ (x : E m), x ∈ D k → DifferentiableAt ℝ g x →
      ∀ (z : E m), z ∈ closedBall x r →
        abs (g z - (g x + a x (z - x))) ≤ η * ‖z - x‖ := by
    intro x hx hdiff z hz
    let w := z - x
    have hw_ball : w ∈ closedBall 0 r := by
      simpa [w, dist_eq_norm] using hz
    have hQ_inter_dense : closedBall 0 r ⊆ closure (Q ∩ closedBall 0 r) := by
      have h1_raw : ball 0 r ⊆ closure ((ball 0 r) ∩ Q) :=
        hQ_dense.open_subset_closure_inter isOpen_ball
      have h_eq : (ball 0 r) ∩ Q = Q ∩ ball 0 r := Set.inter_comm _ _
      have h_closure_eq : closure ((ball 0 r) ∩ Q) = closure (Q ∩ ball 0 r) := by
        rw [h_eq]
      have h1 : ball 0 r ⊆ closure (Q ∩ ball 0 r) :=
        h_closure_eq ▸ h1_raw
      have h2 : closure (ball 0 r) ⊆ closure (Q ∩ ball 0 r) := by
        have h21 : closure (ball 0 r) ⊆ closure (closure (Q ∩ ball 0 r)) := closure_mono h1
        have h22 : closure (closure (Q ∩ ball 0 r)) = closure (Q ∩ ball 0 r) := closure_closure
        rw [h22] at h21
        exact h21
      have h3 : closure (ball (0 : E m) r) = closedBall (0 : E m) r :=
        closure_ball (0 : E m) hr_pos.ne'
      have h4 : Q ∩ ball 0 r ⊆ Q ∩ closedBall 0 r := by
        intro q hq
        have hbs : q ∈ closedBall (0 : E m) r := ball_subset_closedBall hq.2
        exact ⟨hq.1, hbs⟩
      have h5 : closure (Q ∩ ball 0 r) ⊆ closure (Q ∩ closedBall 0 r) := closure_mono h4
      have h6 : closedBall (0 : E m) r ⊆ closure (Q ∩ ball 0 r) := by
        rw [←h3]; exact h2
      exact subset_trans h6 h5
    have h_cont1 : Continuous (fun v : E m => g (x + v)) := by
      have h : Continuous (fun v : E m => x + v) := by fun_prop
      exact hg.continuous.comp h
    have h_cont2 : Continuous (fun v : E m => a x v) := (a x).continuous
    have h_gx : Continuous (fun (_ : E m) => g x) := continuous_const
    have h4 : Continuous (fun v : E m => g (x + v) - g x - a x v) :=
      h_cont1.sub h_gx |>.sub h_cont2
    have h5 : Continuous (fun v : E m => abs (g (x + v) - g x - a x v)) :=
      continuous_abs.comp h4
    have h6 : Continuous (fun v : E m => η * ‖v‖) :=
      continuous_const.mul continuous_norm
    have h_cont : Continuous (fun v : E m => abs (g (x + v) - g x - a x v) - η * ‖v‖) :=
      h5.sub h6
    have h_le : ∀ v ∈ Q ∩ closedBall 0 r, abs (g (x + v) - g x - a x v) - η * ‖v‖ ≤ 0 := by
      intro v hv
      have h' : ∀ q ∈ Q ∩ closedBall 0 r, abs (g (x + q) - g x - a x q) ≤ η * ‖q‖ := by
        have h_int : x ∈ ⋂ q ∈ (Q ∩ closedBall 0 r), {x : E m | abs (g (x + q) - g x - (fderiv ℝ g x) q) ≤ η * ‖q‖} := hx.2
        have h_bi : ∀ q ∈ Q ∩ closedBall 0 r, abs (g (x + q) - g x - (fderiv ℝ g x) q) ≤ η * ‖q‖ := by
          simpa [Set.mem_biInter] using h_int
        intro q hq
        have h9 := h_bi q hq
        simpa [a] using h9
      have h72 : abs (g (x + v) - g x - a x v) ≤ η * ‖v‖ := h' v hv
      exact sub_nonpos.mpr h72
    have h_closed : IsClosed {v : E m | abs (g (x + v) - g x - a x v) - η * ‖v‖ ≤ 0} :=
      isClosed_le h_cont continuous_const
    have h9 : closure (Q ∩ closedBall 0 r) ⊆ {v : E m | abs (g (x + v) - g x - a x v) - η * ‖v‖ ≤ 0} :=
      closure_minimal h_le h_closed
    have h10 : w ∈ closure (Q ∩ closedBall 0 r) := hQ_inter_dense hw_ball
    have h11 : abs (g (x + w) - g x - a x w) - η * ‖w‖ ≤ 0 := h9 h10
    have h12 : x + w = z := by simp [w]
    have h11' : abs (g z - g x - a x w) - η * ‖w‖ ≤ 0 := by
      rw [h12] at h11; exact h11
    have h13 : a x w = a x (z - x) := by rfl
    rw [h13] at h11'
    have h14 : ‖w‖ = ‖z - x‖ := by rfl
    rw [h14] at h11'
    have h15 : abs (g z - (g x + a x (z - x))) ≤ η * ‖z - x‖ := by
      have h16 : g z - g x - a x (z - x) = g z - (g x + a x (z - x)) := by ring
      have h17 : abs (g z - g x - a x (z - x)) = abs (g z - (g x + a x (z - x))) := by rw [h16]
      rw [h17] at h11'
      exact sub_nonpos.mp h11'
    exact h15

  -- Fiber bound function
  let b : E m → ENNReal := fun x =>
    if x ∈ A \ D k then
      ENNReal.ofReal t * ENNReal.ofReal ((L : ℝ) + 1)
    else if x ∈ A then
      ENNReal.ofReal t * (ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2)) + ENNReal.ofReal η)
    else 0

  have h_bad_meas' : MeasurableSet (A \ D k) := hA.diff (hD_meas k)
  have h_f_meas : Measurable (fun x : E m => ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2))) := by fun_prop
  have h_c1 : Measurable (fun _ : E m => ENNReal.ofReal t * ENNReal.ofReal ((L : ℝ) + 1)) := by fun_prop
  have h_c2 : Measurable (fun x : E m => ENNReal.ofReal t * (ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2)) + ENNReal.ofReal η)) := by fun_prop
  have h_else : Measurable (fun x : E m => if x ∈ A then ENNReal.ofReal t * (ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2)) + ENNReal.ofReal η) else 0) := by
    refine Measurable.ite hA h_c2 measurable_const
  have h_b_meas : Measurable b := by
    refine Measurable.ite h_bad_meas' h_c1 h_else

  -- volume fiber ≤ b x a.e.
  have h_fiber : ∀ᵐ (x : E m) ∂volume, volume {y : ℝ | (x, y) ∈ S'} ≤ b x := by
    filter_upwards [hg_diff] with x hdiff
    by_cases hxA : x ∈ A
    · by_cases hxD : x ∈ D k
      · -- x ∈ D k and differentiable: use fiber_bound
        have h_approx' : ∀ z ∈ closedBall x r, abs (g z - (g x + a x (z - x))) ≤ η * ‖z - x‖ :=
          h_approx_full x hxD hdiff
        have h_ind : b x = ENNReal.ofReal t * (ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2)) + ENNReal.ofReal η) := by
          have h1 : x ∉ A \ D k := by intro h; exact h.2 hxD
          simp only [b]
          rw [if_neg h1, if_pos hxA]
        rw [h_ind]
        have h_fiber_subset : {y : ℝ | (x, y) ∈ S'} ⊆
            Set.Ioc (g x) (g x + t * (Real.sqrt (1 + ‖a x‖ ^ 2) + η)) := by
          intro y hy
          let p : E (m + 1) := eSplit.symm (x, y)
          have hp_in_S : p ∈ S := by
            have h5 : eSplit p ∈ S' := by
              have h_eq : eSplit p = (x, y) := eSplit.apply_symm_apply (x, y)
              rw [h_eq]
              exact hy
            rcases h5 with ⟨q, hq, h_eq⟩
            have hq_eq : q = p := eSplit.injective h_eq
            rw [hq_eq] at hq; exact hq
          have hS_p := hp_in_S
          have hp_proj : GraphAreaFormula.proj p = x := by
            have h6 : (eSplit p).1 = x := by simp [p]
            have h7 : (eSplit p).1 = GraphAreaFormula.proj p := by
              rw [eSplit_apply p] <;> rfl
            exact h7.symm.trans h6
          have hp_last : p (Fin.last m) = y := by
            have h6 : (eSplit p).2 = y := by simp [p]
            have h7 : (eSplit p).2 = p (Fin.last m) := by
              rw [eSplit_apply p] <;> rfl
            exact h7.symm.trans h6
          have h_above : y > g x := by
            have h4 : p (Fin.last m) > g (GraphAreaFormula.proj p) := hS_p.2.2.2
            rw [hp_last, hp_proj] at h4; exact h4
          have h_inf : infDist p (GraphAreaFormula.graph g) < t := hS_p.2.2.1
          have h_le : y - g x ≤ t * (Real.sqrt (1 + ‖a x‖ ^ 2) + η) :=
            fiber_bound g x (a x) y r η t hr_pos (by linarith) ht_pos ht_lt h_approx'
              p hp_proj hp_last h_above h_inf
          exact ⟨h_above, by linarith⟩
        calc volume {y : ℝ | (x, y) ∈ S'}
          ≤ volume (Set.Ioc (g x) (g x + t * (Real.sqrt (1 + ‖a x‖ ^ 2) + η))) :=
            measure_mono h_fiber_subset
        _ = ENNReal.ofReal (t * (Real.sqrt (1 + ‖a x‖ ^ 2) + η)) := by
            rw [Real.volume_Ioc]
            have h_nonneg : 0 ≤ t * (Real.sqrt (1 + ‖a x‖ ^ 2) + η) := by positivity
            simp [h_nonneg, max_eq_right h_nonneg] <;> ring
        _ = ENNReal.ofReal t * (ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2)) + ENNReal.ofReal η) := by
            have h_pos1 : 0 ≤ t := by linarith
            have h_pos2 : 0 ≤ Real.sqrt (1 + ‖a x‖ ^ 2) + η := by positivity
            have h_eq1 : t * (Real.sqrt (1 + ‖a x‖ ^ 2) + η) =
                t * Real.sqrt (1 + ‖a x‖ ^ 2) + t * η := by ring
            rw [h_eq1]
            have h : ENNReal.ofReal (t * Real.sqrt (1 + ‖a x‖ ^ 2) + t * η) =
                ENNReal.ofReal (t * Real.sqrt (1 + ‖a x‖ ^ 2)) + ENNReal.ofReal (t * η) := by
              rw [ENNReal.ofReal_add] <;> positivity
            rw [h]
            have h2 : ENNReal.ofReal (t * Real.sqrt (1 + ‖a x‖ ^ 2)) =
                ENNReal.ofReal t * ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2)) := by
              rw [← ENNReal.ofReal_mul h_pos1]
            have h3 : ENNReal.ofReal (t * η) = ENNReal.ofReal t * ENNReal.ofReal η := by
              rw [← ENNReal.ofReal_mul h_pos1]
            have h4 := congr_arg₂ (·+·) h2 h3
            have h5 : ENNReal.ofReal t * ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2)) + ENNReal.ofReal t * ENNReal.ofReal η = ENNReal.ofReal t * (ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2)) + ENNReal.ofReal η) := by rw [mul_add]
            exact h4.trans h5
      · -- x ∈ A \ D k: use crude bound
        have h_xbad : x ∈ A \ D k := ⟨hxA, hxD⟩
        have h_ind : b x = ENNReal.ofReal t * ENNReal.ofReal ((L : ℝ) + 1) := by
          simp only [b]
          rw [if_pos h_xbad]
        rw [h_ind]
        have h_set_eq : {y : ℝ | (x, y) ∈ S'} = {y : ℝ | eSplit.symm (x, y) ∈ S} := by
          ext y
          simp only [Set.mem_setOf_eq, S']
          constructor
          · intro h
            rcases h with ⟨q, hq, h_eq⟩
            have hq_eq : q = eSplit.symm (x, y) := by
              exact eSplit.injective (h_eq.trans (eSplit.apply_symm_apply (x, y)).symm)
            exact hq_eq ▸ hq
          · intro h
            exact ⟨eSplit.symm (x, y), h, eSplit.apply_symm_apply (x, y)⟩
        rw [h_set_eq]
        have h_bound := crude_fiber_bound g hg x t ht_pos hxA
        have h_eq2 : ENNReal.ofReal (t * (1 + (L : ℝ))) = ENNReal.ofReal t * ENNReal.ofReal ((L : ℝ) + 1) := by
          have h_pos1 : 0 ≤ t := by linarith
          rw [← ENNReal.ofReal_mul h_pos1] <;> ring_nf
        rw [h_eq2] at h_bound
        exact h_bound
    · -- x ∉ A: fiber empty
      have h_ind : b x = 0 := by
          have h1 : x ∉ A \ D k := by intro h; exact hxA h.1
          simp only [b]
          rw [if_neg h1, if_neg hxA]
      rw [h_ind]
      have h_empty : {y : ℝ | (x, y) ∈ S'} = ∅ := by
        ext y; simp only [Set.mem_empty_iff_false, iff_false]
        intro hy
        let p : E (m + 1) := eSplit.symm (x, y)
        have hp : p ∈ S := by
          have h5 : eSplit p ∈ S' := by
            have h_eq : eSplit p = (x, y) := eSplit.apply_symm_apply (x, y)
            rw [h_eq]
            exact hy
          rcases h5 with ⟨q, hq, h_eq⟩
          have hq_eq : q = p := eSplit.injective h_eq
          rw [hq_eq] at hq; exact hq
        have h1 : GraphAreaFormula.proj p ∈ A := hp.1
        have hp_proj : GraphAreaFormula.proj p = x := by
          have h6 : (eSplit p).1 = x := by simp [p]
          have h7 : (eSplit p).1 = GraphAreaFormula.proj p := by
            rw [eSplit_apply p] <;> rfl
          exact h7.symm.trans h6
        rw [hp_proj] at h1; exact hxA h1
      rw [h_empty] <;> simp

  have h_main : ∫⁻ (x : E m), volume {y : ℝ | (x, y) ∈ S'} ≤ ∫⁻ (x : E m), b x :=
    lintegral_mono_ae h_fiber

  -- Compute ∫ b
  have hDk_meas : MeasurableSet (D k) := hD_meas k
  have h_bad_meas : MeasurableSet (A \ D k) := hA.diff hDk_meas
  have h_int : ∫⁻ (x : E m), b x =
      ENNReal.ofReal t * (ENNReal.ofReal ((L : ℝ) + 1) * volume (A \ D k) +
        (∫⁻ x in D k, ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2))) +
        ENNReal.ofReal η * volume (D k)) := by
    have h1 : ∫⁻ (x : E m), b x =
        (∫⁻ x in (A \ D k), b x) + (∫⁻ x in (D k), b x) := by
      have hD_sub : D k ⊆ A := fun x hx => hx.1
      have h_union_set : (A \ D k) ∪ D k = A :=
        Set.diff_union_of_subset hD_sub
      have h_disj : Disjoint (A \ D k) (D k) := by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        exact hx1.2 hx2
      have h_bad_meas : MeasurableSet (A \ D k) := hA.diff hDk_meas
      have h_union_int : (∫⁻ x in (A \ D k) ∪ D k, b x) =
          (∫⁻ x in (A \ D k), b x) + (∫⁻ x in (D k), b x) := by
        exact lintegral_union hDk_meas h_disj
      have h2 : ∫⁻ x in A, b x = ∫⁻ (x : E m), b x := by
        have h3 : ∀ x ∉ A, b x = 0 := by
          intro x hx
          have h1 : x ∉ A \ D k := by intro h; exact hx h.1
          simp only [b]
          rw [if_neg h1, if_neg hx]
        have h4 : ∀ x, Set.indicator A b x = b x := by
          intro x
          by_cases hx : x ∈ A
          · simp [hx, Set.indicator_of_mem]
          · have h6 : Set.indicator A b x = 0 := by
              rw [Set.indicator_apply, if_neg hx]
            have h7 : b x = 0 := h3 x hx
            rw [h6, h7]
        have h5 : ∫⁻ x in A, b x = ∫⁻ (x : E m), Set.indicator A b x :=
          (lintegral_indicator hA b).symm
        rw [h5]
        apply lintegral_congr
        exact h4
      calc ∫⁻ (x : E m), b x
        = ∫⁻ x in A, b x := h2.symm
      _ = ∫⁻ x in (A \ D k) ∪ D k, b x := by rw [h_union_set]
      _ = (∫⁻ x in (A \ D k), b x) + (∫⁻ x in (D k), b x) := h_union_int
    rw [h1]
    have h_bad_eq : ∫⁻ x in (A \ D k), b x =
        ENNReal.ofReal t * ENNReal.ofReal ((L : ℝ) + 1) * volume (A \ D k) := by
      have h4 : ∀ x ∈ (A \ D k), b x = ENNReal.ofReal t * ENNReal.ofReal ((L : ℝ) + 1) := by
        intro x hx
        simp only [b]
        rw [if_pos hx]
      rw [setLIntegral_congr_fun h_bad_meas h4]
      have h5 : ∫⁻ x in (A \ D k), (ENNReal.ofReal t * ENNReal.ofReal ((L : ℝ) + 1)) =
          (ENNReal.ofReal t * ENNReal.ofReal ((L : ℝ) + 1)) * volume (A \ D k) := by
        rw [setLIntegral_const]
      rw [h5] <;> ring
    have h_Dk_eq : ∫⁻ x in (D k), b x =
        ENNReal.ofReal t * ((∫⁻ x in D k, ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2))) +
          ENNReal.ofReal η * volume (D k)) := by
      have h4 : ∀ x ∈ (D k), b x = ENNReal.ofReal t *
          (ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2)) + ENNReal.ofReal η) := by
        intro x hx
        have h5 : x ∈ A := hx.1
        have h6 : x ∉ A \ D k := by
          intro h7; exact h7.2 hx
        simp only [b]
        rw [if_neg h6, if_pos h5]
      rw [setLIntegral_congr_fun hDk_meas h4]
      let f : E m → ENNReal := fun x => ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2))
      let c : ENNReal := ENNReal.ofReal η
      have hf : Measurable f := by fun_prop
      have hc : Measurable (fun _ : E m => c) := by fun_prop
      have h_const_mul : ∫⁻ x in D k, ENNReal.ofReal t * (f x + c) =
          ENNReal.ofReal t * ∫⁻ x in D k, (f x + c) :=
        lintegral_const_mul (ENNReal.ofReal t) (hf.add hc)
      rw [h_const_mul]
      have h6 : ∫⁻ x in D k, (f x + c) = (∫⁻ x in D k, f x) + ∫⁻ x in D k, c :=
        lintegral_add_left hf (fun x => c)
      rw [h6]
      have h7 : ∫⁻ x in D k, c = c * volume (D k) := by
        rw [setLIntegral_const]
      rw [h7] <;> ring
    have h_goal : (∫⁻ x in (A \ D k), b x) + (∫⁻ x in (D k), b x) =
        ENNReal.ofReal t * ((ENNReal.ofReal ((L : ℝ) + 1) * volume (A \ D k) +
          (∫⁻ x in D k, ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2)))) +
            ENNReal.ofReal η * volume (D k)) := by
      set c : ENNReal := ENNReal.ofReal t with hc
      set x1 : ENNReal := ENNReal.ofReal ((L : ℝ) + 1) * volume (A \ D k) with hx1
      set x2 : ENNReal := ∫⁻ x in D k, ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2)) with hx2
      set x3 : ENNReal := ENNReal.ofReal η * volume (D k) with hx3
      have h_first : (c * ENNReal.ofReal ((L : ℝ) + 1)) * volume (A \ D k) = c * x1 := by
        simp only [hx1]
        rw [mul_assoc]
      have h_lhs : (∫⁻ x in (A \ D k), b x) + (∫⁻ x in (D k), b x) =
          (c * ENNReal.ofReal ((L : ℝ) + 1)) * volume (A \ D k) + c * (x2 + x3) := by
        have h_bad_eq' : (∫⁻ x in (A \ D k), b x) = (c * ENNReal.ofReal ((L : ℝ) + 1)) * volume (A \ D k) := by
          rw [h_bad_eq, mul_assoc]
        exact congr_arg₂ (· + ·) h_bad_eq' h_Dk_eq
      rw [h_lhs, h_first]
      have h_factor : c * x1 + c * (x2 + x3) = c * (x1 + (x2 + x3)) := by
        rw [← mul_add]
      rw [h_factor]
      have h_add_assoc : x1 + (x2 + x3) = (x1 + x2) + x3 := by rw [add_assoc]
      rw [h_add_assoc]
    exact h_goal

  -- Lower area formula
  have h_area_lower : (∫⁻ x in D k, ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2))) ≤
      ∫⁻ x in A, ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2)) := by
    exact MeasureTheory.lintegral_mono_set (fun x hx => hx.1)
  have h_area : ∫⁻ x in A, ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2)) ≤ H :=
    lipschitz_graph_area_lower hg A hA

  -- Final bound
  have h_final : ∫⁻ (x : E m), b x ≤ ENNReal.ofReal t * (H + ENNReal.ofReal δ) := by
    rw [h_int]
    have h_err1 : ENNReal.ofReal ((L : ℝ) + 1) * volume (A \ D k) ≤ ENNReal.ofReal (δ / 2) := hk
    have h_err2 : ENNReal.ofReal η * volume (D k) ≤ ENNReal.ofReal (δ / 2) := by
      have h_sub : D k ⊆ A := fun x hx => hx.1
      have h_vol : volume (D k) ≤ volume A := measure_mono h_sub
      have h3 : ENNReal.ofReal η * volume (D k) ≤ ENNReal.ofReal η * volume A := mul_le_mul_left' h_vol _
      exact h3.trans hη_vol
    have h_area' : (∫⁻ x in D k, ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2))) ≤ H :=
      h_area_lower.trans h_area
    have h_half_add : ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) = ENNReal.ofReal δ := by
      have h_pos : 0 ≤ δ / 2 := by linarith
      have h_eq : δ / 2 + δ / 2 = δ := by ring
      rw [← ENNReal.ofReal_add h_pos h_pos, h_eq]
    have h_sum : ENNReal.ofReal ((L : ℝ) + 1) * volume (A \ D k) +
        (∫⁻ x in D k, ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2))) +
        ENNReal.ofReal η * volume (D k) ≤ H + ENNReal.ofReal δ := by
      have h_step1 : ENNReal.ofReal ((L : ℝ) + 1) * volume (A \ D k) +
          (∫⁻ x in D k, ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2))) ≤
          ENNReal.ofReal (δ / 2) + H :=
        add_le_add h_err1 h_area'
      have h_step2 : (ENNReal.ofReal ((L : ℝ) + 1) * volume (A \ D k) +
          (∫⁻ x in D k, ENNReal.ofReal (Real.sqrt (1 + ‖a x‖ ^ 2)))) +
          ENNReal.ofReal η * volume (D k) ≤
          (ENNReal.ofReal (δ / 2) + H) + ENNReal.ofReal (δ / 2) :=
        add_le_add h_step1 h_err2
      have h_abel : (ENNReal.ofReal (δ / 2) + H) + ENNReal.ofReal (δ / 2) =
          H + (ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2)) := by abel
      rw [h_abel] at h_step2
      rw [h_half_add] at h_step2
      exact h_step2
    exact mul_le_mul_left' h_sum _

  -- Convert to multiplicative
  have h_mult : H + ENNReal.ofReal δ = ENNReal.ofReal (1 + ε) * H := by
    have h1 : δ = ε * h := by rfl
    have hε_pos' : 0 ≤ ε := by linarith
    have h2 : ENNReal.ofReal δ = ENNReal.ofReal ε * H := by
      rw [h1, hH_eq]
      rw [ENNReal.ofReal_mul hε_pos']
      <;> rfl
    rw [h2]
    have h3 : ENNReal.ofReal (1 + ε) = 1 + ENNReal.ofReal ε := by
      have h4 : 0 ≤ (1 : ℝ) := by norm_num
      rw [ENNReal.ofReal_add h4 hε_pos']
      <;> norm_cast
    rw [h3]
    <;> ring

  calc volume S
    = volume S' := h_vol_eq
    _ = ∫⁻ (x : E m), volume {y : ℝ | (x, y) ∈ S'} := h_fub
    _ ≤ ∫⁻ (x : E m), b x := h_main
    _ ≤ ENNReal.ofReal t * (H + ENNReal.ofReal δ) := h_final
    _ = ENNReal.ofReal t * (ENNReal.ofReal (1 + ε) * H) := by rw [h_mult]
    _ = ENNReal.ofReal (1 + ε) * ENNReal.ofReal t * H := by ring

end LipschitzStrip

end Geometry.Isoperimetric
