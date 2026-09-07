module

/-
Two separated subsets lemma for the non-concentrated case.

If A is a measurable subset of an r-tube around line L with ν(A) ≥ m,
and A is non-concentrated at scale ρ (every ρ-ball contains at most
1/3 of A's mass), then there exist two measurable subsets Y₁, Y₂ ⊂ A,
each of measure ≥ m/6, with dist(Y₁, Y₂) ≥ ρ.

Requires r ≤ (√3/2)·ρ so that a ρ-length segment of the tube fits
inside a ρ-ball (Pythagorean theorem).
-/

public import MyLeanRepo.RadialBootstrapping.Basic

@[expose] public section

open MeasureTheory Metric Set Finset


noncomputable section

namespace RadialBootstrapping

/-- Geometric lemma: a ρ-length axial segment of an r-tube fits in a ρ-ball. -/
lemma tube_segment_in_ball
    (L : Line2) (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ)
    (h_width : r ≤ (Real.sqrt 3 / 2) * ρ)
    (p v : Point) (hv_norm : ‖v‖ = 1)
    (V : Submodule ℝ Point) (hv_V : v ∈ V)
    (hV_eq : V = L.toAffine.direction)
    (hV_eq_span : V = Submodule.span ℝ {v})
    (p0 : Point) (hp0 : p0 ∈ L.toAffine)
    (coord : Point → ℝ)
    (hcoord_def : ∀ x, coord x = inner ℝ (x - p) v)
    (hcoord_on_line : ∀ (x y : Point), x ∈ L.toAffine → y ∈ L.toAffine →
      dist x y = |coord x - coord y|) :
    ∀ (x : Point), x ∈ tube r L → |coord x - coord p0| ≤ ρ / 2 → x ∈ ball p0 ρ := by
  intro x hx_tube h_coord
  letI : Nonempty L.toAffine := ⟨⟨p0, hp0⟩⟩
  let q : Point := (EuclideanGeometry.orthogonalProjection L.toAffine x : Point)
  have hq : q ∈ L.toAffine := (EuclideanGeometry.orthogonalProjection L.toAffine x).property
  have h_in_tube : infDist x (L.toAffine : Set Point) < r := by
    have htube : x ∈ Metric.thickening r (L.toSet) := hx_tube
    rcases Metric.mem_thickening_iff.mp htube with ⟨z, hz, hdist⟩
    have h2 : infDist x (L.toAffine : Set Point) ≤ dist x z := by exact infDist_le_dist_of_mem hz
    exact lt_of_le_of_lt h2 hdist
  have h_dist_xq_eq : dist x q = infDist x (L.toAffine : Set Point) :=
    EuclideanGeometry.dist_orthogonalProjection_eq_infDist L.toAffine x
  have h_dist_xq_lt : dist x q < r := by
    have h : dist x q = infDist x (L.toAffine : Set Point) := h_dist_xq_eq
    rw [h]; exact h_in_tube
  have h_proj_formula : q = V.starProjection (x - p0) + p0 := by
    have h' := EuclideanGeometry.orthogonalProjection_apply_mem (s := L.toAffine) (p := x) (x := p0) hp0
    have h_lin : V.starProjection (x - p0) = V.starProjection x - V.starProjection p0 :=
      V.starProjection.map_sub x p0
    have hV' : V = L.toAffine.direction := hV_eq
    have h_simp : q = V.starProjection x - V.starProjection p0 + p0 := by
      simpa [hV', vadd_eq_add] using h'
    rw [h_simp, h_lin.symm]
  have h_orth_vec : (x - p0) - V.starProjection (x - p0) ∈ Vᗮ :=
    V.sub_starProjection_mem_orthogonal (x - p0)
  have h_xmq : x - q = (x - p0) - V.starProjection (x - p0) := by
    rw [h_proj_formula] <;> abel
  have h_orth : inner ℝ (x - q) v = 0 := by
    rw [h_xmq]
    have h_comm : inner ℝ ((x - p0) - V.starProjection (x - p0)) v =
        inner ℝ v ((x - p0) - V.starProjection (x - p0)) := by
      exact real_inner_comm v (x - p0 - V.starProjection (x - p0))
    rw [h_comm]
    exact h_orth_vec v hv_V
  have h_coord_q : coord q = coord x := by
    have h2 : coord x - coord q = inner ℝ (x - q) v := by
      have h1 : coord x - coord q = inner ℝ (x - p) v - inner ℝ (q - p) v := by
        rw [hcoord_def x, hcoord_def q]
      rw [h1]
      have h3 : inner ℝ (x - p) v - inner ℝ (q - p) v = inner ℝ ((x - p) - (q - p)) v := by
        rw [←inner_sub_left]
      rw [h3]
      have h4 : (x - p) - (q - p) = x - q := by abel
      rw [h4]
    have h3 : coord x - coord q = 0 := by rw [h2, h_orth] <;> ring
    linarith
  have h_p0q_in_V : p0 - q ∈ V := by
    have h : p0 -ᵥ q ∈ L.toAffine.direction := L.toAffine.vsub_mem_direction hp0 hq
    have hV' : V = L.toAffine.direction := hV_eq
    rw [hV']
    simpa [vsub_eq_sub] using h
  have h_orth2 : inner ℝ (x - q) (p0 - q) = 0 := by
    rw [h_xmq]
    have h_comm : inner ℝ ((x - p0) - V.starProjection (x - p0)) (p0 - q) =
        inner ℝ (p0 - q) ((x - p0) - V.starProjection (x - p0)) := by exact real_inner_comm (p0 - q) (x - p0 - V.starProjection (x - p0))
    rw [h_comm]
    exact h_orth_vec (p0 - q) h_p0q_in_V
  have h_pyth : ‖x - p0‖ ^ 2 = ‖x - q‖ ^ 2 + ‖p0 - q‖ ^ 2 := by
    have h : ‖(x - q) - (p0 - q)‖ * ‖(x - q) - (p0 - q)‖ =
        ‖x - q‖ * ‖x - q‖ + ‖p0 - q‖ * ‖p0 - q‖ :=
      norm_sub_sq_eq_norm_sq_add_norm_sq_real (h := h_orth2)
    have h4 : (x - q) - (p0 - q) = x - p0 := by abel
    rw [h4] at h
    have h5 : ‖x - p0‖ * ‖x - p0‖ = ‖x - q‖ * ‖x - q‖ + ‖p0 - q‖ * ‖p0 - q‖ := h
    have h6 : ‖x - p0‖ ^ 2 = ‖x - p0‖ * ‖x - p0‖ := by ring
    have h7 : ‖x - q‖ ^ 2 = ‖x - q‖ * ‖x - q‖ := by ring
    have h8 : ‖p0 - q‖ ^ 2 = ‖p0 - q‖ * ‖p0 - q‖ := by ring
    linarith
  have h_dist_p0q : dist p0 q = |coord p0 - coord q| := hcoord_on_line p0 q hp0 hq
  have h_main_eq : dist p0 x ^ 2 = dist p0 q ^ 2 + dist x q ^ 2 := by
    have h5 : dist p0 x = ‖p0 - x‖ := by simp [dist_eq_norm]
    have h6 : ‖p0 - x‖ = ‖x - p0‖ := by rw [norm_sub_rev]
    have h7 : dist p0 q = ‖p0 - q‖ := by simp [dist_eq_norm]
    have h8 : dist x q = ‖x - q‖ := by simp [dist_eq_norm]
    rw [h5, h6, h7, h8]
    have h9 : ‖x - p0‖ ^ 2 = ‖p0 - q‖ ^ 2 + ‖x - q‖ ^ 2 := by
      rw [h_pyth] <;> ring
    exact h9
  have h2 : (coord x - coord p0) ^ 2 ≤ (ρ / 2) ^ 2 := by
    have h3 : |coord x - coord p0| ^ 2 ≤ (ρ / 2) ^ 2 := by gcongr
    have h4 : (coord x - coord p0) ^ 2 = |coord x - coord p0| ^ 2 := by simp [sq_abs]
    rw [h4]; exact h3
  have h6 : dist x q ^ 2 < r ^ 2 := by
    have h7 : 0 ≤ dist x q := by positivity
    nlinarith
  have h9 : r ^ 2 ≤ (3 / 4 : ℝ) * ρ ^ 2 := by
    have h10 : 0 ≤ r := by linarith
    have h11 : r ^ 2 ≤ ((Real.sqrt 3 / 2) * ρ) ^ 2 := by gcongr
    have h12 : ((Real.sqrt 3 / 2) * ρ) ^ 2 = (3 / 4 : ℝ) * ρ ^ 2 := by
      have h13 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 3]
    linarith
  have h_dist_p0q_sq : dist p0 q ^ 2 = (coord x - coord p0) ^ 2 := by
    rw [h_dist_p0q, h_coord_q]
    have h_abs : |coord p0 - coord x| = |coord x - coord p0| := by
      have h : coord p0 - coord x = -(coord x - coord p0) := by abel
      rw [h, abs_neg]
    rw [h_abs]
    <;> simp [sq_abs]
  have h10 : dist p0 x ^ 2 < ρ ^ 2 := by
    rw [h_main_eq]
    have h11 : dist p0 q ^ 2 ≤ (ρ / 2) ^ 2 := by
      rw [h_dist_p0q_sq]; exact h2
    have h12 : dist p0 q ^ 2 + dist x q ^ 2 < (ρ / 2) ^ 2 + r ^ 2 := by
      exact add_lt_add_of_le_of_lt h11 h6
    have h13 : (ρ / 2) ^ 2 + r ^ 2 ≤ ρ ^ 2 := by
      have h14 : 0 ≤ ρ := by linarith
      nlinarith
    exact lt_of_lt_of_le h12 h13
  have h14 : 0 ≤ dist p0 x := by positivity
  have h15 : dist p0 x < ρ := by nlinarith
  have h16 : dist x p0 < ρ := by rwa [dist_comm] at h15
  simpa [ball, dist_eq_norm] using h16

/-- Two-separated-subsets lemma for subsets of a thin tube. -/
lemma two_separated_subsets_in_tube
    (L : Line2) (r ρ m : ℝ)
    (hr : 0 < r) (hρ : 0 < ρ) (hm : 0 < m)
    (h_width : r ≤ (Real.sqrt 3 / 2) * ρ)
    (ν : Measure Point) [IsProbabilityMeasure ν]
    (A : Set Point) (hA_meas : MeasurableSet A)
    (hA_sub : A ⊆ tube r L)
    (hA_ge : ν A ≥ ENNReal.ofReal m)
    (h_nonconc : ∀ (x : Point), ν (A ∩ ball x ρ) ≤ (ν A) / 3) :
    ∃ (Y1 Y2 : Set Point),
      MeasurableSet Y1 ∧ MeasurableSet Y2 ∧
      Y1 ⊆ A ∧ Y2 ⊆ A ∧
      ν Y1 ≥ ENNReal.ofReal (m / 6) ∧
      ν Y2 ≥ ENNReal.ofReal (m / 6) ∧
      ∀ y1 ∈ Y1, ∀ y2 ∈ Y2, dist y1 y2 ≥ ρ := by
  -- ======================================================================
  -- Step 1: Set up the axial coordinate function
  -- ======================================================================
  let p : Point := L.closestPoint
  have hp : p ∈ L.toAffine := L.closestPoint_mem
  let V : Submodule ℝ Point := L.toAffine.direction
  have hV_rank : Module.finrank ℝ V = 1 := L.2
  have hV_ne_bot : V ≠ (⊥ : Submodule ℝ Point) := by
    intro hbot
    have h : Module.finrank ℝ V = 0 := by rw [hbot] <;> simp
    rw [hV_rank] at h <;> norm_num at h
  have hV_exists : ∃ (w : Point), w ∈ V ∧ w ≠ 0 := by
    simpa [Submodule.ne_bot_iff] using hV_ne_bot
  let w : Point := Classical.choose hV_exists
  have hw_V : w ∈ V := (Classical.choose_spec hV_exists).1
  have hw_ne_zero : w ≠ 0 := (Classical.choose_spec hV_exists).2
  have hwnorm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne_zero
  let v : Point := (1 / ‖w‖ : ℝ) • w
  have hv_V : v ∈ V := V.smul_mem (1 / ‖w‖) hw_V
  have hv_norm : ‖v‖ = 1 := by
    simp [v, norm_smul, hwnorm_pos.ne'] <;> field_simp [hwnorm_pos.ne'] <;> ring
  have hv_ne_zero : v ≠ 0 := by
    intro h; rw [h] at hv_norm; norm_num at hv_norm
  have h1_span : Submodule.span ℝ {v} ≤ V := by
    rw [Submodule.span_le]; intro z hz
    simp only [Set.mem_singleton_iff] at hz; rw [hz] <;> exact hv_V
  have h2_span : Module.finrank ℝ (Submodule.span ℝ {v}) = 1 :=
    finrank_span_singleton hv_ne_zero
  have hV_eq_span : V = Submodule.span ℝ {v} := by
    have h3 : V ≤ Submodule.span ℝ {v} := by
      by_contra h4
      have h5 : Submodule.span ℝ {v} < V := by
        exact lt_iff_le_and_ne.mpr ⟨h1_span, fun h => h4 (le_of_eq h.symm)⟩
      have h6 : Module.finrank ℝ (Submodule.span ℝ {v}) < Module.finrank ℝ V :=
        Submodule.finrank_lt_finrank_of_lt h5
      rw [h2_span, hV_rank] at h6 <;> norm_num at h6
    exact le_antisymm h3 h1_span
  let coord : Point → ℝ := fun x => inner ℝ (x - p) v
  have hcoord_def : ∀ x, coord x = inner ℝ (x - p) v := fun x => rfl
  have hcoord_cont : Continuous coord := by
    have h1 : Continuous (fun x : Point => inner ℝ x v) := by fun_prop
    have h2 : Continuous (fun x : Point => x - p) := by fun_prop
    exact h1.comp h2
  have hcoord_meas : Measurable coord := hcoord_cont.measurable
  have hcoord_lipschitz : ∀ (x y : Point), |coord x - coord y| ≤ dist x y := by
    intro x y
    have h : coord x - coord y = inner ℝ (x - y) v := by
      have h1 : coord x - coord y = inner ℝ (x - p) v - inner ℝ (y - p) v := by
        rw [hcoord_def x, hcoord_def y]
      rw [h1]
      have h2 : inner ℝ (x - p) v - inner ℝ (y - p) v = inner ℝ ((x - p) - (y - p)) v := by
        rw [←inner_sub_left]
      rw [h2]
      have h3 : (x - p) - (y - p) = x - y := by abel
      rw [h3]
    rw [h]
    have h2 : |inner ℝ (x - y) v| ≤ ‖x - y‖ * ‖v‖ := abs_real_inner_le_norm (x - y) v
    rw [hv_norm] at h2
    simpa [dist_eq_norm] using h2
  have hcoord_on_line : ∀ (x y : Point), x ∈ L.toAffine → y ∈ L.toAffine →
      dist x y = |coord x - coord y| := by
    intro x y hx hy
    have h1 : x - y ∈ V := L.toAffine.vsub_mem_direction hx hy
    rw [hV_eq_span] at h1
    rcases Submodule.mem_span_singleton.mp h1 with ⟨c, hc⟩
    have h3 : x - y = c • v := Eq.symm hc
    have h4 : coord x - coord y = c := by
      have h5 : coord x - coord y = inner ℝ (x - y) v := by
        have h1 : coord x - coord y = inner ℝ (x - p) v - inner ℝ (y - p) v := by
          rw [hcoord_def x, hcoord_def y]
        rw [h1]
        have h2 : inner ℝ (x - p) v - inner ℝ (y - p) v = inner ℝ ((x - p) - (y - p)) v := by
          rw [←inner_sub_left]
        rw [h2]
        have h3 : (x - p) - (y - p) = x - y := by abel
        rw [h3]
      rw [h5, h3]
      have h6 : inner ℝ (c • v) v = c * inner ℝ v v := by
        simpa [inner_smul_left] using rfl
      rw [h6, real_inner_self_eq_norm_sq, hv_norm] <;> ring
    have h6 : dist x y = |c| := by
      rw [dist_eq_norm, h3, norm_smul]
      have h7 : ‖c‖ = |c| := by simp
      rw [h7, hv_norm] <;> ring
    rw [h6, h4]
  -- ======================================================================
  -- Step 2: Geometric lemma
  -- ======================================================================
  have h_geom : ∀ (p0 : Point), p0 ∈ L.toAffine → ∀ (x : Point),
      x ∈ tube r L → |coord x - coord p0| ≤ ρ / 2 → x ∈ ball p0 ρ :=
    fun p0 hp0 => tube_segment_in_ball L r ρ hr hρ h_width p v hv_norm V hv_V
      (by rfl) hV_eq_span p0 hp0 coord hcoord_def hcoord_on_line
  -- ======================================================================
  -- Step 3: Define cumulative distribution F(s)
  -- ======================================================================
  let F : ℝ → ENNReal := fun s => ν (A ∩ {x | coord x ≤ s})
  have hF_mono : Monotone F := by
    intro s1 s2 h; apply measure_mono; intro x hx
    exact ⟨hx.1, le_trans hx.2 h⟩
  have hA_lt_top : ν A ≠ ⊤ := by
    have h : ν A ≤ ν Set.univ := measure_mono (Set.subset_univ A)
    have h2 : ν Set.univ = 1 := by simp
    rw [h2] at h
    exact ne_top_of_le_ne_top (by simp) h
  have hm6_pos : 0 < m / 6 := by linarith
  let m6 : ENNReal := ENNReal.ofReal (m / 6)
  have hm6_ne_top : m6 ≠ ⊤ := ENNReal.ofReal_ne_top
  -- F(n) → ν(A) as n → ∞
  have hF_top : ∃ (N : ℕ), F (N : ℝ) ≥ m6 := by
    let f : ℕ → Set Point := fun n => A ∩ {x | coord x ≤ (n : ℝ)}
    have hf_mono : Monotone f := by
      intro m n hmn
      intro x hx
      have hmn' : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
      exact ⟨hx.1, le_trans hx.2 hmn'⟩
    have h2 : (⋃ n : ℕ, f n) = A := by
      ext x
      simp only [f, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨n, hx, _⟩; exact hx
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_ge (coord x)
        exact ⟨n, hx, by exact_mod_cast hn⟩
    have h3 : ν A = ⨆ n : ℕ, F (n : ℝ) := by
      have h4 : ν (⋃ n : ℕ, f n) = ⨆ n : ℕ, ν (f n) := hf_mono.measure_iUnion
      rw [h2] at h4; exact h4
    by_contra h4
    push Not at h4
    have h4' : ∀ n : ℕ, F (n : ℝ) ≤ m6 := fun n => le_of_lt (h4 n)
    have h5 : (⨆ n : ℕ, F (n : ℝ)) ≤ m6 := iSup_le h4'
    have h6 : ν A ≤ m6 := by
      calc ν A = ⨆ n : ℕ, F (n : ℝ) := h3
           _ ≤ m6 := h5
    have h8 : m > m / 6 := by linarith
    have h9 : ENNReal.ofReal m > m6 := by
      have h10 : m / 6 < m := by linarith
      have hpos : 0 < m := by linarith
      have hiff : ENNReal.ofReal (m / 6) < ENNReal.ofReal m ↔ m / 6 < m :=
        ENNReal.ofReal_lt_ofReal_iff hpos
      have h11 : ENNReal.ofReal (m / 6) < ENNReal.ofReal m := hiff.mpr h10
      exact h11
    exact not_le.mpr h9 (le_trans hA_ge h6)
  -- F(-n) → 0 as n → ∞
  have hF_bot : ∃ (M : ℕ), F (-(M : ℝ)) < m6 := by
    let f : ℕ → Set Point := fun n => A ∩ {x | coord x ≤ -(n : ℝ)}
    have hf_dir : Directed (· ⊇ ·) f := by
      intro m n
      use max m n
      constructor
      · intro x hx
        have hcoord : coord x ≤ -(max m n : ℝ) := by simpa using hx.2
        have h' : -(max m n : ℝ) ≤ -(m : ℝ) := by
          have h : (max m n : ℝ) ≥ (m : ℝ) := le_max_left _ _
          linarith
        exact ⟨hx.1, le_trans hcoord h'⟩
      · intro x hx
        have hcoord : coord x ≤ -(max m n : ℝ) := by simpa using hx.2
        have h' : -(max m n : ℝ) ≤ -(n : ℝ) := by
          have h : (max m n : ℝ) ≥ (n : ℝ) := le_max_right _ _
          linarith
        exact ⟨hx.1, le_trans hcoord h'⟩
    have hf_meas : ∀ n, MeasureTheory.NullMeasurableSet (f n) ν := fun n =>
      (hA_meas.inter (hcoord_meas measurableSet_Iic)).nullMeasurableSet
    have hf_fin : ∃ n, ν (f n) ≠ ⊤ := ⟨0, ne_top_of_le_ne_top hA_lt_top
      (measure_mono (by intro x hx; exact hx.1))⟩
    have h1 : (⋂ n : ℕ, f n) = (∅ : Set Point) := by
      ext x
      simp only [f, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false]
      constructor
      · intro h
        have h2 : ∀ n : ℕ, coord x ≤ -(n : ℝ) := fun n => (h n).2
        obtain ⟨n, hn⟩ := exists_nat_ge (-coord x)
        have h3 : coord x ≤ -(n : ℝ) := h2 n
        have h4 : -(n : ℝ) ≤ coord x := by linarith
        have h5 : coord x ≤ -(n + 1 : ℝ) := by
          have h5' := h2 (n + 1)
          simpa [Nat.cast_add] using h5'
        linarith
      · intro h
        exfalso
        exact h
    have h4 : ν (⋂ n : ℕ, f n) = ⨅ n : ℕ, ν (f n) :=
      Directed.measure_iInter hf_meas hf_dir hf_fin
    have h3 : ν (⋂ n : ℕ, f n) = 0 := by rw [h1] <;> simp
    by_contra h5
    push Not at h5
    have h5' : ∀ n : ℕ, m6 ≤ F (-(n : ℝ)) := h5
    have h6 : m6 ≤ ⨅ n : ℕ, F (-(n : ℝ)) := le_iInf h5'
    have h7 : ⨅ n : ℕ, F (-(n : ℝ)) = ν (⋂ n : ℕ, f n) := h4.symm
    rw [h7] at h6
    rw [h3] at h6
    have h8 : (0 : ENNReal) < m6 := ENNReal.ofReal_pos.mpr hm6_pos
    exact not_le.mpr h8 h6
  -- ======================================================================
  -- Step 4: Define s0 = inf {s | F(s) ≥ m6}
  -- ======================================================================
  let S : Set ℝ := {s | F s ≥ m6}
  rcases hF_top with ⟨N, hN⟩
  rcases hF_bot with ⟨M, hM⟩
  have hS_nonempty : S.Nonempty := ⟨(N : ℝ), hN⟩
  have hS_bdd : BddBelow S := by
    use (-(M : ℝ))
    intro s hs
    by_contra h
    have h' : s < (-(M : ℝ)) := by linarith
    have h'' : F s ≤ F (-(M : ℝ)) := hF_mono (by linarith)
    have h3 : F s < m6 := lt_of_le_of_lt h'' hM
    exact not_le.mpr h3 hs
  let s0 : ℝ := sInf S
  have hs0_le : ∀ s ∈ S, s0 ≤ s := fun s hs => csInf_le hS_bdd hs
  have hF_gt_s0 : ∀ (s : ℝ), s > s0 → F s ≥ m6 := by
    intro s hs
    have h_not_lb : ¬(∀ t ∈ S, s ≤ t) := by
      intro hlb
      have h : s ≤ s0 := le_csInf hS_nonempty hlb
      linarith
    push Not at h_not_lb
    rcases h_not_lb with ⟨t, htS, hts⟩
    have h : t < s := by linarith
    exact le_trans htS (hF_mono (by linarith))
  -- Right-continuity at s0: F(s0) = inf_n F(s0 + 1/(n+1))
  let g : ℕ → Set Point := fun n => A ∩ {x | coord x ≤ s0 + 1 / (n + 1 : ℝ)}
  have hg_dir : Directed (· ⊇ ·) g := by
    intro m n
    use max m n
    have hmax1 : (m : ℝ) ≤ (max m n : ℝ) := le_max_left _ _
    have hmax2 : (n : ℝ) ≤ (max m n : ℝ) := le_max_right _ _
    constructor
    · intro x hx
      have hcoord : coord x ≤ s0 + 1 / ((max m n : ℝ) + 1) := by simpa using hx.2
      have hdiv : 1 / ((max m n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
        have hpos1 : 0 < (m : ℝ) + 1 := by positivity
        have hle : (m : ℝ) + 1 ≤ (max m n : ℝ) + 1 := by linarith
        exact one_div_le_one_div_of_le hpos1 hle
      have hresult : coord x ≤ s0 + 1 / ((m : ℝ) + 1) := by linarith
      exact ⟨hx.1, hresult⟩
    · intro x hx
      have hcoord : coord x ≤ s0 + 1 / ((max m n : ℝ) + 1) := by simpa using hx.2
      have hdiv : 1 / ((max m n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
        have hpos1 : 0 < (n : ℝ) + 1 := by positivity
        have hle : (n : ℝ) + 1 ≤ (max m n : ℝ) + 1 := by linarith
        exact one_div_le_one_div_of_le hpos1 hle
      have hresult : coord x ≤ s0 + 1 / ((n : ℝ) + 1) := by linarith
      exact ⟨hx.1, hresult⟩
  have hg_meas : ∀ n, MeasureTheory.NullMeasurableSet (g n) ν := fun n =>
    (hA_meas.inter (hcoord_meas measurableSet_Iic)).nullMeasurableSet
  have hg_fin : ∃ n, ν (g n) ≠ ⊤ := ⟨0, ne_top_of_le_ne_top hA_lt_top
    (measure_mono (by intro x hx; exact hx.1))⟩
  have hg_eq : (⋂ n : ℕ, g n) = A ∩ {x | coord x ≤ s0} := by
    ext x
    simp only [g, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      have hxA : x ∈ A := (h 0).1
      have hle : ∀ n : ℕ, coord x ≤ s0 + 1 / (n + 1 : ℝ) := fun n => (h n).2
      by_cases hcase : coord x ≤ s0
      · exact ⟨hxA, hcase⟩
      · have hgt : s0 < coord x := by linarith
        let ε : ℝ := coord x - s0
        have hε_pos : 0 < ε := by linarith
        obtain ⟨n, hn⟩ := exists_nat_ge (1 / ε)
        have h5 : (n : ℝ) ≥ 1 / ε := by exact_mod_cast hn
        have h6 : 1 / ((n : ℝ) + 1) < ε := by
          have h7 : (n : ℝ) + 1 > 1 / ε := by linarith
          have h8 : 0 < ε := hε_pos
          have h9 : 0 < 1 / ε := by positivity
          have h10 : 1 / ((n : ℝ) + 1) < 1 / (1 / ε) := one_div_lt_one_div_of_lt h9 h7
          have h11 : 1 / (1 / ε) = ε := by field_simp [h8.ne'] <;> ring
          rw [h11] at h10
          exact h10
        have h10 := hle n
        linarith
    · rintro ⟨hxA, hle⟩
      intro n
      have h : coord x ≤ s0 + 1 / (n + 1 : ℝ) := by
        have h2 : 0 < 1 / (n + 1 : ℝ) := by positivity
        linarith
      exact ⟨hxA, h⟩
  have hF_right_cont_s0 : F s0 = ⨅ n : ℕ, F (s0 + 1 / (n + 1 : ℝ)) := by
    have h4 : ν (⋂ n : ℕ, g n) = ⨅ n : ℕ, ν (g n) :=
      Directed.measure_iInter hg_meas hg_dir hg_fin
    have h5 : ν (A ∩ {x | coord x ≤ s0}) = ν (⋂ n : ℕ, g n) := by
      rw [hg_eq]
    simpa [F, g] using h5.trans h4
  have hF_s0 : F s0 ≥ m6 := by
    rw [hF_right_cont_s0]
    apply le_iInf
    intro n
    have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
    have hgt : s0 < s0 + 1 / (n + 1 : ℝ) := by linarith
    exact hF_gt_s0 (s0 + 1 / (n + 1 : ℝ)) hgt
  -- ======================================================================
  -- Step 5: Bound ν({coord < s0}) ≤ m6
  -- ======================================================================
  let E_less : Set Point := A ∩ {x | coord x < s0}
  let hseq : ℕ → Set Point := fun n => A ∩ {x | coord x ≤ s0 - 1 / (n + 1 : ℝ)}
  have hh_mono : Monotone hseq := by
    intro m n hmn
    intro x hx
    have hcoord : coord x ≤ s0 - 1 / ((m : ℝ) + 1) := by simpa using hx.2
    have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      have hpos1 : 0 < (m : ℝ) + 1 := by positivity
      have hle : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
        have h : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
        linarith
      exact one_div_le_one_div_of_le hpos1 hle
    have hresult : coord x ≤ s0 - 1 / ((n : ℝ) + 1) := by linarith
    exact ⟨hx.1, hresult⟩
  have hE_less_union : E_less = ⋃ n : ℕ, hseq n := by
    ext x
    simp only [E_less, hseq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, hlt⟩
      have hε : 0 < s0 - coord x := by linarith
      obtain ⟨n, hn⟩ := exists_nat_ge (1 / (s0 - coord x) - 1)
      have h5 : (n : ℝ) ≥ 1 / (s0 - coord x) - 1 := by exact_mod_cast hn
      have h6 : 1 / ((n : ℝ) + 1) ≤ s0 - coord x := by
        have h7 : (n : ℝ) + 1 ≥ 1 / (s0 - coord x) := by linarith
        have h8 : 0 < s0 - coord x := hε
        calc 1 / ((n : ℝ) + 1) ≤ 1 / (1 / (s0 - coord x)) := by gcongr
          _ = s0 - coord x := by field_simp [h8.ne'] <;> ring
      exact ⟨n, hx, by linarith⟩
    · rintro ⟨n, hx, hle⟩
      have h9 : 0 < 1 / (n + 1 : ℝ) := by positivity
      exact ⟨hx, by linarith⟩
  have hE_less_eq : ν E_less ≤ m6 := by
    rw [hE_less_union]
    have h2 : ν (⋃ n : ℕ, hseq n) = ⨆ n : ℕ, ν (hseq n) := hh_mono.measure_iUnion
    rw [h2]
    apply iSup_le
    intro n
    have hlt : s0 - 1 / (n + 1 : ℝ) < s0 := by
      have h : 0 < 1 / (n + 1 : ℝ) := by positivity
      linarith
    have h_notinS : ¬(F (s0 - 1 / (n + 1 : ℝ)) ≥ m6) := by
      intro h
      have h' : s0 - 1 / (n + 1 : ℝ) ∈ S := h
      have h'' : s0 ≤ s0 - 1 / (n + 1 : ℝ) := hs0_le _ h'
      linarith
    have h_lt : F (s0 - 1 / (n + 1 : ℝ)) < m6 := lt_of_not_ge h_notinS
    exact le_of_lt h_lt
  -- ======================================================================
  -- Step 6: Prove F(s0 + ρ) ≤ ν(A) - m6 by contradiction
  -- ======================================================================
  let μ : ℝ := (ν A).toReal
  have hμ_ge_m : μ ≥ m := by
    have h : (ν A).toReal ≥ (ENNReal.ofReal m).toReal :=
      ENNReal.toReal_mono hA_lt_top hA_ge
    have h2 : (ENNReal.ofReal m).toReal = m := by
      rw [ENNReal.toReal_ofReal (by linarith)]
    rw [h2] at h; exact h
  have hμ_pos : 0 < μ := by linarith
  have hdiv_ne_top : (ν A) / 3 ≠ ⊤ := by
    have h : (ν A) / 3 ≤ ν A := by
      have h2 : (ν A) / 3 = ν A * (1 / 3 : ENNReal) := by
        simp [div_eq_mul_inv]
      rw [h2]
      have h3 : (1 / 3 : ENNReal) ≤ 1 := by norm_num
      have h4 : ν A * (1 / 3 : ENNReal) ≤ ν A * (1 : ENNReal) := by
        exact mul_le_mul_right h3 (ν A)
      simpa using h4
    exact ne_top_of_le_ne_top hA_lt_top h
  have h_nonconc_real : ∀ (x : Point), (ν (A ∩ ball x ρ)).toReal ≤ μ / 3 := by
    intro x
    have h : ν (A ∩ ball x ρ) ≤ (ν A) / 3 := h_nonconc x
    have h2 : (ν (A ∩ ball x ρ)).toReal ≤ ((ν A) / 3).toReal :=
      ENNReal.toReal_mono hdiv_ne_top h
    simpa [μ] using h2
  have h_main : F (s0 + ρ) ≤ ν A - m6 := by
    by_contra h
    have h' : F (s0 + ρ) > ν A - m6 := lt_of_not_ge h
    have h_fin1 : F (s0 + ρ) ≠ ⊤ :=
      ne_top_of_le_ne_top hA_lt_top (measure_mono (by intro x hx; exact hx.1))
    have h_a_ne_top : (ν A - m6) ≠ ⊤ := ne_top_of_le_ne_top hA_lt_top tsub_le_self
    have h_real_gt : ((ν A - m6).toReal) < (F (s0 + ρ)).toReal := by
      have h_iff : (ν A - m6).toReal < (F (s0 + ρ)).toReal ↔ ν A - m6 < F (s0 + ρ) :=
        ENNReal.toReal_lt_toReal h_a_ne_top h_fin1
      exact h_iff.mpr h'
    have h5 : ((ν A - m6).toReal) = μ - m / 6 := by
      have h6 : m6 ≤ ν A := le_trans (by simpa using hF_s0) (measure_mono (by intro x hx; exact hx.1))
      have h7 : m6 + (ν A - m6) = ν A := by
        exact add_tsub_cancel_of_le h6
      have hsum_ne_top : m6 + (ν A - m6) ≠ ⊤ := by
        rw [h7] <;> exact hA_lt_top
      have h8 : (m6 + (ν A - m6)).toReal = m6.toReal + (ν A - m6).toReal :=
        ENNReal.toReal_add hm6_ne_top h_a_ne_top
      have h9 : (ν A).toReal = m6.toReal + (ν A - m6).toReal := by
        rw [←h8, h7]
      have h10 : m6.toReal = m / 6 := by
        simp [m6, ENNReal.toReal_ofReal] <;> linarith
      linarith
    rw [h5] at h_real_gt
    let E_seg : Set Point := A ∩ {x | s0 ≤ coord x ∧ coord x ≤ s0 + ρ}
    have hE_seg_meas : MeasurableSet E_seg := by
      apply hA_meas.inter
      exact hcoord_meas measurableSet_Icc
    have hE_seg_eq : E_seg = (A ∩ {x | coord x ≤ s0 + ρ}) \ E_less := by
      ext x
      simp only [E_seg, E_less, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_diff]
      constructor
      · rintro ⟨hx, h1, h2⟩
        have h3 : ¬(x ∈ A ∧ coord x < s0) := by
          intro hconj
          have h4 : coord x < s0 := hconj.2
          linarith
        exact ⟨⟨hx, h2⟩, h3⟩
      · rintro ⟨⟨hx, h2⟩, h3⟩
        have h4 : ¬(coord x < s0) := by
          intro hlt; exact h3 ⟨hx, hlt⟩
        have h5 : s0 ≤ coord x := by linarith
        exact ⟨hx, h5, h2⟩
    have hE_less_ne_top : ν E_less ≠ ⊤ :=
      ne_top_of_le_ne_top hA_lt_top (measure_mono (by intro x hx; exact hx.1))
    have hE_seg_meas_real : (ν E_seg).toReal =
        (F (s0 + ρ)).toReal - (ν E_less).toReal := by
      rw [hE_seg_eq]
      have hsub : E_less ⊆ (A ∩ {x | coord x ≤ s0 + ρ}) := by
        intro x hx
        have hlt : coord x < s0 := by simpa using hx.2
        have hle : coord x ≤ s0 + ρ := by linarith [hρ]
        exact ⟨hx.1, hle⟩
      have h_disj : Disjoint E_less E_seg := by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        have h1 : coord x < s0 := hx1.2
        have h2 : s0 ≤ coord x := hx2.2.1
        linarith
      have h_union : (A ∩ {x | coord x ≤ s0 + ρ}) = E_less ∪ E_seg := by
        ext x
        simp only [E_less, E_seg, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨hx, hle⟩
          by_cases h : coord x < s0
          · exact Or.inl ⟨hx, h⟩
          · have h' : s0 ≤ coord x := by linarith
            exact Or.inr ⟨hx, h', hle⟩
        · rintro (h | h)
          · have hlt : coord x < s0 := h.2
            have hle : coord x ≤ s0 + ρ := by linarith [hρ]
            exact ⟨h.1, hle⟩
          · exact ⟨h.1, h.2.2⟩
      have h9 : ν (A ∩ {x | coord x ≤ s0 + ρ}) = ν E_less + ν E_seg := by
        rw [h_union]
        exact measure_union h_disj hE_seg_meas
      have hE_seg_ne_top : ν E_seg ≠ ⊤ :=
        ne_top_of_le_ne_top hA_lt_top (measure_mono (by intro y hy; exact hy.1))
      have h10 : (ν (A ∩ {x | coord x ≤ s0 + ρ})).toReal =
          (ν E_less).toReal + (ν E_seg).toReal := by
        rw [h9]
        exact ENNReal.toReal_add hE_less_ne_top hE_seg_ne_top
      have hF_eq : F (s0 + ρ) = ν (A ∩ {x | coord x ≤ s0 + ρ}) := by rfl
      have h_left : (A ∩ {x | coord x ≤ s0 + ρ}) \ E_less = E_seg := hE_seg_eq.symm
      rw [h_left, hF_eq, h10] <;> ring
    have hE_less_real : (ν E_less).toReal ≤ m / 6 := by
      have h : ν E_less ≤ m6 := hE_less_eq
      have h' : (ν E_less).toReal ≤ m6.toReal := ENNReal.toReal_mono hm6_ne_top h
      have hmt : m6.toReal = m / 6 := by
        simp [m6, ENNReal.toReal_ofReal] <;> linarith
      rw [hmt] at h'
      exact h'
    have hE_seg_gt : (ν E_seg).toReal > μ / 3 := by
      rw [hE_seg_meas_real]
      have h1 : (F (s0 + ρ)).toReal > μ - m / 6 := h_real_gt
      have h2 : (ν E_less).toReal ≤ m / 6 := hE_less_real
      have h5 : (F (s0 + ρ)).toReal - (ν E_less).toReal > μ - m / 3 := by
        linarith
      have h6 : μ - m / 3 ≥ μ / 3 := by
        have h7 : μ ≥ m := hμ_ge_m
        have h8 : 0 < m := hm
        linarith
      exact lt_of_le_of_lt h6 h5
    let p0 : Point := p + (s0 + ρ / 2) • v
    have hp0 : p0 ∈ L.toAffine := by
      have h : (s0 + ρ / 2) • v ∈ V := V.smul_mem (s0 + ρ / 2) hv_V
      have h' : (s0 + ρ / 2) • v +ᵥ p ∈ L.toAffine := L.toAffine.vadd_mem_of_mem_direction h hp
      have h_eq : (s0 + ρ / 2) • v +ᵥ p = p0 := by
        simp [p0, vadd_eq_add] <;> abel
      rw [h_eq] at h'
      exact h'
    have hcoord_p0 : coord p0 = s0 + ρ / 2 := by
      rw [hcoord_def p0]
      have h : p0 - p = (s0 + ρ / 2) • v := by simp [p0] <;> abel
      rw [h]
      have h6 : inner ℝ ((s0 + ρ / 2) • v) v = (s0 + ρ / 2) * inner ℝ v v := by exact real_inner_smul_left v v (s0 + ρ / 2)
      rw [h6, real_inner_self_eq_norm_sq, hv_norm] <;> ring
    have hE_seg_sub : E_seg ⊆ A ∩ ball p0 ρ := by
      intro x hx
      have hxA : x ∈ A := hx.1
      have hx1 : s0 ≤ coord x := hx.2.1
      have hx2 : coord x ≤ s0 + ρ := hx.2.2
      have hcoord_bound : |coord x - coord p0| ≤ ρ / 2 := by
        rw [hcoord_p0]
        have h1 : coord x - (s0 + ρ / 2) ≤ ρ / 2 := by linarith
        have h2 : -(ρ / 2) ≤ coord x - (s0 + ρ / 2) := by linarith
        exact abs_le.mpr ⟨h2, h1⟩
      have hxtube : x ∈ tube r L := hA_sub hxA
      have hinball : x ∈ ball p0 ρ := h_geom p0 hp0 x hxtube hcoord_bound
      exact ⟨hxA, hinball⟩
    have hball_ne_top : ν (A ∩ ball p0 ρ) ≠ ⊤ :=
      ne_top_of_le_ne_top hA_lt_top (measure_mono (by intro y hy; exact hy.1))
    have h_final1 : (ν E_seg).toReal ≤ (ν (A ∩ ball p0 ρ)).toReal :=
      ENNReal.toReal_mono hball_ne_top (measure_mono hE_seg_sub)
    have h_final : (ν E_seg).toReal ≤ μ / 3 :=
      le_trans h_final1 (h_nonconc_real p0)
    linarith
  -- ======================================================================
  -- Step 7: Define Y1, Y2 and verify all properties
  -- ======================================================================
  let Y1 : Set Point := A ∩ {x | coord x ≤ s0}
  let Y2 : Set Point := A ∩ {x | coord x ≥ s0 + ρ}
  have hY1_meas : MeasurableSet Y1 := hA_meas.inter (hcoord_meas measurableSet_Iic)
  have hY2_meas : MeasurableSet Y2 := hA_meas.inter (hcoord_meas measurableSet_Ici)
  have hY1_sub : Y1 ⊆ A := by intro x hx; exact hx.1
  have hY2_sub : Y2 ⊆ A := by intro x hx; exact hx.1
  have hY1_meas_val : ν Y1 ≥ m6 := by simpa [Y1, F] using hF_s0
  have hY2_meas_val : ν Y2 ≥ m6 := by
    let Z : Set Point := A ∩ {x | coord x < s0 + ρ}
    have hZ_sub : Z ⊆ A := by intro x hx; exact hx.1
    have hZ_ne_top : ν Z ≠ ⊤ := ne_top_of_le_ne_top hA_lt_top (measure_mono hZ_sub)
    have h1 : Y2 = A \ Z := by
      ext x
      simp only [Y2, Z, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_diff]
      constructor
      · rintro ⟨hx, hge⟩
        have hlt : ¬(x ∈ A ∧ coord x < s0 + ρ) := by
          intro hconj
          have : coord x < s0 + ρ := hconj.2
          linarith
        exact ⟨hx, hlt⟩
      · rintro ⟨hx, hlt⟩
        have hge : coord x ≥ s0 + ρ := by
          by_contra hlt2
          have hcont : coord x < s0 + ρ := by linarith
          exact hlt ⟨hx, hcont⟩
        exact ⟨hx, hge⟩
    rw [h1]
    have hZ_meas : MeasurableSet Z :=
      hA_meas.inter (hcoord_meas measurableSet_Iio)
    have h3 : ν (A \ Z) = ν A - ν Z := by
      rw [measure_sdiff hZ_sub hZ_meas.nullMeasurableSet hZ_ne_top]
    rw [h3]
    have h4 : ν Z ≤ F (s0 + ρ) := by
      apply measure_mono
      intro x hx
      have h5 : coord x < s0 + ρ := hx.2
      have h6 : coord x ≤ s0 + ρ := by linarith
      exact ⟨hx.1, h6⟩
    have h5 : ν A - ν Z ≥ ν A - F (s0 + ρ) := by gcongr
    have h_m6_le : m6 ≤ ν A := le_trans (by simpa using hF_s0) (measure_mono (by intro x hx; exact hx.1))
    have h6 : F (s0 + ρ) + m6 ≤ ν A := by
      have h7 : F (s0 + ρ) ≤ ν A - m6 := h_main
      exact (ENNReal.le_sub_iff_add_le_right hm6_ne_top h_m6_le).mp h7
    have hF_ne_top : F (s0 + ρ) ≠ ⊤ :=
      ne_top_of_le_ne_top hA_lt_top (measure_mono (by intro x hx; exact hx.1))
    have hF_le : F (s0 + ρ) ≤ ν A :=
      measure_mono (by intro x hx; exact hx.1)
    have h7 : m6 ≤ ν A - F (s0 + ρ) := by
      have h8 : F (s0 + ρ) + m6 ≤ ν A := h6
      have h9 : m6 + F (s0 + ρ) ≤ ν A := by
        rw [add_comm] at h8; exact h8
      exact (ENNReal.le_sub_iff_add_le_right hF_ne_top hF_le).mpr h9
    exact le_trans h7 h5
  have h_separation : ∀ y1 ∈ Y1, ∀ y2 ∈ Y2, dist y1 y2 ≥ ρ := by
    intro y1 hy1 y2 hy2
    have h1 : coord y1 ≤ s0 := hy1.2
    have h2 : coord y2 ≥ s0 + ρ := hy2.2
    have h3 : |coord y2 - coord y1| ≥ ρ := by
      have h4 : 0 ≤ coord y2 - coord y1 := by linarith
      rw [abs_of_nonneg h4] <;> linarith
    have h5 : |coord y2 - coord y1| ≤ dist y2 y1 := hcoord_lipschitz y2 y1
    have h6 : dist y2 y1 = dist y1 y2 := dist_comm y2 y1
    rw [h6] at h5
    linarith
  exact ⟨Y1, Y2, hY1_meas, hY2_meas, hY1_sub, hY2_sub,
    hY1_meas_val, hY2_meas_val, h_separation⟩

/-- Bridge lemma: version of `two_separated_subsets_in_tube` that takes a raw
`AffineSubspace` with finrank 1 instead of a `Line2`. -/
lemma two_separated_subsets_in_tube_affine
    (ℓ : AffineSubspace ℝ Point) (hℓ : Module.finrank ℝ ℓ.direction = 1)
    (r ρ m : ℝ)
    (hr : 0 < r) (hρ : 0 < ρ) (hm : 0 < m)
    (h_width : r ≤ (Real.sqrt 3 / 2) * ρ)
    (ν : Measure Point) [IsProbabilityMeasure ν]
    (A : Set Point) (hA_meas : MeasurableSet A)
    (hA_sub : A ⊆ Metric.thickening r (ℓ : Set Point))
    (hA_ge : ν A ≥ ENNReal.ofReal m)
    (h_nonconc : ∀ (x : Point), ν (A ∩ ball x ρ) ≤ (ν A) / 3) :
    ∃ (Y1 Y2 : Set Point),
      MeasurableSet Y1 ∧ MeasurableSet Y2 ∧
      Y1 ⊆ A ∧ Y2 ⊆ A ∧
      ν Y1 ≥ ENNReal.ofReal (m / 6) ∧
      ν Y2 ≥ ENNReal.ofReal (m / 6) ∧
      ∀ y1 ∈ Y1, ∀ y2 ∈ Y2, dist y1 y2 ≥ ρ := by
  let L : Line2 := ⟨ℓ, hℓ⟩
  have h_tube_eq : tube r L = Metric.thickening r (ℓ : Set Point) := by
    rfl
  have hA_sub' : A ⊆ tube r L := by
    rw [h_tube_eq]
    exact hA_sub
  exact two_separated_subsets_in_tube L r ρ m hr hρ hm h_width ν A hA_meas hA_sub' hA_ge h_nonconc

end RadialBootstrapping

end
