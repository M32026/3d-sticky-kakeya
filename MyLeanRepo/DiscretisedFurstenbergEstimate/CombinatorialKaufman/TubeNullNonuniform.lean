module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Tube-null lemma: Non-uniform version

Non-uniform quantitative Rademacher: differentiability a.e. + Vitali covering.
-/

noncomputable section

open MeasureTheory Set Metric Filter Finset

namespace CombinatorialKaufman.TubeNull

/-- If f has derivative d at x, then for any ε > 0, there exists δ > 0 such that
for all intervals [a,b] containing x with b-a < δ, f is ε-linear on [a,b]. -/
lemma differentiable_implies_epsilon_linear
    {f : ℝ → ℝ} {d x : ℝ} (hderiv : HasDerivAt f d x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ), 0 < δ ∧
      ∀ (a b : ℝ), a ≤ x → x ≤ b → b - a < δ →
        EpsilonLinear f ε a b := by
  have h_orig : Filter.Tendsto
      (fun y : ℝ ↦ ‖y - x‖⁻¹ * ‖f y - f x - (y - x) • d‖) (nhds x) (nhds 0) :=
    (hasDerivAt_iff_tendsto (f := f) (f' := d) (x := x)).mp hderiv
  have h_fn_eq : (fun y : ℝ ↦ ‖y - x‖⁻¹ * ‖f y - f x - (y - x) • d‖) =
      (fun y : ℝ ↦ |f y - f x - d * (y - x)| / |y - x|) := by
    funext y
    simp [smul_eq_mul] <;> ring_nf
  have h_tendsto : Filter.Tendsto
      (fun y : ℝ ↦ |f y - f x - d * (y - x)| / |y - x|) (nhds x) (nhds 0) := by
    rw [←h_fn_eq]
    exact h_orig
  have h_ed : ∀ (η : ℝ), 0 < η → ∃ (δ : ℝ), 0 < δ ∧
      ∀ (y : ℝ), |y - x| < δ → |f y - f x - d * (y - x)| ≤ η * |y - x| := by
    intro η hη
    have h1 : ∀ᶠ (y : ℝ) in nhds x,
        dist (|f y - f x - d * (y - x)| / |y - x|) 0 < η :=
      h_tendsto.eventually (Metric.ball_mem_nhds 0 hη)
    rcases Metric.mem_nhds_iff.mp h1 with ⟨δ, hδ_pos, hδ⟩
    refine ⟨δ, hδ_pos, ?_⟩
    intro y hy
    by_cases h : y = x
    · rw [h] <;> simp
    · have h' : y - x ≠ 0 := by
        intro h''; apply h; linarith
      have h_abs_pos : 0 < |y - x| := abs_pos.mpr h'
      have h_dist : dist y x < δ := by
        simpa [dist_eq_norm] using hy
      have h4 : dist (|f y - f x - d * (y - x)| / |y - x|) 0 < η :=
        hδ (show y ∈ Metric.ball x δ from h_dist)
      have h5 : |f y - f x - d * (y - x)| / |y - x| < η := by
        have h6 : dist (|f y - f x - d * (y - x)| / |y - x|) 0 =
            |f y - f x - d * (y - x)| / |y - x| := by
          simp [dist_eq_norm] <;> positivity
        rw [h6] at h4
        exact h4
      have h7 : |f y - f x - d * (y - x)| < η * |y - x| := by
        have h8 : |f y - f x - d * (y - x)| =
            (|f y - f x - d * (y - x)| / |y - x|) * |y - x| := by
          rw [div_mul_cancel₀ _ h_abs_pos.ne'] <;> ring
        rw [h8]
        gcongr
      exact le_of_lt h7
  rcases h_ed (ε / 3) (by linarith) with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro a b ha hx hlen
  have hab : a ≤ b := le_trans ha hx
  by_cases hba : b - a = 0
  · have h_ab : a = b := by linarith
    intro z hz
    have h_z_a : z = a := by linarith [hz.1, hz.2, h_ab]
    rw [h_z_a, h_ab]
    simp [chordValue, chordSlope] <;> norm_num
  · have hba_pos : 0 < b - a := by
      have h : 0 ≤ b - a := by linarith
      exact lt_of_le_of_ne h (Ne.symm hba)
    intro z hz
    have hz1 : a ≤ z := hz.1
    have hz2 : z ≤ b := hz.2
    have h_za_bound : |z - x| ≤ b - a := by
      rw [abs_le] <;> constructor <;> linarith
    have h_aa_bound : |a - x| ≤ b - a := by
      rw [abs_le] <;> constructor <;> linarith
    have h_ba_bound : |b - x| ≤ b - a := by
      rw [abs_le] <;> constructor <;> linarith
    have h_za2_bound : |z - a| ≤ b - a := by
      rw [abs_le] <;> constructor <;> linarith
    have h1 : |f z - f x - d * (z - x)| ≤ (ε / 3) * |z - x| := hδ z (by linarith)
    have h2 : |f a - f x - d * (a - x)| ≤ (ε / 3) * |a - x| := hδ a (by linarith)
    have h3 : |f b - f x - d * (b - x)| ≤ (ε / 3) * |b - x| := hδ b (by linarith)
    have h4 : |f b - f a - d * (b - a)| ≤ (ε / 3) * (b - a) := by
      have h5 : f b - f a - d * (b - a) =
          (f b - f x - d * (b - x)) - (f a - f x - d * (a - x)) := by ring
      rw [h5]
      have h6 : |b - x| + |a - x| = b - a := by
        have h7 : 0 ≤ b - x := by linarith
        have h8 : 0 ≤ x - a := by linarith
        have h9 : |b - x| = b - x := by rw [abs_of_nonneg] <;> linarith
        have h10 : |a - x| = x - a := by
          have h11 : a - x = -(x - a) := by ring
          rw [h11, abs_neg, abs_of_nonneg] <;> linarith
        linarith
      have h_abs : |(f b - f x - d * (b - x)) - (f a - f x - d * (a - x))| ≤
          |f b - f x - d * (b - x)| + |f a - f x - d * (a - x)| := by
        set u := f b - f x - d * (b - x)
        set v := f a - f x - d * (a - x)
        have h : |u - v| ≤ |u| + |v| := by
          calc |u - v|
            = |u + (-v)| := by ring_nf
          _ ≤ |u| + |(-v)| := by exact abs_add_le u (-v)
          _ = |u| + |v| := by rw [abs_neg]
        exact h
      calc _
        ≤ |f b - f x - d * (b - x)| + |f a - f x - d * (a - x)| := h_abs
      _ ≤ (ε / 3) * |b - x| + (ε / 3) * |a - x| := by gcongr
      _ = (ε / 3) * (|b - x| + |a - x|) := by ring
      _ = (ε / 3) * (b - a) := by rw [h6]
    have h_slope_diff : |chordSlope f a b - d| ≤ ε / 3 := by
      dsimp only [chordSlope]
      have h : |(f b - f a) / (b - a) - d| =
          |f b - f a - d * (b - a)| / |b - a| := by
        have h9 : (f b - f a) / (b - a) - d =
            (f b - f a - d * (b - a)) / (b - a) := by
          field_simp [hba] <;> ring
        rw [h9, abs_div] <;> rfl
      rw [h]
      have h10 : |b - a| = b - a := by rw [abs_of_nonneg] <;> linarith
      rw [h10]
      have h11 : |f b - f a - d * (b - a)| / (b - a) ≤ ε / 3 := by
        calc |f b - f a - d * (b - a)| / (b - a)
          ≤ ((ε / 3) * (b - a)) / (b - a) := by gcongr <;> linarith
        _ = ε / 3 := by field_simp [hba] <;> ring
      exact h11
    have h_eq1 : f z - chordValue f a b z =
        (f z - f x - d * (z - x)) - (f a - f x - d * (a - x)) -
          (chordSlope f a b - d) * (z - a) := by
      simp [chordValue, chordSlope] <;> ring
    rw [h_eq1]
    set u := f z - f x - d * (z - x) with hu
    set v := f a - f x - d * (a - x) with hv
    set w := (chordSlope f a b - d) * (z - a) with hw
    have h_tri : |u - v - w| ≤ |u| + |v| + |w| := by
      have h1 : |u - v - w| = |(u - v) + (-w)| := by ring_nf
      rw [h1]
      have h2 : |(u - v) + (-w)| ≤ |u - v| + |(-w)| := by exact abs_add_le (u - v) (-w)
      have h3 : |(-w)| = |w| := by rw [abs_neg]
      have h4 : |u - v| ≤ |u| + |v| := by
        have h5 : |u - v| = |u + (-v)| := by ring_nf
        rw [h5]
        have h6 : |u + (-v)| ≤ |u| + |(-v)| := by exact abs_add_le u (-v)
        rw [show |(-v)| = |v| from by rw [abs_neg]] at h6
        exact h6
      rw [h3] at h2
      linarith
    have h4 : |u| + |v| + |w| ≤
        (ε / 3) * (b - a) + (ε / 3) * (b - a) + (ε / 3) * (b - a) := by
      have h5 : |u| ≤ (ε / 3) * (b - a) := by
        calc |u| ≤ (ε / 3) * |z - x| := h1
             _ ≤ (ε / 3) * (b - a) := by
              exact mul_le_mul_of_nonneg_left h_za_bound (by linarith)
      have h6 : |v| ≤ (ε / 3) * (b - a) := by
        calc |v| ≤ (ε / 3) * |a - x| := h2
             _ ≤ (ε / 3) * (b - a) := by
              exact mul_le_mul_of_nonneg_left h_aa_bound (by linarith)
      have h7 : |w| ≤ (ε / 3) * (b - a) := by
        calc |w| = |chordSlope f a b - d| * |z - a| := by rw [hw, abs_mul]
             _ ≤ (ε / 3) * |z - a| := by gcongr
             _ ≤ (ε / 3) * (b - a) := by
              exact mul_le_mul_of_nonneg_left h_za2_bound (by linarith)
      linarith
    calc |u - v - w|
      ≤ |u| + |v| + |w| := h_tri
    _ ≤ (ε / 3) * (b - a) + (ε / 3) * (b - a) + (ε / 3) * (b - a) := h4
    _ = ε * (b - a) := by ring

/-- Non-uniform quantitative Rademacher: for each fixed monotone f on [a,b],
there exist finitely many disjoint ε-linear intervals covering all but ε*(b-a),
each of length at least τ_f*(b-a). -/
lemma tubeNull_nonuniform {ε : ℝ} (hε : 0 < ε) :
    ∀ (f : ℝ → ℝ) (a b : ℝ),
      a < b →
      MonotoneOn f (Set.Icc a b) →
      ∃ (τ : ℝ), 0 < τ ∧ ∃ (I : Finset (ℝ × ℝ)),
        (∀ p ∈ I, EpsilonLinear f ε p.1 p.2) ∧
        (∀ p ∈ I, p.2 - p.1 ≥ τ * (b - a)) ∧
        (∀ p ∈ I, a ≤ p.1 ∧ p.2 ≤ b) ∧
        (∀ p ∈ I, ∀ q ∈ I, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1) ∧
        (b - a) - ∑ p ∈ I, (p.2 - p.1) ≤ ε * (b - a) := by
  intro f a b hab h_mono
  -- Step 1: f is differentiable a.e. on (a,b)
  have h_diff_ae : ∀ᵐ (x : ℝ) ∂volume.restrict (Set.Icc a b),
      DifferentiableWithinAt ℝ f (Set.Icc a b) x :=
    h_mono.ae_differentiableWithinAt measurableSet_Icc
  have h2 : ∀ᵐ (x : ℝ), x ∈ Set.Ioo a b → DifferentiableAt ℝ f x := by
    have h3 : ∀ᵐ (x : ℝ) ∂volume.restrict (Set.Icc a b),
        DifferentiableWithinAt ℝ f (Set.Icc a b) x := h_diff_ae
    have h4 : ∀ᵐ (x : ℝ), x ∈ Set.Icc a b → DifferentiableWithinAt ℝ f (Set.Icc a b) x := by
      have h41 : ∀ᵐ (x : ℝ) ∂volume.restrict (Set.Icc a b), DifferentiableWithinAt ℝ f (Set.Icc a b) x := h3
      exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp h41
    filter_upwards [h4] with x hx
    intro h_x_in
    have h5 : DifferentiableWithinAt ℝ f (Set.Icc a b) x :=
      hx ⟨h_x_in.1.le, h_x_in.2.le⟩
    have h6 : Set.Icc a b ∈ nhds x := Icc_mem_nhds h_x_in.1 h_x_in.2
    exact h5.differentiableAt h6
  let s : Set ℝ := {x ∈ Set.Ioo a b | DifferentiableAt ℝ f x}
  have h_null_sdiff : volume (Set.Ioo a b \ s) = 0 := by
    have h12 : ∀ᵐ (x : ℝ), x ∈ Set.Ioo a b → DifferentiableAt ℝ f x := h2
    have h13 : volume {x : ℝ | x ∈ Set.Ioo a b ∧ ¬DifferentiableAt ℝ f x} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [h12] with x hx
      simpa using hx
    have h14 : {x : ℝ | x ∈ Set.Ioo a b ∧ ¬DifferentiableAt ℝ f x} = Set.Ioo a b \ s := by
      ext y; simp [s, Set.mem_setOf_eq] <;> tauto
    rw [←h14]
    exact h13
  have h4_null : volume (Set.Icc a b \ s) = 0 := by
    have h5 : Set.Icc a b \ s ⊆ {a, b} ∪ (Set.Ioo a b \ s) := by
      intro x hx
      have h6 : x ∈ Set.Icc a b := hx.1
      have h7 : x ∉ s := hx.2
      by_cases h8 : x = a
      · exact Or.inl (by simp [h8])
      · by_cases h9 : x = b
        · exact Or.inl (by simp [h9])
        · have h10 : a < x := by
            exact lt_of_le_of_ne h6.1 (Ne.symm h8)
          have h11 : x < b := by
            exact lt_of_le_of_ne h6.2 h9
          have h12 : x ∈ Set.Ioo a b := ⟨h10, h11⟩
          exact Or.inr ⟨h12, h7⟩
    have h13 : volume ({a, b} : Set ℝ) = 0 := by
      have h14 : volume ({a} : Set ℝ) = 0 := measure_singleton a
      have h15 : volume ({b} : Set ℝ) = 0 := measure_singleton b
      have h16 : ({a, b} : Set ℝ) = {a} ∪ {b} := by
        ext y; simp [or_comm]
      rw [h16, measure_union_null h14 h15]
    have h14 : volume (({a, b} : Set ℝ) ∪ (Set.Ioo a b \ s)) = 0 :=
      measure_union_null h13 h_null_sdiff
    exact measure_mono_null h5 h14

  -- Step 2: Build the Vitali cover family
  let t : Set (ℝ × ℝ) :=
    {p | a ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b ∧ EpsilonLinear f ε p.1 p.2}

  have hB : ∀ (p : ℝ × ℝ), p ∈ t →
      Set.Icc p.1 p.2 ⊆ closedBall p.1 (p.2 - p.1) := by
    intro p hp y hy
    have h1 : p.1 ≤ y := hy.1
    have h2 : y ≤ p.2 := hy.2
    have h3 : dist y p.1 ≤ p.2 - p.1 := by
      rw [Real.dist_eq, abs_of_nonneg (show 0 ≤ y - p.1 by linarith)] <;> linarith
    exact h3

  have hμB : ∀ (p : ℝ × ℝ), p ∈ t →
      volume (closedBall p.1 (3 * (p.2 - p.1))) ≤ (6 : ENNReal) * volume (Set.Icc p.1 p.2) := by
    intro p hp
    have hpos : 0 < p.2 - p.1 := by have h : p.1 < p.2 := hp.2.1; linarith
    simp only [Real.volume_closedBall, Real.volume_Icc]
    rw [show (6 : ENNReal) = ENNReal.ofReal 6 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num)]
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)]
    have h_abs : |3 * (p.2 - p.1)| = 3 * (p.2 - p.1) := by rw [abs_of_pos] <;> linarith
    simp [h_abs] <;> linarith

  have ht : ∀ (p : ℝ × ℝ), p ∈ t → (interior (Set.Icc p.1 p.2)).Nonempty := by
    intro p hp
    have h1 : p.1 < p.2 := hp.2.1
    refine ⟨(p.1 + p.2) / 2, ?_⟩
    have h2 : (p.1 + p.2) / 2 ∈ Set.Ioo p.1 p.2 := by constructor <;> linarith
    have h3 : Set.Ioo p.1 p.2 ⊆ interior (Set.Icc p.1 p.2) := by
      rw [interior_Icc] <;> exact Set.Subset.refl _
    exact h3 h2

  have h't : ∀ (p : ℝ × ℝ), p ∈ t → IsClosed (Set.Icc p.1 p.2) := by
    intro p _; exact isClosed_Icc

  -- Fine cover condition
  have hf_vitali : ∀ (x : ℝ), x ∈ s →
      Filter.Frequently (fun (ε' : ℝ) => ∃ (p : ℝ × ℝ), p ∈ t ∧ (p.2 - p.1) = ε' ∧ p.1 = x)
        (nhdsWithin 0 (Set.Ioi 0)) := by
    intro x hx
    have hx1 : a < x := hx.1.1
    have hx2 : x < b := hx.1.2
    have hx_diff : DifferentiableAt ℝ f x := hx.2
    have hderiv : HasDerivAt f (deriv f x) x := hx_diff.hasDerivAt
    rcases differentiable_implies_epsilon_linear hderiv hε with ⟨δ, hδ_pos, hδ⟩
    apply Eventually.frequently
    have evn_pos : ∀ᶠ (ε' : ℝ) in nhdsWithin 0 (Set.Ioi 0), 0 < ε' :=
      eventually_mem_of_tendsto_nhdsWithin (fun _ a ↦ a)
    have evn_bound {α : ℝ} (hα : 0 < α) : ∀ᶠ (ε' : ℝ) in nhdsWithin 0 (Set.Ioi 0), ε' < α := by
      have h : Set.Ioi 0 ∩ Set.Iio α ∈ nhdsWithin 0 (Set.Ioi 0) :=
        inter_mem_nhdsWithin _ (Iio_mem_nhds hα)
      filter_upwards [h] with ε' hε'
      exact hε'.2
    filter_upwards [evn_pos, evn_bound hδ_pos, evn_bound (show 0 < b - x by linarith)]
      with ε' hε'_pos hε'_ltδ hε'_ltbx
    let p : ℝ × ℝ := (x, x + ε')
    have h_p1 : a ≤ p.1 := by simp [p] <;> linarith
    have h_p2 : p.1 < p.2 := by simp [p] <;> linarith
    have h_p3 : p.2 ≤ b := by simp [p] <;> linarith
    have h_plen : p.2 - p.1 = ε' := by simp [p] <;> ring
    have h_eps : EpsilonLinear f ε p.1 p.2 :=
      hδ p.1 p.2 (by simp [p] <;> linarith) (by simp [p] <;> linarith)
        (by rw [h_plen] <;> exact hε'_ltδ)
    have hp_t : p ∈ t := ⟨h_p1, h_p2, h_p3, h_eps⟩
    exact ⟨p, hp_t, by simp [p], by simp [p]⟩

  -- Step 3: Apply Vitali covering theorem
  obtain ⟨u, hu_sub, hu_count, hu_disj, h_cover⟩ : ∃ (u : Set (ℝ × ℝ)), u ⊆ t ∧
      u.Countable ∧ u.PairwiseDisjoint (fun p : ℝ × ℝ => Set.Icc p.1 p.2) ∧
      volume (s \ ⋃ p ∈ u, Set.Icc p.1 p.2) = 0 := by
    apply Vitali.exists_disjoint_covering_ae' volume s t 6
      (Prod.snd - Prod.fst) Prod.fst (fun p : ℝ × ℝ => Set.Icc p.1 p.2)
    · exact hB
    · exact hμB
    · exact ht
    · exact h't
    · exact hf_vitali

  let B : (ℝ × ℝ) → Set ℝ := fun p => Set.Icc p.1 p.2

  -- Step 4: The union covers almost all of [a,b]
  have hB_sub : ∀ p ∈ u, B p ⊆ Set.Icc a b := by
    intro p hp
    have hpt : p ∈ t := hu_sub hp
    intro y hy
    exact ⟨by linarith [hpt.1, hy.1], by linarith [hpt.2.2.1, hy.2]⟩
  have h_union_sub : (⋃ p ∈ u, B p) ⊆ Set.Icc a b := by
    intro y hy
    rcases Set.mem_iUnion₂.mp hy with ⟨p, _, hy'⟩
    exact hB_sub p ‹_› hy'
  have h_cover2 : volume (Set.Icc a b \ (⋃ p ∈ u, B p)) = 0 := by
    have h1 : Set.Icc a b \ (⋃ p ∈ u, B p) ⊆ (Set.Icc a b \ s) ∪ (s \ (⋃ p ∈ u, B p)) := by
      intro x hx
      have h2 : x ∈ Set.Icc a b := hx.1
      by_cases h3 : x ∈ s
      · exact Or.inr ⟨h3, hx.2⟩
      · exact Or.inl ⟨h2, h3⟩
    have h4cover : volume (s \ (⋃ p ∈ u, B p)) = 0 := h_cover
    have h5 : volume ((Set.Icc a b \ s) ∪ (s \ (⋃ p ∈ u, B p))) = 0 :=
      measure_union_null h4_null h4cover
    exact measure_mono_null h1 h5

  -- Step 5: Countable additivity
  have hB_meas : ∀ p ∈ u, MeasurableSet (B p) := by
    intro p _; exact measurableSet_Icc
  have h_meas_union : MeasurableSet (⋃ p ∈ u, B p) :=
    MeasurableSet.biUnion hu_count (fun p _ => hB_meas p ‹_›)
  have h_meas_sdiff : MeasurableSet (Set.Icc a b \ (⋃ p ∈ u, B p)) :=
    measurableSet_Icc.diff h_meas_union
  have h_pairwise_subtype : Pairwise (fun (p q : {p // p ∈ u}) => Disjoint (B p.val) (B q.val)) := by
    intro p q hpq
    have hne : p.val ≠ q.val := Subtype.coe_ne_coe.mpr hpq
    exact hu_disj (x := p.val) p.prop (y := q.val) q.prop hne
  letI : Countable {p // p ∈ u} := Set.countable_coe_iff.mpr hu_count
  have hB_meas' : ∀ (p : {p // p ∈ u}), MeasurableSet (B p.val) := by
    intro p; exact hB_meas p.val p.prop
  have h_sum_ennreal : volume (⋃ p : {p // p ∈ u}, B p.val) = ∑' (p : {p // p ∈ u}), volume (B p.val) := by
    rw [measure_iUnion h_pairwise_subtype hB_meas']
  have h_iUnion_eq : (⋃ p ∈ u, B p) = (⋃ p : {p // p ∈ u}, B p.val) := by
    ext x; simp [Set.mem_iUnion]
  have h_vol_union : volume (⋃ p : {p // p ∈ u}, B p.val) = ENNReal.ofReal (b - a) := by
    have h6 : volume (Set.Icc a b) = ENNReal.ofReal (b - a) := by
      rw [Real.volume_Icc] <;> simp [hab.le] <;> ring
    rw [h_iUnion_eq] at h_union_sub
    rw [h_iUnion_eq] at h_cover2
    convert! h6 ▸ measure_eq_measure_of_null_sdiff h_union_sub h_cover2 using 2
    <;> simp
  have h9 : ∀ (p : {p // p ∈ u}), volume (B p.val) = ENNReal.ofReal (p.val.2 - p.val.1) := by
    intro p
    have h10 : p.val.1 < p.val.2 := (hu_sub p.prop).2.1
    dsimp only [B]
    rw [Real.volume_Icc] <;> simp [h10.le] <;> ring
  have h10 : ∑' (p : {p // p ∈ u}), volume (B p.val) =
      ∑' (p : {p // p ∈ u}), ENNReal.ofReal (p.val.2 - p.val.1) := by
    congr with p; exact h9 p
  have h_tsum_ennreal : ∑' (p : {p // p ∈ u}), ENNReal.ofReal (p.val.2 - p.val.1) =
      ENNReal.ofReal (b - a) := by
    rw [←h10, ←h_sum_ennreal, h_vol_union]
  have h11 : ∀ (p : {p // p ∈ u}), 0 ≤ p.val.2 - p.val.1 := by
    intro p; have h12 := (hu_sub p.prop).2.1; linarith
  have h_tsum_ne_top : (∑' (p : {p // p ∈ u}), ENNReal.ofReal (p.val.2 - p.val.1)) ≠ ⊤ := by
    rw [h_tsum_ennreal]; exact ENNReal.ofReal_ne_top
  have h_summable_toReal : Summable (fun (p : {p // p ∈ u}) => (ENNReal.ofReal (p.val.2 - p.val.1)).toReal) :=
    ENNReal.summable_toReal h_tsum_ne_top
  have h_eq_toReal : (fun (p : {p // p ∈ u}) => (ENNReal.ofReal (p.val.2 - p.val.1)).toReal) =
      (fun (p : {p // p ∈ u}) => p.val.2 - p.val.1) := by
    funext p
    rw [ENNReal.toReal_ofReal (h11 p)]
  have h_summable : Summable (fun (p : {p // p ∈ u}) => p.val.2 - p.val.1) := by
    rw [←h_eq_toReal]; exact h_summable_toReal
  have h_tsum_real : ∑' (p : {p // p ∈ u}), (p.val.2 - p.val.1) = b - a := by
    have h_eq1 : ENNReal.ofReal (∑' (p : {p // p ∈ u}), (p.val.2 - p.val.1)) =
        ∑' (p : {p // p ∈ u}), ENNReal.ofReal (p.val.2 - p.val.1) :=
      ENNReal.ofReal_tsum_of_nonneg h11 h_summable
    have h_eq2 : ENNReal.ofReal (∑' (p : {p // p ∈ u}), (p.val.2 - p.val.1)) = ENNReal.ofReal (b - a) := by
      rw [h_eq1, h_tsum_ennreal]
    have h_nonneg1 : 0 ≤ ∑' (p : {p // p ∈ u}), (p.val.2 - p.val.1) := tsum_nonneg h11
    have h_nonneg2 : 0 ≤ b - a := by linarith
    have h_toReal_eq : (ENNReal.ofReal (∑' (p : {p // p ∈ u}), (p.val.2 - p.val.1))).toReal =
        (ENNReal.ofReal (b - a)).toReal := by rw [h_eq2]
    simpa [ENNReal.toReal_ofReal h_nonneg1, ENNReal.toReal_ofReal h_nonneg2] using h_toReal_eq
  have h_hasSum : HasSum (fun (p : {p // p ∈ u}) => p.val.2 - p.val.1) (b - a) :=
    h_summable.hasSum_iff.mpr h_tsum_real

  -- Step 6: Extract finite subfamily
  set δ' : ℝ := ε * (b - a) with hδ'_def
  have hδ'_pos : 0 < δ' := by positivity
  have h_hasSum_approx : ∃ (s_finset : Finset {p // p ∈ u}), |∑ p ∈ s_finset, (p.val.2 - p.val.1) - (b - a)| < δ' := by
    have h_ev : ∀ᶠ (s : Finset {p // p ∈ u}) in Filter.atTop,
        dist (∑ p ∈ s, (p.val.2 - p.val.1)) (b - a) < δ' :=
      h_hasSum (Metric.ball_mem_nhds (b - a) hδ'_pos)
    rcases Filter.eventually_atTop.mp h_ev with ⟨s₀, hs₀⟩
    refine ⟨s₀, ?_⟩
    have h := hs₀ s₀ (by simp)
    have h' : |∑ p ∈ s₀, (p.val.2 - p.val.1) - (b - a)| < δ' := by
      have h_dist : dist (∑ p ∈ s₀, (p.val.2 - p.val.1)) (b - a) =
          |∑ p ∈ s₀, (p.val.2 - p.val.1) - (b - a)| := by
        rw [Real.dist_eq] <;> rfl
      rw [h_dist] at h
      exact h
    exact h'
  rcases h_hasSum_approx with ⟨s_finset, h_approx⟩
  let v : Finset (ℝ × ℝ) := Finset.image (fun p : {p // p ∈ u} => p.val) s_finset
  have h_inj : Set.InjOn (fun p : {p // p ∈ u} => p.val) s_finset := by
    intro p _ q _ h; exact Subtype.ext h
  have h_sum_v : ∑ p ∈ v, (p.2 - p.1) =
      ∑ p ∈ s_finset, (p.val.2 - p.val.1) := by
    rw [Finset.sum_image h_inj] <;> rfl
  have h_cover_bound : (b - a) - ∑ p ∈ v, (p.2 - p.1) ≤ ε * (b - a) := by
    rw [h_sum_v]
    have h12 : |∑ p ∈ s_finset, (p.val.2 - p.val.1) - (b - a)| < ε * (b - a) := h_approx
    have h13 : ∑ p ∈ s_finset, (p.val.2 - p.val.1) ≤ b - a := by
      have h14 : ∀ p ∈ s_finset, 0 ≤ (p.val.2 - p.val.1) := by
        intro p _; have h15 : p.val.1 < p.val.2 := (hu_sub p.prop).2.1; linarith
      have h15 : ∑ p ∈ s_finset, (p.val.2 - p.val.1) ≤ ∑' (p : {p // p ∈ u}), (p.val.2 - p.val.1) := by
        exact Summable.sum_le_tsum s_finset (fun i a => h11 i) h_summable
      rw [h_tsum_real] at h15
      exact h15
    have h16 : (b - a) - ∑ p ∈ s_finset, (p.val.2 - p.val.1) ≤ ε * (b - a) := by
      have h17 : |∑ p ∈ s_finset, (p.val.2 - p.val.1) - (b - a)| =
          (b - a) - ∑ p ∈ s_finset, (p.val.2 - p.val.1) := by
        rw [abs_of_nonpos] <;> linarith
      linarith
    exact h16

  -- Step 7: Minimum length gives τ
  by_cases h_v_empty : v = ∅
  · -- Empty family: cover bound follows from approximation
    have h_s_finset_empty : s_finset = ∅ := by
      by_contra h
      have h' : s_finset.Nonempty := Finset.nonempty_iff_ne_empty.mpr h
      have : v.Nonempty := Finset.Nonempty.image h' _
      rw [h_v_empty] at this
      simpa using this
    rw [h_s_finset_empty] at h_approx
    have h1 : 0 < b - a := by linarith
    have h_abs : |∑ p ∈ (∅ : Finset {p // p ∈ u}), (p.val.2 - p.val.1) - (b - a)| = b - a := by
      have h_sum : ∑ p ∈ (∅ : Finset {p // p ∈ u}), (p.val.2 - p.val.1) = 0 := by simp
      rw [h_sum]
      rw [show (0 : ℝ) - (b - a) = -(b - a) by ring, abs_neg, abs_of_pos h1]
    rw [h_abs] at h_approx
    have h2 : b - a < ε * (b - a) := h_approx
    have h4 : (b - a) - ∑ p ∈ (∅ : Finset (ℝ × ℝ)), (p.2 - p.1) ≤ ε * (b - a) := by
      have h5 : ∑ p ∈ (∅ : Finset (ℝ × ℝ)), (p.2 - p.1) = 0 := by simp
      rw [h5, sub_zero]
      exact h2.le
    exact ⟨1, by norm_num, ∅, by simp, by simp, by simp, by simp, h4⟩
  · have h_v_nonempty : v.Nonempty := by
      exact Finset.nonempty_iff_ne_empty.mpr h_v_empty
    let lengths : Finset ℝ := Finset.image (fun p : ℝ × ℝ => p.2 - p.1) v
    have h_lengths_nonempty : lengths.Nonempty := Finset.Nonempty.image h_v_nonempty _
    set min_len : ℝ := Finset.min' lengths h_lengths_nonempty with hmin_def
    let τ : ℝ := min_len / (b - a)
    have h19 : ∀ p ∈ v, 0 < p.2 - p.1 := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨q, _, rfl⟩
      have h20 : q.val.1 < q.val.2 := (hu_sub q.prop).2.1
      linarith
    have h22 : ∀ l ∈ lengths, 0 < l := by
      intro l hl
      rcases Finset.mem_image.mp hl with ⟨p, hp, rfl⟩
      exact h19 p hp
    have h23 : min_len ∈ lengths := Finset.min'_mem lengths h_lengths_nonempty
    have h24 : 0 < min_len := h22 _ h23
    have hτ_pos : 0 < τ := by
      dsimp only [τ]
      exact div_pos h24 (by linarith)
    have h_len_bound : ∀ p ∈ v, p.2 - p.1 ≥ τ * (b - a) := by
      intro p hp
      have h25 : p.2 - p.1 ∈ lengths := Finset.mem_image.mpr ⟨p, hp, rfl⟩
      have h26 : min_len ≤ p.2 - p.1 := Finset.min'_le lengths (p.2 - p.1) h25
      dsimp only [τ]
      have h27 : 0 < b - a := by linarith
      calc p.2 - p.1
        ≥ min_len := h26
      _ = (min_len / (b - a)) * (b - a) := by
        field_simp [h27.ne'] <;> ring

    -- Step 8: Verify all conditions
    have hI_eps : ∀ p ∈ v, EpsilonLinear f ε p.1 p.2 := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨q, _, rfl⟩
      exact (hu_sub q.prop).2.2.2
    have hI_cont : ∀ p ∈ v, a ≤ p.1 ∧ p.2 ≤ b := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨q, _, rfl⟩
      have h28 := hu_sub q.prop
      exact ⟨h28.1, h28.2.2.1⟩
    have hI_nonover : ∀ p ∈ v, ∀ q ∈ v, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1 := by
      intro p hp q hq hne
      rcases Finset.mem_image.mp hp with ⟨p', hp', rfl⟩
      rcases Finset.mem_image.mp hq with ⟨q', hq', rfl⟩
      have hne' : p' ≠ q' := by
        intro h; apply hne; simp [h]
      have hne_val : p'.val ≠ q'.val := by
        intro h; apply hne'; exact Subtype.ext h
      have h_disj : Disjoint (B p'.val) (B q'.val) :=
        hu_disj p'.prop q'.prop hne_val
      by_cases h : p'.val.2 < q'.val.1
      · exact Or.inl (by linarith)
      · have h' : q'.val.2 ≤ p'.val.1 := by
          by_contra h''
          have hq1 : q'.val.1 ≤ p'.val.2 := by linarith
          have hp1 : p'.val.1 < q'.val.2 := by linarith
          have hp_valid : p'.val.1 < p'.val.2 := (hu_sub p'.prop).2.1
          have hq_valid : q'.val.1 < q'.val.2 := (hu_sub q'.prop).2.1
          have h_in1 : p'.val.1 ≤ max p'.val.1 q'.val.1 := le_max_left _ _
          have h_in2 : max p'.val.1 q'.val.1 ≤ p'.val.2 := by
            apply max_le <;> [exact hp_valid.le; exact hq1]
          have h_in3 : q'.val.1 ≤ max p'.val.1 q'.val.1 := le_max_right _ _
          have h_in4 : max p'.val.1 q'.val.1 ≤ q'.val.2 := by
            apply max_le <;> [exact hp1.le; exact hq_valid.le]
          have h_overlap : max p'.val.1 q'.val.1 ∈ B p'.val ∩ B q'.val := by
            exact ⟨⟨h_in1, h_in2⟩, ⟨h_in3, h_in4⟩⟩
          have h_empty : B p'.val ∩ B q'.val = ∅ := Set.disjoint_iff_inter_eq_empty.mp h_disj
          rw [h_empty] at h_overlap
          simpa using h_overlap
        exact Or.inr (by linarith)
    exact ⟨τ, hτ_pos, v, hI_eps, h_len_bound, hI_cont, hI_nonover, h_cover_bound⟩

end CombinatorialKaufman.TubeNull

end
