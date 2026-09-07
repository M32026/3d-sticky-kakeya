module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.LinearToRegular
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.CodeFunctionLowerBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.BlockConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.BuildBlocksStructural
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.BuildBlocksCorrespondence
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.DecompositionProductHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.BoundedSlopeToDeltaSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.BoundedSlopeToRegular
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.RescaledCodeFunction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.SubintervalRescaling
public import MyLeanRepo.DiscretisedFurstenbergEstimate.combinatorial_kaufman_decomposition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.BoundedSlopeMinimal

@[expose] public section

namespace DirecretisedFurstenbergEstimate
namespace MultiscaleDecomposition

lemma tubeNull {ε : ℝ} (hε : 0 < ε) :
    ∃ (τ : ℝ), 0 < τ ∧
    ∀ (f : ℝ → ℝ) (a b : ℝ),
      a < b →
      (∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → |f x - f y| ≤ 2 * |x - y|) →
      ∃ (I : Finset (ℝ × ℝ)),
        (∀ p ∈ I, EpsLinear f p.1 p.2 ε) ∧
        (∀ p ∈ I, p.2 - p.1 ≥ τ * (b - a)) ∧
        (∀ p ∈ I, a ≤ p.1 ∧ p.2 ≤ b) ∧
        (∀ p ∈ I, ∀ q ∈ I, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1) ∧
        (b - a) - ∑ p ∈ I, (p.2 - p.1) ≤ ε * (b - a) := by
  rcases DirecretisedFurstenbergEstimate.GeneralAdapter.tubeNull_general hε with ⟨τ, hτ_pos, h_main⟩
  refine ⟨τ, hτ_pos, ?_⟩
  intro f a b hab hlip
  rcases h_main f a b hab hlip with ⟨I, hI_eps, hI_len, hI_cont, hI_nonover, hI_cover⟩
  have hI_eps' : ∀ p ∈ I, EpsLinear f p.1 p.2 ε := by
    intro p hp
    have h1 : EpsilonLinear f ε p.1 p.2 := hI_eps p hp
    have h2 : p.1 < p.2 := by
      have h3 : p.2 - p.1 ≥ τ * (b - a) := hI_len p hp
      have h4 : 0 < τ * (b - a) := by positivity
      linarith
    exact ⟨h2, h1⟩
  exact ⟨I, hI_eps', hI_len, hI_cont, hI_nonover, hI_cover⟩

-- ======================================================================
-- More helpers for combinatorialKaufman
-- ======================================================================

/-- If [a,b] is δ-linear and a < c < b with c-a > η·(b-a),
    then [a,c] is (2δ/η)-linear. -/
lemma truncated_linear (f : ℝ → ℝ) {a b c δ η : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 < η)
    (hac : a < c) (hcb : c < b)
    (h_lin : EpsLinear f a b δ)
    (h_frac : c - a > η * (b - a)) :
    EpsLinear f a c (2 * δ / η) := by
  have h_err_c : |f c - linearInterpolant f a b c| ≤ δ * (b - a) :=
    h_lin.2 c ⟨by linarith, by linarith⟩
  have h_slope_diff : |slope f a c - slope f a b| ≤ δ * (b - a) / (c - a) := by
    have h_lin_c : linearInterpolant f a b c = f a + slope f a b * (c - a) := by
      simp [linearInterpolant]
    have h_eq : (f c - linearInterpolant f a b c) / (c - a) = slope f a c - slope f a b := by
      rw [h_lin_c]
      dsimp only [slope]
      field_simp [show c - a ≠ 0 by linarith] <;> ring
    have hpos : 0 < c - a := by linarith
    have hba : 0 < b - a := by linarith
    have h_nonneg : 0 ≤ δ * (b - a) / (c - a) := by
      apply div_nonneg
      · exact mul_nonneg hδ (by linarith)
      · exact by linarith
    have h : |(f c - linearInterpolant f a b c) / (c - a)| ≤ δ * (b - a) / (c - a) := by
      rw [abs_div, abs_of_pos hpos]
      gcongr <;> linarith
    rw [←h_eq]
    exact h
  have h2 : ∀ x ∈ Set.Icc a c, |f x - linearInterpolant f a c x| ≤ (2 * δ / η) * (c - a) := by
    intro x hx
    have h_x_le_c : x ≤ c := hx.2
    have h_x_le_b : x ≤ b := by linarith
    have h_x_in_ab : x ∈ Set.Icc a b := ⟨hx.1, h_x_le_b⟩
    have h3 : |f x - linearInterpolant f a b x| ≤ δ * (b - a) := h_lin.2 x h_x_in_ab
    have h4 : |linearInterpolant f a b x - linearInterpolant f a c x| ≤ δ * (b - a) := by
      have h_eq2 : linearInterpolant f a c x - linearInterpolant f a b x =
                   (slope f a c - slope f a b) * (x - a) := by
        simp [linearInterpolant] <;> ring
      have h_abs : |linearInterpolant f a b x - linearInterpolant f a c x| =
                     |(slope f a c - slope f a b) * (x - a)| := by
        rw [show linearInterpolant f a b x - linearInterpolant f a c x =
                       -(linearInterpolant f a c x - linearInterpolant f a b x) by ring]
        rw [abs_neg, h_eq2]
      rw [h_abs]
      have hba : 0 < b - a := by linarith
      have hca : 0 < c - a := by linarith
      have h5 : |(slope f a c - slope f a b) * (x - a)| ≤ δ * (b - a) := by
        calc |(slope f a c - slope f a b) * (x - a)|
          = |slope f a c - slope f a b| * |x - a| := by rw [abs_mul]
        _ ≤ (δ * (b - a) / (c - a)) * |x - a| := by gcongr
        _ ≤ (δ * (b - a) / (c - a)) * (c - a) := by
          have h_nonneg2 : 0 ≤ δ * (b - a) / (c - a) := by
            apply div_nonneg
            · exact mul_nonneg hδ (by linarith)
            · exact by linarith
          have h_xa_nonneg : 0 ≤ x - a := by linarith [hx.1]
          have h_xa_le : x - a ≤ c - a := by linarith [hx.2]
          have h_abs_le : |x - a| ≤ c - a := by
            rw [abs_of_nonneg h_xa_nonneg]
            exact h_xa_le
          nlinarith
        _ = δ * (b - a) := by
          field_simp [show c - a ≠ 0 by linarith] <;> ring
      exact h5
    have h_triangle : |f x - linearInterpolant f a c x| ≤
        |f x - linearInterpolant f a b x| + |linearInterpolant f a b x - linearInterpolant f a c x| := by
      calc |f x - linearInterpolant f a c x|
        = |(f x - linearInterpolant f a b x) + (linearInterpolant f a b x - linearInterpolant f a c x)| := by ring_nf
      _ ≤ |f x - linearInterpolant f a b x| + |linearInterpolant f a b x - linearInterpolant f a c x| := by
        exact abs_add_le (f x - linearInterpolant f a b x) (linearInterpolant f a b x - linearInterpolant f a c x)
    calc |f x - linearInterpolant f a c x|
      ≤ |f x - linearInterpolant f a b x| + |linearInterpolant f a b x - linearInterpolant f a c x| := h_triangle
    _ ≤ δ * (b - a) + δ * (b - a) := by gcongr
    _ = 2 * δ * (b - a) := by ring
    _ ≤ (2 * δ / η) * (c - a) := by
      have h9 : 0 < c - a := by linarith
      have h10 : b - a < (c - a) / η := by
        have h11 : η * (b - a) < c - a := h_frac
        have h12 : 0 < η := hη
        calc b - a
          = (η * (b - a)) / η := by field_simp [h12.ne'] <;> ring
        _ < (c - a) / η := by gcongr
      have h13 : 2 * δ * (b - a) ≤ (2 * δ / η) * (c - a) := by
        have h14 : (2 * δ / η) * (c - a) = 2 * δ * ((c - a) / η) := by ring
        rw [h14]
        gcongr <;> linarith
      exact h13
  exact ⟨hac, h2⟩

/-- Extend a 2-Lipschitz function on [0,m] to a continuous function on ℝ. -/
lemma extend_continuous (f : ℝ → ℝ) {m : ℝ} (hm : 0 < m)
    (h_lip : ∀ x y, x ∈ Set.Icc 0 m → y ∈ Set.Icc 0 m → |f x - f y| ≤ 2 * |x - y|) :
    ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ Set.Icc 0 m, g x = f x := by
  have h_lip' : LipschitzOnWith 2 f (Set.Icc 0 m) := by
    intro x hx y hy
    have h : |f x - f y| ≤ 2 * |x - y| := h_lip x y hx hy
    have h' : ENNReal.ofReal |f x - f y| ≤ 2 * ENNReal.ofReal |x - y| := by
      have h1 : ENNReal.ofReal |f x - f y| ≤ ENNReal.ofReal (2 * |x - y|) := by
        apply ENNReal.ofReal_le_ofReal <;> linarith
      have h2 : ENNReal.ofReal (2 * |x - y|) = 2 * ENNReal.ofReal |x - y| := by
        rw [ENNReal.ofReal_mul] <;> norm_num
      rw [h2] at h1; exact h1
    have h_dist1 : dist (f x) (f y) = |f x - f y| := by
      simp [dist_eq_norm, Real.norm_eq_abs]
    have h_dist2 : dist x y = |x - y| := by
      simp [dist_eq_norm, Real.norm_eq_abs]
    have h_edist : edist (f x) (f y) ≤ ↑2 * edist x y := by
      simp only [edist_dist]
      rw [h_dist1, h_dist2]
      exact h'
    exact h_edist
  have hf_cont : ContinuousOn f (Set.Icc 0 m) := h_lip'.continuousOn
  let clamp : ℝ → ℝ := fun x => max 0 (min x m)
  have h_clamp_cont : Continuous clamp := by fun_prop
  have h_clamp_range : ∀ x, clamp x ∈ Set.Icc 0 m := by
    intro x
    have h1 : 0 ≤ clamp x := by simp [clamp] <;> linarith
    have h2 : clamp x ≤ m := by simp [clamp] <;> linarith [hm]
    exact ⟨h1, h2⟩
  let g : ℝ → ℝ := f ∘ clamp
  have h1 : ContinuousOn g Set.univ :=
    hf_cont.comp h_clamp_cont.continuousOn (fun x _ => h_clamp_range x)
  have hg_cont : Continuous g := by exact ContinuousOn.comp_continuous hf_cont h_clamp_cont h_clamp_range
  have hg_agree : ∀ x ∈ Set.Icc 0 m, g x = f x := by
    intro x hx
    have h_clamp_id : clamp x = x := by
      simp only [clamp]
      have hmin : min x m = x := by apply min_eq_left; linarith [hx.2]
      rw [hmin]
      have hmax : max 0 x = x := by apply max_eq_right; linarith [hx.1]
      rw [hmax]
    simp [g, h_clamp_id]
  exact ⟨g, hg_cont, hg_agree⟩

/-- Split a sorted list of disjoint intervals at point c'. -/
noncomputable def splitAtPoint (c' : ℝ) : List (ℝ × ℝ) →
    List (ℝ × ℝ) × Option (ℝ × ℝ) × List (ℝ × ℝ)
  | [] => ([], none, [])
  | p :: rest =>
    if p.2 < c' then
      let (before, cont, after) := splitAtPoint c' rest
      (p :: before, cont, after)
    else if c' < p.1 then
      ([], none, p :: rest)
    else
      ([], some p, rest)

lemma splitAtPoint_length (c' : ℝ) (intervals : List (ℝ × ℝ)) :
    let (before, cont, after) := splitAtPoint c' intervals
    before.length + cont.toList.length + after.length = intervals.length := by
  induction intervals with
  | nil => simp [splitAtPoint]
  | cons p rest ih =>
    dsimp only [splitAtPoint]
    split_ifs <;> simp_all [ih] <;> omega

-- ======================================================================
-- Combinatorial Kaufman lemma (OS Lemma 1206)
-- ======================================================================

/-- Combine ε-linear intervals to ensure each resulting interval either:
(a) is ε-linear with slope ≥ s, or
(b) is ε-superlinear with slope = s.

The total uncovered length is `O_{s,t}(ε) * m`.
See OS Lemma `combinatorial-kaufman` line 1206.
-/
lemma combinatorialKaufman {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t ≤ 2)
    {ε : ℝ} (hε : 0 < ε) :
    let C := 2 + 2 / (t - s)
    ∃ (τ : ℝ), 0 < τ ∧
    ∀ (f : ℝ → ℝ) (m : ℝ),
      0 < m →
      (∀ x y, x ∈ Set.Icc 0 m → y ∈ Set.Icc 0 m → |f x - f y| ≤ 2 * |x - y|) →
      f 0 = 0 →
      (∀ x ∈ Set.Icc 0 m, f x ≥ t * x - (ε / C) * m) →
      ∃ (I : Finset (ℝ × ℝ)),
        (∀ p ∈ I,
          (EpsLinear f p.1 p.2 ε ∧ slope f p.1 p.2 ≥ s) ∨
          (EpsSuperlinear f p.1 p.2 ε ∧ slope f p.1 p.2 = s)) ∧
        (∀ p ∈ I, p.2 - p.1 ≥ τ * m) ∧
        (∀ p ∈ I, 0 ≤ p.1 ∧ p.2 ≤ m) ∧
        (∀ p ∈ I, ∀ q ∈ I, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1) ∧
        m - ∑ p ∈ I, (p.2 - p.1) ≤ ε * m := by
  dsimp only
  rcases DirecretisedFurstenbergEstimate.GeneralAdapter.combinatorialKaufman_general
      hs hst ht (hε := hε) with ⟨τ, hτ_pos, h_main⟩
  refine ⟨τ, hτ_pos, fun f m hm_pos hlip hf0 h_lower => ?_⟩
  rcases h_main f m hm_pos hlip hf0 h_lower with
    ⟨I, hI_good, hI_len, hI_cont, hI_nonover, hI_cover⟩
  have hI_good' : ∀ p ∈ I,
      (EpsLinear f p.1 p.2 ε ∧ slope f p.1 p.2 ≥ s) ∨
      (EpsSuperlinear f p.1 p.2 ε ∧ slope f p.1 p.2 = s) := by
    intro p hp
    rcases hI_good p hp with (h | h)
    · -- Linear case
      have h1 : EpsilonLinear f ε p.1 p.2 := h.1
      have h2 : s ≤ chordSlope f p.1 p.2 := h.2
      have h3 : p.1 < p.2 := by
        have h4 : p.2 - p.1 ≥ τ * m := hI_len p hp
        have h5 : 0 < τ * m := by positivity
        linarith
      have h_slope_eq : chordSlope f p.1 p.2 = slope f p.1 p.2 := by rfl
      exact Or.inl ⟨⟨h3, h1⟩, by rw [←h_slope_eq]; exact h2⟩
    · -- Superlinear case
      have h1 : EpsilonSuperlinear f ε p.1 p.2 := h.1
      have h2 : chordSlope f p.1 p.2 = s := h.2
      have h3 : p.1 < p.2 := by
        have h4 : p.2 - p.1 ≥ τ * m := hI_len p hp
        have h5 : 0 < τ * m := by positivity
        linarith
      have h_slope_eq : chordSlope f p.1 p.2 = slope f p.1 p.2 := by rfl
      exact Or.inr ⟨⟨h3, h1⟩, by rw [←h_slope_eq]; exact h2⟩
  exact ⟨I, hI_good', hI_len, hI_cont, hI_nonover, hI_cover⟩

-- ======================================================================
-- Helper lemmas for sorted interval lists
-- ======================================================================

/-- From non-strict left-sorting + disjoint interiors + validity, derive strict left-sorting. -/
lemma strictSortedOfDisjoint (l : List (ℝ × ℝ))
    (h_le : List.Pairwise (fun p q : ℝ × ℝ => p.1 ≤ q.1) l)
    (h_disj : CombinatorialKaufman.PairwiseInteriorDisjointList l)
    (h_valid : ∀ p ∈ l, p.1 < p.2) :
    CombinatorialKaufman.SortedByLeft l := by
  rw [CombinatorialKaufman.SortedByLeft]
  induction l with
  | nil => simp
  | cons p t ih =>
    have h_le_t := (List.pairwise_cons.mp h_le).2
    have h_disj_t := (List.pairwise_cons.mp h_disj).2
    have h_valid_t : ∀ q ∈ t, q.1 < q.2 := fun q hq => h_valid q (by simp [hq])
    have h_ih := ih h_le_t h_disj_t h_valid_t
    have h_left : ∀ q ∈ t, p.1 ≤ q.1 := (List.pairwise_cons.mp h_le).1
    have h_disj' : ∀ q ∈ t, Disjoint (Set.Ioo p.1 p.2) (Set.Ioo q.1 q.2) :=
      (List.pairwise_cons.mp h_disj).1
    have h_strict_left : ∀ q ∈ t, p.1 < q.1 := by
      intro q hq
      have hle : p.1 ≤ q.1 := h_left q hq
      by_contra h
      have h_eq : p.1 = q.1 := by linarith
      have hp_valid : p.1 < p.2 := h_valid p (by simp)
      have hq_valid : q.1 < q.2 := h_valid q (by simp [hq])
      set y := min p.2 q.2 with hy_def
      have hmin : p.1 < y := by
        rw [hy_def, h_eq]
        apply lt_min <;> linarith [hp_valid, hq_valid]
      set x := (p.1 + y) / 2 with hx_def
      have hx1 : p.1 < x := by rw [hx_def]; linarith
      have hx2 : x < y := by rw [hx_def]; linarith
      have h_y_le1 : y ≤ p.2 := min_le_left _ _
      have h_y_le2 : y ≤ q.2 := min_le_right _ _
      have hx3 : x < p.2 := by linarith
      have hx4 : x < q.2 := by linarith
      have h_in_p : x ∈ Set.Ioo p.1 p.2 := ⟨by linarith, hx3⟩
      have h_in_q : x ∈ Set.Ioo q.1 q.2 := by rw [h_eq] at hx1; exact ⟨hx1, hx4⟩
      exact Set.not_disjoint_iff.mpr ⟨x, h_in_p, h_in_q⟩ (h_disj' q hq)
    simp only [List.pairwise_cons]
    exact ⟨h_strict_left, h_ih⟩

/-- From strict left-sorting + disjoint interiors + validity, derive pairwise p.2 ≤ q.1. -/
lemma pairwiseEndAfterStartOfSortedDisjoint (l : List (ℝ × ℝ))
    (h_sorted : CombinatorialKaufman.SortedByLeft l)
    (h_disj : CombinatorialKaufman.PairwiseInteriorDisjointList l)
    (h_valid : ∀ p ∈ l, p.1 < p.2) :
    List.Pairwise (fun p q : ℝ × ℝ => p.2 ≤ q.1) l := by
  induction l with
  | nil => simp
  | cons p t ih =>
    have h_sorted_t := (List.pairwise_cons.mp h_sorted).2
    have h_disj_t := (List.pairwise_cons.mp h_disj).2
    have h_valid_t : ∀ q ∈ t, q.1 < q.2 := fun q hq => h_valid q (by simp [hq])
    have h_ih := ih h_sorted_t h_disj_t h_valid_t
    have h_tail_after : ∀ q ∈ t, p.2 ≤ q.1 :=
      CombinatorialKaufman.sorted_disjoint_tail_after_head
        (h_valid p (by simp)) h_valid_t h_sorted h_disj
    simp only [List.pairwise_cons]
    exact ⟨h_tail_after, h_ih⟩

/-- Every block produced by buildBlocks has slope in [s, 2] if all input intervals do. -/
lemma buildBlocks_slope_in_range (f : ℝ → ℝ) (s t : ℝ) (hs : 0 < s) (hst : s < t) (ht : t ≤ 2)
    (m : ℕ) :
    ∀ (ints : List (ℝ × ℝ)) (pos : ℕ),
      (∀ p ∈ ints, s ≤ chordSlope f p.1 p.2 ∧ chordSlope f p.1 p.2 ≤ 2) →
      ∀ b ∈ MultiscaleBlockConversion.buildBlocks f s m ints pos,
        s ≤ b.2.2.2 ∧ b.2.2.2 ≤ 2 := by
  intro ints
  induction ints with
  | nil =>
    intro pos _ b hb
    dsimp only [MultiscaleBlockConversion.buildBlocks] at hb
    split_ifs at hb
    · have h_eq : b = (pos, m, false, s) := by simpa using hb
      rw [h_eq] <;> constructor <;> linarith [hs, ht, hst]
    · contradiction
  | cons p rest ih =>
    intro pos h_slopes b hb
    let l := Nat.ceil p.1
    let r := Nat.floor p.2
    let sl := chordSlope f p.1 p.2
    dsimp only [MultiscaleBlockConversion.buildBlocks] at hb
    by_cases h_case : pos < l
    · have h_eq1 : b = (pos, l, false, s) ∨ b = (l, r, true, sl) ∨
          b ∈ MultiscaleBlockConversion.buildBlocks f s m rest r := by
        simpa [h_case, l, r, sl] using hb
      rcases h_eq1 with (rfl | rfl | hb)
      · exact ⟨by linarith [hs], by linarith [ht, hst]⟩
      · exact h_slopes p (by simp)
      · exact ih r (fun q hq => h_slopes q (by simp [hq])) b hb
    · have h_eq2 : b = (l, r, true, sl) ∨
          b ∈ MultiscaleBlockConversion.buildBlocks f s m rest r := by
        simpa [h_case, l, r, sl] using hb
      rcases h_eq2 with (rfl | hb)
      · exact h_slopes p (by simp)
      · exact ih r (fun q hq => h_slopes q (by simp [hq])) b hb

-- ======================================================================
-- Rounding lemmas for buildBlocks
-- ======================================================================

/-- Rounded length is at least real length minus 2. -/
lemma roundedLength_ge_real_minus_2 (p : ℝ × ℝ) (h1 : 0 ≤ p.1)
    (h_round : Nat.ceil p.1 < Nat.floor p.2) :
    (MultiscaleBlockConversion.roundedLength p : ℝ) ≥ (p.2 - p.1) - 2 := by
  dsimp only [MultiscaleBlockConversion.roundedLength]
  have h_ceil : (Nat.ceil p.1 : ℝ) ≤ p.1 + 1 := by
    by_cases h0 : Nat.ceil p.1 = 0
    · simp [h0] <;> linarith
    · have h_pos : 0 < Nat.ceil p.1 := by omega
      let n := Nat.ceil p.1 - 1
      have hn : n < Nat.ceil p.1 := by omega
      have h_not_le : ¬(p.1 ≤ (n : ℝ)) := by
        intro h
        have h' : Nat.ceil p.1 ≤ n := by
          have h_iff : Nat.ceil p.1 ≤ n ↔ p.1 ≤ (n : ℝ) := Nat.ceil_le
          exact h_iff.mpr h
        omega
      have h_gt : (n : ℝ) < p.1 := by linarith
      have h_eq : (n : ℝ) = (Nat.ceil p.1 : ℝ) - 1 := by
        rw [show n = Nat.ceil p.1 - 1 from by simp [n] <;> omega]
        rw [Nat.cast_sub (by omega)] <;> norm_cast
      linarith
  have h_floor : p.2 - 1 ≤ (Nat.floor p.2 : ℝ) := by
    have h41 : p.2 < (Nat.floor p.2 : ℝ) + 1 := Nat.lt_floor_add_one p.2
    linarith
  have h6 : (Nat.floor p.2 : ℝ) - (Nat.ceil p.1 : ℝ) ≥ (p.2 - p.1) - 2 := by linarith
  rw [Nat.cast_sub (show Nat.ceil p.1 ≤ Nat.floor p.2 from le_of_lt h_round)]
  exact h6

/-- Slope-weighted rounded length ≥ slope * real length - 4. -/
lemma slopeWeighted_ge (f : ℝ → ℝ) (p : ℝ × ℝ)
    (h_slope_nonneg : 0 ≤ chordSlope f p.1 p.2)
    (h_slope_le_2 : chordSlope f p.1 p.2 ≤ 2)
    (h1 : 0 ≤ p.1) (h_round : Nat.ceil p.1 < Nat.floor p.2) :
    MultiscaleBlockConversion.slopeWeightedLength f p ≥
      chordSlope f p.1 p.2 * (p.2 - p.1) - 4 := by
  dsimp only [MultiscaleBlockConversion.slopeWeightedLength]
  have h_rl : (MultiscaleBlockConversion.roundedLength p : ℝ) ≥ (p.2 - p.1) - 2 :=
    roundedLength_ge_real_minus_2 p h1 h_round
  nlinarith

/-- Sum of rounded lengths ≥ sum of real lengths - 2*K. -/
lemma sum_rounded_ge (l : List (ℝ × ℝ))
    (h1 : ∀ p ∈ l, 0 ≤ p.1)
    (h_round : ∀ p ∈ l, Nat.ceil p.1 < Nat.floor p.2) :
    ((l.map MultiscaleBlockConversion.roundedLength).sum : ℝ) ≥
      (l.map (fun p => p.2 - p.1)).sum - 2 * (l.length : ℝ) := by
  induction l with
  | nil => norm_num
  | cons p rest ih =>
    have h3 : 0 ≤ p.1 := h1 p (by simp)
    have h4 : Nat.ceil p.1 < Nat.floor p.2 := h_round p (by simp)
    have h5 : (MultiscaleBlockConversion.roundedLength p : ℝ) ≥ (p.2 - p.1) - 2 :=
      roundedLength_ge_real_minus_2 p h3 h4
    have h6 : ∀ q ∈ rest, 0 ≤ q.1 := fun q hq => h1 q (by simp [hq])
    have h7 : ∀ q ∈ rest, Nat.ceil q.1 < Nat.floor q.2 := fun q hq => h_round q (by simp [hq])
    have h_ih := ih h6 h7
    simp [List.map_cons, List.sum_cons] at *
    <;> linarith

/-- Sum of slope-weighted rounded lengths ≥ sum slope*length - 4*K. -/
lemma sum_slopeWeighted_ge (f : ℝ → ℝ) (l : List (ℝ × ℝ))
    (h_slopes : ∀ p ∈ l, 0 ≤ chordSlope f p.1 p.2 ∧ chordSlope f p.1 p.2 ≤ 2)
    (h1 : ∀ p ∈ l, 0 ≤ p.1)
    (h_round : ∀ p ∈ l, Nat.ceil p.1 < Nat.floor p.2) :
    (l.map (MultiscaleBlockConversion.slopeWeightedLength f)).sum ≥
      (l.map (fun p => chordSlope f p.1 p.2 * (p.2 - p.1))).sum - 4 * (l.length : ℝ) := by
  induction l with
  | nil => norm_num
  | cons p rest ih =>
    have h3 : 0 ≤ p.1 := h1 p (by simp)
    have h4 : Nat.ceil p.1 < Nat.floor p.2 := h_round p (by simp)
    have h5 : 0 ≤ chordSlope f p.1 p.2 ∧ chordSlope f p.1 p.2 ≤ 2 := h_slopes p (by simp)
    have h6 : MultiscaleBlockConversion.slopeWeightedLength f p ≥
        chordSlope f p.1 p.2 * (p.2 - p.1) - 4 :=
      slopeWeighted_ge f p h5.1 h5.2 h3 h4
    have h7 : ∀ q ∈ rest, 0 ≤ chordSlope f q.1 q.2 ∧ chordSlope f q.1 q.2 ≤ 2 :=
      fun q hq => h_slopes q (by simp [hq])
    have h8 : ∀ q ∈ rest, 0 ≤ q.1 := fun q hq => h1 q (by simp [hq])
    have h9 : ∀ q ∈ rest, Nat.ceil q.1 < Nat.floor q.2 := fun q hq => h_round q (by simp [hq])
    have h_ih := ih h7 h8 h9
    simp [List.map_cons, List.sum_cons] at *
    <;> linarith

/-- If 0 ≤ p.1 and p.2 - p.1 ≥ 2, then Nat.ceil p.1 < Nat.floor p.2. -/
lemma ceil_lt_floor_of_length_ge_two {p : ℝ × ℝ} (h1 : 0 ≤ p.1) (h2 : p.2 - p.1 ≥ 2) :
    Nat.ceil p.1 < Nat.floor p.2 := by
  have h3 : (Nat.ceil p.1 : ℝ) ≤ p.1 + 1 := by
    by_cases h0 : Nat.ceil p.1 = 0
    · rw [h0]
      simpa using show (0 : ℝ) ≤ p.1 + 1 by linarith
    · have h_n_pos : 0 < Nat.ceil p.1 := Nat.pos_of_ne_zero h0
      set n : ℕ := Nat.ceil p.1 - 1 with hn
      have h_n_lt : n < Nat.ceil p.1 := by
        simp [hn, h_n_pos]
      have h_n_eq : (n : ℝ) = (Nat.ceil p.1 : ℝ) - 1 := by
        rw [hn, Nat.cast_sub (by linarith)] <;> norm_cast
      by_contra h
      have h' : p.1 + 1 < (Nat.ceil p.1 : ℝ) := by linarith
      have h_gt : p.1 < (n : ℝ) := by
        rw [h_n_eq] <;> linarith
      have h_le : p.1 ≤ (n : ℝ) := by linarith
      have h_ceil_le : Nat.ceil p.1 ≤ n := (Nat.ceil_le).mpr h_le
      exact not_le.mpr h_n_lt h_ceil_le
  have h4 : p.2 - 1 < (Nat.floor p.2 : ℝ) := by
    have h5 : p.2 < (Nat.floor p.2 : ℝ) + 1 := Nat.lt_floor_add_one p.2
    linarith
  have h5 : (Nat.ceil p.1 : ℝ) < (Nat.floor p.2 : ℝ) := by
    calc
      (Nat.ceil p.1 : ℝ) ≤ p.1 + 1 := h3
      _ ≤ p.2 - 1 := by linarith
      _ < (Nat.floor p.2 : ℝ) := h4
  exact_mod_cast h5

-- ======================================================================
-- Helper lemmas for the main theorem
-- ======================================================================

/-- Permutation of lists preserves sum. -/
lemma perm_sum_eq {α : Type*} [AddCommMonoid α] {l1 l2 : List α}
    (h : l1.Perm l2) : l1.sum = l2.sum :=
  h.sum_eq

/-- Permutation of lists preserves sum under mapping. -/
lemma perm_map_sum_eq {α β : Type*} [AddCommMonoid β] {l1 l2 : List α}
    (h : l1.Perm l2) (f : α → β) : (l1.map f).sum = (l2.map f).sum :=
  (h.map f).sum_eq

/-- Sum of map over finRange equals Finset.sum over Fin n. -/
lemma sum_finRange_map {α : Type*} [AddCommMonoid α] {n : ℕ} (f : Fin n → α) :
    ((List.finRange n).map f).sum = ∑ i : Fin n, f i := by
  have h_main : ∀ (m : ℕ) (g : Fin m → α), (List.ofFn g).sum = ∑ i : Fin m, g i := by
    intro m
    induction m with
    | zero =>
      intro g
      simp
    | succ m ih =>
      intro g
      rw [List.ofFn_succ' g]
      have h_concat : ((List.ofFn (fun i : Fin m => g (Fin.castSucc i))).concat (g (Fin.last m))).sum =
          (List.ofFn (fun i : Fin m => g (Fin.castSucc i))).sum + g (Fin.last m) := by
        simp [List.concat_append]
        <;> rfl
      rw [h_concat, ih (fun i : Fin m => g (Fin.castSucc i))]
      rw [Fin.sum_univ_castSucc]
      <;> rfl
  have h1 : (List.finRange n).map f = List.ofFn f := by
    rw [←List.ofFn_id n, List.map_ofFn]
    <;> simp
  rw [h1]
  exact h_main n f

-- ======================================================================
-- Main multiscale decomposition proposition (OS Proposition 1123)
-- ======================================================================

set_option maxHeartbeats 500000

/-- The sum of a function over a list equals the sum over its finite indices. -/
lemma list_map_sum_eq_fin_sum {α β : Type*} [AddCommMonoid α] (f : β → α) (l : List β) :
    (l.map f).sum = ∑ j : Fin l.length, f (l.get j) := by
  induction l with
  | nil => simp
  | cons b bs ih =>
    have h1 : ((b :: bs).map f).sum = f b + (bs.map f).sum := by
      simp [List.map_cons, List.sum_cons]
    have h2 : ∑ j : Fin (bs.length + 1), f ((b :: bs).get j) =
        f b + ∑ j : Fin bs.length, f (bs.get j) := by
      rw [Fin.sum_univ_succ]
      apply congr_arg₂ (fun x y => x + y)
      · simpa using rfl
      · apply Finset.sum_congr rfl
        intro j _
        simp [List.get_cons_succ] <;> rfl
    calc
      ((b :: bs).map f).sum
        = f b + (bs.map f).sum := h1
      _ = f b + ∑ j : Fin bs.length, f (bs.get j) := by rw [ih]
      _ = ∑ j : Fin (bs.length + 1), f ((b :: bs).get j) := h2.symm

/-- Ratio of powers Δ^a / Δ^b = Δ^(a-b) = Δ^(-(b-a)). -/
lemma ratio_eq_rpow {Δ : ℝ} (hΔ : 0 < Δ) {a b : ℕ} (hab : a < b) :
    (Δ ^ a : ℝ) / (Δ ^ b : ℝ) =
    Real.rpow Δ (-( (b : ℝ) - (a : ℝ))) := by
  have h1 : (Δ ^ a : ℝ) = Real.rpow Δ (a : ℝ) := by simp
  have h2 : (Δ ^ b : ℝ) = Real.rpow Δ (b : ℝ) := by simp
  have h3 : Real.rpow Δ (a : ℝ) / Real.rpow Δ (b : ℝ) = Real.rpow Δ ((a : ℝ) - (b : ℝ)) :=
    (Real.rpow_sub hΔ (a : ℝ) (b : ℝ)).symm
  rw [h1, h2, h3]
  have h4 : (a : ℝ) - (b : ℝ) = -((b : ℝ) - (a : ℝ)) := by abel
  rw [h4]

/-- Real.rpow Δ (c * ↑m) = Real.rpow (Δ ^ m) c for 0 < Δ, m : ℕ. -/
lemma rpow_Δ_m {Δ : ℝ} (hΔ : 0 < Δ) {c : ℝ} {m : ℕ} :
    Real.rpow Δ (c * (m : ℝ)) = Real.rpow (Δ ^ m) c := by
  have h_base : (Δ ^ m : ℝ) = Real.rpow Δ (m : ℝ) := by simp
  have h : Real.rpow (Δ ^ m) c = Real.rpow (Real.rpow Δ (m : ℝ)) c := by rw [h_base]
  rw [h]
  have h2 : Real.rpow (Real.rpow Δ (m : ℝ)) c = Real.rpow Δ ((m : ℝ) * c) :=
    (Real.rpow_mul (le_of_lt hΔ) (m : ℝ) c).symm
  rw [h2, mul_comm]

/-- For 0 < Δ ≤ 1, if x ≤ y then Δ^y ≤ Δ^x. -/
lemma rpow_decreasing {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ < 1) {x y : ℝ} (hxy : x ≤ y) :
    Real.rpow Δ y ≤ Real.rpow Δ x :=
  Real.rpow_le_rpow_of_exponent_ge hΔ (by linarith) hxy

/-- Endpoint error bound: if f is 2-Lipschitz and a ∈ [p1, p1+1), t ∈ [0,2],
    then |f(a) - (f(p1) + t*(a-p1))| ≤ 4. -/
lemma endpoint_bound_lemma {f : ℝ → ℝ} {a p1 t m : ℝ}
    (h_lip : ∀ x y, x ∈ Set.Icc 0 m → y ∈ Set.Icc 0 m → |f x - f y| ≤ 2 * |x - y|)
    (ha_nonneg : 0 ≤ a) (ha_le_m : a ≤ m)
    (hp1_nonneg : 0 ≤ p1) (hp1_le_m : p1 ≤ m)
    (ha_ge_p1 : p1 ≤ a) (ha_lt_p11 : a - p1 < 1)
    (ht_nonneg : 0 ≤ t) (ht_le2 : t ≤ 2) :
    |f a - (f p1 + t * (a - p1))| ≤ 4 := by
  have h_abs_lt1 : |a - p1| < 1 := by
    rw [abs_of_nonneg (by linarith)] <;> linarith
  have h_a_in0 : a ∈ Set.Icc 0 m := ⟨ha_nonneg, ha_le_m⟩
  have h_p1_in0 : p1 ∈ Set.Icc 0 m := ⟨hp1_nonneg, hp1_le_m⟩
  have h_lip2 : |f a - f p1| ≤ 2 * |a - p1| := h_lip a p1 h_a_in0 h_p1_in0
  have h1 : |f a - f p1| ≤ 2 := by
    have h11 : 2 * |a - p1| < 2 := by nlinarith
    exact le_trans h_lip2 h11.le
  have h_t_abs : |t| ≤ 2 := by
    rw [abs_of_nonneg ht_nonneg] <;> linarith
  have h2 : |t * (a - p1)| ≤ 2 := by
    have h21 : |t * (a - p1)| = |t| * |a - p1| := by rw [abs_mul]
    rw [h21]
    have h23 : |t| * |a - p1| ≤ 2 * |a - p1| :=
      mul_le_mul_of_nonneg_right h_t_abs (abs_nonneg _)
    have h24 : 2 * |a - p1| < 2 := by nlinarith
    have h22 : |t| * |a - p1| < 2 := lt_of_le_of_lt h23 h24
    exact h22.le
  have h3 : f a - (f p1 + t * (a - p1)) = (f a - f p1) - t * (a - p1) := by ring
  rw [h3]
  have h4 : |(f a - f p1) - t * (a - p1)| ≤ |f a - f p1| + |t * (a - p1)| := abs_sub _ _
  have h5 : |f a - f p1| + |t * (a - p1)| ≤ 4 := by
    calc |f a - f p1| + |t * (a - p1)| ≤ 2 + 2 := add_le_add h1 h2
      _ = 4 := by norm_num
  exact le_trans h4 h5

/-- Code function bound from ε-linearity: |f(a+k)-f(a) - t*k| ≤ E_lin + E_end. -/
lemma linear_code_bounds_lemma {f : ℝ → ℝ} {a k p1 p2 t E_lin E_end : ℝ}
    (h_lin_bound : ∀ x ∈ Set.Icc p1 p2, |f x - (f p1 + t * (x - p1))| ≤ E_lin)
    (h_endpoint : |f a - (f p1 + t * (a - p1))| ≤ E_end)
    (ha_ge_p1 : p1 ≤ a) (hk_nonneg : 0 ≤ k) (hak_le_p2 : a + k ≤ p2) :
    |(f (a + k) - f a) - t * k| ≤ E_lin + E_end := by
  have h_ak_ge : p1 ≤ a + k := by linarith
  have h_ak_in : a + k ∈ Set.Icc p1 p2 := ⟨h_ak_ge, hak_le_p2⟩
  have h4 : |f (a + k) - (f p1 + t * ((a + k) - p1))| ≤ E_lin := h_lin_bound (a + k) h_ak_in
  have h5 : |f a - (f p1 + t * (a - p1))| ≤ E_end := h_endpoint
  have h6 : (f (a + k) - f a) - t * k =
      (f (a + k) - (f p1 + t * ((a + k) - p1))) -
      (f a - (f p1 + t * (a - p1))) := by ring
  rw [h6]
  have h7 : |(f (a + k) - (f p1 + t * ((a + k) - p1))) -
      (f a - (f p1 + t * (a - p1)))| ≤
      |f (a + k) - (f p1 + t * ((a + k) - p1))| +
      |f a - (f p1 + t * (a - p1))| := abs_sub _ _
  have h8 : |f (a + k) - (f p1 + t * ((a + k) - p1))| + |f a - (f p1 + t * (a - p1))| ≤ E_lin + E_end := by
    exact add_le_add h4 h5
  exact le_trans h7 h8

/-- Code function lower bound from ε-superlinearity:
    f(a+k)-f(a) ≥ s*k - (E_lin + E_end). -/
lemma superlinear_code_lower_lemma {f : ℝ → ℝ} {a k p1 p2 s E_lin E_end : ℝ}
    (h_super_bound : ∀ x ∈ Set.Icc p1 p2, f x ≥ f p1 + s * (x - p1) - E_lin)
    (h_fa_upper : f a ≤ f p1 + E_end)
    (hs_nonneg : 0 ≤ s) (ha_ge_p1 : p1 ≤ a) (hk_nonneg : 0 ≤ k) (hak_le_p2 : a + k ≤ p2) :
    f (a + k) - f a ≥ s * k - (E_lin + E_end) := by
  have h_ak_ge : p1 ≤ a + k := by linarith
  have h_ak_in : a + k ∈ Set.Icc p1 p2 := ⟨h_ak_ge, hak_le_p2⟩
  have h4 : f (a + k) ≥ f p1 + s * ((a + k) - p1) - E_lin := h_super_bound (a + k) h_ak_in
  have h5 : f a ≤ f p1 + E_end := h_fa_upper
  have h6 : 0 ≤ s * (a - p1) := mul_nonneg hs_nonneg (sub_nonneg.mpr ha_ge_p1)
  nlinarith

/-- Bound `4*K ≤ η*m` from `K ≤ 1/τ₀` and `4/(η*τ₀) ≤ m0 ≤ m`. -/
lemma four_K_le_eta_m (K : ℕ) (τ₀ η m m0 : ℝ)
    (hτ₀_pos : 0 < τ₀) (hη_pos : 0 < η)
    (hm0_ητ₀ : 4 / (η * τ₀) ≤ m0) (hm : m0 ≤ m)
    (hK_le : (K : ℝ) ≤ 1 / τ₀) :
    4 * (K : ℝ) ≤ η * m := by
  have h1 : 4 * (K : ℝ) ≤ 4 / τ₀ := by
    have h_pos4 : (0 : ℝ) ≤ 4 := by norm_num
    have h : 4 * (K : ℝ) ≤ 4 * (1 / τ₀) := mul_le_mul_of_nonneg_left hK_le h_pos4
    have h2 : 4 * (1 / τ₀) = 4 / τ₀ := by ring
    rw [h2] at h
    exact h
  have h2 : 4 / τ₀ ≤ η * m := by
    have h21 : 4 / τ₀ = η * (4 / (η * τ₀)) := by
      field_simp [hη_pos.ne', hτ₀_pos.ne'] <;> ring
    have h22 : η * (4 / (η * τ₀)) ≤ η * m0 := by
      gcongr <;> exact hm0_ητ₀
    have h23 : η * m0 ≤ η * m := by
      gcongr <;> exact hm
    rw [h21]
    exact le_trans h22 h23
  exact le_trans h1 h2

/-- Slope sum lower bound chain: from Kaufman slope bound and rounding loss,
    derive sumSlopeLen ≥ (t - ε_bad)*m.
    `slope_sum` uses the Kaufman order `(len * slope)`. -/
lemma slope_lower_bound (t A A_kauf ε_kauf ε_bad η m : ℝ) (K : ℕ)
    (sumSlopeLen slope_sum : ℝ)
    (hA_kauf_eq_A : A_kauf = A)
    (hI_slope_sum : (t - A_kauf * ε_kauf) * m ≤ slope_sum)
    (h_slope_sum : sumSlopeLen ≥ slope_sum - 4 * (K : ℝ))
    (h4K : 4 * (K : ℝ) ≤ η * m)
    (hε_bad_def : ε_bad = A * ε_kauf + η) :
    sumSlopeLen ≥ (t - ε_bad) * m := by
  have h_slope_kauf : (t - A * ε_kauf) * m ≤ slope_sum := by
    rw [hA_kauf_eq_A] at hI_slope_sum
    exact hI_slope_sum
  have h_slope_lower1 : sumSlopeLen ≥ (t - A * ε_kauf) * m - 4 * (K : ℝ) := by
    linarith
  have h : (t - ε_bad) * m = (t - A * ε_kauf) * m - η * m := by
    rw [hε_bad_def] <;> ring
  rw [h]
  linarith

/-- No consecutive bad blocks: if j is bad, then j+1 is not bad. -/
lemma no_consecutive_bad {n : ℕ} {blocks : List (ℕ × ℕ × Bool × ℝ)} (hn : blocks.length = n)
    {B : Finset (Fin n)}
    (hB_def : ∀ (j : Fin n), j ∈ B ↔ ¬MultiscaleBlockConversion.isStruct (blocks.get (Fin.cast hn.symm j)))
    (h_no_bad : ∀ (j : ℕ) (hj1 : j + 1 < n),
      ¬(¬MultiscaleBlockConversion.isStruct (blocks.get (Fin.cast hn.symm ⟨j, Nat.lt_of_succ_lt hj1⟩)) ∧
        ¬MultiscaleBlockConversion.isStruct (blocks.get (Fin.cast hn.symm ⟨j+1, hj1⟩)))) :
    ∀ (j : Fin n), j ∈ B → ∀ (k : Fin n), k.val = j.val + 1 → k ∉ B := by
  intro j hj k hk
  have h1 : j.val + 1 < n := hk ▸ k.is_lt
  have h4 := h_no_bad j.val h1
  have h_j_bad : ¬MultiscaleBlockConversion.isStruct (blocks.get (Fin.cast hn.symm j)) :=
    (hB_def j).mp hj
  have h5 : MultiscaleBlockConversion.isStruct (blocks.get (Fin.cast hn.symm ⟨j.val + 1, h1⟩)) := by
    by_contra h6
    exact h4 ⟨h_j_bad, h6⟩
  have h_k_struct : MultiscaleBlockConversion.isStruct (blocks.get (Fin.cast hn.symm k)) := by
    have h_k_eq : k = ⟨j.val + 1, h1⟩ := Fin.ext hk
    rw [h_k_eq]
    exact h5
  have h_k_not_B : k ∉ B := by
    intro h_contra
    have h_k_bad : ¬MultiscaleBlockConversion.isStruct (blocks.get (Fin.cast hn.symm k)) :=
      (hB_def k).mp h_contra
    exact h_k_bad h_k_struct
  exact h_k_not_B

/-- Linear case error bound: δ_lin * L + 4 ≤ ε_bad * levels. -/
lemma linear_error_bound (δ_lin ε_bad η L levels : ℝ)
    (hδ_lin_nonneg : 0 ≤ δ_lin)
    (hδ_lin_eq : δ_lin = ε_bad - η)
    (hδ_lin_lt2 : δ_lin < 2)
    (hL_le_levels2 : L ≤ levels + 2)
    (h_eta_levels_ge8 : 8 ≤ η * levels) :
    δ_lin * L + 4 ≤ ε_bad * levels := by
  have h1 : δ_lin * L + 4 ≤ δ_lin * (levels + 2) + 4 := by
    have h11 : δ_lin * L ≤ δ_lin * (levels + 2) := mul_le_mul_of_nonneg_left hL_le_levels2 hδ_lin_nonneg
    linarith
  have h2 : δ_lin * (levels + 2) + 4 = δ_lin * levels + 2 * δ_lin + 4 := by ring
  rw [h2] at h1
  have h4 : 2 * δ_lin + 4 < 8 := by linarith
  have h3 : 2 * δ_lin + 4 < η * levels := lt_of_lt_of_le h4 h_eta_levels_ge8
  have h6 : δ_lin * levels + 2 * δ_lin + 4 ≤ δ_lin * levels + η * levels := by linarith
  have h7 : δ_lin * levels + η * levels = ε_bad * levels := by
    rw [hδ_lin_eq] <;> ring
  exact le_trans h1 (le_trans h6 h7.le)

/-- Superlinear case error bound: δ_lin * L + 2 ≤ ε_bad * levels. -/
lemma superlinear_error_bound (δ_lin ε_bad η L levels : ℝ)
    (hδ_lin_nonneg : 0 ≤ δ_lin)
    (hδ_lin_eq : δ_lin = ε_bad - η)
    (hδ_lin_lt2 : δ_lin < 2)
    (hL_le_levels2 : L ≤ levels + 2)
    (h_eta_levels_ge8 : 8 ≤ η * levels) :
    δ_lin * L + 2 ≤ ε_bad * levels := by
  have h1 : δ_lin * L + 2 ≤ δ_lin * (levels + 2) + 2 := by
    have h11 : δ_lin * L ≤ δ_lin * (levels + 2) := mul_le_mul_of_nonneg_left hL_le_levels2 hδ_lin_nonneg
    linarith
  have h2 : δ_lin * (levels + 2) + 2 = δ_lin * levels + 2 * δ_lin + 2 := by ring
  rw [h2] at h1
  have h4 : 2 * δ_lin + 2 < 8 := by linarith
  have h3 : 2 * δ_lin + 2 < η * levels := lt_of_lt_of_le h4 h_eta_levels_ge8
  have h6 : δ_lin * levels + 2 * δ_lin + 2 ≤ δ_lin * levels + η * levels := by linarith
  have h7 : δ_lin * levels + η * levels = ε_bad * levels := by
    rw [hδ_lin_eq] <;> ring
  exact le_trans h1 (le_trans h6 h7.le)

/-- Homothety image of a dyadic square subset is contained in the unit square. -/
lemma homothety_image_subset {P : Set EuclideanPlane} {δ : ℝ} (hδ_pos : 0 < δ)
    (c d : ℤ) :
    (homothetyS δ c d '' (P ∩ dyadicSquare δ c d)) ⊆ dyadicSquare 1 0 0 := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  have hxQ : x ∈ dyadicSquare δ c d := hx.2
  simp only [dyadicSquare, Set.mem_setOf_eq, Set.mem_Ico] at hxQ
  have h10 : (homothetyS δ c d x) 0 = (x 0 - (c : ℝ) * δ) / δ := by
    simp [homothetyS] <;> ring
  have h11 : (homothetyS δ c d x) 1 = (x 1 - (d : ℝ) * δ) / δ := by
    simp [homothetyS] <;> ring
  have h_goal0 : (homothetyS δ c d x) 0 ∈ Set.Ico (0 : ℝ) 1 := by
    rw [h10]
    constructor
    · exact div_nonneg (by linarith [hxQ.1.1]) hδ_pos.le
    · have h : (x 0 - (c : ℝ) * δ) / δ < 1 := by
        rw [div_lt_one hδ_pos] <;> linarith [hxQ.1.2]
      exact h
  have h_goal1 : (homothetyS δ c d x) 1 ∈ Set.Ico (0 : ℝ) 1 := by
    rw [h11]
    constructor
    · exact div_nonneg (by linarith [hxQ.2.1]) hδ_pos.le
    · have h : (x 1 - (d : ℝ) * δ) / δ < 1 := by
        rw [div_lt_one hδ_pos] <;> linarith [hxQ.2.2]
      exact h
  simpa [dyadicSquare, Set.mem_setOf_eq] using ⟨h_goal0, h_goal1⟩

/-- Multiscale decomposition via combinatorial Kaufman lemma.

    NOTE ON AMPLIFIED ε_bad:
    The Kaufman decomposition has an amplification constant A = 1 + 6/(t-s) > 1.
    The S-set lower bound on the code function has error ε + c_Δ (where
    c_Δ = log 9 / log(1/Δ)). Kaufman requires input error ε_K ≥ ε + c_Δ + O(1),
    and outputs bad length A·ε_K. Therefore the bad product bound uses an
    amplified exponent ε_bad = A·ε_K, not the original ε.

    The outer final proof chooses ε(s,t) small enough that ε_bad is also small. -/
theorem multiscaleDecompKaufman {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t ≤ 2)
    {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hΔ2 : Δ ≤ 1 / 2)
    {ε ε_K : ℝ} (hε : 0 < ε) (hεK_pos : 0 < ε_K)
    (hεK : ε + 2 * Real.log 9 / Real.log (1 / Δ) ≤ ε_K)
    (hKaufman : (1 + 6 / (t - s)) * ε_K < t - s)
    (hΔ_dyadic : ∃ (n : ℕ), 0 < n ∧ (1 : ℝ) = (n : ℝ) * Δ) :
    ∃ (τ ε_bad : ℝ), 0 < τ ∧ τ ≤ ε ∧ 0 < ε_bad ∧
      ε_bad ≤ (3 + 12 / (t - s)) * ε_K ∧
    ∃ (m0 : ℕ),
    ∀ (m : ℕ), m ≥ m0 →
    ∀ (P : Set EuclideanPlane) (N : ℕ → ℕ),
      P ⊆ Metric.closedBall (0 : EuclideanPlane) 1 →
      IsDyadicUniform P m Δ N →
      IsDeltaSSet (Δ ^ m) t (Real.rpow (Δ ^ m) (-ε)) P →
      ∃ (n : ℕ) (i : ℕ → ℕ) (t_j : ℕ → ℝ)
        (S B : Finset (Fin n)),
        (i 0 = 0) ∧ (i n = m) ∧
        (∀ j < n, i j < i (j + 1)) ∧
        (∀ j : Fin n, t_j j.val ∈ Set.Icc s 2) ∧
        (S ∪ B = Finset.univ) ∧ (Disjoint S B) ∧
        -- (i) structured scales have large ratio; bad scales small product
        (∀ j : Fin n, j ∈ S →
          (Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1)) ≥
            Real.rpow (Δ ^ m) (-τ)) ∧
        (∏ j ∈ B, ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ≤
          Real.rpow (Δ ^ m) (-ε_bad)) ∧
        -- (ii) structured scales have set/regular properties
        (∀ j : Fin n, j ∈ S →
          let δ_j := Δ ^ i (j.val + 1)
          let Δ_j := Δ ^ i j.val
          let ratio := (Δ_j / δ_j : ℝ)
          let levels := i (j.val + 1) - i j.val
          IsSetBetweenScales P δ_j Δ_j (t_j j.val)
            ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow ratio ε_bad) ∧
          (t_j j.val > s →
            IsRegularBetweenScales P δ_j Δ_j (t_j j.val)
              ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow ratio ε_bad)
              ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow ratio ε_bad))) ∧
        -- (iii) product over structured scales
        (∏ j ∈ S, Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) (t_j j.val) ≥
          Real.rpow (Δ ^ m) (ε_bad - t)) ∧
        -- (iv) no consecutive bad indices
        (∀ j : Fin n, j ∈ B →
          ∀ k : Fin n, k.val = j.val + 1 → k ∉ B) := by
  -- Constants
  set d : ℝ := t - s with hd_def
  have hd_pos : 0 < d := by linarith
  set A : ℝ := 1 + 6 / d with hA_def
  have hA_pos : 0 < A := by
    dsimp only [A, hA_def]
    have h : 0 < 6 / d := by positivity
    linarith
  have hA_gt_one : 1 < A := by
    dsimp only [A, hA_def]
    have h : 0 < 6 / d := by positivity
    linarith
  have hAεK_lt_d : A * ε_K < d := by
    simpa [hA_def] using hKaufman
  -- Choose η > 0 small relative to ε_K such that A*(ε_K + η) < d
  have h_gap : 0 < d - A * ε_K := by linarith
  set η : ℝ := min ε_K ((d - A * ε_K) / (2 * A)) with hη_def
  have hη_pos : 0 < η := by
    apply lt_min hεK_pos
    positivity
  have hη_le_epsK : η ≤ ε_K := min_le_left _ _
  have hη_le_half : η ≤ (d - A * ε_K) / (2 * A) := min_le_right _ _
  have hAεη_lt_d : A * (ε_K + η) < d := by
    have h1 : A * η ≤ (d - A * ε_K) / 2 := by
      have h2 : A * η ≤ A * ((d - A * ε_K) / (2 * A)) := by gcongr
      have h3 : A * ((d - A * ε_K) / (2 * A)) = (d - A * ε_K) / 2 := by
        field_simp [hA_pos.ne'] <;> ring
      linarith
    linarith
  set ε_kauf : ℝ := ε_K + η with hεkauf_def
  set ε_bad : ℝ := A * ε_kauf + η with hε_bad_def
  have hε_bad_pos : 0 < ε_bad := by positivity
  have hε_bad_lt_d : ε_bad < d := by
    set g : ℝ := d - A * ε_K with hg_def
    have hg_pos : 0 < g := h_gap
    have h1 : A * ε_K = d - g := by linarith
    have h2 : A * η ≤ g / 2 := by
      have h3 : A * η ≤ A * (g / (2 * A)) := by gcongr <;> linarith [hη_le_half, hg_def]
      have h4 : A * (g / (2 * A)) = g / 2 := by field_simp [hA_pos.ne'] <;> ring
      linarith
    have h5 : (A + 1) * η ≤ (A + 1) * (g / (2 * A)) := by gcongr <;> linarith [hη_le_half, hg_def]
    have h6 : ε_bad = A * ε_K + (A + 1) * η := by
      rw [hε_bad_def, hεkauf_def] <;> ring
    rw [h6]
    have h7 : A * ε_K + (A + 1) * η < d := by
      calc A * ε_K + (A + 1) * η
        ≤ A * ε_K + (A + 1) * (g / (2 * A)) := by gcongr <;> linarith [hη_le_half, hg_def]
      _ = d - g * (A - 1) / (2 * A) := by
        rw [h1]
        field_simp [hA_pos.ne'] <;> ring
      _ < d := by
        have h8 : 0 < g * (A - 1) / (2 * A) := by
          apply div_pos
          · exact mul_pos hg_pos (by linarith)
          · linarith
        linarith
    exact h7
  have hε_bad_le_amplified : ε_bad ≤ (2 * A + 1) * ε_K := by
    have h6 : ε_bad = A * ε_K + (A + 1) * η := by
      rw [hε_bad_def, hεkauf_def] <;> ring
    rw [h6]
    have h7 : (A + 1) * η ≤ (A + 1) * ε_K := by gcongr <;> exact hη_le_epsK
    linarith
  -- Apply combinatorial Kaufman decomposition
  rcases combinatorial_kaufman_decomposition s t hs hst ht with ⟨A_kauf, hA_eq, h_main_kauf⟩
  have hA_kauf_eq : A_kauf = 1 + 6 / (t - s) := hA_eq
  have hA_kauf_pos : 0 < A_kauf := by
    rw [hA_kauf_eq]
    have h : 0 < 6 / (t - s) := by positivity
    linarith
  have hA_kauf_eq_A : A_kauf = A := by
    rw [hA_kauf_eq, hA_def, hd_def] <;> ring
  have hAεK_lt_d2 : A_kauf * ε_K < d := by
    rw [hA_kauf_eq_A]
    exact hAεK_lt_d
  have h_gap2 : 0 < d - A_kauf * ε_K := by linarith
  have hAεη_lt_d2 : A_kauf * (ε_K + η) < d := by
    rw [hA_kauf_eq_A]
    exact hAεη_lt_d
  rcases h_main_kauf ε_kauf (by positivity) hAεη_lt_d2 with ⟨τ₀, hτ₀_pos, hτ₀_le_ε, h_kaufman⟩
  set τ : ℝ := min (τ₀ / 2) ε with hτ_def
  have hτ_pos : 0 < τ := by
    apply lt_min
    · linarith
    · exact hε
  have hτ_le_ε : τ ≤ ε := min_le_right _ _
  have hτ_le_half : τ ≤ τ₀ / 2 := min_le_left _ _
  -- Choose m0 large enough for rounding errors
  let M_val : ℝ := max (max (max (max (4 / τ₀) ((t + 2) / η)) (4 / τ)) (4 / (η * τ₀))) ((8 / η + 2) / τ₀)
  set m0 : ℕ := Nat.ceil M_val with hm0_def
  have hM_le_m0 : M_val ≤ (m0 : ℝ) := Nat.le_ceil M_val
  have hm0_τ₀ : (4 : ℝ) / τ₀ ≤ (m0 : ℝ) := by
    have h : (4 : ℝ) / τ₀ ≤ M_val := by
      simp only [M_val]
      exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_left _ _)))
    linarith
  have hm0_t2 : (t + 2) ≤ η * (m0 : ℝ) := by
    have h : (t + 2) / η ≤ M_val := by
      simp only [M_val]
      exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))
    have h2 : (t + 2) / η ≤ (m0 : ℝ) := by linarith
    have hη_pos' : 0 < η := hη_pos
    have h3 : t + 2 = η * ((t + 2) / η) := by field_simp [hη_pos'.ne'] <;> ring
    rw [h3]
    gcongr
  have hm0_τ : (4 : ℝ) / τ ≤ (m0 : ℝ) := by
    have h : (4 : ℝ) / τ ≤ M_val := by
      simp only [M_val]
      exact le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
    linarith
  have hm0_ητ₀ : (4 : ℝ) / (η * τ₀) ≤ (m0 : ℝ) := by
    have h : (4 : ℝ) / (η * τ₀) ≤ M_val := by
      simp only [M_val]
      exact le_max_of_le_left (le_max_right _ _)
    linarith
  have hm0_block_len : (8 : ℝ) / η + 2 ≤ τ₀ * (m0 : ℝ) := by
    have h : ((8 : ℝ) / η + 2) / τ₀ ≤ M_val := by
      simp only [M_val]
      exact le_max_right _ _
    have h2 : ((8 : ℝ) / η + 2) / τ₀ ≤ (m0 : ℝ) := by linarith
    have h2 : 0 < τ₀ := hτ₀_pos
    calc (8 : ℝ) / η + 2
      = τ₀ * (((8 : ℝ) / η + 2) / τ₀) := by field_simp [h2.ne'] <;> ring
    _ ≤ τ₀ * (m0 : ℝ) := by gcongr
  have hε_bad_bound : ε_bad ≤ (3 + 12 / (t - s)) * ε_K := by
    have h10 : ε_bad ≤ (2 * A + 1) * ε_K := hε_bad_le_amplified
    have h11 : (2 * A + 1) * ε_K = (3 + 12 / (t - s)) * ε_K := by
      have h12 : 2 * A + 1 = 3 + 12 / (t - s) := by
        rw [hA_def, hd_def] <;> ring
      rw [h12]
    rw [h11] at h10
    exact h10
  refine ⟨τ, ε_bad, hτ_pos, hτ_le_ε, hε_bad_pos, hε_bad_bound, m0, ?_⟩
  intro m hm P N hP h_uniform h_sset
  rcases hΔ_dyadic with ⟨n_dyad, hn_pos, h1⟩
  set f : ℝ → ℝ := codeFunction m Δ N with hf_def
  have hm_pos : 0 < m := by
    have h_pos1 : 0 < (4 : ℝ) / τ₀ := by positivity
    have h2 : (4 : ℝ) / τ₀ ≤ (m0 : ℝ) := hm0_τ₀
    have h3 : (m0 : ℝ) > 0 := by linarith
    have h4 : 0 < m0 := by exact_mod_cast h3
    omega
  -- 2-Lipschitz and monotonicity
  have h_lip_raw : ∀ x y, x ∈ Set.Icc 0 (m : ℝ) → y ∈ Set.Icc 0 (m : ℝ) →
      |f x - f y| ≤ 2 * |x - y| :=
    CodeFunctionLipschitz.codeFunction_two_lipschitz h_uniform hn_pos h1
  have h_lip : LipschitzOnWith 2 f (Set.Icc 0 (m : ℝ)) := by
    intro x hx y hy
    have h : |f x - f y| ≤ 2 * |x - y| := h_lip_raw x y hx hy
    have h_edist : edist (f x) (f y) ≤ (2 : ENNReal) * edist x y := by
      simp only [edist_dist, Real.dist_eq]
      have h5 : ENNReal.ofReal |f x - f y| ≤ ENNReal.ofReal (2 * |x - y|) := by
        exact ENNReal.ofReal_le_ofReal h
      have h6 : ENNReal.ofReal (2 * |x - y|) = (2 : ENNReal) * ENNReal.ofReal |x - y| := by
        rw [ENNReal.ofReal_mul (by positivity)]
        <;> norm_cast
      rw [h6] at h5
      exact h5
    exact h_edist
  have h_mono : MonotoneOn f (Set.Icc 0 (m : ℝ)) := by
    exact CodeFunctionLipschitz.codeFunction_monotone h_uniform
  have h_f0 : f 0 = 0 := by simp [hf_def, codeFunction]
  -- Lower bound for integer j
  set c_Δ : ℝ := Real.log 9 / Real.log (1 / Δ) with hcΔ_def
  have hlog1d_pos : 0 < Real.log (1 / Δ) := by
    have h2 : 1 < 1 / Δ := by apply one_lt_one_div <;> linarith
    exact Real.log_pos h2
  have hcΔ_pos : 0 < c_Δ := by positivity
  have h_lower_int : ∀ (j : ℕ), j ≤ m →
      f (j : ℝ) ≥ t * (j : ℝ) - ε_K * (m : ℝ) := by
    intro j hj
    have ht' : 0 ≤ t := by linarith [hs]
    have hlb := CodeFunctionLowerBound.codeFunction_lower_bound h_uniform hΔ hΔ1 ht' hε hj hm_pos hP h_sset
    have h_eq : f (j : ℝ) = codeFunction m Δ N (j : ℝ) := by simp [hf_def]
    rw [h_eq]
    have h_log_eq : Real.log (1 / Δ) = -Real.log Δ := by
      rw [Real.log_div (by norm_num) (by linarith)] <;> simp
    have h_cΔ_eq : c_Δ = Real.log 9 / Real.log (1 / Δ) := by
      simp [hcΔ_def]
    have h_hlb' : codeFunction m Δ N (j : ℝ) ≥
        t * (j : ℝ) - ε * (m : ℝ) - ((m : ℝ) + 1) * c_Δ := by
      have h_eq2 : ((m : ℝ) + 1) * Real.log 9 / Real.log (1 / Δ) =
          ((m : ℝ) + 1) * c_Δ := by
        rw [h_cΔ_eq] <;> ring
      rw [h_eq2] at hlb
      exact hlb
    have h_cΔ_eq2 : 2 * Real.log 9 / Real.log (1 / Δ) = 2 * c_Δ := by
      rw [h_cΔ_eq] <;> ring
    have hεK' : ε + 2 * c_Δ ≤ ε_K := by
      rw [←h_cΔ_eq2]
      exact hεK
    have h_m_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
    have h9 : ε * (m : ℝ) + ((m : ℝ) + 1) * c_Δ ≤ ε_K * (m : ℝ) := by
      have h10 : ε * (m : ℝ) + 2 * c_Δ * (m : ℝ) ≤ ε_K * (m : ℝ) := by
        have h11 : (ε + 2 * c_Δ) * (m : ℝ) ≤ ε_K * (m : ℝ) := by
          gcongr
          <;> linarith
        ring_nf at h11 ⊢ <;> exact h11
      have h12 : ((m : ℝ) + 1) * c_Δ ≤ 2 * c_Δ * (m : ℝ) := by
        have h13 : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
        have h14 : ((m : ℝ) + 1) * c_Δ ≤ (2 * (m : ℝ)) * c_Δ := by
          exact mul_le_mul_of_nonneg_right h13 (by linarith)
        ring_nf at h14 ⊢ <;> exact h14
      linarith
    linarith [h_hlb', h9]
  -- Extend lower bound to all x using 2-Lipschitz
  have h_lower_all : ∀ x ∈ Set.Icc 0 (m : ℝ),
      f x ≥ t * x - ε_kauf * (m : ℝ) := by
    intro x hx
    let j : ℕ := Nat.floor x
    have hj_le : (j : ℝ) ≤ x := Nat.floor_le hx.1
    have hj_lt : x < (j : ℝ) + 1 := Nat.lt_floor_add_one x
    have hj_m : j ≤ m := by
      have h : (j : ℝ) ≤ x := hj_le
      have h2 : x ≤ (m : ℝ) := hx.2
      have h3 : (j : ℝ) ≤ (m : ℝ) := by linarith
      exact_mod_cast h3
    have h1 : f x ≥ f (j : ℝ) - 2 * (x - (j : ℝ)) := by
      have hj_in : (j : ℝ) ∈ Set.Icc (0 : ℝ) (m : ℝ) := by
        have h_j0 : 0 ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
        have h_jm : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hj_m
        exact ⟨h_j0, h_jm⟩
      have h2 : |f x - f (j : ℝ)| ≤ 2 * |x - (j : ℝ)| := h_lip_raw x (j : ℝ) hx hj_in
      have h3 : 0 ≤ x - (j : ℝ) := by linarith
      have h4 : |x - (j : ℝ)| = x - (j : ℝ) := by rw [abs_of_nonneg h3]
      rw [h4] at h2
      have h5 : -(2 * (x - (j : ℝ))) ≤ f x - f (j : ℝ) := (abs_le.mp h2).1
      linarith
    have h5 : f (j : ℝ) ≥ t * (j : ℝ) - ε_K * (m : ℝ) := h_lower_int j hj_m
    have h6 : t * (j : ℝ) ≥ t * x - t := by
      have h7 : x - (j : ℝ) < 1 := by linarith
      have h8 : x < (j : ℝ) + 1 := by linarith
      have h9 : t * x ≤ t * ((j : ℝ) + 1) := by gcongr <;> linarith [ht]
      have h10 : t * ((j : ℝ) + 1) = t * (j : ℝ) + t := by ring
      rw [h10] at h9
      linarith
    have h8 : t + 2 ≤ η * (m : ℝ) := by
      have h9 : (m0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have h10 : t + 2 ≤ η * (m0 : ℝ) := hm0_t2
      have h11 : η * (m0 : ℝ) ≤ η * (m : ℝ) := by gcongr <;> linarith
      linarith
    have h9 : ε_kauf = ε_K + η := hεkauf_def
    rw [h9]
    linarith
  -- Apply Kaufman decomposition
  rcases h_kaufman (m : ℝ) f (by exact_mod_cast hm_pos) h_lip h_mono h_f0 h_lower_all
    with ⟨K, I, hK_pos, hI_disj, hI_bound, hI_cov, hI_slope_sum, hI_good⟩
  -- =====================================================================
  -- BLOCK CONVERSION
  -- Sort intervals, round to integers, build alternating bad/structured blocks.
  -- =====================================================================
  let ints : List (ℝ × ℝ) := (List.finRange K).map I
  let sorted := ints.mergeSort (fun p q => if p.1 ≤ q.1 then true else false)
  have h_sorted_len : sorted.length = K := by
    simp [sorted, ints, List.length_mergeSort]
  have h_sorted_perm : List.Perm sorted ints := List.mergeSort_perm ints _
  have h_sorted_mem : ∀ (p : ℝ × ℝ), p ∈ sorted ↔ ∃ (i : Fin K), I i = p := by
    intro p
    have h : p ∈ sorted ↔ p ∈ ints := (List.mergeSort_perm ints _).mem_iff
    rw [h]
    simp only [ints, List.mem_map, List.mem_finRange]
    <;> constructor
    · rintro ⟨i, _, h_eq⟩
      exact ⟨i, h_eq⟩
    · rintro ⟨i, h_eq⟩
      exact ⟨i, by simp, h_eq⟩
  have h_ints_mem : ∀ (p : ℝ × ℝ), p ∈ ints ↔ ∃ (i : Fin K), I i = p := by
    intro p
    simp only [ints, List.mem_map, List.mem_finRange]
    <;> constructor
    · rintro ⟨i, _, h_eq⟩; exact ⟨i, h_eq⟩
    · rintro ⟨i, h_eq⟩; exact ⟨i, by simp, h_eq⟩
  have h_bound_sorted : ∀ p ∈ sorted, (0 : ℝ) ≤ p.1 ∧ p.2 ≤ (m : ℝ) := by
    intro p hp
    rcases (h_sorted_mem p).mp hp with ⟨i, rfl⟩
    have h := hI_bound i
    exact ⟨h.1, h.2.2.1⟩
  have h_valid_sorted : ∀ p ∈ sorted, p.1 < p.2 := by
    intro p hp
    rcases (h_sorted_mem p).mp hp with ⟨i, rfl⟩
    exact (hI_bound i).2.1
  have hτm_ge4 : τ * (m : ℝ) ≥ 4 := by
    have h1 : (4 : ℝ) / τ ≤ (m0 : ℝ) := hm0_τ
    have h2 : (m0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h3 : (4 : ℝ) / τ ≤ (m : ℝ) := by linarith
    have h4 : 0 < τ := hτ_pos
    calc τ * (m : ℝ) ≥ τ * ((4 : ℝ) / τ) := by gcongr
      _ = 4 := by field_simp [h4.ne'] <;> ring
  have h_round_sorted : ∀ p ∈ sorted, Nat.ceil p.1 < Nat.floor p.2 := by
    intro p hp
    rcases (h_sorted_mem p).mp hp with ⟨i, rfl⟩
    have h_len0 : τ₀ * (m : ℝ) ≤ (I i).2 - (I i).1 := (hI_bound i).2.2.2
    have hτ_leτ0 : τ ≤ τ₀ := by
      have h : τ ≤ τ₀ / 2 := hτ_le_half
      linarith
    have h_len : (I i).2 - (I i).1 ≥ τ * (m : ℝ) := by
      have h1 : τ * (m : ℝ) ≤ τ₀ * (m : ℝ) := by gcongr <;> linarith
      linarith
    have h_ge2 : (I i).2 - (I i).1 ≥ 2 := by linarith
    have h_nonneg : 0 ≤ (I i).1 := (hI_bound i).1
    exact ceil_lt_floor_of_length_ge_two h_nonneg h_ge2
  have h_slopes_sorted : ∀ p ∈ sorted, s ≤ chordSlope f p.1 p.2 ∧ chordSlope f p.1 p.2 ≤ 2 := by
    intro p hp
    rcases (h_sorted_mem p).mp hp with ⟨i, rfl⟩
    rcases hI_good i with (h | h)
    · exact ⟨h.2.1, h.2.2⟩
    · have hsl : chordSlope f (I i).1 (I i).2 = s := h.2
      exact ⟨by linarith [hsl, hs], by linarith [hsl, ht, hst]⟩
  -- h_pairwise: sorted intervals satisfy p.2 ≤ q.1 for p before q
  have h_pairwise : List.Pairwise (fun (p q : ℝ × ℝ) => p.2 ≤ q.1) sorted := by
    let r : ℝ × ℝ → ℝ × ℝ → Prop := fun p q => p.1 ≤ q.1
    have _i_total : Std.Total r := ⟨fun a b => le_total a.1 b.1⟩
    have _i_trans : IsTrans (ℝ × ℝ) r := ⟨fun a b c h1 h2 => le_trans h1 h2⟩
    have h_le : List.Pairwise r sorted := by
      dsimp only [sorted]
      exact List.pairwise_mergeSort' r ints
    have h_all_disj : ∀ (p q : ℝ × ℝ), p ∈ sorted → q ∈ sorted → p ≠ q →
        Disjoint (Set.Ioo p.1 p.2) (Set.Ioo q.1 q.2) := by
      intro p q hp hq hne
      have hp' : p ∈ ints := (h_sorted_perm.mem_iff).mp hp
      have hq' : q ∈ ints := (h_sorted_perm.mem_iff).mp hq
      rcases (h_ints_mem p).mp hp' with ⟨i, rfl⟩
      rcases (h_ints_mem q).mp hq' with ⟨j, rfl⟩
      have hij : i ≠ j := by intro h; apply hne; simp [h]
      exact hI_disj i j hij
    have hI_inj : Function.Injective I := by
      intro i j h
      by_contra hne
      have h_disj := hI_disj i j hne
      have h_v : (I i).1 < (I i).2 := (hI_bound i).2.1
      have h_nonempty : (Set.Ioo (I i).1 (I i).2).Nonempty := by
        refine ⟨(I i).1 + ((I i).2 - (I i).1) / 2, ?_⟩
        constructor <;> linarith
      have h_eq : Set.Ioo (I j).1 (I j).2 = Set.Ioo (I i).1 (I i).2 := by rw [h]
      rw [h_eq] at h_disj
      have h_self_inter : Set.Ioo (I i).1 (I i).2 ∩ Set.Ioo (I i).1 (I i).2 = Set.Ioo (I i).1 (I i).2 := by
        ext x; simp
      have h_inter : (Set.Ioo (I i).1 (I i).2 ∩ Set.Ioo (I i).1 (I i).2).Nonempty := by
        rw [h_self_inter]; exact h_nonempty
      have h_nd : ¬Disjoint (Set.Ioo (I i).1 (I i).2) (Set.Ioo (I i).1 (I i).2) :=
        Set.not_disjoint_iff.mpr h_inter
      exact h_nd h_disj
    have h_nodup_ints : ints.Nodup := by
      simp only [ints, List.nodup_map_iff_inj_on, List.nodup_finRange]
      <;> exact fun i _ j _ h => hI_inj h
    have h_nodup_sorted : sorted.Nodup := by
      rw [List.nodup_mergeSort] <;> exact h_nodup_ints
    let R : (ℝ × ℝ) → (ℝ × ℝ) → Prop := fun p q => Disjoint (Set.Ioo p.1 p.2) (Set.Ioo q.1 q.2)
    have h_disj_sorted : List.Pairwise R sorted :=
      h_nodup_sorted.pairwise_of_forall_ne (fun a ha b hb hne => h_all_disj a b ha hb hne)
    have h_disj_sorted' : CombinatorialKaufman.PairwiseInteriorDisjointList sorted := h_disj_sorted
    have h_strict : CombinatorialKaufman.SortedByLeft sorted :=
      strictSortedOfDisjoint sorted h_le h_disj_sorted' h_valid_sorted
    exact pairwiseEndAfterStartOfSortedDisjoint sorted h_strict h_disj_sorted' h_valid_sorted
  let pos : ℕ := 0
  let blocks := MultiscaleBlockConversion.buildBlocks f s m sorted pos
  let n := blocks.length
  have h_bound_pos : ∀ p ∈ sorted, (pos : ℝ) ≤ p.1 ∧ p.2 ≤ (m : ℝ) := by
    intro p hp
    have h := h_bound_sorted p hp
    simp only [pos] at *
    <;> exact ⟨by simpa using h.1, h.2⟩
  have h_n_pos : 0 < n := by
    have h_adj := MultiscaleBlockConversion.buildBlocks_adjacent f s m sorted pos (by omega) h_pairwise h_bound_pos h_round_sorted
    have h_empty : blocks = [] ↔ (0 : ℕ) = m := h_adj.1
    have h_ne : blocks ≠ [] := by
      intro h
      have h_eq : (0 : ℕ) = m := h_empty.mp h
      omega
    exact List.length_pos_iff_ne_nil.mpr h_ne
  let getBlock (j : Fin n) : ℕ × ℕ × Bool × ℝ := blocks.get j
  let i_fn (j : ℕ) : ℕ :=
    if h : j < n then (blocks.get ⟨j, h⟩).1 else m
  let t_j (j : ℕ) : ℝ :=
    if h : j < n then (blocks.get ⟨j, h⟩).2.2.2 else s
  let S : Finset (Fin n) := Finset.univ.filter (fun j => MultiscaleBlockConversion.isStruct (getBlock j))
  let B : Finset (Fin n) := Finset.univ.filter (fun j => ¬MultiscaleBlockConversion.isStruct (getBlock j))
  have h_blocks_ne : blocks ≠ [] := by
    simpa [n] using h_n_pos.ne'
  -- Key induction lemma
  have h_induction :
      ((blocks.get ⟨0, h_n_pos⟩).1 = 0) ∧
      (∀ (j : ℕ) (hj : j < n), j + 1 = n → (blocks.get ⟨j, hj⟩).2.1 = m) ∧
      (∀ b ∈ blocks, b.1 < b.2.1) ∧
      (∀ (j : ℕ) (hj1 : j + 1 < n),
         (blocks.get ⟨j, Nat.lt_of_succ_lt hj1⟩).2.1 = (blocks.get ⟨j+1, hj1⟩).1) ∧
      (∀ (j : ℕ) (hj1 : j + 1 < n),
         ¬(¬MultiscaleBlockConversion.isStruct (blocks.get ⟨j, Nat.lt_of_succ_lt hj1⟩) ∧
           ¬MultiscaleBlockConversion.isStruct (blocks.get ⟨j+1, hj1⟩))) ∧
      ((MultiscaleBlockConversion.sumStructLen blocks : ℝ) ≥
         ∑ i : Fin K, ((I i).2 - (I i).1) - 2 * (K : ℝ)) ∧
      ((MultiscaleBlockConversion.sumBlockLen blocks : ℝ) = (m : ℝ)) ∧
      ((MultiscaleBlockConversion.sumSlopeLen blocks) ≥
         ∑ i : Fin K, chordSlope f (I i).1 (I i).2 * ((I i).2 - (I i).1) - 4 * (K : ℝ)) := by
    have h_correct := MultiscaleBlockConversion.buildBlocks_correct f s m sorted pos (by omega) h_pairwise h_bound_pos h_round_sorted
    have h_struct_all := MultiscaleBlockConversion.buildBlocks_structural f s m sorted pos (by omega) h_pairwise h_bound_pos h_round_sorted h_slopes_sorted
    rcases h_struct_all with ⟨_, _, h_pos_len, h_adj, h_no_bad_raw, h_last_getLast, _⟩
    have h_head : (blocks.get ⟨0, h_n_pos⟩).1 = 0 := h_correct.2.1 h_n_pos
    have h_total_len : (MultiscaleBlockConversion.sumBlockLen blocks : ℝ) = (m : ℝ) := by
      have h : MultiscaleBlockConversion.sumBlockLen blocks = m - pos := h_correct.2.2.2.1
      simpa [pos] using h
    have h_no_bad : ∀ (j : ℕ) (hj1 : j + 1 < n),
        ¬(¬MultiscaleBlockConversion.isStruct (blocks.get ⟨j, Nat.lt_of_succ_lt hj1⟩) ∧
          ¬MultiscaleBlockConversion.isStruct (blocks.get ⟨j+1, hj1⟩)) := by
      intro j hj1
      have h_or : MultiscaleBlockConversion.isStruct (blocks.get ⟨j, Nat.lt_of_succ_lt hj1⟩) ∨
                  MultiscaleBlockConversion.isStruct (blocks.get ⟨j+1, hj1⟩) :=
        h_no_bad_raw j hj1
      exact fun h_and => h_or.elim (fun h => h_and.1 h) (fun h => h_and.2 h)
    have h_last : ∀ (j : ℕ) (hj : j < n), j + 1 = n → (blocks.get ⟨j, hj⟩).2.1 = m := by
      intro j hj h_jlast
      have h_j_eq : j = n - 1 := by omega
      have h_getLast_eq : blocks.getLast h_blocks_ne = blocks.get ⟨n - 1, Nat.sub_lt h_n_pos (by norm_num)⟩ :=
        (List.get_length_sub_one (Nat.sub_lt h_n_pos (by norm_num))).symm
      have h_eq : blocks.get ⟨j, hj⟩ = blocks.getLast h_blocks_ne := by
        rw [h_getLast_eq]
        congr
        <;> omega
      rw [h_eq]
      exact h_last_getLast h_blocks_ne
    have h_sum_struct_raw : MultiscaleBlockConversion.sumStructLen blocks = (sorted.map MultiscaleBlockConversion.roundedLength).sum :=
      h_correct.2.2.2.2.1
    have h1_sorted : ∀ p ∈ sorted, 0 ≤ p.1 := fun p hp => (h_bound_sorted p hp).1
    have h_rounded_ge_raw : ((sorted.map MultiscaleBlockConversion.roundedLength).sum : ℝ) ≥
        (sorted.map (fun p : ℝ × ℝ => p.2 - p.1)).sum - 2 * (sorted.length : ℝ) :=
      sum_rounded_ge sorted h1_sorted h_round_sorted
    have h_len_eq : (sorted.length : ℝ) = (K : ℝ) := by exact_mod_cast h_sorted_len
    have h_rounded_ge : ((sorted.map MultiscaleBlockConversion.roundedLength).sum : ℝ) ≥
        (sorted.map (fun p : ℝ × ℝ => p.2 - p.1)).sum - 2 * (K : ℝ) := by
      rw [h_len_eq] at h_rounded_ge_raw
      exact h_rounded_ge_raw
    have h_perm1 : (sorted.map (fun p : ℝ × ℝ => p.2 - p.1)).sum = (ints.map (fun p : ℝ × ℝ => p.2 - p.1)).sum :=
      perm_map_sum_eq h_sorted_perm (fun p => p.2 - p.1)
    have h_ints_sum1 : (ints.map (fun p : ℝ × ℝ => p.2 - p.1)).sum = ∑ i : Fin K, ((I i).2 - (I i).1) := by
      have h : (ints.map (fun p : ℝ × ℝ => p.2 - p.1)) = (List.finRange K).map (fun i : Fin K => (I i).2 - (I i).1) := by
        rw [show ints = (List.finRange K).map I from rfl]
        rw [List.map_map]
        <;> rfl
      rw [h]
      have h2 : ((List.finRange K).map (fun i : Fin K => (I i).2 - (I i).1)).sum = ∑ i : Fin K, ((I i).2 - (I i).1) :=
        sum_finRange_map (fun i : Fin K => (I i).2 - (I i).1)
      exact h2
    have h_struct_sum : (MultiscaleBlockConversion.sumStructLen blocks : ℝ) ≥
        ∑ i : Fin K, ((I i).2 - (I i).1) - 2 * (K : ℝ) := by
      have h : (MultiscaleBlockConversion.sumStructLen blocks : ℝ) = (sorted.map MultiscaleBlockConversion.roundedLength).sum := by
        exact_mod_cast h_sum_struct_raw
      rw [h]
      have h2 : ((sorted.map MultiscaleBlockConversion.roundedLength).sum : ℝ) ≥
          (ints.map (fun p : ℝ × ℝ => p.2 - p.1)).sum - 2 * (K : ℝ) := by
        calc
          ((sorted.map MultiscaleBlockConversion.roundedLength).sum : ℝ) ≥
            (sorted.map (fun p : ℝ × ℝ => p.2 - p.1)).sum - 2 * (K : ℝ) := h_rounded_ge
          _ = (ints.map (fun p : ℝ × ℝ => p.2 - p.1)).sum - 2 * (K : ℝ) := by rw [h_perm1]
      rw [h_ints_sum1] at h2
      exact h2
    have h_sum_slope_raw : MultiscaleBlockConversion.sumSlopeLen blocks = (sorted.map (MultiscaleBlockConversion.slopeWeightedLength f)).sum :=
      h_correct.2.2.2.2.2
    have h_slopes_nonneg : ∀ p ∈ sorted, 0 ≤ chordSlope f p.1 p.2 ∧ chordSlope f p.1 p.2 ≤ 2 := by
      intro p hp
      have h : s ≤ chordSlope f p.1 p.2 ∧ chordSlope f p.1 p.2 ≤ 2 := h_slopes_sorted p hp
      have h_pos : 0 ≤ s := by linarith [hs]
      exact ⟨le_trans h_pos h.1, h.2⟩
    have h_slope_ge_raw : (sorted.map (MultiscaleBlockConversion.slopeWeightedLength f)).sum ≥
        (sorted.map (fun p => chordSlope f p.1 p.2 * (p.2 - p.1))).sum - 4 * (sorted.length : ℝ) :=
      sum_slopeWeighted_ge f sorted h_slopes_nonneg h1_sorted h_round_sorted
    have h_slope_ge : (sorted.map (MultiscaleBlockConversion.slopeWeightedLength f)).sum ≥
        (sorted.map (fun p => chordSlope f p.1 p.2 * (p.2 - p.1))).sum - 4 * (K : ℝ) := by
      rw [h_len_eq] at h_slope_ge_raw
      exact h_slope_ge_raw
    have h_perm2 : (sorted.map (fun p : ℝ × ℝ => chordSlope f p.1 p.2 * (p.2 - p.1))).sum =
        (ints.map (fun p : ℝ × ℝ => chordSlope f p.1 p.2 * (p.2 - p.1))).sum :=
      perm_map_sum_eq h_sorted_perm (fun p => chordSlope f p.1 p.2 * (p.2 - p.1))
    have h_ints_sum2 : (ints.map (fun p : ℝ × ℝ => chordSlope f p.1 p.2 * (p.2 - p.1))).sum =
        ∑ i : Fin K, chordSlope f (I i).1 (I i).2 * ((I i).2 - (I i).1) := by
      have h : (ints.map (fun p : ℝ × ℝ => chordSlope f p.1 p.2 * (p.2 - p.1))) =
          (List.finRange K).map (fun i : Fin K => chordSlope f (I i).1 (I i).2 * ((I i).2 - (I i).1)) := by
        rw [show ints = (List.finRange K).map I from rfl]
        rw [List.map_map]
        <;> rfl
      rw [h]
      have h2 : ((List.finRange K).map (fun i : Fin K => chordSlope f (I i).1 (I i).2 * ((I i).2 - (I i).1))).sum =
          ∑ i : Fin K, chordSlope f (I i).1 (I i).2 * ((I i).2 - (I i).1) :=
        sum_finRange_map (fun i : Fin K => chordSlope f (I i).1 (I i).2 * ((I i).2 - (I i).1))
      exact h2
    have h_slope_sum : (MultiscaleBlockConversion.sumSlopeLen blocks) ≥
        ∑ i : Fin K, chordSlope f (I i).1 (I i).2 * ((I i).2 - (I i).1) - 4 * (K : ℝ) := by
      have h : MultiscaleBlockConversion.sumSlopeLen blocks = (sorted.map (MultiscaleBlockConversion.slopeWeightedLength f)).sum :=
        h_sum_slope_raw
      rw [h]
      have h2 : (sorted.map (MultiscaleBlockConversion.slopeWeightedLength f)).sum ≥
          (ints.map (fun p : ℝ × ℝ => chordSlope f p.1 p.2 * (p.2 - p.1))).sum - 4 * (K : ℝ) := by
        calc
          (sorted.map (MultiscaleBlockConversion.slopeWeightedLength f)).sum ≥
            (sorted.map (fun p => chordSlope f p.1 p.2 * (p.2 - p.1))).sum - 4 * (K : ℝ) := h_slope_ge
          _ = (ints.map (fun p : ℝ × ℝ => chordSlope f p.1 p.2 * (p.2 - p.1))).sum - 4 * (K : ℝ) := by rw [h_perm2]
      rw [h_ints_sum2] at h2
      exact h2
    exact ⟨h_head, h_last, h_pos_len, h_adj, h_no_bad, h_struct_sum, h_total_len, h_slope_sum⟩
  rcases h_induction with ⟨h_head, h_last, h_pos_len, h_adj, h_no_bad, h_struct_sum, h_total_len, h_slope_sum⟩
  have h_i0 : i_fn 0 = 0 := by
    have h_eq : i_fn 0 = (blocks.get ⟨0, h_n_pos⟩).1 := by
      simp only [i_fn, dif_pos h_n_pos]
    rw [h_eq]
    exact h_head
  have h_in : i_fn n = m := by
    simp only [i_fn, dif_neg (show ¬n < n from by omega)]
  have h_ij : ∀ (j : ℕ), j < n → i_fn j < i_fn (j + 1) := by
    intro j hj
    have h1 : i_fn j = (blocks.get ⟨j, hj⟩).1 := by
      simp only [i_fn, dif_pos hj]
    have h2 : i_fn (j + 1) = (blocks.get ⟨j, hj⟩).2.1 := by
      by_cases h3 : j + 1 < n
      · simp only [i_fn, dif_pos h3]
        exact Eq.symm (h_adj j h3)
      · have h4 : j + 1 = n := by omega
        have h_i_fn_next : i_fn (j + 1) = m := by
          have h5 : j + 1 = n := h4
          rw [h5]
          simp only [i_fn, dif_neg (show ¬n < n from by omega)]
        rw [h_i_fn_next]
        have h6 : (blocks.get ⟨j, hj⟩).2.1 = m := h_last j hj h4
        exact Eq.symm h6
    rw [h1, h2]
    exact h_pos_len (blocks.get ⟨j, hj⟩) (blocks.get_mem ⟨j, hj⟩)
  have h_tj_range : ∀ (j : Fin n), t_j j.val ∈ Set.Icc s 2 := by
    intro j
    have hj : j.val < n := j.is_lt
    have hsl : s ≤ t_j j.val ∧ t_j j.val ≤ 2 := by
      simp only [t_j, dif_pos hj]
      have h_b_in : blocks.get ⟨j.val, hj⟩ ∈ blocks := blocks.get_mem ⟨j.val, hj⟩
      exact buildBlocks_slope_in_range f s t hs hst ht m sorted pos h_slopes_sorted (blocks.get ⟨j.val, hj⟩) h_b_in
    exact ⟨hsl.1, hsl.2⟩
  have h_S_B_univ : S ∪ B = Finset.univ := by
    ext j
    simp only [S, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    <;> by_cases h : MultiscaleBlockConversion.isStruct (getBlock j) <;> simp [h] <;> tauto
  have h_S_B_disj : Disjoint S B := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [S, B, Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
    exact hj2 hj1
  -- Shared index equality lemmas (proved once, reused in all product sections)
  have h_i_fn_eq1 : ∀ (j : Fin n), i_fn j.val = (getBlock j).1 := by
    intro j
    have h : i_fn j.val = (blocks.get ⟨j.val, j.is_lt⟩).1 := by
      simp only [i_fn, dif_pos j.is_lt]
    simpa [getBlock] using h
  have h_i_fn_eq2 : ∀ (j : Fin n), i_fn (j.val + 1) = (getBlock j).2.1 := by
    intro j
    by_cases h3 : j.val + 1 < n
    · have h : i_fn (j.val + 1) = (blocks.get ⟨j.val + 1, h3⟩).1 := by
        simpa [i_fn] using dif_pos h3
      rw [h]
      exact Eq.symm (h_adj (j.val) h3)
    · have h4 : j.val + 1 = n := by omega
      have h5 : i_fn (j.val + 1) = m := by
        rw [h4]
        simpa [i_fn] using dif_neg (show ¬n < n from by omega)
      rw [h5]
      exact (h_last j.val j.is_lt h4).symm
  have h_block_ratio : ∀ (j : Fin n),
      (Δ ^ i_fn j.val : ℝ) / (Δ ^ i_fn (j.val + 1)) =
      Real.rpow Δ (-(MultiscaleBlockConversion.blockLen (getBlock j) : ℝ)) := by
    intro j
    have h1 := h_i_fn_eq1 j
    have h2 := h_i_fn_eq2 j
    set b := getBlock j with hb_def
    have h_bl : b.1 < b.2.1 := h_pos_len b (blocks.get_mem j)
    have h_cast : ((b.2.1 : ℝ) - (b.1 : ℝ)) = (MultiscaleBlockConversion.blockLen b : ℝ) := by
      have h : (MultiscaleBlockConversion.blockLen b : ℝ) = (b.2.1 : ℝ) - (b.1 : ℝ) := by
        simp [MultiscaleBlockConversion.blockLen, Nat.cast_sub (le_of_lt h_bl)] <;> norm_cast
      exact h.symm
    rw [h1, h2]
    have h := ratio_eq_rpow hΔ h_bl
    rw [h_cast] at * <;> exact h
  -- Property (i): structured ratio bound
  have h_struct_ratio : ∀ (j : Fin n), j ∈ S →
      (Δ ^ i_fn j.val : ℝ) / (Δ ^ i_fn (j.val + 1)) ≥ Real.rpow (Δ ^ m) (-τ) := by
    intro j hj
    let b := getBlock j
    have h_b_struct : MultiscaleBlockConversion.isStruct b := (Finset.mem_filter.mp hj).2
    have h_b_in : b ∈ blocks := blocks.get_mem j
    have hm0_τ₀_m : (4 : ℝ) / τ₀ ≤ (m : ℝ) := by
      have h1 : (4 : ℝ) / τ₀ ≤ (m0 : ℝ) := hm0_τ₀
      have h2 : (m0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    -- Per-block correspondence: structured block comes from an interval
    have h_corr := MultiscaleBlockConversion.buildBlocks_per_block_correspondence
        f s m sorted pos (by omega) h_bound_pos h_valid_sorted h_pairwise b h_b_in h_b_struct
    rcases h_corr with ⟨p, hp_in, hb1, hb2, hb3⟩
    -- p corresponds to some I i
    rcases (h_sorted_mem p).mp hp_in with ⟨i, rfl⟩
    have h_interval_len : (I i).2 - (I i).1 ≥ τ₀ * (m : ℝ) := (hI_bound i).2.2.2
    have hp1_nonneg : 0 ≤ (I i).1 := (hI_bound i).1
    have hp1_lt_p2 : (I i).1 < (I i).2 := (hI_bound i).2.1
    have hp2_nonneg : 0 ≤ (I i).2 := by linarith
    have h_ceil_lt_floor : Nat.ceil (I i).1 < Nat.floor (I i).2 :=
      h_round_sorted (I i) ((h_sorted_mem (I i)).mpr ⟨i, rfl⟩)
    have h_ceil_le_floor : Nat.ceil (I i).1 ≤ Nat.floor (I i).2 := le_of_lt h_ceil_lt_floor
    have h_block_len : MultiscaleBlockConversion.blockLen b = Nat.floor (I i).2 - Nat.ceil (I i).1 := by
      simp [MultiscaleBlockConversion.blockLen, hb1, hb2] <;> omega
    have h_block_len_eq : (MultiscaleBlockConversion.blockLen b : ℝ) =
        (Nat.floor (I i).2 : ℝ) - (Nat.ceil (I i).1 : ℝ) := by
      rw [h_block_len, Nat.cast_sub h_ceil_le_floor] <;> rfl
    -- Rounded length ≥ τ*m
    have h_len_ge : (MultiscaleBlockConversion.blockLen b : ℝ) ≥ τ * (m : ℝ) := by
      rw [h_block_len_eq]
      exact MultiscaleBlockConversion.struct_block_len_ge_tau (I i)
        (by exact_mod_cast hm_pos) hτ₀_pos hτ_le_half hm0_τ₀_m hp1_nonneg hp2_nonneg h_interval_len
    -- Use shared ratio lemma
    have h_ratio : (Δ ^ i_fn j.val : ℝ) / (Δ ^ i_fn (j.val + 1)) =
        Real.rpow Δ (-(MultiscaleBlockConversion.blockLen b : ℝ)) := h_block_ratio j
    rw [h_ratio]
    have h5 : -(MultiscaleBlockConversion.blockLen b : ℝ) ≤ -τ * (m : ℝ) := by linarith [h_len_ge]
    have h6 : Real.rpow Δ (-(MultiscaleBlockConversion.blockLen b : ℝ)) ≥ Real.rpow Δ (-τ * (m : ℝ)) :=
      rpow_decreasing hΔ hΔ1 h5
    have h7 : Real.rpow Δ (-τ * (m : ℝ)) = Real.rpow (Δ ^ m) (-τ) := rpow_Δ_m hΔ
    rw [h7] at h6
    exact h6
  -- Property (i): bad product bound
  have h_bad_product :
      (∏ j ∈ B, ((Δ ^ i_fn j.val : ℝ) / (Δ ^ i_fn (j.val + 1)))) ≤
        Real.rpow (Δ ^ m) (-ε_bad) := by
    -- Each ratio = Δ^(-blockLen), using shared lemma
    have h_prod_eq : (∏ j ∈ B, ((Δ ^ i_fn j.val : ℝ) / (Δ ^ i_fn (j.val + 1)))) =
        Real.rpow Δ (-(∑ j ∈ B, (MultiscaleBlockConversion.blockLen (getBlock j) : ℝ))) := by
      have h9 : ∏ j ∈ B, ((Δ ^ i_fn j.val : ℝ) / (Δ ^ i_fn (j.val + 1))) =
          ∏ j ∈ B, Real.rpow Δ (-(MultiscaleBlockConversion.blockLen (getBlock j) : ℝ)) := by
        apply Finset.prod_congr rfl
        intro j _
        exact h_block_ratio j
      rw [h9]
      rw [MultiscaleBlockConversion.prod_rpow_eq B (fun j => -(MultiscaleBlockConversion.blockLen (getBlock j) : ℝ)) Δ hΔ]
      rw [Finset.sum_neg_distrib] <;> rfl
    rw [h_prod_eq]
    -- Bad sum = total - structured
    have hS_def : ∀ (j : Fin n), j ∈ S ↔ MultiscaleBlockConversion.isStruct (getBlock j) := by
      intro j
      dsimp only [S]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      <;> rfl
    have h_bad_sum_eq : (∑ j ∈ B, (MultiscaleBlockConversion.blockLen (getBlock j) : ℝ)) =
        (MultiscaleBlockConversion.sumBlockLen blocks : ℝ) - (MultiscaleBlockConversion.sumStructLen blocks : ℝ) :=
      MultiscaleBlockConversion.bad_sum_eq_total_minus_struct S B h_S_B_univ h_S_B_disj hS_def h_pos_len
    -- Interval count bound: K ≤ 1/τ₀
    have h_m_pos' : 0 < (m : ℝ) := by exact_mod_cast hm_pos
    have hK_le : (K : ℝ) ≤ 1 / τ₀ := by
      exact MultiscaleBlockConversion.interval_count_le (m := (m : ℝ)) h_m_pos' hτ₀_pos
        (fun i j hne => hI_disj i j hne) hI_bound
    -- 2K ≤ η*m
    have hm0_ητ₀_m : 4 / (η * τ₀) ≤ (m : ℝ) := by
      have h1 : 4 / (η * τ₀) ≤ (m0 : ℝ) := hm0_ητ₀
      have h2 : (m0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      exact le_trans h1 h2
    have h2K : 2 * (K : ℝ) ≤ η * (m : ℝ) :=
      MultiscaleBlockConversion.twoK_le_eta_m hK_le hτ₀_pos hη_pos hm0_ητ₀_m
    -- Structured sum lower bound
    have h_struct_lower : (MultiscaleBlockConversion.sumStructLen blocks : ℝ) ≥ (1 - A * ε_kauf) * (m : ℝ) - 2 * (K : ℝ) := by
      have h_cov' : (1 - A_kauf * ε_kauf) * (m : ℝ) ≤ ∑ i : Fin K, ((I i).2 - (I i).1) := hI_cov
      have h_cov_A : (1 - A * ε_kauf) * (m : ℝ) ≤ ∑ i : Fin K, ((I i).2 - (I i).1) := by
        rw [hA_kauf_eq_A] at h_cov'; exact h_cov'
      linarith [h_struct_sum]
    -- Bad sum ≤ ε_bad * m
    have h_bad_sum_le : (∑ j ∈ B, (MultiscaleBlockConversion.blockLen (getBlock j) : ℝ)) ≤ ε_bad * (m : ℝ) := by
      rw [h_bad_sum_eq]
      have h_total : (MultiscaleBlockConversion.sumBlockLen blocks : ℝ) = (m : ℝ) := h_total_len
      rw [h_total]
      linarith [h_struct_lower, h2K, hε_bad_def]
    -- Final: Δ^(-bad_sum) ≤ Δ^(-ε_bad*m)
    have h9 : -ε_bad * (m : ℝ) ≤ -(∑ j ∈ B, (MultiscaleBlockConversion.blockLen (getBlock j) : ℝ)) := by
      linarith [h_bad_sum_le]
    have h10 : Real.rpow Δ (-(∑ j ∈ B, (MultiscaleBlockConversion.blockLen (getBlock j) : ℝ))) ≤
        Real.rpow Δ (-ε_bad * (m : ℝ)) :=
      rpow_decreasing hΔ hΔ1 h9
    have h11 : Real.rpow Δ (-ε_bad * (m : ℝ)) = Real.rpow (Δ ^ m) (-ε_bad) := rpow_Δ_m hΔ
    rw [h11] at h10
    exact h10
  -- Property (ii): set/regular properties
  have h_property_ii : ∀ (j : Fin n), j ∈ S →
      let δ_j := Δ ^ i_fn (j.val + 1)
      let Δ_j := Δ ^ i_fn j.val
      let ratio := (Δ_j / δ_j : ℝ)
      let levels := i_fn (j.val + 1) - i_fn j.val
      IsSetBetweenScales P δ_j Δ_j (t_j j.val)
        ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow ratio ε_bad) ∧
      (t_j j.val > s →
        IsRegularBetweenScales P δ_j Δ_j (t_j j.val)
          ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow ratio ε_bad)
          ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow ratio ε_bad)) := by
    intro j hj
    let b := getBlock j
    let a_idx := i_fn j.val
    let b_idx := i_fn (j.val + 1)
    let levels := b_idx - a_idx
    let t_val := t_j j.val
    let C_j := (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow ((Δ ^ a_idx : ℝ) / (Δ ^ b_idx)) ε_bad
    have h_b_struct : MultiscaleBlockConversion.isStruct b := (Finset.mem_filter.mp hj).2
    have h_b_in : b ∈ blocks := blocks.get_mem j
    have h_corr := MultiscaleBlockConversion.buildBlocks_per_block_correspondence
        f s m sorted pos (by omega) h_bound_pos h_valid_sorted h_pairwise b h_b_in h_b_struct
    rcases h_corr with ⟨p, hp_in, hb1, hb2, hb3⟩
    rcases (h_sorted_mem p).mp hp_in with ⟨i, rfl⟩
    let p1 := (I i).1
    let p2 := (I i).2
    let L := p2 - p1
    have h_bl : b.1 < b.2.1 := h_pos_len b h_b_in
    have hi_fn_j : i_fn j.val = b.1 := h_i_fn_eq1 j
    have hi_fn_j1 : i_fn (j.val + 1) = b.2.1 := h_i_fn_eq2 j
    have ha_idx_eq : a_idx = Nat.ceil p1 := by
      have h_eq1 : a_idx = i_fn j.val := by rfl
      rw [h_eq1, hi_fn_j]; exact hb1
    have hb_idx_eq : b_idx = Nat.floor p2 := by
      have h_eq1 : b_idx = i_fn (j.val + 1) := by rfl
      rw [h_eq1, hi_fn_j1]; exact hb2
    have ht_eq : t_val = chordSlope f p1 p2 := by
      have h_eq1 : t_val = t_j j.val := by rfl
      have h_tj : t_j j.val = (blocks.get ⟨j.val, j.is_lt⟩).2.2.2 := by
        dsimp only [t_j]; rw [dif_pos j.is_lt]
      have h_eq : (blocks.get ⟨j.val, j.is_lt⟩) = b := by rfl
      rw [h_eq1, h_tj, h_eq]; exact hb3
    have h_a_lt_b : a_idx < b_idx := by
      have h_eq1 : a_idx = i_fn j.val := by rfl
      have h_eq2 : b_idx = i_fn (j.val + 1) := by rfl
      rw [h_eq1, h_eq2, hi_fn_j, hi_fn_j1]; exact h_bl
    have h_levels_pos : 0 < levels := by
      dsimp only [levels]; omega
    have hp1_nonneg : 0 ≤ p1 := (hI_bound i).1
    have hp2_nonneg : 0 ≤ p2 := by
      have h2 : p1 < p2 := (hI_bound i).2.1
      linarith [hp1_nonneg, h2]
    have hL_pos : 0 < L := by
      dsimp only [L]
      have h : p1 < p2 := (hI_bound i).2.1
      exact sub_pos.mpr h
    have hL_ge : L ≥ τ₀ * (m : ℝ) := (hI_bound i).2.2.2
    have h_ceil_lt_floor : Nat.ceil p1 < Nat.floor p2 :=
      h_round_sorted (I i) ((h_sorted_mem (I i)).mpr ⟨i, rfl⟩)
    have h_ceil_le_floor : Nat.ceil p1 ≤ Nat.floor p2 := le_of_lt h_ceil_lt_floor
    have h_block_len : MultiscaleBlockConversion.blockLen b = Nat.floor p2 - Nat.ceil p1 := by
      simp [MultiscaleBlockConversion.blockLen, hb1, hb2] <;> omega
    have h_levels_eq_blocklen : (levels : ℝ) = (MultiscaleBlockConversion.blockLen b : ℝ) := by
      have h11 : a_idx = b.1 := by
        have h_eq1 : a_idx = i_fn j.val := by rfl
        rw [h_eq1, hi_fn_j]
      have h22 : b_idx = b.2.1 := by
        have h_eq2 : b_idx = i_fn (j.val + 1) := by rfl
        rw [h_eq2, hi_fn_j1]
      simp [levels, MultiscaleBlockConversion.blockLen, h11, h22] <;> omega
    have h_m_ge4τ₀ : (4 : ℝ) / τ₀ ≤ (m : ℝ) := by
      have h5 : (4 : ℝ) / τ₀ ≤ (m0 : ℝ) := hm0_τ₀
      have h6 : (m0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have h_m_ge4τ : (4 : ℝ) / τ ≤ (m : ℝ) := by
      have h5 : (4 : ℝ) / τ ≤ (m0 : ℝ) := hm0_τ
      have h6 : (m0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have h_len_ge : (MultiscaleBlockConversion.blockLen b : ℝ) ≥ τ * (m : ℝ) := by
      rw [h_block_len, Nat.cast_sub h_ceil_le_floor]
      exact MultiscaleBlockConversion.struct_block_len_ge_tau (I i)
        (by exact_mod_cast hm_pos) hτ₀_pos hτ_le_half h_m_ge4τ₀ hp1_nonneg hp2_nonneg hL_ge
    have h_levels_ge4 : (levels : ℝ) ≥ 4 := by
      rw [h_levels_eq_blocklen]
      have h9 : 0 < τ := hτ_pos
      have hτm_ge4 : τ * (m : ℝ) ≥ 4 := by
        calc τ * (m : ℝ) ≥ τ * ((4 : ℝ) / τ) := by gcongr <;> exact h_m_ge4τ
          _ = 4 := by field_simp [h9.ne'] <;> ring
      linarith [h_len_ge, hτm_ge4]
    have h_levels_eq : (levels : ℝ) = (Nat.floor p2 : ℝ) - (Nat.ceil p1 : ℝ) := by
      rw [h_levels_eq_blocklen, h_block_len, Nat.cast_sub h_ceil_le_floor] <;> rfl
    have h_eta_levels_ge8 : η * (levels : ℝ) ≥ 8 := by
      rw [h_levels_eq]
      have h3 := MultiscaleBlockConversion.rounded_len_ge (I i) hp1_nonneg hp2_nonneg
      have h4 : L ≥ (8 : ℝ) / η + 2 := by
        have h5 : L ≥ τ₀ * (m : ℝ) := hL_ge
        have h6 : τ₀ * (m : ℝ) ≥ (8 : ℝ) / η + 2 := by
          have h7 : (8 : ℝ) / η + 2 ≤ τ₀ * (m0 : ℝ) := hm0_block_len
          have h8 : (m0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          have h9 : τ₀ * (m0 : ℝ) ≤ τ₀ * (m : ℝ) := by gcongr <;> linarith
          exact le_trans h7 h9
        exact le_trans h6 h5
      have h10 : (Nat.floor p2 : ℝ) - (Nat.ceil p1 : ℝ) ≥ L - 2 := h3
      have h11 : η * ((Nat.floor p2 : ℝ) - (Nat.ceil p1 : ℝ)) ≥ η * (L - 2) := by gcongr
      have h12 : η * (L - 2) ≥ 8 := by
        have h13 : L - 2 ≥ (8 : ℝ) / η := by linarith
        have h14 : 0 < η := hη_pos
        calc η * (L - 2) ≥ η * ((8 : ℝ) / η) := by gcongr
          _ = 8 := by field_simp [h14.ne'] <;> ring
      exact le_trans h12 h11
    have hA_gt4 : 4 < A := by
      dsimp only [A, hA_def, hd_def]
      have h1 : t - s < 2 := by
        have h2 : t ≤ 2 := ht
        have h3 : 0 < s := hs
        linarith
      have h4 : 0 < t - s := by linarith [hst]
      have h5 : 6 / (t - s) > 3 := by
        calc 6 / (t - s) > 6 / 2 := by gcongr
          _ = 3 := by norm_num
      linarith
    have h_t_range : t_val ∈ Set.Icc s 2 := h_tj_range j
    have ht_nonneg : 0 ≤ t_val :=
      le_trans hs.le h_t_range.1
    have ht_le4 : t_val ≤ 4 := by
      have h1 : t_val ≤ 2 := h_t_range.2
      linarith
    have h_ratio_eq : ((Δ ^ a_idx : ℝ) / (Δ ^ b_idx)) = Real.rpow Δ (-(levels : ℝ)) := by
      have h1 : b_idx = a_idx + levels := by omega
      have h2 : (Δ ^ a_idx : ℝ) / (Δ ^ b_idx) = (Δ ^ levels : ℝ)⁻¹ := by
        rw [h1, pow_add]
        field_simp [pow_pos hΔ] <;> ring
      rw [h2]
      have h3 : (Δ ^ levels : ℝ) = Real.rpow Δ (levels : ℝ) := by simp
      rw [h3]
      exact (Real.rpow_neg hΔ.le (levels : ℝ)).symm
    have hC_j_eq : C_j = (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-(ε_bad * (levels : ℝ))) := by
      simp only [C_j, h_ratio_eq]
      have h6 : Real.rpow (Real.rpow Δ (-(levels : ℝ))) ε_bad = Real.rpow Δ (-(ε_bad * (levels : ℝ))) := by
        have h7 : Real.rpow (Real.rpow Δ (-(levels : ℝ))) ε_bad = Real.rpow Δ ((-(levels : ℝ)) * ε_bad) := by
          have h_raw : Real.rpow Δ ((-(levels : ℝ)) * ε_bad) = (Real.rpow Δ (-(levels : ℝ))) ^ ε_bad :=
            Real.rpow_mul hΔ.le (-(levels : ℝ)) ε_bad
          exact h_raw.symm
        rw [h7]
        have h8 : (-(levels : ℝ)) * ε_bad = -(ε_bad * (levels : ℝ)) := by ring
        rw [h8]
      rw [h6] <;> ring
    have hL_le_levels2 : L ≤ (levels : ℝ) + 2 := by
      rw [h_levels_eq]
      have h3 := MultiscaleBlockConversion.rounded_len_ge (I i) hp1_nonneg hp2_nonneg
      linarith
    have h_b_le_m : b_idx ≤ m := by
      rw [hb_idx_eq]
      have h1 : (Nat.floor p2 : ℝ) ≤ p2 := Nat.floor_le hp2_nonneg
      have h2 : p2 ≤ (m : ℝ) := (hI_bound i).2.2.1
      exact_mod_cast le_trans h1 h2
    have h_a_le_m : a_idx + levels ≤ m := by
      have h_eq : a_idx + levels = b_idx := by omega
      rw [h_eq]
      exact h_b_le_m
    let δ_lin : ℝ := A_kauf * ε_kauf
    have hδ_lin_eq : δ_lin = ε_bad - η := by
      have h1 : δ_lin = A * ε_kauf := by
        dsimp only [δ_lin]
        rw [hA_kauf_eq_A] <;> ring
      rw [h1]
      have h2 : ε_bad = A * ε_kauf + η := hε_bad_def
      linarith
    have hδ_lin_pos : 0 < δ_lin := by positivity
    have hδ_lin_lt2 : δ_lin < 2 := by
      have h1 : δ_lin = A_kauf * ε_kauf := by rfl
      rw [h1]
      have h2 : A_kauf * ε_kauf < d := hAεη_lt_d2
      have h3 : d < 2 := by
        rw [hd_def]
        have h4 : t - s < 2 := by
          calc t - s < t := by linarith [hs]
            _ ≤ 2 := ht
        exact h4
      linarith
    have hδ_div : ((Δ ^ b_idx : ℝ) / (Δ ^ a_idx : ℝ)) = Δ ^ levels := by
      have h_le : a_idx ≤ b_idx := le_of_lt h_a_lt_b
      have h9 : Δ ^ b_idx = Δ ^ (b_idx - a_idx) * Δ ^ a_idx := by
        rw [← pow_add, Nat.sub_add_cancel h_le]
      have h10 : (Δ ^ (b_idx - a_idx) : ℝ) = (Δ ^ b_idx : ℝ) / (Δ ^ a_idx : ℝ) := by
        rw [h9]
        field_simp [pow_pos hΔ a_idx] <;> ring
      have h11 : b_idx - a_idx = levels := by omega
      rw [h11] at h10
      exact h10.symm
    rcases hI_good i with (h_lin_case | h_super_case)
    · -- Case 1: EpsLinear
      let E := δ_lin * L + 4
      have hE_nonneg : 0 ≤ E := by positivity
      have hE_le : E ≤ ε_bad * (levels : ℝ) :=
        linear_error_bound δ_lin ε_bad η L (levels : ℝ) hδ_lin_pos.le hδ_lin_eq hδ_lin_lt2 hL_le_levels2 h_eta_levels_ge8
      have hC_ok : (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) ≤ C_j := by
        rw [hC_j_eq]
        have h5 : -E ≥ -(ε_bad * (levels : ℝ)) := by exact neg_le_neg hE_le
        have h6 : Real.rpow Δ (-E) ≤ Real.rpow Δ (-(ε_bad * (levels : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1.le h5
        have h7 : 0 ≤ (81 : ℝ) * Real.rpow Δ (-4) :=
          mul_nonneg (by norm_num) (Real.rpow_nonneg hΔ.le _)
        exact mul_le_mul_of_nonneg_left h6 h7
      have h_slope_eq : t_val = (f p2 - f p1) / L := by rw [ht_eq] <;> rfl
      have h_lin_bound : ∀ x ∈ Set.Icc p1 p2, |f x - (f p1 + t_val * (x - p1))| ≤ δ_lin * L := by
        intro x hx
        have h : |f x - chordValue f p1 p2 x| ≤ A_kauf * ε_kauf * L := h_lin_case.1 x hx
        have hδ : A_kauf * ε_kauf * L = δ_lin * L := by
          dsimp only [δ_lin] <;> rfl
        have h' : |f x - chordValue f p1 p2 x| ≤ δ_lin * L := by
          rw [hδ] at h
          exact h
        have h_chord_val : chordValue f p1 p2 x = f p1 + t_val * (x - p1) := by
          have h1 : chordValue f p1 p2 x = f p1 + chordSlope f p1 p2 * (x - p1) := by
            simp [chordValue] <;> ring
          rw [h1]
          have h2 : chordSlope f p1 p2 = t_val := ht_eq.symm
          rw [h2] <;> ring
        rw [h_chord_val] at h'
        exact h'
      have h_endpoint_a : |f (a_idx : ℝ) - (f p1 + t_val * ((a_idx : ℝ) - p1))| ≤ 4 := by
        have h_a_ge_p1 : p1 ≤ (a_idx : ℝ) := by rw [ha_idx_eq] <;> exact Nat.le_ceil p1
        have h_a_lt_p11 : (a_idx : ℝ) - p1 < 1 := by
          have h10 : (a_idx : ℝ) = (Nat.ceil p1 : ℝ) := by exact_mod_cast ha_idx_eq
          rw [h10]
          have h11 : (Nat.ceil p1 : ℝ) < p1 + 1 := Nat.ceil_lt_add_one hp1_nonneg
          linarith
        have h_a_le_m' : (a_idx : ℝ) ≤ (m : ℝ) := by
          have h3 : a_idx ≤ b_idx := le_of_lt h_a_lt_b
          exact_mod_cast le_trans h3 h_b_le_m
        have h_p1_le_m : p1 ≤ (m : ℝ) := by
          have h_p2_le_m : p2 ≤ (m : ℝ) := (hI_bound i).2.2.1
          have h_p1_lt_p2 : p1 < p2 := (hI_bound i).2.1
          exact le_trans h_p1_lt_p2.le h_p2_le_m
        exact endpoint_bound_lemma h_lip_raw (by exact_mod_cast Nat.zero_le a_idx) h_a_le_m'
          hp1_nonneg h_p1_le_m h_a_ge_p1 h_a_lt_p11 ht_nonneg h_t_range.2
      have h_code_bounds : ∀ (k : ℕ), k ≤ levels →
          |codeFunction levels Δ (fun x => N (a_idx + x)) (k : ℝ) - t_val * (k : ℝ)| ≤ E := by
        intro k hk
        let N' := fun x : ℕ => N (a_idx + x)
        have h_a_le_m : a_idx + levels ≤ m := h_a_le_m
        have h_g : codeFunction levels Δ N' (k : ℝ) = f ((a_idx : ℝ) + (k : ℝ)) - f (a_idx : ℝ) :=
          rescaled_codeFunction h_a_le_m h_levels_pos (k : ℝ) (by exact_mod_cast Nat.zero_le k) (by exact_mod_cast hk)
        rw [h_g]
        have h_a_ge_p1 : p1 ≤ (a_idx : ℝ) := by rw [ha_idx_eq] <;> exact Nat.le_ceil p1
        have h_ak_le_p2 : (a_idx : ℝ) + (k : ℝ) ≤ p2 := by
          have hk' : (k : ℝ) ≤ (levels : ℝ) := by exact_mod_cast hk
          have hlev : (levels : ℝ) = (b_idx : ℝ) - (a_idx : ℝ) := by
            dsimp only [levels]
            rw [Nat.cast_sub (le_of_lt h_a_lt_b)]
          have h3 : (b_idx : ℝ) ≤ p2 := by rw [hb_idx_eq] <;> exact Nat.floor_le hp2_nonneg
          linarith
        have h_E_split : δ_lin * L + 4 = E := by rfl
        have h := linear_code_bounds_lemma h_lin_bound h_endpoint_a h_a_ge_p1 (by exact_mod_cast Nat.zero_le k) h_ak_le_p2
        rw [h_E_split] at h
        exact h
      have h_code_lower : ∀ (k : ℕ), k ≤ levels →
          codeFunction levels Δ (fun x => N (a_idx + x)) (k : ℝ) ≥ t_val * (k : ℝ) - E := by
        intro k hk
        have h := h_code_bounds k hk
        have h' : -(E) ≤ codeFunction levels Δ (fun x => N (a_idx + x)) (k : ℝ) - t_val * (k : ℝ) := by
          linarith [abs_le.mp h]
        linarith
      have h_set : IsSetBetweenScales P (Δ ^ b_idx) (Δ ^ a_idx) t_val C_j := by
        have hδ_pos : 0 < (Δ ^ b_idx : ℝ) := by positivity
        have hΔj_pos : 0 < (Δ ^ a_idx : ℝ) := by positivity
        have hδ_le : (Δ ^ b_idx : ℝ) ≤ (Δ ^ a_idx : ℝ) := by
          have h : a_idx ≤ b_idx := le_of_lt h_a_lt_b
          exact pow_le_pow_of_le_one hΔ.le hΔ1.le h
        have hC_pos : 0 < C_j := by
          rw [hC_j_eq]; have h1 : 0 < (81 : ℝ) * Real.rpow Δ (-4) :=
            mul_pos (by norm_num) (Real.rpow_pos_of_pos hΔ _)
          have h2 : 0 < Real.rpow Δ (-(ε_bad * (levels : ℝ))) := Real.rpow_pos_of_pos hΔ _; positivity
        refine' ⟨hδ_pos, hΔj_pos, hδ_le, ht_nonneg, hC_pos, _⟩
        intro c d hQ
        let P' := homothetyS (Δ ^ a_idx) c d '' (P ∩ dyadicSquare (Δ ^ a_idx) c d)
        let N' := fun x : ℕ => N (a_idx + x)
        have h_a_lt_b : a_idx < b_idx := by omega
        have h_b_le_m : b_idx ≤ m := h_b_le_m
        have h_uniform' : IsDyadicUniform P' levels Δ N' :=
          uniform_rescaled_square_dyadic h_uniform h_a_lt_b h_b_le_m hn_pos h1 c d hQ
        have hP'_sub2 : P' ⊆ dyadicSquare 1 0 0 := homothety_image_subset (pow_pos hΔ a_idx) c d
        have h_result : IsDeltaSSet (Δ ^ levels) t_val C_j P' :=
          boundedSlopeToDeltaSSet_minimal h_uniform' hn_pos h1 hΔ hΔ1 hΔ2 t_val E C_j ht_nonneg ht_le4 hE_nonneg hC_ok h_levels_pos h_code_lower hP'_sub2
        simpa [hδ_div] using h_result
      have hP'_sub : ∀ (c d : ℤ), (P ∩ dyadicSquare (Δ ^ a_idx) c d).Nonempty →
          (homothetyS (Δ ^ a_idx) c d '' (P ∩ dyadicSquare (Δ ^ a_idx) c d)) ⊆ dyadicSquare 1 0 0 := by
        intro c d hQ
        have hΔa_pos : 0 < Δ ^ a_idx := by positivity
        exact homothety_image_subset hΔa_pos c d
      have h_reg : t_val > s → IsRegularBetweenScales P (Δ ^ b_idx) (Δ ^ a_idx) t_val C_j C_j := by
        intro hts
        have hC_pos' : 0 < C_j := by
          rw [hC_j_eq]; have h1 : 0 < (81 : ℝ) * Real.rpow Δ (-4) :=
            mul_pos (by norm_num) (Real.rpow_pos_of_pos hΔ _)
          have h2 : 0 < Real.rpow Δ (-(ε_bad * (levels : ℝ))) := Real.rpow_pos_of_pos hΔ _; positivity
        refine' ⟨h_set, hC_pos', _⟩
        intro c d hQ
        let P' := homothetyS (Δ ^ a_idx) c d '' (P ∩ dyadicSquare (Δ ^ a_idx) c d)
        let N' := fun x : ℕ => N (a_idx + x)
        have h_a_lt_b : a_idx < b_idx := by omega
        have h_b_le_m : b_idx ≤ m := h_b_le_m
        have h_uniform' : IsDyadicUniform P' levels Δ N' :=
          uniform_rescaled_square_dyadic h_uniform h_a_lt_b h_b_le_m hn_pos h1 c d hQ
        have hP'_sub2 : P' ⊆ dyadicSquare 1 0 0 := hP'_sub c d hQ
        have hC_half_ok : Real.rpow Δ (-4) * Real.rpow Δ (-E) ≤ C_j := by
          have h_pos : 0 ≤ Real.rpow Δ (-4) * Real.rpow Δ (-E) :=
            mul_nonneg (Real.rpow_nonneg hΔ.le _) (Real.rpow_nonneg hΔ.le _)
          have h_le : Real.rpow Δ (-4) * Real.rpow Δ (-E) ≤
              (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) := by
            have h80 : 0 ≤ (80 : ℝ) := by norm_num
            have h : 0 ≤ (80 : ℝ) * (Real.rpow Δ (-4) * Real.rpow Δ (-E)) :=
              mul_nonneg h80 h_pos
            have h2 : (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) -
                (Real.rpow Δ (-4) * Real.rpow Δ (-E)) =
                (80 : ℝ) * (Real.rpow Δ (-4) * Real.rpow Δ (-E)) := by ring
            linarith
          exact le_trans h_le hC_ok
        have h_result := boundedSlopeHalfScaleCovering_minimal h_uniform' hn_pos h1 hΔ hΔ1 t_val E C_j ht_nonneg ht_le4 hE_nonneg hC_half_ok h_levels_pos h_code_bounds hP'_sub2
        have h9 : (Δ ^ levels : ℝ) = (Δ ^ b_idx : ℝ) / (Δ ^ a_idx : ℝ) := hδ_div.symm
        rw [h9] at h_result
        exact h_result
      exact ⟨h_set, h_reg⟩
    · -- Case 2: EpsSuperlinear
      have ht_eq_s : t_val = s := by
        rw [ht_eq]
        exact h_super_case.2
      let E := δ_lin * L + 2
      have hE_nonneg : 0 ≤ E := by positivity
      have hE_le : E ≤ ε_bad * (levels : ℝ) :=
        superlinear_error_bound δ_lin ε_bad η L (levels : ℝ) hδ_lin_pos.le hδ_lin_eq hδ_lin_lt2 hL_le_levels2 h_eta_levels_ge8
      have hC_ok : (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) ≤ C_j := by
        rw [hC_j_eq]
        have h5 : -E ≥ -(ε_bad * (levels : ℝ)) := by exact neg_le_neg hE_le
        have h6 : Real.rpow Δ (-E) ≤ Real.rpow Δ (-(ε_bad * (levels : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1.le h5
        have h7 : 0 ≤ (81 : ℝ) * Real.rpow Δ (-4) :=
          mul_nonneg (by norm_num) (Real.rpow_nonneg hΔ.le _)
        exact mul_le_mul_of_nonneg_left h6 h7
      have h_super1 : ∀ x ∈ Set.Icc p1 p2, f x ≥ f p1 + s * (x - p1) - δ_lin * L := by
        intro x hx
        have h : f x ≥ chordValue f p1 p2 x - A_kauf * ε_kauf * L := h_super_case.1 x hx
        have hδ : A_kauf * ε_kauf = δ_lin := by dsimp only [δ_lin] <;> rfl
        have h' : f x ≥ chordValue f p1 p2 x - δ_lin * L := by
          rw [show A_kauf * ε_kauf * L = δ_lin * L by rw [hδ]] at h
          exact h
        have h_slope_eq_s : chordSlope f p1 p2 = s := h_super_case.2
        have h_chord_eq : chordValue f p1 p2 x = f p1 + s * (x - p1) := by
          simp [chordValue, h_slope_eq_s] <;> ring
        rw [h_chord_eq] at h'
        exact h'
      have h_a_ge_p1 : p1 ≤ (a_idx : ℝ) := by rw [ha_idx_eq] <;> exact Nat.le_ceil p1
      have h_a_in0 : (a_idx : ℝ) ∈ Set.Icc 0 (m : ℝ) := by
        have h1 : 0 ≤ (a_idx : ℝ) := by exact_mod_cast Nat.zero_le a_idx
        have h2 : (a_idx : ℝ) ≤ (m : ℝ) := by
          have h3 : a_idx ≤ b_idx := le_of_lt h_a_lt_b
          exact_mod_cast le_trans h3 h_b_le_m
        exact ⟨h1, h2⟩
      have h_p1_in0 : p1 ∈ Set.Icc 0 (m : ℝ) := by
        have h1 : 0 ≤ p1 := hp1_nonneg
        have h_p2_le_m : p2 ≤ (m : ℝ) := (hI_bound i).2.2.1
        have h_p1_lt_p2 : p1 < p2 := (hI_bound i).2.1
        have h2 : p1 ≤ (m : ℝ) := le_trans h_p1_lt_p2.le h_p2_le_m
        exact ⟨h1, h2⟩
      have h_lip_a : |f (a_idx : ℝ) - f p1| ≤ 2 * |(a_idx : ℝ) - p1| :=
        h_lip_raw (a_idx : ℝ) p1 h_a_in0 h_p1_in0
      have h_fa_upper : f (a_idx : ℝ) ≤ f p1 + 2 := by
        have h5 : 0 ≤ (a_idx : ℝ) - p1 := by linarith [h_a_ge_p1]
        have h6 : (a_idx : ℝ) - p1 < 1 := by
          have h10 : (a_idx : ℝ) = (Nat.ceil p1 : ℝ) := by exact_mod_cast ha_idx_eq
          rw [h10]
          have h11 : (Nat.ceil p1 : ℝ) < p1 + 1 := Nat.ceil_lt_add_one hp1_nonneg
          linarith
        have h7 : |f (a_idx : ℝ) - f p1| ≤ 2 := by
          have h71 : 2 * ((a_idx : ℝ) - p1) < 2 := by linarith
          have h72 : |(a_idx : ℝ) - p1| = (a_idx : ℝ) - p1 := by rw [abs_of_nonneg h5]
          have h73 : 2 * |(a_idx : ℝ) - p1| < 2 := by rw [h72] <;> exact h71
          exact le_trans h_lip_a h73.le
        have h8 : f (a_idx : ℝ) - f p1 ≤ 2 := (abs_le.mp h7).2
        linarith
      have h_s_nonneg : 0 ≤ s := hs.le
      have h_sa_nonneg : 0 ≤ s * ((a_idx : ℝ) - p1) :=
        mul_nonneg h_s_nonneg (sub_nonneg.mpr h_a_ge_p1)
      have h_code_lower : ∀ (k : ℕ), k ≤ levels →
          codeFunction levels Δ (fun x => N (a_idx + x)) (k : ℝ) ≥ t_val * (k : ℝ) - E := by
        intro k hk
        let N' := fun x : ℕ => N (a_idx + x)
        have h_g : codeFunction levels Δ N' (k : ℝ) = f ((a_idx : ℝ) + (k : ℝ)) - f (a_idx : ℝ) :=
          rescaled_codeFunction h_a_le_m h_levels_pos (k : ℝ) (by exact_mod_cast Nat.zero_le k) (by exact_mod_cast hk)
        rw [h_g, ht_eq_s]
        have h_ak_le_p2 : (a_idx : ℝ) + (k : ℝ) ≤ p2 := by
          have hk' : (k : ℝ) ≤ (levels : ℝ) := by exact_mod_cast hk
          have hlev : (levels : ℝ) = (b_idx : ℝ) - (a_idx : ℝ) := by
            dsimp only [levels]
            rw [Nat.cast_sub (le_of_lt h_a_lt_b)]
          have h3 : (b_idx : ℝ) ≤ p2 := by rw [hb_idx_eq] <;> exact Nat.floor_le hp2_nonneg
          linarith
        have h_E_split : δ_lin * L + 2 = E := by rfl
        have h := superlinear_code_lower_lemma h_super1 h_fa_upper h_s_nonneg h_a_ge_p1 (by exact_mod_cast Nat.zero_le k) h_ak_le_p2
        rw [h_E_split] at h
        exact h
      have h_set : IsSetBetweenScales P (Δ ^ b_idx) (Δ ^ a_idx) t_val C_j := by
        have hδ_pos : 0 < (Δ ^ b_idx : ℝ) := by positivity
        have hΔj_pos : 0 < (Δ ^ a_idx : ℝ) := by positivity
        have hδ_le : (Δ ^ b_idx : ℝ) ≤ (Δ ^ a_idx : ℝ) := by
          have h : a_idx ≤ b_idx := le_of_lt h_a_lt_b
          exact pow_le_pow_of_le_one hΔ.le hΔ1.le h
        have hC_pos : 0 < C_j := by
          rw [hC_j_eq]; have h1 : 0 < (81 : ℝ) * Real.rpow Δ (-4) :=
            mul_pos (by norm_num) (Real.rpow_pos_of_pos hΔ _)
          have h2 : 0 < Real.rpow Δ (-(ε_bad * (levels : ℝ))) := Real.rpow_pos_of_pos hΔ _; positivity
        refine' ⟨hδ_pos, hΔj_pos, hδ_le, ht_nonneg, hC_pos, _⟩
        intro c d hQ
        let P' := homothetyS (Δ ^ a_idx) c d '' (P ∩ dyadicSquare (Δ ^ a_idx) c d)
        let N' := fun x : ℕ => N (a_idx + x)
        have h_a_lt_b : a_idx < b_idx := by omega
        have h_b_le_m : b_idx ≤ m := h_b_le_m
        have h_uniform' : IsDyadicUniform P' levels Δ N' :=
          uniform_rescaled_square_dyadic h_uniform h_a_lt_b h_b_le_m hn_pos h1 c d hQ
        have hP'_sub2 : P' ⊆ dyadicSquare 1 0 0 := homothety_image_subset (pow_pos hΔ a_idx) c d
        have h_result : IsDeltaSSet (Δ ^ levels) t_val C_j P' :=
          boundedSlopeToDeltaSSet_minimal h_uniform' hn_pos h1 hΔ hΔ1 hΔ2 t_val E C_j ht_nonneg ht_le4 hE_nonneg hC_ok h_levels_pos h_code_lower hP'_sub2
        have h9 : (Δ ^ levels : ℝ) = (Δ ^ b_idx : ℝ) / (Δ ^ a_idx : ℝ) := hδ_div.symm
        rw [←h9]
        exact h_result
      have h_reg : t_val > s → IsRegularBetweenScales P (Δ ^ b_idx) (Δ ^ a_idx) t_val C_j C_j := by
        intro h; exfalso
        have h_contra : t_val = s := ht_eq_s
        rw [h_contra] at h
        exact lt_irrefl s h
      exact ⟨h_set, h_reg⟩
  -- Property (iii): structured product bound
  have h_struct_product :
      (∏ j ∈ S, Real.rpow ((Δ ^ i_fn j.val : ℝ) / (Δ ^ i_fn (j.val + 1))) (t_j j.val)) ≥
        Real.rpow (Δ ^ m) (ε_bad - t) := by
    -- Each term = Δ^(-t_j * blockLen), using shared ratio lemma
    have h_term_eq : ∀ (j : Fin n), j ∈ S →
        Real.rpow ((Δ ^ i_fn j.val : ℝ) / (Δ ^ i_fn (j.val + 1))) (t_j j.val) =
        Real.rpow Δ (-(t_j j.val * (MultiscaleBlockConversion.blockLen (getBlock j) : ℝ))) := by
      intro j _
      let b := getBlock j
      have h_ratio : (Δ ^ i_fn j.val : ℝ) / (Δ ^ i_fn (j.val + 1)) =
          Real.rpow Δ (-(MultiscaleBlockConversion.blockLen b : ℝ)) := h_block_ratio j
      rw [h_ratio]
      have h_mul : Real.rpow (Real.rpow Δ (-(MultiscaleBlockConversion.blockLen b : ℝ))) (t_j j.val) =
          Real.rpow Δ ((-(MultiscaleBlockConversion.blockLen b : ℝ)) * t_j j.val) :=
        (Real.rpow_mul (le_of_lt hΔ) (-(MultiscaleBlockConversion.blockLen b : ℝ)) (t_j j.val)).symm
      rw [h_mul]
      have h6 : (-(MultiscaleBlockConversion.blockLen b : ℝ)) * t_j j.val =
          -(t_j j.val * (MultiscaleBlockConversion.blockLen b : ℝ)) := by ring
      rw [h6]
    have h_prod_eq : (∏ j ∈ S, Real.rpow ((Δ ^ i_fn j.val : ℝ) / (Δ ^ i_fn (j.val + 1))) (t_j j.val)) =
        Real.rpow Δ (-(∑ j ∈ S, t_j j.val * (MultiscaleBlockConversion.blockLen (getBlock j) : ℝ))) := by
      have h9 : ∏ j ∈ S, Real.rpow ((Δ ^ i_fn j.val : ℝ) / (Δ ^ i_fn (j.val + 1))) (t_j j.val) =
          ∏ j ∈ S, Real.rpow Δ (-(t_j j.val * (MultiscaleBlockConversion.blockLen (getBlock j) : ℝ))) := by
        apply Finset.prod_congr rfl
        intro j hj
        exact h_term_eq j hj
      rw [h9]
      rw [MultiscaleBlockConversion.prod_rpow_eq S
          (fun j => -(t_j j.val * (MultiscaleBlockConversion.blockLen (getBlock j) : ℝ))) Δ hΔ]
      rw [Finset.sum_neg_distrib] <;> rfl
    rw [h_prod_eq]
    -- Structured slope sum = sumSlopeLen
    have hS_def : ∀ (j : Fin n), j ∈ S ↔ MultiscaleBlockConversion.isStruct (getBlock j) := by
      intro j
      dsimp only [S]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      <;> rfl
    have h_tj_eq : ∀ (j : Fin n), t_j j.val = (getBlock j).2.2.2 := by
      intro j
      have h_i : t_j j.val = (blocks.get ⟨j.val, j.is_lt⟩).2.2.2 := by
        simpa [t_j] using dif_pos j.is_lt
      rw [h_i] <;> rfl
    have h_slope_eq : (∑ j ∈ S, t_j j.val * (MultiscaleBlockConversion.blockLen (getBlock j) : ℝ)) =
        (MultiscaleBlockConversion.sumSlopeLen blocks : ℝ) := by
      have h_sumSlope : (MultiscaleBlockConversion.sumSlopeLen blocks : ℝ) =
          ∑ j ∈ Finset.univ, MultiscaleBlockConversion.slopeLen (getBlock j) := by
        have h := list_map_sum_eq_fin_sum MultiscaleBlockConversion.slopeLen blocks
        simpa [MultiscaleBlockConversion.sumSlopeLen, getBlock, n] using h
      rw [h_sumSlope]
      have hS' : S = Finset.univ.filter (fun j : Fin n => MultiscaleBlockConversion.isStruct (getBlock j)) := by
        ext j; simp [S, Finset.mem_filter]
      rw [hS', Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : MultiscaleBlockConversion.isStruct (getBlock j)
      · rw [if_pos h]
        have h3 : t_j j.val = (getBlock j).2.2.2 := h_tj_eq j
        have h4 : MultiscaleBlockConversion.slopeLen (getBlock j) =
            (getBlock j).2.2.2 * (MultiscaleBlockConversion.blockLen (getBlock j) : ℝ) := by
          have h_pos : (getBlock j).1 ≤ (getBlock j).2.1 :=
            le_of_lt (h_pos_len (getBlock j) (blocks.get_mem j))
          have h_slope : MultiscaleBlockConversion.slopeLen (getBlock j) =
              (getBlock j).2.2.2 * ((getBlock j).2.1 - (getBlock j).1 : ℝ) := by
            simp [MultiscaleBlockConversion.slopeLen, h] <;> rfl
          rw [h_slope]
          have h_cast : (MultiscaleBlockConversion.blockLen (getBlock j) : ℝ) =
              ((getBlock j).2.1 - (getBlock j).1 : ℝ) := by
            simp [MultiscaleBlockConversion.blockLen, Nat.cast_sub h_pos]
            <;> norm_cast
          rw [h_cast]
        rw [h4, h3] <;> ring
      · rw [if_neg h]
        have h4 : MultiscaleBlockConversion.slopeLen (getBlock j) = 0 := by
          simp [MultiscaleBlockConversion.slopeLen, h]
        rw [h4] <;> ring
    rw [h_slope_eq]
    -- Interval count bound: K ≤ 1/τ₀
    have h_m_pos' : 0 < (m : ℝ) := by exact_mod_cast hm_pos
    have hK_le : (K : ℝ) ≤ 1 / τ₀ := by
      exact MultiscaleBlockConversion.interval_count_le (m := (m : ℝ)) h_m_pos' hτ₀_pos
        (fun i j hne => hI_disj i j hne) hI_bound
    -- 4K ≤ η*m (from K ≤ 1/τ₀ and 4/(η*τ₀) ≤ m)
    have hm0_m : (m0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h4K : 4 * (K : ℝ) ≤ η * (m : ℝ) :=
      four_K_le_eta_m K τ₀ η (m : ℝ) (m0 : ℝ) hτ₀_pos hη_pos hm0_ητ₀ hm0_m hK_le
    -- Slope sum lower bound: sumSlopeLen ≥ (t - ε_bad)*m
    let slope_sum_kauf : ℝ := ∑ i : Fin K, ((I i).2 - (I i).1) * chordSlope f (I i).1 (I i).2
    have h_slope_sum_kauf : (MultiscaleBlockConversion.sumSlopeLen blocks : ℝ) ≥ slope_sum_kauf - 4 * (K : ℝ) := by
      have h_eq : slope_sum_kauf = ∑ i : Fin K, chordSlope f (I i).1 (I i).2 * ((I i).2 - (I i).1) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [h_eq]
      exact h_slope_sum
    have h_slope_lower : (MultiscaleBlockConversion.sumSlopeLen blocks : ℝ) ≥ (t - ε_bad) * (m : ℝ) :=
      slope_lower_bound t A A_kauf ε_kauf ε_bad η (m : ℝ) K
        (MultiscaleBlockConversion.sumSlopeLen blocks) slope_sum_kauf
        hA_kauf_eq_A hI_slope_sum h_slope_sum_kauf h4K hε_bad_def
    -- Final: Δ^(-sumSlopeLen) ≥ Δ^((ε_bad-t)*m)
    have h9 : -(MultiscaleBlockConversion.sumSlopeLen blocks : ℝ) ≤ (ε_bad - t) * (m : ℝ) := by
      have h10 : (MultiscaleBlockConversion.sumSlopeLen blocks : ℝ) ≥ (t - ε_bad) * (m : ℝ) := h_slope_lower
      have h11 : -(MultiscaleBlockConversion.sumSlopeLen blocks : ℝ) ≤ -((t - ε_bad) * (m : ℝ)) := neg_le_neg h10
      have h12 : -((t - ε_bad) * (m : ℝ)) = (ε_bad - t) * (m : ℝ) := by ring
      rw [h12] at h11
      exact h11
    have h10 : Real.rpow Δ (-(MultiscaleBlockConversion.sumSlopeLen blocks : ℝ)) ≥
        Real.rpow Δ ((ε_bad - t) * (m : ℝ)) :=
      rpow_decreasing hΔ hΔ1 h9
    have h11 : Real.rpow Δ ((ε_bad - t) * (m : ℝ)) = Real.rpow (Δ ^ m) (ε_bad - t) :=
      rpow_Δ_m hΔ
    rw [h11] at h10
    exact h10
  -- Property (iv): no consecutive bad
  have hB_def : ∀ (j : Fin n), j ∈ B ↔ ¬MultiscaleBlockConversion.isStruct (blocks.get j) := by
    intro j
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    <;> rfl
  have h_no_consec_bad : ∀ (j : Fin n), j ∈ B →
      ∀ (k : Fin n), k.val = j.val + 1 → k ∉ B :=
    no_consecutive_bad (rfl : blocks.length = n) hB_def h_no_bad
  exact ⟨n, i_fn, t_j, S, B, h_i0, h_in, h_ij, h_tj_range, h_S_B_univ, h_S_B_disj,
    h_struct_ratio, h_bad_product, h_property_ii, h_struct_product, h_no_consec_bad⟩


end MultiscaleDecomposition
end DirecretisedFurstenbergEstimate
