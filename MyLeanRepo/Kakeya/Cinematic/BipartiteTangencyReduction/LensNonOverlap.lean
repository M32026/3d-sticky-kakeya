import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.PerPair
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Lenses

/-!
# Non-overlap of graph lenses from incomparable rectangles

This module provides:
1. A generalized version of `common_tangent_overlap_comparable` for arbitrary
   tangency constants.
2. The non-overlap lemma: graph lenses associated with pairwise incomparable
   rectangles cannot overlap.
3. A three-way pigeonhole principle used for shift selection (PYZ Corollary 38).
-/

noncomputable section

namespace Kakeya.Cinematic

open Classical Set Finset

/--
Generalized version of `common_tangent_overlap_comparable` for an arbitrary
tangency constant `lambda ≤ Cc`.

If two rectangles have overlapping parameter intervals and both are
`lambda`-tangent to the same function `w ∈ family`, then they are
`Cc`-comparable.
-/
lemma common_tangent_overlap_comparable_general
    {family : Set C2Function} {delta t Cc lambda : ℝ}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hCc : 10 ≤ Cc) (hadm : Cc * delta ≤ t)
    (hlam : lambda ≤ Cc)
    {w : C2Function} (hw : w ∈ family)
    {R S : CurvilinearRectangle delta t}
    (hRt : R.IsLambdaTangent w lambda)
    (hSt : S.IsLambdaTangent w lambda)
    (hoverlap :
      (R.interval.carrier ∩ S.interval.carrier).Nonempty) :
    R.AreLambdaComparable S family Cc := by
  let targetLength := Real.sqrt (Cc * delta / t)
  have htarget : 0 < targetLength := by positivity
  have htarget_one : targetLength ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    exact (div_le_one ht).2 hadm
  let a := min R.interval.left S.interval.left
  let b := max R.interval.right S.interval.right
  have ha : 0 ≤ a :=
    le_min R.interval.left_mem.1 S.interval.left_mem.1
  have hb : b ≤ 1 :=
    max_le R.interval.right_mem.2 S.interval.right_mem.2
  have hab : a ≤ b :=
    (min_le_left _ _).trans
      (R.interval.left_le_right.trans (le_max_left _ _))
  obtain ⟨x, hxR, hxS⟩ := hoverlap
  have hhull : b - a ≤ 2 * Real.sqrt (delta / t) := by
    have hright : b - (x : ℝ) ≤ Real.sqrt (delta / t) := by
      have hR :
          R.interval.right - (x : ℝ) ≤ R.interval.length := by
        change R.interval.right - (x : ℝ) ≤
          R.interval.right - R.interval.left
        linarith [hxR.1]
      have hS :
          S.interval.right - (x : ℝ) ≤ S.interval.length := by
        change S.interval.right - (x : ℝ) ≤
          S.interval.right - S.interval.left
        linarith [hxS.1]
      rw [R.interval_length] at hR
      rw [S.interval_length] at hS
      rcases max_choice R.interval.right S.interval.right with h | h
      · rw [show b = R.interval.right by exact h]
        exact hR
      · rw [show b = S.interval.right by exact h]
        exact hS
    have hleft : (x : ℝ) - a ≤ Real.sqrt (delta / t) := by
      have hR :
          (x : ℝ) - R.interval.left ≤ R.interval.length := by
        change (x : ℝ) - R.interval.left ≤
          R.interval.right - R.interval.left
        linarith [hxR.2]
      have hS :
          (x : ℝ) - S.interval.left ≤ S.interval.length := by
        change (x : ℝ) - S.interval.left ≤
          S.interval.right - S.interval.left
        linarith [hxS.2]
      rw [R.interval_length] at hR
      rw [S.interval_length] at hS
      rcases min_choice R.interval.left S.interval.left with h | h
      · rw [show a = R.interval.left by exact h]
        exact hR
      · rw [show a = S.interval.left by exact h]
        exact hS
    linarith
  have hhull_target : b - a ≤ targetLength := by
    have hsqrtCc : 2 ≤ Real.sqrt Cc := by
      exact Real.le_sqrt_of_sq_le (by nlinarith)
    calc
      b - a ≤ 2 * Real.sqrt (delta / t) := hhull
      _ ≤ Real.sqrt Cc * Real.sqrt (delta / t) := by gcongr
      _ = targetLength := by
        dsimp only [targetLength]
        rw [← Real.sqrt_mul]; ring_nf; positivity
  obtain ⟨J, hJa, hJb, hJlen⟩ :=
    enclosing_interval_exists ha hb hab hhull_target htarget_one
  let U : CurvilinearRectangle (Cc * delta) t :=
    { function := w
      interval := J
      interval_length := hJlen }
  have hlam_delta : lambda * delta ≤ Cc * delta := by
    gcongr
  have hRsub : R.carrier ⊆ U.carrier := by
    intro p hp
    have hpJ : p.1 ∈ J.carrier := by
      exact ⟨hJa.trans ((min_le_left _ _).trans hp.1.1),
        hp.1.2.trans ((le_max_left _ _).trans hJb)⟩
    exact ⟨hpJ, (hRt p hp).trans hlam_delta⟩
  have hSsub : S.carrier ⊆ U.carrier := by
    intro p hp
    have hpJ : p.1 ∈ J.carrier := by
      exact ⟨hJa.trans ((min_le_right _ _).trans hp.1.1),
        hp.1.2.trans ((le_max_right _ _).trans hJb)⟩
    exact ⟨hpJ, (hSt p hp).trans hlam_delta⟩
  exact ⟨U, hw, Set.union_subset hRsub hSsub⟩

/--
Variant of `common_tangent_overlap_comparable_general` that takes a direct
bound on the hull length instead of requiring interval overlap.

If the hull of two rectangle intervals has length at most `√(Cc * δ / t)` and
both rectangles are `lambda`-tangent to the same `w ∈ family`, then they are
`Cc`-comparable.
-/
lemma common_tangent_hull_comparable
    {family : Set C2Function} {delta t Cc lambda : ℝ}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hCc : 10 ≤ Cc) (hadm : Cc * delta ≤ t)
    (hlam : lambda ≤ Cc)
    {w : C2Function} (hw : w ∈ family)
    {R S : CurvilinearRectangle delta t}
    (hRt : R.IsLambdaTangent w lambda)
    (hSt : S.IsLambdaTangent w lambda)
    (hhull : max R.interval.right S.interval.right - min R.interval.left S.interval.left ≤
        Real.sqrt (Cc * delta / t)) :
    R.AreLambdaComparable S family Cc := by
  let targetLength := Real.sqrt (Cc * delta / t)
  have htarget : 0 < targetLength := by positivity
  have htarget_one : targetLength ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    exact (div_le_one ht).2 hadm
  let a := min R.interval.left S.interval.left
  let b := max R.interval.right S.interval.right
  have ha : 0 ≤ a :=
    le_min R.interval.left_mem.1 S.interval.left_mem.1
  have hb : b ≤ 1 :=
    max_le R.interval.right_mem.2 S.interval.right_mem.2
  have hab : a ≤ b :=
    (min_le_left _ _).trans
      (R.interval.left_le_right.trans (le_max_left _ _))
  obtain ⟨J, hJa, hJb, hJlen⟩ :=
    enclosing_interval_exists ha hb hab hhull htarget_one
  let U : CurvilinearRectangle (Cc * delta) t :=
    { function := w
      interval := J
      interval_length := hJlen }
  have hlam_delta : lambda * delta ≤ Cc * delta := by gcongr
  have hRsub : R.carrier ⊆ U.carrier := by
    intro p hp
    have hpJ : p.1 ∈ J.carrier := by
      exact ⟨hJa.trans ((min_le_left _ _).trans hp.1.1),
        hp.1.2.trans ((le_max_left _ _).trans hJb)⟩
    exact ⟨hpJ, (hRt p hp).trans hlam_delta⟩
  have hSsub : S.carrier ⊆ U.carrier := by
    intro p hp
    have hpJ : p.1 ∈ J.carrier := by
      exact ⟨hJa.trans ((min_le_right _ _).trans hp.1.1),
        hp.1.2.trans ((le_max_right _ _).trans hJb)⟩
    exact ⟨hpJ, (hSt p hp).trans hlam_delta⟩
  exact ⟨U, hw, Set.union_subset hRsub hSsub⟩

/--
Non-overlap of graph lenses associated with pairwise incomparable rectangles.

Each lens is assumed to lie within its rectangle's parameter interval. If two
lenses overlap, they must share a graph side; cross-color sharing is excluded
by hypothesis. Same-color sharing plus interval overlap forces the two
rectangles to be lambda-comparable, contradicting pairwise incomparability.

The tangency constant `tangency` is arbitrary (subject to `tangency ≤ Cc`),
making this lemma suitable for the robust core where the tangency threshold
grows with the dilation.
-/
lemma graph_lenses_nonoverlap_of_incomparable
    {family : Set C2Function} {delta t Cc tangency : ℝ}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hCc : 10 ≤ Cc) (hadm : Cc * delta ≤ t)
    (htang_le_Cc : tangency ≤ Cc)
    {R : RectangleFamily delta t}
    (hRincomp : R.IsPairwiseIncomparable family Cc)
    (lenses : Fin R.card → GraphLens)
    (h_lens_in_rect : ∀ i,
      (lenses i).left ∈ (R.rectangle i).interval.carrier ∧
      (lenses i).right ∈ (R.rectangle i).interval.carrier)
    (h_f_common : ∀ i j,
      (lenses i).f = (lenses j).f →
      ∃ w : C2Function, w ∈ family ∧
        (R.rectangle i).IsLambdaTangent w tangency ∧
        (R.rectangle j).IsLambdaTangent w tangency)
    (h_g_common : ∀ i j,
      (lenses i).g = (lenses j).g →
      ∃ b : C2Function, b ∈ family ∧
        (R.rectangle i).IsLambdaTangent b tangency ∧
        (R.rectangle j).IsLambdaTangent b tangency)
    (h_no_cross : ∀ i j, (lenses i).f ≠ (lenses j).g) :
    ∀ i j, i ≠ j → (lenses i).Nonoverlap (lenses j) := by
  intro i j hij hoverlap
  rcases hoverlap with ⟨hshare, hinterval⟩
  -- Eliminate cross-color sharing
  have hcase : (lenses i).f = (lenses j).f ∨ (lenses i).g = (lenses j).g := by
    rcases hshare with (h | h | h | h)
    · exact Or.inl h
    · exfalso; exact h_no_cross i j h
    · exfalso; exact h_no_cross j i (Eq.symm h)
    · exact Or.inr h
  let lo : ℝ := max ((lenses i).left : ℝ) ((lenses j).left : ℝ)
  let hi : ℝ := min ((lenses i).right : ℝ) ((lenses j).right : ℝ)
  have hlo_lt_hi : lo < hi := hinterval
  set x : ℝ := (lo + hi) / 2 with hx_def
  have hlo_le_x : lo ≤ x := by
    rw [hx_def]; linarith
  have hx_le_hi : x ≤ hi := by
    rw [hx_def]; linarith
  have hx_i1 : ((lenses i).left : ℝ) ≤ x := by
    calc ((lenses i).left : ℝ) ≤ lo := le_max_left _ _
      _ ≤ x := hlo_le_x
  have hx_i2 : x ≤ ((lenses i).right : ℝ) := by
    calc x ≤ hi := hx_le_hi
      _ ≤ ((lenses i).right : ℝ) := min_le_left _ _
  have hx_j1 : ((lenses j).left : ℝ) ≤ x := by
    calc ((lenses j).left : ℝ) ≤ lo := le_max_right _ _
      _ ≤ x := hlo_le_x
  have hx_j2 : x ≤ ((lenses j).right : ℝ) := by
    calc x ≤ hi := hx_le_hi
      _ ≤ ((lenses j).right : ℝ) := min_le_right _ _
  have hx01 : 0 ≤ x ∧ x ≤ 1 := by
    have h1 : 0 ≤ ((lenses i).left : ℝ) := (lenses i).left.property.1
    have h2 : ((lenses i).right : ℝ) ≤ 1 := (lenses i).right.property.2
    constructor <;> linarith
  let xp : UnitPoint := ⟨x, hx01⟩
  have hxp_i : xp ∈ (R.rectangle i).interval.carrier := by
    have hli := (h_lens_in_rect i).1
    have hri := (h_lens_in_rect i).2
    simp only [ParameterInterval.carrier, Set.mem_setOf_eq] at hli hri ⊢
    constructor <;> linarith [hli, hri, hx_i1, hx_i2]
  have hxp_j : xp ∈ (R.rectangle j).interval.carrier := by
    have hlj := (h_lens_in_rect j).1
    have hrj := (h_lens_in_rect j).2
    simp only [ParameterInterval.carrier, Set.mem_setOf_eq] at hlj hrj ⊢
    constructor <;> linarith [hlj, hrj, hx_j1, hx_j2]
  have hoverlap_rect :
      ((R.rectangle i).interval.carrier ∩ (R.rectangle j).interval.carrier).Nonempty :=
    ⟨xp, hxp_i, hxp_j⟩
  rcases hcase with (hcase_f | hcase_g)
  · rcases h_f_common i j hcase_f with ⟨w, hw_family, hRt, hSt⟩
    have hcomparable := common_tangent_overlap_comparable_general
      hdelta ht hCc hadm htang_le_Cc hw_family hRt hSt hoverlap_rect
    exact hRincomp i j hij hcomparable
  · rcases h_g_common i j hcase_g with ⟨b, hb_family, hRt, hSt⟩
    have hcomparable := common_tangent_overlap_comparable_general
      hdelta ht hCc hadm htang_le_Cc hb_family hRt hSt hoverlap_rect
    exact hRincomp i j hij hcomparable

/--
Enlarged-interval version of `graph_lenses_nonoverlap_of_incomparable`.

Each lens endpoint lies in the *enlarged* rectangle interval
`[R.interval.left - √(δ/t), R.interval.right + √(δ/t)]`, not necessarily inside
the rectangle interval itself.  If two such lenses overlap, the hull of their
rectangle intervals has length at most `10 * √(δ/t)`.  For `Cc ≥ 100`, this is
within the comparability threshold `√(Cc * δ/t)`, so the rectangles must be
comparable — contradicting pairwise incomparability.
-/
lemma graph_lenses_nonoverlap_of_incomparable_enlarged
    {family : Set C2Function} {delta t Cc tangency : ℝ}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hCc : 100 ≤ Cc) (hadm : Cc * delta ≤ t)
    (htang_le_Cc : tangency ≤ Cc)
    {R : RectangleFamily delta t}
    (hRincomp : R.IsPairwiseIncomparable family Cc)
    (lenses : Fin R.card → GraphLens)
    (h_lens_in_enlarged : ∀ i,
      ↑(lenses i).left ∈ Set.Icc ((R.rectangle i).interval.left - Real.sqrt (delta / t))
                                ((R.rectangle i).interval.right + Real.sqrt (delta / t)) ∧
      ↑(lenses i).right ∈ Set.Icc ((R.rectangle i).interval.left - Real.sqrt (delta / t))
                                 ((R.rectangle i).interval.right + Real.sqrt (delta / t)))
    (h_f_common : ∀ i j,
      (lenses i).f = (lenses j).f →
      ∃ w : C2Function, w ∈ family ∧
        (R.rectangle i).IsLambdaTangent w tangency ∧
        (R.rectangle j).IsLambdaTangent w tangency)
    (h_g_common : ∀ i j,
      (lenses i).g = (lenses j).g →
      ∃ b : C2Function, b ∈ family ∧
        (R.rectangle i).IsLambdaTangent b tangency ∧
        (R.rectangle j).IsLambdaTangent b tangency)
    (h_no_cross : ∀ i j, (lenses i).f ≠ (lenses j).g) :
    ∀ i j, i ≠ j → (lenses i).Nonoverlap (lenses j) := by
  intro i j hij hoverlap
  rcases hoverlap with ⟨hshare, hinterval⟩
  have hcase : (lenses i).f = (lenses j).f ∨ (lenses i).g = (lenses j).g := by
    rcases hshare with (h | h | h | h)
    · exact Or.inl h
    · exfalso; exact h_no_cross i j h
    · exfalso; exact h_no_cross j i (Eq.symm h)
    · exact Or.inr h
  let lo : ℝ := max ((lenses i).left : ℝ) ((lenses j).left : ℝ)
  let hi : ℝ := min ((lenses i).right : ℝ) ((lenses j).right : ℝ)
  have hlo_lt_hi : lo < hi := hinterval
  set x : ℝ := (lo + hi) / 2 with hx_def
  have hlo_le_x : lo ≤ x := by rw [hx_def]; linarith
  have hx_le_hi : x ≤ hi := by rw [hx_def]; linarith
  have hx_i1 : ((lenses i).left : ℝ) ≤ x := by
    calc ((lenses i).left : ℝ) ≤ lo := le_max_left _ _
      _ ≤ x := hlo_le_x
  have hx_i2 : x ≤ ((lenses i).right : ℝ) := by
    calc x ≤ hi := hx_le_hi
      _ ≤ ((lenses i).right : ℝ) := min_le_left _ _
  have hx_j1 : ((lenses j).left : ℝ) ≤ x := by
    calc ((lenses j).left : ℝ) ≤ lo := le_max_right _ _
      _ ≤ x := hlo_le_x
  have hx_j2 : x ≤ ((lenses j).right : ℝ) := by
    calc x ≤ hi := hx_le_hi
      _ ≤ ((lenses j).right : ℝ) := min_le_right _ _
  let s : ℝ := Real.sqrt (delta / t)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  let Ri := (R.rectangle i).interval
  let Rj := (R.rectangle j).interval
  have hRi_len : Ri.length = s := (R.rectangle i).interval_length
  have hRj_len : Rj.length = s := (R.rectangle j).interval_length
  -- x lies in the enlarged interval of both rectangles
  have hx_Ri_left : Ri.left - s ≤ x := by
    have h : ↑(lenses i).left ∈ Set.Icc (Ri.left - s) (Ri.right + s) := (h_lens_in_enlarged i).1
    have h' : Ri.left - s ≤ ((lenses i).left : ℝ) := h.1
    linarith [hx_i1]
  have hx_Ri_right : x ≤ Ri.right + s := by
    have h : ↑(lenses i).right ∈ Set.Icc (Ri.left - s) (Ri.right + s) := (h_lens_in_enlarged i).2
    have h' : ((lenses i).right : ℝ) ≤ Ri.right + s := h.2
    linarith [hx_i2]
  have hx_Rj_left : Rj.left - s ≤ x := by
    have h : ↑(lenses j).left ∈ Set.Icc (Rj.left - s) (Rj.right + s) := (h_lens_in_enlarged j).1
    have h' : Rj.left - s ≤ ((lenses j).left : ℝ) := h.1
    linarith [hx_j1]
  have hx_Rj_right : x ≤ Rj.right + s := by
    have h : ↑(lenses j).right ∈ Set.Icc (Rj.left - s) (Rj.right + s) := (h_lens_in_enlarged j).2
    have h' : ((lenses j).right : ℝ) ≤ Rj.right + s := h.2
    linarith [hx_j2]
  -- Bound the hull of the two rectangle intervals
  let a : ℝ := min Ri.left Rj.left
  let b : ℝ := max Ri.right Rj.right
  have h1 : Ri.right = Ri.left + s := by
    have h2 : Ri.length = Ri.right - Ri.left := by rfl
    linarith [hRi_len]
  have h3 : Rj.right = Rj.left + s := by
    have h4 : Rj.length = Rj.right - Rj.left := by rfl
    linarith [hRj_len]
  have hRi_left_lower : x - 2 * s ≤ Ri.left := by linarith [hx_Ri_right, h1]
  have hRj_left_lower : x - 2 * s ≤ Rj.left := by linarith [hx_Rj_right, h3]
  have ha_lower : x - 2 * s ≤ a := le_min hRi_left_lower hRj_left_lower
  have hRi_right_upper : Ri.right ≤ x + 2 * s := by linarith [hx_Ri_left, h1]
  have hRj_right_upper : Rj.right ≤ x + 2 * s := by linarith [hx_Rj_left, h3]
  have hb_upper : b ≤ x + 2 * s := max_le hRi_right_upper hRj_right_upper
  have hhull : b - a ≤ 4 * s := by linarith
  have h4s_le_target : 4 * s ≤ Real.sqrt (Cc * delta / t) := by
    have h1 : 0 < s := hs_pos
    have h2 : (4 * s) ^ 2 ≤ Cc * delta / t := by
      have h3 : (4 * s) ^ 2 = 16 * (delta / t) := by
        calc (4 * s) ^ 2 = 16 * s ^ 2 := by ring
          _ = 16 * (delta / t) := by
            rw [Real.sq_sqrt (by positivity)] <;> ring
      rw [h3]
      have h4 : 16 ≤ Cc := by linarith
      have h5 : 16 * (delta / t) ≤ Cc * delta / t := by
        have h6 : Cc * delta / t = Cc * (delta / t) := by ring
        rw [h6]
        exact mul_le_mul_of_nonneg_right h4 (by positivity)
      exact h5
    have h5 : 0 ≤ Real.sqrt (Cc * delta / t) := by positivity
    exact Real.le_sqrt_of_sq_le h2
  have hhull' : b - a ≤ Real.sqrt (Cc * delta / t) := le_trans hhull h4s_le_target
  rcases hcase with (hcase_f | hcase_g)
  · rcases h_f_common i j hcase_f with ⟨w, hw_family, hRt, hSt⟩
    have hcomparable := common_tangent_hull_comparable
      hdelta ht (by linarith) hadm htang_le_Cc hw_family hRt hSt hhull'
    exact hRincomp i j hij hcomparable
  · rcases h_g_common i j hcase_g with ⟨b, hb_family, hRt, hSt⟩
    have hcomparable := common_tangent_hull_comparable
      hdelta ht (by linarith) hadm htang_le_Cc hb_family hRt hSt hhull'
    exact hRincomp i j hij hcomparable

/--
Three-way pigeonhole principle (PYZ Corollary 38 shift selection).

If every element of a finite set `S` satisfies at least one of three properties
indexed by `Fin 3`, then at least one property is satisfied by at least one
third of the elements (rounded up).
-/
lemma pigeonhole_three {α : Type*} [DecidableEq α]
    (S : Finset α) (P : α → Fin 3 → Prop)
    [hP : ∀ a k, Decidable (P a k)]
    (h : ∀ a ∈ S, ∃ k : Fin 3, P a k) :
    ∃ k : Fin 3, 3 * (S.filter (fun a => P a k)).card ≥ S.card := by
  let f (k : Fin 3) : Finset α := S.filter (fun a => P a k)
  have hcover : S ⊆ Finset.biUnion (Finset.univ : Finset (Fin 3)) f := by
    intro a ha
    rcases h a ha with ⟨k, hk⟩
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k,
      Finset.mem_filter.mpr ⟨ha, hk⟩⟩
  have hcard : (S.card : ℝ) ≤ ∑ k : Fin 3, (f k).card := by
    calc (S.card : ℝ)
      ≤ ↑((Finset.biUnion (Finset.univ : Finset (Fin 3)) f).card) :=
        by exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ k : Fin 3, (f k).card := by
        exact_mod_cast Finset.card_biUnion_le
  by_contra h'
  push Not at h'
  have h1 : ∀ k : Fin 3, ((f k).card : ℝ) < (S.card : ℝ) / 3 := by
    intro k
    have h2 : 3 * (f k).card < S.card := h' k
    have h3 : (3 : ℝ) * ((f k).card : ℝ) < (S.card : ℝ) := by
      exact_mod_cast h2
    linarith
  have hsum_real : ((f 0).card : ℝ) + ((f 1).card : ℝ) + ((f 2).card : ℝ) < (S.card : ℝ) := by
    have h0 := h1 0
    have h1' := h1 1
    have h2' := h1 2
    linarith
  have hsum_eq : (∑ k : Fin 3, (f k).card : ℝ) =
      ((f 0).card : ℝ) + ((f 1).card : ℝ) + ((f 2).card : ℝ) := by
    simp [Fin.sum_univ_succ]; ring
  have hcard' : (S.card : ℝ) ≤ ∑ k : Fin 3, ((f k).card : ℝ) := by
    exact_mod_cast hcard
  rw [hsum_eq] at hcard'
  linarith

end Kakeya.Cinematic
