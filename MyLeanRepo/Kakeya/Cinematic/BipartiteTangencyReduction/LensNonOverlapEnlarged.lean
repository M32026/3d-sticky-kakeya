import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.LensNonOverlap

/-!
# Non-overlap for graph lenses with enlarged endpoint intervals

The lens-existence argument localizes endpoints to a fixed multiple of the
rectangle interval length. This module generalizes the fixed one-length
enlargement used by `graph_lenses_nonoverlap_of_incomparable_enlarged`.
-/

namespace Kakeya.Cinematic

lemma graph_lenses_nonoverlap_of_incomparable_enlarged_factor
    {family : Set C2Function} {delta t Cc tangency E : ℝ}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hCc : 100 ≤ Cc) (hadm : Cc * delta ≤ t)
    (htang_le_Cc : tangency ≤ Cc)
    (hE_nonneg : 0 ≤ E) (hCc_bound : (2 + 2 * E)^2 ≤ Cc)
    {R : RectangleFamily delta t}
    (hRincomp : R.IsPairwiseIncomparable family Cc)
    (lenses : Fin R.card → GraphLens)
    (h_lens_in_enlarged : ∀ i,
      ↑(lenses i).left ∈
          Set.Icc
            ((R.rectangle i).interval.left -
              E * Real.sqrt (delta / t))
            ((R.rectangle i).interval.right +
              E * Real.sqrt (delta / t)) ∧
      ↑(lenses i).right ∈
          Set.Icc
            ((R.rectangle i).interval.left -
              E * Real.sqrt (delta / t))
            ((R.rectangle i).interval.right +
              E * Real.sqrt (delta / t)))
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
  have hcase :
      (lenses i).f = (lenses j).f ∨
        (lenses i).g = (lenses j).g := by
    rcases hshare with (h | h | h | h)
    · exact Or.inl h
    · exact False.elim (h_no_cross i j h)
    · exact False.elim (h_no_cross j i h.symm)
    · exact Or.inr h
  let lo : ℝ :=
    max ((lenses i).left : ℝ) ((lenses j).left : ℝ)
  let hi : ℝ :=
    min ((lenses i).right : ℝ) ((lenses j).right : ℝ)
  have hlo_lt_hi : lo < hi := hinterval
  let x : ℝ := (lo + hi) / 2
  have hlo_le_x : lo ≤ x := by
    dsimp only [x]
    linarith
  have hx_le_hi : x ≤ hi := by
    dsimp only [x]
    linarith
  have hx_i1 : ((lenses i).left : ℝ) ≤ x :=
    (le_max_left _ _).trans hlo_le_x
  have hx_i2 : x ≤ ((lenses i).right : ℝ) :=
    hx_le_hi.trans (min_le_left _ _)
  have hx_j1 : ((lenses j).left : ℝ) ≤ x :=
    (le_max_right _ _).trans hlo_le_x
  have hx_j2 : x ≤ ((lenses j).right : ℝ) :=
    hx_le_hi.trans (min_le_right _ _)
  let s : ℝ := Real.sqrt (delta / t)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  let Ri := (R.rectangle i).interval
  let Rj := (R.rectangle j).interval
  have hRi_len : Ri.length = s := (R.rectangle i).interval_length
  have hRj_len : Rj.length = s := (R.rectangle j).interval_length
  have hx_Ri_left : Ri.left - E * s ≤ x := by
    have h := (h_lens_in_enlarged i).1.1
    linarith
  have hx_Ri_right : x ≤ Ri.right + E * s := by
    have h := (h_lens_in_enlarged i).2.2
    linarith
  have hx_Rj_left : Rj.left - E * s ≤ x := by
    have h := (h_lens_in_enlarged j).1.1
    linarith
  have hx_Rj_right : x ≤ Rj.right + E * s := by
    have h := (h_lens_in_enlarged j).2.2
    linarith
  let a : ℝ := min Ri.left Rj.left
  let b : ℝ := max Ri.right Rj.right
  have hRi_right : Ri.right = Ri.left + s := by
    have h : Ri.length = Ri.right - Ri.left := rfl
    linarith [hRi_len]
  have hRj_right : Rj.right = Rj.left + s := by
    have h : Rj.length = Rj.right - Rj.left := rfl
    linarith [hRj_len]
  have hRi_left_lower : x - (1 + E) * s ≤ Ri.left := by
    linarith [hx_Ri_right, hRi_right]
  have hRj_left_lower : x - (1 + E) * s ≤ Rj.left := by
    linarith [hx_Rj_right, hRj_right]
  have ha_lower : x - (1 + E) * s ≤ a :=
    le_min hRi_left_lower hRj_left_lower
  have hRi_right_upper : Ri.right ≤ x + (1 + E) * s := by
    linarith [hx_Ri_left, hRi_right]
  have hRj_right_upper : Rj.right ≤ x + (1 + E) * s := by
    linarith [hx_Rj_left, hRj_right]
  have hb_upper : b ≤ x + (1 + E) * s :=
    max_le hRi_right_upper hRj_right_upper
  have hhull : b - a ≤ (2 + 2 * E) * s := by
    linarith
  have h_bound :
      (2 + 2 * E) * s ≤ Real.sqrt (Cc * delta / t) := by
    have hsq :
        ((2 + 2 * E) * s)^2 ≤ Cc * delta / t := by
      have hs_sq : s^2 = delta / t := by
        dsimp only [s]
        rw [Real.sq_sqrt (by positivity)]
      calc
        ((2 + 2 * E) * s)^2 =
            (2 + 2 * E)^2 * (delta / t) := by
              rw [mul_pow, hs_sq]
        _ ≤ Cc * (delta / t) :=
          mul_le_mul_of_nonneg_right hCc_bound (by positivity)
        _ = Cc * delta / t := by ring
    exact Real.le_sqrt_of_sq_le hsq
  have hhull' :
      b - a ≤ Real.sqrt (Cc * delta / t) :=
    hhull.trans h_bound
  rcases hcase with hcase_f | hcase_g
  · rcases h_f_common i j hcase_f with
      ⟨w, hw_family, hRt, hSt⟩
    have hcomparable :=
      common_tangent_hull_comparable
        hdelta ht (by linarith) hadm htang_le_Cc
        hw_family hRt hSt hhull'
    exact hRincomp i j hij hcomparable
  · rcases h_g_common i j hcase_g with
      ⟨g, hg_family, hRt, hSt⟩
    have hcomparable :=
      common_tangent_hull_comparable
        hdelta ht (by linarith) hadm htang_le_Cc
        hg_family hRt hSt hhull'
    exact hRincomp i j hij hcomparable

end Kakeya.Cinematic
