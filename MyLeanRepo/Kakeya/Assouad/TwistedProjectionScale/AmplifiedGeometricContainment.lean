import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockTranslation

/-!
# Domain-restricted geometric containment for amplified blocks

Provides `LipschitzOnWith` bounds for half-parameter slope curves on `[0,1]`
and the resulting fiberwise-translation graph-neighborhood containment.

Global `LipschitzWith` for `shift v.extension` is impossible because
`SlopeFunction` is only constrained on `[-1,1]`. Instead we use
`LipschitzOnWith` on `Icc 0 1`, which is sufficient because all projected
source points have first coordinate in `[0,1]` (from `horizontalSlab 0 1`).
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/--
If two cinematic curves are close in C² distance, their graph neighborhoods
are nested with an enlarged radius.
-/
lemma graphNeighborhood_mono_of_c2Distance
    {g h : Kakeya.Cinematic.C2Function}
    {R ε : ℝ} (hε : 0 ≤ ε)
    (hdist : Kakeya.Cinematic.c2Distance g h ≤ ε) :
    Kakeya.Cinematic.graphNeighborhood g R ⊆
      Kakeya.Cinematic.graphNeighborhood h (R + ε) := by
  intro p hp
  have h_main : ∃ (q : ℝ × ℝ), q ∈ Kakeya.Cinematic.functionGraph g ∧
      dist p q < R := Metric.mem_thickening_iff.mp hp
  rcases h_main with ⟨q, hq, hdist_pq⟩
  have hq1 : q.1 ∈ Kakeya.Cinematic.unitInterval := hq.1
  let q' : ℝ × ℝ := (q.1, h ⟨q.1, hq1⟩)
  have hq' : q' ∈ Kakeya.Cinematic.functionGraph h := by
    exact ⟨hq1, rfl⟩
  have h_val_diff : |g ⟨q.1, hq1⟩ - h ⟨q.1, hq1⟩| ≤ ε :=
    (Kakeya.Cinematic.abs_value_sub_le_c2Distance g h ⟨q.1, hq1⟩).trans hdist
  have h_dist_q : dist q q' ≤ ε := by
    have h : dist q q' = |q.2 - h ⟨q.1, hq1⟩| := by
      simp [q', Prod.dist_eq, Real.dist_eq] <;> rfl
    rw [h, hq.2]
    exact h_val_diff
  have h_final : dist p q' < R + ε := by
    calc dist p q' ≤ dist p q + dist q q' := dist_triangle _ _ _
      _ ≤ dist p q + ε := by gcongr
      _ < R + ε := by linarith
  exact Metric.mem_thickening_iff.mpr ⟨q', hq', h_final⟩

/--
Lipschitz bound for a half-parameter slope curve on `[0,1]`.

If `|p 1| ≤ 2` and `|p 2| ≤ 2`, then the extension of
`halfParameterSlopeCurve f p` is 128-Lipschitz on `[0,1]`.
-/
lemma halfParameterSlopeCurve_lipschitzOn_Icc01
    (f : SlopeFunction) (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    (p : Point 3) (hp1 : |p 1| ≤ 2) (hp2 : |p 2| ≤ 2) :
    LipschitzOnWith (128 : NNReal) (halfParameterSlopeCurve f p).extension
      (Set.Icc (0 : ℝ) 1) := by
  let h := (halfParameterSlopeCurve f p).extension
  have h_cd : ContDiff ℝ 2 h :=
    Kakeya.Cinematic.C2Function.extension_contDiff (halfParameterSlopeCurve f p)
  have h_diff : Differentiable ℝ h := h_cd.differentiable (by norm_num)
  have h_deriv : ∀ (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 →
      HasDerivWithinAt h (deriv h x) (Set.Icc (0 : ℝ) 1) x := by
    intro x _
    exact h_diff.differentiableAt.hasDerivAt.hasDerivWithinAt
  have h_bound : ∀ (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 →
      ‖deriv h x‖₊ ≤ (128 : NNReal) := by
    intro x hx
    let x' : Kakeya.Cinematic.UnitPoint := ⟨x, hx⟩
    have h_deriv_eq : deriv h x = (halfParameterSlopeCurve f p).firstDeriv x' :=
      Kakeya.Cinematic.C2Function.deriv_extension_eq_firstDeriv
        (halfParameterSlopeCurve f p) x'
    rw [h_deriv_eq]
    have h_f' : |deriv f x| ≤ 2 := by
      have h_xin : x ∈ Set.Icc (-1 : ℝ) 1 := by
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      exact (h_ns x h_xin).2.1
    have h_f : |f x| ≤ 2 := abs_fx_le_two f h_ns h0 hx
    have h_x_abs : |x| ≤ 1 := by
      exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h1 : |(halfParameterSlopeCurve f p).firstDeriv x'| ≤ 128 := by
      simp only [halfParameterSlopeCurve, slopeCurve_firstDeriv]
      calc
        |24 * p 1 * deriv f x + 4 * p 2 * (f x + x * deriv f x)|
          ≤ |24 * p 1 * deriv f x| + |4 * p 2 * (f x + x * deriv f x)| := by
            exact abs_add_le _ _
        _ = 24 * |p 1| * |deriv f x| + 4 * |p 2| * |f x + x * deriv f x| := by
          simp [abs_mul] <;> ring
        _ ≤ 24 * |p 1| * |deriv f x| +
              4 * |p 2| * (|f x| + |x| * |deriv f x|) := by
          have h_abs : |f x + x * deriv f x| ≤ |f x| + |x| * |deriv f x| := by
            calc
              |f x + x * deriv f x| ≤ |f x| + |x * deriv f x| := by exact abs_add_le _ _
              _ = |f x| + |x| * |deriv f x| := by rw [abs_mul]
          gcongr <;> exact h_abs
        _ ≤ 24 * 2 * 2 + 4 * 2 * (2 + 1 * 2) := by gcongr <;> linarith
        _ = 128 := by norm_num
    have h2 : ‖(halfParameterSlopeCurve f p).firstDeriv x'‖₊ ≤ (128 : NNReal) := by
      have h_norm : (↑‖(halfParameterSlopeCurve f p).firstDeriv x'‖₊ : ℝ) = |(halfParameterSlopeCurve f p).firstDeriv x'| := by
        simp [Real.norm_eq_abs]
      have h_goal : (↑‖(halfParameterSlopeCurve f p).firstDeriv x'‖₊ : ℝ) ≤ (↑(128 : NNReal) : ℝ) := by
        rw [h_norm]
        simpa using h1
      exact NNReal.coe_le_coe.mp h_goal
    exact h2
  exact Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (convex_Icc 0 1) h_deriv h_bound

/--
If `h` is L-Lipschitz on `[0,1]`, then fiberwise translation is (1+L)-Lipschitz
on the vertical strip `{p : ℝ × ℝ | p.1 ∈ [0,1]}`.
-/
lemma fiberwiseTranslate_lipschitzOn_strip
    (h : ℝ → ℝ) {L : NNReal}
    (hlip : LipschitzOnWith L h (Set.Icc (0 : ℝ) 1)) :
    LipschitzOnWith (1 + L) (Kakeya.Cinematic.fiberwiseTranslate h)
      {p : ℝ × ℝ | p.1 ∈ Set.Icc (0 : ℝ) 1} := by
  intro p hp q hq
  dsimp only [Kakeya.Cinematic.fiberwiseTranslate, Prod.dist_eq]
  have hp1 : p.1 ∈ Set.Icc (0 : ℝ) 1 := by simpa using hp
  have hq1 : q.1 ∈ Set.Icc (0 : ℝ) 1 := by simpa using hq
  have h1 : |h p.1 - h q.1| ≤ (L : ℝ) * |p.1 - q.1| :=
    hlip.dist_le_mul p.1 hp1 q.1 hq1
  have h2 : |p.2 + h p.1 - (q.2 + h q.1)| ≤
      |p.2 - q.2| + (L : ℝ) * |p.1 - q.1| := by
    calc
      |p.2 + h p.1 - (q.2 + h q.1)|
        = |(p.2 - q.2) + (h p.1 - h q.1)| := by ring_nf
      _ ≤ |p.2 - q.2| + |h p.1 - h q.1| := by exact abs_add_le _ _
      _ ≤ |p.2 - q.2| + (L : ℝ) * |p.1 - q.1| := by gcongr
  have h4 : |p.1 - q.1| ≤ ((1 + L : NNReal) : ℝ) * max |p.1 - q.1| |p.2 - q.2| := by
    have hpos : 0 ≤ ((1 + L : NNReal) : ℝ) := by positivity
    calc
      |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
      _ ≤ ((1 + L : NNReal) : ℝ) * max |p.1 - q.1| |p.2 - q.2| := by
        exact le_mul_of_one_le_left (by positivity) (by simp [NNReal.coe_add] <;> linarith)
  have h5 : |p.2 + h p.1 - (q.2 + h q.1)| ≤
      ((1 + L : NNReal) : ℝ) * max |p.1 - q.1| |p.2 - q.2| := by
    have h6 : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
    have h7 : (L : ℝ) * |p.1 - q.1| ≤ (L : ℝ) * max |p.1 - q.1| |p.2 - q.2| := by
      gcongr <;> exact le_max_left _ _
    calc
      |p.2 + h p.1 - (q.2 + h q.1)|
        ≤ |p.2 - q.2| + (L : ℝ) * |p.1 - q.1| := h2
      _ ≤ max |p.1 - q.1| |p.2 - q.2| + (L : ℝ) * max |p.1 - q.1| |p.2 - q.2| := by gcongr
      _ = ((1 + L : NNReal) : ℝ) * max |p.1 - q.1| |p.2 - q.2| := by
        simp [NNReal.coe_add] <;> ring
  have h_main : max |p.1 - q.1| |p.2 + h p.1 - (q.2 + h q.1)| ≤
      ((1 + L : NNReal) : ℝ) * max |p.1 - q.1| |p.2 - q.2| :=
    max_le h4 h5
  have h_pos : 0 ≤ ((1 + L : NNReal) : ℝ) := by positivity
  have h_edist : edist (Kakeya.Cinematic.fiberwiseTranslate h p)
        (Kakeya.Cinematic.fiberwiseTranslate h q) ≤
      (↑(1 + L) : ENNReal) * edist p q := by
    rw [edist_dist, edist_dist]
    have h3 : ENNReal.ofReal (max |p.1 - q.1| |p.2 + h p.1 - (q.2 + h q.1)|) ≤
        ENNReal.ofReal (((1 + L : NNReal) : ℝ) * max |p.1 - q.1| |p.2 - q.2|) := by
      gcongr
    have h4 : ENNReal.ofReal (((1 + L : NNReal) : ℝ) * max |p.1 - q.1| |p.2 - q.2|) =
        (↑(1 + L) : ENNReal) * ENNReal.ofReal (max |p.1 - q.1| |p.2 - q.2|) := by
      have h5 : (↑(1 + L) : ENNReal) = ENNReal.ofReal ((1 + L : NNReal) : ℝ) := by
        exact ENNReal.coe_nnreal_eq (1 + L)
      rw [h5]
      have h6 : ENNReal.ofReal ((1 + L : NNReal) : ℝ) * ENNReal.ofReal (max |p.1 - q.1| |p.2 - q.2|) =
          ENNReal.ofReal (((1 + L : NNReal) : ℝ) * max |p.1 - q.1| |p.2 - q.2|) := by
          rw [ENNReal.ofReal_mul] <;> positivity
      exact h6.symm
    rw [h4] at h3
    exact h3
  exact h_edist

/--
Domain-restricted fiberwise translation of a graph neighborhood.

If `S` is contained in `graphNeighborhood g R` and every point of `S` has
first coordinate in `[0,1]`, and `h` is L-Lipschitz on `[0,1]`, then the
fiberwise-translated image of `S` is contained in
`graphNeighborhood (g.add h) ((1+L)*R)`.
-/
lemma fiberwiseTranslate_graphNeighborhood_on
    (g h : Kakeya.Cinematic.C2Function)
    {L : NNReal} {R : ℝ} (hR : 0 ≤ R)
    (hlip : LipschitzOnWith L h.extension (Set.Icc (0 : ℝ) 1))
    (S : Set (ℝ × ℝ))
    (hS1 : S ⊆ Kakeya.Cinematic.graphNeighborhood g R)
    (hS2 : ∀ p ∈ S, p.1 ∈ Set.Icc (0 : ℝ) 1) :
    Kakeya.Cinematic.fiberwiseTranslate h.extension '' S ⊆
    Kakeya.Cinematic.graphNeighborhood (g.add h)
      (((1 + L : NNReal) : ℝ) * R) := by
  intro y hy
  rcases hy with ⟨p, hp, rfl⟩
  have hp_in_nbhd : p ∈ Kakeya.Cinematic.graphNeighborhood g R := hS1 hp
  have hp1 : p.1 ∈ Set.Icc (0 : ℝ) 1 := hS2 p hp
  have h_main : ∃ (q : ℝ × ℝ), q ∈ Kakeya.Cinematic.functionGraph g ∧
      dist p q < R := Metric.mem_thickening_iff.mp hp_in_nbhd
  rcases h_main with ⟨q, hq, hdist⟩
  have hq1 : q.1 ∈ Set.Icc (0 : ℝ) 1 := hq.1
  let q' := Kakeya.Cinematic.fiberwiseTranslate h.extension q
  have hq' : q' ∈ Kakeya.Cinematic.functionGraph (g.add h) := by
    rw [← Kakeya.Cinematic.fiberwiseTranslate_functionGraph g h]
    exact ⟨q, hq, rfl⟩
  let strip : Set (ℝ × ℝ) := {p | p.1 ∈ Set.Icc (0 : ℝ) 1}
  have hp_strip : p ∈ strip := hp1
  have hq_strip : q ∈ strip := hq1
  have hlip' := fiberwiseTranslate_lipschitzOn_strip h.extension hlip
  have hdist' : dist (Kakeya.Cinematic.fiberwiseTranslate h.extension p) q' ≤
      ((1 + L : NNReal) : ℝ) * dist p q :=
    hlip'.dist_le_mul p hp_strip q hq_strip
  have h6 : ∃ (z : ℝ × ℝ), z ∈ Kakeya.Cinematic.functionGraph (g.add h) ∧
      dist (Kakeya.Cinematic.fiberwiseTranslate h.extension p) z <
        ((1 + L : NNReal) : ℝ) * R := by
    refine ⟨q', hq', ?_⟩
    calc
      dist (Kakeya.Cinematic.fiberwiseTranslate h.extension p) q'
        ≤ ((1 + L : NNReal) : ℝ) * dist p q := hdist'
      _ < ((1 + L : NNReal) : ℝ) * R := by gcongr
  exact Metric.mem_thickening_iff.mpr h6

/--
Geometric containment for amplified projected pieces (domain-restricted version).

Uses `LipschitzOnWith` on `[0,1]` instead of global `LipschitzWith`, and
requires the source set `E` to have first coordinate in `[0,1]` after
cinematic shear.
-/
lemma amplified_geometric_containment_on
    (c0 : ℝ)
    (sourceCurve assignedCurve : Kakeya.Cinematic.C2Function)
    (shift : Kakeya.Cinematic.C2Function)
    {R ε : ℝ} {L : NNReal} (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hlip : LipschitzOnWith L shift.extension (Set.Icc (0 : ℝ) 1))
    (E : Set Point2)
    (hsource : cinematicShear c0 '' E ⊆
          Kakeya.Cinematic.graphNeighborhood sourceCurve R)
    (hclose : Kakeya.Cinematic.c2Distance
        (sourceCurve.add shift) assignedCurve ≤ ε)
    (h_domain : ∀ p ∈ cinematicShear c0 '' E, p.1 ∈ Set.Icc (0 : ℝ) 1) :
    Kakeya.Cinematic.fiberwiseTranslate shift.extension ''
      (cinematicShear c0 '' E) ⊆
    Kakeya.Cinematic.graphNeighborhood assignedCurve
      (((1 + L : NNReal) : ℝ) * R + ε) := by
  let S := cinematicShear c0 '' E
  have h1 : S ⊆ Kakeya.Cinematic.graphNeighborhood sourceCurve R := hsource
  have h2 : Kakeya.Cinematic.fiberwiseTranslate shift.extension '' S ⊆
      Kakeya.Cinematic.graphNeighborhood (sourceCurve.add shift)
        (((1 + L : NNReal) : ℝ) * R) :=
    fiberwiseTranslate_graphNeighborhood_on sourceCurve shift hR hlip S h1 h_domain
  have h3 : Kakeya.Cinematic.graphNeighborhood
      (sourceCurve.add shift) (((1 + L : NNReal) : ℝ) * R) ⊆
    Kakeya.Cinematic.graphNeighborhood assignedCurve
      (((1 + L : NNReal) : ℝ) * R + ε) :=
    graphNeighborhood_mono_of_c2Distance (by linarith) hclose
  exact Set.Subset.trans h2 h3

end Kakeya.Assouad
