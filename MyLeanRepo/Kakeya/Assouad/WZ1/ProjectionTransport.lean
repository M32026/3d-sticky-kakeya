import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49ActualAffineTripleTransportStatements
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# Transport lemmas for WZ1 projection theorem conclusions

Core lemmas: line count bijection, dot-difference scaling,
delta-separated scaling, Frostman scaling, unit-ball affine bound.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal

/-! ## Line count transport -/

/--
Cardinality of points of `A.image e` in a decidable set `S` equals
cardinality of points of `A` in the preimage `e ⁻¹' S`.
-/
lemma line_count_bijection
    {e : Point2 ≃ Point2} {A : DiscreteSet 2}
    {S : Set Point2} [DecidablePred (fun p : Point2 => p ∈ S)] :
    ((A.image e).filter (fun p => p ∈ S)).card =
    (A.filter (fun p => e p ∈ S)).card := by
  have h : (A.image e).filter (fun p => p ∈ S) =
      (A.filter (fun p => e p ∈ S)).image e := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hS⟩
      exact ⟨a, ⟨ha, hS⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hS⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, hS⟩
  rw [h]
  rw [Finset.card_image_of_injective _ e.injective]

/-! ## Dot-difference scaling -/

/--
Scaling all points: F by `s`, G₁/G₂ by `t`, scales dot-differences by `s * t`.
-/
lemma dot_diff_scaling
    (s t : ℝ) (H : Finset (Point2 × Point2 × Point2)) :
    (H.image (fun h => inner ℝ h.1 (h.2.1 - h.2.2))).image (fun x : ℝ => s * t * x) =
    (H.image (fun edge =>
      (s • edge.1, t • edge.2.1, t • edge.2.2))).image
        (fun h => inner ℝ h.1 (h.2.1 - h.2.2)) := by
  classical
  let f1 : (Point2 × Point2 × Point2) → ℝ :=
    fun h => inner ℝ h.1 (h.2.1 - h.2.2)
  let scale : (Point2 × Point2 × Point2) → (Point2 × Point2 × Point2) :=
    fun edge => (s • edge.1, t • edge.2.1, t • edge.2.2)
  have h_comm : ∀ edge, f1 (scale edge) = (s * t) * f1 edge := by
    intro edge
    simp only [f1, scale]
    have h2 : t • edge.2.1 - t • edge.2.2 = t • (edge.2.1 - edge.2.2) := by
      rw [smul_sub]
    rw [h2]
    have h3 : inner ℝ (s • edge.1) (t • (edge.2.1 - edge.2.2)) =
        (s * t) * inner ℝ edge.1 (edge.2.1 - edge.2.2) := by
      rw [inner_smul_left, inner_smul_right]
      <;> simp
      <;> ring
    exact h3
  have h1 : (H.image scale).image f1 =
      (H.image f1).image (fun x : ℝ => s * t * x) := by
    calc
      (H.image scale).image f1
        = H.image (fun edge => f1 (scale edge)) := by
          rw [Finset.image_image] <;> rfl
      _ = H.image (fun edge => (s * t) * f1 edge) := by
          apply Finset.image_congr
          intro edge _
          exact h_comm edge
      _ = (H.image f1).image (fun x : ℝ => s * t * x) := by
          rw [Finset.image_image] <;> rfl
  exact h1.symm

/-! ## Delta-separated scaling -/

/-- Under dilation by `s > 0`, `δ`-separated becomes `s * δ`-separated. -/
lemma is_delta_separated_scaling
    {A : DiscreteSet 2} {δ s : ℝ} (hs : 0 < s)
    (h : DiscreteSet.IsDeltaSeparated A δ) :
    DiscreteSet.IsDeltaSeparated (A.image (fun p => s • p)) (s * δ) := by
  intro x hx y hy hxy
  rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨y0, hy0, rfl⟩
  have hxy0 : x0 ≠ y0 := by
    intro h; apply hxy; rw [h]
  have hdist : dist (s • x0) (s • y0) = s * dist x0 y0 := by
    have h1 : dist (s • x0) (s • y0) = ‖(s • x0) - (s • y0)‖ := by rfl
    rw [h1]
    have h2 : (s • x0) - (s • y0) = s • (x0 - y0) := by
      rw [smul_sub]
    rw [h2]
    have h3 : ‖s • (x0 - y0)‖ = |s| * ‖x0 - y0‖ := norm_smul s (x0 - y0)
    rw [h3]
    have h4 : |s| = s := abs_of_pos hs
    rw [h4]
    have h5 : ‖x0 - y0‖ = dist x0 y0 := by
      simp [dist_eq_norm]
    rw [h5]
  rw [hdist]
  have hsep : δ ≤ dist x0 y0 := h hx0 hy0 hxy0
  exact mul_le_mul_of_nonneg_left hsep (by linarith)

/-! ## Frostman scaling -/

/-- Ball count is preserved under an equivalence that maps balls to balls. -/
lemma ball_count_equiv
    {A : DiscreteSet 2} {e : Point2 ≃ Point2}
    {x x' : Point2} {r r' : ℝ}
    (h : ∀ y, dist (e y) x ≤ r ↔ dist y x' ≤ r') :
    DiscreteSet.ballCount (A.image e) x r =
    DiscreteSet.ballCount A x' r' := by
  simp only [DiscreteSet.ballCount]
  have h_filter : (A.image e).filter (fun y => dist y x ≤ r) =
      (A.filter (fun y => dist y x' ≤ r')).image e := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hS⟩
      have hS' : dist a x' ≤ r' := (h a).mp hS
      exact ⟨a, ⟨ha, hS'⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hS⟩, rfl⟩
      have hS' : dist (e a) x ≤ r := (h a).mpr hS
      exact ⟨⟨a, ha, rfl⟩, hS'⟩
  rw [h_filter, Finset.card_image_of_injective _ e.injective]

/--
Under dilation by `s ≥ 1`, Frostman with constant `C` and exponent `s_exp ≥ 0`
transports to constant `C / s^s_exp` and scale `s * δ`.
-/
lemma is_frostman_scaling
    {A : DiscreteSet 2} {δ s_exp : ℝ} {C : ENNReal} {s : ℝ}
    (hs : 1 ≤ s) (hs_exp : 0 ≤ s_exp) (hδ_nonneg : 0 ≤ δ)
    (h : DiscreteSet.IsFrostman A δ s_exp C) :
    DiscreteSet.IsFrostman (A.image (fun p => s • p))
      (s * δ) s_exp (C / Kakeya.realRpowENN s s_exp) := by
  intro x r hδr hr1
  have hspos : 0 < s := by linarith
  have hr_nonneg : 0 ≤ r := by
    have h1 : 0 ≤ s * δ := by exact mul_nonneg (by linarith) hδ_nonneg
    linarith
  let x0 : Point2 := (s⁻¹ : ℝ) • x
  have hx_eq : s • x0 = x := by
    have h : s • ((s⁻¹ : ℝ) • x) = (s * s⁻¹ : ℝ) • x := by rw [smul_smul]
    rw [h]
    have h2 : s * s⁻¹ = 1 := by
      field_simp
      <;> ring
    rw [h2, one_smul]
  let r0 := r / s
  have hδ0 : δ ≤ r0 := by
    dsimp only [r0]
    have h : s * δ ≤ r := hδr
    have hdiv : (s * δ) / s = δ := by
      field_simp [hspos.ne'] <;> ring
    have h5 : δ ≤ r / s := by
      rw [← hdiv]
      gcongr
    exact h5
  have hr01 : r0 ≤ 1 := by
    dsimp only [r0]
    have h : r ≤ 1 := hr1
    have hdiv1 : r / s ≤ 1 / s := by gcongr
    have hdiv2 : 1 / s ≤ 1 := by
      apply (div_le_one hspos).mpr
      exact hs
    exact hdiv1.trans hdiv2
  have hr0_nonneg : 0 ≤ r0 := by
    dsimp only [r0]
    exact div_nonneg hr_nonneg (by linarith)
  let e : Point2 ≃ Point2 :=
    { toFun := fun p => s • p
      invFun := fun p => (s⁻¹ : ℝ) • p
      left_inv := by
        intro p
        have h : (s⁻¹ : ℝ) • (s • p) = p := by
          rw [smul_smul]
          have h2 : s⁻¹ * s = 1 := by field_simp [hspos.ne'] <;> ring
          rw [h2, one_smul]
        exact h
      right_inv := by
        intro p
        have h : s • ((s⁻¹ : ℝ) • p) = p := by
          rw [smul_smul]
          have h2 : s * s⁻¹ = 1 := by field_simp [hspos.ne'] <;> ring
          rw [h2, one_smul]
        exact h }
  have h_dist_eq : ∀ (y : Point2), dist (e y) x ≤ r ↔ dist y x0 ≤ r0 := by
    intro y
    have h1 : dist (e y) x = s * dist y x0 := by
      have h_x_eq : e x0 = x := by
        simpa [e] using hx_eq
      have h_eq1 : dist (e y) x = dist (e y) (e x0) := by rw [h_x_eq]
      rw [h_eq1]
      have h2 : dist (e y) (e x0) = s * dist y x0 := by
        have h3 : dist (e y) (e x0) = ‖(e y) - (e x0)‖ := by rfl
        rw [h3]
        have h4 : (e y) - (e x0) = s • (y - x0) := by
          simp [e]
          <;> rw [smul_sub]
        rw [h4]
        have h5 : ‖s • (y - x0)‖ = |s| * ‖y - x0‖ := norm_smul s (y - x0)
        rw [h5]
        have h6 : |s| = s := abs_of_pos hspos
        rw [h6]
        have h7 : ‖y - x0‖ = dist y x0 := by simp [dist_eq_norm]
        rw [h7]
      exact h2
    rw [h1]
    have h_div : (s * dist y x0) / s = dist y x0 := by
      field_simp [hspos.ne'] <;> ring
    have h_iff : s * dist y x0 ≤ r ↔ dist y x0 ≤ r / s := by
      constructor
      · intro h8
        have h10 : dist y x0 ≤ r / s := by
          calc dist y x0
            = (s * dist y x0) / s := h_div.symm
          _ ≤ r / s := by gcongr
        exact h10
      · intro h8
        have h9 : s * dist y x0 ≤ s * (r / s) := by gcongr
        have h10 : s * (r / s) = r := by
          field_simp [hspos.ne'] <;> ring
        rw [h10] at h9
        exact h9
    exact h_iff
  have h_image : A.image (fun p : Point2 => s • p) = A.image e := by
    apply Finset.image_congr
    intro p _
    rfl
  rw [h_image]
  have h_ball : DiscreteSet.ballCount (A.image e) x r =
      DiscreteSet.ballCount A x0 r0 :=
    ball_count_equiv h_dist_eq
  rw [h_ball]
  have h_main : DiscreteSet.ballCount A x0 r0 ≤
      C * Kakeya.realRpowENN r0 s_exp * DiscreteSet.enncard A := h x0 r0 hδ0 hr01
  have h_card : DiscreteSet.enncard (A.image e) = DiscreteSet.enncard A := by
    simp [DiscreteSet.enncard, Finset.card_image_of_injective _ e.injective]
  have h_rpow_div : Real.rpow r0 s_exp = Real.rpow r s_exp / Real.rpow s s_exp := by
    have h1 : 0 ≤ r := hr_nonneg
    have h2 : 0 ≤ s := by linarith
    exact Real.div_rpow h1 h2 s_exp
  have h_rpow0 : Kakeya.realRpowENN r0 s_exp =
      Kakeya.realRpowENN r s_exp / Kakeya.realRpowENN s s_exp := by
    simp only [Kakeya.realRpowENN]
    rw [h_rpow_div]
    have h_rpow_s_pos : 0 < Real.rpow s s_exp := by
      apply Real.rpow_pos_of_pos
      linarith
    exact ENNReal.ofReal_div_of_pos h_rpow_s_pos
  calc
    DiscreteSet.ballCount A x0 r0
      ≤ C * Kakeya.realRpowENN r0 s_exp * DiscreteSet.enncard A := h_main
    _ = C * (Kakeya.realRpowENN r s_exp / Kakeya.realRpowENN s s_exp) * DiscreteSet.enncard A := by
        rw [h_rpow0]
    _ = (C / Kakeya.realRpowENN s s_exp) * Kakeya.realRpowENN r s_exp * DiscreteSet.enncard (A.image e) := by
        rw [h_card]
        <;> simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
        <;> ring

/-! ## Unit ball after affine -/

/--
If all points of `A` are within distance `R` of origin, then after scaling by
`s ≥ 0` and translating by `t`, the image is within `s * R + ‖t‖` of origin.
-/
lemma is_in_ball_after_affine
    {A : DiscreteSet 2} {R s : ℝ} {t : Point2}
    (hs : 0 ≤ s)
    (hA : ∀ x ∈ A, dist x 0 ≤ R) :
    ∀ y ∈ A.image (fun p => s • p + t), dist y 0 ≤ s * R + ‖t‖ := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
  have h3 : ‖x‖ ≤ R := by
    simpa [dist_eq_norm] using hA x hx
  have h4 : ‖s • x‖ = s * ‖x‖ := by
    have h5 : ‖s • x‖ = |s| * ‖x‖ := norm_smul s x
    rw [h5]
    have h6 : |s| = s := abs_of_nonneg hs
    rw [h6]
  calc
    dist (s • x + t) 0
      = ‖s • x + t‖ := by simp [dist_eq_norm]
    _ ≤ ‖s • x‖ + ‖t‖ := norm_add_le _ _
    _ = s * ‖x‖ + ‖t‖ := by rw [h4]
    _ ≤ s * R + ‖t‖ := by
      have h7 : s * ‖x‖ ≤ s * R := mul_le_mul_of_nonneg_left h3 hs
      linarith


/-! ## Alternative A transport under dilation -/

/--
Line count is monotone in strip width: a narrower strip has no more points.
-/
lemma line_count_width_mono
    {A : DiscreteSet 2} {base direction : Point2} {r1 r2 : ℝ}
    (h : r1 ≤ r2) :
    wz1DiscreteLineCount A base direction r1 ≤
      wz1DiscreteLineCount A base direction r2 := by
  classical
  have h_filter : A.filter (fun p : Point2 => p ∈ wz1LineNeighborhood base direction r1) ⊆
      A.filter (fun p : Point2 => p ∈ wz1LineNeighborhood base direction r2) := by
    intro x hx
    have h_in : x ∈ A := (Finset.mem_filter.mp hx).1
    have h_prop1 : x ∈ wz1LineNeighborhood base direction r1 := (Finset.mem_filter.mp hx).2
    have h_prop2 : x ∈ wz1LineNeighborhood base direction r2 := by
      simp only [wz1LineNeighborhood, Set.mem_setOf_eq] at h_prop1 ⊢
      exact h_prop1.trans h
    exact Finset.mem_filter.mpr ⟨h_in, h_prop2⟩
  have h_card : (A.filter (fun p : Point2 => p ∈ wz1LineNeighborhood base direction r1)).card ≤
      (A.filter (fun p : Point2 => p ∈ wz1LineNeighborhood base direction r2)).card :=
    Finset.card_le_card h_filter
  have h_enn : ((A.filter (fun p : Point2 => p ∈ wz1LineNeighborhood base direction r1)).card : ENNReal) ≤
      ((A.filter (fun p : Point2 => p ∈ wz1LineNeighborhood base direction r2)).card : ENNReal) := by
    exact_mod_cast h_card
  simpa [wz1DiscreteLineCount] using h_enn

/--
If `A' = s • A` with `s ≥ 1`, then the line count of `A'` at width `delta`
(with base 0) is at most the line count of `A` at width `delta`.
The preimage strip has width `delta/s ≤ delta`, so monotonicity applies.
-/
lemma line_count_dilation_F
    {A : DiscreteSet 2} {s : ℝ} (hs : 1 ≤ s)
    {direction : Point2} {delta : ℝ} (hdelta : 0 < delta) :
    wz1DiscreteLineCount (A.image (fun p => s • p)) 0 direction delta ≤
      wz1DiscreteLineCount A 0 direction delta := by
  classical
  have hspos : 0 < s := by linarith
  let f : Point2 → Point2 := fun p => s • p
  have hf_inj : Function.Injective f := by
    intro p q h
    have h2 : s • p = s • q := h
    have h3 : p = q := by
      simpa [smul_smul, hspos.ne'] using congr_arg (fun x : Point2 => s⁻¹ • x) h2
    exact h3
  let S1 : Finset Point2 := (A.image f).filter (fun p =>
      p ∈ wz1LineNeighborhood 0 direction delta)
  let S2 : Finset Point2 := A.filter (fun p =>
      p ∈ wz1LineNeighborhood 0 direction (delta / s))
  have h_preimage : S1 = S2.image f := by
    ext y
    simp only [S1, S2, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hS⟩
      have hS' : |inner ℝ (f x) (wz1Perp2 direction)| ≤ delta := by
        simpa [wz1LineNeighborhood] using hS
      have hfx : f x = s • x := by simp [f]
      rw [hfx] at hS'
      have h4 : inner ℝ (s • x) (wz1Perp2 direction) =
          s * inner ℝ x (wz1Perp2 direction) := by
        have h41 : inner ℝ (s • x) (wz1Perp2 direction) =
            (starRingEnd ℝ s) * inner ℝ x (wz1Perp2 direction) := by
          rw [inner_smul_left]
        rw [h41]
        have h42 : (starRingEnd ℝ s) = s := by simp
        rw [h42] <;> ring
      rw [h4] at hS'
      have h5 : |s * inner ℝ x (wz1Perp2 direction)| =
          s * |inner ℝ x (wz1Perp2 direction)| := by
        rw [abs_mul, abs_of_pos hspos]
      rw [h5] at hS'
      have h6 : |inner ℝ x (wz1Perp2 direction)| ≤ delta / s := by
        calc
          |inner ℝ x (wz1Perp2 direction)|
            = s⁻¹ * (s * |inner ℝ x (wz1Perp2 direction)|) := by
              field_simp [hspos.ne'] <;> ring
          _ ≤ s⁻¹ * delta := by gcongr
          _ = delta / s := by field_simp [hspos.ne'] <;> ring
      have h_goal : x ∈ wz1LineNeighborhood 0 direction (delta / s) := by
        simpa [wz1LineNeighborhood] using h6
      exact ⟨x, ⟨hx, h_goal⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hS⟩, rfl⟩
      have h_y_in_strip : f x ∈ wz1LineNeighborhood 0 direction delta := by
        have hS' : |inner ℝ x (wz1Perp2 direction)| ≤ delta / s := by
          simpa [wz1LineNeighborhood, sub_zero] using hS
        have h_goal : |inner ℝ (f x) (wz1Perp2 direction)| ≤ delta := by
          have hfx : f x = s • x := by simp [f]
          rw [hfx]
          have h4 : inner ℝ (s • x) (wz1Perp2 direction) =
              s * inner ℝ x (wz1Perp2 direction) := by
            have h41 : inner ℝ (s • x) (wz1Perp2 direction) =
                (starRingEnd ℝ s) * inner ℝ x (wz1Perp2 direction) := by
              rw [inner_smul_left]
            rw [h41]
            have h42 : (starRingEnd ℝ s) = s := by simp
            rw [h42] <;> ring
          rw [h4]
          have h5 : |s * inner ℝ x (wz1Perp2 direction)| =
              s * |inner ℝ x (wz1Perp2 direction)| := by
            rw [abs_mul, abs_of_pos hspos]
          rw [h5]
          have h6 : s * |inner ℝ x (wz1Perp2 direction)| ≤ s * (delta / s) := by
            gcongr
          have h7 : s * (delta / s) = delta := by
            field_simp [hspos.ne'] <;> ring
          rw [h7] at h6
          exact h6
        simpa [wz1LineNeighborhood] using h_goal
      exact ⟨⟨x, hx, rfl⟩, h_y_in_strip⟩
  have h_card : S1.card = S2.card := by
    rw [h_preimage]
    rw [Finset.card_image_of_injective _ hf_inj]
  have h_delta_s_le_delta : delta / s ≤ delta := by
    have h8 : delta / s ≤ delta / 1 := by gcongr <;> linarith
    simpa using h8
  have h_mono : (S2.card : ENNReal) ≤
      ((A.filter (fun p => p ∈ wz1LineNeighborhood 0 direction delta)).card : ENNReal) := by
    have h := line_count_width_mono (A := A) (base := 0) (direction := direction)
        (r1 := delta / s) (r2 := delta) h_delta_s_le_delta
    simpa [wz1DiscreteLineCount, S2] using h
  have h1 : wz1DiscreteLineCount (A.image f) 0 direction delta = (S1.card : ENNReal) := by
    simp only [wz1DiscreteLineCount, S1] <;> rfl
  rw [h1]
  rw [h_card]
  exact h_mono

/--
Line count under dilation with arbitrary base: scaling points and base by `s`
and width by `s` preserves the line count exactly.
-/
lemma line_count_dilation_eq
    {A : DiscreteSet 2} {s : ℝ} (hs : 0 < s)
    {base direction : Point2} {delta : ℝ} :
    wz1DiscreteLineCount (A.image (fun p => s • p)) (s • base) direction (s * delta) =
      wz1DiscreteLineCount A base direction delta := by
  classical
  let f : Point2 → Point2 := fun p => s • p
  have hf_inj : Function.Injective f := by
    intro p q h
    have h2 : s⁻¹ • (s • p) = s⁻¹ • (s • q) := by
      exact congr_arg (fun x : Point2 => s⁻¹ • x) h
    simpa [smul_smul, hs.ne'] using h2
  have h_equiv : ∀ p, f p ∈ wz1LineNeighborhood (s • base) direction (s * delta) ↔
      p ∈ wz1LineNeighborhood base direction delta := by
    intro p
    simp only [wz1LineNeighborhood, Set.mem_setOf_eq]
    have h1 : inner ℝ (f p - s • base) (wz1Perp2 direction) =
        s * inner ℝ (p - base) (wz1Perp2 direction) := by
      have h2 : f p - s • base = s • (p - base) := by
        have hf : f p = s • p := by rfl
        rw [hf]
        exact Eq.symm (smul_sub s p base)
      rw [h2, inner_smul_left] <;> simp
    rw [h1]
    have h_abs : |s * inner ℝ (p - base) (wz1Perp2 direction)| =
        s * |inner ℝ (p - base) (wz1Perp2 direction)| := by
      rw [abs_mul, abs_of_pos hs]
    rw [h_abs]
    exact ⟨fun h => by
      have h3 : s * |inner ℝ (p - base) (wz1Perp2 direction)| ≤ s * delta := h
      have h4 : |inner ℝ (p - base) (wz1Perp2 direction)| ≤ delta := by
        calc |inner ℝ (p - base) (wz1Perp2 direction)|
            = (s * |inner ℝ (p - base) (wz1Perp2 direction)|) / s := by field_simp [hs.ne'] <;> ring
          _ ≤ (s * delta) / s := by gcongr
          _ = delta := by field_simp [hs.ne'] <;> ring
      exact h4,
      fun h => mul_le_mul_of_nonneg_left h (by linarith)⟩
  let S1 : Finset Point2 := (A.image f).filter (fun p =>
      p ∈ wz1LineNeighborhood (s • base) direction (s * delta))
  let S2 : Finset Point2 := A.filter (fun p =>
      p ∈ wz1LineNeighborhood base direction delta)
  have h_filter : S1 = S2.image f := by
    ext y
    simp only [S1, S2, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hS⟩
      exact ⟨x, ⟨hx, (h_equiv x).mp hS⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hS⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, (h_equiv x).mpr hS⟩
  have h_card : S1.card = S2.card := by
    rw [h_filter, Finset.card_image_of_injective _ hf_inj]
  have h1 : wz1DiscreteLineCount (A.image f) (s • base) direction (s * delta) = (S1.card : ENNReal) := by
    simp only [wz1DiscreteLineCount, S1] <;> rfl
  have h2 : wz1DiscreteLineCount A base direction delta = (S2.card : ENNReal) := by
    simp only [wz1DiscreteLineCount, S2] <;> rfl
  rw [h1, h2] <;> exact_mod_cast h_card

/--
Line count is preserved under translation (with correspondingly shifted base).
-/
lemma line_count_translation
    {A : DiscreteSet 2} {t base : Point2} {direction : Point2} {radius : ℝ} :
    wz1DiscreteLineCount (A.image (fun p => p + t)) (base + t) direction radius =
      wz1DiscreteLineCount A base direction radius := by
  classical
  let f : Point2 → Point2 := fun p => p + t
  have hf_inj : Function.Injective f := by
    intro p q h
    simpa [f] using h
  have h_equiv : ∀ p, f p ∈ wz1LineNeighborhood (base + t) direction radius ↔
      p ∈ wz1LineNeighborhood base direction radius := by
    intro p
    simp only [wz1LineNeighborhood, Set.mem_setOf_eq, f]
    have h2 : (p + t) - (base + t) = p - base := by
      have h3 : ∀ (a b c : Point2), (a + c) - (b + c) = a - b := by
        intro a b c
        simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
        <;> aesop
      exact h3 p base t
    rw [h2]
  let S1 : Finset Point2 := (A.image f).filter (fun p =>
      p ∈ wz1LineNeighborhood (base + t) direction radius)
  let S2 : Finset Point2 := A.filter (fun p =>
      p ∈ wz1LineNeighborhood base direction radius)
  have h_filter : S1 = S2.image f := by
    ext y
    simp only [S1, S2, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hS⟩
      exact ⟨x, ⟨hx, (h_equiv x).mp hS⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hS⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, (h_equiv x).mpr hS⟩
  have h_card : S1.card = S2.card := by
    rw [h_filter]
    rw [Finset.card_image_of_injective _ hf_inj]
  have h_goal : (S1.card : ENNReal) = (S2.card : ENNReal) := by
    exact_mod_cast h_card
  have h1 : wz1DiscreteLineCount (A.image f) (base + t) direction radius = (S1.card : ENNReal) := by
    simp only [wz1DiscreteLineCount, S1]
    <;> rfl
  have h2 : wz1DiscreteLineCount A base direction radius = (S2.card : ENNReal) := by
    simp only [wz1DiscreteLineCount, S2]
    <;> rfl
  rw [h1, h2]
  exact h_goal

/--
Line count is monotone in the point set: if `A ⊆ B`, the line count of `A`
is at most the line count of `B`.
-/
lemma line_count_subset_mono
    {A B : DiscreteSet 2} {base direction : Point2} {delta : ℝ}
    (h : A ⊆ B) :
    wz1DiscreteLineCount A base direction delta ≤
      wz1DiscreteLineCount B base direction delta := by
  classical
  have h_filter : ∀ (p : Point2 → Prop) [DecidablePred p],
      (A.filter p).card ≤ (B.filter p).card := by
    intro p _
    apply Finset.card_le_card
    intro x hx
    have h1 : x ∈ A ∧ p x := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨h h1.1, h1.2⟩
  simpa [wz1DiscreteLineCount] using h_filter _

/--
Combined scaling+translation transport for line counts.

If `A_norm = (s • A_cell) + t` with `s ≥ 1` and `A_cell ⊆ A`, then
the line count of `A_norm` at `(base, delta)` is bounded by the line count
of `A` at `(s⁻¹ • (base - t), delta)`.

This is the transport needed for Alternative A on the G₁/G₂ components.
-/
lemma line_count_scaling_transport
    {A A_cell : DiscreteSet 2} {s : ℝ} (hs : 1 ≤ s) {t : Point2}
    (h_sub : A_cell ⊆ A)
    {base direction : Point2} {delta : ℝ} (hdelta : 0 < delta) :
    wz1DiscreteLineCount ((A_cell.image (fun p => s • p)).image (fun p => p + t))
      base direction delta ≤
    wz1DiscreteLineCount A (s⁻¹ • (base - t)) direction delta := by
  classical
  have hspos : 0 < s := by linarith
  set scaled : DiscreteSet 2 := A_cell.image (fun p => s • p) with hscaled
  set b : Point2 := s⁻¹ • (base - t) with hb_def
  have h_sb : s • b = base - t := by
    rw [hb_def, smul_smul]
    have h : s * s⁻¹ = 1 := by field_simp [hspos.ne']
    rw [h]
    simp
  have h_base_add : (base - t) + t = base := by
    exact sub_add_cancel base t
  have h_delta_le : delta ≤ s * delta := by
    have h : s ≥ 1 := hs
    have h2 : s * delta ≥ 1 * delta := by gcongr
    linarith
  have h1 : wz1DiscreteLineCount (scaled.image (fun p => p + t)) base direction delta =
      wz1DiscreteLineCount scaled (base - t) direction delta := by
    have h_trans : wz1DiscreteLineCount (scaled.image (fun p => p + t)) ((base - t) + t) direction delta =
        wz1DiscreteLineCount scaled (base - t) direction delta :=
      line_count_translation (A := scaled) (t := t) (base := base - t) (direction := direction) (radius := delta)
    rw [h_base_add] at h_trans
    exact h_trans
  have h2 : wz1DiscreteLineCount scaled (base - t) direction delta ≤
      wz1DiscreteLineCount scaled (s • b) direction (s * delta) := by
    rw [h_sb]
    exact line_count_width_mono h_delta_le
  have h3 : wz1DiscreteLineCount scaled (s • b) direction (s * delta) =
      wz1DiscreteLineCount A_cell b direction delta :=
    line_count_dilation_eq (A := A_cell) (hs := hspos) (base := b) (direction := direction) (delta := delta)
  have h4 : wz1DiscreteLineCount A_cell b direction delta ≤
      wz1DiscreteLineCount A b direction delta :=
    line_count_subset_mono (A := A_cell) (B := A) (base := b) (direction := direction) (delta := delta) h_sub
  calc
    wz1DiscreteLineCount (scaled.image (fun p => p + t)) base direction delta
      = wz1DiscreteLineCount scaled (base - t) direction delta := h1
    _ ≤ wz1DiscreteLineCount scaled (s • b) direction (s * delta) := h2
    _ = wz1DiscreteLineCount A_cell b direction delta := h3
    _ ≤ wz1DiscreteLineCount A b direction delta := h4

/-! ## Alternative B transport under dilation -/

/--
Scaling of real covering numbers under dilation by `k > 0`.
-/
lemma real_covering_number_scaling
    {k : ℝ} (hk : 0 < k) {ε : ℝ} (hε : 0 ≤ ε) {S : Set ℝ} :
    Metric.externalCoveringNumber (Real.toNNReal (k * ε)) ((fun x : ℝ => k * x) '' S) =
    Metric.externalCoveringNumber (Real.toNNReal ε) S := by
  let f : ℝ → ℝ := fun x => k * x
  let g : ℝ → ℝ := fun x => x / k
  have hf_inj : Function.Injective f := by
    intro x y h
    have h6 : k * x = k * y := h
    have h7 : x = y := by
      apply mul_left_cancel₀ hk.ne'
      exact h6
    exact h7
  have hg_inj : Function.Injective g := by
    intro x y h
    have h6 : x / k = y / k := h
    have h7 : x = y := by
      field_simp [hk.ne'] at h6 <;> exact h6
    exact h7
  have hgf : ∀ x, g (f x) = x := by
    intro x; simp [f, g, hk.ne'] <;> field_simp [hk.ne'] <;> ring
  have hfg : ∀ x, f (g x) = x := by
    intro x; simp [f, g, hk.ne'] <;> field_simp [hk.ne'] <;> ring
  have h_img_g_f : g '' (f '' S) = S := by
    rw [Set.image_image]
    have h1 : (g ∘ f) '' S = S := by
      rw [show g ∘ f = id from funext hgf]
      simp
    exact h1
  have h_lip_f : LipschitzWith (Real.toNNReal k) f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h1 : dist (f x) (f y) = |f x - f y| := by simp [dist_eq_norm]
    have h2 : f x - f y = k * (x - y) := by simp [f] <;> ring
    have h3 : |k * (x - y)| = k * |x - y| := by
      rw [abs_mul, abs_of_pos hk]
    have h4 : dist x y = |x - y| := by simp [dist_eq_norm]
    have hcoef : (↑(Real.toNNReal k) : ℝ) = k := by
      rw [Real.coe_toNNReal] <;> linarith
    have h_eq : dist (f x) (f y) = (↑(Real.toNNReal k) : ℝ) * dist x y := by
      calc
        dist (f x) (f y) = |f x - f y| := h1
        _ = |k * (x - y)| := by rw [h2]
        _ = k * |x - y| := h3
        _ = k * dist x y := by rw [h4]
        _ = (↑(Real.toNNReal k) : ℝ) * dist x y := by rw [hcoef]
    exact le_of_eq h_eq
  have h_lip_g : LipschitzWith (Real.toNNReal (1 / k)) g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hpos : 0 ≤ 1 / k := by positivity
    have h1 : dist (g x) (g y) = |g x - g y| := by simp [dist_eq_norm]
    have h2 : g x - g y = (1 / k) * (x - y) := by simp [g] <;> ring
    have h3 : |(1 / k) * (x - y)| = (1 / k) * |x - y| := by
      rw [abs_mul, abs_of_nonneg hpos]
    have h4 : dist x y = |x - y| := by simp [dist_eq_norm]
    have hcoef : (↑(Real.toNNReal (1 / k)) : ℝ) = 1 / k := by
      rw [Real.coe_toNNReal] <;> positivity
    have h_eq : dist (g x) (g y) = (↑(Real.toNNReal (1 / k)) : ℝ) * dist x y := by
      calc
        dist (g x) (g y) = |g x - g y| := h1
        _ = |(1 / k) * (x - y)| := by rw [h2]
        _ = (1 / k) * |x - y| := h3
        _ = (1 / k) * dist x y := by rw [h4]
        _ = (↑(Real.toNNReal (1 / k)) : ℝ) * dist x y := by rw [hcoef]
    exact le_of_eq h_eq
  have h_mul1 : Real.toNNReal k * Real.toNNReal ε = Real.toNNReal (k * ε) := by
    have h1 : 0 ≤ k := by linarith
    rw [← Real.toNNReal_mul] <;> positivity
  have h_mul2 : Real.toNNReal (1 / k) * Real.toNNReal (k * ε) = Real.toNNReal ε := by
    have h1 : 0 ≤ 1 / k := by positivity
    have h2 : 0 ≤ k * ε := by positivity
    have h3 : Real.toNNReal (1 / k) * Real.toNNReal (k * ε) = Real.toNNReal ((1 / k) * (k * ε)) := by
      rw [← Real.toNNReal_mul] <;> positivity
    rw [h3]
    have h4 : (1 / k) * (k * ε) = ε := by
      field_simp [hk.ne'] <;> ring
    rw [h4]
  have h_forward : Metric.externalCoveringNumber (Real.toNNReal (k * ε)) (f '' S) ≤
      Metric.externalCoveringNumber (Real.toNNReal ε) S := by
    simp only [Metric.externalCoveringNumber, le_iInf_iff]
    intro C hC
    have hC' : Metric.IsCover (Real.toNNReal (k * ε)) (f '' S) (f '' C) := by
      have h := Metric.IsCover.image_lipschitz hC h_lip_f
      rwa [h_mul1] at h
    have h_le : Metric.externalCoveringNumber (Real.toNNReal (k * ε)) (f '' S) ≤
        (f '' C).encard := Metric.IsCover.externalCoveringNumber_le_encard hC'
    have h_encard : (f '' C).encard = C.encard := hf_inj.encard_image C
    rw [h_encard] at h_le
    exact h_le
  have h_backward : Metric.externalCoveringNumber (Real.toNNReal ε) S ≤
      Metric.externalCoveringNumber (Real.toNNReal (k * ε)) (f '' S) := by
    simp only [Metric.externalCoveringNumber, le_iInf_iff]
    intro C' hC'
    have hC'' : Metric.IsCover (Real.toNNReal ε) S (g '' C') := by
      have h : Metric.IsCover (Real.toNNReal (1 / k) * Real.toNNReal (k * ε))
          (g '' (f '' S)) (g '' C') :=
        Metric.IsCover.image_lipschitz hC' h_lip_g
      rw [h_mul2] at h
      rw [h_img_g_f] at h
      exact h
    have h_le : Metric.externalCoveringNumber (Real.toNNReal ε) S ≤ (g '' C').encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hC''
    have h_encard : (g '' C').encard = C'.encard := hg_inj.encard_image C'
    rw [h_encard] at h_le
    exact h_le
  exact le_antisymm h_forward h_backward

/--
Transport Alternative B back under independent dilation.
If `H'` is obtained from `H` by scaling F by `s_F` and G1/G2 by `s_G`,
then a dot-difference covering bound for `H'` implies one for `H`.

Requires `(s_F * s_G) * delta ≤ rho'` so that the scaled-down covering
radius `rho' / (s_F * s_G)` is still at least `delta`.
-/
lemma dot_diff_covering_transport
    {epsilon delta eta : ℝ}
    {s_F s_G : ℝ} (hsF : 1 ≤ s_F) (hsG : 1 ≤ s_G)
    {H H' : Finset (Point2 × Point2 × Point2)}
    (hH'_eq : H' = H.image (fun edge =>
        (s_F • edge.1, s_G • edge.2.1, s_G • edge.2.2)))
    {rho' center' radius' : ℝ}
    (hrho'_nonneg : 0 ≤ rho') (hradius'_pos : 0 < radius')
    (hcover : Kakeya.realRpowENN (2 * radius' / rho') (1 - epsilon) ≤
        (↑(Metric.externalCoveringNumber
          (Real.toNNReal rho')
          (wz1DotDifferenceSet H' ∩ Metric.closedBall center' radius')) : ENNReal))
    (hthin : Real.rpow delta (-eta) * rho' ≤ 2 * radius')
    (hrho'_delta : delta ≤ rho') (hrho'_one : rho' ≤ 1)
    (hdelta_pos : 0 < delta)
    (hscale : (s_F * s_G) * delta ≤ rho') :
    ∃ rho center radius : ℝ,
      delta ≤ rho ∧ rho ≤ 1 ∧ 0 < radius ∧
      Real.rpow delta (-eta) * rho ≤ 2 * radius ∧
      Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon) ≤
        (↑(Metric.externalCoveringNumber
          (Real.toNNReal rho)
          (wz1DotDifferenceSet H ∩ Metric.closedBall center radius)) : ENNReal) := by
  classical
  set k : ℝ := s_F * s_G with hk_def
  have hk_pos : 0 < k := by positivity
  have hk_one : 1 ≤ k := by
    calc
      1 ≤ s_F * s_G := by
        have h1 : 1 ≤ s_F := hsF
        have h2 : 1 ≤ s_G := hsG
        nlinarith
      _ = k := by rfl
  set rho : ℝ := rho' / k with hrho_def
  set center : ℝ := center' / k with hcenter_def
  set radius : ℝ := radius' / k with hradius_def
  have h_rho'_pos : 0 < rho' := by
    have h : 0 < k * delta := by positivity
    linarith [hscale]
  have h_rho_pos : 0 < rho := div_pos h_rho'_pos hk_pos
  have h_radius_pos : 0 < radius := by
    apply div_pos hradius'_pos hk_pos
  have h_delta_le_rho : delta ≤ rho := by
    rw [hrho_def]
    have h : (s_F * s_G) * delta ≤ rho' := hscale
    have h2 : delta ≤ rho' / k := by
      calc
        delta = ((s_F * s_G) * delta) / k := by
          field_simp [hk_def, hk_pos.ne'] <;> ring
        _ ≤ rho' / k := by gcongr
    exact h2
  have h_rho_le_one : rho ≤ 1 := by
    rw [hrho_def]
    have h : rho' / k ≤ rho' := by
      have h2 : rho' / k ≤ rho' / 1 := by gcongr <;> linarith
      simpa using h2
    exact h.trans hrho'_one
  have h_thin : Real.rpow delta (-eta) * rho ≤ 2 * radius := by
    rw [hrho_def, hradius_def]
    have h : Real.rpow delta (-eta) * (rho' / k) ≤ 2 * (radius' / k) := by
      calc
        Real.rpow delta (-eta) * (rho' / k)
          = (Real.rpow delta (-eta) * rho') / k := by ring
        _ ≤ (2 * radius') / k := by gcongr
        _ = 2 * (radius' / k) := by ring
    exact h
  have h_ratio : 2 * radius / rho = 2 * radius' / rho' := by
    rw [hradius_def, hrho_def]
    by_cases h : rho' = 0
    · rw [h]
      simp [div_zero]
    · field_simp [hk_pos.ne', h] <;> ring
  have h_set_eq : (wz1DotDifferenceSet H' ∩ Metric.closedBall center' radius') =
      (fun x : ℝ => k * x) '' (wz1DotDifferenceSet H ∩ Metric.closedBall center radius) := by
    have h1 : wz1DotDifferenceSet H' = (fun x : ℝ => k * x) '' wz1DotDifferenceSet H := by
      let f1 : (Point2 × Point2 × Point2) → ℝ :=
        fun h => inner ℝ h.1 (h.2.1 - h.2.2)
      let scale : (Point2 × Point2 × Point2) → (Point2 × Point2 × Point2) :=
        fun edge => (s_F • edge.1, s_G • edge.2.1, s_G • edge.2.2)
      have h_comm : ∀ edge, f1 (scale edge) = k * f1 edge := by
        intro edge
        simp only [f1, scale, k]
        have h2 : s_G • edge.2.1 - s_G • edge.2.2 = s_G • (edge.2.1 - edge.2.2) := by
          rw [smul_sub]
        rw [h2]
        have h3 : inner ℝ (s_F • edge.1) (s_G • (edge.2.1 - edge.2.2)) =
            (s_F * s_G) * inner ℝ edge.1 (edge.2.1 - edge.2.2) := by
          rw [inner_smul_left, inner_smul_right] <;> simp <;> ring
        exact h3
      have h_def1 : wz1DotDifferenceSet H' = f1 '' ↑H' := by
        simp [wz1DotDifferenceSet, f1, Finset.coe_image] <;> rfl
      have h_def2 : wz1DotDifferenceSet H = f1 '' ↑H := by
        simp [wz1DotDifferenceSet, f1, Finset.coe_image] <;> rfl
      rw [h_def1, h_def2]
      have hH : ↑H' = scale '' ↑H := by
        rw [hH'_eq]
        simp [Finset.coe_image] <;> rfl
      calc
        f1 '' ↑H'
          = f1 '' (scale '' ↑H) := by rw [hH]
        _ = (f1 ∘ scale) '' ↑H := by rw [Set.image_image] <;> rfl
        _ = ((fun x : ℝ => k * x) ∘ f1) '' ↑H := by
          have h_fun : f1 ∘ scale = (fun x : ℝ => k * x) ∘ f1 := by
            funext edge
            exact h_comm edge
          rw [h_fun]
        _ = (fun x : ℝ => k * x) '' (f1 '' ↑H) := by
          exact Set.image_comp (fun x : ℝ => k * x) f1 ↑H
    have h_inj : Function.Injective (fun x : ℝ => k * x) := by
      intro x y h
      have h6 : k * x = k * y := h
      have h7 : x = y := by
        apply mul_left_cancel₀ hk_pos.ne'
        exact h6
      exact h7
    have h3 : Metric.closedBall center' radius' =
        (fun x : ℝ => k * x) '' Metric.closedBall center radius := by
      ext y
      simp only [Set.mem_image, Metric.mem_closedBall]
      constructor
      · intro hy
        refine ⟨y / k, ?_, by field_simp [hk_pos.ne'] <;> ring⟩
        have h41 : dist (y / k) center = |y / k - center| := by simp [dist_eq_norm]
        have h42 : |y / k - center| = |y - center'| / k := by
          have h43 : center = center' / k := by simp [hcenter_def]
          rw [h43]
          have h44 : y / k - center' / k = (y - center') / k := by ring
          rw [h44, abs_div, abs_of_pos hk_pos] <;> ring
        rw [h41, h42]
        have h45 : |y - center'| / k ≤ radius' / k := by
          have h46 : |y - center'| = dist y center' := by simp [dist_eq_norm]
          rw [h46]
          exact div_le_div_of_nonneg_right hy (by positivity)
        have h47 : radius' / k = radius := by simp [hradius_def]
        rw [h47] at h45
        exact h45
      · rintro ⟨x, hx, rfl⟩
        have h51 : dist (k * x) center' = |k * x - center'| := by simp [dist_eq_norm]
        have h52 : |k * x - center'| = k * |x - center| := by
          have h53 : center = center' / k := by simp [hcenter_def]
          calc
            |k * x - center'|
              = |k * (x - center' / k)| := by
                have h : k * (x - center' / k) = k * x - center' := by
                  field_simp [hk_pos.ne'] <;> ring
                rw [h]
            _ = |k| * |x - center' / k| := by rw [abs_mul]
            _ = k * |x - center' / k| := by rw [abs_of_pos hk_pos] <;> ring
            _ = k * |x - center| := by rw [h53]
        rw [h51, h52]
        have h6 : k * |x - center| ≤ k * radius := by
          have h61 : |x - center| = dist x center := by simp [dist_eq_norm]
          rw [h61]
          exact mul_le_mul_of_nonneg_left hx (by positivity)
        have h7 : k * radius = radius' := by
          rw [hradius_def] <;> field_simp [hk_pos.ne'] <;> ring
        rw [h7] at h6
        exact h6
    rw [h1, h3]
    rw [Set.image_inter h_inj]
  have h4 : k * rho = rho' := by
      rw [hrho_def] <;> field_simp [hk_pos.ne'] <;> ring
  have h_cover_eq : Metric.externalCoveringNumber (Real.toNNReal rho')
      (wz1DotDifferenceSet H' ∩ Metric.closedBall center' radius') =
      Metric.externalCoveringNumber (Real.toNNReal rho)
        (wz1DotDifferenceSet H ∩ Metric.closedBall center radius) := by
    rw [h_set_eq]
    have h5 : Real.toNNReal rho' = Real.toNNReal (k * rho) := by rw [h4]
    rw [h5]
    exact real_covering_number_scaling hk_pos (by linarith)
  refine ⟨rho, center, radius, h_delta_le_rho, h_rho_le_one, h_radius_pos, h_thin, ?_⟩
  rw [h_ratio]
  rw [←h_cover_eq]
  exact hcover

/--
Variant of `dot_diff_covering_transport` that takes the dot-difference set
equality directly, allowing translations on the G components.
-/
lemma dot_diff_covering_transport'
    {delta epsilon eta : ℝ}
    {s_F s_G : ℝ} (hsF : 1 ≤ s_F) (hsG : 1 ≤ s_G)
    {H H' : Finset (Point2 × Point2 × Point2)}
    (h_dot_eq : wz1DotDifferenceSet H' = (fun x : ℝ => s_F * s_G * x) '' wz1DotDifferenceSet H)
    {rho' center' radius' : ℝ}
    (hrho'_nonneg : 0 ≤ rho') (hradius'_pos : 0 < radius')
    (hcover : Kakeya.realRpowENN (2 * radius' / rho') (1 - epsilon) ≤
        (↑(Metric.externalCoveringNumber (Real.toNNReal rho')
          (wz1DotDifferenceSet H' ∩ Metric.closedBall center' radius')) : ENNReal))
    (hthin : Real.rpow delta (-eta) * rho' ≤ 2 * radius')
    (hrho'_delta : delta ≤ rho') (hrho'_one : rho' ≤ 1)
    (hdelta_pos : 0 < delta)
    (hscale : (s_F * s_G) * delta ≤ rho') :
    ∃ rho center radius : ℝ,
      delta ≤ rho ∧ rho ≤ 1 ∧ 0 < radius ∧
      Real.rpow delta (-eta) * rho ≤ 2 * radius ∧
      Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon) ≤
        (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
          (wz1DotDifferenceSet H ∩ Metric.closedBall center radius)) : ENNReal) := by
  classical
  set k : ℝ := s_F * s_G with hk_def
  have hk_pos : 0 < k := by positivity
  have hk_one : 1 ≤ k := by
    calc
      1 ≤ s_F * s_G := by
        have h1 : 1 ≤ s_F := hsF
        have h2 : 1 ≤ s_G := hsG
        nlinarith
      _ = k := by rfl
  set rho : ℝ := rho' / k with hrho_def
  set center : ℝ := center' / k with hcenter_def
  set radius : ℝ := radius' / k with hradius_def
  have h_rho'_pos : 0 < rho' := by
    have h : 0 < k * delta := by positivity
    linarith [hscale]
  have h_rho_pos : 0 < rho := div_pos h_rho'_pos hk_pos
  have h_radius_pos : 0 < radius := by apply div_pos hradius'_pos hk_pos
  have h_delta_le_rho : delta ≤ rho := by
    rw [hrho_def]
    have h : (s_F * s_G) * delta ≤ rho' := hscale
    have h2 : delta ≤ rho' / k := by
      calc
        delta = ((s_F * s_G) * delta) / k := by
          field_simp [hk_def, hk_pos.ne'] <;> ring
        _ ≤ rho' / k := by gcongr
    exact h2
  have h_rho_le_one : rho ≤ 1 := by
    rw [hrho_def]
    have h : rho' / k ≤ rho' := by
      have h2 : rho' / k ≤ rho' / 1 := by gcongr <;> linarith
      simpa using h2
    exact h.trans hrho'_one
  have h_thin : Real.rpow delta (-eta) * rho ≤ 2 * radius := by
    rw [hrho_def, hradius_def]
    have h : Real.rpow delta (-eta) * (rho' / k) ≤ 2 * (radius' / k) := by
      calc
        Real.rpow delta (-eta) * (rho' / k)
          = (Real.rpow delta (-eta) * rho') / k := by ring
        _ ≤ (2 * radius') / k := by gcongr
        _ = 2 * (radius' / k) := by ring
    exact h
  have h_ratio : 2 * radius / rho = 2 * radius' / rho' := by
    rw [hradius_def, hrho_def]
    by_cases h : rho' = 0
    · rw [h] <;> simp [div_zero]
    · field_simp [hk_pos.ne', h] <;> ring
  have h_inj : Function.Injective (fun x : ℝ => k * x) := by
    intro x y h
    have h6 : k * x = k * y := h
    have h7 : x = y := by
      apply mul_left_cancel₀ hk_pos.ne'
      exact h6
    exact h7
  have h3 : Metric.closedBall center' radius' =
      (fun x : ℝ => k * x) '' Metric.closedBall center radius := by
    ext y
    simp only [Set.mem_image, Metric.mem_closedBall]
    constructor
    · intro hy
      refine ⟨y / k, ?_, by field_simp [hk_pos.ne'] <;> ring⟩
      have h41 : dist (y / k) center = |y / k - center| := by simp [dist_eq_norm]
      have h42 : |y / k - center| = |y - center'| / k := by
        have h43 : center = center' / k := by simp [hcenter_def]
        rw [h43]
        have h44 : y / k - center' / k = (y - center') / k := by ring
        rw [h44, abs_div, abs_of_pos hk_pos] <;> ring
      rw [h41, h42]
      have h45 : |y - center'| / k ≤ radius' / k := by
        have h46 : |y - center'| = dist y center' := by simp [dist_eq_norm]
        rw [h46]
        exact div_le_div_of_nonneg_right hy (by positivity)
      have h47 : radius' / k = radius := by simp [hradius_def]
      rw [h47] at h45
      exact h45
    · rintro ⟨x, hx, rfl⟩
      have h51 : dist (k * x) center' = |k * x - center'| := by simp [dist_eq_norm]
      have h52 : |k * x - center'| = k * |x - center| := by
        have h53 : center = center' / k := by simp [hcenter_def]
        calc
          |k * x - center'|
            = |k * (x - center' / k)| := by
              have h : k * (x - center' / k) = k * x - center' := by
                field_simp [hk_pos.ne'] <;> ring
              rw [h]
          _ = |k| * |x - center' / k| := by rw [abs_mul]
          _ = k * |x - center' / k| := by rw [abs_of_pos hk_pos] <;> ring
          _ = k * |x - center| := by rw [h53]
      rw [h51, h52]
      have h6 : k * |x - center| ≤ k * radius := by
        have h61 : |x - center| = dist x center := by simp [dist_eq_norm]
        rw [h61]
        exact mul_le_mul_of_nonneg_left hx (by positivity)
      have h7 : k * radius = radius' := by
        rw [hradius_def] <;> field_simp [hk_pos.ne'] <;> ring
      rw [h7] at h6
      exact h6
  have h_set_eq : (wz1DotDifferenceSet H' ∩ Metric.closedBall center' radius') =
      (fun x : ℝ => k * x) '' (wz1DotDifferenceSet H ∩ Metric.closedBall center radius) := by
    rw [h_dot_eq, h3]
    rw [Set.image_inter h_inj]
  have h4 : k * rho = rho' := by
    rw [hrho_def] <;> field_simp [hk_pos.ne'] <;> ring
  have h_cover_eq : Metric.externalCoveringNumber (Real.toNNReal rho')
      (wz1DotDifferenceSet H' ∩ Metric.closedBall center' radius') =
      Metric.externalCoveringNumber (Real.toNNReal rho)
        (wz1DotDifferenceSet H ∩ Metric.closedBall center radius) := by
    rw [h_set_eq]
    have h5 : Real.toNNReal rho' = Real.toNNReal (k * rho) := by rw [h4]
    rw [h5]
    exact real_covering_number_scaling hk_pos (by linarith)
  refine ⟨rho, center, radius, h_delta_le_rho, h_rho_le_one, h_radius_pos, h_thin, ?_⟩
  rw [h_ratio]
  rw [←h_cover_eq]
  exact hcover

/--
Dot-difference set scaling equality when G components are translated by `t_G`.
The translation cancels in the difference `g1 - g2`.
-/
lemma wz1_dot_diff_scaling_translated
    {s_F s_G : ℝ} (t_G : Point2)
    {H_cell H_scaled : Finset (Point2 × Point2 × Point2)}
    (hH_scaled_eq : H_scaled = H_cell.image (fun edge =>
        (s_F • edge.1, s_G • edge.2.1 + t_G, s_G • edge.2.2 + t_G))) :
    wz1DotDifferenceSet H_scaled =
      (fun x : ℝ => s_F * s_G * x) '' wz1DotDifferenceSet H_cell := by
  classical
  let f1 : (Point2 × Point2 × Point2) → ℝ :=
    fun h => inner ℝ h.1 (h.2.1 - h.2.2)
  let scale_trans : (Point2 × Point2 × Point2) → (Point2 × Point2 × Point2) :=
    fun edge => (s_F • edge.1, s_G • edge.2.1 + t_G, s_G • edge.2.2 + t_G)
  set k : ℝ := s_F * s_G with hk_def
  have h_comm : ∀ edge, f1 (scale_trans edge) = k * f1 edge := by
    intro edge
    simp only [f1, scale_trans, k]
    have h2 : (s_G • edge.2.1 + t_G) - (s_G • edge.2.2 + t_G) = s_G • (edge.2.1 - edge.2.2) := by
      simp [smul_sub] <;> abel
    rw [h2]
    have h3 : inner ℝ (s_F • edge.1) (s_G • (edge.2.1 - edge.2.2)) =
        (s_F * s_G) * inner ℝ edge.1 (edge.2.1 - edge.2.2) := by
      rw [inner_smul_left, inner_smul_right] <;> simp <;> ring
    exact h3
  have h_def1 : wz1DotDifferenceSet H_scaled = f1 '' ↑H_scaled := by
    simp [wz1DotDifferenceSet, f1, Finset.coe_image] <;> rfl
  have h_def2 : wz1DotDifferenceSet H_cell = f1 '' ↑H_cell := by
    simp [wz1DotDifferenceSet, f1, Finset.coe_image] <;> rfl
  rw [h_def1, h_def2]
  have hH : ↑H_scaled = scale_trans '' ↑H_cell := by
    rw [hH_scaled_eq]
    simp [Finset.coe_image] <;> rfl
  calc
    f1 '' ↑H_scaled
      = f1 '' (scale_trans '' ↑H_cell) := by rw [hH]
    _ = (f1 ∘ scale_trans) '' ↑H_cell := by rw [Set.image_image] <;> rfl
    _ = ((fun x : ℝ => k * x) ∘ f1) '' ↑H_cell := by
      have h_fun : f1 ∘ scale_trans = (fun x : ℝ => k * x) ∘ f1 := by
        funext edge
        exact h_comm edge
      rw [h_fun]
    _ = (fun x : ℝ => k * x) '' (f1 '' ↑H_cell) := by
      exact Set.image_comp (fun x : ℝ => k * x) f1 ↑H_cell

/-! ## Alternative B transport under affine triple -/

/--
Transport Alternative B back under the affine triple transport.

Since `wz1AffineTriple` preserves dot-differences exactly (contragredient on F,
affine on G1/G2), the dot-difference set is unchanged and the same
`rho, center, radius` witness works for the original hypergraph.
-/
lemma transport_alternative_B_affine
    {delta epsilon eta : ℝ}
    {H : Finset (Point2 × Point2 × Point2)}
    {linear : Point2 ≃ₗ[ℝ] Point2} {translation : Point2}
    {H' : Finset (Point2 × Point2 × Point2)}
    (hH' : H' = H.image (wz1AffineTriple linear translation))
    (hB_normalized :
      ∃ rho center radius : ℝ,
        delta ≤ rho ∧ rho ≤ 1 ∧ 0 < radius ∧
        Real.rpow delta (-eta) * rho ≤ 2 * radius ∧
        Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon) ≤
          (↑(Metric.externalCoveringNumber
            (Real.toNNReal rho)
            (wz1DotDifferenceSet H' ∩ Metric.closedBall center radius)) : ENNReal)) :
    ∃ rho center radius : ℝ,
      delta ≤ rho ∧ rho ≤ 1 ∧ 0 < radius ∧
      Real.rpow delta (-eta) * rho ≤ 2 * radius ∧
      Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon) ≤
        (↑(Metric.externalCoveringNumber
          (Real.toNNReal rho)
          (wz1DotDifferenceSet H ∩ Metric.closedBall center radius)) : ENNReal) := by
  classical
  let f : (Point2 × Point2 × Point2) → ℝ :=
    fun h => inner ℝ h.1 (h.2.1 - h.2.2)
  have h_dot : ∀ edge, f (wz1AffineTriple linear translation edge) = f edge := by
    intro edge
    dsimp only [f, wz1AffineTriple, wz1ContragredientPoint, wz1AffineEndpoint]
    have h_sub :
      (linear edge.2.1 + translation) - (linear edge.2.2 + translation) =
      linear (edge.2.1 - edge.2.2) := by
      simp [map_sub]
    rw [h_sub]
    have h_adj :
      inner ℝ (linear.symm.toLinearMap.adjoint edge.1)
        (linear (edge.2.1 - edge.2.2)) =
      inner ℝ edge.1
        (linear.symm.toLinearMap (linear (edge.2.1 - edge.2.2))) :=
      LinearMap.adjoint_inner_left linear.symm.toLinearMap
        (linear (edge.2.1 - edge.2.2)) edge.1
    rw [h_adj]
    have h_inv :
      linear.symm.toLinearMap (linear (edge.2.1 - edge.2.2)) =
      edge.2.1 - edge.2.2 :=
      linear.left_inv (edge.2.1 - edge.2.2)
    rw [h_inv]
  have h_image_eq : (H.image (wz1AffineTriple linear translation)).image f = H.image f := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    exact h_dot x
  have h_set_eq : wz1DotDifferenceSet H' = wz1DotDifferenceSet H := by
    rw [hH']
    simpa [wz1DotDifferenceSet] using
      congr_arg (fun s : Finset ℝ => (↑s : Set ℝ)) h_image_eq
  rcases hB_normalized with ⟨rho, center, radius, h1, h2, h3, h4, h5⟩
  refine ⟨rho, center, radius, h1, h2, h3, h4, ?_⟩
  have h_inter_eq : wz1DotDifferenceSet H' ∩ Metric.closedBall center radius =
      wz1DotDifferenceSet H ∩ Metric.closedBall center radius := by
    rw [h_set_eq]
  rw [h_inter_eq] at h5
  exact h5

/-! ## Packing bound and Frostman scaling at fixed delta -/

/--
At most 25 pairwise `d`-separated points can lie in a closed ball of radius `r < d`
in `Point2`.  Scale by `2/d` and apply Besicovitch's covering theorem.
-/
lemma separated_ball_card_le_25
    {B : Finset Point2} {x : Point2} {r d : ℝ}
    (hr_pos : 0 ≤ r) (hd_pos : 0 < d) (h_r_lt_d : r < d)
    (h_in : ∀ y ∈ B, dist y x ≤ r)
    (h_sep : ∀ y ∈ B, ∀ z ∈ B, y ≠ z → d ≤ dist y z) :
    B.card ≤ 25 := by
  let scale : ℝ := 2 / d
  have hscale_pos : 0 < scale := by positivity
  let f : Point2 → Point2 := fun y => scale • (y - x)
  let B' : Finset Point2 := B.image f
  have h_inj : Function.Injective f := by
    intro y z h
    have h' : scale • (y - x) = scale • (z - x) := h
    have h_scale_ne_zero : scale ≠ 0 := by positivity
    have h'' : y - x = z - x := by
      have h9 : scale⁻¹ • (scale • (y - x)) = scale⁻¹ • (scale • (z - x)) := by rw [h']
      simpa [h_scale_ne_zero, smul_smul] using h9
    simpa using h''
  have h_card : B'.card = B.card := by
    rw [Finset.card_image_of_injective _ h_inj]
  have h1 : ∀ c ∈ B', ‖c‖ ≤ 2 := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨y, hy, rfl⟩
    have h_dist : dist y x ≤ r := h_in y hy
    have h_norm : ‖f y‖ = scale * dist y x := by
      simp [f, norm_smul, dist_eq_norm, abs_of_pos hscale_pos] <;> ring
    rw [h_norm]
    have h_bound : scale * dist y x ≤ scale * r := by gcongr
    have h9 : scale * r < 2 := by
      have h10 : scale * r = 2 * r / d := by simp [scale] <;> ring
      rw [h10]
      have h11 : 2 * r / d < 2 := by
        have h12 : 2 * r < 2 * d := by gcongr
        have h13 : 0 < d := hd_pos
        calc 2 * r / d < 2 * d / d := by gcongr
             _ = 2 := by field_simp [h13.ne'] <;> ring
      exact h11
    linarith
  have h2 : ∀ c ∈ B', ∀ e ∈ B', c ≠ e → 1 ≤ ‖c - e‖ := by
    intro c hc e he hne
    rcases Finset.mem_image.mp hc with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.mp he with ⟨z, hz, rfl⟩
    have hyne : y ≠ z := by intro h; apply hne; simp [h]
    have h_sep' : d ≤ dist y z := h_sep y hy z hz hyne
    have h_norm : ‖f y - f z‖ = scale * dist y z := by
      have h_eq : f y - f z = scale • (y - z) := by simp [f, smul_sub] <;> ring
      rw [h_eq]
      simp [norm_smul, dist_eq_norm, abs_of_pos hscale_pos] <;> ring
    rw [h_norm]
    have h5 : scale * dist y z ≥ 1 := by
      have h7 : scale * dist y z ≥ scale * d := by gcongr
      have h8 : scale * d = 2 := by simp [scale] <;> field_simp [hd_pos.ne'] <;> ring
      rw [h8] at h7; linarith
    exact h5
  have h_bound : B'.card ≤ 5 ^ Module.finrank ℝ Point2 :=
    Besicovitch.card_le_of_separated B' h1 h2
  have h_dim : Module.finrank ℝ Point2 = 2 := by
    exact finrank_euclideanSpace_fin
  rw [h_dim] at h_bound
  have h_final : B'.card ≤ 25 := by norm_num at h_bound ⊢ <;> exact h_bound
  rw [h_card] at h_final
  exact h_final

/--
Scale a Frostman set by `s ≥ 1` while preserving Frostman at the original scale `δ`.

For `r ≥ sδ`, use the standard scaling lemma (constant `C/s`).
For `δ ≤ r < sδ`, use the packing bound: the scaled set is `sδ`-separated,
so any ball of radius `r < sδ` contains at most 25 points.
-/
lemma is_frostman_scaling_preserve_delta
    {A : DiscreteSet 2} {δ : ℝ} {C C' : ENNReal} {s : ℝ}
    (hs : 1 ≤ s) (hδ_pos : 0 < δ)
    (hA_sep : A.IsDeltaSeparated δ)
    (hA_frost : DiscreteSet.IsFrostman A δ 1 C)
    (h_card_lower : (A.card : ENNReal) ≥ 25 / (C' * ENNReal.ofReal δ))
    (h_constant : C / Kakeya.realRpowENN s 1 ≤ C')
    (hC'_ne_zero : C' ≠ 0) (hC'_ne_top : C' ≠ ⊤) :
    DiscreteSet.IsFrostman (A.image (fun p => s • p)) δ 1 C' := by
  let B : DiscreteSet 2 := A.image (fun p : Point2 => s • p)
  have hspos : 0 < s := by linarith
  have hB_sep : DiscreteSet.IsDeltaSeparated B (s * δ) :=
    is_delta_separated_scaling hspos hA_sep
  have h_card_eq : B.card = A.card := by
    apply Finset.card_image_of_injective
    intro x y h
    have h9 : s ≠ 0 := hspos.ne'
    have h10 : s⁻¹ • (s • x) = s⁻¹ • (s • y) := congr_arg (fun v : Point2 => s⁻¹ • v) h
    simpa [h9, smul_smul] using h10
  have h_enncard_eq : B.enncard = (A.card : ENNReal) := by
    simp [DiscreteSet.enncard, h_card_eq]
  intro x r hδr hr1
  by_cases h_case : s * δ ≤ r
  · -- Case r ≥ sδ: use standard Frostman scaling
    have h_scaled : DiscreteSet.IsFrostman B (s * δ) 1 (C / Kakeya.realRpowENN s 1) :=
      is_frostman_scaling hs (by norm_num) hδ_pos.le hA_frost
    have h_main := h_scaled x r h_case hr1
    have h_rpow_s : Kakeya.realRpowENN s 1 = ENNReal.ofReal s := by
      simp [Kakeya.realRpowENN] <;> norm_cast
    rw [h_rpow_s] at h_main
    rw [h_rpow_s] at h_constant
    calc
      B.ballCount x r
        ≤ (C / ENNReal.ofReal s) * Kakeya.realRpowENN r 1 * B.enncard := h_main
      _ ≤ C' * Kakeya.realRpowENN r 1 * B.enncard := by gcongr
  · -- Case δ ≤ r < sδ: use packing bound
    have h_r_lt : r < s * δ := by linarith
    let S : Finset Point2 := B.filter fun y => dist y x ≤ r
    have hS_in : ∀ y ∈ S, dist y x ≤ r := by
      intro y hy; exact (Finset.mem_filter.mp hy).2
    have hS_sep : ∀ y ∈ S, ∀ z ∈ S, y ≠ z → s * δ ≤ dist y z := by
      intro y hy z hz hne
      exact hB_sep (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hz).1 hne
    have h_pack : S.card ≤ 25 :=
      separated_ball_card_le_25 (by linarith) (by positivity) h_r_lt hS_in hS_sep
    have h_ballCount_eq : B.ballCount x r = (S.card : ENNReal) := by rfl
    rw [h_ballCount_eq]
    have h_ofReal_ne_zero : ENNReal.ofReal δ ≠ 0 := by
      have h10 : 0 < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ_pos
      exact h10.ne'
    have h_a_ne_zero : C' * ENNReal.ofReal δ ≠ 0 :=
      mul_ne_zero hC'_ne_zero h_ofReal_ne_zero
    have h_a_ne_top : C' * ENNReal.ofReal δ ≠ ⊤ :=
      ENNReal.mul_ne_top hC'_ne_top ENNReal.ofReal_ne_top
    have h25 : (25 : ENNReal) ≤ C' * ENNReal.ofReal δ * B.enncard := by
      rw [h_enncard_eq]
      have h6 : (25 : ENNReal) = (C' * ENNReal.ofReal δ) * ((25 : ENNReal) / (C' * ENNReal.ofReal δ)) := by
        rw [ENNReal.mul_div_cancel h_a_ne_zero h_a_ne_top] <;> ring
      rw [h6]
      gcongr
    have h8 : ENNReal.ofReal δ ≤ ENNReal.ofReal r := by
      apply ENNReal.ofReal_le_ofReal <;> linarith
    have h9 : C' * ENNReal.ofReal δ * B.enncard ≤ C' * ENNReal.ofReal r * B.enncard := by gcongr
    have h10 : (25 : ENNReal) ≤ C' * ENNReal.ofReal r * B.enncard := h25.trans h9
    have h_rpow : Kakeya.realRpowENN r 1 = ENNReal.ofReal r := by
      simp [Kakeya.realRpowENN] <;> norm_cast
    have h11 : (S.card : ENNReal) ≤ (25 : ENNReal) := by exact_mod_cast h_pack
    have h_goal : (S.card : ENNReal) ≤ C' * Kakeya.realRpowENN r 1 * B.enncard := by
      rw [h_rpow]
      exact h11.trans h10
    exact h_goal

/--
Transport a dot-difference covering bound from a refined subgraph `H_ref` back to
the original graph `H`, via the scaled intermediate graph `H_scaled`.

The chain is `H_ref ⊆ H_scaled = H_cell.image(scale) ⊆ H.image(scale)` (since
`H_cell ⊆ H`).  We first boost the bound from `H_ref` to `H_scaled` by subset
monotonicity, apply `dot_diff_covering_transport` to descend from `H_scaled` to
`H_cell`, and finally boost from `H_cell` to `H`.
-/
lemma dot_diff_covering_transport_subset
    {delta epsilon eta : ℝ}
    {s_F s_G : ℝ} (hsF : 1 ≤ s_F) (hsG : 1 ≤ s_G)
    {H H_cell H_scaled H_ref : Finset (Point2 × Point2 × Point2)}
    (hH_scaled_eq : H_scaled = H_cell.image (fun edge =>
        (s_F • edge.1, s_G • edge.2.1, s_G • edge.2.2)))
    (hH_ref_subset : H_ref ⊆ H_scaled)
    (hH_cell_subset : H_cell ⊆ H)
    {rho' center' radius' : ℝ}
    (hrho'_nonneg : 0 ≤ rho') (hradius'_pos : 0 < radius')
    (hcover : Kakeya.realRpowENN (2 * radius' / rho') (1 - epsilon) ≤
        (↑(Metric.externalCoveringNumber (Real.toNNReal rho')
          (wz1DotDifferenceSet H_ref ∩ Metric.closedBall center' radius')) : ENNReal))
    (hthin : Real.rpow delta (-eta) * rho' ≤ 2 * radius')
    (hrho'_delta : delta ≤ rho') (hrho'_one : rho' ≤ 1)
    (hdelta_pos : 0 < delta)
    (hscale : (s_F * s_G) * delta ≤ rho') :
    ∃ rho center radius : ℝ,
      delta ≤ rho ∧ rho ≤ 1 ∧ 0 < radius ∧
      Real.rpow delta (-eta) * rho ≤ 2 * radius ∧
      Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon) ≤
        (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
          (wz1DotDifferenceSet H ∩ Metric.closedBall center radius)) : ENNReal) := by
  have h_dot_mono1 : wz1DotDifferenceSet H_ref ∩ Metric.closedBall center' radius' ⊆
      wz1DotDifferenceSet H_scaled ∩ Metric.closedBall center' radius' := by
    have h1 : wz1DotDifferenceSet H_ref ⊆ wz1DotDifferenceSet H_scaled := by
      intro x hx
      simp only [wz1DotDifferenceSet] at hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      exact Finset.mem_image.mpr ⟨y, hH_ref_subset hy, rfl⟩
    exact Set.inter_subset_inter h1 (Set.Subset.refl _)
  have h_cover1 : Kakeya.realRpowENN (2 * radius' / rho') (1 - epsilon) ≤
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho')
        (wz1DotDifferenceSet H_scaled ∩ Metric.closedBall center' radius')) : ENNReal) := by
    have h_mono : (Metric.externalCoveringNumber (Real.toNNReal rho')
        (wz1DotDifferenceSet H_ref ∩ Metric.closedBall center' radius') : ENNReal) ≤
        (Metric.externalCoveringNumber (Real.toNNReal rho')
          (wz1DotDifferenceSet H_scaled ∩ Metric.closedBall center' radius') : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h_dot_mono1
    exact hcover.trans h_mono
  rcases dot_diff_covering_transport hsF hsG hH_scaled_eq hrho'_nonneg hradius'_pos h_cover1 hthin hrho'_delta hrho'_one hdelta_pos hscale
    with ⟨rho, center, radius, hrho1, hrho2, hradius_pos, hthin2, hcover2⟩
  have h_dot_mono2 : wz1DotDifferenceSet H_cell ∩ Metric.closedBall center radius ⊆
      wz1DotDifferenceSet H ∩ Metric.closedBall center radius := by
    have h1 : wz1DotDifferenceSet H_cell ⊆ wz1DotDifferenceSet H := by
      intro x hx
      simp only [wz1DotDifferenceSet] at hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      exact Finset.mem_image.mpr ⟨y, hH_cell_subset hy, rfl⟩
    exact Set.inter_subset_inter h1 (Set.Subset.refl _)
  have h_cover3 : Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon) ≤
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
        (wz1DotDifferenceSet H ∩ Metric.closedBall center radius)) : ENNReal) := by
    have h_mono : (Metric.externalCoveringNumber (Real.toNNReal rho)
        (wz1DotDifferenceSet H_cell ∩ Metric.closedBall center radius) : ENNReal) ≤
        (Metric.externalCoveringNumber (Real.toNNReal rho)
          (wz1DotDifferenceSet H ∩ Metric.closedBall center radius) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h_dot_mono2
    exact hcover2.trans h_mono
  exact ⟨rho, center, radius, hrho1, hrho2, hradius_pos, hthin2, h_cover3⟩

/--
Like `dot_diff_covering_transport_subset`, but the scaled hypergraph includes a
translation `t_G` on the G components.  The translation cancels in the dot
difference `g₁ - g₂`, so the same covering transport goes through.
-/
lemma dot_diff_covering_transport_subset_translated
    {delta epsilon eta : ℝ}
    {s_F s_G : ℝ} (hsF : 1 ≤ s_F) (hsG : 1 ≤ s_G)
    {t_G : Point2}
    {H H_cell H_scaled H_ref : Finset (Point2 × Point2 × Point2)}
    (hH_scaled_eq : H_scaled = H_cell.image (fun edge =>
        (s_F • edge.1, s_G • edge.2.1 + t_G, s_G • edge.2.2 + t_G)))
    (hH_ref_subset : H_ref ⊆ H_scaled)
    (hH_cell_subset : H_cell ⊆ H)
    {rho' center' radius' : ℝ}
    (hrho'_nonneg : 0 ≤ rho') (hradius'_pos : 0 < radius')
    (hcover : Kakeya.realRpowENN (2 * radius' / rho') (1 - epsilon) ≤
        (↑(Metric.externalCoveringNumber (Real.toNNReal rho')
          (wz1DotDifferenceSet H_ref ∩ Metric.closedBall center' radius')) : ENNReal))
    (hthin : Real.rpow delta (-eta) * rho' ≤ 2 * radius')
    (hrho'_delta : delta ≤ rho') (hrho'_one : rho' ≤ 1)
    (hdelta_pos : 0 < delta)
    (hscale : (s_F * s_G) * delta ≤ rho') :
    ∃ rho center radius : ℝ,
      delta ≤ rho ∧ rho ≤ 1 ∧ 0 < radius ∧
      Real.rpow delta (-eta) * rho ≤ 2 * radius ∧
      Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon) ≤
        (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
          (wz1DotDifferenceSet H ∩ Metric.closedBall center radius)) : ENNReal) := by
  have h_dot_scaled : wz1DotDifferenceSet H_scaled =
      (fun x : ℝ => s_F * s_G * x) '' wz1DotDifferenceSet H_cell :=
    wz1_dot_diff_scaling_translated t_G hH_scaled_eq
  have h_dot_mono1 : wz1DotDifferenceSet H_ref ∩ Metric.closedBall center' radius' ⊆
      wz1DotDifferenceSet H_scaled ∩ Metric.closedBall center' radius' := by
    have h1 : wz1DotDifferenceSet H_ref ⊆ wz1DotDifferenceSet H_scaled := by
      intro x hx
      simp only [wz1DotDifferenceSet] at hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      exact Finset.mem_image.mpr ⟨y, hH_ref_subset hy, rfl⟩
    exact Set.inter_subset_inter h1 (Set.Subset.refl _)
  have h_cover1 : Kakeya.realRpowENN (2 * radius' / rho') (1 - epsilon) ≤
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho')
        (wz1DotDifferenceSet H_scaled ∩ Metric.closedBall center' radius')) : ENNReal) := by
    have h_mono : (Metric.externalCoveringNumber (Real.toNNReal rho')
        (wz1DotDifferenceSet H_ref ∩ Metric.closedBall center' radius') : ENNReal) ≤
        (Metric.externalCoveringNumber (Real.toNNReal rho')
          (wz1DotDifferenceSet H_scaled ∩ Metric.closedBall center' radius') : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h_dot_mono1
    exact hcover.trans h_mono
  rcases dot_diff_covering_transport' hsF hsG h_dot_scaled
      hrho'_nonneg hradius'_pos h_cover1 hthin hrho'_delta hrho'_one hdelta_pos hscale
    with ⟨rho, center, radius, hrho1, hrho2, hradius_pos, hthin2, hcover2⟩
  have h_dot_mono2 : wz1DotDifferenceSet H_cell ∩ Metric.closedBall center radius ⊆
      wz1DotDifferenceSet H ∩ Metric.closedBall center radius := by
    have h1 : wz1DotDifferenceSet H_cell ⊆ wz1DotDifferenceSet H := by
      intro x hx
      simp only [wz1DotDifferenceSet] at hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      exact Finset.mem_image.mpr ⟨y, hH_cell_subset hy, rfl⟩
    exact Set.inter_subset_inter h1 (Set.Subset.refl _)
  have h_cover3 : Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon) ≤
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
        (wz1DotDifferenceSet H ∩ Metric.closedBall center radius)) : ENNReal) := by
    have h_mono : (Metric.externalCoveringNumber (Real.toNNReal rho)
        (wz1DotDifferenceSet H_cell ∩ Metric.closedBall center radius) : ENNReal) ≤
        (Metric.externalCoveringNumber (Real.toNNReal rho)
          (wz1DotDifferenceSet H ∩ Metric.closedBall center radius) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h_dot_mono2
    exact hcover2.trans h_mono
  exact ⟨rho, center, radius, hrho1, hrho2, hradius_pos, hthin2, h_cover3⟩

end Kakeya.Assouad
