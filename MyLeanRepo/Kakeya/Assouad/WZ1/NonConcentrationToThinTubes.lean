import MyLeanRepo.Kakeya.Assouad.WZ1.DiscreteThinTubes

/-!
# Line non-concentration implies discrete thin tubes

If G₂ satisfies a uniform strip (line) non-concentration bound for every
width r > 0, then for any G₁ the pair (G₁, G₂) satisfies the discrete
thin-tubes condition with no exceptional pairs (c = 0, E = G₁ ×ˢ G₂).
-/

noncomputable section

open MeasureTheory Set Metric

open scoped ENNReal NNReal

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
A one-dimensional subspace of R² has a unit normal vector.
-/
lemma exists_unit_normal_of_finrank_one
    {V : Submodule ℝ Point2} (hfin : Module.finrank ℝ V = 1) :
    ∃ (n : Point2), ‖n‖ = 1 ∧ ∀ v ∈ V, inner ℝ v n = 0 := by
  have h_rank : Module.finrank ℝ V + Module.finrank ℝ Vᗮ = Module.finrank ℝ Point2 :=
    Submodule.finrank_add_finrank_orthogonal V
  have h_top : Module.finrank ℝ Point2 = 2 := by simp
  have h_orth_rank : Module.finrank ℝ Vᗮ = 1 := by
    rw [h_top] at h_rank
    rw [hfin] at h_rank
    omega
  have h_orth_pos : 0 < Module.finrank ℝ Vᗮ := by
    rw [h_orth_rank] <;> norm_num
  have h_exists : ∃ (n : Point2), n ∈ Vᗮ ∧ n ≠ 0 := by
    have h' : ∃ (x : Vᗮ), x ≠ 0 := Module.finrank_pos_iff_exists_ne_zero.mp h_orth_pos
    rcases h' with ⟨x, hx⟩
    refine ⟨(x : Point2), x.prop, ?_⟩
    exact_mod_cast hx
  rcases h_exists with ⟨n, hnV, hn0⟩
  let n' : Point2 := (‖n‖⁻¹ : ℝ) • n
  have h_n'_norm : ‖n'‖ = 1 := by
    have h1 : ‖n'‖ = |(‖n‖⁻¹ : ℝ)| * ‖n‖ := by exact norm_smul _ _
    have h2 : 0 < ‖n‖ := norm_pos_iff.mpr hn0
    have h3 : |(‖n‖⁻¹ : ℝ)| = ‖n‖⁻¹ := by rw [abs_of_nonneg] <;> positivity
    rw [h1, h3]
    field_simp [h2.ne'] <;> norm_num
  have h_n'_orth : ∀ v ∈ V, inner ℝ v n' = 0 := by
    intro v hv
    have h1 : ∀ u ∈ V, inner ℝ u n = 0 := (Submodule.mem_orthogonal V n).mp hnV
    have h2 : inner ℝ v n = 0 := h1 v hv
    have h3 : inner ℝ v n' = (‖n‖⁻¹ : ℝ) * inner ℝ v n := by
      simp [n', inner_smul_right]
    rw [h3, h2] <;> ring
  exact ⟨n', h_n'_norm, h_n'_orth⟩

/--
For a line ℓ with unit normal n and base point p ∈ ℓ, the thickening
is contained in the closed strip `{y | |inner ℝ y n - inner ℝ p n| ≤ r}`.
-/
lemma thickening_subset_strip
    {ℓ : AffineSubspace ℝ Point2} (hfin : Module.finrank ℝ ℓ.direction = 1)
    (n : Point2) (hn : ‖n‖ = 1) (hn_orth : ∀ v ∈ ℓ.direction, inner ℝ v n = 0)
    (p : Point2) (hp : p ∈ ℓ) (r : ℝ) (hr : 0 < r) :
    Metric.thickening r (ℓ : Set Point2) ⊆
      {y : Point2 | |inner ℝ y n - inner ℝ p n| ≤ r} := by
  intro y hy
  have h_exists : ∃ (q : Point2), q ∈ (ℓ : Set Point2) ∧ dist y q < r := by
    simpa [Metric.mem_thickening_iff] using hy
  rcases h_exists with ⟨q, hq, hdist⟩
  have h1 : q - p ∈ ℓ.direction :=
    AffineSubspace.vsub_mem_direction hq hp
  have h2 : inner ℝ (q - p) n = 0 := hn_orth (q - p) h1
  have h4 : inner ℝ (y - p) n = inner ℝ (y - q) n + inner ℝ (q - p) n := by
    have h5 : y - p = (y - q) + (q - p) := by abel
    rw [h5]
    rw [inner_add_left]
  have h3 : inner ℝ y n - inner ℝ p n = inner ℝ (y - p) n := by
    rw [←inner_sub_left]
  have h6 : inner ℝ y n - inner ℝ p n = inner ℝ (y - q) n := by
    rw [h3, h4, h2, add_zero]
  have h7 : |inner ℝ (y - q) n| ≤ ‖y - q‖ * ‖n‖ := abs_real_inner_le_norm (y - q) n
  have h8 : ‖y - q‖ = dist y q := by rfl
  rw [h8, hn] at h7
  have h9 : |inner ℝ (y - q) n| ≤ dist y q := by simpa using h7
  have h10 : |inner ℝ y n - inner ℝ p n| ≤ r := by
    rw [h6]
    linarith
  exact h10

/--
For a line ℓ with unit normal n and base point base ∈ ℓ, the open strip
`{p | |inner ℝ (p - base) n| < R}` is contained in the R-thickening of ℓ.

Proof: project `p - base` onto the direction of ℓ. Since `ℓ.direction` has
finrank 1 and equals the orthogonal complement of `ℝ ∙ n`, the tangential
component lies in `ℓ.direction`, giving a point `q ∈ ℓ` with `dist p q < R`.
-/
lemma strip_subset_thickening
    {ℓ : AffineSubspace ℝ Point2}
    (hfin : Module.finrank ℝ ℓ.direction = 1)
    (n : Point2) (hn : ‖n‖ = 1)
    (hn_orth : ∀ v ∈ ℓ.direction, inner ℝ v n = 0)
    (base : Point2) (hbase : base ∈ (ℓ : Set Point2))
    (R : ℝ) (_hR : 0 < R) :
    {p : Point2 | |inner ℝ (p - base) n| < R} ⊆
    Metric.thickening R (ℓ : Set Point2) := by
  let V := ℓ.direction
  let W := (Submodule.span ℝ {n})ᗮ
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at hn
    simp at hn
  have hV_sub_W : V ≤ W := by
    intro v hv
    have h1 : ∀ (u : Point2), u ∈ (Submodule.span ℝ {n}) → inner ℝ u v = 0 := by
      intro u hu
      rcases Submodule.mem_span_singleton.mp hu with ⟨c, rfl⟩
      have h2 : inner ℝ (c • n) v = c * inner ℝ n v := by
        simp [inner_smul_left]
      rw [h2]
      have h3 : inner ℝ n v = inner ℝ v n := (real_inner_comm n v).symm
      rw [h3, hn_orth v hv]
      ring
    exact (Submodule.mem_orthogonal _ _).mpr h1
  have h_rank_span : Module.finrank ℝ (Submodule.span ℝ {n}) = 1 :=
    finrank_span_singleton hn0
  have h_rank_sum : Module.finrank ℝ (Submodule.span ℝ {n}) + Module.finrank ℝ W = Module.finrank ℝ Point2 :=
    Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ {n})
  have h_rank_Point2 : Module.finrank ℝ Point2 = 2 := by simp
  have h_rank_W : Module.finrank ℝ W = 1 := by
    rw [h_rank_span, h_rank_Point2] at h_rank_sum
    omega
  have hV_eq_W : V = W := Submodule.eq_of_le_of_finrank_eq hV_sub_W
    (by rw [hfin, h_rank_W])
  intro p hp
  have h_strip : |inner ℝ (p - base) n| < R := hp
  set c : ℝ := inner ℝ (p - base) n with hc_def
  set w : Point2 := c • n with hw_def
  set u : Point2 := (p - base) - w with hu_def
  have h_inner_u_n : inner ℝ u n = 0 := by
    have h_eq1 : inner ℝ u n = inner ℝ (p - base) n - inner ℝ w n := by
      rw [hu_def, inner_sub_left]
    rw [h_eq1]
    have h_eq2 : inner ℝ w n = c * inner ℝ n n := by
      rw [hw_def]
      simp [inner_smul_left]
    rw [h_eq2]
    have h_eq3 : inner ℝ n n = ‖n‖ ^ 2 := real_inner_self_eq_norm_sq n
    rw [h_eq3, hn]
    have h4 : inner ℝ (p - base) n = c := by exact hc_def.symm
    rw [h4]
    norm_num
  have h_u_in_W : u ∈ W := by
    have h1 : ∀ (v : Point2), v ∈ (Submodule.span ℝ {n}) → inner ℝ v u = 0 := by
      intro v hv
      rcases Submodule.mem_span_singleton.mp hv with ⟨d, rfl⟩
      have h2 : inner ℝ (d • n) u = d * inner ℝ n u := by
        simp [inner_smul_left]
      rw [h2]
      have h3 : inner ℝ n u = inner ℝ u n := (real_inner_comm n u).symm
      rw [h3, h_inner_u_n]
      ring
    exact (Submodule.mem_orthogonal _ _).mpr h1
  have h_u_in_V : u ∈ V := by
    rw [hV_eq_W]
    exact h_u_in_W
  let q : Point2 := base + u
  have hq_in_ell : q ∈ (ℓ : Set Point2) := by
    have h : u +ᵥ base ∈ (ℓ : Set Point2) :=
      (AffineSubspace.vadd_mem_iff_mem_direction u hbase).mpr h_u_in_V
    have h_eq : u +ᵥ base = base + u := by
      simp [add_comm]
    rw [h_eq] at h
    exact h
  have h_dist : dist p q < R := by
    have h1 : p - q = w := by
      simp [q, hu_def]
      abel
    have h2 : dist p q = ‖p - q‖ := by rfl
    rw [h2, h1]
    have h3 : ‖w‖ = |c| * ‖n‖ := by
      rw [hw_def]
      exact norm_smul c n
    rw [h3, hn]
    simpa using h_strip
  exact Metric.mem_thickening_iff.mpr ⟨q, hq_in_ell, h_dist⟩

/--
Line non-concentration implies discrete thin tubes.

Given G₂ with strip non-concentration for widths `r ≥ δ` (stated via
unit normals and offsets), and any G₁, we obtain `HasDiscreteThinTubes δ β K 0`
with E = G₁ ×ˢ G₂ (all pairs are good).
-/
lemma lineNonConcentration_to_thinTubes
    {δ : ℝ} (hδ : 0 < δ)
    {G₁ G₂ : DiscreteSet 2} (h1 : G₁.Nonempty) (h2 : G₂.Nonempty)
    {β K : ℝ} (hβ : 0 ≤ β) (hK : 1 ≤ K)
    (h_nonconc : ∀ (n : Point2), ‖n‖ = 1 → ∀ (t r : ℝ), δ ≤ r →
      ((G₂.filter fun y => |inner ℝ y n - t| ≤ r).card : ENNReal) ≤
        ENNReal.ofReal (K * r ^ β) * (G₂.card : ENNReal)) :
    HasDiscreteThinTubes δ β K 0 G₁ G₂ := by
  let E : Finset (Point2 × Point2) := G₁ ×ˢ G₂
  have hE_sub : E ⊆ G₁ ×ˢ G₂ := by simp [E]
  have hE_card : (E.card : ENNReal) = (G₁.card : ENNReal) * (G₂.card : ENNReal) := by
    simp [E, Finset.card_product] <;> ring
  have h_mass : (1 - ENNReal.ofReal (0 : ℝ)) * (G₁.card : ENNReal) * (G₂.card : ENNReal)
      ≤ (E.card : ENNReal) := by
    simp [hE_card] <;> norm_num
  have h_main : ∀ b₁ ∈ G₁, ∀ ℓ : AffineSubspace ℝ Point2,
      b₁ ∈ (ℓ : Set Point2) → Module.finrank ℝ ℓ.direction = 1 →
      ∀ r : ℝ, δ ≤ r →
        ((G₂.filter fun b₂ =>
          b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧
          (b₁, b₂) ∈ E).card : ENNReal) ≤
          ENNReal.ofReal (K * r ^ β) * (G₂.card : ENNReal) := by
    intro b₁ hb₁ ℓ hb₁_line hfin r hr
    have hr_pos : 0 < r := hδ.trans_le hr
    have h_in_E : ∀ b₂ ∈ G₂, (b₁, b₂) ∈ E := by
      intro b₂ hb₂
      simp only [E, Finset.mem_product] <;> exact ⟨hb₁, hb₂⟩
    have h_filter_simp : (G₂.filter fun b₂ =>
        b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E) =
        G₂.filter fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2) := by
      ext b₂
      simp only [Finset.mem_filter]
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, h_in_E b₂ h.1⟩
    rw [h_filter_simp]
    obtain ⟨n, hn, hn_orth⟩ := exists_unit_normal_of_finrank_one hfin
    let t : ℝ := inner ℝ b₁ n
    have h_strip_sub : Metric.thickening r (ℓ : Set Point2) ⊆
        {y : Point2 | |inner ℝ y n - t| ≤ r} :=
      thickening_subset_strip hfin n hn hn_orth b₁ hb₁_line r hr_pos
    have h_filter_sub : (G₂.filter fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2)) ⊆
        G₂.filter fun y => |inner ℝ y n - t| ≤ r := by
      intro b₂ hb₂
      have h_in_G₂ : b₂ ∈ G₂ := (Finset.mem_filter.mp hb₂).1
      have h_in_thick : b₂ ∈ Metric.thickening r (ℓ : Set Point2) :=
        (Finset.mem_filter.mp hb₂).2
      have h_in_strip : b₂ ∈ {y : Point2 | |inner ℝ y n - t| ≤ r} := h_strip_sub h_in_thick
      exact Finset.mem_filter.mpr ⟨h_in_G₂, h_in_strip⟩
    have h_card_le : ((G₂.filter fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2)).card : ENNReal) ≤
        ((G₂.filter fun y => |inner ℝ y n - t| ≤ r).card : ENNReal) := by
      exact_mod_cast Finset.card_le_card h_filter_sub
    have h_bound := h_nonconc n hn t r hr
    exact h_card_le.trans h_bound
  exact ⟨hβ, hK, by norm_num, E, hE_sub, h_mass, h_main⟩

end Kakeya.Assouad
