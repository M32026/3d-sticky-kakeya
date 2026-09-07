module

/-
# Weak Two-Ends Sum-Product Theorem

Proof skeleton for `WeakTwoEndsSumProduct(s, κ)`, corresponding to
Bourgain's Ring Theorem (Theorem 2) in Corso-Shmerkin, simplified.

## Proof route

1. **Strong Ring Theorem** (`strong_ring_theorem`): assumes a `(κ, 1)`-measure
   (much stronger than `(κ, δ^{-ε})`). Uses Theorem 1 (Expansion) + Marstrand
   projection + Plünnecke-Ruzsa + Ruzsa triangle.

2. **Interval maximization** (`maximal_density_interval`): find interval `I₀`
   maximizing `μ(I) / r(I)^{κ/2}`.

3. **Measure renormalization** (`renormalize_to_strong_measure`): the
   normalized restriction to `I₀` is a `(κ/2, 1)`-measure.

4. **Reduction** (`reduce_to_strong`): apply strong theorem to renormalized
   measure, then convert back to original scale using Plünnecke-Ruzsa +
   sum-to-difference corollaries.

5. **Main theorem** (`weak_two_ends_sum_product`): package everything into
   the `WeakTwoEndsSumProduct(s, κ)` format.

## Dependencies

- `MyLeanRepo.ProjectionBasic` — `WeakTwoEndsSumProduct`, `Nreal`, etc.
- (Proof phase will import `DiscretizedPluennecke`, `RuzsaTriangle`,
  `OSW.RuzsaCorollaries` — kept out of skeleton to avoid duplicate-definition
  conflicts with `ProjectionBasic`.)
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.Infrastructure
public import MyLeanRepo.ReduceToStrong_AllScale
public import MyLeanRepo.FiniteScaleToAllScaleSmoothing
public import MyLeanRepo.ProductLikeIncidence.CoefficientRounding
public import MyLeanRepo.DiscretizedStrongRingCorollary
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Classical

namespace WeakTwoEndsSumProduct

noncomputable section

/-- Covering number alias. -/
abbrev N (δ : ℝ) (A : Set ℝ) : ENNReal := Nreal δ A

/-! ## Lemma 2: Measure renormalization (see MaximalDensityInterval.lean for Lemma 1) -/

/-- Renormalize `μ` restricted to `I₀ = [x₀, x₀ + r₀]` via the affine map
`h(x) = (x - x₀) / r₀`. The resulting measure `ν` is a probability measure
on `[0,1]` satisfying the `(κ/2, 1)`-Frostman condition. -/
lemma renormalize_to_strong_measure
    {δ κ : ℝ} (hδ : 0 < δ) (hκ_pos : 0 < κ)
    {μ : Measure ℝ} {x₀ r₀ : ℝ}
    (hr₀_pos : 0 < r₀)
    (hμI₀_pos : 0 < μ (Set.Icc x₀ (x₀ + r₀)))
    (hμI₀_ne_top : μ (Set.Icc x₀ (x₀ + r₀)) ≠ ⊤)
    (C_μ : ℝ)
    (hC_pos : 0 ≤ C_μ)
    (hμ_frost : IsDirectionFrostman δ κ C_μ μ)
    (h_short : ENNReal.ofReal (C_μ * δ ^ (κ / 2)) ≤
        ENNReal.ofReal (2 ^ (κ / 2)) * μ (Set.Icc x₀ (x₀ + r₀)))
    (h_max : ∀ (a b : ℝ),
      Set.Icc a b ⊆ Set.Icc x₀ (x₀ + r₀) →
      δ ≤ b - a →
      μ (Set.Icc a b) ≤
        μ (Set.Icc x₀ (x₀ + r₀)) *
          ENNReal.ofReal (((b - a) / r₀) ^ (κ / 2))) :
    ∃ (ν : Measure ℝ),
      ν Set.univ = 1 ∧
      ν.support ⊆ Set.Icc 0 1 ∧
      IsDirectionFrostman δ (κ / 2) (2 ^ (κ / 2)) ν ∧
      ∀ (z : ℝ), z ∈ ν.support → x₀ + r₀ * z ∈ μ.support := by
  let h : ℝ → ℝ := fun y => (y - x₀) / r₀
  let I₀ := Set.Icc x₀ (x₀ + r₀)
  let μ_map : Measure ℝ := Measure.map h (μ.restrict I₀)
  let ν : Measure ℝ := (μ I₀)⁻¹ • μ_map
  have hμI₀_ne_zero : μ I₀ ≠ 0 := hμI₀_pos.ne'
  have h_meas : Measurable h := by fun_prop
  have h_inj : Function.Injective h := by
    intro y1 y2 h_eq
    simp only [h] at h_eq
    have h : (y1 - x₀) = (y2 - x₀) := by
      field_simp [hr₀_pos.ne'] at h_eq <;> linarith
    linarith
  have h_image : h '' I₀ = Set.Icc (0 : ℝ) 1 := by
    ext z
    simp only [h, Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have h1 : 0 ≤ (y - x₀) / r₀ := by
        apply div_nonneg <;> linarith
      have h2 : (y - x₀) / r₀ ≤ 1 := by
        rw [div_le_one hr₀_pos] <;> linarith
      exact ⟨h1, h2⟩
    · rintro ⟨hz1, hz2⟩
      have h_left : x₀ ≤ x₀ + r₀ * z := by
        have h : 0 ≤ r₀ * z := by positivity
        linarith
      have h_right : x₀ + r₀ * z ≤ x₀ + r₀ := by
        have h : r₀ * z ≤ r₀ := by
          calc r₀ * z ≤ r₀ * 1 := by gcongr
            _ = r₀ := by ring
        linarith
      refine ⟨x₀ + r₀ * z, ⟨h_left, h_right⟩, ?_⟩
      have h_eq : (x₀ + r₀ * z - x₀) / r₀ = z := by
        have h : (x₀ + r₀ * z - x₀) = r₀ * z := by ring
        rw [h]
        field_simp [hr₀_pos.ne'] <;> ring
      exact h_eq
  have h_preimage_all : h ⁻¹' (Set.Icc (0 : ℝ) 1) = I₀ := by
    have h1 : h ⁻¹' (h '' I₀) = I₀ := Set.preimage_image_eq I₀ h_inj
    rw [h_image] at h1
    exact h1
  have hν_univ : ν Set.univ = 1 := by
    have h1 : μ_map Set.univ = μ I₀ := by
      rw [Measure.map_apply h_meas MeasurableSet.univ]
      <;> simp [I₀, Measure.restrict_apply]
      <;> rfl
    have h2 : (μ I₀)⁻¹ * μ I₀ = 1 := ENNReal.inv_mul_cancel hμI₀_ne_zero hμI₀_ne_top
    have h3 : ν Set.univ = (μ I₀)⁻¹ * μ_map Set.univ := by
      simp [ν, Measure.smul_apply] <;> rfl
    rw [h3, h1, h2]
  -- Fix 1: (μ.restrict I₀).support ⊆ I₀
  have h_restrict_support : (μ.restrict I₀).support ⊆ I₀ := by
    have h1 : (μ.restrict I₀).support ⊆ closure I₀ ∩ μ.support :=
      Measure.support_restrict_subset
    have h2 : closure I₀ ∩ μ.support ⊆ closure I₀ := by
      intro x hx
      exact hx.1
    have h3 : (μ.restrict I₀).support ⊆ closure I₀ := h1.trans h2
    have h4 : closure I₀ = I₀ := IsClosed.closure_eq isClosed_Icc
    rw [h4] at h3
    exact h3
  -- Fix 2: μ_map.support ⊆ Set.Icc 0 1 (without support_map_subset)
  have hμmap_support : μ_map.support ⊆ Set.Icc (0 : ℝ) 1 := by
    have h5 : μ_map (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
      rw [Measure.map_apply h_meas (measurableSet_Icc.compl)]
      have h6 : h ⁻¹' ((Set.Icc (0 : ℝ) 1)ᶜ) = (h ⁻¹' (Set.Icc (0 : ℝ) 1))ᶜ := by
        rw [preimage_compl]
      rw [h6, h_preimage_all]
      have h7 : (μ.restrict I₀) (I₀ᶜ) = 0 := by
        have h8 : (μ.restrict I₀) (I₀ᶜ) = μ (I₀ᶜ ∩ I₀) := by
          rw [Measure.restrict_apply (measurableSet_Icc.compl)] <;> rfl
        rw [h8]
        have h9 : I₀ᶜ ∩ I₀ = ∅ := by
          ext x; simp [I₀] <;> tauto
        rw [h9] <;> simp
      exact h7
    have h7 : Set.Icc (0 : ℝ) 1 ∈ {t : Set ℝ | IsClosed t ∧ μ_map tᶜ = 0} :=
      ⟨isClosed_Icc, h5⟩
    rw [Measure.support_eq_sInter]
    exact Set.sInter_subset_of_mem h7
  -- Fix 3: ν.support = μ_map.support
  have hν_support_eq : ν.support = μ_map.support := by
    have hc_ne_zero : (μ I₀)⁻¹ ≠ 0 := by
      intro h
      have h' : μ I₀ = ⊤ := ENNReal.inv_eq_zero.mp h
      exact hμI₀_ne_top h'
    ext x
    constructor
    · intro hx
      by_contra h9
      let U := μ_map.supportᶜ
      have hU_open : IsOpen U := Measure.isOpen_compl_support
      have hxU : x ∈ U := h9
      have hμU : μ_map U = 0 := Measure.measure_compl_support
      have hνU : ν U = 0 := by
        simp [ν, hμU, Measure.smul_apply] <;> rfl
      have h10 : U ⊆ ν.supportᶜ := by
        rw [Measure.compl_support_eq_sUnion]
        intro y hy
        exact ⟨U, ⟨hU_open, hνU⟩, hy⟩
      exact h10 hxU hx
    · intro hx
      by_contra h9
      let U := ν.supportᶜ
      have hU_open : IsOpen U := Measure.isOpen_compl_support
      have hxU : x ∈ U := h9
      have hνU : ν U = 0 := Measure.measure_compl_support
      have h11 : (μ I₀)⁻¹ * μ_map U = 0 := by simpa [ν, Measure.smul_apply] using hνU
      have h12 : μ_map U = 0 := by
        exact (mul_eq_zero.mp h11).resolve_left hc_ne_zero
      have h13 : U ⊆ μ_map.supportᶜ := by
        rw [Measure.compl_support_eq_sUnion]
        intro y hy
        exact ⟨U, ⟨hU_open, h12⟩, hy⟩
      exact h13 hxU hx
  have hν_support : ν.support ⊆ Set.Icc 0 1 := by
    rw [hν_support_eq]
    exact hμmap_support
  have hν_frost : IsDirectionFrostman δ (κ / 2) (2 ^ (κ / 2)) ν := by
    refine' ⟨hν_univ, hν_support, _⟩
    intro a r hδr hr1
    let L := max (a - r) 0
    let R := min (a + r) 1
    have hL_nonneg : 0 ≤ L := by simp [L] <;> linarith
    have hR_le_one : R ≤ 1 := by simp [R] <;> linarith
    have h_clipped : Set.Icc (a - r) (a + r) ∩ Set.Icc (0 : ℝ) 1 = Set.Icc L R := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, L, R]
      constructor
      · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
        have h5 : max (a - r) 0 ≤ x := by
          rw [max_le_iff] <;> exact ⟨h1, h3⟩
        have h6 : x ≤ min (a + r) 1 := by
          rw [le_min_iff] <;> exact ⟨h2, h4⟩
        exact ⟨h5, h6⟩
      · rintro ⟨h1, h2⟩
        have h3 : a - r ≤ x := by
          calc a - r ≤ max (a - r) 0 := le_max_left _ _
               _ ≤ x := h1
        have h4 : x ≤ a + r := by
          calc x ≤ min (a + r) 1 := h2
               _ ≤ a + r := min_le_left _ _
        have h5 : 0 ≤ x := by
          calc 0 ≤ max (a - r) 0 := le_max_right _ _
               _ ≤ x := h1
        have h6 : x ≤ 1 := by
          calc x ≤ min (a + r) 1 := h2
               _ ≤ 1 := min_le_right _ _
        exact ⟨⟨h3, h4⟩, ⟨h5, h6⟩⟩
    by_cases hLR : L ≤ R
    · -- L ≤ R, nonempty clipped interval
      have h_len : R - L ≤ 2 * r := by
        have hL1 : a - r ≤ L := by simp [L] <;> linarith
        have hR1 : R ≤ a + r := by simp [R] <;> linarith
        linarith
      have h_preimage_LR : h ⁻¹' (Set.Icc L R) = Set.Icc (x₀ + r₀ * L) (x₀ + r₀ * R) := by
        ext y
        simp only [h, Set.mem_preimage, Set.mem_Icc]
        constructor
        · rintro ⟨h1, h2⟩
          have h3 : x₀ + r₀ * L ≤ y := by
            have h4 : r₀ * L ≤ y - x₀ := by
              have h5 : L ≤ (y - x₀) / r₀ := h1
              have h6 : r₀ * L ≤ r₀ * ((y - x₀) / r₀) := by gcongr
              have h7 : r₀ * ((y - x₀) / r₀) = y - x₀ := by
                field_simp [hr₀_pos.ne'] <;> ring
              rw [h7] at h6
              exact h6
            linarith
          have h6 : y ≤ x₀ + r₀ * R := by
            have h7 : (y - x₀) / r₀ ≤ R := h2
            have h8 : y - x₀ ≤ r₀ * R := by
              have h9 : y - x₀ = r₀ * ((y - x₀) / r₀) := by
                field_simp [hr₀_pos.ne'] <;> ring
              rw [h9]
              gcongr
            linarith
          exact ⟨h3, h6⟩
        · rintro ⟨h1, h2⟩
          have h3 : L ≤ (y - x₀) / r₀ := by
            have h4 : r₀ * L ≤ y - x₀ := by linarith
            have h5 : L = (r₀ * L) / r₀ := by
              field_simp [hr₀_pos.ne'] <;> ring
            rw [h5]
            gcongr
          have h6 : (y - x₀) / r₀ ≤ R := by
            have h7 : y - x₀ ≤ r₀ * R := by linarith
            have h8 : (r₀ * R) / r₀ = R := by
              field_simp [hr₀_pos.ne'] <;> ring
            have h9 : (y - x₀) / r₀ ≤ (r₀ * R) / r₀ := by gcongr
            rw [h8] at h9
            exact h9
          exact ⟨h3, h6⟩
      have h_sub : Set.Icc (x₀ + r₀ * L) (x₀ + r₀ * R) ⊆ I₀ := by
        intro y hy
        rcases hy with ⟨hyl, hyr⟩
        have h1 : x₀ ≤ y := by
          have h11 : 0 ≤ r₀ * L := by positivity
          linarith
        have h2 : y ≤ x₀ + r₀ := by
          have h21 : r₀ * R ≤ r₀ := by
            have h22 : R ≤ 1 := hR_le_one
            nlinarith
          linarith
        exact ⟨h1, h2⟩
      let J := Set.Icc (x₀ + r₀ * L) (x₀ + r₀ * R)
      have h_len_J : (x₀ + r₀ * R) - (x₀ + r₀ * L) = r₀ * (R - L) := by ring
      have h_bound : μ J ≤ μ I₀ * ENNReal.ofReal ((2 * r) ^ (κ / 2)) := by
        by_cases h_long : δ ≤ r₀ * (R - L)
        · -- Long case: apply maximal density bound
          have h6 : μ J ≤ μ I₀ * ENNReal.ofReal (((R - L) ^ (κ / 2))) := by
            have h7 := h_max (x₀ + r₀ * L) (x₀ + r₀ * R) h_sub (by linarith)
            have h8 : ((x₀ + r₀ * R) - (x₀ + r₀ * L)) / r₀ = R - L := by
              field_simp [hr₀_pos.ne'] <;> ring
            rw [h8] at h7
            exact h7
          have h9 : (R - L) ^ (κ / 2) ≤ (2 * r) ^ (κ / 2) := by
            gcongr <;> linarith
          have h10 : μ J ≤ μ I₀ * ENNReal.ofReal ((2 * r) ^ (κ / 2)) := by
            calc _ ≤ μ I₀ * ENNReal.ofReal ((R - L) ^ (κ / 2)) := h6
                 _ ≤ μ I₀ * ENNReal.ofReal ((2 * r) ^ (κ / 2)) := by
                   gcongr <;> exact ENNReal.ofReal_le_ofReal h9
          exact h10
        · -- Short case: use Frostman at scale δ
          have h_short_len : r₀ * (R - L) < δ := by linarith
          let m := x₀ + r₀ * (L + R) / 2
          have hJ_sub_ball : J ⊆ Set.Icc (m - δ) (m + δ) := by
            intro y hy
            have hyl : x₀ + r₀ * L ≤ y := hy.1
            have hyr : y ≤ x₀ + r₀ * R := hy.2
            dsimp only [m]
            constructor <;> nlinarith
          have h_frost_ball : μ (Set.Icc (m - δ) (m + δ)) ≤
              ENNReal.ofReal (C_μ * δ ^ κ) := by
            have h := hμ_frost.2.2 m δ (by linarith) (by linarith)
            simpa using h
          have hμJ : μ J ≤ ENNReal.ofReal (C_μ * δ ^ κ) := by
            calc μ J ≤ μ (Set.Icc (m - δ) (m + δ)) := measure_mono hJ_sub_ball
                 _ ≤ ENNReal.ofReal (C_μ * δ ^ κ) := h_frost_ball
          have h_pos1 : 0 ≤ C_μ * δ ^ (κ / 2) := by
            have h1 : 0 < δ ^ (κ / 2) := Real.rpow_pos_of_pos hδ (κ / 2)
            have h2 : 0 ≤ C_μ := hC_pos
            exact mul_nonneg h2 h1.le
          have h11 : ENNReal.ofReal (C_μ * δ ^ κ) ≤
              μ I₀ * ENNReal.ofReal ((2 * r) ^ (κ / 2)) := by
            have h12 : ENNReal.ofReal (C_μ * δ ^ κ) =
                ENNReal.ofReal (C_μ * δ ^ (κ / 2)) * ENNReal.ofReal (δ ^ (κ / 2)) := by
              have h13 : C_μ * δ ^ κ = C_μ * δ ^ (κ / 2) * δ ^ (κ / 2) := by
                have h14 : δ ^ κ = δ ^ (κ / 2) * δ ^ (κ / 2) := by
                  rw [← Real.rpow_add (by linarith)] <;> ring_nf
                rw [h14] <;> ring
              rw [h13, ENNReal.ofReal_mul h_pos1]
            rw [h12]
            have h15 : ENNReal.ofReal (C_μ * δ ^ (κ / 2)) * ENNReal.ofReal (δ ^ (κ / 2)) ≤
                (ENNReal.ofReal (2 ^ (κ / 2)) * μ I₀) * ENNReal.ofReal (δ ^ (κ / 2)) := by
              gcongr
            have h16 : (ENNReal.ofReal (2 ^ (κ / 2)) * μ I₀) * ENNReal.ofReal (δ ^ (κ / 2)) =
                μ I₀ * ENNReal.ofReal ((2 * δ) ^ (κ / 2)) := by
              have h17 : (2 * δ) ^ (κ / 2) = (2 ^ (κ / 2)) * δ ^ (κ / 2) := by
                rw [← Real.mul_rpow (by positivity) (by positivity)] <;> ring
              have h18 : ENNReal.ofReal ((2 * δ) ^ (κ / 2)) =
                  ENNReal.ofReal (2 ^ (κ / 2)) * ENNReal.ofReal (δ ^ (κ / 2)) := by
                rw [h17, ENNReal.ofReal_mul (by positivity)]
              rw [h18] <;> ring
            rw [h16] at h15
            have h19 : μ I₀ * ENNReal.ofReal ((2 * δ) ^ (κ / 2)) ≤
                μ I₀ * ENNReal.ofReal ((2 * r) ^ (κ / 2)) := by
              gcongr
              <;> exact ENNReal.ofReal_le_ofReal (by gcongr <;> linarith)
            exact h15.trans h19
          exact hμJ.trans h11
      have h11 : ν (Set.Icc (a - r) (a + r)) =
          μ (Set.Icc (x₀ + r₀ * L) (x₀ + r₀ * R)) / μ I₀ := by
        have h12 : ν (Set.Icc (a - r) (a + r)) =
            (μ I₀)⁻¹ * μ_map (Set.Icc (a - r) (a + r)) := by
          simp [ν, Measure.smul_apply] <;> ring
        rw [h12]
        have h13 : μ_map (Set.Icc (a - r) (a + r)) =
            (μ.restrict I₀) (h ⁻¹' (Set.Icc (a - r) (a + r))) := by
          rw [Measure.map_apply h_meas (measurableSet_Icc)] <;> rfl
        rw [h13]
        have h_meas_set : MeasurableSet (h ⁻¹' (Set.Icc (a - r) (a + r))) :=
          h_meas measurableSet_Icc
        have h14 : (μ.restrict I₀) (h ⁻¹' (Set.Icc (a - r) (a + r))) =
            μ (h ⁻¹' (Set.Icc (a - r) (a + r)) ∩ I₀) := by
          rw [Measure.restrict_apply h_meas_set] <;> rfl
        rw [h14]
        have h15 : h ⁻¹' (Set.Icc (a - r) (a + r)) ∩ I₀ = h ⁻¹' (Set.Icc L R) := by
          ext y
          simp only [Set.mem_inter_iff, Set.mem_preimage]
          constructor
          · rintro ⟨hy1, hy2⟩
            have h_y_in01 : h y ∈ Set.Icc (0 : ℝ) 1 := by
              rw [← h_image]
              exact ⟨y, hy2, rfl⟩
            rw [← h_clipped]
            exact ⟨hy1, h_y_in01⟩
          · intro hy
            have h_y_in_LR : h y ∈ Set.Icc L R := hy
            have h_y_in_ball : h y ∈ Set.Icc (a - r) (a + r) := by
              have h1 : L ≥ a - r := by simp [L] <;> linarith
              have h2 : R ≤ a + r := by simp [R] <;> linarith
              exact ⟨by linarith [h_y_in_LR.1, h1], by linarith [h_y_in_LR.2, h2]⟩
            have h_y_in01 : h y ∈ Set.Icc (0 : ℝ) 1 := by
              have h1 : 0 ≤ L := by simp [L] <;> linarith
              have h2 : R ≤ 1 := by simp [R] <;> linarith
              exact ⟨by linarith [h_y_in_LR.1, h1], by linarith [h_y_in_LR.2, h2]⟩
            have h_y_in_I0 : y ∈ I₀ := by
              rw [← h_preimage_all]
              exact h_y_in01
            exact ⟨h_y_in_ball, h_y_in_I0⟩
        rw [h15, h_preimage_LR]
        -- Fix 4: prove (μ I₀)⁻¹ * μ(...) = μ(...) / μ I₀
        have h16 : (μ I₀)⁻¹ * μ (Set.Icc (x₀ + r₀ * L) (x₀ + r₀ * R)) =
            μ (Set.Icc (x₀ + r₀ * L) (x₀ + r₀ * R)) / μ I₀ := by
          simp [div_eq_mul_inv] <;> ring
        exact h16
      rw [h11]
      have h12 : μ (Set.Icc (x₀ + r₀ * L) (x₀ + r₀ * R)) / μ I₀ ≤
          (μ I₀ * ENNReal.ofReal ((2 * r) ^ (κ / 2))) / μ I₀ := by
        gcongr
      have h_cancel : (μ I₀ * ENNReal.ofReal ((2 * r) ^ (κ / 2))) / μ I₀ =
          ENNReal.ofReal ((2 * r) ^ (κ / 2)) := by
        have h_comm : μ I₀ * ENNReal.ofReal ((2 * r) ^ (κ / 2)) =
            ENNReal.ofReal ((2 * r) ^ (κ / 2)) * μ I₀ := by
          exact mul_comm _ _
        rw [h_comm]
        exact ENNReal.mul_div_cancel_right hμI₀_ne_zero hμI₀_ne_top
      rw [h_cancel] at h12
      have h13 : (2 * r) ^ (κ / 2) = (2 ^ (κ / 2)) * r ^ (κ / 2) := by
        have hr_nonneg : 0 ≤ r := by linarith
        have h : (2 * r) ^ (κ / 2) = (2 : ℝ) ^ (κ / 2) * r ^ (κ / 2) := by
          rw [← Real.mul_rpow (by positivity) hr_nonneg] <;> ring
        exact h
      rw [h13] at h12
      exact h12
    · -- L > R, empty clipped interval
      have h_empty : Set.Icc (a - r) (a + r) ∩ Set.Icc (0 : ℝ) 1 = ∅ := by
        rw [h_clipped]
        rw [Set.Icc_eq_empty_of_lt] <;> linarith
      have h_disj : Disjoint (Set.Icc (a - r) (a + r)) (Set.Icc (0 : ℝ) 1) := by
        rw [disjoint_iff_inter_eq_empty]
        exact h_empty
      have h14 : Set.Icc (a - r) (a + r) ⊆ (ν.support)ᶜ := by
        intro x hx
        intro hxs
        have h16 : x ∈ Set.Icc (0 : ℝ) 1 := hν_support hxs
        exact h_disj.le_bot ⟨hx, h16⟩
      have h17 : ν (Set.Icc (a - r) (a + r)) ≤ ν (ν.supportᶜ) :=
        measure_mono h14
      have h18 : ν (ν.supportᶜ) = 0 := Measure.measure_compl_support
      have h19 : ν (Set.Icc (a - r) (a + r)) = 0 := by
        rw [h18] at h17
        simpa using h17
      rw [h19]
      <;> positivity
  -- Support provenance: z ∈ ν.support → x₀ + r₀*z ∈ μ.support
  have hν_support_eq : ν.support = μ_map.support := hν_support_eq
  have h_inj : Function.Injective h := h_inj
  have h_cont : Continuous h := by fun_prop
  let h_inv : ℝ → ℝ := fun z => x₀ + r₀ * z
  have h_cont_inv : Continuous h_inv := by fun_prop
  have h_left_inv : Function.LeftInverse h_inv h := by
    intro y
    simp [h, h_inv, hr₀_pos.ne'] <;> field_simp [hr₀_pos.ne'] <;> ring
  have h_right_inv : Function.RightInverse h_inv h := by
    intro z
    simp [h, h_inv, hr₀_pos.ne'] <;> field_simp [hr₀_pos.ne'] <;> ring
  let h_homeo : Homeomorph ℝ ℝ :=
    { toFun := h, invFun := h_inv, left_inv := h_left_inv, right_inv := h_right_inv }
  have h_open_map : IsOpenMap h := h_homeo.isOpenMap
  have hprov : ∀ (z : ℝ), z ∈ ν.support → x₀ + r₀ * z ∈ μ.support := by
    intro z hz
    have hz_map : z ∈ μ_map.support := by
      rw [← hν_support_eq]; exact hz
    by_contra h_y_not_supp
    have h_in_compl : (x₀ + r₀ * z) ∈ μ.supportᶜ := h_y_not_supp
    rw [Measure.compl_support_eq_sUnion] at h_in_compl
    rcases h_in_compl with ⟨U, ⟨hU_open, hμU⟩, hxU⟩
    let V : Set ℝ := h '' U
    have hV_open : IsOpen V := h_open_map _ hU_open
    have hzV : z ∈ V := by
      refine ⟨x₀ + r₀ * z, hxU, ?_⟩
      have h_eq : h (x₀ + r₀ * z) = z := by
        simp [h, hr₀_pos.ne'] <;> field_simp [hr₀_pos.ne'] <;> ring
      exact h_eq
    have h_preimage : h ⁻¹' V = U := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨y', hy', h_eq⟩
        have h_inj' : y' = y := h_inj h_eq
        exact h_inj'.symm ▸ hy'
      · intro hy
        exact ⟨y, hy, rfl⟩
    have hμ_mapV : μ_map V = 0 := by
      rw [Measure.map_apply h_meas hV_open.measurableSet]
      rw [h_preimage, Measure.restrict_apply hU_open.measurableSet]
      have h9 : U ∩ I₀ ⊆ U := by intro x hx; exact hx.1
      have h10 : μ (U ∩ I₀) ≤ μ U := measure_mono h9
      rw [hμU] at h10
      simpa using h10
    have h1 : V ⊆ μ_map.supportᶜ :=
      μ_map.subset_compl_support_of_isOpen hV_open hμ_mapV
    have h_contra : z ∉ μ_map.support := h1 hzV
    exact h_contra hz_map
  exact ⟨ν, hν_univ, hν_support, hν_frost, hprov⟩


/-! ## Lemma 3: Reduction from general to strong case -/

/-- Given the strong ring theorem, reduce the general `(κ, δ^{-ε})`-measure
case to the strong `(κ/2, 1)`-measure case.

Uses:
1. Maximal density interval
2. Renormalization
3. Strong ring theorem with `t = r₀`
4. Conversion back: `|r₀⁻¹A + yA| > δ^{-c}|A|`
5. Plünnecke-Ruzsa to extract `|A + zA|` for `z ∈ {1, x, -x₀}`
6. Sum-to-difference corollary to handle the `z = -x₀` case
7. Handle `z = 1` using `x₂ = max supp μ` and Corollary 2.5 -/
lemma reduce_to_strong
    (s κ : ℝ) (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hκ_pos : 0 < κ) (hκ_le_s : κ ≤ s) :
    ∃ (c' ε' : ℝ), 0 < c' ∧ 0 < ε' ∧ ε' ≤ κ / 4 ∧
      ∀ (K : ℝ), 1 ≤ K →
        ∃ (δ₀ : ℝ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧
          ∀ {δ : ℝ}, δ ∈ dyadicScales → 0 < δ → δ ≤ δ₀ →
            ∀ (A : Set ℝ) (μ : Measure ℝ),
              A ⊆ Set.Icc 1 2 →
              IsRealDeltaSet δ κ (K * δ ^ (-ε')) A →
              N δ A ≤ ENNReal.ofReal (K * δ ^ (-(s + ε'))) →
              IsDirectionFrostman δ κ (K * δ ^ (-ε')) μ →
              ∃ x ∈ μ.support,
                ENNReal.ofReal (δ ^ (-c')) * N δ A ≤
                  N δ (Set.image2 (fun a b => a + x * b) A A) := by
  -- Step 1: Obtain all-scale reduction exponents
  rcases reduce_to_strong_allscale s κ hs_pos hs_lt_one hκ_pos hκ_le_s
    with ⟨c_all, ε_all, hc_all_pos, hε_all_pos, hε_all_le_kappa4, h_main_all⟩
  let c' := c_all / 2
  let ε' := ε_all
  have hc'_pos : 0 < c' := by positivity
  have hε'_pos : 0 < ε' := hε_all_pos
  have hc_all_gt_c' : c' < c_all := by
    dsimp only [c']
    linarith [hc_all_pos]
  have hε'_le_kappa4 : ε' ≤ κ / 4 := by
    dsimp only [ε']
    exact hε_all_le_kappa4
  refine ⟨c', ε', hc'_pos, hε'_pos, hε'_le_kappa4, ?_⟩
  intro K hK
  let K' : ℝ := (2 : ℝ)^(κ + 1) * K
  have hK'_ge_one : 1 ≤ K' := by
    dsimp only [K']
    have h1 : (1 : ℝ) ≤ (2 : ℝ)^(κ + 1) := by
      apply Real.one_le_rpow <;> norm_num <;> linarith
    nlinarith
  rcases h_main_all K' hK'_ge_one with ⟨δ₀_all, hδ₀_all_pos, hδ₀_all_le_one, h_reduce_all⟩
  -- Choose δ₀ small enough for rounding absorption: δ^α ≤ 1/5 where α = c_all - c'
  let α : ℝ := c_all - c'
  have hα_pos : 0 < α := by linarith
  let δ₀_round : ℝ := (1 / 5 : ℝ) ^ (1 / α)
  have hδ₀_round_pos : 0 < δ₀_round := by
    dsimp only [δ₀_round]
    exact Real.rpow_pos_of_pos (by norm_num) _
  let δ₀ := min (min δ₀_all δ₀_round) (1 / 5)
  have hδ₀_le_one : δ₀ ≤ 1 := by
    have h : δ₀ ≤ 1 / 5 := min_le_right _ _
    linarith
  refine ⟨δ₀, by positivity, hδ₀_le_one, ?_⟩
  intro δ hδ_dyadic hδ_pos hδle A μ hA_sub hA_delta hN_bound hμ
  have hδ_lt_fourth : δ < 1 / 4 := by
    have h1 : δ ≤ δ₀ := hδle
    have h2 : δ₀ ≤ 1 / 5 := min_le_right _ _
    linarith
  have hδ_le_all : δ ≤ δ₀_all := by
    have h1 : δ ≤ δ₀ := hδle
    have h2 : δ₀ ≤ δ₀_all := by
      have h3 : δ₀ ≤ min δ₀_all δ₀_round := min_le_left _ _
      exact le_trans h3 (min_le_left _ _)
    exact le_trans h1 h2
  have hδ_le_round : δ ≤ δ₀_round := by
    have h1 : δ ≤ δ₀ := hδle
    have h2 : δ₀ ≤ δ₀_round := by
      have h3 : δ₀ ≤ min δ₀_all δ₀_round := min_le_left _ _
      exact le_trans h3 (min_le_right _ _)
    exact le_trans h1 h2
  have hκ_le_one : κ ≤ 1 := by linarith
  have hC_pos : 0 < K * δ ^ (-ε') := by positivity
  -- Step 2: Convert direction-Frostman to finite-scale
  have h_fin : IsFiniteScaleFrostman δ κ (K * δ ^ (-ε')) μ :=
    ⟨hμ.1, hμ.2.1, hδ_pos, hκ_pos, hκ_le_one, hC_pos, hμ.2.2⟩
  -- Step 3: Smooth to all-scale Frostman
  rcases finite_scale_to_all_scale_smoothing hδ_pos hδ_lt_fourth hκ_pos hκ_le_one h_fin
    with ⟨ν, hν_univ, hν_supp, hν_near, hν_frost⟩
  -- Step 4: Upgrade A's constants to K' = 2^(κ+1)*K
  have hK_le_K' : K ≤ K' := by
    dsimp only [K']
    have h1 : (1 : ℝ) ≤ (2 : ℝ)^(κ + 1) := by
      apply Real.one_le_rpow <;> norm_num <;> linarith
    nlinarith
  have hK_le_K'2 : K * δ ^ (-ε') ≤ K' * δ ^ (-ε') := by gcongr
  have hA_delta' : IsRealDeltaSet δ κ (K' * δ ^ (-ε')) A :=
    IsRealDeltaSet.mono_const' hA_delta hK_le_K'2
  have hN_bound' : N δ A ≤ ENNReal.ofReal (K' * δ ^ (-(s + ε'))) := by
    have h1 : K * δ ^ (-(s + ε')) ≤ K' * δ ^ (-(s + ε')) := by gcongr
    have h2 : ENNReal.ofReal (K * δ ^ (-(s + ε'))) ≤ ENNReal.ofReal (K' * δ ^ (-(s + ε'))) :=
      ENNReal.ofReal_le_ofReal h1
    exact le_trans hN_bound h2
  -- Step 5: Call all-scale reduction
  have hν_frost' : IsAllScaleFrostman κ (K' * δ ^ (-ε')) ν := by
    have h_eq : smoothingConstant κ * (K * δ ^ (-ε')) = K' * δ ^ (-ε') := by
      dsimp only [smoothingConstant, K'] <;> ring
    rw [h_eq] at hν_frost
    exact hν_frost
  have h_expansion : ∃ (x' : ℝ), x' ∈ ν.support ∧
      ENNReal.ofReal (δ ^ (-c_all)) * N δ A ≤
        N δ (Set.image2 (fun a b => a + x' * b) A A) :=
    h_reduce_all hδ_dyadic hδ_pos hδ_le_all A ν hA_sub hA_delta' hN_bound' hν_frost' hν_supp
  rcases h_expansion with ⟨x', hx'_supp, h_exp⟩
  -- Step 6: Find x ∈ μ.support near x'
  rcases hν_near x' hx'_supp with ⟨x, hx_supp, h_close⟩
  -- Step 7: Coefficient rounding (C=1 since |x-x'|≤δ)
  have h_close' : |x' - x| ≤ (1 : ℝ) * δ := by
    simpa [one_mul] using h_close
  have h_round_main := ProductLikeIncidence.coefficient_rounding_covering
    (C := 1) hδ_pos (by norm_num) hA_sub h_close'
  have h_round : N δ (Set.image2 (fun a b => a + x' * b) A A) ≤
      (5 : ENNReal) * N δ (Set.image2 (fun a b => a + x * b) A A) := by
    have h_factor : (2 * Nat.ceil (2 * (1 : ℝ)) + 1 : ENNReal) = (5 : ENNReal) := by norm_num
    rw [h_factor] at h_round_main
    exact h_round_main
  have h9 : ENNReal.ofReal (δ ^ (-c_all)) * N δ A ≤
      (5 : ENNReal) * N δ (Set.image2 (fun a b => a + x * b) A A) :=
    le_trans h_exp h_round
  -- Step 8: Absorb factor 5 by shrinking c_all to c'
  have h10 : δ ^ α ≤ 1 / 5 := by
    have h11 : δ ≤ (1 / 5 : ℝ) ^ (1 / α) := hδ_le_round
    have h12 : 0 < α := hα_pos
    have h13 : 0 ≤ 1 / 5 := by norm_num
    have h14 : δ ^ α ≤ ((1 / 5 : ℝ) ^ (1 / α)) ^ α :=
      Real.rpow_le_rpow (by linarith) h11 (by linarith)
    have h15 : ((1 / 5 : ℝ) ^ (1 / α)) ^ α = (1 / 5 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num)]
      have h16 : (1 / α : ℝ) * α = 1 := by field_simp [h12.ne'] <;> ring
      rw [h16, Real.rpow_one]
    rw [h15] at h14
    exact h14
  have h17 : δ ^ (-c') = δ ^ (-c_all) * δ ^ α := by
    have h18 : -c' = -c_all + α := by linarith
    rw [h18, ← Real.rpow_add hδ_pos] <;> ring
  have h19 : δ ^ (-c') ≤ δ ^ (-c_all) / 5 := by
    rw [h17]
    have h20 : δ ^ (-c_all) * δ ^ α ≤ δ ^ (-c_all) * (1 / 5) := by gcongr <;> linarith
    have h21 : δ ^ (-c_all) * (1 / 5) = δ ^ (-c_all) / 5 := by ring
    rw [h21] at h20
    exact h20
  have h_div_ofReal : ENNReal.ofReal (δ ^ (-c_all) / 5) = ENNReal.ofReal (δ ^ (-c_all)) / 5 := by
    have h5_pos : (0 : ℝ) < 5 := by norm_num
    have h : ENNReal.ofReal (δ ^ (-c_all) / 5) =
        ENNReal.ofReal (δ ^ (-c_all)) / ENNReal.ofReal (5 : ℝ) :=
      ENNReal.ofReal_div_of_pos h5_pos
    rw [h]
    have h2 : ENNReal.ofReal (5 : ℝ) = (5 : ENNReal) := by norm_cast
    rw [h2] <;> rfl
  have h22 : ENNReal.ofReal (δ ^ (-c')) ≤ ENNReal.ofReal (δ ^ (-c_all)) / 5 := by
    rw [←h_div_ofReal]
    exact ENNReal.ofReal_le_ofReal h19
  have h23 : ENNReal.ofReal (δ ^ (-c')) * N δ A ≤
      (ENNReal.ofReal (δ ^ (-c_all)) * N δ A) / 5 := by
    calc ENNReal.ofReal (δ ^ (-c')) * N δ A
      ≤ (ENNReal.ofReal (δ ^ (-c_all)) / 5) * N δ A := by gcongr
    _ = (ENNReal.ofReal (δ ^ (-c_all)) * N δ A) / 5 := by
      let a := ENNReal.ofReal (δ ^ (-c_all))
      let b := N δ A
      have h_alg : (a / 5) * b = (a * b) / 5 := by
        calc
          (a / 5) * b
            = a * (5 : ENNReal)⁻¹ * b := by rfl
          _ = a * b * (5 : ENNReal)⁻¹ := by
            rw [mul_assoc a (5 : ENNReal)⁻¹ b, mul_comm (5 : ENNReal)⁻¹ b, ←mul_assoc]
          _ = (a * b) / 5 := by rfl
      exact h_alg
  have h24 : (ENNReal.ofReal (δ ^ (-c_all)) * N δ A) / 5 ≤
      N δ (Set.image2 (fun a b => a + x * b) A A) := by
    have h_div_mono : (ENNReal.ofReal (δ ^ (-c_all)) * N δ A) / 5 ≤
        ((5 : ENNReal) * N δ (Set.image2 (fun a b => a + x * b) A A)) / 5 := by
      gcongr
      <;> exact h9
    have h_cancel : ((5 : ENNReal) * N δ (Set.image2 (fun a b => a + x * b) A A)) / 5 =
        N δ (Set.image2 (fun a b => a + x * b) A A) := by
      let X := N δ (Set.image2 (fun a b => a + x * b) A A)
      have h5_ne_zero : (5 : ENNReal) ≠ 0 := by norm_num
      have h5_ne_top : (5 : ENNReal) ≠ ⊤ := by norm_num
      have h_comm : ((5 : ENNReal) * X) / 5 = (X * (5 : ENNReal)) / 5 := by
        rw [mul_comm (5 : ENNReal) X]
      rw [h_comm]
      exact ENNReal.mul_div_cancel_right h5_ne_zero h5_ne_top
    rw [h_cancel] at h_div_mono
    exact h_div_mono
  exact ⟨x, hx_supp, le_trans h23 h24⟩

/-! ## Main theorem -/

/-- **Weak Two-Ends Sum-Product Theorem**.

For `0 < s < 1` and `0 < κ ≤ s`, there exist exponents `εnc, εgain > 0`
such that for any `K ≥ 1` and sufficiently small dyadic `δ`:

If `A ⊆ [1,2]` is a `(δ, κ, K·δ^{-εnc})`-set with covering number between
`δ^{-(s-εnc)}` and `K·δ^{-(s+εnc)}`, and `μ` is a `(κ, K·δ^{-εnc})`-Frostman
measure on `[0,1]`, then there exists `x ∈ supp μ` such that
`|A + x·A|_δ ≥ δ^{-εgain} · |A|_δ`.

This corresponds to Bourgain's Ring Theorem (Theorem 2). -/
theorem weak_two_ends_sum_product (s κ : ℝ)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hκ_pos : 0 < κ) (hκ_le_s : κ ≤ s) :
    WeakTwoEndsSumProduct s κ := by
  -- Step 1: Reduce to all-scale strong ring theorem
  have h_main := reduce_to_strong s κ hs_pos hs_lt_one hκ_pos hκ_le_s
  -- Step 2: Package into WeakTwoEndsSumProduct format
  rcases h_main with ⟨c', ε', hc_pos, hε_pos, _, h_main⟩
  -- We may need to shrink ε' to satisfy the bound εnc < min(min s κ)(1-s)/100
  let εnc := min ε' (min (min s κ) (1 - s) / 200)
  have henc_pos : 0 < εnc := by positivity
  have henc_bound : εnc < min (min s κ) (1 - s) / 100 := by
    have h1 : εnc ≤ min (min s κ) (1 - s) / 200 := by
      exact min_le_right _ _
    have h2 : min (min s κ) (1 - s) / 200 < min (min s κ) (1 - s) / 100 := by
      have h3 : 0 < min (min s κ) (1 - s) := by positivity
      linarith
    linarith
  refine' ⟨εnc, c', henc_pos, henc_bound, hc_pos, _⟩
  intro K hK
  rcases h_main K hK with ⟨δ₀, hδ₀_pos, hδ₀_le_one, h⟩
  refine' ⟨δ₀, hδ₀_pos, hδ₀_le_one, _⟩
  intro δ hδ hδle
  intro A μ hA_sub hA_delta hA_upper hμ
  -- We need to convert from εnc to ε' since εnc ≤ ε'
  -- The (δ, κ, K*δ^{-εnc}) condition is stronger than (δ, κ, K*δ^{-ε'})
  -- because εnc ≤ ε' means δ^{-εnc} ≤ δ^{-ε'} for δ < 1
  have hδ_pos : 0 < δ := by
    rcases hδ with ⟨n, rfl⟩
    positivity
  have hδ_le_one : δ ≤ 1 := by linarith
  have hεnc_le_ε' : εnc ≤ ε' := min_le_left _ _
  -- For 0 < δ ≤ 1, δ^x is decreasing in x, so εnc ≤ ε' implies δ^{-εnc} ≤ δ^{-ε'}
  have h_rpow1 : δ ^ (-εnc) ≤ δ ^ (-ε') :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one (by linarith)
  have h_C1 : K * δ ^ (-εnc) ≤ K * δ ^ (-ε') := by gcongr
  have h_rpow2 : δ ^ (-(s + εnc)) ≤ δ ^ (-(s + ε')) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one (by linarith)
  have h_C2 : K * δ ^ (-(s + εnc)) ≤ K * δ ^ (-(s + ε')) := by gcongr
  -- IsRealDeltaSet is monotone in the constant C
  have hA_delta' : IsRealDeltaSet δ κ (K * δ ^ (-ε')) A := by
    rcases hA_delta with ⟨h_bdd, h_ne, h_d, h_dyad, hδp, h_s1, h_s2, _, h_bound⟩
    refine' ⟨h_bdd, h_ne, h_d, h_dyad, hδp, h_s1, h_s2, by positivity, _⟩
    intro r Q hr hQ hδr hr1
    have h3 := h_bound hr hQ hδr hr1
    have h4 : ENNReal.ofReal (K * δ ^ (-εnc)) ≤ ENNReal.ofReal (K * δ ^ (-ε')) :=
      ENNReal.ofReal_le_ofReal h_C1
    calc _ ≤ ENNReal.ofReal (K * δ ^ (-εnc)) * _ * _ := h3
         _ ≤ ENNReal.ofReal (K * δ ^ (-ε')) * _ * _ := by gcongr
  -- Upper bound is monotone in the constant
  have hA_upper' : N δ A ≤ ENNReal.ofReal (K * δ ^ (-(s + ε'))) :=
    hA_upper.trans (ENNReal.ofReal_le_ofReal h_C2)
  -- IsDirectionFrostman is monotone in the constant C
  have hμ' : IsDirectionFrostman δ κ (K * δ ^ (-ε')) μ := by
    rcases hμ with ⟨h1, h2, h3⟩
    refine' ⟨h1, h2, _⟩
    intro a r hδr hr1
    have h4 := h3 a r hδr hr1
    have h5 : (K * δ ^ (-εnc)) * r ^ κ ≤ (K * δ ^ (-ε')) * r ^ κ := by
      have hr_nonneg : 0 ≤ r := by linarith
      gcongr
    exact h4.trans (ENNReal.ofReal_le_ofReal h5)
  exact h hδ hδ_pos hδle A μ hA_sub hA_delta' hA_upper' hμ'

end
