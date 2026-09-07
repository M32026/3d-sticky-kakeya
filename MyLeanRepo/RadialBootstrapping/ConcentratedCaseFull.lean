module

/-
  ConcentratedCaseFull.lean

  Bridge between AffineSubspace and Line2 for the concentrated case,
  plus annulus/pigeonhole assembly.

  Main results:
  - `Line2.ofAffine` — convert an affine subspace with finrank 1 to Line2
  - `finsetAffineToLine2` — convert a finset of affine subspaces to Line2
  - `annulus` — annulus definition
  - `concentrated_annulus_pigeonhole` — combine fix_xi and fix_y
  - `concentrated_contradiction_of_affine` — apply core contradiction
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.ConcentratedCase
public import MyLeanRepo.RadialBootstrapping.ConcentratedContradiction

@[expose] public section


open MeasureTheory Metric Set Finset

noncomputable section

namespace RadialBootstrapping

/-! ============================================================================
    1. Bridge: AffineSubspace → Line2
   ============================================================================ -/

/-- Convert an affine subspace with finrank 1 to a Line2. -/
def Line2.ofAffine (ℓ : AffineSubspace ℝ Point)
    (h : Module.finrank ℝ ℓ.direction = 1) : Line2 :=
  ⟨ℓ, h⟩

@[simp]
lemma Line2.ofAffine_toAffine (ℓ : AffineSubspace ℝ Point)
    (h : Module.finrank ℝ ℓ.direction = 1) :
    (Line2.ofAffine ℓ h).toAffine = ℓ := by
  rfl

/-- Convert a finset of affine subspaces, all with finrank 1, to a finset of Line2. -/
def finsetAffineToLine2 (S : Finset (AffineSubspace ℝ Point))
    (h : ∀ ℓ ∈ S, Module.finrank ℝ ℓ.direction = 1) : Finset Line2 :=
  S.attach.image (fun ⟨ℓ, hℓ⟩ => Line2.ofAffine ℓ (h ℓ hℓ))

lemma finsetAffineToLine2_card (S : Finset (AffineSubspace ℝ Point))
    (h : ∀ ℓ ∈ S, Module.finrank ℝ ℓ.direction = 1) :
    (finsetAffineToLine2 S h).card = S.card := by
  have h_inj : Function.Injective (fun (x : {ℓ // ℓ ∈ S}) => Line2.ofAffine x.val (h x.val x.property)) := by
    intro ⟨ℓ₁, hℓ₁⟩ ⟨ℓ₂, hℓ₂⟩ h_eq
    have h : (Line2.ofAffine ℓ₁ (h ℓ₁ hℓ₁)) = (Line2.ofAffine ℓ₂ (h ℓ₂ hℓ₂)) := h_eq
    have h' : ℓ₁ = ℓ₂ := Subtype.ext_iff.mp h
    exact Subtype.ext h'
  rw [finsetAffineToLine2, Finset.card_image_of_injective _ h_inj]
  <;> simp

lemma finsetAffineToLine2_mem (S : Finset (AffineSubspace ℝ Point))
    (h : ∀ ℓ ∈ S, Module.finrank ℝ ℓ.direction = 1)
    (ℓ : AffineSubspace ℝ Point) (hℓ : ℓ ∈ S) :
    Line2.ofAffine ℓ (h ℓ hℓ) ∈ finsetAffineToLine2 S h := by
  simp only [finsetAffineToLine2, Finset.mem_image]
  refine ⟨⟨ℓ, hℓ⟩, by simpa using hℓ, rfl⟩

/-- Direction separation is preserved under the conversion. -/
lemma finsetAffineToLine2_sep (r ξ : ℝ)
    (S : Finset (AffineSubspace ℝ Point))
    (h : ∀ ℓ ∈ S, Module.finrank ℝ ℓ.direction = 1)
    (h_sep : ∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ →
      submoduleDirDist ℓ₁.direction ℓ₂.direction ≥ r / ξ) :
    ∀ L1 ∈ finsetAffineToLine2 S h, ∀ L2 ∈ finsetAffineToLine2 S h,
      L1 ≠ L2 → lineDirDist L1 L2 ≥ r / ξ := by
  intro L1 hL1 L2 hL2 hne
  rcases Finset.mem_image.mp hL1 with ⟨⟨ℓ₁, hℓ₁⟩, _, rfl⟩
  rcases Finset.mem_image.mp hL2 with ⟨⟨ℓ₂, hℓ₂⟩, _, rfl⟩
  have h_ne : ℓ₁ ≠ ℓ₂ := by
    intro h_eq
    apply hne
    simp [Line2.ofAffine, h_eq]
  exact h_sep ℓ₁ hℓ₁ ℓ₂ hℓ₂ h_ne

/-- Tube membership is preserved under the conversion. -/
lemma finsetAffineToLine2_tube (r : ℝ)
    (S : Finset (AffineSubspace ℝ Point))
    (h : ∀ ℓ ∈ S, Module.finrank ℝ ℓ.direction = 1)
    (ℓ : AffineSubspace ℝ Point) (hℓ : ℓ ∈ S) (x : Point)
    (hx : x ∈ Metric.thickening r (ℓ : Set Point)) :
    x ∈ tube r (Line2.ofAffine ℓ (h ℓ hℓ)) := by
  have h_eq : tube r (Line2.ofAffine ℓ (h ℓ hℓ)) = Metric.thickening r (ℓ : Set Point) := by
    simp [tube, Line2.toSet, Line2.ofAffine] <;> rfl
  rw [h_eq]
  exact hx

/-! ============================================================================
    2. Annulus
   ============================================================================ -/

/-- The annulus `A(y, ξ, 2ξ) = ball(y, 2ξ) \ ball(y, ξ). -/
def annulus (y : Point) (ξ : ℝ) : Set Point :=
  Metric.ball y (2 * ξ) \ Metric.ball y ξ

lemma annulus_mem_iff (y : Point) (ξ : ℝ) (z : Point) :
    z ∈ annulus y ξ ↔ ξ ≤ dist y z ∧ dist y z < 2 * ξ := by
  simp only [annulus, Set.mem_diff, Metric.mem_ball]
  constructor
  · rintro ⟨h1, h2⟩
    have h_ge : ξ ≤ dist z y := le_of_not_gt h2
    have h_lt : dist y z < 2 * ξ := by rw [dist_comm] <;> exact h1
    have h_ge' : ξ ≤ dist y z := by rw [dist_comm] <;> exact h_ge
    exact ⟨h_ge', h_lt⟩
  · rintro ⟨h1, h2⟩
    have h1' : dist z y < 2 * ξ := by rw [dist_comm] <;> exact h2
    have h2' : ¬ dist z y < ξ := by
      rw [dist_comm] at h1
      exact not_lt.mpr h1
    exact ⟨h1', h2'⟩

/-! ============================================================================
    3. Dyadic scales (optional helper)
   ============================================================================ -/

/-- Construct a finite set of dyadic annulus scales between r and r^κ. -/
def dyadicScales (r κ : ℝ) (hr : 0 < r) (hκ : 0 < κ) (N : ℕ) : Finset ℝ :=
  Finset.range (N + 1) |>.image (fun k : ℕ => r * Real.rpow r ((κ - 1) * (k : ℝ) / N))

lemma dyadicScales_bounds (r κ : ℝ) (hr : 0 < r) (hr_lt_one : r < 1)
    (hκ : 0 < κ) (hκ_lt_one : κ < 1) (N : ℕ) (hN_pos : 0 < N) :
    ∀ ξ ∈ dyadicScales r κ hr hκ N, r ≤ ξ ∧ ξ ≤ Real.rpow r κ := by
  intro ξ hξ
  rcases Finset.mem_image.mp hξ with ⟨k, hk, rfl⟩
  have h_k_lt : k < N + 1 := Finset.mem_range.mp hk
  have h_k_le : k ≤ N := by linarith
  set e : ℝ := (κ - 1) * (k : ℝ) / N with he_def
  have hN_pos' : (0 : ℝ) < N := by exact_mod_cast hN_pos
  have h2' : κ - 1 ≤ 0 := by linarith
  have h1 : (k : ℝ) / N ≤ 1 := by
    apply (div_le_one hN_pos').mpr
    exact_mod_cast h_k_le
  have h_nonneg : 0 ≤ (k : ℝ) / N := by positivity
  have h_e1 : κ - 1 ≤ e := by
    have h3 : (κ - 1) * ((k : ℝ) / N) ≥ (κ - 1) * 1 := mul_le_mul_of_nonpos_left h1 h2'
    have h4 : (κ - 1) * ((k : ℝ) / N) = (κ - 1) * (k : ℝ) / N := by ring
    have h5 : (κ - 1) * (1 : ℝ) = κ - 1 := by ring
    rw [h4, h5] at h3
    simpa [he_def] using h3
  have h_e2 : e ≤ 0 := by
    have h3 : (κ - 1) * ((k : ℝ) / N) ≤ (κ - 1) * 0 := mul_le_mul_of_nonpos_left h_nonneg h2'
    have h4 : (κ - 1) * ((k : ℝ) / N) = (κ - 1) * (k : ℝ) / N := by ring
    have h5 : (κ - 1) * (0 : ℝ) = (0 : ℝ) := by ring
    rw [h4, h5] at h3
    simpa [he_def] using h3
  have h_log_r_neg : Real.log r < 0 := Real.log_neg hr hr_lt_one
  have h_rpow_decr : ∀ (x y : ℝ), x ≤ y → Real.rpow r y ≤ Real.rpow r x := by
    intro x y hxy
    have h41 : Real.log (Real.rpow r y) = y * Real.log r := Real.log_rpow hr y
    have h42 : Real.log (Real.rpow r x) = x * Real.log r := Real.log_rpow hr x
    have h5 : 0 < Real.rpow r y := Real.rpow_pos_of_pos hr y
    have h6 : 0 < Real.rpow r x := Real.rpow_pos_of_pos hr x
    have h7 : Real.log (Real.rpow r y) ≤ Real.log (Real.rpow r x) := by
      rw [h41, h42] <;> nlinarith
    exact (Real.log_le_log_iff h5 h6).mp h7
  have h_rpow1 : 1 ≤ Real.rpow r e := by
    have h7 : Real.rpow r e ≥ Real.rpow r 0 := h_rpow_decr e 0 h_e2
    simpa using h7
  have h_rpow2 : Real.rpow r e ≤ Real.rpow r (κ - 1) := h_rpow_decr (κ - 1) e h_e1
  have h_ge : r ≤ r * Real.rpow r e := by
    have h5 : 1 ≤ Real.rpow r e := h_rpow1
    nlinarith [hr]
  have h_rpow_add_eq : r * Real.rpow r (κ - 1) = Real.rpow r κ := by
    have h7 : Real.rpow r 1 * Real.rpow r (κ - 1) = Real.rpow r (1 + (κ - 1)) :=
      (Real.rpow_add hr 1 (κ - 1)).symm
    have h8 : Real.rpow r 1 = r := by simp
    have h9 : 1 + (κ - 1) = κ := by ring
    rw [h8, h9] at h7
    exact h7
  have h_le : r * Real.rpow r e ≤ Real.rpow r κ := by
    calc
      r * Real.rpow r e ≤ r * Real.rpow r (κ - 1) := by gcongr
      _ = Real.rpow r κ := h_rpow_add_eq
  exact ⟨h_ge, h_le⟩

lemma dyadicScales_card (r κ : ℝ) (hr : 0 < r) (hr_lt_one : r < 1)
    (hκ : 0 < κ) (hκ_lt_one : κ < 1) (N : ℕ) (hN_pos : 0 < N) :
    (dyadicScales r κ hr hκ N).card = N + 1 := by
  rw [dyadicScales, Finset.card_image_of_injective]
  · simp
  · intro k1 k2 h
    have h_eq1 : r * Real.rpow r ((κ - 1) * (k1 : ℝ) / N) =
        r * Real.rpow r ((κ - 1) * (k2 : ℝ) / N) := h
    have h_eq2 : Real.rpow r ((κ - 1) * (k1 : ℝ) / N) =
        Real.rpow r ((κ - 1) * (k2 : ℝ) / N) := by
      apply (mul_right_inj' hr.ne').mp
      exact h_eq1
    set e1 := (κ - 1) * (k1 : ℝ) / N with he1_def
    set e2 := (κ - 1) * (k2 : ℝ) / N with he2_def
    have h_log : Real.log (Real.rpow r e1) = Real.log (Real.rpow r e2) := by rw [h_eq2]
    have h_log1 : Real.log (Real.rpow r e1) = e1 * Real.log r := Real.log_rpow hr e1
    have h_log2 : Real.log (Real.rpow r e2) = e2 * Real.log r := Real.log_rpow hr e2
    rw [h_log1, h_log2] at h_log
    have h_log_r_ne_zero : Real.log r ≠ 0 := by
      intro h0
      have h10 : r = 1 := by
        rw [← Real.exp_log hr]
        rw [h0] <;> norm_num
      linarith
    have h_kappa_ne_zero : κ - 1 ≠ 0 := by linarith
    have hN_pos' : (0 : ℝ) < N := by exact_mod_cast hN_pos
    have h_log' : Real.log r * e1 = Real.log r * e2 := by
      have h_comm1 : e1 * Real.log r = Real.log r * e1 := by ring
      have h_comm2 : e2 * Real.log r = Real.log r * e2 := by ring
      rw [h_comm1, h_comm2] at h_log
      exact h_log
    have h_eq : e1 = e2 := by
      apply mul_left_cancel₀ h_log_r_ne_zero
      exact h_log'
    have h_final : (k1 : ℝ) = (k2 : ℝ) := by
      have h_eq' : (κ - 1) * (k1 : ℝ) / N = (κ - 1) * (k2 : ℝ) / N := by
        simpa [he1_def, he2_def] using h_eq
      have h_mult : ((κ - 1) * (k1 : ℝ) / N) * N = ((κ - 1) * (k2 : ℝ) / N) * N := by
        rw [h_eq']
      have h_cancel1 : ((κ - 1) * (k1 : ℝ) / N) * N = (κ - 1) * (k1 : ℝ) := by
        field_simp [hN_pos'.ne'] <;> ring
      have h_cancel2 : ((κ - 1) * (k2 : ℝ) / N) * N = (κ - 1) * (k2 : ℝ) := by
        field_simp [hN_pos'.ne'] <;> ring
      rw [h_cancel1, h_cancel2] at h_mult
      exact mul_left_cancel₀ h_kappa_ne_zero h_mult
    exact_mod_cast h_final

/-! ============================================================================
    4. Combined annulus pigeonhole: fix_xi then fix_y
   ============================================================================ -/

/-- Apply fix_xi and fix_y to find a scale ξ₀ and point y such that the
x-fiber at y has measure at least `r^(8η)`. -/
lemma concentrated_annulus_pigeonhole
    {μ ν : Measure Point} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (r η κ : ℝ)
    (hr : 0 < r)
    (heta : 0 < η)
    (scales : Finset ℝ)
    (h_scales_bounds : ∀ ξ ∈ scales, r ≤ ξ ∧ ξ ≤ Real.rpow r κ)
    (h_scales_card : (scales.card : ℝ) ≤ (1 / 6 : ℝ) * Real.rpow r (-η))
    (H' : Set (Point × Point))
    (hH'_meas : MeasurableSet H')
    (H''_ξ : ℝ → Set (Point × Point))
    (h_partition : H' = ⋃ ξ₀ ∈ scales, H''_ξ ξ₀)
    (h_disj : ∀ ξ₁ ∈ scales, ∀ ξ₂ ∈ scales, ξ₁ ≠ ξ₂ →
      Disjoint (H''_ξ ξ₁) (H''_ξ ξ₂))
    (h_meas : ∀ ξ₀ ∈ scales, MeasurableSet (H''_ξ ξ₀))
    (hH'_ge : (μ.prod ν) H' ≥ ENNReal.ofReal (Real.rpow r (7 * η))) :
    ∃ (ξ₀ : ℝ), ξ₀ ∈ scales ∧ r ≤ ξ₀ ∧ ξ₀ ≤ Real.rpow r κ ∧
      ∃ (y : Point), μ {x : Point | (x, y) ∈ H''_ξ ξ₀} ≥
        ENNReal.ofReal (Real.rpow r (8 * η)) := by
  have h_xi := fix_xi r η κ hr heta scales h_scales_bounds h_scales_card
    H' hH'_meas H''_ξ h_partition h_disj h_meas hH'_ge
  rcases h_xi with ⟨ξ₀, hξ₀_in, hξ₀1, hξ₀2, h_meas_ge⟩
  let c : ENNReal := ENNReal.ofReal (Real.rpow r (8 * η))
  have hc_ne_top : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_y := fix_y (H''_ξ ξ₀) (h_meas ξ₀ hξ₀_in) c hc_ne_top h_meas_ge
  exact ⟨ξ₀, hξ₀_in, hξ₀1, hξ₀2, h_y⟩

/-! ============================================================================
    5. Full concentrated contradiction assembly
   ============================================================================ -/

/-- Apply concentrated_core_contradiction to a family of affine subspaces. -/
lemma concentrated_contradiction_of_affine
    {ν : Measure Point} [IsProbabilityMeasure ν]
    (r η σ ξ C m : ℝ)
    (hr : 0 < r) (hη : 0 < η) (hσ : 0 ≤ σ)
    (hξ : 0 < ξ) (hC : 0 ≤ C) (hm : 0 < m)
    (y : Point)
    (S : Finset (AffineSubspace ℝ Point))
    (h_finrank : ∀ ℓ ∈ S, Module.finrank ℝ ℓ.direction = 1)
    (h_through_y : ∀ ℓ ∈ S, y ∈ Metric.thickening r (ℓ : Set Point))
    (h_sep : ∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ →
      submoduleDirDist ℓ₁.direction ℓ₂.direction ≥ r / ξ)
    (h_small : 2 * r / ξ ≤ 1)
    (h_mass : ∀ ℓ ∈ S, ν (annulus y ξ ∩ Metric.thickening r (ℓ : Set Point)) ≥
      ENNReal.ofReal m)
    (hFrostman : ν (Metric.ball y (2 * ξ)) ≤ ENNReal.ofReal (C * (2 * ξ)))
    (h_count : (S.card : ℝ) * m > 26 * C * ξ) :
    False := by
  let T_y := finsetAffineToLine2 S h_finrank
  have h_card : T_y.card = S.card := finsetAffineToLine2_card S h_finrank
  have h_through_y' : ∀ L ∈ T_y, y ∈ tube r L := by
    intro L hL
    rcases Finset.mem_image.mp hL with ⟨⟨ℓ, hℓ⟩, _, rfl⟩
    exact finsetAffineToLine2_tube r S h_finrank ℓ hℓ y (h_through_y ℓ hℓ)
  have h_sep' : ∀ L1 ∈ T_y, ∀ L2 ∈ T_y, L1 ≠ L2 →
      lineDirDist L1 L2 ≥ r / ξ :=
    finsetAffineToLine2_sep r ξ S h_finrank h_sep
  have h_mass' : ∀ L ∈ T_y, ν (annulus y ξ ∩ tube r L) ≥ ENNReal.ofReal m := by
    intro L hL
    rcases Finset.mem_image.mp hL with ⟨⟨ℓ, hℓ⟩, _, rfl⟩
    have h_eq : annulus y ξ ∩ tube r (Line2.ofAffine ℓ (h_finrank ℓ hℓ)) =
        annulus y ξ ∩ Metric.thickening r (ℓ : Set Point) := by
      simp [tube, Line2.toSet, Line2.ofAffine] <;> rfl
    rw [h_eq]
    exact h_mass ℓ hℓ
  have h_count' : (T_y.card : ℝ) * m > 26 * C * ξ := by
    rw [h_card]
    exact h_count
  exact concentrated_core_contradiction r η σ ξ C m hr hη hσ hξ hC hm y T_y
    h_through_y' h_sep' h_small h_mass' hFrostman h_count'

end RadialBootstrapping
