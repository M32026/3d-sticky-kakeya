import MyLeanRepo.Kakeya.Assouad.WZ1.Statements

/-!
WZ1 Proposition 5: at one caller-selected scale, pass to an extremal
same-family refinement whose full shaded union has the required spatial
ball cover.

The premise is the assembled balanced-cover theorem. Count only active
coarse cells, using the coarse extremal volume upper bound at scale `rho`
and the core's explicit `rho^3 / 1000000` lower bound for each active coarse
cell. Cover each diameter-`2rho` cell by at most eight radius-`rho` balls and
absorb the absolute constant into the loss gap.
-/

namespace Kakeya.Assouad

open MeasureTheory

def spatialCoverPoint (f : Fin 3 → ℝ) : Point3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm f

@[simp] lemma spatialCoverPoint_apply (f : Fin 3 → ℝ) (i : Fin 3) :
    (spatialCoverPoint f) i = f i := by
  simp [spatialCoverPoint, WithLp.equiv_symm_apply]

lemma spatialCover_eightBalls {S : Set Point3} {rho : ℝ} (hrho : 0 < rho)
    (hS_nonempty : S.Nonempty)
    (hS_diam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 2 * rho) :
    ∃ centers : Finset Point3, centers.card ≤ 8 ∧
      ∀ y ∈ S, ∃ x ∈ centers, y ∈ Metric.closedBall x rho := by
  let X k := (fun x : Point3 => x k) '' S
  have hX_nonempty : ∀ k, (X k).Nonempty := by
    intro k
    rcases hS_nonempty with ⟨p, hp⟩
    exact ⟨p k, p, hp, rfl⟩
  have h_bounded_above : ∀ k, BddAbove (X k) := by
    intro k
    rcases hS_nonempty with ⟨p, hp⟩
    refine ⟨p k + 2 * rho, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    have h : ‖(x - p) k‖ ≤ ‖x - p‖ := PiLp.norm_apply_le (x - p) k
    have h2 : |x k - p k| ≤ dist x p := by simpa [dist_eq_norm] using h
    have h3 : dist x p ≤ 2 * rho := hS_diam x hx p hp
    have h4 : |x k - p k| ≤ 2 * rho := by linarith
    have h5 : x k ≤ p k + 2 * rho := by linarith [abs_le.mp h4]
    exact h5
  have h_bounded_below : ∀ k, BddBelow (X k) := by
    intro k
    rcases hS_nonempty with ⟨p, hp⟩
    refine ⟨p k - 2 * rho, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    have h : ‖(x - p) k‖ ≤ ‖x - p‖ := PiLp.norm_apply_le (x - p) k
    have h2 : |x k - p k| ≤ dist x p := by simpa [dist_eq_norm] using h
    have h3 : dist x p ≤ 2 * rho := hS_diam x hx p hp
    have h4 : |x k - p k| ≤ 2 * rho := by linarith
    have h5 : p k - 2 * rho ≤ x k := by linarith [abs_le.mp h4]
    exact h5
  let a k := sInf (X k)
  let b k := sSup (X k)
  have h_ab : ∀ k, a k ≤ b k := by
    intro k
    rcases hX_nonempty k with ⟨u, hu⟩
    have h1 : a k ≤ u := csInf_le (h_bounded_below k) hu
    have h2 : u ≤ b k := le_csSup (h_bounded_above k) hu
    exact le_trans h1 h2
  have h_span : ∀ k, b k - a k ≤ 2 * rho := by
    intro k
    have h1 : ∀ u ∈ X k, ∀ v ∈ X k, u - v ≤ 2 * rho := by
      intro u hu v hv
      rcases hu with ⟨x, hx, rfl⟩
      rcases hv with ⟨y, hy, rfl⟩
      have h2 : ‖(x - y) k‖ ≤ ‖x - y‖ := PiLp.norm_apply_le (x - y) k
      have h3 : |x k - y k| ≤ dist x y := by simpa [dist_eq_norm] using h2
      have h4 : x k - y k ≤ |x k - y k| := le_abs_self _
      have h5 : dist x y ≤ 2 * rho := hS_diam x hx y hy
      linarith
    have h2 : ∀ u ∈ X k, u ≤ a k + 2 * rho := by
      intro u hu
      have h3 : ∀ v ∈ X k, u - 2 * rho ≤ v := by
        intro v hv
        linarith [h1 u hu v hv]
      have h4 : u - 2 * rho ≤ a k := le_csInf (hX_nonempty k) h3
      linarith
    have h5 : b k ≤ a k + 2 * rho := csSup_le (hX_nonempty k) h2
    linarith
  let m k := (a k + b k) / 2
  let center (s : Fin 3 → Bool) : Point3 :=
    spatialCoverPoint fun k =>
      if s k then (a k + 3 * b k) / 4 else (3 * a k + b k) / 4
  let centers : Finset Point3 :=
    (Finset.univ : Finset (Fin 3 → Bool)).image center
  have h_card : centers.card ≤ 8 := by
    have h : centers.card ≤ (Finset.univ : Finset (Fin 3 → Bool)).card :=
      Finset.card_image_le
    simpa using h
  refine ⟨centers, h_card, ?_⟩
  intro y hy
  let s : Fin 3 → Bool := fun k => m k < y k
  have h_y_in : ∀ k, y k ∈ X k := by
    intro k
    exact ⟨y, hy, rfl⟩
  have h1 : ∀ k, a k ≤ y k := by
    intro k
    exact csInf_le (h_bounded_below k) (h_y_in k)
  have h2 : ∀ k, y k ≤ b k := by
    intro k
    exact le_csSup (h_bounded_above k) (h_y_in k)
  have h_main : ∀ k, |y k - (center s) k| ≤ (b k - a k) / 4 := by
    intro k
    have h3 : a k ≤ y k := h1 k
    have h4 : y k ≤ b k := h2 k
    have hm : m k = (a k + b k) / 2 := by rfl
    by_cases h5 : m k < y k
    · have h6 : s k = true := by simp [s, h5]
      have h7 : (center s) k = (a k + 3 * b k) / 4 := by
        rw [show center s =
          spatialCoverPoint (fun k =>
            if s k then (a k + 3 * b k) / 4
            else (3 * a k + b k) / 4) from rfl]
        rw [spatialCoverPoint_apply, h6] <;> simp
      rw [h7, abs_le] <;>
        constructor <;>
          linarith [h_span k, h_ab k, hm, h3, h4]
    · have h5' : y k ≤ m k := by linarith
      have h6 : s k = false := by simp [s, h5'] <;> tauto
      have h7 : (center s) k = (3 * a k + b k) / 4 := by
        rw [show center s =
          spatialCoverPoint (fun k =>
            if s k then (a k + 3 * b k) / 4
            else (3 * a k + b k) / 4) from rfl]
        rw [spatialCoverPoint_apply, h6] <;> simp
      rw [h7, abs_le] <;>
        constructor <;>
          linarith [h_span k, h_ab k, hm, h3, h4]
  have h5 :
      dist y (center s) ^ 2 =
        ∑ k : Fin 3, (y k - (center s) k) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq y (center s)]
    apply Finset.sum_congr rfl
    intro i _
    have h_coord :
        dist (y i) ((center s) i) = |y i - (center s) i| := by
      simp [dist_eq_norm] <;> rfl
    rw [h_coord] <;> simp [sq_abs]
  have h6 :
      ∑ k : Fin 3, (y k - (center s) k) ^ 2 ≤
        ∑ k : Fin 3, ((b k - a k) / 4) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    have h7 : |y i - (center s) i| ≤ (b i - a i) / 4 := h_main i
    have h8 :
        (y i - (center s) i) ^ 2 ≤ ((b i - a i) / 4) ^ 2 := by
      have h9 :
          |y i - (center s) i| ^ 2 ≤ ((b i - a i) / 4) ^ 2 := by
        gcongr
      simpa [sq_abs] using h9
    exact h8
  have h10 : ∀ k, ((b k - a k) / 4) ^ 2 ≤ (rho / 2) ^ 2 := by
    intro k
    have h11 : 0 ≤ b k - a k := by linarith [h_ab k]
    have h12 : (b k - a k) / 4 ≤ rho / 2 := by
      have h13 : b k - a k ≤ 2 * rho := h_span k
      linarith
    have h14 : 0 ≤ (b k - a k) / 4 := by positivity
    have h15 : 0 ≤ rho / 2 := by positivity
    have h16 : |(b k - a k) / 4| ≤ |rho / 2| := by
      rw [abs_of_nonneg h14, abs_of_nonneg h15]
      exact h12
    exact sq_le_sq.mpr h16
  have h9 :
      ∑ k : Fin 3, ((b k - a k) / 4) ^ 2 ≤
        3 * (rho / 2) ^ 2 := by
    calc
      ∑ k : Fin 3, ((b k - a k) / 4) ^ 2
          ≤ ∑ _k : Fin 3, (rho / 2) ^ 2 :=
        Finset.sum_le_sum fun i _ => h10 i
      _ = 3 * (rho / 2) ^ 2 := by
        simp [Finset.sum_const] <;> ring
  have h17 : 3 * (rho / 2) ^ 2 ≤ rho ^ 2 := by
    have h18 : 0 ≤ rho := by linarith
    have h19 : 3 * (rho / 2) ^ 2 = (3 / 4 : ℝ) * rho ^ 2 := by ring
    rw [h19]
    have h20 : (3 / 4 : ℝ) * rho ^ 2 ≤ rho ^ 2 := by
      have h21 : 0 ≤ rho ^ 2 := by positivity
      linarith
    exact h20
  have h11 : dist y (center s) ^ 2 ≤ rho ^ 2 := by
    rw [h5]
    calc
      ∑ k : Fin 3, (y k - (center s) k) ^ 2
          ≤ ∑ k : Fin 3, ((b k - a k) / 4) ^ 2 := h6
      _ ≤ 3 * (rho / 2) ^ 2 := h9
      _ ≤ rho ^ 2 := h17
  have h12 : 0 ≤ dist y (center s) := by positivity
  have h13 : 0 ≤ rho := by linarith
  have h14 : |dist y (center s)| ≤ |rho| := sq_le_sq.mp h11
  have h_dist : dist y (center s) ≤ rho := by
    simpa [abs_of_nonneg h12, abs_of_nonneg h13] using h14
  exact
    ⟨center s,
      Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩,
      h_dist⟩

lemma spatialCover_constantAbsorption (gap C : ℝ)
    (hgap : 0 < gap) (hC : 0 < C) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta, 0 < delta → delta ≤ delta₀ →
        ENNReal.ofReal C ≤ Kakeya.realRpowENN delta (-gap) := by
  let base : ℝ := 1 / C
  have hbase_pos : 0 < base := by positivity
  let exponent : ℝ := 1 / gap
  have hexp_pos : 0 < exponent := by positivity
  let delta₀ : ℝ := min 1 (Real.rpow base exponent)
  have hpos : 0 < Real.rpow base exponent :=
    Real.rpow_pos_of_pos hbase_pos exponent
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_le_one : delta₀ ≤ 1 := min_le_left _ _
  have hle_right : delta₀ ≤ Real.rpow base exponent := min_le_right _ _
  have h_rpow_mul : Real.rpow (Real.rpow base exponent) gap = base := by
    have h_eq1 :
        Real.rpow (Real.rpow base exponent) gap =
          Real.rpow base (exponent * gap) :=
      (Real.rpow_mul hbase_pos.le exponent gap).symm
    rw [h_eq1]
    have h2 : exponent * gap = 1 := by
      simp only [exponent]
      field_simp [hgap.ne']
    rw [h2] <;> simp
  have hmain : ∀ delta, 0 < delta → delta ≤ delta₀ →
      C ≤ Real.rpow delta (-gap) := by
    intro delta hdelta hle
    have h9 : delta ≤ Real.rpow base exponent := hle.trans hle_right
    have h10 :
        Real.rpow delta gap ≤ Real.rpow (Real.rpow base exponent) gap := by
      apply Real.rpow_le_rpow <;> linarith
    rw [h_rpow_mul] at h10
    have h11 : Real.rpow delta gap ≤ base := h10
    have h12 : Real.rpow delta (-gap) = (Real.rpow delta gap)⁻¹ :=
      Real.rpow_neg hdelta.le gap
    have h13 : 0 < Real.rpow delta gap := Real.rpow_pos_of_pos hdelta gap
    have h14 : (Real.rpow delta gap)⁻¹ ≥ C := by
      have h15 : (Real.rpow delta gap)⁻¹ = 1 / Real.rpow delta gap := by
        simp
      rw [h15]
      have h16 : 1 / Real.rpow delta gap ≥ 1 / base := by
        apply one_div_le_one_div_of_le <;> linarith
      have h17 : 1 / base = C := by
        simp only [base]
        field_simp [hC.ne']
      rw [h17] at h16
      exact h16
    rw [h12]
    exact h14
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le_one, ?_⟩
  intro delta hdelta hle
  have h17 : C ≤ Real.rpow delta (-gap) := hmain delta hdelta hle
  simpa [Kakeya.realRpowENN] using ENNReal.ofReal_le_ofReal h17

lemma spatialCover_cellCountBound {n : ℕ} {rho sigma epsilon : ℝ}
    {activeCells : Finset (Fin n)}
    {S : Fin n → Set Point3}
    (hrho : 0 < rho)
    (hdisj : Set.Pairwise (↑activeCells) (fun c d => Disjoint (S c) (S d)))
    (hmeas : ∀ c ∈ activeCells, MeasurableSet (S c))
    (hlower : ∀ c ∈ activeCells,
        Kakeya.realRpowENN rho 3 / 1000000 ≤ volume (S c))
    (hupper : volume (⋃ c ∈ activeCells, S c) ≤
        Kakeya.realRpowENN rho (sigma - epsilon)) :
    (activeCells.card : ENNReal) ≤
      1000000 * Kakeya.realRpowENN rho (sigma - epsilon - 3) := by
  have hsum : volume (⋃ c ∈ activeCells, S c) =
      ∑ c ∈ activeCells, volume (S c) :=
    MeasureTheory.measure_biUnion_finset hdisj hmeas
  set rho3 : ENNReal := Kakeya.realRpowENN rho 3 with hrho3_def
  set target : ENNReal :=
    Kakeya.realRpowENN rho (sigma - epsilon) with htarget_def
  have h_rho3_pos : rho3 ≠ 0 := by
    simp [rho3, Kakeya.realRpowENN] <;> positivity
  have h_rho3_top : rho3 ≠ ⊤ := by
    simp [rho3, Kakeya.realRpowENN]
  have h1 :
      (activeCells.card : ENNReal) * (rho3 / 1000000) ≤
        ∑ c ∈ activeCells, volume (S c) := by
    calc
      (activeCells.card : ENNReal) * (rho3 / 1000000)
          = ∑ _c ∈ activeCells, (rho3 / 1000000) := by
        simp [Finset.sum_const]
      _ ≤ ∑ c ∈ activeCells, volume (S c) :=
        Finset.sum_le_sum fun c hc => hlower c hc
  rw [hsum] at hupper
  have h2 :
      (activeCells.card : ENNReal) * (rho3 / 1000000) ≤ target :=
    h1.trans hupper
  have h_div_mul :
      (rho3 / 1000000) * (1000000 : ENNReal) = rho3 := by
    have h :
        (rho3 / 1000000) * (1000000 : ENNReal) =
          rho3 * ((1000000 : ENNReal)⁻¹ * (1000000 : ENNReal)) := by
      simp only [div_eq_mul_inv] <;> ring
    rw [h]
    have h2 : (1000000 : ENNReal)⁻¹ * (1000000 : ENNReal) = 1 := by
      have h_pos : (0 : ℝ) < 1000000 := by norm_num
      have h_coe : (1000000 : ENNReal) =
          ENNReal.ofReal (1000000 : ℝ) := by
        norm_cast
      rw [h_coe]
      have h_inv :
          (ENNReal.ofReal (1000000 : ℝ))⁻¹ =
            ENNReal.ofReal ((1000000 : ℝ)⁻¹) :=
        (ENNReal.ofReal_inv_of_pos h_pos).symm
      rw [h_inv]
      rw [← ENNReal.ofReal_mul (by positivity)] <;> norm_num
    rw [h2, mul_one]
  have h3 :
      (activeCells.card : ENNReal) * rho3 ≤ 1000000 * target := by
    have h4 :
        ((activeCells.card : ENNReal) * (rho3 / 1000000)) *
            (1000000 : ENNReal) =
          (activeCells.card : ENNReal) * rho3 := by
      rw [mul_assoc, h_div_mul]
    have h5 :
        ((activeCells.card : ENNReal) * (rho3 / 1000000)) *
            (1000000 : ENNReal) ≤
          target * (1000000 : ENNReal) := by
      have h51 :
          (1000000 : ENNReal) *
              ((activeCells.card : ENNReal) * (rho3 / 1000000)) ≤
            (1000000 : ENNReal) * target := by
        gcongr
      have h52 :
          (1000000 : ENNReal) *
              ((activeCells.card : ENNReal) * (rho3 / 1000000)) =
            ((activeCells.card : ENNReal) * (rho3 / 1000000)) *
              (1000000 : ENNReal) := by
        ring
      have h53 :
          (1000000 : ENNReal) * target =
            target * (1000000 : ENNReal) := by
        ring
      rw [h52, h53] at h51
      exact h51
    rw [h4] at h5
    simpa [mul_comm] using h5
  have h6 :
      (activeCells.card : ENNReal) ≤ (1000000 * target) / rho3 := by
    have h7 :
        ((activeCells.card : ENNReal) * rho3) / rho3 ≤
          (1000000 * target) / rho3 := by
      gcongr
    have h8 :
        ((activeCells.card : ENNReal) * rho3) / rho3 =
          (activeCells.card : ENNReal) := by
      have h9 :
          ((activeCells.card : ENNReal) * rho3) / rho3 =
            (activeCells.card : ENNReal) * (rho3 / rho3) := by
        simp only [mul_div]
      rw [h9]
      have h10 : rho3 / rho3 = 1 := by
        apply ENNReal.div_self <;> tauto
      rw [h10, mul_one]
    rw [h8] at h7
    exact h7
  have h9 :
      (1000000 * target) / rho3 =
        1000000 *
          Kakeya.realRpowENN rho (sigma - epsilon - 3) := by
    have h10 :
        target / rho3 =
          Kakeya.realRpowENN rho (sigma - epsilon - 3) := by
      simp only [target, rho3, Kakeya.realRpowENN]
      rw [div_eq_mul_inv]
      have h_pos2 : 0 < Real.rpow rho 3 :=
        Real.rpow_pos_of_pos hrho 3
      have h_inv :
          (ENNReal.ofReal (Real.rpow rho 3))⁻¹ =
            ENNReal.ofReal ((Real.rpow rho 3)⁻¹) := by
        rw [ENNReal.ofReal_inv_of_pos h_pos2]
      rw [h_inv]
      have h_eq :
          Real.rpow rho (sigma - epsilon - 3) =
            Real.rpow rho (sigma - epsilon) *
              (Real.rpow rho 3)⁻¹ := by
        have h_sub :
            Real.rpow rho (sigma - epsilon - 3) =
              Real.rpow rho (sigma - epsilon) / Real.rpow rho 3 :=
          Real.rpow_sub hrho (sigma - epsilon) 3
        rw [h_sub, div_eq_mul_inv]
      rw [h_eq]
      have h_nonneg1 : 0 ≤ Real.rpow rho (sigma - epsilon) :=
        Real.rpow_nonneg hrho.le _
      have h_nonneg2 : 0 ≤ (Real.rpow rho 3)⁻¹ := by positivity
      rw [← ENNReal.ofReal_mul h_nonneg1] <;> rfl
    have h12 :
        (1000000 * target) / rho3 =
          1000000 * (target / rho3) := by
      simp only [mul_div]
    rw [h12, h10]
  rw [h9] at h6
  exact h6

lemma spatialCover_cellCover
    {delta sigma epsilon outputLoss scaleLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData (sigma := sigma) (epsilon := epsilon) U Y rho)
    (hsigma : 0 < sigma)
    (hepsilon : 0 < epsilon)
    (hscaleLoss : 0 < scaleLoss)
    (hepsilon_le_scale : epsilon ≤ scaleLoss)
    (hgap_absorb :
      (8 * 1000000 : ENNReal) ≤
        Kakeya.realRpowENN delta (-outputLoss) *
          Kakeya.realRpowENN rho.1 epsilon) :
    CanCoverByBalls balanced.refined.union rho.1
      (Kakeya.realRpowENN delta (-outputLoss) *
        Kakeya.realRpowENN rho.1 (-3 + sigma)) := by
  classical
  let n := balanced.cellCount
  let S (c : Fin n) : Set Point3 :=
    {p | p ∈ balanced.coarseShading.union ∧ balanced.cell p = c}
  let activeCells : Finset (Fin n) :=
    Finset.univ.filter (fun c => (S c).Nonempty)
  have hrho_pos : 0 < rho.1 := by
    have h : delta ≤ rho.1 := rho.2.1
    have hdelta_pos : 0 < delta := balanced.refined_extremal.1
    linarith
  have h_coarse_union_meas :
      MeasurableSet balanced.coarseShading.union := by
    have h1 :
        balanced.coarseShading.union =
          ⋃ i : Fin (U.coarse rho).card,
            balanced.coarseShading.carrier i := by
      ext x
      simp [Kakeya.Streamlined.Shading.union] <;> aesop
    rw [h1]
    apply MeasurableSet.iUnion
    intro i
    exact balanced.coarseShading.measurable_carrier i
  have hmeas : ∀ c ∈ activeCells, MeasurableSet (S c) := by
    intro c _
    have h21 :
        {p : Point3 | balanced.cell p = c} = balanced.cell ⁻¹' {c} := by
      ext x <;> simp
    have h2 : MeasurableSet {p : Point3 | balanced.cell p = c} := by
      rw [h21]
      exact balanced.cell_measurable (measurableSet_singleton c)
    exact h_coarse_union_meas.inter h2
  have hdisj :
      Set.Pairwise (↑activeCells) (fun c d => Disjoint (S c) (S d)) := by
    intro c _ d _ hne
    refine Set.disjoint_left.mpr fun x hx1 hx2 => ?_
    have h3 : balanced.cell x = c := hx1.2
    have h4 : balanced.cell x = d := hx2.2
    exact hne (h3.symm.trans h4)
  have hlower : ∀ c ∈ activeCells,
      Kakeya.realRpowENN rho.1 3 / 1000000 ≤ volume (S c) := by
    intro c hc
    have hnonempty : (S c).Nonempty := (Finset.mem_filter.mp hc).2
    exact balanced.coarse_cell_volume_lower c hnonempty
  have hunion_subset :
      (⋃ c ∈ activeCells, S c) ⊆ balanced.coarseShading.union := by
    intro x hx
    have h_exists :
        ∃ c : Fin n, c ∈ activeCells ∧ x ∈ S c := by
      simpa [Finset.mem_biUnion] using hx
    rcases h_exists with ⟨c, _hc, hxc⟩
    exact hxc.1
  have h_coarse_vol_upper :
      volume balanced.coarseShading.union ≤
        Kakeya.realRpowENN rho.1 (sigma - epsilon) := by
    rcases balanced.coarse_extremal with
      ⟨_, _, _, _, _, _, _, _, h, _⟩
    exact h
  have hupper :
      volume (⋃ c ∈ activeCells, S c) ≤
        Kakeya.realRpowENN rho.1 (sigma - epsilon) :=
    (measure_mono hunion_subset).trans h_coarse_vol_upper
  have hcard :
      (activeCells.card : ENNReal) ≤
        1000000 *
          Kakeya.realRpowENN rho.1 (sigma - epsilon - 3) :=
    spatialCover_cellCountBound hrho_pos hdisj hmeas hlower hupper
  have h_eight :
      ∀ c ∈ activeCells, ∃ centers : Finset Point3,
        centers.card ≤ 8 ∧
          ∀ y ∈ S c, ∃ x ∈ centers,
            y ∈ Metric.closedBall x rho.1 := by
    intro c hc
    have hnonempty : (S c).Nonempty := (Finset.mem_filter.mp hc).2
    have hdiam :
        ∀ x ∈ S c, ∀ y ∈ S c, dist x y ≤ 2 * rho.1 := by
      intro x hx y hy
      exact
        balanced.cell_diameter x hx.1 y hy.1
          (by simp [S, hx.2, hy.2])
    exact spatialCover_eightBalls hrho_pos hnonempty hdiam
  choose centers hcenters_card hcenters_cover using h_eight
  let centers' (c : Fin n) : Finset Point3 :=
    if h : c ∈ activeCells then centers c h else ∅
  let allCenters := activeCells.biUnion centers'
  have h_all_card : allCenters.card ≤ 8 * activeCells.card := by
    calc
      allCenters.card
          ≤ ∑ c ∈ activeCells, (centers' c).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ c ∈ activeCells, 8 := by
        apply Finset.sum_le_sum
        intro c hc
        have h_eq : centers' c = centers c hc := by
          simp [centers', hc]
        rw [h_eq]
        exact hcenters_card c hc
      _ = 8 * activeCells.card := by
        simp [Finset.sum_const] <;> ring
  have h_cover_coarse :
      ∀ y ∈ balanced.coarseShading.union,
        ∃ x ∈ allCenters, y ∈ Metric.closedBall x rho.1 := by
    intro y hy
    let c : Fin n := balanced.cell y
    have hc_active : c ∈ activeCells := by
      simp only [activeCells, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨y, hy, rfl⟩
    have hy_in_S : y ∈ S c := by
      simp only [S, Set.mem_setOf_eq]
      exact ⟨hy, rfl⟩
    rcases hcenters_cover c hc_active y hy_in_S with
      ⟨x, hx, hball⟩
    have h_x_in : x ∈ allCenters := by
      apply Finset.mem_biUnion.mpr
      exact
        ⟨c, hc_active,
          by simpa [centers', hc_active] using hx⟩
    exact ⟨x, h_x_in, hball⟩
  have h_refined_subset :
      balanced.refined.union ⊆ balanced.coarseShading.union := by
    intro p hp
    rcases hp with ⟨i, hpi⟩
    have h_in_carrier :
        p ∈ balanced.coarseShading.carrier ((U.cover rho).parent i) :=
      balanced.point_compatibility i p hpi
    exact ⟨(U.cover rho).parent i, h_in_carrier⟩
  have h_final_ineq :
      (8 * 1000000 : ENNReal) *
          Kakeya.realRpowENN rho.1 (sigma - epsilon - 3) ≤
        Kakeya.realRpowENN delta (-outputLoss) *
          Kakeya.realRpowENN rho.1 (-3 + sigma) := by
    have h1 :
        (8 * 1000000 : ENNReal) *
            Kakeya.realRpowENN rho.1 (sigma - epsilon - 3) ≤
          (Kakeya.realRpowENN delta (-outputLoss) *
              Kakeya.realRpowENN rho.1 epsilon) *
            Kakeya.realRpowENN rho.1 (sigma - epsilon - 3) := by
      gcongr
    have h_rho_add :
        Kakeya.realRpowENN rho.1 epsilon *
            Kakeya.realRpowENN rho.1 (sigma - epsilon - 3) =
          Kakeya.realRpowENN rho.1
            (epsilon + (sigma - epsilon - 3)) := by
      simp only [Kakeya.realRpowENN]
      have hpos1 : 0 ≤ Real.rpow rho.1 epsilon :=
        Real.rpow_nonneg hrho_pos.le _
      rw [← ENNReal.ofReal_mul hpos1]
      have h_add :
          Real.rpow rho.1 epsilon *
              Real.rpow rho.1 (sigma - epsilon - 3) =
            Real.rpow rho.1 (epsilon + (sigma - epsilon - 3)) :=
        (Real.rpow_add hrho_pos epsilon
          (sigma - epsilon - 3)).symm
      rw [h_add]
    have h2 :
        (Kakeya.realRpowENN delta (-outputLoss) *
              Kakeya.realRpowENN rho.1 epsilon) *
            Kakeya.realRpowENN rho.1 (sigma - epsilon - 3) =
          Kakeya.realRpowENN delta (-outputLoss) *
            Kakeya.realRpowENN rho.1
              (epsilon + (sigma - epsilon - 3)) := by
      rw [mul_assoc, h_rho_add] <;> ring
    rw [h2] at h1
    have h3 : epsilon + (sigma - epsilon - 3) = -3 + sigma := by
      ring
    rw [h3] at h1
    exact h1
  have h_final_card :
      (allCenters.card : ENNReal) ≤
        Kakeya.realRpowENN delta (-outputLoss) *
          Kakeya.realRpowENN rho.1 (-3 + sigma) := by
    calc
      (allCenters.card : ENNReal)
          ≤ (8 * activeCells.card : ENNReal) := by
        exact_mod_cast h_all_card
      _ = (8 : ENNReal) * (activeCells.card : ENNReal) := by
        simp [mul_comm] <;> ring
      _ ≤ (8 : ENNReal) *
          (1000000 *
            Kakeya.realRpowENN rho.1 (sigma - epsilon - 3)) := by
        gcongr
      _ = (8 * 1000000 : ENNReal) *
          Kakeya.realRpowENN rho.1 (sigma - epsilon - 3) := by
        ring
      _ ≤ Kakeya.realRpowENN delta (-outputLoss) *
          Kakeya.realRpowENN rho.1 (-3 + sigma) :=
        h_final_ineq
  exact
    ⟨allCenters, h_final_card,
      fun y hy => h_cover_coarse y (h_refined_subset hy)⟩

theorem wz1_proposition5_spatial_cover :
    WZ1Proposition5SpatialCoverStatement := by
  intro balanced_cover
  intro sigma hsigma1 hsigma2 hcritical
  intro outputLoss scaleLoss houtputLoss hscaleLoss
  let epsilon := min scaleLoss outputLoss / 2
  have hepsilon_pos : 0 < epsilon := by
    dsimp only [epsilon] <;> positivity
  have hepsilon_lt_scale : epsilon < scaleLoss := by
    dsimp only [epsilon]
    have h : min scaleLoss outputLoss ≤ scaleLoss := min_le_left _ _
    have h' : 0 < min scaleLoss outputLoss := by positivity
    linarith
  have hepsilon_lt_output : epsilon < outputLoss := by
    dsimp only [epsilon]
    have h : min scaleLoss outputLoss ≤ outputLoss := min_le_right _ _
    have h' : 0 < min scaleLoss outputLoss := by positivity
    linarith
  have hepsilon_le_scale : epsilon ≤ scaleLoss := by linarith
  have hepsilon_le_output : epsilon ≤ outputLoss := by linarith
  rcases
      balanced_cover sigma hsigma1 hsigma2 hcritical epsilon hepsilon_pos with
    ⟨eta, delta₀_bal, heta_pos, hdelta₀_bal_pos,
      hdelta₀_bal_one, hbalanced⟩
  let inputLoss := min eta outputLoss
  have hinput_pos : 0 < inputLoss := by
    dsimp only [inputLoss] <;> positivity
  have hinput_le_output : inputLoss ≤ outputLoss := by
    dsimp only [inputLoss]
    exact min_le_right _ _
  have hinput_le_eta : inputLoss ≤ eta := by
    dsimp only [inputLoss]
    exact min_le_left _ _
  let gap := outputLoss - epsilon * (1 - scaleLoss)
  have hgap_pos : 0 < gap := by
    dsimp only [gap]
    have h1 : epsilon * (1 - scaleLoss) < epsilon := by
      have h2 : 1 - scaleLoss < 1 := by linarith
      have h3 : 0 ≤ epsilon := by linarith
      nlinarith
    linarith [hepsilon_lt_output]
  rcases
      spatialCover_constantAbsorption gap (8 * 1000000)
        hgap_pos (by norm_num) with
    ⟨delta₀_const, hdelta₀_const_pos, hdelta₀_const_one,
      hconst_absorb⟩
  let delta₀ := min delta₀_bal delta₀_const
  have hdelta₀_pos : 0 < delta₀ := by
    dsimp only [delta₀] <;> positivity
  have hdelta₀_one : delta₀ ≤ 1 := by
    dsimp only [delta₀]
    exact le_trans (min_le_left _ _) hdelta₀_bal_one
  refine
    ⟨inputLoss, delta₀, hinput_pos, hinput_le_output,
      hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta hdelta hdelta₀
  intro F U Y hextremal rho hrho_lower hrho_upper
  have hdelta_bal : delta ≤ delta₀_bal :=
    le_trans hdelta₀ (min_le_left delta₀_bal delta₀_const)
  have hdelta_const : delta ≤ delta₀_const :=
    le_trans hdelta₀ (min_le_right delta₀_bal delta₀_const)
  have h_wz1 : WZ1ExtremalPair sigma inputLoss F U Y :=
    hextremal.toWZ1
  have h_eta : WZ1ExtremalPair sigma eta F U Y :=
    h_wz1.mono_epsilon hinput_le_eta
  have hdelta_le_one : delta ≤ 1 :=
    le_trans hdelta₀ hdelta₀_one
  have hrho_lower' : Real.rpow delta (1 - epsilon) ≤ rho.1 := by
    have h1 : 1 - scaleLoss ≤ 1 - epsilon := by linarith
    have h2 :
        Real.rpow delta (1 - epsilon) ≤
          Real.rpow delta (1 - scaleLoss) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_le_one h1
    exact le_trans h2 hrho_lower
  have hrho_upper' : rho.1 ≤ Real.rpow delta epsilon := by
    have h2 :
        Real.rpow delta scaleLoss ≤ Real.rpow delta epsilon :=
      Real.rpow_le_rpow_of_exponent_ge
        hdelta hdelta_le_one hepsilon_le_scale
    exact le_trans hrho_upper h2
  rcases
      hbalanced delta hdelta hdelta_bal F U Y h_eta rho
        hrho_lower' hrho_upper' with
    ⟨balanced⟩
  have h_refined_extremal :
      WZ1ExtremalPair sigma outputLoss F U balanced.refined :=
    balanced.refined_extremal.mono_epsilon hepsilon_le_output
  have hconst :
      (8 * 1000000 : ENNReal) ≤
        Kakeya.realRpowENN delta (-gap) := by
    have h := hconst_absorb delta hdelta hdelta_const
    simpa using h
  have h_rho_eps :
      Kakeya.realRpowENN delta (epsilon * (1 - scaleLoss)) ≤
        Kakeya.realRpowENN rho.1 epsilon := by
    have h1 : Real.rpow delta (1 - scaleLoss) ≤ rho.1 := hrho_lower
    have h2 : 0 ≤ epsilon := by linarith
    have h1' : 0 ≤ Real.rpow delta (1 - scaleLoss) :=
      Real.rpow_nonneg hdelta.le _
    have h3 :
        (Real.rpow delta (1 - scaleLoss)) ^ epsilon ≤
          (rho.1) ^ epsilon :=
      Real.rpow_le_rpow h1' h1 h2
    have h4 :
        (Real.rpow delta (1 - scaleLoss)) ^ epsilon =
          delta ^ (epsilon * (1 - scaleLoss)) := by
      have h5 :
          delta ^ ((1 - scaleLoss) * epsilon) =
            (delta ^ (1 - scaleLoss)) ^ epsilon :=
        Real.rpow_mul hdelta.le (1 - scaleLoss) epsilon
      have h6 :
          (1 - scaleLoss) * epsilon =
            epsilon * (1 - scaleLoss) := by
        ring
      exact h5.symm ▸ by rw [h6]
    rw [h4] at h3
    simpa [Kakeya.realRpowENN] using ENNReal.ofReal_le_ofReal h3
  have hgap_exponent :
      -gap = -outputLoss + epsilon * (1 - scaleLoss) := by
    simp [gap] <;> ring
  have hgap_absorb_ennreal :
      (8 * 1000000 : ENNReal) ≤
        Kakeya.realRpowENN delta (-outputLoss) *
          Kakeya.realRpowENN rho.1 epsilon := by
    have h1 :
        (8 * 1000000 : ENNReal) ≤
          Kakeya.realRpowENN delta (-gap) := hconst
    rw [hgap_exponent] at h1
    have h2 :
        Kakeya.realRpowENN delta
            (-outputLoss + epsilon * (1 - scaleLoss)) =
          Kakeya.realRpowENN delta (-outputLoss) *
            Kakeya.realRpowENN delta
              (epsilon * (1 - scaleLoss)) := by
      simp only [Kakeya.realRpowENN]
      have hpos1 : 0 ≤ Real.rpow delta (-outputLoss) :=
        Real.rpow_nonneg hdelta.le _
      rw [← ENNReal.ofReal_mul hpos1]
      have h_add :
          Real.rpow delta (-outputLoss) *
              Real.rpow delta (epsilon * (1 - scaleLoss)) =
            Real.rpow delta
              (-outputLoss + epsilon * (1 - scaleLoss)) :=
        (Real.rpow_add hdelta (-outputLoss)
          (epsilon * (1 - scaleLoss))).symm
      rw [h_add]
    rw [h2] at h1
    have h3 :
        Kakeya.realRpowENN delta (-outputLoss) *
            Kakeya.realRpowENN delta (epsilon * (1 - scaleLoss)) ≤
          Kakeya.realRpowENN delta (-outputLoss) *
            Kakeya.realRpowENN rho.1 epsilon := by
      gcongr
    exact h1.trans h3
  have h_spatial :
      CanCoverByBalls balanced.refined.union rho.1
        (Kakeya.realRpowENN delta (-outputLoss) *
          Kakeya.realRpowENN rho.1 (-3 + sigma)) :=
    spatialCover_cellCover balanced hsigma1 hepsilon_pos hscaleLoss
      hepsilon_le_scale hgap_absorb_ennreal
  exact
    ⟨balanced.refined, balanced.subshading,
      h_refined_extremal, h_spatial⟩

end Kakeya.Assouad
