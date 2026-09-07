import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDotSpreadGeometricLemmas
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDotSpreadExponentBound
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDotSpreadCountingHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDotSpreadPointPigeonhole
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDotSpreadConcentrationStatements

/-!
# Spread branch for the narrow dot-spread proof

Given a fixed edge `(a₀, b₁⁰, b₂⁰) ∈ H`, pigeonhole the G₁-fiber over
`(a₀, b₂⁰)` longitudinally, then apply a dot-value dichotomy.

Either:
- **Spread**: enough pairwise `>2δ`-separated dot-difference values to satisfy
  `WZ1Proposition8_9NarrowDotSpreadData`.
- **Concentrate**: a G₁ subset of size `≥ δ^(ε-1)` lies in a single transverse
  `δ`-strip, providing the G₁ half of Alternative A.
-/

namespace Kakeya.Assouad

open scoped ENNReal

attribute [local instance] Classical.propDecidable

/--
Eight transverse cells of width `2 * delta` cover a set whose transverse
coordinates remain within `15 * delta / 2` of one anchor.  One cell therefore
retains twice the paper-scale cardinality and lies in one transverse
`delta`-strip.
-/
lemma transverse_eight_cell_pigeonhole
    {delta epsilon : ℝ}
    {points : Finset Point2}
    {anchor direction : Point2}
    (hdelta : 0 < delta)
    (hdirection : ‖direction‖ = 1)
    (hcard :
      (points.card : ℝ) ≥
        16 * Real.rpow delta (epsilon - 1))
    (htransverse :
      ∀ point ∈ points,
        |inner ℝ (point - anchor) (wz1Perp2 direction)| ≤
          15 * delta / 2) :
    ∃ concentrated : Finset Point2,
      concentrated ⊆ points ∧
      (concentrated.card : ℝ) ≥
        2 * Real.rpow delta (epsilon - 1) ∧
      ∃ base : Point2,
        ∀ point ∈ concentrated,
          point ∈ wz1LineNeighborhood base direction delta := by
  let anchorCoordinate : ℝ :=
    inner ℝ anchor (wz1Perp2 direction)
  let cellOf : Point2 → ℕ := fun point =>
    Nat.floor
      ((inner ℝ point (wz1Perp2 direction) -
          (anchorCoordinate - 15 * delta / 2)) /
        (2 * delta))
  let cellPoints : ℕ → Finset Point2 := fun index =>
    points.filter (fun point => cellOf point = index)
  let cells : Finset ℕ := Finset.range 8
  have hcellRange :
      ∀ point ∈ points, cellOf point < 8 := by
    intro point hpoint
    have hcoordinate :
        |inner ℝ point (wz1Perp2 direction) -
            anchorCoordinate| ≤
          15 * delta / 2 := by
      have hbound := htransverse point hpoint
      simpa [anchorCoordinate, inner_sub_left] using hbound
    have hlower :
        anchorCoordinate - 15 * delta / 2 ≤
          inner ℝ point (wz1Perp2 direction) := by
      linarith [abs_le.mp hcoordinate]
    have hupper :
        inner ℝ point (wz1Perp2 direction) ≤
          anchorCoordinate + 15 * delta / 2 := by
      linarith [abs_le.mp hcoordinate]
    have hnonnegative :
        0 ≤
          (inner ℝ point (wz1Perp2 direction) -
              (anchorCoordinate - 15 * delta / 2)) /
            (2 * delta) := by
      exact div_nonneg (by linarith) (by positivity)
    have hquotient :
        (inner ℝ point (wz1Perp2 direction) -
              (anchorCoordinate - 15 * delta / 2)) /
            (2 * delta) ≤
          15 / 2 := by
      have hnumerator :
          inner ℝ point (wz1Perp2 direction) -
              (anchorCoordinate - 15 * delta / 2) ≤
            15 * delta := by
        linarith
      calc
        (inner ℝ point (wz1Perp2 direction) -
              (anchorCoordinate - 15 * delta / 2)) /
              (2 * delta) ≤
            (15 * delta) / (2 * delta) := by
          gcongr
        _ = 15 / 2 := by
          field_simp [hdelta.ne']
    have hfloor :
        cellOf point ≤ 7 := by
      have hfloorReal :
          (cellOf point : ℝ) ≤
            (inner ℝ point (wz1Perp2 direction) -
                (anchorCoordinate - 15 * delta / 2)) /
              (2 * delta) :=
        Nat.floor_le hnonnegative
      have hstrict : (cellOf point : ℝ) < 8 := by
        exact (hfloorReal.trans hquotient).trans_lt (by norm_num)
      have hlt : cellOf point < 8 := by
        exact_mod_cast hstrict
      omega
    exact Nat.lt_succ_iff.mpr hfloor
  have hmaps :
      ∀ point ∈ points, cellOf point ∈ cells := by
    intro point hpoint
    simpa [cells] using hcellRange point hpoint
  have hcellsNonempty : cells.Nonempty := by
    simp [cells]
  rcases finset_pigeonhole hmaps hcellsNonempty with
    ⟨index, _, hindexCard⟩
  have hcellCard :
      2 * Real.rpow delta (epsilon - 1) ≤
        (cellPoints index).card := by
    have hpointsUpper :
        (points.card : ℝ) ≤
          8 * (cellPoints index).card := by
      have hcellsCard : (cells.card : ℝ) = 8 := by
        simp [cells]
      simpa [cellPoints, hcellsCard] using hindexCard
    calc
      2 * Real.rpow delta (epsilon - 1) =
          (16 * Real.rpow delta (epsilon - 1)) / 8 := by
        ring
      _ ≤ (points.card : ℝ) / 8 := by
        gcongr
      _ ≤ (cellPoints index).card := by
        apply
          (div_le_iff₀
            (by norm_num : (0 : ℝ) < 8)).2
        simpa [mul_comm] using hpointsUpper
  let concentrated : Finset Point2 := cellPoints index
  have hsubset : concentrated ⊆ points := by
    intro point hpoint
    exact (Finset.mem_filter.mp hpoint).1
  let centerCoordinate : ℝ :=
    anchorCoordinate - 15 * delta / 2 +
      (index : ℝ) * (2 * delta) + delta
  let base : Point2 :=
    centerCoordinate • wz1Perp2 direction
  have hperpendicularNorm :
      ‖wz1Perp2 direction‖ = 1 := by
    have hnorm :
        ‖wz1Perp2 direction‖ ^ 2 =
          (wz1Perp2 direction) 0 ^ 2 +
            (wz1Perp2 direction) 1 ^ 2 :=
      norm2_sq (wz1Perp2 direction)
    have hdirectionSquare :
        ‖direction‖ ^ 2 =
          direction 0 ^ 2 + direction 1 ^ 2 :=
      norm2_sq direction
    rw [hdirection] at hdirectionSquare
    have hcoordinates := wz1Perp2_coords direction
    rw [hcoordinates.1, hcoordinates.2] at hnorm
    nlinarith [norm_nonneg (wz1Perp2 direction)]
  refine ⟨concentrated, hsubset, hcellCard, base, ?_⟩
  intro point hpoint
  have hpointSource : point ∈ points := hsubset hpoint
  have hindex :
      cellOf point = index :=
    (Finset.mem_filter.mp hpoint).2
  have hcoordinate :
      |inner ℝ point (wz1Perp2 direction) -
          anchorCoordinate| ≤
        15 * delta / 2 := by
    have hbound := htransverse point hpointSource
    simpa [anchorCoordinate, inner_sub_left] using hbound
  have hnonnegative :
      0 ≤
        (inner ℝ point (wz1Perp2 direction) -
            (anchorCoordinate - 15 * delta / 2)) /
          (2 * delta) := by
    exact div_nonneg
      (by linarith [abs_le.mp hcoordinate]) (by positivity)
  have hlower :
      (index : ℝ) * (2 * delta) ≤
        inner ℝ point (wz1Perp2 direction) -
          (anchorCoordinate - 15 * delta / 2) := by
    have hfloor :
        (cellOf point : ℝ) ≤
          (inner ℝ point (wz1Perp2 direction) -
              (anchorCoordinate - 15 * delta / 2)) /
            (2 * delta) :=
      Nat.floor_le hnonnegative
    rw [hindex] at hfloor
    calc
      (index : ℝ) * (2 * delta) ≤
          ((inner ℝ point (wz1Perp2 direction) -
              (anchorCoordinate - 15 * delta / 2)) /
            (2 * delta)) * (2 * delta) := by
        gcongr
      _ =
          inner ℝ point (wz1Perp2 direction) -
            (anchorCoordinate - 15 * delta / 2) := by
        field_simp [hdelta.ne']
  have hupper :
      inner ℝ point (wz1Perp2 direction) -
          (anchorCoordinate - 15 * delta / 2) <
        ((index : ℝ) + 1) * (2 * delta) := by
    have hfloor :
        (inner ℝ point (wz1Perp2 direction) -
              (anchorCoordinate - 15 * delta / 2)) /
            (2 * delta) <
          (cellOf point : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    rw [hindex] at hfloor
    calc
      inner ℝ point (wz1Perp2 direction) -
            (anchorCoordinate - 15 * delta / 2) =
          ((inner ℝ point (wz1Perp2 direction) -
              (anchorCoordinate - 15 * delta / 2)) /
            (2 * delta)) * (2 * delta) := by
        field_simp [hdelta.ne']
      _ < ((index : ℝ) + 1) * (2 * delta) := by
        gcongr
  have hdistance :
      |inner ℝ point (wz1Perp2 direction) -
          centerCoordinate| ≤
        delta := by
    dsimp only [centerCoordinate]
    rw [show
      inner ℝ point (wz1Perp2 direction) -
            (anchorCoordinate - 15 * delta / 2 +
              (index : ℝ) * (2 * delta) + delta) =
          inner ℝ point (wz1Perp2 direction) -
            (anchorCoordinate - 15 * delta / 2) -
              (index : ℝ) * (2 * delta) - delta by
      ring]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hself :
      inner ℝ (wz1Perp2 direction)
          (wz1Perp2 direction) = 1 := by
    rw [real_inner_self_eq_norm_sq, hperpendicularNorm]
    norm_num
  have hinner :
      inner ℝ (point - base) (wz1Perp2 direction) =
        inner ℝ point (wz1Perp2 direction) -
          centerCoordinate := by
    rw [inner_sub_left]
    rw [show base =
      centerCoordinate • wz1Perp2 direction by rfl,
      inner_smul_left, hself]
    simp
  change
    |inner ℝ (point - base) (wz1Perp2 direction)| ≤
      delta
  rw [hinner]
  exact hdistance

/--
The spread branch: from a fixed edge, either produce dot-spread data or a
concentrated G₁ subset in a transverse δ-strip.
-/
lemma narrow_dot_spread_spread_branch
    {delta epsilon eta workingLambda width : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {direction base : Point2}
    (hdirection : ‖direction‖ = 1)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon < 1)
    (heta : 0 < eta)
    (hworkingLambda_pos : 0 < workingLambda)
    (hworkingLambda : workingLambda ≤ epsilon / 100)
    (hetaCap : eta ≤ epsilon / 20)
    (hwidth_pos : 0 < width)
    (hwidth_small : width ≤ 1 / 4)
    (hdelta_le_width : delta ≤ width)
    (hnarrow : width ≤ Real.rpow delta (1 - epsilon / 10))
    (hG1_ball : G₁.IsInUnitBall)
    (hG2_ball : G₂.IsInUnitBall)
    (hF_ball : F.IsInUnitBall)
    (hG1_sep : G₁.IsDeltaSeparated delta)
    (hG1_frostman : G₁.IsFrostman delta 1
        (Kakeya.realRpowENN delta (-workingLambda)))
    (h_standardF : ∀ a ∈ F, 1 / 2 ≤ dist a 0)
    (h_orthogonal : ∀ a ∈ F,
        a ∈ wz1LineNeighborhood 0 (wz1Perp2 direction) width)
    (h_common1 : ∀ b ∈ G₁,
        b ∈ wz1LineNeighborhood base direction width)
    (h_common2 : ∀ b ∈ G₂,
        b ∈ wz1LineNeighborhood base direction width)
    {c : ENNReal}
    (hc : c = (1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta)
    (hdensity : WZ1UniformTripleDensity c F G₁ G₂ H)
    (a0 : Point2) (ha0_in_F : a0 ∈ F)
    (b10 : Point2) (hb10_in_G1 : b10 ∈ G₁)
    (b20 : Point2) (hb20_in_G2 : b20 ∈ G₂)
    (h_edge : (a0, b10, b20) ∈ H)
    (hsmall :
      (1200000 : ℝ) *
          Real.rpow delta (7 * epsilon / 10) ≤ 1) :
    Nonempty (WZ1Proposition8_9NarrowDotSpreadData delta epsilon eta H) ∨
    ∃ concentration :
        NarrowDotSpreadG1Concentrated
          delta epsilon width F G₁ G₂ H direction,
      concentration.AnchoredAt a0 b20 := by
  -- Step 1: Second fiber S = {b1 : (a0, b1, b20) ∈ H}
  let S : Finset Point2 := kaufmanSecondFiber H a0 b20
  have hS_nonempty : S.Nonempty := by
    refine ⟨b10, ?_⟩
    have hfil : (a0, b10, b20) ∈ H.filter (fun e => e.1 = a0 ∧ e.2.2 = b20) := by
      rw [Finset.mem_filter]
      exact ⟨h_edge, by simp⟩
    exact Finset.mem_image.mpr ⟨(a0, b10, b20), hfil, rfl⟩
  have hS_subset : S ⊆ G₁ := by
    intro b1 hb1
    rcases Finset.mem_image.mp hb1 with ⟨e, he, h_eq⟩
    have h_e_in_H : e ∈ H := (Finset.mem_filter.mp he).1
    let e_enc := wz1TripleCoordinate e
    have he_enc : e_enc ∈ wz1EncodeTriples H :=
      Finset.mem_image.mpr ⟨e, h_e_in_H, rfl⟩
    have h1 : e_enc 1 ∈ G₁ := hdensity.2.1 e_enc he_enc 1
    have h2 : e_enc 1 = e.2.1 := by rfl
    rw [h2] at h1
    simpa [h_eq] using h1
  have hS_card : (S.card : ENNReal) ≥ c * G₁.enncard :=
    fiber_size_lower_bound hdensity h_edge
  have hG1_card_lower : G₁.enncard ≥ Kakeya.realRpowENN delta (workingLambda - 1) :=
    frostman_workinglambda_lower_bound
      hdelta hdeltaOne hworkingLambda_pos
      (by linarith [hworkingLambda, hepsilonOne])
      hG1_sep hG1_frostman
      (⟨b10, hb10_in_G1⟩)
  have hS_card_lower : (S.card : ℝ) ≥
      (1 / 256 : ℝ) * Real.rpow delta (eta + workingLambda - 1) := by
    have h1 : c * G₁.enncard ≥
        (1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta *
        Kakeya.realRpowENN delta (workingLambda - 1) := by
      rw [hc]
      gcongr
    have h2 : (1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta *
        Kakeya.realRpowENN delta (workingLambda - 1) ≤ (S.card : ENNReal) :=
      le_trans h1 hS_card
    have h_pos1 : 0 ≤ Real.rpow delta eta := Real.rpow_nonneg hdelta.le _
    have h_add : Real.rpow delta eta * Real.rpow delta (workingLambda - 1) =
        Real.rpow delta (eta + workingLambda - 1) := by
      have h_exp : eta + (workingLambda - 1) = eta + workingLambda - 1 := by ring
      have h : (delta ^ (eta + workingLambda - 1) : ℝ) =
          (delta ^ eta : ℝ) * (delta ^ (workingLambda - 1) : ℝ) := by
        have h' := Real.rpow_add hdelta eta (workingLambda - 1)
        rw [h_exp] at h'
        exact h'
      have h' : (delta ^ eta : ℝ) = Real.rpow delta eta := by rfl
      have h'' : (delta ^ (workingLambda - 1) : ℝ) = Real.rpow delta (workingLambda - 1) := by rfl
      have h''' : (delta ^ (eta + workingLambda - 1) : ℝ) = Real.rpow delta (eta + workingLambda - 1) := by rfl
      rw [h', h'', h'''] at h
      exact h.symm
    have h3 : Kakeya.realRpowENN delta eta *
        Kakeya.realRpowENN delta (workingLambda - 1) =
        Kakeya.realRpowENN delta (eta + workingLambda - 1) := by
      simp only [Kakeya.realRpowENN]
      rw [← ENNReal.ofReal_mul h_pos1, h_add]
    have h2' : (1 / 256 : ENNReal) * (Kakeya.realRpowENN delta eta *
        Kakeya.realRpowENN delta (workingLambda - 1)) ≤ (S.card : ENNReal) := by
      have h_assoc : (1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta *
          Kakeya.realRpowENN delta (workingLambda - 1) =
          (1 / 256 : ENNReal) * (Kakeya.realRpowENN delta eta *
          Kakeya.realRpowENN delta (workingLambda - 1)) := by
        rw [mul_assoc]
      rw [h_assoc] at h2
      exact h2
    rw [h3] at h2'
    have h4 : (S.card : ENNReal) ≠ ⊤ := by simp
    have h5 : (1 / 256 : ENNReal) * Kakeya.realRpowENN delta (eta + workingLambda - 1) ≤ (S.card : ENNReal) := h2'
    have h6 : ENNReal.toReal ((1 / 256 : ENNReal) * Kakeya.realRpowENN delta (eta + workingLambda - 1)) ≤
        ENNReal.toReal (S.card : ENNReal) :=
      ENNReal.toReal_mono h4 h5
    have h_rpow_toReal :
        ENNReal.toReal
            (Kakeya.realRpowENN delta
              (eta + workingLambda - 1)) =
          Real.rpow delta (eta + workingLambda - 1) := by
      simp only [Kakeya.realRpowENN]
      exact ENNReal.toReal_ofReal
        (Real.rpow_nonneg hdelta.le _)
    have h256 :
        ENNReal.toReal (1 / 256 : ENNReal) =
          (1 / 256 : ℝ) := by norm_num
    rw [ENNReal.toReal_mul, h256, h_rpow_toReal] at h6
    simpa using h6

  -- Step 2: Longitudinal pigeonhole with L = delta / (4 * width)
  let L : ℝ := delta / (4 * width)
  have hL_pos : 0 < L := by positivity
  have hL_le_half : L ≤ 1 / 2 := by
    dsimp only [L]
    have h2 : delta / (4 * width) ≤ width / (4 * width) := by
      gcongr
    have h3 : width / (4 * width) = 1 / 4 := by
      field_simp [hwidth_pos.ne']
    rw [h3] at h2
    linarith
  let hball_S : ∀ b ∈ S, ‖b‖ ≤ 1 := by
    intro b hb
    have h : b ∈ G₁ := hS_subset hb
    have h' : dist b 0 ≤ 1 := hG1_ball b h
    simpa [dist_eq_norm] using h'
  rcases
      longitudinal_pigeonhole S (fun b : Point2 => b)
        hdirection hL_pos hball_S with
    ⟨longCenter, hlong⟩
  let S' : Finset Point2 := S.filter fun b =>
    |inner ℝ b direction - longCenter| ≤ L
  have hS'_subset : S' ⊆ S := Finset.filter_subset _ _
  have hS'_card : (S'.card : ℝ) ≥ (S.card : ℝ) * L / 3 := by
    have h1 : 2 + 2 * L ≤ 3 := by linarith [hL_le_half]
    calc (S'.card : ℝ)
        ≥ (S.card : ℝ) * L / (2 + 2 * L) := hlong
      _ ≥ (S.card : ℝ) * L / 3 := by gcongr
  have hS'_nonempty : S'.Nonempty := by
    have h_pos : 0 < (S.card : ℝ) * L / 3 := by positivity
    have h : 0 < (S'.card : ℝ) := h_pos.trans_le hS'_card
    exact Finset.card_pos.mp (by exact_mod_cast h)

  -- Step 3: Dot value range bound
  have hdot_bound : ∀ b1 ∈ S',
      -4 * width ≤ inner ℝ a0 (b1 - b20) ∧
      inner ℝ a0 (b1 - b20) ≤ 4 * width := by
    intro b1 hb1
    have hb1_in_G1 : b1 ∈ G₁ := hS_subset (hS'_subset hb1)
    have hball_a : ‖a0‖ ≤ 1 := by
      have h : dist a0 0 ≤ 1 := hF_ball a0 ha0_in_F
      simpa [dist_eq_norm] using h
    have hball1 : ‖b1‖ ≤ 1 := by
      have h : dist b1 0 ≤ 1 := hG1_ball b1 hb1_in_G1
      simpa [dist_eq_norm] using h
    have hball2 : ‖b20‖ ≤ 1 := by
      have h : dist b20 0 ≤ 1 := hG2_ball b20 hb20_in_G2
      simpa [dist_eq_norm] using h
    have h1 : |inner ℝ a0 (b1 - b20)| ≤ 4 * width :=
      dot_value_range_bound
        (h_orthogonal a0 ha0_in_F)
        (h_common1 b1 hb1_in_G1)
        (h_common2 b20 hb20_in_G2)
        hball_a hball1 hball2 hdirection hwidth_pos
    have h_abs : -4 * width ≤ inner ℝ a0 (b1 - b20) ∧
        inner ℝ a0 (b1 - b20) ≤ 4 * width := by
      have h4 := abs_le.mp h1
      exact ⟨by linarith, by linarith⟩
    exact h_abs

  -- Step 4: Dichotomy on dot values
  let K : ℝ := 16 * Real.rpow delta (epsilon - 1)
  have hK_pos : 0 < K := by
    dsimp only [K]
    have h1 : 0 < Real.rpow delta (epsilon - 1) := Real.rpow_pos_of_pos hdelta _
    exact mul_pos (by norm_num) h1
  let f : Point2 → ℝ := fun b1 => inner ℝ a0 (b1 - b20)
  rcases point_separated_or_concentrated hdelta
      (fun b1 hb1 => hdot_bound b1 hb1) hK_pos hS'_nonempty with
    (h_conc | h_spread)

  -- Case 1: Concentrated dot values → transverse concentration → G1 strip
  · rcases h_conc with ⟨t, ht_card⟩
    let C : Finset Point2 := S'.filter fun b1 => |f b1 - t| ≤ delta
    have hC_subset : C ⊆ S' := Finset.filter_subset _ _
    have hC_card : (C.card : ℝ) ≥ K := by exact_mod_cast ht_card
    have hC_nonempty : C.Nonempty := by
      have h_pos : 0 < K := hK_pos
      have h : 0 < (C.card : ℝ) := h_pos.trans_le hC_card
      exact Finset.card_pos.mp (by exact_mod_cast h)
    rcases hC_nonempty with ⟨b10', hb10'_in_C⟩
    have hb10'_in_S' : b10' ∈ S' := hC_subset hb10'_in_C
    have ha0_perp : 3 / 7 ≤ |inner ℝ a0 (wz1Perp2 direction)| :=
      large_perp_component_three_sevenths hdirection
        (h_standardF a0 ha0_in_F)
        (h_orthogonal a0 ha0_in_F) hwidth_small
    have h_a0_dir : |inner ℝ a0 direction| ≤ width := by
      have h2 : |inner ℝ (a0 - 0) (wz1Perp2 (wz1Perp2 direction))| ≤ width :=
        h_orthogonal a0 ha0_in_F
      have h3 : wz1Perp2 (wz1Perp2 direction) = -direction := by
        ext i
        fin_cases i <;> simp [wz1Perp2_coords]
      simpa [h3, inner_neg_right, abs_neg] using h2
    have h_transverse_bounds : ∀ b1 ∈ C,
        |inner ℝ (b1 - b10') (wz1Perp2 direction)| ≤ 35 * delta / 6 := by
      intro b1 hb1
      have hb1_in_S' : b1 ∈ S' := hC_subset hb1
      have h_dot1 : |f b1 - t| ≤ delta := (Finset.mem_filter.mp hb1).2
      have h_dot2 : |f b10' - t| ≤ delta := (Finset.mem_filter.mp hb10'_in_C).2
      have h_dot_diff : |inner ℝ a0 (b1 - b10')| ≤ 2 * delta := by
        have h_eq : f b1 - f b10' = inner ℝ a0 (b1 - b10') := by
          dsimp only [f]
          have h : inner ℝ a0 (b1 - b20) - inner ℝ a0 (b10' - b20) =
              inner ℝ a0 ((b1 - b20) - (b10' - b20)) := by
            rw [← inner_sub_right]
          rw [h]
          have h3 : (b1 - b20) - (b10' - b20) = b1 - b10' := by
            ext i
            fin_cases i <;> simp
          rw [h3]
        rw [← h_eq]
        have h : |f b1 - f b10'| ≤ |f b1 - t| + |f b10' - t| := by
          have h9 : f b1 - f b10' = (f b1 - t) - (f b10' - t) := by ring
          rw [h9]
          exact abs_sub (f b1 - t) (f b10' - t)
        linarith [h_dot1, h_dot2]
      have h_long1 : |inner ℝ (b1 - b10') direction| ≤ 2 * L := by
        have h1 : |inner ℝ b1 direction - longCenter| ≤ L :=
          (Finset.mem_filter.mp hb1_in_S').2
        have h2 : |inner ℝ b10' direction - longCenter| ≤ L :=
          (Finset.mem_filter.mp hb10'_in_S').2
        have h3 : inner ℝ (b1 - b10') direction =
            inner ℝ b1 direction - inner ℝ b10' direction := by
          simp [inner_sub_left]
        rw [h3]
        have h4 : |inner ℝ b1 direction - inner ℝ b10' direction| ≤
            |inner ℝ b1 direction - longCenter| + |inner ℝ b10' direction - longCenter| := by
          have h5 : inner ℝ b1 direction - inner ℝ b10' direction =
              (inner ℝ b1 direction - longCenter) - (inner ℝ b10' direction - longCenter) := by ring
          rw [h5]
          exact abs_sub _ _
        linarith [h1, h2]
      set v := b1 - b10' with hv
      set c_dir := inner ℝ v direction with hc_dir
      set c_perp := inner ℝ v (wz1Perp2 direction) with hc_perp
      have hdecomp : v = c_dir • direction + c_perp • wz1Perp2 direction :=
        orthonormal_decomp v direction hdirection
      have hinner : inner ℝ a0 v =
          (inner ℝ a0 direction) * c_dir +
          (inner ℝ a0 (wz1Perp2 direction)) * c_perp := by
        rw [hdecomp, inner_add_right, inner_smul_right,
          inner_smul_right]
        ring
      have h_x_bound : |(inner ℝ a0 direction) * c_dir| ≤ delta / 2 := by
        have h_abs : |(inner ℝ a0 direction) * c_dir| =
            |inner ℝ a0 direction| * |c_dir| := by rw [abs_mul]
        rw [h_abs]
        have h_le : |inner ℝ a0 direction| * |c_dir| ≤ width * (2 * L) := by gcongr
        have h_eq : width * (2 * L) = delta / 2 := by
          dsimp only [L]
          field_simp [hwidth_pos.ne']
          norm_num
        rw [h_eq] at h_le
        exact h_le
      have h_main : |(inner ℝ a0 (wz1Perp2 direction)) * c_perp| ≤ 5 * delta / 2 := by
        have h_eq : (inner ℝ a0 (wz1Perp2 direction)) * c_perp =
            inner ℝ a0 v - (inner ℝ a0 direction) * c_dir := by
          rw [hinner]
          ring
        rw [h_eq]
        have h_tri : |inner ℝ a0 v - (inner ℝ a0 direction) * c_dir| ≤
            |inner ℝ a0 v| + |(inner ℝ a0 direction) * c_dir| := abs_sub _ _
        linarith [h_dot_diff, h_x_bound]
      have h5 : |inner ℝ a0 (wz1Perp2 direction)| * |c_perp| ≤ 5 * delta / 2 := by
        have h6 : |(inner ℝ a0 (wz1Perp2 direction)) * c_perp| =
            |inner ℝ a0 (wz1Perp2 direction)| * |c_perp| := by rw [abs_mul]
        rw [← h6]
        exact h_main
      have h7 : 3 / 7 ≤ |inner ℝ a0 (wz1Perp2 direction)| := ha0_perp
      have h7_pos : 0 < |inner ℝ a0 (wz1Perp2 direction)| := by linarith
      have h8 : |c_perp| ≤ 35 * delta / 6 := by
        calc |c_perp|
            = (|inner ℝ a0 (wz1Perp2 direction)| * |c_perp|) /
              |inner ℝ a0 (wz1Perp2 direction)| := by
              field_simp [h7_pos.ne']
          _ ≤ (5 * delta / 2) / (3 / 7 : ℝ) := by gcongr
          _ = 35 * delta / 6 := by ring
      simpa [hc_perp] using h8
    have hC_card_threshold :
        (C.card : ℝ) ≥
          16 * Real.rpow delta (epsilon - 1) := by
      simpa [K] using hC_card
    rcases transverse_eight_cell_pigeonhole
        (anchor := b10')
        hdelta hdirection hC_card_threshold
        (by
          intro point hpoint
          have h := h_transverse_bounds point hpoint
          linarith) with
      ⟨G1conc, hG1conc_subset, hG1conc_card,
        base', h_strip⟩
    have hG1conc_card2 :
        (G1conc.card : ENNReal) ≥
          2 * Kakeya.realRpowENN delta (epsilon - 1) := by
      have hnonnegative :
          0 ≤ 2 * Real.rpow delta (epsilon - 1) := by
        exact mul_nonneg (by norm_num) (Real.rpow_nonneg hdelta.le _)
      rw [Kakeya.realRpowENN]
      rw [← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hG1conc_card
    have hG1conc_subset_G1 : G1conc ⊆ G₁ := by
      intro b hb
      have hb_in_C : b ∈ C := hG1conc_subset hb
      have hb_in_S' : b ∈ S' := hC_subset hb_in_C
      have hb_in_S : b ∈ S := hS'_subset hb_in_S'
      exact hS_subset hb_in_S
    have hG1conc_actual :
        ∀ b ∈ G1conc, (a0, b, b20) ∈ H := by
      intro b hb
      have hb_in_C : b ∈ C := hG1conc_subset hb
      have hb_in_S' : b ∈ S' := hC_subset hb_in_C
      have hb_in_S : b ∈ S := hS'_subset hb_in_S'
      exact kaufmanSecondFiber_actual_edge hb_in_S
    have hG1conc_longitudinal :
        ∀ b ∈ G1conc,
          |inner ℝ b direction - longCenter| ≤
            delta / (4 * width) := by
      intro b hb
      have hb_in_C : b ∈ C := hG1conc_subset hb
      have hb_in_S' : b ∈ S' := hC_subset hb_in_C
      simpa [L] using (Finset.mem_filter.mp hb_in_S').2
    have hG1conc_dot :
        ∀ b ∈ G1conc,
          |inner ℝ a0 (b - b20) - t| ≤ delta := by
      intro b hb
      have hb_in_C : b ∈ C := hG1conc_subset hb
      simpa [f] using (Finset.mem_filter.mp hb_in_C).2
    let concentration :
        NarrowDotSpreadG1Concentrated
          delta epsilon width F G₁ G₂ H direction :=
      ⟨G1conc, hG1conc_subset_G1, hG1conc_card2,
        base', h_strip,
        longCenter, hG1conc_longitudinal,
        a0, b20, ha0_in_F, hb20_in_G2,
        hG1conc_actual,
        t, hG1conc_dot,
        {
          points := C
          selected_subset := hG1conc_subset
          subset := by
            intro second hsecond
            exact
              hS_subset
                (hS'_subset (hC_subset hsecond))
          card_lower := by simpa [K] using hC_card
          transverseAnchor := b10'
          transverse := h_transverse_bounds
          longitudinal := by
            intro second hsecond
            have hsecondS' := hC_subset hsecond
            simpa [L] using (Finset.mem_filter.mp hsecondS').2
          actual_mem := by
            intro second hsecond
            exact
              kaufmanSecondFiber_actual_edge
                (hS'_subset (hC_subset hsecond))
          dot_concentrated := by
            intro second hsecond
            simpa [f] using (Finset.mem_filter.mp hsecond).2
        }⟩
    exact Or.inr
      ⟨concentration, by simp [concentration,
        NarrowDotSpreadG1Concentrated.AnchoredAt]⟩

  -- Case 2: Spread dot values → DotSpreadData
  · rcases h_spread with ⟨selected, hsel_subset, hsep, hcard⟩
    let values : Finset ℝ := selected.image f
    have h_inj : Set.InjOn f (selected : Set Point2) := by
      intro x hx y hy h_eq
      by_contra h_ne
      have h : 2 * delta < |f x - f y| := hsep x hx y hy h_ne
      rw [h_eq] at h
      have h10 : |f y - f y| = 0 := by simp
      rw [h10] at h
      linarith
    have h_values_card : values.card = selected.card := by
      rw [Finset.card_image_of_injOn h_inj]
    have h_values_dot : (values : Set ℝ) ⊆ wz1DotDifferenceSet H := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨b1, hb1, rfl⟩
      have hb1_in_S : b1 ∈ S := hS'_subset (hsel_subset hb1)
      have hb1_in_G1 : b1 ∈ G₁ := hS_subset hb1_in_S
      have h_edge2 : (a0, b1, b20) ∈ H := by
        dsimp only [S, kaufmanSecondFiber] at hb1_in_S
        rcases Finset.mem_image.mp hb1_in_S with
          ⟨e, he, h_eq⟩
        have h_e1 : e.1 = a0 := (Finset.mem_filter.mp he).2.1
        have h_e2 : e.2.2 = b20 := (Finset.mem_filter.mp he).2.2
        have h_b1 : e.2.1 = b1 := by
          simpa using h_eq
        have htuple : e = (a0, b1, b20) := by
          exact Prod.ext h_e1 (Prod.ext h_b1 h_e2)
        rw [← htuple]
        exact (Finset.mem_filter.mp he).1
      exact dot_value_mem h_edge2
    have h_lower_upper : values.Nonempty := by
      have h : selected.Nonempty := by
        have h_pos : 0 < (selected.card : ℝ) := by
          have h2 : 0 < (S'.card : ℝ) / (3 * K) := by positivity
          exact h2.trans_le hcard
        exact Finset.card_pos.mp (by exact_mod_cast h_pos)
      exact Finset.Nonempty.image h f
    let lower : ℝ := values.min' h_lower_upper
    let upper : ℝ := values.max' h_lower_upper
    have h_lower_mem : lower ∈ values := Finset.min'_mem _ _
    have h_upper_mem : upper ∈ values := Finset.max'_mem _ _
    have h_between : ∀ v ∈ values, lower ≤ v ∧ v ≤ upper := by
      intro v hv
      exact ⟨Finset.min'_le values v hv, Finset.le_max' values v hv⟩
    have h_range : upper - lower ≤ 8 * width := by
      rcases Finset.mem_image.mp h_lower_mem with
        ⟨lowerPoint, hlowerPoint, hlowerValue⟩
      rcases Finset.mem_image.mp h_upper_mem with
        ⟨upperPoint, hupperPoint, hupperValue⟩
      have h1 : lower ≥ -4 * width := by
        rw [← hlowerValue]
        exact (hdot_bound lowerPoint (hsel_subset hlowerPoint)).1
      have h2 : upper ≤ 4 * width := by
        rw [← hupperValue]
        exact (hdot_bound upperPoint (hsel_subset hupperPoint)).2
      linarith
    have h_sep2 : ∀ x ∈ values, ∀ y ∈ values,
        x ≠ y → 2 * delta < |x - y| := by
      intro x hx y hy hne
      rcases Finset.mem_image.mp hx with ⟨bx, hbx, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨b2y, hby, rfl⟩
      have hbx_ne : bx ≠ b2y := by
        intro h
        apply hne
        rw [h]
      exact hsep bx hbx b2y hby hbx_ne
    have h_card_lower : (values.card : ℝ) ≥
        Real.rpow delta (eta + workingLambda - 9 * epsilon / 10) / 147456 := by
      rw [h_values_card]
      have h1 : (selected.card : ℝ) ≥ (S'.card : ℝ) / (3 * K) := hcard
      have h2 : (S'.card : ℝ) ≥ (S.card : ℝ) * L / 3 := hS'_card
      have h3 : (S.card : ℝ) ≥
          (1 / 256 : ℝ) * Real.rpow delta (eta + workingLambda - 1) := hS_card_lower
      have h4 : (selected.card : ℝ) ≥
          ((1 / 256 : ℝ) * Real.rpow delta (eta + workingLambda - 1)) * L / 3 / (3 * K) := by
        calc (selected.card : ℝ)
            ≥ (S'.card : ℝ) / (3 * K) := h1
          _ ≥ ((S.card : ℝ) * L / 3) / (3 * K) := by gcongr
          _ ≥ ((1 / 256 : ℝ) * Real.rpow delta (eta + workingLambda - 1)) * L / 3 / (3 * K) := by gcongr
      dsimp only [K, L] at h4
      have h5 : ((1 / 256 : ℝ) * Real.rpow delta (eta + workingLambda - 1)) *
          (delta / (4 * width)) / 3 / (3 * (16 * Real.rpow delta (epsilon - 1))) ≥
          Real.rpow delta (eta + workingLambda - 9 * epsilon / 10) / 147456 := by
        have h6 : width ≤ Real.rpow delta (1 - epsilon / 10) := hnarrow
        have h7 : Real.rpow delta (eta + workingLambda - 1) * delta =
            Real.rpow delta (eta + workingLambda) := by
          calc
            Real.rpow delta (eta + workingLambda - 1) * delta =
                Real.rpow delta (eta + workingLambda - 1) *
                  Real.rpow delta 1 := by simp
            _ =
                Real.rpow delta
                  ((eta + workingLambda - 1) + 1) :=
              (Real.rpow_add hdelta _ _).symm
            _ = Real.rpow delta (eta + workingLambda) := by
              congr 1
              ring
        calc ((1 / 256 : ℝ) * Real.rpow delta (eta + workingLambda - 1)) *
            (delta / (4 * width)) / 3 / (3 * (16 * Real.rpow delta (epsilon - 1)))
            = Real.rpow delta (eta + workingLambda) /
              (256 * 4 * width * 3 * 3 * 16 * Real.rpow delta (epsilon - 1)) := by
              rw [show
                (1 / 256 : ℝ) * Real.rpow delta
                    (eta + workingLambda - 1) *
                    (delta / (4 * width)) =
                  (Real.rpow delta (eta + workingLambda - 1) *
                    delta) / (256 * 4 * width) by ring]
              rw [h7]
              ring
          _ ≥ Real.rpow delta (eta + workingLambda) /
              (147456 * width * Real.rpow delta (epsilon - 1)) := by
              rw [show
                (256 : ℝ) * 4 * width * 3 * 3 * 16 *
                    Real.rpow delta (epsilon - 1) =
                  147456 * width *
                    Real.rpow delta (epsilon - 1) by
                ring]
          _ ≥ Real.rpow delta (eta + workingLambda) /
              (147456 * Real.rpow delta (1 - epsilon / 10) *
                Real.rpow delta (epsilon - 1)) := by
              exact
                div_le_div_of_nonneg_left
                  (Real.rpow_nonneg hdelta.le _)
                  (mul_pos
                    (mul_pos (by norm_num) hwidth_pos)
                    (Real.rpow_pos_of_pos hdelta _))
                  (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left h6 (by norm_num))
                    (Real.rpow_nonneg hdelta.le _))
          _ = Real.rpow delta
              (eta + workingLambda - 9 * epsilon / 10) / 147456 := by
              have h10 : Real.rpow delta (1 - epsilon / 10) * Real.rpow delta (epsilon - 1) =
                  Real.rpow delta (9 * epsilon / 10) := by
                calc
                  Real.rpow delta (1 - epsilon / 10) *
                      Real.rpow delta (epsilon - 1) =
                    Real.rpow delta
                      ((1 - epsilon / 10) + (epsilon - 1)) :=
                    (Real.rpow_add hdelta _ _).symm
                  _ = Real.rpow delta (9 * epsilon / 10) := by
                    congr 1
                    ring
              rw [show
                147456 * Real.rpow delta (1 - epsilon / 10) *
                    Real.rpow delta (epsilon - 1) =
                  147456 *
                    (Real.rpow delta (1 - epsilon / 10) *
                      Real.rpow delta (epsilon - 1)) by ring,
                h10]
              have hsub :=
                Real.rpow_sub hdelta
                  (eta + workingLambda) (9 * epsilon / 10)
              calc
                Real.rpow delta (eta + workingLambda) /
                      (147456 *
                        Real.rpow delta (9 * epsilon / 10)) =
                    (Real.rpow delta (eta + workingLambda) /
                      Real.rpow delta (9 * epsilon / 10)) /
                        147456 := by ring
                _ =
                    Real.rpow delta
                        (eta + workingLambda -
                          9 * epsilon / 10) /
                      147456 :=
                  congrArg (fun value : ℝ => value / 147456)
                    hsub.symm
      exact h5.trans h4
    let D : ℝ := upper - lower
    have hD_nonneg : 0 ≤ D := by
      exact sub_nonneg.mpr (h_between upper h_upper_mem).1
    have hD_le : D ≤ 8 * width := h_range
    have h_main_card := narrow_dot_spread_exponent_bound
        hdelta hdeltaOne hepsilon hepsilonOne heta
        hworkingLambda hetaCap hnarrow hsmall
        (values.card : ℝ) h_card_lower D hD_nonneg hD_le
    have hbase :
        2 *
              max ((upper - lower) / 2)
                (Real.rpow delta (1 - eta) / 2) /
            delta =
          max D (Real.rpow delta (1 - eta)) / delta := by
      dsimp only [D]
      rw [show
        max ((upper - lower) / 2)
            (Real.rpow delta (1 - eta) / 2) =
          max (upper - lower)
              (Real.rpow delta (1 - eta)) / 2 by
        exact
          (max_div_div_right
            (by norm_num : (0 : ℝ) ≤ 2)
            (upper - lower)
            (Real.rpow delta (1 - eta)))]
      ring
    rw [← hbase] at h_main_card
    have h_main_card' :
        Kakeya.realRpowENN
            (2 *
                max ((upper - lower) / 2)
                  (Real.rpow delta (1 - eta) / 2) /
              delta)
            (1 - epsilon) ≤
          (values.card : ENNReal) := by
      simpa [ENNReal.ofReal_natCast] using h_main_card
    exact Or.inl ⟨⟨values, lower, upper, h_lower_mem, h_upper_mem,
      h_sep2, h_values_dot, h_between, h_main_card'⟩⟩

end Kakeya.Assouad
