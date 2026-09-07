import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ActualLocalBins

/-!
# Heterogeneous local-bin input for WZ1 Lemma 23

The volume carrier used by Lemma 23 is a coarse first-stage shading, whereas
the local plane normal and Proposition-9 AD certificate live on a genuine
fine shading.  This module isolates the exact interface needed by the local
bin count without identifying those two carriers.

Each retained coarse cell supplies its own representative together with a
nearby genuine fine witness.  The proof first snaps the coarse representative
to the Lemma-23 cell center and then pays the explicit coarse-to-fine error
before applying the fine local AD certificate at the selected anchor.
-/

namespace Kakeya.Assouad

noncomputable section

/--
The fine-carrier data consumed by the actual local-bin count.

The finite `cells` remain the coarse graph vertices.  The plane normal and AD
set are defined solely from the genuine `fineCarrier`; no plane map is asked
for on the coarse representatives.
-/
structure WZ1Lemma23HeterogeneousLocalBinInput
    (rho sigma : ℝ) (C : ENNReal)
    (cells : Finset (ℤ × ℤ × ℤ)) (g : ℝ → ℝ) where
  fineCarrier : Set Point3
  coarseRepresentative : (ℤ × ℤ × ℤ) → Point3
  fineWitness : (ℤ × ℤ × ℤ) → Point3
  anchor : ℤ → Point3
  normal : ℤ → Point3
  fine_witness_mem :
    ∀ idx ∈ cells, fineWitness idx ∈ fineCarrier
  coarse_representative_index :
    ∀ idx ∈ cells,
      wz1Lemma23CellIndex rho (coarseRepresentative idx) = idx
  coarse_fine_close :
    ∀ idx ∈ cells,
      dist (coarseRepresentative idx) (fineWitness idx) ≤ 2 * rho
  fine_witness_in_anchor_ball :
    ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      ∀ idx (hidx : idx ∈ cells), idx.2.1 = y →
        dist (fineWitness idx) (anchor y) ≤ Real.sqrt rho
  normal_unit :
    ∀ y ∈ wz1Lemma23SnappedYLayers cells, ‖normal y‖ = 1
  normal_vertical :
    ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      |normal y (2 : Fin 3)| ≤ 1 / 2
  normal_first :
    ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      1 / 4 ≤ |normal y (0 : Fin 3)|
  graph_eq :
    ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      g (wz1Lemma23SnappedYValue rho y) =
        normal y (2 : Fin 3) / normal y (0 : Fin 3)
  fine_local_ad :
    ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      IsADSet1
        (scalarProjection (normal y)
          (fineCarrier ∩
            Metric.closedBall (anchor y) (Real.sqrt rho)))
        rho (1 - sigma) C

private lemma wz1Lemma23_heterogeneous_cellCenter_y_eq
    (rho : ℝ) (idx : ℤ × ℤ × ℤ) :
    (wz1Lemma23CellCenter rho idx) (1 : Fin 3) =
      wz1Lemma23SnappedYValue rho idx.2.1 := by
  simp [wz1Lemma23SnappedYValue, wz1Lemma23CellCenter, point3]

/--
Affine localized AD counting with the `12 * rho` error produced by moving a
coarse representative to a genuine fine witness.  The affine source-cover
error contributes another `4 * rho`, so each source center meets at most
thirty-five integer bins.
-/
theorem wz1_lemma23_localized_affine_twelve_perturbed_ad_bin_count
    (rho R alpha a b : ℝ) (C : ENNReal)
    (E : Set ℝ) (targetValues : Finset ℝ)
    (center : ℝ)
    (hAD : IsADSet1 E rho alpha C)
    (hrho_R : rho ≤ R)
    (hR_one : R ≤ 1)
    (ha : |a| ≤ 4)
    (hclose :
      ∀ value ∈ targetValues,
        ∃ sourceValue ∈ E ∩ Metric.closedBall center R,
          |value - (a * sourceValue + b)| ≤ 12 * rho) :
    ((wz1Lemma23ScalarBins rho targetValues).card : ENNReal) ≤
      35 * C * Kakeya.realRpowENN (R / rho) alpha := by
  classical
  rcases hAD with
    ⟨hrho, _halpha, _halphaOne, _hCone, _hbounded, hcover⟩
  by_cases hCtop : C = ⊤
  · rw [hCtop]
    have hrpowPos :
        0 < Kakeya.realRpowENN (R / rho) alpha := by
      apply ENNReal.ofReal_pos.mpr
      apply Real.rpow_pos_of_pos
      have hR : 0 < R := hrho.trans_le hrho_R
      positivity
    have htop :
        (35 : ENNReal) * ⊤ *
            Kakeya.realRpowENN (R / rho) alpha = ⊤ := by
      rw [ENNReal.mul_top (by norm_num)]
      exact ENNReal.top_mul hrpowPos.ne'
    rw [htop]
    exact le_top
  · let rhoNN : NNReal := ⟨rho, hrho.le⟩
    have hrpowNeTop :
        Kakeya.realRpowENN (R / rho) alpha ≠ ⊤ := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
    have hboundNeTop :
        C * Kakeya.realRpowENN (R / rho) alpha ≠ ⊤ :=
      ENNReal.mul_ne_top hCtop hrpowNeTop
    have hcoverBound :
        (↑(Metric.externalCoveringNumber rhoNN
          (E ∩ Metric.closedBall center R)) : ENNReal) ≤
            C * Kakeya.realRpowENN (R / rho) alpha :=
      hcover rho hrho.le le_rfl (by linarith)
        center R hrho_R hR_one
    have hfinite :
        Metric.externalCoveringNumber rhoNN
          (E ∩ Metric.closedBall center R) ≠ ⊤ := by
      intro htop
      rw [htop] at hcoverBound
      exact hboundNeTop (top_le_iff.mp hcoverBound)
    rcases
        exists_finset_cover_of_externalCoveringNumber hfinite with
      ⟨centers, hcentersCover, hcentersCard⟩
    have hcentersCardEq :
        (centers.card : ENNReal) =
          (↑(Metric.externalCoveringNumber rhoNN
            (E ∩ Metric.closedBall center R)) : ENNReal) := by
      exact_mod_cast hcentersCard
    have hcentersCardBound :
        (centers.card : ENNReal) ≤
          C * Kakeya.realRpowENN (R / rho) alpha := by
      rw [hcentersCardEq]
      exact hcoverBound
    rw [Metric.isCover_iff_subset_iUnion_closedBall] at hcentersCover
    let centerBin (sourceCenter : ℝ) : ℤ :=
      Int.floor ((a * sourceCenter + b) / rho)
    let nearbyBins (sourceCenter : ℝ) : Finset ℤ :=
      Finset.Icc
        (centerBin sourceCenter - 17)
        (centerBin sourceCenter + 17)
    have hnearbyCard :
        ∀ sourceCenter : ℝ,
          (nearbyBins sourceCenter).card = 35 := by
      intro sourceCenter
      simp [nearbyBins]
      omega
    have htargetSubset :
        wz1Lemma23ScalarBins rho targetValues ⊆
          centers.biUnion nearbyBins := by
      intro targetBin htargetBin
      rcases Finset.mem_image.mp htargetBin with
        ⟨value, hvalue, rfl⟩
      rcases hclose value hvalue with
        ⟨sourceValue, hsourceLocal, hvalueClose⟩
      have hsourceCover := hcentersCover hsourceLocal
      rcases Set.mem_iUnion₂.mp hsourceCover with
        ⟨sourceCenter, hsourceCenter, hsourceBall⟩
      have hsourceClose :
          |sourceValue - sourceCenter| ≤ rho := by
        rw [Metric.mem_closedBall, Real.dist_eq] at hsourceBall
        change |sourceValue - sourceCenter| ≤ rho at hsourceBall
        exact hsourceBall
      have haSourceClose :
          |a * sourceValue - a * sourceCenter| ≤ 4 * rho := by
        calc
          |a * sourceValue - a * sourceCenter| =
              |a| * |sourceValue - sourceCenter| := by
                rw [← mul_sub, abs_mul]
          _ ≤ 4 * rho := by gcongr
      have htotalClose :
          |value - (a * sourceCenter + b)| ≤ 16 * rho := by
        calc
          |value - (a * sourceCenter + b)| =
              |(value - (a * sourceValue + b)) +
                (a * sourceValue - a * sourceCenter)| := by
                congr 1
                ring
          _ ≤ |value - (a * sourceValue + b)| +
                |a * sourceValue - a * sourceCenter| :=
            abs_add_le _ _
          _ ≤ 12 * rho + 4 * rho := by gcongr
          _ = 16 * rho := by ring
      have hratio :
          |value / rho -
              (a * sourceCenter + b) / rho| < 17 := by
        have hdiv :
            |value / rho -
                (a * sourceCenter + b) / rho| =
              |value - (a * sourceCenter + b)| / rho := by
          rw [← sub_div, abs_div, abs_of_pos hrho]
        rw [hdiv]
        have hle :
            |value - (a * sourceCenter + b)| / rho ≤ 16 := by
          apply (div_le_iff₀ hrho).2
          nlinarith
        linarith
      have hfloor :
          |Int.floor (value / rho) - centerBin sourceCenter| ≤ 17 := by
        exact wz1_abs_floor_sub_lt_le (N := 17) (by norm_num) hratio
      exact Finset.mem_biUnion.mpr
        ⟨sourceCenter, hsourceCenter, by
          simp only [nearbyBins, Finset.mem_Icc]
          have hbounds := abs_le.mp hfloor
          omega⟩
    have hcardNat :
        (wz1Lemma23ScalarBins rho targetValues).card ≤
          35 * centers.card := by
      calc
        (wz1Lemma23ScalarBins rho targetValues).card
            ≤ (centers.biUnion nearbyBins).card :=
          Finset.card_le_card htargetSubset
        _ ≤ ∑ sourceCenter ∈ centers,
            (nearbyBins sourceCenter).card :=
          Finset.card_biUnion_le
        _ = ∑ _sourceCenter ∈ centers, 35 := by
          apply Finset.sum_congr rfl
          intro sourceCenter _
          exact hnearbyCard sourceCenter
        _ = 35 * centers.card := by
          simp [mul_comm]
    have hcardENN :
        ((wz1Lemma23ScalarBins rho targetValues).card : ENNReal) ≤
          35 * (centers.card : ENNReal) := by
      exact_mod_cast hcardNat
    calc
      ((wz1Lemma23ScalarBins rho targetValues).card : ENNReal)
          ≤ 35 * (centers.card : ENNReal) := hcardENN
      _ ≤ 35 *
          (C * Kakeya.realRpowENN (R / rho) alpha) := by
        gcongr
      _ = 35 * C *
          Kakeya.realRpowENN (R / rho) alpha := by
        ring

/--
The actual snapped local bins are controlled by fine local-grain witnesses,
even when the graph cells came from a different coarse carrier.
-/
theorem wz1_lemma23_actual_local_bins_at_heterogeneous
    {rho sigma : ℝ}
    (C : ENNReal)
    (cells : Finset (ℤ × ℤ × ℤ))
    (g : ℝ → ℝ)
    (input :
      WZ1Lemma23HeterogeneousLocalBinInput
        rho sigma C cells g)
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (y : ℤ) (hy : y ∈ wz1Lemma23SnappedYLayers cells) :
    ((wz1Lemma23SnappedLocalBinsAt
        rho g cells y).card : ENNReal) ≤
      35 * C *
        Kakeya.realRpowENN
          (Real.sqrt rho / rho) (1 - sigma) := by
  classical
  let normal := input.normal y
  let a : ℝ := 1 / normal 0
  let b : ℝ :=
    -(normal 1 / normal 0) *
      wz1Lemma23SnappedYValue rho y
  let targetValues : Finset ℝ :=
    (cells.filter fun idx => idx.2.1 = y).image fun idx =>
      wz1Lemma23LocalCoordinate g
        (wz1Lemma23SnappedPoint rho idx)
  have hnormalUnit : ‖normal‖ = 1 :=
    input.normal_unit y hy
  have hnx : 1 / 4 ≤ |normal 0| :=
    input.normal_first y hy
  have hnxPos : 0 < |normal 0| := by
    linarith
  have hnxNe : normal 0 ≠ 0 :=
    abs_ne_zero.mp hnxPos.ne'
  have hcoord0 : |normal 0| ≤ 1 := by
    have h := PiLp.norm_apply_le normal (0 : Fin 3)
    simpa [Real.norm_eq_abs, hnormalUnit] using h
  have hcoord1 : |normal 1| ≤ 1 := by
    have h := PiLp.norm_apply_le normal (1 : Fin 3)
    simpa [Real.norm_eq_abs, hnormalUnit] using h
  have ha : |a| ≤ 4 := by
    rw [abs_div, abs_one]
    have h :
        (1 : ℝ) / |normal 0| ≤
          1 / (1 / 4 : ℝ) := by
      gcongr
    norm_num at h ⊢
    exact h
  have hyRatio : |normal 1 / normal 0| ≤ 4 := by
    rw [abs_div]
    calc
      |normal 1| / |normal 0|
          ≤ 1 / |normal 0| := by gcongr
      _ ≤ 1 / (1 / 4 : ℝ) := by gcongr
      _ = 4 := by norm_num
  have hzRatio : |normal 2 / normal 0| ≤ 2 := by
    rw [abs_div]
    calc
      |normal 2| / |normal 0|
          ≤ (1 / 2 : ℝ) / |normal 0| := by
            gcongr
            exact input.normal_vertical y hy
      _ ≤ (1 / 2 : ℝ) / (1 / 4 : ℝ) := by gcongr
      _ = 2 := by norm_num
  have hrhoSqrt : rho ≤ Real.sqrt rho := by
    have hsquare := Real.sq_sqrt hrho.le
    nlinarith [Real.sqrt_nonneg rho, hrho_one]
  have hsqrtOne : Real.sqrt rho ≤ 1 := by
    have hsquare := Real.sq_sqrt hrho.le
    nlinarith [Real.sqrt_nonneg rho, hrho_one]
  have hAD :
      IsADSet1
        (scalarProjection normal
          (input.fineCarrier ∩
            Metric.closedBall (input.anchor y) (Real.sqrt rho)))
        rho (1 - sigma) C := by
    simpa [normal] using input.fine_local_ad y hy
  have hclose :
      ∀ value ∈ targetValues,
        ∃ sourceValue ∈
            scalarProjection normal
                (input.fineCarrier ∩
                  Metric.closedBall
                    (input.anchor y) (Real.sqrt rho)) ∩
              Metric.closedBall
                (inner ℝ (input.anchor y) normal)
                (Real.sqrt rho),
          |value - (a * sourceValue + b)| ≤ 12 * rho := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with
      ⟨idx, hidxFilter, rfl⟩
    have hidx : idx ∈ cells :=
      (Finset.mem_filter.mp hidxFilter).1
    have hidxY : idx.2.1 = y :=
      (Finset.mem_filter.mp hidxFilter).2
    let point := input.fineWitness idx
    let coarsePoint := input.coarseRepresentative idx
    let snapped := wz1Lemma23SnappedPoint rho idx
    let sourceValue := inner ℝ point normal
    let coarseSourceValue := inner ℝ coarsePoint normal
    have hpointCarrier : point ∈ input.fineCarrier :=
      input.fine_witness_mem idx hidx
    have hpointBall :
        point ∈
          Metric.closedBall (input.anchor y) (Real.sqrt rho) := by
      rw [Metric.mem_closedBall]
      exact input.fine_witness_in_anchor_ball y hy idx hidx hidxY
    have hsourceProjection :
        sourceValue ∈
          scalarProjection normal
            (input.fineCarrier ∩
              Metric.closedBall
                (input.anchor y) (Real.sqrt rho)) :=
      ⟨point, ⟨hpointCarrier, hpointBall⟩, rfl⟩
    have hsourceWindow :
        sourceValue ∈
          Metric.closedBall
            (inner ℝ (input.anchor y) normal)
            (Real.sqrt rho) := by
      rw [Metric.mem_closedBall, Real.dist_eq]
      have hinner :
          |inner ℝ (point - input.anchor y) normal| ≤
            ‖point - input.anchor y‖ * ‖normal‖ :=
        abs_real_inner_le_norm (point - input.anchor y) normal
      have hdist :
          ‖point - input.anchor y‖ ≤ Real.sqrt rho := by
        simpa [dist_eq_norm] using
          input.fine_witness_in_anchor_ball y hy idx hidx hidxY
      have heq :
          sourceValue - inner ℝ (input.anchor y) normal =
            inner ℝ (point - input.anchor y) normal := by
        simp [sourceValue, inner_sub_left]
      rw [heq]
      exact hinner.trans (by
        rw [hnormalUnit, mul_one]
        exact hdist)
    have hcoarseIndex :
        wz1Lemma23CellIndex rho coarsePoint = idx :=
      input.coarse_representative_index idx hidx
    have hgeometry :=
      wz1_lemma23_snapped_cell_geometry rho hrho hrho_one
    have hcoord :
        ∀ i : Fin 3,
          |coarsePoint i - (wz1Lemma23CellCenter rho idx) i| ≤
            rho / 2 :=
      (hgeometry.2.1 idx coarsePoint hcoarseIndex).1
    have hsnappedY :
        snapped 1 = wz1Lemma23SnappedYValue rho y := by
      simpa [snapped, wz1Lemma23SnappedPoint, hidxY] using
        wz1Lemma23_heterogeneous_cellCenter_y_eq rho idx
    have hgraphY :
        g (snapped 1) = normal 2 / normal 0 := by
      rw [hsnappedY]
      simpa [normal] using input.graph_eq y hy
    have hcoarsePointY :
        |coarsePoint 1 - wz1Lemma23SnappedYValue rho y| ≤
          rho / 2 := by
      rw [← hsnappedY]
      simpa [snapped, wz1Lemma23SnappedPoint] using hcoord 1
    have hcoarseSourceFormula :
        a * coarseSourceValue + b =
          coarsePoint 0 +
            (normal 1 / normal 0) *
                (coarsePoint 1 - wz1Lemma23SnappedYValue rho y) +
            (normal 2 / normal 0) * coarsePoint 2 := by
      simp only [a, b, coarseSourceValue, scalarProjection]
      simp [PiLp.inner_apply, Fin.sum_univ_succ]
      field_simp [hnxNe]
      ring
    have hcoarseMain :
        |wz1Lemma23LocalCoordinate g snapped -
            (a * coarseSourceValue + b)| ≤ 4 * rho := by
      rw [hcoarseSourceFormula]
      simp only [wz1Lemma23LocalCoordinate, hgraphY]
      have heq :
          snapped 0 +
                (normal 2 / normal 0) * snapped 2 -
              (coarsePoint 0 +
                  (normal 1 / normal 0) *
                      (coarsePoint 1 -
                        wz1Lemma23SnappedYValue rho y) +
                  (normal 2 / normal 0) * coarsePoint 2) =
            (snapped 0 - coarsePoint 0) +
              (normal 2 / normal 0) *
                (snapped 2 - coarsePoint 2) -
              (normal 1 / normal 0) *
                (coarsePoint 1 -
                  wz1Lemma23SnappedYValue rho y) := by
        ring
      rw [heq]
      calc
        |(snapped 0 - coarsePoint 0) +
              (normal 2 / normal 0) *
                (snapped 2 - coarsePoint 2) -
              (normal 1 / normal 0) *
                (coarsePoint 1 -
                  wz1Lemma23SnappedYValue rho y)|
            ≤ |snapped 0 - coarsePoint 0| +
                |normal 2 / normal 0| *
                  |snapped 2 - coarsePoint 2| +
                |normal 1 / normal 0| *
                  |coarsePoint 1 -
                    wz1Lemma23SnappedYValue rho y| := by
              calc
                |(snapped 0 - coarsePoint 0) +
                      (normal 2 / normal 0) *
                        (snapped 2 - coarsePoint 2) -
                      (normal 1 / normal 0) *
                        (coarsePoint 1 -
                          wz1Lemma23SnappedYValue rho y)|
                    ≤ |(snapped 0 - coarsePoint 0) +
                        (normal 2 / normal 0) *
                          (snapped 2 - coarsePoint 2)| +
                        |(normal 1 / normal 0) *
                          (coarsePoint 1 -
                            wz1Lemma23SnappedYValue rho y)| :=
                      abs_sub _ _
                _ ≤ |snapped 0 - coarsePoint 0| +
                        |(normal 2 / normal 0) *
                          (snapped 2 - coarsePoint 2)| +
                        |(normal 1 / normal 0) *
                          (coarsePoint 1 -
                            wz1Lemma23SnappedYValue rho y)| := by
                      gcongr
                      exact abs_add_le _ _
                _ = |snapped 0 - coarsePoint 0| +
                        |normal 2 / normal 0| *
                          |snapped 2 - coarsePoint 2| +
                        |normal 1 / normal 0| *
                          |coarsePoint 1 -
                            wz1Lemma23SnappedYValue rho y| := by
                      rw [abs_mul, abs_mul]
        _ ≤ rho / 2 + 2 * (rho / 2) + 4 * (rho / 2) := by
          have h0 : |snapped 0 - coarsePoint 0| ≤ rho / 2 := by
            rw [abs_sub_comm]
            simpa [snapped, wz1Lemma23SnappedPoint] using hcoord 0
          have h2 : |snapped 2 - coarsePoint 2| ≤ rho / 2 := by
            rw [abs_sub_comm]
            simpa [snapped, wz1Lemma23SnappedPoint] using hcoord 2
          gcongr
        _ ≤ 4 * rho := by linarith
    have hcoarseFineInner :
        |coarseSourceValue - sourceValue| ≤ 2 * rho := by
      have hinner :
          |inner ℝ (coarsePoint - point) normal| ≤
            ‖coarsePoint - point‖ * ‖normal‖ :=
        abs_real_inner_le_norm (coarsePoint - point) normal
      have hdist : ‖coarsePoint - point‖ ≤ 2 * rho := by
        simpa [dist_eq_norm] using input.coarse_fine_close idx hidx
      have heq :
          coarseSourceValue - sourceValue =
            inner ℝ (coarsePoint - point) normal := by
        simp [coarseSourceValue, sourceValue, inner_sub_left]
      rw [heq]
      exact hinner.trans (by
        rw [hnormalUnit, mul_one]
        exact hdist)
    have haCoarseFine :
        |(a * coarseSourceValue + b) -
            (a * sourceValue + b)| ≤ 8 * rho := by
      have heq :
          (a * coarseSourceValue + b) -
              (a * sourceValue + b) =
            a * (coarseSourceValue - sourceValue) := by ring
      rw [heq, abs_mul]
      calc
        |a| * |coarseSourceValue - sourceValue|
            ≤ 4 * (2 * rho) := by gcongr
        _ = 8 * rho := by ring
    have hmain :
        |wz1Lemma23LocalCoordinate g snapped -
            (a * sourceValue + b)| ≤ 12 * rho := by
      calc
        |wz1Lemma23LocalCoordinate g snapped -
              (a * sourceValue + b)|
            ≤ |wz1Lemma23LocalCoordinate g snapped -
                (a * coarseSourceValue + b)| +
              |(a * coarseSourceValue + b) -
                (a * sourceValue + b)| := by
                  exact abs_sub_le _ _ _
        _ ≤ 4 * rho + 8 * rho := by gcongr
        _ = 12 * rho := by ring
    exact
      ⟨sourceValue, ⟨hsourceProjection, hsourceWindow⟩,
        hmain⟩
  have hbins :=
    wz1_lemma23_localized_affine_twelve_perturbed_ad_bin_count
      rho (Real.sqrt rho) (1 - sigma) a b C
      (scalarProjection normal
        (input.fineCarrier ∩
          Metric.closedBall (input.anchor y) (Real.sqrt rho)))
      targetValues
      (inner ℝ (input.anchor y) normal)
      hAD hrhoSqrt hsqrtOne ha hclose
  have htargetBins :
      wz1Lemma23ScalarBins rho targetValues =
        wz1Lemma23SnappedLocalBinsAt rho g cells y := by
    simp [targetValues, wz1Lemma23ScalarBins,
      wz1Lemma23SnappedLocalBinsAt, Finset.image_image,
      Function.comp_def]
  rw [← htargetBins]
  exact hbins

end

end Kakeya.Assouad
