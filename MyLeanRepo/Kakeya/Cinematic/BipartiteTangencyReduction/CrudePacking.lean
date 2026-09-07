import MyLeanRepo.Kakeya.Cinematic.Targets.GeneralizedPacking
import MyLeanRepo.Kakeya.Cinematic.Targets.PolynomialRectangleRefinement.DoublingCover

/-!
# Crude packing for the robust bipartite reduction

This module combines a polynomial doubling cover with the generalized
rectangle-packing estimate. It bounds a rectangle family whose centers lie
near one fixed cinematic-family member.
-/

namespace Kakeya.Cinematic

lemma robust_crude_packing_bound
    {K D : ℝ} (hK : 1 ≤ K) (hD : 1 ≤ D)
    {family : Set C2Function}
    (hfamily : IsCinematicFamily family K D)
    {I : ParameterInterval} (hI : I.IsControlled K)
    {tangency A delta t : ℝ}
    (htangency : 1 ≤ tangency) (hA : 1 ≤ A)
    (hdelta : 0 < delta) (ht : 0 < t) (hdt : delta ≤ t) (ht1 : t ≤ 1)
    {centerScale centerExponent ratioScale ratioExponent : ℝ}
    (hcenterScale : 3 ≤ centerScale) (hcenterExponent : 0 ≤ centerExponent)
    (hratioScale : 0 < ratioScale) (hratioExponent : 0 ≤ ratioExponent)
    {center : C2Function} (hcenter : center ∈ family)
    {R : RectangleFamily delta t}
    (hRin : R.CentersIn family)
    (hRquarter : R.IsOverCentralQuarterOf I)
    (hR100 : R.IsPairwiseIncomparable family 100)
    (hcenterBound : ∀ i,
      c2Distance center (R.rectangle i).function ≤
        centerScale * Real.rpow tangency centerExponent * t)
    (hratio : t / delta ≤
      ratioScale * Real.rpow tangency ratioExponent *
        Real.rpow A ratioExponent) :
    (R.card : ℝ) ≤
      (D * Real.rpow (centerScale / 3)
          (Real.log D / Real.log 2)) *
        (42 * 103 ^ 2 * Real.rpow ratioScale (5 / 2 : ℝ)) *
        Real.rpow tangency
          (centerExponent * (Real.log D / Real.log 2) +
            ratioExponent * (5 / 2 : ℝ)) *
        Real.rpow A (ratioExponent * (5 / 2 : ℝ)) := by
  classical
  let alpha : ℝ := Real.log D / Real.log 2
  have hD_pos : 0 < D := by linarith
  have halpha_nonneg : 0 ≤ alpha := by
    dsimp only [alpha]
    exact div_nonneg (Real.log_nonneg hD) (Real.log_pos (by norm_num)).le
  have htangency_pos : 0 < tangency := by linarith
  have hA_pos : 0 < A := by linarith
  have htangency_pow_one : 1 ≤ Real.rpow tangency centerExponent :=
    Real.one_le_rpow htangency hcenterExponent

  let coverRadius : ℝ :=
    centerScale * Real.rpow tangency centerExponent * t
  let clusterRadius : ℝ := 3 * t
  have hcoverRadius_pos : 0 < coverRadius := by
    dsimp only [coverRadius]
    have hcenterScale_pos : 0 < centerScale := by linarith
    positivity
  have hclusterRadius_pos : 0 < clusterRadius := by
    dsimp only [clusterRadius]
    positivity
  have hcluster_le_cover : clusterRadius ≤ coverRadius := by
    dsimp only [clusterRadius, coverRadius]
    have hscale :
        3 ≤ centerScale * Real.rpow tangency centerExponent := by
      calc
        3 ≤ centerScale := hcenterScale
        _ = centerScale * 1 := by ring
        _ ≤ centerScale * Real.rpow tangency centerExponent := by
          gcongr
    exact mul_le_mul_of_nonneg_right hscale ht.le

  rcases polynomial_doubling_cover hfamily hD center hcenter
      coverRadius clusterRadius hcoverRadius_pos hclusterRadius_pos
      hcluster_le_cover with
    ⟨centers, hcenters_sub, hcenters_card, hcenters_cover⟩

  let clusterIndices (c : C2Function) : Finset (Fin R.card) :=
    Finset.univ.filter fun i =>
      c2Distance c (R.rectangle i).function ≤ 3 * t
  let x : ℝ := t / delta
  let lambda : ℝ := 100 + 3 * x

  have hx_one : 1 ≤ x := by
    dsimp only [x]
    exact (one_le_div hdelta).2 hdt
  have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx_one
  have hlambda : 100 ≤ lambda := by
    dsimp only [lambda]
    linarith
  have hlambda_bound : lambda ≤ 103 * x := by
    dsimp only [lambda]
    nlinarith
  have hI_length : I.length ≤ 1 := by
    have hshort : I.length ≤ (6 * K)⁻¹ := hI.2
    have hdenom : 1 ≤ 6 * K := by nlinarith
    have hinv : (6 * K)⁻¹ ≤ 1 := by
      simpa using (inv_le_one₀ (by positivity : 0 < 6 * K)).2 hdenom
    exact hshort.trans hinv

  have hperCluster : ∀ c ∈ centers,
      ((clusterIndices c).card : ℝ) ≤
        42 * 103 ^ 2 * Real.rpow x (5 / 2 : ℝ) := by
    intro c hc
    let embedding : Fin (clusterIndices c).card ↪ Fin R.card :=
      (Finset.orderEmbOfFin (clusterIndices c) rfl).toEmbedding
    let cluster : RectangleFamily delta t :=
      { card := (clusterIndices c).card
        rectangle := fun j => R.rectangle (embedding j) }
    have hcluster_in : cluster.CentersIn family := by
      intro j
      exact hRin (embedding j)
    have hcluster_quarter : cluster.IsOverCentralQuarterOf I := by
      intro j
      exact hRquarter (embedding j)
    have hcluster_100 : cluster.IsPairwiseIncomparable family 100 := by
      intro j k hjk
      exact hR100 (embedding j) (embedding k) (embedding.inj'.ne hjk)
    have hcluster_dist : ∀ j,
        c2Distance c (cluster.rectangle j).function ≤ 3 * t := by
      intro j
      have hj :
          embedding j ∈ clusterIndices c :=
        Finset.orderEmbOfFin_mem (clusterIndices c) rfl j
      exact (Finset.mem_filter.mp hj).2
    have hcontain : ∀ j,
        (cluster.rectangle j).carrier ⊆
          verticalNeighborhoodOn c (lambda * delta) I := by
      intro j p hp
      have hpI : p.1 ∈ I.carrier := by
        exact I.centeredCarrier_subset_carrier (by norm_num) (by norm_num)
          (hcluster_quarter j hp.1)
      have hvalue :
          |(cluster.rectangle j).function p.1 - c p.1| ≤ 3 * t := by
        have hdist := hcluster_dist j
        have hvalue_le :
            dist (cluster.rectangle j).function.value c.value ≤
              c2Distance c (cluster.rectangle j).function := by
          rw [c2Distance_eq_dist, dist_comm]
          exact le_max_left _ _
        have happly :
            |(cluster.rectangle j).function p.1 - c p.1| ≤
              dist (cluster.rectangle j).function.value c.value := by
          change
            dist ((cluster.rectangle j).function.value p.1) (c.value p.1) ≤
              dist (cluster.rectangle j).function.value c.value
          exact (ContinuousMap.dist_le dist_nonneg).mp le_rfl p.1
        exact happly.trans (hvalue_le.trans hdist)
      have hvertical :
          |p.2 - c p.1| ≤ delta + 3 * t := by
        calc
          |p.2 - c p.1| ≤
              |p.2 - (cluster.rectangle j).function p.1| +
                |(cluster.rectangle j).function p.1 - c p.1| :=
            abs_sub_le _ _ _
          _ ≤ delta + 3 * t := add_le_add hp.2 hvalue
      refine ⟨hpI, hvertical.trans ?_⟩
      dsimp only [lambda, x]
      field_simp [hdelta.ne']
      nlinarith
    have hpack :
        ((clusterIndices c).card : ℝ) ≤
          42 * lambda ^ 2 * I.length / Real.sqrt (delta / t) := by
      simpa [cluster] using
        generalized_packing_bound hK hI.2 hdelta hdt hlambda
          hcluster_in hcluster_quarter hcluster_100 hcluster_dist hcontain
    have hinverse :
        1 / Real.sqrt (delta / t) = Real.sqrt x := by
      have hproduct :
          Real.sqrt (delta / t) * Real.sqrt (t / delta) = 1 := by
        rw [← Real.sqrt_mul (by positivity)]
        have hratio_eq : (delta / t) * (t / delta) = 1 := by
          field_simp [hdelta.ne', ht.ne']
        rw [hratio_eq]
        norm_num
      dsimp only [x]
      field_simp [show Real.sqrt (delta / t) ≠ 0 by positivity]
      nlinarith
    have hsqrt_x : Real.sqrt x = Real.rpow x (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow x
    have hx_power :
        x ^ 2 * Real.sqrt x = Real.rpow x (5 / 2 : ℝ) := by
      calc
        x ^ 2 * Real.sqrt x =
            Real.rpow x (2 : ℝ) * Real.rpow x (1 / 2 : ℝ) := by
          rw [hsqrt_x]
          congr 1
          exact (Real.rpow_natCast x 2).symm
        _ = Real.rpow x (2 + 1 / 2 : ℝ) :=
          (Real.rpow_add hx_pos (2 : ℝ) (1 / 2 : ℝ)).symm
        _ = Real.rpow x (5 / 2 : ℝ) := by norm_num
    calc
      ((clusterIndices c).card : ℝ)
          ≤ 42 * lambda ^ 2 * I.length / Real.sqrt (delta / t) :=
        hpack
      _ ≤ 42 * (103 * x) ^ 2 * 1 / Real.sqrt (delta / t) := by
        gcongr
        exact I.length_nonneg
      _ = 42 * 103 ^ 2 * (x ^ 2 * Real.sqrt x) := by
        rw [div_eq_mul_inv]
        rw [show (Real.sqrt (delta / t))⁻¹ = Real.sqrt x by
          simpa [one_div] using hinverse]
        ring
      _ = 42 * 103 ^ 2 * Real.rpow x (5 / 2 : ℝ) := by
        rw [hx_power]

  have hcovered : ∀ i : Fin R.card,
      ∃ c ∈ centers,
        c2Distance c (R.rectangle i).function ≤ 3 * t := by
    intro i
    exact hcenters_cover (R.rectangle i).function (hRin i)
      (hcenterBound i)
  have hunion : (Finset.univ : Finset (Fin R.card)) ⊆
      Finset.biUnion centers clusterIndices := by
    intro i _
    rcases hcovered i with ⟨c, hc, hdist⟩
    exact Finset.mem_biUnion.mpr
      ⟨c, hc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩⟩
  have hcard_sum :
      (R.card : ℝ) ≤
        ∑ c ∈ centers, ((clusterIndices c).card : ℝ) := by
    have h₁ :
        (Finset.univ : Finset (Fin R.card)).card ≤
          (Finset.biUnion centers clusterIndices).card :=
      Finset.card_le_card hunion
    have h₂ :
        (Finset.biUnion centers clusterIndices).card ≤
          ∑ c ∈ centers, (clusterIndices c).card :=
      Finset.card_biUnion_le
    have hnat :
        R.card ≤ ∑ c ∈ centers, (clusterIndices c).card := by
      simpa using h₁.trans h₂
    exact_mod_cast hnat
  have hsum :
      (∑ c ∈ centers, ((clusterIndices c).card : ℝ)) ≤
        (centers.card : ℝ) *
          (42 * 103 ^ 2 * Real.rpow x (5 / 2 : ℝ)) := by
    calc
      (∑ c ∈ centers, ((clusterIndices c).card : ℝ))
          ≤ ∑ _c ∈ centers,
              (42 * 103 ^ 2 * Real.rpow x (5 / 2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro c hc
        exact hperCluster c hc
      _ = (centers.card : ℝ) *
          (42 * 103 ^ 2 * Real.rpow x (5 / 2 : ℝ)) := by
        simp [Finset.sum_const]

  have hcover_quotient :
      coverRadius / clusterRadius =
        (centerScale / 3) * Real.rpow tangency centerExponent := by
    dsimp only [coverRadius, clusterRadius]
    field_simp [ht.ne']
  have hcenterScale_pos : 0 < centerScale / 3 := by positivity
  have hcover_power :
      Real.rpow (coverRadius / clusterRadius) alpha =
        Real.rpow (centerScale / 3) alpha *
          Real.rpow tangency (centerExponent * alpha) := by
    rw [hcover_quotient]
    calc
      Real.rpow
          ((centerScale / 3) * Real.rpow tangency centerExponent) alpha =
          Real.rpow (centerScale / 3) alpha *
            Real.rpow (Real.rpow tangency centerExponent) alpha :=
        Real.mul_rpow hcenterScale_pos.le
          (Real.rpow_nonneg htangency_pos.le centerExponent)
      _ = Real.rpow (centerScale / 3) alpha *
          Real.rpow tangency (centerExponent * alpha) := by
        congr 1
        exact (Real.rpow_mul htangency_pos.le centerExponent alpha).symm
  have hcenters_card' :
      (centers.card : ℝ) ≤
        D * Real.rpow (centerScale / 3) alpha *
          Real.rpow tangency (centerExponent * alpha) := by
    rw [hcover_power] at hcenters_card
    simpa [mul_assoc] using hcenters_card

  have hratio_power :
      Real.rpow x (5 / 2 : ℝ) ≤
        Real.rpow ratioScale (5 / 2 : ℝ) *
          Real.rpow tangency (ratioExponent * (5 / 2 : ℝ)) *
          Real.rpow A (ratioExponent * (5 / 2 : ℝ)) := by
    have hbase_nonneg :
        0 ≤ ratioScale * Real.rpow tangency ratioExponent *
          Real.rpow A ratioExponent :=
      mul_nonneg
        (mul_nonneg hratioScale.le
          (Real.rpow_nonneg htangency_pos.le ratioExponent))
        (Real.rpow_nonneg hA_pos.le ratioExponent)
    have hmono :
        Real.rpow x (5 / 2 : ℝ) ≤
          Real.rpow
            (ratioScale * Real.rpow tangency ratioExponent *
              Real.rpow A ratioExponent)
            (5 / 2 : ℝ) :=
      Real.rpow_le_rpow hx_pos.le hratio (by norm_num)
    calc
      Real.rpow x (5 / 2 : ℝ)
          ≤ Real.rpow
              (ratioScale * Real.rpow tangency ratioExponent *
                Real.rpow A ratioExponent)
              (5 / 2 : ℝ) := hmono
      _ = Real.rpow ratioScale (5 / 2 : ℝ) *
            Real.rpow (Real.rpow tangency ratioExponent)
              (5 / 2 : ℝ) *
            Real.rpow (Real.rpow A ratioExponent)
              (5 / 2 : ℝ) := by
        calc
          Real.rpow
              (ratioScale * Real.rpow tangency ratioExponent *
                Real.rpow A ratioExponent)
              (5 / 2 : ℝ) =
              Real.rpow
                  (ratioScale * Real.rpow tangency ratioExponent)
                  (5 / 2 : ℝ) *
                Real.rpow (Real.rpow A ratioExponent)
                  (5 / 2 : ℝ) :=
            Real.mul_rpow
              (mul_nonneg hratioScale.le
                (Real.rpow_nonneg htangency_pos.le ratioExponent))
              (Real.rpow_nonneg hA_pos.le ratioExponent)
          _ = (Real.rpow ratioScale (5 / 2 : ℝ) *
                Real.rpow (Real.rpow tangency ratioExponent)
                  (5 / 2 : ℝ)) *
              Real.rpow (Real.rpow A ratioExponent)
                (5 / 2 : ℝ) := by
            exact congrArg
              (fun y => y *
                Real.rpow (Real.rpow A ratioExponent) (5 / 2 : ℝ))
              (Real.mul_rpow hratioScale.le
                (Real.rpow_nonneg htangency_pos.le ratioExponent))
      _ = Real.rpow ratioScale (5 / 2 : ℝ) *
            Real.rpow tangency (ratioExponent * (5 / 2 : ℝ)) *
            Real.rpow A (ratioExponent * (5 / 2 : ℝ)) := by
        have htangency_flat :
            Real.rpow (Real.rpow tangency ratioExponent) (5 / 2 : ℝ) =
              Real.rpow tangency
                (ratioExponent * (5 / 2 : ℝ)) :=
          (Real.rpow_mul htangency_pos.le ratioExponent
            (5 / 2 : ℝ)).symm
        have hA_flat :
            Real.rpow (Real.rpow A ratioExponent) (5 / 2 : ℝ) =
              Real.rpow A (ratioExponent * (5 / 2 : ℝ)) :=
          (Real.rpow_mul hA_pos.le ratioExponent (5 / 2 : ℝ)).symm
        rw [htangency_flat, hA_flat]

  have hproduct :
      (centers.card : ℝ) *
          (42 * 103 ^ 2 * Real.rpow x (5 / 2 : ℝ)) ≤
        (D * Real.rpow (centerScale / 3) alpha) *
          (42 * 103 ^ 2 * Real.rpow ratioScale (5 / 2 : ℝ)) *
          Real.rpow tangency
            (centerExponent * alpha +
              ratioExponent * (5 / 2 : ℝ)) *
          Real.rpow A (ratioExponent * (5 / 2 : ℝ)) := by
    have hpack_nonneg :
        0 ≤ 42 * 103 ^ 2 * Real.rpow x (5 / 2 : ℝ) :=
      mul_nonneg (by norm_num)
        (Real.rpow_nonneg hx_pos.le (5 / 2 : ℝ))
    have hcenters_factor_nonneg :
        0 ≤ D * Real.rpow (centerScale / 3) alpha *
          Real.rpow tangency (centerExponent * alpha) :=
      mul_nonneg
        (mul_nonneg (by linarith)
          (Real.rpow_nonneg hcenterScale_pos.le alpha))
        (Real.rpow_nonneg htangency_pos.le (centerExponent * alpha))
    have hmul := mul_le_mul hcenters_card'
      (mul_le_mul_of_nonneg_left hratio_power
        (by positivity : 0 ≤ (42 : ℝ) * 103 ^ 2))
      hpack_nonneg hcenters_factor_nonneg
    calc
      (centers.card : ℝ) *
          (42 * 103 ^ 2 * Real.rpow x (5 / 2 : ℝ))
          ≤
        (D * Real.rpow (centerScale / 3) alpha *
          Real.rpow tangency (centerExponent * alpha)) *
        (42 * 103 ^ 2 *
          (Real.rpow ratioScale (5 / 2 : ℝ) *
            Real.rpow tangency (ratioExponent * (5 / 2 : ℝ)) *
            Real.rpow A (ratioExponent * (5 / 2 : ℝ)))) := hmul
      _ = (D * Real.rpow (centerScale / 3) alpha) *
          (42 * 103 ^ 2 * Real.rpow ratioScale (5 / 2 : ℝ)) *
          (Real.rpow tangency (centerExponent * alpha) *
            Real.rpow tangency (ratioExponent * (5 / 2 : ℝ))) *
          Real.rpow A (ratioExponent * (5 / 2 : ℝ)) := by ring
      _ = (D * Real.rpow (centerScale / 3) alpha) *
          (42 * 103 ^ 2 * Real.rpow ratioScale (5 / 2 : ℝ)) *
          Real.rpow tangency
            (centerExponent * alpha +
              ratioExponent * (5 / 2 : ℝ)) *
          Real.rpow A (ratioExponent * (5 / 2 : ℝ)) := by
        have hadd :
            Real.rpow tangency (centerExponent * alpha) *
                Real.rpow tangency (ratioExponent * (5 / 2 : ℝ)) =
              Real.rpow tangency
                (centerExponent * alpha +
                  ratioExponent * (5 / 2 : ℝ)) :=
          (Real.rpow_add htangency_pos
            (centerExponent * alpha)
            (ratioExponent * (5 / 2 : ℝ))).symm
        rw [hadd]

  dsimp only [alpha] at hproduct ⊢
  exact hcard_sum.trans (hsum.trans hproduct)

end Kakeya.Cinematic
