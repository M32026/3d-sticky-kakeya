import MyLeanRepo.Kakeya.Cinematic.Section5.MetricGoodPairIncidenceInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.Counting

/-!
# Incidence double count with automatic tangency

When the desired tangency lower threshold is at most `delta`, tangency
nonnegativity makes it automatic. The per-rectangle lower bound comes from
`RepresentativeMetricGoodPairSelectionStatement`, which filters only by metric
separation. The product-scale upper bound still needs a tangency condition,
which follows from `tangencyLower ≤ delta` and `0 ≤ tangencyParameterOn`.
-/

namespace Kakeya.Cinematic

theorem metric_good_pair_incidence :
    MetricGoodPairIncidenceStatement := by
  intro hRepGood hProduct hTangency hFine hCounting
  intro K D hK hD
  have hProdMain := hProduct hTangency K D hK hD
  rcases hProdMain with ⟨C_inc, hC_inc_pos, hC_inc⟩
  refine' ⟨C_inc, hC_inc_pos, _⟩
  intro family E delta diameter epsilon eta tRep DeltaRep C_R
    metricCut tangencyLower Cc hFamily hdelta hC_R
    hmetricCut_pos hmetricCut_lt ht_lower_pos ht_lower_le_delta
    data hmetricScale hepsilon hsmall hCc hCc_delta
  intro R source hrect hcentral hincomp F_B hF_B h_fiber_subset
    q hq hfiber_lower
  classical
  let I := data.interval
  let t := C_R * tRep * DeltaRep / delta
  let metricLower := metricCut * tRep / 8
  have hI : I.IsControlled K := by
    have h := data.assignment.intervalControlled
    rw [data.assignment_interval] at h
    exact h
  have htRep_pos : 0 < tRep := data.tRep_pos
  have hDeltaRep_pos : 0 < DeltaRep := by
    have h : delta ≤ DeltaRep := data.delta_le_DeltaRep
    linarith
  have ht_pos : 0 < t := by positivity
  have hmetricLower_pos : 0 < metricLower := by positivity
  have htangencyLower_pos : 0 < tangencyLower := ht_lower_pos
  let ambientFinset := F_B.toFinset
  let pairPred : C2Function × C2Function → Prop := fun p =>
    metricLower < c2Distance p.2 p.1
  let pairs : Finset (C2Function × C2Function) :=
    (ambientFinset.product ambientFinset).filter pairPred
  let incidence : Fin R.card → Finset (C2Function × C2Function) := fun i =>
    let G := data.assignment.fiber (source i)
    (G.toFinset.product G.toFinset).filter pairPred
  have hinc_sub : ∀ i, incidence i ⊆ pairs := by
    intro i p hp
    let G := data.assignment.fiber (source i)
    have hmem : p ∈ (G.toFinset.product G.toFinset) :=
      (Finset.mem_filter.mp hp).1
    have h1 : p.1 ∈ G.toFinset := (Finset.mem_product.mp hmem).1
    have h2 : p.2 ∈ G.toFinset := (Finset.mem_product.mp hmem).2
    have h3 : pairPred p := (Finset.mem_filter.mp hp).2
    have h4 : p.1 ∈ ambientFinset := by
      have h5 : p.1 ∈ G.carrier := by
        simpa [FiniteFunctionFamily.toFinset] using h1
      have h6 : p.1 ∈ F_B.carrier :=
        h_fiber_subset i h5
      simpa [ambientFinset, FiniteFunctionFamily.toFinset] using h6
    have h7 : p.2 ∈ ambientFinset := by
      have h8 : p.2 ∈ G.carrier := by
        simpa [FiniteFunctionFamily.toFinset] using h2
      have h9 : p.2 ∈ F_B.carrier :=
        h_fiber_subset i h8
      simpa [ambientFinset, FiniteFunctionFamily.toFinset] using h9
    have h_in_prod : p ∈ ambientFinset.product ambientFinset :=
      Finset.mem_product.mpr ⟨h4, h7⟩
    exact Finset.mem_filter.mpr ⟨h_in_prod, h3⟩
  have h_lower : ∀ (i : Fin R.card),
      i ∈ (Finset.univ : Finset (Fin R.card)) →
        q ^ 2 ≤ 3 * (pairs ∩ incidence i).card := by
    intro i _
    let G := data.assignment.fiber (source i)
    have hGood : G.card ^ 2 ≤ 3 * (incidence i).card := by
      exact hRepGood good_pair_counting
        (family := family) (E := E) (K := K) (delta := delta)
        (diameter := diameter) (epsilon := epsilon) (eta := eta)
        (tRep := tRep) (DeltaRep := DeltaRep) (C_R := C_R)
        hdelta data (source i) metricCut
        hmetricCut_pos hmetricCut_lt (hmetricScale (source i))
        (hepsilon (source i))
    have hq2 : q ^ 2 ≤ G.card ^ 2 := by
      have hq' : q ≤ G.card := hfiber_lower i
      nlinarith
    have h_inter : pairs ∩ incidence i = incidence i := by
      apply Finset.inter_eq_right.mpr
      exact hinc_sub i
    rw [h_inter]
    exact hq2.trans hGood
  let x : ℝ :=
    C_inc * Real.sqrt (delta * t / (metricLower * tangencyLower))
  let perPair : ℕ := Nat.ceil x
  have h_x_nonneg : 0 ≤ x := by positivity
  have h_upper : ∀ (p : C2Function × C2Function), p ∈ pairs →
      ((Finset.univ : Finset (Fin R.card)).filter
        (fun i => p ∈ incidence i)).card ≤ perPair := by
    intro p hp
    let S := (Finset.univ : Finset (Fin R.card)).filter
      (fun i => p ∈ incidence i)
    let w := p.2
    let b := p.1
    have hp1 : p.1 ∈ ambientFinset :=
      (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    have hp2 : p.2 ∈ ambientFinset :=
      (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
    have hpair : pairPred p := (Finset.mem_filter.mp hp).2
    have hw : w ∈ family := by
      have h : w ∈ F_B.carrier := by
        simpa [ambientFinset, FiniteFunctionFamily.toFinset] using hp2
      exact hF_B h
    have hb : b ∈ family := by
      have h : b ∈ F_B.carrier := by
        simpa [ambientFinset, FiniteFunctionFamily.toFinset] using hp1
      exact hF_B h
    have hne : w ≠ b := by
      intro h
      have hpos : 0 < c2Distance w b :=
        hmetricLower_pos.trans hpair
      have hzero : c2Distance w b = 0 := by
        rw [h]
        simp
      rw [hzero] at hpos
      exact hpos.false
    have hmetric : metricLower ≤ c2Distance w b := by
      have h : metricLower < c2Distance p.2 p.1 := hpair
      simpa [w, b] using h.le
    have htangency :
        tangencyLower ≤ tangencyParameterOn I w b + delta := by
      have htp_nonneg : 0 ≤ tangencyParameterOn I w b :=
        localAssembly_tangencyParameterOn_nonneg I w b
      have h : tangencyLower ≤ delta := ht_lower_le_delta
      linarith
    let e : Fin S.card ↪ Fin R.card :=
      (S.orderEmbOfFin rfl).toEmbedding
    let sub : RectangleSubfamily R := ⟨S.card, e⟩
    let S_family := sub.family
    have hcentral' : S_family.IsOverCentralQuarterOf I := by
      intro j
      exact hcentral (e j)
    have hincomp' :
        S_family.IsPairwiseIncomparable family Cc := by
      intro i j hne'
      have h : e i ≠ e j := by
        intro h2
        exact hne' (e.inj' h2)
      exact hincomp (e i) (e j) h
    have htangent' : ∀ (j : Fin S.card),
        (S_family.rectangle j).IsLambdaTangent w 5 ∧
        (S_family.rectangle j).IsLambdaTangent b 5 := by
      intro j
      have hej : e j ∈ S := Finset.orderEmbOfFin_mem S rfl j
      have hpin : p ∈ incidence (e j) :=
        (Finset.mem_filter.mp hej).2
      let G := data.assignment.fiber (source (e j))
      have hmem : p ∈ (G.toFinset.product G.toFinset) :=
        (Finset.mem_filter.mp hpin).1
      have h1 : p.1 ∈ G.toFinset :=
        (Finset.mem_product.mp hmem).1
      have h2 : p.2 ∈ G.toFinset :=
        (Finset.mem_product.mp hmem).2
      have h1' : p.1 ∈ G.carrier := by
        simpa [FiniteFunctionFamily.toFinset] using h1
      have h2' : p.2 ∈ G.carrier := by
        simpa [FiniteFunctionFamily.toFinset] using h2
      have hwt : (R.rectangle (e j)).IsLambdaTangent w 5 := by
        have h :
            (data.assignment.rectangle
              (source (e j))).IsLambdaTangent w 5 :=
          data.assignment.fiber_tangent (source (e j)) w h2'
        have hreq :
            R.rectangle (e j) =
              data.assignment.rectangle (source (e j)) :=
          hrect (e j)
        rw [hreq]
        exact h
      have hbt : (R.rectangle (e j)).IsLambdaTangent b 5 := by
        have h :
            (data.assignment.rectangle
              (source (e j))).IsLambdaTangent b 5 :=
          data.assignment.fiber_tangent (source (e j)) b h1'
        have hreq :
            R.rectangle (e j) =
              data.assignment.rectangle (source (e j)) :=
          hrect (e j)
        rw [hreq]
        exact h
      have hrect_eq :
          S_family.rectangle j = R.rectangle (e j) := by rfl
      rw [hrect_eq]
      exact ⟨hwt, hbt⟩
    have hbound' : (S_family.card : ℝ) ≤ x := by
      exact hC_inc (delta := delta) (t := t)
        (metricLower := metricLower) (tangencyLower := tangencyLower)
        (Cc := Cc) hdelta ht_pos hmetricLower_pos
        htangencyLower_pos hsmall hCc hCc_delta
        hFamily hI hw hb hne hmetric htangency
        hcentral' hincomp' htangent'
    have hcard : S_family.card = S.card := by rfl
    rw [hcard] at hbound'
    have h9 : (S.card : ℝ) ≤ x := hbound'
    have h10 : (S.card : ℝ) ≤ (perPair : ℝ) :=
      h9.trans (Nat.le_ceil x)
    exact Nat.cast_le.mp h10
  have hBound := hFine hCounting
    (ρ := Fin R.card) (σ := C2Function × C2Function)
    (Finset.univ) pairs incidence q perPair h_lower h_upper
  have hpairs_card : pairs.card ≤ F_B.card ^ 2 := by
    have h1 : pairs ⊆ ambientFinset.product ambientFinset :=
      Finset.filter_subset _ _
    have h2 :
        pairs.card ≤ (ambientFinset.product ambientFinset).card :=
      Finset.card_le_card h1
    have h3 :
        (ambientFinset.product ambientFinset).card =
          ambientFinset.card ^ 2 := by
      have h4 :
          (ambientFinset.product ambientFinset).card =
            ambientFinset.card * ambientFinset.card :=
        Finset.card_product ambientFinset ambientFinset
      rw [h4]
      ring
    rw [h3] at h2
    have h4 : ambientFinset.card = F_B.card := by
      have hS_coe :
          (ambientFinset : Set C2Function) =
            F_B.carrier := by
        simp [ambientFinset, FiniteFunctionFamily.toFinset]
      have h1 :
          ambientFinset.card =
            (ambientFinset : Set C2Function).ncard :=
        (Set.ncard_coe_finset ambientFinset).symm
      rw [h1, hS_coe]
      rfl
    rw [h4] at h2
    exact h2
  have hperPair : (perPair : ℝ) ≤ x + 1 := by
    by_cases hpos : 0 < Nat.ceil x
    · have h1 : Nat.ceil x - 1 < Nat.ceil x := by omega
      have h2 : ((Nat.ceil x - 1 : ℕ) : ℝ) < x := by
        by_contra h2'
        have h3 : x ≤ ((Nat.ceil x - 1 : ℕ) : ℝ) := by
          linarith
        have h4 : Nat.ceil x ≤ Nat.ceil x - 1 :=
          Nat.ceil_le.mpr h3
        omega
      have h5 : ((Nat.ceil x : ℕ) : ℝ) - 1 < x := by
        simpa [Nat.cast_sub hpos] using h2
      linarith
    · have h5 : Nat.ceil x = 0 := by omega
      have h6 : x ≤ 0 := by
        have h7 : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
        have h8 : (Nat.ceil x : ℝ) = 0 := by exact_mod_cast h5
        rw [h8] at h7
        exact h7
      have h8 : x = 0 := by linarith [h_x_nonneg]
      have h9 : perPair = 0 := by
        simp [perPair, h5]
      rw [h9, h8]
      norm_num
  have hfinal :
      (R.card : ℝ) * (q : ℝ)^2 ≤
        3 * (F_B.card : ℝ)^2 * (x + 1) := by
    have h5 :
        (R.card : ℕ) * q^2 ≤ 3 * pairs.card * perPair := by
      simpa [Finset.card_univ] using hBound
    have h6 :
        ((R.card : ℕ) * q^2 : ℝ) ≤
          (3 * pairs.card * perPair : ℝ) := by
      exact_mod_cast h5
    have h7 :
        ((R.card : ℕ) * q^2 : ℝ) =
          (R.card : ℝ) * (q : ℝ)^2 := by simp
    rw [h7] at h6
    have h8 :
        (3 * pairs.card * perPair : ℝ) ≤
          3 * (F_B.card : ℝ)^2 * (x + 1) := by
      have h9 :
          (pairs.card : ℝ) ≤
            (F_B.card : ℝ)^2 := by
        exact_mod_cast hpairs_card
      have h10 : (perPair : ℝ) ≤ x + 1 := hperPair
      nlinarith
    exact h6.trans h8
  simpa [x, t, metricLower] using hfinal

end Kakeya.Cinematic
