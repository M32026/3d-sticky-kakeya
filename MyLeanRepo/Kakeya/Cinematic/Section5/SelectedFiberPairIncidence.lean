import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedFiberPairIncidenceInputs

/-!
# Pair incidence for selected fine-rectangle fibers

Double count good ordered pairs in arbitrary selected incidence fibers and
use the uniform product-scale fixed-pair bound for the opposite direction.
-/

namespace Kakeya.Cinematic

theorem selected_fiber_pair_incidence :
    SelectedFiberPairIncidenceStatement := by
  intro hProduct hTangency hFine hCounting
  intro K D hK hD
  have hProdMain := hProduct hTangency K D hK hD
  rcases hProdMain with ⟨C_inc, hC_inc_pos, hC_inc⟩
  refine' ⟨C_inc, hC_inc_pos, _⟩
  intro delta t metricLower tangencyLower Cc
    hdelta ht_pos hmetricLower_pos htangencyLower_pos
    hsmall hCc hCc_delta
    family hFamily I hI R hcentral hincomp
    ambient hambient selectedFiber hfiber_subset hfiber_tangent
    q hq hfiber_lower hgood
  classical
  let ambientFinset := ambient.toFinset
  let pairPred : C2Function × C2Function → Prop := fun p =>
    metricLower < c2Distance p.2 p.1 ∧
    tangencyLower ≤ tangencyParameterOn I p.2 p.1 + delta
  let pairs : Finset (C2Function × C2Function) :=
    (ambientFinset.product ambientFinset).filter pairPred
  let incidence :
      Fin R.card → Finset (C2Function × C2Function) := fun i =>
    ((selectedFiber i).product
      (selectedFiber i)).filter pairPred
  have hinc_sub : ∀ i, incidence i ⊆ pairs := by
    intro i p hp
    have hmem :
        p ∈ (selectedFiber i).product (selectedFiber i) :=
      (Finset.mem_filter.mp hp).1
    have h1 : p.1 ∈ selectedFiber i :=
      (Finset.mem_product.mp hmem).1
    have h2 : p.2 ∈ selectedFiber i :=
      (Finset.mem_product.mp hmem).2
    have h3 : pairPred p := (Finset.mem_filter.mp hp).2
    have h4 : p.1 ∈ ambientFinset := by
      have h5 : p.1 ∈ ambient.carrier :=
        hfiber_subset i h1
      simpa [ambientFinset, FiniteFunctionFamily.toFinset] using h5
    have h7 : p.2 ∈ ambientFinset := by
      have h8 : p.2 ∈ ambient.carrier :=
        hfiber_subset i h2
      simpa [ambientFinset, FiniteFunctionFamily.toFinset] using h8
    have h_in_prod :
        p ∈ ambientFinset.product ambientFinset :=
      Finset.mem_product.mpr ⟨h4, h7⟩
    exact Finset.mem_filter.mpr ⟨h_in_prod, h3⟩
  have h_lower :
      ∀ (i : Fin R.card),
        i ∈ (Finset.univ : Finset (Fin R.card)) →
          q ^ 2 ≤ 3 * (pairs ∩ incidence i).card := by
    intro i _
    have hGood :
        (selectedFiber i).card ^ 2 ≤
          3 * (incidence i).card :=
      hgood i
    have hq2 :
        q ^ 2 ≤ (selectedFiber i).card ^ 2 := by
      have hq' : q ≤ (selectedFiber i).card :=
        hfiber_lower i
      nlinarith
    have h_inter : pairs ∩ incidence i = incidence i := by
      apply Finset.inter_eq_right.mpr
      exact hinc_sub i
    rw [h_inter]
    exact hq2.trans hGood
  let x : ℝ :=
    C_inc *
      Real.sqrt
        (delta * t / (metricLower * tangencyLower))
  let perPair : ℕ := Nat.ceil x
  have h_x_nonneg : 0 ≤ x := by positivity
  have h_upper :
      ∀ (p : C2Function × C2Function), p ∈ pairs →
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
      have h : w ∈ ambient.carrier := by
        simpa [ambientFinset, FiniteFunctionFamily.toFinset] using hp2
      exact hambient h
    have hb : b ∈ family := by
      have h : b ∈ ambient.carrier := by
        simpa [ambientFinset, FiniteFunctionFamily.toFinset] using hp1
      exact hambient h
    have hne : w ≠ b := by
      intro h
      have hpos : 0 < c2Distance w b :=
        hmetricLower_pos.trans hpair.1
      have hzero : c2Distance w b = 0 := by
        rw [h]
        simp
      rw [hzero] at hpos
      exact hpos.false
    have hmetric :
        metricLower ≤ c2Distance w b := by
      have h : metricLower < c2Distance p.2 p.1 :=
        hpair.1
      simpa [w, b] using h.le
    have htangency :
        tangencyLower ≤
          tangencyParameterOn I w b + delta := by
      have h :
          tangencyLower ≤
            tangencyParameterOn I p.2 p.1 + delta :=
        hpair.2
      simpa [w, b] using h
    let e : Fin S.card ↪ Fin R.card :=
      (S.orderEmbOfFin rfl).toEmbedding
    let sub : RectangleSubfamily R := ⟨S.card, e⟩
    let S_family := sub.family
    have hcentral' :
        S_family.IsOverCentralQuarterOf I := by
      intro j
      exact hcentral (e j)
    have hincomp' :
        S_family.IsPairwiseIncomparable family Cc := by
      intro i j hne'
      have h : e i ≠ e j := by
        intro h2
        exact hne' (e.inj' h2)
      exact hincomp (e i) (e j) h
    have htangent' :
        ∀ (j : Fin S.card),
          (S_family.rectangle j).IsLambdaTangent w 5 ∧
          (S_family.rectangle j).IsLambdaTangent b 5 := by
      intro j
      have hej : e j ∈ S :=
        Finset.orderEmbOfFin_mem S rfl j
      have hpin : p ∈ incidence (e j) :=
        (Finset.mem_filter.mp hej).2
      have hmem :
          p ∈ (selectedFiber (e j)).product
            (selectedFiber (e j)) :=
        (Finset.mem_filter.mp hpin).1
      have h1 : p.1 ∈ selectedFiber (e j) :=
        (Finset.mem_product.mp hmem).1
      have h2 : p.2 ∈ selectedFiber (e j) :=
        (Finset.mem_product.mp hmem).2
      have hwt :
          (R.rectangle (e j)).IsLambdaTangent w 5 :=
        hfiber_tangent (e j) w h2
      have hbt :
          (R.rectangle (e j)).IsLambdaTangent b 5 :=
        hfiber_tangent (e j) b h1
      have hrect_eq :
          S_family.rectangle j = R.rectangle (e j) := by
        rfl
      rw [hrect_eq]
      exact ⟨hwt, hbt⟩
    have hbound' : (S_family.card : ℝ) ≤ x := by
      exact hC_inc
        (delta := delta) (t := t)
        (metricLower := metricLower)
        (tangencyLower := tangencyLower)
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
    (ρ := Fin R.card)
    (σ := C2Function × C2Function)
    (Finset.univ) pairs incidence q perPair
    h_lower h_upper
  have hpairs_card : pairs.card ≤ ambient.card ^ 2 := by
    have h1 : pairs ⊆ ambientFinset.product ambientFinset :=
      Finset.filter_subset _ _
    have h2 :
        pairs.card ≤
          (ambientFinset.product ambientFinset).card :=
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
    have h4 : ambientFinset.card = ambient.card := by
      have hS_coe :
          (ambientFinset : Set C2Function) =
            ambient.carrier := by
        simp [ambientFinset, FiniteFunctionFamily.toFinset]
      have h1 :
          ambientFinset.card =
            (ambientFinset : Set C2Function).ncard :=
        (Set.ncard_coe_finset ambientFinset).symm
      rw [h1, hS_coe]
      rfl
    rw [h4] at h2
    exact h2
  have hperPair : (perPair : ℝ) ≤ x + 1 :=
    (Nat.ceil_lt_add_one h_x_nonneg).le
  have hfinal :
      (R.card : ℝ) * (q : ℝ) ^ 2 ≤
        3 * (ambient.card : ℝ) ^ 2 * (x + 1) := by
    have h5 :
        (R.card : ℕ) * q ^ 2 ≤
          3 * pairs.card * perPair := by
      simpa [Finset.card_univ] using hBound
    have h6 :
        ((R.card : ℕ) * q ^ 2 : ℝ) ≤
          (3 * pairs.card * perPair : ℝ) := by
      exact_mod_cast h5
    have h7 :
        ((R.card : ℕ) * q ^ 2 : ℝ) =
          (R.card : ℝ) * (q : ℝ) ^ 2 := by
      simp
    rw [h7] at h6
    have h8 :
        (3 * pairs.card * perPair : ℝ) ≤
          3 * (ambient.card : ℝ) ^ 2 * (x + 1) := by
      have h9 :
          (pairs.card : ℝ) ≤
            (ambient.card : ℝ) ^ 2 := by
        exact_mod_cast hpairs_card
      have h10 : (perPair : ℝ) ≤ x + 1 := hperPair
      nlinarith
    exact h6.trans h8
  simpa [x] using hfinal

end Kakeya.Cinematic
