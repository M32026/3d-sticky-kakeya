import MyLeanRepo.Kakeya.Cinematic.Section5.DirectFiberFunctionIncidenceInputs
import MyLeanRepo.Kakeya.Cinematic.Targets.GeneralizedPacking

/-!
# Count rectangles by retained functions
-/

namespace Kakeya.Cinematic

theorem direct_fiber_function_incidence :
    DirectFiberFunctionIncidenceStatement := by
  intros h_pair K delta t hK hdelta hdt family I hI R hCenters hOver hIncomp
    center hdist H fiber hfiber_sub hfiber_tan q hq_pos hfiber_card
  classical
  let B : ℝ := 42 * (100 : ℝ)^2 * I.length / Real.sqrt (delta / t)
  have ht_pos : 0 < t := by linarith
  have hdt_pos : 0 < delta / t := by positivity
  have h_sqrt_pos : 0 < Real.sqrt (delta / t) := Real.sqrt_pos.mpr hdt_pos
  have hI_len : 0 ≤ I.length := I.length_nonneg
  have hB_nonneg : 0 ≤ B := by
    dsimp only [B]
    have h :
        0 ≤ 42 * (100 : ℝ)^2 * I.length / Real.sqrt (delta / t) := by
      positivity
    exact h
  have h_ceil_le : (Nat.ceil B : ℝ) ≤ B + 1 := by
    by_cases h : Nat.ceil B = 0
    · have hB0 : B = 0 := by
        have h1 : B ≤ (Nat.ceil B : ℝ) := Nat.le_ceil B
        rw [h] at h1
        have h2 : B ≤ 0 := by exact_mod_cast h1
        linarith [hB_nonneg]
      rw [hB0]
      norm_num
    · have hpos : 0 < Nat.ceil B := Nat.pos_of_ne_zero h
      have h4 : ¬(Nat.ceil B ≤ Nat.ceil B - 1) := by omega
      have h5 : ¬(B ≤ ↑(Nat.ceil B - 1)) := by
        rwa [Nat.ceil_le] at h4
      have h6 : ((Nat.ceil B - 1 : ℕ) : ℝ) = (Nat.ceil B : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        simp
      rw [h6] at h5
      linarith
  have h_per_function : ∀ f ∈ H.toFinset,
      (Finset.univ.filter
        (fun i : Fin R.card => f ∈ (fiber i).toFinset)).card ≤
        Nat.ceil B := by
    intro f hf
    let S_f : Finset (Fin R.card) :=
      Finset.univ.filter (fun i => f ∈ (fiber i).toFinset)
    have h_mem_iff : ∀ (i : Fin R.card),
        i ∈ S_f ↔ f ∈ (fiber i).carrier := by
      intro i
      simp only [S_f, Finset.mem_filter, Finset.mem_univ, true_and]
      have h2 : f ∈ (fiber i).toFinset ↔ f ∈ (fiber i).carrier := by
        simp [FiniteFunctionFamily.toFinset]
      exact h2
    let e : Fin S_f.card ↪ Fin R.card :=
      (S_f.orderEmbOfFin rfl).toEmbedding
    let sub : RectangleSubfamily R := { card := S_f.card, embedding := e }
    let R_f := sub.family
    have h_e_mem : ∀ j : Fin S_f.card, e j ∈ S_f :=
      Finset.orderEmbOfFin_mem S_f rfl
    have hCenters_f : R_f.CentersIn family := by
      intro j
      exact hCenters (e j)
    have hOver_f : R_f.IsOverCentralQuarterOf I := by
      intro j
      exact hOver (e j)
    have hIncomp_f : R_f.IsPairwiseIncomparable family 100 := by
      intro i j hij
      have hne : e i ≠ e j := by
        intro h
        exact hij (e.inj' h)
      exact hIncomp (e i) (e j) hne
    have hdist_f : ∀ j,
        c2Distance center (R_f.rectangle j).function ≤ 3 * t := by
      intro j
      exact hdist (e j)
    have hcontain_f : ∀ j, (R_f.rectangle j).carrier ⊆
        verticalNeighborhoodOn f (100 * delta) I := by
      intro j
      let i := e j
      have hi_in_S : i ∈ S_f := h_e_mem j
      have hf_in_carrier : f ∈ (fiber i).carrier :=
        (h_mem_iff i).mp hi_in_S
      have h_tan : (R.rectangle i).IsLambdaTangent f 5 :=
        hfiber_tan i f hf_in_carrier
      have h_interval_sub :
          (R.rectangle i).interval.carrier ⊆ I.carrier := by
        have h1 :
            (R.rectangle i).interval.carrier ⊆
              I.centeredCarrier (1 / 4) :=
          hOver i
        have h2 : I.centeredCarrier (1 / 4) ⊆ I.carrier :=
          I.centeredCarrier_subset_carrier (by norm_num) (by norm_num)
        exact h1.trans h2
      intro p hp
      have h_p1 : p.1 ∈ (R.rectangle i).interval.carrier := hp.1
      have h_p1_I : p.1 ∈ I.carrier := h_interval_sub h_p1
      have h_abs : |p.2 - f p.1| ≤ 5 * delta := h_tan p hp
      have h_abs2 : |p.2 - f p.1| ≤ 100 * delta := by
        calc
          |p.2 - f p.1| ≤ 5 * delta := h_abs
          _ ≤ 100 * delta := by linarith
      exact ⟨h_p1_I, h_abs2⟩
    have h_pack : (R_f.card : ℝ) ≤ B :=
      generalized_packing_bound hK hI hdelta hdt (by norm_num)
        hCenters_f hOver_f hIncomp_f hdist_f
        (J := I) (g := f) hcontain_f
    have h_card_eq : (R_f.card : ℝ) = (S_f.card : ℝ) := by rfl
    rw [h_card_eq] at h_pack
    have h9 : (S_f.card : ℝ) ≤ (Nat.ceil B : ℝ) := by
      calc
        (S_f.card : ℝ) ≤ B := h_pack
        _ ≤ (Nat.ceil B : ℝ) := Nat.le_ceil B
    have h_nat_le : S_f.card ≤ Nat.ceil B := by exact_mod_cast h9
    exact h_nat_le
  have h_lower : ∀ (i : Fin R.card),
      i ∈ (Finset.univ : Finset (Fin R.card)) →
        q ≤ (H.toFinset ∩ (fiber i).toFinset).card := by
    intro i _
    have h1 : (fiber i).carrier ⊆ H.carrier := hfiber_sub i
    have h2 : (fiber i).toFinset ⊆ H.toFinset := by
      intro g hg
      have h3 : g ∈ (fiber i).carrier := by
        simpa [FiniteFunctionFamily.toFinset] using hg
      have h4 : g ∈ H.carrier := h1 h3
      simpa [FiniteFunctionFamily.toFinset] using h4
    have h3 : H.toFinset ∩ (fiber i).toFinset = (fiber i).toFinset := by
      rw [Finset.inter_eq_right.mpr h2]
    rw [h3]
    have h4 : (fiber i).toFinset.card = (fiber i).card := by
      have h_coe :
          ((fiber i).toFinset : Set C2Function) = (fiber i).carrier :=
        (fiber i).finite.coe_toFinset
      have h5 :
          (fiber i).toFinset.card =
            ((fiber i).toFinset : Set C2Function).ncard := by
        simp
      have h6 : (fiber i).card = (fiber i).carrier.ncard := by
        simp [FiniteFunctionFamily.card]
      rw [h5, h_coe, h6]
    rw [h4]
    exact hfiber_card i
  have h_upper : ∀ (f : C2Function), f ∈ H.toFinset →
      ((Finset.univ : Finset (Fin R.card)).filter
        (fun i => f ∈ (fiber i).toFinset)).card ≤ Nat.ceil B :=
    h_per_function
  have h_count := h_pair (ρ := Fin R.card) (σ := C2Function)
    (rectangles := Finset.univ) (pairs := H.toFinset)
    (incidence := fun i => (fiber i).toFinset)
    (q := q) (L := Nat.ceil B) h_lower h_upper
  have h_univ_card :
      (Finset.univ : Finset (Fin R.card)).card = R.card := by
    simp
  have h_H_card : H.toFinset.card = H.card := by
    have h_coe : (H.toFinset : Set C2Function) = H.carrier :=
      H.finite.coe_toFinset
    have h5 :
        H.toFinset.card = (H.toFinset : Set C2Function).ncard := by
      simp
    have h6 : H.card = H.carrier.ncard := by
      simp [FiniteFunctionFamily.card]
    rw [h5, h_coe, h6]
  rw [h_univ_card, h_H_card] at h_count
  have h_real :
      (R.card : ℝ) * (q : ℝ) ≤
        (H.card : ℝ) * (Nat.ceil B : ℝ) := by
    exact_mod_cast h_count
  have h_final :
      (R.card : ℝ) * (q : ℝ) ≤ (H.card : ℝ) * (B + 1) := by
    calc
      (R.card : ℝ) * (q : ℝ)
          ≤ (H.card : ℝ) * (Nat.ceil B : ℝ) := h_real
      _ ≤ (H.card : ℝ) * (B + 1) := by
        gcongr
  simpa [B] using h_final

end Kakeya.Cinematic
