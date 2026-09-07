import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# AD-based global grain pigeonhole

Given a set S in Point3 and a continuous projection f : Point3 → ℝ such that
f '' S is an AD set, find a sqrt-rho ball in the projection whose preimage
contains a large fraction of the volume of S.
-/

namespace Kakeya.Assouad

open MeasureTheory Metric Set

/-- Extract a finite ε-cover from a finite external covering number. -/
lemma exists_finset_cover_of_externalCoveringNumber_ne_top
    {X : Type*} [PseudoMetricSpace X] {A : Set X} {ε : NNReal}
    (h : Metric.externalCoveringNumber ε A ≠ ⊤) :
    ∃ (S : Finset X), Metric.IsCover ε A (S : Set X) ∧
      (S.card : ENat) = Metric.externalCoveringNumber ε A := by
  let P : Set X → Prop := Metric.IsCover ε A
  have h_def : Metric.externalCoveringNumber ε A =
      ⨅ (C : Set X) (_ : P C), C.encard := by rfl
  have h1 : (⨅ (C : Set X) (_ : P C), C.encard) ≠ ⊤ := by
    rw [← h_def]; exact h
  have h_exists : ∃ (C : Set X), P C ∧ C.encard ≠ ⊤ := by
    simpa [iInf_eq_top, encard_eq_top_iff] using h1
  rcases h_exists with ⟨C0, hC0_cover, hC0_fin⟩
  letI : Nonempty {C : Set X // P C} := ⟨⟨C0, hC0_cover⟩⟩
  have h_iInf_subtype : (⨅ (x : {C : Set X // P C}), (x : Set X).encard) =
      ⨅ (C : Set X) (_ : P C), C.encard := by
    rw [iInf_subtype]
  have h_main := ENat.exists_eq_iInf
    (fun x : {C : Set X // P C} => (x : Set X).encard)
  rcases h_main with ⟨C, hC_eq⟩
  have h2 : (C : Set X).encard ≠ ⊤ := by
    rw [hC_eq, h_iInf_subtype, ← h_def]; exact h
  have h_finite : (C : Set X).Finite := Set.encard_ne_top_iff.mp h2
  let S := h_finite.toFinset
  have hS_coe : (S : Set X) = (C : Set X) := Set.Finite.coe_toFinset h_finite
  have h_card : (S.card : ENat) = (C : Set X).encard := by
    have hS : (S : Set X) = (C : Set X) := hS_coe
    have h : (S.card : ENat) = (S : Set X).encard := by simp
    rw [h, hS]
  refine ⟨S, ?_, ?_⟩
  · rw [hS_coe]; exact C.prop
  · rw [h_card, hC_eq, h_iInf_subtype, ← h_def]

/-- Pigeonhole strict sum for ENNReal: if every term is strictly below `b ≠ ⊤`
and every term is finite, then the sum is strictly below `card * b`. -/
lemma finset_sum_lt_card_mul_ennreal {α : Type*} {s : Finset α} {f : α → ENNReal} {b : ENNReal}
    (hne : s.Nonempty) (_hb : b ≠ ⊤) (hfin : ∀ x ∈ s, f x ≠ ⊤)
    (h : ∀ x ∈ s, f x < b) :
    ∑ x ∈ s, f x < (s.card : ENNReal) * b := by
  classical
  let P : Finset α → Prop := fun t =>
    (∀ x ∈ t, f x ≠ ⊤) → (∀ x ∈ t, f x < b) → t.Nonempty →
    ∑ x ∈ t, f x < (t.card : ENNReal) * b
  have h_base : P ∅ := by
    intro _ _ hne; exact False.elim (Finset.not_nonempty_empty hne)
  have h_step : ∀ (a : α) (t : Finset α), a ∉ t → P t → P (insert a t) := by
    intro a t ha ih hfin_t hlt_t hne_t
    have h1 : f a < b := hlt_t a (Finset.mem_insert_self a t)
    by_cases hte : t = ∅
    · subst hte
      simpa using h1
    · have hne' : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr hte
      have hfin' : ∀ x ∈ t, f x ≠ ⊤ := fun x hx => hfin_t x (Finset.mem_insert_of_mem hx)
      have hlt' : ∀ x ∈ t, f x < b := fun x hx => hlt_t x (Finset.mem_insert_of_mem hx)
      have h2 := ih hfin' hlt' hne'
      have hsum_fin : (∑ x ∈ t, f x) ≠ ⊤ := ENNReal.sum_ne_top.mpr hfin'
      have h3 : f a + ∑ x ∈ t, f x < b + ∑ x ∈ t, f x := by
        have h3' : ∑ x ∈ t, f x + f a < ∑ x ∈ t, f x + b := ENNReal.add_lt_add_left hsum_fin h1
        have h_comm1 : f a + ∑ x ∈ t, f x = ∑ x ∈ t, f x + f a := by rw [add_comm]
        have h_comm2 : b + ∑ x ∈ t, f x = ∑ x ∈ t, f x + b := by rw [add_comm]
        rw [h_comm1, h_comm2]
        exact h3'
      have h4 : b + ∑ x ∈ t, f x ≤ b + (t.card : ENNReal) * b := by gcongr
      have h5 : f a + ∑ x ∈ t, f x < b + (t.card : ENNReal) * b := h3.trans_le h4
      have hcard : (insert a t).card = t.card + 1 := by
        simp [ha]
      have h6 : b + (t.card : ENNReal) * b = ((insert a t).card : ENNReal) * b := by
        rw [hcard]
        simp [add_mul] <;> ring
      have hsum : ∑ x ∈ insert a t, f x = f a + ∑ x ∈ t, f x := by
        rw [Finset.sum_insert ha]
      rw [hsum]
      rw [h6] at h5
      exact h5
  have h_main : ∀ t, P t := fun t => Finset.induction_on t h_base h_step
  exact h_main s hfin h hne

/--
AD-based pigeonhole: given a set S and a continuous projection f such that
f '' S is `IsADSet1` with parameters (rho, 1-sigma, C), there exists a
sqrt-rho ball whose f-preimage intersects S in volume at least
`volume S * rho^((1-sigma)/2) / (4 * C)`.
-/
theorem ad_global_grain_pigeonhole
    {S : Set Point3} {f : Point3 → ℝ}
    {rho sigma : ℝ} {C : ENNReal}
    (hAD : IsADSet1 (f '' S) rho (1 - sigma) C)
    (hf_cont : Continuous f)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hC : C ≠ ⊤)
    (hS_top : volume S ≠ ⊤) :
    ∃ (x : ℝ),
      volume (S ∩ f ⁻¹' (Metric.closedBall x (Real.sqrt rho))) ≥
        volume S * Kakeya.realRpowENN rho ((1 - sigma) / 2) / (4 * C) := by
  let E := f '' S
  let ε : NNReal := ⟨Real.sqrt rho, Real.sqrt_nonneg rho⟩
  have hsqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have hsqrt_one : Real.sqrt rho ≤ 1 := Real.sqrt_le_one.mpr hrho_one
  have hrho_le_sqrt : rho ≤ Real.sqrt rho := by
    have h : Real.sqrt rho ^ 2 = rho := Real.sq_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg rho]
  have hE_sub : E ⊆ Set.Icc (-4 : ℝ) 4 := hAD.2.2.2.2.1

  let centers4 : Finset ℝ := insert (-3) (insert (-1) (insert 1 (insert 3 (∅ : Finset ℝ))))

  have hcenters4_card : centers4.card = 4 := by
    simp [centers4] <;> norm_num

  have hcover4 : Set.Icc (-4 : ℝ) 4 ⊆ ⋃ c ∈ centers4, Metric.closedBall c 1 := by
    intro x hx
    have h1 : -4 ≤ x := hx.1
    have h2 : x ≤ 4 := hx.2
    by_cases h3 : x ≤ -2
    · have h4 : |x + 3| ≤ 1 := by rw [abs_le] <;> constructor <;> linarith
      have h5 : dist x (-3 : ℝ) ≤ 1 := by
        have h6 : dist x (-3 : ℝ) = |x + 3| := by simp [Real.dist_eq] <;> ring
        rw [h6]; exact h4
      exact Set.mem_iUnion₂.mpr ⟨-3, by simp [centers4] <;> norm_num, h5⟩
    · by_cases h4 : x ≤ 0
      · have h5 : |x + 1| ≤ 1 := by rw [abs_le] <;> constructor <;> linarith
        have h6 : dist x (-1 : ℝ) ≤ 1 := by
          have h7 : dist x (-1 : ℝ) = |x + 1| := by simp [Real.dist_eq] <;> ring
          rw [h7]; exact h5
        exact Set.mem_iUnion₂.mpr ⟨-1, by simp [centers4] <;> norm_num, h6⟩
      · by_cases h5 : x ≤ 2
        · have h6 : |x - 1| ≤ 1 := by rw [abs_le] <;> constructor <;> linarith
          have h7 : dist x (1 : ℝ) ≤ 1 := by
            have h8 : dist x (1 : ℝ) = |x - 1| := by simp [Real.dist_eq] <;> ring
            rw [h8]; exact h6
          exact Set.mem_iUnion₂.mpr ⟨1, by simp [centers4] <;> norm_num, h7⟩
        · have h6 : |x - 3| ≤ 1 := by rw [abs_le] <;> constructor <;> linarith
          have h7 : dist x (3 : ℝ) ≤ 1 := by
            have h8 : dist x (3 : ℝ) = |x - 3| := by simp [Real.dist_eq] <;> ring
            rw [h8]; exact h6
          exact Set.mem_iUnion₂.mpr ⟨3, by simp [centers4] <;> norm_num, h7⟩

  let bound : ENNReal := C * Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma)

  have h_rpow_ne_top : Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hbound_ne_top : bound ≠ ⊤ := ENNReal.mul_ne_top hC h_rpow_ne_top

  have h_AD_bound : ∀ c ∈ centers4,
      (Metric.externalCoveringNumber ε (E ∩ Metric.closedBall c 1) : ENNReal) ≤ bound := by
    intro c _
    have h := hAD.2.2.2.2.2 (Real.sqrt rho) (Real.sqrt_nonneg rho)
      hrho_le_sqrt hsqrt_one c 1 (by linarith) (by norm_num)
    exact h

  choose covers hcovers1 hcovers2 using fun c hc =>
    exists_finset_cover_of_externalCoveringNumber_ne_top
      (by
        have h : (Metric.externalCoveringNumber ε (E ∩ Metric.closedBall c 1) : ENNReal) ≤ bound :=
          h_AD_bound c hc
        have h' : (Metric.externalCoveringNumber ε (E ∩ Metric.closedBall c 1) : ENNReal) ≠ ⊤ :=
          ne_of_lt (h.trans_lt (lt_top_iff_ne_top.mpr hbound_ne_top))
        exact_mod_cast h')

  have hm3 : (-3 : ℝ) ∈ centers4 := by simp [centers4] <;> norm_num
  have hm1 : (-1 : ℝ) ∈ centers4 := by simp [centers4] <;> norm_num
  have hp1 : (1 : ℝ) ∈ centers4 := by simp [centers4] <;> norm_num
  have hp3 : (3 : ℝ) ∈ centers4 := by simp [centers4] <;> norm_num

  let allCenters : Finset ℝ :=
    covers (-3) hm3 ∪ covers (-1) hm1 ∪ covers 1 hp1 ∪ covers 3 hp3

  let g (x : ℝ) : Set Point3 := S ∩ f ⁻¹' (Metric.closedBall x (Real.sqrt rho))

  have hcover_E : ∀ (y : ℝ), y ∈ E →
      ∃ (x : ℝ), x ∈ allCenters ∧ y ∈ Metric.closedBall x (Real.sqrt rho) := by
    intro y hy
    have h1 : y ∈ Set.Icc (-4 : ℝ) 4 := hE_sub hy
    have h_mem : y ∈ ⋃ c ∈ centers4, Metric.closedBall c 1 := hcover4 h1
    have h_exists : ∃ (c : ℝ), c ∈ centers4 ∧ y ∈ Metric.closedBall c 1 := by
      simpa [Set.mem_iUnion₂] using h_mem
    rcases h_exists with ⟨c, hc, h2⟩
    have h3 : y ∈ E ∩ Metric.closedBall c 1 := ⟨hy, h2⟩
    have h4 : ∃ (x : ℝ), x ∈ covers c hc ∧ edist y x ≤ (ε : ENNReal) := hcovers1 c hc h3
    rcases h4 with ⟨x, hx, hdist⟩
    have h6 : dist y x ≤ Real.sqrt rho := by
      have h1 : (edist y x : ENNReal) ≤ (ε : ENNReal) := hdist
      have h2 : edist y x = ENNReal.ofReal (dist y x) := edist_dist y x
      have h3 : (ε : ENNReal) = ENNReal.ofReal (Real.sqrt rho) := by
        have h4 : (ε : ENNReal) = ENNReal.ofReal (ε : ℝ) := ENNReal.coe_nnreal_eq ε
        rw [h4]
        <;> rfl
      rw [h2, h3] at h1
      have h10 : ENNReal.ofReal (dist y x) ≤ ENNReal.ofReal (Real.sqrt rho) := h1
      by_cases h11 : dist y x ≤ Real.sqrt rho
      · exact h11
      · have h12 : 0 < dist y x := by linarith [Real.sqrt_nonneg rho]
        have h13 : Real.sqrt rho < dist y x := by linarith
        have h14 : ENNReal.ofReal (Real.sqrt rho) < ENNReal.ofReal (dist y x) := by
          exact (ENNReal.ofReal_lt_ofReal_iff h12).mpr h13
        exfalso
        exact not_le.mpr h14 h10
    have h9 : y ∈ Metric.closedBall x (Real.sqrt rho) := by
      simpa [Metric.mem_closedBall] using h6
    have h10 : x ∈ allCenters := by
      have h_c_eq : c = -3 ∨ c = -1 ∨ c = 1 ∨ c = 3 := by
        have h : c ∈ centers4 := hc
        simp [centers4] at h <;> tauto
      rcases h_c_eq with (rfl | rfl | rfl | rfl) <;> simp [allCenters, hx] <;> tauto
    exact ⟨x, h10, h9⟩

  have hcover_S : S ⊆ ⋃ x ∈ allCenters, g x := by
    intro p hp
    have h1 : f p ∈ E := ⟨p, hp, rfl⟩
    rcases hcover_E (f p) h1 with ⟨x, hx, h2⟩
    exact Set.mem_iUnion₂.mpr ⟨x, hx, ⟨hp, h2⟩⟩

  have hvol : volume S ≤ ∑ x ∈ allCenters, volume (g x) := by
    have h1 : volume S ≤ volume (⋃ x ∈ allCenters, g x) := measure_mono hcover_S
    have h2 : volume (⋃ x ∈ allCenters, g x) ≤ ∑ x ∈ allCenters, volume (g x) := by
      exact measure_biUnion_finset_le allCenters g
    exact h1.trans h2

  by_cases hS_empty : allCenters = ∅
  · have hE_empty : E = ∅ := by
      by_contra hE
      have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE
      rcases hE_nonempty with ⟨y, hy⟩
      rcases hcover_E y hy with ⟨x, hx, _⟩
      rw [hS_empty] at hx
      simp at hx
    have hS_empty' : S = ∅ := by
      by_contra h
      have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr h
      rcases hS_nonempty with ⟨p, hp⟩
      have hfp : f p ∈ E := ⟨p, hp, rfl⟩
      rw [hE_empty] at hfp
      simp at hfp
    rw [hS_empty']
    simp
  · have hne : allCenters.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
    have hcard_pos : (allCenters.card : ENNReal) ≠ 0 := by
      have h : 0 < allCenters.card := Finset.card_pos.mpr hne
      exact_mod_cast h.ne'
    have hcard_top : (allCenters.card : ENNReal) ≠ ⊤ := by simp

    have h_each_bound : ∀ (c : ℝ) (hc : c ∈ centers4),
        ((covers c hc).card : ENNReal) ≤ bound := by
      intro c hc
      have h1 : ((covers c hc).card : ENat) =
          Metric.externalCoveringNumber ε (E ∩ Metric.closedBall c 1) :=
        hcovers2 c hc
      have h2 : ((covers c hc).card : ENNReal) =
          (Metric.externalCoveringNumber ε (E ∩ Metric.closedBall c 1) : ENNReal) := by
        exact_mod_cast h1
      rw [h2]
      exact h_AD_bound c hc

    have hcard_le : (allCenters.card : ENNReal) ≤ 4 * bound := by
      let A := covers (-3) hm3
      let B := covers (-1) hm1
      let D := covers 1 hp1
      let E' := covers 3 hp3
      have h14 : allCenters.card ≤ A.card + B.card + D.card + E'.card := by
        let rest := B ∪ (D ∪ E')
        have h11 : allCenters = A ∪ rest := by simp [allCenters, A, B, D, E', rest]
        have h15 : allCenters.card ≤ A.card + rest.card := by
          rw [h11]
          exact Finset.card_union_le A rest
        have h16 : rest.card ≤ B.card + (D ∪ E').card := Finset.card_union_le B (D ∪ E')
        have h17 : (D ∪ E').card ≤ D.card + E'.card := Finset.card_union_le D E'
        calc allCenters.card
          ≤ A.card + rest.card := h15
        _ ≤ A.card + (B.card + (D ∪ E').card) := add_le_add le_rfl h16
        _ ≤ A.card + (B.card + (D.card + E'.card)) := add_le_add le_rfl (add_le_add le_rfl h17)
        _ = A.card + B.card + D.card + E'.card := by ring
      have h3 : (A.card : ENNReal) ≤ bound := h_each_bound (-3) hm3
      have h4 : (B.card : ENNReal) ≤ bound := h_each_bound (-1) hm1
      have h5 : (D.card : ENNReal) ≤ bound := h_each_bound 1 hp1
      have h6 : (E'.card : ENNReal) ≤ bound := h_each_bound 3 hp3
      have h2 : (allCenters.card : ENNReal) ≤
          (A.card : ENNReal) + (B.card : ENNReal) + (D.card : ENNReal) + (E'.card : ENNReal) := by
        exact_mod_cast h14
      have hs1 : (A.card : ENNReal) + (B.card : ENNReal) ≤ bound + bound := by
        gcongr <;> tauto
      have hs2 : (D.card : ENNReal) + (E'.card : ENNReal) ≤ bound + bound := by
        gcongr <;> tauto
      have hs3 : (A.card : ENNReal) + (B.card : ENNReal) + (D.card : ENNReal) + (E'.card : ENNReal) ≤
          (bound + bound) + (bound + bound) := by
        have h : ((A.card : ENNReal) + (B.card : ENNReal)) + ((D.card : ENNReal) + (E'.card : ENNReal)) ≤
            (bound + bound) + (bound + bound) := add_le_add hs1 hs2
        have h_eq : (A.card : ENNReal) + (B.card : ENNReal) + (D.card : ENNReal) + (E'.card : ENNReal) =
            ((A.card : ENNReal) + (B.card : ENNReal)) + ((D.card : ENNReal) + (E'.card : ENNReal)) := by ring
        rw [h_eq]
        exact h
      have hs4 : (bound + bound) + (bound + bound) = 4 * bound := by ring
      exact h2.trans (hs3.trans (le_of_eq hs4))

    have hmain : ∃ x ∈ allCenters,
        volume S / (allCenters.card : ENNReal) ≤ volume (g x) := by
      by_contra h
      push Not at h
      let b := volume S / (allCenters.card : ENNReal)
      have hb_top : b ≠ ⊤ := by
        have h : b = volume S * (allCenters.card : ENNReal)⁻¹ := by rfl
        rw [h]
        have hinv_ne_top : (allCenters.card : ENNReal)⁻¹ ≠ ⊤ := by
          simp [hcard_pos]
        exact ENNReal.mul_ne_top hS_top hinv_ne_top
      have hg_fin : ∀ x ∈ allCenters, volume (g x) ≠ ⊤ := by
        intro x _
        have h_sub : g x ⊆ S := by
          dsimp only [g]
          exact Set.inter_subset_left
        have h_le : volume (g x) ≤ volume S := measure_mono h_sub
        exact ne_top_of_le_ne_top hS_top h_le
      have h3 : ∑ x ∈ allCenters, volume (g x) < (allCenters.card : ENNReal) * b :=
        finset_sum_lt_card_mul_ennreal hne hb_top hg_fin h
      have h4 : (allCenters.card : ENNReal) * b = volume S := by
        have hdiv : b = volume S * (allCenters.card : ENNReal)⁻¹ := by rfl
        rw [hdiv]
        have hmul : (allCenters.card : ENNReal) * (allCenters.card : ENNReal)⁻¹ = 1 := by
          apply ENNReal.mul_inv_cancel <;> assumption
        have h9 : (allCenters.card : ENNReal) * (volume S * (allCenters.card : ENNReal)⁻¹) =
            volume S * ((allCenters.card : ENNReal) * (allCenters.card : ENNReal)⁻¹) := by
          rw [mul_left_comm]
        rw [h9, hmul, mul_one]
      rw [h4] at h3
      have h_not : ¬(volume S ≤ ∑ x ∈ allCenters, volume (g x)) := by
        exact Std.not_le.mpr h3
      exact h_not hvol
    rcases hmain with ⟨x, hx, hbound_vol⟩

    have h_rpow_eq : Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) =
        (Kakeya.realRpowENN rho ((1 - sigma) / 2))⁻¹ := by
      simp only [Kakeya.realRpowENN]
      let y := Real.rpow rho ((1 - sigma) / 2)
      have hpos : 0 < y := Real.rpow_pos_of_pos hrho _
      have h1 : Real.rpow (1 / Real.sqrt rho) (1 - sigma) = y⁻¹ := by
        have h2 : 1 / Real.sqrt rho = rho ^ (-(1 / 2 : ℝ)) := by
          have h3 : Real.sqrt rho = rho ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
          have h4 : 1 / Real.sqrt rho = (Real.sqrt rho)⁻¹ := by field_simp
          rw [h4, h3]
          have h5 : (rho ^ (1 / 2 : ℝ))⁻¹ = rho ^ (-(1 / 2 : ℝ)) := by
            rw [← Real.rpow_neg (by linarith)] <;> ring
          exact h5
        rw [h2]
        have h3 : Real.rpow (rho ^ (-(1 / 2 : ℝ))) (1 - sigma) =
            Real.rpow rho ((-(1 / 2 : ℝ)) * (1 - sigma)) :=
          (Real.rpow_mul (by linarith) (-(1 / 2 : ℝ)) (1 - sigma)).symm
        rw [h3]
        have h4 : Real.rpow rho (-(1 / 2 : ℝ) * (1 - sigma)) =
            Real.rpow rho (-(1 - sigma) / 2) := by ring_nf
        rw [h4]
        have h51 : -(1 - sigma) / 2 = -((1 - sigma) / 2) := by ring
        rw [h51]
        have h52 : Real.rpow rho (-((1 - sigma) / 2)) =
            (Real.rpow rho ((1 - sigma) / 2))⁻¹ :=
          Real.rpow_neg (by linarith) ((1 - sigma) / 2)
        exact h52
      rw [h1]
      exact ENNReal.ofReal_inv_of_pos hpos

    have hfinal : volume S * Kakeya.realRpowENN rho ((1 - sigma) / 2) / (4 * C) ≤
        volume S / (allCenters.card : ENNReal) := by
      let R := Kakeya.realRpowENN rho ((1 - sigma) / 2)
      have hR_pos : R ≠ 0 := by
        simp [R, Kakeya.realRpowENN, Real.rpow_pos_of_pos hrho]
      have hR_top : R ≠ ⊤ := by
        simp [R, Kakeya.realRpowENN]
      have hbound_eq : bound = C * R⁻¹ := by
        dsimp only [bound]
        exact congr_arg (fun x => C * x) h_rpow_eq
      have hC_pos : C ≠ 0 := by
        by_contra hC0
        have hbound0 : bound = 0 := by
          rw [hbound_eq, hC0] <;> simp
        have h1 : ∀ (c : ℝ) (hc : c ∈ centers4), covers c hc = ∅ := by
          intro c hc
          have h2 : (covers c hc).card ≤ bound := h_each_bound c hc
          rw [hbound0] at h2
          have h3 : (covers c hc).card = 0 := by simpa using h2
          exact Finset.card_eq_zero.mp h3
        have hA : covers (-3) hm3 = ∅ := h1 (-3) hm3
        have hB : covers (-1) hm1 = ∅ := h1 (-1) hm1
        have hD : covers 1 hp1 = ∅ := h1 1 hp1
        have hE' : covers 3 hp3 = ∅ := h1 3 hp3
        have hall : allCenters = ∅ := by
          simp [allCenters, hA, hB, hD, hE']
        exact hS_empty hall
      have h4C_pos : (4 * C : ENNReal) ≠ 0 := by
        simp [hC_pos]
      have h4C_top : (4 * C : ENNReal) ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · simp
        · exact hC
      have h9 : (4 * bound)⁻¹ = R / (4 * C) := by
        have h_mul : (4 * bound) * (R / (4 * C)) = 1 := by
          rw [hbound_eq]
          have hdiv : R / (4 * C) = R * (4 * C)⁻¹ := by
            simp [div_eq_mul_inv]
          rw [hdiv]
          have h_comm : (4 * (C * R⁻¹)) * (R * (4 * C)⁻¹) =
              (4 * C) * (R⁻¹ * R) * (4 * C)⁻¹ := by
            ac_rfl
          rw [h_comm]
          have hRinv : R⁻¹ * R = 1 := ENNReal.inv_mul_cancel hR_pos hR_top
          rw [hRinv]
          have h1 : (4 * C) * (1 : ENNReal) * (4 * C)⁻¹ = (4 * C) * (4 * C)⁻¹ := by
            rw [mul_one]
          rw [h1]
          exact ENNReal.mul_inv_cancel h4C_pos h4C_top
        have h_mul' : (R / (4 * C)) * (4 * bound) = 1 := by
          rw [mul_comm]
          exact h_mul
        have h10 : R / (4 * C) = (4 * bound)⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left h_mul'
        exact h10.symm
      have h_eq : volume S * R / (4 * C) = volume S / (4 * bound) := by
        have h13 : volume S * R / (4 * C) = volume S * (R / (4 * C)) := by
          simp [div_eq_mul_inv, mul_assoc] <;> ring
        rw [h13, ← h9]
        <;> rfl
      rw [h_eq]
      have h6 : (allCenters.card : ENNReal) ≤ 4 * bound := hcard_le
      gcongr

    exact ⟨x, hfinal.trans hbound_vol⟩

end Kakeya.Assouad
