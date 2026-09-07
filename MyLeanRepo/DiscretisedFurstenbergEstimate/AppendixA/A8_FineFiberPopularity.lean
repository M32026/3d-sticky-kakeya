module

/-
  A8: Fine-fiber popularity from H2 (OS (A.43)-(A.46)) — CANONICAL INTERFACES.

  Uses canonical structures from AppendixA.Interfaces.
  Removes vacuous hfine_tubes_sset per operator correction.

  Key result: Given A5+A7 output with common coarse tube T0, extract for each
  coarse square Q ∈ Q0 a subset P'_Q and fine tubes through each point,
  with uniform cardinality lower bounds and projection data.

  Requires hΔ_small : 25 ≤ Δ^{-10ε} for projection robustness transfer
  (canonical ProjectionData uses Δ^{-12ε} robustness constant).

  Whiteprint node: appendix_a_alternative / a8_fine_fiber_popularity
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_Main
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeEnergyExtraction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.EnergyToDeltaSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductContradiction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductStructureRescaling.Basics
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineParams
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HCommonWiring
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Phase2

/-! ========================================================================
   Abstract fine-fiber popularity extraction (Markov/pigeonhole)
   ======================================================================== -/

lemma A8_fine_fiber_popularity_abstract
    {α : Type*} [DecidableEq α]
    (P : Finset α)
    (f : α → ℕ)
    (H U P_max : ℝ)
    (hH_pos : 0 < H)
    (hU_pos : 0 < U)
    (hPmax_pos : 0 < P_max)
    (h_sum : H ≤ ∑ p ∈ P, (f p : ℝ))
    (h_upper : ∀ p ∈ P, (f p : ℝ) ≤ U)
    (h_card : (P.card : ℝ) ≤ P_max) :
    ∃ (P' : Finset α), P' ⊆ P ∧
      (P'.card : ℝ) ≥ H / (2 * U) ∧
      ∀ p ∈ P', (f p : ℝ) ≥ H / (2 * P_max) := by
  classical
  let τ : ℝ := H / (2 * P_max)
  have hτ_pos : 0 < τ := by positivity
  let B : Finset α := P.filter (fun p => (f p : ℝ) < τ)
  have hB_sub : B ⊆ P := Finset.filter_subset _ _
  have h_sum_B : ∑ p ∈ B, (f p : ℝ) ≤ H / 2 := by
    have h2 : ∀ p ∈ B, (f p : ℝ) < τ := by
      intro p hp; simpa [B, Finset.mem_filter] using (Finset.mem_filter.mp hp).2
    have h3 : ∑ p ∈ B, (f p : ℝ) ≤ ∑ p ∈ B, τ := by
      apply Finset.sum_le_sum; intro p hp; exact (h2 p hp).le
    have h4 : ∑ p ∈ B, τ = τ * (B.card : ℝ) := by simp [Finset.sum_const] <;> ring
    rw [h4] at h3
    have h5 : τ * (B.card : ℝ) ≤ τ * P_max := by
      have h6 : (B.card : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast Finset.card_le_card hB_sub
      have h7 : (B.card : ℝ) ≤ P_max := by linarith
      gcongr
    have h8 : τ * P_max = H / 2 := by
      dsimp only [τ]; field_simp [hPmax_pos.ne'] <;> ring
    rw [h8] at h5; exact h3.trans h5
  let P' : Finset α := P \ B
  have hP'_sub : P' ⊆ P := Finset.sdiff_subset
  have h_sum_P' : H / 2 ≤ ∑ p ∈ P', (f p : ℝ) := by
    have h9 : P = P' ∪ B := by ext x; simp [P', B, Finset.mem_filter] <;> tauto
    have h10 : Disjoint P' B := by simp [P', Finset.disjoint_left] <;> tauto
    have h11 : ∑ p ∈ P, (f p : ℝ) = ∑ p ∈ P', (f p : ℝ) + ∑ p ∈ B, (f p : ℝ) := by
      rw [h9, Finset.sum_union h10]
    have h12 : ∑ p ∈ P, (f p : ℝ) ≥ H := h_sum
    linarith
  have h_high : ∀ p ∈ P', (f p : ℝ) ≥ τ := by
    intro p hp
    have h_in_P : p ∈ P := Finset.mem_sdiff.mp hp |>.1
    by_contra h
    have h' : (f p : ℝ) < τ := by linarith
    have h_in_B : p ∈ B := by
      simp only [B, Finset.mem_filter]; exact ⟨h_in_P, h'⟩
    have h_cont : p ∉ B := (Finset.mem_sdiff.mp hp).2
    exact h_cont h_in_B
  have h_card_lower : (P'.card : ℝ) ≥ H / (2 * U) := by
    have h12 : ∑ p ∈ P', (f p : ℝ) ≤ U * (P'.card : ℝ) := by
      have h13 : ∀ p ∈ P', (f p : ℝ) ≤ U := by intro p hp; exact h_upper p (hP'_sub hp)
      have h14 : ∑ p ∈ P', (f p : ℝ) ≤ ∑ p ∈ P', U := by
        apply Finset.sum_le_sum; intro p hp; exact h13 p hp
      have h15 : ∑ p ∈ P', U = U * (P'.card : ℝ) := by simp [Finset.sum_const] <;> ring
      rw [h15] at h14; exact h14
    have h16 : H / 2 ≤ U * (P'.card : ℝ) := by
      calc H / 2 ≤ ∑ p ∈ P', (f p : ℝ) := h_sum_P'
        _ ≤ U * (P'.card : ℝ) := h12
    have h17 : H / (2 * U) ≤ (P'.card : ℝ) := by
      calc H / (2 * U)
        = (H / 2) / U := by field_simp [hU_pos.ne'] <;> ring
      _ ≤ (U * (P'.card : ℝ)) / U := by gcongr
      _ = (P'.card : ℝ) := by field_simp [hU_pos.ne'] <;> ring
    exact h17
  exact ⟨P', hP'_sub, h_card_lower, h_high⟩

/-! ========================================================================
   Packing bound: ≤25 Δ-separated points per Δ-ball in Plane
   ======================================================================== -/

lemma round_to_grid5 {a center Δ : ℝ} (hΔ : 0 < Δ) (h : |a - center| ≤ Δ) :
    ∃ (k : Fin 5),
      center - Δ + (k : ℝ) * (2 * Δ / 5) ≤ a ∧
      a ≤ center - Δ + ((k : ℝ) + 1) * (2 * Δ / 5) := by
  have h1 : center - Δ ≤ a := by have h11 : -Δ ≤ a - center := (abs_le.mp h).1; linarith
  have h2 : a ≤ center + Δ := by have h21 : a - center ≤ Δ := (abs_le.mp h).2; linarith
  by_cases h3 : a ≤ center - 3 * Δ / 5
  · refine ⟨(0 : Fin 5), ?_⟩; constructor <;> norm_num <;> linarith
  · have h3' : a > center - 3 * Δ / 5 := by linarith
    by_cases h4 : a ≤ center - Δ / 5
    · refine ⟨(1 : Fin 5), ?_⟩; constructor <;> norm_num <;> linarith
    · have h4' : a > center - Δ / 5 := by linarith
      by_cases h5 : a ≤ center + Δ / 5
      · refine ⟨(2 : Fin 5), ?_⟩; constructor <;> norm_num <;> linarith
      · have h5' : a > center + Δ / 5 := by linarith
        by_cases h6 : a ≤ center + 3 * Δ / 5
        · refine ⟨(3 : Fin 5), ?_⟩; constructor <;> norm_num <;> linarith
        · refine ⟨(4 : Fin 5), ?_⟩; constructor <;> norm_num <;> linarith

noncomputable def coordIndex (Δ : ℝ) (hΔ : 0 < Δ) (center t : ℝ) : Fin 5 :=
  if h : |t - center| ≤ Δ then Classical.choose (round_to_grid5 hΔ h) else (0 : Fin 5)

lemma coordIndex_bounds {Δ center t : ℝ} (hΔ : 0 < Δ) (h : |t - center| ≤ Δ) :
    center - Δ + ((coordIndex Δ hΔ center t : ℝ)) * (2 * Δ / 5) ≤ t ∧
    t ≤ center - Δ + ((coordIndex Δ hΔ center t : ℝ) + 1) * (2 * Δ / 5) := by
  have h' : coordIndex Δ hΔ center t = Classical.choose (round_to_grid5 hΔ h) := by
    rw [coordIndex, dif_pos h]
  rw [h']; exact Classical.choose_spec (round_to_grid5 hΔ h)

lemma coord_bound_imp_dist_lt_delta {Δ : ℝ} (hΔ : 0 < Δ)
    {x y : Plane} (hdx : |x 0 - y 0| ≤ 2 * Δ / 5)
    (hdy : |x 1 - y 1| ≤ 2 * Δ / 5) : dist x y < Δ := by
  set a : ℝ := 2 * Δ / 5 with ha
  have ha_pos : 0 < a := by positivity
  have hdx2 : (x 0 - y 0)^2 ≤ a^2 := by
    calc (x 0 - y 0)^2 = |x 0 - y 0|^2 := by rw [sq_abs]
      _ ≤ a^2 := by gcongr
  have hdy2 : (x 1 - y 1)^2 ≤ a^2 := by
    calc (x 1 - y 1)^2 = |x 1 - y 1|^2 := by rw [sq_abs]
      _ ≤ a^2 := by gcongr
  have h_sum2 : (x 0 - y 0)^2 + (x 1 - y 1)^2 ≤ 2 * a^2 := by linarith
  have h_norm_sq : ‖x - y‖ ^ 2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
    have h_pos : 0 ≤ ∑ i : Fin 2, ((x - y) i)^2 := by positivity
    have h4 : ‖x - y‖ = Real.sqrt (∑ i : Fin 2, ‖(x - y) i‖ ^ 2) := by
      rw [EuclideanSpace.norm_eq]
    have h5 : ∑ i : Fin 2, ‖(x - y) i‖ ^ 2 = ∑ i : Fin 2, ((x - y) i)^2 := by
      apply Finset.sum_congr rfl; intro i _; simp [sq_abs]
    rw [h4, h5]
    have h6 : Real.sqrt (∑ i : Fin 2, ((x - y) i)^2) ^ 2 = ∑ i : Fin 2, ((x - y) i)^2 :=
      Real.sq_sqrt h_pos
    rw [h6, Fin.sum_univ_two] <;> simp
  have h_main : ‖x - y‖ ^ 2 ≤ 2 * a^2 := by
    rw [h_norm_sq]; exact h_sum2
  have h7 : (Real.sqrt 2 * a)^2 = 2 * a^2 := by
    have h8 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    calc
      (Real.sqrt 2 * a)^2 = (Real.sqrt 2)^2 * a^2 := by ring
      _ = 2 * a^2 := by rw [h8] <;> ring
  have h_bound : ‖x - y‖ ≤ Real.sqrt 2 * a := by
    by_contra h10
    have h11 : Real.sqrt 2 * a < ‖x - y‖ := by linarith
    have h12 : (Real.sqrt 2 * a)^2 < ‖x - y‖^2 := by
      gcongr <;> positivity
    rw [h7] at h12
    linarith
  have h10 : Real.sqrt 2 * a < Δ := by
    have h11 : Real.sqrt 2 < 5 / 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [ha]
    nlinarith
  exact lt_of_le_of_lt h_bound h10

lemma separated_in_ball_le_25 {Δ : ℝ} (hΔ : 0 < Δ)
    {T : Finset Plane} {center : Plane}
    (hT_in_ball : (T : Set Plane) ⊆ Metric.closedBall center Δ)
    (h_sep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Δ ≤ dist x y) : T.card ≤ 25 := by
  let boxIndex : Plane → Fin 5 × Fin 5 := fun x =>
    (coordIndex Δ hΔ (center 0) (x 0), coordIndex Δ hΔ (center 1) (x 1))
  have h_inj : Set.InjOn boxIndex (T : Set Plane) := by
    intro x hx y hy hbox
    by_contra hxy
    have hx_center : ‖x - center‖ ≤ Δ := hT_in_ball hx
    have hy_center : ‖y - center‖ ≤ Δ := hT_in_ball hy
    have hx0' : |x 0 - center 0| ≤ Δ := by have h : |x 0 - center 0| ≤ ‖x - center‖ := PiLp.norm_apply_le (x - center) 0; linarith
    have hx1' : |x 1 - center 1| ≤ Δ := by have h : |x 1 - center 1| ≤ ‖x - center‖ := PiLp.norm_apply_le (x - center) 1; linarith
    have hy0' : |y 0 - center 0| ≤ Δ := by have h : |y 0 - center 0| ≤ ‖y - center‖ := PiLp.norm_apply_le (y - center) 0; linarith
    have hy1' : |y 1 - center 1| ≤ Δ := by have h : |y 1 - center 1| ≤ ‖y - center‖ := PiLp.norm_apply_le (y - center) 1; linarith
    let k0 := coordIndex Δ hΔ (center 0) (x 0)
    let k1 := coordIndex Δ hΔ (center 1) (x 1)
    have h_same0 : coordIndex Δ hΔ (center 0) (y 0) = k0 := by
      have h : (k0, k1) = (coordIndex Δ hΔ (center 0) (y 0), coordIndex Δ hΔ (center 1) (y 1)) := hbox
      exact Eq.symm (Prod.ext_iff.mp h).1
    have h_same1 : coordIndex Δ hΔ (center 1) (y 1) = k1 := by
      have h : (k0, k1) = (coordIndex Δ hΔ (center 0) (y 0), coordIndex Δ hΔ (center 1) (y 1)) := hbox
      exact Eq.symm (Prod.ext_iff.mp h).2
    have hxb := coordIndex_bounds hΔ hx0'
    have hyb := coordIndex_bounds hΔ hy0'
    have hxb1 := coordIndex_bounds hΔ hx1'
    have hyb1 := coordIndex_bounds hΔ hy1'
    have hdx : |x 0 - y 0| ≤ 2 * Δ / 5 := by
      have h_lo_x : center 0 - Δ + (k0 : ℝ) * (2 * Δ / 5) ≤ x 0 := hxb.1
      have h_hi_x : x 0 ≤ center 0 - Δ + ((k0 : ℝ) + 1) * (2 * Δ / 5) := hxb.2
      have h_lo_y : center 0 - Δ + (k0 : ℝ) * (2 * Δ / 5) ≤ y 0 := by simpa [h_same0] using hyb.1
      have h_hi_y : y 0 ≤ center 0 - Δ + ((k0 : ℝ) + 1) * (2 * Δ / 5) := by simpa [h_same0] using hyb.2
      rw [abs_le] <;> constructor <;> linarith
    have hdy : |x 1 - y 1| ≤ 2 * Δ / 5 := by
      have h_lo_x : center 1 - Δ + (k1 : ℝ) * (2 * Δ / 5) ≤ x 1 := hxb1.1
      have h_hi_x : x 1 ≤ center 1 - Δ + ((k1 : ℝ) + 1) * (2 * Δ / 5) := hxb1.2
      have h_lo_y : center 1 - Δ + (k1 : ℝ) * (2 * Δ / 5) ≤ y 1 := by simpa [h_same1] using hyb1.1
      have h_hi_y : y 1 ≤ center 1 - Δ + ((k1 : ℝ) + 1) * (2 * Δ / 5) := by simpa [h_same1] using hyb1.2
      rw [abs_le] <;> constructor <;> linarith
    have h_dist_lt : dist x y < Δ := coord_bound_imp_dist_lt_delta hΔ hdx hdy
    have h_sep' : Δ ≤ dist x y := h_sep x hx y hy hxy
    linarith
  let Im := T.image boxIndex
  have h_card_image : Im.card = T.card := Finset.card_image_of_injOn h_inj
  have h_sub : Im ⊆ (Finset.univ : Finset (Fin 5 × Fin 5)) := by simp
  have h : Im.card ≤ (Finset.univ : Finset (Fin 5 × Fin 5)).card := Finset.card_le_card h_sub
  rw [h_card_image] at h; simpa using h

lemma card_biUnion_le_sum {α β : Type*} [DecidableEq α]
    (s : Finset β) (f : β → Finset α) :
    (s.biUnion f).card ≤ ∑ x ∈ s, (f x).card := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h : (f a ∪ s.biUnion f).card ≤ (f a).card + (s.biUnion f).card := Finset.card_union_le _ _
    linarith

lemma exists_external_cover_realizing {X : Type*} [PseudoMetricSpace X] {ε : NNReal} {A : Set X}
    (hA_finite : A.Finite) :
    ∃ (C : Set X), C.Finite ∧ Metric.IsCover ε A C ∧ C.encard = Metric.externalCoveringNumber ε A := by
  have h_ne_top : Metric.externalCoveringNumber ε A ≠ ⊤ := by
    have h1 : Metric.externalCoveringNumber ε A ≤ A.encard := Metric.externalCoveringNumber_le_encard_self A
    have h2 : A.encard ≠ ⊤ := (Set.Finite.encard_lt_top hA_finite).ne
    exact ne_top_of_le_ne_top h2 h1
  have h_main : ∃ (C : Set X), Metric.IsCover ε A C ∧ C.encard = Metric.externalCoveringNumber ε A := by
    simp only [Metric.externalCoveringNumber, ne_eq, iInf_eq_top, Set.encard_eq_top_iff, not_forall] at h_ne_top
    obtain ⟨C', hC'_cover, hC'_fin⟩ := h_ne_top
    have : Nonempty { s : Set X // Metric.IsCover ε A s } := ⟨C', hC'_cover⟩
    let h_exists := ENat.exists_eq_iInf (fun C : {s : Set X // Metric.IsCover ε A s} ↦ (C : Set X).encard)
    obtain ⟨C, hC⟩ := h_exists
    refine ⟨C, C.2, ?_⟩
    rw [hC]; simp_rw [iInf_subtype] <;> rfl
  rcases h_main with ⟨C, hC_cover, hC_eq⟩
  have h_lt_top : C.encard < ⊤ := by rw [hC_eq]; exact h_ne_top.lt_top
  have hC_finite : C.Finite := Set.encard_lt_top_iff.mp h_lt_top
  exact ⟨C, hC_finite, hC_cover, hC_eq⟩

lemma a8_packing_bound {S : Finset Plane} {Δ : ℝ} (hΔ_pos : 0 < Δ)
    (hsep : SeparatedAt Δ (S : Set Plane)) :
    (S.card : ENNReal) ≤ 25 * Metric.externalCoveringNumber Δ.toNNReal (S : Set Plane) := by
  let ε : NNReal := ⟨Δ, hΔ_pos.le⟩
  have hε : (ε : ℝ) = Δ := by
    unfold ε
    exact Subtype.coe_mk Δ hΔ_pos.le
  have h_sep' : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Δ ≤ dist x y := by
    intro x hx y hy hxy; exact hsep hx hy hxy
  rcases exists_external_cover_realizing (S.finite_toSet) with ⟨C, hC_finite, hC_cover, hC_eq⟩
  let Cfin : Finset Plane := hC_finite.toFinset
  have hCfin_eq : (Cfin : Set Plane) = C := hC_finite.coe_toFinset
  have h_cover : (S : Set Plane) ⊆ ⋃ c ∈ C, Metric.closedBall c ε := by
    rw [Metric.isCover_iff_subset_iUnion_closedBall] at hC_cover; exact hC_cover
  let f : Plane → Finset Plane := fun c => S.filter fun x => x ∈ Metric.closedBall c ε
  have h_union : S = Cfin.biUnion f := by
    ext z; simp only [Finset.mem_biUnion, f, Finset.mem_filter]
    constructor
    · intro hz
      have hcov : z ∈ ⋃ c ∈ C, Metric.closedBall c ε := h_cover hz
      have hcov' : ∃ (c : Plane), c ∈ C ∧ z ∈ Metric.closedBall c ε := by simpa [Set.mem_iUnion] using hcov
      rcases hcov' with ⟨c, hcC, hcball⟩
      have hcCfin : c ∈ Cfin := by
        have h : c ∈ (Cfin : Set Plane) := by rw [hCfin_eq]; exact hcC
        exact h
      exact ⟨c, hcCfin, hz, hcball⟩
    · rintro ⟨c, hcCfin, hz, _⟩; exact hz
  have h2 : ∀ c ∈ Cfin, (f c).card ≤ 25 := by
    intro c _
    let T := f c
    have hT_sub : (T : Set Plane) ⊆ Metric.closedBall c Δ := by
      intro x hx; have h_in : x ∈ Metric.closedBall c ε := (Finset.mem_filter.mp hx).2; simpa [hε] using h_in
    have hT_sep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Δ ≤ dist x y := by
      intro x hx y hy hxy
      have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
      have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
      exact h_sep' x hxS y hyS hxy
    exact separated_in_ball_le_25 hΔ_pos hT_sub hT_sep
  have h_main : S.card ≤ 25 * Cfin.card := by
    calc S.card = (Cfin.biUnion f).card := by rw [h_union]
      _ ≤ ∑ c ∈ Cfin, (f c).card := card_biUnion_le_sum Cfin f
      _ ≤ ∑ c ∈ Cfin, 25 := by gcongr <;> exact h2 c ‹_›
      _ = 25 * Cfin.card := by simp [Finset.sum_const] <;> ring
  have h3 : (Cfin.card : ENNReal) = Metric.externalCoveringNumber ε (S : Set Plane) := by
    have h4 : (Cfin.card : ENNReal) = C.encard := by rw [← hCfin_eq] <;> simp
    rw [h4, hC_eq]
  have h5 : (S.card : ENNReal) ≤ 25 * (Cfin.card : ENNReal) := by exact_mod_cast h_main
  have h6 : (Cfin.card : ENNReal) = Metric.externalCoveringNumber Δ.toNNReal (S : Set Plane) := by
    have h7 : (ε : ℝ) = (Δ.toNNReal : ℝ) := by
      have h8 : (ε : ℝ) = Δ := hε
      have h9 : (Δ.toNNReal : ℝ) = Δ := by
        have h10 : 0 ≤ Δ := hΔ_pos.le
        simp [Real.toNNReal, h10] <;> linarith
      rw [h8, h9]
    have h7' : ε = Δ.toNNReal := NNReal.coe_injective h7
    rw [h7'] at h3
    exact h3
  rw [h6] at h5
  exact h5

/-- Transfer δ-scale S-set from T_Q to fineTubes subset using cardinality ratio.
    N_δ(T_Q) ≤ |T_Q| ≤ M
    |fineTubes| ≤ K_affine * N_δ(fineTubes)  (packing bound)
    |fineTubes| ≥ Δ^{-s+34ε}
    Therefore N_δ(T_Q) ≤ M * K_affine * Δ^{s-34ε} * N_δ(fineTubes) -/
lemma a8_fine_tubes_sset_transfer
    {δ Δ s ε C M : ℝ}
    {T_Q fineTubes : Finset FineTube}
    (hδ_pos : 0 < δ)
    (hΔ_pos : 0 < Δ)
    (hC_pos : 0 < C)
    (hM_pos : 0 < M)
    (h_pack_pos : 0 < (MainAppendix.affineLine_packing_constant : ℝ))
    (h_orig_sset : IsDeltaSSet δ s C (T_Q : Set FineTube))
    (h_sub : (fineTubes : Set FineTube) ⊆ (T_Q : Set FineTube))
    (h_sep : SeparatedAt (δ / 2) (fineTubes : Set FineTube))
    (h_card_TQ_upper : (T_Q.card : ℝ) ≤ M)
    (h_card_fine_lower : Real.rpow Δ (-s + 40 * ε) ≤ (fineTubes.card : ℝ)) :
    IsDeltaSSet δ s (C * M * (MainAppendix.affineLine_packing_constant : ℝ) * Real.rpow Δ (s - 40 * ε))
      (fineTubes : Set FineTube) := by
  let K_affine := (MainAppendix.affineLine_packing_constant : ℝ)
  let D := M * K_affine * Real.rpow Δ (s - 40 * ε)
  have hD_pos : 0 < D := by
    dsimp only [D, K_affine]
    apply mul_pos
    · apply mul_pos
      · exact hM_pos
      · exact h_pack_pos
    · exact Real.rpow_pos_of_pos hΔ_pos _
  let δnn : NNReal := δ.toNNReal
  let rnn : NNReal := (δ / 2).toNNReal
  have hδnn_eq : (δnn : ℝ) = δ := by
    have h : (δnn : ℝ) = max δ 0 := by rfl
    rw [h, max_eq_left hδ_pos.le]
  have h2pos : 0 ≤ δ / 2 := by linarith [hδ_pos]
  have hrnn_eq : (rnn : ℝ) = δ / 2 := by
    have h : (rnn : ℝ) = max (δ / 2) 0 := by rfl
    rw [h, max_eq_left h2pos]
  have h2r : 2 * rnn = δnn := by
    apply NNReal.coe_injective
    simp [hδnn_eq, hrnn_eq] <;> ring
  have hM_nonneg : 0 ≤ M := by linarith
  have hKaff_nonneg : 0 ≤ K_affine := by positivity
  have hrpow_nonneg : 0 ≤ Real.rpow Δ (s - 40 * ε) := Real.rpow_nonneg hΔ_pos.le _
  have hrpow2_nonneg : 0 ≤ Real.rpow Δ (-s + 40 * ε) := Real.rpow_nonneg hΔ_pos.le _
  -- N_δ(T_Q) ≤ |T_Q| ≤ M
  have h1 : (Metric.externalCoveringNumber δnn (T_Q : Set FineTube) : ENNReal) ≤
      ENNReal.ofReal M := by
    have h11 : Metric.externalCoveringNumber δnn (T_Q : Set FineTube) ≤
        (T_Q : Set FineTube).encard := Metric.externalCoveringNumber_le_encard_self _
    have h12 : (T_Q : Set FineTube).encard = ↑(T_Q.card) := by simp
    have h13 : (Metric.externalCoveringNumber δnn (T_Q : Set FineTube) : ENNReal) ≤ (↑(T_Q.card) : ENNReal) := by
      exact_mod_cast h11
    have h14 : ((T_Q.card : ℝ) ≤ M) := h_card_TQ_upper
    calc (Metric.externalCoveringNumber δnn (T_Q : Set FineTube) : ENNReal)
      ≤ (↑(T_Q.card) : ENNReal) := h13
    _ = ENNReal.ofReal ((T_Q.card : ℝ)) := by simp
    _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal h14
  -- Packing bound: |fineTubes| ≤ K_affine * N_δ(fineTubes) using half-separation
  have h_pack_arg : ∀ (z : AffineLine) (T : Set AffineLine),
      Set.Pairwise T (fun x y => (rnn : ℝ) ≤ dist x y) →
      T ⊆ Metric.closedBall z (2 * (rnn : ℝ)) →
      T.Finite ∧ T.encard ≤ (MainAppendix.affineLine_packing_constant : ENat) := by
    intro z T hsep hsub
    have hsep' : Set.Pairwise T (fun x y => (δ / 2 : ℝ) ≤ dist x y) := by
      simpa [hrnn_eq] using hsep
    have hsub' : T ⊆ Metric.closedBall z (2 * (δ / 2 : ℝ)) := by
      simpa [hrnn_eq] using hsub
    have hδ2_pos : 0 < δ / 2 := by linarith
    exact MainAppendix.affineLine_packing_bound (δ / 2) hδ2_pos hsep' z hsub'
  have h_sep' : Set.Pairwise (fineTubes : Set FineTube) (fun x y => (rnn : ℝ) ≤ dist x y) := by
    intro x hx y hy hne
    have h : (δ / 2 : ℝ) ≤ dist x y := h_sep hx hy hne
    have h' : (rnn : ℝ) ≤ dist x y := by rw [hrnn_eq]; exact h
    exact h'
  have hcov_fin : (Metric.externalCoveringNumber δnn (fineTubes : Set FineTube) : ENNReal) < ⊤ := by
    have h : Metric.externalCoveringNumber δnn (fineTubes : Set FineTube) ≤
        (fineTubes : Set FineTube).encard := Metric.externalCoveringNumber_le_encard_self _
    have h' : (Metric.externalCoveringNumber δnn (fineTubes : Set FineTube) : ENNReal) ≤
        ((fineTubes.card) : ENNReal) := by
      have h2 : (fineTubes : Set FineTube).encard = ↑(fineTubes.card) := by simp
      rw [h2] at h; exact_mod_cast h
    exact h'.trans_lt (ENNReal.coe_lt_top)
  have h4 : ((fineTubes : Set FineTube).encard : ENNReal) ≤
      (MainAppendix.affineLine_packing_constant : ENNReal) *
      Metric.externalCoveringNumber δnn (fineTubes : Set FineTube) :=
    A2.separated_set_card_le_covering_half h2r h_sep'
      MainAppendix.affineLine_packing_constant h_pack_arg hcov_fin
  have h5 : ((fineTubes.card) : ENNReal) = ((fineTubes : Set FineTube).encard : ENNReal) := by simp
  have h6 : ((fineTubes.card) : ENNReal) ≤
      (MainAppendix.affineLine_packing_constant : ENNReal) *
      Metric.externalCoveringNumber δnn (fineTubes : Set FineTube) := by
    rw [h5] <;> exact h4
  -- |fineTubes| ≥ Δ^{-s+34ε}
  have h7 : ENNReal.ofReal (Real.rpow Δ (-s + 40 * ε)) ≤ ((fineTubes.card) : ENNReal) := by
    have h71 : Real.rpow Δ (-s + 40 * ε) ≤ (fineTubes.card : ℝ) := h_card_fine_lower
    simpa using ENNReal.ofReal_le_ofReal h71
  have h8 : ENNReal.ofReal (Real.rpow Δ (-s + 40 * ε)) ≤
      (MainAppendix.affineLine_packing_constant : ENNReal) *
      Metric.externalCoveringNumber δnn (fineTubes : Set FineTube) :=
    le_trans h7 h6
  -- Multiply both sides by M * Δ^{s-34ε} to get M ≤ D * N_δ(fineTubes)
  have h9 : ENNReal.ofReal M ≤
      ENNReal.ofReal D * Metric.externalCoveringNumber δnn (fineTubes : Set FineTube) := by
    set N := Metric.externalCoveringNumber δnn (fineTubes : Set FineTube) with hN
    set K_affine_nn : ENNReal := ↑MainAppendix.affineLine_packing_constant with hKaff_nn
    have hKaff_coe : K_affine_nn = ENNReal.ofReal K_affine := by
      simp [hKaff_nn, K_affine] <;> rfl
    have h10 : ENNReal.ofReal (M * Real.rpow Δ (s - 40 * ε)) *
        ENNReal.ofReal (Real.rpow Δ (-s + 40 * ε)) ≤
        ENNReal.ofReal (M * Real.rpow Δ (s - 40 * ε)) * (K_affine_nn * N) := by
      exact mul_le_mul_of_nonneg_left h8 (by positivity)
    have h11 : ENNReal.ofReal (M * Real.rpow Δ (s - 40 * ε)) *
        ENNReal.ofReal (Real.rpow Δ (-s + 40 * ε)) = ENNReal.ofReal M := by
      have h12 : 0 ≤ M * Real.rpow Δ (s - 40 * ε) := by positivity
      rw [← ENNReal.ofReal_mul h12]
      have h14 : (M * Real.rpow Δ (s - 40 * ε)) * Real.rpow Δ (-s + 40 * ε) = M := by
        have h_sum : (s - 40 * ε) + (-s + 40 * ε) = 0 := by ring
        have h15 : Real.rpow Δ (s - 40 * ε) * Real.rpow Δ (-s + 40 * ε) = 1 := by
          have h16 : Real.rpow Δ (s - 40 * ε) * Real.rpow Δ (-s + 40 * ε) =
              Real.rpow Δ ((s - 40 * ε) + (-s + 40 * ε)) :=
            (Real.rpow_add hΔ_pos _ _).symm
          rw [h16, h_sum]
          <;> simp
        calc
          (M * Real.rpow Δ (s - 40 * ε)) * Real.rpow Δ (-s + 40 * ε)
            = M * (Real.rpow Δ (s - 40 * ε) * Real.rpow Δ (-s + 40 * ε)) := by ring
          _ = M * 1 := by rw [h15]
          _ = M := by ring
      rw [h14]
    have h15 : ENNReal.ofReal (M * Real.rpow Δ (s - 40 * ε)) * (K_affine_nn * N) =
        ENNReal.ofReal D * N := by
      have h16 : D = M * Real.rpow Δ (s - 40 * ε) * K_affine := by
        simp [D, K_affine] <;> ring
      rw [h16]
      have h17 : ENNReal.ofReal (M * Real.rpow Δ (s - 40 * ε)) * (K_affine_nn * N) =
          (ENNReal.ofReal (M * Real.rpow Δ (s - 40 * ε)) * K_affine_nn) * N := by
        simp [mul_assoc] <;> ring
      rw [h17]
      have h18 : ENNReal.ofReal (M * Real.rpow Δ (s - 40 * ε)) * K_affine_nn =
          ENNReal.ofReal (M * Real.rpow Δ (s - 40 * ε) * K_affine) := by
        rw [hKaff_coe]
        have h19 : 0 ≤ M * Real.rpow Δ (s - 40 * ε) := by positivity
        rw [← ENNReal.ofReal_mul h19] <;> rfl
      rw [h18]
    rw [h11, h15] at h10
    exact h10
  have h_factor : (Metric.externalCoveringNumber δnn (T_Q : Set FineTube) : ENNReal) ≤
      ENNReal.ofReal D * Metric.externalCoveringNumber δnn (fineTubes : Set FineTube) :=
    le_trans h1 h9
  have h_result : IsDeltaSSet δ s (D * C) (fineTubes : Set FineTube) :=
    A2.IsDeltaSSet.transfer_subset h_orig_sset h_sub hD_pos h_factor
  have h_comm : D * C = C * M * K_affine * Real.rpow Δ (s - 40 * ε) := by
    simp [D, K_affine] <;> ring
  rw [h_comm] at h_result
  exact h_result

/-! ========================================================================
   Main A8: Fine-fiber popularity from H2
   ======================================================================== -/

/-- A8 fine-fiber popularity: given A5 + A7 output, extract popular points
    and fine fibers for each square in Q0.

    Uses canonical A5_Output/A7_Output/A8_Output interfaces.
    Requires `hΔ_small : 25 ≤ Δ^{-2ε}` for the projection robustness transfer
    (canonical ProjectionData.h_robust uses Δ^{-20ε}). -/
def A8_fine_fiber_popularity
    (Δ δ s t ε : ℝ)
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hδ_eq : δ = Δ ^ 2)
    (hs : 0 < s) (hst : s < t) (hε_pos : 0 < ε)
    (hΔ_small : (25 : ℝ) ≤ Real.rpow Δ (-2 * ε))
    (h50_le_DeltainvEps : (50 : ℝ) ≤ Real.rpow Δ (-ε))
    (a7 : A7_Output Δ δ s t ε) :
    A8_Output Δ δ s t ε := by
  classical
  let a5 := a7.a5
  let T0 := a7.T0
  let Q0 := a7.Q0

  let perSquare (Q : CoarseSquare Δ) (hQ : Q ∈ Q0) : A8_SquareData Δ δ s t ε T0 Q := by
    let a4 := a5.perSquare Q (a7.hQ0_sub hQ)
    let base := a4.base
    have hT0_in : T0 ∈ a4.C_Q_pi := by
      simpa [T0, a4, a5] using a7.hT0_in_Cpi Q hQ
    let proj_Q := a4.projData T0 hT0_in
    let orig : Plane → Plane := fun p => Δ • p + a4.z_Q
    have h_orig_in_PQ : ∀ p ∈ a4.P_norm, orig p ∈ base.P_Q := a4.hP_norm_unnormalize
    have h_orig_inj : Set.InjOn orig (a4.P_norm : Set Plane) := by
      intro p _ q _ h
      have hsmul : Δ • p = Δ • q := by simpa [orig] using h
      ext i
      have h_eq : Δ * p i = Δ * q i := by
        have h : (Δ • p) i = (Δ • q) i := by rw [hsmul]
        simpa [Pi.smul_apply] using h
      exact (mul_right_inj' hΔ_pos.ne').mp h_eq
    let P_norm_img : Finset Plane := a4.P_norm.image orig
    have h_img_sub : P_norm_img ⊆ base.P_Q := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
      exact h_orig_in_PQ p hp
    have h_img_card : P_norm_img.card = base.P_Q.card := by
      have h1 : P_norm_img.card = a4.P_norm.card := Finset.card_image_of_injOn h_orig_inj
      have h2 : (P_norm_img.card : ℝ) = (base.P_Q.card : ℝ) := by
        rw [h1]
        exact a4.hP_norm_card
      exact_mod_cast h2
    have h_img_eq : P_norm_img = base.P_Q :=
      Finset.eq_of_subset_of_card_le h_img_sub (by rw [h_img_card])
    let f : Plane → ℕ := fun p_norm =>
      if h : p_norm ∈ a4.P_norm then
        (pointFiber Δ base.hΔ_pos base.T_Q (orig p_norm) T0).card
      else 0
    let H : ℝ := base.H_Q
    let U : ℝ := Real.rpow Δ (-s - 7 * ε)
    let P_max : ℝ := Real.rpow Δ (-t - 3 * ε)
    have hH_pos : 0 < H := base.hH_Q_pos
    have hU_pos : 0 < U := Real.rpow_pos_of_pos hΔ_pos _
    have hPmax_pos : 0 < P_max := Real.rpow_pos_of_pos hΔ_pos _
    let g : Plane → ℕ := fun p =>
      if h : p ∈ base.P_Q then
        (pointFiber Δ base.hΔ_pos base.T_Q p T0).card
      else 0
    have h_sum_transfer : ∑ p_norm ∈ a4.P_norm, (f p_norm : ℝ) = ∑ p ∈ base.P_Q, (g p : ℝ) := by
      have h1 : ∑ p_norm ∈ a4.P_norm, (f p_norm : ℝ) = ∑ q ∈ P_norm_img, (g q : ℝ) := by
        rw [Finset.sum_image h_orig_inj]
        apply Finset.sum_congr rfl
        intro p hp
        have h2 : f p = g (orig p) := by
          have hpin : p ∈ a4.P_norm := hp
          have hq : orig p ∈ base.P_Q := h_orig_in_PQ p hpin
          unfold f g
          rw [dif_pos hpin, dif_pos hq] <;> rfl
        exact_mod_cast h2
      rw [h1, h_img_eq]
    have hT0_in_CQ : T0 ∈ base.C_Q := a4.hC_Q_pi_sub hT0_in
    have hH2 : H ≤ ∑ p ∈ base.P_Q, (g p : ℝ) := by
      have h_orig : H ≤ ∑ p ∈ base.P_Q, (pointFiber Δ base.hΔ_pos base.T_Q p T0).card :=
        base.hH2 T0 hT0_in_CQ
      have h_eq : ∑ p ∈ base.P_Q, (g p : ℝ) = ↑(∑ p ∈ base.P_Q, (pointFiber Δ base.hΔ_pos base.T_Q p T0).card) := by
        have h1 : ∑ p ∈ base.P_Q, (g p : ℝ) = ∑ p ∈ base.P_Q, ↑((pointFiber Δ base.hΔ_pos base.T_Q p T0).card) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hgp : g p = (pointFiber Δ base.hΔ_pos base.T_Q p T0).card := by
            unfold g
            rw [dif_pos hp]
          rw [hgp]
        rw [h1, Nat.cast_sum]
      rw [h_eq]
      exact h_orig
    have hH2' : H ≤ ∑ p_norm ∈ a4.P_norm, (f p_norm : ℝ) := by
      rw [h_sum_transfer]; exact hH2
    have h_upper : ∀ p ∈ a4.P_norm, (f p : ℝ) ≤ U := by
      intro p hp
      have hq : orig p ∈ base.P_Q := h_orig_in_PQ p hp
      have h_eq : f p = (pointFiber Δ base.hΔ_pos base.T_Q (orig p) T0).card := by
        simp [f, hp] <;> rfl
      rw [h_eq]
      exact base.h_pointFiber_upper (orig p) hq T0 hT0_in_CQ
    have h_card : (a4.P_norm.card : ℝ) ≤ P_max := by
      have h1 : (a4.P_norm.card : ℝ) = (base.P_Q.card : ℝ) := by exact_mod_cast a4.hP_norm_card
      rw [h1]; exact base.hP_Q_card_upper
    have h2_le_DeltainvEps : (2 : ℝ) ≤ Real.rpow Δ (-ε) := by
      set x := Real.rpow Δ (-ε) with hx
      have hx_pos : 0 < x := Real.rpow_pos_of_pos hΔ_pos _
      have h_sq : x ^ 2 = Real.rpow Δ (-2 * ε) := by
        simp only [hx]
        have h5 : -2 * ε = -ε + -ε := by ring
        have h61 : Real.rpow Δ (-ε + -ε) = Real.rpow Δ (-ε) * Real.rpow Δ (-ε) :=
          Real.rpow_add hΔ_pos (-ε) (-ε)
        have h6 : Real.rpow Δ (-2 * ε) = Real.rpow Δ (-ε) ^ 2 := by
          rw [h5, h61] <;> ring
        exact h6.symm
      have h4 : x ^ 2 ≥ 25 := by
        rw [h_sq]; exact hΔ_small
      have h5 : 5 ≤ x := by
        nlinarith [sq_nonneg (x - 5)]
      linarith
    have h_eps_le_half : Real.rpow Δ ε ≤ 1 / 2 := by
      have h_pos : 0 < Real.rpow Δ ε := Real.rpow_pos_of_pos hΔ_pos _
      have h_mul : Real.rpow Δ ε * Real.rpow Δ (-ε) = 1 := by
        have h_sum : ε + (-ε) = 0 := by ring
        have h := Real.rpow_add hΔ_pos ε (-ε)
        have h2 : Real.rpow Δ (ε + (-ε)) = Real.rpow Δ ε * Real.rpow Δ (-ε) := h
        rw [h_sum] at h2
        have h3 : Real.rpow Δ 0 = 1 := by simp
        rw [h3] at h2
        exact h2.symm
      have h6 : Real.rpow Δ (-ε) ≥ 2 := h2_le_DeltainvEps
      nlinarith
    have h_card_out : Real.rpow Δ (-t + 44 * ε) ≤ H / (2 * U) := by
      have hH : H ≥ Real.rpow Δ (-(s + t) + 36 * ε) := a4.hH_Q_lower
      have h_posU : 0 < 2 * U := by positivity
      have h_main : 2 * Real.rpow Δ (-t + 44 * ε) * U ≤ Real.rpow Δ (-(s + t) + 36 * ε) := by
        have h_sum1 : (-t + 44 * ε) + (-s - 7 * ε) = -(s + t) + 37 * ε := by ring
        have h_mul : Real.rpow Δ (-t + 44 * ε) * U = Real.rpow Δ (-(s + t) + 37 * ε) := by
          have hU : U = Real.rpow Δ (-s - 7 * ε) := by rfl
          have h_rpow : Real.rpow Δ ((-t + 44 * ε) + (-s - 7 * ε)) =
              Real.rpow Δ (-t + 44 * ε) * Real.rpow Δ (-s - 7 * ε) :=
            Real.rpow_add hΔ_pos (-t + 44 * ε) (-s - 7 * ε)
          rw [h_sum1] at h_rpow
          rw [hU]
          exact h_rpow.symm
        have h_assoc : 2 * Real.rpow Δ (-t + 44 * ε) * U =
            2 * (Real.rpow Δ (-t + 44 * ε) * U) := by ring
        rw [h_assoc, h_mul]
        have h_decomp : Real.rpow Δ (-(s + t) + 37 * ε) =
            Real.rpow Δ (-(s + t) + 36 * ε) * Real.rpow Δ ε := by
          have h_sum2 : (-(s + t) + 36 * ε) + ε = -(s + t) + 37 * ε := by ring
          have h_rpow2 : Real.rpow Δ ((-(s + t) + 36 * ε) + ε) =
              Real.rpow Δ (-(s + t) + 36 * ε) * Real.rpow Δ ε :=
            Real.rpow_add hΔ_pos (-(s + t) + 36 * ε) ε
          rw [h_sum2] at h_rpow2
          exact h_rpow2
        rw [h_decomp]
        have h_pos2 : 0 < Real.rpow Δ (-(s + t) + 36 * ε) := Real.rpow_pos_of_pos hΔ_pos _
        have h_eps : Real.rpow Δ ε ≤ 1 / 2 := h_eps_le_half
        nlinarith
      calc Real.rpow Δ (-t + 44 * ε)
        = (2 * Real.rpow Δ (-t + 44 * ε) * U) / (2 * U) := by field_simp [h_posU.ne'] <;> ring
      _ ≤ Real.rpow Δ (-(s + t) + 36 * ε) / (2 * U) := by gcongr
      _ ≤ H / (2 * U) := by gcongr
    have h_fine_lower_out : Real.rpow Δ (-s + 40 * ε) ≤ H / (2 * P_max) := by
      have hH : H ≥ Real.rpow Δ (-(s + t) + 36 * ε) := a4.hH_Q_lower
      have h_posP : 0 < 2 * P_max := by positivity
      have h_main : 2 * Real.rpow Δ (-s + 40 * ε) * P_max ≤ Real.rpow Δ (-(s + t) + 36 * ε) := by
        have h_sum1 : (-s + 40 * ε) + (-t - 3 * ε) = -(s + t) + 37 * ε := by ring
        have h_mul : Real.rpow Δ (-s + 40 * ε) * P_max = Real.rpow Δ (-(s + t) + 37 * ε) := by
          have hP : P_max = Real.rpow Δ (-t - 3 * ε) := by rfl
          have h_rpow : Real.rpow Δ ((-s + 40 * ε) + (-t - 3 * ε)) =
              Real.rpow Δ (-s + 40 * ε) * Real.rpow Δ (-t - 3 * ε) :=
            Real.rpow_add hΔ_pos (-s + 40 * ε) (-t - 3 * ε)
          rw [h_sum1] at h_rpow
          rw [hP]
          exact h_rpow.symm
        have h_assoc : 2 * Real.rpow Δ (-s + 40 * ε) * P_max =
            2 * (Real.rpow Δ (-s + 40 * ε) * P_max) := by ring
        rw [h_assoc, h_mul]
        have h_decomp : Real.rpow Δ (-(s + t) + 37 * ε) =
            Real.rpow Δ (-(s + t) + 36 * ε) * Real.rpow Δ ε := by
          have h_sum2 : (-(s + t) + 36 * ε) + ε = -(s + t) + 37 * ε := by ring
          have h_rpow2 : Real.rpow Δ ((-(s + t) + 36 * ε) + ε) =
              Real.rpow Δ (-(s + t) + 36 * ε) * Real.rpow Δ ε :=
            Real.rpow_add hΔ_pos (-(s + t) + 36 * ε) ε
          rw [h_sum2] at h_rpow2
          exact h_rpow2
        rw [h_decomp]
        have h_pos2 : 0 < Real.rpow Δ (-(s + t) + 36 * ε) := Real.rpow_pos_of_pos hΔ_pos _
        have h_eps : Real.rpow Δ ε ≤ 1 / 2 := h_eps_le_half
        nlinarith
      calc Real.rpow Δ (-s + 40 * ε)
        = (2 * Real.rpow Δ (-s + 40 * ε) * P_max) / (2 * P_max) := by field_simp [h_posP.ne'] <;> ring
      _ ≤ Real.rpow Δ (-(s + t) + 36 * ε) / (2 * P_max) := by gcongr
      _ ≤ H / (2 * P_max) := by gcongr
    have h_exists : ∃ (P' : Finset Plane), P' ⊆ a4.P_norm ∧
        (P'.card : ℝ) ≥ H / (2 * U) ∧ ∀ p ∈ P', (f p : ℝ) ≥ H / (2 * P_max) :=
      A8_fine_fiber_popularity_abstract a4.P_norm f H U P_max
        hH_pos hU_pos hPmax_pos hH2' h_upper h_card
    let P'_Q : Finset Plane := Classical.choose h_exists
    have hP'_Q_sub : P'_Q ⊆ a4.P_norm := (Classical.choose_spec h_exists).1
    have hP'_Q_card : (P'_Q.card : ℝ) ≥ H / (2 * U) := (Classical.choose_spec h_exists).2.1
    have h_high : ∀ p ∈ P'_Q, (f p : ℝ) ≥ H / (2 * P_max) := (Classical.choose_spec h_exists).2.2
    let fineTubes : Plane → Finset FineTube := fun p_norm =>
      if h : p_norm ∈ a4.P_norm then
        pointFiber Δ base.hΔ_pos base.T_Q (orig p_norm) T0
      else ∅
    have hP_norm_separated : SeparatedAt Δ (a4.P_norm : Set Plane) := a4.hP_norm_separated
    have h_card_ratio_exact : (a4.P_norm.card : ℝ) ≤
        2 * Real.rpow Δ (-46 * ε) * (P'_Q.card : ℝ) := by
      have h1 : (a4.P_norm.card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε) := h_card
      have hH : H ≥ Real.rpow Δ (-(s + t) + 36 * ε) := a4.hH_Q_lower
      have h_posU : 0 < U := hU_pos
      have h_lower2 : H / (2 * U) ≥ (1 / 2 : ℝ) * Real.rpow Δ (-t + 43 * ε) := by
        have hU_def : U = Real.rpow Δ (-s - 7 * ε) := by rfl
        have h_mul : Real.rpow Δ (-(s + t) + 36 * ε) / (2 * Real.rpow Δ (-s - 7 * ε)) =
            (1 / 2 : ℝ) * Real.rpow Δ (-t + 43 * ε) := by
          have h_sum : (-(s + t) + 36 * ε) - (-s - 7 * ε) = -t + 43 * ε := by ring
          have h_div : Real.rpow Δ (-(s + t) + 36 * ε) / Real.rpow Δ (-s - 7 * ε) =
              Real.rpow Δ ((-(s + t) + 36 * ε) - (-s - 7 * ε)) :=
            (Real.rpow_sub hΔ_pos _ _).symm
          have h9 : Real.rpow Δ (-(s + t) + 36 * ε) / (2 * Real.rpow Δ (-s - 7 * ε)) =
              (1 / 2 : ℝ) * (Real.rpow Δ (-(s + t) + 36 * ε) / Real.rpow Δ (-s - 7 * ε)) := by ring
          rw [h9, h_div, h_sum] <;> ring
        have hH2 : H ≥ Real.rpow Δ (-(s + t) + 36 * ε) := a4.hH_Q_lower
        rw [hU_def]
        calc H / (2 * Real.rpow Δ (-s - 7 * ε))
          ≥ Real.rpow Δ (-(s + t) + 36 * ε) / (2 * Real.rpow Δ (-s - 7 * ε)) := by gcongr
        _ = (1 / 2 : ℝ) * Real.rpow Δ (-t + 43 * ε) := h_mul
      have h2 : (P'_Q.card : ℝ) ≥ H / (2 * U) := hP'_Q_card
      have h3 : (P'_Q.card : ℝ) ≥ (1 / 2 : ℝ) * Real.rpow Δ (-t + 43 * ε) :=
        le_trans h_lower2 h2
      have hpos46 : 0 ≤ Real.rpow Δ (-46 * ε) := Real.rpow_nonneg hΔ_pos.le _
      have h4 : 2 * Real.rpow Δ (-46 * ε) * (P'_Q.card : ℝ) ≥
          2 * Real.rpow Δ (-46 * ε) * ((1 / 2 : ℝ) * Real.rpow Δ (-t + 43 * ε)) := by
        gcongr
        <;> linarith [hpos46]
      have h5 : 2 * Real.rpow Δ (-46 * ε) * ((1 / 2 : ℝ) * Real.rpow Δ (-t + 43 * ε)) =
          Real.rpow Δ (-t - 3 * ε) := by
        have h_sum : (-46 * ε) + (-t + 43 * ε) = -t - 3 * ε := by ring
        have h_rpow : Real.rpow Δ ((-46 * ε) + (-t + 43 * ε)) =
            Real.rpow Δ (-46 * ε) * Real.rpow Δ (-t + 43 * ε) :=
          Real.rpow_add hΔ_pos (-46 * ε) (-t + 43 * ε)
        rw [h_sum] at h_rpow
        linarith
      calc (a4.P_norm.card : ℝ)
        ≤ Real.rpow Δ (-t - 3 * ε) := h1
      _ ≤ 2 * Real.rpow Δ (-46 * ε) * (P'_Q.card : ℝ) := le_trans h5.symm.le h4
    have h_pack_P' : (P'_Q.card : ENNReal) ≤
        25 * Metric.externalCoveringNumber Δ.toNNReal (P'_Q : Set Plane) :=
      a8_packing_bound hΔ_pos (hP_norm_separated.mono hP'_Q_sub)
    have h_cover_P_norm : (Metric.externalCoveringNumber Δ.toNNReal (a4.P_norm : Set Plane) : ENNReal) ≤
        (a4.P_norm.card : ENNReal) := by
      have h1 : Metric.externalCoveringNumber Δ.toNNReal (a4.P_norm : Set Plane) ≤
          (a4.P_norm : Set Plane).encard :=
        Metric.externalCoveringNumber_le_encard_self (a4.P_norm : Set Plane)
      have h2 : (a4.P_norm : Set Plane).encard = ↑a4.P_norm.card := by simp
      rw [h2] at h1
      exact_mod_cast h1
    have h4_exact : (a4.P_norm.card : ENNReal) ≤
        ENNReal.ofReal (2 * Real.rpow Δ (-46 * ε)) * (P'_Q.card : ENNReal) := by
      have h46pos : 0 ≤ 2 * Real.rpow Δ (-46 * ε) :=
        mul_nonneg (by norm_num) (Real.rpow_nonneg hΔ_pos.le _)
      have h46 : ENNReal.ofReal ((a4.P_norm.card : ℝ)) ≤
          ENNReal.ofReal (2 * Real.rpow Δ (-46 * ε) * (P'_Q.card : ℝ)) :=
        ENNReal.ofReal_le_ofReal h_card_ratio_exact
      have h47 : ENNReal.ofReal (2 * Real.rpow Δ (-46 * ε) * (P'_Q.card : ℝ)) =
          ENNReal.ofReal (2 * Real.rpow Δ (-46 * ε)) * ENNReal.ofReal ((P'_Q.card : ℝ)) := by
        rw [ENNReal.ofReal_mul h46pos]
      have h48 : ENNReal.ofReal ((a4.P_norm.card : ℝ)) = (a4.P_norm.card : ENNReal) := by simp
      have h49 : ENNReal.ofReal ((P'_Q.card : ℝ)) = (P'_Q.card : ENNReal) := by simp
      rw [h47, h48, h49] at h46
      exact h46
    have h67_new : (50 : ℝ) * Real.rpow Δ (-46 * ε) ≤ Real.rpow Δ (-47 * ε) := by
      have h68 : (50 : ℝ) ≤ Real.rpow Δ (-ε) := h50_le_DeltainvEps
      have h69 : Real.rpow Δ (-47 * ε) = Real.rpow Δ (-ε) * Real.rpow Δ (-46 * ε) := by
        have h_sum : (-ε) + (-46 * ε) = -47 * ε := by ring
        have h : Real.rpow Δ ((-ε) + (-46 * ε)) = Real.rpow Δ (-ε) * Real.rpow Δ (-46 * ε) :=
          Real.rpow_add hΔ_pos _ _
        rw [h_sum] at h
        exact h
      rw [h69]
      have h70 : 0 ≤ Real.rpow Δ (-46 * ε) := Real.rpow_nonneg hΔ_pos.le _
      nlinarith
    have h_const_new : (25 : ENNReal) * ENNReal.ofReal (2 * Real.rpow Δ (-46 * ε)) ≤
        ENNReal.ofReal (Real.rpow Δ (-47 * ε)) := by
      have h71 : (25 : ENNReal) * ENNReal.ofReal (2 * Real.rpow Δ (-46 * ε)) =
          ENNReal.ofReal ((50 : ℝ) * Real.rpow Δ (-46 * ε)) := by
        have h : (25 : ENNReal) = ENNReal.ofReal (25 : ℝ) := by norm_cast
        rw [h]
        have h2 : ENNReal.ofReal (25 : ℝ) * ENNReal.ofReal (2 * Real.rpow Δ (-46 * ε)) =
            ENNReal.ofReal ((25 : ℝ) * (2 * Real.rpow Δ (-46 * ε))) := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ (25 : ℝ))]
        rw [h2]
        have h3 : (25 : ℝ) * (2 * Real.rpow Δ (-46 * ε)) = (50 : ℝ) * Real.rpow Δ (-46 * ε) := by ring
        rw [h3]
      rw [h71]
      exact ENNReal.ofReal_le_ofReal h67_new
    have h_cover_cond47 : Metric.externalCoveringNumber Δ.toNNReal (a4.P_norm : Set Plane) ≤
        ENNReal.ofReal (Real.rpow Δ (-47 * ε)) *
        Metric.externalCoveringNumber Δ.toNNReal (P'_Q : Set Plane) := by
      calc Metric.externalCoveringNumber Δ.toNNReal (a4.P_norm : Set Plane)
        ≤ (a4.P_norm.card : ENNReal) := h_cover_P_norm
      _ ≤ ENNReal.ofReal (2 * Real.rpow Δ (-46 * ε)) * (P'_Q.card : ENNReal) := h4_exact
      _ ≤ ENNReal.ofReal (2 * Real.rpow Δ (-46 * ε)) *
            (25 * Metric.externalCoveringNumber Δ.toNNReal (P'_Q : Set Plane)) := by gcongr
      _ = (25 : ENNReal) * ENNReal.ofReal (2 * Real.rpow Δ (-46 * ε)) *
            Metric.externalCoveringNumber Δ.toNNReal (P'_Q : Set Plane) := by ring
      _ ≤ ENNReal.ofReal (Real.rpow Δ (-47 * ε)) *
            Metric.externalCoveringNumber Δ.toNNReal (P'_Q : Set Plane) := by
              gcongr <;> exact h_const_new
    have h_cover_cond : Metric.externalCoveringNumber Δ.toNNReal (a4.P_norm : Set Plane) ≤
        ENNReal.ofReal (Real.rpow Δ (-48 * ε)) *
        Metric.externalCoveringNumber Δ.toNNReal (P'_Q : Set Plane) := by
      have h_weaken : ENNReal.ofReal (Real.rpow Δ (-47 * ε)) ≤ ENNReal.ofReal (Real.rpow Δ (-48 * ε)) := by
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos (by linarith [hΔ_lt_half]) (by linarith [hε_pos])
      calc Metric.externalCoveringNumber Δ.toNNReal (a4.P_norm : Set Plane)
        ≤ ENNReal.ofReal (Real.rpow Δ (-47 * ε)) *
            Metric.externalCoveringNumber Δ.toNNReal (P'_Q : Set Plane) := h_cover_cond47
      _ ≤ ENNReal.ofReal (Real.rpow Δ (-48 * ε)) *
            Metric.externalCoveringNumber Δ.toNNReal (P'_Q : Set Plane) := by gcongr
    let proj' : BasicProjectionData Δ s ε P'_Q T0 :=
      proj_Q.h_robust P'_Q hP'_Q_sub h_cover_cond
    have hP'_Q_card_lower : Real.rpow Δ (-t + 44 * ε) ≤ (P'_Q.card : ℝ) :=
      le_trans h_card_out hP'_Q_card
    have hP'_Q_card_upper : (P'_Q.card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε) := by
      have h1 : P'_Q ⊆ a4.P_norm := hP'_Q_sub
      have h2 : (P'_Q.card : ℝ) ≤ (a4.P_norm.card : ℝ) := by
        exact_mod_cast Finset.card_le_card h1
      exact le_trans h2 h_card
    have hδ_pos : 0 < δ := by
      rw [hδ_eq]
      positivity
    have hfine_card_lower' : ∀ p ∈ P'_Q, Real.rpow Δ (-s + 40 * ε) ≤ (fineTubes p).card := by
      intro p hp
      have hpin : p ∈ a4.P_norm := hP'_Q_sub hp
      have hft : (fineTubes p).card = f p := by
        simp [fineTubes, f, hpin] <;> rfl
      rw [hft]
      have h : (f p : ℝ) ≥ H / (2 * P_max) := h_high p hp
      exact le_trans h_fine_lower_out h
    have hfine_sub_TQ' : ∀ p ∈ P'_Q, (fineTubes p : Set FineTube) ⊆ (base.T_Q (orig p) : Set FineTube) := by
      intro p hp
      have hpin : p ∈ a4.P_norm := hP'_Q_sub hp
      have h : fineTubes p = pointFiber Δ base.hΔ_pos base.T_Q (orig p) T0 := by
        simp [fineTubes, hpin]
      rw [h]
      exact Finset.filter_subset _ _
    exact
      { a4 := a4
      , P'_Q := P'_Q
      , hP'_Q_sub := hP'_Q_sub
      , hP'_Q_card_lower := hP'_Q_card_lower
      , hP'_Q_card_upper := hP'_Q_card_upper
      , originalOfNorm := orig
      , h_originalOfNorm := fun p hp => h_orig_in_PQ p (hP'_Q_sub hp)
      , h_norm_formula := fun p hp => by simp [orig]
      , fineTubes := fineTubes
      , hfine_eq_pointFiber := fun p hp => by
          have hpin : p ∈ a4.P_norm := hP'_Q_sub hp
          simp [fineTubes, hpin, base] <;> rfl
      , hfine_inc := fun p hp T hT => by
          have hpin : p ∈ a4.P_norm := hP'_Q_sub hp
          have hT' : T ∈ base.T_Q (orig p) := hfine_sub_TQ' p hp hT
          have hq : orig p ∈ base.P_Q := h_orig_in_PQ p hpin
          exact base.h_inc (orig p) hq T hT'
      , hfine_card_lower := fun p hp => by
          have hpin : p ∈ a4.P_norm := hP'_Q_sub hp
          have hft : (fineTubes p).card = f p := by
            simp [fineTubes, f, hpin] <;> rfl
          rw [hft]
          have h : (f p : ℝ) ≥ H / (2 * P_max) := h_high p hp
          exact le_trans h_fine_lower_out h
      , hfine_card_upper := fun p hp => by
          have hpin : p ∈ a4.P_norm := hP'_Q_sub hp
          have hft : (fineTubes p).card = f p := by
            simp [fineTubes, f, hpin] <;> rfl
          rw [hft]
          exact h_upper p hpin
      , hfine_tubes_separated := fun p hp => by
          have hpin : p ∈ a4.P_norm := hP'_Q_sub hp
          have hq : orig p ∈ base.P_Q := h_orig_in_PQ p hpin
          exact (base.hT_Q_separated (orig p) hq).mono (hfine_sub_TQ' p hp)
      , hfine_tubes_sset := fun p hp => by
          have hpin : p ∈ a4.P_norm := hP'_Q_sub hp
          have hq : orig p ∈ base.P_Q := h_orig_in_PQ p hpin
          have h_sub : (fineTubes p : Set FineTube) ⊆ (base.T_Q (orig p) : Set FineTube) := hfine_sub_TQ' p hp
          have h_sep : SeparatedAt (δ / 2) (fineTubes p : Set FineTube) :=
            (base.hT_Q_separated (orig p) hq).mono h_sub
          have h_card_lower : Real.rpow Δ (-s + 40 * ε) ≤ (fineTubes p).card :=
            hfine_card_lower' p hp
          have h_card_upper : (base.T_Q (orig p)).card ≤ base.M :=
            base.hT_Q_card_upper (orig p) hq
          have hM_pos : 0 < base.M := by
            have h1 : 0 < Real.rpow Δ (-2 * s + 2 * ε) := Real.rpow_pos_of_pos hΔ_pos _
            have h2 : 0 < base.K_pack := base.hKpack_pos
            have h3 : 0 < Real.rpow Δ (-2 * s + 2 * ε) / base.K_pack := by positivity
            have h4 : Real.rpow Δ (-2 * s + 2 * ε) / base.K_pack ≤ base.M := base.hM_lower
            linarith
          let C_TQ := max 1 (base.K_pack * Real.rpow δ (-ε)) * base.K_Q *
            (MainAppendix.affineLine_packing_constant : ℝ)
          have hC_TQ_pos : 0 < C_TQ := by
            have h1 : 0 < max 1 (base.K_pack * Real.rpow δ (-ε)) := by positivity
            have h2 : 0 < base.K_Q := base.hK_Q_pos
            have h3 : 0 < (MainAppendix.affineLine_packing_constant : ℝ) :=
              Nat.cast_pos.mpr MainAppendix.affineLine_packing_constant_pos
            positivity
          have h_pack_pos : 0 < (MainAppendix.affineLine_packing_constant : ℝ) :=
            Nat.cast_pos.mpr MainAppendix.affineLine_packing_constant_pos
          exact a8_fine_tubes_sset_transfer hδ_pos hΔ_pos hC_TQ_pos hM_pos h_pack_pos
            (base.hT_Q_sset (orig p) hq)
            h_sub h_sep h_card_upper h_card_lower
      , h_dirV_nonzero := fun p hp T hT => by
          have hpin : p ∈ a4.P_norm := hP'_Q_sub hp
          have hT' : T ∈ base.T_Q (orig p) := hfine_sub_TQ' p hp hT
          have hq : orig p ∈ base.P_Q := h_orig_in_PQ p hpin
          exact (base.h_slope_bound (orig p) hq T hT').1
      , h_tube_param_bounds := fun p hp T hT => by
          have hpin : p ∈ a4.P_norm := hP'_Q_sub hp
          have hT' : T ∈ base.T_Q (orig p) := hfine_sub_TQ' p hp hT
          have hq : orig p ∈ base.P_Q := h_orig_in_PQ p hpin
          exact (base.h_slope_bound (orig p) hq T hT').2
      , hfine_sub_TQ := fun p hp => hfine_sub_TQ' p hp
      , proj := proj'
      }

  exact
    { a7 := a7
    , T0_norm := T0
    , hT0_norm_eq := rfl
    , Q0 := Q0
    , hQ0_eq := rfl
    , perSquare := perSquare
    , h_perSquare_a4 := fun Q hQ => by
        dsimp only [perSquare]
        <;> rfl
    }

end DirecretisedFurstenbergEstimate.AppendixA
