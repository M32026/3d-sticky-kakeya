module

/-
  Provenance transfer via radius addition and Lipschitz map.

  Chain:
    |A| / C_pack ≤ Ncover(64·δ_n, A)
                   ≤ Ncover((31/2)·δ', A)
                   ≤ Ncover(2·δ, B)
                   ≤ Ncover(δ, originalFamily)

  Whiteprint node: provenance_radius_addition
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.ProvenanceRadiusAddition

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence
open DyadicCardToNcover (toAffineLine)

abbrev Ncover {X : Type*} [PseudoMetricSpace X] (δ : ℝ) (E : Set X) : ENNReal :=
  Metric.externalCoveringNumber δ.toNNReal E

/-! ========================================================================
   Lemma 1: Thickening transfer (radius addition)
   ======================================================================== -/

/-- If every point of `A` is within distance `d` of some point of `B`, then
    `Ncover(r+d, A) ≤ Ncover(r, B)`. -/
lemma ncover_thickening_transfer
    {X : Type*} [PseudoMetricSpace X]
    {A B : Set X} {r d : ℝ} (hr_nonneg : 0 ≤ r) (hd_nonneg : 0 ≤ d)
    (h : ∀ (x : X), x ∈ A → ∃ (y : X), y ∈ B ∧ dist x y ≤ d) :
    Metric.externalCoveringNumber (r + d).toNNReal A ≤
    Metric.externalCoveringNumber r.toNNReal B := by
  have hrd_nonneg : 0 ≤ r + d := by linarith
  have h_main : ∀ (C : Set X), Metric.IsCover r.toNNReal B C →
      Metric.IsCover (r + d).toNNReal A C := by
    intro C hC
    intro x hx
    rcases h x hx with ⟨y, hy, hxy⟩
    rcases hC hy with ⟨c, hc, hyc⟩
    have h_yc : nndist y c ≤ r.toNNReal := by
      exact_mod_cast hyc
    have h_yc' : dist y c ≤ r := by
      have h9 : (nndist y c : ℝ) ≤ (r.toNNReal : ℝ) := by exact_mod_cast h_yc
      have h10 : (nndist y c : ℝ) = dist y c := by exact coe_nndist y c
      have h11 : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr_nonneg
      rw [h10, h11] at h9; exact h9
    have h_dist : dist x c ≤ r + d := by
      calc dist x c ≤ dist x y + dist y c := dist_triangle x y c
      _ ≤ d + r := by linarith
      _ = r + d := by ring
    have h6 : nndist x c ≤ (r + d).toNNReal := by
      have h7 : (nndist x c : ℝ) = dist x c := by exact coe_nndist x c
      have h8 : ((r + d).toNNReal : ℝ) = r + d := Real.coe_toNNReal (r + d) hrd_nonneg
      have h9 : (nndist x c : ℝ) ≤ ((r + d).toNNReal : ℝ) := by
        rw [h7, h8] <;> exact h_dist
      exact NNReal.coe_le_coe.mp h9
    exact ⟨c, hc, by exact_mod_cast h6⟩
  exact le_iInf₂_iff.mpr fun C hC => iInf₂_le C (h_main C hC)

/-! ========================================================================
   Lemma 2: Lipschitz forward transfer
   ======================================================================== -/

/-- If `f : X → Y` is `L`-Lipschitz, then
    `Ncover(L*r, f '' A) ≤ Ncover(r, A)`. -/
lemma ncover_lipschitz_image
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {A : Set X} {r L : ℝ}
    (hr_nonneg : 0 ≤ r) (hL_nonneg : 0 ≤ L)
    (hLipschitz : ∀ (x y : X), dist (f x) (f y) ≤ L * dist x y) :
    Metric.externalCoveringNumber (L * r).toNNReal (f '' A) ≤
    Metric.externalCoveringNumber r.toNNReal A := by
  have hLr_nonneg : 0 ≤ L * r := by positivity
  let L_nn : NNReal := ⟨L, hL_nonneg⟩
  have hLipschitz' : LipschitzWith L_nn f := by exact lipschitzWith_iff_dist_le_mul.mpr hLipschitz
  have h_prod : L_nn * r.toNNReal = (L * r).toNNReal := by
    apply NNReal.coe_injective
    have h_r_coe : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr_nonneg
    have h_L_coe : (L_nn : ℝ) = L := by exact Real.ext_cauchy rfl
    have h_left : ((L_nn * r.toNNReal : NNReal) : ℝ) = L * r := by
      have h_mul : ((L_nn * r.toNNReal : NNReal) : ℝ) = (L_nn : ℝ) * (r.toNNReal : ℝ) := by
        exact NNReal.coe_mul L_nn r.toNNReal
      rw [h_mul, h_L_coe, h_r_coe] <;> ring
    have h_right : (((L * r).toNNReal : NNReal) : ℝ) = L * r :=
      Real.coe_toNNReal (L * r) hLr_nonneg
    exact Eq.trans h_left h_right.symm
  have h_main : ∀ (C : Set X), Metric.IsCover r.toNNReal A C →
      Metric.IsCover (L * r).toNNReal (f '' A) (f '' C) := by
    intro C hC
    have h_img : Metric.IsCover (L_nn * r.toNNReal) (f '' A) (f '' C) :=
      hC.image_lipschitz hLipschitz'
    rw [h_prod] at h_img
    exact h_img
  exact le_iInf₂_iff.mpr fun C hC =>
    le_trans (iInf₂_le (f '' C) (h_main C hC)) (Set.encard_image_le f C)

/-! ========================================================================
   Lemma 3: Packing lower bound
   ======================================================================== -/

/-- If every `r`-ball contains at most `K` points of finite `A`,
    then `|A| ≤ K * Ncover(r, A)`. -/
lemma packing_to_ncover_lower
    {X : Type*} [PseudoMetricSpace X]
    {A : Set X} {r : ℝ} {K : ℕ}
    (hA_fin : A.Finite) (hr_nonneg : 0 ≤ r)
    (h_mult : ∀ (x : X), (A ∩ Metric.closedBall x r).ncard ≤ K) :
    (A.ncard : ENNReal) ≤ (K : ENNReal) * Metric.externalCoveringNumber r.toNNReal A := by
  classical
  let A_finset : Finset X := hA_fin.toFinset
  have hA_coe : (A_finset : Set X) = A := Set.Finite.coe_toFinset hA_fin
  by_cases hK0 : K = 0
  · have hA_empty : A = ∅ := by
      by_contra hne
      have h_nonempty : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
      rcases h_nonempty with ⟨a, ha⟩
      have hball : a ∈ Metric.closedBall a r := by
        simp [Metric.mem_closedBall, hr_nonneg]
      have h4 : (A ∩ Metric.closedBall a r).Nonempty := ⟨a, ⟨ha, hball⟩⟩
      have h_sub : A ∩ Metric.closedBall a r ⊆ A := by intro x hx; exact hx.1
      have h_fin : (A ∩ Metric.closedBall a r).Finite := hA_fin.subset h_sub
      have h5 : 0 < (A ∩ Metric.closedBall a r).ncard :=
        Set.Nonempty.ncard_pos h_fin h4
      have h6 := h_mult a
      rw [hK0] at h6
      linarith
    rw [hA_empty]
    simp
  · have hK_ne_zero' : (K : ENNReal) ≠ 0 := by exact_mod_cast hK0
    by_cases h_top : Metric.externalCoveringNumber r.toNNReal A = ⊤
    · have h_goal : (A.ncard : ENNReal) ≤ (K : ENNReal) * Metric.externalCoveringNumber r.toNNReal A := by
        rw [h_top]
        have h_mul : (K : ENNReal) * (⊤ : ENNReal) = ⊤ := ENNReal.mul_top hK_ne_zero'
        have h_final : (A.ncard : ENNReal) ≤ (K : ENNReal) * (⊤ : ENNReal) := by
          rw [h_mul]
          exact le_top
        exact h_final
      exact h_goal
    · have h_ne_top : Metric.externalCoveringNumber r.toNNReal A ≠ ⊤ := h_top
      have h_lt_top : Metric.externalCoveringNumber r.toNNReal A < ⊤ := by exact Ne.lt_top' (id (Ne.symm h_ne_top))
      let ι := {C : Set X // Metric.IsCover r.toNNReal A C}
      have hι_nonempty : Nonempty ι := by
        refine' ⟨⟨A, _⟩⟩
        intro x hx
        exact ⟨x, hx, by simp [Metric.IsCover, edist_dist]⟩
      let f : ι → ℕ∞ := fun C => (C.val).encard
      have h_exists : ∃ (C : ι), f C = ⨅ (x : ι), f x := ENat.exists_eq_iInf f
      rcases h_exists with ⟨C_min, hC_min_eq⟩
      have h_ext_def : Metric.externalCoveringNumber r.toNNReal A = ⨅ (C : ι), f C := by
        have h : Metric.externalCoveringNumber r.toNNReal A =
            ⨅ (C : Set X) (_ : Metric.IsCover r.toNNReal A C), C.encard := by rfl
        rw [h, iInf_subtype] <;> rfl
      have h_encard_eq : (C_min.val).encard = Metric.externalCoveringNumber r.toNNReal A := by
        have h10 : f C_min = Metric.externalCoveringNumber r.toNNReal A := by
          rw [hC_min_eq, h_ext_def]
        simpa [f] using h10
      have hC_fin : (C_min.val).Finite := by
        have h_lt : (C_min.val).encard < ⊤ := by
          rw [h_encard_eq] <;> exact h_lt_top
        exact Set.encard_lt_top_iff.mp h_lt
      let C_finset : Finset X := hC_fin.toFinset
      have hC_coe : (C_finset : Set X) = C_min.val := Set.Finite.coe_toFinset hC_fin
      let A_c : X → Finset X := fun c =>
        (hA_fin.subset (show A ∩ Metric.closedBall c r ⊆ A from Set.inter_subset_left)).toFinset
      have hA_c_card : ∀ c ∈ C_finset, (A_c c).card ≤ K := by
        intro c _
        have h5 : (A_c c : Set X) = A ∩ Metric.closedBall c r := by
          ext x; simp [A_c] <;> tauto
        have h6 : (A_c c).card = (A ∩ Metric.closedBall c r).ncard := by
          have h7 : (A_c c : Set X) = A ∩ Metric.closedBall c r := h5
          have h8 : (A_c c).card = (A_c c : Set X).ncard := by exact Eq.symm (Set.ncard_coe_finset (A_c c))
          rw [h8, h7]
        rw [h6]; exact h_mult c
      have h_union : A ⊆ ⋃ c ∈ C_finset, (A_c c : Set X) := by
        intro a ha
        have h2 := C_min.property ha
        rcases h2 with ⟨c, hc, hball⟩
        have hc' : c ∈ C_finset := by
          have h1 : c ∈ (C_finset : Set X) := by rw [hC_coe] <;> exact hc
          simpa using h1
        have h4 : dist a c ≤ r := by
          have h5 : nndist a c ≤ r.toNNReal := by exact_mod_cast hball
          have h6 : (nndist a c : ℝ) ≤ (r.toNNReal : ℝ) := by exact_mod_cast h5
          have h7 : (nndist a c : ℝ) = dist a c := by exact coe_nndist a c
          have h8 : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr_nonneg
          rw [h7, h8] at h6; exact h6
        have h3 : a ∈ A ∩ Metric.closedBall c r := ⟨ha, h4⟩
        have h5 : a ∈ (A_c c : Set X) := by
          have h6 : (A_c c : Set X) = A ∩ Metric.closedBall c r := by
            ext x; simp [A_c] <;> tauto
          rw [h6] <;> exact h3
        exact Set.mem_iUnion₂.mpr ⟨c, hc', h5⟩
      have hA_card : A_finset.card ≤ K * C_finset.card := by
        have h_sub2 : A_finset ⊆ Finset.biUnion C_finset (A_c) := by
          intro x hx
          have h6 : x ∈ A := by
            have h7 : x ∈ (A_finset : Set X) := hx
            rw [hA_coe] at h7 <;> exact h7
          have h8 := h_union h6
          simpa using h8
        calc A_finset.card
          ≤ (Finset.biUnion C_finset (A_c)).card := Finset.card_le_card h_sub2
        _ ≤ ∑ c ∈ C_finset, (A_c c).card := Finset.card_biUnion_le
        _ ≤ ∑ c ∈ C_finset, K := by gcongr <;> exact hA_c_card c ‹_›
        _ = K * C_finset.card := by simp [Finset.sum_const] <;> ring
      have h_final : (A_finset.card : ENNReal) ≤ (K : ENNReal) * (C_finset.card : ENNReal) := by
        exact_mod_cast hA_card
      have h_C_card : (C_finset.card : ENNReal) = Metric.externalCoveringNumber r.toNNReal A := by
        have h5 : (C_finset.card : ℕ∞) = (C_min.val).encard := by
          have h6 : C_finset.card = (C_min.val).ncard := by
            exact Eq.symm (Set.ncard_eq_toFinset_card (C_min.val) hC_fin)
          have h7 : ((C_min.val).ncard : ℕ∞) = (C_min.val).encard := by
            letI : Fintype (C_min.val) := Set.Finite.fintype hC_fin
            exact Set.coe_ncard_eq_encard (s := C_min.val)
          rw [h6, h7]
        have h9 : (C_finset.card : ENNReal) = ↑(C_finset.card : ℕ∞) := by simp
        rw [h9, h5, h_encard_eq]
      have hA_ncard_eq : A.ncard = A_finset.card := Set.ncard_eq_toFinset_card A hA_fin
      have h10 : (A.ncard : ENNReal) = (A_finset.card : ENNReal) := by
        exact_mod_cast hA_ncard_eq
      calc (A.ncard : ENNReal)
        = (A_finset.card : ENNReal) := h10
      _ ≤ (K : ENNReal) * (C_finset.card : ENNReal) := h_final
      _ = (K : ENNReal) * Metric.externalCoveringNumber r.toNNReal A := by rw [h_C_card]

/-! ========================================================================
   Main: Provenance radius addition transfer
   ======================================================================== -/

/-- Full provenance transfer via radius addition and Lipschitz map. -/
lemma provenance_radius_addition_transfer
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {A : Set X} {originalFamily : Set Y} {f : Y → X}
    {δ_n δ' δ : ℝ} {C_pack : ℕ}
    (hA_fin : A.Finite)
    (hδn_pos : 0 < δ_n)
    (hδ'_pos : 0 < δ')
    (hδ_pos : 0 < δ)
    (h_scale2 : δ' < 4 * δ_n)
    (hδ'_eq : δ' = δ / 4)
    (h_thick : ∀ (x : X), x ∈ A → ∃ (y : X), y ∈ f '' originalFamily ∧ dist x y ≤ (15 / 2 : ℝ) * δ')
    (hLipschitz : ∀ (x y : Y), dist (f x) (f y) ≤ 2 * dist x y)
    (h_packing : ∀ (x : X), (A ∩ Metric.closedBall x (64 * δ_n)).ncard ≤ C_pack) :
    (A.ncard : ENNReal) ≤ (C_pack : ENNReal) * Ncover δ originalFamily := by
  let B : Set X := f '' originalFamily
  have h1 : (31 / 2 : ℝ) * δ' < 64 * δ_n := by
    calc (31 / 2 : ℝ) * δ'
      < (31 / 2 : ℝ) * (4 * δ_n) := by gcongr
    _ = 62 * δ_n := by ring
    _ < 64 * δ_n := by linarith
  have h1' : ((31 / 2 : ℝ) * δ').toNNReal ≤ (64 * δ_n).toNNReal := by
    apply NNReal.coe_le_coe.mp
    have h_pos : 0 ≤ (31 / 2 : ℝ) * δ' := by positivity
    have h_pos2 : 0 ≤ 64 * δ_n := by positivity
    simp [Real.coe_toNNReal _ h_pos, Real.coe_toNNReal _ h_pos2] <;> linarith
  have h2 : Metric.externalCoveringNumber (64 * δ_n).toNNReal A ≤
      Metric.externalCoveringNumber ((31 / 2 : ℝ) * δ').toNNReal A :=
    Metric.externalCoveringNumber_anti h1'
  have h3 : 2 * δ + (15 / 2 : ℝ) * δ' = (31 / 2 : ℝ) * δ' := by
    rw [hδ'_eq] <;> ring
  have h4 : Metric.externalCoveringNumber ((31 / 2 : ℝ) * δ').toNNReal A ≤
      Metric.externalCoveringNumber (2 * δ).toNNReal B := by
    rw [show ((31 / 2 : ℝ) * δ') = (2 * δ) + ((15 / 2 : ℝ) * δ') from h3.symm]
    exact ncover_thickening_transfer
      (hr_nonneg := by positivity) (hd_nonneg := by positivity) h_thick
  have h5 : Metric.externalCoveringNumber (2 * δ).toNNReal B ≤
      Metric.externalCoveringNumber δ.toNNReal originalFamily :=
    ncover_lipschitz_image
      (hr_nonneg := by positivity) (hL_nonneg := by norm_num) hLipschitz
  have h6 : (A.ncard : ENNReal) ≤ (C_pack : ENNReal) * Metric.externalCoveringNumber (64 * δ_n).toNNReal A :=
    packing_to_ncover_lower hA_fin (by positivity) h_packing
  calc (A.ncard : ENNReal)
    ≤ (C_pack : ENNReal) * Metric.externalCoveringNumber (64 * δ_n).toNNReal A := h6
  _ ≤ (C_pack : ENNReal) * Metric.externalCoveringNumber ((31 / 2 : ℝ) * δ').toNNReal A := by gcongr
  _ ≤ (C_pack : ENNReal) * Metric.externalCoveringNumber (2 * δ).toNNReal B := by gcongr
  _ ≤ (C_pack : ENNReal) * Metric.externalCoveringNumber δ.toNNReal originalFamily := by gcongr

end DirecretisedFurstenbergEstimate.ProvenanceRadiusAddition

end
