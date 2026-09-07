import MyLeanRepo.Kakeya.Assouad.Statements
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Frostman to Katz--Tao extraction

WZ2 Section 7: given a δ-separated Frostman set A, extract a large Katz--Tao
subset A' with logarithmic loss.
-/

noncomputable section

open Classical Kakeya.Assouad DiscreteSet Metric Set Finset

namespace Kakeya.Assouad

/-! ## Helper definitions and lemmas -/

def ballCountNat {n : ℕ} (A : DiscreteSet n) (x : Point n) (r : ℝ) : ℕ :=
  (A.filter fun y => dist y x ≤ r).card

lemma ballCountNat_eq {n : ℕ} (A : DiscreteSet n) (x : Point n) (r : ℝ) :
    (ballCountNat A x r : ENNReal) = A.ballCount x r := by
  simp [ballCountNat, DiscreteSet.ballCount]

lemma witness_ball {n : ℕ} {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    {A A' : DiscreteSet n} (hA'_KT : A'.IsKatzTao δ s 100)
    (hmax : ∀ (x : Point n), x ∈ A → x ∉ A' →
      ¬ (insert x A').IsKatzTao δ s 100)
    {x : Point n} (hxA : x ∈ A) (hnxA : x ∉ A') :
    ∃ (y : Point n) (r : ℝ), δ ≤ r ∧ r ≤ 1 ∧
      dist x y ≤ r ∧
      (ballCountNat A' y r : ℝ) ≥ 99 * Real.rpow (r / δ) s := by
  have h1 : ¬ (insert x A').IsKatzTao δ s 100 := hmax x hxA hnxA
  simp only [DiscreteSet.IsKatzTao] at h1
  push Not at h1
  rcases h1 with ⟨y, r, hδr, hr1, hgt⟩
  have h2 : (insert x A').ballCount y r >
      100 * Kakeya.realRpowENN (r / δ) s := hgt
  have h_x_in : dist x y ≤ r := by
    by_contra h
    have h3 : (insert x A').ballCount y r = A'.ballCount y r := by
      simp [DiscreteSet.ballCount, Finset.filter_insert, h]
    rw [h3] at h2
    have h4 : A'.ballCount y r ≤
        100 * Kakeya.realRpowENN (r / δ) s := hA'_KT y r hδr hr1
    exact lt_irrefl _ (h4.trans_lt h2)
  let F := A'.filter (fun z => dist z y ≤ r)
  have h_x_notin_filter : x ∉ F := by
    intro h
    exact hnxA (Finset.mem_filter.mp h).1
  have h_filter_eq :
      (insert x A').filter (fun z => dist z y ≤ r) = insert x F := by
    rw [Finset.filter_insert, if_pos h_x_in]
  have h3 :
      ballCountNat (insert x A') y r = ballCountNat A' y r + 1 := by
    dsimp only [ballCountNat]
    rw [h_filter_eq, Finset.card_insert_of_notMem h_x_notin_filter]
  have h_rpos : 0 < r / δ := by
    apply div_pos <;> linarith
  have h_rpow_pos : 0 < Real.rpow (r / δ) s :=
    Real.rpow_pos_of_pos h_rpos s
  have h7 : (ballCountNat (insert x A') y r : ENNReal) >
      100 * ENNReal.ofReal (Real.rpow (r / δ) s) := by
    have h4 :
        (ballCountNat (insert x A') y r : ENNReal) =
          (insert x A').ballCount y r := ballCountNat_eq _ _ _
    rw [h4]
    exact h2
  have h9 : ENNReal.ofReal (ballCountNat (insert x A') y r : ℝ) >
      ENNReal.ofReal (100 * Real.rpow (r / δ) s) := by
    simpa [ENNReal.ofReal_natCast] using h7
  have h10 :
      (100 * Real.rpow (r / δ) s) <
        (ballCountNat (insert x A') y r : ℝ) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp h9
  have h11 :
      (ballCountNat A' y r : ℝ) + 1 >
        100 * Real.rpow (r / δ) s := by
    have h12 :
        (ballCountNat (insert x A') y r : ℝ) =
          (ballCountNat A' y r : ℝ) + 1 := by
      exact_mod_cast h3
    rw [h12] at h10
    exact h10
  have h14 : 1 ≤ r / δ := by
    have h : δ ≤ r := hδr
    have h' : 0 < δ := hδ
    have : δ / δ ≤ r / δ := by gcongr
    have : δ / δ = 1 := by field_simp [h'.ne']
    linarith
  have h13 : 1 ≤ Real.rpow (r / δ) s :=
    Real.one_le_rpow h14 (by linarith)
  have h15 :
      (ballCountNat A' y r : ℝ) ≥ 99 * Real.rpow (r / δ) s := by
    linarith
  exact ⟨y, r, hδr, hr1, h_x_in, h15⟩

lemma frostman_extended {n : ℕ} {A : DiscreteSet n}
    {δ s : ℝ} {C : ENNReal}
    (hA_frost : A.IsFrostman δ s C) (_hA_unit : A.IsInUnitBall)
    (hC_one : 1 ≤ C) (_hC_top : C ≠ ⊤)
    (_hδ_pos : 0 < δ) (hs : 0 < s) :
    ∀ (x : Point n) (r : ℝ), δ ≤ r →
      A.ballCount x r ≤ C * Kakeya.realRpowENN r s * A.enncard := by
  intro x r hδr
  by_cases h : r ≤ 1
  · exact hA_frost x r hδr h
  · have hr1 : 1 < r := by linarith
    have h1 : A.ballCount x r ≤ A.enncard := by
      have h_filter :
          (A.filter fun y => dist y x ≤ r) ⊆ A := Finset.filter_subset _ _
      have h_card :
          (A.filter fun y => dist y x ≤ r).card ≤ A.card :=
        Finset.card_le_card h_filter
      have h_enn :
          ((A.filter fun y => dist y x ≤ r).card : ENNReal) ≤
            (A.card : ENNReal) := by
        exact_mod_cast h_card
      simpa [DiscreteSet.ballCount, DiscreteSet.enncard] using h_enn
    have h2 : A.enncard ≤ C * A.enncard := by
      have h21 :
          (1 : ENNReal) * A.enncard ≤ C * A.enncard := by
        gcongr
      simpa using h21
    have h3 : (1 : ENNReal) ≤ Kakeya.realRpowENN r s := by
      have h31 : 1 ≤ r := by linarith
      have h32 : 1 ≤ Real.rpow r s :=
        Real.one_le_rpow h31 (by linarith)
      simpa [Kakeya.realRpowENN, ENNReal.one_le_ofReal] using h32
    have h4 :
        C * A.enncard ≤
          C * Kakeya.realRpowENN r s * A.enncard := by
      calc
        C * A.enncard =
            C * (1 : ENNReal) * A.enncard := by ring
        _ ≤ C * Kakeya.realRpowENN r s * A.enncard := by gcongr
    exact h1.trans (h2.trans h4)

/-! ## Core: Vitali covering + summation step -/

lemma vitali_covering_step {n : ℕ} {δ s : ℝ} {C : ENNReal}
    {A A' : DiscreteSet n}
    (hδ_pos : 0 < δ) (hs : 0 < s)
    (hC_one : 1 ≤ C) (hC_top : C ≠ ⊤)
    (hA_frost : A.IsFrostman δ s C)
    (hA_unit : A.IsInUnitBall)
    (h_sub : A' ⊆ A)
    (h_kt : A'.IsKatzTao δ s 100)
    (h_max : ∀ x ∈ A \ A', ¬ (insert x A').IsKatzTao δ s 100) :
    (A.card : ℝ) ≤
      (A'.card : ℝ) *
        (1 + (Real.rpow 5 s) *
          (C.toReal * (A.card : ℝ) * Real.rpow δ s) / 99) := by
  let S : DiscreteSet n := A \ A'
  have hmax' :
      ∀ (x : Point n), x ∈ A → x ∉ A' →
        ¬ (insert x A').IsKatzTao δ s 100 := by
    intro x hxA hnxA
    have h : x ∈ S := Finset.mem_sdiff.mpr ⟨hxA, hnxA⟩
    exact h_max x h
  let ι := {x : Point n // x ∈ S}
  have h_exists :
      ∀ (i : ι), ∃ (y : Point n) (r : ℝ),
        δ ≤ r ∧ r ≤ 1 ∧ dist i.val y ≤ r ∧
          (ballCountNat A' y r : ℝ) ≥ 99 * Real.rpow (r / δ) s := by
    intro i
    have hxA : i.val ∈ A := (Finset.mem_sdiff.mp i.property).1
    have hnxA : i.val ∉ A' := (Finset.mem_sdiff.mp i.property).2
    exact witness_ball hs hδ_pos h_kt hmax' hxA hnxA
  classical
  let y : ι → Point n := fun i => Classical.choose (h_exists i)
  let r : ι → ℝ :=
    fun i => Classical.choose (Classical.choose_spec (h_exists i))
  have h_witness :
      ∀ (i : ι), δ ≤ r i ∧ r i ≤ 1 ∧
        dist i.val (y i) ≤ r i ∧
        (ballCountNat A' (y i) (r i) : ℝ) ≥
          99 * Real.rpow (r i / δ) s := by
    intro i
    exact Classical.choose_spec (Classical.choose_spec (h_exists i))
  have h_vitali :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
      (Set.univ : Set ι) y r 1 (fun i _ => (h_witness i).2.1)
      5 (by norm_num)
  rcases h_vitali with ⟨u, _hu_sub, h_disj, h_cover⟩
  have h_u_finite : u.Finite := Set.toFinite u
  let U : Finset ι := h_u_finite.toFinset
  have hU_coe : (↑U : Set ι) = u := by
    simp [U]
  have h_disj' :
      (↑U : Set ι).PairwiseDisjoint
        (fun i => closedBall (y i) (r i)) := by
    rw [hU_coe]
    exact h_disj
  have h_cover' :
      ∀ (i : ι), ∃ b ∈ U,
        closedBall (y i) (r i) ⊆ closedBall (y b) (5 * r b) := by
    intro i
    rcases h_cover i (Set.mem_univ i) with ⟨b, hb, hsub⟩
    have hb' : b ∈ U := by simpa [U] using hb
    exact ⟨b, hb', hsub⟩
  let F : ι → Finset (Point n) :=
    fun i => A'.filter (fun z => dist z (y i) ≤ r i)
  have hF_disj : (↑U : Set ι).PairwiseDisjoint F := by
    intro i hi j hj hne
    have h_ball :
        Disjoint (closedBall (y i) (r i)) (closedBall (y j) (r j)) :=
      h_disj' hi hj hne
    have h : Disjoint (F i) (F j) := by
      rw [Finset.disjoint_left]
      intro z hzi hzj
      have h1 : z ∈ closedBall (y i) (r i) :=
        (Finset.mem_filter.mp hzi).2
      have h2 : z ∈ closedBall (y j) (r j) :=
        (Finset.mem_filter.mp hzj).2
      exact h_ball.le_bot ⟨h1, h2⟩
    simpa [Set.PairwiseDisjoint] using h
  have hF_card :
      ∀ i, (F i).card = ballCountNat A' (y i) (r i) := by
    intro i
    rfl
  have h_unionF_sub : U.biUnion F ⊆ A' := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨i, _, hzF⟩
    exact (Finset.mem_filter.mp hzF).1
  have h_sum_disj1 :
      (U.biUnion F).card = ∑ i ∈ U, (F i).card :=
    Finset.card_biUnion hF_disj
  have h_sum_disj2 :
      ∑ i ∈ U, (ballCountNat A' (y i) (r i) : ℝ) ≤
        (A'.card : ℝ) := by
    have h : ∑ i ∈ U, (F i).card ≤ A'.card := by
      rw [← h_sum_disj1]
      exact Finset.card_le_card h_unionF_sub
    have h' :
        (∑ i ∈ U, (F i).card : ℝ) =
          ∑ i ∈ U, (ballCountNat A' (y i) (r i) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact_mod_cast hF_card i
    have h'' :
        (∑ i ∈ U, (F i).card : ℝ) ≤ (A'.card : ℝ) := by
      exact_mod_cast h
    rw [h'] at h''
    exact h''
  have h_lower :
      ∀ i ∈ U,
        99 * Real.rpow (r i / δ) s ≤
          (ballCountNat A' (y i) (r i) : ℝ) := by
    intro i _
    exact (h_witness i).2.2.2
  have h_sum_lower :
      ∑ i ∈ U, (99 * Real.rpow (r i / δ) s) ≤
        ∑ i ∈ U, (ballCountNat A' (y i) (r i) : ℝ) :=
    Finset.sum_le_sum h_lower
  have h_sum_rpow :
      ∑ i ∈ U, Real.rpow (r i / δ) s ≤ (A'.card : ℝ) / 99 := by
    have h :
        ∑ i ∈ U, (99 * Real.rpow (r i / δ) s) =
          99 * ∑ i ∈ U, Real.rpow (r i / δ) s := by
      rw [Finset.mul_sum]
    rw [h] at h_sum_lower
    linarith
  let G : ι → Finset (Point n) :=
    fun i => A.filter (fun z => dist z (y i) ≤ 5 * r i)
  have hG_card :
      ∀ i, (G i).card = ballCountNat A (y i) (5 * r i) := by
    intro i
    rfl
  have h_coverS : S ⊆ U.biUnion G := by
    intro x hx
    let i : ι := ⟨x, hx⟩
    rcases h_cover' i with ⟨b, hb, hsub⟩
    have h_x_in_small : x ∈ closedBall (y i) (r i) :=
      (h_witness i).2.2.1
    have h_x_in_big : x ∈ closedBall (y b) (5 * r b) :=
      hsub h_x_in_small
    have hxA : x ∈ A := (Finset.mem_sdiff.mp hx).1
    have h_x_in_G : x ∈ G b := by
      simp only [G, Finset.mem_filter]
      exact ⟨hxA, h_x_in_big⟩
    exact Finset.mem_biUnion.mpr ⟨b, hb, h_x_in_G⟩
  have hS_card1 : S.card ≤ (U.biUnion G).card :=
    Finset.card_le_card h_coverS
  have hS_card2 :
      (U.biUnion G).card ≤ ∑ i ∈ U, (G i).card := by
    exact card_biUnion_le
  have hS_card3 :
      (S.card : ℝ) ≤
        ∑ i ∈ U, (ballCountNat A (y i) (5 * r i) : ℝ) := by
    have h : (S.card : ℝ) ≤ ((U.biUnion G).card : ℝ) := by
      exact_mod_cast hS_card1
    have h2 :
        ((U.biUnion G).card : ℝ) ≤
          (∑ i ∈ U, (G i).card : ℝ) := by
      exact_mod_cast hS_card2
    have h3 :
        (∑ i ∈ U, (G i).card : ℝ) =
          ∑ i ∈ U, (ballCountNat A (y i) (5 * r i) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact_mod_cast hG_card i
    calc
      (S.card : ℝ) ≤ ((U.biUnion G).card : ℝ) := h
      _ ≤ (∑ i ∈ U, (G i).card : ℝ) := h2
      _ = ∑ i ∈ U, (ballCountNat A (y i) (5 * r i) : ℝ) := h3
  have h_frost_bound :
      ∀ i ∈ U,
        (ballCountNat A (y i) (5 * r i) : ℝ) ≤
          C.toReal * Real.rpow (5 * r i) s * (A.card : ℝ) := by
    intro i _
    have h5r : δ ≤ 5 * r i := by
      have h1 : δ ≤ r i := (h_witness i).1
      linarith
    have h_posr : 0 < r i := by linarith
    have h_rpos : 0 < 5 * r i := by positivity
    have h_enn :
        A.ballCount (y i) (5 * r i) ≤
          C * Kakeya.realRpowENN (5 * r i) s * A.enncard :=
      frostman_extended hA_frost hA_unit hC_one hC_top hδ_pos hs
        (y i) (5 * r i) h5r
    have h_fin_rhs :
        (C * Kakeya.realRpowENN (5 * r i) s * A.enncard) ≠ ⊤ := by
      have h1 : C ≠ ⊤ := hC_top
      have h2 : Kakeya.realRpowENN (5 * r i) s ≠ ⊤ := by
        simp [Kakeya.realRpowENN]
      have h3 : A.enncard ≠ ⊤ := by simp [DiscreteSet.enncard]
      have h4 :
          (C * Kakeya.realRpowENN (5 * r i) s) ≠ ⊤ :=
        ENNReal.mul_ne_top h1 h2
      exact ENNReal.mul_ne_top h4 h3
    have h_fin_lhs : A.ballCount (y i) (5 * r i) ≠ ⊤ := by
      simp [DiscreteSet.ballCount]
    have h_toReal_iff :
        (A.ballCount (y i) (5 * r i)).toReal ≤
            (C * Kakeya.realRpowENN (5 * r i) s *
              A.enncard).toReal ↔
          A.ballCount (y i) (5 * r i) ≤
            C * Kakeya.realRpowENN (5 * r i) s * A.enncard :=
      ENNReal.toReal_le_toReal h_fin_lhs h_fin_rhs
    have h_toReal :
        (A.ballCount (y i) (5 * r i)).toReal ≤
          (C * Kakeya.realRpowENN (5 * r i) s *
            A.enncard).toReal :=
      h_toReal_iff.mpr h_enn
    have h_eq1 :
        (A.ballCount (y i) (5 * r i)).toReal =
          (ballCountNat A (y i) (5 * r i) : ℝ) := by
      have h_eq :
          (ballCountNat A (y i) (5 * r i) : ENNReal) =
            A.ballCount (y i) (5 * r i) :=
        ballCountNat_eq A (y i) (5 * r i)
      have h :
          (A.ballCount (y i) (5 * r i)).toReal =
            (ballCountNat A (y i) (5 * r i) : ENNReal).toReal := by
        rw [← h_eq]
      simpa using h
    have h_eq2 :
        (C * Kakeya.realRpowENN (5 * r i) s * A.enncard).toReal =
          C.toReal * Real.rpow (5 * r i) s * (A.card : ℝ) := by
      have h2_ne_top : Kakeya.realRpowENN (5 * r i) s ≠ ⊤ := by
        simp [Kakeya.realRpowENN]
      have h3_ne_top : A.enncard ≠ ⊤ := by
        simp [DiscreteSet.enncard]
      have h4_ne_top :
          (C * Kakeya.realRpowENN (5 * r i) s) ≠ ⊤ :=
        ENNReal.mul_ne_top hC_top h2_ne_top
      have h1 :
          (C * Kakeya.realRpowENN (5 * r i) s *
              A.enncard).toReal =
            (C * Kakeya.realRpowENN (5 * r i) s).toReal *
              A.enncard.toReal := by
        rw [ENNReal.toReal_mul]
      rw [h1]
      have h2 :
          (C * Kakeya.realRpowENN (5 * r i) s).toReal =
            C.toReal * (Kakeya.realRpowENN (5 * r i) s).toReal := by
        rw [ENNReal.toReal_mul]
      rw [h2]
      have h_5r_pos : 0 ≤ 5 * r i := by
        have h1 : δ ≤ r i := (h_witness i).1
        linarith
      have h_rpow_nonneg :
          0 ≤ Real.rpow (5 * r i) s :=
        Real.rpow_nonneg h_5r_pos s
      have h3 :
          (Kakeya.realRpowENN (5 * r i) s).toReal =
            Real.rpow (5 * r i) s := by
        rw [Kakeya.realRpowENN, ENNReal.toReal_ofReal h_rpow_nonneg]
      have h4 : A.enncard.toReal = (A.card : ℝ) := by
        simp [DiscreteSet.enncard]
      rw [h3, h4] <;> ring
    rw [h_eq1, h_eq2] at h_toReal
    exact h_toReal
  have h_sum_frost :
      ∑ i ∈ U, (ballCountNat A (y i) (5 * r i) : ℝ) ≤
        ∑ i ∈ U,
          (C.toReal * Real.rpow (5 * r i) s * (A.card : ℝ)) :=
    Finset.sum_le_sum h_frost_bound
  have h_rpow_factor :
      ∀ i ∈ U,
        Real.rpow (5 * r i) s =
          Real.rpow 5 s * Real.rpow δ s *
            Real.rpow (r i / δ) s := by
    intro i _
    have h_ri_ge_delta : δ ≤ r i := (h_witness i).1
    have h_nonneg5 : 0 ≤ (5 : ℝ) := by norm_num
    have h_nonnegr : 0 ≤ r i := by linarith
    have h_nonnegδ : 0 ≤ δ := by linarith
    have h_nonneg_ratio : 0 ≤ r i / δ := by positivity
    have h1 :
        Real.rpow (5 * r i) s =
          Real.rpow 5 s * Real.rpow (r i) s :=
      Real.mul_rpow h_nonneg5 h_nonnegr
    have h2 :
        Real.rpow (r i) s =
          Real.rpow δ s * Real.rpow (r i / δ) s := by
      calc
        Real.rpow (r i) s =
            Real.rpow (δ * (r i / δ)) s := by
          apply congr_arg (fun value : ℝ => Real.rpow value s)
          field_simp [hδ_pos.ne'] <;> ring
        _ = Real.rpow δ s * Real.rpow (r i / δ) s :=
          Real.mul_rpow h_nonnegδ h_nonneg_ratio
    rw [h1, h2] <;> ring
  have h_sum_factor :
      ∑ i ∈ U,
          (C.toReal * Real.rpow (5 * r i) s * (A.card : ℝ)) =
        C.toReal * (A.card : ℝ) * Real.rpow 5 s *
          Real.rpow δ s *
          ∑ i ∈ U, Real.rpow (r i / δ) s := by
    have h4 :
        ∑ i ∈ U,
            (C.toReal * Real.rpow (5 * r i) s * (A.card : ℝ)) =
          C.toReal * (A.card : ℝ) *
            ∑ i ∈ U, Real.rpow (5 * r i) s := by
      have h_comm :
          ∀ i ∈ U,
            C.toReal * Real.rpow (5 * r i) s * (A.card : ℝ) =
              C.toReal * (A.card : ℝ) * Real.rpow (5 * r i) s := by
        intro i _
        ring
      rw [Finset.sum_congr rfl h_comm, Finset.mul_sum]
    rw [h4]
    have h5 :
        ∑ i ∈ U, Real.rpow (5 * r i) s =
          ∑ i ∈ U,
            (Real.rpow 5 s * Real.rpow δ s *
              Real.rpow (r i / δ) s) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact h_rpow_factor i hi
    rw [h5]
    have h6 :
        ∑ i ∈ U,
            (Real.rpow 5 s * Real.rpow δ s *
              Real.rpow (r i / δ) s) =
          Real.rpow 5 s * Real.rpow δ s *
            ∑ i ∈ U, Real.rpow (r i / δ) s := by
      rw [Finset.mul_sum]
    rw [h6] <;> ring
  have h_coeff_nonneg :
      0 ≤ C.toReal * (A.card : ℝ) *
        Real.rpow 5 s * Real.rpow δ s := by
    have h1 : 0 ≤ C.toReal := by positivity
    have h2 : 0 ≤ (A.card : ℝ) := by positivity
    have h3 : 0 ≤ Real.rpow 5 s :=
      Real.rpow_nonneg (by norm_num) s
    have h4 : 0 ≤ Real.rpow δ s :=
      Real.rpow_nonneg (by linarith) s
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
  have h_final :
      (S.card : ℝ) ≤
        C.toReal * (A.card : ℝ) * Real.rpow 5 s *
          Real.rpow δ s * ((A'.card : ℝ) / 99) := by
    calc
      (S.card : ℝ) ≤
          ∑ i ∈ U, (ballCountNat A (y i) (5 * r i) : ℝ) :=
        hS_card3
      _ ≤ ∑ i ∈ U,
          (C.toReal * Real.rpow (5 * r i) s * (A.card : ℝ)) :=
        h_sum_frost
      _ = C.toReal * (A.card : ℝ) * Real.rpow 5 s *
          Real.rpow δ s *
          ∑ i ∈ U, Real.rpow (r i / δ) s := h_sum_factor
      _ ≤ C.toReal * (A.card : ℝ) * Real.rpow 5 s *
          Real.rpow δ s * ((A'.card : ℝ) / 99) := by
        exact mul_le_mul_of_nonneg_left h_sum_rpow h_coeff_nonneg
  have h_card_eq :
      (A.card : ℝ) = (A'.card : ℝ) + (S.card : ℝ) := by
    have h_disj : Disjoint A' S := by
      simp [S, Finset.disjoint_left] <;> tauto
    have h : A'.card + S.card = (A' ∪ S).card := by
      rw [Finset.card_union_of_disjoint h_disj]
    have h_union : A' ∪ S = A := by
      rw [Finset.union_sdiff_of_subset h_sub]
    have h5 : A'.card + S.card = A.card := by
      rw [h, h_union]
    exact_mod_cast h5.symm
  have h_final2 :
      (A.card : ℝ) ≤
        (A'.card : ℝ) +
          C.toReal * (A.card : ℝ) * Real.rpow 5 s *
            Real.rpow δ s * ((A'.card : ℝ) / 99) := by
    have h : (A.card : ℝ) = (A'.card : ℝ) + (S.card : ℝ) := h_card_eq
    linarith [h_final]
  have h_goal :
      (A.card : ℝ) ≤
        (A'.card : ℝ) *
          (1 + Real.rpow 5 s *
            (C.toReal * (A.card : ℝ) * Real.rpow δ s) / 99) := by
    have h6 :
        (A'.card : ℝ) +
            C.toReal * (A.card : ℝ) * Real.rpow 5 s *
              Real.rpow δ s * ((A'.card : ℝ) / 99) =
          (A'.card : ℝ) *
            (1 + Real.rpow 5 s *
              (C.toReal * (A.card : ℝ) * Real.rpow δ s) / 99) := by
      ring
    rw [h6] at h_final2
    exact h_final2
  exact h_goal

/-! ## Maximal Katz--Tao subset existence -/

lemma singleton_is_katz_tao {n : ℕ} {δ s : ℝ}
    (hδ : 0 < δ) (hs : 0 < s) {z : Point n} :
    ({z} : DiscreteSet n).IsKatzTao δ s 100 := by
  intro y r hδr _
  have h1 : ({z} : DiscreteSet n).ballCount y r ≤ 1 := by
    simp only [DiscreteSet.ballCount]
    have h_sub :
        (({z} : DiscreteSet n).filter fun y_1 => dist y_1 y ≤ r) ⊆
          ({z} : DiscreteSet n) := Finset.filter_subset _ _
    have h_card :
        (({z} : DiscreteSet n).filter fun y_1 => dist y_1 y ≤ r).card ≤
          1 := by
      calc
        _ ≤ ({z} : DiscreteSet n).card := Finset.card_le_card h_sub
        _ = 1 := by simp
    exact_mod_cast h_card
  have h3 : 1 ≤ r / δ := by
    exact (one_le_div hδ).mpr hδr
  have h4 : (1 : ℝ) ≤ Real.rpow (r / δ) s := by
    apply Real.one_le_rpow <;> linarith
  have h5 : (1 : ENNReal) ≤ Kakeya.realRpowENN (r / δ) s := by
    rw [Kakeya.realRpowENN]
    have h51 :
        ENNReal.ofReal (1 : ℝ) ≤
          ENNReal.ofReal (Real.rpow (r / δ) s) := by
      gcongr
    simpa using h51
  have h6 :
      (1 : ENNReal) ≤
        (100 : ENNReal) * Kakeya.realRpowENN (r / δ) s := by
    calc
      (1 : ENNReal) ≤ (100 : ENNReal) := by norm_num
      _ ≤ (100 : ENNReal) * Kakeya.realRpowENN (r / δ) s :=
        le_mul_of_one_le_right (by norm_num) h5
  exact le_trans h1 h6

lemma exists_maximal_katz_tao {n : ℕ} {δ s : ℝ}
    (hδ : 0 < δ) (hs : 0 < s)
    {A : DiscreteSet n} (hA : A.Nonempty) :
    ∃ A' : DiscreteSet n,
      A' ⊆ A ∧ A'.Nonempty ∧ A'.IsKatzTao δ s 100 ∧
        ∀ x ∈ A \ A', ¬ (A' ∪ {x}).IsKatzTao δ s 100 := by
  let S : Finset (DiscreteSet n) :=
    A.powerset.filter (fun B => B.Nonempty ∧ B.IsKatzTao δ s 100)
  have hS_nonempty : S.Nonempty := by
    rcases hA with ⟨x, hx⟩
    have h1 : ({x} : DiscreteSet n) ∈ A.powerset := by
      simp only [Finset.mem_powerset] <;> simp [hx]
    have h2 : ({x} : DiscreteSet n).Nonempty := by simp
    have h3 : ({x} : DiscreteSet n).IsKatzTao δ s 100 :=
      singleton_is_katz_tao hδ hs
    have h_in : ({x} : DiscreteSet n) ∈ S := by
      simp only [S, Finset.mem_filter]
      exact ⟨h1, h2, h3⟩
    have h_ne : S ≠ ∅ := by
      intro h
      rw [h] at h_in
      simpa using h_in
    exact Finset.nonempty_iff_ne_empty.mpr h_ne
  rcases
      Finset.exists_max_image S (fun B : DiscreteSet n => B.card)
        hS_nonempty with
    ⟨A', hA'_in_S, hA'_max⟩
  have hA'_in_powerset : A' ∈ A.powerset := by
    simp only [S, Finset.mem_filter] at hA'_in_S
    exact hA'_in_S.1
  have hA'_subset : A' ⊆ A :=
    Finset.mem_powerset.mp hA'_in_powerset
  have hA'_props :
      A'.Nonempty ∧ A'.IsKatzTao δ s 100 := by
    simp only [S, Finset.mem_filter] at hA'_in_S
    exact hA'_in_S.2
  refine ⟨A', hA'_subset, hA'_props.1, hA'_props.2, ?_⟩
  intro x hx
  have hsdiff : x ∈ A ∧ x ∉ A' := Finset.mem_sdiff.mp hx
  have h_x_in_A : x ∈ A := hsdiff.1
  have h_x_notin_A' : x ∉ A' := hsdiff.2
  by_contra h
  have h41 : A' ∪ {x} ⊆ A := by
    apply Finset.union_subset
    · exact hA'_subset
    · simp [h_x_in_A]
  have h_x_in_union : x ∈ A' ∪ {x} :=
    Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self x))
  have h42 : (A' ∪ {x}).Nonempty := by
    exact
      Finset.nonempty_iff_ne_empty.mpr
        (fun h => by rw [h] at h_x_in_union; simpa using h_x_in_union)
  have h4 : (A' ∪ {x}) ∈ S := by
    simp only [S, Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr h41, h42, h⟩
  have h5 : (A' ∪ {x}).card > A'.card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · apply Finset.subset_union_left
    · intro h6
      have h8 : x ∈ A' ∪ {x} :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self x))
      have h9 : A' ∪ {x} = A' := h6.symm
      rw [h9] at h8
      exact h_x_notin_A' h8
  have h8 := hA'_max (A' ∪ {x}) h4
  linarith

/-! ## Final lifting: real inequality to ENNReal conclusion -/

lemma final_lifting {n : ℕ} {δ s : ℝ} {C : ENNReal}
    {A A' : DiscreteSet n}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (hs : 0 < s)
    (hC_one : 1 ≤ C) (hC_top : C ≠ ⊤)
    (h_main_real :
      (A.card : ℝ) ≤
        (A'.card : ℝ) *
          (1 + Real.rpow 5 s * C.toReal *
            (A.card : ℝ) * Real.rpow δ s / 99))
    (hA_card : Kakeya.realRpowENN δ (-s) ≤ A.enncard) :
    Kakeya.realRpowENN δ (-s) ≤
      ENNReal.ofReal ((99 + Real.rpow 5 s) / 99) *
        ENNReal.ofReal (1 + Real.log δ⁻¹) * C * A'.enncard := by
  set N : ℝ := (A.card : ℝ) with hN
  set N' : ℝ := (A'.card : ℝ) with hN'
  set C_R : ℝ := C.toReal with hC_R
  set a : ℝ := Real.rpow 5 s with ha
  set M : ℝ := C_R * N * Real.rpow δ s with hM
  have hN_nonneg : 0 ≤ N := by
    exact_mod_cast Nat.cast_nonneg A.card
  have hδns_nonneg : 0 ≤ Real.rpow δ (-s) := by
    apply Real.rpow_nonneg <;> linarith
  have h1 : Real.rpow δ (-s) ≤ N := by
    have h1a :
        Kakeya.realRpowENN δ (-s) =
          ENNReal.ofReal (Real.rpow δ (-s)) := by
      rw [Kakeya.realRpowENN] <;> rfl
    have h1b : A.enncard = ENNReal.ofReal N := by
      simp [DiscreteSet.enncard, hN] <;> norm_cast
    have hA_card' :
        ENNReal.ofReal (Real.rpow δ (-s)) ≤ ENNReal.ofReal N := by
      rw [h1a, h1b] at hA_card
      exact hA_card
    exact (ENNReal.ofReal_le_ofReal_iff hN_nonneg).mp hA_card'
  have hδs_pos : 0 < Real.rpow δ s :=
    Real.rpow_pos_of_pos hδ_pos s
  have hδns_pos : 0 < Real.rpow δ (-s) :=
    Real.rpow_pos_of_pos hδ_pos (-s)
  have hN_pos : 0 < N := by linarith
  have hCR_ge_one : 1 ≤ C_R := by
    have h22 : (1 : ENNReal) ≠ ⊤ := by simp
    exact (ENNReal.toReal_le_toReal h22 hC_top).mpr hC_one
  have hCR_pos : 0 < C_R := by linarith
  have ha_pos : 0 < a := by
    simp [ha]
    exact Real.rpow_pos_of_pos (by norm_num) s
  have hM_pos : 0 < M := by
    simp [hM] <;> positivity
  have h3 : Real.rpow δ (-s) * Real.rpow δ s = 1 := by
    have h4 :
        Real.rpow δ (-s + s) =
          Real.rpow δ (-s) * Real.rpow δ s :=
      Real.rpow_add (by linarith) (-s) s
    have h5 : -s + s = 0 := by ring
    rw [h5] at h4
    have h6 : Real.rpow δ 0 = 1 := by norm_num
    rw [h6] at h4
    exact h4.symm
  have h4 : C_R ≤ M := by
    have h5 :
        Real.rpow δ (-s) * (C_R * Real.rpow δ s) ≤
          N * (C_R * Real.rpow δ s) := by
      gcongr <;> linarith
    have h6 :
        Real.rpow δ (-s) * (C_R * Real.rpow δ s) = C_R := by
      have h7 :
          Real.rpow δ (-s) * (C_R * Real.rpow δ s) =
            C_R * (Real.rpow δ (-s) * Real.rpow δ s) := by
        ring
      rw [h7, h3] <;> ring
    rw [h6] at h5
    have h8 : N * (C_R * Real.rpow δ s) = M := by
      simp [hM] <;> ring
    rw [h8] at h5
    exact h5
  have hM_ge_one : 1 ≤ M := by linarith
  have h5 : N ≤ N' * (1 + a * M / 99) := by
    have h51 :
        N ≤ N' * (1 + a * C_R * N * Real.rpow δ s / 99) := by
      simpa [hN, hN', hC_R] using h_main_real
    have h52 :
        1 + a * C_R * N * Real.rpow δ s / 99 =
          1 + a * M / 99 := by
      simp [hM] <;> ring
    rw [h52] at h51
    exact h51
  have h6 : N * 99 ≤ N' * (99 + a * M) := by
    have h7 : N ≤ N' * ((99 + a * M) / 99) := by
      have h8 : 1 + a * M / 99 = (99 + a * M) / 99 := by
        ring
      rw [h8] at h5
      exact h5
    nlinarith
  have h9 : 0 < 99 + a * M := by positivity
  have h10 : N' ≥ N * 99 / (99 + a * M) := by
    calc
      N' = N' * (99 + a * M) / (99 + a * M) := by
        field_simp [h9.ne'] <;> ring
      _ ≥ N * 99 / (99 + a * M) := by gcongr
  have h11 : 99 + a * M ≤ (99 + a) * M := by
    have h12 : 99 ≤ 99 * M := by nlinarith
    nlinarith
  have h13 : 0 < (99 + a) * M := by positivity
  have h14 :
      N * 99 / (99 + a * M) ≥
        N * 99 / ((99 + a) * M) := by
    apply div_le_div_of_nonneg_left
    · positivity
    · positivity
    · nlinarith
  have h15 : N' ≥ N * 99 / ((99 + a) * M) := by
    linarith
  have h16 : N / M = Real.rpow δ (-s) / C_R := by
    have h17 : M = C_R * N * Real.rpow δ s := by simp [hM]
    rw [h17]
    have h18 :
        N / (C_R * N * Real.rpow δ s) =
          1 / (C_R * Real.rpow δ s) := by
      field_simp [hN_pos.ne', hCR_pos.ne', hδs_pos.ne'] <;> ring
    rw [h18]
    have h19 :
        1 / (C_R * Real.rpow δ s) =
          Real.rpow δ (-s) / C_R := by
      have h20 : Real.rpow δ (-s) = (Real.rpow δ s)⁻¹ := by
        have h21 : Real.rpow δ (-s) * Real.rpow δ s = 1 := h3
        field_simp [hδs_pos.ne'] at h21 ⊢ <;> exact h21
      rw [h20]
      field_simp [hCR_pos.ne', hδs_pos.ne'] <;> ring
    exact h19
  have h21 :
      N' ≥ 99 * Real.rpow δ (-s) / ((99 + a) * C_R) := by
    calc
      N' ≥ N * 99 / ((99 + a) * M) := h15
      _ = (N / M) * (99 / (99 + a)) := by
        field_simp [h13.ne'] <;> ring
      _ = (Real.rpow δ (-s) / C_R) * (99 / (99 + a)) := by
        rw [h16]
      _ = 99 * Real.rpow δ (-s) / ((99 + a) * C_R) := by
        field_simp [hCR_pos.ne'] <;> ring
  have h22 :
      Real.rpow δ (-s) ≤ ((99 + a) / 99) * C_R * N' := by
    have h23 : 0 < (99 + a) * C_R := by positivity
    have h24 :
        N' * (((99 + a) * C_R) / 99) ≥
          Real.rpow δ (-s) := by
      calc
        N' * (((99 + a) * C_R) / 99) ≥
            (99 * Real.rpow δ (-s) / ((99 + a) * C_R)) *
              (((99 + a) * C_R) / 99) := by
          gcongr
        _ = Real.rpow δ (-s) := by
          field_simp [h23.ne'] <;> ring
    have h25 :
        N' * (((99 + a) * C_R) / 99) =
          ((99 + a) / 99) * C_R * N' := by
      ring
    rw [h25] at h24
    exact h24
  have h_log_pos : 0 < Real.log δ⁻¹ := by
    apply Real.log_pos
    have h24 : 1 < δ⁻¹ := by
      have h_pos : 0 < δ := hδ_pos
      calc
        δ⁻¹ = 1 / δ := by field_simp [h_pos.ne'] <;> ring
        _ > 1 / 1 := by gcongr
        _ = 1 := by norm_num
    exact h24
  have h25 : 1 ≤ 1 + Real.log δ⁻¹ := by linarith
  have h26 :
      Real.rpow δ (-s) ≤
        ((99 + a) / 99) * (1 + Real.log δ⁻¹) * C_R * N' := by
    calc
      Real.rpow δ (-s) ≤ ((99 + a) / 99) * C_R * N' := h22
      _ = ((99 + a) / 99) * (1 : ℝ) * C_R * N' := by ring
      _ ≤ ((99 + a) / 99) * (1 + Real.log δ⁻¹) * C_R * N' := by
        gcongr <;> linarith
  set X : ℝ :=
    ((99 + a) / 99) * (1 + Real.log δ⁻¹) * C_R * N' with hX
  have h29 :
      ENNReal.ofReal (Real.rpow δ (-s)) ≤ ENNReal.ofReal X := by
    have h : Real.rpow δ (-s) ≤ X := by
      simpa [hX, ha] using h26
    exact ENNReal.ofReal_le_ofReal h
  have h301 :
      ENNReal.ofReal
          ((((99 + a) / 99) * (1 + Real.log δ⁻¹)) * (C_R * N')) =
        ENNReal.ofReal
            (((99 + a) / 99) * (1 + Real.log δ⁻¹)) *
          ENNReal.ofReal (C_R * N') := by
    rw [ENNReal.ofReal_mul] <;> positivity
  have h302 :
      ENNReal.ofReal (((99 + a) / 99) * (1 + Real.log δ⁻¹)) =
        ENNReal.ofReal ((99 + a) / 99) *
          ENNReal.ofReal (1 + Real.log δ⁻¹) := by
    rw [ENNReal.ofReal_mul] <;> positivity
  have h303 :
      ENNReal.ofReal (C_R * N') =
        ENNReal.ofReal C_R * ENNReal.ofReal N' := by
    rw [ENNReal.ofReal_mul] <;> positivity
  have h30 :
      ENNReal.ofReal X =
        ENNReal.ofReal ((99 + a) / 99) *
          ENNReal.ofReal (1 + Real.log δ⁻¹) *
          ENNReal.ofReal C_R * ENNReal.ofReal N' := by
    have hX_eq :
        X =
          (((99 + a) / 99) * (1 + Real.log δ⁻¹)) * (C_R * N') := by
      simp [hX] <;> ring
    rw [hX_eq, h301, h302, h303] <;> ring
  have h31 : ENNReal.ofReal C_R = C := by
    rw [ENNReal.ofReal_toReal hC_top]
  have h32 : ENNReal.ofReal N' = A'.enncard := by
    simp [DiscreteSet.enncard, hN'] <;> norm_cast
  have h33 :
      Kakeya.realRpowENN δ (-s) =
        ENNReal.ofReal (Real.rpow δ (-s)) := by
    rw [Kakeya.realRpowENN] <;> rfl
  have h34 :
      ENNReal.ofReal ((99 + a) / 99) =
        ENNReal.ofReal ((99 + Real.rpow 5 s) / 99) := by
    rw [ha]
  rw [h33]
  rw [h30, h31, h32, h34] at h29
  exact h29

/-! ## Main theorem -/

theorem frostman_to_katz_tao : FrostmanToKatzTaoStatement := by
  intro n s hs_pos hsn
  let L : ENNReal := ENNReal.ofReal ((99 + Real.rpow 5 s) / 99)
  use L
  constructor
  · have h1 : 0 < Real.rpow 5 s :=
      Real.rpow_pos_of_pos (by norm_num) s
    have h2 : (99 + Real.rpow 5 s) / 99 ≥ 1 := by
      have h3 : 99 + Real.rpow 5 s ≥ 99 := by linarith
      have h4 : (99 + Real.rpow 5 s) / 99 ≥ 99 / 99 := by gcongr
      linarith
    have h5 :
        (1 : ENNReal) ≤
          ENNReal.ofReal ((99 + Real.rpow 5 s) / 99) := by
      rw [ENNReal.one_le_ofReal]
      linarith
    exact h5
  constructor
  · exact ENNReal.ofReal_ne_top
  intro δ C hδ_pos hδ_lt_one hC_one hC_top
    A hA_nonempty hA_unit _hA_sep hA_frost hA_card
  rcases exists_maximal_katz_tao hδ_pos hs_pos hA_nonempty with
    ⟨A', h_sub, hA'_nonempty, h_kt, h_max_union⟩
  have h_max_insert :
      ∀ x ∈ A \ A', ¬ (insert x A').IsKatzTao δ s 100 := by
    intro x hx
    have h_eq : insert x A' = A' ∪ {x} := by
      ext z
      simp [Finset.mem_insert, Finset.mem_union] <;> tauto
    rw [h_eq]
    exact h_max_union x hx
  by_cases h_eq : A' = A
  · subst h_eq
    have h_bound :
        Kakeya.realRpowENN δ (-s) ≤
          L * ENNReal.ofReal (1 + Real.log δ⁻¹) *
            C * A'.enncard := by
      have h1 : Kakeya.realRpowENN δ (-s) ≤ A'.enncard := hA_card
      have h2 : (1 : ENNReal) ≤ L := by
        have h1 : 0 < Real.rpow 5 s :=
          Real.rpow_pos_of_pos (by norm_num) s
        have h2 : (99 + Real.rpow 5 s) / 99 ≥ 1 := by linarith
        rw [ENNReal.one_le_ofReal]
        linarith
      have h3 :
          (1 : ENNReal) ≤ ENNReal.ofReal (1 + Real.log δ⁻¹) := by
        have h_log_pos : 0 < Real.log δ⁻¹ := by
          apply Real.log_pos
          have h : 1 < δ⁻¹ := by
            have h_pos : 0 < δ := hδ_pos
            calc
              δ⁻¹ = 1 / δ := by field_simp [h_pos.ne'] <;> ring
              _ > 1 / 1 := by gcongr
              _ = 1 := by norm_num
          exact h
        have h4 : 1 ≤ 1 + Real.log δ⁻¹ := by linarith
        rw [ENNReal.one_le_ofReal]
        linarith
      have h4 :
          A'.enncard ≤
            L * ENNReal.ofReal (1 + Real.log δ⁻¹) *
              C * A'.enncard := by
        calc
          A'.enncard =
              (1 : ENNReal) * (1 : ENNReal) *
                (1 : ENNReal) * A'.enncard := by ring
          _ ≤ L * ENNReal.ofReal (1 + Real.log δ⁻¹) *
              C * A'.enncard := by gcongr <;> tauto
      exact le_trans h1 h4
    exact ⟨A', hA'_nonempty, h_sub, h_kt, h_bound⟩
  · have h_main_real :
        (A.card : ℝ) ≤
          (A'.card : ℝ) *
            (1 + Real.rpow 5 s * C.toReal *
              (A.card : ℝ) * Real.rpow δ s / 99) := by
      have h :=
        vitali_covering_step hδ_pos hs_pos hC_one hC_top
          hA_frost hA_unit h_sub h_kt h_max_insert
      simpa [mul_assoc] using h
    have h_bound :
        Kakeya.realRpowENN δ (-s) ≤
          L * ENNReal.ofReal (1 + Real.log δ⁻¹) *
            C * A'.enncard :=
      final_lifting hδ_pos hδ_lt_one hs_pos hC_one hC_top
        h_main_real hA_card
    exact ⟨A', hA'_nonempty, h_sub, h_kt, h_bound⟩

end Kakeya.Assouad
