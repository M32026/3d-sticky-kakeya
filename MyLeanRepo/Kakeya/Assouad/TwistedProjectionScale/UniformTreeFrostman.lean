import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CubicGridPartitionTree
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FrostmanScaling
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalFrostmanBlockPruningStatement
import Mathlib.Tactic

/-!
# Frostman bounds from a uniform cubic-grid subtree

This module contains the scale-selection and counting consequences used after
exact branching uniformization.  It is independent of the historical
relative-cardinality formulation of the spacing lemma.
-/

noncomputable section

namespace Kakeya.Assouad

lemma uniform_tree_frostman_core_real
    {n : ℕ} {A' : DiscreteSet n}
    {x : Point n} {r r_k d : ℝ}
    {C_geom M_k N_k : ℝ}
    (hd : 0 ≤ d)
    (hrk_pos : 0 < r_k)
    (hrk_le_r : r_k ≤ r)
    (_hr_le_one : r ≤ 1)
    (hC_nonneg : 0 ≤ C_geom)
    (_hM_nonneg : 0 ≤ M_k)
    (hN_pos : 0 < N_k)
    (h_geom : (A'.ballCount x r).toReal ≤ C_geom * M_k)
    (h_total : N_k * M_k ≤ A'.enncard.toReal)
    (h_branch : Real.rpow r_k (-d) ≤ N_k) :
    (A'.ballCount x r).toReal ≤
      C_geom * Real.rpow r d * A'.enncard.toReal := by
  have hM :
      M_k ≤ A'.enncard.toReal / N_k := by
    calc
      M_k = (N_k * M_k) / N_k := by
        field_simp [hN_pos.ne']
      _ ≤ A'.enncard.toReal / N_k := by gcongr
  have hreciprocal : 1 / N_k ≤ Real.rpow r_k d := by
    have hproduct :
        Real.rpow r_k (-d) * Real.rpow r_k d = 1 := by
      calc
        Real.rpow r_k (-d) * Real.rpow r_k d =
            Real.rpow r_k (-d + d) :=
          (Real.rpow_add hrk_pos (-d) d).symm
        _ = 1 := by simp
    calc
      1 / N_k ≤ 1 / Real.rpow r_k (-d) := by
        exact one_div_le_one_div_of_le
          (Real.rpow_pos_of_pos hrk_pos (-d)) h_branch
      _ = Real.rpow r_k d := by
        have hne : Real.rpow r_k (-d) ≠ 0 :=
          (Real.rpow_pos_of_pos hrk_pos (-d)).ne'
        field_simp [hne]
        linarith
  have hrpow :
      Real.rpow r_k d ≤ Real.rpow r d :=
    Real.rpow_le_rpow (by linarith) hrk_le_r hd
  calc
    (A'.ballCount x r).toReal
        ≤ C_geom * M_k := h_geom
    _ ≤ C_geom * (A'.enncard.toReal / N_k) := by gcongr
    _ = C_geom * A'.enncard.toReal * (1 / N_k) := by ring
    _ ≤ C_geom * A'.enncard.toReal * Real.rpow r_k d := by
      gcongr
    _ ≤ C_geom * A'.enncard.toReal * Real.rpow r d := by
      gcongr
    _ = C_geom * Real.rpow r d * A'.enncard.toReal := by ring

lemma uniform_tree_frostman_core_real_with_loss
    {n : ℕ} {A' : DiscreteSet n}
    {x : Point n} {r r_k d : ℝ}
    {C_geom K M_k N_k : ℝ}
    (hd : 0 ≤ d)
    (hrk_pos : 0 < r_k)
    (hrk_le_r : r_k ≤ r)
    (_hr_le_one : r ≤ 1)
    (hC_nonneg : 0 ≤ C_geom)
    (hK_nonneg : 0 ≤ K)
    (_hM_nonneg : 0 ≤ M_k)
    (hN_pos : 0 < N_k)
    (h_geom :
      (A'.ballCount x r).toReal ≤
        C_geom * M_k)
    (h_total :
      N_k * M_k ≤ A'.enncard.toReal)
    (h_branch :
      Real.rpow r_k (-d) ≤ K * N_k) :
    (A'.ballCount x r).toReal ≤
      C_geom * K * Real.rpow r d *
        A'.enncard.toReal := by
  have hM :
      M_k ≤ A'.enncard.toReal / N_k := by
    calc
      M_k = (N_k * M_k) / N_k := by
        field_simp [hN_pos.ne']
      _ ≤ A'.enncard.toReal / N_k := by
        gcongr
  have hreciprocal :
      1 / N_k ≤ K * Real.rpow r_k d := by
    have hproduct :
        Real.rpow r_k (-d) *
            Real.rpow r_k d = 1 := by
      calc
        Real.rpow r_k (-d) *
              Real.rpow r_k d =
            Real.rpow r_k (-d + d) :=
          (Real.rpow_add hrk_pos (-d) d).symm
        _ = 1 := by simp
    have hmul :
        Real.rpow r_k (-d) *
            Real.rpow r_k d ≤
          (K * N_k) * Real.rpow r_k d :=
      mul_le_mul_of_nonneg_right h_branch
        (Real.rpow_nonneg hrk_pos.le d)
    rw [hproduct] at hmul
    calc
      1 / N_k ≤
          ((K * N_k) * Real.rpow r_k d) /
            N_k := by
        exact div_le_div_of_nonneg_right
          hmul hN_pos.le
      _ = K * Real.rpow r_k d := by
        field_simp [hN_pos.ne']
  have hrpow :
      Real.rpow r_k d ≤ Real.rpow r d :=
    Real.rpow_le_rpow (by linarith)
      hrk_le_r hd
  calc
    (A'.ballCount x r).toReal
        ≤ C_geom * M_k := h_geom
    _ ≤ C_geom *
          (A'.enncard.toReal / N_k) := by
      gcongr
    _ = C_geom * A'.enncard.toReal *
          (1 / N_k) := by ring
    _ ≤ C_geom * A'.enncard.toReal *
          (K * Real.rpow r_k d) := by
      gcongr
    _ ≤ C_geom * A'.enncard.toReal *
          (K * Real.rpow r d) := by
      gcongr
    _ = C_geom * K * Real.rpow r d *
          A'.enncard.toReal := by ring

lemma frostman_to_finite_scale_content
    {n : ℕ} {A : DiscreteSet n}
    {fineScale s s' : ℝ} {C : ENNReal}
    (hA_nonempty : A.Nonempty)
    (hfine : 0 < fineScale)
    (hFrost : A.IsFrostman fineScale s C)
    (hs'_le_s : s' ≤ s)
    (hs'_nonneg : 0 ≤ s') :
    HasFiniteScaleHausdorffContent
      A fineScale s' C⁻¹ := by
  intro m center radius hranges hcover
  have hFrost' : A.IsFrostman fineScale s' C :=
    frostman_exponent_weakening
      hFrost hfine hs'_nonneg hs'_le_s
  let pieces : Fin m → DiscreteSet n := fun i =>
    A.filter fun p => dist p (center i) ≤ radius i
  have hpiece :
      ∀ i : Fin m,
        (pieces i).enncard ≤
          C * Kakeya.realRpowENN (radius i) s' *
            A.enncard := by
    intro i
    exact
      hFrost' (center i) (radius i)
        (hranges i).1 (hranges i).2
  have hcover' :
      A ⊆ Finset.biUnion Finset.univ pieces := by
    intro p hp
    rcases Set.mem_iUnion.mp (hcover hp) with ⟨i, hi⟩
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i,
        Finset.mem_filter.mpr ⟨hp, hi⟩⟩
  have hcard :
      A.enncard ≤ ∑ i : Fin m, (pieces i).enncard := by
    have hnat :
        A.card ≤ ∑ i : Fin m, (pieces i).card :=
      (Finset.card_le_card hcover').trans
        Finset.card_biUnion_le
    simpa [DiscreteSet.enncard] using
      (show
        (A.card : ENNReal) ≤
          ∑ i : Fin m, ((pieces i).card : ENNReal) by
        exact_mod_cast hnat)
  let total : ENNReal :=
    ∑ i : Fin m,
      Kakeya.realRpowENN (radius i) s'
  have hsum :
      ∑ i : Fin m, (pieces i).enncard ≤
        C * total * A.enncard := by
    calc
      ∑ i : Fin m, (pieces i).enncard
          ≤ ∑ i : Fin m,
              C * Kakeya.realRpowENN (radius i) s' *
                A.enncard := by
            exact Finset.sum_le_sum fun i _ => hpiece i
      _ = C * total * A.enncard := by
            simp [total, Finset.mul_sum, Finset.sum_mul]
  have hmain :
      A.enncard ≤ C * total * A.enncard :=
    hcard.trans hsum
  have hA_zero : A.enncard ≠ 0 := by
    simpa [DiscreteSet.enncard] using
      (show (A.card : ENNReal) ≠ 0 by
        exact_mod_cast hA_nonempty.card_pos.ne')
  have hA_top : A.enncard ≠ ⊤ := by
    simp [DiscreteSet.enncard]
  by_cases hC_top : C = ⊤
  · simp [hC_top]
  by_cases hC_zero : C = 0
  · rw [hC_zero] at hmain
    simp at hmain
    exact False.elim (hA_zero hmain)
  have hone : (1 : ENNReal) ≤ C * total := by
    have hcancel :
        A.enncard * A.enncard⁻¹ ≤
          (C * total * A.enncard) *
            A.enncard⁻¹ := by
      gcongr
    rw [ENNReal.mul_inv_cancel hA_zero hA_top] at hcancel
    have hrhs :
        (C * total * A.enncard) * A.enncard⁻¹ =
          C * total := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hA_zero hA_top,
        mul_one]
    rwa [hrhs] at hcancel
  calc
    C⁻¹ = C⁻¹ * 1 := by simp
    _ ≤ C⁻¹ * (C * total) := by gcongr
    _ = total := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hC_zero hC_top,
        one_mul]

lemma find_rel_level
    {base : ℕ} (hbase : 2 ≤ base)
    {maxLevel : ℕ} {r : ℝ}
    (hr_pos : 0 < r)
    (hr_lt_one : r < 1)
    (hfine : 1 / (base : ℝ) ^ maxLevel ≤ r) :
    ∃ m : ℕ,
      0 < m ∧
      m ≤ maxLevel ∧
      1 / (base : ℝ) ^ m ≤ r ∧
      r < 1 / (base : ℝ) ^ (m - 1) := by
  have hbase_growth :
      ∀ n : ℕ, (n : ℝ) ≤ (base : ℝ) ^ n := by
    intro n
    have htwo : n ≤ 2 ^ n := by
      induction n with
      | zero => norm_num
      | succ n ih =>
          have hone : 1 ≤ 2 ^ n :=
            Nat.one_le_two_pow
          calc
            n + 1 ≤ 2 ^ n + 2 ^ n := add_le_add ih hone
            _ = 2 ^ (n + 1) := by
              rw [pow_succ]
              ring
    exact_mod_cast
      htwo.trans (Nat.pow_le_pow_left hbase n)
  let predicate : ℕ → Prop :=
    fun n => 1 / r ≤ (base : ℝ) ^ n
  have hexists : ∃ n, predicate n := by
    obtain ⟨n, hn⟩ := exists_nat_ge (1 / r)
    have hn' : 1 / r ≤ (n : ℝ) := by
      exact_mod_cast hn
    exact ⟨n, hn'.trans (hbase_growth n)⟩
  let m := Nat.find hexists
  have hm_spec : predicate m := Nat.find_spec hexists
  have hm_pos : 0 < m := by
    by_contra h
    have hm_zero : m = 0 := by omega
    rw [hm_zero] at hm_spec
    dsimp only [predicate] at hm_spec
    norm_num at hm_spec
    exact
      (not_le_of_gt
        (one_lt_one_div hr_pos hr_lt_one))
        (by simpa [one_div] using hm_spec)
  have hm_min : ¬predicate (m - 1) :=
    Nat.find_min hexists (by omega)
  have hlower :
      1 / (base : ℝ) ^ m ≤ r := by
    have hpow : 0 < (base : ℝ) ^ m := by positivity
    calc
      1 / (base : ℝ) ^ m
          ≤ 1 / (1 / r) := by gcongr
      _ = r := by field_simp [hr_pos.ne']
  have hupper :
      r < 1 / (base : ℝ) ^ (m - 1) := by
    have hlt :
        (base : ℝ) ^ (m - 1) < 1 / r :=
      lt_of_not_ge hm_min
    have hpow : 0 < (base : ℝ) ^ (m - 1) := by positivity
    calc
      r = 1 / (1 / r) := by field_simp [hr_pos.ne']
      _ < 1 / (base : ℝ) ^ (m - 1) := by gcongr
  have hm_le : m ≤ maxLevel := by
    by_contra hnot
    have hmax : predicate maxLevel := by
      dsimp only [predicate]
      have hpow : 0 < (base : ℝ) ^ maxLevel := by positivity
      have hinv :
          1 / r ≤ (base : ℝ) ^ maxLevel := by
        calc
          1 / r ≤
              1 / (1 / (base : ℝ) ^ maxLevel) := by
                gcongr
          _ = (base : ℝ) ^ maxLevel := by
                field_simp [hpow.ne']
      exact hinv
    exact Nat.find_min hexists (by omega) hmax
  exact ⟨m, hm_pos, hm_le, hlower, hupper⟩

lemma uniform_subtree_frostman
    (subtreePoints : DiscreteSet 3)
    (base : ℕ)
    (hbase : 2 ≤ base)
    (maxLevel : ℕ)
    (d : ℝ)
    (hd : 0 ≤ d)
    (fineScale : ℝ)
    (hfine : fineScale = 1 / (base : ℝ) ^ maxLevel)
    (N M : ℕ → ℕ)
    (h_total :
      ∀ m, 0 < m → m ≤ maxLevel →
        N m * M m = subtreePoints.card)
    (hN_pos :
      ∀ m, 0 < m → m ≤ maxLevel → 0 < N m)
    (h_ball_bound :
      ∀ m x r,
        0 < m →
        m ≤ maxLevel →
        1 / (base : ℝ) ^ m ≤ r →
        r * (base : ℝ) ^ m < base →
        (subtreePoints.ballCount x r).toReal ≤
          ((2 * base + 3) ^ 3 : ℝ) * (M m : ℝ))
    (h_branch_dim :
      ∀ m, 0 < m → m ≤ maxLevel →
        (base : ℝ) ^ ((m : ℝ) * d) ≤ N m) :
    subtreePoints.IsFrostman
      fineScale d ((2 * base + 3) ^ 3 : ENNReal) := by
  let constant : ENNReal := (2 * base + 3) ^ 3
  have hconstant_top : constant ≠ ⊤ := by
    apply ENNReal.pow_ne_top
    exact (ENNReal.add_ne_top).2
      ⟨ENNReal.mul_ne_top (by norm_num) (by simp),
        by norm_num⟩
  intro x r hr_fine hr_one
  have hr_pos : 0 < r := by
    have hfine_pos : 0 < fineScale := by
      rw [hfine]
      exact one_div_pos.mpr (by positivity)
    linarith
  by_cases hr_eq : r = 1
  · have hcount :
        subtreePoints.ballCount x r ≤
          subtreePoints.enncard := by
      simp [hr_eq, DiscreteSet.ballCount,
        DiscreteSet.enncard, Finset.card_le_card]
    have hone : (1 : ENNReal) ≤ constant := by
      change
        (1 : ENNReal) ≤
          (2 * (base : ENNReal) + 3) ^ 3
      apply one_le_pow₀
      calc
        (1 : ENNReal) ≤ 3 := by norm_num
        _ ≤ 2 * (base : ENNReal) + 3 := by
          exact le_add_of_nonneg_left bot_le
    have hrpow :
        Kakeya.realRpowENN r d = 1 := by
      simp [hr_eq, Kakeya.realRpowENN]
    change
      subtreePoints.ballCount x r ≤
        constant *
          Kakeya.realRpowENN r d *
            subtreePoints.enncard
    rw [hrpow, mul_one]
    exact hcount.trans
      (by
        simpa using
          mul_le_mul_right' hone subtreePoints.enncard)
  have hr_lt : r < 1 := lt_of_le_of_ne hr_one hr_eq
  have hscale :
      1 / (base : ℝ) ^ maxLevel ≤ r := by
    rwa [hfine] at hr_fine
  obtain ⟨m, hm_pos, hm_le, hm_lower, hm_upper⟩ :=
    find_rel_level hbase hr_pos hr_lt hscale
  let mesh : ℝ := 1 / (base : ℝ) ^ m
  have hmesh_pos : 0 < mesh := by positivity
  have hr_mesh :
      r * (base : ℝ) ^ m < base := by
    have hidentity :
        1 / (base : ℝ) ^ (m - 1) =
          (base : ℝ) / (base : ℝ) ^ m := by
      cases m with
      | zero => contradiction
      | succ m' =>
          simp [pow_succ] <;> field_simp <;> ring
    rw [hidentity] at hm_upper
    have hpow : 0 < (base : ℝ) ^ m := by positivity
    calc
      r * (base : ℝ) ^ m
          < ((base : ℝ) / (base : ℝ) ^ m) *
              (base : ℝ) ^ m := by gcongr
      _ = base := by field_simp [hpow.ne']
  have hgeom :
      (subtreePoints.ballCount x r).toReal ≤
        constant.toReal * (M m : ℝ) := by
    have h := h_ball_bound
      m x r hm_pos hm_le hm_lower hr_mesh
    have hconstant_real :
        constant.toReal = ((2 * base + 3) ^ 3 : ℝ) := by
      simp [constant] <;> norm_cast
    rwa [hconstant_real]
  have htotal :
      (N m : ℝ) * (M m : ℝ) ≤
        subtreePoints.enncard.toReal := by
    rw [show subtreePoints.enncard.toReal =
        (subtreePoints.card : ℝ) by
      simp [DiscreteSet.enncard]]
    exact_mod_cast (h_total m hm_pos hm_le).le
  have hbranch :
      Real.rpow mesh (-d) ≤ N m := by
    have hbase_pos : 0 < (base : ℝ) := by positivity
    have hmesh_eq :
        mesh = Real.rpow (base : ℝ) (-(m : ℝ)) := by
      dsimp only [mesh]
      calc
        1 / (base : ℝ) ^ m =
            (Real.rpow (base : ℝ) (m : ℝ))⁻¹ := by
          simp only [one_div]
          exact congrArg Inv.inv
            (Real.rpow_natCast (base : ℝ) m).symm
        _ = Real.rpow (base : ℝ) (-(m : ℝ)) :=
          (Real.rpow_neg hbase_pos.le (m : ℝ)).symm
    rw [hmesh_eq]
    have hrpow_mul :
        Real.rpow
            (Real.rpow (base : ℝ) (-(m : ℝ)))
            (-d) =
          Real.rpow (base : ℝ) ((-(m : ℝ)) * (-d)) := by
      exact (Real.rpow_mul hbase_pos.le (-(m : ℝ)) (-d)).symm
    rw [hrpow_mul]
    have hsource := h_branch_dim m hm_pos hm_le
    change
      Real.rpow (base : ℝ) ((m : ℝ) * d) ≤
        (N m : ℝ) at hsource
    simpa only [neg_mul_neg] using hsource
  have hreal :=
    uniform_tree_frostman_core_real
      hd hmesh_pos hm_lower hr_one
      (by positivity) (by positivity)
      (by exact_mod_cast hN_pos m hm_pos hm_le)
      hgeom htotal hbranch
  have hlhs_top :
      subtreePoints.ballCount x r ≠ ⊤ := by
    simp [DiscreteSet.ballCount]
  have hrpow_top :
      Kakeya.realRpowENN r d ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hpoints_top :
      subtreePoints.enncard ≠ ⊤ := by
    simp [DiscreteSet.enncard]
  have hrhs_top :
      constant * Kakeya.realRpowENN r d *
          subtreePoints.enncard ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hconstant_top hrpow_top)
      hpoints_top
  apply
    (ENNReal.toReal_le_toReal hlhs_top hrhs_top).mp
  simpa [constant, ENNReal.toReal_mul,
    Kakeya.realRpowENN,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hr_pos.le d)]
    using hreal

lemma uniform_subtree_content
    {subtreePoints : DiscreteSet 3}
    {fineScale d s' : ℝ}
    {constant : ENNReal}
    (hFrost :
      subtreePoints.IsFrostman fineScale d constant)
    (hs'_le_d : s' ≤ d)
    (hs'_nonneg : 0 ≤ s')
    (hfine_pos : 0 < fineScale)
    (h_nonempty : subtreePoints.Nonempty) :
    HasFiniteScaleHausdorffContent
      subtreePoints fineScale s' constant⁻¹ := by
  exact frostman_to_finite_scale_content
    h_nonempty hfine_pos hFrost
    hs'_le_d hs'_nonneg

end Kakeya.Assouad
