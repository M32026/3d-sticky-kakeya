import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyPBase
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CordobaSlabLower
import MyLeanRepo.Kakeya.Assouad.WZ1.CordobaProjectionCoveringGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.ImprovedSeparatedPoints
import MyLeanRepo.Kakeya.Assouad.WZ1.CordobaL2
import MyLeanRepo.Kakeya.Assouad.WZ1.CordobaSeparatedCardinality
import MyLeanRepo.Kakeya.Assouad.WZ1.CordobaAssemblyHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.CrossPerturbation
import MyLeanRepo.Kakeya.Assouad.WZ1.PairwiseIntersection
import MyLeanRepo.Kakeya.Assouad.WZ1.SlabContainment
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma17CordobaSlabLower

set_option maxHeartbeats 0
set_option maxRecDepth 1000

/-!
# Córdoba L² slab lower bound WITHOUT plane map incidence

Variant of `pureWz2_cordoba_slab_lower_with_hypotheses` that does NOT require a
Lipschitz plane map with incidence bound.

When `tau = O(L)` (specifically `tau ≤ 20 * L`), slab containment follows by
Cauchy-Schwarz alone: for any `x` in the selected sets, `dist(x, p_mid) ≤ 2 * tau`,
so `|inner(x - p_mid, n)| ≤ 2 * tau ≤ 40 * L` for ANY unit vector `n`.

This bypasses the weak planiness / absorption requirement entirely.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/--
Córdoba L² slab lower bound WITHOUT plane map or incidence hypothesis.

Requires only an arbitrary unit direction `n` and `tau ≤ 20 * L`.
All other hypotheses are the same as the incidence-based version.
-/
theorem pureWz2_cordoba_slab_lower_no_incidence
    {sigma L tau : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (epsilon₁ epsilon₃ : ℝ)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := coarseShading)
      (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃) (tau := tau))
    (n : Point3)
    (hn_unit : ‖n‖ = 1)
    (htau_le_20L : tau ≤ 20 * L)
    (h_propertyThree_full :
        ∀ (j : Fin coarse.card) (p : Point3),
          p ∈ propP.propertyThree.carrier j →
            Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
              volume (propP.propertyThree.carrier j ∩ Metric.closedBall p tau))
    (h_log_absorption : ∀ (k : ℕ), 0 < k →
        (k : ℝ) ≤ 100 / L^3 →
          Real.rpow L epsilon₁ *
            (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (h_ax_condition : 4 * (6 * L)^2 ≤ (3 / 4 : ℝ) * (Real.rpow L (1 - epsilon₃))^2)
    (hL_pos : 0 < L) (hL_small : L ≤ 1 / 1000)
    (htau_pos : 0 < tau) (hL_le_tau : L ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * L) (htau_le_one : tau ≤ 1)
    (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (heps₁_pos : 0 < epsilon₁) (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (q : Point3) (hq : q ∈ propP.propertyThree.union)
    (t : ℝ)
    (ht : t ∈ scalarProjection n
            (propP.propertyThree.union ∩ Metric.closedBall q tau)) :
    volume (coarseShading.union ∩ Metric.closedBall q (3 * tau) ∩
        {x | |inner ℝ x n - t| ≤ 40 * L}) ≥
      Kakeya.realRpowENN L (1 + 7 * epsilon₁ + epsilon₃) *
        ENNReal.ofReal (tau ^ 2 / 200) := by
  -- Step 1: Extract p_mid realizing t from scalar projection
  have hq' : q ∈ propP.propertyThree.union := hq
  rcases ht with ⟨p_mid, hpmid_in, h_eq_t⟩
  have hpmid_union : p_mid ∈ propP.propertyThree.union := hpmid_in.1
  have hpmid_ball : dist p_mid q ≤ tau := hpmid_in.2
  rcases hpmid_union with ⟨i_ref, hp_mid_prop3⟩
  have hpmid_union' : p_mid ∈ propP.propertyThree.union := ⟨i_ref, hp_mid_prop3⟩
  let T_ref : Kakeya.DeltaTube L := coarse.tube i_ref
  have hu_ax_unit : ‖T_ref.direction‖ = 1 := T_ref.direction_unit
  let u_ax : Point3 := T_ref.direction

  -- Step 2: Convert reference paper tube to DeltaTube(6L)
  rcases paper_tube_piece_in_delta_tube hL_pos hL_small htau_pos htau_sq T_ref p_mid
      (propP.propertyThree.subset_body i_ref hp_mid_prop3) with
    ⟨T_ref6, hT_ref6_dir, hT_ref6_contain⟩

  -- Step 3: Extract separated points from propertyThree around p_mid
  let sep_scale : ℝ := Real.rpow L (1 - epsilon₃)
  have hsep_pos : 0 < sep_scale := Real.rpow_pos_of_pos hL_pos _
  let S_ref : Set Point3 := propP.propertyThree.carrier i_ref ∩ Metric.closedBall p_mid tau
  have hS_ref_meas : MeasurableSet S_ref :=
    (propP.propertyThree.measurable_carrier i_ref).inter
      Metric.isClosed_closedBall.measurableSet
  have hS_ref_sub : S_ref ⊆ T_ref6.carrier ∩ Metric.closedBall p_mid tau := by
    intro x hx
    have h1 : x ∈ propP.propertyThree.carrier i_ref := hx.1
    have h2 : x ∈ wz1PaperTubeCarrier T_ref :=
      propP.propertyThree.subset_body i_ref h1
    have h3 : x ∈ T_ref6.carrier := hT_ref6_contain ⟨h2, hx.2⟩
    exact ⟨h3, hx.2⟩
  let V : ℝ := Real.rpow L (2 + 2 * epsilon₁) * tau
  have hV_pos : 0 < V := mul_pos (Real.rpow_pos_of_pos hL_pos _) htau_pos
  have h_vol_S_ref : volume S_ref ≥ ENNReal.ofReal V := by
    have h := h_propertyThree_full i_ref p_mid hp_mid_prop3
    have h_eq : Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau =
        ENNReal.ofReal V := by
      unfold Kakeya.realRpowENN
      have h1 : 0 ≤ Real.rpow L (2 + 2 * epsilon₁) := Real.rpow_nonneg hL_pos.le _
      rw [ENNReal.ofReal_mul h1] <;> rfl
    rw [h_eq] at h
    exact h

  obtain ⟨p, k, hk_lower, hp_in_S, hp_sep⟩ := separated_points_from_tube_volume_slab
      (show 0 < 6 * L by positivity)
      T_ref6 p_mid tau htau_pos S_ref hS_ref_meas hS_ref_sub sep_scale hsep_pos V hV_pos
      h_vol_S_ref

  have hk_pos : 0 < k := by
    have h1 : (k : ℝ) ≥ 5 * V / (24 * (6 * L)^2 * sep_scale) := hk_lower
    have h2 : 0 < 5 * V / (24 * (6 * L)^2 * sep_scale) := by positivity
    have h3 : (k : ℝ) > 0 := by linarith
    exact_mod_cast h3

  -- Step 4: Select transverse tubes at each point
  choose j_m hj1 hj_trans using fun (m : ℕ) (hm : m < k) =>
    propP.transverse (p m) (⟨i_ref, (hp_in_S m hm).1⟩) i_ref (hp_in_S m hm).1

  -- Step 5: Define Córdoba sets (without slab)
  let A : Fin k → Set Point3 := fun i =>
    propP.propertyOne.carrier (j_m i.val i.is_lt) ∩
    Metric.closedBall (p i.val) tau

  have hA_meas : ∀ i, MeasurableSet (A i) := by
    intro i
    let idx := j_m i.val i.is_lt
    have h1 : MeasurableSet (propP.propertyOne.carrier idx) :=
      propP.propertyOne.measurable_carrier idx
    have h2 : MeasurableSet (Metric.closedBall (p i.val) tau) :=
      Metric.isClosed_closedBall.measurableSet
    exact h1.inter h2

  -- Step 6: Volume lower bound via propertyOne_full
  have h_vol_lower : ∀ i, volume (A i) ≥ ENNReal.ofReal V := by
    intro i
    let j_i := j_m i.val i.is_lt
    let p_i := p i.val
    have hj1_i : p_i ∈ propP.propertyOne.carrier j_i := hj1 i.val i.is_lt
    have h := propP.propertyOne_full j_i p_i hj1_i
    have h_eq : Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau =
        ENNReal.ofReal V := by
      unfold Kakeya.realRpowENN
      have h1 : 0 ≤ Real.rpow L (2 + 2 * epsilon₁) := Real.rpow_nonneg hL_pos.le _
      rw [ENNReal.ofReal_mul h1] <;> rfl
    rw [h_eq] at h
    exact h

  -- Step 7: Volume upper bound via DeltaTube(6L)
  have h_vol_upper : ∀ i, volume (A i) ≤ ENNReal.ofReal (288 * L^2 * tau) := by
    intro i
    let j_i := j_m i.val i.is_lt
    let p_i := p i.val
    have hj1_i : p_i ∈ propP.propertyOne.carrier j_i := hj1 i.val i.is_lt
    have h_paper : p_i ∈ wz1PaperTubeCarrier (coarse.tube j_i) :=
      propP.propertyOne.subset_body j_i hj1_i
    rcases paper_tube_piece_in_delta_tube hL_pos hL_small htau_pos htau_sq
        (coarse.tube j_i) p_i h_paper with
      ⟨T_ji, hT_ji_dir, hT_ji_contain⟩
    have h1 : A i ⊆ T_ji.carrier ∩ Metric.closedBall p_i tau := by
      intro x hx
      have h2 : x ∈ propP.propertyOne.carrier j_i := hx.1
      have h3 : x ∈ wz1PaperTubeCarrier (coarse.tube j_i) :=
        propP.propertyOne.subset_body j_i h2
      have h4 : x ∈ T_ji.carrier := hT_ji_contain ⟨h3, hx.2⟩
      exact ⟨h4, hx.2⟩
    have h5 : volume (A i) ≤ volume (T_ji.carrier ∩ Metric.closedBall p_i tau) :=
      measure_mono h1
    have h6 : volume (T_ji.carrier ∩ Metric.closedBall p_i tau) ≤
        ENNReal.ofReal (8 * (6 * L)^2 * tau) :=
      tube_ball_intersection_volume_simple (hδ := by positivity) (hR := htau_pos.le) T_ji p_i
    have h7 : 8 * (6 * L)^2 * tau = 288 * L^2 * tau := by ring
    rw [h7] at h6
    exact h5.trans h6

  -- Step 8: Slab containment via Cauchy-Schwarz (NO incidence needed)
  -- For any x ∈ A_i: dist(x, p_i) ≤ tau and dist(p_i, p_mid) ≤ tau,
  -- so dist(x, p_mid) ≤ 2*tau ≤ 40*L by htau_le_20L.
  -- Then |inner(x - p_mid, n)| ≤ ‖x - p_mid‖ * ‖n‖ ≤ 2*tau ≤ 40*L.
  have h_slab_contain : ∀ i, A i ⊆ {x : Point3 | |inner ℝ x n - t| ≤ 40 * L} := by
    intro i x hx
    have hx1 : x ∈ propP.propertyOne.carrier (j_m i.val i.is_lt) := hx.1
    have hx2 : dist x (p i.val) ≤ tau := hx.2
    have hpi_ball : dist (p i.val) p_mid ≤ tau := (hp_in_S i.val i.is_lt).2
    have hdist : dist x p_mid ≤ 2 * tau := by
      calc dist x p_mid
        ≤ dist x (p i.val) + dist (p i.val) p_mid := dist_triangle _ _ _
      _ ≤ tau + tau := by gcongr
      _ = 2 * tau := by ring
    have h_main : |inner ℝ (x - p_mid) n| ≤ 2 * tau := by
      have h1 : |inner ℝ (x - p_mid) n| ≤ ‖x - p_mid‖ * ‖n‖ :=
        abs_real_inner_le_norm _ _
      rw [hn_unit] at h1
      have h2 : ‖x - p_mid‖ = dist x p_mid := by simp [dist_eq_norm]
      rw [h2] at h1
      linarith
    have h3 : 2 * tau ≤ 40 * L := by
      have h4 : tau ≤ 20 * L := htau_le_20L
      linarith
    have h4 : |inner ℝ (x - p_mid) n| ≤ 40 * L := by linarith
    have h5 : inner ℝ (x - p_mid) n = inner ℝ x n - t := by
      have h6 : inner ℝ (x - p_mid) n = inner ℝ x n - inner ℝ p_mid n := by
        exact inner_sub_left x p_mid n
      have h7 : inner ℝ p_mid n = t := by simpa using h_eq_t
      rw [h6, h7]
    rw [h5] at h4
    exact h4

  -- Step 9: Sort points by axial projection along u_ax
  let s : Fin k → ℝ := fun i => inner ℝ (p i.val) u_ax
  have h_s_inj : Function.Injective s := by
    intro i j h
    by_contra hne
    have hne' : i.val ≠ j.val := by intro h; exact hne (Fin.ext h)
    have h_sep_points : dist (p i.val) (p j.val) ≥ sep_scale :=
      hp_sep i.val j.val i.is_lt j.is_lt hne'
    have hpi_Tref6 : p i.val ∈ T_ref6.carrier := hT_ref6_contain ⟨
      propP.propertyThree.subset_body i_ref (hp_in_S i.val i.is_lt).1,
      (hp_in_S i.val i.is_lt).2⟩
    have hpj_Tref6 : p j.val ∈ T_ref6.carrier := hT_ref6_contain ⟨
      propP.propertyThree.subset_body i_ref (hp_in_S j.val j.is_lt).1,
      (hp_in_S j.val j.is_lt).2⟩
    have h_ax : |inner ℝ (p j.val - p i.val) u_ax| ≥ sep_scale / 2 :=
      axial_separation_two_points (by positivity) hsep_pos u_ax hu_ax_unit
        T_ref6 hT_ref6_dir (p i.val) (p j.val) hpi_Tref6 hpj_Tref6 h_sep_points h_ax_condition
    have h_sub : inner ℝ (p j.val - p i.val) u_ax = inner ℝ (p j.val) u_ax - inner ℝ (p i.val) u_ax := by
      rw [inner_sub_left]
    have h_eq : inner ℝ (p j.val - p i.val) u_ax = 0 := by
      rw [h_sub]
      have h9 : inner ℝ (p i.val) u_ax = inner ℝ (p j.val) u_ax := h
      linarith
    rw [h_eq] at h_ax
    have h_pos : 0 < sep_scale / 2 := by linarith
    linarith
  let S_finset : Finset ℝ := Finset.image s Finset.univ
  have hS_card : S_finset.card = k := by
    rw [Finset.card_image_of_injective _ h_s_inj] <;> simp
  let e_ord : Fin k ≃o S_finset := Finset.orderIsoOfFin S_finset hS_card
  let sorted_idx_fin (i : Fin k) : Fin k :=
    Classical.choose (Finset.mem_image.mp (e_ord i).2)
  have h_choice_spec : ∀ (i : Fin k),
      sorted_idx_fin i ∈ Finset.univ ∧ s (sorted_idx_fin i) = (e_ord i : ℝ) := by
    intro i
    exact Classical.choose_spec (Finset.mem_image.mp (e_ord i).2)
  let sorted_idx (i : Fin k) : ℕ := (sorted_idx_fin i).val
  have hsorted_idx_lt : ∀ (i : Fin k), sorted_idx i < k := by
    intro i; exact (sorted_idx_fin i).is_lt
  have h_s_spec : ∀ (i : Fin k), s ⟨sorted_idx i, hsorted_idx_lt i⟩ = (e_ord i : ℝ) := by
    intro i
    have h_eq : ⟨sorted_idx i, hsorted_idx_lt i⟩ = sorted_idx_fin i := by apply Fin.ext; rfl
    rw [h_eq]; exact (h_choice_spec i).2
  let q_sorted (i : Fin k) : Point3 := p (sorted_idx i)
  have h_sorted_axially : ∀ (i j : Fin k), i ≤ j →
      inner ℝ (q_sorted i) u_ax ≤ inner ℝ (q_sorted j) u_ax := by
    intro i j hij
    have h1 : (e_ord i : ℝ) ≤ (e_ord j : ℝ) := e_ord.monotone hij
    have h2 : inner ℝ (q_sorted i) u_ax = (e_ord i : ℝ) := by simpa [q_sorted, s] using h_s_spec i
    have h3 : inner ℝ (q_sorted j) u_ax = (e_ord j : ℝ) := by simpa [q_sorted, s] using h_s_spec j
    linarith

  -- Consecutive axial gap ≥ sep_scale / 2
  have h_consec_gap : ∀ (a : Fin k), (h : a.val + 1 < k) →
      inner ℝ (q_sorted ⟨a.val + 1, h⟩ - q_sorted a) u_ax ≥ sep_scale / 2 := by
    intro a h
    let i : Fin k := a
    let j : Fin k := ⟨a.val + 1, h⟩
    have hne : i ≠ j := by
      intro h_eq
      have h9 : i.val = j.val := congr_arg Fin.val h_eq
      simp [j] at h9 <;> omega
    have h_idx_ne : sorted_idx i ≠ sorted_idx j := by
      intro h10
      have h10' : sorted_idx_fin i = sorted_idx_fin j := by
        apply Fin.ext
        exact h10
      have h11 : s (sorted_idx_fin i) = s (sorted_idx_fin j) := by rw [h10']
      have h12 : (e_ord i : ℝ) = (e_ord j : ℝ) := by
        calc (e_ord i : ℝ)
          = s (sorted_idx_fin i) := (h_choice_spec i).2.symm
        _ = s (sorted_idx_fin j) := h11
        _ = (e_ord j : ℝ) := (h_choice_spec j).2
      have h13 : i = j := e_ord.injective (Subtype.ext h12)
      exact hne h13
    have h_sep_points : dist (q_sorted i) (q_sorted j) ≥ sep_scale :=
      hp_sep (sorted_idx i) (sorted_idx j) (hsorted_idx_lt i) (hsorted_idx_lt j) h_idx_ne
    have hpi_Tref6 : q_sorted i ∈ T_ref6.carrier := hT_ref6_contain ⟨
      propP.propertyThree.subset_body i_ref (hp_in_S (sorted_idx i) (hsorted_idx_lt i)).1,
      (hp_in_S (sorted_idx i) (hsorted_idx_lt i)).2⟩
    have hpj_Tref6 : q_sorted j ∈ T_ref6.carrier := hT_ref6_contain ⟨
      propP.propertyThree.subset_body i_ref (hp_in_S (sorted_idx j) (hsorted_idx_lt j)).1,
      (hp_in_S (sorted_idx j) (hsorted_idx_lt j)).2⟩
    have h_nonneg : 0 ≤ inner ℝ (q_sorted j - q_sorted i) u_ax := by
      have h_ij : i ≤ j := by
        have h : i.val ≤ j.val := by
          simp [i, j] <;> omega
        exact_mod_cast h
      have h : inner ℝ (q_sorted i) u_ax ≤ inner ℝ (q_sorted j) u_ax :=
        h_sorted_axially i j h_ij
      have h2 : inner ℝ (q_sorted j - q_sorted i) u_ax =
          inner ℝ (q_sorted j) u_ax - inner ℝ (q_sorted i) u_ax := by
        rw [inner_sub_left]
      rw [h2]
      linarith
    have h_ax_abs : |inner ℝ (q_sorted j - q_sorted i) u_ax| ≥ sep_scale / 2 :=
      axial_separation_two_points (by positivity) hsep_pos u_ax hu_ax_unit
        T_ref6 hT_ref6_dir (q_sorted i) (q_sorted j) hpi_Tref6 hpj_Tref6 h_sep_points h_ax_condition
    have h_ax_pos : |inner ℝ (q_sorted j - q_sorted i) u_ax| =
        inner ℝ (q_sorted j - q_sorted i) u_ax := by
      rw [abs_of_nonneg h_nonneg]
    rw [h_ax_pos] at h_ax_abs
    exact h_ax_abs

  -- Total axial gap for i < j
  have h_axial_gap : ∀ (i j : Fin k), i.val < j.val →
      inner ℝ (q_sorted j - q_sorted i) u_ax ≥
        ((j.val : ℝ) - (i.val : ℝ)) * sep_scale / 2 := by
    intro i j hij
    let make_fin : ∀ (n : ℕ), i.val + n ≤ j.val → Fin k :=
      fun n hn => ⟨i.val + n, Nat.lt_of_le_of_lt hn j.is_lt⟩
    have h_main : ∀ (n : ℕ) (hn : i.val + n ≤ j.val),
        inner ℝ (q_sorted (make_fin n hn) - q_sorted i) u_ax ≥
          (n : ℝ) * sep_scale / 2 := by
      intro n hn
      induction n with
      | zero =>
        simp [make_fin]
      | succ n ih =>
        have h_n1_lt_k : i.val + n + 1 < k := by linarith [hn, j.is_lt]
        have h_n_lt_k : i.val + n < k := by linarith
        let a : Fin k := ⟨i.val + n, h_n_lt_k⟩
        let b : Fin k := ⟨i.val + n + 1, h_n1_lt_k⟩
        have h_ih' := ih (by linarith)
        have h_gap : inner ℝ (q_sorted b - q_sorted a) u_ax ≥ sep_scale / 2 :=
          h_consec_gap a h_n1_lt_k
        have h_sum : inner ℝ (q_sorted b - q_sorted i) u_ax =
            inner ℝ (q_sorted b - q_sorted a) u_ax +
            inner ℝ (q_sorted a - q_sorted i) u_ax := by
          have h_eq : q_sorted b - q_sorted i = (q_sorted b - q_sorted a) + (q_sorted a - q_sorted i) := by abel
          rw [h_eq, inner_add_left]
        rw [h_sum]
        have h5 : (n.succ : ℝ) * sep_scale / 2 =
            (n : ℝ) * sep_scale / 2 + sep_scale / 2 := by
          simp [Nat.cast_add, Nat.cast_one] <;> ring
        rw [h5]
        linarith
    have h_ile : i.val ≤ j.val := le_of_lt hij
    have h_add : i.val + (j.val - i.val) = j.val := Nat.add_sub_of_le h_ile
    have h_arg : i.val + (j.val - i.val) ≤ j.val := by rw [h_add]
    have h1 := h_main (j.val - i.val) h_arg
    have h2 : make_fin (j.val - i.val) h_arg = j := by
      apply Fin.ext
      have h4 : (make_fin (j.val - i.val) h_arg).val = j.val := by
        simp [make_fin, h_add]
      exact h4
    have h3 : ((j.val - i.val : ℕ) : ℝ) = (j.val : ℝ) - (i.val : ℝ) := by
      rw [Nat.cast_sub h_ile] <;> simp
    rw [h2, h3] at h1
    exact h1

  -- Transverse separation bound
  have h_trans_sep : ∀ (i j : Fin k),
      ‖q_sorted j - q_sorted i - (inner ℝ (q_sorted j - q_sorted i) u_ax) • u_ax‖ ≤ 2 * (6 * L) := by
    intro i j
    exact tube_two_point_perp_bound (by positivity) T_ref6 u_ax hu_ax_unit hT_ref6_dir
      (q_sorted i) (q_sorted j)
      (hT_ref6_contain ⟨propP.propertyThree.subset_body i_ref
        (hp_in_S (sorted_idx i) (hsorted_idx_lt i)).1,
        (hp_in_S (sorted_idx i) (hsorted_idx_lt i)).2⟩)
      (hT_ref6_contain ⟨propP.propertyThree.subset_body i_ref
        (hp_in_S (sorted_idx j) (hsorted_idx_lt j)).1,
        (hp_in_S (sorted_idx j) (hsorted_idx_lt j)).2⟩)

  -- Step 10: Pairwise intersection bound
  let C_int : ℝ := 28224 * L^2 * tau
  have hC_int_pos : 0 < C_int := by positivity
  have h_1536_tau_le_98 : 1536 * tau ≤ 98 := by
    have h1 : (1536 * tau) ^ 2 ≤ 98 ^ 2 := by
      have h2 : tau ^ 2 ≤ 4 * L := htau_sq
      have h3 : L ≤ 1 / 1000 := hL_small
      nlinarith
    have h4 : 0 ≤ 1536 * tau := by positivity
    nlinarith
  have h_pairwise : ∀ (i j : Fin k), i ≠ j →
      volume (A (sorted_idx_fin i) ∩ A (sorted_idx_fin j)) ≤
        ENNReal.ofReal (C_int / |(i : ℝ) - (j : ℝ)|) :=
    fun i j hne =>
      pairwise_intersection_bound_paper
        propP.toCordoba
        hL_pos hL_small htau_pos htau_sq heps₁_pos heps₃_pos heps_sum h_log_absorption
        sep_scale (by rfl) u_ax hu_ax_unit p j_m hj1 hj_trans
        h_vol_upper sorted_idx_fin
        h_trans_sep h_axial_gap C_int (by rfl) h_1536_tau_le_98 i j hne

  -- Step 11: Apply finite Córdoba L²
  have h_cordoba : volume (⋃ i, A (sorted_idx_fin i)) ≥
      ENNReal.ofReal ((k : ℝ)^2 * V^2) /
      ENNReal.ofReal ((k : ℝ) * (288 * L^2 * tau) +
        2 * C_int * (k : ℝ) * (1 + Real.log (k : ℝ))) :=
    finite_cordoba_l2 hk_pos (fun i => A (sorted_idx_fin i))
      (fun i => hA_meas (sorted_idx_fin i)) V (288 * L^2 * tau) C_int
      hV_pos (by positivity) (by positivity) (fun i => h_vol_lower (sorted_idx_fin i))
      (fun i => h_vol_upper (sorted_idx_fin i)) h_pairwise

  -- Step 12: Log absorption and arithmetic
  have hk_upper : (k : ℝ) ≤ 100 / L^3 :=
    cordoba_cardinality_bound_paper
      hL_pos hL_small heps₁_pos heps₃_pos heps_sum htau_le_one sep_scale (by rfl) p p_mid
      (fun m hm => ⟨trivial, (hp_in_S m hm).2⟩)
      (fun m n hm hn hne => hp_sep m n hm hn hne)
  have h_log_main : Real.rpow L epsilon₁ *
      (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108 :=
    h_log_absorption k hk_pos hk_upper
  have hk_lower' : (k : ℝ) ≥
      (5 : ℝ) / 864 * Real.rpow L (2 * epsilon₁ - 1 + epsilon₃) * tau := by
    let a : ℝ := 2 * epsilon₁ - 1 + epsilon₃
    let b : ℝ := 2
    let c : ℝ := 1 - epsilon₃
    let X := Real.rpow L a
    let Y := Real.rpow L b
    let Z := Real.rpow L c
    have hY_pos : 0 < Y := Real.rpow_pos_of_pos hL_pos b
    have hZ_pos : 0 < Z := Real.rpow_pos_of_pos hL_pos c
    have h_sum : a + b + c = 2 + 2 * epsilon₁ := by ring
    have h_rpow : Real.rpow L (2 + 2 * epsilon₁) = X * Y * Z := by
      have h3 : Real.rpow L (a + b + c) = Real.rpow L (a + b) * Real.rpow L c :=
        Real.rpow_add hL_pos (a + b) c
      have h4 : Real.rpow L (a + b) = Real.rpow L a * Real.rpow L b :=
        Real.rpow_add hL_pos a b
      have h5 : Real.rpow L (2 + 2 * epsilon₁) = Real.rpow L (a + b + c) := by
        rw [←h_sum]
      have h6 : Real.rpow L (a + b + c) = (Real.rpow L a * Real.rpow L b) * Real.rpow L c := by
        rw [h3, h4] <;> ring
      rw [h5, h6] <;> rfl
    have h_denom : (24 * (6 * L)^2 * sep_scale) = 864 * Y * Z := by
      have h1 : (6 * L)^2 = 36 * L^2 := by ring
      have hL2 : L^2 = Real.rpow L 2 := by simp
      have hsep : sep_scale = Real.rpow L (1 - epsilon₃) := by rfl
      have hY : Y = Real.rpow L 2 := by rfl
      have hZ : Z = Real.rpow L (1 - epsilon₃) := by rfl
      rw [h1, hL2, hsep, hY, hZ] <;> ring
    have h_expand : 5 * V / (24 * (6 * L)^2 * sep_scale) = (5 : ℝ) / 864 * X * tau := by
      dsimp only [V]
      have h9 : (864 * Y * Z : ℝ) ≠ 0 := by positivity
      have h_cancel : (5 * ((X * Y * Z) * tau)) / (864 * Y * Z) = (5 : ℝ) / 864 * X * tau := by
        rw [div_eq_iff h9] <;> ring
      have h_num : 5 * (Real.rpow L (2 + 2 * epsilon₁) * tau) = 5 * ((X * Y * Z) * tau) := by
        rw [h_rpow] <;> ring
      rw [h_num, h_denom]
      exact h_cancel
    have h : (k : ℝ) ≥ 5 * V / (24 * (6 * L)^2 * sep_scale) := hk_lower
    rw [h_expand] at h
    exact h
  have hL_one : L ≤ 1 := by linarith [hL_small]
  have h_arithmetic := cordoba_final_arithmetic_paper
    hL_pos hL_one htau_pos heps₁_pos heps₃_pos hk_pos hk_lower' h_log_main

  -- Step 13: Union containment
  have h_union_sub : (⋃ i, A (sorted_idx_fin i)) ⊆
      coarseShading.union ∩ Metric.closedBall q (3 * tau) ∩
        {x | |inner ℝ x n - t| ≤ 40 * L} := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    have h1 : x ∈ coarseShading.union := by
      let j_i := j_m (sorted_idx i) (hsorted_idx_lt i)
      have h2 : x ∈ propP.propertyOne.carrier j_i := hxi.1
      have h2' : x ∈ coarseShading.carrier j_i := propP.propertyOne_sub j_i h2
      exact ⟨j_i, h2'⟩
    have h2 : dist x q ≤ 3 * tau := by
      let p_i := p (sorted_idx i)
      have h3 : dist x p_i ≤ tau := hxi.2
      have h41 : p (sorted_idx i) ∈ S_ref := hp_in_S (sorted_idx i) (hsorted_idx_lt i)
      have h42 : p (sorted_idx i) ∈ T_ref6.carrier ∩ Metric.closedBall p_mid tau := hS_ref_sub h41
      have h4 : dist p_i p_mid ≤ tau := h42.2
      have h5 : dist p_mid q ≤ tau := hpmid_ball
      have h6 : dist x q ≤ dist x p_i + dist p_i q := dist_triangle _ _ _
      have h7 : dist p_i q ≤ dist p_i p_mid + dist p_mid q := dist_triangle _ _ _
      have h8 : dist x q ≤ dist x p_i + dist p_i p_mid + dist p_mid q := by
        calc dist x q
          ≤ dist x p_i + dist p_i q := h6
        _ ≤ dist x p_i + (dist p_i p_mid + dist p_mid q) := by gcongr
        _ = dist x p_i + dist p_i p_mid + dist p_mid q := by ring
      linarith
    have h3 : x ∈ {x : Point3 | |inner ℝ x n - t| ≤ 40 * L} := h_slab_contain (sorted_idx_fin i) hxi
    have h12 : x ∈ coarseShading.union ∩ Metric.closedBall q (3 * tau) := Set.mem_inter h1 h2
    exact Set.mem_inter h12 h3

  calc
    volume (coarseShading.union ∩ Metric.closedBall q (3 * tau) ∩
        {x | |inner ℝ x n - t| ≤ 40 * L})
      ≥ volume (⋃ i, A (sorted_idx_fin i)) := measure_mono h_union_sub
    _ ≥ _ := h_cordoba
    _ ≥ _ := h_arithmetic

/--
Variant of `pureWz2_cordoba_slab_lower_no_incidence` that does NOT require
`q ∈ propP.propertyThree.union`.

The original theorem's proof never uses the `hq` hypothesis; the ball
containment goes through `p_mid` (realizing `t` from the projection).
This variant extracts `p_mid` from `ht`, applies the original theorem
centered at `p_mid`, and weakens the ball from `3*tau` to `4*tau` around
the original `q` via the triangle inequality.

Use this when `q` is an arbitrary point (e.g. from a local AD query) and
you only know that `propertyThree.union` intersects `ball(q, tau)`.
-/
theorem pureWz2_cordoba_slab_lower_no_incidence_no_q
    {sigma L tau : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (epsilon₁ epsilon₃ : ℝ)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := coarseShading)
      (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃) (tau := tau))
    (n : Point3)
    (hn_unit : ‖n‖ = 1)
    (htau_le_20L : tau ≤ 20 * L)
    (h_propertyThree_full :
        ∀ (j : Fin coarse.card) (p : Point3),
          p ∈ propP.propertyThree.carrier j →
            Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
              volume (propP.propertyThree.carrier j ∩ Metric.closedBall p tau))
    (h_log_absorption : ∀ (k : ℕ), 0 < k →
        (k : ℝ) ≤ 100 / L^3 →
          Real.rpow L epsilon₁ *
            (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (h_ax_condition : 4 * (6 * L)^2 ≤ (3 / 4 : ℝ) * (Real.rpow L (1 - epsilon₃))^2)
    (hL_pos : 0 < L) (hL_small : L ≤ 1 / 1000)
    (htau_pos : 0 < tau) (hL_le_tau : L ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * L) (htau_le_one : tau ≤ 1)
    (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (heps₁_pos : 0 < epsilon₁) (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (q : Point3)
    (t : ℝ)
    (ht : t ∈ scalarProjection n
            (propP.propertyThree.union ∩ Metric.closedBall q tau)) :
    volume (coarseShading.union ∩ Metric.closedBall q (4 * tau) ∩
        {x | |inner ℝ x n - t| ≤ 40 * L}) ≥
      Kakeya.realRpowENN L (1 + 7 * epsilon₁ + epsilon₃) *
        ENNReal.ofReal (tau ^ 2 / 200) := by
  rcases ht with ⟨p_mid, hpmid_in, h_eq_t⟩
  have hpmid_union : p_mid ∈ propP.propertyThree.union := hpmid_in.1
  have hpmid_ball : dist p_mid q ≤ tau := hpmid_in.2
  have h_t_pmid : t ∈ scalarProjection n
      (propP.propertyThree.union ∩ Metric.closedBall p_mid tau) := by
    refine ⟨p_mid, ⟨hpmid_union, ?_⟩, h_eq_t⟩
    simpa using dist_nonneg.trans hpmid_ball
  have h_main := pureWz2_cordoba_slab_lower_no_incidence
    epsilon₁ epsilon₃ propP n hn_unit htau_le_20L
    h_propertyThree_full h_log_absorption h_ax_condition
    hL_pos hL_small htau_pos hL_le_tau htau_sq htau_le_one
    hsigma_pos hsigma_lt_one heps₁_pos heps₃_pos heps_sum
    p_mid hpmid_union t h_t_pmid
  have h_sub : (coarseShading.union ∩ Metric.closedBall p_mid (3 * tau) ∩
      {x : Point3 | |inner ℝ x n - t| ≤ 40 * L}) ⊆
    (coarseShading.union ∩ Metric.closedBall q (4 * tau) ∩
      {x : Point3 | |inner ℝ x n - t| ≤ 40 * L}) := by
    intro x hx
    have h1 : x ∈ coarseShading.union := hx.1.1
    have h2 : dist x p_mid ≤ 3 * tau := hx.1.2
    have h3 : dist x q ≤ dist x p_mid + dist p_mid q := dist_triangle _ _ _
    have h4 : dist x q ≤ 4 * tau := by linarith
    have h5 : |inner ℝ x n - t| ≤ 40 * L := hx.2
    exact ⟨⟨h1, h4⟩, h5⟩
  exact le_trans h_main (measure_mono h_sub)

end Kakeya.Assouad

end
