module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.SSet
public import MyLeanRepo.InductionOnScales.SlopeCells
public import MyLeanRepo.InductionOnScales.RetentionSelection
public import MyLeanRepo.InductionOnScales.UniformizeFamiliesPerSquareGeneralized
public import MyLeanRepo.InductionOnScales.PointSelection
public import MyLeanRepo.InductionOnScales.FinePhaseAssembly
public import MyLeanRepo.InductionOnScales.Homothety
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Per-Q Steps 8-9: Point Selection + Uniformization

Composes `select_points_by_retention` (Step 8) with
`uniformize_families_per_square_generalized` (Step 9) for a single coarse square Q.

Given retained tube families `candRet` for points in P_Q with a global average
retention bound, select a subset P_Q' with uniform retention and uniformize
slope-cell packets across all selected points.

## Total loss factor
- Step 8: K_ret = 2 * K_cpd
- Step 9: K_loss = 16 * (numDyadicLevels M)^2
- Combined: K_total = K_ret * K_loss
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales

/-- Per-Q Steps 8-9: point selection followed by slope-cell uniformization.

Given `candRet` families for points in `P_Q` with global average retention
≥ M * |P_Q| / K_cpd, produces `P_Q' ⊆ P_Q` and `uniformFamily` with:
- Uniform retention: M ≤ K_total * |uniformFamily p hp|
- Point coverage: |P_Q| ≤ K_total * |P_Q'|
- Uniform slope-cell packets of size m_Q and cell count MQ
- SSet constant K_loss * C_ret
where K_total = K_ret * K_loss, K_ret = 2 * K_cpd,
K_loss = 16 * (numDyadicLevels M)^2.
-/
lemma per_q_steps_8_9
    {n m : ℕ} (hnm : m ≤ n)
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (M : ℕ) (hM : 0 < M)
    (config : NiceConfiguration n s C₁ M)
    (Q : DyadicSquare m)
    (P_Q : Finset (DyadicSquare n))
    (hP_Q_nonempty : P_Q.Nonempty)
    (candRet : DyadicSquare n → Finset (DyadicTube n))
    (C_ret : ℝ) (hC_ret : 1 ≤ C_ret)
    (K_cpd : ℝ) (hK_cpd : 1 ≤ K_cpd)
    (h_candRet_sset : ∀ p ∈ P_Q, IsFiniteTubeSSet s C_ret (candRet p))
    (h_candRet_incidence : ∀ p ∈ P_Q, ∀ T ∈ candRet p,
        (T.toSet ∩ p.toSet).Nonempty)
    (h_candRet_params : ∀ p ∈ P_Q, ∀ T ∈ candRet p,
        T.IsInAllowedParameterStrip)
    (h_ret_upper : ∀ p ∈ P_Q, (candRet p).card ≤ M)
    (h_retention_sum : (∑ p ∈ P_Q, (candRet p).card : ℝ) ≥
        (P_Q.card : ℝ) * (M : ℝ) / K_cpd) :
    ∃ (P_Q' : Finset (DyadicSquare n))
      (hP_Q'_sub : P_Q' ⊆ P_Q)
      (hP_Q'_nonempty : P_Q'.Nonempty)
      (uniformFamily : (p : DyadicSquare n) → p ∈ P_Q' → Finset (DyadicTube n))
      (m_Q MQ : ℕ) (hmQ_pos : 0 < m_Q) (hMQ_pos : 0 < MQ)
      (K_ret K_loss : ℝ) (hK_ret : 1 ≤ K_ret) (hK_loss : 1 ≤ K_loss)
      (hK_loss_eq : K_loss = 16 * (numDyadicLevels M : ℝ)^2),
      (∀ p hp, uniformFamily p hp ⊆ candRet p) ∧
      (∀ p hp, (M : ℝ) ≤ K_ret * K_loss * ((uniformFamily p hp).card : ℝ)) ∧
      ((P_Q.card : ℝ) ≤ K_ret * K_loss * (P_Q'.card : ℝ)) ∧
      (∀ p hp, IsFiniteTubeSSet s (K_loss * C_ret) (uniformFamily p hp)) ∧
      (∀ p hp (a : ℤ), ((uniformFamily p hp).filter
          (fun T => localSlopeCellIndex m T.a = a)).card =
        if a ∈ (uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a)
        then m_Q else 0) ∧
      (∀ p hp, ((uniformFamily p hp).image
          (fun T => localSlopeCellIndex m T.a)).card = MQ) ∧
      (∀ p hp T, T ∈ uniformFamily p hp → (T.toSet ∩ p.toSet).Nonempty) ∧
      (∀ p hp T, T ∈ uniformFamily p hp → T.IsInAllowedParameterStrip) := by
  -- Step 8: Point selection by retention
  have h_ret_upper' : ∀ p ∈ P_Q, (candRet p).card ≤ M := h_ret_upper

  rcases select_points_by_retention hnm P_Q candRet M hM K_cpd hK_cpd
      hP_Q_nonempty h_ret_upper' h_retention_sum
    with ⟨P_Q1, K_ret, hP_Q1_sub, hK_ret, _, hP_Q1_nonempty, h_size_ret, h_coverage1⟩

  -- Step 9: Uniformize families per square
  let candRet1 (p : DyadicSquare n) (hp : p ∈ P_Q1) : Finset (DyadicTube n) :=
    candRet p

  have h_candRet1_sset : ∀ p hp, IsFiniteTubeSSet s C_ret (candRet1 p hp) := by
    intro p hp
    exact h_candRet_sset p (hP_Q1_sub hp)

  have h_candRet1_size : ∀ p hp, (candRet1 p hp).card ≤ M := by
    intro p hp
    exact h_ret_upper p (hP_Q1_sub hp)

  have h_candRet1_incidence : ∀ p hp T, T ∈ candRet1 p hp →
      (T.toSet ∩ p.toSet).Nonempty := by
    intro p hp T hT
    exact h_candRet_incidence p (hP_Q1_sub hp) T hT

  have h_candRet1_params : ∀ p hp T, T ∈ candRet1 p hp →
      T.IsInAllowedParameterStrip := by
    intro p hp T hT
    exact h_candRet_params p (hP_Q1_sub hp) T hT

  rcases uniformize_families_per_square_generalized hnm s hs hs_one
      C_ret hC_ret M hM Q P_Q1 hP_Q1_nonempty candRet1
      h_candRet1_sset h_candRet1_size h_candRet1_incidence h_candRet1_params
    with ⟨m_Q, hmQ_pos, MQ, hMQ_pos, P_Q', hP_Q'_sub1, hP_Q'_nonempty,
      uniformFamily, K_loss, hK_loss, hK_loss_eq,
      h_uniform_sub, h_tube_retention, h_sset_uniform,
      h_uniform_packets, h_cell_count, h_incidence_uniform, h_params_uniform,
      h_coverage2⟩

  let hP_Q'_sub : P_Q' ⊆ P_Q := Finset.Subset.trans hP_Q'_sub1 hP_Q1_sub

  -- Combined coverage: |P_Q| ≤ K_ret * |P_Q1| ≤ K_ret * K_loss * |P_Q'|
  have h_coverage_total : (P_Q.card : ℝ) ≤ K_ret * K_loss * (P_Q'.card : ℝ) := by
    calc (P_Q.card : ℝ)
      ≤ K_ret * (P_Q1.card : ℝ) := h_coverage1
    _ ≤ K_ret * (K_loss * (P_Q'.card : ℝ)) := by
      gcongr
      <;> exact h_coverage2
    _ = K_ret * K_loss * (P_Q'.card : ℝ) := by ring

  -- Combined retention: M ≤ K_ret * |candRet1 p| ≤ K_ret * K_loss * |uniformFamily p hp|
  have h_retention_total : ∀ p hp, (M : ℝ) ≤ K_ret * K_loss * ((uniformFamily p hp).card : ℝ) := by
    intro p hp
    have h1 : (M : ℝ) ≤ K_ret * ((candRet1 p (hP_Q'_sub1 hp)).card : ℝ) :=
      h_size_ret p (hP_Q'_sub1 hp)
    have h2 : ((candRet1 p (hP_Q'_sub1 hp)).card : ℝ) ≤
        K_loss * ((uniformFamily p hp).card : ℝ) :=
      h_tube_retention p hp
    calc (M : ℝ)
      ≤ K_ret * ((candRet1 p (hP_Q'_sub1 hp)).card : ℝ) := h1
    _ ≤ K_ret * (K_loss * ((uniformFamily p hp).card : ℝ)) := by gcongr
    _ = K_ret * K_loss * ((uniformFamily p hp).card : ℝ) := by ring

  have h_uniform_sub' : ∀ p hp, uniformFamily p hp ⊆ candRet p := by
    intro p hp
    have h1 : uniformFamily p hp ⊆ candRet1 p (hP_Q'_sub1 hp) := h_uniform_sub p hp
    exact h1

  exact ⟨P_Q', hP_Q'_sub, hP_Q'_nonempty, uniformFamily, m_Q, MQ, hmQ_pos, hMQ_pos,
    K_ret, K_loss, hK_ret, hK_loss, hK_loss_eq,
    h_uniform_sub', h_retention_total, h_coverage_total,
    h_sset_uniform, h_uniform_packets, h_cell_count,
    h_incidence_uniform, h_params_uniform⟩

/-- Per-Q Steps 8-10: point selection, uniformization, and fine phase.

Extends `per_q_steps_8_9` with the construction of a local fine configuration
for one coarse square Q using `build_single_fine_config`.

The SSet constant of the fine config is `K_fine * C₁`, where
`K_fine = max 1 ((K_loss * C_ret) * 16^s / C₁)`.
-/
lemma per_q_steps_8_10
    {n m : ℕ} (hnm : m ≤ n)
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (M : ℕ) (hM : 0 < M)
    (config : NiceConfiguration n s C₁ M)
    (Q : DyadicSquare m)
    (P_Q : Finset (DyadicSquare n))
    (hP_Q_nonempty : P_Q.Nonempty)
    (hP_Q_sub : P_Q ⊆ config.points)
    (hP_Q_contained : ∀ p ∈ P_Q, squareContained hnm p Q)
    (candRet : DyadicSquare n → Finset (DyadicTube n))
    (C_ret : ℝ) (hC_ret : 1 ≤ C_ret)
    (K_cpd : ℝ) (hK_cpd : 1 ≤ K_cpd)
    (h_candRet_sset : ∀ p ∈ P_Q, IsFiniteTubeSSet s C_ret (candRet p))
    (h_candRet_incidence : ∀ p ∈ P_Q, ∀ T ∈ candRet p,
        (T.toSet ∩ p.toSet).Nonempty)
    (h_candRet_params : ∀ p ∈ P_Q, ∀ T ∈ candRet p,
        T.IsInAllowedParameterStrip)
    (h_ret_upper : ∀ p ∈ P_Q, (candRet p).card ≤ M)
    (h_retention_sum : (∑ p ∈ P_Q, (candRet p).card : ℝ) ≥
        (P_Q.card : ℝ) * (M : ℝ) / K_cpd) :
    ∃ (P_Q' : Finset (DyadicSquare n))
      (hP_Q'_sub : P_Q' ⊆ P_Q)
      (hP_Q'_nonempty : P_Q'.Nonempty)
      (uniformFamily : (p : DyadicSquare n) → p ∈ P_Q' → Finset (DyadicTube n))
      (m_Q MQ : ℕ) (hmQ_pos : 0 < m_Q) (hMQ_pos : 0 < MQ)
      (K_ret K_loss K_fine : ℝ) (hK_ret : 1 ≤ K_ret) (hK_loss : 1 ≤ K_loss)
      (hK_fine : 1 ≤ K_fine) (hK_loss_eq : K_loss = 16 * (numDyadicLevels M : ℝ)^2),
      (∀ p hp, uniformFamily p hp ⊆ candRet p) ∧
      (∀ p hp, (M : ℝ) ≤ K_ret * K_loss * ((uniformFamily p hp).card : ℝ)) ∧
      ((P_Q.card : ℝ) ≤ K_ret * K_loss * (P_Q'.card : ℝ)) ∧
      (∀ p hp, IsFiniteTubeSSet s (K_loss * C_ret) (uniformFamily p hp)) ∧
      (∀ p hp (a : ℤ), ((uniformFamily p hp).filter
          (fun T => localSlopeCellIndex m T.a = a)).card =
        if a ∈ (uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a)
        then m_Q else 0) ∧
      (∀ p hp, ((uniformFamily p hp).image
          (fun T => localSlopeCellIndex m T.a)).card = MQ) ∧
      (∀ p hp T, T ∈ uniformFamily p hp → (T.toSet ∩ p.toSet).Nonempty) ∧
      (∀ p hp T, T ∈ uniformFamily p hp → T.IsInAllowedParameterStrip) ∧
      -- Step 10 outputs
      (∃ (fineConfig : NiceConfiguration (n - m) s (K_fine * C₁) MQ),
        fineConfig.points = P_Q'.image (squareHomothety hnm Q) ∧
        (∀ p (hp : p ∈ P_Q'),
          ∃ hq : squareHomothety hnm Q p ∈ fineConfig.points,
            (fineConfig.tubeFamily (squareHomothety hnm Q p) hq).image (fun U => U.a) =
              (uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a))) := by
  -- Steps 8-9
  rcases per_q_steps_8_9 hnm s hs hs_one C₁ hC₁ M hM config Q P_Q hP_Q_nonempty
      candRet C_ret hC_ret K_cpd hK_cpd
      h_candRet_sset h_candRet_incidence h_candRet_params
      h_ret_upper h_retention_sum
    with ⟨P_Q', hP_Q'_sub, hP_Q'_nonempty, uniformFamily, m_Q, MQ, hmQ_pos, hMQ_pos,
      K_ret, K_loss, hK_ret, hK_loss, hK_loss_eq,
      h_uniform_sub', h_retention_total, h_coverage_total,
      h_sset_uniform, h_uniform_packets, h_cell_count,
      h_incidence_uniform, h_params_uniform⟩

  have hP_Q'_sub_config : P_Q' ⊆ config.points :=
    Finset.Subset.trans hP_Q'_sub hP_Q_sub
  have hP_Q'_contained : ∀ p ∈ P_Q', squareContained hnm p Q :=
    fun p hp => hP_Q_contained p (hP_Q'_sub hp)

  -- hQ: Q is in the image of containingSquare on P_Q'
  have hQ : Q ∈ P_Q'.image (containingSquare hnm) := by
    rcases hP_Q'_nonempty with ⟨p, hp⟩
    have h_cont : squareContained hnm p Q := hP_Q'_contained p hp
    have h_eq : containingSquare hnm p = Q :=
      squareContained_iff_containingSquare hnm p Q |>.mp h_cont
    exact Finset.mem_image.mpr ⟨p, hp, h_eq⟩

  -- K_fine for the geometric transfer bound
  let C_in : ℝ := K_loss * C_ret
  let K_fine : ℝ := max 1 (C_in * Real.rpow 16 s / C₁)
  have hK_fine : 1 ≤ K_fine := by
    simp [K_fine] <;> linarith
  have hC_in_bound : C_in * Real.rpow 16 s ≤ K_fine * C₁ := by
    have hC₁_pos : 0 < C₁ := by linarith
    have h1 : C_in * Real.rpow 16 s / C₁ ≤ K_fine := by
      simp [K_fine] <;> linarith
    calc C_in * Real.rpow 16 s
      = (C_in * Real.rpow 16 s / C₁) * C₁ := by field_simp [hC₁_pos.ne'] <;> ring
    _ ≤ K_fine * C₁ := by gcongr

  -- Construct G function using construct_fine_tube_family
  have h_G_exists : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q') (hpQ : squareContained hnm p Q),
      ∃ (G : Finset (DyadicTube (n - m))),
        (G.image (fun U => U.a) = (uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a)) ∧
        Set.InjOn (fun U : DyadicTube (n - m) => U.a) G ∧
        IsFiniteTubeSSet s (C_in * Real.rpow 16 s) G ∧
        ∀ U ∈ G, (U.toSet ∩ (squareHomothety hnm Q p).toSet).Nonempty := by
    intro p hp hpQ
    have h_bounded : p.toSet ⊆ unitSquare := config.h_bounded p (hP_Q'_sub_config hp)
    exact FineConfig.construct_fine_tube_family hnm p hs (uniformFamily p hp)
      (h_sset_uniform p hp)
      (h_incidence_uniform p hp)
      h_bounded
      (h_params_uniform p hp)
      m_Q hmQ_pos
      (h_uniform_packets p hp)
      rfl (squareHomothety hnm Q p)

  classical
  choose G_p hG_spec using h_G_exists

  let G (p : DyadicSquare n) (hp : p ∈ P_Q') (hpQ : squareContained hnm p Q) :
      Finset (DyadicTube (n - m)) := G_p p hp hpQ

  have hG_spec' : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q') (hpQ : squareContained hnm p Q),
      (G p hp hpQ).image (fun U => U.a) = (uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a) ∧
      Set.InjOn (fun U : DyadicTube (n - m) => U.a) (G p hp hpQ) ∧
      IsFiniteTubeSSet s (C_in * Real.rpow 16 s) (G p hp hpQ) ∧
      ∀ U ∈ G p hp hpQ, (U.toSet ∩ (squareHomothety hnm Q p).toSet).Nonempty :=
    hG_spec

  have h_cell_count' : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q') (hpQ : squareContained hnm p Q),
      ((uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a)).card = MQ := by
    intro p hp _
    exact h_cell_count p hp

  have h_tube_params' : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q') (T : DyadicTube n),
      T ∈ uniformFamily p hp → T.IsInAllowedParameterStrip := by
    intro p hp T hT
    exact h_params_uniform p hp T hT

  let fineConfig : NiceConfiguration (n - m) s (K_fine * C₁) MQ :=
    build_single_fine_config hnm s hs C₁ K_fine C_in hK_fine hC₁ hC_in_bound
      P_Q' uniformFamily m_Q hmQ_pos MQ Q hQ G hG_spec' h_cell_count' h_tube_params'

  -- fineConfig.points = P_Q'.image (squareHomothety hnm Q)
  -- Since all p ∈ P_Q' are contained in Q, the filter in build_single_fine_config is P_Q' itself
  have h_fine_points : fineConfig.points = P_Q'.image (squareHomothety hnm Q) := by
    have h_filter_eq : P_Q'.filter (fun p => squareContained hnm p Q) = P_Q' := by
      apply Finset.filter_true_of_mem
      intro p hp
      exact hP_Q'_contained p hp
    simp [fineConfig, build_single_fine_config, h_filter_eq]

  -- Slope cell preservation
  have h_slope_cells : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q'),
      ∃ hq : squareHomothety hnm Q p ∈ fineConfig.points,
        (fineConfig.tubeFamily (squareHomothety hnm Q p) hq).image (fun U => U.a) =
          (uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a) := by
    intro p hp
    have hpQ : squareContained hnm p Q := hP_Q'_contained p hp
    have hq : squareHomothety hnm Q p ∈ fineConfig.points := by
      rw [h_fine_points]
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have h_eq : fineConfig.tubeFamily (squareHomothety hnm Q p) hq = G p hp hpQ := by
      simp [fineConfig, build_single_fine_config, fine_local_tube_family_at_point hnm P_Q' Q G p hp hpQ _ hq rfl]
      <;> rfl
    refine ⟨hq, ?_⟩
    rw [h_eq]
    exact (hG_spec' p hp hpQ).1

  exact ⟨P_Q', hP_Q'_sub, hP_Q'_nonempty, uniformFamily, m_Q, MQ, hmQ_pos, hMQ_pos,
    K_ret, K_loss, K_fine, hK_ret, hK_loss, hK_fine, hK_loss_eq,
    h_uniform_sub', h_retention_total, h_coverage_total,
    h_sset_uniform, h_uniform_packets, h_cell_count,
    h_incidence_uniform, h_params_uniform,
    ⟨fineConfig, h_fine_points, h_slope_cells⟩⟩


/-- Per-Q Steps 8-10 with SSet establishment between Steps 8 and 9.

Step 8: Point selection by retention (no SSet required).
Then: Establish SSet(K_ret * C₁) for candRet on selected points.
Step 9: Uniformize slope-cell packets.
Step 10: Build local fine configuration.
-/
lemma per_q_steps_8_10_with_sset
    {n m : ℕ} (hnm : m ≤ n)
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (M : ℕ) (hM : 0 < M)
    (config : NiceConfiguration n s C₁ M)
    (Q : DyadicSquare m)
    (P_Q : Finset (DyadicSquare n))
    (hP_Q_nonempty : P_Q.Nonempty)
    (hP_Q_sub : P_Q ⊆ config.points)
    (hP_Q_contained : ∀ p ∈ P_Q, squareContained hnm p Q)
    (originalFamily : DyadicSquare n → Finset (DyadicTube n))
    (h_orig_sset : ∀ p ∈ P_Q, IsFiniteTubeSSet s C₁ (originalFamily p))
    (h_orig_size : ∀ p ∈ P_Q, (originalFamily p).card = M)
    (candRet : DyadicSquare n → Finset (DyadicTube n))
    (h_candRet_sub : ∀ p ∈ P_Q, candRet p ⊆ originalFamily p)
    (h_candRet_incidence : ∀ p ∈ P_Q, ∀ T ∈ candRet p,
        (T.toSet ∩ p.toSet).Nonempty)
    (h_candRet_params : ∀ p ∈ P_Q, ∀ T ∈ candRet p,
        T.IsInAllowedParameterStrip)
    (K_cpd : ℝ) (hK_cpd : 1 ≤ K_cpd)
    (h_retention_sum : (∑ p ∈ P_Q, (candRet p).card : ℝ) ≥
        (P_Q.card : ℝ) * (M : ℝ) / K_cpd) :
    ∃ (P_Q' : Finset (DyadicSquare n))
      (hP_Q'_sub : P_Q' ⊆ P_Q)
      (hP_Q'_nonempty : P_Q'.Nonempty)
      (uniformFamily : (p : DyadicSquare n) → p ∈ P_Q' → Finset (DyadicTube n))
      (m_Q MQ : ℕ) (hmQ_pos : 0 < m_Q) (hMQ_pos : 0 < MQ)
      (K_ret K_loss K_fine : ℝ) (hK_ret : 1 ≤ K_ret) (hK_ret_eq : K_ret = 2 * K_cpd)
      (hK_loss : 1 ≤ K_loss) (hK_loss_eq : K_loss = 16 * (numDyadicLevels M : ℝ)^2)
      (hK_fine : 1 ≤ K_fine) (hK_fine_eq : K_fine = K_loss * K_ret * Real.rpow 16 s),
      (∀ p hp, uniformFamily p hp ⊆ candRet p) ∧
      (∀ p hp, (M : ℝ) ≤ K_ret * K_loss * ((uniformFamily p hp).card : ℝ)) ∧
      ((P_Q.card : ℝ) ≤ K_ret * K_loss * (P_Q'.card : ℝ)) ∧
      (∀ p hp, IsFiniteTubeSSet s (K_loss * K_ret * C₁) (uniformFamily p hp)) ∧
      (∀ p hp (a : ℤ), ((uniformFamily p hp).filter
          (fun T => localSlopeCellIndex m T.a = a)).card =
        if a ∈ (uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a)
        then m_Q else 0) ∧
      (∀ p hp, ((uniformFamily p hp).image
          (fun T => localSlopeCellIndex m T.a)).card = MQ) ∧
      (∀ p hp T, T ∈ uniformFamily p hp → (T.toSet ∩ p.toSet).Nonempty) ∧
      (∀ p hp T, T ∈ uniformFamily p hp → T.IsInAllowedParameterStrip) ∧
      (∃ (fineConfig : NiceConfiguration (n - m) s (K_fine * C₁) MQ),
        fineConfig.points = P_Q'.image (squareHomothety hnm Q) ∧
        fineConfig.tubes = fineConfig.points.biUnion (fun q =>
          if hq : q ∈ fineConfig.points then fineConfig.tubeFamily q hq else ∅) ∧
        (∀ p (hp : p ∈ P_Q'),
          ∃ hq : squareHomothety hnm Q p ∈ fineConfig.points,
            (fineConfig.tubeFamily (squareHomothety hnm Q p) hq).image (fun U => U.a) =
              (uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a))) := by
  -- Step 8: Point selection by retention
  have h_ret_upper : ∀ p ∈ P_Q, (candRet p).card ≤ M := by
    intro p hp
    have h1 : candRet p ⊆ originalFamily p := h_candRet_sub p hp
    have h2 : (candRet p).card ≤ (originalFamily p).card := Finset.card_le_card h1
    have h3 : (originalFamily p).card = M := h_orig_size p hp
    rw [h3] at h2; exact h2

  rcases select_points_by_retention hnm P_Q candRet M hM K_cpd hK_cpd
      hP_Q_nonempty h_ret_upper h_retention_sum
    with ⟨P_Q1, K_ret, hP_Q1_sub, hK_ret, hK_ret_eq, hP_Q1_nonempty, h_size_ret, h_coverage1⟩

  -- Establish SSet for candRet on P_Q1: C_ret = K_ret * C₁
  let C_ret : ℝ := K_ret * C₁
  have hC_ret : 1 ≤ C_ret := by
    have h1 : 1 ≤ K_ret := hK_ret
    have h2 : 1 ≤ C₁ := hC₁
    nlinarith

  have h_candRet_sset1 : ∀ p ∈ P_Q1, IsFiniteTubeSSet s C_ret (candRet p) := by
    intro p hp
    have hpQ : p ∈ P_Q := hP_Q1_sub hp
    have h_sub : candRet p ⊆ originalFamily p := h_candRet_sub p hpQ
    have h_orig_sset' : IsFiniteTubeSSet s C₁ (originalFamily p) := h_orig_sset p hpQ
    have h_size : (originalFamily p).card = M := h_orig_size p hpQ
    have h_ret_pos : (candRet p).Nonempty := by
      have h4 : (M : ℝ) ≤ K_ret * ((candRet p).card : ℝ) := h_size_ret p hp
      have h5 : 0 < (M : ℝ) := by exact_mod_cast hM
      have h6 : 0 < ((candRet p).card : ℝ) := by
        by_contra h7
        have h8 : ((candRet p).card : ℝ) ≤ 0 := by linarith
        have h9 : ((candRet p).card : ℝ) = 0 := by linarith
        rw [h9] at h4
        linarith
      exact Finset.card_pos.mp (by exact_mod_cast h6)
    have h_loss_bound : ((originalFamily p).card : ℝ) ≤ K_ret * ((candRet p).card : ℝ) := by
      rw [h_size]; exact h_size_ret p hp
    have h_result : IsFiniteTubeSSet s (C₁ * K_ret) (candRet p) :=
      IsFiniteTubeSSet.subset_with_loss h_orig_sset' h_sub h_ret_pos h_loss_bound
    have h_comm : C₁ * K_ret = C_ret := by
      dsimp only [C_ret] <;> ring
    rw [h_comm] at h_result
    exact h_result

  have h_candRet_incidence1 : ∀ p ∈ P_Q1, ∀ T ∈ candRet p, (T.toSet ∩ p.toSet).Nonempty :=
    fun p hp T hT => h_candRet_incidence p (hP_Q1_sub hp) T hT
  have h_candRet_params1 : ∀ p ∈ P_Q1, ∀ T ∈ candRet p, T.IsInAllowedParameterStrip :=
    fun p hp T hT => h_candRet_params p (hP_Q1_sub hp) T hT

  have h_ret_upper1 : ∀ p ∈ P_Q1, (candRet p).card ≤ M := by
    intro p hp
    exact h_ret_upper p (hP_Q1_sub hp)

  -- Step 9: Uniformize families per square
  rcases uniformize_families_per_square_generalized hnm s hs hs_one
      C_ret hC_ret M hM Q P_Q1 hP_Q1_nonempty (fun p hp => candRet p)
      h_candRet_sset1 h_ret_upper1 h_candRet_incidence1 h_candRet_params1
    with ⟨m_Q, hmQ_pos, MQ, hMQ_pos, P_Q', hP_Q'_sub1, hP_Q'_nonempty,
      uniformFamily, K_loss, hK_loss, hK_loss_eq,
      h_uniform_sub, h_tube_retention, h_sset_uniform,
      h_uniform_packets, h_cell_count, h_incidence_uniform, h_params_uniform,
      h_coverage2⟩

  let hP_Q'_sub : P_Q' ⊆ P_Q := Finset.Subset.trans hP_Q'_sub1 hP_Q1_sub

  have h_coverage_total : (P_Q.card : ℝ) ≤ K_ret * K_loss * (P_Q'.card : ℝ) := by
    calc (P_Q.card : ℝ)
      ≤ K_ret * (P_Q1.card : ℝ) := h_coverage1
    _ ≤ K_ret * (K_loss * (P_Q'.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left h_coverage2 (by positivity)
    _ = K_ret * K_loss * (P_Q'.card : ℝ) := by ring

  have h_retention_total : ∀ p hp, (M : ℝ) ≤ K_ret * K_loss * ((uniformFamily p hp).card : ℝ) := by
    intro p hp
    have h1 : (M : ℝ) ≤ K_ret * ((candRet p).card : ℝ) := h_size_ret p (hP_Q'_sub1 hp)
    have h2 : ((candRet p).card : ℝ) ≤ K_loss * ((uniformFamily p hp).card : ℝ) :=
      h_tube_retention p hp
    calc (M : ℝ)
      ≤ K_ret * ((candRet p).card : ℝ) := h1
    _ ≤ K_ret * (K_loss * ((uniformFamily p hp).card : ℝ)) := by gcongr
    _ = K_ret * K_loss * ((uniformFamily p hp).card : ℝ) := by ring

  have hP_Q'_sub_config : P_Q' ⊆ config.points :=
    Finset.Subset.trans hP_Q'_sub hP_Q_sub
  have hP_Q'_contained : ∀ p ∈ P_Q', squareContained hnm p Q :=
    fun p hp => hP_Q_contained p (hP_Q'_sub hp)

  have hQ : Q ∈ P_Q'.image (containingSquare hnm) := by
    rcases hP_Q'_nonempty with ⟨p, hp⟩
    have h_cont : squareContained hnm p Q := hP_Q'_contained p hp
    have h_eq : containingSquare hnm p = Q :=
      squareContained_iff_containingSquare hnm p Q |>.mp h_cont
    exact Finset.mem_image.mpr ⟨p, hp, h_eq⟩

  -- Step 10: Fine phase
  let C_in : ℝ := K_loss * C_ret
  let K_fine : ℝ := max 1 (C_in * Real.rpow 16 s / C₁)
  have hK_fine : 1 ≤ K_fine := by simp [K_fine] <;> linarith
  have hK_fine_eq : K_fine = K_loss * K_ret * Real.rpow 16 s := by
    have h1 : C_in * Real.rpow 16 s / C₁ = K_loss * K_ret * Real.rpow 16 s := by
      dsimp only [C_in, C_ret]
      have hC₁_pos : 0 < C₁ := by linarith
      field_simp [hC₁_pos.ne'] <;> ring
    have h2 : 1 ≤ K_loss * K_ret * Real.rpow 16 s := by
      have h3 : 1 ≤ K_loss := hK_loss
      have h4 : 1 ≤ K_ret := hK_ret
      have h5 : 1 ≤ Real.rpow 16 s := by
        apply Real.one_le_rpow
        · norm_num
        · linarith
      have h6 : 1 ≤ K_loss * K_ret := by
        have h61 : 1 * 1 ≤ K_loss * K_ret := mul_le_mul hK_loss hK_ret (by exact_mod_cast zero_le_one) (by linarith)
        simpa using h61
      have h7 : 0 ≤ Real.rpow 16 s := Real.rpow_nonneg (by norm_num) s
      calc 1
        = 1 * 1 := by ring
      _ ≤ (K_loss * K_ret) * Real.rpow 16 s := by gcongr <;> linarith
      _ = K_loss * K_ret * Real.rpow 16 s := by ring
    have h_main : max 1 (C_in * Real.rpow 16 s / C₁) = K_loss * K_ret * Real.rpow 16 s := by
      rw [h1, max_eq_right h2]
    exact h_main
  have hC_in_bound : C_in * Real.rpow 16 s ≤ K_fine * C₁ := by
    have hC₁_pos : 0 < C₁ := by linarith
    have h1 : C_in * Real.rpow 16 s / C₁ ≤ K_fine := by simp [K_fine] <;> linarith
    calc C_in * Real.rpow 16 s
      = (C_in * Real.rpow 16 s / C₁) * C₁ := by field_simp [hC₁_pos.ne'] <;> ring
    _ ≤ K_fine * C₁ := by gcongr

  have h_G_exists : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q') (hpQ : squareContained hnm p Q),
      ∃ (G : Finset (DyadicTube (n - m))),
        (G.image (fun U => U.a) = (uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a)) ∧
        Set.InjOn (fun U : DyadicTube (n - m) => U.a) G ∧
        IsFiniteTubeSSet s (C_in * Real.rpow 16 s) G ∧
        ∀ U ∈ G, (U.toSet ∩ (squareHomothety hnm Q p).toSet).Nonempty := by
    intro p hp hpQ
    have h_bounded : p.toSet ⊆ unitSquare := config.h_bounded p (hP_Q'_sub_config hp)
    exact FineConfig.construct_fine_tube_family hnm p hs (uniformFamily p hp)
      (h_sset_uniform p hp) (h_incidence_uniform p hp) h_bounded
      (h_params_uniform p hp) m_Q hmQ_pos (h_uniform_packets p hp) rfl
      (squareHomothety hnm Q p)

  classical
  choose G_p hG_spec using h_G_exists

  let G (p : DyadicSquare n) (hp : p ∈ P_Q') (hpQ : squareContained hnm p Q) :
      Finset (DyadicTube (n - m)) := G_p p hp hpQ

  have hG_spec' : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q') (hpQ : squareContained hnm p Q),
      (G p hp hpQ).image (fun U => U.a) = (uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a) ∧
      Set.InjOn (fun U : DyadicTube (n - m) => U.a) (G p hp hpQ) ∧
      IsFiniteTubeSSet s (C_in * Real.rpow 16 s) (G p hp hpQ) ∧
      ∀ U ∈ G p hp hpQ, (U.toSet ∩ (squareHomothety hnm Q p).toSet).Nonempty :=
    hG_spec

  have h_cell_count' : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q') (hpQ : squareContained hnm p Q),
      ((uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a)).card = MQ := by
    intro p hp _; exact h_cell_count p hp

  have h_tube_params' : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q') (T : DyadicTube n),
      T ∈ uniformFamily p hp → T.IsInAllowedParameterStrip := by
    intro p hp T hT; exact h_params_uniform p hp T hT

  let fineConfig : NiceConfiguration (n - m) s (K_fine * C₁) MQ :=
    build_single_fine_config hnm s hs C₁ K_fine C_in hK_fine hC₁ hC_in_bound
      P_Q' uniformFamily m_Q hmQ_pos MQ Q hQ G hG_spec' h_cell_count' h_tube_params'

  have h_fine_points : fineConfig.points = P_Q'.image (squareHomothety hnm Q) := by
    have h_filter_eq : P_Q'.filter (fun p => squareContained hnm p Q) = P_Q' := by
      apply Finset.filter_true_of_mem
      intro p hp; exact hP_Q'_contained p hp
    simp [fineConfig, build_single_fine_config, h_filter_eq]

  have h_slope_cells : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q'),
      ∃ hq : squareHomothety hnm Q p ∈ fineConfig.points,
        (fineConfig.tubeFamily (squareHomothety hnm Q p) hq).image (fun U => U.a) =
          (uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a) := by
    intro p hp
    have hpQ : squareContained hnm p Q := hP_Q'_contained p hp
    have hq : squareHomothety hnm Q p ∈ fineConfig.points := by
      rw [h_fine_points]; exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have h_eq : fineConfig.tubeFamily (squareHomothety hnm Q p) hq = G p hp hpQ := by
      simp [fineConfig, build_single_fine_config, fine_local_tube_family_at_point hnm P_Q' Q G p hp hpQ _ hq rfl]
      <;> rfl
    refine ⟨hq, ?_⟩
    rw [h_eq]
    exact (hG_spec' p hp hpQ).1

  have h_inj_homothety2 : Set.InjOn (squareHomothety hnm Q) (P_Q' : Set (DyadicSquare n)) := by
    intro p1 hp1 p2 hp2 h
    have h1 : fine_local_p_of_q hnm Q (squareHomothety hnm Q p1) = p1 :=
      fine_local_p_of_q_inverse hnm Q p1 (hP_Q'_contained p1 hp1)
    have h2 : fine_local_p_of_q hnm Q (squareHomothety hnm Q p2) = p2 :=
      fine_local_p_of_q_inverse hnm Q p2 (hP_Q'_contained p2 hp2)
    rw [h] at h1
    exact (h2.symm.trans h1).symm

  have h_fine_tubes_eq : fineConfig.tubes = fineConfig.points.biUnion (fun q =>
      if hq : q ∈ fineConfig.points then fineConfig.tubeFamily q hq else ∅) := by
    let tubeFamily_total (q : DyadicSquare (n - m)) : Finset (DyadicTube (n - m)) :=
      if hq : q ∈ fineConfig.points then fineConfig.tubeFamily q hq else ∅
    let G_total (p : DyadicSquare n) : Finset (DyadicTube (n - m)) :=
      if hp : p ∈ P_Q' then G p hp (hP_Q'_contained p hp) else ∅
    have h_filter_eq2 : P_Q'.filter (fun p => squareContained hnm p Q) = P_Q' := by
      apply Finset.filter_true_of_mem
      intro p hp; exact hP_Q'_contained p hp
    have h2 : fineConfig.tubes = P_Q'.biUnion G_total := by
      ext U
      have h_def : fineConfig.tubes =
          (P_Q'.filter (fun p => squareContained hnm p Q)).attach.biUnion
            (fun (p : {x // x ∈ P_Q'.filter (fun p => squareContained hnm p Q)}) =>
              G p.val (Finset.mem_filter.mp p.property).1 (Finset.mem_filter.mp p.property).2) := by
        simp [fineConfig, build_single_fine_config] <;> rfl
      rw [h_def]
      simp only [Finset.mem_biUnion, Finset.mem_attach]
      constructor
      · rintro ⟨p_sub, hP, hU⟩
        let p : DyadicSquare n := p_sub.val
        have hp_filter : p ∈ P_Q'.filter (fun p => squareContained hnm p Q) := p_sub.property
        have hp : p ∈ P_Q' := (Finset.mem_filter.mp hp_filter).1
        have hpQ : squareContained hnm p Q := (Finset.mem_filter.mp hp_filter).2
        have h_gt : G_total p = G p hp hpQ := by
          simp [G_total, hp] <;> rfl
        exact ⟨p, hp, h_gt ▸ hU⟩
      · rintro ⟨p, hp, hU⟩
        have hpQ : squareContained hnm p Q := hP_Q'_contained p hp
        have hp_filter : p ∈ P_Q'.filter (fun p => squareContained hnm p Q) :=
          Finset.mem_filter.mpr ⟨hp, hpQ⟩
        let p_sub : {x // x ∈ P_Q'.filter (fun p => squareContained hnm p Q)} :=
          ⟨p, hp_filter⟩
        have h_gt : G_total p = G p hp hpQ := by
          simp [G_total, hp] <;> rfl
        have hU' : U ∈ G p_sub.val (Finset.mem_filter.mp p_sub.property).1
            (Finset.mem_filter.mp p_sub.property).2 := by
          rw [h_gt] at hU
          exact hU
        exact ⟨p_sub, by trivial, hU'⟩
    have h1 : fineConfig.points.biUnion tubeFamily_total = P_Q'.biUnion G_total := by
      have h_points : fineConfig.points = P_Q'.image (squareHomothety hnm Q) := h_fine_points
      rw [h_points]
      have h_biUnion_img : (P_Q'.image (squareHomothety hnm Q)).biUnion tubeFamily_total =
          P_Q'.biUnion (fun p => tubeFamily_total (squareHomothety hnm Q p)) := by
        ext z
        simp only [Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro ⟨q, ⟨p, hp, rfl⟩, hz⟩
          exact ⟨p, hp, hz⟩
        · rintro ⟨p, hp, hz⟩
          exact ⟨squareHomothety hnm Q p, ⟨p, hp, rfl⟩, hz⟩
      rw [h_biUnion_img]
      refine' Finset.biUnion_congr rfl _
      intro p hp
      have hq : squareHomothety hnm Q p ∈ fineConfig.points := by
        rw [h_fine_points]; exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
      have h_a : tubeFamily_total (squareHomothety hnm Q p) =
          fineConfig.tubeFamily (squareHomothety hnm Q p) hq := by
        simp [tubeFamily_total, hq]
      have h_b : fineConfig.tubeFamily (squareHomothety hnm Q p) hq =
          G p hp (hP_Q'_contained p hp) := by
        simp [fineConfig, build_single_fine_config,
          fine_local_tube_family_at_point hnm P_Q' Q G p hp (hP_Q'_contained p hp) _ hq rfl] <;> rfl
      have h_c : G_total p = G p hp (hP_Q'_contained p hp) := by
        simp [G_total, hp]
      rw [h_a, h_b, h_c]
    rw [h2]
    exact h1.symm

  have h_sset_uniform' : ∀ p hp, IsFiniteTubeSSet s (K_loss * K_ret * C₁) (uniformFamily p hp) := by
    intro p hp
    have h1 : IsFiniteTubeSSet s (K_loss * C_ret) (uniformFamily p hp) := h_sset_uniform p hp
    have h_eq : K_loss * C_ret = K_loss * K_ret * C₁ := by
      dsimp only [C_ret] <;> ring
    rw [h_eq] at h1
    exact h1

  exact ⟨P_Q', hP_Q'_sub, hP_Q'_nonempty, uniformFamily, m_Q, MQ, hmQ_pos, hMQ_pos,
    K_ret, K_loss, K_fine, hK_ret, hK_ret_eq, hK_loss, hK_loss_eq, hK_fine, hK_fine_eq,
    h_uniform_sub, h_retention_total, h_coverage_total,
    h_sset_uniform', h_uniform_packets, h_cell_count,
    h_incidence_uniform, h_params_uniform,
    ⟨fineConfig, h_fine_points, h_fine_tubes_eq, h_slope_cells⟩⟩

end InductionOnScales
