import MyLeanRepo.Kakeya.CV.Statements
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace Kakeya.CV

/-- Pointwise convergence on a finite set gives uniform boundedness on that set. -/
lemma finite_pointwise_bounded {E : Type*} {P : Set E} (hP : P.Finite)
    (f : ℕ → E → ℝ) (g : E → ℝ)
    (hpt : ∀ x, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x))) :
    ∃ (M : ℝ), 0 < M ∧ ∀ n, ∀ p ∈ P, |f n p| ≤ M := by
  classical
  let P' : Finset E := hP.toFinset
  have hP'_eq : (P' : Set E) = P := by
    exact Set.Finite.coe_toFinset hP
  have h1 : ∀ (p : E), p ∈ P' → ∃ (B : ℝ), 0 ≤ B ∧ ∀ n, |f n p| ≤ B := by
    intro p _
    have hconv : Filter.Tendsto (fun n => |f n p|) Filter.atTop (nhds (|g p|)) :=
      (hpt p).norm
    have h2 : BddAbove (Set.range (fun n => |f n p|)) := hconv.bddAbove_range
    rcases h2 with ⟨B, hB⟩
    have h3 : ∀ n, |f n p| ≤ B := fun n => hB (Set.mem_range_self n)
    have h4 : 0 ≤ B := by
      have h5 : |f 0 p| ≤ B := h3 0
      exact abs_nonneg (f 0 p) |>.trans h5
    exact ⟨B, h4, h3⟩
  choose B hB_nonneg hB_bound using h1
  let B' : E → ℝ := fun p => if h : p ∈ P' then B p h else 0
  by_cases hPempty : P'.Nonempty
  · let Bs : Finset ℝ := P'.image B'
    have hBs_nonempty : Bs.Nonempty := hPempty.image _
    let M := Bs.max' hBs_nonempty
    have h5 : ∀ p ∈ P', B' p ≤ M := by
      intro p hp
      have h6 : B' p ∈ Bs := Finset.mem_image.mpr ⟨p, hp, rfl⟩
      exact Finset.le_max' Bs (B' p) h6
    have hM_nonneg : 0 ≤ M := by
      obtain ⟨x, hx⟩ := hPempty
      have h7 : 0 ≤ B' x := by
        dsimp only [B']
        rw [dif_pos hx]
        exact hB_nonneg x hx
      have h8 : B' x ≤ M := h5 x hx
      linarith
    refine ⟨M + 1, by linarith, fun n p hp => ?_⟩
    have hp' : p ∈ P' := by
      have h : p ∈ (P' : Set E) := hP'_eq.symm ▸ hp
      exact h
    have h9 : |f n p| ≤ B' p := by
      dsimp only [B']
      rw [dif_pos hp']
      exact hB_bound p hp' n
    have h10 : B' p ≤ M := h5 p hp'
    linarith
  · refine ⟨1, by norm_num, fun n p hp => ?_⟩
    have hcont : False := by
      have h : P' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hPempty
      have hp' : p ∈ P' := by
        have h2 : p ∈ (P' : Set E) := hP'_eq.symm ▸ hp
        exact h2
      rw [h] at hp'
      simpa using hp'
    exact False.elim hcont

theorem tendstoUniformlyOn_of_convex_pointwise {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : ℕ → E → ℝ) (g : E → ℝ) (K : Set E)
    (hf : ∀ n, ConvexOn ℝ Set.univ (f n))
    (hg : ConvexOn ℝ Set.univ g)
    (hpt : ∀ x, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x)))
    (hK : IsCompact K) :
    TendstoUniformlyOn f g Filter.atTop K := by
  by_cases hKempty : K = ∅
  · rw [hKempty]
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε _
    filter_upwards with n
    <;> simp
  · have hKnonempty : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
    classical
    let x₀ : E := Classical.choose hKnonempty
    have hx₀ : x₀ ∈ K := Classical.choose_spec hKnonempty

    -- Step 1: K is bounded, pick R > 0 with K ⊆ closedBall 0 R
    have hKbdd : Bornology.IsBounded K := hK.isBounded
    have h1 : ∃ (R0 : ℝ), ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ R0 :=
      Metric.isBounded_iff (α := E) |>.mp hKbdd
    rcases h1 with ⟨R0, hR0⟩
    let R : ℝ := R0 + dist x₀ 0 + 1
    have hR_pos : 0 < R := by
      dsimp only [R]
      have h2 : 0 ≤ R0 := by
        have h3 : dist x₀ x₀ ≤ R0 := hR0 x₀ hx₀ x₀ hx₀
        have h4 : dist x₀ x₀ = 0 := dist_self x₀
        rw [h4] at h3
        exact h3
      have h5 : 0 ≤ dist x₀ 0 := dist_nonneg
      linarith
    have hKsub : K ⊆ Metric.closedBall (0 : E) R := by
      intro x hx
      have h4 : dist x x₀ ≤ R0 := hR0 x hx x₀ hx₀
      have h5 : dist x 0 ≤ dist x x₀ + dist x₀ 0 := dist_triangle _ _ _
      have h6 : dist x 0 ≤ R := by linarith
      simpa [Metric.mem_closedBall] using h6

    let s : Set E := Metric.closedBall (0 : E) R
    have hs_conv : Convex ℝ s := convex_closedBall 0 R
    have hs_compact : IsCompact s := isCompact_closedBall 0 R
    have hs_nonempty : s.Nonempty := by
      refine ⟨0, ?_⟩
      simp [s, hR_pos.le]

    -- Step 2: Get finite set u whose convex hull contains a neighborhood of s
    have h_main : ∃ (u : Finset E), s ⊆ interior (convexHull ℝ (u : Set E)) := by
      have h_univ_nhds : (Set.univ : Set E) ∈ nhdsSet s :=
        (IsOpen.mem_nhdsSet isOpen_univ).mpr (Set.subset_univ s)
      have h₁ := Convex.exists_subset_interior_convexHull_finset_of_isCompact
        hs_conv hs_compact h_univ_nhds
      rcases h₁ with ⟨u, h₂, _⟩
      exact ⟨u, h₂⟩
    rcases h_main with ⟨u, hu_sub⟩

    let U : Set E := convexHull ℝ (u : Set E)
    have hU_interior_open : IsOpen (interior U) := isOpen_interior
    have hs_sub : s ⊆ interior U := hu_sub

    -- Step 3: Get δ > 0 such that thickening δ s ⊆ interior U
    have hδ : ∃ (δ : ℝ), 0 < δ ∧ Metric.thickening δ s ⊆ interior U :=
      hs_compact.exists_thickening_subset_open hU_interior_open hs_sub
    rcases hδ with ⟨δ, hδ_pos, hthick⟩
    let δ' := δ / 2
    have hδ'_pos : 0 < δ' := half_pos hδ_pos

    -- closedBall 0 (R + δ') ⊆ U
    have hball_sub : Metric.closedBall (0 : E) (R + δ') ⊆ U := by
      intro y hy
      have h₁ : ‖y‖ ≤ R + δ' := by simpa [Metric.mem_closedBall] using hy
      have h_exists : ∃ (z : E), z ∈ s ∧ dist y z < δ := by
        by_cases h₃ : ‖y‖ ≤ R
        · refine ⟨y, ?_ , ?_⟩
          · simpa [s, Metric.mem_closedBall] using h₃
          · have h4 : dist y y = 0 := dist_self y
            rw [h4] <;> linarith
        · have h₄ : R < ‖y‖ := by linarith
          have h₄' : ‖y‖ ≠ 0 := by linarith
          let z : E := (R / ‖y‖) • y
          have hR_nonneg : 0 ≤ R := by linarith
          have h_pos2 : 0 ≤ R / ‖y‖ := by positivity
          have hz_norm : ‖z‖ = R := by
            calc ‖z‖
              = ‖(R / ‖y‖) • y‖ := by rfl
            _ = |R / ‖y‖| * ‖y‖ := norm_smul _ _
            _ = (R / ‖y‖) * ‖y‖ := by rw [abs_of_nonneg h_pos2]
            _ = R := by field_simp [h₄'] <;> ring
          have hz_s : z ∈ s := by
            simpa [s, Metric.mem_closedBall] using hz_norm.le
          have h₅ : y - z = (1 - R / ‖y‖) • y := by
            simp [z, sub_smul] <;> abel
          have h₇ : 0 ≤ 1 - R / ‖y‖ := by
            have h₈ : R / ‖y‖ ≤ 1 := by
              apply (div_le_one (by linarith)).mpr
              linarith
            linarith
          have h_dist : dist y z = ‖y‖ - R := by
            have h₆ : dist y z = ‖y - z‖ := dist_eq_norm y z
            rw [h₆, h₅]
            have h₉ : ‖(1 - R / ‖y‖) • y‖ = (1 - R / ‖y‖) * ‖y‖ := by
              rw [norm_smul]
              have h₁₀ : ‖(1 - R / ‖y‖)‖ = 1 - R / ‖y‖ := by
                rw [Real.norm_eq_abs, abs_of_nonneg h₇]
              rw [h₁₀]
            rw [h₉]
            field_simp [h₄'] <;> ring
          refine ⟨z, hz_s, ?_⟩
          rw [h_dist]
          have h_goal : ‖y‖ - R < δ := by
            calc ‖y‖ - R ≤ (R + δ') - R := by gcongr <;> linarith
              _ = δ' := by ring
              _ < δ := by dsimp only [δ']; linarith [hδ_pos]
          exact h_goal
      have h₃ : y ∈ Metric.thickening δ s := by
        rcases h_exists with ⟨z, hz_s, hzy⟩
        simpa [Metric.mem_thickening_iff] using ⟨z, hz_s, hzy⟩
      have h₄ : y ∈ interior U := hthick h₃
      exact interior_subset h₄

    -- Step 4: Uniform boundedness on u
    have h_vertex : ∃ (M : ℝ), 0 < M ∧ ∀ n, ∀ p ∈ (u : Set E), |f n p| ≤ M :=
      finite_pointwise_bounded (Finset.finite_toSet u) f g hpt
    rcases h_vertex with ⟨M, hM_pos, hM_bound⟩

    -- Step 5: Upper bound on U
    have h_upper : ∀ n, ∀ y ∈ U, f n y ≤ M := by
      intro n y hy
      have h₁ : ∃ (p : E), p ∈ (u : Set E) ∧ f n y ≤ f n p :=
        (hf n).exists_ge_of_mem_convexHull (by simp) hy
      rcases h₁ with ⟨p, hp, hle⟩
      have h₂ : |f n p| ≤ M := hM_bound n p hp
      have h₃ : f n p ≤ M := by
        have h₄ : -M ≤ f n p ∧ f n p ≤ M := abs_le.mp h₂
        exact h₄.2
      linarith

    -- Step 6: Boundedness at 0
    have h_f0 : ∃ (C0 : ℝ), 0 < C0 ∧ ∀ n, |f n 0| ≤ C0 := by
      have hconv : Filter.Tendsto (fun n => |f n 0|) Filter.atTop (nhds (|g 0|)) :=
        (hpt 0).norm
      have h₂ : BddAbove (Set.range (fun n => |f n 0|)) := hconv.bddAbove_range
      rcases h₂ with ⟨C, hC⟩
      have h₃ : ∀ n, |f n 0| ≤ C := fun n => hC (Set.mem_range_self n)
      have h₄ : 0 ≤ C := by
        have h₅ : |f 0 0| ≤ C := h₃ 0
        exact abs_nonneg (f 0 0) |>.trans h₅
      exact ⟨C + 1, by linarith, fun n => by linarith [h₃ n]⟩
    rcases h_f0 with ⟨C0, hC0_pos, hC0_bound⟩

    let M' := max M (2 * C0 + M)
    have hM'_pos : 0 < M' := by
      apply lt_max_of_lt_left
      exact hM_pos

    -- Step 7: Uniform bound |f n y| ≤ M' on closedBall 0 (R + δ')
    have h_bound : ∀ n, ∀ y ∈ Metric.closedBall (0 : E) (R + δ'), |f n y| ≤ M' := by
      intro n y hy
      have h_y_in_U : y ∈ U := hball_sub hy
      have h_upper_y : f n y ≤ M := h_upper n y h_y_in_U
      have h_neg_y_in_U : -y ∈ U := by
        have h₁ : ‖-y‖ = ‖y‖ := by simp
        have h₂ : ‖y‖ ≤ R + δ' := by simpa [Metric.mem_closedBall] using hy
        have h₃ : ‖-y‖ ≤ R + δ' := by rw [h₁] <;> exact h₂
        have h₄ : -y ∈ Metric.closedBall (0 : E) (R + δ') := by
          simpa [Metric.mem_closedBall] using h₃
        exact hball_sub h₄
      have h_upper_neg_y : f n (-y) ≤ M := h_upper n (-y) h_neg_y_in_U
      have h_conv0 : f n 0 ≤ (1 / 2 : ℝ) * f n y + (1 / 2 : ℝ) * f n (-y) := by
        have h₁ : (0 : E) = (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • (-y) := by
          simp [smul_smul] <;> abel
        rw [h₁]
        exact (hf n).2 trivial trivial (by norm_num) (by norm_num) (by norm_num)
      have h_f0_lower : -C0 ≤ f n 0 := by
        have h₂ : |f n 0| ≤ C0 := hC0_bound n
        have h₃ : -C0 ≤ f n 0 ∧ f n 0 ≤ C0 := abs_le.mp h₂
        exact h₃.1
      have h_lower_y : f n y ≥ -2 * C0 - M := by linarith
      have h₃ : -M' ≤ f n y := by
        have h₄ : -M' ≤ -2 * C0 - M := by
          simp [M'] <;> linarith
        linarith
      have h₄ : f n y ≤ M' := by
        have h₅ : M ≤ M' := by simp [M'] <;> linarith
        linarith
      exact abs_le.mpr ⟨h₃, h₄⟩

    -- Step 8: Uniform Lipschitz on ball x δ_L for all x ∈ K
    let ε_L := δ' / 2
    have hεL_pos : 0 < ε_L := half_pos hδ'_pos
    let L : NNReal := (2 * M' / ε_L).toNNReal
    have hL_coe : (L : ℝ) = 2 * M' / ε_L := by
      simp [L, Real.toNNReal_of_nonneg (show 0 ≤ 2 * M' / ε_L by positivity)]
      <;> ring
    let δ_L := δ' - ε_L
    have hδL_pos : 0 < δ_L := by
      dsimp only [δ_L, ε_L]
      linarith [hδ'_pos]

    have hLipschitz : ∀ (x : E), x ∈ K → ∀ n, LipschitzOnWith L (f n) (Metric.ball x δ_L) := by
      intro x hx n
      have h₁ : ∀ y ∈ Metric.ball x δ', |f n y| ≤ M' := by
        intro y hy
        have h₂ : ‖x‖ ≤ R := by
          have h₃ : x ∈ K := hx
          have h₄ : x ∈ s := hKsub h₃
          simpa [s, Metric.mem_closedBall] using h₄
        have h₃ : dist y x < δ' := by simpa [Metric.mem_ball] using hy
        have h₄ : ‖y‖ < R + δ' := by
          have h_tri : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
            calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
              _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
          have h6 : ‖y - x‖ = dist y x := by rw [dist_eq_norm]
          rw [h6] at h_tri
          linarith
        have h₇ : y ∈ Metric.closedBall (0 : E) (R + δ') := by
          simpa [Metric.mem_closedBall] using le_of_lt h₄
        exact h_bound n y h₇
      have h_conv_ball : ConvexOn ℝ (Metric.ball x δ') (f n) := by
        refine' ⟨convex_ball x δ', _⟩
        intro y _ z _ a b ha hb hab
        exact (hf n).2 trivial trivial ha hb hab
      exact h_conv_ball.lipschitzOnWith_of_abs_le hεL_pos h₁

    -- Step 9: Uniform equicontinuity on K
    have h_equicont : ∀ n, ∀ (x y : E), x ∈ K → y ∈ K → dist x y < δ_L →
        |f n x - f n y| ≤ (L : ℝ) * dist x y := by
      intro n x y hx hy hdist
      have hdist' : dist y x < δ_L := by
        rw [dist_comm] at hdist
        exact hdist
      have h₁ : y ∈ Metric.ball x δ_L := by simpa [Metric.mem_ball] using hdist'
      have h₂ : x ∈ Metric.ball x δ_L := by
        simp [Metric.mem_ball, hδL_pos]
      have h₃ := hLipschitz x hx n
      have h₄ : dist (f n x) (f n y) ≤ (L : ℝ) * dist x y :=
        h₃.dist_le_mul x h₂ y h₁
      simpa [Real.dist_eq] using h₄

    -- Step 10: g is continuous, hence uniformly continuous on K
    have hg_cont : Continuous g := by
      have h₁ : ContinuousOn g Set.univ := hg.continuousOn isOpen_univ
      simpa [continuousOn_univ] using h₁
    have hg_contOn : ContinuousOn g K := hg_cont.continuousOn.mono (Set.subset_univ K)
    have hg_uniform : UniformContinuousOn g K :=
      hK.uniformContinuousOn_of_continuous hg_contOn
    have hg_metric : ∀ (ε : ℝ), 0 < ε → ∃ (δ₂ : ℝ), 0 < δ₂ ∧
        ∀ (x y : E), x ∈ K → y ∈ K → dist x y < δ₂ → |g x - g y| < ε := by
      intro ε hε
      have h₁ := (Metric.uniformContinuousOn_iff.mp hg_uniform) ε hε
      rcases h₁ with ⟨δ₂, hδ₂_pos, h₂⟩
      exact ⟨δ₂, hδ₂_pos, fun x y hx hy hdist => h₂ x hx y hy hdist⟩

    -- Step 11: ε-net argument
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set η : ℝ := ε / 3 with hη_def
    have hη_pos : 0 < η := by
      rw [hη_def]
      exact div_pos hε (by norm_num)

    set δ₁ : ℝ := min δ_L (η / ((L : ℝ) + 1)) with hδ₁_def
    have hL_nonneg : 0 ≤ (L : ℝ) := NNReal.coe_nonneg L
    have h_pos_div : 0 < η / ((L : ℝ) + 1) := by
      apply div_pos hη_pos
      have h : 0 < (L : ℝ) + 1 := by linarith [hL_nonneg]
      exact h
    have hδ₁_pos : 0 < δ₁ := by
      rw [hδ₁_def]
      exact lt_min hδL_pos h_pos_div

    rcases hg_metric η hη_pos with ⟨δ₂, hδ₂_pos, hg_η⟩
    set δ_net : ℝ := min δ₁ δ₂ with hδ_net_def
    have hδ_net_pos : 0 < δ_net := by
      rw [hδ_net_def]
      exact lt_min hδ₁_pos hδ₂_pos

    -- Finite δ_net-net in K
    have h_net : ∃ (t : Finset E), (t : Set E) ⊆ K ∧
        K ⊆ ⋃ z ∈ (t : Set E), Metric.ball z δ_net := by
      have h₁ : TotallyBounded K := hK.totallyBounded
      have h₂ : ∃ (s : Set E), s ⊆ K ∧ s.Finite ∧ K ⊆ ⋃ y ∈ s, Metric.ball y δ_net :=
        Metric.finite_approx_of_totallyBounded h₁ δ_net hδ_net_pos
      rcases h₂ with ⟨s, hs_sub, hs_finite, hs_cover⟩
      let t : Finset E := hs_finite.toFinset
      have h3 : (t : Set E) = s := hs_finite.coe_toFinset
      refine ⟨t, ?_⟩
      rw [h3]
      exact ⟨hs_sub, hs_cover⟩
    rcases h_net with ⟨t, ht_sub, ht_cover⟩

    -- Pointwise convergence on t
    have h₂ : ∀ (z : E), z ∈ (t : Set E) → ∀ᶠ n in Filter.atTop, |f n z - g z| < η := by
      intro z _
      have h₃ : Filter.Tendsto (fun n => f n z) Filter.atTop (nhds (g z)) := hpt z
      have h₄ : ∀ᶠ n in Filter.atTop, f n z ∈ Metric.ball (g z) η :=
        h₃.eventually (Metric.ball_mem_nhds (g z) hη_pos)
      filter_upwards [h₄] with n h₅
      have h₆ : dist (f n z) (g z) < η := by simpa [Metric.mem_ball] using h₅
      simpa [Real.dist_eq] using h₆
    have h_conv_t : ∀ᶠ n in Filter.atTop, ∀ z ∈ (t : Set E), |f n z - g z| < η :=
      (Filter.eventually_all_finite (Finset.finite_toSet t)).mpr h₂

    filter_upwards [h_conv_t] with n hn
    intro x hx
    have h_x_in_net : ∃ (z : E), z ∈ (t : Set E) ∧ x ∈ Metric.ball z δ_net := by
      have h₄ : x ∈ K := hx
      have h₅ : x ∈ ⋃ z ∈ (t : Set E), Metric.ball z δ_net := ht_cover h₄
      simpa [Set.mem_iUnion] using h₅
    rcases h_x_in_net with ⟨z, hz_t, hxz⟩
    have hz_K : z ∈ K := ht_sub hz_t
    have h_dist : dist x z < δ_net := by simpa [Metric.mem_ball] using hxz

    have h_dist_lt_L : dist x z < δ_L := by
      calc dist x z < δ_net := h_dist
        _ ≤ δ₁ := min_le_left _ _
        _ ≤ δ_L := min_le_left _ _
    have h1 : |f n x - f n z| ≤ (L : ℝ) * dist x z :=
      h_equicont n x z hx hz_K h_dist_lt_L

    have h_dist_le_div : dist x z ≤ η / ((L : ℝ) + 1) := by
      have h2 : dist x z ≤ δ₁ := by
        have h3 : dist x z < δ_net := h_dist
        linarith [min_le_left (α := ℝ) δ₁ δ₂]
      rw [hδ₁_def] at h2
      exact h2.trans (min_le_right _ _)
    have h_mul_le : (L : ℝ) * dist x z ≤ (L : ℝ) * (η / ((L : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left h_dist_le_div hL_nonneg
    have h_strict : (L : ℝ) * (η / ((L : ℝ) + 1)) < η := by
      have h₃ : 0 ≤ (L : ℝ) := hL_nonneg
      have h₄ : (L : ℝ) / ((L : ℝ) + 1) < 1 := by
        apply (div_lt_one (by linarith)).mpr
        linarith
      calc (L : ℝ) * (η / ((L : ℝ) + 1))
        = η * ((L : ℝ) / ((L : ℝ) + 1)) := by ring
      _ < η * 1 := by gcongr
      _ = η := by ring
    have h1' : |f n x - f n z| < η := by
      calc |f n x - f n z| ≤ (L : ℝ) * dist x z := h1
        _ ≤ (L : ℝ) * (η / ((L : ℝ) + 1)) := h_mul_le
        _ < η := h_strict

    have h2 : |f n z - g z| < η := hn z hz_t

    have h_dist2 : dist z x < δ₂ := by
      calc dist z x = dist x z := dist_comm _ _
        _ < δ_net := h_dist
        _ ≤ δ₂ := min_le_right _ _
    have h3 : |g z - g x| < η := hg_η z x hz_K hx h_dist2

    have h_main : |f n x - g x| < ε := by
      have h4 : f n x - g x = (f n x - f n z) + (f n z - g z) + (g z - g x) := by ring
      rw [h4]
      have h5 : |(f n x - f n z) + (f n z - g z) + (g z - g x)| ≤
          |f n x - f n z| + |f n z - g z| + |g z - g x| := by
        calc |(f n x - f n z) + (f n z - g z) + (g z - g x)|
          ≤ |(f n x - f n z) + (f n z - g z)| + |g z - g x| := abs_add_le _ _
        _ ≤ |f n x - f n z| + |f n z - g z| + |g z - g x| := by
          have h6 := abs_add_le (f n x - f n z) (f n z - g z)
          linarith
      have h_sum : |f n x - f n z| + |f n z - g z| + |g z - g x| < η + η + η := by
        linarith [h1', h2, h3]
      have h7 : η + η + η = ε := by
        simp [η] <;> ring
      rw [h7] at h_sum
      exact h5.trans_lt h_sum
    have h_goal : dist (g x) (f n x) = |f n x - g x| := by
      rw [Real.dist_eq]
      have h_abs : |g x - f n x| = |f n x - g x| := by
        rw [show g x - f n x = -(f n x - g x) by ring, abs_neg]
      exact h_abs
    rw [h_goal]
    exact h_main

end Kakeya.CV
