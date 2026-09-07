module

/-
  Uniformization with representative points.

  Pipeline:
  1. Construct dyadic square cover X' of X
  2. basic_uniformization_dyadic → RangeUniformityProp (density: 24^m)
  3. multi_level_thin → exact counts (density: 2^m, total: 48^m)
  4. Pick representative point from X in each selected square → P'
  5. Prove IsDyadicUniform P' (same intersection pattern)
  6. Density bound: external(X) ≤ (48*log)^m * 9 * external(P')
  7. S-set transfer via budget condition
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BasicUniformization
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.RangeUniformityBridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.DyadicUniform
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.UniformityBridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9Assembly

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.BasicUniformization
open DiscretisedFurstenbergEstimate.Section9Bridge
open DiscretisedFurstenbergEstimate.DyadicCubes
open MultiscaleDecomposition

local notation "dSquare" => BasicUniformization.dyadicSquare

/-- Helper: Union of dyadic squares intersecting X satisfies union-of-squares property. -/
lemma dyadic_cover_union_property
    {δ : ℝ} {nδ : ℕ} (hδ_eq : δ = dyadicDelta nδ)
    {X : Set EuclideanPlane} (hX_bdd : Bornology.IsBounded X) :
    ∀ (x : EuclideanPlane),
      x ∈ (⋃ (q : DyadicCube nδ) (hq : q ∈ D_nFinset nδ X hX_bdd), q.toSet) →
      ∃ (i j : ℤ), x ∈ dSquare δ i j ∧ (dSquare δ i j : Set EuclideanPlane) ⊆
        (⋃ (q : DyadicCube nδ) (hq : q ∈ D_nFinset nδ X hX_bdd), q.toSet) := by
  intro x hx
  rcases Set.mem_iUnion₂.mp hx with ⟨q, hq, xq⟩
  have h1 : q.toSet = dSquare δ q.i q.j := by
    have h2 := dyadicCube_toSet_eq nδ q
    rw [hδ_eq] at *
    <;> exact h2
  refine ⟨q.i, q.j, ?_, ?_⟩
  · rw [←h1]; exact xq
  · rw [←h1]
    intro y hy
    exact Set.mem_iUnion₂.mpr ⟨q, hq, hy⟩

/-- Helper: Representative point set is IsDyadicUniform. -/
lemma rep_points_dyadic_uniform_general
    {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (a : Fin (m + 1) → ℕ)
    (ha_eq : ∀ i, a i = q * i.val)
    (S'' : Finset (ℤ × ℤ)) (hS''_nonempty : S''.Nonempty) (N : Fin m → ℕ)
    (hN_pos : ∀ j, 1 ≤ N j)
    (h_exact : ∀ (j : Fin m) (g : ℤ × ℤ),
      let k := a (Fin.last m)
      let m_fine := k - a (Fin.succ j)
      let m_coarse := a (Fin.succ j) - a j.castSucc
      let fineSquares := S''.image (parentBy m_fine)
      let count := (fineSquares.filter (fun idx => parentBy m_coarse idx = g)).card
      count = 0 ∨ count = N j)
    (X : Set EuclideanPlane)
    (δ_d : ℝ) (hδ_d_eq : δ_d = (1 / 2 : ℝ) ^ (q * m))
    (h_intersect : ∀ idx ∈ S'',
      (X ∩ dSquare δ_d idx.1 idx.2).Nonempty) :
    ∃ (P' : Set EuclideanPlane),
      P' ⊆ X ∧
      IsDyadicUniform P' m ((1 / 2 : ℝ) ^ q)
        (fun i : ℕ => if h : i < m then N ⟨i, h⟩ else 1) ∧
      (∀ idx ∈ S'', ∃ x, x ∈ P' ∧ x ∈ dSquare δ_d idx.1 idx.2) := by
  let f : (ℤ × ℤ) → EuclideanPlane := fun idx =>
    if h : idx ∈ S'' then
      Classical.choose (h_intersect idx h)
    else
      (0 : EuclideanPlane)
  let P' : Set EuclideanPlane := f '' S''

  have hf_spec : ∀ idx ∈ S'', f idx ∈ X ∩ dSquare δ_d idx.1 idx.2 := by
    intro idx hidx
    have h_f_def : f idx = Classical.choose (h_intersect idx hidx) := by
      simp [f, hidx]
    rw [h_f_def]
    exact Classical.choose_spec (h_intersect idx hidx)

  have hP'_sub : P' ⊆ X := by
    intro y hy
    rcases hy with ⟨idx, hidx, rfl⟩
    exact (hf_spec idx hidx).1

  have hP'_nonempty : P'.Nonempty := by
    rcases hS''_nonempty with ⟨idx, hidx⟩
    exact ⟨f idx, Set.mem_image_of_mem f hidx⟩

  have h_fine_scale : δ_d = (1 / 2 : ℝ) ^ (q * m) := hδ_d_eq

  -- Key lemma: f idx ∈ coarse square at level i iff parentBy relation
  have h_key : ∀ (idx : ℤ × ℤ) (hidx : idx ∈ S'') (i : ℕ) (hi : i ≤ m) (a b : ℤ),
      f idx ∈ dSquare ((1 / 2 : ℝ) ^ (q * i)) a b ↔
      parentBy (q * (m - i)) idx = (a, b) := by
    intro idx hidx i hi a b
    have hx_fine : f idx ∈ dSquare ((1 / 2 : ℝ) ^ (q * m)) idx.1 idx.2 := by
      have h := (hf_spec idx hidx).2
      rw [h_fine_scale] at h
      exact h
    have h_arith_sub : q * m - q * (m - i) = q * i := by
      have h1 : q * (m - i) + q * i = q * m := by
        have h2 : (m - i) + i = m := by omega
        calc q * (m - i) + q * i = q * ((m - i) + i) := by rw [mul_add]
          _ = q * m := by rw [h2]
      have h3 : q * (m - i) ≤ q * m := by
        rw [←h1] <;> omega
      omega
    have h_arith_add : q * i + q * (m - i) = q * m := by
      have h2 : i + (m - i) = m := by omega
      calc q * i + q * (m - i) = q * (i + (m - i)) := by rw [mul_add]
        _ = q * m := by rw [h2]
    constructor
    · intro hx_coarse
      have h_coarse' : f idx ∈ dSquare ((1 / 2 : ℝ) ^ (q * m - q * (m - i))) a b := by
        rw [h_arith_sub]
        exact hx_coarse
      exact parentBy_of_intersection (by omega) ⟨f idx, hx_fine, h_coarse'⟩
    · intro h_parent
      have h_contain : dSquare ((1 / 2 : ℝ) ^ (q * m)) idx.1 idx.2 ⊆
          dSquare ((1 / 2 : ℝ) ^ (q * i)) a b := by
        have h := parentBy_square_containment (m := q * i) (k := q * (m - i))
            idx.1 idx.2 a b h_parent
        rw [h_arith_add] at h
        exact h
      exact h_contain hx_fine

  let N' : ℕ → ℕ := fun i => if h : i < m then N ⟨i, h⟩ else 1
  have hN'_pos : ∀ i < m, 1 ≤ N' i := by
    intro i hi
    simp [N', hi]
    exact hN_pos ⟨i, hi⟩

  -- Rewrite h_exact in specific q format
  have h_exact' : ∀ (j : Fin m) (g : ℤ × ℤ),
      let fineSquares := S''.image (parentBy (q * (m - (j.val + 1))))
      let count := (fineSquares.filter (fun idx => parentBy q idx = g)).card
      count = 0 ∨ count = N j := by
    intro j g
    have h1 : a (Fin.last m) = q * m := by
      have h : (Fin.last m).val = m := by simp
      rw [ha_eq (Fin.last m), h] <;> ring
    have h2 : a (Fin.succ j) = q * (j.val + 1) := by
      rw [ha_eq (Fin.succ j)] <;> simp <;> ring
    have h3 : a j.castSucc = q * j.val := by
      rw [ha_eq j.castSucc] <;> simp <;> ring
    have h4 := h_exact j g
    dsimp only at h4
    rw [h1, h2, h3] at h4
    have h_arith1 : q * m - q * (j.val + 1) = q * (m - (j.val + 1)) := by
      have h_le : j.val + 1 ≤ m := by exact_mod_cast j.is_lt
      exact (Nat.mul_sub_left_distrib q m (j.val + 1)).symm
    have h_arith2 : q * (j.val + 1) - q * j.val = q := by
      have h : q * (j.val + 1) - q * j.val = q * ((j.val + 1) - j.val) := by
        rw [←Nat.mul_sub_left_distrib] <;> omega
      rw [h]
      have h2 : (j.val + 1) - j.val = 1 := by omega
      rw [h2] <;> ring
    rw [h_arith1, h_arith2] at h4
    simpa using h4

  have h_main : ∀ (i : ℕ), i < m → ∀ (a b : ℤ),
      (P' ∩ dSquare ((1 / 2 : ℝ) ^ (q * i)) a b).Nonempty →
      (dyadicSquareCount ((1 / 2 : ℝ) ^ (q * (i + 1)))
         (P' ∩ dSquare ((1 / 2 : ℝ) ^ (q * i)) a b) : ENNReal) =
      (↑(N' i) : ENNReal) := by
    intro i hi a b h_nonempty
    let j : Fin m := ⟨i, hi⟩
    have hi_succ : i + 1 ≤ m := by omega
    let filtered := S''.filter (fun idx => parentBy (q * (m - i)) idx = (a, b))
    let img := filtered.image (parentBy (q * (m - (i + 1))))

    -- Set equality: the set of squares intersecting P' ∩ coarse equals img
    have h_set_eq : {p : ℤ × ℤ | (P' ∩ dSquare ((1 / 2 : ℝ) ^ (q * i)) a b ∩
          dSquare ((1 / 2 : ℝ) ^ (q * (i + 1))) p.1 p.2).Nonempty} =
        (img : Set (ℤ × ℤ)) := by
      ext p
      simp only [Set.mem_setOf_eq, Finset.mem_coe]
      constructor
      · rintro ⟨y, ⟨hyP, hy_coarse⟩, hy_fine⟩
        have h_exists : ∃ (idx : ℤ × ℤ), idx ∈ S'' ∧ f idx = y := by
          rcases hyP with ⟨idx, hidx, rfl⟩
          exact ⟨idx, hidx, rfl⟩
        rcases h_exists with ⟨idx, hidx, h_eq⟩
        have h1 : parentBy (q * (m - i)) idx = (a, b) := by
          have h_coarse_y : f idx ∈ dSquare ((1 / 2 : ℝ) ^ (q * i)) a b := by
            rw [h_eq]; exact hy_coarse
          exact (h_key idx hidx i (by omega) a b).mp h_coarse_y
        have h2 : parentBy (q * (m - (i + 1))) idx = p := by
          have h_fine_y : f idx ∈ dSquare ((1 / 2 : ℝ) ^ (q * (i + 1))) p.1 p.2 := by
            rw [h_eq]; exact hy_fine
          exact (h_key idx hidx (i + 1) (by omega) p.1 p.2).mp h_fine_y
        exact Finset.mem_image.mpr ⟨idx, Finset.mem_filter.mpr ⟨hidx, h1⟩, h2⟩
      · intro hpin
        rcases Finset.mem_image.mp hpin with ⟨idx, hfilter, rfl⟩
        have hidx : idx ∈ S'' := (Finset.mem_filter.mp hfilter).1
        have h1 : parentBy (q * (m - i)) idx = (a, b) :=
          (Finset.mem_filter.mp hfilter).2
        have h2 : f idx ∈ dSquare ((1 / 2 : ℝ) ^ (q * i)) a b :=
          (h_key idx hidx i (by omega) a b).mpr h1
        have h3 : f idx ∈ dSquare ((1 / 2 : ℝ) ^ (q * (i + 1)))
            (parentBy (q * (m - (i + 1))) idx).1
            (parentBy (q * (m - (i + 1))) idx).2 :=
          (h_key idx hidx (i + 1) (by omega) _ _).mpr rfl
        exact ⟨f idx, ⟨Set.mem_image_of_mem f hidx, h2⟩, h3⟩

    have h_count : dyadicSquareCount ((1 / 2 : ℝ) ^ (q * (i + 1)))
        (P' ∩ dSquare ((1 / 2 : ℝ) ^ (q * i)) a b) = ↑img.card := by
      rw [MultiscaleDecomposition.dyadicSquareCount, h_set_eq]
      have h_fin : Set.Finite (img : Set (ℤ × ℤ)) := Finset.finite_toSet img
      have h_encard : Set.encard (img : Set (ℤ × ℤ)) = ↑img.card := by
        exact Set.encard_coe_eq_coe_finsetCard img
      rw [h_encard]
      <;> rfl

    -- img = (S''.image parentBy(q*(m-(i+1)))).filter (parentBy q = (a,b))
    have h_comm : img = (S''.image (parentBy (q * (m - (i + 1))))).filter
        (fun idx => parentBy q idx = (a, b)) :=
      image_filter_commute_q hi_succ hq S'' a b

    rw [h_count, h_comm]
    let fineSquares := S''.image (parentBy (q * (m - (i + 1))))
    let count := (fineSquares.filter (fun idx => parentBy q idx = (a, b))).card
    have h_count_range : count = 0 ∨ count = N j := h_exact' j (a, b)

    -- Nonemptiness implies count > 0
    have h_count_pos : 0 < count := by
      rcases h_nonempty with ⟨y, ⟨hyP, hy_coarse⟩⟩
      have h_exists : ∃ (idx : ℤ × ℤ), idx ∈ S'' ∧ f idx = y := by
        rcases hyP with ⟨idx, hidx, rfl⟩
        exact ⟨idx, hidx, rfl⟩
      rcases h_exists with ⟨idx, hidx, h_eq⟩
      have h1 : parentBy (q * (m - i)) idx = (a, b) := by
        have h_coarse_y : f idx ∈ dSquare ((1 / 2 : ℝ) ^ (q * i)) a b := by
          rw [h_eq]; exact hy_coarse
        exact (h_key idx hidx i (by omega) a b).mp h_coarse_y
      let p := parentBy (q * (m - (i + 1))) idx
      have hpin : p ∈ fineSquares.filter (fun idx => parentBy q idx = (a, b)) := by
        have h4 : p ∈ fineSquares := Finset.mem_image.mpr ⟨idx, hidx, rfl⟩
        have h5 : parentBy q p = (a, b) := by
          have h6 : parentBy q p = parentBy (q * (m - i)) idx := by
            rw [parentBy_comp q (q * (m - (i + 1))) idx, arith_q_add hi_succ]
          rw [h6, h1]
        simp only [Finset.mem_filter] <;> exact ⟨h4, h5⟩
      exact Finset.card_pos.mpr ⟨p, hpin⟩

    have h_count_eq : count = N j := by
      rcases h_count_range with (h0 | h_eq)
      · exfalso; rw [h0] at h_count_pos; simpa using h_count_pos
      · exact h_eq

    have hN'_i : N' i = N j := by
      have h_i_lt_m : i < m := hi
      have h : N' i = N ⟨i, h_i_lt_m⟩ := by
        unfold N'
        rw [dif_pos h_i_lt_m]
      rw [h]
    have h_target : (↑img.card : ENNReal) = ↑(N' i) := by
      have h_card_eq : img.card = count := by
        rw [h_comm] <;> rfl
      rw [h_card_eq]
      rw [h_count_eq, hN'_i] <;> norm_cast
    exact h_comm ▸ h_target

  have h_uniform : IsDyadicUniform P' m ((1 / 2 : ℝ) ^ q) N' := by
    have h_main' : ∀ (i : ℕ), i < m → ∀ (a b : ℤ),
        (P' ∩ MultiscaleDecomposition.dyadicSquare (((1 / 2 : ℝ) ^ q) ^ i) a b).Nonempty →
        (dyadicSquareCount (((1 / 2 : ℝ) ^ q) ^ (i + 1))
           (P' ∩ MultiscaleDecomposition.dyadicSquare (((1 / 2 : ℝ) ^ q) ^ i) a b) : ENNReal) =
        (↑(N' i) : ENNReal) := by
      intro i hi a b h_nonempty
      have h_pow1 : ((1 / 2 : ℝ) ^ q) ^ i = (1 / 2 : ℝ) ^ (q * i) := by
        rw [←pow_mul] <;> ring
      have h_pow2 : ((1 / 2 : ℝ) ^ q) ^ (i + 1) = (1 / 2 : ℝ) ^ (q * (i + 1)) := by
        rw [←pow_mul] <;> ring
      have h_eq1 : MultiscaleDecomposition.dyadicSquare (((1 / 2 : ℝ) ^ q) ^ i) a b =
          dSquare ((1 / 2 : ℝ) ^ (q * i)) a b := by
        rw [h_pow1] <;> rfl
      have h_nonempty' : (P' ∩ dSquare ((1 / 2 : ℝ) ^ (q * i)) a b).Nonempty := by
        rw [h_eq1] at h_nonempty
        exact h_nonempty
      have h_result := h_main i hi a b h_nonempty'
      have h_eq2 : MultiscaleDecomposition.dyadicSquare (((1 / 2 : ℝ) ^ q) ^ (i + 1)) a b =
          dSquare ((1 / 2 : ℝ) ^ (q * (i + 1))) a b := by
        rw [h_pow2] <;> rfl
      have h_goal : (dyadicSquareCount (((1 / 2 : ℝ) ^ q) ^ (i + 1))
          (P' ∩ MultiscaleDecomposition.dyadicSquare (((1 / 2 : ℝ) ^ q) ^ i) a b) : ENNReal) =
          (↑(N' i) : ENNReal) := by
        have h_eq_scale1 : MultiscaleDecomposition.dyadicSquare (((1 / 2 : ℝ) ^ q) ^ i) a b =
            dSquare ((1 / 2 : ℝ) ^ (q * i)) a b := by
          rw [h_pow1] <;> rfl
        rw [h_pow2, h_eq_scale1]
        exact h_result
      exact h_goal
    have h_base_lt_one : ((1 / 2 : ℝ) ^ q) < 1 := by
      have hq' : q ≠ 0 := by linarith
      exact pow_lt_one₀ (by norm_num) (by norm_num) hq'
    exact ⟨by positivity, h_base_lt_one, hP'_nonempty, hN'_pos, h_main'⟩

  have h_witness : ∀ idx ∈ S'', ∃ x, x ∈ P' ∧ x ∈ dSquare δ_d idx.1 idx.2 := by
    intro idx hidx
    refine ⟨f idx, Set.mem_image_of_mem f hidx, (hf_spec idx hidx).2⟩

  exact ⟨P', hP'_sub, h_uniform, h_witness⟩

/-- Uniformize X by selecting dyadic squares and picking representative points. -/
lemma uniformize_with_representatives
    (s t : ℝ) (Δ : ℝ) (m : ℕ) (hm_pos : 0 < m)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (q : ℕ) (hq_pos : 0 < q) (hΔ_eq : Δ = (1 / 2 : ℝ) ^ q)
    (C ε : ℝ) (hC_pos : 0 < C) (hε_pos : 0 < ε)
    (X : Set EuclideanPlane) (hX_bdd : X ⊆ Metric.closedBall 0 1)
    (hX_sset : IsDeltaSSet (Δ ^ m) t C X)
    (h_budget : C * (48 * Real.log (1 / Δ)) ^ m * 9 ≤ Real.rpow (Δ ^ m) (-ε)) :
    ∃ (P' : Set EuclideanPlane) (N : ℕ → ℕ),
      P' ⊆ X ∧
      IsDyadicUniform P' m Δ N ∧
      Metric.externalCoveringNumber (Δ ^ m).toNNReal X ≤
        ENNReal.ofReal ((48 * Real.log (1 / Δ)) ^ m * 9) *
        Metric.externalCoveringNumber (Δ ^ m).toNNReal P' ∧
      IsDeltaSSet (Δ ^ m) t (Real.rpow (Δ ^ m) (-ε)) P' := by
  let nδ : ℕ := q * m
  let δ_d : ℝ := Δ ^ m
  have hδ_d_pos : 0 < δ_d := by positivity
  have hδ_d_lt_one : δ_d < 1 := by
    have h1 : 0 < m := hm_pos
    exact pow_lt_pow_right_of_lt_one₀ hΔ_pos hΔ_lt_one (by exact_mod_cast h1)
  have hδ_eq : δ_d = dyadicDelta nδ := by
    dsimp only [δ_d, nδ]
    rw [hΔ_eq]
    have h1 : ((1 / 2 : ℝ) ^ q) ^ m = (1 / 2 : ℝ) ^ (q * m) := by
      rw [←pow_mul] <;> ring
    rw [h1]
    have h2 : (1 / 2 : ℝ) ^ (q * m) = dyadicDelta (q * m) := by
      simp [dyadicDelta] <;> field_simp <;> ring
    exact h2
  have hδ_d_eq2 : δ_d = (1 / 2 : ℝ) ^ (q * m) := by
    dsimp only [δ_d]
    rw [hΔ_eq, ←pow_mul] <;> ring

  have hX_bdd' : Bornology.IsBounded X :=
    Metric.isBounded_closedBall.subset hX_bdd

  -- Step 1: Construct dyadic cover X'
  let squares := D_nFinset nδ X hX_bdd'
  let X' : Set EuclideanPlane := ⋃ q ∈ squares, q.toSet

  have hX'_bdd : Bornology.IsBounded X' := by
    have h : ∀ (q : DyadicCube nδ), q ∈ squares → Bornology.IsBounded q.toSet := by
      intro q _
      have h_eq : q.toSet = dSquare δ_d q.i q.j := by
        have h2 := dyadicCube_toSet_eq nδ q
        rw [hδ_eq] at * <;> exact h2
      rw [h_eq]
      exact dyadicSquare_isBounded δ_d hδ_d_pos q.i q.j
    exact (Bornology.isBounded_biUnion_finset (s := squares)).mpr h

  have hX_nonempty : X.Nonempty := hX_sset.1
  have hX'_nonempty : X'.Nonempty := by
    rcases hX_nonempty with ⟨x, hx⟩
    let i : ℤ := Int.floor (x 0 / δ_d)
    let j : ℤ := Int.floor (x 1 / δ_d)
    have hi : (i : ℝ) * δ_d ≤ x 0 := by
      have h : (i : ℝ) ≤ x 0 / δ_d := Int.floor_le (x 0 / δ_d)
      have h' : (i : ℝ) * δ_d ≤ (x 0 / δ_d) * δ_d := by gcongr
      have h'' : (x 0 / δ_d) * δ_d = x 0 := by
        field_simp [hδ_d_pos.ne'] <;> ring
      rw [h''] at h'; exact h'
    have hi2 : x 0 < ((i : ℝ) + 1) * δ_d := by
      have h : x 0 / δ_d < (i : ℝ) + 1 := Int.lt_floor_add_one (x 0 / δ_d)
      have h' : (x 0 / δ_d) * δ_d < ((i : ℝ) + 1) * δ_d := by gcongr
      have h'' : (x 0 / δ_d) * δ_d = x 0 := by
        field_simp [hδ_d_pos.ne'] <;> ring
      rw [h''] at h'; exact h'
    have hj : (j : ℝ) * δ_d ≤ x 1 := by
      have h : (j : ℝ) ≤ x 1 / δ_d := Int.floor_le (x 1 / δ_d)
      have h' : (j : ℝ) * δ_d ≤ (x 1 / δ_d) * δ_d := by gcongr
      have h'' : (x 1 / δ_d) * δ_d = x 1 := by
        field_simp [hδ_d_pos.ne'] <;> ring
      rw [h''] at h'; exact h'
    have hj2 : x 1 < ((j : ℝ) + 1) * δ_d := by
      have h : x 1 / δ_d < (j : ℝ) + 1 := Int.lt_floor_add_one (x 1 / δ_d)
      have h' : (x 1 / δ_d) * δ_d < ((j : ℝ) + 1) * δ_d := by gcongr
      have h'' : (x 1 / δ_d) * δ_d = x 1 := by
        field_simp [hδ_d_pos.ne'] <;> ring
      rw [h''] at h'; exact h'
    let q : DyadicCube nδ := ⟨i, j⟩
    have hxq : x ∈ q.toSet := by
      have h : q.toSet = dSquare δ_d i j := by
        have h2 := dyadicCube_toSet_eq nδ q
        rw [hδ_eq] at * <;> exact h2
      rw [h]
      exact ⟨⟨hi, hi2⟩, ⟨hj, hj2⟩⟩
    have hq_in : q ∈ squares := by
      rw [D_nFinset_mem]
      exact ⟨x, hxq, hx⟩
    exact ⟨x, Set.mem_iUnion₂.mpr ⟨q, hq_in, hxq⟩⟩
  have h_union_squares := dyadic_cover_union_property hδ_eq hX_bdd'

  -- Step 2: Scale array
  let scaleArray : Fin (m + 1) → ℝ := fun i => Δ ^ i.val

  have h_scale_dyadic : ∀ i, scaleArray i ∈ dyadicScales := by
    intro i
    refine' ⟨q * i.val, _⟩
    have h1 : scaleArray i = (2 : ℝ) ^ (-( (q * i.val : ℤ))) := by
      simp [scaleArray, hΔ_eq] <;> rw [←pow_mul] <;> norm_cast
    exact h1

  let a : Fin (m + 1) → ℕ := fun i => Classical.choose (h_scale_dyadic i)
  have ha_spec : ∀ i, scaleArray i = (2 : ℝ) ^ (-( (a i : ℤ))) :=
    fun i => Classical.choose_spec (h_scale_dyadic i)
  have ha_eq : ∀ i, a i = q * i.val := by
    intro i
    have h1 : scaleArray i = (2 : ℝ) ^ (-( (a i : ℤ))) := ha_spec i
    have h2 : scaleArray i = (2 : ℝ) ^ (-( (q * i.val : ℤ))) := by
      simp [scaleArray, hΔ_eq] <;> rw [←pow_mul] <;> norm_cast
    have h_inj : Function.Injective (fun k : ℕ => (2 : ℝ) ^ (-(k : ℤ))) := by
      intro k l h
      simp_all [zpow_neg, zpow_ofNat] <;> norm_cast at * <;> omega
    exact h_inj (h1.symm.trans h2)

  have h_scale_pos : ∀ i, 0 < scaleArray i := by intro i; positivity
  have h_scale_strict : ∀ j : Fin m, scaleArray (Fin.succ j) < scaleArray j.castSucc := by
    intro j
    have h1 : j.val < j.val + 1 := by linarith
    exact pow_lt_pow_right_of_lt_one₀ hΔ_pos hΔ_lt_one h1
  have h_scale_end : scaleArray (Fin.last m) = δ_d := by
    simp [scaleArray] <;> rfl
  have h_scale_start : scaleArray 0 = 1 := by
    simp [scaleArray]

  -- Step 3: Apply basic_uniformization_dyadic
  rcases basic_uniformization_dyadic m hm_pos δ_d hδ_d_pos hδ_d_lt_one nδ hδ_eq
      scaleArray h_scale_dyadic h_scale_pos h_scale_strict h_scale_end h_scale_start
      X' hX'_bdd hX'_nonempty h_union_squares
    with ⟨S', N_range, hS'_sub, h_range, h_density1⟩

  -- Rewrite h_range to use a (since a = Classical.choose)
  have h_range' : RangeUniformityProp m a S' N_range := by
    have h_eq : (fun i : Fin (m + 1) => Classical.choose (h_scale_dyadic i)) = a := by
      funext i; rfl
    rw [h_eq] at h_range
    exact h_range

  -- Step 4: multi_level_thin
  have ha_strict : ∀ j : Fin m, a j.castSucc < a (Fin.succ j) := by
    intro j
    have hq_pos' : 0 < q := hq_pos
    have h1 : a j.castSucc = q * j.val := ha_eq j.castSucc
    have h2 : a (Fin.succ j) = q * (j.val + 1) := ha_eq (Fin.succ j)
    rw [h1, h2]
    exact mul_lt_mul_of_pos_left (by linarith) hq_pos'
  rcases multi_level_thin m a ha_strict S' N_range h_range'
    with ⟨S'', hS''_sub, hS''_nonempty, h_exact, h_density2⟩

  -- Step 5: Each selected square intersects X
  have h_selected_intersect_X : ∀ idx ∈ S'',
      (X ∩ dSquare δ_d idx.1 idx.2).Nonempty := by
    intro idx hidx
    have h_idx_in_S' : idx ∈ S' := hS''_sub hidx
    have h_square_sub : dSquare δ_d idx.1 idx.2 ⊆ setFromIndices δ_d S' := by
      intro x hx
      exact Set.mem_iUnion₂.mpr ⟨idx, h_idx_in_S', hx⟩
    have h_square_sub_X' : dSquare δ_d idx.1 idx.2 ⊆ X' :=
      Set.Subset.trans h_square_sub hS'_sub
    have h_square_nonempty : (dSquare δ_d idx.1 idx.2).Nonempty :=
      dyadicSquare_nonempty hδ_d_pos idx.1 idx.2
    rcases h_square_nonempty with ⟨x, hx_square⟩
    have hx_X' : x ∈ X' := h_square_sub_X' hx_square
    rcases Set.mem_iUnion₂.mp hx_X' with ⟨q, hq, hx_q⟩
    have h_q_square : q.toSet = dSquare δ_d q.i q.j := by
      have h2 := dyadicCube_toSet_eq nδ q
      rw [hδ_eq] at * <;> exact h2
    have h1 : x ∈ dSquare δ_d q.i q.j := by
      rw [←h_q_square]; exact hx_q
    have h_eq_squares : dSquare δ_d idx.1 idx.2 = dSquare δ_d q.i q.j := by
      have h_disj := dyadicSquare_eq_or_disjoint δ_d hδ_d_pos idx.1 idx.2 q.i q.j
      rcases h_disj with (h_eq | h_disj)
      · exact h_eq
      · exfalso
        have h_not_in : x ∉ dSquare δ_d q.i q.j := Set.disjoint_left.mp h_disj hx_square
        exact h_not_in h1
    have h_intersect : (q.toSet ∩ X).Nonempty := by
      rw [D_nFinset_mem] at hq
      exact hq
    rw [h_q_square] at h_intersect
    have h_final : (X ∩ dSquare δ_d idx.1 idx.2).Nonempty := by
      have h5 : (dSquare δ_d q.i q.j ∩ X).Nonempty := h_intersect
      have h6 : dSquare δ_d q.i q.j = dSquare δ_d idx.1 idx.2 := h_eq_squares.symm
      rw [h6] at h5
      have h7 : (dSquare δ_d idx.1 idx.2 ∩ X).Nonempty := h5
      have h8 : (X ∩ dSquare δ_d idx.1 idx.2).Nonempty := by
        rw [Set.inter_comm]
        exact h7
      exact h8
    exact h_final

  -- Step 6: Representative points and IsDyadicUniform
  have hN_range_pos : ∀ (j : Fin m), 1 ≤ N_range j := h_range'.2.1
  rcases rep_points_dyadic_uniform_general hm_pos hq_pos a ha_eq
      S'' hS''_nonempty N_range hN_range_pos h_exact X δ_d hδ_d_eq2 h_selected_intersect_X
    with ⟨P', hP'_sub, h_uniform_raw, h_witness⟩

  let N : ℕ → ℕ := fun i => if h : i < m then N_range ⟨i, h⟩ else 1

  -- Convert Δ = (1/2)^q in IsDyadicUniform
  have h_uniform : IsDyadicUniform P' m Δ N := by
    have hΔ_eq' : Δ = (1 / 2 : ℝ) ^ q := hΔ_eq
    rw [hΔ_eq']
    exact h_uniform_raw

  -- Step 7: Density bound
  have hP'_bdd : Bornology.IsBounded P' :=
    Metric.isBounded_closedBall.subset (Set.Subset.trans hP'_sub hX_bdd)

  -- dyadicCovering(X) ≤ dyadicCovering(X') (monotonicity)
  have hX_sub_X' : X ⊆ X' := by
    intro x hx
    let i : ℤ := Int.floor (x 0 / δ_d)
    let j : ℤ := Int.floor (x 1 / δ_d)
    have hi : (i : ℝ) * δ_d ≤ x 0 := by
      have h : (i : ℝ) ≤ x 0 / δ_d := Int.floor_le (x 0 / δ_d)
      have h' : (i : ℝ) * δ_d ≤ (x 0 / δ_d) * δ_d := by gcongr
      have h'' : (x 0 / δ_d) * δ_d = x 0 := by field_simp [hδ_d_pos.ne'] <;> ring
      rw [h''] at h'; exact h'
    have hi2 : x 0 < ((i : ℝ) + 1) * δ_d := by
      have h : x 0 / δ_d < (i : ℝ) + 1 := Int.lt_floor_add_one (x 0 / δ_d)
      have h' : (x 0 / δ_d) * δ_d < ((i : ℝ) + 1) * δ_d := by gcongr
      have h'' : (x 0 / δ_d) * δ_d = x 0 := by field_simp [hδ_d_pos.ne'] <;> ring
      rw [h''] at h'; exact h'
    have hj : (j : ℝ) * δ_d ≤ x 1 := by
      have h : (j : ℝ) ≤ x 1 / δ_d := Int.floor_le (x 1 / δ_d)
      have h' : (j : ℝ) * δ_d ≤ (x 1 / δ_d) * δ_d := by gcongr
      have h'' : (x 1 / δ_d) * δ_d = x 1 := by field_simp [hδ_d_pos.ne'] <;> ring
      rw [h''] at h'; exact h'
    have hj2 : x 1 < ((j : ℝ) + 1) * δ_d := by
      have h : x 1 / δ_d < (j : ℝ) + 1 := Int.lt_floor_add_one (x 1 / δ_d)
      have h' : (x 1 / δ_d) * δ_d < ((j : ℝ) + 1) * δ_d := by gcongr
      have h'' : (x 1 / δ_d) * δ_d = x 1 := by field_simp [hδ_d_pos.ne'] <;> ring
      rw [h''] at h'; exact h'
    let q : DyadicCube nδ := ⟨i, j⟩
    have hxq : x ∈ q.toSet := by
      have h : q.toSet = dSquare δ_d i j := by
        have h2 := dyadicCube_toSet_eq nδ q
        rw [hδ_eq] at * <;> exact h2
      rw [h]
      exact ⟨⟨hi, hi2⟩, ⟨hj, hj2⟩⟩
    have hq_in : q ∈ squares := by
      rw [D_nFinset_mem] <;> exact ⟨x, hxq, hx⟩
    exact Set.mem_iUnion₂.mpr ⟨q, hq_in, hxq⟩

  have h_dyadic_X_le_X' : (DyadicCubes.dyadicCoveringNumber nδ X hX_bdd' : ℝ) ≤
      (DyadicCubes.dyadicCoveringNumber nδ X' hX'_bdd : ℝ) := by
    have h_sub : D_nFinset nδ X hX_bdd' ⊆ D_nFinset nδ X' hX'_bdd := by
      intro q hq
      rw [D_nFinset_mem] at hq ⊢
      rcases hq with ⟨x, hxq, hxX⟩
      exact ⟨x, hxq, hX_sub_X' hxX⟩
    exact_mod_cast Finset.card_le_card h_sub

  -- count_eq_card for S' and density from basic_uniformization
  have h_bddδ : Bornology.IsBounded (setFromIndices δ_d S') := by
    have h1 : setFromIndices δ_d S' = setFromIndices (dyadicDelta nδ) S' := by rw [hδ_eq]
    rw [h1]
    exact setFromIndices_isBounded nδ S'
  have h_count_general : ∀ (h : Bornology.IsBounded (setFromIndices δ_d S')),
      DyadicCubes.dyadicCoveringNumber nδ (setFromIndices δ_d S') h = S'.card := by
    intro h
    have h1 : setFromIndices δ_d S' = setFromIndices (dyadicDelta nδ) S' := by rw [hδ_eq]
    have h_general : ∀ (X Y : Set EuclideanPlane) (hX : Bornology.IsBounded X) (hY : Bornology.IsBounded Y),
        X = Y → DyadicCubes.dyadicCoveringNumber nδ X hX = DyadicCubes.dyadicCoveringNumber nδ Y hY := by
      intro X Y hX hY hXY
      subst hXY <;> rfl
    have h_eq2 := h_general (setFromIndices δ_d S') (setFromIndices (dyadicDelta nδ) S') h (setFromIndices_isBounded nδ S') h1
    rw [h_eq2]
    exact count_eq_card nδ S' h_range'.1

  -- Density from basic_uniformization
  have h_log_eq : Real.log (1 / δ_d) = (m : ℝ) * Real.log (1 / Δ) := by
    have h1 : 1 / δ_d = (1 / Δ) ^ m := by
      dsimp only [δ_d]
      rw [←one_pow m, ←div_pow] <;> ring
    rw [h1, Real.log_pow] <;> ring
  let D_unif : ℝ := (24 * Real.log (1 / δ_d) / (m : ℝ)) ^ m
  have h_log_pos : 0 < Real.log (1 / δ_d) := by
    apply Real.log_pos
    have h : 1 < 1 / δ_d := by
      apply one_lt_one_div
      <;> linarith
    exact h
  have hD_unif_pos : 0 < D_unif := by
    dsimp only [D_unif]
    have h1 : 0 < 24 * Real.log (1 / δ_d) / (m : ℝ) := by positivity
    positivity
  have hD_unif_eq : D_unif = (24 * Real.log (1 / Δ)) ^ m := by
    dsimp only [D_unif]
    rw [h_log_eq]
    have h2 : (24 * ((m : ℝ) * Real.log (1 / Δ)) / (m : ℝ)) = 24 * Real.log (1 / Δ) := by
      field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hm_pos.ne'] <;> ring
    rw [h2]

  have h_density1' : (DyadicCubes.dyadicCoveringNumber nδ X' hX'_bdd : ℝ) ≤
      D_unif * (S'.card : ℝ) := by
    have h : (S'.card : ℝ) ≥ (DyadicCubes.dyadicCoveringNumber nδ X' hX'_bdd : ℝ) / D_unif := by
      convert h_density1
      · exact (h_count_general _).symm
    have hpos : 0 < D_unif := hD_unif_pos
    have h_eq : D_unif * ((DyadicCubes.dyadicCoveringNumber nδ X' hX'_bdd : ℝ) / D_unif) =
        (DyadicCubes.dyadicCoveringNumber nδ X' hX'_bdd : ℝ) := by
      field_simp [hpos.ne'] <;> ring
    have h'' : (DyadicCubes.dyadicCoveringNumber nδ X' hX'_bdd : ℝ) ≤ D_unif * (S'.card : ℝ) := by
      calc (DyadicCubes.dyadicCoveringNumber nδ X' hX'_bdd : ℝ)
        = D_unif * ((DyadicCubes.dyadicCoveringNumber nδ X' hX'_bdd : ℝ) / D_unif) := h_eq.symm
      _ ≤ D_unif * (S'.card : ℝ) := by gcongr
    exact h''

  -- Density from multi_level_thin: S'.card ≤ 2^m * S''.card
  have h_density2' : (S'.card : ℝ) ≤ (2 : ℝ)^m * (S''.card : ℝ) := by
    have h := h_density2
    linarith

  -- Combined: dyadic(X) ≤ D_unif * 2^m * S''.card
  have h_dyadic_X_le : (DyadicCubes.dyadicCoveringNumber nδ X hX_bdd' : ℝ) ≤
      D_unif * (2 : ℝ)^m * (S''.card : ℝ) := by
    have hD_nonneg : 0 ≤ D_unif := le_of_lt hD_unif_pos
    calc (DyadicCubes.dyadicCoveringNumber nδ X hX_bdd' : ℝ)
      ≤ (DyadicCubes.dyadicCoveringNumber nδ X' hX'_bdd : ℝ) := h_dyadic_X_le_X'
    _ ≤ D_unif * (S'.card : ℝ) := h_density1'
    _ ≤ D_unif * ((2 : ℝ)^m * (S''.card : ℝ)) := by
      gcongr
      <;> exact_mod_cast h_density2'
    _ = D_unif * (2 : ℝ)^m * (S''.card : ℝ) := by ring

  -- S''.card ≤ dyadicCovering(P')
  have hS''_le_dyadic_P' : (S''.card : ℕ) ≤
      DyadicCubes.dyadicCoveringNumber nδ P' hP'_bdd := by
    let f_map : (ℤ × ℤ) → DyadicCube nδ := fun p => ⟨p.1, p.2⟩
    have h_inj : Set.InjOn f_map S'' := by
      intro p1 _ p2 _ h
      simpa [f_map] using congr_arg (fun (q : DyadicCube nδ) => (q.i, q.j)) h
    have h_sub : S''.image f_map ⊆ D_nFinset nδ P' hP'_bdd := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨idx, hidx, rfl⟩
      rcases h_witness idx hidx with ⟨x, hxP', hxSquare⟩
      have h3 : x ∈ (f_map idx).toSet := by
        have h4 : (f_map idx).toSet = dSquare δ_d idx.1 idx.2 := by
          have h5 := dyadicCube_toSet_eq nδ (f_map idx)
          rw [hδ_eq] at * <;> exact h5
        rw [h4]; exact hxSquare
      have h1 : ((f_map idx).toSet ∩ P').Nonempty := ⟨x, h3, hxP'⟩
      rw [D_nFinset_mem] <;> exact h1
    have h_card : (S''.image f_map).card = S''.card :=
      Finset.card_image_of_injOn h_inj
    rw [←h_card]
    exact Finset.card_le_card h_sub

  -- Convert to ENNReal and apply comparability
  have h_final_factor : D_unif * (2 : ℝ)^m * 9 = (48 * Real.log (1 / Δ)) ^ m * 9 := by
    rw [hD_unif_eq]
    have h3 : (24 * Real.log (1 / Δ)) ^ m * (2 : ℝ)^m = (48 * Real.log (1 / Δ)) ^ m := by
      have h4 : (24 * Real.log (1 / Δ)) ^ m * (2 : ℝ)^m =
          ((24 * Real.log (1 / Δ)) * 2) ^ m := by rw [←mul_pow] <;> ring
      rw [h4]
      have h5 : (24 * Real.log (1 / Δ)) * 2 = 48 * Real.log (1 / Δ) := by ring
      rw [h5]
    rw [h3] <;> ring

  have hδ_toNNReal : δ_d.toNNReal = (dyadicDelta nδ).toNNReal := by
    rw [hδ_eq]

  have h_density_final : Metric.externalCoveringNumber δ_d.toNNReal X ≤
      ENNReal.ofReal ((48 * Real.log (1 / Δ)) ^ m * 9) *
      Metric.externalCoveringNumber δ_d.toNNReal P' := by
    have h_comp_X := (dyadicCoveringNumber_comparable nδ hX_bdd').1
    have h_comp_P' := (dyadicCoveringNumber_comparable nδ hP'_bdd).2
    have h_step1 : (Metric.externalCoveringNumber δ_d.toNNReal X : ENNReal) ≤
        (↑(DyadicCubes.dyadicCoveringNumber nδ X hX_bdd') : ENNReal) := by
      rw [hδ_toNNReal]
      exact_mod_cast h_comp_X
    have h_step2 : (↑(DyadicCubes.dyadicCoveringNumber nδ X hX_bdd') : ENNReal) ≤
        ENNReal.ofReal (D_unif * (2 : ℝ)^m) * ↑(S''.card) := by
      have h_real : (DyadicCubes.dyadicCoveringNumber nδ X hX_bdd' : ℝ) ≤
          (D_unif * (2 : ℝ)^m) * (S''.card : ℝ) := h_dyadic_X_le
      have h1 : 0 ≤ D_unif * (2 : ℝ)^m := by
        have h1a : 0 < D_unif := hD_unif_pos
        have h1b : 0 < (2 : ℝ)^m := by positivity
        exact le_of_lt (mul_pos h1a h1b)
      have h2 : 0 ≤ (S''.card : ℝ) := Nat.cast_nonneg S''.card
      have h3 : 0 ≤ (D_unif * (2 : ℝ)^m) * (S''.card : ℝ) := mul_nonneg h1 h2
      have h4 : ENNReal.ofReal (↑(DyadicCubes.dyadicCoveringNumber nδ X hX_bdd') : ℝ) ≤
          ENNReal.ofReal ((D_unif * (2 : ℝ)^m) * (S''.card : ℝ)) :=
        ENNReal.ofReal_le_ofReal h_real
      have h5 : ENNReal.ofReal (↑(DyadicCubes.dyadicCoveringNumber nδ X hX_bdd') : ℝ) =
          (↑(DyadicCubes.dyadicCoveringNumber nδ X hX_bdd') : ENNReal) := by
        norm_cast
      have h6 : ENNReal.ofReal ((D_unif * (2 : ℝ)^m) * (S''.card : ℝ)) =
          ENNReal.ofReal (D_unif * (2 : ℝ)^m) * ENNReal.ofReal (↑(S''.card) : ℝ) := by
        rw [←ENNReal.ofReal_mul] <;> assumption
      have h7 : ENNReal.ofReal (↑(S''.card) : ℝ) = (↑(S''.card) : ENNReal) := by
        norm_cast
      rw [h5, h6, h7] at h4
      exact h4
    have h_step3 : (↑(S''.card) : ENNReal) ≤
        (↑(DyadicCubes.dyadicCoveringNumber nδ P' hP'_bdd) : ENNReal) := by
      exact_mod_cast hS''_le_dyadic_P'
    have h_step4 : (↑(DyadicCubes.dyadicCoveringNumber nδ P' hP'_bdd) : ENNReal) ≤
        (9 : ENNReal) * (Metric.externalCoveringNumber δ_d.toNNReal P' : ENNReal) := by
      have h_comp_P'2 := h_comp_P'
      rw [←hδ_toNNReal] at h_comp_P'2
      exact_mod_cast h_comp_P'2
    have h_pos_mul : 0 ≤ D_unif * (2 : ℝ)^m := by
      have h1a : 0 < D_unif := hD_unif_pos
      have h1b : 0 < (2 : ℝ)^m := by positivity
      exact le_of_lt (mul_pos h1a h1b)
    have h6 : ENNReal.ofReal (D_unif * (2 : ℝ)^m) * (9 : ENNReal) =
        ENNReal.ofReal ((48 * Real.log (1 / Δ)) ^ m * 9) := by
      have h9 : (9 : ENNReal) = ENNReal.ofReal (9 : ℝ) := by norm_cast
      have h7 : ENNReal.ofReal (D_unif * (2 : ℝ)^m) * (9 : ENNReal) =
          ENNReal.ofReal ((D_unif * (2 : ℝ)^m) * 9) := by
        rw [h9]
        rw [←ENNReal.ofReal_mul]
        <;> exact h_pos_mul
      rw [h7, h_final_factor]
    calc (Metric.externalCoveringNumber δ_d.toNNReal X : ENNReal)
      ≤ (↑(DyadicCubes.dyadicCoveringNumber nδ X hX_bdd') : ENNReal) := h_step1
    _ ≤ ENNReal.ofReal (D_unif * (2 : ℝ)^m) * ↑(S''.card) := h_step2
    _ ≤ ENNReal.ofReal (D_unif * (2 : ℝ)^m) * (↑(DyadicCubes.dyadicCoveringNumber nδ P' hP'_bdd) : ENNReal) := by gcongr
    _ ≤ ENNReal.ofReal (D_unif * (2 : ℝ)^m) * ((9 : ENNReal) * (Metric.externalCoveringNumber δ_d.toNNReal P' : ENNReal)) := by gcongr
    _ = (ENNReal.ofReal (D_unif * (2 : ℝ)^m) * (9 : ENNReal)) * (Metric.externalCoveringNumber δ_d.toNNReal P' : ENNReal) := by ring
    _ = ENNReal.ofReal ((48 * Real.log (1 / Δ)) ^ m * 9) * (Metric.externalCoveringNumber δ_d.toNNReal P' : ENNReal) := by rw [h6]

  -- Step 8: S-set property
  have h_sset_P' : IsDeltaSSet δ_d t (Real.rpow δ_d (-ε)) P' := by
    have hP'_nonempty : P'.Nonempty := h_uniform.2.2.1
    have hδ_pos' : 0 < δ_d := hδ_d_pos
    have hC'_pos : 0 < Real.rpow δ_d (-ε) := Real.rpow_pos_of_pos hδ_d_pos (-ε)
    have ht_nonneg : 0 ≤ t := hX_sset.2.2.2.1
    let D : ℝ := (48 * Real.log (1 / Δ)) ^ m * 9
    have h_log_pos2 : 0 < Real.log (1 / Δ) := by
      apply Real.log_pos
      have h : 1 < 1 / Δ := by
        apply one_lt_one_div hΔ_pos
        exact hΔ_lt_one
      exact h
    have hD_pos : 0 < D := by
      dsimp only [D]
      have h1 : 0 < (48 * Real.log (1 / Δ)) ^ m := by positivity
      positivity
    have h_budget' : C * D ≤ Real.rpow δ_d (-ε) := by
      dsimp only [D, δ_d]
      have h_assoc : C * ((48 * Real.log (1 / Δ)) ^ m * 9) = C * (48 * Real.log (1 / Δ)) ^ m * 9 := by ring
      rw [h_assoc]
      exact h_budget
    have h_main : ∀ (x : EuclideanPlane) (r : ℝ), δ_d ≤ r →
        (Metric.externalCoveringNumber δ_d.toNNReal (P' ∩ Metric.closedBall x r) : ENNReal) ≤
          ENNReal.ofReal (Real.rpow δ_d (-ε)) * (ENNReal.ofReal r) ^ t *
            (Metric.externalCoveringNumber δ_d.toNNReal P' : ENNReal) := by
      intro x r hr
      have h1 : P' ∩ Metric.closedBall x r ⊆ X ∩ Metric.closedBall x r := by
        intro y hy
        exact ⟨hP'_sub hy.1, hy.2⟩
      have h2 : (Metric.externalCoveringNumber δ_d.toNNReal (P' ∩ Metric.closedBall x r) : ENNReal) ≤
          (Metric.externalCoveringNumber δ_d.toNNReal (X ∩ Metric.closedBall x r) : ENNReal) := by
        exact_mod_cast Metric.externalCoveringNumber_mono_set h1
      have h3 := hX_sset.2.2.2.2 x r hr
      have h4 : (Metric.externalCoveringNumber δ_d.toNNReal (X ∩ Metric.closedBall x r) : ENNReal) ≤
          ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (Metric.externalCoveringNumber δ_d.toNNReal X : ENNReal) := by
        exact_mod_cast h3
      have h5 : (Metric.externalCoveringNumber δ_d.toNNReal X : ENNReal) ≤
          ENNReal.ofReal D * (Metric.externalCoveringNumber δ_d.toNNReal P' : ENNReal) := by
        simpa [D] using h_density_final
      have h6 : ENNReal.ofReal C * ENNReal.ofReal D = ENNReal.ofReal (C * D) := by
        rw [←ENNReal.ofReal_mul (by positivity)]
      calc (Metric.externalCoveringNumber δ_d.toNNReal (P' ∩ Metric.closedBall x r) : ENNReal)
        ≤ (Metric.externalCoveringNumber δ_d.toNNReal (X ∩ Metric.closedBall x r) : ENNReal) := h2
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (Metric.externalCoveringNumber δ_d.toNNReal X : ENNReal) := h4
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (ENNReal.ofReal D * (Metric.externalCoveringNumber δ_d.toNNReal P' : ENNReal)) := by gcongr
      _ = (ENNReal.ofReal C * ENNReal.ofReal D) * (ENNReal.ofReal r) ^ t * (Metric.externalCoveringNumber δ_d.toNNReal P' : ENNReal) := by ring
      _ = ENNReal.ofReal (C * D) * (ENNReal.ofReal r) ^ t * (Metric.externalCoveringNumber δ_d.toNNReal P' : ENNReal) := by rw [h6] <;> ring
      _ ≤ ENNReal.ofReal (Real.rpow δ_d (-ε)) * (ENNReal.ofReal r) ^ t * (Metric.externalCoveringNumber δ_d.toNNReal P' : ENNReal) := by
        gcongr <;> exact_mod_cast h_budget'
    exact ⟨hP'_nonempty, hδ_pos', hC'_pos, ht_nonneg, h_main⟩

  have h_sset_final : IsDeltaSSet (Δ ^ m) t (Real.rpow (Δ ^ m) (-ε)) P' := by
    exact h_sset_P'

  exact ⟨P', N, hP'_sub, h_uniform, h_density_final, h_sset_final⟩

end DirecretisedFurstenbergEstimate.Section9Assembly

end
