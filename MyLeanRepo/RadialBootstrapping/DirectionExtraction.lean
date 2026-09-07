module

/-
  DirectionExtraction.lean

  Extract a direction-separated family of lines from a measure-theoretic fiber.

  Main result:
  - `direction_separated_extraction`

  Proof route (greedy selection):
  1. Partition direction angles [0, π] into N intervals of half-width α = δ/8.
  2. For each non-empty class, pick representative x_j and reference line L_j
     through y parallel to ℓ x_j.
  3. Apply greedy_selection_finite to {L_j} to get δ-separated, δ-covering T_ref.
  4. For each selected L', every x in classes covered by L' has direction within
     δ + 2α = 5δ/4 of L'.
  5. Geometric lemma places such x in tube_{r+(D+r)*5δ/4}(L').
  6. Reverse thin-tubes gives each cluster measure ≤ K·W_greedy^σ.
  7. Subadditivity: mass ≤ |T_ref|·K·W_greedy^σ.
  8. Ratio W_greedy / W_thm < 10, so W_greedy^σ ≤ 15·W_thm^σ (σ ≤ 1).
  9. Map T_ref back to original lines; cardinality and separation preserved.
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.GreedySelection

@[expose] public section

open MeasureTheory Metric Set Finset


noncomputable section

namespace RadialBootstrapping

/-! 1. Geometric lemma -/

lemma point_in_wider_tube
    {r D d : ℝ} (hr : 0 < r) (hD : 0 ≤ D) (hd : 0 ≤ d)
    (y x : Point) (L ℓ : AffineSubspace ℝ Point)
    (V W : Submodule ℝ Point)
    (hV : V = L.direction) (hW : W = ℓ.direction)
    (hyL : y ∈ (L : Set Point))
    (hxℓ : x ∈ (ℓ : Set Point))
    (hytube : y ∈ Metric.thickening r (ℓ : Set Point))
    (hD_bound : dist x y ≤ D)
    (hdir : submoduleDirDist V W ≤ d) :
    x ∈ Metric.thickening (r + (D + r) * d) (L : Set Point) := by
  rcases Metric.mem_thickening_iff.mp hytube with ⟨z, hzℓ, hdist_yz⟩
  have hxz_in_W : x - z ∈ W := by
    rw [hW]; exact AffineSubspace.vsub_mem_direction hxℓ hzℓ
  have h_proj_id : W.starProjection (x - z) = x - z :=
    Submodule.starProjection_eq_self_iff.mpr hxz_in_W
  have h1 : (x - z) - V.starProjection (x - z) = (W.starProjection - V.starProjection) (x - z) := by
    have h2 : (W.starProjection - V.starProjection) (x - z) = W.starProjection (x - z) - V.starProjection (x - z) := by
      exact sub_apply W.starProjection V.starProjection (x - z)
    rw [h2, h_proj_id] <;> abel
  have h_perp_xz : ‖(x - z) - V.starProjection (x - z)‖ ≤ d * ‖x - z‖ := by
    rw [h1]
    have h3 : ‖(W.starProjection - V.starProjection) (x - z)‖ ≤ ‖W.starProjection - V.starProjection‖ * ‖x - z‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h4 : ‖W.starProjection - V.starProjection‖ = submoduleDirDist V W := by
      have h5 : submoduleDirDist V W = ‖V.starProjection - W.starProjection‖ := by
        simp [submoduleDirDist, submoduleProj_eq_starProjection] <;> rfl
      have h6 : ‖W.starProjection - V.starProjection‖ = ‖V.starProjection - W.starProjection‖ := by
        rw [show W.starProjection - V.starProjection = -(V.starProjection - W.starProjection) by ext x; simp <;> abel]
        rw [norm_neg]
      rw [h6, h5]
    rw [h4] at h3
    exact le_trans h3 (mul_le_mul_of_nonneg_right hdir (by positivity))
  set q := (z - y) - V.starProjection (z - y) with hq_def
  have h_norm_sq : ‖z - y‖ ^ 2 = ‖q‖ ^ 2 + ‖V.starProjection (z - y)‖ ^ 2 := by
    have h := V.orthogonalProjectionFn_norm_sq (z - y)
    have h' : ‖z - y‖ * ‖z - y‖ = ‖q‖ * ‖q‖ + ‖V.starProjection (z - y)‖ * ‖V.starProjection (z - y)‖ := by
      simpa [hq_def] using h
    have h1 : ‖z - y‖ * ‖z - y‖ = ‖z - y‖ ^ 2 := by ring
    have h2 : ‖q‖ * ‖q‖ = ‖q‖ ^ 2 := by ring
    have h3 : ‖V.starProjection (z - y)‖ * ‖V.starProjection (z - y)‖ = ‖V.starProjection (z - y)‖ ^ 2 := by ring
    rw [h1, h2, h3] at h'; exact h'
  have h_perp_zy : ‖q‖ ≤ ‖z - y‖ := by
    have h4 : ‖q‖ ^ 2 ≤ ‖z - y‖ ^ 2 := by rw [h_norm_sq] <;> nlinarith
    nlinarith [norm_nonneg q, norm_nonneg (z - y)]
  have h_dist_xz : ‖x - z‖ ≤ D + r := by
    calc ‖x - z‖ = dist x z := by rfl
      _ ≤ dist x y + dist y z := dist_triangle _ _ _
      _ ≤ D + r := by linarith [dist_comm y z]
  have h_zy_lt_r : ‖z - y‖ < r := by
    have h : ‖y - z‖ < r := by simpa [dist_eq_norm] using hdist_yz
    have h' : ‖z - y‖ = ‖y - z‖ := by rw [norm_sub_rev]
    rw [h'] <;> exact h
  have h_main : ‖(x - y) - V.starProjection (x - y)‖ < r + (D + r) * d := by
    have h6 : V.starProjection (x - y) = V.starProjection (x - z) + V.starProjection (z - y) := by
      rw [show x - y = (x - z) + (z - y) by abel]
      exact V.starProjection.map_add _ _
    have h5 : (x - y) - V.starProjection (x - y) = ((x - z) - V.starProjection (x - z)) + q := by
      rw [h6, hq_def] <;> abel
    rw [h5]
    have h_sum : ‖((x - z) - V.starProjection (x - z)) + q‖ ≤ ‖(x - z) - V.starProjection (x - z)‖ + ‖q‖ := norm_add_le _ _
    have h_strict : ‖(x - z) - V.starProjection (x - z)‖ + ‖q‖ < r + (D + r) * d := by
      calc ‖(x - z) - V.starProjection (x - z)‖ + ‖q‖
        ≤ d * ‖x - z‖ + ‖z - y‖ := by gcongr <;> exact h_perp_zy
      _ ≤ d * (D + r) + ‖z - y‖ := by gcongr
      _ < d * (D + r) + r := by gcongr
      _ = r + (D + r) * d := by ring
    exact lt_of_le_of_lt h_sum h_strict
  letI : Nonempty (L : Set Point) := ⟨⟨y, hyL⟩⟩
  have h_ortho_proj : (EuclideanGeometry.orthogonalProjection L x : Point) = y + V.starProjection (x - y) := by
    have h9 := EuclideanGeometry.orthogonalProjection_apply_mem (s := L) (p := x) (x := y) hyL
    have h10 : (EuclideanGeometry.orthogonalProjection L x : Point) = V.starProjection (x - y) + y := by
      simpa [hV, vadd_eq_add] using h9
    rw [h10] <;> abel
  have h_nonempty_L : (L : Set Point).Nonempty := ⟨y, hyL⟩
  have h_dist_to_L : infDist x (L : Set Point) = ‖(x - y) - V.starProjection (x - y)‖ := by
    have h7 : dist x (EuclideanGeometry.orthogonalProjection L x) = infDist x (L : Set Point) :=
      EuclideanGeometry.dist_orthogonalProjection_eq_infDist L x
    have h8 : dist x (EuclideanGeometry.orthogonalProjection L x) = ‖x - (EuclideanGeometry.orthogonalProjection L x : Point)‖ := by
      simp [dist_eq_norm]
    rw [←h7, h8, h_ortho_proj] <;> abel_nf
  have h9 : infDist x (L : Set Point) < r + (D + r) * d := by
    rw [h_dist_to_L] <;> exact h_main
  have h10 : ∃ (z' : Point), z' ∈ (L : Set Point) ∧ dist x z' < r + (D + r) * d :=
    (Metric.infDist_lt_iff h_nonempty_L).mp h9
  rcases h10 with ⟨z', hz', hdist⟩
  exact Metric.mem_thickening_iff.mpr ⟨z', hz', hdist⟩

/-! 2. Main extraction lemma -/

/-- Extract a direction-separated family of affine lines from a measure-theoretic fiber.

Given `X_y` with mass `mass`, where each `x ∈ X_y` has a line `ℓ x` through x with y in its r-tube,
extract a finite family S of lines such that:
- Each line comes from some x ∈ X_y
- y is in the r-tube of each line
- Lines are direction-separated by δ
- |S| ≥ mass / (15 * K * W^σ) where W = r + (D+r)*δ/8

Uses angle partitioning, greedy selection, and reverse thin-tube bounds. -/
lemma direction_separated_extraction
    {ν₁ : Measure Point} [IsProbabilityMeasure ν₁]
    (G : Set (Point × Point))
    (K σ r ξ D δ mass : ℝ)
    (hσ : 0 ≤ σ) (hσ_le_one : σ ≤ 1)
    (hr : 0 < r) (hξ : 0 < ξ) (hD : 0 ≤ D)
    (hK : 1 ≤ K) (hmass : 0 ≤ mass)
    (hδ : δ = r / ξ) (hδ_pos : 0 < δ)
    (y : Point)
    (X_y : Set Point)
    (hX_y_mass : ν₁ X_y ≥ ENNReal.ofReal mass)
    (ℓ : Point → AffineSubspace ℝ Point)
    (hℓ1 : ∀ x ∈ X_y, x ∈ (ℓ x : Set Point))
    (hℓ2 : ∀ x ∈ X_y, Module.finrank ℝ (ℓ x).direction = 1)
    (h_y_in_tube : ∀ x ∈ X_y, y ∈ Metric.thickening r ((ℓ x) : Set Point))
    (h_in_G : ∀ x ∈ X_y, (x, y) ∈ G)
    (h_bounded : ∀ x ∈ X_y, dist x y ≤ D)
    (hG_reverse : ∀ (ℓ' : AffineSubspace ℝ Point), y ∈ (ℓ' : Set Point) →
        Module.finrank ℝ ℓ'.direction = 1 → ∀ r' : ℝ, 0 < r' →
          ν₁ {b₁ | b₁ ∈ Metric.thickening r' (ℓ' : Set Point) ∧ (b₁, y) ∈ G} ≤
            ENNReal.ofReal (K * Real.rpow r' σ)) :
    ∃ (S : Finset (AffineSubspace ℝ Point)),
      (∀ L ∈ S, ∃ x ∈ X_y, L = ℓ x) ∧
      (∀ L ∈ S, y ∈ Metric.thickening r (L : Set Point)) ∧
      (∀ L1 ∈ S, ∀ L2 ∈ S, L1 ≠ L2 → submoduleDirDist L1.direction L2.direction ≥ δ) ∧
      (S.card : ℝ) ≥ mass / (15 * K * Real.rpow (r + (D + r) * (δ / 8)) σ) ∧
      (∀ (x : Point), x ∈ X_y → ∃ L ∈ S,
        submoduleDirDist (ℓ x).direction L.direction ≤ 5 * δ / 4) := by
  classical
  by_cases hXy_empty : X_y = ∅
  · -- X_y is empty → mass must be 0, conclusion trivial
    have h_mass_zero : mass = 0 := by
      rw [hXy_empty] at hX_y_mass
      have h1 : ν₁ (∅ : Set Point) = 0 := measure_empty
      rw [h1] at hX_y_mass
      have h2 : ENNReal.ofReal mass ≤ 0 := hX_y_mass
      have h3 : ENNReal.ofReal mass = 0 := by simpa using h2
      have h4 : mass ≤ 0 := ENNReal.ofReal_eq_zero.mp h3
      linarith [hmass]
    refine ⟨∅, by simp, by simp, by simp, ?_, ?_⟩
    · rw [h_mass_zero] <;> simp
    · intro x hx
      rw [hXy_empty] at hx
      simpa using hx
  · -- X_y is non-empty → main proof
    have hXy_nonempty : X_y.Nonempty := Set.nonempty_iff_ne_empty.mpr hXy_empty
    let α : ℝ := δ / 8
    have hα_pos : 0 < α := by positivity
    let N : ℕ := Nat.ceil (Real.pi / α) + 1
    have hN_cover : (N : ℝ) * α ≥ Real.pi := by
      have h1 : (N : ℝ) ≥ Real.pi / α + 1 := by
        simp [N] <;> linarith [Nat.le_ceil (Real.pi / α)]
      calc (N : ℝ) * α ≥ (Real.pi / α + 1) * α := by gcongr
        _ = Real.pi + α := by field_simp [hα_pos.ne'] <;> ring
        _ ≥ Real.pi := by linarith

    let refAngle (j : ℕ) : ℝ := (j : ℝ) * α

    -- Angle cover: for any φ ∈ [0, π], exists j < N with |φ - j*α| ≤ α
    have h_cover_angle : ∀ (φ : ℝ), 0 ≤ φ → φ ≤ Real.pi →
        ∃ j ∈ Finset.range N, |φ - refAngle j| ≤ α := by
      intro φ hφ1 hφ2
      let j0 : ℕ := Nat.floor (φ / α)
      have h_nonneg : 0 ≤ φ / α := by positivity
      have h_j0_le : (j0 : ℝ) ≤ φ / α := Nat.floor_le h_nonneg
      have h_j0_lt_N : j0 < N := by
        have h : (j0 : ℝ) ≤ φ / α := h_j0_le
        have h2 : φ / α + 1 ≤ (N : ℝ) := by
          have h3 : φ ≤ Real.pi := hφ2
          have h4 : (N : ℝ) ≥ Real.pi / α + 1 := by
            simp [N] <;> linarith [Nat.le_ceil (Real.pi / α)]
          have h5 : φ / α ≤ Real.pi / α := by
            apply div_le_div_of_nonneg_right h3 (by positivity)
          linarith
        have h5 : (j0 : ℝ) < (N : ℝ) := by linarith
        exact_mod_cast h5
      refine ⟨j0, Finset.mem_range.mpr h_j0_lt_N, ?_⟩
      have h6 : (j0 : ℝ) * α ≤ φ := by
        calc (j0 : ℝ) * α ≤ (φ / α) * α := by gcongr
          _ = φ := by field_simp [hα_pos.ne'] <;> ring
      have h7 : φ < ((j0 : ℝ) + 1) * α := by
        have h8 : φ / α < (j0 : ℝ) + 1 := Nat.lt_floor_add_one (φ / α)
        have h9 : φ < ((j0 : ℝ) + 1) * α := by
          calc φ = (φ / α) * α := by field_simp [hα_pos.ne'] <;> ring
            _ < ((j0 : ℝ) + 1) * α := by gcongr
        exact h9
      rw [abs_le] <;> constructor <;> linarith

    let X_class (j : ℕ) : Set Point :=
      {x : Point | ∃ (h : x ∈ X_y), |directionAngle (ℓ x).direction (hℓ2 x h) - refAngle j| ≤ α}

    have h_cover_X : X_y ⊆ ⋃ j ∈ Finset.range N, X_class j := by
      intro x hx
      let φ := directionAngle (ℓ x).direction (hℓ2 x hx)
      have hφ1 : 0 ≤ φ := (directionAngle_range _ _).1
      have hφ2 : φ ≤ Real.pi := (directionAngle_range _ _).2
      rcases h_cover_angle φ hφ1 hφ2 with ⟨j, hj_in, h_abs⟩
      have h_in_class : x ∈ X_class j := by
        simp only [X_class, Set.mem_setOf_eq]
        exact ⟨hx, h_abs⟩
      have h : x ∈ (⋃ j ∈ Finset.range N, X_class j) := by
        exact Set.mem_iUnion₂.mpr ⟨j, hj_in, h_in_class⟩
      exact h

    let active : Finset ℕ := (Finset.range N).filter (fun j => (X_class j).Nonempty)
    have h_active_sub : active ⊆ Finset.range N := Finset.filter_subset _ _

    have h_active_nonempty : active.Nonempty := by
      by_contra h
      have h' : active = ∅ := by simpa using h
      have h_empty : ∀ j ∈ Finset.range N, X_class j = ∅ := by
        intro j hj
        have h2 : j ∉ active := by rw [h']; simp
        have h3 : ¬(X_class j).Nonempty := by
          have h4 : j ∈ Finset.range N := hj
          simpa [active, Finset.mem_filter, h4] using h2
        exact Set.not_nonempty_iff_eq_empty.mp h3
      have h4 : (⋃ j ∈ Finset.range N, X_class j) = ∅ := by
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        intro h
        rcases Set.mem_iUnion₂.mp h with ⟨j, hj, hxj⟩
        have h_empty_j : X_class j = ∅ := h_empty j hj
        rw [h_empty_j] at hxj
        simpa using hxj
      have h5 : X_y ⊆ (∅ : Set Point) := by rw [←h4]; exact h_cover_X
      have h6 : X_y = ∅ := by simpa using h5
      exact hXy_empty h6

    -- Pick representative for each active class
    choose x_j hxj using fun (j : ℕ) (hj : (X_class j).Nonempty) => hj

    -- Helper: extract Nonempty proof from active membership
    have hne_of_active : ∀ (j : ℕ), j ∈ active → (X_class j).Nonempty := by
      intro j hj
      have h : j ∈ Finset.range N ∧ (X_class j).Nonempty := by
        simpa [active, Finset.mem_filter] using hj
      exact h.2

    -- Reference line through y, parallel to ℓ(x_j)
    let refLine (j : ℕ) (hj : j ∈ active) : AffineSubspace ℝ Point :=
      AffineSubspace.mk' y (ℓ (x_j j (hne_of_active j hj))).direction

    have hRefLine_mem : ∀ j hj, y ∈ (refLine j hj : Set Point) := by
      intro j hj
      exact AffineSubspace.self_mem_mk' y _
    have hRefLine_dir : ∀ j hj, (refLine j hj).direction = (ℓ (x_j j (hne_of_active j hj))).direction := by
      intro j _; simp [refLine]
    have hRefLine_finrank : ∀ j hj, Module.finrank ℝ (refLine j hj).direction = 1 := by
      intro j hj
      rw [hRefLine_dir j hj]
      exact hℓ2 (x_j j (hne_of_active j hj)) (hxj j (hne_of_active j hj)).1

    -- Finset of reference lines (as Line2) through y
    let S_ref : Finset Line2 := active.attach.image (fun ⟨j, hj⟩ =>
      ⟨refLine j hj, hRefLine_finrank j hj⟩)

    have hS_ref_through_y : ∀ (L : Line2), L ∈ S_ref → y ∈ L.toSet := by
      intro L hL
      rcases Finset.mem_image.mp hL with ⟨⟨j, hj⟩, _, rfl⟩
      exact hRefLine_mem j hj

    -- Greedy selection
    rcases greedy_selection_finite y S_ref hS_ref_through_y δ hδ_pos with
      ⟨T_ref, hT_sub, hT_sep, hT_cover⟩

    have hT_ref_nonempty : T_ref.Nonempty := by
      by_contra h
      have h' : T_ref = ∅ := by simpa using h
      have h_nonempty_Sref : S_ref.Nonempty := by
        rcases h_active_nonempty with ⟨j, hj⟩
        refine ⟨_, Finset.mem_image.mpr ⟨⟨j, hj⟩, by simp, rfl⟩⟩
      rcases h_nonempty_Sref with ⟨L, hL⟩
      rcases hT_cover L hL with ⟨L', hL', _⟩
      rw [h'] at hL' <;> simp at hL'

    -- Default values for else branch
    let j_default : ℕ := Classical.choose h_active_nonempty
    have hj_default : j_default ∈ active := Classical.choose_spec h_active_nonempty
    let hne_default : (X_class j_default).Nonempty := hne_of_active j_default hj_default

    -- For each selected reference line, find corresponding active class
    have h_extract : ∀ (L : Line2), L ∈ T_ref →
        ∃ (j : ℕ) (hj : j ∈ active),
          (⟨refLine j hj, hRefLine_finrank j hj⟩ : Line2) = L := by
      intro L hL
      have hL_in_Sref : L ∈ S_ref := hT_sub hL
      rcases Finset.mem_image.mp hL_in_Sref with ⟨x, hx1, hx2⟩
      exact ⟨x.val, x.property, hx2⟩
    choose j_L hj_L h_j_eq using h_extract

    -- Map selected reference lines back to original lines
    let origLine (L : Line2) : AffineSubspace ℝ Point :=
      if hL : L ∈ T_ref then
        ℓ (x_j (j_L L hL) (hne_of_active (j_L L hL) (hj_L L hL)))
      else
        ℓ (x_j j_default hne_default)

    let S : Finset (AffineSubspace ℝ Point) := T_ref.image origLine

    -- Helper: origLine equation
    have h_orig_eq : ∀ (Lref : Line2) (hLref : Lref ∈ T_ref),
        origLine Lref = ℓ (x_j (j_L Lref hLref) (hne_of_active (j_L Lref hLref) (hj_L Lref hLref))) := by
      intro Lref hLref
      have h : origLine Lref = ℓ (x_j (j_L Lref hLref) (hne_of_active (j_L Lref hLref) (hj_L Lref hLref))) := by
        unfold origLine
        rw [dif_pos hLref]
      exact h

    -- Helper: direction of origLine equals direction of Lref
    have h_orig_dir : ∀ (Lref : Line2) (hLref : Lref ∈ T_ref),
        (origLine Lref).direction = Lref.toAffine.direction := by
      intro Lref hLref
      set j : ℕ := j_L Lref hLref with hj_def
      set hj : j ∈ active := hj_L Lref hLref with hj_mem
      set hne : (X_class j).Nonempty := hne_of_active j hj with hne_def
      set xj : Point := x_j j hne with hxj_def
      set L_j : Line2 := ⟨refLine j hj, hRefLine_finrank j hj⟩ with hL_j_def
      have h_eq1 : origLine Lref = ℓ xj := h_orig_eq Lref hLref
      have h_dir1 : (refLine j hj).direction = (ℓ xj).direction := hRefLine_dir j hj
      have h_j_eq2 : L_j = Lref := h_j_eq Lref hLref
      have h_dir2 : (refLine j hj).direction = Lref.toAffine.direction := by
        have h3 : L_j.toAffine.direction = Lref.toAffine.direction := by
          rw [h_j_eq2]
        exact h3
      rw [h_eq1]
      exact h_dir1.symm.trans h_dir2

    -- Injectivity of origLine on T_ref
    have h_inj : Set.InjOn origLine (T_ref : Set Line2) := by
      intro L1 hL1 L2 hL2 heq
      have h_dir_eq : L1.toAffine.direction = L2.toAffine.direction := by
        rw [←h_orig_dir L1 hL1, ←h_orig_dir L2 hL2, heq]
      have h1 : y ∈ (L1.toAffine : Set Point) := hS_ref_through_y L1 (hT_sub hL1)
      have h2 : y ∈ (L2.toAffine : Set Point) := hS_ref_through_y L2 (hT_sub hL2)
      have h_line_eq : L1.toAffine = L2.toAffine := by
        have h_iff : L1.toAffine = L2.toAffine ↔ L1.toAffine.direction = L2.toAffine.direction :=
          AffineSubspace.eq_iff_direction_eq_of_mem h1 h2
        exact h_iff.mpr h_dir_eq
      exact Subtype.ext h_line_eq

    have hS_card : S.card = T_ref.card := by
      rw [Finset.card_image_of_injOn h_inj]

    -- Property 1: each line in S comes from some x ∈ X_y
    have hS_orig : ∀ L ∈ S, ∃ x ∈ X_y, L = ℓ x := by
      intro L hL
      rcases Finset.mem_image.mp hL with ⟨Lref, hLref, rfl⟩
      let j := j_L Lref hLref
      let hne := hne_of_active j (hj_L Lref hLref)
      have h_eq : origLine Lref = ℓ (x_j j hne) := h_orig_eq Lref hLref
      exact ⟨x_j j hne, (hxj j hne).1, h_eq⟩

    -- Property 2: y in tube_r of each line
    have hS_tube : ∀ L ∈ S, y ∈ Metric.thickening r (L : Set Point) := by
      intro L hL
      rcases Finset.mem_image.mp hL with ⟨Lref, hLref, rfl⟩
      let j := j_L Lref hLref
      let hne := hne_of_active j (hj_L Lref hLref)
      have h_eq : origLine Lref = ℓ (x_j j hne) := h_orig_eq Lref hLref
      rw [h_eq]
      exact h_y_in_tube (x_j j hne) (hxj j hne).1

    -- Property 3: direction separation
    have hS_sep : ∀ L1 ∈ S, ∀ L2 ∈ S, L1 ≠ L2 →
        submoduleDirDist L1.direction L2.direction ≥ δ := by
      intro L1 hL1 L2 hL2 hne
      rcases Finset.mem_image.mp hL1 with ⟨Lref1, hLref1, rfl⟩
      rcases Finset.mem_image.mp hL2 with ⟨Lref2, hLref2, rfl⟩
      have h_Lref_ne : Lref1 ≠ Lref2 := by
        intro h; rw [h] at hne; exact hne rfl
      rw [h_orig_dir Lref1 hLref1, h_orig_dir Lref2 hLref2]
      exact hT_sep Lref1 hLref1 Lref2 hLref2 h_Lref_ne

    -- Cover: every x ∈ X_y is within direction distance d = 5δ/4 of some selected reference line
    let d : ℝ := 5 * δ / 4
    have hd_pos : 0 < d := by positivity

    have h_cover_dir : ∀ (x : Point), x ∈ X_y → ∃ (Lref : Line2), Lref ∈ T_ref ∧
        submoduleDirDist (ℓ x).direction Lref.toAffine.direction ≤ d := by
      intro x hx
      have h_in_union : x ∈ ⋃ j ∈ Finset.range N, X_class j := h_cover_X hx
      rcases Set.mem_iUnion₂.mp h_in_union with ⟨j, hj_in, hx_class⟩
      have h_j_active : j ∈ active := by
        have h : j ∈ Finset.range N ∧ (X_class j).Nonempty := ⟨hj_in, ⟨x, hx_class⟩⟩
        simpa [active, Finset.mem_filter] using h
      let hne : (X_class j).Nonempty := hne_of_active j h_j_active
      let xj := x_j j hne
      let φ_x := directionAngle (ℓ x).direction (hℓ2 x hx)
      let φ_j := directionAngle (ℓ xj).direction (hℓ2 xj (hxj j hne).1)
      have h_abs_x : |φ_x - refAngle j| ≤ α := hx_class.2
      have h_abs_j : |φ_j - refAngle j| ≤ α := (hxj j hne).2
      have h_angle_diff : |φ_x - φ_j| ≤ 2 * α := by
        have h_eq : φ_x - φ_j = (φ_x - refAngle j) - (φ_j - refAngle j) := by ring
        rw [h_eq]
        have h_tri : |(φ_x - refAngle j) - (φ_j - refAngle j)| ≤
            |φ_x - refAngle j| + |φ_j - refAngle j| := abs_sub _ _
        calc |(φ_x - refAngle j) - (φ_j - refAngle j)|
          ≤ |φ_x - refAngle j| + |φ_j - refAngle j| := h_tri
        _ ≤ α + α := by gcongr
        _ = 2 * α := by ring
      have h_dir_class : submoduleDirDist (ℓ x).direction (ℓ xj).direction ≤ 2 * α := by
        have h_eq : submoduleDirDist (ℓ x).direction (ℓ xj).direction =
            |Real.sin (φ_x - φ_j)| :=
          dirDist_eq_abs_sin (ℓ x).direction (ℓ xj).direction
            (hℓ2 x hx) (hℓ2 xj (hxj j hne).1)
        rw [h_eq]
        have h_sin : |Real.sin (φ_x - φ_j)| ≤ |φ_x - φ_j| := Real.abs_sin_le_abs
        exact le_trans h_sin h_angle_diff
      let L_j : Line2 := ⟨refLine j h_j_active, hRefLine_finrank j h_j_active⟩
      have h_Lj_in_Sref : L_j ∈ S_ref := by
        exact Finset.mem_image.mpr ⟨⟨j, h_j_active⟩, by simp, rfl⟩
      rcases hT_cover L_j h_Lj_in_Sref with ⟨Lref, hLref, h_dist_lt⟩
      have h_dist_lt' : submoduleDirDist L_j.toAffine.direction Lref.toAffine.direction < δ := by
        simpa [lineDirDist] using h_dist_lt
      have h_dir_cover : submoduleDirDist (ℓ xj).direction Lref.toAffine.direction < δ := by
        have h_eq_dir : L_j.toAffine.direction = (ℓ xj).direction := by
          dsimp only [L_j, xj, hne]
          exact hRefLine_dir j h_j_active
        rw [h_eq_dir] at h_dist_lt'
        exact h_dist_lt'
      have h_dir_total : submoduleDirDist (ℓ x).direction Lref.toAffine.direction ≤ d := by
        have h_tri : submoduleDirDist (ℓ x).direction Lref.toAffine.direction ≤
            submoduleDirDist (ℓ x).direction (ℓ xj).direction +
            submoduleDirDist (ℓ xj).direction Lref.toAffine.direction :=
          submoduleDirDist_triangle (ℓ x).direction (ℓ xj).direction Lref.toAffine.direction
        have h2α : 2 * α = δ / 4 := by
          dsimp only [α] <;> ring
        have h_a : submoduleDirDist (ℓ x).direction (ℓ xj).direction ≤ δ / 4 := by
          rw [h2α] at h_dir_class; exact h_dir_class
        have h_b : submoduleDirDist (ℓ xj).direction Lref.toAffine.direction ≤ δ := le_of_lt h_dir_cover
        have h : submoduleDirDist (ℓ x).direction Lref.toAffine.direction ≤ δ / 4 + δ := by
          exact le_trans h_tri (add_le_add h_a h_b)
        have h_goal : δ / 4 + δ = d := by
          dsimp only [d] <;> ring
        rw [h_goal] at h
        exact h
      exact ⟨Lref, hLref, h_dir_total⟩

    -- Tube width for greedy clusters
    let W_greedy : ℝ := r + (D + r) * d
    have hW_greedy_pos : 0 < W_greedy := by positivity

    -- Theorem's tube width
    let W_thm : ℝ := r + (D + r) * (δ / 8)
    have hW_thm_pos : 0 < W_thm := by positivity

    -- Each selected cluster has measure ≤ K * W_greedy^σ
    have h_cluster_meas : ∀ (Lref : Line2), Lref ∈ T_ref →
        ν₁ {x : Point | x ∈ X_y ∧ submoduleDirDist (ℓ x).direction Lref.toAffine.direction ≤ d} ≤
          ENNReal.ofReal (K * Real.rpow W_greedy σ) := by
      intro Lref hLref
      let L_aff := Lref.toAffine
      have h_y_in_L : y ∈ (L_aff : Set Point) := hS_ref_through_y Lref (hT_sub hLref)
      have h_finrank : Module.finrank ℝ L_aff.direction = 1 := Lref.2
      have h_contain : {x : Point | x ∈ X_y ∧ submoduleDirDist (ℓ x).direction L_aff.direction ≤ d} ⊆
          {b₁ | b₁ ∈ Metric.thickening W_greedy (L_aff : Set Point) ∧ (b₁, y) ∈ G} := by
        intro x hx
        have hx_X : x ∈ X_y := hx.1
        have hdir : submoduleDirDist (ℓ x).direction L_aff.direction ≤ d := hx.2
        have hdir' : submoduleDirDist L_aff.direction (ℓ x).direction ≤ d := by
          rw [submoduleDirDist_comm] <;> exact hdir
        have h_geom : x ∈ Metric.thickening W_greedy (L_aff : Set Point) :=
          point_in_wider_tube hr hD (by linarith) y x L_aff (ℓ x)
            L_aff.direction (ℓ x).direction rfl rfl
            h_y_in_L (hℓ1 x hx_X)
            (h_y_in_tube x hx_X) (h_bounded x hx_X) hdir'
        exact ⟨h_geom, h_in_G x hx_X⟩
      have h1 : ν₁ (_) ≤ ν₁ (_) := measure_mono h_contain
      have h2 := hG_reverse L_aff h_y_in_L h_finrank W_greedy hW_greedy_pos
      exact le_trans h1 h2

    -- The clusters cover X_y
    have h_Xy_covered : X_y ⊆ ⋃ Lref ∈ T_ref,
        {x : Point | x ∈ X_y ∧ submoduleDirDist (ℓ x).direction Lref.toAffine.direction ≤ d} := by
      intro x hx
      rcases h_cover_dir x hx with ⟨Lref, hLref, hdir⟩
      have h : x ∈ {x : Point | x ∈ X_y ∧ submoduleDirDist (ℓ x).direction Lref.toAffine.direction ≤ d} :=
        ⟨hx, hdir⟩
      have h2 : x ∈ (⋃ Lref ∈ T_ref, {x : Point | x ∈ X_y ∧ submoduleDirDist (ℓ x).direction Lref.toAffine.direction ≤ d}) := by
        exact Set.mem_iUnion₂.mpr ⟨Lref, hLref, h⟩
      exact h2

    -- Measure bound via subadditivity
    have h_sum_le : ν₁ X_y ≤ ∑ Lref ∈ T_ref,
          ν₁ {x : Point | x ∈ X_y ∧ submoduleDirDist (ℓ x).direction Lref.toAffine.direction ≤ d} := by
      calc ν₁ X_y
        ≤ ν₁ (⋃ Lref ∈ T_ref, _) := measure_mono h_Xy_covered
      _ ≤ ∑ Lref ∈ T_ref, ν₁ (_) := measure_biUnion_finset_le _ _

    have h_mass_le : ENNReal.ofReal mass ≤
        (T_ref.card : ENNReal) * ENNReal.ofReal (K * Real.rpow W_greedy σ) := by
      calc ENNReal.ofReal mass
        ≤ ν₁ X_y := hX_y_mass
      _ ≤ ∑ Lref ∈ T_ref, ν₁ (_) := h_sum_le
      _ ≤ ∑ Lref ∈ T_ref, ENNReal.ofReal (K * Real.rpow W_greedy σ) := by
        apply Finset.sum_le_sum
        intro Lref hLref
        exact h_cluster_meas Lref hLref
      _ = (T_ref.card : ENNReal) * ENNReal.ofReal (K * Real.rpow W_greedy σ) := by
        simp [Finset.sum_const] <;> ring

    have hK_pos' : 0 < K := by linarith
    have h_rpow_pos : 0 < Real.rpow W_greedy σ := Real.rpow_pos_of_pos hW_greedy_pos σ
    have h_mul_pos : 0 < K * Real.rpow W_greedy σ := mul_pos hK_pos' h_rpow_pos

    have h_real_bound : mass ≤ (T_ref.card : ℝ) * (K * Real.rpow W_greedy σ) := by
      have h : ENNReal.ofReal mass ≤ ENNReal.ofReal ((T_ref.card : ℝ) * (K * Real.rpow W_greedy σ)) := by
        simpa [ENNReal.ofReal_mul] using h_mass_le
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

    -- Ratio inequality: W_greedy < 10 * W_thm, hence W_greedy^σ ≤ 15 * W_thm^σ
    have h_ratio1 : W_greedy < 10 * W_thm := by
      dsimp only [W_greedy, W_thm, d, α]
      have h : r + (D + r) * (5 * δ / 4) < 10 * (r + (D + r) * (δ / 8)) := by
        ring_nf
        nlinarith [hr, hD, hδ_pos]
      exact h

    have h_rpow_ratio : Real.rpow W_greedy σ ≤ 15 * Real.rpow W_thm σ := by
      have h1 : 0 < W_thm := hW_thm_pos
      have h2 : W_greedy / W_thm < 10 := by
        calc W_greedy / W_thm
          < (10 * W_thm) / W_thm := by gcongr
        _ = 10 := by
              have h9 : (10 * W_thm) / W_thm = 10 := by
                field_simp [h1.ne'] <;> ring
              exact h9
      by_cases h_case : W_greedy ≤ W_thm
      · -- Case W_greedy ≤ W_thm
        have h_a : Real.rpow W_greedy σ ≤ Real.rpow W_thm σ :=
          Real.rpow_le_rpow (by positivity) h_case hσ
        have h_b : Real.rpow W_thm σ ≤ 15 * Real.rpow W_thm σ := by
          have h_nonneg : 0 ≤ Real.rpow W_thm σ := Real.rpow_nonneg (by positivity) σ
          nlinarith
        exact le_trans h_a h_b
      · -- Case W_greedy > W_thm
        have h_gt : W_thm < W_greedy := by linarith
        have h_ratio_gt_one : 1 < W_greedy / W_thm := by
          calc 1
            = W_thm / W_thm := by field_simp [hW_thm_pos.ne'] <;> ring
          _ < W_greedy / W_thm := by gcongr
        have h_ratio_ge_one : 1 ≤ W_greedy / W_thm := h_ratio_gt_one.le
        have h4 : Real.rpow (W_greedy / W_thm) σ ≤ W_greedy / W_thm := by
          have h5 : Real.rpow (W_greedy / W_thm) σ ≤ Real.rpow (W_greedy / W_thm) 1 := by
            apply Real.rpow_le_rpow_of_exponent_le h_ratio_ge_one
            exact hσ_le_one
          have h6 : Real.rpow (W_greedy / W_thm) 1 = W_greedy / W_thm := by simp
          rw [h6] at h5
          exact h5
        have h7 : Real.rpow W_greedy σ = Real.rpow (W_thm * (W_greedy / W_thm)) σ := by
          apply congr_arg (fun x : ℝ => Real.rpow x σ)
          field_simp [h1.ne'] <;> ring
        rw [h7]
        have h9 : Real.rpow (W_thm * (W_greedy / W_thm)) σ =
            Real.rpow W_thm σ * Real.rpow (W_greedy / W_thm) σ :=
          Real.mul_rpow (hW_thm_pos.le) (by positivity)
        rw [h9]
        have h10 : 0 ≤ Real.rpow W_thm σ := Real.rpow_nonneg (by positivity) σ
        have h11 : Real.rpow (W_greedy / W_thm) σ ≤ 10 := by
          calc Real.rpow (W_greedy / W_thm) σ
            ≤ W_greedy / W_thm := h4
          _ ≤ 10 := by linarith [h2]
        have h12 : Real.rpow W_thm σ * Real.rpow (W_greedy / W_thm) σ ≤
            Real.rpow W_thm σ * 15 := by
          gcongr
          <;> linarith
        have h13 : Real.rpow W_thm σ * 15 = 15 * Real.rpow W_thm σ := by ring
        rw [h13] at h12
        exact h12

    have h_pos2 : 0 < 15 * K * Real.rpow W_thm σ := by
      have h_rpow2_pos : 0 < Real.rpow W_thm σ := Real.rpow_pos_of_pos hW_thm_pos σ
      positivity

    have h4 : K * Real.rpow W_greedy σ ≤ 15 * K * Real.rpow W_thm σ := by
      have h5 : 0 ≤ K := by linarith
      nlinarith [h_rpow_ratio]

    have h_final_card : (T_ref.card : ℝ) ≥ mass / (15 * K * Real.rpow W_thm σ) := by
      have h : mass ≤ (T_ref.card : ℝ) * (K * Real.rpow W_greedy σ) := h_real_bound
      have h6 : (T_ref.card : ℝ) * (K * Real.rpow W_greedy σ) ≤
          (T_ref.card : ℝ) * (15 * K * Real.rpow W_thm σ) := by
        exact mul_le_mul_of_nonneg_left h4 (by positivity)
      have h7 : mass ≤ (T_ref.card : ℝ) * (15 * K * Real.rpow W_thm σ) := le_trans h h6
      have h_div : mass / (15 * K * Real.rpow W_thm σ) ≤
          ((T_ref.card : ℝ) * (15 * K * Real.rpow W_thm σ)) / (15 * K * Real.rpow W_thm σ) := by
        apply div_le_div_of_nonneg_right h7
        positivity
      have h_eq : ((T_ref.card : ℝ) * (15 * K * Real.rpow W_thm σ)) / (15 * K * Real.rpow W_thm σ) = (T_ref.card : ℝ) := by
        have h_rpow_ne_zero : Real.rpow W_thm σ ≠ 0 := (Real.rpow_pos_of_pos hW_thm_pos σ).ne'
        field_simp [h_pos2.ne', h_rpow_ne_zero] <;> ring
      rw [h_eq] at h_div
      exact h_div

    have hS_card_lower : (S.card : ℝ) ≥ mass / (15 * K * Real.rpow (r + (D + r) * (δ / 8)) σ) := by
      rw [hS_card]
      dsimp only [W_thm] at h_final_card
      exact h_final_card

    have h_cover_S : ∀ (x : Point), x ∈ X_y → ∃ L ∈ S,
        submoduleDirDist (ℓ x).direction L.direction ≤ 5 * δ / 4 := by
      intro x hx
      rcases h_cover_dir x hx with ⟨Lref, hLref, hdir⟩
      let L : AffineSubspace ℝ Point := origLine Lref
      have hL_in_S : L ∈ S := Finset.mem_image.mpr ⟨Lref, hLref, rfl⟩
      have h_dir_eq : L.direction = Lref.toAffine.direction := h_orig_dir Lref hLref
      refine ⟨L, hL_in_S, ?_⟩
      rw [h_dir_eq]
      exact hdir
    exact ⟨S, hS_orig, hS_tube, hS_sep, hS_card_lower, h_cover_S⟩

end RadialBootstrapping
