module

/-
  Geometric lemma: a tube within 2δ of two points q, q' at distance d,
  with ‖q‖, ‖q'‖ ≤ 2, lies within 200*(δ + δ/d) of the unique line through q and q'.

  This is the bounded version of the `h_geom` hypothesis needed by
  `common_tubes_bound_proof`. The universal version (without ‖q‖ bound) is false
  because AffineLine.offset depends on distance from origin.

  Proof:
  1. Let p, p' be orthogonal projections of q, q' onto ℓ. Then ‖p-q‖, ‖p'-q'‖ ≤ 2δ.
  2. Direction: perpendicular component of q'-q relative to ℓ is (p-q)+(q'-p'),
     norm ≤ 4δ. Thus sin(angle) ≤ 4δ/d, giving ‖P_ℓ - P_ℓ₀‖ ≤ 8√2·δ/d.
  3. Offset: off_ℓ - off_ℓ₀ = (I-P_ℓ)(p-q) + (P_ℓ₀-P_ℓ)(q),
     bounded by 2δ + ‖P_ℓ-P_ℓ₀‖·‖q‖ ≤ 2δ + 16√2·δ/d.
  4. Total: ≤ 2δ + 24√2·δ/d ≤ 200(δ + δ/d).

  Whiteprint node: Phase2 / CommonTubeGeometricLemma
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Phase2

open DirecretisedFurstenbergEstimate
open Metric Set EuclideanGeometry

/-- General operator norm bound for projections onto 1D subspaces spanned by
    unit vectors: ‖P_{u1} - P_{u2}‖ ≤ 2 * ‖u1 - u2‖. -/
lemma proj_op_norm_bound {u1 u2 : EuclideanPlane}
    (hu1_norm : ‖u1‖ = 1) (hu2_norm : ‖u2‖ = 1) :
    ‖(Submodule.span ℝ {u1}).starProjection -
      (Submodule.span ℝ {u2}).starProjection‖ ≤ 2 * ‖u1 - u2‖ := by
  let P1 := (Submodule.span ℝ {u1}).starProjection
  let P2 := (Submodule.span ℝ {u2}).starProjection
  have h_bound : ∀ (x : EuclideanPlane), ‖(P1 - P2) x‖ ≤ 2 * ‖u1 - u2‖ * ‖x‖ := by
    intro x
    have h1 : P1 x = inner ℝ x u1 • u1 := by
      have h := Submodule.starProjection_unit_singleton ℝ hu1_norm x
      have h_comm : inner ℝ u1 x = inner ℝ x u1 := by exact real_inner_comm x u1
      rw [h_comm] at h; exact h
    have h2 : P2 x = inner ℝ x u2 • u2 := by
      have h := Submodule.starProjection_unit_singleton ℝ hu2_norm x
      have h_comm : inner ℝ u2 x = inner ℝ x u2 := by exact real_inner_comm x u2
      rw [h_comm] at h; exact h
    have h3 : (P1 - P2) x = (inner ℝ x u1 • u1) - (inner ℝ x u2 • u2) := by
      simp [h1, h2]
    rw [h3]
    have h4 : (inner ℝ x u1 • u1) - (inner ℝ x u2 • u2) =
        (inner ℝ x u1) • (u1 - u2) + (inner ℝ x (u1 - u2)) • u2 := by
      have h5 : inner ℝ x (u1 - u2) = inner ℝ x u1 - inner ℝ x u2 := by
        rw [← inner_sub_right] <;> rfl
      apply Eq.symm
      calc (inner ℝ x u1) • (u1 - u2) + (inner ℝ x (u1 - u2)) • u2
          = (inner ℝ x u1) • u1 - (inner ℝ x u1) • u2 + (inner ℝ x (u1 - u2)) • u2 := by
            rw [smul_sub]
        _ = (inner ℝ x u1) • u1 - (inner ℝ x u1) • u2 + ((inner ℝ x u1) - (inner ℝ x u2)) • u2 := by
            rw [h5]
        _ = (inner ℝ x u1) • u1 - (inner ℝ x u2 • u2) := by rw [sub_smul] <;> abel
        _ = (inner ℝ x u1 • u1) - (inner ℝ x u2 • u2) := by rfl
    rw [h4]
    calc ‖(inner ℝ x u1) • (u1 - u2) + (inner ℝ x (u1 - u2)) • u2‖
        ≤ ‖(inner ℝ x u1) • (u1 - u2)‖ + ‖(inner ℝ x (u1 - u2)) • u2‖ := norm_add_le _ _
      _ = |inner ℝ x u1| * ‖u1 - u2‖ + |inner ℝ x (u1 - u2)| * ‖u2‖ := by
        simp [norm_smul] <;> ring
      _ ≤ ‖x‖ * ‖u1‖ * ‖u1 - u2‖ + ‖x‖ * ‖u1 - u2‖ * ‖u2‖ := by
        have h5 : |inner ℝ x u1| ≤ ‖x‖ * ‖u1‖ := abs_real_inner_le_norm x u1
        have h6 : |inner ℝ x (u1 - u2)| ≤ ‖x‖ * ‖u1 - u2‖ := abs_real_inner_le_norm x (u1 - u2)
        gcongr <;> linarith
      _ = 2 * ‖u1 - u2‖ * ‖x‖ := by rw [hu1_norm, hu2_norm] <;> ring
  exact ContinuousLinearMap.opNorm_le_bound (P1 - P2) (by positivity) h_bound

/-- Geometric lemma (bounded version): if an AffineLine ℓ passes within 2δ of both
    q and q', and ‖q‖, ‖q'‖ ≤ 2, then there is a line ℓ₀ through q and q' such that
    `dist ℓ ℓ₀ ≤ 200 * (δ + δ / dist q q')`. -/
lemma common_tube_geometric_lemma_bounded
    (δ : ℝ) (hδ_pos : 0 < δ)
    (q q' : EuclideanPlane) (hd_pos : 0 < dist q q')
    (hq_bound : ‖q‖ ≤ 2) (hq'_bound : ‖q'‖ ≤ 2)
    (ℓ : AffineLine)
    (hq_near : q ∈ cthickening (2 * δ) ℓ.1)
    (hq'_near : q' ∈ cthickening (2 * δ) ℓ.1) :
    ∃ (ℓ₀ : AffineLine), q ∈ ℓ₀.1 ∧ q' ∈ ℓ₀.1 ∧
      dist ℓ ℓ₀ ≤ 200 * (δ + δ / dist q q') := by
  set ε : ℝ := 2 * δ with hε_def
  have hε_pos : 0 < ε := by positivity
  set d : ℝ := dist q q' with hd_def
  have hd_pos' : 0 < d := hd_pos
  set v : EuclideanPlane := q' - q with hv_def
  have h_v_norm : ‖v‖ = d := by
    have h : ‖q' - q‖ = dist q' q := by simp [dist_eq_norm]
    rw [h, dist_comm q' q] <;> simp [hd_def]
  have hne : q ≠ q' := by
    exact dist_pos.mp hd_pos'

  -- Construct ℓ₀ through q and q'
  let S₀ : AffineSubspace ℝ EuclideanPlane := AffineSubspace.mk' q (Submodule.span ℝ {v})
  have hq_in_S0 : q ∈ S₀ := by
    have h : q - q ∈ (Submodule.span ℝ {v}) := by simp
    simpa [S₀, AffineSubspace.mem_mk'] using h
  have hq'_in_S0 : q' ∈ S₀ := by
    have h : q' - q = v := by simp [hv_def] <;> abel
    have h2 : q' - q ∈ (Submodule.span ℝ {v}) := by
      rw [h]; exact Submodule.mem_span_singleton.mpr ⟨1, by simp⟩
    simpa [S₀, AffineSubspace.mem_mk'] using h2
  have h_dir0 : S₀.direction = Submodule.span ℝ {v} := by
    simp [S₀, AffineSubspace.direction_mk']
  have h_finrank0 : Module.finrank ℝ S₀.direction = 1 := by
    rw [h_dir0]
    have hv_ne_zero : v ≠ 0 := by
      intro h
      have : ‖v‖ = 0 := by rw [h] <;> simp
      rw [h_v_norm] at this
      linarith
    exact finrank_span_singleton hv_ne_zero
  let ℓ₀ : AffineLine := ⟨S₀, h_finrank0⟩

  -- Orthogonal projections onto ℓ
  let p : EuclideanPlane := orthogonalProjection ℓ.1 q
  let p' : EuclideanPlane := orthogonalProjection ℓ.1 q'
  have hp_mem : p ∈ ℓ.1 := orthogonalProjection_mem q
  have hp'_mem : p' ∈ ℓ.1 := orthogonalProjection_mem q'

  -- Distance bounds from thickening: for any ε' > ε, ∃ y ∈ ℓ.1 with dist q y < ε'
  -- Then dist q p ≤ dist q y < ε', so by taking ε' → ε, dist q p ≤ ε.
  have h_dist_p : dist q p ≤ ε := by
    have h_main : ∀ (ε' : ℝ), ε < ε' → dist q p ≤ ε' := by
      intro ε' hε'
      have h1 : Metric.infEDist q ℓ.1 < ENNReal.ofReal ε' := by
        have h2 : Metric.infEDist q ℓ.1 ≤ ENNReal.ofReal ε := Metric.mem_cthickening_iff.mp hq_near
        have h3 : ENNReal.ofReal ε < ENNReal.ofReal ε' := by
          have hpos : 0 ≤ ε := by linarith
          exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hpos).mpr hε'
        exact lt_of_le_of_lt h2 h3
      rcases Metric.infEDist_lt_iff.mp h1 with ⟨y, hy, h4⟩
      have h5 : dist q y < ε' := by
        have h51 : ENNReal.ofReal (dist q y) < ENNReal.ofReal ε' := by
          simpa [edist_dist] using h4
        exact edist_lt_ofReal.mp h4
      have h6 : dist q p ≤ dist q y := by
        have h61 : dist q p = Metric.infDist q ℓ.1 :=
          EuclideanGeometry.dist_orthogonalProjection_eq_infDist ℓ.1 q
        have hne : (ℓ.1 : Set EuclideanPlane).Nonempty := ℓ.nonempty
        have h62 : Metric.infDist q ℓ.1 ≤ dist q y := Metric.infDist_le_dist_of_mem hy
        rw [h61]; exact h62
      linarith
    exact le_of_forall_pos_le_add (fun δ' hδ' => h_main (ε + δ') (by linarith))
  have h_dist_p' : dist q' p' ≤ ε := by
    have h_main : ∀ (ε' : ℝ), ε < ε' → dist q' p' ≤ ε' := by
      intro ε' hε'
      have h1 : Metric.infEDist q' ℓ.1 < ENNReal.ofReal ε' := by
        have h2 : Metric.infEDist q' ℓ.1 ≤ ENNReal.ofReal ε := Metric.mem_cthickening_iff.mp hq'_near
        have h3 : ENNReal.ofReal ε < ENNReal.ofReal ε' := by
          have hpos : 0 ≤ ε := by linarith
          exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hpos).mpr hε'
        exact lt_of_le_of_lt h2 h3
      rcases Metric.infEDist_lt_iff.mp h1 with ⟨y, hy, h4⟩
      have h5 : dist q' y < ε' := by
        have h51 : ENNReal.ofReal (dist q' y) < ENNReal.ofReal ε' := by
          simpa [edist_dist] using h4
        exact edist_lt_ofReal.mp h4
      have h6 : dist q' p' ≤ dist q' y := by
        have h61 : dist q' p' = Metric.infDist q' ℓ.1 :=
          EuclideanGeometry.dist_orthogonalProjection_eq_infDist ℓ.1 q'
        have hne : (ℓ.1 : Set EuclideanPlane).Nonempty := ℓ.nonempty
        have h62 : Metric.infDist q' ℓ.1 ≤ dist q' y := by exact infDist_le_dist_of_mem hy
        rw [h61]; exact h62
      linarith
    exact le_of_forall_pos_le_add (fun δ' hδ' => h_main (ε + δ') (by linarith))

  let K := ℓ.1.direction
  let P1 := K.starProjection
  let P0 := ℓ₀.1.direction.starProjection

  -- Perpendicularity: p - q ∈ Kᗮ
  have h_perp1 : p - q ∈ Kᗮ := by
    have h : q - p ∈ Kᗮ := by
      have h_eq : (orthogonalProjection ℓ.1 q : EuclideanPlane) = p := rfl
      have h_iff := EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem (s := ℓ.1) (p := q) (q := p)
      exact h_iff.mp h_eq |>.2
    have h2 : p - q = -(q - p) := by abel
    rw [h2]
    exact Submodule.neg_mem Kᗮ h

  have h_perp2 : p' - q' ∈ Kᗮ := by
    have h : q' - p' ∈ Kᗮ := by
      have h_eq : (orthogonalProjection ℓ.1 q' : EuclideanPlane) = p' := rfl
      have h_iff := EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem (s := ℓ.1) (p := q') (q := p')
      exact h_iff.mp h_eq |>.2
    have h2 : p' - q' = -(q' - p') := by abel
    rw [h2]
    exact Submodule.neg_mem Kᗮ h

  -- p' - p ∈ K
  have h_parallel : p' - p ∈ K := AffineSubspace.vsub_mem_direction hp'_mem hp_mem

  -- Decompose v = (p' - p) + w where w is perpendicular to K
  let w := (p - q) + (q' - p')
  have h_v_decomp : v = (p' - p) + w := by
    simp [w, hv_def] <;> abel
  have h_w_perp : w ∈ Kᗮ := by
    apply Submodule.add_mem Kᗮ h_perp1
    have h : q' - p' = -(p' - q') := by abel
    rw [h]
    exact Submodule.neg_mem Kᗮ h_perp2
  have h_w_norm : ‖w‖ ≤ 2 * ε := by
    calc ‖w‖ ≤ ‖p - q‖ + ‖q' - p'‖ := norm_add_le _ _
      _ = ‖q - p‖ + ‖q' - p'‖ := by rw [norm_sub_rev]
      _ = dist q p + dist q' p' := by simp [dist_eq_norm]
      _ ≤ ε + ε := by linarith
      _ = 2 * ε := by ring

  -- P1(v) = p' - p
  have h_P1_v : P1 v = p' - p := by
    apply Submodule.eq_starProjection_of_mem_orthogonal h_parallel
    have h : v - (p' - p) = w := by
      rw [h_v_decomp] <;> abel
    rw [h]
    exact h_w_perp

  -- Pythagorean: ‖v‖² = ‖p'-p‖² + ‖w‖²
  have h_inner_perp : inner ℝ (p' - p) w = 0 := h_w_perp (p' - p) h_parallel
  have h_pyth : ‖v‖ ^ 2 = ‖p' - p‖ ^ 2 + ‖w‖ ^ 2 := by
    have h2 := norm_add_sq_eq_norm_sq_add_norm_sq_real h_inner_perp
    have h3 : ‖(p' - p) + w‖ ^ 2 = ‖p' - p‖ ^ 2 + ‖w‖ ^ 2 := by
      have h4 : ‖(p' - p) + w‖ * ‖(p' - p) + w‖ = ‖p' - p‖ * ‖p' - p‖ + ‖w‖ * ‖w‖ := h2
      have h5 : ‖(p' - p) + w‖ ^ 2 = ‖(p' - p) + w‖ * ‖(p' - p) + w‖ := by ring
      have h6 : ‖p' - p‖ ^ 2 + ‖w‖ ^ 2 = ‖p' - p‖ * ‖p' - p‖ + ‖w‖ * ‖w‖ := by ring
      rw [h5, h4, ←h6]
    have h4 : (p' - p) + w = v := by rw [h_v_decomp] <;> abel
    rw [h4] at h3
    exact h3

  -- Unit vector u2 = v/d
  let u2 : EuclideanPlane := (1 / d : ℝ) • v
  have h_u2_norm : ‖u2‖ = 1 := by
    have h : ‖u2‖ = |(1 / d : ℝ)| * ‖v‖ := by
      rw [norm_smul] <;> rfl
    rw [h]
    have hpos : 0 < (1 / d : ℝ) := by positivity
    rw [abs_of_pos hpos, h_v_norm]
    <;> field_simp [hd_pos'.ne'] <;> ring

  -- Nonzero vector in K, normalize
  have hK_ne_bot : K ≠ ⊥ := by
    intro h
    have h1 : Module.finrank ℝ K = 1 := ℓ.2
    have h2 : Module.finrank ℝ (⊥ : Submodule ℝ EuclideanPlane) = 0 := by simp
    have h3 : Module.finrank ℝ K = Module.finrank ℝ (⊥ : Submodule ℝ EuclideanPlane) := by rw [h]
    rw [h1, h2] at h3
    <;> norm_num at h3
  have hK_nontrivial : ∃ (u : EuclideanPlane), u ∈ K ∧ u ≠ 0 := by
    have h : K ≠ ⊥ := hK_ne_bot
    simpa [Submodule.ne_bot_iff] using h
  rcases hK_nontrivial with ⟨u1_raw, hu1_raw_mem, hu1_raw_ne⟩
  let u1_unit : EuclideanPlane := (1 / ‖u1_raw‖) • u1_raw
  have h_u1_unit_mem : u1_unit ∈ K := K.smul_mem (1 / ‖u1_raw‖) hu1_raw_mem
  have h_u1_unit_norm : ‖u1_unit‖ = 1 := by
    have h : ‖u1_unit‖ = |(1 / ‖u1_raw‖ : ℝ)| * ‖u1_raw‖ := by
      rw [norm_smul] <;> rfl
    rw [h]
    have hpos : 0 < (1 / ‖u1_raw‖ : ℝ) := by positivity
    rw [abs_of_pos hpos]
    <;> field_simp [hu1_raw_ne] <;> ring

  -- Choose sign so inner u1 u2 ≥ 0
  let c_raw := inner ℝ u1_unit u2
  let u1 := if c_raw ≥ 0 then u1_unit else -u1_unit
  have h_u1_mem : u1 ∈ K := by
    dsimp only [u1]
    split_ifs <;> simp [h_u1_unit_mem] <;> tauto
  have h_u1_norm : ‖u1‖ = 1 := by
    dsimp only [u1]
    split_ifs <;> simp [h_u1_unit_norm] <;> norm_num
  have h_inner_nonneg : 0 ≤ inner ℝ u1 u2 := by
    dsimp only [u1]
    split_ifs with h
    · exact h
    · have h' : inner ℝ (-u1_unit) u2 = -inner ℝ u1_unit u2 := by simp
      rw [h']
      linarith

  -- K = span{u1}, ℓ₀.direction = span{u2}
  have h_span1 : K = Submodule.span ℝ {u1} := by
    have h1 : Submodule.span ℝ {u1} ≤ K := by
      apply Submodule.span_le.mpr
      intro x hx
      have h_x_eq : x = u1 := by simpa [Set.mem_singleton_iff] using hx
      rw [h_x_eq]
      exact h_u1_mem
    have h_u1_ne_zero : u1 ≠ 0 := by
      intro h
      rw [h] at h_u1_norm
      simp at h_u1_norm
    have h2 : Module.finrank ℝ (Submodule.span ℝ {u1}) = 1 :=
      finrank_span_singleton h_u1_ne_zero
    have h_eq : Submodule.span ℝ {u1} = K :=
      Submodule.eq_of_le_of_finrank_eq (S₁ := Submodule.span ℝ {u1}) (S₂ := K) h1 (h2.trans ℓ.2.symm)
    exact h_eq.symm

  have h_span2 : ℓ₀.1.direction = Submodule.span ℝ {u2} := by
    rw [h_dir0]
    have h_le1 : Submodule.span ℝ {u2} ≤ Submodule.span ℝ {v} := by
      apply Submodule.span_le.mpr
      intro x hx
      have h_x_eq : x = u2 := by simpa [Set.mem_singleton_iff] using hx
      rw [h_x_eq]
      have h : u2 = (1 / d : ℝ) • v := by rfl
      rw [h]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton.mpr ⟨1, by simp⟩)
    have h_le2 : Submodule.span ℝ {v} ≤ Submodule.span ℝ {u2} := by
      apply Submodule.span_le.mpr
      intro x hx
      have h_x_eq : x = v := by simpa [Set.mem_singleton_iff] using hx
      rw [h_x_eq]
      have h : v = d • u2 := by
        simp [u2, h_v_norm, hd_pos'.ne'] <;> field_simp <;> abel
      rw [h]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton.mpr ⟨1, by simp⟩)
    exact le_antisymm h_le2 h_le1

  -- Direction bound
  have h_dir_bound : ‖P1 - P0‖ ≤ 2 * ‖u1 - u2‖ := by
    have h : ‖K.starProjection - ℓ₀.1.direction.starProjection‖ ≤ 2 * ‖u1 - u2‖ := by
      rw [h_span1, h_span2]
      exact proj_op_norm_bound h_u1_norm h_u2_norm
    simpa [P1, P0] using h

  -- Bound inner product c' = inner u1 u2
  let c' := inner ℝ u1 u2
  have h_c'_nonneg : 0 ≤ c' := h_inner_nonneg

  have h_P1_v2 : P1 v = (d * c') • u1 := by
    have h_goal : K.starProjection v = (d * c') • u1 := by
      rw [h_span1]
      have h := Submodule.starProjection_unit_singleton ℝ h_u1_norm v
      have h_comm : inner ℝ u1 v = inner ℝ v u1 := by exact real_inner_comm v u1
      rw [h_comm] at h
      rw [h]
      have h4 : inner ℝ v u1 = d * c' := by
        have h5 : v = d • u2 := by
          simp [u2, h_v_norm, hd_pos'.ne'] <;> field_simp <;> abel
        have h6 : inner ℝ v u1 = d * inner ℝ u2 u1 := by
          calc inner ℝ v u1
            = inner ℝ (d • u2) u1 := by rw [h5]
          _ = d * inner ℝ u2 u1 := by simp [inner_smul_left]
        have h7 : inner ℝ u2 u1 = inner ℝ u1 u2 := by exact real_inner_comm u1 u2
        have h8 : inner ℝ u1 u2 = c' := by rfl
        rw [h6, h7, h8] <;> ring
      rw [h4] <;> rfl
    simpa [P1] using h_goal

  have h_P1_v_norm : ‖P1 v‖ = d * c' := by
    rw [h_P1_v2]
    have h_pos : 0 ≤ d * c' := by positivity
    have h : ‖(d * c') • u1‖ = |d * c'| * ‖u1‖ := by
      rw [norm_smul] <;> rfl
    rw [h, h_u1_norm]
    have h2 : |d * c'| = d * c' := abs_of_nonneg h_pos
    rw [h2] <;> ring

  have h_c'_sq : c' ^ 2 = 1 - (‖w‖ / d) ^ 2 := by
    have h1 : ‖P1 v‖ ^ 2 + ‖w‖ ^ 2 = d ^ 2 := by
      have h_eq1 : ‖P1 v‖ = ‖p' - p‖ := by rw [h_P1_v]
      rw [h_eq1]
      have h : ‖p' - p‖ ^ 2 + ‖w‖ ^ 2 = ‖v‖ ^ 2 := h_pyth.symm
      rw [h, h_v_norm]
    have h1' : (d * c') ^ 2 + ‖w‖ ^ 2 = d ^ 2 := by
      rw [h_P1_v_norm] at h1
      exact h1
    have h_d2_pos : 0 < d ^ 2 := by positivity
    have h_eq2 : d ^ 2 * c' ^ 2 = d ^ 2 - ‖w‖ ^ 2 := by
      have h_expand : (d * c') ^ 2 = d ^ 2 * c' ^ 2 := by ring
      rw [h_expand] at h1'
      linarith
    have h_eq3 : c' ^ 2 = 1 - (‖w‖ / d) ^ 2 := by
      calc c' ^ 2
        = (d ^ 2 * c' ^ 2) / d ^ 2 := by field_simp [h_d2_pos.ne'] <;> ring
      _ = (d ^ 2 - ‖w‖ ^ 2) / d ^ 2 := by rw [h_eq2]
      _ = 1 - (‖w‖ / d) ^ 2 := by field_simp [h_d2_pos.ne'] <;> ring
    exact h_eq3

  have h_u1_u2_dist_sq : ‖u1 - u2‖ ^ 2 = 2 * (1 - c') := by
    have h9 : ‖u1 - u2‖ ^ 2 = inner ℝ (u1 - u2) (u1 - u2) := by
      rw [← real_inner_self_eq_norm_sq]
    rw [h9]
    have h10 : inner ℝ (u1 - u2) (u1 - u2) = inner ℝ u1 u1 - inner ℝ u1 u2 - inner ℝ u2 u1 + inner ℝ u2 u2 := by
      have h101 : inner ℝ (u1 - u2) (u1 - u2) = inner ℝ u1 (u1 - u2) - inner ℝ u2 (u1 - u2) := by
        rw [inner_sub_left]
      rw [h101]
      have h102 : inner ℝ u1 (u1 - u2) = inner ℝ u1 u1 - inner ℝ u1 u2 := by rw [inner_sub_right]
      have h103 : inner ℝ u2 (u1 - u2) = inner ℝ u2 u1 - inner ℝ u2 u2 := by rw [inner_sub_right]
      rw [h102, h103] <;> ring
    rw [h10]
    have h11 : inner ℝ u2 u1 = inner ℝ u1 u2 := by exact real_inner_comm u1 u2
    have h12 : inner ℝ u1 u1 = ‖u1‖ ^ 2 := by rw [← real_inner_self_eq_norm_sq]
    have h13 : inner ℝ u2 u2 = ‖u2‖ ^ 2 := by rw [← real_inner_self_eq_norm_sq]
    rw [h11, h12, h13, h_u1_norm, h_u2_norm] <;> ring

  have h_1min_c' : 1 - c' ≤ (‖w‖ / d) ^ 2 := by
    have h_eq : (1 - c') * (1 + c') = 1 - c' ^ 2 := by ring
    have h_eq2 : 1 - c' ^ 2 = (‖w‖ / d) ^ 2 := by
      rw [h_c'_sq] <;> ring
    have h_pos1 : 0 ≤ c' := h_c'_nonneg
    have h_pos2 : 0 ≤ 1 - c' := by
      have h_cs : |inner ℝ u1 u2| ≤ ‖u1‖ * ‖u2‖ := abs_real_inner_le_norm u1 u2
      have h_cs2 : |c'| ≤ 1 := by
        simpa [h_u1_norm, h_u2_norm, c'] using h_cs
      have h_c'_le1 : c' ≤ 1 := by
        have h : |c'| ≤ 1 := h_cs2
        have h' : -1 ≤ c' ∧ c' ≤ 1 := abs_le.mp h
        exact h'.2
      linarith
    have h_ineq : 1 - c' ≤ (1 - c') * (1 + c') := by
      have h6 : (1 - c') * (1 + c') - (1 - c') = (1 - c') * c' := by ring
      have h7 : 0 ≤ (1 - c') * c' := mul_nonneg h_pos2 h_pos1
      linarith
    have h8 : (1 - c') * (1 + c') = (‖w‖ / d) ^ 2 := by
      rw [h_eq, h_eq2]
    rw [h8] at h_ineq
    exact h_ineq

  have h_u1_u2_dist : ‖u1 - u2‖ ≤ Real.sqrt 2 * (‖w‖ / d) := by
    have h4 : ‖u1 - u2‖ ^ 2 ≤ 2 * (‖w‖ / d) ^ 2 := by
      rw [h_u1_u2_dist_sq]
      linarith [h_1min_c']
    have h5 : 0 ≤ ‖u1 - u2‖ := by positivity
    have h6 : 0 ≤ Real.sqrt 2 * (‖w‖ / d) := by positivity
    have h7 : (Real.sqrt 2 * (‖w‖ / d)) ^ 2 = 2 * (‖w‖ / d) ^ 2 := by
      have h8 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      calc (Real.sqrt 2 * (‖w‖ / d)) ^ 2
        = (Real.sqrt 2) ^ 2 * (‖w‖ / d) ^ 2 := by ring
      _ = 2 * (‖w‖ / d) ^ 2 := by rw [h8] <;> ring
    have h9 : ‖u1 - u2‖ ^ 2 ≤ (Real.sqrt 2 * (‖w‖ / d)) ^ 2 := by
      rw [h7]; exact h4
    have h10 : |‖u1 - u2‖| ≤ |Real.sqrt 2 * (‖w‖ / d)| := (sq_le_sq).mp h9
    have h11 : 0 ≤ Real.sqrt 2 * (‖w‖ / d) := by positivity
    simpa [h5, abs_of_nonneg h11] using h10

  have h_dir_bound2 : ‖P1 - P0‖ ≤ 4 * Real.sqrt 2 * ε / d := by
    calc ‖P1 - P0‖ ≤ 2 * ‖u1 - u2‖ := h_dir_bound
      _ ≤ 2 * (Real.sqrt 2 * (‖w‖ / d)) := by gcongr
      _ ≤ 2 * Real.sqrt 2 * ((2 * ε) / d) := by
        have h_w_norm2 : ‖w‖ / d ≤ (2 * ε) / d := by gcongr
        calc 2 * (Real.sqrt 2 * (‖w‖ / d))
          = 2 * Real.sqrt 2 * (‖w‖ / d) := by ring
        _ ≤ 2 * Real.sqrt 2 * ((2 * ε) / d) := by gcongr
      _ = 4 * Real.sqrt 2 * ε / d := by ring

  -- Offset formula: off_ℓ = p - P1 p, off_ℓ₀ = q - P0 q
  have h_p_perp : p - P1 p ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal (K := K) p
  have h_off_ℓ_eq : ℓ.offset = p - P1 p := by
    have h1 : p - P1 p ∈ ℓ.1 := by
      have hP1p : P1 p ∈ K := by
        have h : P1 p ∈ P1.range := ⟨p, rfl⟩
        rw [K.range_starProjection] at h; exact h
      have hneg : -P1 p ∈ K := K.neg_mem hP1p
      have h_vadd : (-P1 p) +ᵥ p ∈ ℓ.1 :=
        (AffineSubspace.vadd_mem_iff_mem_of_mem_direction hneg).mpr hp_mem
      have h_eq : (-P1 p) +ᵥ p = p - P1 p := by
        simp [vadd_eq_add] <;> abel
      exact h_eq ▸ h_vadd
    have h2 : (0 : EuclideanPlane) - (p - P1 p) ∈ Kᗮ := by
      simpa [sub_neg] using Submodule.neg_mem Kᗮ h_p_perp
    have h5 : (orthogonalProjection ℓ.1 0 : EuclideanPlane) = p - P1 p := by
      rw [EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem]
      exact ⟨h1, h2⟩
    simpa [AffineLine.offset] using h5

  let K0 := ℓ₀.1.direction
  have h_q_perp : q - P0 q ∈ K0ᗮ := Submodule.sub_starProjection_mem_orthogonal (K := K0) q
  have h_off_ℓ₀_eq : ℓ₀.offset = q - P0 q := by
    have h1 : q - P0 q ∈ ℓ₀.1 := by
      have hP0q : P0 q ∈ K0 := by
        have h : P0 q ∈ P0.range := ⟨q, rfl⟩
        rw [K0.range_starProjection] at h; exact h
      have hneg : -P0 q ∈ K0 := K0.neg_mem hP0q
      have h_vadd : (-P0 q) +ᵥ q ∈ ℓ₀.1 :=
        (AffineSubspace.vadd_mem_iff_mem_of_mem_direction hneg).mpr hq_in_S0
      have h_eq : (-P0 q) +ᵥ q = q - P0 q := by
        simp [vadd_eq_add] <;> abel
      exact h_eq ▸ h_vadd
    have h2 : (0 : EuclideanPlane) - (q - P0 q) ∈ K0ᗮ := by
      simpa [sub_neg] using Submodule.neg_mem K0ᗮ h_q_perp
    have h5 : (orthogonalProjection ℓ₀.1 0 : EuclideanPlane) = q - P0 q := by
      rw [EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem]
      exact ⟨h1, h2⟩
    simpa [AffineLine.offset] using h5

  -- Offset difference bound
  have h_off_diff : ℓ.offset - ℓ₀.offset = (p - q) - P1 (p - q) + (P0 - P1) q := by
    rw [h_off_ℓ_eq, h_off_ℓ₀_eq]
    simp [P1.map_sub, P0.map_sub] <;> abel

  have h_off_norm : ‖ℓ.offset - ℓ₀.offset‖ ≤ ε + ‖P1 - P0‖ * ‖q‖ := by
    rw [h_off_diff]
    calc ‖(p - q) - P1 (p - q) + (P0 - P1) q‖
        ≤ ‖(p - q) - P1 (p - q)‖ + ‖(P0 - P1) q‖ := norm_add_le _ _
      _ ≤ ‖p - q‖ + ‖P0 - P1‖ * ‖q‖ := by
        have h7 : ‖(p - q) - P1 (p - q)‖ ≤ ‖p - q‖ := by
          let x := p - q
          have h_eq : x - P1 x = Kᗮ.starProjection x := by
            have h : Kᗮ.starProjection x = x - K.starProjection x := by
              rw [Submodule.starProjection_orthogonal K]
              <;> simp
            have hP1 : P1 = K.starProjection := by rfl
            rw [hP1]
            exact h.symm
          rw [h_eq]
          exact Submodule.norm_starProjection_apply_le (K := Kᗮ) x
        have h9 : ‖(P0 - P1) q‖ ≤ ‖P0 - P1‖ * ‖q‖ := (P0 - P1).le_opNorm q
        exact add_le_add h7 h9
      _ ≤ ε + ‖P1 - P0‖ * ‖q‖ := by
        have h10 : ‖p - q‖ = dist q p := by
          rw [norm_sub_rev] <;> simp [dist_eq_norm]
        have h11 : ‖P0 - P1‖ = ‖P1 - P0‖ := norm_sub_rev P0 P1
        rw [h10, h11]
        exact add_le_add h_dist_p (le_refl _)

  have h_off_bound : ‖ℓ.offset - ℓ₀.offset‖ ≤ ε + 8 * Real.sqrt 2 * ε / d := by
    calc ‖ℓ.offset - ℓ₀.offset‖ ≤ ε + ‖P1 - P0‖ * ‖q‖ := h_off_norm
      _ ≤ ε + (4 * Real.sqrt 2 * ε / d) * 2 := by gcongr <;> linarith
      _ = ε + 8 * Real.sqrt 2 * ε / d := by ring

  -- Total distance
  have h_total : dist ℓ ℓ₀ ≤ ε + 12 * Real.sqrt 2 * ε / d := by
    have h_dist_def : dist ℓ ℓ₀ = ‖P1 - P0‖ + ‖ℓ.offset - ℓ₀.offset‖ := by
      rfl
    rw [h_dist_def]
    calc ‖P1 - P0‖ + ‖ℓ.offset - ℓ₀.offset‖
        ≤ (4 * Real.sqrt 2 * ε / d) + (ε + 8 * Real.sqrt 2 * ε / d) := by gcongr
      _ = ε + 12 * Real.sqrt 2 * ε / d := by ring

  -- Final bound with ε = 2δ
  have h_sqrt2_le : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left] <;> norm_num
  have h_final : ε + 12 * Real.sqrt 2 * ε / d ≤ 200 * (δ + δ / d) := by
    dsimp only [ε]
    have h_posd : 0 < d := hd_pos'
    have h1 : 12 * Real.sqrt 2 * (2 * δ) ≤ 48 * δ := by
      have h_sqrt : Real.sqrt 2 ≤ 2 := h_sqrt2_le
      calc 12 * Real.sqrt 2 * (2 * δ)
        ≤ 12 * (2 : ℝ) * (2 * δ) := by gcongr <;> linarith
      _ = 48 * δ := by ring
    have h2 : 12 * Real.sqrt 2 * (2 * δ) / d ≤ 48 * δ / d := by
      gcongr
    have h3 : 2 * δ + 12 * Real.sqrt 2 * (2 * δ) / d ≤ 2 * δ + 48 * δ / d := by linarith
    have h4 : 2 * δ + 48 * δ / d ≤ 200 * (δ + δ / d) := by
      have h5 : 2 * δ ≤ 200 * δ := by linarith [hδ_pos]
      have h6 : 48 * δ / d ≤ 200 * δ / d := by
        have h61 : (48 : ℝ) ≤ 200 := by norm_num
        gcongr
      have h7 : 200 * (δ + δ / d) = 200 * δ + 200 * δ / d := by ring
      rw [h7]
      linarith
    linarith

  exact ⟨ℓ₀, hq_in_S0, hq'_in_S0, le_trans h_total h_final⟩

end DirecretisedFurstenbergEstimate.Phase2
