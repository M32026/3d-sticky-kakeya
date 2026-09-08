/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Analysis.InnerProductSpace
public import Kakeya.DimensionN.Prism
public import Kakeya.Thickness.Basic
public import Kakeya.Thickness.Projection
public import Mathlib.Geometry.Euclidean.Projection

/-!
# Outer prism

We show the existence of a prism containing a given set of comparable size.

-/

@[expose] public section

open Metric EuclideanGeometry

variable
  {V E}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MetricSpace E] [NormedAddTorsor V E]

namespace epsilonOuterPrism

/-- Construction of `basis` in `epsilonOuterPrism : PrismNDim` -/
noncomputable def basis
    {n : ℕ} (hn : Module.finrank ℝ V = n)
    {s : Set E} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) :
    OrthonormalBasis (Fin n) ℝ V := by
  induction n generalizing V E with
  | zero =>
    exact (stdOrthonormalBasis ℝ V).reindex (finCongr hn)
  | succ n ih =>
    let hAex := hs.isBounded.exists_cthickening_thickness (𝕜 := ℝ) hn hε
    let A := hAex.choose
    haveI : Nonempty A := hAex.choose_spec.1
    -- Recursively obtain an ONB of `A.direction` and extend it by one orthogonal direction.
    exact ih hAex.choose_spec.2.1 (hs.image <| (orthogonalProjection A).continuous)
      |>.extend_codim_one hn

/-- Construction of `center` in `epsilonOuterPrism : PrismNDim` -/
noncomputable def center
    {n : ℕ} (hn : Module.finrank ℝ V = n)
    {s : Set E} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) : E := by
  induction n generalizing V E with
  | zero =>
    exact Classical.arbitrary E
  | succ n ih =>
    let hAex := hs.isBounded.exists_cthickening_thickness (𝕜 := ℝ) hn hε
    let A := hAex.choose
    haveI : Nonempty A := hAex.choose_spec.1
    exact ih hAex.choose_spec.2.1 (hs.image <| (orthogonalProjection A).continuous) |>.val

-- set_option trace.profiler.useHeartbeats true in
-- set_option trace.profiler true in
theorem basis_repr_of_le
    {m : ℕ} (hn : Module.finrank ℝ V = m + 1)
    {s : Set E} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) (x : E) (k : Fin m) :
    let hAex := hs.isBounded.exists_cthickening_thickness (𝕜 := ℝ) hn hε
    let A := hAex.choose
    haveI : Nonempty A := hAex.choose_spec.1
    let hn' := hAex.choose_spec.2.1
    let hs' := hs.image <| (orthogonalProjection A).continuous
    (basis hn hs hε).repr (x -ᵥ center hn hs hε) k.castSucc =
      (basis hn' hs' hε).repr (orthogonalProjection A x -ᵥ center hn' hs' hε) k := by
  intro hAex A hn' hs'
  haveI : Nonempty A := hAex.choose_spec.1
  set b := basis hn' hs' hε
  have hbasis_eq : basis hn hs hε = b.extend_codim_one hn := rfl
  have hcenter_eq : center hn hs hε = ((center hn' hs' hε : ↥A) : E) := rfl
  rw [hbasis_eq, b.extend_codim_one_repr_apply, b.repr_apply_apply,
      Submodule.coe_inner, AffineSubspace.coe_vsub, hcenter_eq]
  exact EuclideanGeometry.inner_vsub_eq_inner_orthogonalProjection_vsub (b k).2 x _

/-- The absolute value of the last coordinate of `x -ᵥ center hn hs hε` in the orthonormal basis
`basis hn hs hε` equals the distance from `x` to the affine subspace `A` produced by
`Bornology.IsBounded.exists_cthickening_thickness`. -/
theorem basis_repr_last_abs_eq_dist
    {m : ℕ} (hn : Module.finrank ℝ V = m + 1)
    {s : Set E} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) (x : E) :
    let hAex := hs.isBounded.exists_cthickening_thickness (𝕜 := ℝ) hn hε
    let A := hAex.choose
    haveI : Nonempty A := hAex.choose_spec.1
    |(basis hn hs hε).repr (x -ᵥ center hn hs hε) (Fin.last m)| =
      dist x ((orthogonalProjection A x : ↥A) : E) := by
  intro hAex A
  haveI : Nonempty A := hAex.choose_spec.1
  let hn' := hAex.choose_spec.2.1
  let hs' := hs.image ((orthogonalProjection A).continuous)
  set b_inner := basis hn' hs' hε
  have hbasis_eq : basis hn hs hε = b_inner.extend_codim_one hn := rfl
  set bn := b_inner.extend_codim_one hn (Fin.last m) with hbn_def
  set proj := ((orthogonalProjection A x : ↥A) : E) with hproj_def
  have hcenter_eq : center hn hs hε = ((center hn' hs' hε : ↥A) : E) := rfl
  rw [hbasis_eq, OrthonormalBasis.repr_apply_apply]
  -- Drop the part of `x -ᵥ center` lying inside `A.direction` using `bn ∈ A.directionᗮ`.
  have h_n_orth : bn ∈ A.directionᗮ :=
    b_inner.last_mem_orthogonal_of_extend hn
  have h_in_dir : proj -ᵥ center hn hs hε ∈ A.direction := by
    rw [hcenter_eq]
    exact AffineSubspace.vsub_mem_direction
      (orthogonalProjection A x : ↥A).2 (center hn' hs' hε : ↥A).2
  have hsum : x -ᵥ center hn hs hε = (x -ᵥ proj) + (proj -ᵥ center hn hs hε) :=
    (vsub_add_vsub_cancel _ _ _).symm
  rw [hsum, inner_add_right,
      Submodule.inner_left_of_mem_orthogonal h_in_dir h_n_orth, add_zero]
  -- Now `x -ᵥ proj ∈ A.directionᗮ`, which is 1-dimensional and spanned by the unit vector `bn`.
  have h_xp_orth : x -ᵥ proj ∈ A.directionᗮ :=
    EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal A x
  have hnorm : ‖bn‖ = 1 := (b_inner.extend_codim_one hn).orthonormal.1 (Fin.last m)
  have h_n_inner : inner ℝ bn bn = 1 := by
    rw [real_inner_self_eq_norm_mul_norm, hnorm, mul_one]
  have h_n_ne : bn ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hnorm; exact one_ne_zero hnorm.symm
  have h_dim_perp : Module.finrank ℝ A.directionᗮ = 1 := by
    apply Submodule.finrank_add_finrank_orthogonal'
    rw [hAex.choose_spec.2.1, hn]
  have h_span_eq : A.directionᗮ = Submodule.span ℝ {bn} := by
    refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · rwa [Submodule.span_singleton_le_iff_mem]
    · rw [h_dim_perp, finrank_span_singleton h_n_ne]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c • bn = x -ᵥ proj := by
    rw [← Submodule.mem_span_singleton, ← h_span_eq]; exact h_xp_orth
  rw [dist_eq_norm_vsub, ← hc, real_inner_smul_right, h_n_inner, mul_one,
      norm_smul, Real.norm_eq_abs, hnorm, mul_one]

/-- The last coordinate of `x -ᵥ center hn hs hε` in the orthonormal basis `basis hn hs hε`
is bounded in absolute value by `thickness ℝ s m + ε`. -/
theorem abs_basis_repr_last_le_thickness
    {m : ℕ} (hn : Module.finrank ℝ V = m + 1)
    {s : Set E} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε)
    {x : E} (hx : x ∈ s) :
    |(basis hn hs hε).repr (x -ᵥ center hn hs hε) (Fin.last m)| ≤ thickness ℝ s m + ε := by
  set hAex := hs.isBounded.exists_cthickening_thickness (𝕜 := ℝ) hn hε with hAex_def
  set A := hAex.choose
  haveI : Nonempty A := hAex.choose_spec.1
  rw [basis_repr_last_abs_eq_dist hn hs hε x, dist_orthogonalProjection_eq_infDist]
  have hne : (0 : ℝ) ≤ Metric.thickness ℝ s m + ε :=
    add_nonneg (Metric.thickness_nonneg s m) hε.le
  have hinfE : Metric.infEDist x A ≤ ENNReal.ofReal (Metric.thickness ℝ s m + ε) :=
    Metric.mem_cthickening_iff.mp (hAex.choose_spec.2.2 hx)
  calc Metric.infDist x A
      = (Metric.infEDist x A).toReal := rfl
    _ ≤ (ENNReal.ofReal (Metric.thickness ℝ s m + ε)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hinfE
    _ = Metric.thickness ℝ s m + ε := ENNReal.toReal_ofReal hne

/-- Each coordinate of `x -ᵥ center hn hs hε` in the orthonormal basis `basis hn hs hε`
is bounded in absolute value by `thickness ℝ s k + ε`. -/
theorem basis_repr_le_thickness
    {n : ℕ} (hn : Module.finrank ℝ V = n)
    {s : Set E} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε)
    {x : E} (hx : x ∈ s) (k : Fin n) :
    |(basis hn hs hε).repr (x -ᵥ center hn hs hε) k| ≤ thickness ℝ s k.val + ε := by
  induction n generalizing V E with
  | zero => exact k.elim0
  | succ m ih =>
    induction k using Fin.lastCases with
    | last =>
      simpa using abs_basis_repr_last_le_thickness hn hs hε hx
    | cast i =>
      set hAex := hs.isBounded.exists_cthickening_thickness (𝕜 := ℝ) hn hε
      set A := hAex.choose
      haveI : Nonempty A := hAex.choose_spec.1
      rw [basis_repr_of_le hn hs hε x i]
      calc
        _ ≤ Metric.thickness ℝ ((orthogonalProjection A) '' s) i + ε := by
            refine ih hAex.choose_spec.2.1 (hs.image (orthogonalProjection A).continuous) ?_ i
            use x
        _ ≤ Metric.thickness ℝ s i + ε := by
            apply add_le_add_left
            apply thickness_image_orthogonalProjection_le A hs.isBounded

end epsilonOuterPrism

/-- A prism containing a given compact set, with thicknesses with error ε. -/
noncomputable def epsilonOuterPrism {n : ℕ} (hn : Module.finrank ℝ V = n)
    {s : Set E} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) : PrismNDim n V E :=
  PrismNDim.mk' (epsilonOuterPrism.center hn hs hε)
    (epsilonOuterPrism.basis hn hs hε)
      (fun i ↦ ⟨thickness ℝ s i + ε, add_nonneg (thickness_nonneg s i) hε.le⟩)

theorem epsilonOuterPrism.self_subset {n : ℕ} (hn : Module.finrank ℝ V = n)
    {s : Set E} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) :
    s ⊆ (epsilonOuterPrism hn hs hε).carrier := by
  intro x hx
  rw [PrismNDim.mem_carrier_iff]
  apply basis_repr_le_thickness hn hs hε hx

namespace outerPrism

/-- Existence of the limiting prism data: a center `c` and an orthonormal basis of axes `b` for
which the axis-aligned box with half-widths `thickness ℝ s ·` contains `s`. This is obtained from
`epsilonOuterPrism` by a compactness argument: as `ε → 0` the centers lie in a compact ball and
the bases in the (compact) space of orthonormal frames, so the map `ε ↦ (center ε, frame ε)` has a
cluster point along `atTop`, and the limit inequalities hold there. -/
theorem exists_limit {n : ℕ} (hn : Module.finrank ℝ V = n)
    {s : Set E} (hs : IsCompact s) (hsne : s.Nonempty) :
    ∃ (c : E) (b : OrthonormalBasis (Fin n) ℝ V),
      ∀ x ∈ s, ∀ i, |b.repr (x -ᵥ c) i| ≤ thickness ℝ s i := by
  obtain ⟨p, hp⟩ := hsne
  have hk : ∀ k : ℕ, (0 : ℝ) < 1 / (k + 1) := fun k => by positivity
  have hkle : ∀ k : ℕ, (1 : ℝ) / (k + 1) ≤ 1 := fun k => by
    rw [div_le_one (by positivity)]; simp
  -- the sequence of `(center -ᵥ p, frame)`, living in `V × (Fin n → V)`
  set u : ℕ → V × (Fin n → V) := fun k =>
    (epsilonOuterPrism.center hn hs (hk k) -ᵥ p,
      fun i => epsilonOuterPrism.basis hn hs (hk k) i)
    with hu_def
  set R : ℝ := ∑ i : Fin n, (thickness ℝ s i + 1) with hR_def
  set K : Set (V × (Fin n → V)) :=
    closedBall (0 : V) R ×ˢ {v : Fin n → V | Orthonormal ℝ v}
  have hKcompact : IsCompact K :=
    (isCompact_closedBall (0 : V) R).prod isCompact_orthonormal
  -- per-coordinate inner-product bound at any point
  have hcoord : ∀ k : ℕ, ∀ x ∈ s, ∀ i : Fin n,
      |inner ℝ ((u k).2 i) (x -ᵥ epsilonOuterPrism.center hn hs (hk k))|
        ≤ thickness ℝ s i + 1 / (k + 1) := by
    intro k x hx i
    have := epsilonOuterPrism.basis_repr_le_thickness hn hs (hk k) hx i
    rwa [OrthonormalBasis.repr_apply_apply] at this
  have huK : ∀ k : ℕ, u k ∈ K := by
    intro k
    constructor
    · rw [Metric.mem_closedBall, dist_zero_right]
      rw [← dist_eq_norm_vsub V, dist_comm]
      -- `p` lies in the ε-prism, which sits in the ball of radius `∑ thicknesses`.
      have hpc := (epsilonOuterPrism hn hs (hk k)).carrier_subset_closedBall
        (epsilonOuterPrism.self_subset hn hs (hk k) hp)
      rw [Metric.mem_closedBall] at hpc
      refine le_trans hpc ?_
      rw [hR_def]
      refine Finset.sum_le_sum fun i _ => ?_
      calc
        _ = thickness ℝ s i + 1 / (k + 1) := rfl
        _ ≤ thickness ℝ s i + 1 := by linarith [hkle k]
    · exact (epsilonOuterPrism.basis hn hs (hk k)).orthonormal
  have hmap : Filter.map u Filter.atTop ≤ Filter.principal K :=
    Filter.le_principal_iff.mpr (Filter.Eventually.of_forall (p := fun k => u k ∈ K) huK)
  obtain ⟨⟨cv, v⟩, hcvK, hcluster⟩ := hKcompact.exists_mapClusterPt hmap
  have hvorth : Orthonormal ℝ v := hcvK.2
  set c : E := cv +ᵥ p with hc_def
  -- the key limiting bound, expressed via inner products
  have hlim : ∀ x ∈ s, ∀ i : Fin n, |inner ℝ (v i) (x -ᵥ c)| ≤ thickness ℝ s i := by
    intro x hx i
    set g : V × (Fin n → V) → ℝ :=
      fun q => |inner ℝ (q.2 i) ((x -ᵥ p) - q.1)| with hg_def
    have hgcont : Continuous g := by
      apply continuous_abs.comp
      exact ((continuous_apply i).comp continuous_snd).inner
        ((continuous_const).sub continuous_fst)
    have hgval : g (cv, v) = |inner ℝ (v i) (x -ᵥ c)| := by
      simp only [hg_def, hc_def]
      congr 2
      rw [vsub_vadd_eq_vsub_sub]
    refine le_of_forall_pos_le_add (fun δ hδ => ?_)
    set L : Set ℝ := Set.Iic (thickness ℝ s i + δ) with hL_def
    suffices g (cv, v) ∈ L by
      rw [← hgval]
      simpa only [hL_def, Set.mem_Iic]
    apply IsClosed.mem_of_mapClusterPt
    · exact isClosed_Iic
    · exact MapClusterPt.continuousAt_comp hgcont.continuousAt hcluster
    · have htend : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hδev : ∀ᶠ k : ℕ in Filter.atTop, (1 : ℝ) / (k + 1) ≤ δ := by
        have hx := htend.eventually (gt_mem_nhds hδ)
        filter_upwards [hx] with k hkδ using hkδ.le
      filter_upwards [hδev] with k hkδ
      simp only [hL_def, Set.mem_Iic]
      trans thickness ℝ s i + 1 / (k + 1)
      · simpa [hg_def, hu_def] using hcoord k x hx i
      · linarith
  -- assemble the result, building the orthonormal basis from the limit frame `v`
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ V := by
    rw [Fintype.card_fin, hn]
  refine ⟨c, orthonormalBasisOfCardEqFinrank hvorth hcard, fun x hx i => ?_⟩
  rw [OrthonormalBasis.repr_apply_apply, coe_orthonormalBasisOfCardEqFinrank]
  exact hlim x hx i

/-- Center of the limiting `outerPrism`. -/
noncomputable def center {n : ℕ} (hn : Module.finrank ℝ V = n)
    {s : Set E} (hs : IsCompact s) (hsne : s.Nonempty) : E :=
  (exists_limit hn hs hsne).choose

/-- Orthonormal basis of axes of the limiting `outerPrism`. -/
noncomputable def basis {n : ℕ} (hn : Module.finrank ℝ V = n)
    {s : Set E} (hs : IsCompact s) (hsne : s.Nonempty) : OrthonormalBasis (Fin n) ℝ V :=
  (exists_limit hn hs hsne).choose_spec.choose

/-- Defining property of `outerPrism.center` and `outerPrism.basis`: every point of `s` lies in
the box of half-widths `thickness ℝ s ·`. -/
theorem basis_repr_le {n : ℕ} (hn : Module.finrank ℝ V = n)
    {s : Set E} (hs : IsCompact s) (hsne : s.Nonempty)
    {x : E} (hx : x ∈ s) (i : Fin n) :
    |(basis hn hs hsne).repr (x -ᵥ center hn hs hsne) i| ≤ thickness ℝ s i :=
  (exists_limit hn hs hsne).choose_spec.choose_spec x hx i

end outerPrism

/-- A prism containing a given nonempty compact set `s`, whose thicknesses are exactly the
thicknesses of `s`. Built as the `ε → 0` limit of `epsilonOuterPrism`. -/
noncomputable def outerPrism {n : ℕ} (hn : Module.finrank ℝ V = n)
    {s : Set E} (hs : IsCompact s) (hsne : s.Nonempty) : PrismNDim n V E :=
  PrismNDim.mk' (outerPrism.center hn hs hsne) (outerPrism.basis hn hs hsne)
    (fun i ↦ ⟨thickness ℝ s i, thickness_nonneg s i⟩)

theorem outerPrism.thicknesses_eq {n : ℕ} (hn : Module.finrank ℝ V = n)
    {s : Set E} (hs : IsCompact s) (hsne : s.Nonempty) (i : Fin n) :
    (outerPrism hn hs hsne).thicknesses i = ⟨thickness ℝ s i, thickness_nonneg s i⟩ :=
  congrFun (PrismNDim.thicknesses_mk' _ _ _) i

theorem outerPrism.self_subset {n : ℕ} (hn : Module.finrank ℝ V = n)
    {s : Set E} (hs : IsCompact s) (hsne : s.Nonempty) :
    s ⊆ (outerPrism hn hs hsne).carrier := by
  intro x hx
  rw [PrismNDim.mem_carrier_iff]
  intro i
  rw [show (outerPrism hn hs hsne).basis = outerPrism.basis hn hs hsne from
        PrismNDim.basis_mk' _ _ _,
      show (outerPrism hn hs hsne).center = outerPrism.center hn hs hsne from
        PrismNDim.center_mk' _ _ _,
      outerPrism.thicknesses_eq]
  exact outerPrism.basis_repr_le hn hs hsne hx i
