module

/-
  Helper lemmas for Lemma E rewrite that do NOT depend on AffineLine
  or the main discretised_furstenberg_estimate module.

  Contains:
  - grid_subset_covering_bound
  - y_set_from_grid
  - IsDeltaSSet.finite_union
  - IsDeltaSSet.surjective_isometry_image
  - x_set_from_projection
  - coarse_params_to_T_coarse
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductStructureRescaling.product_structure_rescaling
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace LemmaE

abbrev CoarseSquare (Δ : ℝ) := ℤ × ℤ

/-! ========================================================================
   Helper: IsDeltaSSet transfer under isometry
   ======================================================================== -/

/-- IsDeltaSSet is preserved under surjective isometric images. -/
lemma IsDeltaSSet.surjective_isometry_image {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {δ s C : ℝ} {S : Set X} {f : X → Y} (hf : Isometry f) (hsurj : Function.Surjective f)
    (h : IsDeltaSSet δ s C S) : IsDeltaSSet δ s C (f '' S) := by
  rcases h with ⟨hS_nonempty, hδ_pos, hC_pos, hs_nonneg, hmain⟩
  have h_image_nonempty : (f '' S).Nonempty := hS_nonempty.image f
  let g : Y → X := Function.surjInv hsurj
  have hg : ∀ y, f (g y) = y := Function.rightInverse_surjInv hsurj
  have h_inj : Function.Injective f := by
    intro x y hxy
    have h : dist x y = dist (f x) (f y) := (hf.dist_eq x y).symm
    have h0 : dist (f x) (f y) = 0 := by
      rw [hxy]
      exact dist_self _
    have h1 : dist x y = 0 := by rw [h, h0]
    exact dist_eq_zero.mp h1
  let e : X ≃ᵢ Y :=
    { toFun := f,
      invFun := g,
      left_inv := fun x => h_inj (hg (f x)),
      right_inv := hg,
      isometry_toFun := hf }
  refine ⟨h_image_nonempty, hδ_pos, hC_pos, hs_nonneg, ?_⟩
  intro y r hr
  let x := g y
  have hfx : f x = y := hg y
  have h_eq : (f '' S) ∩ Metric.closedBall y r =
      f '' (S ∩ Metric.closedBall x r) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_image]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hball⟩
      have hball' : dist (f p) (f x) ≤ r := by
        have hy : y = f x := hfx.symm
        rw [hy] at hball
        exact hball
      have hdist : dist p x ≤ r := by
        have h : dist (f p) (f x) = dist p x := hf.dist_eq p x
        rw [h] at hball'
        exact hball'
      exact ⟨p, ⟨hp, hdist⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hdist⟩, rfl⟩
      have hball : dist (f p) y ≤ r := by
        have h : dist (f p) (f x) = dist p x := hf.dist_eq p x
        have h2 : dist (f p) (f x) ≤ r := by rw [h]; exact hdist
        have hy : y = f x := hfx.symm
        rw [hy]
        exact h2
      exact ⟨⟨p, hp, rfl⟩, hball⟩
  rw [h_eq]
  have h2 : Metric.externalCoveringNumber δ.toNNReal (f '' (S ∩ Metric.closedBall x r)) =
      Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall x r) :=
    DiscretisedFurstenbergEstimate.CoveringUtils.externalCoveringNumber_image_isometryEquiv e
  rw [h2]
  have h3 : Metric.externalCoveringNumber δ.toNNReal (f '' S) =
      Metric.externalCoveringNumber δ.toNNReal S :=
    DiscretisedFurstenbergEstimate.CoveringUtils.externalCoveringNumber_image_isometryEquiv e
  rw [h3]
  exact hmain x r hr

/-! ========================================================================
   Helper: Weaken S-set constant
   ======================================================================== -/

lemma IsDeltaSSet.weaken_constant {X : Type*} [PseudoMetricSpace X]
    {δ s C C' : ℝ} {P : Set X}
    (h : IsDeltaSSet δ s C P) (hC_le : C ≤ C') :
    IsDeltaSSet δ s C' P := by
  rcases h with ⟨hP_nonempty, hδ_pos, hC_pos, hs_nonneg, hmain⟩
  have hC'_pos : 0 < C' := by linarith
  refine ⟨hP_nonempty, hδ_pos, hC'_pos, hs_nonneg, ?_⟩
  intro x r hr
  have h4 := hmain x r hr
  have h5 : ENNReal.ofReal C ≤ ENNReal.ofReal C' := ENNReal.ofReal_le_ofReal hC_le
  calc
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal P := h4
    _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal P := by
      gcongr

/-! ========================================================================
   Helper: Finite union of S-sets is an S-set
   ======================================================================== -/

/-- A finite union of at most K nonempty sets, each a (δ,s,C)-set, is a (δ,s,K*C)-set. -/
lemma IsDeltaSSet.finite_union {X : Type*} [PseudoMetricSpace X]
    {δ s C : ℝ} {ι : Type*} [DecidableEq ι] (K : ℝ) (hK_pos : 0 < K)
    (sets : ι → Set X) (ioc : Finset ι)
    (h_ioc_nonempty : ioc.Nonempty)
    (h_card : (ioc.card : ℝ) ≤ K)
    (h_all : ∀ i ∈ ioc, IsDeltaSSet δ s C (sets i)) :
    IsDeltaSSet δ s (K * C) (⋃ i ∈ ioc, sets i) := by
  rcases h_ioc_nonempty with ⟨i0, hi0⟩
  rcases h_all i0 hi0 with ⟨hS_nonempty, hδ_pos, hC_pos', hs_nonneg, _⟩
  have hKC_pos : 0 < K * C := mul_pos hK_pos hC_pos'
  have h_nonempty : (⋃ i ∈ ioc, sets i).Nonempty := by
    rcases hS_nonempty with ⟨x, hx⟩
    refine ⟨x, Set.mem_iUnion₂.mpr ⟨i0, hi0, hx⟩⟩
  refine ⟨h_nonempty, hδ_pos, hKC_pos, hs_nonneg, ?_⟩
  intro x r hr
  have h_inter : (⋃ i ∈ ioc, sets i) ∩ Metric.closedBall x r =
      ⋃ i ∈ ioc, (sets i ∩ Metric.closedBall x r) := by
    ext y; simp [Set.mem_iUnion] <;> tauto
  rw [h_inter]
  have h1 : Metric.externalCoveringNumber δ.toNNReal (⋃ i ∈ ioc, (sets i ∩ Metric.closedBall x r)) ≤
      ∑ i ∈ ioc, Metric.externalCoveringNumber δ.toNNReal (sets i ∩ Metric.closedBall x r) :=
    DiscretisedFurstenbergEstimate.CoveringUtils.externalCoveringNumber_biUnion
      (ε := δ.toNNReal) (s := ioc) (A := fun i => sets i ∩ Metric.closedBall x r)
  have h_add : ∀ (a b : ℕ∞), (↑(a + b) : ENNReal) = (↑a : ENNReal) + (↑b : ENNReal) := by
    intro a b
    exact ENat.toENNReal_add a b
  have h_sum_coe_aux : ∀ (s' : Finset ι) (f : ι → ℕ∞),
      (↑(∑ i ∈ s', f i) : ENNReal) = ∑ i ∈ s', (↑(f i) : ENNReal) := by
    intro s' f
    induction s' using Finset.induction with
    | empty => simp
    | @insert a s ha ih =>
      calc
        (↑(∑ i ∈ insert a s, f i) : ENNReal)
          = (↑(f a + ∑ i ∈ s, f i) : ENNReal) := by rw [Finset.sum_insert ha] <;> rfl
        _ = (↑(f a) : ENNReal) + (↑(∑ i ∈ s, f i) : ENNReal) := h_add (f a) _
        _ = (↑(f a) : ENNReal) + ∑ i ∈ s, (↑(f i) : ENNReal) := by rw [ih]
        _ = ∑ i ∈ insert a s, (↑(f i) : ENNReal) := by rw [Finset.sum_insert ha] <;> rfl
  have h_sum_coe : ∀ (f : ι → ℕ∞),
      (↑(∑ i ∈ ioc, f i) : ENNReal) = ∑ i ∈ ioc, (↑(f i) : ENNReal) :=
    h_sum_coe_aux ioc
  have h1' : (Metric.externalCoveringNumber δ.toNNReal (⋃ i ∈ ioc, (sets i ∩ Metric.closedBall x r)) : ENNReal) ≤
      ∑ i ∈ ioc, (Metric.externalCoveringNumber δ.toNNReal (sets i ∩ Metric.closedBall x r) : ENNReal) := by
    have h_cast : (Metric.externalCoveringNumber δ.toNNReal (⋃ i ∈ ioc, (sets i ∩ Metric.closedBall x r)) : ENNReal) ≤
        (↑(∑ i ∈ ioc, Metric.externalCoveringNumber δ.toNNReal (sets i ∩ Metric.closedBall x r)) : ENNReal) := by
      exact_mod_cast h1
    rw [h_sum_coe (fun i => Metric.externalCoveringNumber δ.toNNReal (sets i ∩ Metric.closedBall x r))] at h_cast
    exact h_cast
  have h2 : ∀ i ∈ ioc,
      (Metric.externalCoveringNumber δ.toNNReal (sets i ∩ Metric.closedBall x r) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
      (Metric.externalCoveringNumber δ.toNNReal (sets i) : ENNReal) := by
    intro i hi
    rcases h_all i hi with ⟨_, _, _, _, hmain⟩
    exact hmain x r hr
  have h_sum : ∑ i ∈ ioc, (Metric.externalCoveringNumber δ.toNNReal (sets i ∩ Metric.closedBall x r) : ENNReal) ≤
      ∑ i ∈ ioc, (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal (sets i) : ENNReal)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact h2 i hi
  have h_main_ineq : (Metric.externalCoveringNumber δ.toNNReal (⋃ i ∈ ioc, (sets i ∩ Metric.closedBall x r)) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
      ∑ i ∈ ioc, (Metric.externalCoveringNumber δ.toNNReal (sets i) : ENNReal) := by
    calc
      _ ≤ ∑ i ∈ ioc, (Metric.externalCoveringNumber δ.toNNReal (sets i ∩ Metric.closedBall x r) : ENNReal) := h1'
      _ ≤ ∑ i ∈ ioc, (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
              (Metric.externalCoveringNumber δ.toNNReal (sets i) : ENNReal)) := h_sum
      _ = ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
              ∑ i ∈ ioc, (Metric.externalCoveringNumber δ.toNNReal (sets i) : ENNReal) := by
        rw [Finset.mul_sum] <;> ring
  have h3 : ∑ i ∈ ioc, (Metric.externalCoveringNumber δ.toNNReal (sets i) : ENNReal) ≤
      (↑ioc.card : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (⋃ i ∈ ioc, sets i) : ENNReal) := by
    have h4 : ∀ i ∈ ioc, (Metric.externalCoveringNumber δ.toNNReal (sets i) : ENNReal) ≤
          (Metric.externalCoveringNumber δ.toNNReal (⋃ j ∈ ioc, sets j) : ENNReal) := by
      intro i hi
      have h_sub : sets i ⊆ (⋃ j ∈ ioc, sets j) := by
        intro x hx
        exact Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩
      exact_mod_cast Metric.externalCoveringNumber_mono_set h_sub
    have h_sum2 : ∑ i ∈ ioc, (Metric.externalCoveringNumber δ.toNNReal (sets i) : ENNReal) ≤
        ∑ i ∈ ioc, (Metric.externalCoveringNumber δ.toNNReal (⋃ j ∈ ioc, sets j) : ENNReal) := by
      apply Finset.sum_le_sum
      intro i hi
      exact h4 i hi
    calc
      _ ≤ _ := h_sum2
      _ = (↑ioc.card : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (⋃ i ∈ ioc, sets i) : ENNReal) := by
        simp [Finset.sum_const] <;> ring
  have h9 : ENNReal.ofReal C * (↑ioc.card : ENNReal) ≤ ENNReal.ofReal (K * C) := by
    have h10 : (↑ioc.card : ENNReal) = ENNReal.ofReal (ioc.card : ℝ) := by
      exact Eq.symm (ENNReal.ofReal_natCast ioc.card)
    rw [h10]
    have h11 : 0 ≤ (ioc.card : ℝ) := by positivity
    have h12 : ENNReal.ofReal C * ENNReal.ofReal (ioc.card : ℝ) = ENNReal.ofReal (C * (ioc.card : ℝ)) := by
      have h_nonneg1 : 0 ≤ C := by linarith
      have h_nonneg2 : 0 ≤ (ioc.card : ℝ) := by positivity
      have h : ENNReal.ofReal (C * (ioc.card : ℝ)) = ENNReal.ofReal C * ENNReal.ofReal (ioc.card : ℝ) := by
        rw [ENNReal.ofReal_mul] <;> assumption
      exact h.symm
    rw [h12]
    have h13 : C * (ioc.card : ℝ) ≤ K * C := by
      have h14 : C * (ioc.card : ℝ) ≤ C * K := by gcongr
      linarith
    exact ENNReal.ofReal_le_ofReal h13
  calc
    (Metric.externalCoveringNumber δ.toNNReal (⋃ i ∈ ioc, (sets i ∩ Metric.closedBall x r)) : ENNReal)
      ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          ∑ i ∈ ioc, (Metric.externalCoveringNumber δ.toNNReal (sets i) : ENNReal) := h_main_ineq
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          ((↑ioc.card : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (⋃ i ∈ ioc, sets i) : ENNReal)) := by gcongr
    _ = (ENNReal.ofReal C * (↑ioc.card : ENNReal)) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal (⋃ i ∈ ioc, sets i) : ENNReal) := by ring
    _ ≤ ENNReal.ofReal (K * C) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal (⋃ i ∈ ioc, sets i) : ENNReal) := by
      gcongr
      <;> exact h9

/-! ========================================================================
   Grid covering bound
   ======================================================================== -/

/-- A Δ-grid subset contained in a ball of radius r has external Δ-covering
    number at most 5r/Δ. -/
lemma grid_subset_covering_bound
    {Δ r y : ℝ} (hΔ_pos : 0 < Δ) (hr : Δ ≤ r)
    {Y : Set ℝ} (hY_grid : Y ⊆ integerGrid Δ)
    {s : Set ℝ} (hsY : s ⊆ Y) (hsB : s ⊆ Metric.closedBall y r) :
    (Metric.externalCoveringNumber Δ.toNNReal s : ENNReal) ≤ ENNReal.ofReal (5 * r / Δ) := by
  have hS_grid : s ⊆ integerGrid Δ := Set.Subset.trans hsY hY_grid
  have hS_int : s ⊆ Set.Icc (y - r) (y + r) := by
    intro x hx
    have h : dist x y ≤ r := hsB hx
    have h' : |x - y| ≤ r := by simpa [Real.dist_eq] using h
    have h'' : y - r ≤ x ∧ x ≤ y + r := by
      rw [abs_sub_le_iff] at h'
      exact ⟨by linarith, by linarith⟩
    exact ⟨h''.1, h''.2⟩
  let a : ℤ := ⌈(y - r) / Δ⌉
  let b : ℤ := ⌊(y + r) / Δ⌋
  have h_ab : a ≤ b := by
    have h2 : r / Δ ≥ 1 := by
      calc r / Δ ≥ Δ / Δ := by gcongr
           _ = 1 := by field_simp [hΔ_pos.ne'] <;> ring
    have h11 : (y + r) / Δ - (y - r) / Δ = 2 * r / Δ := by
      field_simp [hΔ_pos.ne'] <;> ring
    have h12 : 2 * r / Δ ≥ 2 := by
      calc 2 * r / Δ = 2 * (r / Δ) := by ring
           _ ≥ 2 * 1 := by gcongr
           _ = 2 := by ring
    have h13 : (y + r) / Δ - (y - r) / Δ ≥ 2 := by rw [h11]; exact h12
    have h3 : (a : ℝ) ≤ (y - r) / Δ + 1 := by
      have h31 : (a : ℝ) < (y - r) / Δ + 1 := Int.ceil_lt_add_one ((y - r) / Δ)
      exact h31.le
    have h4 : (y + r) / Δ - 1 ≤ (b : ℝ) := by
      have h41 : (y + r) / Δ - 1 < (b : ℝ) := Int.sub_one_lt_floor ((y + r) / Δ)
      exact h41.le
    have h5 : (a : ℝ) ≤ (b : ℝ) := by
      calc (a : ℝ) ≤ (y - r) / Δ + 1 := h3
           _ ≤ (y + r) / Δ - 1 := by linarith [h13]
           _ ≤ (b : ℝ) := h4
    exact_mod_cast h5
  let g : ℝ → ℤ := fun x => ⌊x / Δ⌋
  have h1 : ∀ x ∈ s, ∃ k : ℤ, x = Δ * (k : ℝ) ∧ g x = k := by
    intro x hx
    have hx_grid : x ∈ integerGrid Δ := hS_grid hx
    rcases hx_grid with ⟨k, hk⟩
    have hgk : g x = k := by
      simp only [g]
      have hdiv : x / Δ = (k : ℝ) := by
        rw [hk]; field_simp [hΔ_pos.ne'] <;> ring
      rw [hdiv]; simp
    exact ⟨k, hk, hgk⟩
  have h_img : s ⊆ (fun k : ℤ => Δ * (k : ℝ)) '' (Finset.Icc a b : Set ℤ) := by
    intro x hx
    rcases h1 x hx with ⟨k, hxk, hgk⟩
    have h2 : y - r ≤ x := (hS_int hx).1
    have h3 : x ≤ y + r := (hS_int hx).2
    have h4 : (y - r) / Δ ≤ (k : ℝ) := by
      have h5 : (y - r) ≤ Δ * (k : ℝ) := by linarith [hxk]
      calc (y - r) / Δ ≤ (Δ * (k : ℝ)) / Δ := by gcongr
           _ = (k : ℝ) := by field_simp [hΔ_pos.ne'] <;> ring
    have h6 : (k : ℝ) ≤ (y + r) / Δ := by
      have h7 : Δ * (k : ℝ) ≤ y + r := by linarith [hxk]
      calc (k : ℝ) = (Δ * (k : ℝ)) / Δ := by field_simp [hΔ_pos.ne'] <;> ring
           _ ≤ (y + r) / Δ := by gcongr
    have ha : a ≤ k := Int.ceil_le.mpr h4
    have hb : k ≤ b := Int.le_floor.mpr h6
    exact ⟨k, Finset.mem_Icc.mpr ⟨ha, hb⟩, hxk.symm⟩
  have h_finite : Set.Finite s := Set.Finite.subset (Set.Finite.image _ (Finset.finite_toSet _)) h_img
  let fs : Finset ℝ := h_finite.toFinset
  have hfs : (fs : Set ℝ) = s := h_finite.coe_toFinset
  have h_cover : (Metric.externalCoveringNumber Δ.toNNReal s : ENNReal) ≤ (↑fs.card : ENNReal) := by
    have h_is_cover : Metric.IsCover Δ.toNNReal s (fs : Set ℝ) := by
      intro x hx
      have hxf : x ∈ (fs : Set ℝ) := by
        rw [hfs]
        exact hx
      have hball : edist x x ≤ (Δ.toNNReal : ENNReal) := by
        simp
      exact ⟨x, hxf, hball⟩
    have h1 : Metric.externalCoveringNumber Δ.toNNReal s ≤ (fs : Set ℝ).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard h_is_cover
    have h2 : (fs : Set ℝ).encard = ↑fs.card := by simp
    have h3 : Metric.externalCoveringNumber Δ.toNNReal s ≤ ↑fs.card := by
      rw [h2] at h1
      exact h1
    exact_mod_cast h3
  have h_g_inj : Set.InjOn g (fs : Set ℝ) := by
    intro x hx y hy hxy
    have hxS : x ∈ s := by
      have h : x ∈ (fs : Set ℝ) := hx
      rw [hfs] at h
      exact h
    have hyS : y ∈ s := by
      have h : y ∈ (fs : Set ℝ) := hy
      rw [hfs] at h
      exact h
    rcases h1 x hxS with ⟨kx, hx_eq, hgx⟩
    rcases h1 y hyS with ⟨ky, hy_eq, hgy⟩
    have h_k_eq : kx = ky := by rw [hgx, hgy] at hxy; exact hxy
    rw [hx_eq, hy_eq, h_k_eq]
  let K : Finset ℤ := Finset.image g fs
  have hK_card : K.card = fs.card := by
    rw [Finset.card_image_of_injOn]; exact h_g_inj
  have hK_sub : K ⊆ Finset.Icc a b := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨x, hx, rfl⟩
    have hxS : x ∈ s := by
      have h : x ∈ (fs : Set ℝ) := hx
      rw [hfs] at h
      exact h
    rcases h1 x hxS with ⟨kx, hxk, hgk⟩
    have h_k_eq : g x = kx := hgk
    rw [h_k_eq] at *
    have h2 : y - r ≤ x := (hS_int hxS).1
    have h3 : x ≤ y + r := (hS_int hxS).2
    have h4 : (y - r) / Δ ≤ (kx : ℝ) := by
      have h5 : y - r ≤ Δ * (kx : ℝ) := by
        calc y - r ≤ x := h2
             _ = Δ * (kx : ℝ) := by exact hxk
      calc (y - r) / Δ ≤ (Δ * (kx : ℝ)) / Δ := by gcongr
           _ = (kx : ℝ) := by field_simp [hΔ_pos.ne'] <;> ring
    have h6 : (kx : ℝ) ≤ (y + r) / Δ := by
      have h7 : Δ * (kx : ℝ) ≤ y + r := by
        calc Δ * (kx : ℝ) = x := by exact hxk.symm
             _ ≤ y + r := h3
      calc (kx : ℝ) = (Δ * (kx : ℝ)) / Δ := by field_simp [hΔ_pos.ne'] <;> ring
           _ ≤ (y + r) / Δ := by gcongr
    have ha : a ≤ kx := Int.ceil_le.mpr h4
    have hb : kx ≤ b := Int.le_floor.mpr h6
    exact Finset.mem_Icc.mpr ⟨ha, hb⟩
  have h_card_bound : K.card ≤ (Finset.Icc a b).card := Finset.card_le_card hK_sub
  have h_alg : ((Finset.Icc a b).card : ℝ) ≤ 2 * r / Δ + 1 := by
    have h_card_formula : ((Finset.Icc a b).card : ℝ) = (b : ℝ) - (a : ℝ) + 1 := by
      simp [h_ab, Finset.card_eq_zero] <;> norm_cast <;> omega
    rw [h_card_formula]
    have h2 : (b : ℝ) ≤ (y + r) / Δ := Int.floor_le _
    have h3 : (a : ℝ) ≥ (y - r) / Δ := Int.le_ceil _
    have h7 : (b : ℝ) - (a : ℝ) ≤ (y + r) / Δ - (y - r) / Δ := by linarith
    have h8 : (y + r) / Δ - (y - r) / Δ = 2 * r / Δ := by
      field_simp [hΔ_pos.ne'] <;> ring
    have h9 : (b : ℝ) - (a : ℝ) ≤ 2 * r / Δ := by
      calc (b : ℝ) - (a : ℝ) ≤ (y + r) / Δ - (y - r) / Δ := h7
           _ = 2 * r / Δ := h8
    have h10 : (b : ℝ) - (a : ℝ) + 1 ≤ 2 * r / Δ + 1 := by
      exact add_le_add h9 (by norm_num)
    exact h10
  have h_card5 : (fs.card : ℝ) ≤ 5 * r / Δ := by
    have h4 : (K.card : ℝ) ≤ 2 * r / Δ + 1 := by
      have h41 : K.card ≤ (Finset.Icc a b).card := h_card_bound
      have h42 : (K.card : ℝ) ≤ ((Finset.Icc a b).card : ℝ) := by exact_mod_cast h41
      exact le_trans h42 h_alg
    have h5 : 2 * r / Δ + 1 ≤ 3 * r / Δ := by
      have h6 : 1 ≤ r / Δ := by
        have h7 : Δ / Δ ≤ r / Δ := by gcongr
        have h8 : Δ / Δ = 1 := by field_simp [hΔ_pos.ne'] <;> ring
        rw [h8] at h7
        exact h7
      have h9 : 2 * r / Δ + 1 ≤ 2 * r / Δ + r / Δ := by gcongr
      have h10 : 2 * r / Δ + r / Δ = 3 * r / Δ := by ring
      rw [h10] at h9
      exact h9
    have h10 : (K.card : ℝ) = (fs.card : ℝ) := by exact_mod_cast hK_card
    have h11 : (fs.card : ℝ) ≤ 3 * r / Δ := by
      calc (fs.card : ℝ) = (K.card : ℝ) := h10.symm
           _ ≤ 2 * r / Δ + 1 := h4
           _ ≤ 3 * r / Δ := h5
    have h12 : 3 * r / Δ ≤ 5 * r / Δ := by
      have h13 : 0 ≤ r := by linarith
      have h14 : 0 ≤ Δ := by linarith
      have h15 : 0 ≤ r / Δ := div_nonneg h13 h14
      have h16 : (3 : ℝ) ≤ 5 := by norm_num
      have h17 : 3 * (r / Δ) ≤ 5 * (r / Δ) := mul_le_mul_of_nonneg_right h16 h15
      ring_nf at h17 ⊢
      exact h17
    calc (fs.card : ℝ) ≤ 3 * r / Δ := h11
         _ ≤ 5 * r / Δ := h12
  calc
    (Metric.externalCoveringNumber Δ.toNNReal s : ENNReal)
      ≤ (↑fs.card : ENNReal) := h_cover
    _ ≤ ENNReal.ofReal (5 * r / Δ) := by
      have h_eq : (↑fs.card : ENNReal) = ENNReal.ofReal (fs.card : ℝ) := by simp
      rw [h_eq]
      exact ENNReal.ofReal_le_ofReal h_card5

/-- Any nonempty set Y is a (Δ, u, 5*Δ^{-u})-set, because C*Δ^u = 5 ≥ 1
    makes the S-set inequality trivial via monotonicity. -/
lemma y_set_from_grid
    {Δ u : ℝ} (hΔ_pos : 0 < Δ) (hΔ_le_one : Δ ≤ 1)
    (hu_pos : 0 < u) (hu_le_one : u ≤ 1)
    {Y : Set ℝ}
    (hY_grid : Y ⊆ integerGrid Δ)
    (hY_bounded : Y ⊆ Set.Icc (-1 : ℝ) 1)
    (hY_nonempty : Y.Nonempty) :
    IsDeltaSSet Δ u (5 * Real.rpow Δ (-u)) Y := by
  have h_rpow_pos : 0 < Real.rpow Δ (-u) := Real.rpow_pos_of_pos hΔ_pos (-u)
  have hC_pos : 0 < 5 * Real.rpow Δ (-u) := by
    have h : 0 < (5 : ℝ) := by norm_num
    exact mul_pos h h_rpow_pos
  have h_main : ∀ (x : ℝ) (r : ℝ), Δ ≤ r →
      (Metric.externalCoveringNumber Δ.toNNReal (Y ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal (5 * Real.rpow Δ (-u)) * (ENNReal.ofReal r) ^ u *
          (Metric.externalCoveringNumber Δ.toNNReal Y : ENNReal) := by
    intro x r hr
    have h_sub : Y ∩ Metric.closedBall x r ⊆ Y := by simp
    have h1' : Metric.externalCoveringNumber Δ.toNNReal (Y ∩ Metric.closedBall x r) ≤
        Metric.externalCoveringNumber Δ.toNNReal Y :=
      Metric.externalCoveringNumber_mono_set h_sub
    have h1 : (Metric.externalCoveringNumber Δ.toNNReal (Y ∩ Metric.closedBall x r) : ENNReal) ≤
        (Metric.externalCoveringNumber Δ.toNNReal Y : ENNReal) := by
      exact_mod_cast h1'
    have h_posr : 0 < r := by linarith
    have h3 : Real.rpow r (-u) ≤ 5 * Real.rpow Δ (-u) := by
      have h4 : Real.rpow r (-u) ≤ Real.rpow Δ (-u) :=
        Real.rpow_le_rpow_of_nonpos hΔ_pos hr (by linarith)
      have h5 : 0 < Real.rpow Δ (-u) := h_rpow_pos
      calc Real.rpow r (-u) ≤ Real.rpow Δ (-u) := h4
           _ ≤ 5 * Real.rpow Δ (-u) := by nlinarith
    have h4 : ENNReal.ofReal (Real.rpow r (-u)) ≤ ENNReal.ofReal (5 * Real.rpow Δ (-u)) :=
      ENNReal.ofReal_le_ofReal h3
    have h5 : ENNReal.ofReal (Real.rpow r (-u)) * (ENNReal.ofReal r) ^ u = 1 := by
      have h6 : ENNReal.ofReal (Real.rpow r (-u)) = (ENNReal.ofReal r) ^ (-u) := by
        have h61 : Real.rpow r (-u) = r ^ (-u) := by rfl
        rw [h61]
        exact (ENNReal.ofReal_rpow_of_pos h_posr).symm
      rw [h6]
      have h7 : (ENNReal.ofReal r) ≠ 0 := by
        have h71 : 0 < ENNReal.ofReal r := ENNReal.ofReal_pos.mpr h_posr
        exact h71.ne'
      have h8 : (ENNReal.ofReal r) ≠ ⊤ := by simp
      rw [← ENNReal.rpow_add (-u) u h7 h8] <;> ring_nf <;> norm_num
    have h9 : 1 ≤ ENNReal.ofReal (5 * Real.rpow Δ (-u)) * (ENNReal.ofReal r) ^ u := by
      calc
        (1 : ENNReal)
          = ENNReal.ofReal (Real.rpow r (-u)) * (ENNReal.ofReal r) ^ u := h5.symm
        _ ≤ ENNReal.ofReal (5 * Real.rpow Δ (-u)) * (ENNReal.ofReal r) ^ u := by gcongr
    calc
      (Metric.externalCoveringNumber Δ.toNNReal (Y ∩ Metric.closedBall x r) : ENNReal)
        ≤ (Metric.externalCoveringNumber Δ.toNNReal Y : ENNReal) := h1
      _ = (1 : ENNReal) * (Metric.externalCoveringNumber Δ.toNNReal Y : ENNReal) := by simp
      _ ≤ ENNReal.ofReal (5 * Real.rpow Δ (-u)) * (ENNReal.ofReal r) ^ u *
            (Metric.externalCoveringNumber Δ.toNNReal Y : ENNReal) := by
        gcongr
  exact ⟨hY_nonempty, hΔ_pos, hC_pos, by linarith, h_main⟩

/-! ========================================================================
   X_y S-set from projection
   ======================================================================== -/

/-- X_y is a union of projection sets for squares in row y.
    If each row has at most K squares, and each projection set is a (Δ,s,C)-set,
    then X_y is a (Δ,s,K*C)-set. -/
lemma x_set_from_projection
    {Δ s C K : ℝ} (hΔ_pos : 0 < Δ) (hs_pos : 0 < s) (hC_pos : 0 < C) (hK_pos : 0 < K)
    {Q0 : Finset (CoarseSquare Δ)}
    {Y : Set ℝ} {X : ℝ → Set ℝ}
    (projData : ∀ Q ∈ Q0, Set ℝ)
    (hY_def : Y = (fun Q : CoarseSquare Δ => Δ * (Q.2 : ℝ)) '' (Q0 : Set (CoarseSquare Δ)))
    (hX_def : ∀ y, X y = ⋃ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0) (h : Δ * (Q.2 : ℝ) = y), projData Q hQ)
    (h_proj_sset : ∀ Q hQ, IsDeltaSSet Δ s C (projData Q hQ))
    (h_max_fiber : ∀ y ∈ Y,
      (Q0.filter (fun Q => Δ * (Q.2 : ℝ) = y)).card ≤ K) :
    ∀ y ∈ Y, IsDeltaSSet Δ s (K * C) (X y) := by
  intro y hy
  let fiber_y : Finset (CoarseSquare Δ) := Q0.filter (fun Q => Δ * (Q.2 : ℝ) = y)
  have h_fiber_sub_Q0 : fiber_y ⊆ Q0 := by
    simp [fiber_y, Finset.filter_subset]
  have h_fiber_nonempty : fiber_y.Nonempty := by
    have h_img : y ∈ (fun Q : CoarseSquare Δ => Δ * (Q.2 : ℝ)) '' (Q0 : Set (CoarseSquare Δ)) := by
      rw [←hY_def]; exact hy
    rcases h_img with ⟨Q, hQ, h_eq⟩
    exact ⟨Q, Finset.mem_filter.mpr ⟨hQ, h_eq⟩⟩
  have h_card : (fiber_y.card : ℝ) ≤ K := h_max_fiber y hy
  let projData_fiber : CoarseSquare Δ → Set ℝ := fun Q =>
    if h : Q ∈ Q0 then projData Q h else ∅
  have hQ1 : ∀ Q ∈ fiber_y, Q ∈ Q0 := fun Q hQ => h_fiber_sub_Q0 hQ
  have h_eq : X y = ⋃ Q ∈ fiber_y, projData_fiber Q := by
    rw [hX_def y]
    ext z
    simp only [Set.mem_iUnion, projData_fiber]
    constructor
    · rintro ⟨Q, hQ, h_eq_y, hz⟩
      have hQ' : Q ∈ fiber_y := by simp [fiber_y, Finset.mem_filter, hQ, h_eq_y]
      refine ⟨Q, hQ', ?_⟩
      rw [dif_pos hQ]; exact hz
    · rintro ⟨Q, hQ', hz⟩
      have hQ : Q ∈ Q0 := hQ1 Q hQ'
      have h_eq_y : Δ * (Q.2 : ℝ) = y := by
        simp [fiber_y, Finset.mem_filter] at hQ' <;> tauto
      refine ⟨Q, hQ, h_eq_y, ?_⟩
      rwa [dif_pos hQ] at hz
  have h_all : ∀ Q ∈ fiber_y, IsDeltaSSet Δ s C (projData_fiber Q) := by
    intro Q hQ
    have hQ0 : Q ∈ Q0 := hQ1 Q hQ
    have h_eq2 : projData_fiber Q = projData Q hQ0 := by
      simp [projData_fiber, hQ0]
    rw [h_eq2]
    exact h_proj_sset Q hQ0
  rw [h_eq]
  exact IsDeltaSSet.finite_union K hK_pos projData_fiber fiber_y h_fiber_nonempty h_card h_all

/-! ========================================================================
   Coarse parameter set to ℝ×ℝ conversion
   ======================================================================== -/

/-- Convert coarseParams (EuclideanSpace ℝ (Fin 2)) to T_coarse (ℝ×ℝ) and transfer properties. -/
lemma coarse_params_to_T_coarse
    {Δ : ℝ} (hΔ_pos : 0 < Δ)
    {Y : Set ℝ} {X : ℝ → Set ℝ}
    {fineParams coarseParams : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    (h_coarse_bounded : ∀ z ∈ productIncidenceSet Y X,
      coarseParams z ⊆ {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ Set.Icc (-2 : ℝ) 2 ∧ p 1 ∈ Set.Icc (-2 : ℝ) 2})
    (h_coarse_eq : ∀ z ∈ productIncidenceSet Y X,
      coarseParams z = scaleParameters Δ (fineParams z))
    (h_coarse_resid : ∀ z ∈ productIncidenceSet Y X,
      ∀ θ ∈ coarseParams z, lineResidual z θ ≤ 3 * Δ) :
    ∃ (T_coarse : ∀ (z : ℝ × ℝ),
        z ∈ (⋃ y ∈ Y, X y ×ˢ {y}) → Set (ℝ × ℝ)),
      (∀ z hz, T_coarse z hz ⊆ Set.Icc (-2 : ℝ) 2 ×ˢ Set.Icc (-2 : ℝ) 2) ∧
      (∀ z hz, ∀ (p : ℝ × ℝ), p ∈ T_coarse z hz →
        |p.1 * z.2 + p.2 - z.1| ≤ 3 * Δ) := by
  let S : Set (EuclideanSpace ℝ (Fin 2)) := productIncidenceSet Y X
  let e : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ := fun p => (p 0, p 1)
  let z_of_pair : ℝ × ℝ → EuclideanSpace ℝ (Fin 2) := fun z =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => if i = 0 then z.1 else z.2)
  let T_coarse (z : ℝ × ℝ) (_ : z ∈ (⋃ y ∈ Y, X y ×ˢ {y})) : Set (ℝ × ℝ) :=
    e '' coarseParams (z_of_pair z)
  have hS_eq : ∀ (z : ℝ × ℝ), z ∈ (⋃ y ∈ Y, X y ×ˢ {y}) ↔ z_of_pair z ∈ S := by
    intro z
    simp [S, productIncidenceSet, Set.mem_iUnion, z_of_pair, e] <;> aesop
  have h_coarse_bounds : ∀ z ∈ S, coarseParams z ⊆ {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ Set.Icc (-2 : ℝ) 2 ∧ p 1 ∈ Set.Icc (-2 : ℝ) 2} :=
    h_coarse_bounded
  refine ⟨T_coarse, ?_, ?_⟩
  · intro z hz p hp
    rcases (Set.mem_image e (coarseParams (z_of_pair z)) p).mp hp with ⟨θ, hθ, rfl⟩
    have hb : θ 0 ∈ Set.Icc (-2 : ℝ) 2 ∧ θ 1 ∈ Set.Icc (-2 : ℝ) 2 := by
      have h_sub : coarseParams (z_of_pair z) ⊆ {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ Set.Icc (-2 : ℝ) 2 ∧ p 1 ∈ Set.Icc (-2 : ℝ) 2} :=
        h_coarse_bounds (z_of_pair z) ((hS_eq z).mp hz)
      exact h_sub hθ
    have hb1 : θ 0 ∈ Set.Icc (-2 : ℝ) 2 := hb.1
    have hb2 : θ 1 ∈ Set.Icc (-2 : ℝ) 2 := hb.2
    exact ⟨hb1, hb2⟩
  · intro z hz p hp
    rcases (Set.mem_image e (coarseParams (z_of_pair z)) p).mp hp with ⟨θ, hθ, rfl⟩
    have h_res := h_coarse_resid (z_of_pair z) ((hS_eq z).mp hz) θ hθ
    have h_eq : lineResidual (z_of_pair z) θ = |(e θ).1 * z.2 + (e θ).2 - z.1| := by
      have h_simp : lineResidual (z_of_pair z) θ = |z.1 - (θ 0 * z.2 + θ 1)| := by
        simp [lineResidual, z_of_pair, e]
      rw [h_simp]
      have h2 : z.1 - (θ 0 * z.2 + θ 1) = -(θ 0 * z.2 + θ 1 - z.1) := by ring
      rw [h2, abs_neg] <;> rfl
    rw [h_eq] at h_res
    exact h_res

end LemmaE
