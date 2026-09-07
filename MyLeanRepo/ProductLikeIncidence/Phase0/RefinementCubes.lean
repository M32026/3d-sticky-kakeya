module

/-
# Popular Subset Refinement for Cube Families

Phase 0 refinement lemma: given per-y cube families that are (δ,2s,C)-regular
and each has size ≥ c·|𝒯|, select a popular subfamily T_bar such that:
- T_bar ⊆ 𝒯
- ⋃₀ T_bar is a (δ,2s,4C/c²)-set
- |T_bar| ≥ (c/2)·|𝒯|
- Each cube in T_bar appears in ≥ (c/2)·|Y| families

This is a direct port of `refinement_is_delta_2s_set` from Appendix tube labels
to dyadic cube labels. The canonical parameter cube map is replaced by the
identity (each cube IS its own parameter realization), and
`tubeParamCoveringEqCard` is replaced by `cubeFamilyCoveringEqCard`.

## Whiteprint node
`phase0_refinement_cubes`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProductLikeIncidence.ProductLikeProof
public import MyLeanRepo.ProductLikeIncidence.Phase0.CubeUnion
public import MyLeanRepo.ProductLikeIncidence.Phase0.CubeFamilyAggregation
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open ProductLikeIncidence ENNReal Set Bornology Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- For a family 𝒮 of δ-dyadic cubes and an r-dyadic cube Q with δ ≤ r,
the intersection of the union with Q equals the union of those cubes in 𝒮
that are contained in Q (by dyadic nesting). -/
lemma cubeFamilyIntersectCube {δ r : ℝ}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hr_dyadic : r ∈ dyadicScales) (hδ_le_r : δ ≤ r)
    {𝒮 : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hS_cubes : 𝒮 ⊆ dyadicCubes 2 δ)
    {Q : Set (EuclideanSpace ℝ (Fin 2))}
    (hQ_cube : Q ∈ dyadicCubes 2 r) :
    (⋃₀ 𝒮) ∩ Q = ⋃₀ {T ∈ 𝒮 | T ⊆ Q} := by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_sUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨T, hTin, hpT⟩, hpQ⟩
    have hT_dyadic : T ∈ dyadicCubes 2 δ := hS_cubes hTin
    rcases hT_dyadic with ⟨k, hk⟩
    rcases hQ_cube with ⟨j, hj⟩
    have hN : ∃ (N : ℕ), r = (N : ℝ) * δ :=
      dyadic_scale_multiple hδ_dyadic hr_dyadic hδ_le_r
    have hr_pos : 0 < r := by
      rcases hr_dyadic with ⟨m, rfl⟩; positivity
    have h_inter : (T ∩ Q).Nonempty := ⟨p, hpT, hpQ⟩
    rw [hk, hj] at h_inter
    have h_sub : T ⊆ Q := by
      rw [hk, hj]
      exact dyadicCubeContainment hδ hr_pos hN h_inter
    exact ⟨T, ⟨hTin, h_sub⟩, hpT⟩
  · rintro ⟨T, ⟨hTin, hT_sub⟩, hpT⟩
    exact ⟨⟨T, hTin, hpT⟩, hT_sub hpT⟩

/-- Single-family covering bound for cube families: if ⋃₀ 𝒮 is a (δ,2s,C)-set
and 𝒮 consists of δ-dyadic cubes, then for any r-cube Q, the number of cubes
in 𝒮 contained in Q is ≤ C·|𝒮|·r^{2s}. -/
lemma cubeFamilySingleCoveringBound {δ s C r : ℝ}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hr_dyadic : r ∈ dyadicScales) (hδ_le_r : δ ≤ r) (hr_le_one : r ≤ 1)
    {𝒮 : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hS_cubes : 𝒮 ⊆ dyadicCubes 2 δ)
    (hS_set : IsDeltaSCSet (d := 2) δ (2 * s) C (⋃₀ 𝒮))
    {Q : Set (EuclideanSpace ℝ (Fin 2))}
    (hQ_cube : Q ∈ dyadicCubes 2 r) :
    ENat.toENNReal ({T ∈ 𝒮 | T ⊆ Q}).encard ≤
      ENNReal.ofReal C * ENat.toENNReal 𝒮.encard *
        ENNReal.ofReal (r ^ (2 * s)) := by
  let S_Q := {T ∈ 𝒮 | T ⊆ Q}
  have hS_Q_cubes : S_Q ⊆ dyadicCubes 2 δ := fun T hT => hS_cubes hT.1
  have h_eq1 : dyadicCoveringNumber δ (⋃₀ S_Q) = S_Q.encard :=
    cubeFamilyCoveringEqCard hδ hS_Q_cubes
  have h_eq2 : (⋃₀ 𝒮) ∩ Q = ⋃₀ S_Q :=
    cubeFamilyIntersectCube hδ hδ_dyadic hr_dyadic hδ_le_r hS_cubes hQ_cube
  rcases hS_set with ⟨_, _, _, _, _, _, _, _, hMain⟩
  have h := hMain hr_dyadic hQ_cube hδ_le_r hr_le_one
  rw [h_eq2] at h
  rw [h_eq1] at h
  have h_eq3 : dyadicCoveringNumber δ (⋃₀ 𝒮) = 𝒮.encard :=
    cubeFamilyCoveringEqCard hδ hS_cubes
  rw [h_eq3] at h
  exact h

/-- Boundedness of a single dyadic cube. -/
private lemma dyadicCube_isBounded {δ : ℝ} (hδ : 0 < δ) (k : Fin 2 → ℤ) :
    Bornology.IsBounded (dyadicCube δ k) := by
  have hδ_nonneg : 0 ≤ δ := by linarith
  let M : ℝ := δ * (|(k 0 : ℝ)| + |(k 1 : ℝ)| + 2)
  have hM_nonneg : 0 ≤ M := by positivity
  have h1 : ∀ (x : EuclideanSpace ℝ (Fin 2)), x ∈ dyadicCube δ k → ‖x‖ ≤ M := by
    intro x hx
    have h2 : ∀ (i : Fin 2), |x i| ≤ δ * (|(k i : ℝ)| + 1) := by
      intro i
      by_cases hxi : 0 ≤ x i
      · rw [abs_of_nonneg hxi]
        have h6 : x i < δ * ((k i : ℝ) + 1) := (hx i).2
        have h7 : (k i : ℝ) + 1 ≤ |(k i : ℝ)| + 1 := by
          have h71 : (k i : ℝ) ≤ |(k i : ℝ)| := le_abs_self (k i : ℝ)
          linarith
        have h8 : δ * ((k i : ℝ) + 1) ≤ δ * (|(k i : ℝ)| + 1) := by gcongr
        linarith
      · have hxi' : x i < 0 := by linarith
        rw [abs_of_neg hxi']
        have h6 : -(x i) ≤ -(δ * (k i : ℝ)) := by linarith [(hx i).1]
        have h71 : -(k i : ℝ) ≤ |(k i : ℝ)| := by
          have h81 : -(k i : ℝ) ≤ |-(k i : ℝ)| := le_abs_self (-(k i : ℝ))
          have h82 : |-(k i : ℝ)| = |(k i : ℝ)| := by rw [abs_neg]
          exact h82 ▸ h81
        have h7 : -(δ * (k i : ℝ)) ≤ δ * (|(k i : ℝ)| + 1) := by
          have h9 : -(δ * (k i : ℝ)) = δ * (-(k i : ℝ)) := by ring
          rw [h9]
          gcongr
          <;> linarith [h71]
        linarith
    have h_sum_sq : (x 0)^2 + (x 1)^2 ≤ (|x 0| + |x 1|)^2 := by
      have h1 : (|x 0| + |x 1|)^2 = (x 0)^2 + (x 1)^2 + 2 * |x 0| * |x 1| := by
        have h2 : |x 0| ^ 2 = (x 0)^2 := by rw [sq_abs]
        have h3 : |x 1| ^ 2 = (x 1)^2 := by rw [sq_abs]
        nlinarith
      rw [h1]
      have h4 : 0 ≤ 2 * |x 0| * |x 1| := by positivity
      linarith
    have h_euclid : ‖x‖ ≤ |x 0| + |x 1| := by
      have h_norm2 : ‖x‖ = Real.sqrt ((x 0)^2 + (x 1)^2) := by
        simp [EuclideanSpace.norm_eq] <;> rfl
      rw [h_norm2]
      have h9 : Real.sqrt ((x 0)^2 + (x 1)^2) ≤ Real.sqrt ((|x 0| + |x 1|)^2) :=
        Real.sqrt_le_sqrt h_sum_sq
      have h10 : Real.sqrt ((|x 0| + |x 1|)^2) = |x 0| + |x 1| := by
        have h11 : 0 ≤ |x 0| + |x 1| := by positivity
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_nonneg h11]
      rw [h10] at h9
      exact h9
    have h_bound : |x 0| + |x 1| ≤ M := by
      have h20 := h2 0
      have h21 := h2 1
      dsimp only [M]
      linarith
    exact le_trans h_euclid h_bound
  have h_sub : dyadicCube δ k ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) M := by
    intro x hx
    have h9 : ‖x‖ ≤ M := h1 x hx
    simpa [Metric.mem_closedBall, dist_zero_right] using h9
  exact Metric.isBounded_closedBall.subset h_sub

/-- **Popular subset refinement for dyadic cube families.**

Given per-y cube families T_y y whose unions are (δ,2s,C)-sets, each of size
≥ c·|𝒯|, all contained in an ambient family 𝒯 of δ-dyadic cubes, there exists
a popular subfamily T_bar with:
- T_bar ⊆ 𝒯
- ⋃₀ T_bar is a (δ,2s,4C/c²)-set
- |T_bar| ≥ (c/2)·|𝒯|
- Each cube in T_bar belongs to ≥ (c/2)·|Y| families T_y y.
-/
lemma phase0_refinement_cubes {δ s C c : ℝ} {Y : Set ℝ}
    {𝒯 : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    {T_y : ℝ → Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hs_nonneg : 0 ≤ s) (hs_le_two : 2 * s ≤ 2)
    (hC_pos : 0 < C) (hc_pos : 0 < c)
    (hY_fin : Y.Finite) (hY_nonempty : Y.Nonempty)
    (hT_y_set : ∀ y ∈ Y, IsDeltaSCSet (d := 2) δ (2 * s) C (⋃₀ (T_y y)))
    (hT_y_sub : ∀ y ∈ Y, T_y y ⊆ 𝒯)
    (h𝒯_cubes : 𝒯 ⊆ dyadicCubes 2 δ)
    (h_card : ∀ y ∈ Y, ENat.toENNReal (T_y y).encard ≥
      ENNReal.ofReal c * ENat.toENNReal 𝒯.encard) :
    ∃ (T_bar : Set (Set (EuclideanSpace ℝ (Fin 2)))),
      T_bar ⊆ 𝒯 ∧
      IsDeltaSCSet (d := 2) δ (2 * s) (4 * C / c^2) (⋃₀ T_bar) ∧
      ENat.toENNReal T_bar.encard ≥
        ENNReal.ofReal (c / 2) * ENat.toENNReal 𝒯.encard ∧
      (∀ T ∈ T_bar, ENat.toENNReal ({y ∈ Y | T ∈ T_y y}).encard ≥
        ENNReal.ofReal (c / 2) * ENat.toENNReal Y.encard) := by
  rcases hY_nonempty with ⟨y0, hy0⟩

  have hT_y_cubes : ∀ y ∈ Y, T_y y ⊆ dyadicCubes 2 δ := fun y hy =>
    (hT_y_sub y hy).trans h𝒯_cubes

  -- Finiteness of each T_y y
  have hTy_fin : ∀ y ∈ Y, (T_y y).Finite := by
    intro y hy
    have h1 : Bornology.IsBounded (⋃₀ (T_y y)) := (hT_y_set y hy).1
    have h2 : dyadicCoveringNumber δ (⋃₀ (T_y y)) < ⊤ :=
      dyadicCoveringNumber_lt_top hδ h1
    have h3 : dyadicCoveringNumber δ (⋃₀ (T_y y)) = (T_y y).encard :=
      cubeFamilyCoveringEqCard hδ (hT_y_cubes y hy)
    rw [h3] at h2
    exact encard_lt_top_iff.mp h2

  -- Finiteness of 𝒯
  have h𝒯_fin : 𝒯.Finite := by
    by_contra h
    have h_top : 𝒯.encard = ⊤ := by rw [Set.encard_eq_top_iff] <;> exact h
    have h_top' : ENat.toENNReal 𝒯.encard = ⊤ := by rw [h_top] <;> simp
    have h_card0 := h_card y0 hy0
    have h_pos : 0 < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hc_pos
    have h_rhs_top : ENNReal.ofReal c * ENat.toENNReal 𝒯.encard = ⊤ := by
      rw [h_top']
      have h : ENNReal.ofReal c * ⊤ = ⊤ := by simp [h_pos.ne']
      exact h
    rw [h_rhs_top] at h_card0
    have h_eq : ENat.toENNReal (T_y y0).encard = ⊤ := top_le_iff.mp h_card0
    have h_cont : (T_y y0).encard = ⊤ := by exact Eq.symm ((fun {m n} => ENat.toENNReal_inj.mp) (id (Eq.symm h_eq)))
    have h_lt : (T_y y0).encard < ⊤ := Set.Finite.encard_lt_top (hTy_fin y0 hy0)
    rw [h_cont] at h_lt <;> simp at h_lt <;> tauto

  -- Nonemptiness of T_y y0 and 𝒯
  have hTy0_nonempty : (T_y y0).Nonempty := by
    have hP_nonempty : (⋃₀ (T_y y0)).Nonempty := (hT_y_set y0 hy0).2.1
    by_contra h
    have h' : T_y y0 = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [h'] at hP_nonempty
    simp at hP_nonempty <;> tauto
  have h𝒯_nonempty : 𝒯.Nonempty := hTy0_nonempty.mono (hT_y_sub y0 hy0)

  -- Finset conversions
  let Yf : Finset ℝ := hY_fin.toFinset
  let 𝒯f : Finset (Set (EuclideanSpace ℝ (Fin 2))) := h𝒯_fin.toFinset
  let Tyf : ℝ → Finset (Set (EuclideanSpace ℝ (Fin 2))) := fun y =>
    if hy : y ∈ Y then (hTy_fin y hy).toFinset else ∅

  have hYf_eq : (Yf : Set ℝ) = Y := by exact hY_fin.coe_toFinset
  have h𝒯f_eq : (𝒯f : Set _) = 𝒯 := by exact h𝒯_fin.coe_toFinset
  have hTyf_eq : ∀ y ∈ Y, (↑(Tyf y) : Set _) = T_y y := by
    intro y hy; simp [Tyf, hy] <;> rfl
  have hTyf_sub : ∀ y ∈ Y, Tyf y ⊆ 𝒯f := by
    intro y hy
    have h1 : (↑(Tyf y) : Set _) ⊆ 𝒯 := by
      rw [hTyf_eq y hy] <;> exact hT_y_sub y hy
    have h2 : (↑(Tyf y) : Set (Set (EuclideanSpace ℝ (Fin 2)))) ⊆
        (↑𝒯f : Set (Set (EuclideanSpace ℝ (Fin 2)))) := by
      rw [h𝒯f_eq] at * <;> exact h1
    exact Finset.coe_subset.mp h2
  have hTyf_card : ∀ y ∈ Y, ENat.toENNReal (T_y y).encard = (↑(Tyf y).card : ENNReal) := by
    intro y hy
    have h4 : (T_y y).encard = ↑(Tyf y).card := by
      rw [← hTyf_eq y hy] <;> simp
    rw [h4] <;> rfl
  have h𝒯_card : ENat.toENNReal 𝒯.encard = (↑𝒯f.card : ENNReal) := by
    have h4 : 𝒯.encard = ↑𝒯f.card := by rw [← h𝒯f_eq] <;> simp
    rw [h4] <;> rfl

  -- Convert h_card to real inequalities
  have h_card_real : ∀ y ∈ Y, ((Tyf y).card : ℝ) ≥ c * (𝒯f.card : ℝ) := by
    intro y hy
    have h5 := h_card y hy
    rw [hTyf_card y hy, h𝒯_card] at h5
    have h_pos2 : 0 ≤ c * (𝒯f.card : ℝ) := by positivity
    have h_card_nonneg : 0 ≤ ((Tyf y).card : ℝ) := Nat.cast_nonneg _
    have h9 : (↑(Tyf y).card : ENNReal) = ENNReal.ofReal ((Tyf y).card : ℝ) := by
      norm_cast
    rw [h9] at h5
    have h6 : ENNReal.ofReal c * (↑𝒯f.card : ENNReal) =
        ENNReal.ofReal (c * (𝒯f.card : ℝ)) := by
      have h7 : 0 ≤ c := by linarith
      rw [ENNReal.ofReal_mul h7] <;> simp <;> ring
    rw [h6] at h5
    have h10 : ENNReal.ofReal (c * (𝒯f.card : ℝ)) ≤
        ENNReal.ofReal ((Tyf y).card : ℝ) := h5
    have h11 : c * (𝒯f.card : ℝ) ≤ ((Tyf y).card : ℝ) := by exact (ofReal_le_ofReal_iff h_card_nonneg).mp h5
    exact h11

  -- Multiplicity function
  let m : (Set (EuclideanSpace ℝ (Fin 2))) → ℕ := fun T =>
    (Yf.filter (fun y => T ∈ Tyf y)).card
  have h1_m : ∀ T, m T = ∑ y ∈ Yf, if T ∈ Tyf y then 1 else 0 := by
    intro T; simp [m, Finset.filter_eq', Finset.sum_boole] <;> rfl

  -- Double counting
  have h_double_count : ∑ T ∈ 𝒯f, (m T : ℝ) = ∑ y ∈ Yf, ((Tyf y).card : ℝ) := by
    have h2 : ∑ T ∈ 𝒯f, (m T : ℝ) =
        ∑ T ∈ 𝒯f, ∑ y ∈ Yf, (if T ∈ Tyf y then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl; intro T _; exact_mod_cast h1_m T
    rw [h2, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    have hyY : y ∈ Y := by
      have h : y ∈ (Yf : Set ℝ) := hy
      rw [hYf_eq] at h; exact h
    have h3 : 𝒯f.filter (fun T => T ∈ Tyf y) = Tyf y := by
      ext T; simp [hTyf_sub y hyY] <;> tauto
    rw [Finset.sum_boole, h3] <;> norm_cast

  -- Lower bound on sum
  have h_sum_lower : ∑ y ∈ Yf, ((Tyf y).card : ℝ) ≥
      (Yf.card : ℝ) * c * (𝒯f.card : ℝ) := by
    calc
      ∑ y ∈ Yf, ((Tyf y).card : ℝ)
        ≥ ∑ y ∈ Yf, c * (𝒯f.card : ℝ) := Finset.sum_le_sum (fun y hy =>
          h_card_real y (by
            have h : y ∈ (Yf : Set ℝ) := hy
            rw [hYf_eq] at h; exact h))
      _ = (Yf.card : ℝ) * c * (𝒯f.card : ℝ) := by
        simp [Finset.sum_const] <;> ring

  -- Define T_bar by thresholding
  let threshold : ℝ := c * (Yf.card : ℝ) / 2
  let T_barf : Finset (Set (EuclideanSpace ℝ (Fin 2))) :=
    𝒯f.filter (fun T => (m T : ℝ) ≥ threshold)
  let T_bar : Set (Set (EuclideanSpace ℝ (Fin 2))) := ↑T_barf

  have h_m_le_ycard : ∀ T ∈ 𝒯f, (m T : ℝ) ≤ (Yf.card : ℝ) := by
    intro T _; have h : m T ≤ Yf.card := Finset.card_filter_le _ _
    exact_mod_cast h

  -- Size bound: |T_bar| ≥ (c/2)·|𝒯|
  have h_sum_upper : ∑ T ∈ 𝒯f, (m T : ℝ) ≤
      (Yf.card : ℝ) * (T_barf.card : ℝ) + threshold * (𝒯f.card : ℝ) := by
    have h1 : ∑ T ∈ 𝒯f, (m T : ℝ) =
        ∑ T ∈ T_barf, (m T : ℝ) + ∑ T ∈ (𝒯f \ T_barf), (m T : ℝ) := by
      have h_disj : Disjoint T_barf (𝒯f \ T_barf) := by exact Finset.disjoint_sdiff
      have h_univ : T_barf ∪ (𝒯f \ T_barf) = 𝒯f := by
        ext x; simp [T_barf] <;> tauto
      rw [← Finset.sum_union h_disj, h_univ]
    rw [h1]
    have hT_barf_sub : T_barf ⊆ 𝒯f := Finset.filter_subset _ _
    have h2 : ∑ T ∈ T_barf, (m T : ℝ) ≤
        (Yf.card : ℝ) * (T_barf.card : ℝ) := by
      calc
        ∑ T ∈ T_barf, (m T : ℝ)
          ≤ ∑ T ∈ T_barf, (Yf.card : ℝ) := Finset.sum_le_sum
            (fun T hT => h_m_le_ycard T (hT_barf_sub hT))
        _ = (Yf.card : ℝ) * (T_barf.card : ℝ) := by
          simp [Finset.sum_const] <;> ring
    have h3 : ∑ T ∈ (𝒯f \ T_barf), (m T : ℝ) ≤
        threshold * ((𝒯f \ T_barf).card : ℝ) := by
      calc
        ∑ T ∈ (𝒯f \ T_barf), (m T : ℝ)
          ≤ ∑ T ∈ (𝒯f \ T_barf), threshold := Finset.sum_le_sum
            (fun T hT => by
              have hTin : T ∈ 𝒯f := Finset.mem_sdiff.mp hT |>.1
              have h5' : T ∉ T_barf := Finset.mem_sdiff.mp hT |>.2
              have h6 : ¬((m T : ℝ) ≥ threshold) := by
                by_contra h7
                have h8 : T ∈ T_barf := Finset.mem_filter.mpr ⟨hTin, h7⟩
                exact h5' h8
              linarith)
        _ = threshold * ((𝒯f \ T_barf).card : ℝ) := by
          simp [Finset.sum_const] <;> ring
    have h41 : (𝒯f \ T_barf) ⊆ 𝒯f := by simp
    have h4 : ((𝒯f \ T_barf).card : ℝ) ≤ (𝒯f.card : ℝ) := by
      exact_mod_cast Finset.card_le_card h41
    have h_thresh_nonneg : 0 ≤ threshold := by positivity
    have h5 : threshold * ((𝒯f \ T_barf).card : ℝ) ≤
        threshold * (𝒯f.card : ℝ) := by gcongr
    calc
      (∑ T ∈ T_barf, (m T : ℝ)) + (∑ T ∈ (𝒯f \ T_barf), (m T : ℝ))
        ≤ (Yf.card : ℝ) * (T_barf.card : ℝ) +
            threshold * ((𝒯f \ T_barf).card : ℝ) := by
          exact add_le_add h2 h3
      _ ≤ (Yf.card : ℝ) * (T_barf.card : ℝ) + threshold * (𝒯f.card : ℝ) := by
          exact add_le_add_right h5 _

  have h_ycard_pos : 0 < (Yf.card : ℝ) := by
    have hYf_nonempty : Yf.Nonempty := by
      have h1 : (Yf : Set ℝ) = Y := hYf_eq
      have h2 : (Yf : Set ℝ).Nonempty := by rw [h1]; exact ⟨y0, hy0⟩
      exact_mod_cast h2
    have h3 : 0 < Yf.card := Finset.card_pos.mpr hYf_nonempty
    exact_mod_cast h3

  have h_size : (T_barf.card : ℝ) ≥ (c / 2) * (𝒯f.card : ℝ) := by
    have h6 : (Yf.card : ℝ) * c * (𝒯f.card : ℝ) ≤
        (Yf.card : ℝ) * (T_barf.card : ℝ) + threshold * (𝒯f.card : ℝ) := by
      calc
        (Yf.card : ℝ) * c * (𝒯f.card : ℝ)
          ≤ ∑ y ∈ Yf, ((Tyf y).card : ℝ) := h_sum_lower
        _ = ∑ T ∈ 𝒯f, (m T : ℝ) := h_double_count.symm
        _ ≤ (Yf.card : ℝ) * (T_barf.card : ℝ) + threshold * (𝒯f.card : ℝ) :=
          h_sum_upper
    have h7 : threshold = c * (Yf.card : ℝ) / 2 := by rfl
    rw [h7] at h6
    have h9 : (Yf.card : ℝ) * ((c / 2) * (𝒯f.card : ℝ)) ≤
        (Yf.card : ℝ) * (T_barf.card : ℝ) := by linarith
    calc
      (c / 2) * (𝒯f.card : ℝ)
        = ((Yf.card : ℝ) * ((c / 2) * (𝒯f.card : ℝ))) / (Yf.card : ℝ) := by
          field_simp [h_ycard_pos.ne'] <;> ring
      _ ≤ ((Yf.card : ℝ) * (T_barf.card : ℝ)) / (Yf.card : ℝ) := by gcongr
      _ = (T_barf.card : ℝ) := by
          field_simp [h_ycard_pos.ne'] <;> ring

  -- T_bar subset properties
  have hT_bar_sub : T_bar ⊆ 𝒯 := by
    have h : T_barf ⊆ 𝒯f := Finset.filter_subset _ _
    have h_coe1 : (↑T_barf : Set _) = T_bar := by simp [T_bar]
    have h_coe2 : (↑𝒯f : Set _) = 𝒯 := by simp [𝒯f]
    intro x hx
    have hx' : x ∈ (↑T_barf : Set _) := by rw [h_coe1] <;> exact hx
    have h4 : x ∈ (↑𝒯f : Set _) := h hx'
    rw [h_coe2] at h4
    exact h4

  have hT_bar_cubes : T_bar ⊆ dyadicCubes 2 δ :=
    hT_bar_sub.trans h𝒯_cubes

  -- Nonemptiness of T_bar
  have hT_bar_nonempty : T_bar.Nonempty := by
    have h9 : (T_barf.card : ℝ) > 0 := by
      have h10 : 0 < 𝒯f.card := Finset.card_pos.mpr (by exact (Finite.toFinset_nonempty h𝒯_fin).mpr h𝒯_nonempty)
      have h11 : (T_barf.card : ℝ) ≥ (c / 2) * (𝒯f.card : ℝ) := h_size
      have h12 : (c / 2) * (𝒯f.card : ℝ) > 0 := by positivity
      linarith
    have h13 : 0 < T_barf.card := by exact_mod_cast h9
    exact Finset.card_pos.mp h13

  -- Let P_bar := ⋃₀ T_bar
  let P_bar := ⋃₀ T_bar

  -- Nonemptiness of P_bar
  have hP_bar_nonempty : P_bar.Nonempty := by
    rcases hT_bar_nonempty with ⟨T, hT⟩
    have hT_dyadic : T ∈ dyadicCubes 2 δ := hT_bar_cubes hT
    rcases hT_dyadic with ⟨k, hk⟩
    have h_cube_nonempty : T.Nonempty := by
      rw [hk]; exact dyadicCube_nonempty hδ k
    have h_in_Pbar : T ⊆ P_bar := by
      intro p hp
      simp only [P_bar, Set.mem_sUnion]
      exact ⟨T, hT, hp⟩
    exact h_cube_nonempty.mono h_in_Pbar

  -- Boundedness of P_bar
  have h_cube_bounded : ∀ (T : Set (EuclideanSpace ℝ (Fin 2))),
      T ∈ dyadicCubes 2 δ → Bornology.IsBounded T := by
    intro T hT
    rcases hT with ⟨k, rfl⟩
    exact dyadicCube_isBounded hδ k
  have hP_bar_bdd : Bornology.IsBounded P_bar := by
    have h1 : ∀ T ∈ T_barf, Bornology.IsBounded T := fun T hT =>
      h_cube_bounded T (hT_bar_cubes (by simpa [T_bar] using hT))
    have h2 : Bornology.IsBounded (⋃ T ∈ T_barf, T) :=
      (Bornology.isBounded_biUnion_finset T_barf).mpr h1
    have hP_bar_eq : P_bar = (⋃ T ∈ T_barf, T) := by
      ext p
      simp only [P_bar, T_bar, Set.mem_sUnion, Set.mem_iUnion, Finset.mem_coe]
      <;> tauto
    rw [hP_bar_eq]
    exact h2

  -- Covering bound (core)
  have h_covering_main : ∀ (r : ℝ) (Q : Set (EuclideanSpace ℝ (Fin 2))),
      r ∈ dyadicScales → Q ∈ dyadicCubes 2 r → δ ≤ r → r ≤ 1 →
        ENat.toENNReal (dyadicCoveringNumber δ (P_bar ∩ Q)) ≤
          ENNReal.ofReal (4 * C / c^2) *
            ENat.toENNReal (dyadicCoveringNumber δ P_bar) *
              ENNReal.ofReal (r ^ (2 * s)) := by
    intro r Q hr_dyadic hQ_cube hδ_le_r hr_le_one
    let restrictQ (𝒮 : Finset (Set (EuclideanSpace ℝ (Fin 2)))) : Finset _ :=
      𝒮.filter (fun T => T ⊆ Q)
    let T_bar_Q := restrictQ T_barf

    have h_y_cover : ∀ y ∈ Yf, ((restrictQ (Tyf y)).card : ℝ) ≤
        C * ((Tyf y).card : ℝ) * (r ^ (2 * s)) := by
      intro y hy
      have hyY : y ∈ Y := by
        have h : y ∈ (Yf : Set ℝ) := hy
        rw [hYf_eq] at h; exact h
      let S_y : Set (Set (EuclideanSpace ℝ (Fin 2))) := {T ∈ T_y y | T ⊆ Q}
      have h_ennat := cubeFamilySingleCoveringBound hδ hδ_dyadic hr_dyadic
        hδ_le_r hr_le_one (hT_y_cubes y hyY) (hT_y_set y hyY) hQ_cube
      have h_fin : S_y.Finite := (hTy_fin y hyY).subset (fun _ h => h.1)
      have h_eq1 : S_y.encard = ↑(restrictQ (Tyf y)).card := by
        have h3 : (↑S_y : Set _) = ↑(restrictQ (Tyf y)) := by
          ext T
          simp only [S_y, restrictQ, Finset.mem_coe, Finset.mem_filter,
            Set.mem_setOf_eq]
          have h4 : T ∈ T_y y ↔ T ∈ Tyf y := by
            rw [← hTyf_eq y hyY] <;> rfl
          tauto
        rw [h3] <;> simp
      have h_eq2 : (T_y y).encard = ↑(Tyf y).card := by
        rw [← hTyf_eq y hyY] <;> simp
      have hC_nonneg : 0 ≤ C := by linarith
      have h_rpow_nonneg : 0 ≤ r ^ (2 * s) := Real.rpow_nonneg (by linarith) _
      have ha_ne_top : ENat.toENNReal S_y.encard ≠ ⊤ := by
        have h : S_y.encard ≠ ⊤ := Set.Finite.encard_lt_top h_fin |>.ne
        simpa [ENat.toENNReal_eq_top] using h
      have hb_ne_top : (ENNReal.ofReal C * ENat.toENNReal (T_y y).encard *
          ENNReal.ofReal (r ^ (2 * s))) ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · simp [hC_nonneg]
          · have h : (T_y y).encard ≠ ⊤ := Set.Finite.encard_lt_top (hTy_fin y hyY) |>.ne
            simpa [ENat.toENNReal_eq_top] using h
        · simp [h_rpow_nonneg]
      have h_ineq_real : ENNReal.toReal (ENat.toENNReal S_y.encard) ≤
          ENNReal.toReal (ENNReal.ofReal C * ENat.toENNReal (T_y y).encard *
            ENNReal.ofReal (r ^ (2 * s))) :=
        (ENNReal.toReal_le_toReal ha_ne_top hb_ne_top).mpr h_ennat
      have h_toReal_left : ENNReal.toReal (ENat.toENNReal S_y.encard) =
          ((restrictQ (Tyf y)).card : ℝ) := by
        rw [h_eq1] <;> simp
      have h_toReal_right : ENNReal.toReal (ENNReal.ofReal C * ENat.toENNReal (T_y y).encard *
          ENNReal.ofReal (r ^ (2 * s))) = C * ((Tyf y).card : ℝ) * (r ^ (2 * s)) := by
        rw [h_eq2]
        simp [ENNReal.toReal_mul, hC_nonneg, h_rpow_nonneg]
        <;> ring
      rw [h_toReal_left, h_toReal_right] at h_ineq_real
      exact h_ineq_real

    -- Double count restricted families
    have h_double_count_Q : ∑ T ∈ T_bar_Q, (m T : ℝ) ≤
        ∑ y ∈ Yf, ((restrictQ (Tyf y)).card : ℝ) := by
      have h1 : ∑ T ∈ T_bar_Q, (m T : ℝ) =
          ∑ T ∈ T_bar_Q, ∑ y ∈ Yf, (if T ∈ Tyf y then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl; intro T _; exact_mod_cast h1_m T
      rw [h1]
      have h2 : ∑ T ∈ T_bar_Q, ∑ y ∈ Yf, (if T ∈ Tyf y then (1 : ℝ) else 0) =
          ∑ y ∈ Yf, ∑ T ∈ T_bar_Q, (if T ∈ Tyf y then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
      rw [h2]
      apply Finset.sum_le_sum
      intro y hy
      have hyY : y ∈ Y := by
        have h : y ∈ (Yf : Set ℝ) := hy
        rw [hYf_eq] at h; exact h
      have h3 : T_bar_Q ⊆ 𝒯f := by
        have h4 : T_bar_Q ⊆ T_barf := Finset.filter_subset _ _
        exact h4.trans (Finset.filter_subset _ _)
      have h4 : ∑ T ∈ T_bar_Q, (if T ∈ Tyf y then (1 : ℝ) else 0) ≤
          ∑ T ∈ restrictQ (Tyf y), (1 : ℝ) := by
        have h5 : ∑ T ∈ T_bar_Q, (if T ∈ Tyf y then (1 : ℝ) else 0) =
            ((T_bar_Q ∩ Tyf y).card : ℝ) := by
          rw [Finset.sum_boole]
          <;> simp [Finset.filter]
          <;> rfl
        rw [h5]
        have h6 : T_bar_Q ∩ Tyf y ⊆ restrictQ (Tyf y) := by
          intro T hT
          have hT_in_barQ : T ∈ T_bar_Q := (Finset.mem_inter.mp hT).1
          have hT_in_Tyf : T ∈ Tyf y := (Finset.mem_inter.mp hT).2
          have hT_sub : T ⊆ Q := (Finset.mem_filter.mp hT_in_barQ).2
          exact Finset.mem_filter.mpr ⟨hT_in_Tyf, hT_sub⟩
        have h7 : (T_bar_Q ∩ Tyf y).card ≤ (restrictQ (Tyf y)).card := Finset.card_le_card h6
        have h7' : ((T_bar_Q ∩ Tyf y).card : ℝ) ≤ ((restrictQ (Tyf y)).card : ℝ) := Nat.cast_le.mpr h7
        have h8 : ∑ T ∈ restrictQ (Tyf y), (1 : ℝ) = ((restrictQ (Tyf y)).card : ℝ) := by
          simp [Finset.sum_const]
        rw [h8]
        exact h7'
      simpa [Finset.sum_const] using h4

    -- Threshold lower bound on double count
    have h_thresh_pos : 0 < threshold := by positivity
    have h_lower_Q : threshold * (T_bar_Q.card : ℝ) ≤
        ∑ T ∈ T_bar_Q, (m T : ℝ) := by
      calc
        ∑ T ∈ T_bar_Q, (m T : ℝ)
          ≥ ∑ T ∈ T_bar_Q, threshold := Finset.sum_le_sum (fun T hT => by
            have hT' : T ∈ T_barf := (Finset.mem_filter.mp hT).1
            have h_above : (m T : ℝ) ≥ threshold :=
              (Finset.mem_filter.mp hT').2
            exact h_above)
        _ = threshold * (T_bar_Q.card : ℝ) := by
          simp [Finset.sum_const] <;> ring

    -- Upper bound via per-y covering
    have h_upper_Q : ∑ y ∈ Yf, ((restrictQ (Tyf y)).card : ℝ) ≤
        (Yf.card : ℝ) * C * (𝒯f.card : ℝ) * (r ^ (2 * s)) := by
      calc
        ∑ y ∈ Yf, ((restrictQ (Tyf y)).card : ℝ)
          ≤ ∑ y ∈ Yf, C * ((Tyf y).card : ℝ) * (r ^ (2 * s)) :=
            Finset.sum_le_sum (fun y hy => h_y_cover y hy)
        _ = C * (r ^ (2 * s)) * ∑ y ∈ Yf, ((Tyf y).card : ℝ) := by
          have h_factor : ∑ y ∈ Yf, C * ((Tyf y).card : ℝ) * (r ^ (2 * s)) =
              ∑ y ∈ Yf, (C * (r ^ (2 * s))) * ((Tyf y).card : ℝ) := by
            apply Finset.sum_congr rfl
            intro y _; ring
          rw [h_factor, Finset.mul_sum] <;> ring
        _ ≤ C * (r ^ (2 * s)) * ((Yf.card : ℝ) * (𝒯f.card : ℝ)) := by
          have h_sum_upper_simple : ∑ y ∈ Yf, ((Tyf y).card : ℝ) ≤ (Yf.card : ℝ) * (𝒯f.card : ℝ) := by
            calc
              ∑ y ∈ Yf, ((Tyf y).card : ℝ)
                ≤ ∑ y ∈ Yf, (𝒯f.card : ℝ) := Finset.sum_le_sum (fun y hy => by
                  have hyY : y ∈ Y := by
                    have h : y ∈ (Yf : Set ℝ) := hy
                    rw [hYf_eq] at h; exact h
                  exact Nat.cast_le.mpr (Finset.card_le_card (hTyf_sub y hyY)))
              _ = (Yf.card : ℝ) * (𝒯f.card : ℝ) := by simp [Finset.sum_const] <;> ring
          have hC_nonneg' : 0 ≤ C := by linarith [hC_pos]
          have hr_pos : 0 < r := by rcases hr_dyadic with ⟨m, rfl⟩; positivity
          have h_rpow_nonneg' : 0 ≤ r ^ (2 * s) := Real.rpow_nonneg (by linarith) _
          have h_nonneg : 0 ≤ C * (r ^ (2 * s)) := mul_nonneg hC_nonneg' h_rpow_nonneg'
          exact mul_le_mul_of_nonneg_left h_sum_upper_simple h_nonneg
        _ = (Yf.card : ℝ) * C * (𝒯f.card : ℝ) * (r ^ (2 * s)) := by ring

    have h_main_ineq : threshold * (T_bar_Q.card : ℝ) ≤
        (Yf.card : ℝ) * C * (𝒯f.card : ℝ) * (r ^ (2 * s)) := by
      calc
        threshold * (T_bar_Q.card : ℝ)
          ≤ ∑ T ∈ T_bar_Q, (m T : ℝ) := h_lower_Q
        _ ≤ ∑ y ∈ Yf, ((restrictQ (Tyf y)).card : ℝ) := h_double_count_Q
        _ ≤ (Yf.card : ℝ) * C * (𝒯f.card : ℝ) * (r ^ (2 * s)) := h_upper_Q

    -- First algebra: |T_bar_Q| ≤ (2C/c)·|𝒯|·r^{2s}
    set yc := (Yf.card : ℝ) with hyc
    set tc := (𝒯f.card : ℝ) with htc
    set rp := r ^ (2 * s) with hrp
    have hc_pos' : 0 < c := hc_pos
    have h1 : (c * yc / 2)⁻¹ = 2 / (c * yc) := by
      have hyc_ne : yc ≠ 0 := h_ycard_pos.ne'
      have hc_ne : c ≠ 0 := hc_pos'.ne'
      field_simp [hyc_ne, hc_ne] <;> ring
    have h_algebra : (yc * C * tc * rp) / threshold = (2 * C / c) * tc * rp := by
      calc
        (yc * C * tc * rp) / threshold
          = (yc * C * tc * rp) * (c * yc / 2)⁻¹ := by rw [div_eq_mul_inv]
        _ = (yc * C * tc * rp) * (2 / (c * yc)) := by rw [h1]
        _ = (yc * (2 * C * tc * rp)) / (c * yc) := by ring
        _ = (2 * C * tc * rp) / c := by
          have h2 : c * yc = yc * c := by ring
          rw [h2]
          have hyc_ne' : yc ≠ 0 := h_ycard_pos.ne'
          have hc_ne' : c ≠ 0 := hc_pos'.ne'
          field_simp [hyc_ne', hc_ne'] <;> ring
        _ = (2 * C / c) * tc * rp := by ring
    have h_result : (T_bar_Q.card : ℝ) ≤ (yc * C * tc * rp) / threshold := by
      have h_pos : 0 < threshold := h_thresh_pos
      have h_ne : threshold ≠ 0 := h_pos.ne'
      have h_mul_div : threshold * ((yc * C * tc * rp) / threshold) =
          yc * C * tc * rp := by field_simp [h_ne] <;> ring
      have h : threshold * (T_bar_Q.card : ℝ) ≤ yc * C * tc * rp := h_main_ineq
      rw [← h_mul_div] at h
      nlinarith
    have h_cover1 : (T_bar_Q.card : ℝ) ≤ (2 * C / c) * tc * rp := by
      calc
        (T_bar_Q.card : ℝ) ≤ (yc * C * tc * rp) / threshold := h_result
        _ = (2 * C / c) * tc * rp := h_algebra

    -- Second algebra: substitute |𝒯| ≤ (2/c)|T_bar|
    have h_cover2 : (T_bar_Q.card : ℝ) ≤
        (4 * C / c^2) * (T_barf.card : ℝ) * (r ^ (2 * s)) := by
      set tbc := (T_barf.card : ℝ) with htbc
      have hc_ne : c ≠ 0 := hc_pos.ne'
      have h_helper : (2 / c) * ((c / 2) * tc) = tc := by
        calc
          (2 / c) * ((c / 2) * tc)
            = ((2 / c) * (c / 2)) * tc := by ring
          _ = 1 * tc := by
            have h9 : (2 / c) * (c / 2) = 1 := by
              have hc_ne' : c ≠ 0 := hc_pos.ne'
              field_simp [hc_ne'] <;> ring
            rw [h9]
          _ = tc := by ring
      have h7 : tc ≤ (2 / c) * tbc := by
        have h8 : (2 / c) * tbc ≥ (2 / c) * ((c / 2) * tc) := by gcongr
        rw [h_helper] at h8
        exact h8
      have hrp_nonneg : 0 ≤ rp := Real.rpow_nonneg (by linarith) _
      have h10 : (2 * C / c) * (2 / c) = 4 * C / c^2 := by
        have hc_ne' : c ≠ 0 := hc_pos.ne'
        field_simp [hc_ne'] <;> ring
      have h_final : (2 * C / c) * ((2 / c) * tbc) * rp =
          (4 * C / c^2) * tbc * rp := by
        calc
          (2 * C / c) * ((2 / c) * tbc) * rp
            = ((2 * C / c) * (2 / c)) * tbc * rp := by ring
          _ = (4 * C / c^2) * tbc * rp := by rw [h10]
      have hC2_nonneg' : 0 ≤ 2 * C / c := by positivity
      have h_cover2_mul : (2 * C / c) * tc * rp ≤
          (2 * C / c) * ((2 / c) * tbc) * rp :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h7 hC2_nonneg') hrp_nonneg
      calc
        (T_bar_Q.card : ℝ)
          ≤ (2 * C / c) * tc * rp := h_cover1
        _ ≤ (2 * C / c) * ((2 / c) * tbc) * rp := h_cover2_mul
        _ = (4 * C / c^2) * tbc * rp := h_final

    -- Convert to ENNReal
    let S_bar_Q : Set (Set (EuclideanSpace ℝ (Fin 2))) := {T ∈ T_bar | T ⊆ Q}
    have hS_bar_Q_cubes : S_bar_Q ⊆ dyadicCubes 2 δ := fun T hT =>
      hT_bar_cubes hT.1
    have h_eq_inter : P_bar ∩ Q = ⋃₀ S_bar_Q :=
      cubeFamilyIntersectCube hδ hδ_dyadic hr_dyadic hδ_le_r hT_bar_cubes hQ_cube
    have h_eq_coverQ : dyadicCoveringNumber δ (P_bar ∩ Q) = S_bar_Q.encard := by
      rw [h_eq_inter]
      exact cubeFamilyCoveringEqCard hδ hS_bar_Q_cubes
    have h_eq_cover : dyadicCoveringNumber δ P_bar = T_bar.encard :=
      cubeFamilyCoveringEqCard hδ hT_bar_cubes
    have h_eq_card1 : S_bar_Q.encard = ↑(T_bar_Q.card) := by
      have h3 : (↑S_bar_Q : Set _) = ↑T_bar_Q := by
        ext T
        simp only [S_bar_Q, T_bar_Q, T_bar, restrictQ, Finset.mem_coe,
          Finset.mem_filter, Set.mem_setOf_eq] <;> aesop
      rw [h3] <;> simp
    have h_eq_card2 : T_bar.encard = ↑T_barf.card := by
      simp [T_bar] <;> rfl
    rw [h_eq_coverQ, h_eq_cover, h_eq_card1, h_eq_card2]
    have hC2_nonneg : 0 ≤ 4 * C / c^2 := by positivity
    have h_rpow_nonneg : 0 ≤ r ^ (2 * s) := Real.rpow_nonneg (by linarith) _
    exact real_covering_bound_to_ennat hC2_nonneg h_rpow_nonneg h_cover2

  -- Assemble conclusion
  have h_s2_nonneg : 0 ≤ 2 * s := by linarith [hs_nonneg]
  have h_s2_le_two : 2 * s ≤ 2 := hs_le_two
  have h_final_set : IsDeltaSCSet (d := 2) δ (2 * s) (4 * C / c^2) P_bar :=
    ⟨hP_bar_bdd, hP_bar_nonempty, by norm_num, hδ_dyadic, hδ, h_s2_nonneg,
      h_s2_le_two, by positivity, h_covering_main⟩

  have h_final_card : ENat.toENNReal T_bar.encard ≥
      ENNReal.ofReal (c / 2) * ENat.toENNReal 𝒯.encard := by
    have h11 : T_bar.encard = ↑T_barf.card := by simp [T_bar] <;> rfl
    have h1 : ENat.toENNReal T_bar.encard = (↑T_barf.card : ENNReal) := by
      rw [h11] <;> rfl
    have h3 : (c / 2) * (𝒯f.card : ℝ) ≤ (T_barf.card : ℝ) := h_size
    have h4 : 0 ≤ (T_barf.card : ℝ) := Nat.cast_nonneg _
    have h_ofReal_card : (↑T_barf.card : ENNReal) =
        ENNReal.ofReal (T_barf.card : ℝ) := by norm_cast
    have h_mul : ENNReal.ofReal ((c / 2) * (𝒯f.card : ℝ)) =
        ENNReal.ofReal (c / 2) * (↑𝒯f.card : ENNReal) := by
      have h7 : 0 ≤ c / 2 := by positivity
      rw [ENNReal.ofReal_mul h7] <;> norm_cast <;> ring
    have h8 : ENNReal.ofReal ((c / 2) * (𝒯f.card : ℝ)) ≤
        ENNReal.ofReal (T_barf.card : ℝ) :=
      ENNReal.ofReal_le_ofReal_iff h4 |>.mpr h3
    have h9 : ENNReal.ofReal (c / 2) * (↑𝒯f.card : ENNReal) ≤
        ENNReal.ofReal (T_barf.card : ℝ) := h_mul ▸ h8
    have h10 : ENNReal.ofReal (c / 2) * (↑𝒯f.card : ENNReal) ≤
        (↑T_barf.card : ENNReal) := h_ofReal_card.symm ▸ h9
    simpa [h1, h𝒯_card] using h10

  -- Multiplicity bound
  have h_final_mult : ∀ T ∈ T_bar,
      ENat.toENNReal ({y ∈ Y | T ∈ T_y y}).encard ≥
        ENNReal.ofReal (c / 2) * ENat.toENNReal Y.encard := by
    intro T hT
    have hT' : T ∈ T_barf := by exact_mod_cast hT
    have h_above : (m T : ℝ) ≥ threshold := (Finset.mem_filter.mp hT').2
    have h_set_eq : ({y ∈ Y | T ∈ T_y y} : Set ℝ) =
        ↑(Yf.filter (fun y => T ∈ Tyf y)) := by
      ext y
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
      have h_y_in_Y : y ∈ Y ↔ y ∈ (Yf : Set ℝ) := by
        rw [hYf_eq] <;> rfl
      constructor
      · rintro ⟨hyY, hTin⟩
        have hyf : y ∈ Yf := by
          have h : y ∈ (Yf : Set ℝ) := by rw [hYf_eq] <;> exact hyY
          exact_mod_cast h
        have h_eq : T ∈ Tyf y := by
          have h : (↑(Tyf y) : Set _) = T_y y := hTyf_eq y hyY
          have h6 : T ∈ (↑(Tyf y) : Set _) := by rw [h]; exact hTin
          exact_mod_cast h6
        exact ⟨hyf, h_eq⟩
      · rintro ⟨hyf, h_eq⟩
        have hyY : y ∈ Y := by
          have h : y ∈ (Yf : Set ℝ) := by exact_mod_cast hyf
          rw [hYf_eq] at h; exact h
        have hTin : T ∈ T_y y := by
          have h : (↑(Tyf y) : Set _) = T_y y := hTyf_eq y hyY
          have h6 : T ∈ (↑(Tyf y) : Set _) := by exact_mod_cast h_eq
          rw [h] at h6; exact h6
        exact ⟨hyY, hTin⟩
    have h_filter_eq : (Yf.filter (fun y => T ∈ Tyf y)).card = m T := by
      simp [m] <;> rfl
    have h_encard : (↑(Yf.filter (fun y => T ∈ Tyf y)) : Set ℝ).encard = ↑(m T) := by
      rw [Set.encard_coe_eq_coe_finsetCard, h_filter_eq]
    have h_card_eq : ENat.toENNReal ({y ∈ Y | T ∈ T_y y}).encard = ↑(m T) := by
      rw [h_set_eq, h_encard] <;> rfl
    rw [h_card_eq]
    have hY_card_eq : ENat.toENNReal Y.encard = ↑Yf.card := by
      rw [←hYf_eq, Set.encard_coe_eq_coe_finsetCard] <;> rfl
    rw [hY_card_eq]
    have h_thresh_eq : threshold = (c / 2) * (Yf.card : ℝ) := by
      simp [threshold] <;> ring
    rw [h_thresh_eq] at h_above
    have h_mul_eq : ENNReal.ofReal (c / 2) * ↑Yf.card =
        ENNReal.ofReal ((c / 2) * (Yf.card : ℝ)) := by
      have h7 : 0 ≤ c / 2 := by positivity
      have h8 : (↑Yf.card : ENNReal) = ENNReal.ofReal (Yf.card : ℝ) := by norm_cast
      rw [h8]
      rw [← ENNReal.ofReal_mul h7] <;> norm_cast
    have h_ennreal : ENNReal.ofReal ((c / 2) * (Yf.card : ℝ)) ≤ ↑(m T) := by
      have h3 : (c / 2) * (Yf.card : ℝ) ≤ (m T : ℝ) := h_above
      have h_mT_nonneg : 0 ≤ (m T : ℝ) := Nat.cast_nonneg (m T)
      have h4 : ENNReal.ofReal ((c / 2) * (Yf.card : ℝ)) ≤
          ENNReal.ofReal ((m T : ℝ)) :=
        (ENNReal.ofReal_le_ofReal_iff h_mT_nonneg).mpr h3
      have h5 : ENNReal.ofReal ((m T : ℝ)) = ↑(m T) := by norm_cast
      rw [h5] at h4; exact h4
    rw [h_mul_eq]
    exact h_ennreal

  exact ⟨T_bar, hT_bar_sub, h_final_set, h_final_card, h_final_mult⟩

end ProductLikeIncidence.ProductReduction
