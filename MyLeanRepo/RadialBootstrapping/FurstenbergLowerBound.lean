module

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.discretised_furstenberg_estimate

@[expose] public section

/-!
# Furstenberg Lower Bound Interface (Canonical)

This file proves `furstenberg_lower_bound` using the supplied axiom
`discretised_furstenberg_estimate`.

## Proof route

1. Extract `ε_axiom` from the supplied axiom.
2. Choose `ε := ε_axiom(s,t) / 2` and shrink `δ₀` to absorb the `2^s`, `2^t` factors
   from the `IsDeltaSet → IsDeltaSSet` bridge.
3. Bridge `IsDeltaSet` → `IsDeltaSSet` (loses factor `2^s` or `2^t`).
4. Bridge `Line2` → `AffineLine` via isometry (metrics match after changing Line2
   metric from max to sum).
5. Apply the axiom to get a covering number lower bound.
6. Transfer back to `Line2` and convert covering number to cardinality.
-/

open Metric Set

noncomputable section

namespace FurstenbergEstimate

open RadialBootstrapping
open DirecretisedFurstenbergEstimate

/-! ## Component equality lemmas -/

lemma lineDirDist_eq_affineDirDist (L₁ L₂ : Line2) :
    lineDirDist L₁ L₂ =
      ‖L₁.toAffine.direction.starProjection - L₂.toAffine.direction.starProjection‖ := by
  have h1 : submoduleProj L₁.toAffine.direction = L₁.toAffine.direction.starProjection :=
    submoduleProj_eq_starProjection _
  have h2 : submoduleProj L₂.toAffine.direction = L₂.toAffine.direction.starProjection :=
    submoduleProj_eq_starProjection _
  simp [lineDirDist, submoduleDirDist, h1, h2]

lemma lineOffsetDist_eq_affineOffsetDist (L₁ L₂ : Line2) :
    lineOffsetDist L₁ L₂ =
      ‖(EuclideanGeometry.orthogonalProjection L₁.toAffine 0 : Point) -
        (EuclideanGeometry.orthogonalProjection L₂.toAffine 0 : Point)‖ := by
  have h1 : L₁.closestPoint = (EuclideanGeometry.orthogonalProjection L₁.toAffine 0 : Point) :=
    L₁.closestPoint_eq_orthogonalProjection
  have h2 : L₂.closestPoint = (EuclideanGeometry.orthogonalProjection L₂.toAffine 0 : Point) :=
    L₂.closestPoint_eq_orthogonalProjection
  simp [lineOffsetDist, h1, h2, dist_eq_norm]

/-! ## Isometry equivalence Line2 ≃ᵢ AffineLine -/

def line2EquivAffineLine : Line2 ≃ᵢ AffineLine :=
  { toFun := fun L : Line2 => ⟨L.toAffine, L.2⟩,
    invFun := fun ℓ : AffineLine => ⟨ℓ.1, ℓ.2⟩,
    left_inv := by intro x; simp <;> exact Subtype.ext rfl,
    right_inv := by intro y; simp <;> exact Subtype.ext rfl,
    isometry_toFun := by
      intro x1 x2
      let y1 : AffineLine := ⟨x1.toAffine, x1.2⟩
      let y2 : AffineLine := ⟨x2.toAffine, x2.2⟩
      have hd := lineDirDist_eq_affineDirDist x1 x2
      have ho := lineOffsetDist_eq_affineOffsetDist x1 x2
      have h_dist : dist y1 y2 = dist x1 x2 := by
        have h_main : dist x1 x2 = lineDirDist x1 x2 + lineOffsetDist x1 x2 := by rfl
        have h_aff : dist y1 y2 =
            ‖x1.toAffine.direction.starProjection - x2.toAffine.direction.starProjection‖ +
            ‖(EuclideanGeometry.orthogonalProjection x1.toAffine 0 : Point) -
              (EuclideanGeometry.orthogonalProjection x2.toAffine 0 : Point)‖ := by rfl
        rw [h_main, h_aff, hd, ho] <;> ring
      have h_edist : edist y1 y2 = edist x1 x2 := by
        rw [edist_dist, edist_dist, h_dist]
      exact h_edist }

/-! ## Covering number transfer -/

lemma externalCoveringNumber_congr {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (e : X ≃ᵢ Y) (ε : NNReal) (A : Set X) :
    Metric.externalCoveringNumber ε (e '' A) = Metric.externalCoveringNumber ε A := by
  have h_inj : Function.Injective e := e.injective
  have h_symm_inj : Function.Injective e.symm := e.symm.injective
  have h_encard : ∀ (C : Set X), (e '' C).encard = C.encard :=
    fun C => h_inj.encard_image C
  have h_encard2 : ∀ (D : Set Y), (e.symm '' D).encard = D.encard :=
    fun D => h_symm_inj.encard_image D
  apply le_antisymm
  · apply le_iInf
    intro C
    apply le_iInf
    intro hC
    have hC' : Metric.IsCover ε (e '' A) (e '' C) := by
      have h := hC.image_lipschitz (e.isometry.lipschitz)
      simpa [one_mul] using h
    have h_le : Metric.externalCoveringNumber ε (e '' A) ≤ (e '' C).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hC'
    rw [h_encard C] at h_le
    exact h_le
  · apply le_iInf
    intro D
    apply le_iInf
    intro hD
    let C : Set X := e.symm '' D
    have h_eq1 : e.symm '' (e '' A) = A := by ext z; simp
    have h' : Metric.IsCover (1 * ε) (e.symm '' (e '' A)) (e.symm '' D) :=
      hD.image_lipschitz (e.symm.isometry.lipschitz)
    have h'' : Metric.IsCover ε (e.symm '' (e '' A)) (e.symm '' D) := by
      simpa [one_mul] using h'
    have hC : Metric.IsCover ε A C := by
      rw [h_eq1] at h''
      exact h''
    have h_le : Metric.externalCoveringNumber ε A ≤ C.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hC
    have h_eq : C.encard = D.encard := h_encard2 D
    rw [h_eq] at h_le
    exact h_le

/-! ## IsDeltaSet → IsDeltaSSet -/

lemma pow_bridge (r : ℝ) (hr : 0 ≤ r) (s : ℝ) (hs : 0 ≤ s) :
    (ENNReal.ofReal r)^s = ENNReal.ofReal (Real.rpow r s) :=
  ENNReal.ofReal_rpow_of_nonneg hr hs

lemma IsDeltaSSet.mono_C {X : Type*} [PseudoMetricSpace X] {P : Set X} {δ s C C' : ℝ}
    (h : IsDeltaSSet δ s C P) (hC' : 0 < C') (hCC' : C ≤ C') :
    IsDeltaSSet δ s C' P := by
  have hP : P.Nonempty := h.1
  have hδ : 0 < δ := h.2.1
  have hs : 0 ≤ s := h.2.2.2.1
  refine' ⟨hP, hδ, hC', hs, _⟩
  intro x r hr
  have h6 : ENNReal.ofReal C ≤ ENNReal.ofReal C' := ENNReal.ofReal_le_ofReal hCC'
  calc (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal)
    ≤ ENNReal.ofReal C * (ENNReal.ofReal r)^s *
          Metric.externalCoveringNumber δ.toNNReal P := h.2.2.2.2 x r hr
  _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r)^s *
          Metric.externalCoveringNumber δ.toNNReal P := by gcongr

lemma IsDeltaSet.toIsDeltaSSet {X : Type*} [PseudoMetricSpace X]
    {P : Set X} {δ s C : ℝ} {hδ : 0 < δ} {hs : 0 ≤ s} {hC : 0 ≤ C}
    (h : IsDeltaSet δ s C hδ hs hC P) (hP : P.Nonempty) (hCpos : 0 < C) :
    IsDeltaSSet δ s (C * Real.rpow 2 s) P := by
  have h2pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
  have hC'pos : 0 < C * Real.rpow 2 s := mul_pos hCpos h2pos
  refine' ⟨hP, hδ, hC'pos, hs, _⟩
  intro x r hr
  have h_rpos : 0 < r := by linarith
  have h1 : Metric.closedBall x r ⊆ Metric.ball x (r + δ) :=
    Metric.closedBall_subset_ball (by linarith)
  have h2 : P ∩ Metric.closedBall x r ⊆ P ∩ Metric.ball x (r + δ) := by
    gcongr <;> tauto
  have hδn : δ.toNNReal = (⟨δ, hδ.le⟩ : NNReal) := by
    apply NNReal.coe_injective
    have h_coe1 : (δ.toNNReal : ℝ) = δ := Real.coe_toNNReal δ hδ.le
    let δn' : NNReal := ⟨δ, hδ.le⟩
    have h_coe2 : (δn' : ℝ) = δ := by exact Real.ext_cauchy rfl
    rw [h_coe1, h_coe2]
  have h3 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.ball x (r + δ)) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set h2
  have h4 : δ ≤ r + δ := by linarith
  have h5 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.ball x (r + δ)) : ENNReal) ≤
      ENNReal.ofReal (C * Real.rpow (r + δ) s) *
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
    rw [hδn]
    simpa using h.spec x (r + δ) h4
  have h6 : r + δ ≤ 2 * r := by linarith
  have h7 : Real.rpow (r + δ) s ≤ Real.rpow (2 * r) s :=
    Real.rpow_le_rpow (by linarith) h6 hs
  have h8 : Real.rpow (2 * r) s = Real.rpow 2 s * Real.rpow r s := by
    have h9 : Real.rpow (2 * r) s = Real.rpow ((2 : ℝ) * r) s := by ring_nf
    rw [h9]
    exact Real.mul_rpow (by norm_num) (by linarith)
  have h9 : C * Real.rpow (r + δ) s ≤ C * Real.rpow 2 s * Real.rpow r s := by
    calc C * Real.rpow (r + δ) s
      ≤ C * Real.rpow (2 * r) s := by gcongr
    _ = C * (Real.rpow 2 s * Real.rpow r s) := by rw [h8]
    _ = C * Real.rpow 2 s * Real.rpow r s := by ring
  have h10 : ENNReal.ofReal (C * Real.rpow (r + δ) s) ≤
      ENNReal.ofReal (C * Real.rpow 2 s * Real.rpow r s) :=
    ENNReal.ofReal_le_ofReal h9
  have h12 : 0 ≤ C * Real.rpow 2 s := by positivity
  have h11 : ENNReal.ofReal (C * Real.rpow 2 s * Real.rpow r s) =
      ENNReal.ofReal (C * Real.rpow 2 s) * (ENNReal.ofReal r)^s := by
    have h14 : C * Real.rpow 2 s * Real.rpow r s = (C * Real.rpow 2 s) * Real.rpow r s := by ring
    rw [h14]
    rw [ENNReal.ofReal_mul h12]
    rw [pow_bridge r (by linarith) s hs]
    <;> rfl
  calc (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal)
    ≤ (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.ball x (r + δ)) : ENNReal) := h3
  _ ≤ ENNReal.ofReal (C * Real.rpow (r + δ) s) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h5
  _ ≤ ENNReal.ofReal (C * Real.rpow 2 s * Real.rpow r s) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
      gcongr
  _ = ENNReal.ofReal (C * Real.rpow 2 s) * (ENNReal.ofReal r)^s *
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
      rw [h11] <;> ring

lemma IsDeltaSSet.toAffineImage {P : Set Line2} {δ s C : ℝ}
    (h : IsDeltaSSet δ s C P) :
    IsDeltaSSet δ s C (line2EquivAffineLine '' P) := by
  let e : Line2 ≃ᵢ AffineLine := line2EquivAffineLine
  have hP : P.Nonempty := h.1
  have hδ : 0 < δ := h.2.1
  have hC : 0 < C := h.2.2.1
  have hs : 0 ≤ s := h.2.2.2.1
  have h_image_nonempty : (e '' P).Nonempty := hP.image _
  refine' ⟨h_image_nonempty, hδ, hC, hs, _⟩
  intro y r hr
  let x : Line2 := e.symm y
  have hxy : e x = y := e.apply_symm_apply y
  have h_ball : e '' (P ∩ Metric.closedBall x r) =
      (e '' P) ∩ Metric.closedBall y r := by
    ext z
    simp only [Set.mem_image, Set.mem_inter_iff]
    constructor
    · rintro ⟨a, ⟨haP, ha⟩, rfl⟩
      have hdist : dist (e a) y ≤ r := by
        have h' : dist (e a) (e x) ≤ r := by
          rw [e.dist_eq] <;> exact ha
        have h_eq : e x = y := hxy
        exact h_eq ▸ h'
      exact ⟨⟨a, haP, rfl⟩, hdist⟩
    · rintro ⟨⟨a, haP, rfl⟩, hz⟩
      have hdist : dist a x ≤ r := by
        have h : dist (e a) y ≤ r := hz
        have h_eq : y = e x := hxy.symm
        have h' : dist (e a) (e x) ≤ r := by
          rw [h_eq] at h
          exact h
        rw [e.dist_eq] at h'
        exact h'
      exact ⟨a, ⟨haP, hdist⟩, rfl⟩
  have h_cov : (Metric.externalCoveringNumber δ.toNNReal (e '' (P ∩ Metric.closedBall x r)) : ENNReal) =
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) := by
    exact_mod_cast externalCoveringNumber_congr e δ.toNNReal (P ∩ Metric.closedBall x r)
  have h_covP : (Metric.externalCoveringNumber δ.toNNReal (e '' P) : ENNReal) =
      (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
    exact_mod_cast externalCoveringNumber_congr e δ.toNNReal P
  have h_goal : (Metric.externalCoveringNumber δ.toNNReal ((e '' P) ∩ Metric.closedBall y r) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r)^s *
        Metric.externalCoveringNumber δ.toNNReal (e '' P) := by
    rw [← h_ball, h_cov, h_covP]
    exact h.2.2.2.2 x r hr
  exact h_goal

lemma tube_subset_cthickening {L : Line2} {δ : ℝ} :
    tube δ L ⊆ Metric.cthickening δ L.toSet :=
  Metric.thickening_subset_cthickening δ L.toSet

/-- Convert an ENNReal inequality involving `ofReal` and a natural coefficient
to a real inequality. This is a standard fact but extracted here to avoid
`exact_mod_cast` timeouts. -/
lemma enreal_ofReal_le_coe_nat {x : ℝ} {n : ℕ} (hx : 0 ≤ x)
    (h : ENNReal.ofReal x ≤ (↑n : ENNReal)) : x ≤ (n : ℝ) := by
  have h_nat_coe : (↑n : ENNReal) = ENNReal.ofReal (↑n : ℝ) := by simp
  rw [h_nat_coe] at h
  have h_pos' : 0 ≤ (↑n : ℝ) := by positivity
  have h_iff : ENNReal.ofReal x ≤ ENNReal.ofReal (↑n : ℝ) ↔ x ≤ (↑n : ℝ) := by
    exact ENNReal.ofReal_le_ofReal_iff h_pos'
  exact h_iff.mp h

/-! ## Scale adjustment lemma

If `δ ≤ 2^{-2K/ε_a}`, then `δ^{-ε_a/2} * 2^K ≤ δ^{-ε_a}`.
-/

lemma scale_lemma (δ K ε_a : ℝ) (hδ : 0 < δ) (hK : 0 ≤ K) (hεa : 0 < ε_a)
    (h : δ ≤ Real.rpow 2 (-(2 * K / ε_a))) :
    Real.rpow δ (-(ε_a / 2)) * Real.rpow 2 K ≤ Real.rpow δ (-ε_a) := by
  have h_exp_nonneg : 0 ≤ ε_a / 2 := by positivity
  -- Step 1: δ^{ε_a/2} ≤ (2^{-2K/ε_a})^{ε_a/2} = 2^{-K}
  have h1 : Real.rpow δ (ε_a / 2) ≤ Real.rpow 2 (-K) := by
    have h2 : Real.rpow δ (ε_a / 2) ≤ Real.rpow (Real.rpow 2 (-(2 * K / ε_a))) (ε_a / 2) :=
      Real.rpow_le_rpow (by positivity) h h_exp_nonneg
    have h3 : Real.rpow (Real.rpow 2 (-(2 * K / ε_a))) (ε_a / 2) = Real.rpow 2 (-K) := by
      have h4 : 0 ≤ (2 : ℝ) := by norm_num
      have h5 : Real.rpow (Real.rpow 2 (-(2 * K / ε_a))) (ε_a / 2) =
          Real.rpow 2 ((-(2 * K / ε_a)) * (ε_a / 2)) := by
        have h51 : ((Real.rpow 2 (-(2 * K / ε_a))) ^ (ε_a / 2)) =
            (2 : ℝ) ^ ((-(2 * K / ε_a)) * (ε_a / 2)) :=
          (Real.rpow_mul h4 _ _).symm
        have h52 : Real.rpow (Real.rpow 2 (-(2 * K / ε_a))) (ε_a / 2) =
            (Real.rpow 2 (-(2 * K / ε_a))) ^ (ε_a / 2) := by rfl
        have h53 : Real.rpow 2 ((-(2 * K / ε_a)) * (ε_a / 2)) =
            (2 : ℝ) ^ ((-(2 * K / ε_a)) * (ε_a / 2)) := by rfl
        rw [h52, h53]
        exact h51
      rw [h5]
      have h6 : (-(2 * K / ε_a)) * (ε_a / 2) = -K := by
        field_simp [hεa.ne'] <;> ring
      rw [h6]
      <;> rfl
    rw [h3] at h2
    exact h2
  -- Step 2: take inverses: 2^K ≤ δ^{-ε_a/2}
  have h4 : 0 < Real.rpow δ (ε_a / 2) := Real.rpow_pos_of_pos hδ _
  have h5 : 0 < Real.rpow 2 K := Real.rpow_pos_of_pos (by norm_num) K
  have h6 : Real.rpow 2 (-K) = (Real.rpow 2 K)⁻¹ := by
    have h7 : Real.rpow 2 (-K) = (Real.rpow 2 K)⁻¹ := by
      simp [Real.rpow_neg, hK]
      <;> ring
    exact h7
  have h8 : Real.rpow δ (-(ε_a / 2)) = (Real.rpow δ (ε_a / 2))⁻¹ := by
    simp [Real.rpow_neg, hδ.le]
    <;> ring
  have h9 : (Real.rpow 2 (-K))⁻¹ ≤ (Real.rpow δ (ε_a / 2))⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le h4 h1
  have h10 : (Real.rpow 2 (-K))⁻¹ = Real.rpow 2 K := by
    rw [h6]
    <;> field_simp
  have h11 : Real.rpow 2 K ≤ (Real.rpow δ (ε_a / 2))⁻¹ := by
    rw [← h10]
    exact h9
  have h12 : Real.rpow 2 K ≤ Real.rpow δ (-(ε_a / 2)) := by
    rw [h8]
    exact h11
  -- Step 3: multiply by δ^{-ε_a/2}
  have h13 : 0 ≤ Real.rpow δ (-(ε_a / 2)) := (Real.rpow_pos_of_pos hδ _).le
  have h14 : Real.rpow δ (-(ε_a / 2)) * Real.rpow 2 K ≤
      Real.rpow δ (-(ε_a / 2)) * Real.rpow δ (-(ε_a / 2)) := by
    gcongr
    <;> exact h12
  -- Step 4: δ^{-ε_a/2} * δ^{-ε_a/2} = δ^{-ε_a}
  have h13 : Real.rpow δ (-(ε_a / 2)) * Real.rpow δ (-(ε_a / 2)) = Real.rpow δ (-ε_a) := by
    have h14 : Real.rpow δ (-(ε_a / 2)) * Real.rpow δ (-(ε_a / 2)) =
        Real.rpow δ (-(ε_a / 2) + -(ε_a / 2)) :=
      (Real.rpow_add (hx := hδ) (-(ε_a / 2)) (-(ε_a / 2))).symm
    rw [h14]
    have h15 : -(ε_a / 2) + -(ε_a / 2) = -ε_a := by ring
    rw [h15]
    <;> rfl
  rw [h13] at h14
  exact h14

/-! ## Main theorem -/

theorem furstenberg_lower_bound
    (s t : ℝ) (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2) :
    ∃ (ε : ℝ), 0 < ε ∧
      ∃ (δ₀ : ℝ), 0 < δ₀ ∧
        ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ δ₀ →
          ∀ (X : Set Point) (T : Point → Set Line2),
            X.Nonempty →
              X ⊆ closedBall 0 1 →
                IsDeltaSet δ t (Real.rpow δ (-ε)) hδ
                  (le_of_lt (lt_trans hs hst)) (Real.rpow_nonneg hδ.le _) X →
                  (∀ x ∈ X, (T x).Nonempty ∧
                    IsDeltaSet δ s (Real.rpow δ (-ε)) hδ
                      (le_of_lt hs) (Real.rpow_nonneg hδ.le _) (T x) ∧
                      ∀ ℓ ∈ T x, x ∈ tube δ ℓ) →
                  (hfin : Set.Finite (⋃ x ∈ X, T x)) →
                    (⋃ x ∈ X, T x).ncard ≥
                      Nat.ceil (Real.rpow δ (-2 * s - ε)) := by
  rcases discretised_furstenberg_estimate with ⟨ε_axiom, hε_pos, _, h_main_axiom⟩
  have h_range : (s, t) ∈ parameterRange := by
    simp [parameterRange, hs, hs1, hst, ht2] <;> norm_num <;> linarith
  let ε_a : ℝ := ε_axiom (s, t)
  have hεa_pos : 0 < ε_a := hε_pos (s, t) h_range
  rcases h_main_axiom s t h_range with ⟨δ₀_axiom, hδ₀_pos, h_axiom⟩

  let ε : ℝ := ε_a / 2
  have hε_pos' : 0 < ε := half_pos hεa_pos
  have hε_lt : ε < ε_a := by
    dsimp only [ε]
    linarith [hεa_pos]
  let K : ℝ := max s t
  have hK_nonneg : 0 ≤ K := by positivity
  have hK_pos : 0 < K := by
    dsimp only [K]
    positivity
  let δ_scale : ℝ := Real.rpow 2 (-(2 * K / ε_a))
  have hδ_scale_pos : 0 < δ_scale := Real.rpow_pos_of_pos (by norm_num) _
  have hδ_scale_lt_one : δ_scale < 1 := by
    dsimp only [δ_scale]
    have h1 : 0 < 2 * K / ε_a := by positivity
    have h2 : Real.rpow 2 (-(2 * K / ε_a)) < 1 := by
      have h3 : Real.rpow 2 (-(2 * K / ε_a)) < Real.rpow 2 0 :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      have h4 : Real.rpow 2 0 = 1 := by simp
      linarith
    exact h2
  let δ₀ : ℝ := min δ₀_axiom δ_scale
  have hδ₀_pos' : 0 < δ₀ := lt_min hδ₀_pos hδ_scale_pos

  refine' ⟨ε, hε_pos', δ₀, hδ₀_pos', _⟩
  intro δ hδ hδ₀ X T hX_nonempty hX_ball hX_delta hT hfin

  have hδ_le_axiom : δ ≤ δ₀_axiom := le_trans hδ₀ (min_le_left _ _)
  have hδ_le_scale : δ ≤ δ_scale := le_trans hδ₀ (min_le_right _ _)
  have hδ_lt_one : δ < 1 := by
    calc δ ≤ δ_scale := hδ_le_scale
         _ < 1 := hδ_scale_lt_one

  have h_const : Real.rpow δ (-ε) * Real.rpow 2 K ≤ Real.rpow δ (-ε_a) :=
    scale_lemma δ K ε_a hδ hK_nonneg hεa_pos hδ_le_scale

  have hX_sset : IsDeltaSSet δ t (Real.rpow δ (-ε_a)) X := by
    have h1 : IsDeltaSSet δ t (Real.rpow δ (-ε) * Real.rpow 2 t) X :=
      IsDeltaSet.toIsDeltaSSet hX_delta hX_nonempty (Real.rpow_pos_of_pos hδ _)
    have h2 : Real.rpow δ (-ε) * Real.rpow 2 t ≤ Real.rpow δ (-ε_a) := by
      have h3 : Real.rpow 2 t ≤ Real.rpow 2 K := by
        have h4 : t ≤ K := le_max_right s t
        have h5 : 0 ≤ t := by linarith
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h4
      have hpos1 : 0 ≤ Real.rpow δ (-ε) := Real.rpow_nonneg (by linarith) (-ε)
      calc Real.rpow δ (-ε) * Real.rpow 2 t
        ≤ Real.rpow δ (-ε) * Real.rpow 2 K := by gcongr <;> positivity
      _ ≤ Real.rpow δ (-ε_a) := h_const
    exact IsDeltaSSet.mono_C h1 (Real.rpow_pos_of_pos hδ _) h2

  have hT_sset : ∀ (x : Point) (hx : x ∈ X),
      IsDeltaSSet δ s (Real.rpow δ (-ε_a)) (line2EquivAffineLine '' (T x)) := by
    intro x hx
    have hT_x := hT x hx
    have hT_nonempty : (T x).Nonempty := hT_x.1
    have hT_delta := hT_x.2.1
    have h1 : IsDeltaSSet δ s (Real.rpow δ (-ε) * Real.rpow 2 s) (T x) :=
      IsDeltaSet.toIsDeltaSSet hT_delta hT_nonempty (Real.rpow_pos_of_pos hδ _)
    have h2 : Real.rpow δ (-ε) * Real.rpow 2 s ≤ Real.rpow δ (-ε_a) := by
      have h3 : Real.rpow 2 s ≤ Real.rpow 2 K := by
        have h4 : s ≤ K := le_max_left s t
        have h5 : 0 ≤ s := by linarith
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h4
      have hpos1 : 0 ≤ Real.rpow δ (-ε) := Real.rpow_nonneg (by linarith) (-ε)
      calc Real.rpow δ (-ε) * Real.rpow 2 s
        ≤ Real.rpow δ (-ε) * Real.rpow 2 K := by gcongr <;> positivity
      _ ≤ Real.rpow δ (-ε_a) := h_const
    have h3 : IsDeltaSSet δ s (Real.rpow δ (-ε_a)) (T x) :=
      IsDeltaSSet.mono_C h1 (Real.rpow_pos_of_pos hδ _) h2
    exact IsDeltaSSet.toAffineImage h3

  have h_tube : ∀ (x : Point) (hx : x ∈ X),
      ∀ (ℓ : AffineLine), ℓ ∈ line2EquivAffineLine '' (T x) →
        x ∈ Metric.cthickening δ ℓ.1 := by
    intro x hx ℓ hℓ
    rcases hℓ with ⟨L, hL, rfl⟩
    have h4 : x ∈ tube δ L := (hT x hx).2.2 L hL
    exact tube_subset_cthickening h4

  let 𝓣 : ∀ (x : Point), x ∈ X → Set AffineLine :=
    fun x hx => line2EquivAffineLine '' (T x)

  have h_lower := h_axiom δ ⟨hδ, hδ_le_axiom⟩ X hX_ball hX_sset 𝓣 hT_sset h_tube

  let S : Set Line2 := ⋃ x ∈ X, T x
  let S' : Set AffineLine := ⋃ (x : Point) (hx : x ∈ X), 𝓣 x hx
  have h_image : S' = line2EquivAffineLine '' S := by
    ext z
    simp only [S', S, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨x, hx, ℓ, hℓ, rfl⟩
      exact ⟨ℓ, ⟨x, hx, hℓ⟩, rfl⟩
    · rintro ⟨ℓ, ⟨x, hx, hℓ⟩, rfl⟩
      exact ⟨x, hx, ℓ, hℓ, rfl⟩
  have h_cov_transfer : (Metric.externalCoveringNumber δ.toNNReal S' : ENNReal) =
      (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := by
    rw [h_image]
    exact_mod_cast externalCoveringNumber_congr line2EquivAffineLine δ.toNNReal S

  have h_main1 : ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_a))) ≤
      (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := by
    rw [← h_cov_transfer]
    exact h_lower

  have h1 : Metric.externalCoveringNumber δ.toNNReal S ≤ S.encard :=
    Metric.externalCoveringNumber_le_encard_self (A := S)
  have h_encard : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤ (S.encard : ENNReal) := by
    exact_mod_cast h1
  have h_fin_encard : S.encard = ↑S.ncard := Set.Finite.encard_eq_coe hfin
  have h4 : ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_a))) ≤ (↑S.ncard : ENNReal) := by
    rw [h_fin_encard] at h_encard
    exact le_trans h_main1 h_encard

  have h5 : Real.rpow δ (-(2 * s + ε)) ≤ Real.rpow δ (-(2 * s + ε_a)) := by
    have h6 : -(2 * s + ε_a) ≤ -(2 * s + ε) := by
      dsimp only [ε]
      linarith [hεa_pos]
    exact Real.rpow_le_rpow_of_exponent_ge hδ (by linarith) h6

  have h7 : ENNReal.ofReal (Real.rpow δ (-(2 * s + ε))) ≤ (↑S.ncard : ENNReal) :=
    le_trans (ENNReal.ofReal_le_ofReal h5) h4

  have h_pos : 0 ≤ Real.rpow δ (-(2 * s + ε)) := Real.rpow_nonneg (by linarith) _
  have h8 : Real.rpow δ (-(2 * s + ε)) ≤ (S.ncard : ℝ) :=
    enreal_ofReal_le_coe_nat h_pos h7

  have h9 : Real.rpow δ (-2 * s - ε) = Real.rpow δ (-(2 * s + ε)) := by ring_nf
  have h10 : (S.ncard : ℝ) = ((⋃ x ∈ X, T x).ncard : ℝ) := by
    congr <;> rfl
  have h_final : Real.rpow δ (-2 * s - ε) ≤ ((⋃ x ∈ X, T x).ncard : ℝ) := by
    rw [h9, ←h10]
    exact h8
  exact Nat.ceil_le.mpr h_final

/-- Derive a Furstenberg lower bound with a smaller epsilon `εF ≤ ε_F`.

If `furstenberg_lower_bound` gives `ε_F`, and we choose `εF ≤ ε_F`, then:
- The delta-set constant `δ^{-εF}` is smaller (stronger), so it mono's to `δ^{-ε_F}`
- The lower bound `δ^{-2s-εF}` is weaker, so it follows from the `ε_F` bound

This is used to wire the main proof's chosen `εF` to the axiom's existential `ε_F`.
-/
lemma furstenberg_lower_bound_with_epsilon
    (s t : ℝ) (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2)
    (ε_F δ₀ : ℝ) (hεF_pos : 0 < ε_F) (hδ₀_pos : 0 < δ₀)
    (hF : ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ δ₀ →
      ∀ (X : Set Point) (T : Point → Set Line2),
        X.Nonempty → X ⊆ closedBall 0 1 →
        IsDeltaSet δ t (Real.rpow δ (-ε_F)) hδ (le_of_lt (lt_trans hs hst))
          (Real.rpow_nonneg hδ.le _) X →
        (∀ x ∈ X, (T x).Nonempty ∧
          IsDeltaSet δ s (Real.rpow δ (-ε_F)) hδ (le_of_lt hs)
            (Real.rpow_nonneg hδ.le _) (T x) ∧
          ∀ ℓ ∈ T x, x ∈ tube δ ℓ) →
        Set.Finite (⋃ x ∈ X, T x) →
        (⋃ x ∈ X, T x).ncard ≥ Nat.ceil (Real.rpow δ (-2 * s - ε_F)))
    (εF : ℝ) (hεF'_pos : 0 < εF) (hεF_le : εF ≤ ε_F)
    (δ : ℝ) (hδ : 0 < δ) (hδ_lt_one : δ < 1) (hδ_le : δ ≤ δ₀)
    (X : Set Point) (T : Point → Set Line2)
    (hX_nonempty : X.Nonempty) (hX_ball : X ⊆ closedBall 0 1)
    (hX_delta : IsDeltaSet δ t (Real.rpow δ (-εF)) hδ
      (le_of_lt (lt_trans hs hst)) (Real.rpow_nonneg hδ.le _) X)
    (hT : ∀ x ∈ X, (T x).Nonempty ∧
      IsDeltaSet δ s (Real.rpow δ (-εF)) hδ (le_of_lt hs)
        (Real.rpow_nonneg hδ.le _) (T x) ∧
      ∀ ℓ ∈ T x, x ∈ tube δ ℓ)
    (hfin : Set.Finite (⋃ x ∈ X, T x)) :
    (⋃ x ∈ X, T x).ncard ≥ Nat.ceil (Real.rpow δ (-2 * s - εF)) := by
  have h_rpow_le1 : Real.rpow δ (-εF) ≤ Real.rpow δ (-ε_F) := by
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ_lt_one.le (by linarith)
  have hX_delta' : IsDeltaSet δ t (Real.rpow δ (-ε_F)) hδ
      (le_of_lt (lt_trans hs hst)) (Real.rpow_nonneg hδ.le _) X :=
    IsDeltaSet.mono_C hX_delta (Real.rpow_nonneg hδ.le _) h_rpow_le1
  have hT' : ∀ x ∈ X, (T x).Nonempty ∧
      IsDeltaSet δ s (Real.rpow δ (-ε_F)) hδ (le_of_lt hs)
        (Real.rpow_nonneg hδ.le _) (T x) ∧
      ∀ ℓ ∈ T x, x ∈ tube δ ℓ := by
    intro x hx
    have h1 := hT x hx
    have h2 : IsDeltaSet δ s (Real.rpow δ (-ε_F)) hδ (le_of_lt hs)
        (Real.rpow_nonneg hδ.le _) (T x) :=
      IsDeltaSet.mono_C h1.2.1 (Real.rpow_nonneg hδ.le _) h_rpow_le1
    exact ⟨h1.1, h2, h1.2.2⟩
  have h_ncard_F : (⋃ x ∈ X, T x).ncard ≥ Nat.ceil (Real.rpow δ (-2 * s - ε_F)) :=
    hF δ hδ hδ_le X T hX_nonempty hX_ball hX_delta' hT' hfin
  have h_bound_le : Real.rpow δ (-2 * s - εF) ≤ Real.rpow δ (-2 * s - ε_F) := by
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ_lt_one.le (by linarith)
  have h9 : ((⋃ x ∈ X, T x).ncard : ℝ) ≥ Real.rpow δ (-2 * s - ε_F) := by
    have h10 : ((⋃ x ∈ X, T x).ncard : ℝ) ≥
        ↑(Nat.ceil (Real.rpow δ (-2 * s - ε_F))) := by exact_mod_cast h_ncard_F
    have h11 : (↑(Nat.ceil (Real.rpow δ (-2 * s - ε_F))) : ℝ) ≥
        Real.rpow δ (-2 * s - ε_F) := Nat.le_ceil _
    linarith
  have h12 : ((⋃ x ∈ X, T x).ncard : ℝ) ≥ Real.rpow δ (-2 * s - εF) := by
    linarith [h_bound_le]
  exact Nat.ceil_le.mpr h12

end FurstenbergEstimate
