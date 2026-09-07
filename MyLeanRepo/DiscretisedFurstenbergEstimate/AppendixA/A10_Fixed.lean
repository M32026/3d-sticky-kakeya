module

/-
  A10: Product witness assembly — FIXED version.

  Changes from A10_Correct:
  - τ := min(t-s, 1) instead of ε
  - Y := {y_Q} (bounded-fibre projection of Q0)
  - X_y := union of translated Pi_Q_norm for squares with y_Q=y
  - Intercept shear cancels witness-y mismatch exactly
  - Shear transfer for IsDeltaSSet with constant degradation

  Whiteprint node: appendix_a_alternative / a10_product_witness
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductStructureRescaling.product_structure_rescaling
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A10_FineRescalable
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA.A10

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CoveringUtils

/-- Convert ℝ×ℝ to EuclideanPlane. -/
noncomputable def toPlane' : ℝ × ℝ → EuclideanPlane := fun p =>
  EuclideanSpace.equiv (Fin 2) ℝ |>.symm (fun i => if i = 0 then p.1 else p.2)

/-- Convert EuclideanPlane to ℝ×ℝ. -/
def fromPlane' : EuclideanPlane → ℝ × ℝ := fun q => (q 0, q 1)

/-- Weaken the constant of an IsDeltaSSet. -/
lemma IsDeltaSSet.mono_const' {X : Type*} [PseudoMetricSpace X]
    {δ s C1 C2 : ℝ} {A : Set X}
    (h : IsDeltaSSet δ s C1 A) (hC : C1 ≤ C2) :
    IsDeltaSSet δ s C2 A := by
  rcases h with ⟨hne, hδ, hC1_pos, hs, hmain⟩
  have hC2_pos : 0 < C2 := by linarith
  refine ⟨hne, hδ, hC2_pos, hs, fun x r hr => ?_⟩
  have h := hmain x r hr
  have h' : ENNReal.ofReal C1 ≤ ENNReal.ofReal C2 := ENNReal.ofReal_le_ofReal hC
  calc (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r) : ENNReal)
    ≤ ENNReal.ofReal C1 * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := h
  _ ≤ ENNReal.ofReal C2 * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by
    gcongr <;> exact h'

/-- Translation preserves IsDeltaSSet on ℝ. -/
lemma IsDeltaSSet.translation_real {δ s C : ℝ} {A : Set ℝ} {c : ℝ}
    (h : IsDeltaSSet δ s C A) :
    IsDeltaSSet δ s C ((fun x : ℝ => x + c) '' A) := by
  let f : ℝ → ℝ := fun x => x + c
  let g : ℝ → ℝ := fun x => x - c
  have hf : LipschitzWith (1 : NNReal) f :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simp [f, Real.dist_eq] <;> ring_nf <;> norm_num
  have hg : LipschitzWith (1 : NNReal) g :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simp [g, Real.dist_eq] <;> ring_nf <;> norm_num
  have hcov : ∀ (B : Set ℝ), Metric.externalCoveringNumber δ.toNNReal (f '' B) =
      Metric.externalCoveringNumber δ.toNNReal B := by
    intro B
    have h1 : Metric.externalCoveringNumber ((1 : NNReal) * δ.toNNReal) (f '' B) ≤
        Metric.externalCoveringNumber δ.toNNReal B :=
      _root_.externalCoveringNumber_image_lipschitz (hf := hf)
    have h1' : Metric.externalCoveringNumber δ.toNNReal (f '' B) ≤
        Metric.externalCoveringNumber δ.toNNReal B := by
      have h_eq : (1 : NNReal) * δ.toNNReal = δ.toNNReal := by simp
      rw [h_eq] at h1
      exact h1
    have h3 : g '' (f '' B) = B := by
      ext z
      simp only [Set.mem_image]
      constructor
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        have h4 : g (f x) = x := by simp [g, f] <;> ring
        rw [h4]; exact hx
      · intro hz
        exact ⟨f z, ⟨z, hz, rfl⟩, by simp [g, f]⟩
    have h4 : Metric.externalCoveringNumber ((1 : NNReal) * δ.toNNReal) (g '' (f '' B)) ≤
        Metric.externalCoveringNumber δ.toNNReal (f '' B) :=
      _root_.externalCoveringNumber_image_lipschitz (hf := hg)
    have h4' : Metric.externalCoveringNumber δ.toNNReal (g '' (f '' B)) ≤
        Metric.externalCoveringNumber δ.toNNReal (f '' B) := by
      have h_eq : (1 : NNReal) * δ.toNNReal = δ.toNNReal := by simp
      rw [h_eq] at h4
      exact h4
    rw [h3] at h4'
    exact le_antisymm h1' h4'
  rcases h with ⟨hA_nonempty, hδ_pos, hC_pos, hs_nonneg, h_main⟩
  refine ⟨hA_nonempty.image f, hδ_pos, hC_pos, hs_nonneg, ?_⟩
  intro y r hr
  have hball : (f '' A) ∩ Metric.closedBall y r =
      f '' (A ∩ Metric.closedBall (g y) r) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_image, Metric.mem_closedBall]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hdist⟩
      have h5 : dist x (g y) ≤ r := by
        have h6 : dist (f x) y ≤ r := hdist
        have h7 : dist x (g y) = dist (f x) y := by
          simpa [f, g, Real.dist_eq] using rfl
        rw [h7]; exact h6
      exact ⟨x, ⟨hx, h5⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hdist⟩, rfl⟩
      have h5 : dist (f x) y ≤ r := by
        have h6 : dist x (g y) ≤ r := hdist
        have h7 : dist (f x) y = dist x (g y) := by
          simpa [f, g, Real.dist_eq] using rfl
        rw [h7]; exact h6
      exact ⟨⟨x, hx, rfl⟩, h5⟩
  rw [hball]
  rw [hcov (A ∩ Metric.closedBall (g y) r)]
  have h7 := h_main (g y) r hr
  rw [hcov A] at *
  exact h7

/-! ### Covering refinement on ℝ×ℝ -/

/-- Covering number of Lipschitz image: N_{Kε}(f '' A) ≤ N_ε(A). -/
lemma external_covering_number_lipschitz_image {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {K : NNReal} (hf : LipschitzWith K f) {ε : NNReal} {A : Set X} :
    Metric.externalCoveringNumber (K * ε) (f '' A) ≤ Metric.externalCoveringNumber ε A := by
  have h_main : ∀ (S : Set X), Metric.IsCover ε A S →
      Metric.externalCoveringNumber (K * ε) (f '' A) ≤ S.encard := by
    intro S hS
    have h' : Metric.IsCover (K * ε) (f '' A) (f '' S) := hS.image_lipschitz hf
    have h1 : Metric.externalCoveringNumber (K * ε) (f '' A) ≤ (f '' S).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard h'
    have h2 : (f '' S).encard ≤ S.encard := Set.encard_image_le f S
    exact h1.trans h2
  have h_iInf : Metric.externalCoveringNumber (K * ε) (f '' A) ≤
      ⨅ (S : Set X), ⨅ (_ : Metric.IsCover ε A S), S.encard := by
    apply le_iInf; intro S; apply le_iInf; exact h_main S
  simpa [Metric.externalCoveringNumber] using h_iInf

/-- General covering refinement using a minimal cover. -/
lemma covering_refine_factor {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    {δ R : NNReal} (hδ_pos : 0 < δ) (hR_pos : 0 < R)
    {C : ℕ} (hC_pos : 0 < C)
    (h_ball : ∀ (x : X), ∃ (D : Finset X), D.card ≤ C ∧
      Metric.IsCover δ (Metric.closedBall x (R : ℝ)) D)
    {A : Set X} :
    (Metric.externalCoveringNumber δ A : ENNReal) ≤
    (C : ENNReal) * (Metric.externalCoveringNumber R A : ENNReal) := by
  by_cases h_top : Metric.externalCoveringNumber R A = ⊤
  · rw [h_top]; simp [hC_pos.ne'] <;> exact le_top
  · have h_lt_top : Metric.externalCoveringNumber R A < ⊤ := Ne.lt_top h_top
    rcases DiscretisedFurstenbergEstimate.CoveringUtils.exists_external_cover_eq h_lt_top with ⟨S, hS_cover, hS_encard⟩
    have hS_finite : S.Finite := by
      have h : S.encard ≠ ⊤ := by rw [hS_encard]; exact h_lt_top.ne
      exact Set.encard_ne_top_iff.mp h
    let S_finset := hS_finite.toFinset
    choose D hD_card hD_cover using h_ball
    let Dfin := S_finset.biUnion D
    have h_cover : Metric.IsCover δ A (Dfin : Set X) := by
      intro x hx
      rcases hS_cover hx with ⟨c, hc, hdist⟩
      have hc' : c ∈ S_finset := by
        have h : c ∈ (S_finset : Set X) := by rw [Set.Finite.coe_toFinset] <;> exact hc
        exact_mod_cast h
      have h_x_in : x ∈ Metric.closedBall c (R : ℝ) := by simpa [Metric.mem_closedBall] using hdist
      rcases hD_cover c h_x_in with ⟨d, hd_in_D, hdist_d⟩
      have hd_in_Dfin : d ∈ Dfin := Finset.mem_biUnion.mpr ⟨c, hc', hd_in_D⟩
      exact ⟨d, hd_in_Dfin, hdist_d⟩
    have h1 : Metric.externalCoveringNumber δ A ≤ (Dfin : Set X).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard h_cover
    have h4 : Dfin.card ≤ S_finset.card * C := by
      calc Dfin.card
        ≤ ∑ c ∈ S_finset, (D c).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ S_finset, C := by apply Finset.sum_le_sum; intro c _; exact hD_card c
      _ = S_finset.card * C := by rw [Finset.sum_const] <;> ring
    have h5 : (S.encard : ENNReal) = ↑S_finset.card := by
      have h6 : (S_finset : Set X) = S := Set.Finite.coe_toFinset hS_finite
      rw [←h6]; simp
    have h6 : (Metric.externalCoveringNumber δ A : ENNReal) ≤ (C : ENNReal) * (S.encard : ENNReal) := by
      calc (Metric.externalCoveringNumber δ A : ENNReal)
          ≤ (Dfin.card : ENNReal) := by exact_mod_cast h1
        _ ≤ ((S_finset.card * C : ℕ) : ENNReal) := by exact_mod_cast h4
        _ = (C : ENNReal) * (S.encard : ENNReal) := by rw [h5] <;> simp [mul_comm] <;> ring
    rw [hS_encard] at h6
    exact h6

/-- A 2δ-ball in L∞ on ℝ×ℝ is covered by 4 δ-balls. -/
lemma prod_ball_cover_4 {δ : NNReal} (hδ_pos : 0 < δ) (x : ℝ × ℝ) :
    ∃ (D : Finset (ℝ × ℝ)), D.card ≤ 4 ∧
    Metric.IsCover δ (Metric.closedBall x (2 * (δ : ℝ))) (D : Set (ℝ × ℝ)) := by
  let δr : ℝ := (δ : ℝ)
  let c1 := (x.1 - δr, x.2 - δr)
  let c2 := (x.1 + δr, x.2 - δr)
  let c3 := (x.1 - δr, x.2 + δr)
  let c4 := (x.1 + δr, x.2 + δr)
  let D : Finset (ℝ × ℝ) := {c1, c2, c3, c4}
  have hD_card : D.card ≤ 4 := by exact Finset.card_le_four
  have h_cover : Metric.IsCover δ (Metric.closedBall x (2 * δr)) (D : Set (ℝ × ℝ)) := by
    intro y hy
    have h_dist : dist y x ≤ 2 * δr := by simpa [Metric.mem_closedBall] using hy
    have h1 : |y.1 - x.1| ≤ 2 * δr := by
      have h : dist y x = max (|y.1 - x.1|) (|y.2 - x.2|) := by simp [Prod.dist_eq] <;> rfl
      rw [h] at h_dist; exact le_trans (le_max_left _ _) h_dist
    have h2 : |y.2 - x.2| ≤ 2 * δr := by
      have h : dist y x = max (|y.1 - x.1|) (|y.2 - x.2|) := by simp [Prod.dist_eq] <;> rfl
      rw [h] at h_dist; exact le_trans (le_max_right _ _) h_dist
    let c : ℝ × ℝ :=
      (if y.1 ≤ x.1 then x.1 - δr else x.1 + δr,
       if y.2 ≤ x.2 then x.2 - δr else x.2 + δr)
    have hc_in_D : c ∈ D := by
      simp only [D, Finset.mem_insert, Finset.mem_singleton]
      by_cases h1' : y.1 ≤ x.1 <;> by_cases h2' : y.2 ≤ x.2 <;>
        simp [c, h1', h2', c1, c2, c3, c4]
    have h3 : |y.1 - c.1| ≤ δr := by
      have hc1 : c.1 = (if y.1 ≤ x.1 then x.1 - δr else x.1 + δr) := by rfl
      rw [hc1]; by_cases h : y.1 ≤ x.1
      · rw [if_pos h]; have h4 : -(2 * δr) ≤ y.1 - x.1 := (abs_le.mp h1).1
        have h6 : -δr ≤ y.1 - (x.1 - δr) := by linarith
        have h7 : y.1 - (x.1 - δr) ≤ δr := by linarith
        exact abs_le.mpr ⟨h6, h7⟩
      · rw [if_neg h]; have h4 : y.1 - x.1 ≤ 2 * δr := (abs_le.mp h1).2
        have h6 : -δr ≤ y.1 - (x.1 + δr) := by linarith
        have h7 : y.1 - (x.1 + δr) ≤ δr := by linarith
        exact abs_le.mpr ⟨h6, h7⟩
    have h4 : |y.2 - c.2| ≤ δr := by
      have hc2 : c.2 = (if y.2 ≤ x.2 then x.2 - δr else x.2 + δr) := by rfl
      rw [hc2]; by_cases h : y.2 ≤ x.2
      · rw [if_pos h]; have h4 : -(2 * δr) ≤ y.2 - x.2 := (abs_le.mp h2).1
        have h6 : -δr ≤ y.2 - (x.2 - δr) := by linarith
        have h7 : y.2 - (x.2 - δr) ≤ δr := by linarith
        exact abs_le.mpr ⟨h6, h7⟩
      · rw [if_neg h]; have h4 : y.2 - x.2 ≤ 2 * δr := (abs_le.mp h2).2
        have h6 : -δr ≤ y.2 - (x.2 + δr) := by linarith
        have h7 : y.2 - (x.2 + δr) ≤ δr := by linarith
        exact abs_le.mpr ⟨h6, h7⟩
    have h5 : dist y c ≤ δr := by simpa [Prod.dist_eq, max_le_iff] using ⟨h3, h4⟩
    have h6 : edist y c ≤ δ := by
      have h7 : edist y c = ENNReal.ofReal (dist y c) := by exact edist_dist y c
      rw [h7]
      have h8 : ENNReal.ofReal (dist y c) ≤ ENNReal.ofReal δr := ENNReal.ofReal_le_ofReal h5
      have h9 : ENNReal.ofReal δr = ↑δ := by simp [δr]
      rw [h9] at h8; exact h8
    exact ⟨c, hc_in_D, h6⟩
  exact ⟨D, hD_card, h_cover⟩

/-- N_δ(A) ≤ 4 * N_{2δ}(A) on ℝ×ℝ. -/
lemma prod_covering_refine_4 {δ : NNReal} (hδ_pos : 0 < δ) {A : Set (ℝ × ℝ)} :
    (Metric.externalCoveringNumber δ A : ENNReal) ≤
    (4 : ENNReal) * (Metric.externalCoveringNumber (2 * δ) A : ENNReal) :=
  covering_refine_factor (R := 2 * δ) (C := 4) hδ_pos (by positivity) (by norm_num)
    (fun x => prod_ball_cover_4 hδ_pos x)

/-- If every point of V is within distance R of some point in W, then an ε-cover
    of W is an (ε+R)-cover of V. -/
lemma thickening_cover {X : Type*} [PseudoMetricSpace X] {V W : Set X} {ε R : NNReal}
    (h : ∀ v ∈ V, ∃ w ∈ W, dist v w ≤ (R : ℝ))
    {C : Set X} (hC : Metric.IsCover ε W C) :
    Metric.IsCover (ε + R) V C := by
  intro v hv
  rcases h v hv with ⟨w, hw, hdist⟩
  have hCw : ∃ c ∈ C, edist w c ≤ (ε : ENNReal) := by exact Set.inter_nonempty.mp (hC hw)
  rcases hCw with ⟨c, hc, hwc⟩
  have h_edist_vw : edist v w ≤ (R : ENNReal) := by
    have h1 : edist v w = ENNReal.ofReal (dist v w) := by exact edist_dist v w
    rw [h1]
    have h_pos1 : 0 ≤ dist v w := dist_nonneg
    have h_pos2 : 0 ≤ (R : ℝ) := by positivity
    have h_iff : ENNReal.ofReal (dist v w) ≤ ENNReal.ofReal (R : ℝ) ↔ dist v w ≤ (R : ℝ) := by
      simp [h_pos1, h_pos2]
    have h_R_eq : (R : ENNReal) = ENNReal.ofReal (R : ℝ) := by simp
    rw [h_R_eq]
    exact h_iff.mpr hdist
  have h_edist : edist v c ≤ edist v w + edist w c := edist_triangle v w c
  have h_total : edist v c ≤ ((ε + R : NNReal) : ENNReal) := by
    calc edist v c
      ≤ edist v w + edist w c := h_edist
    _ ≤ (R : ENNReal) + (ε : ENNReal) := by gcongr
    _ = ((ε + R : NNReal) : ENNReal) := by
      simp [add_comm] <;> rfl
  exact ⟨c, hc, h_total⟩

/-- External covering number bound under pointwise thickening. -/
lemma externalCoveringNumber_thickening {X : Type*} [PseudoMetricSpace X]
    {V W : Set X} {ε R : NNReal}
    (h : ∀ v ∈ V, ∃ w ∈ W, dist v w ≤ (R : ℝ)) :
    Metric.externalCoveringNumber (ε + R) V ≤ Metric.externalCoveringNumber ε W := by
  apply le_iInf
  intro C
  apply le_iInf
  intro hC
  exact Metric.IsCover.externalCoveringNumber_le_encard (thickening_cover h hC)

/-! ### Shear transfer for IsDeltaSSet on ℝ×ℝ -/

/-- The shear map g_d(p) = (p.1, p.2 + p.1*d). -/
def shearMap (d : ℝ) : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.2 + p.1 * d)

/-- g_d is LipschitzWith constant 2 when |d| ≤ 1. -/
lemma shearMap_lipschitz {d : ℝ} (hd : |d| ≤ 1) :
    LipschitzWith (2 : NNReal) (shearMap d) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  let a : ℝ := p.1 - q.1
  let b : ℝ := p.2 - q.2
  have h1 : dist (shearMap d p) (shearMap d q) = max (|a|) (|b + a * d|) := by
    have h11 : (shearMap d p).1 - (shearMap d q).1 = a := by simp [shearMap] <;> ring
    have h12 : (shearMap d p).2 - (shearMap d q).2 = b + a * d := by simp [shearMap] <;> ring
    have h13 : dist (shearMap d p) (shearMap d q) =
        max (|(shearMap d p).1 - (shearMap d q).1|) (|(shearMap d p).2 - (shearMap d q).2|) := by
      simp [Prod.dist_eq] <;> rfl
    rw [h13, h11, h12]
  rw [h1]
  have h2 : |b + a * d| ≤ |b| + |a| := by
    calc |b + a * d|
      ≤ |b| + |a * d| := by exact DiscretisedFurstenbergEstimate.real_abs_add b (a * d)
    _ = |b| + |a| * |d| := by rw [abs_mul]
    _ ≤ |b| + |a| := by
      have h3 : |a| * |d| ≤ |a| := by
        have h4 : |d| ≤ 1 := hd
        nlinarith [abs_nonneg a]
      linarith
  have hdist : dist p q = max (|a|) (|b|) := by
    have h5 : dist p q = max (|p.1 - q.1|) (|p.2 - q.2|) := by simp [Prod.dist_eq] <;> rfl
    rw [h5] <;> rfl
  rw [hdist]
  have h_pos : 0 ≤ max (|a|) (|b|) := by positivity
  have h5 : |a| ≤ 2 * max (|a|) (|b|) := by
    have h6 : |a| ≤ max (|a|) (|b|) := le_max_left _ _
    linarith
  have h7 : |b + a * d| ≤ 2 * max (|a|) (|b|) := by
    have h8 : |b| ≤ max (|a|) (|b|) := le_max_right _ _
    have h9 : |a| ≤ max (|a|) (|b|) := le_max_left _ _
    calc |b + a * d|
      ≤ |b| + |a| := h2
    _ ≤ max (|a|) (|b|) + max (|a|) (|b|) := by linarith [h8, h9]
    _ = 2 * max (|a|) (|b|) := by ring
  exact max_le h5 h7

/-- g_d^{-1} = g_{-d} is also LipschitzWith constant 2. -/
lemma shearMap_inv_lipschitz {d : ℝ} (hd : |d| ≤ 1) :
    LipschitzWith (2 : NNReal) (shearMap (-d)) := by
  have h2 : |(-d)| ≤ 1 := by simpa [abs_neg] using hd
  exact shearMap_lipschitz h2

/-- Transfer IsDeltaSSet through shear g_d on ℝ×ℝ.
    Constant: 16 * C * 2^s. -/
lemma IsDeltaSSet.shear_transfer {δ s C d : ℝ} {P : Set (ℝ × ℝ)}
    (hδ_pos : 0 < δ) (hs_nonneg : 0 ≤ s) (hd : |d| ≤ 1)
    (h : IsDeltaSSet δ s C P) :
    IsDeltaSSet δ s (16 * C * (2 : ℝ) ^ s) ((shearMap d) '' P) := by
  let g := shearMap d
  let ginv := shearMap (-d)
  let Q : Set (ℝ × ℝ) := g '' P
  have hP_nonempty : P.Nonempty := h.1
  have hQ_nonempty : Q.Nonempty := hP_nonempty.image g
  have hC_pos : 0 < C := h.2.2.1
  let δnn : NNReal := δ.toNNReal
  have hδnn_coe : (δnn : ℝ) = δ := by simp [δnn, Real.toNNReal_of_nonneg hδ_pos.le]
  have hδnn_pos : 0 < δnn := by
    have h : (δnn : ℝ) = δ := hδnn_coe
    exact NNReal.coe_pos.mp (by rw [h]; exact hδ_pos)
  have hg_lip : LipschitzWith (2 : NNReal) g := shearMap_lipschitz hd
  have hginv_lip : LipschitzWith (2 : NNReal) ginv := shearMap_inv_lipschitz hd
  have h_left_inv : ∀ p, ginv (g p) = p := by
    intro p
    have h1 : (ginv (g p)).1 = p.1 := by simp [g, ginv, shearMap] <;> ring
    have h2 : (ginv (g p)).2 = p.2 := by simp [g, ginv, shearMap] <;> ring
    exact Prod.ext h1 h2
  have h_right_inv : ∀ q, g (ginv q) = q := by
    intro q
    have h1 : (g (ginv q)).1 = q.1 := by simp [g, ginv, shearMap] <;> ring
    have h2 : (g (ginv q)).2 = q.2 := by simp [g, ginv, shearMap] <;> ring
    exact Prod.ext h1 h2
  have h_img_inv : ginv '' Q = P := by
    ext θ; simp only [Set.mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨p, hp, hgp⟩
      have h4 : ginv q = p := by rw [←hgp]; exact h_left_inv p
      rw [h4]; exact hp
    · intro hθ
      have h5 : g θ ∈ Q := ⟨θ, hθ, rfl⟩
      exact ⟨g θ, h5, h_left_inv θ⟩
  have h_cover_upper : ∀ (A : Set (ℝ × ℝ)),
      (Metric.externalCoveringNumber δnn (g '' A) : ENNReal) ≤
      (4 : ENNReal) * (Metric.externalCoveringNumber δnn A : ENNReal) := by
    intro A
    have h4 : Metric.externalCoveringNumber ((2 : NNReal) * δnn) (g '' A) ≤
        Metric.externalCoveringNumber δnn A :=
      external_covering_number_lipschitz_image hg_lip
    have h3 : (Metric.externalCoveringNumber δnn (g '' A) : ENNReal) ≤
        (4 : ENNReal) * (Metric.externalCoveringNumber ((2 : NNReal) * δnn) (g '' A) : ENNReal) :=
      prod_covering_refine_4 hδnn_pos
    calc (Metric.externalCoveringNumber δnn (g '' A) : ENNReal)
      ≤ (4 : ENNReal) * (Metric.externalCoveringNumber ((2 : NNReal) * δnn) (g '' A) : ENNReal) := h3
    _ ≤ (4 : ENNReal) * (Metric.externalCoveringNumber δnn A : ENNReal) := by gcongr
  have h_cover_lower : (Metric.externalCoveringNumber δnn P : ENNReal) ≤
      (4 : ENNReal) * (Metric.externalCoveringNumber δnn Q : ENNReal) := by
    have h2 : Metric.externalCoveringNumber ((2 : NNReal) * δnn) (ginv '' Q) ≤
        Metric.externalCoveringNumber δnn Q :=
      external_covering_number_lipschitz_image hginv_lip
    rw [h_img_inv] at h2
    have h3 : (Metric.externalCoveringNumber δnn P : ENNReal) ≤
        (4 : ENNReal) * (Metric.externalCoveringNumber ((2 : NNReal) * δnn) P : ENNReal) :=
      prod_covering_refine_4 hδnn_pos
    calc (Metric.externalCoveringNumber δnn P : ENNReal)
      ≤ (4 : ENNReal) * (Metric.externalCoveringNumber ((2 : NNReal) * δnn) P : ENNReal) := h3
    _ ≤ (4 : ENNReal) * (Metric.externalCoveringNumber δnn Q : ENNReal) := by gcongr
  have h_main : ∀ (y : ℝ × ℝ) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δnn (Q ∩ Metric.closedBall y r) : ENNReal) ≤
        ENNReal.ofReal (16 * C * (2 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δnn Q : ENNReal) := by
    intro y r hr
    let x : ℝ × ℝ := ginv y
    have hgx : g x = y := h_right_inv y
    have hr_pos : 0 < r := by linarith
    have h8 : 0 ≤ r := by linarith
    have h_ball : Q ∩ Metric.closedBall y r ⊆ g '' (P ∩ Metric.closedBall x (2 * r)) := by
      intro q hq
      have hq1 : q ∈ Q := hq.1
      have hq2 : q ∈ Metric.closedBall y r := hq.2
      rcases hq1 with ⟨θ, hθ, rfl⟩
      have h_dist : dist θ x ≤ 2 * r := by
        have h6 : dist (g θ) y ≤ r := by simpa [Metric.mem_closedBall] using hq2
        have h7 : dist θ x ≤ 2 * dist (g θ) y := by
          have h8 := hginv_lip.dist_le_mul (g θ) y
          have h9 : ginv (g θ) = θ := h_left_inv θ
          rw [h9] at h8; exact h8
        exact h7.trans (by gcongr)
      exact ⟨θ, ⟨hθ, by simpa [Metric.mem_closedBall] using h_dist⟩, rfl⟩
    have h1 : (Metric.externalCoveringNumber δnn (Q ∩ Metric.closedBall y r) : ENNReal) ≤
        (Metric.externalCoveringNumber δnn (g '' (P ∩ Metric.closedBall x (2 * r))) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h_ball
    have h2 : (Metric.externalCoveringNumber δnn (g '' (P ∩ Metric.closedBall x (2 * r))) : ENNReal) ≤
        (4 : ENNReal) * (Metric.externalCoveringNumber δnn (P ∩ Metric.closedBall x (2 * r))) :=
      h_cover_upper (P ∩ Metric.closedBall x (2 * r))
    have h4 : δ ≤ 2 * r := by linarith
    have h3 := h.2.2.2.2 x (2 * r) h4
    have h14 : ENNReal.ofReal (r ^ s) = (ENNReal.ofReal r) ^ s := by
      rw [ENNReal.ofReal_rpow_of_nonneg h8 hs_nonneg]
    have h15 : (ENNReal.ofReal (2 * r)) ^ s = ENNReal.ofReal ((2 * r) ^ s) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) hs_nonneg]
    have h9 : (2 * r) ^ s = (2 : ℝ) ^ s * r ^ s := by
      rw [← Real.mul_rpow (by norm_num) h8]
    have h_rpow : ENNReal.ofReal ((2 * r) ^ s) =
        ENNReal.ofReal ((2 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s := by
      rw [h9]
      rw [ENNReal.ofReal_mul (by positivity), h14]
    have h_step1 : (Metric.externalCoveringNumber δnn (Q ∩ Metric.closedBall y r) : ENNReal) ≤
        (4 : ENNReal) * (Metric.externalCoveringNumber δnn (P ∩ Metric.closedBall x (2 * r))) :=
      le_trans h1 h2
    have h_step2 : (Metric.externalCoveringNumber δnn (P ∩ Metric.closedBall x (2 * r)) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (2 * r)) ^ s * (Metric.externalCoveringNumber δnn P) := h3
    have h_step3 : (4 : ENNReal) * (Metric.externalCoveringNumber δnn (P ∩ Metric.closedBall x (2 * r))) ≤
        (4 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal (2 * r)) ^ s *
          (Metric.externalCoveringNumber δnn P)) := by gcongr
    have h_step4 : (4 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal (2 * r)) ^ s *
          (Metric.externalCoveringNumber δnn P)) =
        (4 : ENNReal) * (ENNReal.ofReal C * ENNReal.ofReal ((2 * r) ^ s) *
          (Metric.externalCoveringNumber δnn P)) := by rw [h15]
    have h_step5 : (4 : ENNReal) * (ENNReal.ofReal C * ENNReal.ofReal ((2 * r) ^ s) *
          (Metric.externalCoveringNumber δnn P)) ≤
        (4 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal ((2 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s) *
          (Metric.externalCoveringNumber δnn P)) := by
      gcongr <;> rw [h_rpow]
    have h_step6 : (4 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal ((2 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s) *
          (Metric.externalCoveringNumber δnn P)) ≤
        (4 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal ((2 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s) *
          ((4 : ENNReal) * (Metric.externalCoveringNumber δnn Q))) := by
      let A := (4 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal ((2 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s))
      have h_goal : (4 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal ((2 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s) *
            (Metric.externalCoveringNumber δnn P)) = A * (Metric.externalCoveringNumber δnn P) := by
        simp [A, mul_assoc] <;> ac_rfl
      have h_goal2 : (4 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal ((2 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s) *
            ((4 : ENNReal) * (Metric.externalCoveringNumber δnn Q))) = A * ((4 : ENNReal) * (Metric.externalCoveringNumber δnn Q)) := by
        simp [A, mul_assoc] <;> ac_rfl
      rw [h_goal, h_goal2]
      exact mul_le_mul_left' h_cover_lower A
    have h10 : (4 : ENNReal) * ENNReal.ofReal C * ENNReal.ofReal ((2 : ℝ) ^ s) * (4 : ENNReal) =
        ENNReal.ofReal (16 * C * (2 : ℝ) ^ s) := by
      have h_posC : 0 < C := hC_pos
      have h_pos2 : 0 ≤ (2 : ℝ) ^ s := by positivity
      calc (4 : ENNReal) * ENNReal.ofReal C * ENNReal.ofReal ((2 : ℝ) ^ s) * (4 : ENNReal)
        = ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal C * ENNReal.ofReal ((2 : ℝ) ^ s) * ENNReal.ofReal (4 : ℝ) := by norm_cast
      _ = ENNReal.ofReal ((4 : ℝ) * C * (2 : ℝ) ^ s * (4 : ℝ)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)] <;> rfl
      _ = ENNReal.ofReal (16 * C * (2 : ℝ) ^ s) := by
        have h_eq : (4 : ℝ) * C * (2 : ℝ) ^ s * (4 : ℝ) = 16 * C * (2 : ℝ) ^ s := by ring
        rw [h_eq]
    have h_assoc : (4 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal ((2 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s) *
          ((4 : ENNReal) * (Metric.externalCoveringNumber δnn Q))) =
        ((4 : ENNReal) * ENNReal.ofReal C * ENNReal.ofReal ((2 : ℝ) ^ s) * (4 : ENNReal)) *
          (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δnn Q) := by
      simp only [mul_assoc] <;> ac_rfl
    have h_final : (4 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal ((2 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s) *
          ((4 : ENNReal) * (Metric.externalCoveringNumber δnn Q))) ≤
        ENNReal.ofReal (16 * C * (2 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δnn Q) := by
      rw [h_assoc, h10]
    exact le_trans (le_trans (le_trans (le_trans h_step1 h_step3) (le_of_eq h_step4)) h_step5) (le_trans h_step6 h_final)
  have hC_pos' : 0 < 16 * C * (2 : ℝ) ^ s := by positivity
  exact ⟨hQ_nonempty, hδ_pos, hC_pos', hs_nonneg, h_main⟩

/-- Finite subadditivity of external covering number. -/
lemma external_covering_number_finite_iUnion_le {X : Type*} [PseudoMetricSpace X]
    {ε : NNReal} {ι : Type*} [DecidableEq ι] (I : Finset ι) (A : ι → Set X) :
    Metric.externalCoveringNumber ε (⋃ i ∈ I, A i) ≤
      ∑ i ∈ I, Metric.externalCoveringNumber ε (A i) := by
  exact externalCoveringNumber_biUnion (ε := ε) (s := I) (A := A)

/-- Local finite union of S-sets: union of N sets with constant N*C. -/
lemma local_finite_union {δ s C : ℝ} {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {P : ι → Set ℝ}
    (hP : ∀ i ∈ I, IsDeltaSSet δ s C (P i))
    (hI_nonempty : I.Nonempty) :
    IsDeltaSSet δ s ((I.card : ℝ) * C) (⋃ i ∈ I, P i) := by
  let U : Set ℝ := ⋃ i ∈ I, P i
  have hU_nonempty : U.Nonempty := by
    rcases hI_nonempty with ⟨i, hi⟩
    have hPi_nonempty : (P i).Nonempty := (hP i hi).1
    have h_sub : P i ⊆ U := by
      intro x hx; exact Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩
    exact hPi_nonempty.mono h_sub
  have hδ_pos : 0 < δ := (hP (Classical.choose hI_nonempty) (Classical.choose_spec hI_nonempty)).2.1
  have hC_pos : 0 < C := (hP (Classical.choose hI_nonempty) (Classical.choose_spec hI_nonempty)).2.2.1
  have hs_nonneg : 0 ≤ s := (hP (Classical.choose hI_nonempty) (Classical.choose_spec hI_nonempty)).2.2.2.1
  have h_sum_coe : ∀ (s' : Finset ι) (f : ι → ℕ∞),
      (↑(∑ i ∈ s', f i) : ENNReal) = ∑ i ∈ s', (↑(f i) : ENNReal) := by
    intro s' f
    induction s' using Finset.induction with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [ENat.toENNReal_add, ih]
  have h_main : ∀ (x : ℝ) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (U ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal ((I.card : ℝ) * C) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal U : ENNReal) := by
    intro x r hr
    have h_inter : U ∩ Metric.closedBall x r = ⋃ i ∈ I, (P i ∩ Metric.closedBall x r) := by
      ext y; simp [U, Set.mem_iUnion] <;> tauto
    rw [h_inter]
    let K : ENNReal := ENNReal.ofReal C * (ENNReal.ofReal r) ^ s
    have h_union : Metric.externalCoveringNumber δ.toNNReal (⋃ i ∈ I, (P i ∩ Metric.closedBall x r)) ≤
        ∑ i ∈ I, Metric.externalCoveringNumber δ.toNNReal (P i ∩ Metric.closedBall x r) :=
      externalCoveringNumber_biUnion (ε := δ.toNNReal) (s := I) (A := fun i => P i ∩ Metric.closedBall x r)
    have h1 : (Metric.externalCoveringNumber δ.toNNReal (⋃ i ∈ I, (P i ∩ Metric.closedBall x r)) : ENNReal) ≤
        ∑ i ∈ I, (Metric.externalCoveringNumber δ.toNNReal (P i ∩ Metric.closedBall x r) : ENNReal) := by
      have h_coe : (↑(∑ i ∈ I, Metric.externalCoveringNumber δ.toNNReal (P i ∩ Metric.closedBall x r)) : ENNReal) =
          ∑ i ∈ I, (Metric.externalCoveringNumber δ.toNNReal (P i ∩ Metric.closedBall x r) : ENNReal) :=
        h_sum_coe I _
      have h_mono : ∀ (a b : ℕ∞), a ≤ b → (↑a : ENNReal) ≤ (↑b : ENNReal) := by
        intro a b h
        exact ENat.toENNReal_le.mpr h
      have h1' : (↑(Metric.externalCoveringNumber δ.toNNReal (⋃ i ∈ I, (P i ∩ Metric.closedBall x r))) : ENNReal) ≤
          (↑(∑ i ∈ I, Metric.externalCoveringNumber δ.toNNReal (P i ∩ Metric.closedBall x r)) : ENNReal) :=
        h_mono _ _ h_union
      rw [h_coe] at h1'
      exact h1'
    have h2 : ∀ i ∈ I, (Metric.externalCoveringNumber δ.toNNReal (P i ∩ Metric.closedBall x r) : ENNReal) ≤
        K * (Metric.externalCoveringNumber δ.toNNReal (P i) : ENNReal) := by
      intro i hi
      exact (hP i hi).2.2.2.2 x r hr
    have h3 : ∑ i ∈ I, (Metric.externalCoveringNumber δ.toNNReal (P i ∩ Metric.closedBall x r) : ENNReal) ≤
        ∑ i ∈ I, (K * (Metric.externalCoveringNumber δ.toNNReal (P i) : ENNReal)) := by
      apply Finset.sum_le_sum; intro i hi; exact h2 i hi
    have h4 : ∑ i ∈ I, (K * (Metric.externalCoveringNumber δ.toNNReal (P i) : ENNReal)) =
        K * ∑ i ∈ I, (Metric.externalCoveringNumber δ.toNNReal (P i) : ENNReal) := by
      rw [Finset.mul_sum]
    have h5 : ∀ i ∈ I, (Metric.externalCoveringNumber δ.toNNReal (P i) : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal U : ENNReal) := by
      intro i hi
      have h_sub : P i ⊆ U := by
        intro x hx; exact Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩
      have h : Metric.externalCoveringNumber δ.toNNReal (P i) ≤ Metric.externalCoveringNumber δ.toNNReal U :=
        Metric.externalCoveringNumber_mono_set h_sub
      simpa using h
    have h6 : ∑ i ∈ I, (Metric.externalCoveringNumber δ.toNNReal (P i) : ENNReal) ≤
        ∑ i ∈ I, (Metric.externalCoveringNumber δ.toNNReal U : ENNReal) := by
      apply Finset.sum_le_sum; intro i hi; exact h5 i hi
    have h7 : ∑ i ∈ I, (Metric.externalCoveringNumber δ.toNNReal U : ENNReal) =
        (I.card : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal U : ENNReal) := by
      simpa [Finset.sum_const] using mul_comm (Metric.externalCoveringNumber δ.toNNReal U : ENNReal) (I.card : ENNReal)
    have h8 : ENNReal.ofReal ((I.card : ℝ) * C) = (I.card : ENNReal) * ENNReal.ofReal C := by
      rw [ENNReal.ofReal_mul (by positivity)] <;> norm_cast
    calc (Metric.externalCoveringNumber δ.toNNReal (⋃ i ∈ I, (P i ∩ Metric.closedBall x r)) : ENNReal)
      ≤ ∑ i ∈ I, (Metric.externalCoveringNumber δ.toNNReal (P i ∩ Metric.closedBall x r) : ENNReal) := h1
    _ ≤ ∑ i ∈ I, (K * (Metric.externalCoveringNumber δ.toNNReal (P i) : ENNReal)) := h3
    _ = K * ∑ i ∈ I, (Metric.externalCoveringNumber δ.toNNReal (P i) : ENNReal) := h4
    _ ≤ K * ((I.card : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal U : ENNReal)) := by
      have h9 : ∑ i ∈ I, (Metric.externalCoveringNumber δ.toNNReal (P i) : ENNReal) ≤
          (I.card : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal U : ENNReal) := by
        calc ∑ i ∈ I, (Metric.externalCoveringNumber δ.toNNReal (P i) : ENNReal)
          ≤ ∑ i ∈ I, (Metric.externalCoveringNumber δ.toNNReal U : ENNReal) := h6
        _ = (I.card : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal U : ENNReal) := h7
      exact mul_le_mul_left' h9 K
    _ = ENNReal.ofReal ((I.card : ℝ) * C) * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal U : ENNReal) := by
        rw [h8] <;> ring
  exact ⟨hU_nonempty, hδ_pos, by positivity, hs_nonneg, h_main⟩

/-! ### EuclideanPlane ↔ ℝ×ℝ metric transfer -/

/-- Norm squared of a EuclideanPlane vector equals sum of coordinate squares. -/
private lemma plane_norm_sq (x : EuclideanPlane) : ‖x‖^2 = (x 0)^2 + (x 1)^2 := by
  have h1 : ‖x‖ = Real.sqrt ((x 0)^2 + (x 1)^2) := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> rfl
  rw [h1]
  rw [Real.sq_sqrt] <;> positivity

/-- A 2δ-ball in EuclideanPlane can be covered by at most 25 δ-balls (5×5 grid). -/
lemma plane_ball_cover_25 {δ : NNReal} (hδ_pos : 0 < δ) (x : EuclideanPlane) :
    ∃ (D : Finset EuclideanPlane), D.card ≤ 25 ∧
    Metric.IsCover δ (Metric.closedBall x (2 * (δ : ℝ))) (D : Set EuclideanPlane) := by
  let δr : ℝ := (δ : ℝ)
  let e : EuclideanPlane ≃ (Fin 2 → ℝ) := WithLp.equiv 2 _
  let idx : Finset ℤ := {-2, -1, 0, 1, 2}
  let g : ℤ × ℤ → EuclideanPlane := fun p =>
    e.symm (fun i : Fin 2 => x i + (if i = 0 then (p.1 : ℝ) else (p.2 : ℝ)) * δr)
  let D : Finset EuclideanPlane := Finset.image g (idx ×ˢ idx)
  have h_card : D.card ≤ 25 := by
    have h1 : D.card ≤ (idx ×ˢ idx).card := Finset.card_image_le
    have h2 : (idx ×ˢ idx).card = 25 := by decide
    rw [h2] at h1; exact h1
  have h_round_real : ∀ (z : ℝ), |z| ≤ 2 → ∃ (k : ℤ), k ∈ idx ∧ |z - (k : ℝ)| ≤ 1 / 2 := by
    intro z hz
    have hz1 : -2 ≤ z := (abs_le.mp hz).1
    have hz2 : z ≤ 2 := (abs_le.mp hz).2
    let k : ℤ := Int.floor (z + 1 / 2)
    have h1 : (k : ℝ) ≤ z + 1 / 2 := Int.floor_le (z + 1 / 2)
    have h2 : z + 1 / 2 < (k : ℝ) + 1 := Int.lt_floor_add_one (z + 1 / 2)
    have h_near : |z - (k : ℝ)| ≤ 1 / 2 := by
      have h3 : -(1 / 2 : ℝ) ≤ z - (k : ℝ) := by linarith
      have h4 : z - (k : ℝ) ≤ 1 / 2 := by linarith
      exact abs_le.mpr ⟨h3, h4⟩
    have h_k_ge : (k : ℝ) > -5 / 2 := by linarith
    have h_k_le : (k : ℝ) ≤ 5 / 2 := by linarith
    have h_k_in : k ∈ idx := by
      simp only [idx, Finset.mem_insert, Finset.mem_singleton]
      have h4 : -2 ≤ k := by
        by_contra h5
        have h6 : k ≤ -3 := by omega
        have h7 : (k : ℝ) ≤ -3 := by exact_mod_cast h6
        linarith
      have h5 : k ≤ 2 := by
        by_contra h6
        have h7 : k ≥ 3 := by omega
        have h8 : (k : ℝ) ≥ 3 := by exact_mod_cast h7
        linarith
      omega
    exact ⟨k, h_k_in, h_near⟩
  have h_cover : Metric.IsCover δ (Metric.closedBall x (2 * δr)) D := by
    intro y hy
    have h_norm : ‖y - x‖ ≤ 2 * δr := by simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    have h2 : ‖y - x‖^2 = ((y - x) 0)^2 + ((y - x) 1)^2 := plane_norm_sq (y - x)
    have h_coord : ∀ i : Fin 2, |(y - x) i| ≤ 2 * δr := by
      intro i
      have h_sq : ((y - x) i)^2 ≤ ‖y - x‖^2 := by
        rw [h2]
        fin_cases i
        · have h_pos : 0 ≤ ((y - x) 1)^2 := by positivity
          exact le_add_of_nonneg_right h_pos
        · have h_pos : 0 ≤ ((y - x) 0)^2 := by positivity
          exact le_add_of_nonneg_left h_pos
      have h_abs : |(y - x) i| ≤ ‖y - x‖ := by
        have h5 : 0 ≤ |(y - x) i| := by positivity
        have h6 : 0 ≤ ‖y - x‖ := by positivity
        have h7 : |(y - x) i|^2 ≤ ‖y - x‖^2 := by
          rw [sq_abs] <;> exact h_sq
        have h8 : |(|(y - x) i|)| ≤ |‖y - x‖| := sq_le_sq.mp h7
        simpa [abs_of_nonneg h5, abs_of_nonneg h6] using h8
      have h9 : ‖y - x‖ ≤ 2 * δr := h_norm
      exact h_abs.trans h9
    have h_round : ∀ i : Fin 2, ∃ (k : ℤ), k ∈ idx ∧ |(y - x) i - (k : ℝ) * δr| ≤ δr / 2 := by
      intro i
      let z := (y - x) i / δr
      have hz_bound : |z| ≤ 2 := by
        have h10 : |(y - x) i| ≤ 2 * δr := h_coord i
        have h11 : |z| = |(y - x) i| / δr := by
          dsimp only [z]
          rw [abs_div]
          have h11b : |δr| = δr := abs_of_pos (show 0 < δr by positivity)
          rw [h11b] <;> ring
        rw [h11]
        have h12 : |(y - x) i| / δr ≤ 2 := by
          have h12a : 0 < δr := by positivity
          calc |(y - x) i| / δr ≤ (2 * δr) / δr := by gcongr
            _ = 2 := by field_simp [h12a.ne'] <;> ring
        exact h12
      rcases h_round_real z hz_bound with ⟨k, hk_in, hk_near⟩
      have h_final : |(y - x) i - (k : ℝ) * δr| ≤ δr / 2 := by
        have h14 : (y - x) i = z * δr := by
          dsimp only [z]
          have hδr_ne : δr ≠ 0 := by positivity
          have h : ((y - x) i / δr) * δr = (y - x) i := by
            exact div_mul_cancel₀ ((y - x) i) hδr_ne
          exact h.symm
        calc |(y - x) i - (k : ℝ) * δr|
          = |z * δr - (k : ℝ) * δr| := by rw [h14]
        _ = |(z - (k : ℝ)) * δr| := by ring_nf
        _ = |z - (k : ℝ)| * |δr| := by rw [abs_mul]
        _ = |z - (k : ℝ)| * δr := by rw [abs_of_pos (show 0 < δr by positivity)] <;> ring
        _ ≤ δr * (1 / 2 : ℝ) := by
          have h_nonneg : 0 ≤ δr := by positivity
          have h' : |z - (k : ℝ)| * δr ≤ (1 / 2 : ℝ) * δr := mul_le_mul_of_nonneg_right hk_near h_nonneg
          have h'' : (1 / 2 : ℝ) * δr = δr * (1 / 2 : ℝ) := by ring
          rw [h''] at h'
          exact h'
        _ = δr / 2 := by ring
      exact ⟨k, hk_in, h_final⟩
    choose k hk using h_round
    let p : ℤ × ℤ := (k 0, k 1)
    have hp : p ∈ idx ×ˢ idx := Finset.mem_product.mpr ⟨(hk 0).1, (hk 1).1⟩
    have hg_in_D : g p ∈ D := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have h_coord0 : |(y - g p) 0| ≤ δr / 2 := by
      have h_eq : (y - g p) 0 = (y - x) 0 - (p.1 : ℝ) * δr := by
        simp [g, e] <;> ring
      rw [h_eq]
      exact (hk 0).2
    have h_coord1 : |(y - g p) 1| ≤ δr / 2 := by
      have h_eq : (y - g p) 1 = (y - x) 1 - (p.2 : ℝ) * δr := by
        simp [g, e] <;> ring
      rw [h_eq]
      exact (hk 1).2
    have h_nsq2 : ‖y - g p‖^2 = ((y - g p) 0)^2 + ((y - g p) 1)^2 := plane_norm_sq (y - g p)
    have h_sq0 : ((y - g p) 0)^2 ≤ (δr / 2)^2 := by
      have h_abs : |(y - g p) 0| ≤ δr / 2 := h_coord0
      have h1 : ((y - g p) 0)^2 = |(y - g p) 0|^2 := by rw [sq_abs]
      rw [h1]
      have h_nonneg : 0 ≤ δr / 2 := by positivity
      gcongr
    have h_sq1 : ((y - g p) 1)^2 ≤ (δr / 2)^2 := by
      have h_abs : |(y - g p) 1| ≤ δr / 2 := h_coord1
      have h1 : ((y - g p) 1)^2 = |(y - g p) 1|^2 := by rw [sq_abs]
      rw [h1]
      have h_nonneg : 0 ≤ δr / 2 := by positivity
      gcongr
    have h_dist_sq : ‖y - g p‖^2 ≤ δr^2 := by
      rw [h_nsq2]
      have h_sum : ((y - g p) 0)^2 + ((y - g p) 1)^2 ≤ (δr / 2)^2 + (δr / 2)^2 := by gcongr
      have h_double : (δr / 2)^2 + (δr / 2)^2 = δr^2 / 2 := by ring
      rw [h_double] at h_sum
      have h_half : δr^2 / 2 ≤ δr^2 := by
        have h_nonneg : 0 ≤ δr^2 := by positivity
        exact half_le_self h_nonneg
      exact h_sum.trans h_half
    have h_dist : ‖y - g p‖ ≤ δr := by
      have h1 : Real.sqrt (‖y - g p‖^2) ≤ Real.sqrt (δr^2) := Real.sqrt_le_sqrt h_dist_sq
      have h2 : Real.sqrt (‖y - g p‖^2) = ‖y - g p‖ := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
      have h3 : Real.sqrt (δr^2) = δr := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
      rw [h2, h3] at h1
      exact h1
    have h_edist : edist y (g p) ≤ ↑δ := by
      have h14 : dist y (g p) ≤ δr := by simpa [dist_eq_norm] using h_dist
      have h15 : edist y (g p) = ENNReal.ofReal (dist y (g p)) := by
        simp [edist_dist]
      rw [h15]
      have h16 : ENNReal.ofReal (dist y (g p)) ≤ ENNReal.ofReal δr := ENNReal.ofReal_le_ofReal h14
      have h17 : ENNReal.ofReal δr = ↑δ := by simp [δr]
      rw [h17] at h16; exact h16
    exact ⟨g p, hg_in_D, h_edist⟩
  exact ⟨D, h_card, h_cover⟩

/-- Covering refinement on EuclideanPlane: N_δ(A) ≤ 25 * N_{2δ}(A). -/
lemma plane_covering_refine_25 {δ : NNReal} (hδ_pos : 0 < δ) {A : Set EuclideanPlane} :
    (Metric.externalCoveringNumber δ A : ENNReal) ≤
    (25 : ENNReal) * (Metric.externalCoveringNumber (2 * δ) A : ENNReal) :=
  covering_refine_factor (R := 2 * δ) (C := 25) hδ_pos (by positivity) (by norm_num)
    (fun x => plane_ball_cover_25 hδ_pos x)

/-- `fromPlane'` is 1-Lipschitz: L∞ ≤ L2. -/
lemma fromPlane'_lip : LipschitzWith (1 : NNReal) fromPlane' := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h1 : dist (fromPlane' x) (fromPlane' y) = max (|x 0 - y 0|) (|x 1 - y 1|) := by
    simp [fromPlane', Prod.dist_eq] <;> rfl
  rw [h1]
  have h_sub0 : (x - y) 0 = x 0 - y 0 := by simp
  have h_sub1 : (x - y) 1 = x 1 - y 1 := by simp
  have h2 : ‖x - y‖^2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
    rw [plane_norm_sq (x - y), h_sub0, h_sub1]
  have h41 : (x 0 - y 0)^2 ≤ ‖x - y‖ ^ 2 := by
    rw [h2]
    have h_pos : 0 ≤ (x 1 - y 1)^2 := by positivity
    exact le_add_of_nonneg_right h_pos
  have h42 : (x 1 - y 1)^2 ≤ ‖x - y‖ ^ 2 := by
    rw [h2]
    have h_pos : 0 ≤ (x 0 - y 0)^2 := by positivity
    exact le_add_of_nonneg_left h_pos
  have h4 : |x 0 - y 0| ≤ ‖x - y‖ := by
    have h5 : |x 0 - y 0|^2 = (x 0 - y 0)^2 := by rw [sq_abs]
    nlinarith [norm_nonneg (x - y), h41, h5]
  have h5 : |x 1 - y 1| ≤ ‖x - y‖ := by
    have h6 : |x 1 - y 1|^2 = (x 1 - y 1)^2 := by rw [sq_abs]
    nlinarith [norm_nonneg (x - y), h42, h6]
  have h3 : max (|x 0 - y 0|) (|x 1 - y 1|) ≤ ‖x - y‖ := max_le h4 h5
  simpa [dist_eq_norm] using h3

/-- `toPlane'` is √2-Lipschitz: L2 ≤ √2 * L∞. -/
lemma toPlane'_lip : LipschitzWith (Real.toNNReal (Real.sqrt 2)) toPlane' := by
  let K : NNReal := Real.toNNReal (Real.sqrt 2)
  have hK : (K : ℝ) = Real.sqrt 2 := by
    simp [K, Real.toNNReal_of_nonneg (show 0 ≤ Real.sqrt 2 by positivity)]
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h1 : dist (toPlane' p) (toPlane' q) = ‖toPlane' p - toPlane' q‖ := by rw [dist_eq_norm]
  rw [h1]
  have h_sub0 : (toPlane' p - toPlane' q) 0 = p.1 - q.1 := by simp [toPlane'] <;> aesop
  have h_sub1 : (toPlane' p - toPlane' q) 1 = p.2 - q.2 := by simp [toPlane'] <;> aesop
  have h2 : ‖toPlane' p - toPlane' q‖ ^ 2 = (p.1 - q.1)^2 + (p.2 - q.2)^2 := by
    rw [plane_norm_sq (toPlane' p - toPlane' q), h_sub0, h_sub1]
  have h3 : dist p q = max (|p.1 - q.1|) (|p.2 - q.2|) := by simp [Prod.dist_eq] <;> rfl
  rw [h3]
  let M := max (|p.1 - q.1|) (|p.2 - q.2|)
  have h51 : (p.1 - q.1)^2 ≤ M^2 := by
    have h : |p.1 - q.1| ≤ M := le_max_left _ _
    have h' : (p.1 - q.1)^2 = |p.1 - q.1|^2 := by rw [sq_abs]
    rw [h']; gcongr
  have h52 : (p.2 - q.2)^2 ≤ M^2 := by
    have h : |p.2 - q.2| ≤ M := le_max_right _ _
    have h' : (p.2 - q.2)^2 = |p.2 - q.2|^2 := by rw [sq_abs]
    rw [h']; gcongr
  have h4 : (p.1 - q.1)^2 + (p.2 - q.2)^2 ≤ 2 * M^2 := by linarith
  have h9 : ‖toPlane' p - toPlane' q‖ ≤ Real.sqrt 2 * M := by
    have h10 : 0 ≤ ‖toPlane' p - toPlane' q‖ := by positivity
    have h11 : 0 ≤ Real.sqrt 2 * M := by positivity
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [hK]; exact h9

/-- Transfer IsDeltaSSet from EuclideanPlane (L2) to ℝ×ℝ (L∞).
    Constant: 25 * C * (√2)^s. -/
lemma IsDeltaSSet.euclidean_to_prod' {δ s C : ℝ} {P : Set EuclideanPlane}
    (hδ_pos : 0 < δ) (hs_nonneg : 0 ≤ s)
    (h : IsDeltaSSet δ s C P) :
    IsDeltaSSet δ s (25 * C * (Real.sqrt 2) ^ s) (fromPlane' '' P) := by
  let Q : Set (ℝ × ℝ) := fromPlane' '' P
  let δnn : NNReal := δ.toNNReal
  have hδnn_coe : (δnn : ℝ) = δ := by simp [δnn, Real.toNNReal_of_nonneg hδ_pos.le]
  have hδnn_pos : 0 < δnn := by
    have h : (δnn : ℝ) = δ := hδnn_coe
    exact NNReal.coe_pos.mp (by rw [h]; exact hδ_pos)
  have hC_pos : 0 < C := h.2.2.1
  have hf_lip : LipschitzWith (1 : NNReal) fromPlane' := fromPlane'_lip
  let Ksqrt2 : NNReal := Real.toNNReal (Real.sqrt 2)
  have hKsqrt2 : (Ksqrt2 : ℝ) = Real.sqrt 2 := by
    simp [Ksqrt2, Real.toNNReal_of_nonneg (show 0 ≤ Real.sqrt 2 by positivity)]
  have hg_lip : LipschitzWith Ksqrt2 toPlane' := toPlane'_lip
  have h_left_inv : ∀ p, toPlane' (fromPlane' p) = p := by
    intro p; ext i; fin_cases i <;> simp [toPlane', fromPlane'] <;> aesop
  have h_right_inv : ∀ q, fromPlane' (toPlane' q) = q := by
    intro q; ext <;> simp [toPlane', fromPlane'] <;> aesop
  have h_img_inv : toPlane' '' Q = P := by
    ext θ; simp only [Set.mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨p, hp, hgp⟩
      have h4 : toPlane' q = p := by rw [←hgp]; exact h_left_inv p
      rw [h4]; exact hp
    · intro hθ
      have h5 : fromPlane' θ ∈ Q := ⟨θ, hθ, rfl⟩
      exact ⟨fromPlane' θ, h5, h_left_inv θ⟩
  have h_cover_upper : ∀ (A : Set EuclideanPlane),
      (Metric.externalCoveringNumber δnn (fromPlane' '' A) : ENNReal) ≤
      (Metric.externalCoveringNumber δnn A : ENNReal) := by
    intro A
    have h := _root_.externalCoveringNumber_image_lipschitz (hf := hf_lip) (ε := δnn) (A := A)
    have h_eq : (1 : NNReal) * δnn = δnn := by simp
    rw [h_eq] at h
    exact_mod_cast h
  have h1 : (Metric.externalCoveringNumber δnn P : ENNReal) ≤
      (25 : ENNReal) * (Metric.externalCoveringNumber (2 * δnn) P : ENNReal) :=
    plane_covering_refine_25 hδnn_pos
  have hK_le_2 : Ksqrt2 ≤ (2 : NNReal) := by
    apply NNReal.coe_le_coe.mp
    rw [hKsqrt2]
    have h4 : Real.sqrt 2 ≤ 2 := by
      have h5 : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      have h6 : Real.sqrt 4 = 2 := by rw [Real.sqrt_eq_cases] <;> norm_num
      linarith
    exact h4
  have h3 : Ksqrt2 * δnn ≤ 2 * δnn := by
    calc Ksqrt2 * δnn ≤ (2 : NNReal) * δnn := by gcongr
         _ = 2 * δnn := by ring
  have h2 : (Metric.externalCoveringNumber (2 * δnn) P : ENNReal) ≤
      (Metric.externalCoveringNumber (Ksqrt2 * δnn) P : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_anti h3
  have h4 : (Metric.externalCoveringNumber (Ksqrt2 * δnn) P : ENNReal) ≤
      (Metric.externalCoveringNumber δnn Q : ENNReal) := by
    have h5 : Metric.externalCoveringNumber (Ksqrt2 * δnn) (toPlane' '' Q) ≤
        Metric.externalCoveringNumber δnn Q :=
      _root_.externalCoveringNumber_image_lipschitz (hf := hg_lip) (ε := δnn) (A := Q)
    rw [h_img_inv] at h5
    exact_mod_cast h5
  have h_cover_lower : (Metric.externalCoveringNumber δnn P : ENNReal) ≤
      (25 : ENNReal) * (Metric.externalCoveringNumber δnn Q : ENNReal) := by
    calc (Metric.externalCoveringNumber δnn P : ENNReal)
      ≤ (25 : ENNReal) * (Metric.externalCoveringNumber (2 * δnn) P : ENNReal) := h1
    _ ≤ (25 : ENNReal) * (Metric.externalCoveringNumber (Ksqrt2 * δnn) P : ENNReal) := by gcongr
    _ ≤ (25 : ENNReal) * (Metric.externalCoveringNumber δnn Q : ENNReal) := by gcongr
  have h_const_pos : 0 < 25 * C * (Real.sqrt 2) ^ s := by
    have h1 : 0 < C := hC_pos
    have h2 : 0 < (Real.sqrt 2) ^ s := by positivity
    positivity
  have h_main : ∀ (y : ℝ × ℝ) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δnn (Q ∩ Metric.closedBall y r) : ENNReal) ≤
        ENNReal.ofReal (25 * C * (Real.sqrt 2) ^ s) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δnn Q : ENNReal) := by
    intro y r hr
    let x : EuclideanPlane := toPlane' y
    have h_rnonneg : 0 ≤ r := by linarith
    have h_ball : Q ∩ Metric.closedBall y r ⊆ fromPlane' '' (P ∩ Metric.closedBall x (Real.sqrt 2 * r)) := by
      intro q hq
      have hq1 : q ∈ Q := hq.1
      have hq2 : q ∈ Metric.closedBall y r := hq.2
      rcases hq1 with ⟨θ, hθ, rfl⟩
      have h_dist : dist θ x ≤ Real.sqrt 2 * r := by
        have h6 : dist (fromPlane' θ) y ≤ r := by simpa [Metric.mem_closedBall] using hq2
        have h7 : dist θ x ≤ Real.sqrt 2 * dist (fromPlane' θ) y := by
          have h8 := hg_lip.dist_le_mul (fromPlane' θ) y
          have h9 : toPlane' (fromPlane' θ) = θ := h_left_inv θ
          rw [h9] at h8
          simpa [hKsqrt2] using h8
        have h10 : Real.sqrt 2 * dist (fromPlane' θ) y ≤ Real.sqrt 2 * r := by gcongr
        exact h7.trans h10
      exact ⟨θ, ⟨hθ, by simpa [Metric.mem_closedBall] using h_dist⟩, rfl⟩
    have h_step1 : (Metric.externalCoveringNumber δnn (Q ∩ Metric.closedBall y r) : ENNReal) ≤
        (Metric.externalCoveringNumber δnn (fromPlane' '' (P ∩ Metric.closedBall x (Real.sqrt 2 * r))) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h_ball
    have h_step2 : (Metric.externalCoveringNumber δnn (fromPlane' '' (P ∩ Metric.closedBall x (Real.sqrt 2 * r))) : ENNReal) ≤
        (Metric.externalCoveringNumber δnn (P ∩ Metric.closedBall x (Real.sqrt 2 * r)) : ENNReal) :=
      h_cover_upper (P ∩ Metric.closedBall x (Real.sqrt 2 * r))
    have h4 : δ ≤ Real.sqrt 2 * r := by
      have h5 : (1 : ℝ) ≤ Real.sqrt 2 := by
        have h6 : Real.sqrt 1 ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
        have h7 : Real.sqrt 1 = 1 := by simp
        linarith
      have h8 : r ≥ δ := hr
      nlinarith
    have h5 := h.2.2.2.2 x (Real.sqrt 2 * r) h4
    have h6 : (ENNReal.ofReal (Real.sqrt 2 * r)) ^ s =
        ENNReal.ofReal ((Real.sqrt 2) ^ s) * (ENNReal.ofReal r) ^ s := by
      have h7 : ENNReal.ofReal (Real.sqrt 2 * r) = ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal r := by
        rw [ENNReal.ofReal_mul (by positivity)]
      rw [h7, ENNReal.mul_rpow_of_nonneg _ _ hs_nonneg]
      have h8 : ENNReal.ofReal (Real.sqrt 2) ^ s = ENNReal.ofReal ((Real.sqrt 2) ^ s) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hs_nonneg]
      rw [h8] <;> ring
    have h10 : ENNReal.ofReal (25 * C * (Real.sqrt 2) ^ s) =
        (25 : ENNReal) * ENNReal.ofReal C * ENNReal.ofReal ((Real.sqrt 2) ^ s) := by
      have h11 : 0 ≤ C := by linarith
      have h12 : 0 ≤ (Real.sqrt 2) ^ s := by positivity
      simp [ENNReal.ofReal_mul, h11, h12] <;> ring
    calc (Metric.externalCoveringNumber δnn (Q ∩ Metric.closedBall y r) : ENNReal)
      ≤ (Metric.externalCoveringNumber δnn (P ∩ Metric.closedBall x (Real.sqrt 2 * r)) : ENNReal) :=
        le_trans h_step1 h_step2
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (Real.sqrt 2 * r)) ^ s *
          (Metric.externalCoveringNumber δnn P : ENNReal) := h5
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal ((Real.sqrt 2) ^ s) * (ENNReal.ofReal r) ^ s) *
          ((25 : ENNReal) * (Metric.externalCoveringNumber δnn Q : ENNReal)) := by
      gcongr <;> rw [h6] <;> exact h_cover_lower
    _ = ENNReal.ofReal (25 * C * (Real.sqrt 2) ^ s) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δnn Q : ENNReal) := by
      rw [h10] <;> ring
  have hQ_nonempty : Q.Nonempty := h.1.image fromPlane'
  exact ⟨hQ_nonempty, hδ_pos, h_const_pos, hs_nonneg, h_main⟩

/-! ### Main theorem: A10 product witness with τ = t-s, Y={y_Q}, intercept shear -/

/-- allFineParams: union of all fine tube parameter sets across all squares and points. -/
def allFineParamsEuclidean {Δ δ s t ε : ℝ} (a9 : A9_Output Δ δ s t ε) :
    Set EuclideanPlane :=
  ⋃ (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0),
    ⋃ (p : EuclideanPlane) (hp : p ∈ (a9.perSquare Q hQ).P_norm_Q),
      (fun cell => toPlane' (paramsOfDyadicCell δ cell)) ''
        ((a9.perSquare Q hQ).fineTubes_norm p : Set (DyadicTubeCell δ))

/-- Proof that fineParams z ⊆ allFine. -/
lemma allFineParams_contains {Δ δ s t ε : ℝ} (a9 : A9_Output Δ δ s t ε)
    (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0) (p : EuclideanPlane)
    (hp : p ∈ (a9.perSquare Q hQ).P_norm_Q) :
    ((fun cell => toPlane' (paramsOfDyadicCell δ cell)) ''
      ((a9.perSquare Q hQ).fineTubes_norm p : Set (DyadicTubeCell δ))) ⊆
    allFineParamsEuclidean a9 := by
  intro θ hθ
  rcases hθ with ⟨cell, hcell, rfl⟩
  simp only [allFineParamsEuclidean, Set.mem_iUnion]
  exact ⟨Q, hQ, p, hp, cell, hcell, rfl⟩

noncomputable def A10_product_witness_fixed
    {Δ δ s t ε η_upper : ℝ}
    (a9 : A9_Output Δ δ s t ε)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2)
    (hε_pos : 0 < ε)
    (hη_upper_pos : 0 < η_upper)
    (hη_upper_gt_ε : ε < η_upper)
    (hδ_eq : δ = Δ ^ 2)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hΔ_lt_third : Δ < 1 / 3)
    (hΔ_lt_1_16 : Δ < 1 / 16)
    (hε_le_one : ε ≤ 1)
    (hQ0_nonempty : a9.Q0.Nonempty)
    -- A9 tau must match our tau
    (h_a9_τ : a9.τ = min (t - s) 1)
    -- Y S-set with ε-only constant Δ^{-10000ε}
    (hY_sset_better : IsDeltaSSet Δ (min (t - s) 1) (Real.rpow Δ (-10000 * ε))
        (⋃ (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0), {(a9.perSquare Q hQ).y_Q}))
    -- Shear absorption: 400*(√2)^s*2^s*Δ^{-499ε} ≤ Δ^{-500ε}
    (h_absorb_shear : (400 : ℝ) * (Real.sqrt 2) ^ s * (2 : ℝ) ^ s * Real.rpow Δ (-501 * ε) ≤ Real.rpow Δ (-600 * ε))
    -- Union absorption: 120*Δ^{-528ε} ≤ Δ^{-534ε}
    (h_absorb_union : (120 : ℝ) * Real.rpow Δ (-576 * ε) ≤ Real.rpow Δ (-600 * ε))
    -- Global thickening absorption: 2000*N_δ(allFine) < Δ^{-(2s+η_upper)}
    -- (relaxed exponent; discharged from counter-assumption upstream)
    (h_allFine_upper : (2000 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal (allFineParamsEuclidean a9) <
        ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_upper))))
    -- Fine params rescalable with constant Δ^{-499ε}
    (h_fine_rescalable : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0)
        (p : EuclideanPlane), p ∈ (a9.perSquare Q hQ).P_norm_Q →
        IsRescalableDeltaSet δ Δ s (Real.rpow Δ (-501 * ε))
          ((fun cell => toPlane' (paramsOfDyadicCell δ cell)) ''
            ((a9.perSquare Q hQ).fineTubes_norm p : Set (DyadicTubeCell δ))))
    -- Fine params on ℝ×ℝ rescalable (for coarse shear transfer)
    (h_fine_rescalable_prod : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0)
        (p : EuclideanPlane), p ∈ (a9.perSquare Q hQ).P_norm_Q →
        IsRescalableDeltaSet δ Δ s (Real.rpow Δ (-501 * ε))
          ((fun cell => paramsOfDyadicCell δ cell) ''
            ((a9.perSquare Q hQ).fineTubes_norm p : Set (DyadicTubeCell δ)))) :
    A10_Output Δ s t ε := by
  let τ : ℝ := min (t - s) 1
  have hτ_pos : 0 < τ := by
    have h1 : 0 < t - s := by linarith
    exact lt_min h1 (by norm_num)
  have hτ_le_one : τ ≤ 1 := min_le_right _ _
  have hτ_le_t_sub_s : τ ≤ t - s := min_le_left _ _
  let sqOf := a9.perSquare

  /- Y = {y_Q | Q ∈ Q0} -/
  let Y : Set ℝ :=
    ⋃ (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0), {(sqOf Q hQ).y_Q}

  let QsForY (y : ℝ) : Finset {Q : CoarseSquare Δ // Q ∈ a9.Q0} :=
    (a9.Q0.attach.filter fun Q' => (sqOf Q'.val Q'.property).y_Q = y)

  have hQsForY_card : ∀ (y : ℝ), (QsForY y).card ≤ 120 :=
    fun y => a9.hY_bounded_fiber y

  /- X_y = union over squares with y_Q=y of (Pi_Q_norm + c_Q/Δ) -/
  let X (y : ℝ) (hy : y ∈ Y) : Set ℝ :=
    ⋃ (Q' : {Q : CoarseSquare Δ // Q ∈ a9.Q0}) (hQ : Q' ∈ QsForY y),
      (fun x : ℝ => x + (sqOf Q'.val Q'.property).c_Q / Δ) ''
        (sqOf Q'.val Q'.property).Pi_Q_norm

  let Z : Set (ℝ × ℝ) := ⋃ (y : ℝ) (hy : y ∈ Y), X y hy ×ˢ {y}

  have getZ_data : ∀ (z : ℝ × ℝ) (hz : z ∈ Z),
      ∃ (Q' : {Q : CoarseSquare Δ // Q ∈ a9.Q0}) (x_norm : ℝ),
        x_norm ∈ (sqOf Q'.val Q'.property).Pi_Q_norm ∧
        (sqOf Q'.val Q'.property).y_Q = z.2 ∧
        x_norm + (sqOf Q'.val Q'.property).c_Q / Δ = z.1 := by
    intro z hz
    rcases Set.mem_iUnion₂.mp hz with ⟨y, hy, hz'⟩
    have hzy : z.2 = y := by simpa [Set.mem_singleton_iff] using hz'.2
    have hz1 : z.1 ∈ X y hy := hz'.1
    rcases Set.mem_iUnion₂.mp hz1 with ⟨Q', hQ, hrest⟩
    rcases hrest with ⟨x_norm, hx, h_eq⟩
    have hyQ_eq : (sqOf Q'.val Q'.property).y_Q = y := by
      simp only [QsForY, Finset.mem_filter] at hQ
      exact hQ.2
    exact ⟨Q', x_norm, hx, by rw [hyQ_eq, hzy], h_eq⟩

  let zQ' (z : ℝ × ℝ) (hz : z ∈ Z) : {Q : CoarseSquare Δ // Q ∈ a9.Q0} :=
    Classical.choose (getZ_data z hz)
  let zRest (z : ℝ × ℝ) (hz : z ∈ Z) :=
    Classical.choose_spec (getZ_data z hz)
  let zXnorm (z : ℝ × ℝ) (hz : z ∈ Z) : ℝ :=
    (zRest z hz).choose
  let zSpec (z : ℝ × ℝ) (hz : z ∈ Z) :=
    (zRest z hz).choose_spec

  let zQ (z : ℝ × ℝ) (hz : z ∈ Z) := (zQ' z hz).val
  let zH (z : ℝ × ℝ) (hz : z ∈ Z) := (zQ' z hz).property

  have h_zXnorm_in : ∀ z hz,
      zXnorm z hz ∈ (sqOf (zQ z hz) (zH z hz)).Pi_Q_norm :=
    fun z hz => (zSpec z hz).1
  have h_yQ_eq : ∀ z hz, (sqOf (zQ z hz) (zH z hz)).y_Q = z.2 :=
    fun z hz => (zSpec z hz).2.1
  have h_x_eq : ∀ z hz,
      zXnorm z hz + (sqOf (zQ z hz) (zH z hz)).c_Q / Δ = z.1 :=
    fun z hz => (zSpec z hz).2.2

  /- For each z, compute x_orig, p_wit, and shear offset d = p_wit 1 - y_Q -/
  let x_orig (z : ℝ × ℝ) (hz : z ∈ Z) : ℝ :=
    Δ * zXnorm z hz + (sqOf (zQ z hz) (zH z hz)).c_Q
  let p_wit (z : ℝ × ℝ) (hz : z ∈ Z) : EuclideanPlane :=
    (sqOf (zQ z hz) (zH z hz)).witness (x_orig z hz)
  let d_shear (z : ℝ × ℝ) (hz : z ∈ Z) : ℝ :=
    (p_wit z hz) 1 - (sqOf (zQ z hz) (zH z hz)).y_Q

  have h_d_bound : ∀ z hz, |d_shear z hz| ≤ 3 * Δ := by
    intro z hz
    let sq := sqOf (zQ z hz) (zH z hz)
    have hx : x_orig z hz ∈ sq.Pi_Q := by
      have h1 : zXnorm z hz ∈ sq.Pi_Q_norm := h_zXnorm_in z hz
      rw [sq.hPi_Q_rel]
      exact Set.mem_image_of_mem _ h1
    exact sq.h_witness_y_close (x_orig z hz) hx

  have h_d_le_one : ∀ z hz, |d_shear z hz| ≤ 1 := by
    intro z hz
    have h1 : |d_shear z hz| ≤ 3 * Δ := h_d_bound z hz
    have h2 : 3 * Δ < 1 := by linarith [hΔ_lt_third]
    linarith

  /- fineParams at each z (EuclideanPlane), ORIGINAL (no shear) -/
  let fineParams (z : EuclideanPlane) : Set EuclideanPlane :=
    let z' : ℝ × ℝ := (z 0, z 1)
    if hz : z' ∈ Z then
      let sq := sqOf (zQ z' hz) (zH z' hz)
      let pw := p_wit z' hz
      (fun cell => toPlane' (paramsOfDyadicCell δ cell)) ''
        (sq.fineTubes_norm pw : Set (DyadicTubeCell δ))
    else ∅

  let allFine : Set EuclideanPlane := allFineParamsEuclidean a9

  let X0 : ℝ → Set ℝ := fun y => if hy : y ∈ Y then X y hy else ∅
  let S : Set EuclideanPlane := productIncidenceSet Y X0

  have hZ_to_S : ∀ (z : ℝ × ℝ), z ∈ Z → toPlane' z ∈ S := by
    intro z hz
    rcases Set.mem_iUnion₂.mp hz with ⟨y, hy, hz'⟩
    have hzy : z.2 = y := by simpa [Set.mem_singleton_iff] using hz'.2
    have hz1 : z.1 ∈ X y hy := hz'.1
    have hX0 : X0 y = X y hy := by simp [X0, hy]
    simp only [S, productIncidenceSet, Set.mem_iUnion]
    refine ⟨y, hy, ?_⟩
    simp only [Set.mem_setOf_eq]
    constructor
    · have h_eq : (toPlane' z) 0 = z.1 := by simp [toPlane']
      rw [h_eq, hX0]; exact hz1
    · have h_eq2 : (toPlane' z) 1 = z.2 := by simp [toPlane']
      rw [h_eq2, hzy]

  /- Apply product_structure_rescaling with K_resid = 27 -/
  let h_resc := product_structure_rescaling s hs hs1
  let A : ℝ := Classical.choose h_resc
  have hA_eq : A = 1 := (Classical.choose_spec h_resc).1
  have h_main_resc := (Classical.choose_spec h_resc).2 (Δ := Δ) (δ := δ) (C := Real.rpow Δ (-501 * ε)) (K_resid := 27)

  have h_fine_main : ∀ (z : EuclideanPlane), z ∈ S →
      fineParams z ⊆ allFine ∧
      fineParams z ⊆ parameterGrid δ ∧
      IsRescalableDeltaSet δ Δ s (Real.rpow Δ (-501 * ε)) (fineParams z) ∧
      ∀ θ ∈ fineParams z, lineResidual (unscaleHorizontal Δ z) θ ≤ 27 * δ := by
    intro z hz
    let z' := fromPlane' z
    have hz' : z' ∈ Z := by
      have hz2 : z 0 ∈ X0 (z 1) ∧ z 1 ∈ Y := by
        simpa [S, productIncidenceSet, Set.mem_iUnion, Set.mem_setOf_eq] using hz
      have hz3 : z 1 ∈ Y := hz2.2
      have hz4 : z 0 ∈ X0 (z 1) := hz2.1
      have hX0 : X0 (z 1) = X (z 1) hz3 := by simp [X0, hz3]
      rw [hX0] at hz4
      simp only [Z, Set.mem_iUnion₂]
      exact ⟨z 1, hz3, hz4, rfl⟩
    let sq := sqOf (zQ z' hz') (zH z' hz')
    let pw := p_wit z' hz'
    let d := d_shear z' hz'
    have hx_orig : x_orig z' hz' ∈ sq.Pi_Q := by
      have h1 : zXnorm z' hz' ∈ sq.Pi_Q_norm := h_zXnorm_in z' hz'
      rw [sq.hPi_Q_rel]
      exact Set.mem_image_of_mem _ h1
    have hp_wit : pw ∈ sq.P_norm_Q := (sq.h_witness (x_orig z' hz') hx_orig).1
    have h_pwit0 : pw 0 = x_orig z' hz' := (sq.h_witness (x_orig z' hz') hx_orig).2
    have h_yQ : sq.y_Q = z'.2 := h_yQ_eq z' hz'
    have h_xorig : x_orig z' hz' = Δ * z'.1 := by
      have h : zXnorm z' hz' + sq.c_Q / Δ = z'.1 := h_x_eq z' hz'
      field_simp [hΔ_pos.ne'] at h ⊢ <;> linarith
    have h_d : d = pw 1 - sq.y_Q := by rfl

    have hz'' : fromPlane' z ∈ Z := by simpa [z'] using hz'
    have hz''' : (z 0, z 1) ∈ Z := by
      have h_eq : (z 0, z 1) = fromPlane' z := by simp [fromPlane'] <;> rfl
      rw [h_eq]; exact hz''
    have h1 : fineParams z = (fun cell => toPlane' (paramsOfDyadicCell δ cell)) ''
        (sq.fineTubes_norm pw : Set (DyadicTubeCell δ)) := by
      unfold fineParams
      rw [dif_pos hz'''] <;> rfl

    have h_part1 : fineParams z ⊆ allFine := by
      rw [h1]
      exact allFineParams_contains a9 (zQ z' hz') (zH z' hz') pw hp_wit

    have h_part2 : fineParams z ⊆ parameterGrid δ := by
      rw [h1]
      intro θ hθ
      rcases hθ with ⟨cell, _, rfl⟩
      have h_a : (toPlane' (paramsOfDyadicCell δ cell)) 0 ∈ integerGrid δ := by
        simp [toPlane', integerGrid, paramsOfDyadicCell] <;> exact ⟨cell.1, by ring⟩
      have h_b : (toPlane' (paramsOfDyadicCell δ cell)) 1 ∈ integerGrid δ := by
        simp [toPlane', integerGrid, paramsOfDyadicCell] <;> exact ⟨cell.2, by ring⟩
      exact ⟨h_a, h_b⟩

    have h_part3 : IsRescalableDeltaSet δ Δ s (Real.rpow Δ (-501 * ε)) (fineParams z) := by
      rw [h1]
      exact h_fine_rescalable (zQ z' hz') (zH z' hz') pw hp_wit

    have h_part4 : ∀ θ ∈ fineParams z, lineResidual (unscaleHorizontal Δ z) θ ≤ 27 * δ := by
      rw [h1]
      intro θ hθ
      rcases hθ with ⟨cell, hcell, hθ_eq⟩
      have h_res : |(x_orig z' hz') - tubeSlope (sq.fineTubeOfCell pw cell) * (pw 1) -
          tubeIntercept (sq.fineTubeOfCell pw cell)| ≤ 6 * δ :=
        sq.h_residual (x_orig z' hz') hx_orig cell hcell
      have h_params := sq.hfineTube_params pw hp_wit cell hcell
      have h_slope_bound : |tubeSlope (sq.fineTubeOfCell pw cell)| ≤ 7 * Δ := by
        have h := sq.hfine_cell_bounds pw hp_wit cell hcell
        simpa [h_params] using h.1
      have h_z1 : (unscaleHorizontal Δ z) 0 = Δ * z'.1 := by
        have h_eq1 : (unscaleHorizontal Δ z) 0 = Δ * (z 0) := by
          simp [unscaleHorizontal] <;> ring
        have h_eq2 : z 0 = z'.1 := by simp [z', fromPlane']
        rw [h_eq1, h_eq2]
      have h_z2 : (unscaleHorizontal Δ z) 1 = z'.2 := by
        have h_eq1 : (unscaleHorizontal Δ z) 1 = z 1 := by simp [unscaleHorizontal]
        have h_eq2 : z 1 = z'.2 := by simp [z', fromPlane']
        rw [h_eq1, h_eq2]
      have h_goal : lineResidual (unscaleHorizontal Δ z) θ =
          |(x_orig z' hz') - tubeSlope (sq.fineTubeOfCell pw cell) * (sq.y_Q) -
            tubeIntercept (sq.fineTubeOfCell pw cell)| := by
        have hθ_eq2 : θ = toPlane' (paramsOfDyadicCell δ cell) := hθ_eq.symm
        rw [hθ_eq2]
        simp only [lineResidual]
        have h_expr : (unscaleHorizontal Δ z) 0 -
            ((toPlane' (paramsOfDyadicCell δ cell)) 0 * (unscaleHorizontal Δ z) 1 +
             (toPlane' (paramsOfDyadicCell δ cell)) 1) =
            (x_orig z' hz') - tubeSlope (sq.fineTubeOfCell pw cell) * (sq.y_Q) -
              tubeIntercept (sq.fineTubeOfCell pw cell) := by
          rw [h_z1, h_z2]
          have h3 : (toPlane' (paramsOfDyadicCell δ cell)) 0 = tubeSlope (sq.fineTubeOfCell pw cell) := by
            simp [h_params, toPlane']
          have h4 : (toPlane' (paramsOfDyadicCell δ cell)) 1 = tubeIntercept (sq.fineTubeOfCell pw cell) := by
            simp [h_params, toPlane']
          rw [h3, h4, h_xorig, h_yQ] <;> ring
        rw [h_expr]
      rw [h_goal]
      have h5 : |(x_orig z' hz') - tubeSlope (sq.fineTubeOfCell pw cell) * (sq.y_Q) -
            tubeIntercept (sq.fineTubeOfCell pw cell)| ≤
          |(x_orig z' hz') - tubeSlope (sq.fineTubeOfCell pw cell) * (pw 1) -
            tubeIntercept (sq.fineTubeOfCell pw cell)| +
          |tubeSlope (sq.fineTubeOfCell pw cell)| * |pw 1 - sq.y_Q| := by
        have h6 : (x_orig z' hz') - tubeSlope (sq.fineTubeOfCell pw cell) * (sq.y_Q) -
              tubeIntercept (sq.fineTubeOfCell pw cell) =
            ((x_orig z' hz') - tubeSlope (sq.fineTubeOfCell pw cell) * (pw 1) -
              tubeIntercept (sq.fineTubeOfCell pw cell)) +
            tubeSlope (sq.fineTubeOfCell pw cell) * (pw 1 - sq.y_Q) := by ring
        rw [h6]
        have h_tri : |((x_orig z' hz') - tubeSlope (sq.fineTubeOfCell pw cell) * (pw 1) -
            tubeIntercept (sq.fineTubeOfCell pw cell)) +
            tubeSlope (sq.fineTubeOfCell pw cell) * (pw 1 - sq.y_Q)| ≤
          |(x_orig z' hz') - tubeSlope (sq.fineTubeOfCell pw cell) * (pw 1) -
            tubeIntercept (sq.fineTubeOfCell pw cell)| +
          |tubeSlope (sq.fineTubeOfCell pw cell) * (pw 1 - sq.y_Q)| := by
          have h_abs_add : ∀ (a b : ℝ), |a + b| ≤ |a| + |b| := by
            intro a b
            have h1 : a + b ≤ |a| + |b| := by linarith [le_abs_self a, le_abs_self b]
            have h2 : -(a + b) ≤ |a| + |b| := by
              have h2a : -a ≤ |a| := by simpa [abs_neg] using le_abs_self (-a)
              have h2b : -b ≤ |b| := by simpa [abs_neg] using le_abs_self (-b)
              linarith
            rw [abs_le]
            constructor <;> linarith
          exact h_abs_add _ _
        have h_mul : |tubeSlope (sq.fineTubeOfCell pw cell) * (pw 1 - sq.y_Q)| =
            |tubeSlope (sq.fineTubeOfCell pw cell)| * |pw 1 - sq.y_Q| := by
          rw [abs_mul]
        rw [h_mul] at h_tri
        exact h_tri
      have h7 : |pw 1 - sq.y_Q| ≤ 3 * Δ := h_d_bound z' hz'
      have h8 : |tubeSlope (sq.fineTubeOfCell pw cell)| * |pw 1 - sq.y_Q| ≤ (7 * Δ) * (3 * Δ) :=
        mul_le_mul h_slope_bound h7 (by positivity) (by positivity)
      linarith [h_res, h8]

    exact ⟨h_part1, h_part2, h_part3, h_part4⟩

  /- Define coarseParams via product_structure_rescaling -/
  let coarseParams : EuclideanPlane → Set EuclideanPlane :=
    fun z => scaleParameters Δ (fineParams z)
  let c : ℝ := Δ⁻¹
  have hc : 0 < c := by positivity

  have hC_one : 1 ≤ Real.rpow Δ (-501 * ε) := by
    have h1 : 0 < 501 * ε := by positivity
    have h2 : Real.rpow Δ (501 * ε) < 1 := Real.rpow_lt_one (by linarith) (by linarith) h1
    have h3 : Real.rpow Δ (-501 * ε) = (Real.rpow Δ (501 * ε))⁻¹ := by
      have h4 : (-501 * ε) = -(501 * ε) := by ring
      rw [h4]
      exact Real.rpow_neg hΔ_pos.le (y := (501 * ε))
    rw [h3]
    exact one_le_inv₀ (Real.rpow_pos_of_pos hΔ_pos _) |>.mpr h2.le

  let h_main_resc_applied := h_main_resc Y X0 fineParams allFine hΔ_pos (by linarith) hδ_eq hC_one (by positivity)
      (fun z hz => let ⟨a,b,c,d⟩ := h_fine_main z hz; ⟨a,b,c,d⟩)
  let coarseP : EuclideanPlane → Set EuclideanPlane := Classical.choose h_main_resc_applied
  let h_coarseP := Classical.choose_spec h_main_resc_applied

  have h_pointwise : ∀ z ∈ S,
      coarseParams z = scaleParameters Δ (fineParams z) ∧
      coarseParams z ⊆ parameterGrid Δ ∧
      IsDeltaSSet Δ s (Real.rpow Δ (-501 * ε)) (coarseParams z) ∧
      ∀ θ ∈ coarseParams z, lineResidual z θ ≤ 27 * Δ := by
    intro z hz
    have h2 := h_coarseP.1 z hz
    rcases h2 with ⟨h_eqP, h_grid, h_sset, h_resid⟩
    have h_eq : coarseP z = coarseParams z := by
      simpa [coarseParams] using h_eqP
    have h1 : coarseParams z = scaleParameters Δ (fineParams z) := by rfl
    have h3 : coarseParams z ⊆ parameterGrid Δ := by
      rw [← h_eq]; exact h_grid
    have h4 : IsDeltaSSet Δ s (Real.rpow Δ (-501 * ε)) (coarseParams z) := by
      have h_le : A * Real.rpow Δ (-501 * ε) ≤ Real.rpow Δ (-501 * ε) := by
        rw [hA_eq] <;> simp
      have h_sset' : IsDeltaSSet Δ s (Real.rpow Δ (-501 * ε)) (coarseP z) :=
        IsDeltaSSet.mono_const' h_sset h_le
      have h_eq' : coarseP z = coarseParams z := h_eq
      exact h_eq' ▸ h_sset'
    have h5 : ∀ θ ∈ coarseParams z, lineResidual z θ ≤ 27 * Δ := by
      rw [← h_eq]; exact h_resid
    exact ⟨h1, h3, h4, h5⟩

  have h_global_bound : Metric.externalCoveringNumber Δ.toNNReal
      (⋃ (z : EuclideanPlane) (hz : z ∈ S), coarseParams z) ≤
      Metric.externalCoveringNumber δ.toNNReal allFine := by
    have h_eq : (⋃ (z : EuclideanPlane) (hz : z ∈ S), coarseParams z) =
        (⋃ (z : EuclideanPlane) (hz : z ∈ S), coarseP z) := by
      apply Set.ext; intro x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨z, hz, hx⟩
        have h2 := h_coarseP.1 z hz
        rcases h2 with ⟨h_eqP, _, _, _⟩
        have h_eq2 : coarseParams z = coarseP z := by
          simpa [coarseParams] using h_eqP.symm
        rw [h_eq2] at hx
        exact ⟨z, hz, hx⟩
      · rintro ⟨z, hz, hx⟩
        have h2 := h_coarseP.1 z hz
        rcases h2 with ⟨h_eqP, _, _, _⟩
        have h_eq2 : coarseP z = coarseParams z := by
          simpa [coarseParams] using h_eqP
        rw [h_eq2] at hx
        exact ⟨z, hz, hx⟩
    rw [h_eq]
    have h_bound : _ := h_coarseP.2
    have hA_one : ENNReal.ofReal A = 1 := by
      rw [hA_eq] <;> simp
    have h' : (Metric.externalCoveringNumber Δ.toNNReal (⋃ z ∈ S, coarseP z) : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal allFine : ENNReal) := by
      have h9 : ENNReal.ofReal A * (Metric.externalCoveringNumber δ.toNNReal allFine : ENNReal) =
          (Metric.externalCoveringNumber δ.toNNReal allFine : ENNReal) := by
        rw [hA_one] <;> simp
      have h10 : (Metric.externalCoveringNumber Δ.toNNReal (⋃ z ∈ S, coarseP z) : ENNReal) ≤
          ENNReal.ofReal A * (Metric.externalCoveringNumber δ.toNNReal allFine : ENNReal) := by
        have h11 : (Metric.externalCoveringNumber Δ.toNNReal (⋃ z ∈ S, coarseP z) : ENNReal) ≤
            ENNReal.ofReal (Classical.choose h_resc) * (Metric.externalCoveringNumber δ.toNNReal allFine : ENNReal) := by
          exact h_bound
        simpa [A] using h11
      rw [h9] at h10
      exact h10
    exact_mod_cast h'

  /- Define T_coarse as sheared coarseParams on ℝ×ℝ -/
  let T_coarse (z : ℝ × ℝ) (hz : z ∈ Z) : Set (ℝ × ℝ) :=
    let zE := toPlane' z
    let d := d_shear z hz
    (shearMap d) '' (fromPlane' '' (coarseParams zE))

  /- hT_bounds -/
  have hΔ_lt_1_16 : Δ < 1 / 16 := hΔ_lt_1_16
  have hT_bounds : ∀ z hz, T_coarse z hz ⊆ Set.Icc (-10 : ℝ) 10 ×ˢ Set.Icc (-10 : ℝ) 10 := by
    intro z hz p hp
    rcases hp with ⟨q, hq, rfl⟩
    rcases hq with ⟨θE, hθE, rfl⟩
    let zE := toPlane' z
    let d := d_shear z hz
    let sq := sqOf (zQ z hz) (zH z hz)
    let pw := p_wit z hz
    have hzE_in_S : zE ∈ S := hZ_to_S z hz
    have h_coarse_eq : coarseParams zE = scaleParameters Δ (fineParams zE) :=
      (h_pointwise zE hzE_in_S).1
    rw [h_coarse_eq] at hθE
    rcases hθE with ⟨cell, hcell, hθE_eq⟩
    have hθE_eq' : θE = Δ⁻¹ • cell := by simpa [scaleParameters] using hθE_eq.symm
    have hz''' : (zE 0, zE 1) ∈ Z := by
      have h_eq : (zE 0, zE 1) = z := by simp [zE, toPlane'] <;> aesop
      rw [h_eq]; exact hz
    have h1 : fineParams zE = (fun tubeCell => toPlane' (paramsOfDyadicCell δ tubeCell)) ''
        (sq.fineTubes_norm pw : Set (DyadicTubeCell δ)) := by
      unfold fineParams
      rw [dif_pos hz'''] <;> rfl
    rw [h1] at hcell
    rcases hcell with ⟨tubeCell, htubeCell, hcell_eq⟩
    have hcell_eq' : cell = toPlane' (paramsOfDyadicCell δ tubeCell) := by simpa using hcell_eq.symm
    have hx_orig : x_orig z hz ∈ sq.Pi_Q := by
      have h2 : zXnorm z hz ∈ sq.Pi_Q_norm := h_zXnorm_in z hz
      rw [sq.hPi_Q_rel]
      exact Set.mem_image_of_mem _ h2
    have hp_wit : pw ∈ sq.P_norm_Q := (sq.h_witness (x_orig z hz) hx_orig).1
    have h_bounds := sq.hfine_cell_bounds pw hp_wit tubeCell htubeCell
    have hcell0 : |cell 0| ≤ 7 * Δ := by
      rw [hcell_eq']; simpa [toPlane'] using h_bounds.1
    have hcell1 : |cell 1| ≤ 7 * Δ := by
      rw [hcell_eq']; simpa [toPlane'] using h_bounds.2
    have hθE0 : |θE 0| ≤ 7 := by
      have h_eq : θE 0 = Δ⁻¹ * cell 0 := by
        rw [hθE_eq']; simp [smul_eq_mul]
      rw [h_eq]
      have h_abs : |Δ⁻¹ * cell 0| = Δ⁻¹ * |cell 0| := by
        rw [abs_mul, abs_of_pos (show (0 : ℝ) < Δ⁻¹ by positivity)]
      rw [h_abs]
      calc Δ⁻¹ * |cell 0|
        ≤ Δ⁻¹ * (7 * Δ) := by gcongr
      _ = 7 := by field_simp [hΔ_pos.ne'] <;> ring
    have hθE1 : |θE 1| ≤ 7 := by
      have h_eq : θE 1 = Δ⁻¹ * cell 1 := by
        rw [hθE_eq']; simp [smul_eq_mul]
      rw [h_eq]
      have h_abs : |Δ⁻¹ * cell 1| = Δ⁻¹ * |cell 1| := by
        rw [abs_mul, abs_of_pos (show (0 : ℝ) < Δ⁻¹ by positivity)]
      rw [h_abs]
      calc Δ⁻¹ * |cell 1|
        ≤ Δ⁻¹ * (7 * Δ) := by gcongr
      _ = 7 := by field_simp [hΔ_pos.ne'] <;> ring
    have hd_bound : |d| ≤ 3 * Δ := h_d_bound z hz
    let θ := fromPlane' θE
    have hθ1 : θ.1 = θE 0 := by simp [θ, fromPlane']
    have hθ2 : θ.2 = θE 1 := by simp [θ, fromPlane']
    have hp1 : |(shearMap d θ).1| ≤ 10 := by
      have h : (shearMap d θ).1 = θ.1 := by simp [shearMap]
      rw [h, hθ1]
      linarith [hθE0]
    have hp2 : |(shearMap d θ).2| ≤ 10 := by
      have h : (shearMap d θ).2 = θ.2 + θ.1 * d := by simp [shearMap]
      rw [h, hθ2, hθ1]
      calc |θE 1 + θE 0 * d|
          ≤ |θE 1| + |θE 0 * d| := by
            have h_abs_add : ∀ (a b : ℝ), |a + b| ≤ |a| + |b| := by
              intro a b
              have h1 : a + b ≤ |a| + |b| := by linarith [le_abs_self a, le_abs_self b]
              have h2 : -(a + b) ≤ |a| + |b| := by
                have h2a : -a ≤ |a| := by simpa [abs_neg] using le_abs_self (-a)
                have h2b : -b ≤ |b| := by simpa [abs_neg] using le_abs_self (-b)
                linarith
              rw [abs_le]
              constructor <;> linarith
            exact h_abs_add _ _
        _ = |θE 1| + |θE 0| * |d| := by rw [abs_mul]
        _ ≤ 7 + 7 * (3 * Δ) := by gcongr <;> linarith
        _ = 7 + 21 * Δ := by ring
        _ ≤ 10 := by linarith [hΔ_lt_1_16]
    have h_p1_bounds : -10 ≤ (shearMap d θ).1 ∧ (shearMap d θ).1 ≤ 10 := by
      have h : |(shearMap d θ).1| ≤ 10 := hp1
      exact abs_le.mp h
    have h_p2_bounds : -10 ≤ (shearMap d θ).2 ∧ (shearMap d θ).2 ≤ 10 := by
      have h : |(shearMap d θ).2| ≤ 10 := hp2
      exact abs_le.mp h
    exact ⟨h_p1_bounds, h_p2_bounds⟩

  /- hT_sset via shear transfer -/
  have hT_sset : ∀ z hz, IsDeltaSSet Δ s (Real.rpow Δ (-600 * ε)) (T_coarse z hz) := by
    intro z hz
    let zE := toPlane' z
    let d := d_shear z hz
    have hd_le_one : |d| ≤ 1 := h_d_le_one z hz
    have h_coarse_sset : IsDeltaSSet Δ s (Real.rpow Δ (-501 * ε)) (coarseParams zE) :=
      (h_pointwise zE (hZ_to_S z hz)).2.2.1
    -- Transfer from EuclideanPlane (L2) to ℝ×ℝ (L∞): constant 25*(√2)^s
    have h_prod_sset : IsDeltaSSet Δ s
        (25 * Real.rpow Δ (-501 * ε) * (Real.sqrt 2) ^ s)
        (fromPlane' '' coarseParams zE) :=
      IsDeltaSSet.euclidean_to_prod' (h := h_coarse_sset) hΔ_pos (by linarith)
    -- Shear transfer: constant 16 * C * 2^s
    have h_sheared : IsDeltaSSet Δ s
        (16 * (25 * Real.rpow Δ (-501 * ε) * (Real.sqrt 2) ^ s) * (2 : ℝ) ^ s)
        (shearMap d '' (fromPlane' '' coarseParams zE)) :=
      IsDeltaSSet.shear_transfer (show 0 < Δ from hΔ_pos) (by linarith) hd_le_one h_prod_sset
    -- Weaken constant to Δ^{-500ε}
    have h_const : 16 * (25 * Real.rpow Δ (-501 * ε) * (Real.sqrt 2) ^ s) * (2 : ℝ) ^ s ≤
        Real.rpow Δ (-600 * ε) := by
      have h_eq : 16 * (25 * Real.rpow Δ (-501 * ε) * (Real.sqrt 2) ^ s) * (2 : ℝ) ^ s =
          (400 : ℝ) * (Real.sqrt 2) ^ s * (2 : ℝ) ^ s * Real.rpow Δ (-501 * ε) := by ring
      rw [h_eq]
      exact h_absorb_shear
    exact IsDeltaSSet.mono_const' h_sheared h_const

  /- h_inc: shear cancels y-mismatch, residual ≤ 6Δ (weakened to 27Δ for interface) -/
  have h_inc : ∀ z hz, ∀ p ∈ T_coarse z hz,
      |p.1 * z.2 + p.2 - z.1| ≤ 27 * Δ := by
    intro z hz p hp
    rcases hp with ⟨q, hq, rfl⟩
    rcases hq with ⟨θE, hθE, rfl⟩
    let zE := toPlane' z
    let d := d_shear z hz
    let sq := sqOf (zQ z hz) (zH z hz)
    let pw := p_wit z hz
    have hzE_in_S : zE ∈ S := hZ_to_S z hz
    have h_coarse_eq : coarseParams zE = scaleParameters Δ (fineParams zE) :=
      (h_pointwise zE hzE_in_S).1
    rw [h_coarse_eq] at hθE
    rcases hθE with ⟨cell, hcell, hθE_eq⟩
    have hθE_eq' : θE = Δ⁻¹ • cell := by simpa [scaleParameters] using hθE_eq.symm
    have hθE0 : θE 0 = cell 0 / Δ := by
      rw [hθE_eq']; simp [smul_eq_mul] <;> field_simp [hΔ_pos.ne'] <;> ring
    have hθE1 : θE 1 = cell 1 / Δ := by
      rw [hθE_eq']; simp [smul_eq_mul] <;> field_simp [hΔ_pos.ne'] <;> ring
    have hz''' : (zE 0, zE 1) ∈ Z := by
      have h_eq : (zE 0, zE 1) = z := by
        simp [zE, toPlane'] <;> aesop
      rw [h_eq]; exact hz
    have h1 : fineParams zE = (fun tubeCell => toPlane' (paramsOfDyadicCell δ tubeCell)) ''
        (sq.fineTubes_norm pw : Set (DyadicTubeCell δ)) := by
      unfold fineParams
      rw [dif_pos hz'''] <;> rfl
    rw [h1] at hcell
    rcases hcell with ⟨tubeCell, htubeCell, hcell_eq⟩
    have hcell_eq' : cell = toPlane' (paramsOfDyadicCell δ tubeCell) := by simpa using hcell_eq.symm
    have hx_orig : x_orig z hz ∈ sq.Pi_Q := by
      have h2 : zXnorm z hz ∈ sq.Pi_Q_norm := h_zXnorm_in z hz
      rw [sq.hPi_Q_rel]
      exact Set.mem_image_of_mem _ h2
    have hp_wit : pw ∈ sq.P_norm_Q := (sq.h_witness (x_orig z hz) hx_orig).1
    have h_params := sq.hfineTube_params pw hp_wit tubeCell htubeCell
    have hcell0 : cell 0 = tubeSlope (sq.fineTubeOfCell pw tubeCell) := by
      rw [hcell_eq']; simp [toPlane', h_params]
    have hcell1 : cell 1 = tubeIntercept (sq.fineTubeOfCell pw tubeCell) := by
      rw [hcell_eq']; simp [toPlane', h_params]
    have h_res : |(x_orig z hz) - tubeSlope (sq.fineTubeOfCell pw tubeCell) * (pw 1) -
        tubeIntercept (sq.fineTubeOfCell pw tubeCell)| ≤ 6 * δ :=
      sq.h_residual (x_orig z hz) hx_orig tubeCell htubeCell
    have h_xorig : x_orig z hz = Δ * z.1 := by
      have h : zXnorm z hz + sq.c_Q / Δ = z.1 := h_x_eq z hz
      field_simp [hΔ_pos.ne'] at h ⊢ <;> linarith
    have h_yQ : sq.y_Q = z.2 := h_yQ_eq z hz
    let θ := fromPlane' θE
    have hθ1 : θ.1 = θE 0 := by simp [θ, fromPlane']
    have hθ2 : θ.2 = θE 1 := by simp [θ, fromPlane']
    have h_zd : z.2 + d = pw 1 := by
      have h_d : d = pw 1 - sq.y_Q := by rfl
      rw [h_d, h_yQ] <;> ring
    let slope := tubeSlope (sq.fineTubeOfCell pw tubeCell)
    let intercept := tubeIntercept (sq.fineTubeOfCell pw tubeCell)
    have h_main_calc : (shearMap d θ).1 * z.2 + (shearMap d θ).2 - z.1 =
        (slope * (pw 1) + intercept - x_orig z hz) / Δ := by
      have hs1 : (shearMap d θ).1 = θ.1 := by simp [shearMap]
      have hs2 : (shearMap d θ).2 = θ.2 + θ.1 * d := by simp [shearMap]
      rw [hs1, hs2]
      have hθ1' : θ.1 = slope / Δ := by rw [hθ1, hθE0, hcell0]
      have hθ2' : θ.2 = intercept / Δ := by rw [hθ2, hθE1, hcell1]
      rw [hθ1', hθ2']
      have h_factor : slope / Δ * z.2 + (intercept / Δ + slope / Δ * d) - z.1 =
          (slope * (z.2 + d) + intercept - Δ * z.1) / Δ := by
        field_simp [hΔ_pos.ne'] <;> ring
      rw [h_factor, h_zd, h_xorig] <;> ring
    rw [h_main_calc]
    have h_abs : |(slope * (pw 1) + intercept - x_orig z hz) / Δ| =
        |x_orig z hz - slope * (pw 1) - intercept| / Δ := by
      calc
        |(slope * (pw 1) + intercept - x_orig z hz) / Δ|
          = |slope * (pw 1) + intercept - x_orig z hz| / |Δ| := by rw [abs_div]
        _ = |slope * (pw 1) + intercept - x_orig z hz| / Δ := by
          have h_absΔ : |Δ| = Δ := abs_of_pos hΔ_pos
          rw [h_absΔ]
        _ = |x_orig z hz - slope * (pw 1) - intercept| / Δ := by
          have h9 : slope * (pw 1) + intercept - x_orig z hz =
              -(x_orig z hz - slope * (pw 1) - intercept) := by ring
          rw [h9, abs_neg]
    rw [h_abs]
    have h10 : |x_orig z hz - slope * (pw 1) - intercept| / Δ ≤ (6 * δ) / Δ := by
      exact div_le_div_of_nonneg_right h_res (by positivity)
    have h11 : (6 * δ) / Δ = 6 * Δ := by
      rw [hδ_eq]
      field_simp [hΔ_pos.ne'] <;> ring
    rw [h11] at h10
    linarith

  /- hY_bounds -/
  have hY_bounds : Y ⊆ Set.Icc (-3 : ℝ) 3 := by
    intro y hy
    rcases Set.mem_iUnion₂.mp hy with ⟨Q, hQ, hrest⟩
    have h_y_eq : y = (sqOf Q hQ).y_Q := by simpa using hrest
    rw [h_y_eq]
    have h_bounds : (sqOf Q hQ).y_Q ∈ Set.Icc (-2 : ℝ) 2 := (sqOf Q hQ).hy_Q_bounds
    have h_lower : -3 ≤ (sqOf Q hQ).y_Q := by linarith [h_bounds.1]
    have h_upper : (sqOf Q hQ).y_Q ≤ 3 := by linarith [h_bounds.2]
    exact ⟨h_lower, h_upper⟩

  /- hY_sset with ε-only constant -/
  have hY_sset : IsDeltaSSet Δ τ (Real.rpow Δ (-10000 * ε)) Y := by
    have hY_def : Y = (⋃ (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0), {(a9.perSquare Q hQ).y_Q}) := by
      rfl
    rw [hY_def]
    exact hY_sset_better

  /- hX_bounds: use Pi_Q_delta_bounds directly -/
  have hX_bounds : ∀ y hy, X y hy ⊆ Set.Icc (-50 : ℝ) 50 := by
    intro y hy x' hx'
    rcases Set.mem_iUnion₂.mp hx' with ⟨Q', hQ, hrest⟩
    rcases hrest with ⟨x_norm, hx, h_x_eq⟩
    let sq := sqOf Q'.val Q'.property
    have h1 : Δ * x_norm + sq.c_Q ∈ sq.Pi_Q := by
      rw [sq.hPi_Q_rel]
      exact Set.mem_image_of_mem _ hx
    have h_eq : Δ * (x_norm + sq.c_Q / Δ) = Δ * x_norm + sq.c_Q := by
      field_simp [hΔ_pos.ne'] <;> ring
    have h2 : Δ * (x_norm + sq.c_Q / Δ) ∈ Set.Icc (-50 * Δ) (50 * Δ) := by
      rw [h_eq]
      exact sq.hPi_Q_delta_bounds h1
    have h2' : -50 * Δ ≤ Δ * (x_norm + sq.c_Q / Δ) ∧ Δ * (x_norm + sq.c_Q / Δ) ≤ 50 * Δ :=
      Set.mem_Icc.mp h2
    have h_lower : -50 ≤ x_norm + sq.c_Q / Δ := by
      have h4 : -50 * Δ ≤ Δ * (x_norm + sq.c_Q / Δ) := h2'.1
      have h5 : 0 < Δ := hΔ_pos
      calc -50
        = (-50 * Δ) / Δ := by field_simp [h5.ne'] <;> ring
      _ ≤ (Δ * (x_norm + sq.c_Q / Δ)) / Δ := by gcongr
      _ = x_norm + sq.c_Q / Δ := by field_simp [h5.ne'] <;> ring
    have h_upper : x_norm + sq.c_Q / Δ ≤ 50 := by
      have h7 : Δ * (x_norm + sq.c_Q / Δ) ≤ 50 * Δ := h2'.2
      have h8 : 0 < Δ := hΔ_pos
      calc x_norm + sq.c_Q / Δ
        = (Δ * (x_norm + sq.c_Q / Δ)) / Δ := by field_simp [h8.ne'] <;> ring
      _ ≤ (50 * Δ) / Δ := by gcongr
      _ = 50 := by field_simp [h8.ne'] <;> ring
    have h_x_eq' : x_norm + sq.c_Q / Δ = x' := h_x_eq
    rw [h_x_eq'] at h_lower h_upper
    exact ⟨h_lower, h_upper⟩

  /- hX_sset via translation + finite union -/
  have hX_sset : ∀ y hy, IsDeltaSSet Δ s (Real.rpow Δ (-600 * ε)) (X y hy) := by
    intro y hy
    let I := QsForY y
    have hI_card : I.card ≤ 120 := hQsForY_card y
    by_cases hI_empty : I = ∅
    · exfalso
      have h1 : y ∈ Y := hy
      rcases Set.mem_iUnion₂.mp h1 with ⟨Q, hQ, hrest⟩
      have h_y_eq : y = (sqOf Q hQ).y_Q := by simpa using hrest
      let Q' : {Q : CoarseSquare Δ // Q ∈ a9.Q0} := ⟨Q, hQ⟩
      have hQ'_in : Q' ∈ I := by
        simp only [I, QsForY, Finset.mem_filter, Finset.mem_attach]
        have h_eq2 : (sqOf Q'.val Q'.property).y_Q = y := by
          simpa [Q'] using h_y_eq.symm
        exact ⟨trivial, h_eq2⟩
      rw [hI_empty] at hQ'_in
      simpa using hQ'_in
    · have hI_nonempty : I.Nonempty := by
        simpa [Finset.nonempty_iff_ne_empty] using hI_empty
      -- Each translated Pi_Q_norm is an S-set
      have h_each : ∀ (Q' : {Q : CoarseSquare Δ // Q ∈ a9.Q0}), Q' ∈ I →
          IsDeltaSSet Δ s (Real.rpow Δ (-576 * ε))
            ((fun x : ℝ => x + (sqOf Q'.val Q'.property).c_Q / Δ) ''
              (sqOf Q'.val Q'.property).Pi_Q_norm) := by
        intro Q' _
        let sq := sqOf Q'.val Q'.property
        have h : IsDeltaSSet Δ s (Real.rpow Δ (-576 * ε)) sq.Pi_Q_norm := sq.hPi_Q_norm_sset
        exact IsDeltaSSet.translation_real h (c := sq.c_Q / Δ)
      let P' (Q' : {Q : CoarseSquare Δ // Q ∈ a9.Q0}) : Set ℝ :=
        (fun x : ℝ => x + (sqOf Q'.val Q'.property).c_Q / Δ) ''
          (sqOf Q'.val Q'.property).Pi_Q_norm
      have h_union : IsDeltaSSet Δ s ((I.card : ℝ) * Real.rpow Δ (-576 * ε)) (⋃ i ∈ I, P' i) :=
        local_finite_union I h_each hI_nonempty
      have h_card_le : (I.card : ℝ) ≤ 120 := by exact_mod_cast hI_card
      have h_rpow_nonneg : 0 ≤ Real.rpow Δ (-576 * ε) := Real.rpow_nonneg (by linarith) _
      have h_const_le : (I.card : ℝ) * Real.rpow Δ (-576 * ε) ≤ (120 : ℝ) * Real.rpow Δ (-576 * ε) :=
        mul_le_mul_of_nonneg_right h_card_le h_rpow_nonneg
      have h_final : IsDeltaSSet Δ s (Real.rpow Δ (-600 * ε)) (⋃ i ∈ I, P' i) :=
        IsDeltaSSet.mono_const' h_union (h_const_le.trans h_absorb_union)
      have h_eq : X y hy = ⋃ i ∈ I, P' i := by
        ext x
        simp only [X, P', Set.mem_iUnion₂]
        <;> constructor
        · rintro ⟨Q', hQ1, hQ2, hx⟩
          exact ⟨Q', hQ1, hQ2, hx⟩
        · rintro ⟨Q', hQ1, hQ2, hx⟩
          exact ⟨Q', hQ1, hQ2, hx⟩
      rw [h_eq]
      exact h_final

  /- h_upper: global bound with thickening factor -/
  have h_upper : Metric.externalCoveringNumber Δ.toNNReal
      (⋃ (z : ℝ × ℝ) (hz : z ∈ Z), T_coarse z hz) <
      ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_upper))) := by
    let U : Set EuclideanPlane := ⋃ (z : EuclideanPlane) (hz : z ∈ S), coarseParams z
    let V : Set (ℝ × ℝ) := ⋃ (z : ℝ × ℝ) (hz : z ∈ Z), T_coarse z hz
    let W : Set (ℝ × ℝ) := fromPlane' '' U
    let δ0 : NNReal := Δ.toNNReal
    let δ30 : NNReal := 30 * δ0
    let δ31 : NNReal := δ0 + δ30
    let δ32 : NNReal := 32 * δ0
    have hΔ_nonneg : 0 ≤ Δ := by linarith
    have hδ0_pos : 0 < δ0 := by positivity
    -- Step 1: Pointwise thickening property: every v ∈ V is within 30Δ of some w ∈ W
    have h_thicken : ∀ (v : ℝ × ℝ), v ∈ V → ∃ (w : ℝ × ℝ), w ∈ W ∧ dist v w ≤ (30 * Δ : ℝ) := by
      intro p hp
      rcases Set.mem_iUnion₂.mp hp with ⟨z, hz, hpz⟩
      rcases hpz with ⟨q, hq, rfl⟩
      rcases hq with ⟨θE, hθE, rfl⟩
      let d := d_shear z hz
      have hθ_in_U : θE ∈ U := by
        let zE := toPlane' z
        have hzE_in_S : zE ∈ S := hZ_to_S z hz
        exact Set.mem_iUnion₂.mpr ⟨zE, hzE_in_S, hθE⟩
      let w : ℝ × ℝ := fromPlane' θE
      have hw_in_W : w ∈ W := Set.mem_image_of_mem fromPlane' hθ_in_U
      have hd_bound : |d| ≤ 3 * Δ := h_d_bound z hz
      have hq' : w ∈ fromPlane' '' coarseParams (toPlane' z) := Set.mem_image_of_mem fromPlane' hθE
      have h_in_T : shearMap d w ∈ T_coarse z hz := ⟨w, hq', rfl⟩
      have h_bound_p : shearMap d w ∈ Set.Icc (-10 : ℝ) 10 ×ˢ Set.Icc (-10 : ℝ) 10 :=
        hT_bounds z hz h_in_T
      have h_p1 : (shearMap d w).1 = θE 0 := by simp [shearMap, fromPlane', w]
      have h_theta0 : |θE 0| ≤ 10 := by
        have h : (shearMap d w).1 ∈ Set.Icc (-10 : ℝ) 10 := h_bound_p.1
        rw [h_p1] at h
        exact abs_le.mpr h
      have h21 : (shearMap d w).1 = w.1 := by simp [shearMap, fromPlane', w]
      have h22 : (shearMap d w).2 - w.2 = θE 0 * d := by
        simp [shearMap, fromPlane', w] <;> ring
      have h_dist_eq : dist (shearMap d w) w = |θE 0 * d| := by
        have h1 : dist (shearMap d w) w = max (dist ((shearMap d w).1) (w.1)) (dist ((shearMap d w).2) (w.2)) := by
          rw [Prod.dist_eq]
        rw [h1]
        have h3 : dist ((shearMap d w).1) (w.1) = 0 := by
          rw [h21] <;> simp
        have h4 : dist ((shearMap d w).2) (w.2) = |θE 0 * d| := by
          rw [Real.dist_eq, h22]
        rw [h3, h4]
        have h5 : 0 ≤ |θE 0 * d| := abs_nonneg _
        rw [max_eq_right h5]
      have h_dist : dist (shearMap d w) w ≤ 30 * Δ := by
        rw [h_dist_eq]
        have h_abs : |θE 0 * d| = |θE 0| * |d| := by rw [abs_mul]
        rw [h_abs]
        calc |θE 0| * |d|
          ≤ 10 * |d| := by gcongr
        _ ≤ 10 * (3 * Δ) := by gcongr
        _ = 30 * Δ := by ring
      exact ⟨w, hw_in_W, h_dist⟩
    -- Step 1b: Convert bound to δ30
    have hδ30_coe : (δ30 : ℝ) = 30 * Δ := by
      have h1 : (δ0 : ℝ) = Δ := by
        simp [δ0, Real.toNNReal_of_nonneg hΔ_nonneg]
      simp [δ30, h1] <;> ring
    have h_thicken' : ∀ (v : ℝ × ℝ), v ∈ V → ∃ (w : ℝ × ℝ), w ∈ W ∧ dist v w ≤ (δ30 : ℝ) := by
      intro v hv
      rcases h_thicken v hv with ⟨w, hw, hdist⟩
      refine ⟨w, hw, ?_⟩
      rw [hδ30_coe]
      exact hdist
    -- Step 2: N_{31Δ}(V) ≤ N_Δ(W) via thickening
    have h2_nat : Metric.externalCoveringNumber δ31 V ≤ Metric.externalCoveringNumber δ0 W :=
      externalCoveringNumber_thickening (h := h_thicken')
    have h2 : (Metric.externalCoveringNumber δ31 V : ENNReal) ≤
        (Metric.externalCoveringNumber δ0 W : ENNReal) := by
      exact_mod_cast h2_nat
    -- Step 3: N_Δ(V) ≤ 1024 * N_{32Δ}(V) by iterated refinement
    let δ1 : NNReal := (2 : NNReal) * δ0
    let δ2 : NNReal := (2 : NNReal) * δ1
    let δ3 : NNReal := (2 : NNReal) * δ2
    let δ4 : NNReal := (2 : NNReal) * δ3
    let δ5 : NNReal := (2 : NNReal) * δ4
    have hδ5_eq : δ5 = δ32 := by
      apply NNReal.coe_injective
      simp [δ1, δ2, δ3, δ4, δ5, δ32] <;> ring
    have h_ref1 := prod_covering_refine_4 (A := V) hδ0_pos
    have h_ref2 := prod_covering_refine_4 (A := V) (show 0 < δ1 from by positivity)
    have h_ref3 := prod_covering_refine_4 (A := V) (show 0 < δ2 from by positivity)
    have h_ref4 := prod_covering_refine_4 (A := V) (show 0 < δ3 from by positivity)
    have h_ref5 := prod_covering_refine_4 (A := V) (show 0 < δ4 from by positivity)
    have h3 : (Metric.externalCoveringNumber δ0 V : ENNReal) ≤
        (1024 : ENNReal) * (Metric.externalCoveringNumber δ32 V : ENNReal) := by
      have h_a : (Metric.externalCoveringNumber δ0 V : ENNReal) ≤
          (4 : ENNReal) * (Metric.externalCoveringNumber δ1 V : ENNReal) := h_ref1
      have h_b : (4 : ENNReal) * (Metric.externalCoveringNumber δ1 V : ENNReal) ≤
          (16 : ENNReal) * (Metric.externalCoveringNumber δ2 V : ENNReal) := by
        calc (4 : ENNReal) * (Metric.externalCoveringNumber δ1 V : ENNReal)
          ≤ (4 : ENNReal) * ((4 : ENNReal) * (Metric.externalCoveringNumber δ2 V : ENNReal)) :=
            mul_le_mul_left' h_ref2 _
        _ = (16 : ENNReal) * (Metric.externalCoveringNumber δ2 V : ENNReal) := by
          have h_mul : (4 : ENNReal) * (4 : ENNReal) = (16 : ENNReal) := by norm_cast
          rw [← mul_assoc, h_mul]
      have h_c : (16 : ENNReal) * (Metric.externalCoveringNumber δ2 V : ENNReal) ≤
          (64 : ENNReal) * (Metric.externalCoveringNumber δ3 V : ENNReal) := by
        calc (16 : ENNReal) * (Metric.externalCoveringNumber δ2 V : ENNReal)
          ≤ (16 : ENNReal) * ((4 : ENNReal) * (Metric.externalCoveringNumber δ3 V : ENNReal)) :=
            mul_le_mul_left' h_ref3 _
        _ = (64 : ENNReal) * (Metric.externalCoveringNumber δ3 V : ENNReal) := by
          have h_mul : (16 : ENNReal) * (4 : ENNReal) = (64 : ENNReal) := by norm_cast
          rw [← mul_assoc, h_mul]
      have h_d : (64 : ENNReal) * (Metric.externalCoveringNumber δ3 V : ENNReal) ≤
          (256 : ENNReal) * (Metric.externalCoveringNumber δ4 V : ENNReal) := by
        calc (64 : ENNReal) * (Metric.externalCoveringNumber δ3 V : ENNReal)
          ≤ (64 : ENNReal) * ((4 : ENNReal) * (Metric.externalCoveringNumber δ4 V : ENNReal)) :=
            mul_le_mul_left' h_ref4 _
        _ = (256 : ENNReal) * (Metric.externalCoveringNumber δ4 V : ENNReal) := by
          have h_mul : (64 : ENNReal) * (4 : ENNReal) = (256 : ENNReal) := by norm_cast
          rw [← mul_assoc, h_mul]
      have h_e : (256 : ENNReal) * (Metric.externalCoveringNumber δ4 V : ENNReal) ≤
          (1024 : ENNReal) * (Metric.externalCoveringNumber δ5 V : ENNReal) := by
        calc (256 : ENNReal) * (Metric.externalCoveringNumber δ4 V : ENNReal)
          ≤ (256 : ENNReal) * ((4 : ENNReal) * (Metric.externalCoveringNumber δ5 V : ENNReal)) :=
            mul_le_mul_left' h_ref5 _
        _ = (1024 : ENNReal) * (Metric.externalCoveringNumber δ5 V : ENNReal) := by
          have h_mul : (256 : ENNReal) * (4 : ENNReal) = (1024 : ENNReal) := by norm_cast
          rw [← mul_assoc, h_mul]
      calc (Metric.externalCoveringNumber δ0 V : ENNReal)
        ≤ (4 : ENNReal) * (Metric.externalCoveringNumber δ1 V : ENNReal) := h_a
      _ ≤ (16 : ENNReal) * (Metric.externalCoveringNumber δ2 V : ENNReal) := h_b
      _ ≤ (64 : ENNReal) * (Metric.externalCoveringNumber δ3 V : ENNReal) := h_c
      _ ≤ (256 : ENNReal) * (Metric.externalCoveringNumber δ4 V : ENNReal) := h_d
      _ ≤ (1024 : ENNReal) * (Metric.externalCoveringNumber δ5 V : ENNReal) := h_e
      _ = (1024 : ENNReal) * (Metric.externalCoveringNumber δ32 V : ENNReal) := by
        rw [hδ5_eq]
    -- Step 4: N_{32Δ}(V) ≤ N_{31Δ}(V) by monotonicity
    have h4 : (Metric.externalCoveringNumber δ32 V : ENNReal) ≤
        (Metric.externalCoveringNumber δ31 V : ENNReal) := by
      have h_eq31 : δ31 = 31 * δ0 := by
        simp [δ31, δ30] <;> ring
      rw [h_eq31]
      have h_le : (31 * δ0 : NNReal) ≤ δ32 := by
        apply NNReal.coe_le_coe.mp
        have h : (31 : ℝ) * (δ0 : ℝ) ≤ (32 : ℝ) * (δ0 : ℝ) := by
          gcongr <;> norm_num
        simpa [δ32] using h
      exact_mod_cast Metric.externalCoveringNumber_anti h_le
    -- Step 5: N_Δ(W) ≤ N_Δ(U) since fromPlane' is 1-Lipschitz
    have h_fromPlane_lip : LipschitzWith (1 : NNReal) fromPlane' := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      let z := x - y
      have h_norm2 : ‖z‖ ^ 2 = |z 0| ^ 2 + |z 1| ^ 2 := by
        have h : ‖z‖ = Real.sqrt (|z 0| ^ 2 + |z 1| ^ 2) := by
          simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, z]
          <;> ring
        rw [h]
        rw [Real.sq_sqrt (by positivity)]
      have h1 : |z 0| ≤ ‖z‖ := by
        have hsq : |z 0| ^ 2 ≤ ‖z‖ ^ 2 := by
          rw [h_norm2]
          have h : |z 0| ^ 2 ≤ |z 0| ^ 2 + |z 1| ^ 2 := by
            apply le_add_of_nonneg_right
            exact sq_nonneg _
          exact h
        calc |z 0|
          = Real.sqrt (|z 0| ^ 2) := by rw [Real.sqrt_sq (abs_nonneg _)]
        _ ≤ Real.sqrt (‖z‖ ^ 2) := Real.sqrt_le_sqrt hsq
        _ = ‖z‖ := by rw [Real.sqrt_sq (norm_nonneg _)]
      have h2 : |z 1| ≤ ‖z‖ := by
        have hsq : |z 1| ^ 2 ≤ ‖z‖ ^ 2 := by
          rw [h_norm2]
          have h : |z 1| ^ 2 ≤ |z 0| ^ 2 + |z 1| ^ 2 := by
            apply le_add_of_nonneg_left
            exact sq_nonneg _
          exact h
        calc |z 1|
          = Real.sqrt (|z 1| ^ 2) := by rw [Real.sqrt_sq (abs_nonneg _)]
        _ ≤ Real.sqrt (‖z‖ ^ 2) := Real.sqrt_le_sqrt hsq
        _ = ‖z‖ := by rw [Real.sqrt_sq (norm_nonneg _)]
      have h3 : dist (fromPlane' x) (fromPlane' y) ≤ ‖x - y‖ := by
        have h4 : (fromPlane' x).1 - (fromPlane' y).1 = z 0 := by simp [fromPlane', z]
        have h5 : (fromPlane' x).2 - (fromPlane' y).2 = z 1 := by simp [fromPlane', z]
        have h6 : dist (fromPlane' x) (fromPlane' y) = max (|z 0|) (|z 1|) := by
          rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, h4, h5] <;> rfl
        rw [h6]
        exact max_le h1 h2
      simpa [dist_eq_norm, z] using h3
    have h5 : (Metric.externalCoveringNumber δ0 W : ENNReal) ≤
        (Metric.externalCoveringNumber δ0 U : ENNReal) := by
      have h := _root_.externalCoveringNumber_image_lipschitz (hf := h_fromPlane_lip) (ε := δ0) (A := U)
      have h_eq : (1 : NNReal) * δ0 = δ0 := by simp
      rw [h_eq] at h
      simpa using h
    -- Step 6: N_Δ(U) ≤ N_δ(allFine)
    have h6 : (Metric.externalCoveringNumber δ0 U : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal allFine : ENNReal) := by
      exact_mod_cast h_global_bound
    -- Combine
    calc (Metric.externalCoveringNumber δ0 V : ENNReal)
      ≤ (1024 : ENNReal) * (Metric.externalCoveringNumber δ32 V : ENNReal) := h3
    _ ≤ (1024 : ENNReal) * (Metric.externalCoveringNumber δ31 V : ENNReal) := by gcongr
    _ ≤ (1024 : ENNReal) * (Metric.externalCoveringNumber δ0 W : ENNReal) := by gcongr
    _ ≤ (1024 : ENNReal) * (Metric.externalCoveringNumber δ0 U : ENNReal) := by gcongr
    _ ≤ (1024 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal allFine : ENNReal) := by gcongr
    _ ≤ (2000 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal allFine : ENNReal) := by
      gcongr <;> norm_num
    _ < ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_upper))) := h_allFine_upper

  exact {
    η_upper := η_upper,
    hη_upper_pos := hη_upper_pos,
    hη_upper_gt_ε := hη_upper_gt_ε,
    τ := τ,
    hτ_pos := hτ_pos,
    hτ_le_one := hτ_le_one,
    hτ_le_t_sub_s := hτ_le_t_sub_s,
    Y := Y,
    hY_bounds := hY_bounds,
    hY_sset := hY_sset_better,
    X := X,
    hX_bounds := hX_bounds,
    hX_sset := hX_sset,
    Z := Z,
    hZ_def := rfl,
    T_coarse := T_coarse,
    hT_bounds := hT_bounds,
    hT_sset := hT_sset,
    h_inc := h_inc,
    h_upper := h_upper
  }

/-- Wrapper around A10_product_witness_fixed that discharges the easy
    hypotheses from A9_Output and numerical bounds on Δ.

    Discharged: hY_sset_better (via mono_const', weaken Δ^{-188ε} → Δ^{-10000ε}),
    h_a9_τ (passed through).
    Remaining hard assumptions: h_allFine_upper, h_fine_rescalable,
    h_fine_rescalable_prod.
    Note: h_370ε_ge_τ removed — ε-only target constant makes it
    unnecessary since a9.τ ≤ t-s and 10000ε provides ample slack. -/
noncomputable def A10_product_witness_from_A9_easy
    {Δ δ s t ε η_upper : ℝ}
    (a9 : A9_Output Δ δ s t ε)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2)
    (hε_pos : 0 < ε)
    (hη_upper_pos : 0 < η_upper)
    (hη_upper_gt_ε : ε < η_upper)
    (hδ_eq : δ = Δ ^ 2)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hΔ_lt_third : Δ < 1 / 3)
    (hΔ_lt_1_16 : Δ < 1 / 16)
    (hε_le_one : ε ≤ 1)
    (hQ0_nonempty : a9.Q0.Nonempty)
    (h_a9_τ : a9.τ = min (t - s) 1)
    -- Numerical absorption hypotheses (hold for sufficiently small Δ)
    (h_absorb_shear : (400 : ℝ) * (Real.sqrt 2) ^ s * (2 : ℝ) ^ s * Real.rpow Δ (-501 * ε) ≤ Real.rpow Δ (-600 * ε))
    (h_absorb_union : (120 : ℝ) * Real.rpow Δ (-576 * ε) ≤ Real.rpow Δ (-600 * ε))
    -- Hard hypothesis: 2000*N_δ(allFine) < Δ^{-(2s+η_upper)}
    -- Discharged from counter-assumption upstream (η_upper < 2s+2ε).
    (h_allFine_upper : (2000 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal (allFineParamsEuclidean a9) <
        ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_upper))))
    (h_fine_rescalable : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0)
        (p : EuclideanPlane), p ∈ (a9.perSquare Q hQ).P_norm_Q →
        IsRescalableDeltaSet δ Δ s (Real.rpow Δ (-501 * ε))
          ((fun cell => toPlane' (paramsOfDyadicCell δ cell)) ''
            ((a9.perSquare Q hQ).fineTubes_norm p : Set (DyadicTubeCell δ))))
    (h_fine_rescalable_prod : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0)
        (p : EuclideanPlane), p ∈ (a9.perSquare Q hQ).P_norm_Q →
        IsRescalableDeltaSet δ Δ s (Real.rpow Δ (-501 * ε))
          ((fun cell => paramsOfDyadicCell δ cell) ''
            ((a9.perSquare Q hQ).fineTubes_norm p : Set (DyadicTubeCell δ)))) :
    A10_Output Δ s t ε := by
  -- Weaken A9's Y constant Δ^{-378ε} to target Δ^{-10000ε}
  -- Since -378ε ≥ -10000ε for ε>0, we have Δ^{-378ε} ≤ Δ^{-10000ε}.
  have h1 : -378 * ε ≥ -10000 * ε := by linarith
  have h_const_le : Real.rpow Δ (-378 * ε) ≤ Real.rpow Δ (-10000 * ε) :=
    Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h1
  have hY_sset_better : IsDeltaSSet Δ (min (t - s) 1) (Real.rpow Δ (-10000 * ε))
      (⋃ (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0), {(a9.perSquare Q hQ).y_Q}) := by
    have hY_sset_a9 := a9.hY_sset
    rw [h_a9_τ] at hY_sset_a9
    exact IsDeltaSSet.mono_const' hY_sset_a9 h_const_le
  exact A10_product_witness_fixed
    (a9 := a9)
    (hs := hs) (hs1 := hs1) (hst := hst) (ht2 := ht2)
    (hε_pos := hε_pos)
    (hη_upper_pos := hη_upper_pos) (hη_upper_gt_ε := hη_upper_gt_ε)
    (hδ_eq := hδ_eq)
    (hΔ_pos := hΔ_pos) (hΔ_lt_one := hΔ_lt_one)
    (hΔ_lt_third := hΔ_lt_third) (hΔ_lt_1_16 := hΔ_lt_1_16) (hε_le_one := hε_le_one)
    (hQ0_nonempty := hQ0_nonempty)
    (h_a9_τ := h_a9_τ)
    (hY_sset_better := hY_sset_better)
    (h_absorb_shear := h_absorb_shear)
    (h_absorb_union := h_absorb_union)
    (h_allFine_upper := h_allFine_upper)
    (h_fine_rescalable := h_fine_rescalable)
    (h_fine_rescalable_prod := h_fine_rescalable_prod)

/-- Full A10 wrapper: discharges h_fine_rescalable hypotheses from A9 data,
    then calls A10_product_witness_from_A9_easy.

    Requires the constant absorption bound `16 * C_fine_resc ≤ Δ^{-499ε}`.
    The toPlane' conversion is by definitional equality. -/
noncomputable def A10_from_A9_full
    {Δ δ s t ε η_upper : ℝ}
    (a9 : A9_Output Δ δ s t ε)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2)
    (hε_pos : 0 < ε)
    (hη_upper_pos : 0 < η_upper)
    (hη_upper_gt_ε : ε < η_upper)
    (hδ_eq : δ = Δ ^ 2)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hΔ_lt_third : Δ < 1 / 3)
    (hΔ_lt_1_16 : Δ < 1 / 16)
    (hε_le_one : ε ≤ 1)
    (hQ0_nonempty : a9.Q0.Nonempty)
    (h_a9_τ : a9.τ = min (t - s) 1)
    (h_absorb_shear : (400 : ℝ) * (Real.sqrt 2) ^ s * (2 : ℝ) ^ s * Real.rpow Δ (-501 * ε) ≤ Real.rpow Δ (-600 * ε))
    (h_absorb_union : (120 : ℝ) * Real.rpow Δ (-576 * ε) ≤ Real.rpow Δ (-600 * ε))
    (h_allFine_upper : (2000 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal (allFineParamsEuclidean a9) <
        ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_upper))))
    (hC_fine_le : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0),
      16 * (a9.perSquare Q hQ).C_fine_resc ≤ Real.rpow Δ (-501 * ε)) :
    A10_Output Δ s t ε := by
  have h_fine := DirecretisedFurstenbergEstimate.A10.a10_fine_rescalable_of_a9
    (a9 := a9) (hC_le := hC_fine_le) (hΔ_pos := hΔ_pos) (hs := hs.le)
  have h_fine_rescalable_prod := h_fine.1
  have h_fine_rescalable_plane := h_fine.2
  -- Convert toPlane' from A10 namespace to AppendixA.A10 namespace (defeq)
  have h_fine_rescalable : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0) (p : EuclideanPlane),
      p ∈ (a9.perSquare Q hQ).P_norm_Q →
      IsRescalableDeltaSet δ Δ s (Real.rpow Δ (-501 * ε))
        ((fun cell => toPlane' (paramsOfDyadicCell δ cell)) ''
          ((a9.perSquare Q hQ).fineTubes_norm p : Set (DyadicTubeCell δ))) := by
    intro Q hQ p hp
    have h := h_fine_rescalable_plane Q hQ p hp
    have h_eq : (fun cell : DyadicTubeCell δ => DirecretisedFurstenbergEstimate.A10.toPlane' (paramsOfDyadicCell δ cell)) =
        (fun cell : DyadicTubeCell δ => toPlane' (paramsOfDyadicCell δ cell)) := by
      rfl
    rw [h_eq] at h
    exact h
  exact A10_product_witness_from_A9_easy
    (a9 := a9) (hs := hs) (hs1 := hs1) (hst := hst) (ht2 := ht2)
    (hε_pos := hε_pos) (hη_upper_pos := hη_upper_pos) (hη_upper_gt_ε := hη_upper_gt_ε)
    (hδ_eq := hδ_eq) (hΔ_pos := hΔ_pos) (hΔ_lt_one := hΔ_lt_one)
    (hΔ_lt_third := hΔ_lt_third) (hΔ_lt_1_16 := hΔ_lt_1_16) (hε_le_one := hε_le_one)
    (hQ0_nonempty := hQ0_nonempty) (h_a9_τ := h_a9_τ)
    (h_absorb_shear := h_absorb_shear) (h_absorb_union := h_absorb_union)
    (h_allFine_upper := h_allFine_upper)
    (h_fine_rescalable := h_fine_rescalable)
    (h_fine_rescalable_prod := h_fine_rescalable_prod)

end DirecretisedFurstenbergEstimate.AppendixA.A10
