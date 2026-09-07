module

/-
  Physical S-set to Y S-set transfer lemma.

  Given a physical S-set Q0_phys (square centers) with exponent u = t-s,
  a near-line condition, and bounded y-fibers, prove that the projection
  Y = {Δ*(Q.2:ℝ) | Q ∈ Q0} is a (Δ, τ, C_Y)-set with τ = min(u,1) and C_Y
  containing NO fixed dimensional exponent (only ε-dependent loss).

  Uses a generalized tube projection with strip factor a=61 (from near-line W=59Δ),
  then weakens exponent u → τ for bounded 1D sets.

  Whiteprint node: appendix_a_alternative / physical_to_y_sset
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Lagoon (squareCenter)

/-! ========================================================================
   Local copies of two PieceAHelpers lemmas (to avoid import conflict between
   LemmaE_Helpers and AffineLineParams).
   ======================================================================== -/

/-- At most 3 δ-separated real points in a δ-ball. -/
lemma local_separated_real_ball_card_le_three {δ : ℝ} (hδ_pos : 0 < δ)
    {S : Finset ℝ} {center : ℝ}
    (hS_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → |x - y| ≥ δ)
    (hS_in : ∀ x ∈ S, |x - center| ≤ δ) :
    S.card ≤ 3 := by
  by_contra h
  have h_card4 : 4 ≤ S.card := by linarith
  let k := S.card
  let e : Fin k ≃o S := Finset.orderIsoOfFin S rfl
  have h0 : 0 < k := by omega
  have h1 : 1 < k := by omega
  have h2 : 2 < k := by omega
  have h3 : 3 < k := by omega
  let i0 : Fin k := ⟨0, h0⟩
  let i1 : Fin k := ⟨1, h1⟩
  let i2 : Fin k := ⟨2, h2⟩
  let i3 : Fin k := ⟨3, h3⟩
  let a : ℝ := ↑(e i0)
  let b : ℝ := ↑(e i1)
  let c_pt : ℝ := ↑(e i2)
  let d : ℝ := ↑(e i3)
  have ha : a ∈ S := (e i0).property
  have hb : b ∈ S := (e i1).property
  have hc : c_pt ∈ S := (e i2).property
  have hd : d ∈ S := (e i3).property
  have h_i0_lt_i1 : i0 < i1 := by simp [i0, i1, Fin.lt_iff_val_lt_val] <;> norm_num
  have h_i1_lt_i2 : i1 < i2 := by simp [i1, i2, Fin.lt_iff_val_lt_val] <;> norm_num
  have h_i2_lt_i3 : i2 < i3 := by simp [i2, i3, Fin.lt_iff_val_lt_val] <;> norm_num
  have h_ab : (e i0 : ℝ) < (e i1 : ℝ) := e.strictMono h_i0_lt_i1
  have h_bc : (e i1 : ℝ) < (e i2 : ℝ) := e.strictMono h_i1_lt_i2
  have h_cd : (e i2 : ℝ) < (e i3 : ℝ) := e.strictMono h_i2_lt_i3
  have h1 : b - a ≥ δ := by
    have hsep : |a - b| ≥ δ := hS_sep a ha b hb (ne_of_lt h_ab)
    have hpos : 0 < b - a := by linarith
    have habs : |a - b| = b - a := by
      rw [show a - b = -(b - a) from by ring, abs_neg, abs_of_pos hpos]
    rw [habs] at hsep; exact hsep
  have h2 : c_pt - b ≥ δ := by
    have hsep : |b - c_pt| ≥ δ := hS_sep b hb c_pt hc (ne_of_lt h_bc)
    have hpos : 0 < c_pt - b := by linarith
    have habs : |b - c_pt| = c_pt - b := by
      rw [show b - c_pt = -(c_pt - b) from by ring, abs_neg, abs_of_pos hpos]
    rw [habs] at hsep; exact hsep
  have h3 : d - c_pt ≥ δ := by
    have hsep : |c_pt - d| ≥ δ := hS_sep c_pt hc d hd (ne_of_lt h_cd)
    have hpos : 0 < d - c_pt := by linarith
    have habs : |c_pt - d| = d - c_pt := by
      rw [show c_pt - d = -(d - c_pt) from by ring, abs_neg, abs_of_pos hpos]
    rw [habs] at hsep; exact hsep
  have h4' : d - a ≥ 3 * δ := by linarith
  have h5 : d - a ≤ 2 * δ := by
    have hda : |d - center| ≤ δ := hS_in d hd
    have hac : |a - center| ≤ δ := hS_in a ha
    have h : d - a ≤ |d - center| + |a - center| := by
      have h' : d - a = (d - center) + (center - a) := by ring
      rw [h']
      have h1 : d - center ≤ |d - center| := le_abs_self _
      have h2 : center - a ≤ |center - a| := le_abs_self _
      have h3 : |center - a| = |a - center| := by
        rw [show center - a = -(a - center) from by ring, abs_neg]
      linarith
    linarith
  linarith

/-- For δ-separated finite Y ⊆ ℝ, |Y| ≤ 3·cov_δ(Y). -/
lemma local_separated_encard_le_three_times_covering
    {δ : ℝ} (hδ_pos : 0 < δ) {Y : Set ℝ} (hY_fin : Set.Finite Y)
    (hY_nonempty : Y.Nonempty)
    (h_sep : ∀ y1 y2, y1 ∈ Y → y2 ∈ Y → y1 ≠ y2 → |y1 - y2| ≥ δ) :
    (Y.encard : ENNReal) ≤ 3 * (Metric.externalCoveringNumber δ.toNNReal Y : ENNReal) := by
  classical
  let Y' := hY_fin.toFinset
  have hY'_eq : (Y' : Set ℝ) = Y := hY_fin.coe_toFinset
  let ballFinset : ℝ → Finset ℝ := fun c =>
    Y'.filter (fun x => x ∈ Metric.closedBall c δ)
  have h_main : ∀ (C : Set ℝ), Metric.IsCover δ.toNNReal Y C →
      (Y.encard : ENNReal) ≤ 3 * (C.encard : ENNReal) := by
    intro C hC
    by_cases hC_inf : Set.Infinite C
    · have h_top : C.encard = ⊤ := by exact Set.encard_eq_top_iff.mpr hC_inf
      rw [h_top]; simp
    · have hC_fin : Set.Finite C := by exact Set.not_infinite.mp hC_inf
      let C' := hC_fin.toFinset
      have hcover : Y ⊆ ⋃ c ∈ (C' : Set ℝ), Metric.closedBall c δ := by
        intro y hy
        have h1 : ∃ c : ℝ, c ∈ C ∧ edist y c ≤ δ.toNNReal := hC hy
        rcases h1 with ⟨c, hcC, hdist⟩
        have h2 : c ∈ (C' : Set ℝ) := by simpa [C', hC_fin.mem_toFinset] using hcC
        have h3 : dist y c ≤ δ := by
          have h41 : (δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by exact ENNReal.ofNNReal_toNNReal δ
          have h42 : edist y c ≤ (δ.toNNReal : ENNReal) := hdist
          rw [h41] at h42
          rw [edist_dist] at h42
          exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp h42
        have h5 : |y - c| ≤ δ := by simpa [Real.dist_eq] using h3
        exact Set.mem_iUnion₂.mpr ⟨c, h2, h5⟩
      have h_card : ∀ c ∈ C', (ballFinset c).card ≤ 3 := by
        intro c _
        let S := ballFinset c
        have hS_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → |x - y| ≥ δ := by
          intro x hx y hy hxy
          have hxY' : x ∈ Y' := (Finset.mem_filter.mp hx).1
          have hyY' : y ∈ Y' := (Finset.mem_filter.mp hy).1
          have hxY : x ∈ Y := hY'_eq ▸ hxY'
          have hyY : y ∈ Y := hY'_eq ▸ hyY'
          exact h_sep x y hxY hyY hxy
        have hS_in : ∀ x ∈ S, |x - c| ≤ δ := by
          intro x hx
          have hball : x ∈ Metric.closedBall c δ := (Finset.mem_filter.mp hx).2
          simpa [Metric.mem_closedBall, Real.dist_eq] using hball
        exact local_separated_real_ball_card_le_three hδ_pos (hS_sep := hS_sep) (hS_in := hS_in)
      let S_union : Finset ℝ := Finset.biUnion C' ballFinset
      have hY_sub : Y' ⊆ S_union := by
        intro x hx
        have hxY : x ∈ Y := hY'_eq ▸ hx
        have h2 : x ∈ ⋃ c ∈ (C' : Set ℝ), Metric.closedBall c δ := hcover hxY
        rcases Set.mem_iUnion₂.mp h2 with ⟨c, hcC', hball⟩
        have hcC'_fin : c ∈ C' := by exact_mod_cast hcC'
        have hxin : x ∈ ballFinset c := by
          rw [Finset.mem_filter]; exact ⟨hx, hball⟩
        exact Finset.mem_biUnion.mpr ⟨c, hcC'_fin, hxin⟩
      have h4 : Y'.card ≤ ∑ c ∈ C', (ballFinset c).card := by
        calc Y'.card ≤ S_union.card := Finset.card_le_card hY_sub
          _ ≤ ∑ c ∈ C', (ballFinset c).card := Finset.card_biUnion_le
      have h5 : ∑ c ∈ C', (ballFinset c).card ≤ ∑ c ∈ C', (3 : ℕ) := by
        apply Finset.sum_le_sum; intro i _; exact h_card i ‹_›
      have h6 : ∑ c ∈ C', (3 : ℕ) = 3 * C'.card := by simp [Finset.sum_const] <;> ring
      have h7 : Y'.card ≤ 3 * C'.card := by linarith
      have h8 : (Y.encard : ENNReal) = ↑Y'.card := by
        have h9 : Y.encard = Y'.card := by rw [←hY'_eq]; simp
        exact_mod_cast h9
      have h9 : (C.encard : ENNReal) = ↑C'.card := by
        have h10 : (C' : Set ℝ) = C := hC_fin.coe_toFinset
        have h11 : C.encard = (C' : Set ℝ).encard := by rw [h10]
        have h12 : (C' : Set ℝ).encard = C'.card := by simp
        rw [h11, h12] <;> exact_mod_cast rfl
      rw [h8, h9]; exact_mod_cast h7
  set n : ℕ∞ := Metric.externalCoveringNumber δ.toNNReal Y with hn
  have h_n_le_Y : n ≤ Y.encard := Metric.externalCoveringNumber_le_encard_self Y
  have h_n_lt_top : n < ⊤ := lt_of_le_of_lt h_n_le_Y (Set.Finite.encard_lt_top hY_fin)
  have h_n_ne_top : n ≠ ⊤ := ne_of_lt h_n_lt_top
  have h_exists : ∃ (k : ℕ), n = ↑k := by exact Option.ne_none_iff_exists'.mp h_n_ne_top
  rcases h_exists with ⟨k, hk⟩
  have h1 : ¬ (↑(k + 1) : ℕ∞) ≤ n := by
    rw [hk]
    have h_lt : (↑k : ℕ∞) < ↑(k + 1) := by exact ENat.coe_lt_coe.mpr (Nat.lt_succ_self k)
    exact not_le.mpr h_lt
  let f : Set ℝ → ℕ∞ := fun C => ⨅ (h : Metric.IsCover δ.toNNReal Y C), C.encard
  have hn_eq : n = ⨅ (C : Set ℝ), f C := by
    simp [hn, Metric.externalCoveringNumber, f]
  have h2 : ∃ (C : Set ℝ), ¬ (↑(k + 1) : ℕ∞) ≤ f C := by
    rw [hn_eq] at h1
    have h_not_all : ¬ ∀ (C : Set ℝ), (↑(k + 1) : ℕ∞) ≤ f C := by
      intro hall
      have hle : (↑(k + 1) : ℕ∞) ≤ ⨅ (C : Set ℝ), f C := le_ciInf hall
      exact h1 hle
    simpa [not_forall] using h_not_all
  rcases h2 with ⟨C, h2C⟩
  have hC_true : Metric.IsCover δ.toNNReal Y C := by
    by_contra hC_false
    have h_f_top : f C = ⊤ := by
      dsimp only [f]
      have h : ¬Metric.IsCover δ.toNNReal Y C := hC_false
      simp [h]
    rw [h_f_top] at h2C <;> simp at h2C <;> tauto
  have h_f_eq : f C = C.encard := by
    dsimp only [f]; simp [hC_true] <;> rfl
  have h3 : ¬ (↑(k + 1) : ℕ∞) ≤ C.encard := by
    rw [h_f_eq] at h2C; exact h2C
  have h4 : C.encard < ↑(k + 1) := by exact Std.not_le.mp h3
  have h5 : C.encard ≤ ↑k := by exact ENat.lt_coe_add_one_iff.mp h4
  have h6 : C.encard ≤ n := by rw [hk]; exact h5
  have h7 : n ≤ C.encard := Metric.IsCover.externalCoveringNumber_le_encard hC_true
  have h8 : C.encard = n := le_antisymm h6 h7
  have h9 : (Y.encard : ENNReal) ≤ 3 * (C.encard : ENNReal) := h_main C hC_true
  rw [h8] at h9; exact h9

/-- externalCoveringNumber does not increase under 1-Lipschitz images. -/
lemma local_externalCoveringNumber_image_lipschitz_one
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {A : Set X} {ε : NNReal}
    (hf : LipschitzWith 1 f) :
    Metric.externalCoveringNumber ε (f '' A) ≤ Metric.externalCoveringNumber ε A := by
  have h : ∀ (C : Set X), Metric.IsCover ε A C →
      Metric.externalCoveringNumber ε (f '' A) ≤ C.encard := by
    intro C hC
    have hC' : Metric.IsCover ε (f '' A) (f '' C) := by
      have h_tmp := Metric.IsCover.image_lipschitz hC hf
      simpa [one_mul] using h_tmp
    have h1 : Metric.externalCoveringNumber ε (f '' A) ≤ (f '' C).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hC'
    have h2 : (f '' C).encard ≤ C.encard := Set.encard_image_le f C
    exact le_trans h1 h2
  have h3 : Metric.externalCoveringNumber ε (f '' A) ≤
      ⨅ (C : Set X) (_ : Metric.IsCover ε A C), C.encard := by
    exact le_iInf_iff.mpr (fun C => le_iInf_iff.mpr (h C))
  simpa [Metric.externalCoveringNumber] using h3

/-- Norm squared of a plane vector equals sum of coordinate squares. -/
lemma plane_norm_sq (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  have h1 : ‖x‖ = Real.sqrt (∑ i : Fin 2, x i ^ 2) := by
    simpa [EuclideanSpace.norm_eq] using rfl
  rw [h1]
  have h2 : 0 ≤ ∑ i : Fin 2, x i ^ 2 := by positivity
  rw [Real.sq_sqrt h2, Fin.sum_univ_two] <;> ring

/-! ========================================================================
   Main: physical S-set → Y S-set
   ======================================================================== -/

/-- Transfer a physical S-set of square centers to a 1D S-set of y-coordinates.

    Given Q0_phys = Q0.image(squareCenter Δ) with physical S-set exponent u
    and constant C, near-line condition with width W ≤ 59Δ, and bounded
    y-fibers of size ≤ K, produces Y = {Δ*(Q.2:ℝ) | Q ∈ Q0} as a
    (Δ, τ, C_Y)-set where C_Y = 3·K·C·61^u·(2D)^{u-τ}.

    No fixed dimensional exponent in C_Y — only u appears in 61^u and (2D)^{u-τ},
    both of which are constants independent of Δ (since u < 2 and D is constant).
-/
lemma physical_sset_to_y_sset
    {Δ u τ C C_Y : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hu_pos : 0 < u) (hτ_pos : 0 < τ) (hτ_le_u : τ ≤ u) (hτ_le_one : τ ≤ 1)
    (Q0 : Finset (CoarseSquare Δ))
    (Q0_phys : Finset Plane)
    (hQ0_phys_eq : Q0_phys = Q0.image (squareCenter Δ))
    (h_sset : IsDeltaSSet Δ u C (Q0_phys : Set Plane))
    (σ₀ h₀ : ℝ) (hσ₀_abs : |σ₀| ≤ 1)
    (W : ℝ) (hW_nonneg : 0 ≤ W) (hW_le_59Δ : W ≤ 59 * Δ)
    (h_near : ∀ p ∈ Q0_phys, |p 0 - σ₀ * p 1 - h₀| ≤ W)
    (K : ℕ) (hK_pos : 0 < K)
    (h_fiber : ∀ y : ℝ, (Q0.filter fun Q => Δ * (Q.2 : ℝ) = y).card ≤ K)
    (D : ℝ) (hD_pos : 0 < D) (hD_ge_one : 1 ≤ D)
    (hY_bounded : (fun Q : CoarseSquare Δ => Δ * (Q.2 : ℝ)) '' (Q0 : Set (CoarseSquare Δ)) ⊆ Set.Icc (-D) D)
    (hC_Y_pos : 0 < C_Y) (hC_Y_ge_one : 1 ≤ C_Y)
    (h_absorb : 3 * (K : ℝ) * C * (61 : ℝ)^u * (2 * D)^(u - τ) ≤ C_Y) :
    IsDeltaSSet Δ τ C_Y
      ((fun Q : CoarseSquare Δ => Δ * (Q.2 : ℝ)) '' (Q0 : Set (CoarseSquare Δ))) := by
  let f : Plane → ℝ := fun p => p 1 - Δ / 2
  have hf_eq : ∀ Q : CoarseSquare Δ, f (squareCenter Δ Q) = Δ * (Q.2 : ℝ) := by
    intro Q; simp [f, squareCenter] <;> ring
  let Y_phys : Set ℝ := f '' (Q0_phys : Set Plane)
  let Y : Set ℝ := (fun Q : CoarseSquare Δ => Δ * (Q.2 : ℝ)) '' (Q0 : Set (CoarseSquare Δ))
  have hY_eq : Y_phys = Y := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨p, hp, rfl⟩
      have hp' : p ∈ (Q0.image (squareCenter Δ) : Set Plane) := by
        have h5 : p ∈ (Q0_phys : Set Plane) := hp
        rw [hQ0_phys_eq] at h5
        exact h5
      rcases Finset.mem_image.mp hp' with ⟨Q, hQ, rfl⟩
      exact ⟨Q, hQ, (hf_eq Q).symm⟩
    · intro hy
      rcases hy with ⟨Q, hQ, rfl⟩
      have hp : squareCenter Δ Q ∈ Q0_phys := by
        rw [hQ0_phys_eq]
        exact Finset.mem_image.mpr ⟨Q, hQ, rfl⟩
      exact ⟨squareCenter Δ Q, hp, hf_eq Q⟩
  have hf_lip : LipschitzWith 1 f := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    have h_coord : |p 1 - q 1| ≤ dist p q := by
      rw [dist_eq_norm]
      have h1 : ‖p - q‖ = Real.sqrt ((p 0 - q 0)^2 + (p 1 - q 1)^2) := by
        simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring_nf
      rw [h1]
      have h2 : (p 1 - q 1)^2 ≤ (p 0 - q 0)^2 + (p 1 - q 1)^2 := by
        have h21 : 0 ≤ (p 0 - q 0)^2 := by positivity
        linarith
      have h3 : |p 1 - q 1| ≤ Real.sqrt ((p 1 - q 1)^2) := by
        have h4 : Real.sqrt ((p 1 - q 1)^2) = |p 1 - q 1| := by
          rw [Real.sqrt_sq_eq_abs]
        rw [h4]
      have h5 : Real.sqrt ((p 1 - q 1)^2) ≤ Real.sqrt ((p 0 - q 0)^2 + (p 1 - q 1)^2) := by
        gcongr <;> positivity
      exact le_trans h3 h5
    simpa [f, Real.dist_eq] using h_coord
  let a : ℝ := 61
  have ha_one : 1 ≤ a := by norm_num
  -- Strip condition
  have h_strip : ∀ (y : ℝ) (r : ℝ), Δ ≤ r → ∃ (c : Plane),
      ∀ p ∈ Q0_phys, |f p - y| ≤ r → dist p c ≤ a * r := by
    intro y r hr
    let c : Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm
      (fun i : Fin 2 => if i = 0 then σ₀ * (y + Δ / 2) + h₀ else y + Δ / 2)
    have hc0 : c 0 = σ₀ * (y + Δ / 2) + h₀ := by
      simp [c] <;> aesop
    have hc1 : c 1 = y + Δ / 2 := by
      simp [c] <;> aesop
    have h_main : ∀ p ∈ Q0_phys, |f p - y| ≤ r → dist p c ≤ a * r := by
      intro p hp hfy
      have h_r_nonneg : 0 ≤ r := by linarith
      have h1 : |p 1 - (y + Δ / 2)| = |f p - y| := by simp [f] <;> ring_nf
      have hfy' : |p 1 - (y + Δ / 2)| ≤ r := by
        rw [h1]; exact hfy
      have h_near_p : |p 0 - σ₀ * p 1 - h₀| ≤ W := h_near p hp
      have h_alg : p 0 - σ₀ * (y + Δ / 2) - h₀ =
          (p 0 - σ₀ * p 1 - h₀) + σ₀ * (p 1 - (y + Δ / 2)) := by ring
      have h2 : |p 0 - σ₀ * (y + Δ / 2) - h₀| ≤ W + r := by
        rw [h_alg]
        have h_tri : |(p 0 - σ₀ * p 1 - h₀) + σ₀ * (p 1 - (y + Δ / 2))| ≤
            |p 0 - σ₀ * p 1 - h₀| + |σ₀ * (p 1 - (y + Δ / 2))| := by
          exact DiscretisedFurstenbergEstimate.real_abs_add (p.ofLp 0 - σ₀ * p.ofLp 1 - h₀)
            (σ₀ * (p.ofLp 1 - (y + Δ / 2)))
        have h_mul : |σ₀ * (p 1 - (y + Δ / 2))| = |σ₀| * |p 1 - (y + Δ / 2)| := by
          rw [abs_mul]
        rw [h_mul] at h_tri
        have h_s1 : |p 0 - σ₀ * p 1 - h₀| ≤ W := h_near_p
        have h_s2 : |σ₀| * |p 1 - (y + Δ / 2)| ≤ r := by
          calc |σ₀| * |p 1 - (y + Δ / 2)|
            ≤ 1 * |p 1 - (y + Δ / 2)| := by gcongr <;> exact hσ₀_abs
          _ = |p 1 - (y + Δ / 2)| := by ring
          _ ≤ r := hfy'
        linarith
      have h4 : W ≤ 59 * r := by
        have h41 : W ≤ 59 * Δ := hW_le_59Δ
        have h42 : Δ ≤ r := hr
        linarith
      have h5 : |p 0 - c 0| ≤ 60 * r := by
        have h50 : |p 0 - (σ₀ * (y + Δ / 2) + h₀)| = |p 0 - σ₀ * (y + Δ / 2) - h₀| := by ring_nf
        rw [hc0, h50]
        have h51 : |p 0 - σ₀ * (y + Δ / 2) - h₀| ≤ W + r := h2
        have h52 : W + r ≤ 60 * r := by linarith
        exact le_trans h51 h52
      have h6 : |p 1 - c 1| ≤ r := by
        rw [hc1]; exact hfy'
      have h_eucl : dist p c ^ 2 = (p 0 - c 0)^2 + (p 1 - c 1)^2 := by
        have h1 : dist p c = ‖p - c‖ := by rw [dist_eq_norm]
        rw [h1]
        exact plane_norm_sq (p - c)
      have h_sum_nonneg : 0 ≤ (p 0 - c 0)^2 + (p 1 - c 1)^2 := by positivity
      have h5' : (p 0 - c 0)^2 ≤ (60 * r)^2 := by
        have h51 : |p 0 - c 0| ≤ 60 * r := h5
        have h52 : (p 0 - c 0)^2 = |p 0 - c 0|^2 := by rw [sq_abs]
        rw [h52]
        gcongr
      have h6' : (p 1 - c 1)^2 ≤ r^2 := by
        have h61 : |p 1 - c 1| ≤ r := h6
        have h62 : (p 1 - c 1)^2 = |p 1 - c 1|^2 := by rw [sq_abs]
        rw [h62]
        gcongr
      have h_sum_sq : (p 0 - c 0)^2 + (p 1 - c 1)^2 ≤ (60 * r)^2 + r^2 := by linarith
      have h_final_sq : (60 * r)^2 + r^2 ≤ (a * r)^2 := by
        have h_ra : 0 ≤ r := h_r_nonneg
        simp only [a]
        have h : (60 * r)^2 + r^2 = 3601 * r^2 := by ring
        have h4 : (61 * r)^2 = 3721 * r^2 := by ring
        rw [h, h4]
        have h2 : 3601 * r^2 ≤ 3721 * r^2 := by
          have h3 : 0 ≤ r^2 := by positivity
          nlinarith
        exact h2
      have h_dist_sq_le : dist p c ^ 2 ≤ (a * r)^2 := by
        rw [h_eucl]
        exact le_trans h_sum_sq h_final_sq
      have h7 : dist p c ≤ a * r := by
        have h71 : 0 ≤ dist p c := dist_nonneg
        have h72 : 0 ≤ a * r := by positivity
        have h73 : |dist p c| ≤ |a * r| := sq_le_sq.mp h_dist_sq_le
        have h74 : |dist p c| = dist p c := abs_of_nonneg h71
        have h75 : |a * r| = a * r := abs_of_nonneg h72
        rw [h74, h75] at h73
        exact h73
      exact h7
    exact ⟨c, h_main⟩
  -- Fiber condition
  have h_fiber' : ∀ y : ℝ, ((Q0_phys.filter (fun p => f p = y)).card : ℝ) ≤ (K : ℝ) := by
    intro y
    have h_inj : Function.Injective (squareCenter Δ) := by
      intro Q1 Q2 h
      have h1 : (squareCenter Δ Q1) 0 = (squareCenter Δ Q2) 0 := by rw [h]
      have h2 : (squareCenter Δ Q1) 1 = (squareCenter Δ Q2) 1 := by rw [h]
      have hq1 : (squareCenter Δ Q1) 0 = Δ * ((Q1.1 : ℝ) + 1 / 2) := by
        simp [squareCenter] <;> ring
      have hq2 : (squareCenter Δ Q2) 0 = Δ * ((Q2.1 : ℝ) + 1 / 2) := by
        simp [squareCenter] <;> ring
      have hq3 : (squareCenter Δ Q1) 1 = Δ * ((Q1.2 : ℝ) + 1 / 2) := by
        simp [squareCenter] <;> ring
      have hq4 : (squareCenter Δ Q2) 1 = Δ * ((Q2.2 : ℝ) + 1 / 2) := by
        simp [squareCenter] <;> ring
      have h1' : Δ * ((Q1.1 : ℝ) + 1 / 2) = Δ * ((Q2.1 : ℝ) + 1 / 2) := by
        rw [←hq1, ←hq2, h1]
      have h2' : Δ * ((Q1.2 : ℝ) + 1 / 2) = Δ * ((Q2.2 : ℝ) + 1 / 2) := by
        rw [←hq3, ←hq4, h2]
      have hQ1 : (Q1.1 : ℝ) = (Q2.1 : ℝ) := by
        apply (mul_right_inj' hΔ_pos.ne').mp
        linarith
      have hQ2 : (Q1.2 : ℝ) = (Q2.2 : ℝ) := by
        apply (mul_right_inj' hΔ_pos.ne').mp
        linarith
      have hQ1' : Q1.1 = Q2.1 := by exact_mod_cast hQ1
      have hQ2' : Q1.2 = Q2.2 := by exact_mod_cast hQ2
      exact Prod.ext hQ1' hQ2'
    have h_eq : Q0_phys.filter (fun p => f p = y) =
        (Q0.filter (fun Q => Δ * (Q.2 : ℝ) = y)).image (squareCenter Δ) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · intro h
        have hpQ : p ∈ Q0_phys := h.1
        rw [hQ0_phys_eq] at hpQ
        rcases Finset.mem_image.mp hpQ with ⟨Q, hQ, hpeq⟩
        have hfy : f p = y := h.2
        have hfy' : f (squareCenter Δ Q) = y := by
          exact hpeq.symm ▸ hfy
        have hyq : Δ * (Q.2 : ℝ) = y := by
          have h_eq2 : f (squareCenter Δ Q) = Δ * (Q.2 : ℝ) := hf_eq Q
          rw [h_eq2] at hfy'
          exact hfy'
        exact ⟨Q, ⟨hQ, hyq⟩, hpeq⟩
      · rintro ⟨Q, ⟨hQ, hyq⟩, rfl⟩
        have hpQ : squareCenter Δ Q ∈ Q0_phys := by
          rw [hQ0_phys_eq]; exact Finset.mem_image.mpr ⟨Q, hQ, rfl⟩
        have hfy : f (squareCenter Δ Q) = y := by
          rw [hf_eq Q]; exact hyq
        exact ⟨hpQ, hfy⟩
    rw [h_eq]
    have h_card : ((Q0.filter (fun Q => Δ * (Q.2 : ℝ) = y)).image (squareCenter Δ)).card =
        (Q0.filter (fun Q => Δ * (Q.2 : ℝ) = y)).card := by
      rw [Finset.card_image_of_injective _ h_inj]
    rw [h_card]; exact_mod_cast h_fiber y
  -- Y separation
  have hY_sep : ∀ y1 y2, y1 ∈ Y_phys → y2 ∈ Y_phys → y1 ≠ y2 → |y1 - y2| ≥ Δ := by
    intro y1 y2 hy1 hy2 hne
    rcases hy1 with ⟨p1, hp1, rfl⟩
    rcases hy2 with ⟨p2, hp2, rfl⟩
    rw [hQ0_phys_eq] at hp1 hp2
    rcases Finset.mem_image.mp hp1 with ⟨Q1, hQ1, rfl⟩
    rcases Finset.mem_image.mp hp2 with ⟨Q2, hQ2, rfl⟩
    have hQne : Q1 ≠ Q2 := by intro h; exact hne (by rw [h])
    have h : Q1.2 ≠ Q2.2 := by
      intro h2
      have h3 : f (squareCenter Δ Q1) = f (squareCenter Δ Q2) := by
        have h4 : f (squareCenter Δ Q1) = Δ * (Q1.2 : ℝ) := hf_eq Q1
        have h5 : f (squareCenter Δ Q2) = Δ * (Q2.2 : ℝ) := hf_eq Q2
        rw [h4, h5, h2]
      exact hne h3
    have h4 : (Q1.2 : ℤ) ≠ (Q2.2 : ℤ) := by exact_mod_cast h
    have h5 : |(Q1.2 : ℝ) - (Q2.2 : ℝ)| ≥ 1 := by
      have h6 : (Q1.2 - Q2.2 : ℤ) ≠ 0 := by omega
      have h7 : 1 ≤ |(Q1.2 - Q2.2 : ℤ)| := by exact Int.one_le_abs h6
      exact_mod_cast h7
    have h10 : |f (squareCenter Δ Q1) - f (squareCenter Δ Q2)| = Δ * |(Q1.2 : ℝ) - (Q2.2 : ℝ)| := by
      have h101 : f (squareCenter Δ Q1) = Δ * (Q1.2 : ℝ) := hf_eq Q1
      have h102 : f (squareCenter Δ Q2) = Δ * (Q2.2 : ℝ) := hf_eq Q2
      rw [h101, h102]
      have h103 : |Δ * (Q1.2 : ℝ) - Δ * (Q2.2 : ℝ)| = |Δ * ((Q1.2 : ℝ) - (Q2.2 : ℝ))| := by ring_nf
      rw [h103, abs_mul]
      rw [abs_of_nonneg hΔ_pos.le]
    rw [h10]
    have h11 : 0 ≤ Δ := by linarith
    have h12 : Δ * |(Q1.2 : ℝ) - (Q2.2 : ℝ)| ≥ Δ * 1 := by
      gcongr
      <;> linarith
    linarith
  -- Apply tube projection with factor a=61 and exponent u
  rcases h_sset with ⟨hP_nonempty, hδ_pos, hC_pos, hτ_nonneg, hbound⟩
  let ε_nn : NNReal := Δ.toNNReal
  let C_proj : ℝ := 3 * (K : ℝ) * C * a^u
  have hC_proj_pos : 0 < C_proj := by positivity
  have hY_nonempty : Y_phys.Nonempty := hP_nonempty.image f
  have hY_fin : Set.Finite Y_phys := Set.Finite.image f (Finset.finite_toSet Q0_phys)
  have h_sep_lemma : (Y_phys.encard : ENNReal) ≤ 3 * (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal) :=
    local_separated_encard_le_three_times_covering hδ_pos hY_fin hY_nonempty hY_sep
  have h_fiber_sum : (Q0_phys.card : ℝ) ≤ (K : ℝ) * (Q0_phys.image f).card := by
    let fiber : ℝ → Finset Plane := fun y => Q0_phys.filter (fun p => f p = y)
    have h_partition : Q0_phys = Finset.biUnion (Q0_phys.image f) fiber := by
      ext x
      simp only [Finset.mem_biUnion]
      constructor
      · intro hx
        have hfx : f x ∈ Q0_phys.image f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
        have hxin : x ∈ fiber (f x) := by
          simp only [fiber, Finset.mem_filter]
          exact ⟨hx, trivial⟩
        exact ⟨f x, hfx, hxin⟩
      · rintro ⟨y, hy, hxy⟩
        have hx' : x ∈ Q0_phys := (Finset.mem_filter.mp hxy).1
        exact hx'
    have h_disj : ∀ y1 ∈ Q0_phys.image f, ∀ y2 ∈ Q0_phys.image f, y1 ≠ y2 →
        Disjoint (fiber y1) (fiber y2) := by
      intro y1 _ y2 _ hne
      rw [Finset.disjoint_left]; intro x hx1 hx2
      have h1 : f x = y1 := (Finset.mem_filter.mp hx1).2
      have h2 : f x = y2 := (Finset.mem_filter.mp hx2).2
      exact hne (by rw [←h1, h2])
    have h_card : Q0_phys.card = ∑ y ∈ Q0_phys.image f, (fiber y).card := by
      let s := Q0_phys.image f
      have h_eq1 : Q0_phys = Finset.biUnion s fiber := h_partition
      have h_eq2 : (Finset.biUnion s fiber).card = ∑ y ∈ s, (fiber y).card :=
        Finset.card_biUnion h_disj
      exact Eq.trans (congr_arg Finset.card h_eq1) h_eq2
    have h_cast : (↑(∑ y ∈ Q0_phys.image f, (fiber y).card) : ℝ) = ∑ y ∈ Q0_phys.image f, ((fiber y).card : ℝ) := by
      rw [Nat.cast_sum]
    have h_sum : ∑ y ∈ Q0_phys.image f, ((fiber y).card : ℝ) ≤ ∑ y ∈ Q0_phys.image f, (K : ℝ) := by
      apply Finset.sum_le_sum; intro y _; exact h_fiber' y
    have h_sum2 : ∑ y ∈ Q0_phys.image f, (K : ℝ) = (K : ℝ) * (Q0_phys.image f).card := by
      simp [Finset.sum_const] <;> ring
    calc (Q0_phys.card : ℝ)
      = ↑(∑ y ∈ Q0_phys.image f, (fiber y).card) := by rw [h_card]
    _ = ∑ y ∈ Q0_phys.image f, ((fiber y).card : ℝ) := h_cast
    _ ≤ ∑ y ∈ Q0_phys.image f, (K : ℝ) := h_sum
    _ = (K : ℝ) * (Q0_phys.image f).card := h_sum2
  let Y' := hY_fin.toFinset
  have hY'_eq2 : (Y' : Set ℝ) = Y_phys := hY_fin.coe_toFinset
  have h9 : Y'.card = (Q0_phys.image f).card := by
    have h91 : (Y' : Set ℝ) = (Q0_phys.image f : Set ℝ) := by
      rw [hY'_eq2] <;> ext y; simp [Y_phys]
    have h92 : Y' = Q0_phys.image f := Finset.coe_inj.mp h91
    rw [h92]
  have h10 : (Q0_phys.card : ℝ) ≤ (K : ℝ) * (Y'.card : ℝ) := by
    have h101 : (Q0_phys.card : ℝ) ≤ (K : ℝ) * ((Q0_phys.image f).card : ℝ) := h_fiber_sum
    have h102 : ((Q0_phys.image f).card : ℝ) = (Y'.card : ℝ) := by exact_mod_cast h9.symm
    rw [h102] at h101; exact h101
  have h8 : ((Q0_phys : Set Plane).encard : ENNReal) ≤ ENNReal.ofReal (K : ℝ) * (Y_phys.encard : ENNReal) := by
    have h11 : ((Q0_phys : Set Plane).encard : ENNReal) = ENNReal.ofReal (Q0_phys.card : ℝ) := by simp
    have h12 : (Y_phys.encard : ENNReal) = ENNReal.ofReal (Y'.card : ℝ) := by
      have h121 : Y_phys.encard = Y'.card := by rw [←hY'_eq2]; simp
      exact_mod_cast h121
    rw [h11, h12]
    have h13 : ENNReal.ofReal (Q0_phys.card : ℝ) ≤ ENNReal.ofReal ((K : ℝ) * (Y'.card : ℝ)) :=
      ENNReal.ofReal_le_ofReal h10
    have h14 : ENNReal.ofReal ((K : ℝ) * (Y'.card : ℝ)) =
        ENNReal.ofReal (K : ℝ) * ENNReal.ofReal (Y'.card : ℝ) := by
      rw [ENNReal.ofReal_mul] <;> positivity
    rw [h14] at h13; exact h13
  have h10b : ((Q0_phys : Set Plane).encard : ENNReal) ≤
      ENNReal.ofReal (K : ℝ) * (3 * (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal)) := by
    calc ((Q0_phys : Set Plane).encard : ENNReal)
        ≤ ENNReal.ofReal (K : ℝ) * (Y_phys.encard : ENNReal) := h8
      _ ≤ ENNReal.ofReal (K : ℝ) * (3 * (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal)) := by
        gcongr <;> exact h_sep_lemma
  -- Projection S-set with exponent u
  have hY_sset_u : IsDeltaSSet Δ u C_proj Y_phys := by
    refine' ⟨hY_nonempty, hδ_pos, hC_proj_pos, hu_pos.le, _⟩
    intro y r hr
    rcases h_strip y r hr with ⟨c, hc_strip⟩
    have h_sub1 : Y_phys ∩ Metric.closedBall y r ⊆
        f '' ((Q0_phys : Set Plane) ∩ Metric.closedBall c (a * r)) := by
      intro z hz
      have hzY : z ∈ Y_phys := hz.1
      have hzball : |z - y| ≤ r := by simpa [Metric.mem_closedBall, Real.dist_eq] using hz.2
      rcases hzY with ⟨x, hxP, rfl⟩
      have hstrip : dist x c ≤ a * r := hc_strip x hxP (by simpa using hzball)
      exact ⟨x, ⟨hxP, by simpa [Metric.mem_closedBall] using hstrip⟩, rfl⟩
    have h_step1 : (Metric.externalCoveringNumber ε_nn (Y_phys ∩ Metric.closedBall y r) : ENNReal) ≤
        (Metric.externalCoveringNumber ε_nn (f '' ((Q0_phys : Set Plane) ∩ Metric.closedBall c (a * r))) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h_sub1
    have h_step2 : (Metric.externalCoveringNumber ε_nn (f '' ((Q0_phys : Set Plane) ∩ Metric.closedBall c (a * r))) : ENNReal) ≤
        (Metric.externalCoveringNumber ε_nn ((Q0_phys : Set Plane) ∩ Metric.closedBall c (a * r)) : ENNReal) := by
      exact_mod_cast local_externalCoveringNumber_image_lipschitz_one hf_lip
    have h_hr3 : Δ ≤ a * r := by
      have h1 : Δ ≤ r := hr
      have h2 : r ≤ a * r := by
        have h3 : 0 ≤ r := by linarith
        nlinarith [ha_one]
      linarith
    have h_step3 : (Metric.externalCoveringNumber ε_nn ((Q0_phys : Set Plane) ∩ Metric.closedBall c (a * r)) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (a * r)) ^ u *
        (Metric.externalCoveringNumber ε_nn (Q0_phys : Set Plane) : ENNReal) := hbound c (a * r) h_hr3
    have h_pow : (ENNReal.ofReal (a * r)) ^ u =
        ENNReal.ofReal (a^u) * (ENNReal.ofReal r) ^ u := by
      have h1 : ENNReal.ofReal (a * r) = ENNReal.ofReal a * ENNReal.ofReal r := by
        rw [ENNReal.ofReal_mul] <;> positivity
      rw [h1]
      have h2 : (ENNReal.ofReal a * ENNReal.ofReal r) ^ u =
          (ENNReal.ofReal a) ^ u * (ENNReal.ofReal r) ^ u := by
        rw [ENNReal.mul_rpow_of_nonneg] <;> positivity
      rw [h2]
      have h3 : (ENNReal.ofReal a) ^ u = ENNReal.ofReal (a^u) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg] <;> positivity
      rw [h3] <;> simp [mul_assoc]
    have h_cov_le_encard : (Metric.externalCoveringNumber ε_nn (Q0_phys : Set Plane) : ENNReal) ≤
        ((Q0_phys : Set Plane).encard : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_le_encard_self (Q0_phys : Set Plane)
    have hC_proj_def : ENNReal.ofReal C_proj =
        ENNReal.ofReal C * ENNReal.ofReal (a^u) * ENNReal.ofReal (K : ℝ) * 3 := by
      have h1 : C_proj = 3 * (K : ℝ) * C * a^u := by rfl
      rw [h1]
      have hpos1 : 0 ≤ (3 : ℝ) := by norm_num
      have hpos2 : 0 ≤ (K : ℝ) := by positivity
      have hpos3 : 0 ≤ C := by linarith [hC_pos]
      have hpos4 : 0 ≤ a^u := by positivity
      rw [ENNReal.ofReal_mul (show 0 ≤ (3 * (K : ℝ)) * C by positivity),
          ENNReal.ofReal_mul (show 0 ≤ 3 * (K : ℝ) by positivity),
          ENNReal.ofReal_mul hpos1]
      <;> simp [mul_assoc, mul_comm, mul_left_comm]
    calc (Metric.externalCoveringNumber ε_nn (Y_phys ∩ Metric.closedBall y r) : ENNReal)
      ≤ (Metric.externalCoveringNumber ε_nn (f '' ((Q0_phys : Set Plane) ∩ Metric.closedBall c (a * r))) : ENNReal) := h_step1
    _ ≤ (Metric.externalCoveringNumber ε_nn ((Q0_phys : Set Plane) ∩ Metric.closedBall c (a * r)) : ENNReal) := h_step2
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (a * r)) ^ u * (Metric.externalCoveringNumber ε_nn (Q0_phys : Set Plane) : ENNReal) := h_step3
    _ = ENNReal.ofReal C * ENNReal.ofReal (a^u) * (ENNReal.ofReal r) ^ u * (Metric.externalCoveringNumber ε_nn (Q0_phys : Set Plane) : ENNReal) := by
      rw [h_pow] <;> simp [mul_assoc]
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (a^u) * (ENNReal.ofReal r) ^ u * ((Q0_phys : Set Plane).encard : ENNReal) := by
      gcongr <;> exact h_cov_le_encard
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (a^u) * (ENNReal.ofReal r) ^ u * (ENNReal.ofReal (K : ℝ) * (3 * (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal))) := by
      gcongr <;> exact h10b
    _ = ENNReal.ofReal C_proj * (ENNReal.ofReal r) ^ u * (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal) := by
      rw [hC_proj_def]
      simp [mul_assoc, mul_comm, mul_left_comm]
  -- Weaken exponent u → τ for bounded Y
  have hY_bounded' : Y_phys ⊆ Set.Icc (-D) D := by
    rw [hY_eq]; exact hY_bounded
  have h_final : IsDeltaSSet Δ τ C_Y Y_phys := by
    rcases hY_sset_u with ⟨hY_ne, _, _, hτ_u, hbound_u⟩
    refine' ⟨hY_ne, hδ_pos, hC_Y_pos, hτ_pos.le, _⟩
    intro y r hr
    by_cases h_r_le_one : r ≤ 1
    · -- r ≤ 1: r^u ≤ r^τ
      have h1 : (ENNReal.ofReal r) ^ u ≤ (ENNReal.ofReal r) ^ τ := by
        have h41 : ENNReal.ofReal r ≤ 1 := by exact_mod_cast h_r_le_one
        have h42 : τ ≤ u := hτ_le_u
        exact ENNReal.rpow_le_rpow_of_exponent_ge h41 h42
      have h5 := hbound_u y r hr
      have h7 : 1 ≤ (2 * D)^(u - τ) := by
        have h8 : 1 ≤ 2 * D := by linarith [hD_ge_one]
        have h9 : 0 ≤ u - τ := by linarith
        exact Real.one_le_rpow h8 h9
      have h6 : C_proj ≤ C_Y := by
        dsimp only [C_proj, a]
        have h10 : 3 * (K : ℝ) * C * (61 : ℝ)^u ≤ 3 * (K : ℝ) * C * (61 : ℝ)^u * (2 * D)^(u - τ) := by
          have h11 : 0 < 3 * (K : ℝ) * C * (61 : ℝ)^u := by positivity
          nlinarith
        calc C_proj
          = 3 * (K : ℝ) * C * (61 : ℝ)^u := by rfl
        _ ≤ 3 * (K : ℝ) * C * (61 : ℝ)^u * (2 * D)^(u - τ) := h10
        _ ≤ C_Y := h_absorb
      calc (Metric.externalCoveringNumber ε_nn (Y_phys ∩ Metric.closedBall y r) : ENNReal)
        ≤ ENNReal.ofReal C_proj * (ENNReal.ofReal r) ^ u *
            (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal) := h5
      _ ≤ ENNReal.ofReal C_proj * (ENNReal.ofReal r) ^ τ *
            (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal) := by gcongr
      _ ≤ ENNReal.ofReal C_Y * (ENNReal.ofReal r) ^ τ *
            (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal) := by
        gcongr <;> exact_mod_cast h6
    · -- r > 1: use C_Y ≥ 1 and boundedness
      have h_r_gt_one : 1 < r := by linarith
      have h_sub : Y_phys ∩ Metric.closedBall y r ⊆ Y_phys := Set.inter_subset_left
      have h9 : (Metric.externalCoveringNumber ε_nn (Y_phys ∩ Metric.closedBall y r) : ENNReal) ≤
          (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal) := by
        exact_mod_cast Metric.externalCoveringNumber_mono_set h_sub
      have h10 : (1 : ENNReal) ≤ (ENNReal.ofReal r) ^ τ := by
        have h11 : 1 ≤ r := by linarith
        have h12 : (1 : ENNReal) ≤ ENNReal.ofReal r := by
          have h121 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal h11
          simpa using h121
        exact ENNReal.one_le_rpow h12 hτ_pos
      have h13 : (1 : ENNReal) ≤ ENNReal.ofReal C_Y := by
        have h131 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal C_Y := ENNReal.ofReal_le_ofReal hC_Y_ge_one
        simpa using h131
      have h14 : ENNReal.ofReal C_Y ≤ ENNReal.ofReal C_Y * (ENNReal.ofReal r) ^ τ := by
        have h141 : ENNReal.ofReal C_Y * (1 : ENNReal) ≤ ENNReal.ofReal C_Y * (ENNReal.ofReal r) ^ τ :=
          mul_le_mul_left' h10 (ENNReal.ofReal C_Y)
        simpa using h141
      have hA : (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal) ≤
          ENNReal.ofReal C_Y * (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal) := by
        have hA1 : (1 : ENNReal) * (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal) ≤
            ENNReal.ofReal C_Y * (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal) :=
          mul_le_mul_right' h13 (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal)
        simpa using hA1
      have hB : ENNReal.ofReal C_Y * (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal) ≤
          ENNReal.ofReal C_Y * (ENNReal.ofReal r) ^ τ * (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal) := by
        have hB2 : (ENNReal.ofReal C_Y) * (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal) ≤
            (ENNReal.ofReal C_Y * (ENNReal.ofReal r) ^ τ) * (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal) :=
          mul_le_mul_right' h14 (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal)
        simpa [mul_assoc] using hB2
      calc (Metric.externalCoveringNumber ε_nn (Y_phys ∩ Metric.closedBall y r) : ENNReal)
        ≤ (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal) := h9
      _ ≤ ENNReal.ofReal C_Y * (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal) := hA
      _ ≤ ENNReal.ofReal C_Y * (ENNReal.ofReal r) ^ τ * (Metric.externalCoveringNumber ε_nn Y_phys : ENNReal) := hB
  rw [hY_eq] at h_final
  exact h_final

end DirecretisedFurstenbergEstimate.AppendixA
