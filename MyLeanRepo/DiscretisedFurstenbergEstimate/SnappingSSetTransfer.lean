module

/-
  Snapping S-set transfer for AffineLine.

  Provides grid snapping of AffineLine via slope-intercept parameters,
  with fiber diameter bound and S-set property transfer.

  ## Main results
  - `affineLineSnap`: snap map via slope-intercept δ-grid
  - `affineLineSnap_near`: dist(ℓ, snap(ℓ)) = O(δ)
  - `affineLineSnap_fiber_diam`: fibers have diameter O(δ)
  - `affineLine_doubling`: covering_δ ≤ K_pack · covering_{2δ}
  - `affineLineSnap_covering_lower`: |snap(S)| ≥ covering_δ(S) / K_pack

  Whiteprint node: appendix_a_alternative / snapping_sset_transfer
  Dependencies: TubesAndSlopes, PackingBound, CoveringUtils
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineParams
public import MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate.Snapping

open TubesAndSlopes
open LemmaE
open MainAppendix
open DiscretisedFurstenbergEstimate.CoveringUtils

attribute [local instance] Classical.propDecidable

/-- The affine line packing constant is positive. -/
lemma affineLine_packing_constant_pos' : 0 < affineLine_packing_constant := by
  let ℓ : AffineLine := makeAffineLine 0 0
  have h := affineLine_packing_bound (1 : ℝ) (by norm_num) (S := {ℓ}) (by simp) ℓ (by simp)
  have h2 : ({ℓ} : Set AffineLine).encard = 1 := by simp
  rw [h2] at h
  have h3 : (1 : ENat) ≤ ↑affineLine_packing_constant := h.2
  exact_mod_cast h3

/-! ### Grid snapping in 1D -/

/-- Snap a real number to the δ-grid using floor. -/
noncomputable def gridSnap1D (δ : ℝ) (x : ℝ) : ℝ := δ * (⌊x / δ⌋ : ℝ)

lemma gridSnap1D_bound {δ : ℝ} (hδ_pos : 0 < δ) (x : ℝ) :
    |x - gridSnap1D δ x| < δ := by
  have h1 : (x / δ) - 1 < (⌊x / δ⌋ : ℝ) := Int.sub_one_lt_floor (x / δ)
  have h2 : (⌊x / δ⌋ : ℝ) ≤ x / δ := Int.floor_le (x / δ)
  have h3 : 0 ≤ x / δ - (⌊x / δ⌋ : ℝ) := by linarith
  have h4 : x / δ - (⌊x / δ⌋ : ℝ) < 1 := by linarith
  have h5 : x - gridSnap1D δ x = δ * (x / δ - (⌊x / δ⌋ : ℝ)) := by
    have h51 : gridSnap1D δ x = δ * (⌊x / δ⌋ : ℝ) := by rfl
    rw [h51]
    have h52 : δ * (x / δ) = x := by field_simp [hδ_pos.ne'] <;> ring
    linarith
  rw [h5]
  have h6 : 0 ≤ δ * (x / δ - (⌊x / δ⌋ : ℝ)) := mul_nonneg hδ_pos.le h3
  have h7 : δ * (x / δ - (⌊x / δ⌋ : ℝ)) < δ := by nlinarith
  rw [abs_of_nonneg h6]
  exact h7

lemma gridSnap1D_abs_le {δ : ℝ} (hδ_pos : 0 < δ) (x : ℝ) :
    |gridSnap1D δ x| ≤ |x| + δ := by
  have h1 : |x - gridSnap1D δ x| < δ := gridSnap1D_bound hδ_pos x
  have h2 : |gridSnap1D δ x| ≤ |x| + |x - gridSnap1D δ x| := by
    calc |gridSnap1D δ x|
      = |x - (x - gridSnap1D δ x)| := by ring_nf
    _ ≤ |x| + |x - gridSnap1D δ x| := by exact abs_sub _ _
  linarith

/-! ### AffineLine snapping map -/

/-- Snap an AffineLine to the δ-grid in slope-intercept parameter space. -/
noncomputable def affineLineSnap (δ : ℝ) (ℓ : AffineLine) : AffineLine :=
  let p := affineLineParams ℓ
  makeAffineLine (gridSnap1D δ p.1) (gridSnap1D δ p.2)

lemma affineLineSnap_params (δ : ℝ) (ℓ : AffineLine) :
    affineLineParams (affineLineSnap δ ℓ) =
      (gridSnap1D δ (affineLineParams ℓ).1, gridSnap1D δ (affineLineParams ℓ).2) := by
  dsimp only [affineLineSnap]
  let p := affineLineParams ℓ
  exact makeAffineLine_params (gridSnap1D δ p.1) (gridSnap1D δ p.2)

lemma affineLineSnap_v1 (δ : ℝ) (ℓ : AffineLine) :
    (getDirV (affineLineSnap δ ℓ)) 1 ≠ 0 := by
  dsimp only [affineLineSnap]
  let p := affineLineParams ℓ
  exact makeAffineLine_v1 (gridSnap1D δ p.1) (gridSnap1D δ p.2)

/-! ### Perturbation and fiber diameter bounds -/

/-- Distance from a line to its snap: dist(ℓ, snap(ℓ)) ≤ (3 + B + δ) · δ
    when |slope| ≤ 1, |intercept| ≤ B, and δ ≤ 1. -/
lemma affineLineSnap_near (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (ℓ : AffineLine) (B : ℝ) (hB_nonneg : 0 ≤ B)
    (hv1 : (getDirV ℓ) 1 ≠ 0)
    (h_slope : |(affineLineParams ℓ).1| ≤ 1)
    (h_intercept : |(affineLineParams ℓ).2| ≤ B) :
    AffineLine.dist ℓ (affineLineSnap δ ℓ) ≤ (3 + B + δ) * δ := by
  set a := (affineLineParams ℓ).1 with ha
  set b := (affineLineParams ℓ).2 with hb
  set a' := gridSnap1D δ a with ha'
  set b' := gridSnap1D δ b with hb'
  set ℓ' := affineLineSnap δ ℓ with hℓ'
  have h_params' : affineLineParams ℓ' = (a', b') := affineLineSnap_params δ ℓ
  have h1 : |a - a'| < δ := gridSnap1D_bound hδ_pos a
  have h2 : |b - b'| < δ := gridSnap1D_bound hδ_pos b
  have h3 : |b'| ≤ B + δ := by
    have h31 : |b'| ≤ |b| + δ := gridSnap1D_abs_le hδ_pos b
    linarith [h_intercept]
  have h3' : |(affineLineParams ℓ').2| ≤ B + δ := by
    rw [h_params'] <;> exact h3
  have h4 := dist_bound_general ℓ ℓ' hv1 (affineLineSnap_v1 δ ℓ) (show 0 ≤ B + δ by linarith) h3'
  have h_diff1 : (affineLineParams ℓ).1 - (affineLineParams ℓ').1 = a - a' := by
    simp [ha, ha', h_params'] <;> rfl
  have h_diff2 : (affineLineParams ℓ).2 - (affineLineParams ℓ').2 = b - b' := by
    simp [hb, hb', h_params'] <;> rfl
  rw [h_diff1, h_diff2] at h4
  have h4' : AffineLine.dist ℓ ℓ' ≤ (2 + B + δ) * |a - a'| + |b - b'| := by
    have h_eq : (2 + (B + δ)) = (2 + B + δ) := by ring
    rw [h_eq] at h4
    exact h4
  have h6 : (2 + B + δ) * |a - a'| + |b - b'| ≤ (3 + B + δ) * δ := by
    have h7 : (2 + B + δ) * |a - a'| ≤ (2 + B + δ) * δ := by gcongr <;> linarith
    have h8 : |b - b'| ≤ δ := by linarith [h2.le]
    linarith
  exact le_trans h4' h6

/-- Fiber diameter: if snap(ℓ₁) = snap(ℓ₂), then dist(ℓ₁, ℓ₂) ≤ (6 + 2B) · δ
    when both lines have |slope| ≤ 1, |intercept| ≤ B. -/
lemma affineLineSnap_fiber_diam (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (ℓ₁ ℓ₂ : AffineLine) (B : ℝ) (hB_nonneg : 0 ≤ B)
    (hv1₁ : (getDirV ℓ₁) 1 ≠ 0) (hv1₂ : (getDirV ℓ₂) 1 ≠ 0)
    (h_slope₁ : |(affineLineParams ℓ₁).1| ≤ 1)
    (h_slope₂ : |(affineLineParams ℓ₂).1| ≤ 1)
    (h_intercept₁ : |(affineLineParams ℓ₁).2| ≤ B)
    (h_intercept₂ : |(affineLineParams ℓ₂).2| ≤ B)
    (h_snap_eq : affineLineSnap δ ℓ₁ = affineLineSnap δ ℓ₂) :
    AffineLine.dist ℓ₁ ℓ₂ ≤ (6 + 2 * B) * δ := by
  set a1 := (affineLineParams ℓ₁).1 with ha1
  set b1 := (affineLineParams ℓ₁).2 with hb1
  set a2 := (affineLineParams ℓ₂).1 with ha2
  set b2 := (affineLineParams ℓ₂).2 with hb2
  set a1' := gridSnap1D δ a1 with ha1'
  set b1' := gridSnap1D δ b1 with hb1'
  set a2' := gridSnap1D δ a2 with ha2'
  set b2' := gridSnap1D δ b2 with hb2'
  have h_params1 : affineLineParams (affineLineSnap δ ℓ₁) = (a1', b1') :=
    affineLineSnap_params δ ℓ₁
  have h_params2 : affineLineParams (affineLineSnap δ ℓ₂) = (a2', b2') :=
    affineLineSnap_params δ ℓ₂
  have h_eq_params : affineLineParams (affineLineSnap δ ℓ₁) =
      affineLineParams (affineLineSnap δ ℓ₂) := by rw [h_snap_eq]
  have ha'_eq : a1' = a2' := by
    rw [h_params1, h_params2] at h_eq_params
    exact congr_arg Prod.fst h_eq_params
  have hb'_eq : b1' = b2' := by
    rw [h_params1, h_params2] at h_eq_params
    exact congr_arg Prod.snd h_eq_params
  have h1 : |a1 - a2| < 2 * δ := by
    have h11 : |a1 - a1'| < δ := gridSnap1D_bound hδ_pos a1
    have h12 : |a2 - a2'| < δ := gridSnap1D_bound hδ_pos a2
    have h_eq : a1 - a2 = (a1 - a1') + (a1' - a2) := by ring
    have h_tri : |a1 - a2| ≤ |a1 - a1'| + |a1' - a2| := by
      rw [h_eq]
      exact abs_add_le (a1 - a1') (a1' - a2)
    have h_comm : |a1' - a2| = |a2 - a1'| := by
      rw [show a1' = a2' from ha'_eq]
      <;> rw [abs_sub_comm]
    have h_strict : |a1 - a1'| + |a2 - a2'| < 2 * δ := by linarith
    have h_final : |a1 - a2| < 2 * δ := by
      calc |a1 - a2|
        ≤ |a1 - a1'| + |a1' - a2| := h_tri
      _ = |a1 - a1'| + |a2 - a1'| := by rw [h_comm]
      _ = |a1 - a1'| + |a2 - a2'| := by rw [show a1' = a2' from ha'_eq]
      _ < 2 * δ := h_strict
    exact h_final
  have h2 : |b1 - b2| < 2 * δ := by
    have h21 : |b1 - b1'| < δ := gridSnap1D_bound hδ_pos b1
    have h22 : |b2 - b2'| < δ := gridSnap1D_bound hδ_pos b2
    have h_eq : b1 - b2 = (b1 - b1') + (b1' - b2) := by ring
    have h_tri : |b1 - b2| ≤ |b1 - b1'| + |b1' - b2| := by
      rw [h_eq]
      exact abs_add_le (b1 - b1') (b1' - b2)
    have h_comm : |b1' - b2| = |b2 - b1'| := by
      rw [show b1' = b2' from hb'_eq]
      <;> rw [abs_sub_comm]
    have h_strict : |b1 - b1'| + |b2 - b2'| < 2 * δ := by linarith
    have h_final : |b1 - b2| < 2 * δ := by
      calc |b1 - b2|
        ≤ |b1 - b1'| + |b1' - b2| := h_tri
      _ = |b1 - b1'| + |b2 - b1'| := by rw [h_comm]
      _ = |b1 - b1'| + |b2 - b2'| := by rw [show b1' = b2' from hb'_eq]
      _ < 2 * δ := h_strict
    exact h_final
  have h3 : |b2| ≤ B := h_intercept₂
  have h4 := dist_bound_general ℓ₁ ℓ₂ hv1₁ hv1₂ hB_nonneg h3
  have h5 : AffineLine.dist ℓ₁ ℓ₂ ≤ (2 + B) * |a1 - a2| + |b1 - b2| := h4
  have h6 : (2 + B) * |a1 - a2| + |b1 - b2| ≤ (2 + B) * (2 * δ) + 2 * δ := by
    have h7 : (2 + B) * |a1 - a2| ≤ (2 + B) * (2 * δ) := by gcongr <;> linarith [h1.le]
    have h8 : |b1 - b2| ≤ 2 * δ := by linarith [h2.le]
    linarith
  have h10 : (2 + B) * (2 * δ) + 2 * δ = (6 + 2 * B) * δ := by
    ring
  rw [h10] at h6
  exact le_trans h5 h6

/-! ### Doubling bound for AffineLine -/

/-- Any subset of a 2δ-ball can be δ-covered by at most K_pack points. -/
lemma bounded_set_delta_cover (δ : ℝ) (hδ_pos : 0 < δ)
    {T : Set AffineLine} {c : AffineLine} (hT : T ⊆ Metric.closedBall c (2 * δ)) :
    ∃ (Q : Finset AffineLine), (Q : Set AffineLine) ⊆ T ∧
      Set.Pairwise (Q : Set AffineLine) (fun x y => δ ≤ dist x y) ∧
      Q.card ≤ affineLine_packing_constant ∧
      Metric.IsCover δ.toNNReal T (Q : Set AffineLine) := by
  let K : ℕ := affineLine_packing_constant
  let P : Finset AffineLine → Prop := fun Q =>
    (Q : Set AffineLine) ⊆ T ∧ Set.Pairwise (Q : Set AffineLine) (fun x y => δ ≤ dist x y)
  have h0 : P (∅ : Finset AffineLine) := by
    simp [P] <;> tauto
  have h_card_bound : ∀ (Q : Finset AffineLine), P Q → Q.card ≤ K := by
    intro Q hQ
    have hQ_sub : (Q : Set AffineLine) ⊆ T := hQ.1
    have hQ_sep : Set.Pairwise (Q : Set AffineLine) (fun x y => δ ≤ dist x y) := hQ.2
    have hQ_in_ball : (Q : Set AffineLine) ⊆ Metric.closedBall c (2 * δ) :=
      Set.Subset.trans hQ_sub hT
    have h := affineLine_packing_bound δ hδ_pos hQ_sep c hQ_in_ball
    exact_mod_cast h.2
  let P' : ℕ → Prop := fun k => ∃ (Q : Finset AffineLine), P Q ∧ Q.card = K - k
  have hP'_nonempty : ∃ k, P' k := by
    refine ⟨K, ?_⟩
    refine ⟨(∅ : Finset AffineLine), h0, ?_⟩
    simp
  let k_min : ℕ := Nat.find hP'_nonempty
  have hP'_kmin : P' k_min := Nat.find_spec hP'_nonempty
  let m : ℕ := K - k_min
  rcases hP'_kmin with ⟨Q₀, hPQ₀, hQ₀_card⟩
  have hQ₀_sub : (Q₀ : Set AffineLine) ⊆ T := hPQ₀.1
  have hQ₀_sep : Set.Pairwise (Q₀ : Set AffineLine) (fun x y => δ ≤ dist x y) := hPQ₀.2
  have hQ₀_card_le : Q₀.card ≤ K := h_card_bound Q₀ hPQ₀
  have hP'_K : P' K := by
    refine ⟨(∅ : Finset AffineLine), h0, ?_⟩
    simp
  have h_kmin_le_K : k_min ≤ K := Nat.find_min' hP'_nonempty hP'_K
  have h_cover : Metric.IsCover δ.toNNReal T (Q₀ : Set AffineLine) := by
    intro t ht
    by_cases h : ∃ (q : AffineLine), q ∈ (Q₀ : Set AffineLine) ∧ edist t q ≤ ↑δ.toNNReal
    · exact h
    · have h' : ∀ (q : AffineLine), q ∈ (Q₀ : Set AffineLine) → dist t q > δ := by
        intro q hq
        have h2 : ¬(edist t q ≤ ↑δ.toNNReal) := by
          intro h3
          exact h ⟨q, hq, h3⟩
        have h3 : edist t q > ↑δ.toNNReal := by exact Std.not_le.mp h2
        have h_edist_eq : edist t q = ENNReal.ofReal (dist t q) := by
          rw [edist_dist] <;> rfl
        have h_toNNReal_eq : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by
          have h_pos : 0 ≤ δ := by linarith
          have h : (δ.toNNReal : ℝ) = δ := by
            simp [NNReal.coe_mk, h_pos] <;> linarith
          have h2 : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal (↑δ.toNNReal : ℝ) := by
            exact Eq.symm ENNReal.ofReal_coe_nnreal
          rw [h2, h]
        rw [h_edist_eq, h_toNNReal_eq] at h3
        have h_pos : 0 ≤ dist t q := dist_nonneg
        have h_ne_zero : dist t q ≠ 0 := by
          intro h_eq
          rw [h_eq] at h3
          simp at h3 <;> exact h3
        have h4 : 0 < dist t q := by
          exact lt_of_le_of_ne h_pos h_ne_zero.symm
        exact (ENNReal.ofReal_lt_ofReal_iff h4).mp h3
      have h_t_in_ball : t ∈ Metric.closedBall c (2 * δ) := hT ht
      have h_t_notin : t ∉ (Q₀ : Set AffineLine) := by
        intro htin
        have h9 : dist t t ≤ δ := by
          rw [dist_self]
          <;> linarith [hδ_pos]
        exact not_lt.mpr h9 (h' t htin)
      let Q₁ : Finset AffineLine := insert t Q₀
      have hQ₁_sub : (Q₁ : Set AffineLine) ⊆ T := by
        intro x hx
        have h_xin : x = t ∨ x ∈ (Q₀ : Set AffineLine) := by
          simpa [Q₁, Finset.mem_insert] using hx
        rcases h_xin with (rfl | hx)
        · exact ht
        · exact hQ₀_sub hx
      have hQ₁_sep : Set.Pairwise (Q₁ : Set AffineLine) (fun x y => δ ≤ dist x y) := by
        intro x hx y hy hne
        have h_xin : x = t ∨ x ∈ (Q₀ : Set AffineLine) := by simpa [Q₁, Finset.mem_insert] using hx
        have h_yin : y = t ∨ y ∈ (Q₀ : Set AffineLine) := by simpa [Q₁, Finset.mem_insert] using hy
        by_cases hxt : x = t
        · by_cases hyt : y = t
          · exfalso; exact hne (by rw [hxt, hyt])
          · have hy' : y ∈ (Q₀ : Set AffineLine) := by tauto
            have h_gt : dist t y > δ := h' y hy'
            have h_eq : x = t := hxt
            rw [h_eq]
            exact le_of_lt h_gt
        · have hx' : x ∈ (Q₀ : Set AffineLine) := by tauto
          by_cases hyt : y = t
          · have h_gt : dist t x > δ := h' x hx'
            have h_comm : dist x t = dist t x := dist_comm x t
            have h_y_eq : y = t := hyt
            rw [h_y_eq]
            exact le_of_lt (by rw [h_comm]; exact h_gt)
          · have hy' : y ∈ (Q₀ : Set AffineLine) := by tauto
            exact hQ₀_sep hx' hy' hne
      have h_t_notin' : t ∉ Q₀ := h_t_notin
      have hQ₁_card : Q₁.card = Q₀.card + 1 := by
        have h : Q₁ = insert t Q₀ := by rfl
        rw [h]
        exact Finset.card_insert_of_notMem h_t_notin
      have hPQ₁ : P Q₁ := ⟨hQ₁_sub, hQ₁_sep⟩
      have hQ₁_bound : Q₁.card ≤ K := h_card_bound Q₁ hPQ₁
      by_cases h_kmin_zero : k_min = 0
      · rw [hQ₁_card] at hQ₁_bound
        rw [hQ₀_card, h_kmin_zero] at hQ₁_bound
        <;> omega
      · have h_kmin_pos : 0 < k_min := by omega
        have h_kmin_pred : k_min - 1 < k_min := by omega
        have hQ₁_card_eq : Q₁.card = K - (k_min - 1) := by
          rw [hQ₁_card, hQ₀_card] <;> omega
        have hP'_pred : P' (k_min - 1) := ⟨Q₁, hPQ₁, hQ₁_card_eq⟩
        exfalso
        exact Nat.find_min hP'_nonempty h_kmin_pred hP'_pred
  exact ⟨Q₀, hQ₀_sub, hQ₀_sep, hQ₀_card_le, h_cover⟩

/-- Doubling: covering_δ(S) ≤ K_pack · covering_{2δ}(S) for AffineLine. -/
lemma affineLine_doubling (δ : ℝ) (hδ_pos : 0 < δ) {S : Set AffineLine}
    (hcov : Metric.externalCoveringNumber (2 * δ).toNNReal S < ⊤) :
    Metric.externalCoveringNumber δ.toNNReal S ≤
      (affineLine_packing_constant : ENNReal) *
        Metric.externalCoveringNumber (2 * δ).toNNReal S := by
  rcases exists_external_cover_eq hcov with ⟨C, hCcover, hC_eq⟩
  have hC_fin : C.Finite := by
    have h_lt : C.encard < ⊤ := by rw [hC_eq]; exact hcov
    exact Set.encard_lt_top_iff.mp h_lt
  let C' : Finset AffineLine := hC_fin.toFinset
  have hC'_eq : (C' : Set AffineLine) = C := hC_fin.coe_toFinset
  let Q_c : AffineLine → Finset AffineLine := fun c =>
    if hc : c ∈ C' then
      Classical.choose (bounded_set_delta_cover δ hδ_pos
        (show (S ∩ Metric.closedBall c (2 * δ)) ⊆ Metric.closedBall c (2 * δ) from Set.inter_subset_right))
    else ∅
  have hQc_spec : ∀ (c : AffineLine), c ∈ C' →
      ((Q_c c : Set AffineLine) ⊆ S ∩ Metric.closedBall c (2 * δ) ∧
       (Q_c c).card ≤ affineLine_packing_constant ∧
       Metric.IsCover δ.toNNReal (S ∩ Metric.closedBall c (2 * δ)) (Q_c c : Set AffineLine)) := by
    intro c hc
    dsimp only [Q_c]
    rw [dif_pos hc]
    have h_full := Classical.choose_spec (bounded_set_delta_cover δ hδ_pos
      (show (S ∩ Metric.closedBall c (2 * δ)) ⊆ Metric.closedBall c (2 * δ) from Set.inter_subset_right))
    exact ⟨h_full.1, h_full.2.2.1, h_full.2.2.2⟩
  let Q_all : Finset AffineLine := C'.biUnion (fun c => Q_c c)
  have h_cover : Metric.IsCover δ.toNNReal S (Q_all : Set AffineLine) := by
    intro s hs
    have h10 : ∃ (c : AffineLine), c ∈ C ∧ edist s c ≤ ↑(2 * δ).toNNReal := hCcover hs
    rcases h10 with ⟨c, hc, hed⟩
    have hc' : c ∈ (C' : Set AffineLine) := by rw [hC'_eq] <;> exact hc
    have hdist : dist s c ≤ 2 * δ := by
      rw [edist_dist] at hed
      have h_eq : (↑(2 * δ).toNNReal : ENNReal) = ENNReal.ofReal (2 * δ) := by exact ENNReal.ofNNReal_toNNReal (2 * δ)
      rw [h_eq] at hed
      have h_nonneg : 0 ≤ dist s c := dist_nonneg
      have h_edist' : ENNReal.ofReal (dist s c) ≤ ENNReal.ofReal (2 * δ) := by
        simpa [edist_dist, h_nonneg] using hed
      exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp h_edist'
    have h_s_in_Tc : s ∈ S ∩ Metric.closedBall c (2 * δ) := ⟨hs, Metric.mem_closedBall.mpr hdist⟩
    have hspec := hQc_spec c hc'
    have h11 : ∃ (q : AffineLine), q ∈ (Q_c c : Set AffineLine) ∧ edist s q ≤ ↑δ.toNNReal :=
      hspec.2.2 h_s_in_Tc
    rcases h11 with ⟨q, hq_in, hq_edist⟩
    have hq_in_Qall : q ∈ Q_all := Finset.mem_biUnion.mpr ⟨c, hc', hq_in⟩
    exact ⟨q, hq_in_Qall, hq_edist⟩
  have h1 : Metric.externalCoveringNumber δ.toNNReal S ≤ (Q_all : Set AffineLine).encard :=
    Metric.IsCover.externalCoveringNumber_le_encard h_cover
  have h1' : (Q_all : Set AffineLine).encard = ↑Q_all.card := by simp
  have h2 : Q_all.card ≤ C'.card * affineLine_packing_constant := by
    calc Q_all.card
      ≤ ∑ c ∈ C', (Q_c c).card := Finset.card_biUnion_le
    _ ≤ ∑ c ∈ C', affineLine_packing_constant :=
      Finset.sum_le_sum (fun c hc => (hQc_spec c hc).2.1)
    _ = C'.card * affineLine_packing_constant := by simp [Finset.sum_const] <;> ring
  have hCcard : (C.encard : ENNReal) = ↑C'.card := by
    have h9 : C.encard = ↑C.ncard := Set.Finite.encard_eq_coe hC_fin
    have hC_ncard : C.ncard = C'.card := by
      have h_coe_C : (C' : Set _) = C := hC_fin.coe_toFinset
      have h : C.ncard = ((C' : Set AffineLine)).ncard := by rw [h_coe_C]
      rw [h] <;> simp
    rw [h9, hC_ncard] <;> rfl
  rw [hC_eq] at hCcard
  have h1_enn : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤ ↑((Q_all : Set AffineLine).encard) := by
    exact ENat.toENNReal_le.mpr h1
  have h1_cast : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤ ↑Q_all.card := by
    have h_eq : (↑((Q_all : Set AffineLine).encard) : ENNReal) = ↑Q_all.card := by
      have h2 : (Q_all : Set AffineLine).encard = ↑Q_all.card := h1'
      rw [h2]
      <;> simp
    rw [h_eq] at h1_enn
    exact h1_enn
  calc (Metric.externalCoveringNumber δ.toNNReal S : ENNReal)
    ≤ ↑Q_all.card := h1_cast
  _ ≤ ↑(C'.card * affineLine_packing_constant) := by exact_mod_cast h2
  _ = (affineLine_packing_constant : ENNReal) * (Metric.externalCoveringNumber (2 * δ).toNNReal S) := by
    rw [hCcard] <;> simp [mul_comm] <;> ring

/-- Iterated doubling: covering_δ(S) ≤ K_pack^k · covering_{2^k·δ}(S).
    No finiteness assumption needed. -/
lemma affineLine_doubling_iter (δ : ℝ) (hδ_pos : 0 < δ) (k : ℕ)
    {S : Set AffineLine} :
    Metric.externalCoveringNumber δ.toNNReal S ≤
      (affineLine_packing_constant : ENNReal)^k *
        Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal S := by
  induction k with
  | zero =>
    simpa using le_refl _
  | succ k ih =>
    set δ' : ℝ := ((2^k : ℕ) : ℝ) * δ with hδ'_def
    have hδ'_pos : 0 < δ' := by positivity
    have h_eq2 : 2 * δ' = ((2^(k+1) : ℕ) : ℝ) * δ := by
      simp [hδ'_def, pow_succ] <;> ring
    by_cases hcov : Metric.externalCoveringNumber (2 * δ').toNNReal S < ⊤
    · have h_step : Metric.externalCoveringNumber δ'.toNNReal S ≤
          (affineLine_packing_constant : ENNReal) * Metric.externalCoveringNumber (2 * δ').toNNReal S :=
        affineLine_doubling δ' hδ'_pos hcov
      calc Metric.externalCoveringNumber δ.toNNReal S
        ≤ (affineLine_packing_constant : ENNReal)^k * Metric.externalCoveringNumber δ'.toNNReal S := ih
      _ ≤ (affineLine_packing_constant : ENNReal)^k *
            ((affineLine_packing_constant : ENNReal) * Metric.externalCoveringNumber (2 * δ').toNNReal S) := by
          gcongr <;> exact h_step
      _ = (affineLine_packing_constant : ENNReal)^(k+1) *
            Metric.externalCoveringNumber (2 * δ').toNNReal S := by
          simp [pow_succ] <;> ring
      _ = (affineLine_packing_constant : ENNReal)^(k+1) *
            Metric.externalCoveringNumber (((2^(k+1) : ℕ) : ℝ) * δ).toNNReal S := by
          congr 1
          <;> rw [h_eq2]
    · have h_top : Metric.externalCoveringNumber (2 * δ').toNNReal S = ⊤ := by
        simpa [not_lt] using hcov
      have h_goal : Metric.externalCoveringNumber (((2^(k+1) : ℕ) : ℝ) * δ).toNNReal S = ⊤ := by
        have h_eq4 : ((2^(k+1) : ℕ) : ℝ) * δ = 2 * δ' := by
          simp [hδ'_def, pow_succ] <;> ring
        have h_eq3 : (((2^(k+1) : ℕ) : ℝ) * δ).toNNReal = (2 * δ').toNNReal := by
          rw [h_eq4]
        rw [h_eq3]
        exact h_top
      have h_rhs_top : (affineLine_packing_constant : ENNReal)^(k+1) *
          Metric.externalCoveringNumber (((2^(k+1) : ℕ) : ℝ) * δ).toNNReal S = (⊤ : ENNReal) := by
        rw [h_goal]
        have hK_nat_pos : 0 < affineLine_packing_constant := affineLine_packing_constant_pos'
        have hK_pos : 0 < (affineLine_packing_constant : ENNReal) := by exact_mod_cast hK_nat_pos
        have hK_ne_zero : (affineLine_packing_constant : ENNReal)^(k+1) ≠ 0 :=
          pow_ne_zero (k+1) hK_pos.ne'
        exact ENNReal.mul_top hK_ne_zero
      exact le_top.trans h_rhs_top.symm.le

/-- If S is δ-separated and contained in a ball of radius R ≤ 2^k·δ,
    then |S| ≤ K_pack^(k+1). -/
lemma separated_set_large_ball_bound (δ : ℝ) (hδ_pos : 0 < δ)
    {S : Finset AffineLine}
    (hS_sep : Set.Pairwise (S : Set AffineLine) (fun x y => δ ≤ dist x y))
    (z : AffineLine) (R : ℝ) (hR_pos : 0 < R)
    (hS_sub : (S : Set AffineLine) ⊆ Metric.closedBall z R)
    (k : ℕ) (hk : R ≤ ((2^k : ℕ) : ℝ) * δ) :
    S.card ≤ affineLine_packing_constant ^ (k + 1) := by
  let δnn : NNReal := δ.toNNReal
  have hδnn : (δnn : ℝ) = δ := Real.coe_toNNReal δ hδ_pos.le
  have h_cov_large : Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal (S : Set AffineLine) ≤ 1 := by
    have h1 : Metric.IsCover (((2^k : ℕ) : ℝ) * δ).toNNReal (S : Set AffineLine) {z} := by
      intro x hx
      have h2 : x ∈ Metric.closedBall z R := hS_sub hx
      have h3 : dist x z ≤ R := (Metric.mem_closedBall).mp h2
      have h4 : dist x z ≤ ((2^k : ℕ) : ℝ) * δ := le_trans h3 hk
      have h5 : edist x z ≤ ↑(((2^k : ℕ) : ℝ) * δ).toNNReal := by
        rw [edist_dist]
        have h6 : 0 ≤ dist x z := dist_nonneg
        exact ENNReal.ofReal_le_ofReal (by linarith)
      exact ⟨z, by simp, h5⟩
    have h7 : Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal (S : Set AffineLine) ≤ ({z} : Set AffineLine).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard h1
    simpa using h7
  have h_cov_top : Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal (S : Set AffineLine) < ⊤ :=
    lt_of_le_of_lt h_cov_large (by simp)
  have h_doub := affineLine_doubling_iter δ hδ_pos k (S := (S : Set AffineLine))
  have h_cov_small : Metric.externalCoveringNumber δnn (S : Set AffineLine) ≤ (affineLine_packing_constant : ENNReal)^k := by
    calc Metric.externalCoveringNumber δnn (S : Set AffineLine)
      ≤ (affineLine_packing_constant : ENNReal)^k *
          Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal (S : Set AffineLine) := h_doub
    _ ≤ (affineLine_packing_constant : ENNReal)^k * 1 := by
      gcongr
      exact_mod_cast h_cov_large
    _ = (affineLine_packing_constant : ENNReal)^k := by simp
  have h_pack'' : ∀ (z' : AffineLine) (T : Set AffineLine),
      Set.Pairwise T (fun x y => (δnn : ℝ) ≤ dist x y) →
      T ⊆ Metric.closedBall z' (2 * (δnn : ℝ)) →
      T.Finite ∧ T.encard ≤ (affineLine_packing_constant : ENat) := by
    intro z' T hT_sep hT_sub
    have hT_sep' : Set.Pairwise T (fun x y => δ ≤ dist x y) := by
      simpa [hδnn] using hT_sep
    have hT_sub' : T ⊆ Metric.closedBall z' (2 * δ) := by
      simpa [hδnn] using hT_sub
    exact affineLine_packing_bound δ hδ_pos hT_sep' z' hT_sub'
  have h_cov_small_top : (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) < ⊤ := by
    calc (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal)
      ≤ (affineLine_packing_constant : ENNReal)^k := h_cov_small
    _ < ⊤ := by
      have h_lt_top : (affineLine_packing_constant : ENNReal) < ⊤ :=
        (ENNReal.natCast_ne_top affineLine_packing_constant).lt_top
      exact ENNReal.pow_lt_top h_lt_top
  have h_card : ((S : Set AffineLine).encard : ENNReal) ≤
      (affineLine_packing_constant : ENNReal) * Metric.externalCoveringNumber δnn (S : Set AffineLine) :=
    separated_set_card_le_covering (δ := δnn) (by simpa [hδnn] using hS_sep)
      affineLine_packing_constant h_pack'' h_cov_small_top
  have h_main : ((S : Set AffineLine).encard : ENNReal) ≤ (affineLine_packing_constant : ENNReal)^(k + 1) := by
    calc ((S : Set AffineLine).encard : ENNReal)
      ≤ (affineLine_packing_constant : ENNReal) * Metric.externalCoveringNumber δnn (S : Set AffineLine) := h_card
    _ ≤ (affineLine_packing_constant : ENNReal) * (affineLine_packing_constant : ENNReal)^k := by gcongr
    _ = (affineLine_packing_constant : ENNReal)^(k + 1) := by
      simp [pow_succ] <;> ring
  have h_encard : (S : Set AffineLine).encard = ↑S.card := by simp
  rw [h_encard] at h_main
  exact_mod_cast h_main

/-! ### Lemma A: Covering lower bound via snapping -/

/-- If S is δ-separated, then |snap(S)| ≥ |S| / K_pack^(k+1),
    where k satisfies 6 + 2B ≤ 2^k. Each snap fiber has diameter (6+2B)·δ,
    so it contains at most K_pack^(k+1) δ-separated points. -/
lemma affineLineSnap_covering_lower (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    {S : Finset AffineLine}
    (hS_sep : Set.Pairwise (S : Set AffineLine) (fun x y => δ ≤ dist x y))
    (B : ℝ) (hB_nonneg : 0 ≤ B)
    (k : ℕ) (hk : (6 + 2 * B) ≤ ((2^k : ℕ) : ℝ))
    (h_slope : ∀ ℓ ∈ S, |(affineLineParams ℓ).1| ≤ 1)
    (h_intercept : ∀ ℓ ∈ S, |(affineLineParams ℓ).2| ≤ B)
    (h_v1 : ∀ ℓ ∈ S, (getDirV ℓ) 1 ≠ 0) :
    (S.card : ENNReal) ≤ (affineLine_packing_constant : ENNReal)^(k + 1) *
        (Finset.image (affineLineSnap δ) S).card := by
  let Q : Finset AffineLine := Finset.image (affineLineSnap δ) S
  have h_fiber_bound : ∀ q ∈ Q,
      (S.filter (fun ℓ => affineLineSnap δ ℓ = q)).card ≤ affineLine_packing_constant ^ (k + 1) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨ℓ₀, hℓ₀, rfl⟩
    let F : Finset AffineLine := S.filter (fun ℓ => affineLineSnap δ ℓ = affineLineSnap δ ℓ₀)
    have hF_sub : (F : Set AffineLine) ⊆ (S : Set AffineLine) := by
      intro x hx; exact (Finset.mem_filter.mp hx).1
    have hF_sep : Set.Pairwise (F : Set AffineLine) (fun x y => δ ≤ dist x y) :=
      hS_sep.mono hF_sub
    have hF_diam : ∀ ℓ₁ ∈ F, ∀ ℓ₂ ∈ F,
        AffineLine.dist ℓ₁ ℓ₂ ≤ (6 + 2 * B) * δ := by
      intro ℓ₁ hℓ₁ ℓ₂ hℓ₂
      have h_eq1 : affineLineSnap δ ℓ₁ = affineLineSnap δ ℓ₀ :=
        (Finset.mem_filter.mp hℓ₁).2
      have h_eq2 : affineLineSnap δ ℓ₂ = affineLineSnap δ ℓ₀ :=
        (Finset.mem_filter.mp hℓ₂).2
      have h_eq : affineLineSnap δ ℓ₁ = affineLineSnap δ ℓ₂ := by
        rw [h_eq1, h_eq2]
      exact affineLineSnap_fiber_diam δ hδ_pos hδ_le_one ℓ₁ ℓ₂ B hB_nonneg
        (h_v1 ℓ₁ (hF_sub hℓ₁)) (h_v1 ℓ₂ (hF_sub hℓ₂))
        (h_slope ℓ₁ (hF_sub hℓ₁)) (h_slope ℓ₂ (hF_sub hℓ₂))
        (h_intercept ℓ₁ (hF_sub hℓ₁)) (h_intercept ℓ₂ (hF_sub hℓ₂))
        h_eq
    by_cases hF_empty : F = ∅
    · have h_goal : F.card = 0 := by
        rw [hF_empty] <;> simp
      rw [h_goal] <;> positivity
    · have h_ne : F ≠ ∅ := hF_empty
      have hF_nonempty : (F : Set AffineLine).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr h_ne
      rcases hF_nonempty with ⟨ℓ₁, hℓ₁⟩
      have hF_in_ball : (F : Set AffineLine) ⊆ Metric.closedBall ℓ₁ ((6 + 2 * B) * δ) := by
        intro ℓ₂ hℓ₂
        have h_dist' : dist ℓ₂ ℓ₁ ≤ (6 + 2 * B) * δ := by
          have h_dist : AffineLine.dist ℓ₁ ℓ₂ ≤ (6 + 2 * B) * δ := hF_diam ℓ₁ hℓ₁ ℓ₂ hℓ₂
          rw [dist_comm] at *
          exact h_dist
        exact Metric.mem_closedBall.mpr h_dist'
      have hR_pos : 0 < (6 + 2 * B) * δ := by positivity
      exact separated_set_large_ball_bound δ hδ_pos hF_sep ℓ₁ ((6 + 2 * B) * δ) hR_pos hF_in_ball k
        (by gcongr)
  have hS_card_le : S.card ≤ Q.card * affineLine_packing_constant ^ (k + 1) := by
    have h_disj : ∀ q1 ∈ Q, ∀ q2 ∈ Q, q1 ≠ q2 →
        Disjoint (S.filter (fun ℓ => affineLineSnap δ ℓ = q1))
          (S.filter (fun ℓ => affineLineSnap δ ℓ = q2)) := by
      intro q1 _ q2 _ hne
      simp only [Finset.disjoint_left, Finset.mem_filter]
      intro ℓ h1 h2
      have h_eq1 : affineLineSnap δ ℓ = q1 := h1.2
      have h_eq2 : affineLineSnap δ ℓ = q2 := h2.2
      rw [h_eq1] at h_eq2
      exact hne h_eq2
    have h_bunion : Q.biUnion (fun q => S.filter (fun ℓ => affineLineSnap δ ℓ = q)) = S := by
      ext ℓ
      simp only [Finset.mem_biUnion, Finset.mem_filter, Q, Finset.mem_image]
      constructor
      · rintro ⟨q, _, hℓ, _⟩
        exact hℓ
      · intro hℓ
        refine ⟨affineLineSnap δ ℓ, ⟨ℓ, hℓ, rfl⟩, hℓ, rfl⟩
    have h : S.card = ∑ q ∈ Q, (S.filter (fun ℓ => affineLineSnap δ ℓ = q)).card := by
      rw [← Finset.card_biUnion h_disj, h_bunion]
    rw [h]
    calc ∑ q ∈ Q, (S.filter (fun ℓ => affineLineSnap δ ℓ = q)).card
      ≤ ∑ q ∈ Q, affineLine_packing_constant ^ (k + 1) :=
        Finset.sum_le_sum (fun q hq => h_fiber_bound q hq)
    _ = Q.card * affineLine_packing_constant ^ (k + 1) := by simp [Finset.sum_const] <;> ring
  have h_main : (S.card : ENNReal) ≤
      (affineLine_packing_constant : ENNReal)^(k + 1) * (Q.card : ENNReal) := by
    have h_comm : Q.card * affineLine_packing_constant ^ (k + 1) =
        affineLine_packing_constant ^ (k + 1) * Q.card := by ring
    rw [h_comm] at hS_card_le
    exact_mod_cast hS_card_le
  exact h_main

/-! ### Near-incidence preservation under snapping -/

/-- A point q lies on `makeAffineLine a b` iff q 0 = a * q 1 + b. -/
lemma makeAffineLine_iff (a b : ℝ) (q : EuclideanPlane) :
    q ∈ (makeAffineLine a b).1 ↔ q 0 = a * q 1 + b := by
  constructor
  · intro hq
    have h_params : affineLineParams (makeAffineLine a b) = (a, b) := makeAffineLine_params a b
    have h := affineLineParams_correct (makeAffineLine a b) (makeAffineLine_v1 a b) q hq
    rw [h_params] at h
    simpa using h
  · intro h_eq
    have h_point : q = mkPlane b 0 + (q 1) • mkPlane a 1 := by
      ext i
      fin_cases i <;> simp [h_eq, mkPlane_apply0, mkPlane_apply1] <;> ring
    rw [h_point]
    have h_dir : (q 1) • mkPlane a 1 ∈ Submodule.span ℝ ({mkPlane a 1} : Set EuclideanPlane) :=
      Submodule.mem_span_singleton.mpr ⟨q 1, rfl⟩
    have h2 : mkPlane b 0 + (q 1) • mkPlane a 1 ∈ makeAffineSubspace a b := by
      simpa [makeAffineSubspace] using h_dir
    simpa [makeAffineLine] using h2

/-- If p is within δ of ℓ and ‖p‖ ≤ 1, then p is within (3+δ)·δ of snap(ℓ).
    Uses slope-intercept parameterization: snapping changes slope and intercept by < δ each. -/
lemma affineLineSnap_near_point (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (ℓ : AffineLine) (B : ℝ)
    (hv1 : (getDirV ℓ) 1 ≠ 0)
    (p : EuclideanPlane) (hp_norm : ‖p‖ ≤ 1)
    (hp_near : p ∈ Metric.cthickening δ (ℓ.1 : Set EuclideanPlane)) :
    p ∈ Metric.cthickening ((3 + δ) * δ) ((affineLineSnap δ ℓ).1 : Set EuclideanPlane) := by
  let q : EuclideanPlane := EuclideanGeometry.orthogonalProjection ℓ.1 p
  have hq_in : q ∈ (ℓ.1 : Set EuclideanPlane) := EuclideanGeometry.orthogonalProjection_mem p
  have h_infEDist : Metric.infEDist p (ℓ.1 : Set EuclideanPlane) ≤ ENNReal.ofReal δ :=
    Metric.mem_cthickening_iff.mp hp_near
  have h_nonempty : (ℓ.1 : Set EuclideanPlane).Nonempty := ℓ.nonempty
  have h_ne_top : Metric.infEDist p (ℓ.1 : Set EuclideanPlane) ≠ ⊤ :=
    Metric.infEDist_ne_top h_nonempty
  have h_infDist : Metric.infDist p (ℓ.1 : Set EuclideanPlane) ≤ δ := by
    have h_eq : Metric.infDist p (ℓ.1 : Set EuclideanPlane) =
        ENNReal.toReal (Metric.infEDist p (ℓ.1 : Set EuclideanPlane)) := by rfl
    rw [h_eq]
    have h4 : ENNReal.toReal (Metric.infEDist p (ℓ.1 : Set EuclideanPlane)) ≤
        ENNReal.toReal (ENNReal.ofReal δ) := by
      have h_b_ne_top : ENNReal.ofReal δ ≠ ⊤ := by simp
      have h_iff : ENNReal.toReal (Metric.infEDist p (ℓ.1 : Set EuclideanPlane)) ≤
          ENNReal.toReal (ENNReal.ofReal δ) ↔
          Metric.infEDist p (ℓ.1 : Set EuclideanPlane) ≤ ENNReal.ofReal δ :=
        ENNReal.toReal_le_toReal h_ne_top h_b_ne_top
      exact h_iff.mpr h_infEDist
    have h5 : ENNReal.toReal (ENNReal.ofReal δ) = δ := by
      simp [hδ_pos.le]
    rw [h5] at h4
    exact h4
  have hdist : dist p q ≤ δ := by
    have h_eq : dist p q = Metric.infDist p (ℓ.1 : Set EuclideanPlane) :=
      EuclideanGeometry.dist_orthogonalProjection_eq_infDist ℓ.1 p
    rw [h_eq]
    exact h_infDist
  set m := (affineLineParams ℓ).1 with hm_def
  set b := (affineLineParams ℓ).2 with hb_def
  set m' := (affineLineParams (affineLineSnap δ ℓ)).1 with hm'_def
  set b' := (affineLineParams (affineLineSnap δ ℓ)).2 with hb'_def
  have hq_eq : q 0 = m * q 1 + b := affineLineParams_correct ℓ hv1 q hq_in
  have h_params : affineLineParams (affineLineSnap δ ℓ) = (gridSnap1D δ m, gridSnap1D δ b) :=
    affineLineSnap_params δ ℓ
  have h_m'_eq : m' = gridSnap1D δ m := by
    simp [hm'_def, h_params] <;> rfl
  have h_b'_eq : b' = gridSnap1D δ b := by
    simp [hb'_def, h_params] <;> rfl
  have h_snap_eq : affineLineSnap δ ℓ = makeAffineLine m' b' := by
    have h_inj : affineLineParams (affineLineSnap δ ℓ) = affineLineParams (makeAffineLine m' b') := by
      simp [hm'_def, hb'_def, makeAffineLine_params]
    have h_v1' : (getDirV (affineLineSnap δ ℓ)) 1 ≠ 0 := affineLineSnap_v1 δ ℓ
    have h_v1'' : (getDirV (makeAffineLine m' b')) 1 ≠ 0 := makeAffineLine_v1 m' b'
    exact affineLineParams_injective h_v1' h_v1'' h_inj
  have h_dm : |m - m'| < δ := by
    rw [h_m'_eq]
    exact gridSnap1D_bound hδ_pos m
  have h_db : |b - b'| < δ := by
    rw [h_b'_eq]
    exact gridSnap1D_bound hδ_pos b
  let q' : EuclideanPlane := mkPlane (m' * q 1 + b') (q 1)
  have hq'_eq0 : q' 0 = m' * q 1 + b' := by simp [q', mkPlane_apply0]
  have hq'_eq1 : q' 1 = q 1 := by simp [q', mkPlane_apply1]
  have hq'_in_line : q' ∈ (affineLineSnap δ ℓ).1 := by
    rw [h_snap_eq]
    rw [makeAffineLine_iff m' b' q']
    <;> simp [hq'_eq0, hq'_eq1] <;> ring
  have hq_norm : ‖q‖ ≤ 1 + δ := by
    have h_tri : ‖q‖ ≤ ‖p‖ + dist p q := by
      calc ‖q‖ = ‖p + (q - p)‖ := by simp [sub_add_cancel]
      _ ≤ ‖p‖ + ‖q - p‖ := norm_add_le _ _
      _ = ‖p‖ + dist q p := by rw [dist_eq_norm]
      _ = ‖p‖ + dist p q := by rw [dist_comm]
    linarith [hp_norm, hdist]
  have hq1_abs : |q 1| ≤ ‖q‖ :=
    coord_abs_le_norm q 1
  have h_dist_qq' : dist q q' ≤ (2 + δ) * δ := by
    have h1 : dist q q' = |q 0 - q' 0| := by
      have h2 : q - q' = mkPlane (q 0 - q' 0) 0 := by
        ext i
        fin_cases i <;> simp [mkPlane_apply0, mkPlane_apply1, hq'_eq1] <;> ring
      rw [dist_eq_norm, h2]
      have h3 : ‖mkPlane (q 0 - q' 0) 0‖ = |q 0 - q' 0| := by
        have h4 : ‖mkPlane (q 0 - q' 0) 0‖ ^ 2 = (q 0 - q' 0) ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
          <;> simp [mkPlane_apply0, mkPlane_apply1] <;> ring
        have h5 : 0 ≤ ‖mkPlane (q 0 - q' 0) 0‖ := by positivity
        have h6 : 0 ≤ |q 0 - q' 0| := abs_nonneg _
        have h7 : ‖mkPlane (q 0 - q' 0) 0‖ ^ 2 = |q 0 - q' 0| ^ 2 := by
          rw [h4, sq_abs]
        nlinarith
      rw [h3]
    rw [h1]
    have h6 : q 0 - q' 0 = (m - m') * q 1 + (b - b') := by
      linarith [hq_eq, hq'_eq0]
    rw [h6]
    have h7 : |(m - m') * q 1 + (b - b')| ≤ |m - m'| * |q 1| + |b - b'| := by
      have h71 : |(m - m') * q 1 + (b - b')| ≤ |(m - m') * q 1| + |b - b'| := by
        have h_abs_tri : ∀ (a b : ℝ), |a + b| ≤ |a| + |b| := by
          intro a b
          exact abs_add_le a b
        exact h_abs_tri ((m - m') * q 1) (b - b')
      have h72 : |(m - m') * q 1| = |m - m'| * |q 1| := by rw [abs_mul]
      rw [h72] at h71
      exact h71
    have h8 : |m - m'| * |q 1| + |b - b'| < δ * (1 + δ) + δ := by
      have hq1_nonneg : 0 ≤ |q 1| := abs_nonneg _
      have h92 : |q 1| ≤ 1 + δ := by
        calc |q 1| ≤ ‖q‖ := hq1_abs
             _ ≤ 1 + δ := hq_norm
      have h93 : |m - m'| * |q 1| ≤ δ * (1 + δ) := by
        calc |m - m'| * |q 1|
          ≤ δ * |q 1| := by gcongr <;> linarith [h_dm.le]
        _ ≤ δ * (1 + δ) := by gcongr <;> linarith
      have h10 : |b - b'| < δ := h_db
      linarith
    have h9 : |(m - m') * q 1 + (b - b')| < δ * (1 + δ) + δ := by
      calc |(m - m') * q 1 + (b - b')|
        ≤ |m - m'| * |q 1| + |b - b'| := h7
      _ < δ * (1 + δ) + δ := h8
    have h10 : (2 + δ) * δ = δ * (1 + δ) + δ := by ring
    rw [h10]
    exact h9.le
  have h_final : dist p q' ≤ (3 + δ) * δ := by
    calc dist p q' ≤ dist p q + dist q q' := dist_triangle _ _ _
    _ ≤ δ + (2 + δ) * δ := by gcongr <;> exact h_dist_qq'
    _ = (3 + δ) * δ := by ring
  have h_edist : edist p q' ≤ ENNReal.ofReal ((3 + δ) * δ) := by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal h_final
  have h_inf : Metric.infEDist p ((affineLineSnap δ ℓ).1 : Set EuclideanPlane) ≤
      ENNReal.ofReal ((3 + δ) * δ) := by
    have h : Metric.infEDist p ((affineLineSnap δ ℓ).1 : Set EuclideanPlane) ≤ edist p q' :=
      Metric.infEDist_le_edist_of_mem (x := p) (s := ((affineLineSnap δ ℓ).1)) (y := q') hq'_in_line
    exact h.trans h_edist
  have h_pos : 0 ≤ (3 + δ) * δ := by positivity
  exact Metric.mem_cthickening_iff.mpr (by simpa [h_pos] using h_inf)

/-! ### Covering movement lemmas -/

/-- If f moves points in A by at most D, then covering_{ε+D}(f(A)) ≤ covering_ε(A). -/
lemma covering_movement {X : Type*} [PseudoMetricSpace X] {f : X → X} {D : ℝ} (hD : 0 ≤ D)
    {A : Set X} (h_move : ∀ x ∈ A, dist x (f x) ≤ D) {ε : NNReal} :
    Metric.externalCoveringNumber (ε + D.toNNReal) (f '' A) ≤ Metric.externalCoveringNumber ε A := by
  apply le_iInf
  intro C
  apply le_iInf
  intro hC
  have h1 : Metric.IsCover (ε + D.toNNReal) (f '' A) C := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases hC hx with ⟨c, hc_in, hdist⟩
    have h3 : dist (f x) x ≤ D := by
      have h4 : dist x (f x) ≤ D := h_move x hx
      rw [dist_comm] at h4; exact h4
    have h4 : dist x c ≤ (ε : ℝ) := by simpa [edist_dist] using hdist
    have h2 : dist (f x) c ≤ D + (ε : ℝ) := by
      linarith [dist_triangle (f x) x c]
    have h_pos : 0 ≤ D + (ε : ℝ) := by positivity
    have h6 : ((ε + D.toNNReal : ℝ)) = D + (ε : ℝ) := by
      simp [NNReal.coe_add, hD] <;> ring
    have h5 : (↑(ε + D.toNNReal) : ENNReal) = ENNReal.ofReal (D + (ε : ℝ)) := by
      have h71 : (↑(ε + D.toNNReal) : ENNReal) = ENNReal.ofReal (↑(ε + D.toNNReal) : ℝ) := by
        exact ENNReal.coe_nnreal_eq (ε + D.toNNReal)
      rw [h71]
      have h72 : (↑(ε + D.toNNReal) : ℝ) = D + (ε : ℝ) := h6
      rw [h72]
    have h_edist : edist (f x) c ≤ ↑(ε + D.toNNReal) := by
      rw [edist_dist, h5]
      exact ENNReal.ofReal_le_ofReal h2
    exact ⟨c, hc_in, h_edist⟩
  exact Metric.IsCover.externalCoveringNumber_le_encard h1

/-- If f moves points in A by at most D, then covering_{ε+D}(A) ≤ covering_ε(f(A)). -/
lemma covering_movement_preimage {X : Type*} [PseudoMetricSpace X] {f : X → X} {D : ℝ} (hD : 0 ≤ D)
    {A : Set X} (h_move : ∀ x ∈ A, dist x (f x) ≤ D) {ε : NNReal} :
    Metric.externalCoveringNumber (ε + D.toNNReal) A ≤ Metric.externalCoveringNumber ε (f '' A) := by
  apply le_iInf
  intro C
  apply le_iInf
  intro hC
  have h1 : Metric.IsCover (ε + D.toNNReal) A C := by
    intro x hx
    have hfx_in : f x ∈ f '' A := ⟨x, hx, rfl⟩
    rcases hC hfx_in with ⟨c, hc_in, hdist⟩
    have h3 : dist x (f x) ≤ D := h_move x hx
    have h4 : dist (f x) c ≤ (ε : ℝ) := by simpa [edist_dist] using hdist
    have h2 : dist x c ≤ D + (ε : ℝ) := by
      linarith [dist_triangle x (f x) c]
    have h_pos : 0 ≤ D + (ε : ℝ) := by positivity
    have h6 : ((ε + D.toNNReal : ℝ)) = D + (ε : ℝ) := by
      simp [NNReal.coe_add, hD] <;> ring
    have h5 : (↑(ε + D.toNNReal) : ENNReal) = ENNReal.ofReal (D + (ε : ℝ)) := by
      have h71 : (↑(ε + D.toNNReal) : ENNReal) = ENNReal.ofReal (↑(ε + D.toNNReal) : ℝ) := by
        exact ENNReal.coe_nnreal_eq (ε + D.toNNReal)
      rw [h71]
      have h72 : (↑(ε + D.toNNReal) : ℝ) = D + (ε : ℝ) := h6
      rw [h72]
    have h_edist : edist x c ≤ ↑(ε + D.toNNReal) := by
      rw [edist_dist, h5]
      exact ENNReal.ofReal_le_ofReal h2
    exact ⟨c, hc_in, h_edist⟩
  exact Metric.IsCover.externalCoveringNumber_le_encard h1

/-! ### Lemma B: S-set transfer under snapping -/

/-- Transfer of IsDeltaSSet under affineLineSnap. If S is a (δ,s,C)-S-set of lines with
    bounded intercept B and finite δ-covering number, then Q = snap(S) is a (δ,s,C')-S-set
    with constant blowup. -/
lemma IsDeltaSSet.affineLine_snap {δ s C : ℝ} {S : Set AffineLine}
    (hS : IsDeltaSSet δ s C S)
    (hS_fin : Metric.externalCoveringNumber δ.toNNReal S < ⊤)
    (B : ℝ) (hB_nonneg : 0 ≤ B) (hδ_le_one : δ ≤ 1)
    (h_slope : ∀ ℓ ∈ S, |(affineLineParams ℓ).1| ≤ 1)
    (h_intercept : ∀ ℓ ∈ S, |(affineLineParams ℓ).2| ≤ B)
    (h_v1 : ∀ ℓ ∈ S, (getDirV ℓ) 1 ≠ 0) :
    ∃ (C' : ℝ), 0 < C' ∧ IsDeltaSSet δ s C' (affineLineSnap δ '' S) := by
  let D : ℝ := (3 + B + δ) * δ
  have hδ_pos : 0 < δ := hS.2.1
  have hD_nonneg : 0 ≤ D := by
    have h1 : 0 ≤ 3 + B + δ := by linarith
    exact mul_nonneg h1 hδ_pos.le
  let f : AffineLine → AffineLine := affineLineSnap δ
  let Q : Set AffineLine := f '' S
  have h_move : ∀ (x : AffineLine), x ∈ S → dist x (f x) ≤ D := by
    intro x hx
    exact affineLineSnap_near δ hδ_pos hδ_le_one x B hB_nonneg
      (h_v1 x hx) (h_slope x hx) (h_intercept x hx)
  have hR_ge : ∃ (k : ℕ), ((2^k : ℕ) : ℝ) * δ ≥ δ + D := by
    have h1 : ∃ (n : ℕ), (4 + B + δ : ℝ) ≤ (n : ℝ) := exists_nat_ge (4 + B + δ)
    rcases h1 with ⟨n, hn⟩
    have h2 : (n : ℝ) ≤ (2 : ℝ)^n := by
      have h3 : ∀ m : ℕ, (m : ℝ) ≤ (2 : ℝ)^m := by
        intro m
        induction m with
        | zero => norm_num
        | succ m ih =>
          by_cases h : m = 0
          · subst h; norm_num
          · have h5 : (m : ℝ) ≥ 1 := by exact_mod_cast (Nat.pos_of_ne_zero h)
            have h6 : ((m.succ : ℝ)) ≤ 2 * (2 : ℝ)^m := by
              have h7 : (m.succ : ℝ) = (m : ℝ) + 1 := by simp
              rw [h7]
              nlinarith [ih]
            have h8 : (2 : ℝ)^m.succ = 2 * (2 : ℝ)^m := by
              simp [pow_succ] <;> ring
            rw [h8]
            exact h6
      exact h3 n
    refine ⟨n, ?_⟩
    have h3 : δ + D = (4 + B + δ) * δ := by
      simp [D] <;> ring
    rw [h3]
    have h4 : ((2^n : ℕ) : ℝ) ≥ 4 + B + δ := by
      calc ((2^n : ℕ) : ℝ) = (2 : ℝ)^n := by simp
      _ ≥ (n : ℝ) := h2
      _ ≥ 4 + B + δ := hn
    have h5 : 0 ≤ δ := hδ_pos.le
    nlinarith
  rcases hR_ge with ⟨k, hk⟩
  let δnn : NNReal := δ.toNNReal
  let δDnn : NNReal := (δ + D).toNNReal
  have hδnn : (δnn : ℝ) = δ := Real.coe_toNNReal δ hδ_pos.le
  have hδDnn : (δDnn : ℝ) = δ + D := by
    have hpos : 0 ≤ δ + D := by linarith [hD_nonneg]
    exact Real.coe_toNNReal (δ + D) hpos
  have h_goalD : δDnn ≤ (((2^k : ℕ) : ℝ) * δ).toNNReal := by
    apply NNReal.coe_le_coe.mp
    have h_goal : (δDnn : ℝ) ≤ ((((2^k : ℕ) : ℝ) * δ).toNNReal : ℝ) := by
      have h1 : (δDnn : ℝ) = δ + D := hδDnn
      have h2 : ((((2^k : ℕ) : ℝ) * δ).toNNReal : ℝ) = ((2^k : ℕ) : ℝ) * δ := by
        rw [Real.coe_toNNReal] <;> positivity
      rw [h1, h2]
      exact hk
    exact h_goal
  have hδDnn_eq : δDnn = δnn + D.toNNReal := by
    have h : (δDnn : ℝ) = (δnn + D.toNNReal : ℝ) := by
      simp [δDnn, δnn, hδ_pos.le, hD_nonneg, NNReal.coe_add] <;> ring
    exact_mod_cast h
  have hQ_nonempty : Q.Nonempty := hS.1.image f
  have hC_pos : 0 < C := hS.2.2.1
  have hs_nonneg : 0 ≤ s := hS.2.2.2.1
  have h_covering_lower : Metric.externalCoveringNumber δnn S ≤
      (affineLine_packing_constant : ENNReal)^k * Metric.externalCoveringNumber δnn Q := by
    have h1 : Metric.externalCoveringNumber δDnn S ≤ Metric.externalCoveringNumber δnn Q := by
      rw [hδDnn_eq]
      exact covering_movement_preimage (X := AffineLine) (f := f) (A := S) (ε := δnn) hD_nonneg h_move
    have h2 : Metric.externalCoveringNumber δnn S ≤
        (affineLine_packing_constant : ENNReal)^k * Metric.externalCoveringNumber δDnn S := by
      have h21 : Metric.externalCoveringNumber δnn S ≤
          (affineLine_packing_constant : ENNReal)^k *
            Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal S :=
        affineLine_doubling_iter δ hδ_pos k (S := S)
      have h22 : Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal S ≤
          Metric.externalCoveringNumber δDnn S :=
        Metric.externalCoveringNumber_anti h_goalD
      have h22' : (Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal S : ENNReal) ≤
          (Metric.externalCoveringNumber δDnn S : ENNReal) := by exact_mod_cast h22
      have h_mul : (affineLine_packing_constant : ENNReal)^k * (Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal S : ENNReal) ≤
          (affineLine_packing_constant : ENNReal)^k * (Metric.externalCoveringNumber δDnn S : ENNReal) :=
        mul_le_mul_left' h22' _
      exact_mod_cast le_trans h21 h_mul
    calc Metric.externalCoveringNumber δnn S
      ≤ (affineLine_packing_constant : ENNReal)^k * Metric.externalCoveringNumber δDnn S := h2
    _ ≤ (affineLine_packing_constant : ENNReal)^k * Metric.externalCoveringNumber δnn Q := by gcongr
  let C' : ℝ := (affineLine_packing_constant : ℝ)^(2 * k) * C * (5 + B)^s
  have hK_real_pos : 0 < (affineLine_packing_constant : ℝ) := by exact_mod_cast affineLine_packing_constant_pos'
  have h5B_pos : 0 < (5 + B)^s := Real.rpow_pos_of_pos (by linarith [hB_nonneg]) s
  have hC'_pos : 0 < C' := by
    have h1 : 0 < (affineLine_packing_constant : ℝ)^(2 * k) := pow_pos hK_real_pos (2 * k)
    exact mul_pos (mul_pos h1 hC_pos) h5B_pos
  have h_main : ∀ (y : AffineLine) (r : ℝ), δ ≤ r →
      Metric.externalCoveringNumber δnn (Q ∩ Metric.closedBall y r) ≤
        ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δnn Q := by
    intro y r hr
    have hD_ball : Q ∩ Metric.closedBall y r ⊆ f '' (S ∩ Metric.closedBall y (r + D)) := by
      intro q hq
      have hq_in_Q : q ∈ Q := hq.1
      have hq_in_ball : q ∈ Metric.closedBall y r := hq.2
      rcases hq_in_Q with ⟨ℓ, hℓ_in_S, rfl⟩
      have hdist : dist ℓ y ≤ r + D := by
        calc dist ℓ y ≤ dist ℓ (f ℓ) + dist (f ℓ) y := dist_triangle _ _ _
        _ ≤ D + r := by
          have h4 : dist ℓ (f ℓ) ≤ D := h_move ℓ hℓ_in_S
          have h5 : dist (f ℓ) y ≤ r := (Metric.mem_closedBall).mp hq_in_ball
          linarith
        _ = r + D := by ring
      exact ⟨ℓ, ⟨hℓ_in_S, Metric.mem_closedBall.mpr hdist⟩, rfl⟩
    have h3 : Metric.externalCoveringNumber δnn (Q ∩ Metric.closedBall y r) ≤
        Metric.externalCoveringNumber δnn (f '' (S ∩ Metric.closedBall y (r + D))) :=
      Metric.externalCoveringNumber_mono_set hD_ball
    have h4 : Metric.externalCoveringNumber δnn (f '' (S ∩ Metric.closedBall y (r + D))) ≤
        (affineLine_packing_constant : ENNReal)^k *
          Metric.externalCoveringNumber δDnn (f '' (S ∩ Metric.closedBall y (r + D))) := by
      let A := S ∩ Metric.closedBall y (r + D)
      have h41 : Metric.externalCoveringNumber δnn (f '' A) ≤
          (affineLine_packing_constant : ENNReal)^k *
            Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal (f '' A) :=
        affineLine_doubling_iter δ hδ_pos k (S := f '' A)
      have h42 : Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal (f '' A) ≤
          Metric.externalCoveringNumber δDnn (f '' A) :=
        Metric.externalCoveringNumber_anti h_goalD
      have h42' : (Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal (f '' A) : ENNReal) ≤
          (Metric.externalCoveringNumber δDnn (f '' A) : ENNReal) := by exact_mod_cast h42
      have h_mul : (affineLine_packing_constant : ENNReal)^k * (Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal (f '' A) : ENNReal) ≤
          (affineLine_packing_constant : ENNReal)^k * (Metric.externalCoveringNumber δDnn (f '' A) : ENNReal) :=
        mul_le_mul_left' h42' _
      exact_mod_cast le_trans h41 h_mul
    have h5 : Metric.externalCoveringNumber δDnn (f '' (S ∩ Metric.closedBall y (r + D))) ≤
        Metric.externalCoveringNumber δnn (S ∩ Metric.closedBall y (r + D)) := by
      rw [hδDnn_eq]
      exact covering_movement (X := AffineLine) (f := f) (ε := δnn) hD_nonneg
        (A := S ∩ Metric.closedBall y (r + D))
        (fun x hx => h_move x hx.1)
    have h6 : δ ≤ r + D := by linarith [hD_nonneg]
    have h7 : Metric.externalCoveringNumber δnn (S ∩ Metric.closedBall y (r + D)) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (r + D)) ^ s * Metric.externalCoveringNumber δnn S :=
      hS.2.2.2.2 y (r + D) h6
    have h8 : r + D ≤ (5 + B) * r := by
      have h9 : D ≤ (4 + B) * δ := by
        have h10 : (3 + B + δ) ≤ (4 + B) := by linarith
        have h11 : (3 + B + δ) * δ ≤ (4 + B) * δ := by
          gcongr <;> linarith
        simpa [D] using h11
      have h12 : (4 + B) * δ ≤ (4 + B) * r := by
        have h13 : 0 ≤ 4 + B := by linarith
        gcongr <;> linarith
      have h14 : D ≤ (4 + B) * r := le_trans h9 h12
      linarith
    have h9 : (ENNReal.ofReal (r + D)) ^ s ≤ ENNReal.ofReal ((5 + B)^s) * (ENNReal.ofReal r) ^ s := by
      have h10 : r + D ≤ (5 + B) * r := h8
      have h11 : 0 ≤ r := by linarith
      have h12 : ENNReal.ofReal (r + D) ≤ ENNReal.ofReal ((5 + B) * r) := by
        exact ENNReal.ofReal_le_ofReal h10
      have h13 : ENNReal.ofReal ((5 + B) * r) = ENNReal.ofReal (5 + B) * ENNReal.ofReal r := by
        rw [ENNReal.ofReal_mul (by positivity)] <;> ring
      rw [h13] at h12
      have h14 : (ENNReal.ofReal (r + D)) ^ s ≤ (ENNReal.ofReal (5 + B) * ENNReal.ofReal r) ^ s := by
        gcongr
      have h15 : (ENNReal.ofReal (5 + B) * ENNReal.ofReal r) ^ s =
          ENNReal.ofReal ((5 + B)^s) * (ENNReal.ofReal r) ^ s := by
        have h_pos1 : 0 ≤ 5 + B := by linarith [hB_nonneg]
        have h_pos2 : 0 ≤ r := by linarith
        have h_eq1 : ENNReal.ofReal (5 + B) * ENNReal.ofReal r = ENNReal.ofReal ((5 + B) * r) := by
          rw [ENNReal.ofReal_mul h_pos1] <;> ring
        rw [h_eq1]
        have h_eq2 : (ENNReal.ofReal ((5 + B) * r)) ^ s = ENNReal.ofReal (((5 + B) * r) ^ s) :=
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hs_nonneg
        rw [h_eq2]
        have h_eq3 : ((5 + B) * r) ^ s = (5 + B)^s * r^s := by
          rw [Real.mul_rpow h_pos1 h_pos2] <;> ring
        rw [h_eq3]
        have h_eq4 : ENNReal.ofReal ((5 + B)^s * r^s) = ENNReal.ofReal ((5 + B)^s) * ENNReal.ofReal (r^s) := by
          rw [ENNReal.ofReal_mul (by positivity)] <;> ring
        rw [h_eq4]
        have h_eq5 : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) :=
          ENNReal.ofReal_rpow_of_nonneg h_pos2 hs_nonneg
        rw [h_eq5]
      rw [h15] at h14
      exact h14
    have h_final : (Metric.externalCoveringNumber δnn (Q ∩ Metric.closedBall y r) : ENNReal) ≤
        ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δnn Q : ENNReal) := by
      set eQr := (Metric.externalCoveringNumber δnn (Q ∩ Metric.closedBall y r) : ENNReal) with heQr
      set eA := (Metric.externalCoveringNumber δnn (f '' (S ∩ Metric.closedBall y (r + D))) : ENNReal) with heA
      set eD := (Metric.externalCoveringNumber δDnn (f '' (S ∩ Metric.closedBall y (r + D))) : ENNReal) with heD
      set eS := (Metric.externalCoveringNumber δnn (S ∩ Metric.closedBall y (r + D)) : ENNReal) with heS
      set eS0 := (Metric.externalCoveringNumber δnn S : ENNReal) with heS0
      set eQ := (Metric.externalCoveringNumber δnn Q : ENNReal) with heQ
      set K := (affineLine_packing_constant : ENNReal) with hK
      have s1 : eQr ≤ eA := by
        rw [heQr, heA]; exact_mod_cast h3
      have s2 : eA ≤ K^k * eD := by
        rw [heA, heD]; exact_mod_cast h4
      have s3 : K^k * eD ≤ K^k * eS := by
        have h : eD ≤ eS := by rw [heD, heS]; exact_mod_cast h5
        exact mul_le_mul_left' h (K^k)
      have s4 : K^k * eS ≤ K^k * (ENNReal.ofReal C * (ENNReal.ofReal (r + D)) ^ s * eS0) := by
        have h : eS ≤ ENNReal.ofReal C * (ENNReal.ofReal (r + D)) ^ s * eS0 := by
          rw [heS, heS0]; exact_mod_cast h7
        exact mul_le_mul_left' h (K^k)
      have s5 : K^k * (ENNReal.ofReal C * (ENNReal.ofReal (r + D)) ^ s * eS0) ≤
          K^k * (ENNReal.ofReal C * ENNReal.ofReal ((5 + B)^s) * (ENNReal.ofReal r) ^ s * eS0) := by
        have h : ENNReal.ofReal C * (ENNReal.ofReal (r + D)) ^ s * eS0 ≤
            ENNReal.ofReal C * (ENNReal.ofReal ((5 + B)^s) * (ENNReal.ofReal r) ^ s) * eS0 := by
          gcongr
        have h2 : ENNReal.ofReal C * (ENNReal.ofReal ((5 + B)^s) * (ENNReal.ofReal r) ^ s) * eS0 =
            ENNReal.ofReal C * ENNReal.ofReal ((5 + B)^s) * (ENNReal.ofReal r) ^ s * eS0 := by ring
        rw [h2] at h
        exact mul_le_mul_left' h (K^k)
      have s6 : K^k * (ENNReal.ofReal C * ENNReal.ofReal ((5 + B)^s) * (ENNReal.ofReal r) ^ s * eS0) ≤
          K^k * (ENNReal.ofReal C * ENNReal.ofReal ((5 + B)^s) * (ENNReal.ofReal r) ^ s * (K^k * eQ)) := by
        have h : eS0 ≤ K^k * eQ := by rw [heS0, heQ]; exact_mod_cast h_covering_lower
        have h2 : ENNReal.ofReal C * ENNReal.ofReal ((5 + B)^s) * (ENNReal.ofReal r) ^ s * eS0 ≤
            ENNReal.ofReal C * ENNReal.ofReal ((5 + B)^s) * (ENNReal.ofReal r) ^ s * (K^k * eQ) := by
          gcongr
        exact mul_le_mul_left' h2 (K^k)
      have s7 : K^k * (ENNReal.ofReal C * ENNReal.ofReal ((5 + B)^s) * (ENNReal.ofReal r) ^ s * (K^k * eQ)) =
          ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * eQ := by
        have hC'_eq : ENNReal.ofReal C' = K^(2 * k) * ENNReal.ofReal C * ENNReal.ofReal ((5 + B)^s) := by
          have h1 : C' = (affineLine_packing_constant : ℝ)^(2 * k) * C * (5 + B)^s := by
            simp [C'] <;> ring
          rw [h1]
          have h_pos1 : 0 ≤ (affineLine_packing_constant : ℝ)^(2 * k) := by positivity
          have h_pos2 : 0 ≤ C := hC_pos.le
          have h_pos3 : 0 ≤ (5 + B)^s := by positivity
          have eq1 : ENNReal.ofReal (((affineLine_packing_constant : ℝ)^(2 * k) * C) * (5 + B)^s) =
              ENNReal.ofReal ((affineLine_packing_constant : ℝ)^(2 * k) * C) * ENNReal.ofReal ((5 + B)^s) := by
            rw [ENNReal.ofReal_mul (by positivity)]
          have eq2 : ENNReal.ofReal ((affineLine_packing_constant : ℝ)^(2 * k) * C) =
              ENNReal.ofReal ((affineLine_packing_constant : ℝ)^(2 * k)) * ENNReal.ofReal C := by
            rw [ENNReal.ofReal_mul h_pos1]
          have eq3 : ENNReal.ofReal ((affineLine_packing_constant : ℝ)^(2 * k)) = K^(2 * k) := by
            simp [hK]
          rw [eq1, eq2, eq3] <;> ring
        have hK_pow : K^(2 * k) = K^k * K^k := by rw [← pow_add] <;> ring
        simp [hK, hC'_eq, hK_pow, mul_assoc, mul_comm, mul_left_comm] <;> ring
      exact le_trans s1 (le_trans s2 (le_trans s3 (le_trans s4 (le_trans s5 (le_trans s6 (le_of_eq s7))))))
    exact_mod_cast h_final
  exact ⟨C', hC'_pos, ⟨hQ_nonempty, hS.2.1, hC'_pos, hs_nonneg, h_main⟩⟩

end DirecretisedFurstenbergEstimate.Snapping
