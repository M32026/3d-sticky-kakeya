module

public import MyLeanRepo.robust_kaufman_projection.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Near-identity perturbation covering bounds

Given a map `f : ℝ → ℝ` that moves points by at most `c * δ`, the
δ-covering number changes by at most a factor `K = 2 * ⌈c⌉ + 3`.

This is used in the main proof: the affine projection is 2-Lipschitz,
so a plane perturbation of `δ` becomes a 1D perturbation of `2δ`.

## Main results
- `ncover_near_identity_upper`: `Ncover δ (f '' X) ≤ K * Ncover δ X`
- `ncover_near_identity_lower`: `Ncover δ X ≤ K * Ncover δ (f '' X)`
-/

noncomputable section

open scoped ENNReal NNReal
open Metric Set Classical

namespace RobustKaufmanProjection.PerturbationGeneral

/-! ### General covering lemma -/

/-- A closed ball of radius `(c+1) * δ` in ℝ is covered by `2 * ⌈c⌉ + 3`
closed balls of radius δ. -/
lemma ball_cover_general {δ : ℝ} (hδ : 0 < δ) {c : ℝ} (hc : 0 ≤ c) (center : ℝ) :
    let n : ℕ := (Int.ceil c).toNat
    IsCover δ.toNNReal (closedBall center ((c + 1) * δ))
      (Finset.image (fun k : ℤ => center + (k : ℝ) * δ)
        (Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ)) : Set ℝ) := by
  let n : ℕ := (Int.ceil c).toNat
  have h1 : 0 ≤ Int.ceil c := by
    have h2 : 0 ≤ c := hc
    exact Int.ceil_nonneg hc
  have h_n_ceil : (n : ℤ) = Int.ceil c := by
    simp [n, Int.toNat_of_nonneg h1] <;> omega
  have h_c_le_n : c ≤ (n : ℝ) := by
    have h3 : c ≤ Int.ceil c := Int.le_ceil c
    have h4 : (Int.ceil c : ℝ) = (n : ℝ) := by exact_mod_cast h_n_ceil.symm
    linarith
  rw [isCover_iff_subset_iUnion_closedBall]
  intro x hx
  have h_dist : dist x center ≤ (c + 1) * δ := hx
  have h2 : |x - center| ≤ (c + 1) * δ := by simpa [Real.dist_eq] using h_dist
  set d : ℝ := x - center with hd
  have h3 : -(c + 1) * δ ≤ d := by
    have h4 : -((c + 1) * δ) ≤ d := (abs_le.mp h2).1
    linarith
  have h4 : d ≤ (c + 1) * δ := (abs_le.mp h2).2
  let k : ℤ := ⌊d / δ⌋
  have hk1 : (k : ℝ) * δ ≤ d := by
    have h5 : (k : ℝ) ≤ d / δ := Int.floor_le (d / δ)
    have h6 : (k : ℝ) * δ ≤ (d / δ) * δ := by gcongr
    have h7 : (d / δ) * δ = d := by
      field_simp [hδ.ne'] <;> ring
    rw [h7] at h6; exact h6
  have hk2 : d < ((k : ℝ) + 1) * δ := by
    have h5 : d / δ < (k : ℝ) + 1 := Int.lt_floor_add_one (d / δ)
    have h6 : (d / δ) * δ < ((k : ℝ) + 1) * δ := by gcongr
    have h7 : (d / δ) * δ = d := by
      field_simp [hδ.ne'] <;> ring
    rw [h7] at h6; exact h6
  have hk3 : |d - (k : ℝ) * δ| < δ := by
    have h7 : 0 ≤ d - (k : ℝ) * δ := by linarith
    have h8 : d - (k : ℝ) * δ < δ := by linarith
    rw [abs_of_nonneg h7] <;> linarith
  have hk4 : -(n + 1 : ℤ) ≤ k := by
    have h9 : d / δ ≥ -(c + 1) := by
      have h10 : d ≥ -(c + 1) * δ := h3
      have h11 : d / δ ≥ -(c + 1) := by
        calc d / δ ≥ (-(c + 1) * δ) / δ := by gcongr
          _ = -(c + 1) := by field_simp [hδ.ne'] <;> ring
      exact h11
    have h10 : Int.floor (-(c + 1)) ≤ k := Int.floor_mono h9
    have h11 : Int.floor (-(c + 1)) = -Int.ceil (c + 1) := by
      rw [Int.floor_neg]
    have h12 : Int.ceil (c + 1) = Int.ceil c + 1 := by
      have h121 : Int.ceil (c + (1 : ℤ)) = Int.ceil c + 1 := by
        exact Int.ceil_add_intCast c 1
      simpa using h121
    rw [h11, h12] at h10
    have h13 : -(Int.ceil c + 1) ≤ k := h10
    have h14 : Int.ceil c = (n : ℤ) := by
      exact_mod_cast h_n_ceil.symm
    rw [h14] at h13
    simpa using h13
  have hk5 : k ≤ (n + 1 : ℤ) := by
    have h9 : d / δ ≤ c + 1 := by
      have h10 : d ≤ (c + 1) * δ := h4
      calc d / δ ≤ ((c + 1) * δ) / δ := by gcongr
        _ = c + 1 := by field_simp [hδ.ne'] <;> ring
    have h10 : (k : ℝ) ≤ d / δ := Int.floor_le (d / δ)
    have h11 : (k : ℝ) ≤ c + 1 := by linarith
    have h12 : (k : ℝ) ≤ (n + 1 : ℝ) := by linarith [h_c_le_n]
    exact_mod_cast h12
  have hk_in : k ∈ Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ) := by
    simp [Finset.mem_Icc, hk4, hk5] <;> omega
  let y : ℝ := center + (k : ℝ) * δ
  have hy_in : y ∈ (Finset.image (fun k : ℤ => center + (k : ℝ) * δ)
      (Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ)) : Set ℝ) := by
    apply Finset.mem_image_of_mem _ hk_in
  have h_dist_y : dist x y ≤ δ := by
    have h14 : x - y = d - (k : ℝ) * δ := by
      simp [y, hd] <;> ring
    rw [Real.dist_eq, h14]
    exact hk3.le
  have h15 : (δ.toNNReal : ℝ) = δ := by simp [hδ.le]
  have h16 : dist x y ≤ (δ.toNNReal : ℝ) := by rw [h15] <;> exact h_dist_y
  have h17 : x ∈ closedBall y δ.toNNReal := by exact mem_closedBall.mpr h16
  exact Set.mem_iUnion₂.mpr ⟨y, hy_in, h17⟩

/-- If every point of S is within `(c+1) * δ` of some point of C,
then S has a δ-cover of cardinality at most `(2⌈c⌉+3) * |C|`. -/
lemma near_identity_cover {δ : ℝ} (hδ : 0 < δ) {c : ℝ} (hc : 0 ≤ c)
    {S C : Set ℝ}
    (h : ∀ x ∈ S, ∃ c0 ∈ C, dist x c0 ≤ (c + 1) * δ) :
    ∃ (C' : Set ℝ), IsCover δ.toNNReal S C' ∧
      C'.encard ≤ (2 * (Int.ceil c).toNat + 3) * C.encard := by
  let n : ℕ := (Int.ceil c).toNat
  let K : ℕ := 2 * n + 3
  by_cases hC_inf : C.Infinite
  · have h_top : C.encard = ⊤ := by simpa [Set.encard_eq_top] using hC_inf
    have h_univ_cover : IsCover δ.toNNReal S Set.univ := by
      intro x _; exact ⟨x, by simp, by simp⟩
    exact ⟨Set.univ, h_univ_cover, by rw [h_top] <;> simp⟩
  · have hC_fin : C.Finite := Set.not_infinite.mp hC_inf
    classical
    let C_fin : Finset ℝ := hC_fin.toFinset
    have hCfin_eq : (C_fin : Set ℝ) = C := hC_fin.coe_toFinset
    let centers (c0 : ℝ) : Finset ℝ :=
      Finset.image (fun k : ℤ => c0 + (k : ℝ) * δ)
        (Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ))
    let C' : Finset ℝ := C_fin.biUnion centers
    have h_card_centers : ∀ c0 : ℝ, (centers c0).card ≤ K := by
      intro c0
      have h_inj : Set.InjOn (fun k : ℤ => c0 + (k : ℝ) * δ)
          (Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ) : Set ℤ) := by
        intro k _ l _ h
        have h1 : (k : ℝ) * δ = (l : ℝ) * δ := by linarith
        have h2 : (k : ℝ) = (l : ℝ) := by
          apply mul_left_cancel₀ hδ.ne'
          linarith
        exact_mod_cast h2
      have h_card : (centers c0).card = (Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ)).card := by
        rw [Finset.card_image_of_injOn h_inj]
      rw [h_card]
      simp [K, Finset.Icc_eq_empty_of_lt]
      <;> omega
    have hC'_card : C'.card ≤ K * C_fin.card := by
      calc C'.card
        ≤ ∑ c0 ∈ C_fin, (centers c0).card := Finset.card_biUnion_le
      _ ≤ ∑ c0 ∈ C_fin, K := Finset.sum_le_sum (fun c0 _ => h_card_centers c0)
      _ = K * C_fin.card := by simp [mul_comm]
    have h_cover : IsCover δ.toNNReal S (C' : Set ℝ) := by
      rw [isCover_iff_subset_iUnion_closedBall]
      intro x hx
      rcases h x hx with ⟨c0, hc0, hdist⟩
      have h1 : x ∈ closedBall c0 ((c + 1) * δ) := by
        simpa [Metric.mem_closedBall] using hdist
      have h2 : IsCover δ.toNNReal (closedBall c0 ((c + 1) * δ))
          ((centers c0 : Set ℝ)) :=
        ball_cover_general hδ hc c0
      have h3 : x ∈ (⋃ d ∈ (centers c0 : Set ℝ), closedBall d δ.toNNReal) :=
        (isCover_iff_subset_iUnion_closedBall.mp h2) h1
      rcases Set.mem_iUnion₂.mp h3 with ⟨d, hd, hdist2⟩
      have h_c0_in_Cfin : c0 ∈ C_fin := by
        have h9 : c0 ∈ (C_fin : Set ℝ) := by rw [hCfin_eq] <;> exact hc0
        simpa using h9
      have h4 : d ∈ (C' : Set ℝ) := by
        simp only [C', Finset.mem_coe, Finset.mem_biUnion]
        exact ⟨c0, h_c0_in_Cfin, hd⟩
      exact Set.mem_iUnion₂.mpr ⟨d, h4, hdist2⟩
    have h5 : (C' : Set ℝ).encard ≤ (K : ENat) * C.encard := by
      calc (C' : Set ℝ).encard = ↑C'.card := by simp
        _ ≤ ↑(K * C_fin.card) := by exact_mod_cast hC'_card
        _ = (K : ENat) * ↑C_fin.card := by simp
        _ = (K : ENat) * C.encard := by rw [← hCfin_eq] <;> simp
    exact ⟨(C' : Set ℝ), h_cover, h5⟩

/-- Ncover monotonicity. -/
lemma ncover_mono {δ : ℝ} {A B : Set ℝ} (h : A ⊆ B) :
    Ncover δ A ≤ Ncover δ B := by
  let δ' := δ.toNNReal
  have h1 : Metric.externalCoveringNumber δ' A ≤ Metric.externalCoveringNumber δ' B := by
    simp only [Metric.externalCoveringNumber, le_iInf_iff]
    intro C hC
    have hC' : IsCover δ' A C :=
      IsCover.of_subset_iUnion_closedBall (h.trans (hC.subset_iUnion_closedBall))
    exact iInf₂_le C hC'
  have h2 : Ncover δ A = ↑(Metric.externalCoveringNumber δ' A) := by rfl
  have h3 : Ncover δ B = ↑(Metric.externalCoveringNumber δ' B) := by rfl
  rw [h2, h3]
  exact_mod_cast h1

/-! ### Main perturbation bounds -/

/-- If `f` moves points by at most `c * δ`, then
`Ncover δ (f '' X) ≤ K * Ncover δ X` where `K = 2 * ⌈c⌉ + 3`. -/
lemma ncover_near_identity_upper {δ : ℝ} {X : Set ℝ} {f : ℝ → ℝ}
    (hδ : 0 < δ) {c : ℝ} (hc : 0 ≤ c)
    (h_perturb : ∀ x ∈ X, dist (f x) x ≤ c * δ) :
    Ncover δ (f '' X) ≤ (2 * (Int.ceil c).toNat + 3 : ENNReal) * Ncover δ X := by
  let δ' : NNReal := δ.toNNReal
  let K : ℕ := 2 * (Int.ceil c).toNat + 3
  have h_main : ∀ (C : Set ℝ), IsCover δ' X C →
      ∃ (C' : Set ℝ), IsCover δ' (f '' X) C' ∧ C'.encard ≤ (K : ENat) * C.encard := by
    intro C hC
    have h' : ∀ y ∈ f '' X, ∃ c0 ∈ C, dist y c0 ≤ (c + 1) * δ := by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hdist : ∃ c0 ∈ C, edist x c0 ≤ ↑δ' := hC hx
      rcases hdist with ⟨c0, hc0, hedist⟩
      have h4 : dist x c0 ≤ δ := by
        have h51 : edist x c0 ≤ ↑δ' := hedist
        have h52 : edist x c0 = ENNReal.ofReal (dist x c0) := by rw [edist_dist]
        rw [h52] at h51
        have h53 : (↑δ' : ENNReal) = ENNReal.ofReal δ := by
          simp [δ', hδ.le] <;> norm_cast
        rw [h53] at h51
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h51
      have h6 : dist (f x) c0 ≤ (c + 1) * δ := by
        have h7 : dist (f x) x ≤ c * δ := h_perturb x hx
        calc dist (f x) c0
          ≤ dist (f x) x + dist x c0 := dist_triangle (f x) x c0
        _ ≤ c * δ + δ := by gcongr
        _ = (c + 1) * δ := by ring
      exact ⟨c0, hc0, h6⟩
    exact near_identity_cover hδ hc h'
  let S' := {C : Set ℝ // IsCover δ' X C}
  have h_self_cover : IsCover δ' X X := by
    intro z hz; exact ⟨z, hz, by simp⟩
  have hS'_nonempty : Nonempty S' := by refine' ⟨⟨X, h_self_cover⟩⟩
  let f_enc : S' → ENat := fun C => (C : Set ℝ).encard
  have h1 : iInf f_enc = Metric.externalCoveringNumber δ' X := by
    rw [iInf_subtype] <;> rfl
  rcases ENat.exists_eq_iInf f_enc with ⟨C0, hC0_eq⟩
  have h2 : (C0 : Set ℝ).encard = Metric.externalCoveringNumber δ' X := by
    have h21 : f_enc C0 = (C0 : Set ℝ).encard := by rfl
    have h22 : f_enc C0 = iInf f_enc := hC0_eq
    rw [h21] at h22; rw [h22, h1]
  rcases h_main C0.val C0.property with ⟨C', hC'_cover, hC'_encard⟩
  have h3 : Metric.externalCoveringNumber δ' (f '' X) ≤ (C' : Set ℝ).encard :=
    IsCover.externalCoveringNumber_le_encard hC'_cover
  have h4 : Metric.externalCoveringNumber δ' (f '' X) ≤ (K : ENat) * Metric.externalCoveringNumber δ' X := by
    calc Metric.externalCoveringNumber δ' (f '' X)
      ≤ (C' : Set ℝ).encard := h3
    _ ≤ (K : ENat) * (C0 : Set ℝ).encard := hC'_encard
    _ = (K : ENat) * Metric.externalCoveringNumber δ' X := by rw [h2]
  have h5 : Ncover δ (f '' X) = ↑(Metric.externalCoveringNumber δ' (f '' X)) := by rfl
  have h6 : Ncover δ X = ↑(Metric.externalCoveringNumber δ' X) := by rfl
  rw [h5, h6]
  exact_mod_cast h4

/-- If `f` moves points by at most `c * δ` and `Y = f '' X`, then
`Ncover δ X ≤ K * Ncover δ Y` where `K = 2 * ⌈c⌉ + 3`. -/
lemma ncover_near_identity_lower {δ : ℝ} {X Y : Set ℝ} {f : ℝ → ℝ}
    (hδ : 0 < δ) {c : ℝ} (hc : 0 ≤ c)
    (h_perturb : ∀ x ∈ X, dist (f x) x ≤ c * δ) (hY : Y = f '' X) :
    Ncover δ X ≤ (2 * (Int.ceil c).toNat + 3 : ENNReal) * Ncover δ Y := by
  let δ' : NNReal := δ.toNNReal
  let K : ℕ := 2 * (Int.ceil c).toNat + 3
  have h_main : ∀ (C : Set ℝ), IsCover δ' Y C →
      ∃ (C' : Set ℝ), IsCover δ' X C' ∧ C'.encard ≤ (K : ENat) * C.encard := by
    intro C hC
    have h' : ∀ x ∈ X, ∃ c0 ∈ C, dist x c0 ≤ (c + 1) * δ := by
      intro x hx
      have hfy : f x ∈ Y := by rw [hY] <;> exact ⟨x, hx, rfl⟩
      have hdist : ∃ c0 ∈ C, edist (f x) c0 ≤ ↑δ' := hC hfy
      rcases hdist with ⟨c0, hc0, hedist⟩
      have h4 : dist (f x) c0 ≤ δ := by
        have h51 : edist (f x) c0 ≤ ↑δ' := hedist
        have h52 : edist (f x) c0 = ENNReal.ofReal (dist (f x) c0) := by rw [edist_dist]
        rw [h52] at h51
        have h53 : (↑δ' : ENNReal) = ENNReal.ofReal δ := by
          simp [δ', hδ.le] <;> norm_cast
        rw [h53] at h51
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h51
      have h6 : dist x c0 ≤ (c + 1) * δ := by
        have h7 : dist x (f x) ≤ c * δ := by
          simpa [dist_comm] using h_perturb x hx
        calc dist x c0
          ≤ dist x (f x) + dist (f x) c0 := dist_triangle x (f x) c0
        _ ≤ c * δ + δ := by gcongr
        _ = (c + 1) * δ := by ring
      exact ⟨c0, hc0, h6⟩
    exact near_identity_cover hδ hc h'
  let S' := {C : Set ℝ // IsCover δ' Y C}
  have h_self_cover : IsCover δ' Y Y := by
    intro z hz; exact ⟨z, hz, by simp⟩
  have hS'_nonempty : Nonempty S' := by refine' ⟨⟨Y, h_self_cover⟩⟩
  let f_enc : S' → ENat := fun C => (C : Set ℝ).encard
  have h1 : iInf f_enc = Metric.externalCoveringNumber δ' Y := by
    rw [iInf_subtype] <;> rfl
  rcases ENat.exists_eq_iInf f_enc with ⟨C0, hC0_eq⟩
  have h2 : (C0 : Set ℝ).encard = Metric.externalCoveringNumber δ' Y := by
    have h21 : f_enc C0 = (C0 : Set ℝ).encard := by rfl
    have h22 : f_enc C0 = iInf f_enc := hC0_eq
    rw [h21] at h22; rw [h22, h1]
  rcases h_main C0.val C0.property with ⟨C', hC'_cover, hC'_encard⟩
  have h3 : Metric.externalCoveringNumber δ' X ≤ (C' : Set ℝ).encard :=
    IsCover.externalCoveringNumber_le_encard hC'_cover
  have h4 : Metric.externalCoveringNumber δ' X ≤ (K : ENat) * Metric.externalCoveringNumber δ' Y := by
    calc Metric.externalCoveringNumber δ' X
      ≤ (C' : Set ℝ).encard := h3
    _ ≤ (K : ENat) * (C0 : Set ℝ).encard := hC'_encard
    _ = (K : ENat) * Metric.externalCoveringNumber δ' Y := by rw [h2]
  have h5 : Ncover δ X = ↑(Metric.externalCoveringNumber δ' X) := by rfl
  have h6 : Ncover δ Y = ↑(Metric.externalCoveringNumber δ' Y) := by rfl
  rw [h5, h6]
  exact_mod_cast h4

/-! ### IsDeltaSSet transfer under near-identity perturbation -/

/-- IsDeltaSSet is preserved under a `c·δ`-perturbation, with constant degraded by
`K^2 * (1+c)^s` where `K = 2⌈c⌉+3`. Also gives a lower bound on Ncover. -/
lemma isDeltaSSet_near_identity_transfer {δ s C : ℝ} {X Y : Set ℝ} {f : ℝ → ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) {c : ℝ} (hc : 0 ≤ c)
    (hX_sset : IsDeltaSSet δ s C X)
    (h_perturb : ∀ x ∈ X, dist (f x) x ≤ c * δ)
    (hY : Y = f '' X) :
    IsDeltaSSet δ s (C * ((2 * (Int.ceil c).toNat + 3 : ℝ)^2) * (1 + c)^s) Y ∧
    Ncover δ X ≤ (2 * (Int.ceil c).toNat + 3 : ENNReal) * Ncover δ Y := by
  let K : ℕ := 2 * (Int.ceil c).toNat + 3
  let C' : ℝ := C * (K : ℝ)^2 * (1 + c)^s
  have hK_def : (K : ENNReal) = (2 * (Int.ceil c).toNat + 3 : ENNReal) := by
    simp [K] <;> norm_cast
  have hX_nonempty : X.Nonempty := hX_sset.1
  have hC_pos : 0 < C := hX_sset.2.2.1
  have hY_nonempty : Y.Nonempty := by
    rcases hX_nonempty with ⟨x, hx⟩
    exact ⟨f x, by rw [hY] <;> exact ⟨x, hx, rfl⟩⟩
  have hC'_pos : 0 < C * ((K : ℝ)^2) * (1 + c)^s := by positivity
  have h_lower : Ncover δ X ≤ (K : ENNReal) * Ncover δ Y := by
    have h := ncover_near_identity_lower hδ hc h_perturb hY
    simpa [K] using h
  have h_main_cover : ∀ (y : ℝ) (r : ℝ), δ ≤ r →
      Ncover δ (Y ∩ closedBall y r) ≤
        ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * Ncover δ Y := by
    intro y r hr
    have hr_pos : 0 < r := by linarith
    have hrc : 0 ≤ r := by linarith
    have h1pc : 0 ≤ 1 + c := by linarith
    have h4 : r + c * δ ≤ (1 + c) * r := by
      have h5 : δ ≤ r := hr
      have h6 : c * δ ≤ c * r := by gcongr
      linarith
    have h_subset : Y ∩ closedBall y r ⊆ f '' (X ∩ closedBall y (r + c * δ)) := by
      intro z hz
      have hz1 : z ∈ Y := hz.1
      have hz2 : dist z y ≤ r := hz.2
      have hzy : z ∈ f '' X := by rw [← hY] <;> exact hz1
      rcases hzy with ⟨x, hx, rfl⟩
      have h5 : dist (f x) y ≤ r := hz2
      have h6 : dist x y ≤ r + c * δ := by
        have h7 : dist x y ≤ dist x (f x) + dist (f x) y := dist_triangle x (f x) y
        have h8 : dist x (f x) ≤ c * δ := by
          simpa [dist_comm] using h_perturb x hx
        linarith
      have h9 : x ∈ X ∩ closedBall y (r + c * δ) := ⟨hx, h6⟩
      exact ⟨x, h9, rfl⟩
    have h_perturb' : ∀ (x : ℝ), x ∈ (X ∩ closedBall y (r + c * δ)) → dist (f x) x ≤ c * δ := by
      intro x hx
      have h_x_in_X : x ∈ X := by
        simp only [Set.mem_inter_iff] at hx <;> tauto
      exact h_perturb x h_x_in_X
    have h1 : Ncover δ (Y ∩ closedBall y r) ≤
        Ncover δ (f '' (X ∩ closedBall y (r + c * δ))) :=
      ncover_mono h_subset
    have h2_raw : Ncover δ (f '' (X ∩ closedBall y (r + c * δ))) ≤
        (2 * (Int.ceil c).toNat + 3 : ENNReal) * Ncover δ (X ∩ closedBall y (r + c * δ)) :=
      ncover_near_identity_upper hδ hc h_perturb'
    have h2 : Ncover δ (f '' (X ∩ closedBall y (r + c * δ))) ≤
        (K : ENNReal) * Ncover δ (X ∩ closedBall y (r + c * δ)) := by
      rw [hK_def] at *; exact h2_raw
    have h_δ_le : δ ≤ r + c * δ := by
      have h1 : 0 ≤ c * δ := by positivity
      have h2 : δ ≤ r := hr
      linarith
    have h3 : Ncover δ (X ∩ closedBall y (r + c * δ)) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (r + c * δ)) ^ s * Ncover δ X :=
      hX_sset.2.2.2.2 y (r + c * δ) h_δ_le
    have h5 : (ENNReal.ofReal (r + c * δ)) ^ s ≤
        ENNReal.ofReal ((1 + c)^s) * (ENNReal.ofReal r) ^ s := by
      have h6 : (ENNReal.ofReal (r + c * δ)) ^ s ≤ (ENNReal.ofReal ((1 + c) * r)) ^ s := by
        gcongr <;> exact_mod_cast h4
      have h7 : (ENNReal.ofReal ((1 + c) * r)) ^ s =
          ENNReal.ofReal (((1 + c) * r) ^ s) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hs]
      have h8 : ((1 + c) * r) ^ s = (1 + c)^s * r ^ s := by
        rw [← Real.mul_rpow h1pc hrc] <;> ring
      have h11 : ENNReal.ofReal (((1 + c) * r) ^ s) =
          ENNReal.ofReal ((1 + c)^s) * (ENNReal.ofReal r) ^ s := by
        rw [h8]
        have h12 : 0 ≤ (1 + c)^s := by positivity
        have h13 : 0 ≤ r ^ s := by positivity
        rw [ENNReal.ofReal_mul h12, ENNReal.ofReal_rpow_of_nonneg hrc hs] <;> ring
      calc (ENNReal.ofReal (r + c * δ)) ^ s
        ≤ (ENNReal.ofReal ((1 + c) * r)) ^ s := h6
      _ = ENNReal.ofReal (((1 + c) * r) ^ s) := h7
      _ = ENNReal.ofReal ((1 + c)^s) * (ENNReal.ofReal r) ^ s := h11
    have h_nonneg1 : 0 ≤ C := by linarith
    have h_nonneg2 : 0 ≤ (1 + c)^s := by positivity
    have h6 : Ncover δ (X ∩ closedBall y (r + c * δ)) ≤
        ENNReal.ofReal (C * (1 + c)^s) * (ENNReal.ofReal r) ^ s * Ncover δ X := by
      calc Ncover δ (X ∩ closedBall y (r + c * δ))
        ≤ ENNReal.ofReal C * (ENNReal.ofReal (r + c * δ)) ^ s * Ncover δ X := h3
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal ((1 + c)^s) * (ENNReal.ofReal r) ^ s) * Ncover δ X := by
          gcongr <;> exact h5
      _ = ENNReal.ofReal (C * (1 + c)^s) * (ENNReal.ofReal r) ^ s * Ncover δ X := by
          have h14 : ENNReal.ofReal C * ENNReal.ofReal ((1 + c)^s) = ENNReal.ofReal (C * (1 + c)^s) := by
            rw [← ENNReal.ofReal_mul h_nonneg1]
          have h15 : ENNReal.ofReal C * (ENNReal.ofReal ((1 + c)^s) * (ENNReal.ofReal r) ^ s) * Ncover δ X =
              (ENNReal.ofReal C * ENNReal.ofReal ((1 + c)^s)) * (ENNReal.ofReal r) ^ s * Ncover δ X := by
            simp [mul_assoc] <;> ring
          rw [h15, h14] <;> simp [mul_assoc] <;> ring
    have h7 : Ncover δ (Y ∩ closedBall y r) ≤
        (K : ENNReal) * (ENNReal.ofReal (C * (1 + c)^s) * (ENNReal.ofReal r) ^ s * Ncover δ X) := by
      calc Ncover δ (Y ∩ closedBall y r)
        ≤ Ncover δ (f '' (X ∩ closedBall y (r + c * δ))) := h1
      _ ≤ (K : ENNReal) * Ncover δ (X ∩ closedBall y (r + c * δ)) := h2
      _ ≤ (K : ENNReal) * (ENNReal.ofReal (C * (1 + c)^s) * (ENNReal.ofReal r) ^ s * Ncover δ X) := by gcongr
    have h8 : Ncover δ (Y ∩ closedBall y r) ≤
        (K : ENNReal) * (ENNReal.ofReal (C * (1 + c)^s) * (ENNReal.ofReal r) ^ s * ((K : ENNReal) * Ncover δ Y)) := by
      calc Ncover δ (Y ∩ closedBall y r)
        ≤ (K : ENNReal) * (ENNReal.ofReal (C * (1 + c)^s) * (ENNReal.ofReal r) ^ s * Ncover δ X) := h7
      _ ≤ (K : ENNReal) * (ENNReal.ofReal (C * (1 + c)^s) * (ENNReal.ofReal r) ^ s * ((K : ENNReal) * Ncover δ Y)) := by
          gcongr <;> exact h_lower
    have h9 : ENNReal.ofReal C' = (K : ENNReal)^2 * ENNReal.ofReal (C * (1 + c)^s) := by
      have h10 : C' = C * (1 + c)^s * (K : ℝ)^2 := by
        simp [C'] <;> ring
      rw [h10]
      have h11 : 0 ≤ C * (1 + c)^s := by positivity
      have h12 : ENNReal.ofReal (C * (1 + c)^s * (K : ℝ)^2) =
          ENNReal.ofReal (C * (1 + c)^s) * ENNReal.ofReal ((K : ℝ)^2) := by
        rw [ENNReal.ofReal_mul h11]
      rw [h12]
      have h13 : ENNReal.ofReal ((K : ℝ)^2) = (K : ENNReal)^2 := by norm_cast
      rw [h13] <;> ring
    have h_final : Ncover δ (Y ∩ closedBall y r) ≤
        ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * Ncover δ Y := by
      calc Ncover δ (Y ∩ closedBall y r)
        ≤ (K : ENNReal) * (ENNReal.ofReal (C * (1 + c)^s) * (ENNReal.ofReal r) ^ s * ((K : ENNReal) * Ncover δ Y)) := h8
      _ = (K : ENNReal)^2 * ENNReal.ofReal (C * (1 + c)^s) * (ENNReal.ofReal r) ^ s * Ncover δ Y := by
          simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
      _ = ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * Ncover δ Y := by
          rw [h9] <;> simp [mul_assoc] <;> ring
    exact h_final
  have hC'_eq : C' = C * ((2 * (Int.ceil c).toNat + 3 : ℝ)^2) * (1 + c)^s := by
    simp [C', K] <;> ring
  have h_final_sset : IsDeltaSSet δ s (C * ((2 * (Int.ceil c).toNat + 3 : ℝ)^2) * (1 + c)^s) Y := by
    have h10 : IsDeltaSSet δ s C' Y := ⟨hY_nonempty, hδ, hC'_pos, hs, h_main_cover⟩
    rw [hC'_eq] at h10
    exact h10
  have h_final_lower : Ncover δ X ≤ (2 * (Int.ceil c).toNat + 3 : ENNReal) * Ncover δ Y := by
    rw [←hK_def]
    exact h_lower
  exact ⟨h_final_sset, h_final_lower⟩

end RobustKaufmanProjection.PerturbationGeneral
