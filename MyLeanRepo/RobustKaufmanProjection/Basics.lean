module

/-
  Basic infrastructure for the robust Kaufman projection lemma.

  Provides:
  - Re-exports of core definitions from the target file
  - Doubling property for covering numbers in the Euclidean plane
  - Extraction of a maximal δ-separated subset with ball-growth from IsDeltaSSet
  - Lipschitz property of the affine projection
  - Covering number monotonicity

  Whiteprint node: basics
  Dependencies: none
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace RobustKaufmanProjection

open MeasureTheory Metric Set

/-! ### Re-exports from target file -/

abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

def IsDeltaSSet {X : Type*} [PseudoMetricSpace X]
    (δ s C : ℝ) (P : Set X) : Prop :=
  P.Nonempty ∧ 0 < δ ∧ 0 < C ∧ 0 ≤ s ∧
    ∀ x : X, ∀ r : ℝ, δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal
          (P ∩ Metric.closedBall x r) : ℝ≥0∞) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞)

noncomputable def Ncover {X : Type*} [PseudoMetricSpace X]
    (δ : ℝ) (P : Set X) : ℝ≥0∞ :=
  Metric.externalCoveringNumber δ.toNNReal P

def affineProjection (σ : ℝ) (P : Set EuclideanPlane) : Set ℝ :=
  (fun p => p 0 - σ * p 1) '' P

def InUnitSquare (P : Set EuclideanPlane) : Prop :=
  P ⊆ {p | p 0 ∈ Set.Icc (0 : ℝ) 1 ∧ p 1 ∈ Set.Icc (0 : ℝ) 1}

/-! ### Grid covering for the doubling property -/

/-- For any `a ∈ [-δ, δ]`, there exists `k ∈ Fin 3` such that
`|a - (2k-2)δ/3| ≤ δ/3`. -/
lemma round_to_grid {a δ : ℝ} (hδ : 0 ≤ δ) (h : |a| ≤ δ) :
    ∃ (k : Fin 3), |a - (2 * (k : ℝ) - 2) * δ / 3| ≤ δ / 3 := by
  by_cases hδ0 : δ = 0
  · subst hδ0
    have h0 : |a| ≤ 0 := h
    have ha : a = 0 := by
      have h1 : -0 ≤ a ∧ a ≤ 0 := abs_le.mp h0
      linarith
    refine ⟨(0 : Fin 3), ?_⟩
    rw [ha] <;> norm_num
  have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
  have h1 : -δ ≤ a := (abs_le.mp h).1
  have h2 : a ≤ δ := (abs_le.mp h).2
  by_cases h3 : a ≤ -δ / 3
  · refine ⟨(0 : Fin 3), ?_⟩
    have h4 : |a + 2 * δ / 3| ≤ δ / 3 := by
      rw [abs_le] <;> constructor <;> linarith
    have h5 : (2 * ((0 : Fin 3) : ℝ) - 2) * δ / 3 = -2 * δ / 3 := by norm_num
    rw [h5]
    have h6 : a - (-2 * δ / 3) = a + 2 * δ / 3 := by ring
    rw [h6]; exact h4
  · have h3' : a > -δ / 3 := by linarith
    by_cases h4 : a ≤ δ / 3
    · refine ⟨(1 : Fin 3), ?_⟩
      have h5 : |a| ≤ δ / 3 := by
        rw [abs_le] <;> constructor <;> linarith
      have h6 : (2 * ((1 : Fin 3) : ℝ) - 2) * δ / 3 = 0 := by norm_num
      rw [h6] <;> simpa using h5
    · refine ⟨(2 : Fin 3), ?_⟩
      have h7 : |a - 2 * δ / 3| ≤ δ / 3 := by
        rw [abs_le] <;> constructor <;> linarith
      have h8 : (2 * ((2 : Fin 3) : ℝ) - 2) * δ / 3 = 2 * δ / 3 := by norm_num
      rw [h8] <;> exact h7

/-- The set of 9 centers forming a 3×3 grid around `c` with spacing `2δ/3`. -/
noncomputable
def nineCenters (δ : ℝ) (c : EuclideanPlane) : Set EuclideanPlane :=
  Set.image (fun (p : Fin 3 × Fin 3) =>
    let e0 : EuclideanPlane := EuclideanSpace.single 0 1
    let e1 : EuclideanPlane := EuclideanSpace.single 1 1
    c + ((2 * (p.1 : ℝ) - 2) * δ / 3) • e0 + ((2 * (p.2 : ℝ) - 2) * δ / 3) • e1)
    Set.univ

lemma nineCenters_encard_le_nine (δ : ℝ) (c : EuclideanPlane) :
    (nineCenters δ c).encard ≤ 9 := by
  have h1 : (nineCenters δ c).encard ≤ (Set.univ : Set (Fin 3 × Fin 3)).encard :=
    Set.encard_image_le _ _
  have h2 : (Set.univ : Set (Fin 3 × Fin 3)).encard ≤ 9 := by
    have hfin : (Set.univ : Set (Fin 3 × Fin 3)).Finite := Set.toFinite _
    have h3 : (Set.univ : Set (Fin 3 × Fin 3)).encard = ↑(hfin.toFinset.card) := by exact Finite.encard_eq_coe_toFinset_card hfin
    rw [h3] <;> simp [hfin] <;> decide
  exact le_trans h1 h2

/-- A closed ball of radius `δ` in the Euclidean plane can be covered by
9 closed balls of radius `δ/2`, using a 3×3 grid. -/
lemma ball_covered_by_nine (δ : ℝ) (c : EuclideanPlane) (hδ : 0 ≤ δ) :
    IsCover (δ / 2).toNNReal (closedBall c δ) (nineCenters δ c) := by
  rw [isCover_iff_subset_iUnion_closedBall]
  intro z hz
  have h_dist : ‖z - c‖ ≤ δ := hz
  let w : EuclideanPlane := z - c
  have hwnorm : ‖w‖ ≤ δ := h_dist
  have h_coord0 : |w 0| ≤ ‖w‖ := PiLp.norm_apply_le w 0
  have h_coord1 : |w 1| ≤ ‖w‖ := PiLp.norm_apply_le w 1
  have h0 : |w 0| ≤ δ := by linarith
  have h1 : |w 1| ≤ δ := by linarith
  rcases round_to_grid hδ h0 with ⟨k0, hk0⟩
  rcases round_to_grid hδ h1 with ⟨k1, hk1⟩
  let e0 : EuclideanPlane := EuclideanSpace.single 0 1
  let e1 : EuclideanPlane := EuclideanSpace.single 1 1
  let a0 : ℝ := (2 * (k0 : ℝ) - 2) * δ / 3
  let a1 : ℝ := (2 * (k1 : ℝ) - 2) * δ / 3
  let d : EuclideanPlane := c + a0 • e0 + a1 • e1
  have hd_in : d ∈ nineCenters δ c := by
    have himg : d ∈ Set.image (fun (p : Fin 3 × Fin 3) =>
        let e0 : EuclideanPlane := EuclideanSpace.single 0 1
        let e1 : EuclideanPlane := EuclideanSpace.single 1 1
        c + ((2 * (p.1 : ℝ) - 2) * δ / 3) • e0 + ((2 * (p.2 : ℝ) - 2) * δ / 3) • e1) Set.univ := by
      exact ⟨(k0, k1), by trivial, by simp [d, e0, e1, a0, a1]⟩
    exact himg
  have h_est0 : |w 0 - a0| ≤ δ / 3 := by simpa [a0] using hk0
  have h_est1 : |w 1 - a1| ≤ δ / 3 := by simpa [a1] using hk1
  have h_cd0 : (d - c) 0 = a0 := by
    simp [d, e0, e1, EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply] <;> aesop
  have h_cd1 : (d - c) 1 = a1 := by
    simp [d, e0, e1, EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply] <;> aesop
  have h_dist2 : ‖z - d‖ ≤ δ / 2 := by
    let v : EuclideanPlane := w - (d - c)
    have hv0 : v 0 = w 0 - a0 := by simp [v, PiLp.sub_apply, h_cd0]
    have hv1 : v 1 = w 1 - a1 := by simp [v, PiLp.sub_apply, h_cd1]
    have h_norm2 : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq v, Fin.sum_univ_two]
    have h_sq : ‖v‖ ^ 2 ≤ (δ / 2) ^ 2 := by
      rw [h_norm2, hv0, hv1]
      have h3 : (w 0 - a0) ^ 2 ≤ (δ / 3) ^ 2 := by
        have h31 : |w 0 - a0| ≤ δ / 3 := h_est0
        have h32 : |w 0 - a0| ^ 2 ≤ (δ / 3) ^ 2 := by gcongr <;> positivity
        have h33 : |w 0 - a0| ^ 2 = (w 0 - a0) ^ 2 := by rw [sq_abs]
        rw [h33] at h32; exact h32
      have h4 : (w 1 - a1) ^ 2 ≤ (δ / 3) ^ 2 := by
        have h41 : |w 1 - a1| ≤ δ / 3 := h_est1
        have h42 : |w 1 - a1| ^ 2 ≤ (δ / 3) ^ 2 := by gcongr <;> positivity
        have h43 : |w 1 - a1| ^ 2 = (w 1 - a1) ^ 2 := by rw [sq_abs]
        rw [h43] at h42; exact h42
      have h5 : 2 * (δ / 3) ^ 2 ≤ (δ / 2) ^ 2 := by
        have h7 : (2 / 9 : ℝ) ≤ (1 / 4 : ℝ) := by norm_num
        have h8 : 0 ≤ δ ^ 2 := by positivity
        calc
          2 * (δ / 3) ^ 2 = (2 / 9 : ℝ) * δ ^ 2 := by ring
          _ ≤ (1 / 4 : ℝ) * δ ^ 2 := by gcongr
          _ = (δ / 2) ^ 2 := by ring
      linarith
    have h5 : 0 ≤ ‖v‖ := by positivity
    have h6 : 0 ≤ δ / 2 := by positivity
    have h_eq : ‖z - d‖ = ‖v‖ := by
      have h9 : z - d = v := by simp [v, w, sub_sub_sub_cancel_left]
      rw [h9]
    rw [h_eq]
    nlinarith [sq_nonneg (‖v‖ - δ / 2)]
  have h_nonneg2 : 0 ≤ δ / 2 := by positivity
  have h_rad : (↑((δ / 2).toNNReal) : ℝ) = δ / 2 := by exact Real.coe_toNNReal (δ / 2) h_nonneg2
  have h_z_in : z ∈ closedBall d (δ / 2).toNNReal := by
    have h_dist' : dist z d ≤ ↑(δ / 2).toNNReal := by
      rw [dist_eq_norm, h_rad]; exact h_dist2
    exact h_dist'
  exact Set.mem_iUnion₂.mpr ⟨d, hd_in, h_z_in⟩

/-- Doubling property for external covering numbers in the Euclidean plane:
covering at half the radius costs at most a factor of 9. -/
lemma externalCoveringNumber_half_le_plane (A : Set EuclideanPlane) (δ : NNReal) :
    externalCoveringNumber (δ / 2) A ≤ 9 * externalCoveringNumber δ A := by
  by_cases h_top : externalCoveringNumber δ A = ⊤
  · rw [h_top] <;> simp
  · have hfin : ∃ (n : ℕ), externalCoveringNumber δ A = ↑n := by exact Option.ne_none_iff_exists'.mp h_top
    rcases hfin with ⟨n, hn⟩
    have h1 : (↑n : ℕ∞) < ↑(n + 1) := by exact_mod_cast Nat.lt_succ_self n
    have h2 : ¬ (↑(n + 1) : ℕ∞) ≤ externalCoveringNumber δ A := by
      rw [hn]; exact not_le.mpr h1
    have h3 : ∃ (C : Set EuclideanPlane), IsCover δ A C ∧ ¬ (↑(n + 1) : ℕ∞) ≤ C.encard := by
      simpa [externalCoveringNumber, le_iInf_iff] using h2
    rcases h3 with ⟨C, hC, hlt⟩
    have h4 : C.encard < ↑(n + 1) := by exact Std.not_le.mp hlt
    have h5 : externalCoveringNumber δ A ≤ C.encard := IsCover.externalCoveringNumber_le_encard hC
    have h6 : (↑n : ℕ∞) ≤ C.encard := by rw [hn] at h5; exact h5
    have h7 : C.encard = ↑n := by
      have h_ne_top : C.encard ≠ ⊤ := by
        intro h_top2; rw [h_top2] at h4; simp at h4
      have h_exists : ∃ (m : ℕ), C.encard = ↑m := by exact Option.ne_none_iff_exists'.mp h_ne_top
      rcases h_exists with ⟨m, hm⟩
      rw [hm] at h6 h4
      have hmn : n ≤ m := by exact_mod_cast h6
      have hmn2 : m < n + 1 := by exact_mod_cast h4
      have hmeq : m = n := by omega
      rw [hmeq] at hm; exact hm
    let D : Set EuclideanPlane := {d | ∃ c ∈ C, d ∈ nineCenters (δ : ℝ) c}
    have hD_cover : IsCover (δ / 2) A D := by
      rw [isCover_iff_subset_iUnion_closedBall]
      intro z hz
      have hU : A ⊆ ⋃ c ∈ C, closedBall c (δ : ℝ) :=
        (isCover_iff_subset_iUnion_closedBall.mp hC)
      rcases Set.mem_iUnion₂.mp (hU hz) with ⟨c, hcC, hzc⟩
      have h_rad_eq : ((↑δ / 2 : ℝ).toNNReal) = δ / 2 := by ext <;> simp <;> positivity
      have h9 : IsCover (δ / 2) (closedBall c (δ : ℝ)) (nineCenters (δ : ℝ) c) := by
        rw [← h_rad_eq]; exact ball_covered_by_nine (δ : ℝ) c (by positivity)
      have h10 : closedBall c (δ : ℝ) ⊆ ⋃ d ∈ nineCenters (δ : ℝ) c, closedBall d (δ / 2) :=
        (isCover_iff_subset_iUnion_closedBall.mp h9)
      rcases Set.mem_iUnion₂.mp (h10 hzc) with ⟨d, hd_in, hdz⟩
      have hD_in : d ∈ D := ⟨c, hcC, hd_in⟩
      exact Set.mem_iUnion₂.mpr ⟨d, hD_in, hdz⟩
    let f : EuclideanPlane × (Fin 3 × Fin 3) → EuclideanPlane := fun p =>
      let e0 : EuclideanPlane := EuclideanSpace.single 0 1
      let e1 : EuclideanPlane := EuclideanSpace.single 1 1
      p.1 + ((2 * (p.2.1 : ℝ) - 2) * (δ : ℝ) / 3) • e0
          + ((2 * (p.2.2 : ℝ) - 2) * (δ : ℝ) / 3) • e1
    have hD_subset : D ⊆ Set.image f (C ×ˢ (Set.univ : Set (Fin 3 × Fin 3))) := by
      intro d hd
      rcases hd with ⟨c, hcC, hdnine⟩
      have h_exists : ∃ (p : Fin 3 × Fin 3), p ∈ (Set.univ : Set (Fin 3 × Fin 3)) ∧ f (c, p) = d := by
        simpa [nineCenters, f] using hdnine
      rcases h_exists with ⟨p, hp, rfl⟩
      exact Set.mem_image_of_mem f ⟨hcC, hp⟩
    have hD_encard : D.encard ≤ 9 * C.encard := by
      have h1 : D.encard ≤ (Set.image f (C ×ˢ (Set.univ : Set (Fin 3 × Fin 3)))).encard :=
        Set.encard_mono hD_subset
      have h2 : (Set.image f (C ×ˢ (Set.univ : Set (Fin 3 × Fin 3)))).encard ≤
                  (C ×ˢ (Set.univ : Set (Fin 3 × Fin 3))).encard := Set.encard_image_le _ _
      have h3 : (C ×ˢ (Set.univ : Set (Fin 3 × Fin 3))).encard =
                  C.encard * (Set.univ : Set (Fin 3 × Fin 3)).encard := Set.encard_prod
      have h4 : (Set.univ : Set (Fin 3 × Fin 3)).encard ≤ 9 := by
        have hfin : (Set.univ : Set (Fin 3 × Fin 3)).Finite := Set.toFinite _
        have h5 : (Set.univ : Set (Fin 3 × Fin 3)).encard = ↑(hfin.toFinset.card) := by exact Finite.encard_eq_coe_toFinset_card hfin
        rw [h5] <;> simp [hfin] <;> decide
      calc
        D.encard ≤ (Set.image f (C ×ˢ Set.univ)).encard := h1
        _ ≤ (C ×ˢ (Set.univ : Set (Fin 3 × Fin 3))).encard := h2
        _ = C.encard * (Set.univ : Set (Fin 3 × Fin 3)).encard := h3
        _ ≤ C.encard * 9 := by gcongr
        _ = 9 * C.encard := by ring
    have h_main : externalCoveringNumber (δ / 2) A ≤ D.encard :=
      IsCover.externalCoveringNumber_le_encard hD_cover
    have h_final : D.encard ≤ 9 * externalCoveringNumber δ A := by
      have h10 : 9 * C.encard = 9 * externalCoveringNumber δ A := by
        calc 9 * C.encard = 9 * (↑n : ℕ∞) := by rw [h7]
             _ = 9 * externalCoveringNumber δ A := by rw [hn]
      rw [h10] at hD_encard
      exact hD_encard
    exact le_trans h_main h_final

/-! ### IsDeltaSSet to ball-growth on separated subset -/

/-- Extract a maximal δ-separated finite subset `S` of `P` with ball-growth.

Given `h : IsDeltaSSet δ t C P`, produces `S : Finset EuclideanPlane` such that:
- `S ⊆ P`
- `S` is δ-separated
- `Ncover δ P ≤ S.card`
- For all `p ∈ S` and `r ≥ δ`, the number of points of `S` in `closedBall p r`
  is at most `9 * C * r^t * S.card`.

The factor 9 comes from the doubling property of covering numbers in ℝ². -/
theorem IsDeltaSSet.to_ball_growth {δ t C : ℝ} {P : Set EuclideanPlane}
    (h : IsDeltaSSet δ t C P) (hP_bounded : Bornology.IsBounded P) :
    ∃ (S : Finset EuclideanPlane),
      (S : Set EuclideanPlane) ⊆ P ∧
      S.Nonempty ∧
      (∀ p ∈ S, ∀ q ∈ S, p ≠ q → δ ≤ ‖p - q‖) ∧
      (Ncover δ P ≤ (S.card : ENNReal)) ∧
      (∀ p ∈ S, ∀ r : ℝ, δ ≤ r →
        (S.filter (fun q => ‖p - q‖ ≤ r)).card ≤ (9 * C) * r ^ t * S.card) := by
  have hδpos : 0 < δ := h.2.1
  have hCpos : 0 < C := h.2.2.1
  have hs_nonneg : 0 ≤ t := h.2.2.2.1
  have hPnonempty : P.Nonempty := h.1
  let δ' : NNReal := ⟨δ, hδpos.le⟩
  have hδ'_co : (δ' : ℝ) = δ := by rfl
  have hδ'pos : 0 < δ' := by exact_mod_cast hδpos
  have hP_tb : TotallyBounded P := by
    rcases hP_bounded.subset_closedBall (0 : EuclideanPlane) with ⟨R, hR⟩
    have hK : IsCompact (Metric.closedBall (0 : EuclideanPlane) R) :=
      isCompact_closedBall (0 : EuclideanPlane) R
    have hTB : TotallyBounded (Metric.closedBall (0 : EuclideanPlane) R) :=
      hK.totallyBounded
    exact hTB.subset hR
  have h_ec_ne_top : externalCoveringNumber (δ' / 2) P ≠ ⊤ := by
    have hhalf_pos : 0 < δ' / 2 := by positivity
    have hfc := exists_finite_isCover_of_totallyBounded hhalf_pos.ne' hP_tb
    rcases hfc with ⟨N, _, hNfin, hNcover⟩
    have h : externalCoveringNumber (δ' / 2) P ≤ N.encard :=
      IsCover.externalCoveringNumber_le_encard hNcover
    have h2 : N.encard ≠ ⊤ := by exact encard_ne_top_iff.mpr hNfin
    exact ne_top_of_le_ne_top h2 h
  have hmul : 2 * (δ' / 2) = δ' := by
    apply NNReal.coe_injective; simp [hδ'_co] <;> ring
  have h_pack_ne_top : packingNumber δ' P ≠ ⊤ := by
    have h : packingNumber (2 * (δ' / 2)) P ≤ externalCoveringNumber (δ' / 2) P :=
      packingNumber_two_mul_le_externalCoveringNumber (δ' / 2) P
    rw [hmul] at h
    exact ne_top_of_le_ne_top h_ec_ne_top h
  let S : Set EuclideanPlane := maximalSeparatedSet δ' P
  have hS_subset : S ⊆ P := maximalSeparatedSet_subset
  have hS_sep : IsSeparated δ' S := isSeparated_maximalSeparatedSet
  have hS_encard : S.encard = packingNumber δ' P := encard_maximalSeparatedSet h_pack_ne_top
  have hS_cover : IsCover δ' P S := isCover_maximalSeparatedSet h_pack_ne_top
  have hS_finite : S.Finite := by
    have h : S.encard ≠ ⊤ := by rw [hS_encard] <;> exact h_pack_ne_top
    exact encard_ne_top_iff.mp h
  have hS_nonempty : S.Nonempty := hS_cover.nonempty hPnonempty
  classical
  let Sfin : Finset EuclideanPlane := hS_finite.toFinset
  have hSfin_eq : (Sfin : Set EuclideanPlane) = S := by simp [Sfin]
  have hSfin_card : S.encard = ↑Sfin.card := by rw [← hSfin_eq] <;> simp
  have hSfin_pos : 0 < Sfin.card := by
    have h : 0 < S.encard := by
      have h' : 0 < packingNumber δ' P := packingNumber_pos_iff.mpr hPnonempty
      rw [hS_encard] <;> exact h'
    rw [hSfin_card] at h
    exact_mod_cast h
  have hNcover_le : Ncover δ P ≤ (Sfin.card : ENNReal) := by
    have h1 : externalCoveringNumber δ' P ≤ S.encard :=
      IsCover.externalCoveringNumber_le_encard hS_cover
    have hδ'_eq : δ' = δ.toNNReal := by ext <;> simp [δ', hδ'_co] <;> linarith
    rw [hδ'_eq] at h1
    rw [hSfin_card] at h1
    have h2 : (↑(externalCoveringNumber δ.toNNReal P) : ENNReal) ≤ (↑Sfin.card : ENNReal) := by
      exact_mod_cast h1
    simpa [Ncover] using h2
  have h_sep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → δ ≤ ‖p - q‖ := by
    intro p hp q hq hne
    have h_edist : (δ' : ENNReal) < edist p q := hS_sep hp hq hne
    have h_dist : edist p q = ENNReal.ofReal ‖p - q‖ := by
      rw [edist_dist] <;> rfl
    rw [h_dist] at h_edist
    have h_coe : (↑δ' : ENNReal) = ENNReal.ofReal (δ' : ℝ) := by
      simp
    rw [h_coe] at h_edist
    have h_pos : 0 < ‖p - q‖ := by
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have h' : (δ' : ℝ) < ‖p - q‖ := by
      exact (ENNReal.ofReal_lt_ofReal_iff h_pos).mp h_edist
    have h2 : (δ' : ℝ) = δ := hδ'_co
    rw [h2] at h'
    exact le_of_lt h'
  have h_ball_growth : ∀ p ∈ S, ∀ r : ℝ, δ ≤ r →
      (Sfin.filter (fun q => ‖p - q‖ ≤ r)).card ≤ (9 * C) * r ^ t * Sfin.card := by
    intro p hp r hr
    have hrpos : 0 < r := by linarith
    have hrnonneg : 0 ≤ r := by linarith
    let B : Set EuclideanPlane := closedBall p r
    let T : Finset EuclideanPlane := Sfin.filter (fun q => ‖p - q‖ ≤ r)
    have hT_eq : (T : Set EuclideanPlane) = S ∩ B := by
      ext x
      have h_xin : x ∈ Sfin ↔ x ∈ S := by
        have h : x ∈ (Sfin : Set EuclideanPlane) ↔ x ∈ S := by rw [hSfin_eq]
        simpa using h
      simp only [T, Finset.mem_coe, Finset.mem_filter, h_xin, Set.mem_inter_iff, Set.mem_setOf_eq]
      have hB : x ∈ B ↔ ‖x - p‖ ≤ r := by
        simp [B, dist_eq_norm]
      have h_comm : ‖x - p‖ = ‖p - x‖ := by exact norm_sub_rev x p
      have h_goal : (x ∈ S ∧ ‖p - x‖ ≤ r) ↔ (x ∈ S ∧ x ∈ B) := by
        constructor
        · rintro ⟨hxS, hxr⟩
          exact ⟨hxS, hB.mpr (by rw [h_comm] <;> exact hxr)⟩
        · rintro ⟨hxS, hxB⟩
          exact ⟨hxS, by have h := hB.mp hxB; rw [h_comm] at h; exact h⟩
      exact h_goal
    have hT_subset_PB : (T : Set EuclideanPlane) ⊆ P ∩ B := by
      rw [hT_eq]
      intro y hy
      exact ⟨hS_subset hy.1, hy.2⟩
    have hT_sep : IsSeparated δ' (T : Set EuclideanPlane) := by
      rw [hT_eq]
      exact IsSeparated.subset (show S ∩ B ⊆ S from fun y hy => hy.1) hS_sep
    have h1 : (T : Set EuclideanPlane).encard ≤ packingNumber δ' (P ∩ B) :=
      IsSeparated.encard_le_packingNumber hT_subset_PB hT_sep
    have h2 : packingNumber δ' (P ∩ B) ≤ externalCoveringNumber (δ' / 2) (P ∩ B) := by
      have h2' : packingNumber (2 * (δ' / 2)) (P ∩ B) ≤
          externalCoveringNumber (δ' / 2) (P ∩ B) :=
        packingNumber_two_mul_le_externalCoveringNumber (δ' / 2) (P ∩ B)
      rw [hmul] at h2'; exact h2'
    have h3 : externalCoveringNumber (δ' / 2) (P ∩ B) ≤ 9 * externalCoveringNumber δ' (P ∩ B) :=
      externalCoveringNumber_half_le_plane (P ∩ B) δ'
    have hδ'_eq : δ' = δ.toNNReal := by ext <;> simp [δ', hδ'_co] <;> linarith
    have h4 : (externalCoveringNumber δ' (P ∩ B) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (externalCoveringNumber δ' P : ENNReal) := by
      have h5 := h.2.2.2.2 p r hr
      rw [hδ'_eq] at *; exact h5
    have h5 : externalCoveringNumber δ' P ≤ S.encard :=
      IsCover.externalCoveringNumber_le_encard hS_cover
    have h_rpow : (ENNReal.ofReal r) ^ t = ENNReal.ofReal (r ^ t) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hrnonneg hs_nonneg]
    have h9C : (9 : ENNReal) * ENNReal.ofReal C = ENNReal.ofReal (9 * C) := by
      have h11 : 0 ≤ C := by linarith
      have h12 : ENNReal.ofReal (9 * C) = (9 : ENNReal) * ENNReal.ofReal C := by
        simp [ENNReal.ofReal_mul h11] <;> norm_num
      exact h12.symm
    have h6 : (↑T.card : ENNReal) ≤
        ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ t) * (↑Sfin.card : ENNReal) := by
      have h1' : (↑T.card : ENNReal) ≤ ↑(packingNumber δ' (P ∩ B)) := by
        have h1'' : (T : Set EuclideanPlane).encard ≤ packingNumber δ' (P ∩ B) := h1
        have h_eq : (T : Set EuclideanPlane).encard = ↑T.card := by simp
        rw [h_eq] at h1''
        exact_mod_cast h1''
      have h2' : (↑(packingNumber δ' (P ∩ B)) : ENNReal) ≤
          (↑(externalCoveringNumber (δ' / 2) (P ∩ B)) : ENNReal) := by exact_mod_cast h2
      have h3' : ↑(externalCoveringNumber (δ' / 2) (P ∩ B)) ≤
          (9 : ENNReal) * ↑(externalCoveringNumber δ' (P ∩ B)) := by exact_mod_cast h3
      have h4' : (↑(externalCoveringNumber δ' (P ∩ B)) : ENNReal) ≤
          ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (↑Sfin.card : ENNReal) := by
        calc
          (↑(externalCoveringNumber δ' (P ∩ B)) : ENNReal)
            ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (↑(externalCoveringNumber δ' P) : ENNReal) := h4
          _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (↑Sfin.card : ENNReal) := by
            gcongr
            have h61 : (↑(externalCoveringNumber δ' P) : ENNReal) ≤ (↑Sfin.card : ENNReal) := by
              exact_mod_cast (le_trans h5 (le_of_eq hSfin_card))
            exact h61
      calc
        (↑T.card : ENNReal)
          ≤ ↑(packingNumber δ' (P ∩ B)) := h1'
        _ ≤ ↑(externalCoveringNumber (δ' / 2) (P ∩ B)) := h2'
        _ ≤ (9 : ENNReal) * ↑(externalCoveringNumber δ' (P ∩ B)) := h3'
        _ ≤ (9 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (↑Sfin.card : ENNReal)) := by gcongr
        _ = ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ t) * (↑Sfin.card : ENNReal) := by
          have h_eq : (9 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (↑Sfin.card : ENNReal)) =
              ((9 : ENNReal) * ENNReal.ofReal C) * (ENNReal.ofReal r) ^ t * (↑Sfin.card : ENNReal) := by ring
          rw [h_eq, h9C, h_rpow] <;> ring
    have h_bound_real : 0 ≤ (9 * C) * r ^ t * (Sfin.card : ℝ) := by positivity
    have h8 : ENNReal.ofReal ((9 * C) * r ^ t * (Sfin.card : ℝ)) =
        ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ t) * (↑Sfin.card : ENNReal) := by
      have h_pos1 : 0 ≤ 9 * C := by positivity
      have h_pos2 : 0 ≤ r ^ t := by positivity
      have h_pos3 : 0 ≤ (Sfin.card : ℝ) := by positivity
      have h_parse : (9 * C) * r ^ t * (Sfin.card : ℝ) = (9 * C) * (r ^ t * (Sfin.card : ℝ)) := by ring
      rw [h_parse]
      have h_step1 : ENNReal.ofReal ((9 * C) * (r ^ t * (Sfin.card : ℝ))) =
          ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ t * (Sfin.card : ℝ)) := by
        rw [ENNReal.ofReal_mul h_pos1]
      have h_step2 : ENNReal.ofReal (r ^ t * (Sfin.card : ℝ)) =
          ENNReal.ofReal (r ^ t) * ENNReal.ofReal (Sfin.card : ℝ) := by
        rw [ENNReal.ofReal_mul h_pos2]
      have h_step3 : ENNReal.ofReal (Sfin.card : ℝ) = (↑Sfin.card : ENNReal) := by simp
      rw [h_step1, h_step2, h_step3] <;> ring
    have h9 : (↑T.card : ENNReal) ≤ ENNReal.ofReal ((9 * C) * r ^ t * (Sfin.card : ℝ)) := by
      rw [h8]; exact h6
    have h10 : ENNReal.ofReal (↑T.card : ℝ) ≤ ENNReal.ofReal ((9 * C) * r ^ t * (Sfin.card : ℝ)) := by
      have h11 : (↑T.card : ENNReal) = ENNReal.ofReal (↑T.card : ℝ) := by simp
      rw [h11] at h9; exact h9
    have h_iff : ENNReal.ofReal (↑T.card : ℝ) ≤ ENNReal.ofReal ((9 * C) * r ^ t * (Sfin.card : ℝ)) ↔
        (↑T.card : ℝ) ≤ (9 * C) * r ^ t * (Sfin.card : ℝ) :=
      ENNReal.ofReal_le_ofReal_iff h_bound_real
    exact h_iff.mp h10
  have hSfin_nonempty : Sfin.Nonempty := by
    have h : (Sfin : Set EuclideanPlane).Nonempty := by
      rw [hSfin_eq]; exact hS_nonempty
    exact (Finite.toFinset_nonempty hS_finite).mpr hS_nonempty
  have h_sep' : ∀ p ∈ Sfin, ∀ q ∈ Sfin, p ≠ q → δ ≤ ‖p - q‖ := by
    intro p hp q hq hne
    have hp' : p ∈ S := by rw [← hSfin_eq]; exact hp
    have hq' : q ∈ S := by rw [← hSfin_eq]; exact hq
    exact h_sep p hp' q hq' hne
  have h_ball_growth' : ∀ p ∈ Sfin, ∀ r : ℝ, δ ≤ r →
      (Sfin.filter (fun q => ‖p - q‖ ≤ r)).card ≤ (9 * C) * r ^ t * Sfin.card := by
    intro p hp r hr
    have hp' : p ∈ S := by rw [← hSfin_eq]; exact hp
    exact h_ball_growth p hp' r hr
  exact ⟨Sfin, by simpa [hSfin_eq] using hS_subset, hSfin_nonempty, h_sep', hNcover_le, h_ball_growth'⟩

/-! ### Ncover and separated subset comparison -/

/-- A maximal δ-separated subset has covering number at most its cardinality,
and its cardinality is at most the covering number at half scale.
This lemma states the simpler direction: `Ncover δ P ≤ S.card` for a
maximal δ-separated set `S` that covers `P`. -/
lemma Ncover_separated_subset {δ : ℝ} {P : Set EuclideanPlane}
    (S : Finset EuclideanPlane) (hS_subset : (S : Set EuclideanPlane) ⊆ P)
    (hS_cover : IsCover δ.toNNReal P (S : Set EuclideanPlane)) :
    Ncover δ P ≤ (S.card : ENNReal) := by
  have h1 : externalCoveringNumber δ.toNNReal P ≤ (S : Set EuclideanPlane).encard :=
    IsCover.externalCoveringNumber_le_encard hS_cover
  have h2 : (S : Set EuclideanPlane).encard = ↑S.card := by simp
  rw [h2] at h1
  have h3 : (↑(externalCoveringNumber δ.toNNReal P) : ENNReal) ≤ (↑S.card : ENNReal) := by
    exact_mod_cast h1
  simpa [Ncover] using h3

/-! ### Lipschitz property of affine projection -/

/-- For `σ ∈ [-1, 1]`, the projection `p ↦ p 0 - σ * p 1` is 2-Lipschitz. -/
lemma affineProjection_lipschitz {σ : ℝ} (hσ : σ ∈ Set.Icc (-1 : ℝ) 1) :
    LipschitzWith 2 (fun p : EuclideanPlane => p 0 - σ * p 1) := by
  have h1 : |σ| ≤ 1 := by
    rcases hσ with ⟨hσ1, hσ2⟩
    rw [abs_le] <;> constructor <;> linarith
  refine' LipschitzWith.of_dist_le_mul fun x y => _
  have h2 : dist (x 0 - σ * x 1) (y 0 - σ * y 1) = |(x 0 - y 0) - σ * (x 1 - y 1)| := by
    simp [dist_eq_norm, sub_sub_sub_cancel_left]
    <;> ring_nf
  rw [h2]
  have h3 : |(x 0 - y 0) - σ * (x 1 - y 1)| ≤ |x 0 - y 0| + |σ| * |x 1 - y 1| := by
    calc
      |(x 0 - y 0) - σ * (x 1 - y 1)|
        ≤ |x 0 - y 0| + |σ * (x 1 - y 1)| := by exact abs_sub _ _
      _ = |x 0 - y 0| + |σ| * |x 1 - y 1| := by rw [abs_mul]
  have h4 : |x 0 - y 0| ≤ ‖x - y‖ := PiLp.norm_apply_le (x - y) 0
  have h5 : |x 1 - y 1| ≤ ‖x - y‖ := PiLp.norm_apply_le (x - y) 1
  calc
    |(x 0 - y 0) - σ * (x 1 - y 1)|
      ≤ |x 0 - y 0| + |σ| * |x 1 - y 1| := h3
    _ ≤ ‖x - y‖ + 1 * ‖x - y‖ := by gcongr <;> linarith
    _ = 2 * ‖x - y‖ := by ring

/-! ### Covering number monotonicity -/

/-- Covering number is monotone with respect to set inclusion. -/
lemma Ncover_mono {X : Type*} [PseudoMetricSpace X] {δ : ℝ} {A B : Set X}
    (h : A ⊆ B) : Ncover δ A ≤ Ncover δ B := by
  simpa [Ncover] using Metric.externalCoveringNumber_mono_set h

/-- Covering number decreases as radius increases. -/
lemma Ncover_anti {X : Type*} [PseudoMetricSpace X] {δ₁ δ₂ : ℝ} {A : Set X}
    (h : δ₁ ≤ δ₂) (hδ₁ : 0 ≤ δ₁) :
    Ncover δ₂ A ≤ Ncover δ₁ A := by
  have h1 : δ₁.toNNReal ≤ δ₂.toNNReal := by exact Real.toNNReal_mono h
  simpa [Ncover] using Metric.externalCoveringNumber_anti h1

end RobustKaufmanProjection
