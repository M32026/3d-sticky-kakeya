module

/-
  Coarse tube parameter S-set transfer.

  Transfers IsDeltaSSet from CoarseTube (AffineLine metric) to
  parameter space ℝ×ℝ (max norm) via T ↦ (tubeSlope T, tubeIntercept T).

  Whiteprint node: appendix_a_alternative / coarse_params_sset
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineLipschitzTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal Classical

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CoveringUtils

/-! ### Helper: edist/dist conversion with NNReal radius -/

lemma edist_toNNReal_iff_dist {X : Type*} [PseudoMetricSpace X] {x y : X} {r : ℝ} (hr : 0 ≤ r) :
    edist x y ≤ ↑r.toNNReal ↔ dist x y ≤ r := by
  have h1 : edist x y = ENNReal.ofReal (dist x y) := by exact edist_dist x y
  have h2 : (↑r.toNNReal : ENNReal) = ENNReal.ofReal r := by
    have h3 : (r.toNNReal : ℝ) = r := by
      have h4 : (r.toNNReal : ℝ) = max r 0 := by rfl
      rw [h4]
      rw [max_eq_left] <;> linarith
    have h4 : (↑r.toNNReal : ENNReal) = ENNReal.ofReal (↑r.toNNReal : ℝ) := by exact Eq.symm ENNReal.ofReal_coe_nnreal
    rw [h4, h3]
  rw [h1, h2]
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)]

/-! ### Optimal cover existence -/

/-- Existence of an optimal cover attaining the external covering number. -/
lemma exists_optimal_cover {X : Type*} [PseudoMetricSpace X] {ε : ℝ≥0} {S : Set X} :
    ∃ (C : Set X), Metric.IsCover ε S C ∧
      C.encard = Metric.externalCoveringNumber ε S := by
  let b := Metric.externalCoveringNumber ε S
  by_cases hb : b = ⊤
  · -- b = ⊤: use S itself as cover (it has encard = ⊤)
    have hS_cover : Metric.IsCover ε S S := by
      intro x hx
      refine' ⟨x, hx, _⟩
      simp
    have hS_encard : S.encard = ⊤ := by
      have h : b ≤ S.encard := Metric.externalCoveringNumber_le_encard_self S
      rw [hb] at h
      simpa using h
    have h_goal : S.encard = b := by
      rw [hS_encard, hb]
    exact ⟨S, hS_cover, h_goal⟩
  · -- b < ⊤, so b = ↑n for some n : ℕ
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b = ↑n := by exact Option.ne_none_iff_exists'.mp hb
    have h_lb : ∀ (C : Set X), Metric.IsCover ε S C → b ≤ C.encard :=
      fun C hC => Metric.IsCover.externalCoveringNumber_le_encard hC
    have h_not_lb : ¬ ∀ (C : Set X), Metric.IsCover ε S C → (↑(n + 1) : ℕ∞) ≤ C.encard := by
      intro h
      have h9 : ∀ (C : Set X), (↑(n + 1) : ℕ∞) ≤
          (⨅ (h : Metric.IsCover ε S C), C.encard) := by
        intro C
        by_cases hC : Metric.IsCover ε S C
        · simpa [hC] using h C hC
        · simp [hC]
      have h' : (↑(n + 1) : ℕ∞) ≤ b := by
        simpa [b, Metric.externalCoveringNumber] using le_iInf h9
      rw [hn] at h'
      have h_contra : (n + 1 : ℕ∞) ≤ (n : ℕ∞) := h'
      have h_false : False := by
        have h_lt : (n : ℕ∞) < (n + 1 : ℕ∞) := by exact_mod_cast Nat.lt_succ_self n
        exact not_le.mpr h_lt h_contra
      exact h_false
    push Not at h_not_lb
    rcases h_not_lb with ⟨C, hC, h_not_le⟩
    have h_lt : C.encard < (↑(n + 1) : ℕ∞) := by exact lt_of_lt_of_eq h_not_le rfl
    have h_le : C.encard ≤ (↑n : ℕ∞) := by exact ENat.lt_coe_add_one_iff.mp h_not_le
    have h_ge : (↑n : ℕ∞) ≤ C.encard := by
      have h : b ≤ C.encard := h_lb C hC
      rw [hn] at h
      exact h
    have h_eq : C.encard = (↑n : ℕ∞) := le_antisymm h_le h_ge
    have h_goal : C.encard = b := by
      rw [h_eq, hn]
    exact ⟨C, hC, h_goal⟩

/-! ### Grid cover of a ball in ℝ² -/

/-- A finite grid covering any ball of radius R in ℝ² at scale δ, with ≤ 49*(R/δ)^2 points. -/
lemma grid_cover_plane {c : ℝ × ℝ} {R δ : ℝ} (hδ_pos : 0 < δ) (hR_pos : 0 < R) (hδ_le_R : δ ≤ R) :
    ∃ (G : Finset (ℝ × ℝ)),
      Metric.IsCover δ.toNNReal (Metric.closedBall c R) (G : Set (ℝ × ℝ)) ∧
      (G.card : ℝ) ≤ 49 * (R / δ) ^ 2 := by
  let M : ℕ := Nat.ceil (R / δ + 1)
  have hM1 : (R / δ + 1 : ℝ) ≤ (M : ℝ) := Nat.le_ceil (R / δ + 1)
  have hM2 : (M : ℝ) ≤ R / δ + 2 := by
    have h_pos : (0 : ℝ) ≤ R / δ + 1 := by positivity
    have h : (M : ℝ) < (R / δ + 1) + 1 := Nat.ceil_lt_add_one h_pos
    linarith
  let idx : Finset ℤ := (Finset.range (2 * M + 1)).image (fun k : ℕ => (k : ℤ) - (M : ℤ))
  have hidx_inj : Function.Injective (fun k : ℕ => (k : ℤ) - (M : ℤ)) := by
    intro k1 k2 h
    simpa using h
  have hidx_card : idx.card = 2 * M + 1 := by
    rw [Finset.card_image_of_injective _ hidx_inj, Finset.card_range] <;> ring
  have h4 : 1 ≤ R / δ := by
    exact (one_le_div₀ hδ_pos).mpr hδ_le_R
  have hidx_bound : (idx.card : ℝ) ≤ 7 * (R / δ) := by
    rw [hidx_card]
    have h7 : (↑(2 * M + 1) : ℝ) ≤ 7 * (R / δ) := by
      have h71 : (2 * (M : ℝ) + 1) ≤ 7 * (R / δ) := by linarith
      exact_mod_cast h71
    exact_mod_cast h7
  let g : ℤ × ℤ → ℝ × ℝ := fun (i, j) => (c.1 + (i : ℝ) * δ, c.2 + (j : ℝ) * δ)
  let G : Finset (ℝ × ℝ) := (idx ×ˢ idx).image g
  have hG_card : (G.card : ℝ) ≤ 49 * (R / δ) ^ 2 := by
    have h1 : G.card ≤ (idx ×ˢ idx).card := Finset.card_image_le
    have h2 : (idx ×ˢ idx).card = idx.card * idx.card := by
      rw [Finset.card_product] <;> ring
    have h3 : (G.card : ℝ) ≤ ((idx.card : ℝ) * (idx.card : ℝ)) := by
      exact_mod_cast (h1.trans (by rw [h2]))
    nlinarith [hidx_bound]
  have h_cover : Metric.IsCover δ.toNNReal (Metric.closedBall c R) (G : Set (ℝ × ℝ)) := by
    intro x hx
    have hR : dist x c ≤ R := hx
    have h11 : |x.1 - c.1| ≤ R := by
      have h_dist_eq : dist x c = max (|x.1 - c.1|) (|x.2 - c.2|) := by
        simp [Prod.dist_eq, Real.dist_eq] <;> rfl
      rw [h_dist_eq] at hR
      exact le_trans (le_max_left _ _) hR
    have h12 : |x.2 - c.2| ≤ R := by
      have h_dist_eq : dist x c = max (|x.1 - c.1|) (|x.2 - c.2|) := by
        simp [Prod.dist_eq, Real.dist_eq] <;> rfl
      rw [h_dist_eq] at hR
      exact le_trans (le_max_right _ _) hR
    let i : ℤ := Int.floor ((x.1 - c.1) / δ)
    let j : ℤ := Int.floor ((x.2 - c.2) / δ)
    have hi1 : (i : ℝ) ≤ (x.1 - c.1) / δ := Int.floor_le _
    have hi2 : (x.1 - c.1) / δ < (i : ℝ) + 1 := Int.lt_floor_add_one _
    have hj1 : (j : ℝ) ≤ (x.2 - c.2) / δ := Int.floor_le _
    have hj2 : (x.2 - c.2) / δ < (j : ℝ) + 1 := Int.lt_floor_add_one _
    have h_i_upper : (i : ℝ) ≤ R / δ + 1 := by
      have h : (x.1 - c.1) / δ ≤ R / δ := by
        apply div_le_div_of_nonneg_right
        · exact (abs_le.mp h11).2
        · positivity
      linarith
    have h_i_lower : -(R / δ + 1) ≤ (i : ℝ) := by
      have h1 : -R ≤ x.1 - c.1 := (abs_le.mp h11).1
      have h2 : (-R : ℝ) / δ ≤ (x.1 - c.1) / δ := by
        exact div_le_div_of_nonneg_right h1 (by positivity)
      have h3 : (-R : ℝ) / δ = -(R / δ) := by ring
      have h4 : -(R / δ) ≤ (x.1 - c.1) / δ := by rw [←h3]; exact h2
      have h' : (i : ℝ) > (x.1 - c.1) / δ - 1 := by linarith
      linarith
    have h_j_upper : (j : ℝ) ≤ R / δ + 1 := by
      have h : (x.2 - c.2) / δ ≤ R / δ := by
        apply div_le_div_of_nonneg_right
        · exact (abs_le.mp h12).2
        · positivity
      linarith
    have h_j_lower : -(R / δ + 1) ≤ (j : ℝ) := by
      have h1 : -R ≤ x.2 - c.2 := (abs_le.mp h12).1
      have h2 : (-R : ℝ) / δ ≤ (x.2 - c.2) / δ := by
        exact div_le_div_of_nonneg_right h1 (by positivity)
      have h3 : (-R : ℝ) / δ = -(R / δ) := by ring
      have h4 : -(R / δ) ≤ (x.2 - c.2) / δ := by rw [←h3]; exact h2
      have h' : (j : ℝ) > (x.2 - c.2) / δ - 1 := by linarith
      linarith
    have h_i_in : i ∈ idx := by
      have h_i_abs : |(i : ℝ)| ≤ (M : ℝ) := by
        have h_lower : -(M : ℝ) ≤ (i : ℝ) := by linarith [hM1]
        have h_upper : (i : ℝ) ≤ (M : ℝ) := by linarith [hM1]
        exact abs_le.mpr ⟨h_lower, h_upper⟩
      have h6 : 0 ≤ i + (M : ℤ) := by
        have h61 : -(M : ℝ) ≤ (i : ℝ) := (abs_le.mp h_i_abs).1
        have h62 : 0 ≤ (i : ℝ) + (M : ℝ) := by linarith
        exact_mod_cast h62
      have h_i_le_M : i ≤ (M : ℤ) := by exact_mod_cast (show (i : ℝ) ≤ (M : ℝ) from (abs_le.mp h_i_abs).2)
      have h81 : (i + (M : ℤ)).toNat < 2 * M + 1 := by
        have h9 : 0 ≤ i + (M : ℤ) := h6
        have h10 : i + (M : ℤ) < ↑(2 * M + 1) := by
          have h11 : i ≤ (M : ℤ) := h_i_le_M
          simp [add_assoc] <;> omega
        have h12 : ((i + (M : ℤ)).toNat : ℤ) = i + (M : ℤ) := Int.toNat_of_nonneg h9
        have h13 : ((i + (M : ℤ)).toNat : ℤ) < ↑(2 * M + 1) := by
          rw [h12] <;> exact h10
        exact_mod_cast h13
      have h82 : ((i + (M : ℤ)).toNat : ℤ) - (M : ℤ) = i := by
        have h9 : ((i + (M : ℤ)).toNat : ℤ) = i + (M : ℤ) := by
          rw [Int.toNat_of_nonneg h6]
        rw [h9] <;> ring
      simp only [idx, Finset.mem_image]
      exact ⟨(i + (M : ℤ)).toNat, Finset.mem_range.mpr h81, h82⟩
    have h_j_in : j ∈ idx := by
      have h_j_abs : |(j : ℝ)| ≤ (M : ℝ) := by
        have h_lower : -(M : ℝ) ≤ (j : ℝ) := by linarith [hM1]
        have h_upper : (j : ℝ) ≤ (M : ℝ) := by linarith [hM1]
        exact abs_le.mpr ⟨h_lower, h_upper⟩
      have h6 : 0 ≤ j + (M : ℤ) := by
        have h61 : -(M : ℝ) ≤ (j : ℝ) := (abs_le.mp h_j_abs).1
        have h62 : 0 ≤ (j : ℝ) + (M : ℝ) := by linarith
        exact_mod_cast h62
      have h_j_le_M : j ≤ (M : ℤ) := by exact_mod_cast (show (j : ℝ) ≤ (M : ℝ) from (abs_le.mp h_j_abs).2)
      have h81 : (j + (M : ℤ)).toNat < 2 * M + 1 := by
        have h9 : 0 ≤ j + (M : ℤ) := h6
        have h10 : j + (M : ℤ) < ↑(2 * M + 1) := by
          have h11 : j ≤ (M : ℤ) := h_j_le_M
          simp [add_assoc] <;> omega
        have h12 : ((j + (M : ℤ)).toNat : ℤ) = j + (M : ℤ) := Int.toNat_of_nonneg h9
        have h13 : ((j + (M : ℤ)).toNat : ℤ) < ↑(2 * M + 1) := by
          rw [h12] <;> exact h10
        exact_mod_cast h13
      have h82 : ((j + (M : ℤ)).toNat : ℤ) - (M : ℤ) = j := by
        have h9 : ((j + (M : ℤ)).toNat : ℤ) = j + (M : ℤ) := by
          rw [Int.toNat_of_nonneg h6]
        rw [h9] <;> ring
      simp only [idx, Finset.mem_image]
      exact ⟨(j + (M : ℤ)).toNat, Finset.mem_range.mpr h81, h82⟩
    let p : ℝ × ℝ := g (i, j)
    have hp_in_G : p ∈ G := by
      apply Finset.mem_image.mpr
      exact ⟨(i, j), Finset.mem_product.mpr ⟨h_i_in, h_j_in⟩, rfl⟩
    have h_dist1 : |x.1 - p.1| < δ := by
      have h_eq : x.1 - p.1 = x.1 - c.1 - (i : ℝ) * δ := by
        simp [p, g] <;> ring
      rw [h_eq]
      have h_a : (i : ℝ) * δ ≤ x.1 - c.1 := by
        calc (i : ℝ) * δ ≤ ((x.1 - c.1) / δ) * δ := by gcongr
          _ = x.1 - c.1 := by field_simp [hδ_pos.ne'] <;> ring
      have h_b : x.1 - c.1 < (i : ℝ) * δ + δ := by
        calc x.1 - c.1 = ((x.1 - c.1) / δ) * δ := by field_simp [hδ_pos.ne'] <;> ring
          _ < ((i : ℝ) + 1) * δ := by gcongr
          _ = (i : ℝ) * δ + δ := by ring
      have h_pos : 0 ≤ x.1 - c.1 - (i : ℝ) * δ := by linarith
      rw [abs_of_nonneg h_pos]
      linarith
    have h_dist2 : |x.2 - p.2| < δ := by
      have h_eq : x.2 - p.2 = x.2 - c.2 - (j : ℝ) * δ := by
        simp [p, g] <;> ring
      rw [h_eq]
      have h_a : (j : ℝ) * δ ≤ x.2 - c.2 := by
        calc (j : ℝ) * δ ≤ ((x.2 - c.2) / δ) * δ := by gcongr
          _ = x.2 - c.2 := by field_simp [hδ_pos.ne'] <;> ring
      have h_b : x.2 - c.2 < (j : ℝ) * δ + δ := by
        calc x.2 - c.2 = ((x.2 - c.2) / δ) * δ := by field_simp [hδ_pos.ne'] <;> ring
          _ < ((j : ℝ) + 1) * δ := by gcongr
          _ = (j : ℝ) * δ + δ := by ring
      have h_pos : 0 ≤ x.2 - c.2 - (j : ℝ) * δ := by linarith
      rw [abs_of_nonneg h_pos]
      linarith
    have h_dist : dist x p ≤ δ := by
      have h : dist x p = max (|x.1 - p.1|) (|x.2 - p.2|) := by
        simp [Prod.dist_eq, Real.dist_eq] <;> rfl
      rw [h]
      exact max_le (by linarith) (by linarith)
    have h_edist : edist x p ≤ ↑δ.toNNReal := by
      rw [edist_toNNReal_iff_dist hδ_pos.le]
      exact h_dist
    exact ⟨p, hp_in_G, h_edist⟩
  exact ⟨G, h_cover, hG_card⟩

/-! ### Covering refinement in ℝ² -/

/-- Refinement bound in ℝ²: Ncover_δ(S) ≤ 49*(R/δ)^2 * Ncover_R(S). -/
lemma covering_refinement_plane {δ R : ℝ} (hδ_pos : 0 < δ) (hR_pos : 0 < R) (hδ_le_R : δ ≤ R)
    {S : Set (ℝ × ℝ)} :
    (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤
      ENNReal.ofReal (49 * (R / δ) ^ 2) * (Metric.externalCoveringNumber R.toNNReal S : ENNReal) := by
  let K : ℝ := 49 * (R / δ) ^ 2
  have hK_pos : 0 < K := by positivity
  rcases exists_optimal_cover (S := S) (ε := R.toNNReal) with ⟨C, hC, hC_eq⟩
  rcases grid_cover_plane (c := (0,0)) (R := R) (δ := δ) hδ_pos hR_pos hδ_le_R with ⟨G0, hG0_cover, hG0_card⟩
  have h_main : ∃ (D : Set (ℝ × ℝ)), Metric.IsCover δ.toNNReal S D ∧
      (D.encard : ENNReal) ≤ ENNReal.ofReal K * (C.encard : ENNReal) := by
    by_cases hCfin : C.Finite
    · let Cfin := hCfin.toFinset
      let grid_c (c : ℝ × ℝ) : Finset (ℝ × ℝ) :=
        G0.image (fun g => (g.1 + c.1, g.2 + c.2))
      have h_grid_c_cover : ∀ c ∈ Cfin,
          Metric.IsCover δ.toNNReal (Metric.closedBall c R) ((grid_c c : Set (ℝ × ℝ))) := by
        intro c _
        intro x hx
        let y := (x.1 - c.1, x.2 - c.2)
        have hy_dist : dist y (0,0) = dist x c := by
          simp [y, Prod.dist_eq, Real.dist_eq] <;> rfl
        have hy : y ∈ Metric.closedBall (0,0) R := by
          rw [Metric.mem_closedBall, hy_dist]
          exact hx
        rcases hG0_cover hy with ⟨g, hg_in, hg_edist⟩
        let p := (g.1 + c.1, g.2 + c.2)
        have hp_in : p ∈ grid_c c := by
          apply Finset.mem_image.mpr
          exact ⟨g, hg_in, by simp [p, grid_c] <;> ring⟩
        have h_eq_dist : dist x p = dist y g := by
          simp [p, y, Prod.dist_eq, Real.dist_eq] <;> ring
        have h_edist : edist x p ≤ ↑δ.toNNReal := by
          rw [edist_toNNReal_iff_dist hδ_pos.le, h_eq_dist]
          exact (edist_toNNReal_iff_dist hδ_pos.le).mp hg_edist
        exact ⟨p, hp_in, h_edist⟩
      let D : Finset (ℝ × ℝ) := Cfin.biUnion grid_c
      have hD_cover : Metric.IsCover δ.toNNReal S (D : Set (ℝ × ℝ)) := by
        intro x hx
        rcases hC hx with ⟨c, hcC, hc_edist⟩
        have hc_in : c ∈ Cfin := by simpa [Cfin] using hcC
        have h1 : x ∈ Metric.closedBall c R := by
          rw [Metric.mem_closedBall]
          have h_dist : dist x c ≤ R := (edist_toNNReal_iff_dist hR_pos.le).mp hc_edist
          exact h_dist
        rcases h_grid_c_cover c hc_in h1 with ⟨p, hp_in, hp_edist⟩
        have hp_in_D : p ∈ (D : Set (ℝ × ℝ)) := by
          exact Finset.mem_biUnion.mpr ⟨c, hc_in, hp_in⟩
        exact ⟨p, hp_in_D, hp_edist⟩
      have hD_card_nat : D.card ≤ Cfin.card * G0.card := by
        calc D.card
          ≤ ∑ c ∈ Cfin, (grid_c c).card := Finset.card_biUnion_le
        _ ≤ ∑ c ∈ Cfin, G0.card := by
          apply Finset.sum_le_sum
          intro c _
          exact Finset.card_image_le
        _ = Cfin.card * G0.card := by simp [Finset.sum_const] <;> ring
      have hD_card_real : (D.card : ℝ) ≤ (Cfin.card : ℝ) * K := by
        calc (D.card : ℝ)
          ≤ (Cfin.card : ℝ) * (G0.card : ℝ) := by exact_mod_cast hD_card_nat
        _ ≤ (Cfin.card : ℝ) * K := by gcongr <;> exact hG0_card
      have h_encard : (D : Set (ℝ × ℝ)).encard = ↑D.card := by simp
      have h_C_encard : C.encard = ↑Cfin.card := by
        exact_mod_cast Set.Finite.encard_eq_coe_toFinset_card hCfin
      have h_final : (↑D.card : ENNReal) ≤ ENNReal.ofReal K * (C.encard : ENNReal) := by
        have h : (D.card : ℝ) ≤ (Cfin.card : ℝ) * K := hD_card_real
        have h_eq1 : (↑D.card : ENNReal) = ENNReal.ofReal (D.card : ℝ) := by simp
        have h_eq2 : (C.encard : ENNReal) = (↑Cfin.card : ENNReal) := by
          exact_mod_cast Set.Finite.encard_eq_coe_toFinset_card hCfin
        rw [h_eq1, h_eq2]
        have h' : ENNReal.ofReal (D.card : ℝ) ≤ ENNReal.ofReal ((Cfin.card : ℝ) * K) :=
          ENNReal.ofReal_le_ofReal h
        have h'' : ENNReal.ofReal ((Cfin.card : ℝ) * K) = (↑Cfin.card : ENNReal) * ENNReal.ofReal K := by
          rw [ENNReal.ofReal_mul (by positivity)] <;> simp <;> ring
        rw [h''] at h'
        simpa [mul_comm] using h'
      have h_final' : (D : Set (ℝ × ℝ)).encard ≤ ENNReal.ofReal K * C.encard := by
        rw [h_encard]
        exact h_final
      exact ⟨(D : Set (ℝ × ℝ)), hD_cover, h_final'⟩
    · -- C infinite
      have hC_inf : C.encard = ⊤ := by simpa [Set.encard_eq_top] using hCfin
      have h_pos : 0 < ENNReal.ofReal K := ENNReal.ofReal_pos.mpr hK_pos
      have h_cover : Metric.IsCover δ.toNNReal S (Set.univ : Set (ℝ × ℝ)) := by
        intro x _
        exact ⟨x, Set.mem_univ x, by simp⟩
      have h_card : ((Set.univ : Set (ℝ × ℝ)).encard : ENNReal) ≤ ENNReal.ofReal K * (C.encard : ENNReal) := by
        rw [hC_inf]
        simp [h_pos.ne']
        <;> exact le_top
      exact ⟨(Set.univ : Set (ℝ × ℝ)), h_cover, h_card⟩
  rcases h_main with ⟨D, hD_cover, hD_card⟩
  have h1 : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤ (D.encard : ENNReal) := by
    exact_mod_cast Metric.IsCover.externalCoveringNumber_le_encard hD_cover
  have h2 : (D.encard : ENNReal) ≤ ENNReal.ofReal K * (C.encard : ENNReal) := hD_card
  have h3 : (C.encard : ENNReal) = (Metric.externalCoveringNumber R.toNNReal S : ENNReal) := by
    rw [hC_eq]
  rw [h3] at h2
  exact le_trans h1 h2

/-! ### Forward Lipschitz bound -/

/-- Generalized forward Lipschitz: dist(params) ≤ (2+2B) * dist(lines). -/
lemma affineLineParams_lipschitz_general
    {ℓ₁ ℓ₂ : AffineLine} {B : ℝ} (hB : 0 ≤ B)
    (hv1 : (LemmaE.getDirV ℓ₁) 1 ≠ 0)
    (hv2 : (LemmaE.getDirV ℓ₂) 1 ≠ 0)
    (ha1 : |tubeSlope ℓ₁| ≤ 1) (ha2 : |tubeSlope ℓ₂| ≤ 1)
    (hb1 : |tubeIntercept ℓ₁| ≤ B) (hb2 : |tubeIntercept ℓ₂| ≤ B) :
    dist (tubeSlope ℓ₁, tubeIntercept ℓ₁) (tubeSlope ℓ₂, tubeIntercept ℓ₂) ≤
      (2 + 2 * B) * dist ℓ₁ ℓ₂ := by
  set a1 := tubeSlope ℓ₁ with ha1_def
  set a2 := tubeSlope ℓ₂ with ha2_def
  set b1 := tubeIntercept ℓ₁ with hb1_def
  set b2 := tubeIntercept ℓ₂ with hb2_def
  set d := dist ℓ₁ ℓ₂ with hd_def
  set o := ‖ℓ₁.offset - ℓ₂.offset‖ with ho_def
  have h_o_le_d : o ≤ d := by
    have h : d = ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ + o := by
      simp [AffineLine.dist, ho_def] <;> rfl
    have h_nonneg : 0 ≤ ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ := by positivity
    linarith
  have h_a : |a1 - a2| ≤ 2 * d :=
    TubesAndSlopes.slope_lipschitz ℓ₁ ℓ₂ hv1 hv2 ha1 ha2
  have h_form1 := TubesAndSlopes.offset_formula ℓ₁ hv1
  have h_form2 := TubesAndSlopes.offset_formula ℓ₂ hv2
  have hb1_eq : b1 = ℓ₁.offset 0 - a1 * ℓ₁.offset 1 := by
    have h1 : ℓ₁.offset 0 = b1 / (1 + a1^2) := by
      simpa [a1, b1, tubeSlope, tubeIntercept] using h_form1.1
    have h2 : ℓ₁.offset 1 = -a1 * b1 / (1 + a1^2) := by
      simpa [a1, b1, tubeSlope, tubeIntercept] using h_form1.2
    rw [h1, h2]
    field_simp <;> ring
  have hb2_eq : b2 = ℓ₂.offset 0 - a2 * ℓ₂.offset 1 := by
    have h1 : ℓ₂.offset 0 = b2 / (1 + a2^2) := by
      simpa [a2, b2, tubeSlope, tubeIntercept] using h_form2.1
    have h2 : ℓ₂.offset 1 = -a2 * b2 / (1 + a2^2) := by
      simpa [a2, b2, tubeSlope, tubeIntercept] using h_form2.2
    rw [h1, h2]
    field_simp <;> ring
  have h_off2_1 : |ℓ₂.offset 1| ≤ B := by
    have h : |ℓ₂.offset 1| ≤ ‖ℓ₂.offset‖ := TubesAndSlopes.coord_abs_le_norm ℓ₂.offset 1
    have h2 : ‖ℓ₂.offset‖ ≤ |b2| := AffineLineLipschitzTransfer.offset_norm_le_abs_b ℓ₂ hv2
    exact le_trans h (le_trans h2 hb2)
  have h_off0_diff : |ℓ₁.offset 0 - ℓ₂.offset 0| ≤ o :=
    TubesAndSlopes.coord_abs_le_norm (ℓ₁.offset - ℓ₂.offset) 0
  have h_off1_diff : |ℓ₁.offset 1 - ℓ₂.offset 1| ≤ o :=
    TubesAndSlopes.coord_abs_le_norm (ℓ₁.offset - ℓ₂.offset) 1
  have h_b : |b1 - b2| ≤ (2 + 2 * B) * d := by
    rw [hb1_eq, hb2_eq]
    set x := ℓ₁.offset 0 - ℓ₂.offset 0 with hx_def
    set y := a1 * (ℓ₁.offset 1 - ℓ₂.offset 1) + (a1 - a2) * ℓ₂.offset 1 with hy_def
    have h_alg : (ℓ₁.offset 0 - a1 * ℓ₁.offset 1) - (ℓ₂.offset 0 - a2 * ℓ₂.offset 1) = x - y := by
      simp [hx_def, hy_def] <;> ring
    rw [h_alg]
    have h_tri : |x - y| ≤ |x| + |a1| * |ℓ₁.offset 1 - ℓ₂.offset 1| + |a1 - a2| * |ℓ₂.offset 1| := by
      have h_abs1 : |x - y| ≤ |x| + |y| := by exact DiscretisedFurstenbergEstimate.real_abs_sub x y
      have h_abs2 : |y| ≤ |a1| * |ℓ₁.offset 1 - ℓ₂.offset 1| + |a1 - a2| * |ℓ₂.offset 1| := by
        have h : |y| ≤ |a1 * (ℓ₁.offset 1 - ℓ₂.offset 1)| + |(a1 - a2) * ℓ₂.offset 1| := by
          have h_y_def : y = a1 * (ℓ₁.offset 1 - ℓ₂.offset 1) + (a1 - a2) * ℓ₂.offset 1 := by rfl
          rw [h_y_def]
          have h_tri : ∀ (a b : ℝ), |a + b| ≤ |a| + |b| := by
            intro a b
            exact DiscretisedFurstenbergEstimate.real_abs_add a b
          exact h_tri _ _
        have h2 : |a1 * (ℓ₁.offset 1 - ℓ₂.offset 1)| = |a1| * |ℓ₁.offset 1 - ℓ₂.offset 1| := by rw [abs_mul]
        have h3 : |(a1 - a2) * ℓ₂.offset 1| = |a1 - a2| * |ℓ₂.offset 1| := by rw [abs_mul]
        linarith
      linarith [h_abs1, h_abs2]
    calc |x - y|
      ≤ |x| + |a1| * |ℓ₁.offset 1 - ℓ₂.offset 1| + |a1 - a2| * |ℓ₂.offset 1| := h_tri
    _ ≤ o + 1 * o + (2 * d) * B := by gcongr <;> linarith [ha1, h_off0_diff, h_off1_diff, h_a, h_off2_1]
    _ = 2 * o + 2 * B * d := by ring
    _ ≤ 2 * d + 2 * B * d := by gcongr
    _ = (2 + 2 * B) * d := by ring
  have h_goal_a : |a1 - a2| ≤ (2 + 2 * B) * d := by
    have h : |a1 - a2| ≤ 2 * d := h_a
    have h2 : 2 * d ≤ (2 + 2 * B) * d := by
      have h3 : 0 ≤ d := by positivity
      have h4 : 0 ≤ 2 * B := by linarith
      nlinarith
    linarith
  have h_main : dist (a1, b1) (a2, b2) ≤ (2 + 2 * B) * d := by
    simp only [Prod.dist_eq, max_le_iff]
    exact ⟨h_goal_a, h_b⟩
  exact h_main

/-! ### Main transfer theorem -/

/-- Main transfer: IsDeltaSSet on CoarseTube transfers to parameter space. -/
lemma coarseParams_sset_transfer
    {Δ s C B : ℝ} (hΔ_pos : 0 < Δ)
    (hs_nonneg : 0 ≤ s)
    (hB_nonneg : 0 ≤ B)
    {P : Set CoarseTube}
    (hP : IsDeltaSSet Δ s C P)
    (h_dir : ∀ T ∈ P, (LemmaE.getDirV T) 1 ≠ 0)
    (h_slope : ∀ T ∈ P, |tubeSlope T| ≤ 1)
    (h_intercept : ∀ T ∈ P, |tubeIntercept T| ≤ B) :
    IsDeltaSSet Δ s (200000 * (2 + 2 * B) ^ 4 * (3 + B) ^ 4 * (2 * (3 + B)) ^ s * C)
      ((fun T : CoarseTube => (tubeSlope T, tubeIntercept T)) '' P) := by
  let Kf : ℝ := 2 + 2 * B
  let Kb : ℝ := 3 + B
  let f : CoarseTube → ℝ × ℝ := fun T => (tubeSlope T, tubeIntercept T)
  let Q : Set (ℝ × ℝ) := f '' P
  let C' : ℝ := 200000 * Kf ^ 4 * Kb ^ 4 * (2 * Kb) ^ s * C
  let Kref : ℝ := 1000 * Kf ^ 2 * Kb ^ 4
  have hKf_pos : 0 < Kf := by positivity
  have hKb_pos : 0 < Kb := by positivity
  have hC_pos : 0 < C := hP.2.2.1
  have hC'_pos : 0 < C' := by positivity
  have hKref_pos : 0 < Kref := by positivity
  have hP_nonempty : P.Nonempty := hP.1
  have hQ_nonempty : Q.Nonempty := hP_nonempty.image f
  have h_fwd : ∀ (T1 T2 : CoarseTube), T1 ∈ P → T2 ∈ P →
      dist (f T1) (f T2) ≤ Kf * dist T1 T2 := by
    intro T1 T2 h1 h2
    exact affineLineParams_lipschitz_general hB_nonneg
      (h_dir T1 h1) (h_dir T2 h2) (h_slope T1 h1) (h_slope T2 h2)
      (h_intercept T1 h1) (h_intercept T2 h2)
  have h_bwd : ∀ (T1 T2 : CoarseTube), T1 ∈ P → T2 ∈ P →
      dist T1 T2 ≤ Kb * dist (f T1) (f T2) := by
    intro T1 T2 h1 h2
    set dp := dist (f T1) (f T2) with hdp_def
    have h1' : |(tubeSlope T1) - (tubeSlope T2)| ≤ dp := by
      have h_dist : dp = max (|(f T1).1 - (f T2).1|) (|(f T1).2 - (f T2).2|) := by
        simp [hdp_def, Prod.dist_eq, Real.dist_eq] <;> rfl
      rw [h_dist]
      exact le_max_left _ _
    have h2' : |(tubeIntercept T1) - (tubeIntercept T2)| ≤ dp := by
      have h_dist : dp = max (|(f T1).1 - (f T2).1|) (|(f T1).2 - (f T2).2|) := by
        simp [hdp_def, Prod.dist_eq, Real.dist_eq] <;> rfl
      rw [h_dist]
      exact le_max_right _ _
    have h_main : dist T1 T2 ≤ (2 + B) * |(tubeSlope T1) - (tubeSlope T2)| +
        |(tubeIntercept T1) - (tubeIntercept T2)| :=
      TubesAndSlopes.dist_bound_general T1 T2 (h_dir T1 h1) (h_dir T2 h2)
        hB_nonneg (h_intercept T2 h2)
    calc dist T1 T2
      ≤ (2 + B) * |(tubeSlope T1) - (tubeSlope T2)| + |(tubeIntercept T1) - (tubeIntercept T2)| := h_main
    _ ≤ (2 + B) * dp + dp := by gcongr <;> linarith
    _ = Kb * dp := by simp [Kb] <;> ring

  -- Pullback-refinement: Ncover_Δ(P) ≤ Kref * Ncover_Δ(Q)
  have h_pullback_refine :
      (Metric.externalCoveringNumber Δ.toNNReal P : ENNReal) ≤
        ENNReal.ofReal Kref * (Metric.externalCoveringNumber Δ.toNNReal Q : ENNReal) := by
    rcases exists_optimal_cover (S := Q) (ε := Δ.toNNReal) with ⟨D_Q, hD_Q, hD_Q_eq⟩
    have h_main : ∃ (D_P : Set CoarseTube), Metric.IsCover Δ.toNNReal P D_P ∧
        (D_P.encard : ENNReal) ≤ ENNReal.ofReal Kref * (D_Q.encard : ENNReal) := by
      by_cases hDQfin : D_Q.Finite
      · let DQfin := hDQfin.toFinset
        -- Step 1: pick one representative tube per D_Q point
        let S_d (d : ℝ × ℝ) : Set CoarseTube := {T ∈ P | f T ∈ Metric.closedBall d Δ}
        let default_tube : CoarseTube := hP_nonempty.some
        let p_d (d : ℝ × ℝ) : CoarseTube :=
          if h : (S_d d).Nonempty then Classical.choose h else default_tube
        let DQ_nonempty : Finset (ℝ × ℝ) := DQfin.filter (fun d => (S_d d).Nonempty)
        let p_set : Finset CoarseTube := DQ_nonempty.image p_d
        have h_pd_spec : ∀ (d : ℝ × ℝ), (S_d d).Nonempty → p_d d ∈ S_d d := by
          intro d h
          have h_eq : p_d d = Classical.choose h := by simp [p_d, h]
          rw [h_eq]
          exact Classical.choose_spec h
        have h_p_set_cover : Metric.IsCover ( (2 * Kb * Δ).toNNReal) P (p_set : Set CoarseTube) := by
          intro p hp
          have hfpQ : f p ∈ Q := ⟨p, hp, rfl⟩
          rcases hD_Q hfpQ with ⟨d, hd_in_DQ, h_edist⟩
          have hd_in_fin : d ∈ DQfin := by
            simpa [DQfin] using hd_in_DQ
          have h_dist : dist (f p) d ≤ Δ := (edist_toNNReal_iff_dist hΔ_pos.le).mp h_edist
          have h_Sd_nonempty : (S_d d).Nonempty := ⟨p, hp, h_dist⟩
          have hd_in_filter : d ∈ DQ_nonempty := by
            exact Finset.mem_filter.mpr ⟨hd_in_fin, h_Sd_nonempty⟩
          let pd := p_d d
          have hpd_in_P : pd ∈ P := (h_pd_spec d h_Sd_nonempty).1
          have hpd_near : f pd ∈ Metric.closedBall d Δ := (h_pd_spec d h_Sd_nonempty).2
          have h_dist2 : dist (f p) (f pd) ≤ 2 * Δ := by
            calc dist (f p) (f pd)
              ≤ dist (f p) d + dist d (f pd) := dist_triangle _ _ _
            _ ≤ Δ + Δ := by
              have h1 : dist (f p) d ≤ Δ := h_dist
              have h2 : dist d (f pd) ≤ Δ := by
                have h21 : dist (f pd) d ≤ Δ := by simpa [Metric.mem_closedBall] using hpd_near
                rw [dist_comm] at h21
                exact h21
              linarith
            _ = 2 * Δ := by ring
          have h_dist3 : dist p pd ≤ 2 * Kb * Δ := by
            have h4 : dist p pd ≤ Kb * dist (f p) (f pd) := h_bwd p pd hp hpd_in_P
            calc dist p pd ≤ Kb * dist (f p) (f pd) := h4
              _ ≤ Kb * (2 * Δ) := by gcongr
              _ = 2 * Kb * Δ := by ring
          have hpd_in_set : pd ∈ (p_set : Set CoarseTube) := by
            apply Finset.mem_image.mpr
            exact ⟨d, hd_in_filter, rfl⟩
          have h_edist2 : edist p pd ≤ ↑(2 * Kb * Δ).toNNReal := by
            rw [edist_toNNReal_iff_dist (by positivity)]
            exact h_dist3
          exact ⟨pd, hpd_in_set, h_edist2⟩
        -- Step 2: grid refinement around each pd
        let step : ℝ := Δ / (2 * Kb)
        have hstep_pos : 0 < step := by positivity
        let R_grid : ℝ := 2 * Kf * Kb * Δ
        have hR_grid_pos : 0 < R_grid := by positivity
        have hstep_le_R : step ≤ R_grid := by
          dsimp only [step, R_grid]
          have h1 : 0 < 2 * Kb := by positivity
          have h2 : Δ / (2 * Kb) ≤ Δ := div_le_self hΔ_pos.le (by linarith)
          have h3 : 1 ≤ 2 * Kf * Kb := by
            have hKf_eq : Kf = 2 + 2 * B := by rfl
            have hKb_eq : Kb = 3 + B := by rfl
            have h4 : Kf ≥ 2 := by rw [hKf_eq]; linarith [hB_nonneg]
            have h5 : Kb ≥ 3 := by rw [hKb_eq]; linarith [hB_nonneg]
            nlinarith
          have h4 : Δ ≤ 2 * Kf * Kb * Δ := by
            calc Δ = 1 * Δ := by ring
              _ ≤ (2 * Kf * Kb) * Δ := by gcongr <;> linarith
          linarith
        rcases grid_cover_plane (c := (0,0)) (R := R_grid) (δ := step) hstep_pos hR_grid_pos hstep_le_R
          with ⟨G0, hG0_cover, hG0_card⟩
        have h_ratio : R_grid / step = 4 * Kf * Kb ^ 2 := by
          dsimp only [R_grid, step]
          field_simp [hKb_pos.ne', hΔ_pos.ne'] <;> ring
        have hG0_bound : (G0.card : ℝ) ≤ Kref := by
          have h1 : (G0.card : ℝ) ≤ 49 * (R_grid / step) ^ 2 := hG0_card
          rw [h_ratio] at h1
          have h2 : 49 * (4 * Kf * Kb ^ 2) ^ 2 = 784 * Kf ^ 2 * Kb ^ 4 := by ring
          rw [h2] at h1
          have h4 : (G0.card : ℝ) ≤ 784 * Kf ^ 2 * Kb ^ 4 := h1
          have h5 : 0 < Kf ^ 2 * Kb ^ 4 := by positivity
          have h6 : 784 * Kf ^ 2 * Kb ^ 4 ≤ 1000 * Kf ^ 2 * Kb ^ 4 := by
            have h7 : (784 : ℝ) ≤ 1000 := by norm_num
            nlinarith
          have h8 : (G0.card : ℝ) ≤ 1000 * Kf ^ 2 * Kb ^ 4 := le_trans h4 h6
          have h9 : Kref = 1000 * Kf ^ 2 * Kb ^ 4 := by rfl
          rw [h9]
          exact h8
        let grid_at (pd : CoarseTube) : Finset (ℝ × ℝ) :=
          G0.image (fun g => (g.1 + (f pd).1, g.2 + (f pd).2))
        have h_grid_cover : ∀ pd ∈ p_set,
            Metric.IsCover step.toNNReal (Metric.closedBall (f pd) R_grid)
              ((grid_at pd : Set (ℝ × ℝ))) := by
          intro pd _
          intro x hx
          let y := (x.1 - (f pd).1, x.2 - (f pd).2)
          have hy_dist : dist y (0,0) = dist x (f pd) := by
            simp [y, Prod.dist_eq, Real.dist_eq] <;> rfl
          have hy : y ∈ Metric.closedBall (0,0) R_grid := by
            rw [Metric.mem_closedBall, hy_dist]
            exact hx
          rcases hG0_cover hy with ⟨g, hg_in, hg_edist⟩
          let q := (g.1 + (f pd).1, g.2 + (f pd).2)
          have hq_in : q ∈ grid_at pd := by
            apply Finset.mem_image.mpr
            exact ⟨g, hg_in, by simp [q, grid_at] <;> ring⟩
          have h_eq_dist : dist x q = dist y g := by
            simp [q, y, Prod.dist_eq, Real.dist_eq] <;> ring
          have h_edist : edist x q ≤ ↑step.toNNReal := by
            rw [edist_toNNReal_iff_dist hstep_pos.le, h_eq_dist]
            exact (edist_toNNReal_iff_dist hstep_pos.le).mp hg_edist
          exact ⟨q, hq_in, h_edist⟩
        -- Pick a tube near each grid point
        let S_q (q : ℝ × ℝ) : Set CoarseTube := {T ∈ P | f T ∈ Metric.closedBall q step}
        let pick_tube (q : ℝ × ℝ) : CoarseTube :=
          if h : (S_q q).Nonempty then Classical.choose h else default_tube
        have h_pick_spec : ∀ (q : ℝ × ℝ) (h : (S_q q).Nonempty),
            pick_tube q ∈ S_q q := by
          intro q h
          have h_eq : pick_tube q = Classical.choose h := by simp [pick_tube, h]
          rw [h_eq]
          exact Classical.choose_spec h
        let D_P_c (pd : CoarseTube) : Finset CoarseTube := (grid_at pd).image pick_tube
        let D_P : Finset CoarseTube := p_set.biUnion D_P_c
        -- Step 3: D_P is a Δ-cover of P
        have hD_P_cover : Metric.IsCover Δ.toNNReal P (D_P : Set CoarseTube) := by
          intro p hp
          rcases h_p_set_cover hp with ⟨pd, hpd_in_set, hpd_edist⟩
          have hpd_in_P : pd ∈ P := by
            rcases Finset.mem_image.mp hpd_in_set with ⟨d, hd_in_DQnonempty, rfl⟩
            have h_Sd_nonempty : (S_d d).Nonempty := (Finset.mem_filter.mp hd_in_DQnonempty).2
            exact (h_pd_spec d h_Sd_nonempty).1
          have h1 : dist p pd ≤ 2 * Kb * Δ :=
            (edist_toNNReal_iff_dist (by positivity)).mp hpd_edist
          have h2 : dist (f p) (f pd) ≤ Kf * (2 * Kb * Δ) := by
            calc dist (f p) (f pd) ≤ Kf * dist p pd := h_fwd p pd hp hpd_in_P
                 _ ≤ Kf * (2 * Kb * Δ) := by gcongr
          have h3 : f p ∈ Metric.closedBall (f pd) R_grid := by
            have h4 : dist (f p) (f pd) ≤ 2 * Kf * Kb * Δ := by
              rw [show Kf * (2 * Kb * Δ) = 2 * Kf * Kb * Δ by ring] at h2
              exact h2
            simpa [R_grid] using h4
          rcases h_grid_cover pd hpd_in_set h3 with ⟨q, hq_in_grid, hq_edist⟩
          have hq_dist : dist (f p) q ≤ step :=
            (edist_toNNReal_iff_dist hstep_pos.le).mp hq_edist
          have h_inter : (S_q q).Nonempty := ⟨p, hp, hq_dist⟩
          let pg := pick_tube q
          have hpg_in_P : pg ∈ P := (h_pick_spec q h_inter).1
          have hpg_near : f pg ∈ Metric.closedBall q step := (h_pick_spec q h_inter).2
          have hpg_in_DP : pg ∈ (D_P : Set CoarseTube) := by
            have h5 : pg ∈ D_P_c pd := by
              apply Finset.mem_image.mpr
              exact ⟨q, hq_in_grid, rfl⟩
            exact Finset.mem_biUnion.mpr ⟨pd, hpd_in_set, h5⟩
          have h_dist : dist p pg ≤ Δ := by
            have h6 : dist (f p) (f pg) ≤ dist (f p) q + dist q (f pg) := dist_triangle _ _ _
            have h7 : dist (f p) q ≤ step := hq_dist
            have h8 : dist q (f pg) ≤ step := by
              have h81 : dist (f pg) q ≤ step := by simpa [Metric.mem_closedBall] using hpg_near
              rw [dist_comm] at h81
              exact h81
            have h9 : dist (f p) (f pg) ≤ 2 * step := by linarith
            have h10 : dist p pg ≤ Kb * dist (f p) (f pg) := h_bwd p pg hp hpg_in_P
            have h11 : 2 * step = Δ / Kb := by
              simp [step] <;> ring_nf
            rw [h11] at h9
            calc dist p pg ≤ Kb * dist (f p) (f pg) := h10
              _ ≤ Kb * (Δ / Kb) := by gcongr
              _ = Δ := by
                field_simp [hKb_pos.ne'] <;> ring
          have h_edist : edist p pg ≤ ↑Δ.toNNReal := by
            rw [edist_toNNReal_iff_dist hΔ_pos.le]
            exact h_dist
          exact ⟨pg, hpg_in_DP, h_edist⟩
        -- Step 4: cardinality bound
        have hD_P_card : (D_P.card : ℝ) ≤ (p_set.card : ℝ) * Kref := by
          calc (D_P.card : ℝ)
            ≤ (∑ pd ∈ p_set, (D_P_c pd).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
          _ ≤ (∑ pd ∈ p_set, (grid_at pd).card : ℝ) := by
            exact_mod_cast Finset.sum_le_sum (fun pd _ => Finset.card_image_le)
          _ ≤ (∑ pd ∈ p_set, G0.card : ℝ) := by
            exact_mod_cast Finset.sum_le_sum (fun pd _ => by
              simpa [grid_at] using Finset.card_image_le)
          _ = (p_set.card : ℝ) * (G0.card : ℝ) := by simp [Finset.sum_const] <;> ring
          _ ≤ (p_set.card : ℝ) * Kref := by gcongr <;> exact hG0_bound
        have h_p_set_card1 : p_set.card ≤ DQ_nonempty.card := Finset.card_image_le
        have h_p_set_card2 : DQ_nonempty.card ≤ DQfin.card := Finset.card_le_card (Finset.filter_subset _ _)
        have h_p_set_card : p_set.card ≤ DQfin.card := le_trans h_p_set_card1 h_p_set_card2
        have h_final : (D_P.card : ℝ) ≤ (DQfin.card : ℝ) * Kref := by
          calc (D_P.card : ℝ)
            ≤ (p_set.card : ℝ) * Kref := hD_P_card
          _ ≤ (DQfin.card : ℝ) * Kref := by gcongr <;> exact_mod_cast h_p_set_card
        have h_encard : (D_P : Set CoarseTube).encard = ↑D_P.card := by simp
        have h_DQ_encard : D_Q.encard = ↑DQfin.card := by
          exact_mod_cast Set.Finite.encard_eq_coe_toFinset_card hDQfin
        refine' ⟨(D_P : Set CoarseTube), hD_P_cover, _⟩
        rw [h_encard, h_DQ_encard]
        have h_final' : (↑D_P.card : ENNReal) ≤ ENNReal.ofReal Kref * (↑DQfin.card : ENNReal) := by
          have h' : ENNReal.ofReal (D_P.card : ℝ) ≤ ENNReal.ofReal ((DQfin.card : ℝ) * Kref) :=
            ENNReal.ofReal_le_ofReal h_final
          have h'' : ENNReal.ofReal ((DQfin.card : ℝ) * Kref) = (↑DQfin.card : ENNReal) * ENNReal.ofReal Kref := by
            rw [ENNReal.ofReal_mul (by positivity)] <;> simp <;> ring
          rw [h''] at h'
          simpa [mul_comm] using h'
        exact h_final'
      · -- D_Q infinite
        have hDQ_inf : D_Q.encard = ⊤ := by simpa [Set.encard_eq_top] using hDQfin
        refine' ⟨(Set.univ : Set CoarseTube), _, _⟩
        · intro x _
          exact ⟨x, Set.mem_univ x, by simp⟩
        · rw [hDQ_inf]
          have h_ne : ENNReal.ofReal Kref ≠ 0 := by positivity
          simp [h_ne]
    rcases h_main with ⟨D_P, hD_P_cover, hD_P_card⟩
    have h1 : (Metric.externalCoveringNumber Δ.toNNReal P : ENNReal) ≤ (D_P.encard : ENNReal) := by
      exact_mod_cast Metric.IsCover.externalCoveringNumber_le_encard hD_P_cover
    have h2 : (D_P.encard : ENNReal) ≤ ENNReal.ofReal Kref * (D_Q.encard : ENNReal) := hD_P_card
    have h3 : (D_Q.encard : ENNReal) = (Metric.externalCoveringNumber Δ.toNNReal Q : ENNReal) := by
      rw [hD_Q_eq]
    rw [h3] at h2
    exact le_trans h1 h2

  -- Main S-set proof for Q
  have h_main_sset : ∀ (y : ℝ × ℝ) (r : ℝ), Δ ≤ r →
      (Metric.externalCoveringNumber Δ.toNNReal (Q ∩ Metric.closedBall y r) : ENNReal) ≤
        ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber Δ.toNNReal Q : ENNReal) := by
    intro y r hr
    by_cases h_empty : (Q ∩ Metric.closedBall y r).Nonempty
    · rcases h_empty with ⟨q0, hq0_in_Q, hq0_near⟩
      rcases hq0_in_Q with ⟨x0, hx0_in_P, rfl⟩
      have h1 : Q ∩ Metric.closedBall y r ⊆ f '' (P ∩ Metric.closedBall x0 (2 * Kb * r)) := by
        intro q hq
        rcases hq with ⟨q_in_Q, hq_near⟩
        rcases q_in_Q with ⟨p, hp_in_P, rfl⟩
        have h_dist : dist p x0 ≤ 2 * Kb * r := by
          have h2 : dist (f p) (f x0) ≤ dist (f p) y + dist y (f x0) := dist_triangle _ _ _
          have h3 : dist (f p) y ≤ r := hq_near
          have h4 : dist y (f x0) ≤ r := by
            have h41 : dist (f x0) y ≤ r := hq0_near
            rw [dist_comm] at h41
            exact h41
          have h5 : dist (f p) (f x0) ≤ 2 * r := by linarith
          have h6 : dist p x0 ≤ Kb * dist (f p) (f x0) := h_bwd p x0 hp_in_P hx0_in_P
          calc dist p x0 ≤ Kb * dist (f p) (f x0) := h6
            _ ≤ Kb * (2 * r) := by gcongr
            _ = 2 * Kb * r := by ring
        exact ⟨p, ⟨hp_in_P, h_dist⟩, rfl⟩
      have h2 : (Metric.externalCoveringNumber ( (2 * Kf * Δ).toNNReal) (Q ∩ Metric.closedBall y r) : ENNReal) ≤
          (Metric.externalCoveringNumber Δ.toNNReal (P ∩ Metric.closedBall x0 (2 * Kb * r)) : ENNReal) := by
        rcases exists_optimal_cover (S := P ∩ Metric.closedBall x0 (2 * Kb * r)) (ε := Δ.toNNReal)
          with ⟨C_P, hC_P, hC_P_eq⟩
        by_cases hfin : C_P.Finite
        · let C_Pfin := hfin.toFinset
          let default_tube : CoarseTube := hP_nonempty.some
          let S_c (c : CoarseTube) : Set CoarseTube :=
            {p | p ∈ P ∩ Metric.closedBall x0 (2 * Kb * r) ∧ dist p c ≤ Δ}
          let pick_p (c : CoarseTube) : CoarseTube :=
            if h : (S_c c).Nonempty then
              Classical.choose (show ∃ (x : CoarseTube), x ∈ S_c c from h)
            else default_tube
          let C_P'fin : Finset CoarseTube := C_Pfin.image pick_p
          have h_pick_spec : ∀ c, (S_c c).Nonempty → pick_p c ∈ S_c c := by
            intro c h
            have h' : ∃ (x : CoarseTube), x ∈ S_c c := h
            have h_eq : pick_p c = Classical.choose h' := by
              simp [pick_p, h]
            rw [h_eq]
            exact Classical.choose_spec h'
          have h_pick_in_P : ∀ (c : CoarseTube), pick_p c ∈ P := by
            intro c
            by_cases h : (S_c c).Nonempty
            · exact (h_pick_spec c h).1.1
            · have h_eq : pick_p c = default_tube := by simp [pick_p, h]
              rw [h_eq]
              exact hP_nonempty.some_mem
          have hC_P'_cover : Metric.IsCover ( (2 * Δ).toNNReal)
              (P ∩ Metric.closedBall x0 (2 * Kb * r)) (C_P'fin : Set CoarseTube) := by
            intro p hp
            rcases hC_P hp with ⟨c, hc_in, hc_edist⟩
            have h_dist_c : dist p c ≤ Δ := (edist_toNNReal_iff_dist hΔ_pos.le).mp hc_edist
            have h_Sc_nonempty : (S_c c).Nonempty := ⟨p, hp, h_dist_c⟩
            let p' := pick_p c
            have hp'_in : p' ∈ S_c c := h_pick_spec c h_Sc_nonempty
            have hp'_in_P : p' ∈ P ∩ Metric.closedBall x0 (2 * Kb * r) := hp'_in.1
            have hp'_dist : dist p' c ≤ Δ := hp'_in.2
            have hp'_in_set : p' ∈ (C_P'fin : Set CoarseTube) := by
              apply Finset.mem_image.mpr
              exact ⟨c, by simpa [C_Pfin] using hc_in, rfl⟩
            have h_dist_pp' : dist p p' ≤ 2 * Δ := by
              have h1 : dist p c ≤ Δ := h_dist_c
              have h2 : dist c p' ≤ Δ := by
                rw [dist_comm]
                exact hp'_dist
              calc dist p p' ≤ dist p c + dist c p' := dist_triangle _ _ _
                _ ≤ Δ + Δ := by linarith
                _ = 2 * Δ := by ring
            have h_edist : edist p p' ≤ ↑(2 * Δ).toNNReal := by
              rw [edist_toNNReal_iff_dist (by positivity)]
              exact h_dist_pp'
            exact ⟨p', hp'_in_set, h_edist⟩
          let fC_P' : Set (ℝ × ℝ) := f '' (C_P'fin : Set CoarseTube)
          have h_image_cover : Metric.IsCover ( (2 * Kf * Δ).toNNReal)
              (f '' (P ∩ Metric.closedBall x0 (2 * Kb * r))) fC_P' := by
            intro z hz
            rcases hz with ⟨p, hp_in, rfl⟩
            rcases hC_P'_cover hp_in with ⟨p', hp'_in_set, hp'_edist⟩
            have hp'_in_P : p' ∈ P := by
              rcases Finset.mem_image.mp hp'_in_set with ⟨c, _, rfl⟩
              exact h_pick_in_P c
            have h_dist : dist (f p) (f p') ≤ 2 * Kf * Δ := by
              have h1 : dist (f p) (f p') ≤ Kf * dist p p' := h_fwd p p' hp_in.1 hp'_in_P
              have h2 : dist p p' ≤ 2 * Δ := (edist_toNNReal_iff_dist (by positivity)).mp hp'_edist
              calc dist (f p) (f p') ≤ Kf * dist p p' := h1
                _ ≤ Kf * (2 * Δ) := by gcongr
                _ = 2 * Kf * Δ := by ring
            have h_edist : edist (f p) (f p') ≤ ↑(2 * Kf * Δ).toNNReal := by
              rw [edist_toNNReal_iff_dist (by positivity)]
              exact h_dist
            exact ⟨f p', Set.mem_image_of_mem f hp'_in_set, h_edist⟩
          have h_sub : Q ∩ Metric.closedBall y r ⊆ f '' (P ∩ Metric.closedBall x0 (2 * Kb * r)) := h1
          have h_cover : Metric.IsCover ( (2 * Kf * Δ).toNNReal) (Q ∩ Metric.closedBall y r) fC_P' :=
            h_image_cover.anti h_sub
          have h4_nat : Metric.externalCoveringNumber ( (2 * Kf * Δ).toNNReal) (Q ∩ Metric.closedBall y r) ≤ fC_P'.encard :=
            Metric.IsCover.externalCoveringNumber_le_encard h_cover
          have h5_nat : fC_P'.encard ≤ (C_P'fin : Set CoarseTube).encard := Set.encard_image_le f _
          have h9 : C_P'fin.card ≤ C_Pfin.card := Finset.card_image_le
          have h6_nat : (C_P'fin : Set CoarseTube).encard ≤ C_P.encard := by
            have h7 : (C_P'fin : Set CoarseTube).encard = ↑C_P'fin.card := by simp
            have h8 : C_P.encard = ↑C_Pfin.card := by
              exact_mod_cast Set.Finite.encard_eq_coe_toFinset_card hfin
            rw [h7, h8]
            exact_mod_cast h9
          have h10_nat : C_P.encard = Metric.externalCoveringNumber Δ.toNNReal (P ∩ Metric.closedBall x0 (2 * Kb * r)) := hC_P_eq
          have h2_nat : Metric.externalCoveringNumber ( (2 * Kf * Δ).toNNReal) (Q ∩ Metric.closedBall y r) ≤
              Metric.externalCoveringNumber Δ.toNNReal (P ∩ Metric.closedBall x0 (2 * Kb * r)) := by
            calc Metric.externalCoveringNumber ( (2 * Kf * Δ).toNNReal) (Q ∩ Metric.closedBall y r)
              ≤ fC_P'.encard := h4_nat
            _ ≤ (C_P'fin : Set CoarseTube).encard := h5_nat
            _ ≤ C_P.encard := h6_nat
            _ = Metric.externalCoveringNumber Δ.toNNReal (P ∩ Metric.closedBall x0 (2 * Kb * r)) := h10_nat
          exact_mod_cast h2_nat
        · -- C_P infinite, so RHS = ⊤
          have h_inf : C_P.encard = ⊤ := by simpa [Set.encard_eq_top] using hfin
          have h10 : C_P.encard = Metric.externalCoveringNumber Δ.toNNReal (P ∩ Metric.closedBall x0 (2 * Kb * r)) := hC_P_eq
          have h_RHS_top : Metric.externalCoveringNumber Δ.toNNReal (P ∩ Metric.closedBall x0 (2 * Kb * r)) = ⊤ := by
            rw [←h10, h_inf]
          exact_mod_cast (show Metric.externalCoveringNumber ( (2 * Kf * Δ).toNNReal) (Q ∩ Metric.closedBall y r) ≤
            Metric.externalCoveringNumber Δ.toNNReal (P ∩ Metric.closedBall x0 (2 * Kb * r)) from by
            rw [h_RHS_top] <;> exact le_top)
      have h_ratio2 : (2 * Kf * Δ) / Δ = 2 * Kf := by
        field_simp [hΔ_pos.ne'] <;> ring
      have h3 : (Metric.externalCoveringNumber Δ.toNNReal (Q ∩ Metric.closedBall y r) : ENNReal) ≤
          ENNReal.ofReal (49 * (2 * Kf) ^ 2) *
            (Metric.externalCoveringNumber ( (2 * Kf * Δ).toNNReal) (Q ∩ Metric.closedBall y r) : ENNReal) := by
        have h_one_le : 1 ≤ 2 * Kf := by
          dsimp only [Kf]
          linarith
        have h_le : Δ ≤ 2 * Kf * Δ := by
          calc Δ = 1 * Δ := by ring
            _ ≤ (2 * Kf) * Δ := by gcongr <;> linarith
        have h_tmp := covering_refinement_plane (S := Q ∩ Metric.closedBall y r) hΔ_pos (by positivity) h_le
        rw [h_ratio2] at h_tmp
        exact h_tmp
      have h_le2 : Δ ≤ 2 * Kb * r := by
        have h1 : 0 ≤ r := by linarith
        have h2 : 1 ≤ 2 * Kb := by
          dsimp only [Kb]
          linarith
        have h3 : r ≤ (2 * Kb) * r := by
          calc r = 1 * r := by ring
            _ ≤ (2 * Kb) * r := by gcongr <;> linarith
        calc Δ ≤ r := hr
          _ ≤ (2 * Kb) * r := h3
          _ = 2 * Kb * r := by ring
      have h4 : (Metric.externalCoveringNumber Δ.toNNReal
            (P ∩ Metric.closedBall x0 (2 * Kb * r)) : ENNReal) ≤
          ENNReal.ofReal C * (ENNReal.ofReal (2 * Kb * r)) ^ s *
            (Metric.externalCoveringNumber Δ.toNNReal P : ENNReal) :=
        hP.2.2.2.2 x0 (2 * Kb * r) h_le2
      have h5 : (ENNReal.ofReal (2 * Kb * r)) ^ s =
          (ENNReal.ofReal (2 * Kb)) ^ s * (ENNReal.ofReal r) ^ s := by
        have h6 : ENNReal.ofReal (2 * Kb * r) = ENNReal.ofReal (2 * Kb) * ENNReal.ofReal r := by
          rw [ENNReal.ofReal_mul (by positivity)] <;> ring
        rw [h6]
        have h_rpow : ∀ (x y : ENNReal), (x * y) ^ s = x ^ s * y ^ s := by
          intro x y
          exact ENNReal.mul_rpow_of_nonneg x y hs_nonneg
        exact h_rpow _ _
      set A : ENNReal := ENNReal.ofReal (49 * (2 * Kf) ^ 2) * ENNReal.ofReal C * (ENNReal.ofReal (2 * Kb)) ^ s with hA_def
      set B : ENNReal := (ENNReal.ofReal r) ^ s with hB_def
      set N_P : ENNReal := (Metric.externalCoveringNumber Δ.toNNReal P : ENNReal) with hNP_def
      set N_Q : ENNReal := (Metric.externalCoveringNumber Δ.toNNReal Q : ENNReal) with hNQ_def
      have h_const : 49 * (2 * Kf) ^ 2 * C * (2 * Kb) ^ s * Kref ≤ C' := by
        dsimp only [C']
        have h_pos2 : 0 < (2 * Kb) ^ s := by positivity
        have h_ineq : 49 * (2 * Kf) ^ 2 * Kref ≤ 200000 * Kf ^ 4 * Kb ^ 4 := by
          dsimp only [Kref]
          nlinarith
        have h9 : 49 * (2 * Kf) ^ 2 * C * (2 * Kb) ^ s * Kref =
            (49 * (2 * Kf) ^ 2 * Kref) * (C * (2 * Kb) ^ s) := by ring
        rw [h9]
        have h10 : (49 * (2 * Kf) ^ 2 * Kref) * (C * (2 * Kb) ^ s) ≤
            (200000 * Kf ^ 4 * Kb ^ 4) * (C * (2 * Kb) ^ s) := by
          gcongr <;> positivity
        have h11 : (200000 * Kf ^ 4 * Kb ^ 4) * (C * (2 * Kb) ^ s) = C' := by
          dsimp only [C'] <;> ring
        rw [h11] at h10
        exact h10
      have h_rpow_ofReal : (ENNReal.ofReal (2 * Kb)) ^ s = ENNReal.ofReal ((2 * Kb) ^ s) := by
        exact ENNReal.ofReal_rpow_of_nonneg (by positivity) hs_nonneg
      have h_A_Kref_le : A * ENNReal.ofReal Kref ≤ ENNReal.ofReal C' := by
        have h71 : ENNReal.ofReal (49 * (2 * Kf) ^ 2) * ENNReal.ofReal C =
            ENNReal.ofReal (49 * (2 * Kf) ^ 2 * C) := by
          rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
        have h72 : ENNReal.ofReal ((2 * Kb) ^ s) * ENNReal.ofReal Kref =
            ENNReal.ofReal ((2 * Kb) ^ s * Kref) := by
          rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
        have h7 : A * ENNReal.ofReal Kref =
            ENNReal.ofReal (49 * (2 * Kf) ^ 2 * C * (2 * Kb) ^ s * Kref) := by
          simp only [hA_def]
          rw [h_rpow_ofReal]
          repeat rw [←ENNReal.ofReal_mul (by positivity)]
          <;> ring_nf
        rw [h7]
        exact ENNReal.ofReal_le_ofReal h_const
      have h7 : N_P ≤ ENNReal.ofReal Kref * N_Q := h_pullback_refine
      calc (Metric.externalCoveringNumber Δ.toNNReal (Q ∩ Metric.closedBall y r) : ENNReal)
        ≤ ENNReal.ofReal (49 * (2 * Kf) ^ 2) *
            (Metric.externalCoveringNumber ( (2 * Kf * Δ).toNNReal) (Q ∩ Metric.closedBall y r) : ENNReal) := h3
      _ ≤ ENNReal.ofReal (49 * (2 * Kf) ^ 2) *
            (Metric.externalCoveringNumber Δ.toNNReal (P ∩ Metric.closedBall x0 (2 * Kb * r)) : ENNReal) :=
          by gcongr
      _ ≤ ENNReal.ofReal (49 * (2 * Kf) ^ 2) *
            (ENNReal.ofReal C * (ENNReal.ofReal (2 * Kb * r)) ^ s * N_P) := by gcongr
      _ = A * B * N_P := by
          rw [h5] <;> simp [hA_def, hB_def, hNP_def] <;> ring
      _ ≤ A * B * (ENNReal.ofReal Kref * N_Q) := by gcongr
      _ = A * ENNReal.ofReal Kref * B * N_Q := by ring
      _ ≤ ENNReal.ofReal C' * B * N_Q := by gcongr
      _ = ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * N_Q := by
          simp [hB_def, hNQ_def] <;> ring
    · have h_empty' : Q ∩ Metric.closedBall y r = ∅ := by
        simpa [Set.not_nonempty_iff_eq_empty] using h_empty
      rw [h_empty']
      simp
  exact ⟨hQ_nonempty, hΔ_pos, hC'_pos, hs_nonneg, h_main_sset⟩

end DirecretisedFurstenbergEstimate.AppendixA
