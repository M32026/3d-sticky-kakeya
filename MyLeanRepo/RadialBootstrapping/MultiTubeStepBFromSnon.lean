module

/-
  MultiTubeStepBFromSnon.lean

  Multi-tube Step B construction from a direction-separated subset S_non.
  Avoids the multiplicity bound by using injectivity of the grid mapping.

  C_B ≈ r^(-κ-5τ), satisfying ε_F > κ+5τ.
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.TubeLine
public import MyLeanRepo.RadialBootstrapping.TubeFamilies
public import MyLeanRepo.RadialBootstrapping.TxDeltaSet
public import MyLeanRepo.RadialBootstrapping.AbsoluteCountBound
public import MyLeanRepo.RadialBootstrapping.MultiTubeStepB
public import MyLeanRepo.RadialBootstrapping.MultiTubeStepBHelpers
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping
namespace B1

/-- Iterated doubling: a ball of radius R can be covered by D^n balls of radius R/2^n. -/
lemma iterated_doubling_cover {X : Type*} [MetricSpace X]
    (D : ℕ) (hD_pos : 0 < D)
    (h_double : ∀ (x : X) (ε : ℝ), 0 < ε →
      ∃ (S : Finset X), Metric.closedBall x (2 * ε) ⊆ ⋃ y ∈ S, Metric.closedBall y ε ∧ S.card ≤ D)
    (n : ℕ) (x : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ (S : Finset X), Metric.closedBall x ((2 : ℝ)^n * ε) ⊆
      ⋃ y ∈ S, Metric.closedBall y ε ∧ S.card ≤ D^n := by
  have h_ind : ∀ (n : ℕ), ∀ (x : X) (ε : ℝ), 0 < ε →
      ∃ (S : Finset X), Metric.closedBall x ((2 : ℝ)^n * ε) ⊆
        ⋃ y ∈ S, Metric.closedBall y ε ∧ S.card ≤ D^n := by
    intro n
    induction n with
    | zero =>
      intro x ε hε
      refine ⟨{x}, ?_, ?_⟩
      · simpa using Metric.closedBall_subset_closedBall (by positivity)
      · simp
    | succ n ih =>
      intro x ε hε
      rcases ih x (2 * ε) (by positivity) with ⟨S1, hcover1, hcard1⟩
      have h_main : Metric.closedBall x ((2 : ℝ)^(n + 1) * ε) ⊆
          ⋃ z ∈ S1, Metric.closedBall z (2 * ε) := by
        have h_eq : (2 : ℝ)^(n + 1) * ε = (2 : ℝ)^n * (2 * ε) := by ring
        rw [h_eq]; exact hcover1
      choose S_z_dep hS_z_cover hS_z_card using fun (z : X) (_ : z ∈ S1) =>
        h_double z ε hε
      let S_z : X → Finset X := fun z => if h : z ∈ S1 then S_z_dep z h else ∅
      have hS_z_cover' : ∀ z ∈ S1, Metric.closedBall z (2 * ε) ⊆ ⋃ y ∈ S_z z, Metric.closedBall y ε := by
        intro z hz
        have h_eq : S_z z = S_z_dep z hz := by simp [S_z, hz]
        rw [h_eq]; exact hS_z_cover z hz
      have hS_z_card' : ∀ z ∈ S1, (S_z z).card ≤ D := by
        intro z hz
        have h_eq : S_z z = S_z_dep z hz := by simp [S_z, hz]
        rw [h_eq]; exact hS_z_card z hz
      let S_big : Finset X := S1.biUnion S_z
      have h_cover2 : (⋃ z ∈ S1, Metric.closedBall z (2 * ε)) ⊆
          ⋃ y ∈ S_big, Metric.closedBall y ε := by
        intro w hw
        rcases Set.mem_iUnion₂.mp hw with ⟨z, hz, hwz⟩
        have h_in : w ∈ ⋃ y ∈ S_z z, Metric.closedBall y ε := hS_z_cover' z hz hwz
        have h_in' : ∃ (y : X), y ∈ S_z z ∧ w ∈ Metric.closedBall y ε := by
          simpa [Set.mem_iUnion] using h_in
        rcases h_in' with ⟨y, hy_mem, hwy⟩
        have hy_big : y ∈ S_big := Finset.mem_biUnion.mpr ⟨z, hz, hy_mem⟩
        exact Set.mem_iUnion₂.mpr ⟨y, hy_big, hwy⟩
      have h_card : S_big.card ≤ D^(n + 1) := by
        calc S_big.card
          ≤ ∑ z ∈ S1, (S_z z).card := Finset.card_biUnion_le
        _ ≤ ∑ _z ∈ S1, D := Finset.sum_le_sum fun z _ => hS_z_card' z ‹_›
        _ = S1.card * D := by
          simp [Finset.sum_const] <;> ring
        _ ≤ D^n * D := by gcongr
        _ = D^(n + 1) := by ring
      exact ⟨S_big, Set.Subset.trans h_main h_cover2, h_card⟩
  exact h_ind n x ε hε

/-- Covering number lower bound for r/20-separated subset of tubeFamily.
    Each r-ball contains at most D_T^6 grid lines, so covering number ≥ |S| / D_T^6. -/
lemma grid_covering_lower_bound
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (D_T : ℕ) (hD_T_pos : 0 < D_T)
    (h_double_T : ∀ (L : Line2) (ε : ℝ), 0 < ε →
      ∃ (S : Finset Line2), Metric.closedBall L (2 * ε) ⊆ ⋃ M ∈ S, Metric.closedBall M ε ∧ S.card ≤ D_T)
    (S : Finset Line2) (hS_sub : S ⊆ tubeFamily r) (hS_nonempty : S.Nonempty) :
    (S.card : ℝ) ≤ (D_T : ℝ)^6 *
      ((Metric.externalCoveringNumber (⟨r, hr.le⟩ : NNReal) (S : Set Line2)).toNat : ℝ) := by
  have h_sep : ∀ (L1 L2 : Line2), L1 ∈ S → L2 ∈ S → L1 ≠ L2 → dist L1 L2 ≥ r / 20 := by
    intro L1 L2 h1 h2 hne
    exact tubeFamily_separation r hr hr1 L1 L2 (hS_sub h1) (hS_sub h2) hne
  let δn : NNReal := ⟨r, hr.le⟩
  have h64_pos : 0 < r / 64 := by positivity
  have h_cover_ball : ∀ (L : Line2), ∃ (B : Finset Line2),
      Metric.closedBall L r ⊆ ⋃ M ∈ B, Metric.closedBall M (r / 64) ∧ B.card ≤ D_T^6 := by
    intro L
    have h := iterated_doubling_cover D_T hD_T_pos h_double_T 6 L (r / 64) h64_pos
    have h_eq : (2 : ℝ)^6 * (r / 64) = r := by
      have h1 : (2 : ℝ)^6 = 64 := by norm_num
      rw [h1]
      have h2 : (64 : ℝ) * (r / 64) = r := by
        have h3 : (64 : ℝ) ≠ 0 := by norm_num
        field_simp [h3] <;> ring
      exact h2
    rw [h_eq] at h; exact h
  have h_ball_size : ∀ (L : Line2), (S.filter (fun M => M ∈ Metric.closedBall L r)).card ≤ D_T^6 := by
    intro L
    rcases h_cover_ball L with ⟨B, hcover, hcard⟩
    have h_small_one : ∀ (N : Line2), (S.filter (fun M => M ∈ Metric.closedBall N (r / 64))).card ≤ 1 := by
      intro N
      by_contra h2
      have h3 : 1 < (S.filter (fun M => M ∈ Metric.closedBall N (r / 64))).card := by linarith
      rcases Finset.one_lt_card.mp h3 with ⟨M1, hM1, M2, hM2, hne⟩
      have h4 : dist M1 N ≤ r / 64 := (Finset.mem_filter.mp hM1).2
      have h5 : M2 ∈ Metric.closedBall N (r / 64) := (Finset.mem_filter.mp hM2).2
      have h6 : dist N M2 ≤ r / 64 := by simpa [Metric.mem_closedBall, dist_comm] using h5
      have h7 : dist M1 M2 ≤ r / 32 := by
        calc dist M1 M2 ≤ dist M1 N + dist N M2 := dist_triangle _ _ _
          _ ≤ r / 64 + r / 64 := by linarith
          _ = r / 32 := by ring
      have h8 : dist M1 M2 ≥ r / 20 := h_sep M1 M2 (Finset.mem_filter.mp hM1).1 (Finset.mem_filter.mp hM2).1 hne
      linarith
    let S_big := S.filter (fun M => M ∈ Metric.closedBall L r)
    have hchoose : ∀ (M : Line2), M ∈ S_big →
        ∃ (N : Line2), N ∈ B ∧ M ∈ Metric.closedBall N (r / 64) := by
      intro M hM
      have hMball : M ∈ Metric.closedBall L r := (Finset.mem_filter.mp hM).2
      have h_in : M ∈ (⋃ N ∈ B, Metric.closedBall N (r / 64)) := hcover hMball
      rcases Set.mem_iUnion₂.mp h_in with ⟨N, hN, hMN⟩
      exact ⟨N, hN, hMN⟩
    let f : Line2 → Line2 := fun M =>
      if h : M ∈ S_big then Classical.choose (hchoose M h) else M
    have hfB : ∀ M ∈ S_big, f M ∈ B := by
      intro M hM
      have h_f_def : f M = Classical.choose (hchoose M hM) := by
        simp [f, hM]
      rw [h_f_def]; exact (Classical.choose_spec (hchoose M hM)).1
    have hf_in : ∀ M ∈ S_big, M ∈ Metric.closedBall (f M) (r / 64) := by
      intro M hM
      have h_f_def : f M = Classical.choose (hchoose M hM) := by simp [f, hM]
      rw [h_f_def]; exact (Classical.choose_spec (hchoose M hM)).2
    have h_inj : Set.InjOn f (S_big : Set Line2) := by
      intro M1 hM1 M2 hM2 h_eq
      by_contra hne
      have h1 : M1 ∈ Metric.closedBall (f M1) (r / 64) := hf_in M1 hM1
      have h2 : M2 ∈ Metric.closedBall (f M1) (r / 64) := by
        rw [h_eq] at *; exact hf_in M2 hM2
      let F := S.filter (fun M => M ∈ Metric.closedBall (f M1) (r / 64))
      have h4 : M1 ∈ F := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hM1).1, h1⟩
      have h5 : M2 ∈ F := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hM2).1, h2⟩
      have h6 : (insert M1 {M2} : Finset Line2) ⊆ F := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with (rfl | rfl) <;> tauto
      have h7 : (insert M1 {M2} : Finset Line2).card = 2 := by
        simp [hne]
      have h8 : 2 ≤ F.card := by
        calc 2 = (insert M1 {M2} : Finset Line2).card := h7.symm
          _ ≤ F.card := Finset.card_le_card h6
      have h9 := h_small_one (f M1)
      linarith
    have h_img_sub : S_big.image f ⊆ B := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨M, hM, rfl⟩
      exact hfB M hM
    have h_img_card : (S_big.image f).card = S_big.card := by
      rw [Finset.card_image_of_injOn h_inj]
    have h_main : S_big.card ≤ B.card := by
      rw [←h_img_card]; exact Finset.card_le_card h_img_sub
    exact le_trans h_main hcard
  have h_cover_bound : ∀ (C : Finset Line2), (S : Set Line2) ⊆ ⋃ M ∈ C, Metric.closedBall M r →
      S.card ≤ D_T^6 * C.card := by
    intro C hcover
    have h : S.card ≤ ∑ M ∈ C, (S.filter (fun N => N ∈ Metric.closedBall M r)).card := by
      have h1 : S ⊆ (C.biUnion (fun M => S.filter (fun N => N ∈ Metric.closedBall M r))) := by
        intro N hN
        have h3 : N ∈ ⋃ M ∈ C, Metric.closedBall M r := hcover hN
        rcases Set.mem_iUnion₂.mp h3 with ⟨M, hM, hNM⟩
        exact Finset.mem_biUnion.mpr ⟨M, hM, Finset.mem_filter.mpr ⟨hN, hNM⟩⟩
      calc S.card
        ≤ (C.biUnion (fun M => S.filter (fun N => N ∈ Metric.closedBall M r))).card := Finset.card_le_card h1
      _ ≤ ∑ M ∈ C, (S.filter (fun N => N ∈ Metric.closedBall M r)).card := Finset.card_biUnion_le
    calc S.card
      ≤ ∑ M ∈ C, (S.filter (fun N => N ∈ Metric.closedBall M r)).card := h
    _ ≤ ∑ _M ∈ C, D_T^6 := Finset.sum_le_sum fun M _ => h_ball_size M
    _ = C.card * D_T^6 := by
      have h : ∑ _M ∈ C, D_T^6 = C.card * D_T^6 := by
        rw [Finset.sum_const] <;> ring
      exact h
    _ = D_T^6 * C.card := by ring
  have h_main : ∀ (C : Set Line2), Metric.IsCover δn (S : Set Line2) C →
      (S.card : ENat) ≤ (D_T^6 : ENat) * C.encard := by
    intro C hC
    by_cases h_fin : C.Finite
    · let C' : Finset Line2 := h_fin.toFinset
      have h_coe : (C' : Set Line2) = C := by
        ext z; simp [C', Set.Finite.coe_toFinset]
      have hcover' : (S : Set Line2) ⊆ ⋃ M ∈ C', Metric.closedBall M (δn : ℝ) := by
        intro x hx
        have h1 : ∃ (y : Line2), y ∈ C ∧ edist x y ≤ δn := hC hx
        rcases h1 with ⟨y, hyC, hy_dist⟩
        have h2 : dist x y ≤ (δn : ℝ) := by exact_mod_cast hy_dist
        have hyC' : y ∈ C' := by
          simpa [C', Set.Finite.coe_toFinset] using hyC
        exact Set.mem_iUnion₂.mpr ⟨y, hyC', h2⟩
      have h1 : S.card ≤ D_T^6 * C'.card := h_cover_bound C' hcover'
      have h2 : C.encard = (C'.card : ENat) := by
        have h3 : (C' : Set Line2) = C := h_coe
        rw [←h3]; simp
      rw [h2]; exact_mod_cast h1
    · have h_top : C.encard = ⊤ := by
        simpa [Set.encard_eq_top_iff] using h_fin
      rw [h_top]
      have h_mul_top : (D_T^6 : ENat) * (⊤ : ENat) = ⊤ := by
        apply ENat.mul_top
        positivity
      rw [h_mul_top]
      exact le_top
  have h_ecn_fin : Metric.externalCoveringNumber δn (S : Set Line2) ≠ ⊤ := by
    have h1 : Metric.externalCoveringNumber δn (S : Set Line2) ≤ (S : Set Line2).encard :=
      Metric.externalCoveringNumber_le_encard_self (S : Set Line2)
    have h2 : (S : Set Line2).encard < ⊤ := Set.Finite.encard_lt_top (S.finite_toSet)
    exact ne_top_of_le_ne_top h2.ne h1
  let m : ℕ := (Metric.externalCoveringNumber δn (S : Set Line2)).toNat
  have h_eq : Metric.externalCoveringNumber δn (S : Set Line2) = (m : ENat) := by
    exact (ENat.coe_toNat h_ecn_fin).symm
  have h_final : S.card ≤ D_T^6 * m := by
    by_contra h
    have h_lt : D_T^6 * m < S.card := by omega
    have h5 : ∀ (C : Set Line2), Metric.IsCover δn (S : Set Line2) C → (m + 1 : ENat) ≤ C.encard := by
      intro C hC
      by_cases hC_top : C.encard = ⊤
      · rw [hC_top]; simp
      · obtain ⟨n, hn⟩ : ∃ n : ℕ, C.encard = ↑n := by exact Option.ne_none_iff_exists'.mp hC_top
        have h6 : (S.card : ENat) ≤ (D_T^6 : ENat) * C.encard := h_main C hC
        rw [hn] at h6
        have h7 : S.card ≤ D_T^6 * n := by exact_mod_cast h6
        have h9 : D_T^6 * m < D_T^6 * n := by linarith
        have h10 : 0 < D_T^6 := by positivity
        have h11 : m < n := by nlinarith
        have h12 : m + 1 ≤ n := Nat.succ_le_iff.mpr h11
        rw [hn]
        exact_mod_cast h12
    have h9 : (m + 1 : ENat) ≤ Metric.externalCoveringNumber δn (S : Set Line2) := by
      rw [Metric.externalCoveringNumber]
      apply le_iInf
      intro C
      apply le_iInf
      intro hC
      exact h5 C hC
    rw [h_eq] at h9
    have h10 : ¬((m + 1 : ENat) ≤ (m : ENat)) := by
      exact_mod_cast (show ¬(m + 1 ≤ m) from by omega)
    exact False.elim (h10 h9)
  have h_goal : (S.card : ℝ) ≤ (D_T : ℝ)^6 * (m : ℝ) := by exact_mod_cast h_final
  have h_m_eq : (m : ℝ) = ((Metric.externalCoveringNumber δn (S : Set Line2)).toNat : ℝ) := by
    rw [h_eq] <;> simp
  rw [h_m_eq]
  exact h_goal


/-- General normalized IsDeltaSet: if ECN(r, S) ≥ N_lower and every ball of
    radius ρ ≥ r contains at most C_count * ρ^σ points of S, then S is a
    (r, σ, C_count/N_lower)-delta set. -/
lemma normalized_count_to_isDeltaSet
    {X : Type*} [PseudoMetricSpace X]
    {S : Finset X} {r σ C_count N_lower : ℝ}
    (hr : 0 < r) (hσ : 0 ≤ σ)
    (hC_count_nonneg : 0 ≤ C_count)
    (hN_lower_pos : 0 < N_lower)
    (h_ecn_lower : ENNReal.ofReal N_lower ≤
      (Metric.externalCoveringNumber ⟨r, hr.le⟩ (S : Set X) : ENNReal))
    (h_count : ∀ (x : X) (ρ : ℝ), r ≤ ρ →
      (S.filter (fun y => y ∈ Metric.ball x ρ)).card ≤ C_count * Real.rpow ρ σ) :
    IsDeltaSet r σ (C_count / N_lower) hr hσ
      (by positivity) (S : Set X) := by
  let rn : NNReal := ⟨r, hr.le⟩
  intro x ρ hρ
  have hρ_pos : 0 < ρ := lt_of_lt_of_le hr hρ
  let S_ball := S.filter (fun y => y ∈ Metric.ball x ρ)
  have h_set_eq : (S : Set X) ∩ Metric.ball x ρ = (S_ball : Set X) := by
    ext y
    simp only [S_ball, Finset.mem_filter, Set.mem_inter_iff]
    <;> constructor <;> intro h <;> simp_all <;> tauto
  rw [h_set_eq]
  have h_ecn_upper : (Metric.externalCoveringNumber rn (S_ball : Set X) : ENNReal) ≤
      (S_ball.card : ENNReal) := by
    have h : Metric.externalCoveringNumber rn (S_ball : Set X) ≤
        (S_ball : Set X).encard := Metric.externalCoveringNumber_le_encard_self _
    have h2 : (S_ball : Set X).encard = ↑(S_ball.card) := by simp
    rw [h2] at h
    exact_mod_cast h
  have h_card_bound : (S_ball.card : ℝ) ≤ C_count * Real.rpow ρ σ :=
    h_count x ρ hρ
  have h_ecn_ball : (Metric.externalCoveringNumber rn (S_ball : Set X) : ENNReal) ≤
      ENNReal.ofReal (C_count * Real.rpow ρ σ) := by
    calc (Metric.externalCoveringNumber rn (S_ball : Set X) : ENNReal)
      ≤ (S_ball.card : ENNReal) := h_ecn_upper
      _ = ENNReal.ofReal (S_ball.card : ℝ) := by simp
      _ ≤ ENNReal.ofReal (C_count * Real.rpow ρ σ) := by gcongr
  let a : ℝ := (C_count / N_lower) * Real.rpow ρ σ
  have ha_nonneg : 0 ≤ a := by
    dsimp only [a]
    have h1 : 0 ≤ C_count / N_lower := div_nonneg hC_count_nonneg hN_lower_pos.le
    have h2 : 0 ≤ Real.rpow ρ σ := Real.rpow_nonneg hρ_pos.le σ
    exact mul_nonneg h1 h2
  have h3 : a * N_lower = C_count * Real.rpow ρ σ := by
    dsimp only [a]
    field_simp [hN_lower_pos.ne'] <;> ring
  have h_rhs_ge : ENNReal.ofReal (C_count * Real.rpow ρ σ) ≤
      ENNReal.ofReal a * (Metric.externalCoveringNumber rn (S : Set X) : ENNReal) := by
    have h1 : ENNReal.ofReal a * (Metric.externalCoveringNumber rn (S : Set X) : ENNReal) ≥
        ENNReal.ofReal a * ENNReal.ofReal N_lower := by
      gcongr <;> exact h_ecn_lower
    have h2 : ENNReal.ofReal a * ENNReal.ofReal N_lower = ENNReal.ofReal (a * N_lower) := by
      rw [ENNReal.ofReal_mul ha_nonneg] <;> rfl
    rw [h2, h3] at h1
    exact h1
  exact le_trans h_ecn_ball h_rhs_ge

/-- Multi-tube Step B construction from a direction-separated subset S_non.

    Uses injectivity of grid mapping (no multiplicity bound needed).
    C_B ≈ r^(-κ-5τ), satisfying ε_F > κ+5τ.

    Input: S_non with grid mapping already provided and proved injective.
    Output: h_step_B_data format.
-/
lemma multi_tube_step_B_from_Snon
    {ν₂ : Measure Point} [IsProbabilityMeasure ν₂]
    {r σ τ κ K ε_F : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hr_small : r < 1) (hr2 : 2 * r ≤ 1)
    (hσ_pos : 0 < σ) (hσ_lt_one : σ < 1) (hτ : 0 < τ) (hκ_pos : 0 < κ) (hκ_lt_one : κ < 1)
    (hr_small4 : 4 * r^(1 - κ) ≤ 1)
    (hK : 1 ≤ K)
    (x : Point) (hxBall : x ∈ closedBall (0 : Point) 1)
    -- S_non and its grid mapping
    (S_non : Finset Line2)
    (hS_non_nonempty : S_non.Nonempty)
    (hS_non_card : (S_non.card : ℝ) ≥ Real.rpow r (2 * τ - σ) / (2 * K * (2 : ℝ)^σ))
    (gridMap : Line2 → Line2)
    (hGridMap_mem : ∀ L ∈ S_non, gridMap L ∈ tubeFamily r)
    (hGridMap_2r : ∀ L ∈ S_non, x ∈ tube (2 * r) (gridMap L))
    (hGridMap_contain : ∀ L ∈ S_non, tube r L ∩ closedBall (0 : Point) 1 ⊆ tube (2 * r) (gridMap L))
    (hGridMap_inj : Set.InjOn gridMap (S_non : Set Line2))
    -- Y_x
    (Y_x : Set Point)
    (hY_meas : MeasurableSet Y_x)
    (hY_sub1 : Y_x ⊆ closedBall (0 : Point) 1)
    (hY_mass : ν₂ Y_x ≥ ENNReal.ofReal (Real.rpow r (2 * τ)))
    -- Per-line properties for L ∈ S_non
    (h_mass_lower : ∀ L ∈ S_non,
        ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) ≤ ν₂ (tubeLine r L.toAffine ∩ Y_x))
    (h_mass_upper : ∀ L ∈ S_non,
        ν₂ (tubeLine r L.toAffine ∩ Y_x) ≤ ENNReal.ofReal (Real.rpow r (σ - τ)))
    (h_nonconc : ∀ L ∈ S_non,
        IsNonConcentrated ν₂ Y_x (tubeLine r L.toAffine) r κ)
    -- Thin tubes (Y_x-restricted)
    (h_thin : ∀ (l : AffineSubspace ℝ Point), x ∈ (l : Set Point) →
        Module.finrank ℝ l.direction = 1 → ∀ ρ : ℝ, 0 < ρ →
          ν₂ (tubeLine ρ l ∩ Y_x) ≤ ENNReal.ofReal (K * Real.rpow ρ σ))
    -- Doubling
    (D_T : ℕ) (hD_T_pos : 0 < D_T)
    (h_double_T : ∀ (L : Line2) (ε : ℝ), 0 < ε →
      ∃ (S : Finset Line2), Metric.closedBall L (2 * ε) ⊆ ⋃ M ∈ S, Metric.closedBall M ε ∧ S.card ≤ D_T)
    -- C_B bound hypothesis (caller proves from parameter selection)
    (hC_B_bound :
      (max (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 * Real.rpow r (-(κ + 5 * τ))) 1) * (D_T : ℝ)
        ≤ Real.rpow (2 * r) (-ε_F)) :
    ∃ (S_x : Finset Line2) (A_x : Line2 → Set Point) (C_B : ℝ) (hC_B : 0 ≤ C_B),
      S_x.Nonempty ∧
      (∀ L ∈ S_x, L ∈ (tubeFamily r : Set Line2) ∧ x ∈ tube (2 * r) L) ∧
      IsDeltaSet r σ C_B hr hσ_pos.le hC_B (S_x : Set Line2) ∧
      C_B * (D_T : ℝ) ≤ Real.rpow (2 * r) (-ε_F) ∧
      (∀ L ∈ S_x, MeasurableSet (A_x L) ∧ A_x L ⊆ tube (2 * r) L ∧
        ν₂ (A_x L) ≥ ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) ∧
        (∀ (z : Point), ν₂ (A_x L ∩ Metric.ball z (Real.rpow r κ)) ≤ ν₂ (A_x L) / 3)) := by
  classical
  have hσ : 0 ≤ σ := le_of_lt hσ_pos

  -- Step 1: S_x = image of S_non under gridMap
  let S_x : Finset Line2 := S_non.image gridMap
  have hS_card_eq : S_x.card = S_non.card :=
    Finset.card_image_of_injOn hGridMap_inj
  have hS_nonempty' : S_x.Nonempty :=
    hS_non_nonempty.image _
  have hS_sub : S_x ⊆ tubeFamily r := by
    intro L hL
    rcases Finset.mem_image.mp hL with ⟨L0, hL0, rfl⟩
    exact hGridMap_mem L0 hL0
  have hS_2r : ∀ L ∈ S_x, x ∈ tube (2 * r) L := by
    intro L hL
    rcases Finset.mem_image.mp hL with ⟨L0, hL0, rfl⟩
    exact hGridMap_2r L0 hL0

  -- Step 2: Choose preimage for each L ∈ S_x
  have h_repr_exists : ∀ (L : Line2), L ∈ S_x →
      ∃ (L0 : Line2), L0 ∈ S_non ∧ gridMap L0 = L := by
    intro L hL
    rcases Finset.mem_image.mp hL with ⟨L0, hL0, h_eq⟩
    exact ⟨L0, hL0, h_eq⟩
  choose L_repr hL_repr_in hL_repr_grid using h_repr_exists

  -- Step 3: Define A_x
  let A_x : Line2 → Set Point := fun L =>
    if hL : L ∈ S_x then
      tubeLine r (L_repr L hL).toAffine ∩ Y_x
    else ∅

  have hA_meas : ∀ L ∈ S_x, MeasurableSet (A_x L) := by
    intro L hL
    dsimp only [A_x]; rw [dif_pos hL]
    exact (isOpen_thickening.measurableSet).inter hY_meas

  have hA_sub2r : ∀ L ∈ S_x, A_x L ⊆ tube (2 * r) L := by
    intro L hL
    dsimp only [A_x]; rw [dif_pos hL]
    let L0 := L_repr L hL
    have hL0_in : L0 ∈ S_non := hL_repr_in L hL
    have h_eq : gridMap L0 = L := hL_repr_grid L hL
    have h_contain : tube r L0 ∩ closedBall (0 : Point) 1 ⊆ tube (2 * r) L := by
      have h : tube r L0 ∩ closedBall (0 : Point) 1 ⊆ tube (2 * r) (gridMap L0) :=
        hGridMap_contain L0 hL0_in
      rw [h_eq] at h
      exact h
    have h_sub1 : tubeLine r L0.toAffine ∩ Y_x ⊆ tube r L0 ∩ closedBall (0 : Point) 1 := by
      intro y hy
      exact ⟨hy.1, hY_sub1 hy.2⟩
    exact h_sub1.trans h_contain

  have hA_Y : ∀ L ∈ S_x, A_x L ⊆ Y_x := by
    intro L hL
    dsimp only [A_x]; rw [dif_pos hL]
    exact Set.inter_subset_right

  have hA_mass : ∀ L ∈ S_x, ν₂ (A_x L) ≥ ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) := by
    intro L hL
    dsimp only [A_x]; rw [dif_pos hL]
    let L0 := L_repr L hL
    have hL0_in : L0 ∈ S_non := hL_repr_in L hL
    exact h_mass_lower L0 hL0_in

  have hA_nonconc : ∀ L ∈ S_x, ∀ (z : Point),
      ν₂ (A_x L ∩ Metric.ball z (Real.rpow r κ)) ≤ ν₂ (A_x L) / 3 := by
    intro L hL z
    dsimp only [A_x]; rw [dif_pos hL]
    let L0 := L_repr L hL
    have hL0_in : L0 ∈ S_non := hL_repr_in L hL
    have h_nc : IsNonConcentrated ν₂ Y_x (tubeLine r L0.toAffine) r κ :=
      h_nonconc L0 hL0_in
    have h9 : (tubeLine r L0.toAffine ∩ Y_x) ∩ Metric.ball z (Real.rpow r κ) =
        tubeLine r L0.toAffine ∩ Metric.ball z (Real.rpow r κ) ∩ Y_x := by
      ext y; simp [and_assoc, and_comm, and_left_comm] <;> tauto
    rw [h9]
    have h10 := h_nc z
    have h_div : (1 / 3 : ENNReal) * ν₂ (tubeLine r L0.toAffine ∩ Y_x) =
        ν₂ (tubeLine r L0.toAffine ∩ Y_x) / 3 := by
      simp [div_eq_mul_inv, mul_comm] <;> ring
    rw [h_div] at h10
    exact h10

  have hA_nonconc_x : ∀ L ∈ S_x,
      ν₂ (A_x L ∩ Metric.ball x (Real.rpow r κ)) ≤ (1 / 3 : ENNReal) * ν₂ (A_x L) := by
    intro L hL
    have h := hA_nonconc L hL x
    have h2 : ν₂ (A_x L) / 3 = (1 / 3 : ENNReal) * ν₂ (A_x L) := by
      simp [div_eq_mul_inv, mul_comm] <;> norm_num
    rw [h2] at h
    exact h

  -- Step 4: Conditional mass upper bound
  let K' : ℝ := K * (17 : ℝ)^σ
  have hK'_nonneg : 0 ≤ K' := by positivity

  have h_mass_upper_cond : ∀ (L : Line2) (ρ : ℝ), r ≤ ρ → ρ ≤ 1 →
      (S_x.filter (fun L' => L' ∈ Metric.ball L ρ)).Nonempty →
        ν₂ (tube (2 * r + 4 * ρ) L ∩ Y_x) ≤ ENNReal.ofReal (K' * Real.rpow ρ σ) := by
    intro L ρ hρ hρ1 h_nonempty
    exact conditional_mass_upper_bound hr hσ (by linarith) hρ1 hρ hK x Y_x hY_sub1
      S_x hS_2r L h_nonempty h_thin

  -- Step 5: Count bound
  let C_count : ℝ := (30000 / Real.rpow r κ) * K' / Real.rpow r (σ + 3 * τ)
  have hC_count_nonneg : 0 ≤ C_count := by
    dsimp only [C_count, K']
    have h1 : 0 ≤ 30000 / Real.rpow r κ := by
      apply div_nonneg <;> norm_num <;> exact Real.rpow_nonneg hr.le κ
    have h2 : 0 ≤ K * (17 : ℝ)^σ := by positivity
    have h3 : 0 ≤ Real.rpow r (σ + 3 * τ) := Real.rpow_nonneg hr.le _
    have h12 : 0 ≤ (30000 / Real.rpow r κ) * (K * (17 : ℝ)^σ) := mul_nonneg h1 h2
    exact div_nonneg h12 h3

  have h_count : ∀ (L : Line2) (ρ : ℝ), r ≤ ρ → ρ ≤ 1 →
      (S_x.filter (fun L' => L' ∈ Metric.ball L ρ)).card ≤ C_count * Real.rpow ρ σ :=
    grid_family_absolute_count_gen_conditional r σ κ hr hr1 hr2 hσ hκ_pos hκ_lt_one
      hr_small4 x hxBall S_x hS_sub hS_2r Y_x hY_meas hY_sub1 ν₂ A_x hA_meas hA_sub2r hA_Y hA_nonconc_x
      K' (Real.rpow r (σ + 3 * τ)) hK'_nonneg
      (Real.rpow_pos_of_pos hr (σ + 3 * τ)) h_mass_upper_cond hA_mass

  -- Step 6: ECN lower bound
  let δn : NNReal := ⟨r, hr.le⟩
  let ecn : ENat := Metric.externalCoveringNumber δn (S_x : Set Line2)
  have h_ecn_fin : ecn ≠ ⊤ := by
    have h : ecn ≤ (S_x : Set Line2).encard := Metric.externalCoveringNumber_le_encard_self (S_x : Set Line2)
    have h2 : (S_x : Set Line2).encard < ⊤ := Set.Finite.encard_lt_top (S_x.finite_toSet)
    exact ne_top_of_le_ne_top h2.ne h
  have h_ecn_real : (S_x.card : ℝ) ≤ (D_T : ℝ)^6 * (ecn.toNat : ℝ) :=
    grid_covering_lower_bound r hr hr1 D_T hD_T_pos h_double_T S_x hS_sub hS_nonempty'
  have h_ecn_coe : (ecn : ENNReal) = ↑(ecn.toNat) := by
    exact_mod_cast (ENat.coe_toNat h_ecn_fin).symm
  have h_ecn_lower : (S_x.card : ENNReal) ≤ (D_T : ENNReal)^6 * (ecn : ENNReal) := by
    rw [h_ecn_coe]
    exact_mod_cast h_ecn_real

  -- Step 7: Define N_lower and C_B
  let N_lower : ℝ := (S_x.card : ℝ) / (D_T : ℝ)^6
  have hN_lower_pos : 0 < N_lower := by
    dsimp only [N_lower]
    have h1 : 0 < (S_x.card : ℝ) := by exact_mod_cast hS_nonempty'.card_pos
    have h2 : 0 < (D_T : ℝ)^6 := by positivity
    exact div_pos h1 h2

  have h_ecn_lower' : ENNReal.ofReal N_lower ≤ (ecn : ENNReal) := by
    have h_pos : 0 < (D_T : ℝ)^6 := by positivity
    have h_real2 : N_lower ≤ (ecn.toNat : ℝ) := by
      dsimp only [N_lower]
      calc (S_x.card : ℝ) / (D_T : ℝ)^6
        ≤ ((D_T : ℝ)^6 * (ecn.toNat : ℝ)) / (D_T : ℝ)^6 := by gcongr
      _ = (ecn.toNat : ℝ) := by
        field_simp [h_pos.ne'] <;> ring
    have h3 : ENNReal.ofReal N_lower ≤ ENNReal.ofReal (ecn.toNat : ℝ) := by
      exact_mod_cast h_real2
    have h4 : ENNReal.ofReal (ecn.toNat : ℝ) = (ecn : ENNReal) := by
      rw [h_ecn_coe] <;> simp
    rw [h4] at h3
    exact h3

  let C_B : ℝ := max (C_count / N_lower) 1
  have hC_B_nonneg : 0 ≤ C_B := by positivity
  have hC_B_ge1 : 1 ≤ C_B := le_max_right _ _
  have hC_B_ge_raw : C_B ≥ C_count / N_lower := le_max_left _ _

  -- Step 7b: IsDeltaSet with split on ρ ≤ 1
  have h_isDelta : IsDeltaSet r σ C_B hr hσ hC_B_nonneg (S_x : Set Line2) := by
    intro x0 ρ hρ
    by_cases hρ1 : ρ ≤ 1
    · -- Case r ≤ ρ ≤ 1: use count bound
      have hρ_pos : 0 < ρ := lt_of_lt_of_le hr hρ
      let S_ball := S_x.filter (fun y => y ∈ Metric.ball x0 ρ)
      have h_set_eq : (S_x : Set Line2) ∩ Metric.ball x0 ρ = (S_ball : Set Line2) := by
        ext y; simp [S_ball, Finset.mem_filter, Set.mem_inter_iff] <;> tauto
      rw [h_set_eq]
      have h_ecn_upper : (Metric.externalCoveringNumber δn (S_ball : Set Line2) : ENNReal) ≤
          (S_ball.card : ENNReal) := by
        have h : Metric.externalCoveringNumber δn (S_ball : Set Line2) ≤ (S_ball : Set Line2).encard :=
          Metric.externalCoveringNumber_le_encard_self _
        have h2 : (S_ball : Set Line2).encard = ↑(S_ball.card) := by simp
        rw [h2] at h; exact_mod_cast h
      have h_card : (S_ball.card : ℝ) ≤ C_count * Real.rpow ρ σ := h_count x0 ρ hρ hρ1
      have h_ecn_ball : (Metric.externalCoveringNumber δn (S_ball : Set Line2) : ENNReal) ≤
          ENNReal.ofReal (C_count * Real.rpow ρ σ) := by
        calc (Metric.externalCoveringNumber δn (S_ball : Set Line2) : ENNReal)
          ≤ (S_ball.card : ENNReal) := h_ecn_upper
        _ = ENNReal.ofReal (S_ball.card : ℝ) := by simp
        _ ≤ ENNReal.ofReal (C_count * Real.rpow ρ σ) := by gcongr
      let a : ℝ := (C_count / N_lower) * Real.rpow ρ σ
      have ha_nonneg : 0 ≤ a := by
        dsimp only [a]
        have h1 : 0 ≤ C_count / N_lower := div_nonneg hC_count_nonneg hN_lower_pos.le
        have h2 : 0 ≤ Real.rpow ρ σ := Real.rpow_nonneg hρ_pos.le σ
        exact mul_nonneg h1 h2
      have h3 : a * N_lower = C_count * Real.rpow ρ σ := by
        dsimp only [a]
        field_simp [hN_lower_pos.ne'] <;> ring
      have h_rhs_ge : ENNReal.ofReal (C_count * Real.rpow ρ σ) ≤
          ENNReal.ofReal (C_B * Real.rpow ρ σ) * (ecn : ENNReal) := by
        have h1 : ENNReal.ofReal (C_count * Real.rpow ρ σ) =
            ENNReal.ofReal a * ENNReal.ofReal N_lower := by
          have h_eq1 : C_count * Real.rpow ρ σ = a * N_lower := by
            dsimp only [a]; field_simp [hN_lower_pos.ne'] <;> ring
          rw [h_eq1, ENNReal.ofReal_mul ha_nonneg] <;> rfl
        rw [h1]
        have h2 : ENNReal.ofReal N_lower ≤ (ecn : ENNReal) := h_ecn_lower'
        have h3 : a ≤ C_B * Real.rpow ρ σ := by
          dsimp only [a]
          have h4 : C_count / N_lower ≤ C_B := hC_B_ge_raw
          have h5 : 0 ≤ Real.rpow ρ σ := Real.rpow_nonneg hρ_pos.le σ
          exact mul_le_mul_of_nonneg_right h4 h5
        have h6 : ENNReal.ofReal a ≤ ENNReal.ofReal (C_B * Real.rpow ρ σ) := by
          have h7 : 0 ≤ C_B * Real.rpow ρ σ := mul_nonneg hC_B_nonneg (Real.rpow_nonneg hρ_pos.le σ)
          gcongr
        have h_goal : ENNReal.ofReal a * ENNReal.ofReal N_lower ≤
            ENNReal.ofReal (C_B * Real.rpow ρ σ) * (ecn : ENNReal) := by
          calc ENNReal.ofReal a * ENNReal.ofReal N_lower
            ≤ ENNReal.ofReal a * (ecn : ENNReal) := mul_le_mul_of_nonneg_left h2 (by positivity)
          _ ≤ ENNReal.ofReal (C_B * Real.rpow ρ σ) * (ecn : ENNReal) := mul_le_mul_of_nonneg_right h6 (by positivity)
        exact h_goal
      exact le_trans h_ecn_ball h_rhs_ge
    · -- Case ρ > 1: ECN(subset) ≤ ECN(S) ≤ C_B * ρ^σ * ECN(S)
      have hρ_gt_one : 1 < ρ := by linarith
      have h_sub : (S_x : Set Line2) ∩ Metric.ball x0 ρ ⊆ (S_x : Set Line2) := Set.inter_subset_left
      have h1 : (Metric.externalCoveringNumber δn ((S_x : Set Line2) ∩ Metric.ball x0 ρ) : ENNReal) ≤
          (ecn : ENNReal) := mod_cast Metric.externalCoveringNumber_mono_set h_sub
      have h2 : 1 ≤ C_B * Real.rpow ρ σ := by
        have h22 : 1 ≤ Real.rpow ρ σ := Real.one_le_rpow (show 1 ≤ ρ by linarith) hσ
        have hCB : 1 ≤ C_B := hC_B_ge1
        nlinarith
      have h3 : (1 : ENNReal) ≤ ENNReal.ofReal (C_B * Real.rpow ρ σ) := by
        rw [ENNReal.one_le_ofReal] <;> linarith
      have h4 : (ecn : ENNReal) ≤ ENNReal.ofReal (C_B * Real.rpow ρ σ) * (ecn : ENNReal) :=
        le_mul_of_one_le_left' h3
      exact le_trans h1 h4

  -- Step 8: C_B bound
  have hS_card_lower : (S_x.card : ℝ) ≥ Real.rpow r (2 * τ - σ) / (2 * K * (2 : ℝ)^σ) := by
    rw [hS_card_eq]; exact hS_non_card

  have hC_B_le : C_B ≤ 60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 * Real.rpow r (-(κ + 5 * τ)) := by
    dsimp only [C_B]
    have h_card_pos : 0 < (S_x.card : ℝ) := by exact_mod_cast hS_nonempty'.card_pos
    have h_DT_pos : 0 < (D_T : ℝ)^6 := by positivity
    have h_low_pos : 0 < Real.rpow r (2 * τ - σ) / (2 * K * (2 : ℝ)^σ) := by
      have h1 : 0 < Real.rpow r (2 * τ - σ) := Real.rpow_pos_of_pos hr (2 * τ - σ)
      have h2 : 0 < 2 * K * (2 : ℝ)^σ := by positivity
      exact div_pos h1 h2
    have h_div : C_count / N_lower = C_count * (D_T : ℝ)^6 / (S_x.card : ℝ) := by
      dsimp only [N_lower]
      field_simp [h_card_pos.ne', h_DT_pos.ne'] <;> ring
    rw [h_div]
    have h_num_nonneg : 0 ≤ C_count * (D_T : ℝ)^6 := by positivity
    have h_main : C_count * (D_T : ℝ)^6 / (S_x.card : ℝ) ≤
        C_count * (D_T : ℝ)^6 / (Real.rpow r (2 * τ - σ) / (2 * K * (2 : ℝ)^σ)) := by
      apply div_le_div_of_nonneg_left h_num_nonneg
      <;> linarith [hS_card_lower]
    have h_final : C_count * (D_T : ℝ)^6 / (Real.rpow r (2 * τ - σ) / (2 * K * (2 : ℝ)^σ)) =
        60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 * Real.rpow r (-(κ + 5 * τ)) := by
      dsimp only [C_count, K']
      set rκ := Real.rpow r κ with hrκ_def
      set rσ := Real.rpow r σ with hrσ_def
      set r3τ := Real.rpow r (3 * τ) with hr3τ_def
      set r2τ := Real.rpow r (2 * τ) with hr2τ_def
      set rk5τ := Real.rpow r (κ + 5 * τ) with hrk5τ_def
      have hrκ_pos : 0 < rκ := Real.rpow_pos_of_pos hr κ
      have hrσ_pos : 0 < rσ := Real.rpow_pos_of_pos hr σ
      have hr3τ_pos : 0 < r3τ := Real.rpow_pos_of_pos hr (3 * τ)
      have hr2τ_pos : 0 < r2τ := Real.rpow_pos_of_pos hr (2 * τ)
      have hrk5τ_pos : 0 < rk5τ := Real.rpow_pos_of_pos hr (κ + 5 * τ)
      have h172 : (17 : ℝ)^σ * (2 : ℝ)^σ = (34 : ℝ)^σ := by
        rw [← Real.mul_rpow] <;> norm_num
      have h_denom : rκ * r3τ * r2τ = rk5τ := by
        simp only [hrk5τ_def, hr3τ_def, hr2τ_def, hrκ_def]
        have h51 : Real.rpow r (κ + 5 * τ) = Real.rpow r κ * Real.rpow r (5 * τ) := Real.rpow_add hr κ (5 * τ)
        have h52 : Real.rpow r (5 * τ) = Real.rpow r (3 * τ) * Real.rpow r (2 * τ) := by
          have h53 := Real.rpow_add hr (3 * τ) (2 * τ)
          have h54 : (3 * τ) + (2 * τ) = 5 * τ := by ring
          rw [h54] at h53; exact h53
        rw [h51, h52] <;> ring
      have h_rpow_neg2 : Real.rpow r (-(κ + 5 * τ)) = rk5τ⁻¹ := Real.rpow_neg hr.le (κ + 5 * τ)
      have h_rpow_sub2 : Real.rpow r (2 * τ - σ) = r2τ / rσ := by
        have h_eq : Real.rpow r (2 * τ) = Real.rpow r (2 * τ - σ) * Real.rpow r σ := by
          have h2 := Real.rpow_add hr (2 * τ - σ) σ
          have h3 : (2 * τ - σ) + σ = 2 * τ := by ring
          rw [h3] at h2; exact h2
        have h : Real.rpow r (2 * τ - σ) * rσ = r2τ := by
          exact h_eq.symm
        field_simp [hrσ_pos.ne'] at h ⊢; exact h
      have h_rpow_add2 : Real.rpow r (σ + 3 * τ) = rσ * r3τ := Real.rpow_add hr σ (3 * τ)
      rw [h_rpow_neg2, h_rpow_sub2, h_rpow_add2]
      field_simp [hrκ_pos.ne', hrσ_pos.ne', hr3τ_pos.ne', hr2τ_pos.ne', hrk5τ_pos.ne']
      have h_goal : (30000 : ℝ) * (17 : ℝ)^σ * 2 * (2 : ℝ)^σ * rk5τ =
          rκ * r3τ * r2τ * (60000 : ℝ) * (34 : ℝ)^σ := by
        have h10 : rκ * r3τ * r2τ = rk5τ := h_denom
        have h11 : (30000 : ℝ) * (17 : ℝ)^σ * 2 * (2 : ℝ)^σ = (60000 : ℝ) * (34 : ℝ)^σ := by
          have h12 : (17 : ℝ)^σ * (2 : ℝ)^σ = (34 : ℝ)^σ := h172
          calc (30000 : ℝ) * (17 : ℝ)^σ * 2 * (2 : ℝ)^σ
            = (30000 : ℝ) * 2 * ((17 : ℝ)^σ * (2 : ℝ)^σ) := by ring
          _ = (60000 : ℝ) * ((17 : ℝ)^σ * (2 : ℝ)^σ) := by ring
          _ = (60000 : ℝ) * (34 : ℝ)^σ := by rw [h12]
        rw [h10, h11] <;> ring
      exact h_goal
    have h_bound_ge1 : (1 : ℝ) ≤ 60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 * Real.rpow r (-(κ + 5 * τ)) := by
      have h1 : 1 ≤ 60000 := by norm_num
      have h2 : 1 ≤ K^2 := by nlinarith
      have h3 : 1 ≤ (34 : ℝ)^σ := Real.one_le_rpow (by norm_num) (by linarith [hσ_pos])
      have h4 : 1 ≤ (D_T : ℝ)^6 := by
        have h5 : 1 ≤ (D_T : ℝ) := by exact_mod_cast hD_T_pos
        have h6 : (1 : ℝ)^6 ≤ (D_T : ℝ)^6 := by gcongr
        norm_num at h6 ⊢; exact h6
      have h64 : Real.rpow r (κ + 5 * τ) ≤ 1 := Real.rpow_le_one hr.le hr1 (by linarith [hκ_pos, hτ])
      have h65 : 0 < Real.rpow r (κ + 5 * τ) := Real.rpow_pos_of_pos hr (κ + 5 * τ)
      have h6 : 1 ≤ Real.rpow r (-(κ + 5 * τ)) := by
        have h66 : Real.rpow r (-(κ + 5 * τ)) = (Real.rpow r (κ + 5 * τ))⁻¹ := Real.rpow_neg hr.le (κ + 5 * τ)
        rw [h66]
        have h67 : (Real.rpow r (κ + 5 * τ))⁻¹ ≥ (1 : ℝ)⁻¹ := by gcongr
        norm_num at h67 ⊢; exact h67
      have h_pos1 : 0 ≤ 60000 * K^2 := by positivity
      have h7a : 1 ≤ 60000 * K^2 := by nlinarith
      have h_pos2 : 0 ≤ 60000 * K^2 * (34 : ℝ)^σ := by positivity
      have h7b : 1 ≤ 60000 * K^2 * (34 : ℝ)^σ := by
        have h : (60000 * K^2) * 1 ≤ (60000 * K^2) * (34 : ℝ)^σ := mul_le_mul_of_nonneg_left h3 h_pos1
        have h' : 60000 * K^2 ≤ 60000 * K^2 * (34 : ℝ)^σ := by simpa using h
        exact le_trans h7a h'
      have h_pos3 : 0 ≤ 60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 := by positivity
      have h7c : 1 ≤ 60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 := by
        have h : (60000 * K^2 * (34 : ℝ)^σ) * 1 ≤ (60000 * K^2 * (34 : ℝ)^σ) * (D_T : ℝ)^6 :=
          mul_le_mul_of_nonneg_left h4 h_pos2
        have h' : 60000 * K^2 * (34 : ℝ)^σ ≤ 60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 := by simpa using h
        exact le_trans h7b h'
      have h_pos4 : 0 ≤ 60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 := h_pos3
      have h7 : 1 ≤ 60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 * Real.rpow r (-(κ + 5 * τ)) := by
        have h : (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6) * 1 ≤
            (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6) * Real.rpow r (-(κ + 5 * τ)) :=
          mul_le_mul_of_nonneg_left h6 h_pos4
        have h' : 60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 ≤
            60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 * Real.rpow r (-(κ + 5 * τ)) := by simpa using h
        exact le_trans h7c h'
      exact h7
    have h_main' : C_count * (D_T : ℝ)^6 / (S_x.card : ℝ) ≤
        60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 * Real.rpow r (-(κ + 5 * τ)) := by
      calc C_count * (D_T : ℝ)^6 / (S_x.card : ℝ)
        ≤ C_count * (D_T : ℝ)^6 / (Real.rpow r (2 * τ - σ) / (2 * K * (2 : ℝ)^σ)) := h_main
      _ = 60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 * Real.rpow r (-(κ + 5 * τ)) := h_final
    have h_main2 : max (C_count * (D_T : ℝ)^6 / (S_x.card : ℝ)) 1 ≤
        60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 * Real.rpow r (-(κ + 5 * τ)) := by
      exact max_le h_main' h_bound_ge1
    exact h_main2

  have hC_B_bound' : C_B * (D_T : ℝ) ≤ Real.rpow (2 * r) (-ε_F) := by
    have h1 : C_B ≤ max (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 *
        Real.rpow r (-(κ + 5 * τ))) 1 := by
      exact le_max_of_le_left hC_B_le
    have hDT_nonneg : 0 ≤ (D_T : ℝ) := by positivity
    have h2 : C_B * (D_T : ℝ) ≤ (max (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 *
        Real.rpow r (-(κ + 5 * τ))) 1) * (D_T : ℝ) := by
      gcongr
      <;> exact hDT_nonneg
    exact le_trans h2 hC_B_bound

  have hS_mem_and_2r : ∀ (L : Line2), L ∈ S_x →
      L ∈ (tubeFamily r : Set Line2) ∧ x ∈ tube (2 * r) L := by
    intro L hL
    exact ⟨hS_sub hL, hS_2r L hL⟩
  have hA_all : ∀ (L : Line2), L ∈ S_x →
      MeasurableSet (A_x L) ∧ A_x L ⊆ tube (2 * r) L ∧
        ν₂ (A_x L) ≥ ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) ∧
        (∀ (z : Point), ν₂ (A_x L ∩ Metric.ball z (Real.rpow r κ)) ≤ ν₂ (A_x L) / 3) := by
    intro L hL
    exact ⟨hA_meas L hL, hA_sub2r L hL, hA_mass L hL, hA_nonconc L hL⟩

  exact ⟨S_x, A_x, C_B, hC_B_nonneg, hS_nonempty',
    hS_mem_and_2r, h_isDelta, hC_B_bound', hA_all⟩

end B1
end RadialBootstrapping
