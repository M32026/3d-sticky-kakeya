module

/-
  A7 physical energy extraction.

  Uses the GEOMETRIC energy bound from DirectGeometricEnergy:
    E ≤ C_int · log · 4^t · C_Qset · |Qset|^2
  where C_int = packing · C_T · (800k)^s · M · Δ^s.

  Dividing by I ≳ Δ^{-(s+t)+73ε} gives:
    E/I ≲ Δ^{-(t-s)-300ε} = Δ^{-u-300ε}

  Whiteprint node: appendix_a_alternative / a7_physical_extraction
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A6_A7
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A4_CQpiSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.DirectGeometricEnergy
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeEnergyExtraction
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MainAppendix
open DirecretisedFurstenbergEstimate.Lagoon (squareCenter)
open DirecretisedFurstenbergEstimate.AppendixA4

namespace DirecretisedFurstenbergEstimate.AppendixA

noncomputable section

/-! ========================================================================
   Distance conversion: physical vs index
   ======================================================================== -/

/-- squareCenter is injective. -/
lemma squareCenter_injective' {Δ : ℝ} (hΔ_pos : 0 < Δ) :
    Function.Injective (squareCenter Δ) := by
  intro Q1 Q2 h
  have h1 : (squareCenter Δ Q1) 0 = (squareCenter Δ Q2) 0 := by rw [h]
  have h2 : (squareCenter Δ Q1) 1 = (squareCenter Δ Q2) 1 := by rw [h]
  have hQ1 : Q1.1 = Q2.1 := by
    simpa [Lagoon.squareCenter_zero, hΔ_pos.ne'] using h1
  have hQ2 : Q1.2 = Q2.2 := by
    simpa [Lagoon.squareCenter_one, hΔ_pos.ne'] using h2
  exact Prod.ext hQ1 hQ2

/-- Physical distance between square centers is at least Δ times index distance. -/
lemma squareCenter_dist_lower {Δ : ℝ} (hΔ_pos : 0 < Δ)
    (Q1 Q2 : CoarseSquare Δ) :
    Δ * dist Q1 Q2 ≤ dist (squareCenter Δ Q1) (squareCenter Δ Q2) := by
  let a : ℝ := |(Q1.1 : ℝ) - (Q2.1 : ℝ)|
  let b : ℝ := |(Q1.2 : ℝ) - (Q2.2 : ℝ)|
  have h_idx : dist Q1 Q2 = max a b := by
    simp [dist, a, b] <;> rfl
  let x := squareCenter Δ Q1 - squareCenter Δ Q2
  have h_norm2 : ‖x‖ = Real.sqrt (|x 0|^2 + |x 1|^2) := by
    rw [PiLp.norm_eq_of_L2]
    <;> simp [Fin.sum_univ_two]
    <;> rfl
  have h_coord0 : |x 0| ≤ ‖x‖ := by
    rw [h_norm2]
    have h_nonneg : 0 ≤ |x 1|^2 := by positivity
    have h : |x 0|^2 ≤ |x 0|^2 + |x 1|^2 := by linarith
    have h' : 0 ≤ |x 0| := by positivity
    exact Real.le_sqrt_of_sq_le h
  have h_coord1 : |x 1| ≤ ‖x‖ := by
    rw [h_norm2]
    have h_nonneg : 0 ≤ |x 0|^2 := by positivity
    have h : |x 1|^2 ≤ |x 0|^2 + |x 1|^2 := by linarith
    have h' : 0 ≤ |x 1| := by positivity
    exact Real.le_sqrt_of_sq_le h
  have h_dist : dist (squareCenter Δ Q1) (squareCenter Δ Q2) = ‖x‖ := by
    simp [x, dist_eq_norm]
  have h4 : |x 0| = Δ * a := by
    have h5 : x 0 = Δ * ((Q1.1 : ℝ) - (Q2.1 : ℝ)) := by
      simp [x, Lagoon.squareCenter_zero] <;> ring
    rw [h5, abs_mul, abs_of_pos hΔ_pos] <;> rfl
  have h5 : |x 1| = Δ * b := by
    have h6 : x 1 = Δ * ((Q1.2 : ℝ) - (Q2.2 : ℝ)) := by
      simp [x, Lagoon.squareCenter_one] <;> ring
    rw [h6, abs_mul, abs_of_pos hΔ_pos] <;> rfl
  rw [h_idx, h_dist]
  rw [h4] at h_coord0
  rw [h5] at h_coord1
  cases' le_total a b with h7 h7
  · rw [max_eq_right h7]; exact h_coord1
  · rw [max_eq_left h7]; exact h_coord0

/-! ========================================================================
   Physical energy ≤ Δ^{-u} * index energy
   ======================================================================== -/

/-- For any finset of coarse squares, physical pair energy ≤ Δ^{-u} · index pair energy. -/
lemma physical_pairEnergy_le_index {Δ u : ℝ} (hΔ_pos : 0 < Δ) (hu_pos : 0 < u)
    (F : Finset (CoarseSquare Δ)) :
    pairEnergy u (F.image (squareCenter Δ)) ≤
    Real.rpow Δ (-u) * pairEnergy u F := by
  let f := squareCenter Δ
  have h_inj' : Function.Injective f := squareCenter_injective' hΔ_pos
  have h_injOn : Set.InjOn f (F : Set (CoarseSquare Δ)) :=
    fun x _ y _ h => h_inj' h
  have h_pair : ∀ (x y : CoarseSquare Δ), x ≠ y →
      Real.rpow (dist (f x) (f y)) (-u) ≤
      Real.rpow Δ (-u) * Real.rpow (dist x y) (-u) := by
    intro x y _
    set d := dist x y with hd_def
    set d_phys := dist (f x) (f y) with hphys_def
    have h_posd : 0 < d := by apply dist_pos.mpr; tauto
    have h_pos2 : 0 < Δ * d := mul_pos hΔ_pos h_posd
    have h1 : Δ * d ≤ d_phys := squareCenter_dist_lower hΔ_pos x y
    have h_pos_phys : 0 ≤ d_phys := by positivity
    have h_pos_a : 0 < Δ * d := h_pos2
    have h_pos_b : 0 ≤ d_phys := by positivity
    have h3 : Real.rpow (Δ * d) u ≤ Real.rpow d_phys u :=
      Real.rpow_le_rpow (by linarith) h1 (by linarith)
    have h4 : 0 < Real.rpow (Δ * d) u := Real.rpow_pos_of_pos h_pos_a u
    have h5 : 0 < Real.rpow d_phys u := Real.rpow_pos_of_pos (lt_of_lt_of_le h_pos_a h1) u
    have h6 : (Real.rpow d_phys u)⁻¹ ≤ (Real.rpow (Δ * d) u)⁻¹ := by gcongr
    have h7 : Real.rpow d_phys (-u) = (Real.rpow d_phys u)⁻¹ := Real.rpow_neg h_pos_b u
    have h8 : Real.rpow (Δ * d) (-u) = (Real.rpow (Δ * d) u)⁻¹ := Real.rpow_neg (by linarith) u
    have h9 : Real.rpow (Δ * d) (-u) = Real.rpow Δ (-u) * Real.rpow d (-u) := by
      have h10 : 0 ≤ Δ := by linarith
      have h11 : 0 ≤ d := by positivity
      exact Real.mul_rpow h10 h11
    calc Real.rpow d_phys (-u)
      = (Real.rpow d_phys u)⁻¹ := h7
    _ ≤ (Real.rpow (Δ * d) u)⁻¹ := h6
    _ = Real.rpow (Δ * d) (-u) := h8.symm
    _ = Real.rpow Δ (-u) * Real.rpow d (-u) := h9
  have h_erase : ∀ (x : CoarseSquare Δ), x ∈ F →
      (F.image f).erase (f x) = (F.erase x).image f := by
    intro x hx
    ext y
    simp only [Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro ⟨hne, ⟨z, hz, rfl⟩⟩
      have hzne : z ≠ x := by intro h; rw [h] at hne; simp at hne
      exact ⟨z, ⟨hzne, hz⟩, rfl⟩
    · rintro ⟨z, ⟨hne, hz⟩, rfl⟩
      have h' : f z ≠ f x := by intro h; apply hne; exact h_inj' h
      exact ⟨h', z, hz, rfl⟩
  have h_step1 : pairEnergy u (F.image f) =
      ∑ x ∈ F, pointEnergy u (F.image f) (f x) := by
    have h_expand : pairEnergy u (F.image f) = ∑ c ∈ F.image f, pointEnergy u (F.image f) c := by rfl
    rw [h_expand]
    exact Finset.sum_image h_injOn
  have h_step2 : ∀ x ∈ F, pointEnergy u (F.image f) (f x) =
      ∑ y ∈ F.erase x, Real.rpow (dist (f x) (f y)) (-u) := by
    intro x hx
    have h_e : (F.image f).erase (f x) = (F.erase x).image f := h_erase x hx
    simp [pointEnergy, h_e]
    <;> rw [Finset.sum_image (show Set.InjOn f (F.erase x : Set (CoarseSquare Δ)) from
        fun a _ b _ h => h_inj' h)]
  have h_main : ∑ x ∈ F, ∑ y ∈ F.erase x, Real.rpow (dist (f x) (f y)) (-u) ≤
      ∑ x ∈ F, ∑ y ∈ F.erase x, (Real.rpow Δ (-u) * Real.rpow (dist x y) (-u)) := by
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro y hy
    have hne : x ≠ y := by simp only [Finset.mem_erase] at hy; tauto
    exact h_pair x y hne
  have h_final : ∑ x ∈ F, ∑ y ∈ F.erase x, (Real.rpow Δ (-u) * Real.rpow (dist x y) (-u)) =
      Real.rpow Δ (-u) * pairEnergy u F := by
    have h9 : ∀ x ∈ F, ∑ y ∈ F.erase x, (Real.rpow Δ (-u) * Real.rpow (dist x y) (-u)) =
        Real.rpow Δ (-u) * ∑ y ∈ F.erase x, Real.rpow (dist x y) (-u) := by
      intro x _
      rw [Finset.mul_sum]
    calc
      ∑ x ∈ F, ∑ y ∈ F.erase x, (Real.rpow Δ (-u) * Real.rpow (dist x y) (-u))
        = ∑ x ∈ F, (Real.rpow Δ (-u) * ∑ y ∈ F.erase x, Real.rpow (dist x y) (-u)) := by
          apply Finset.sum_congr rfl; intro x hx; exact h9 x hx
      _ = Real.rpow Δ (-u) * ∑ x ∈ F, ∑ y ∈ F.erase x, Real.rpow (dist x y) (-u) := by
          rw [Finset.mul_sum]
      _ = Real.rpow Δ (-u) * pairEnergy u F := by rfl
  calc
    pairEnergy u (F.image f)
      = ∑ x ∈ F, pointEnergy u (F.image f) (f x) := h_step1
    _ = ∑ x ∈ F, ∑ y ∈ F.erase x, Real.rpow (dist (f x) (f y)) (-u) := by
      apply Finset.sum_congr rfl; intro x hx; exact h_step2 x hx
    _ ≤ ∑ x ∈ F, ∑ y ∈ F.erase x, (Real.rpow Δ (-u) * Real.rpow (dist x y) (-u)) := h_main
    _ = Real.rpow Δ (-u) * pairEnergy u F := h_final

/-! ========================================================================
   Geometric energy bound (OS lines 1488-1504)

   Bounds E_phys directly using the (Δ,s)-S-set property of C_Q_pi families
   and the t-dimensional ball growth of Qset centers.

   E ≤ C_int · log · 4^t · C_Qset · |Qset|^2
   E/I ≤ Δ^{-u-300ε}
   ======================================================================== -/

/-- Geometric physical total energy bound: E_phys ≤ 16·Δ^{-u-300ε}·I.

    Uses direct_geometric_energy_data with A5 bridge data.
    Density transfer: C_pi Q = C_Q_pi ∩ C_global inherits S-set with constant
      affineLine_packing_constant · Δ^{-52ε} · Δ^{-59ε} = affineLine_packing_constant · Δ^{-111ε}.
    C_int = packing^2 · (800·53)^s · Δ^{-140ε}.
    E ≤ C_int · log · 4^t · C_Qset · |Qset|² ≤ Δ^{-2t-226ε}.
    E/I ≤ Δ^{-u-299ε} ≤ 16·Δ^{-u-300ε}. -/
lemma physical_energy_bound
    {Δ δ s t ε : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2) (hε_pos : 0 < ε)
    (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (a5 : A5_Output Δ δ s t ε)
    (hQset_bdd : ∀ p ∈ a5.Qset.image (squareCenter Δ), ‖p‖ ≤ 2)
    (hQset_le_3 : ∀ (p1 : Plane) (hp1 : p1 ∈ a5.Qset.image (squareCenter Δ))
      (p2 : Plane) (hp2 : p2 ∈ a5.Qset.image (squareCenter Δ)), dist p1 p2 ≤ 3)
    (h_log_absorb : 4 * Real.log (3 / Δ) + 1 ≤ Real.rpow Δ (-3 * ε))
    (h_pack_absorb : (affineLine_packing_constant : ℝ) ≤ Real.rpow Δ (-ε))
    (h_const_absorb : (affineLine_packing_constant : ℝ)^2 * ((800 * (53 : ℝ)) : ℝ)^s * (4 : ℝ)^t + 1 ≤ Real.rpow Δ (-ε))
    (I : ℝ)
    (hI_def : I = ∑ Q ∈ a5.Qset, (a5Cpi a5 Q).card) :
    let u := t - s
    let E_phys := ∑ T ∈ a5.C_global, pairEnergy u ((a5Fiber a5 T).image (squareCenter Δ))
    E_phys ≤ 4 * Real.rpow Δ (-(t - s) - 300 * ε) * I := by
  let u := t - s
  have hu_pos : 0 < u := by linarith
  let C_pi : CoarseSquare Δ → Finset CoarseTube := fun Q => a5Cpi a5 Q
  let K_density : ℝ := (affineLine_packing_constant : ℝ) * Real.rpow Δ (-52 * ε)
  let C_T : ℝ := K_density * Real.rpow Δ (-59 * ε)
  let M : ℝ := Real.rpow Δ (-s - 29 * ε)
  let k : ℝ := 53
  let C_Qset : ℝ := Real.rpow Δ (-80 * ε)
  let C_int : ℝ := (affineLine_packing_constant : ℝ) * C_T * ((800 * k) : ℝ)^s * M * Real.rpow Δ s

  have hC_T_pos : 0 < C_T := by
    dsimp only [C_T, K_density]
    have h_pack_pos' : 0 < (affineLine_packing_constant : ℝ) := by
      exact_mod_cast affineLine_packing_constant_pos
    have h1 : 0 < Real.rpow Δ (-52 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h2 : 0 < Real.rpow Δ (-59 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    positivity
  have hM_pos : 0 < M := Real.rpow_pos_of_pos hΔ_pos _
  have hk : 1 ≤ k := by norm_num
  have hC_Qset_pos : 0 < C_Qset := Real.rpow_pos_of_pos hΔ_pos _

  -- Helper: C_pi Q = C_Q_pi ∩ C_global and subset relations
  have hC_pi_eq : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a5.Qset), C_pi Q = (a5.perSquare Q hQ).C_Q_pi ∩ a5.C_global := by
    intro Q hQ
    dsimp only [C_pi, a5Cpi]
    rw [dif_pos hQ]
  have hC_pi_sub_CQpi : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a5.Qset), (C_pi Q : Set CoarseTube) ⊆
      ((a5.perSquare Q hQ).C_Q_pi : Set CoarseTube) := by
    intro Q hQ
    rw [hC_pi_eq Q hQ]
    simpa [Finset.coe_inter] using Set.inter_subset_left _ _
  have hC_pi_sub_CQ : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a5.Qset), (C_pi Q : Set CoarseTube) ⊆
      ((a5.perSquare Q hQ).base.C_Q : Set CoarseTube) := by
    intro Q hQ
    rw [hC_pi_eq Q hQ]
    have h2 : ((a5.perSquare Q hQ).C_Q_pi : Set CoarseTube) ⊆
        ((a5.perSquare Q hQ).base.C_Q : Set CoarseTube) :=
      (a5.perSquare Q hQ).hC_Q_pi_sub
    have h3 : (((a5.perSquare Q hQ).C_Q_pi ∩ a5.C_global : Finset CoarseTube) : Set CoarseTube) ⊆
        ((a5.perSquare Q hQ).C_Q_pi : Set CoarseTube) := by
      simpa [Finset.coe_inter] using Set.inter_subset_left _ _
    exact Set.Subset.trans h3 h2

  -- Bridge: separation for C_pi
  have hC_pi_sep : ∀ Q ∈ a5.Qset, SeparatedAt Δ (C_pi Q : Set CoarseTube) := by
    intro Q hQ
    have h_sep : SeparatedAt Δ ((a5.perSquare Q hQ).base.C_Q : Set CoarseTube) :=
      (a5.perSquare Q hQ).base.hC_Q_separated
    exact Set.Pairwise.mono (hC_pi_sub_CQ Q hQ) h_sep

  -- Bridge: card bound for C_pi
  have hC_pi_card : ∀ Q ∈ a5.Qset, (C_pi Q).card ≤ M := by
    intro Q hQ
    have h2 : (C_pi Q).card ≤ (a5.perSquare Q hQ).base.C_Q.card :=
      Finset.card_le_card (hC_pi_sub_CQ Q hQ)
    have h3 : ((a5.perSquare Q hQ).base.C_Q.card : ℝ) ≤ M :=
      (a5.perSquare Q hQ).hC_card_upper
    have h4 : ((C_pi Q).card : ℝ) ≤ ((a5.perSquare Q hQ).base.C_Q.card : ℝ) := by exact_mod_cast h2
    exact_mod_cast le_trans h4 h3

  -- Bridge: nonempty for C_pi
  have hC_pi_nonempty : ∀ Q ∈ a5.Qset, (C_pi Q).Nonempty := by
    intro Q hQ
    have h3 : Real.rpow Δ (-s + 23 * ε) ≤ ((C_pi Q).card : ℝ) := by
      rw [hC_pi_eq Q hQ]
      exact a5.hG3_intersection Q hQ
    have h4 : 0 < Real.rpow Δ (-s + 23 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h5 : 0 < (C_pi Q).card := by exact_mod_cast lt_of_lt_of_le h4 h3
    exact Finset.card_pos.mp h5

  -- Bridge: density-transfer S-set for C_pi (Correction 1)
  -- C_pi Q ⊆ C_Q_pi, with density ≥ Δ^{-48ε}.
  -- Covering ratio ≤ affineLine_packing_constant · Δ^{-48ε}.
  have hC_pi_sset : ∀ Q ∈ a5.Qset, IsDeltaSSet Δ s C_T (C_pi Q : Set CoarseTube) := by
    intro Q hQ
    let S : Set CoarseTube := (a5.perSquare Q hQ).C_Q_pi
    let S' : Set CoarseTube := (C_pi Q : Set CoarseTube)
    have hS'_sub : S' ⊆ S := hC_pi_sub_CQpi Q hQ
    have hS_sset : IsDeltaSSet Δ s (Real.rpow Δ (-59 * ε)) S :=
      (a5.perSquare Q hQ).hC_Q_pi_sset
    have h_card_CQ_upper : ((a5.perSquare Q hQ).base.C_Q.card : ℝ) ≤ Real.rpow Δ (-s - 29 * ε) :=
      (a5.perSquare Q hQ).hC_card_upper
    have h_card_S'_lower : Real.rpow Δ (-s + 23 * ε) ≤ ((C_pi Q).card : ℝ) := by
      have h_eq : C_pi Q = (a5.perSquare Q hQ).C_Q_pi ∩ a5.C_global := hC_pi_eq Q hQ
      rw [h_eq]
      exact a5.hG3_intersection Q hQ
    have hS_fin : S.Finite := Finset.finite_toSet _
    have hS'_fin : S'.Finite := Finset.finite_toSet _
    -- covering(S) ≤ |S| ≤ |C_Q| ≤ Δ^{-s-29ε}
    have h_cov_S : (Metric.externalCoveringNumber Δ.toNNReal S : ENNReal) ≤
        ENNReal.ofReal (Real.rpow Δ (-s - 29 * ε)) := by
      have h1 : Metric.externalCoveringNumber Δ.toNNReal S ≤ S.encard :=
        Metric.externalCoveringNumber_le_encard_self S
      have h1b : (S.encard : ENNReal) ≤ ((a5.perSquare Q hQ).base.C_Q.card : ENNReal) := by
        have hS_eq : S = ((a5.perSquare Q hQ).C_Q_pi : Set CoarseTube) := by rfl
        rw [hS_eq]
        have h2 : ((a5.perSquare Q hQ).C_Q_pi : Set CoarseTube).encard =
            ((a5.perSquare Q hQ).C_Q_pi.card : ENat) := by simp
        rw [h2]
        have h3 : (a5.perSquare Q hQ).C_Q_pi.card ≤ (a5.perSquare Q hQ).base.C_Q.card :=
          Finset.card_le_card (a5.perSquare Q hQ).hC_Q_pi_sub
        exact_mod_cast h3
      have h4 : ((a5.perSquare Q hQ).base.C_Q.card : ENNReal) ≤
          ENNReal.ofReal (Real.rpow Δ (-s - 29 * ε)) := by
        have h41 : ((a5.perSquare Q hQ).base.C_Q.card : ENNReal) =
            ENNReal.ofReal ((a5.perSquare Q hQ).base.C_Q.card : ℝ) := by simp
        rw [h41]
        gcongr
      exact le_trans (le_trans (by exact_mod_cast h1) h1b) h4
    -- |S'| ≤ packing_constant · covering(S')
    have h_sep'_nn : Set.Pairwise S' (fun x y => (↑Δ.toNNReal : ℝ) ≤ dist x y) := by
      have h_eq : (↑Δ.toNNReal : ℝ) = Δ := by
        simp [NNReal.coe_mk, hΔ_pos.le]
      rw [h_eq]
      exact hC_pi_sep Q hQ
    have hcov' : (Metric.externalCoveringNumber Δ.toNNReal S' : ENNReal) < ⊤ := by
      have h1 : Metric.externalCoveringNumber Δ.toNNReal S' ≤ S'.encard :=
        Metric.externalCoveringNumber_le_encard_self S'
      have h2 : S'.encard < ⊤ := Set.Finite.encard_lt_top hS'_fin
      exact_mod_cast lt_of_le_of_lt h1 h2
    have h_pack_arg : ∀ (z : CoarseTube) (T : Set CoarseTube),
        Set.Pairwise T (fun x y => (↑Δ.toNNReal : ℝ) ≤ dist x y) →
        T ⊆ Metric.closedBall z (2 * (↑Δ.toNNReal : ℝ)) →
        T.Finite ∧ T.encard ≤ (affineLine_packing_constant : ENat) := by
      intro z T hT_sep hT_sub
      have h_eq : (↑Δ.toNNReal : ℝ) = Δ := by simp [NNReal.coe_mk, hΔ_pos.le]
      have hT_sep' : Set.Pairwise T (fun x y => Δ ≤ dist x y) := by
        rw [h_eq] at hT_sep; exact hT_sep
      have hT_sub' : T ⊆ Metric.closedBall z (2 * Δ) := by
        rw [h_eq] at hT_sub; exact hT_sub
      exact affineLine_packing_bound Δ hΔ_pos hT_sep' z hT_sub'
    have h_card_cover : (S'.encard : ENNReal) ≤
        (affineLine_packing_constant : ENNReal) * Metric.externalCoveringNumber Δ.toNNReal S' :=
      separated_set_card_le_covering h_sep'_nn affineLine_packing_constant h_pack_arg hcov'
    let K : ℝ := (affineLine_packing_constant : ℝ) * Real.rpow Δ (-52 * ε)
    have h_pack_pos : 0 < (affineLine_packing_constant : ℝ) := by
      exact_mod_cast affineLine_packing_constant_pos
    have hK_pos : 0 < K := mul_pos h_pack_pos (Real.rpow_pos_of_pos hΔ_pos _)
    have h_S'_card_ennreal : (S'.encard : ENNReal) = ((C_pi Q).card : ENNReal) := by
      have h : S' = (C_pi Q : Set CoarseTube) := by rfl
      rw [h]; simp
    have h_lower_ennreal : ENNReal.ofReal (Real.rpow Δ (-s + 23 * ε)) ≤ (S'.encard : ENNReal) := by
      rw [h_S'_card_ennreal]
      exact_mod_cast h_card_S'_lower
    have h_pack_ennreal_eq : (affineLine_packing_constant : ENNReal) =
        ENNReal.ofReal ((affineLine_packing_constant : ℝ)) := by simp
    -- K · covering(S') ≥ Δ^{-52ε} · |S'| ≥ Δ^{-52ε} · Δ^{-s+23ε} = Δ^{-s-29ε}
    have h5 : ENNReal.ofReal (Real.rpow Δ (-52 * ε)) * (S'.encard : ENNReal) ≤
        ENNReal.ofReal (Real.rpow Δ (-52 * ε)) *
          ((affineLine_packing_constant : ENNReal) * Metric.externalCoveringNumber Δ.toNNReal S') :=
      mul_le_mul_of_nonneg_left h_card_cover (show 0 ≤ ENNReal.ofReal (Real.rpow Δ (-52 * ε)) from bot_le)
    have h6 : ENNReal.ofReal (Real.rpow Δ (-52 * ε)) *
          ((affineLine_packing_constant : ENNReal) * Metric.externalCoveringNumber Δ.toNNReal S') =
        ENNReal.ofReal K * Metric.externalCoveringNumber Δ.toNNReal S' := by
      rw [h_pack_ennreal_eq]
      have h_mul : ENNReal.ofReal (Real.rpow Δ (-52 * ε)) *
            (ENNReal.ofReal ((affineLine_packing_constant : ℝ)) * Metric.externalCoveringNumber Δ.toNNReal S') =
          (ENNReal.ofReal ((affineLine_packing_constant : ℝ)) * ENNReal.ofReal (Real.rpow Δ (-52 * ε))) *
            Metric.externalCoveringNumber Δ.toNNReal S' := by ring
      rw [h_mul]
      have h_ofReal_mul : ENNReal.ofReal ((affineLine_packing_constant : ℝ)) * ENNReal.ofReal (Real.rpow Δ (-52 * ε)) =
          ENNReal.ofReal K := by
        rw [← ENNReal.ofReal_mul h_pack_pos.le]
        <;> congr <;> rfl
      rw [h_ofReal_mul]
    have h71 : ENNReal.ofReal (Real.rpow Δ (-52 * ε)) * ENNReal.ofReal (Real.rpow Δ (-s + 23 * ε)) ≤
        ENNReal.ofReal (Real.rpow Δ (-52 * ε)) * (S'.encard : ENNReal) :=
      mul_le_mul_of_nonneg_left h_lower_ennreal (show 0 ≤ ENNReal.ofReal (Real.rpow Δ (-52 * ε)) from bot_le)
    have h72 : ENNReal.ofReal (Real.rpow Δ (-52 * ε)) * (S'.encard : ENNReal) ≤
        ENNReal.ofReal K * Metric.externalCoveringNumber Δ.toNNReal S' := by
      calc ENNReal.ofReal (Real.rpow Δ (-52 * ε)) * (S'.encard : ENNReal)
        ≤ ENNReal.ofReal (Real.rpow Δ (-52 * ε)) *
            ((affineLine_packing_constant : ENNReal) * Metric.externalCoveringNumber Δ.toNNReal S') := h5
      _ = ENNReal.ofReal K * Metric.externalCoveringNumber Δ.toNNReal S' := h6
    have h7 : ENNReal.ofReal (Real.rpow Δ (-52 * ε)) * ENNReal.ofReal (Real.rpow Δ (-s + 23 * ε)) ≤
        ENNReal.ofReal K * Metric.externalCoveringNumber Δ.toNNReal S' :=
      le_trans h71 h72
    have h8 : ENNReal.ofReal (Real.rpow Δ (-52 * ε)) * ENNReal.ofReal (Real.rpow Δ (-s + 23 * ε)) =
        ENNReal.ofReal (Real.rpow Δ (-s - 29 * ε)) := by
      have h9 : Real.rpow Δ (-52 * ε) * Real.rpow Δ (-s + 23 * ε) =
          Real.rpow Δ (-s - 29 * ε) := by
        rw [← rpow_add_eq hΔ_pos] <;> ring_nf
      have h_nonneg2 : 0 ≤ Real.rpow Δ (-52 * ε) := Real.rpow_nonneg hΔ_pos.le _
      have h10 : ENNReal.ofReal (Real.rpow Δ (-52 * ε)) * ENNReal.ofReal (Real.rpow Δ (-s + 23 * ε)) =
          ENNReal.ofReal (Real.rpow Δ (-52 * ε) * Real.rpow Δ (-s + 23 * ε)) := by
        rw [← ENNReal.ofReal_mul h_nonneg2]
      rw [h10, h9]
    have h_ratio : (Metric.externalCoveringNumber Δ.toNNReal S : ENNReal) ≤
        ENNReal.ofReal K * Metric.externalCoveringNumber Δ.toNNReal S' := by
      rw [h8] at h7
      exact le_trans h_cov_S h7
    have hC_T_eq : C_T = K * Real.rpow Δ (-59 * ε) := by
      dsimp only [C_T, K_density, K] <;> ring
    rw [hC_T_eq]
    exact IsDeltaSSet.subset_with_cover_ratio hK_pos hS_sset hS'_sub h_ratio

  -- Bridge: nearness for C_pi (k=53)
  have hC_pi_near : ∀ Q ∈ a5.Qset, ∀ T ∈ C_pi Q,
      squareCenter Δ Q ∈ Metric.cthickening (k * Δ) (T.1 : Set EuclideanPlane) := by
    intro Q hQ T hT
    have hT_in_CQ : T ∈ (a5.perSquare Q hQ).base.C_Q :=
      hC_pi_sub_CQ Q hQ hT
    exact AppendixA3.coarse_tube_near_square_center
      (a5.perSquare Q hQ).base hΔ_pos hδ_pos hδ_le_Δ (by linarith) T hT_in_CQ

  -- Bridge: Qset ball growth in image form
  have hQset_ball : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((a5.Qset.image (squareCenter Δ)).filter (fun y => dist y c ≤ r)).card ≤
        C_Qset * r^t * (a5.Qset.image (squareCenter Δ)).card := by
    intro c r hr
    have h_inj : Function.Injective (squareCenter Δ) := squareCenter_injective' hΔ_pos
    have h_filter_eq : (a5.Qset.image (squareCenter Δ)).filter (fun y => dist y c ≤ r) =
        (a5.Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).image (squareCenter Δ) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨h_image, h_dist⟩
        rcases h_image with ⟨Q, hQ, rfl⟩
        exact ⟨Q, ⟨hQ, h_dist⟩, rfl⟩
      · rintro ⟨Q, ⟨hQ, h_dist⟩, rfl⟩
        exact ⟨⟨Q, hQ, rfl⟩, h_dist⟩
    rw [h_filter_eq]
    have h_card : ((a5.Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).image (squareCenter Δ)).card =
        (a5.Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card :=
      Finset.card_image_of_injective _ h_inj
    rw [h_card]
    have h_growth := a5.hQset_phys_growth c r hr
    have h_card2 : (a5.Qset.image (squareCenter Δ)).card = a5.Qset.card :=
      Finset.card_image_of_injective _ h_inj
    rw [h_card2] at *
    <;> exact h_growth

  have hQset_nonempty : a5.Qset.Nonempty := a5.hQset_sset.1

  -- Call direct geometric energy bound
  have h_data := direct_geometric_energy_data (δ := δ)
    hΔ_pos hΔ_lt_half hs hs1 hst ht2 hε_pos
    a5.Qset hQset_nonempty hQset_bdd hQset_le_3
    C_Qset hC_Qset_pos hQset_ball
    C_pi C_T M k hC_T_pos hM_pos hk
    hC_pi_sset hC_pi_sep hC_pi_card hC_pi_near hC_pi_nonempty
    C_int rfl

  rcases h_data with ⟨E, I', L, centers, C_global, fiber,
    hI_pos, hE_nonneg, hL_pos, hcenters_sep, hfiber, hcard,
    hincidence_eq, hcenters_eq, hCglobal_eq, hE_def, hfiber_eq_data, hE_bound⟩

  -- Qset.biUnion C_pi ⊆ a5.C_global (first direction only; reverse may fail)
  have h_sub1 : a5.Qset.biUnion C_pi ⊆ a5.C_global := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨Q, hQ, hTQ⟩
    have h2 : a5Cpi a5 Q ⊆ a5.C_global := by
      dsimp only [a5Cpi]; rw [dif_pos hQ]; simp
    exact h2 hTQ

  -- fiber T = (a5Fiber a5 T).image (squareCenter Δ) for all T
  have h_fiber_eq : ∀ T, fiber T = (a5Fiber a5 T).image (squareCenter Δ) := by
    intro T
    have h1 : fiber T = (a5.Qset.filter (fun Q => T ∈ C_pi Q)).image (squareCenter Δ) :=
      hfiber_eq_data T
    rw [h1]
    rfl

  -- For T ∉ Qset.biUnion C_pi, a5Fiber a5 T is empty
  have h_emp : ∀ T ∈ a5.C_global, T ∉ a5.Qset.biUnion C_pi → a5Fiber a5 T = ∅ := by
    intro T _ hT_not
    ext Q
    simp [a5Fiber]
    intro hQ1 hT_in
    exact hT_not (Finset.mem_biUnion.mpr ⟨Q, hQ1, hT_in⟩)

  -- Verify E matches E_phys: extend sum from data's C_global to a5.C_global
  have hE_eq : E = ∑ T ∈ a5.C_global, pairEnergy u ((a5Fiber a5 T).image (squareCenter Δ)) := by
    have h_sum1 : ∑ T ∈ a5.Qset.biUnion C_pi, pairEnergy u (fiber T) =
        ∑ T ∈ a5.Qset.biUnion C_pi, pairEnergy u ((a5Fiber a5 T).image (squareCenter Δ)) := by
      apply Finset.sum_congr rfl
      intro T _
      rw [h_fiber_eq T]
    have h_sum_ext : ∑ T ∈ a5.Qset.biUnion C_pi, pairEnergy u ((a5Fiber a5 T).image (squareCenter Δ)) =
        ∑ T ∈ a5.C_global, pairEnergy u ((a5Fiber a5 T).image (squareCenter Δ)) := by
      rw [Finset.sum_subset h_sub1]
      · intro T hT_global hT_not
        have h_empty : a5Fiber a5 T = ∅ := h_emp T hT_global hT_not
        rw [h_empty]
        have h_pe : pairEnergy u (∅ : Finset Plane) = 0 := by
          simp [pairEnergy]
        exact h_pe
    rw [hE_def, hCglobal_eq]
    rw [h_sum1, h_sum_ext]

  -- Verify I' = our I via double counting
  have h_fiber_card : ∀ T, (fiber T).card = (a5Fiber a5 T).card := by
    intro T
    rw [h_fiber_eq T]
    exact Finset.card_image_of_injective _ (squareCenter_injective' hΔ_pos)
  have hI_eq : I' = I := by
    have h1 : I' = ∑ T ∈ C_global, ((fiber T).card : ℝ) := hincidence_eq
    rw [h1]
    have h2 : ∑ T ∈ C_global, ((fiber T).card : ℝ) = ∑ T ∈ C_global, ((a5Fiber a5 T).card : ℝ) := by
      apply Finset.sum_congr rfl; intro T _; rw [h_fiber_card T]
    rw [h2, hCglobal_eq]
    have h3 : ∑ T ∈ a5.Qset.biUnion C_pi, ((a5Fiber a5 T).card : ℝ) =
        ∑ T ∈ a5.C_global, ((a5Fiber a5 T).card : ℝ) := by
      rw [Finset.sum_subset h_sub1]
      · intro T hT_global hT_not
        have h_empty : a5Fiber a5 T = ∅ := h_emp T hT_global hT_not
        rw [h_empty]
        simp
    rw [h3]
    have h4 : ∑ T ∈ a5.C_global, ((a5Fiber a5 T).card : ℝ) =
        ∑ Q ∈ a5.Qset, ((a5Cpi a5 Q).card : ℝ) := by
      exact_mod_cast (a5_double_counting a5).symm
    rw [h4]
    have hI_def' : (I : ℝ) = ∑ Q ∈ a5.Qset, ((a5Cpi a5 Q).card : ℝ) := by
      exact_mod_cast hI_def
    exact hI_def'.symm

  have hI_pos' : 0 < I := by
    rw [hI_eq] at hI_pos; exact hI_pos

  -- Corrected exponent calculation:
  -- C_T = packing · Δ^{-111ε} (density transfer)
  -- C_int = packing^2 · (800·53)^s · Δ^{-140ε}
  -- E ≤ C_int · log · 4^t · C_Qset · |Qset|²
  --   ≤ Δ^{-141ε} · Δ^{-3ε} · Δ^{-80ε} · Δ^{-2t-2ε}
  --   = Δ^{-2t-226ε}
  -- I ≥ Δ^{-(s+t)+73ε}
  -- E/I ≤ Δ^{-u-299ε} ≤ 16·Δ^{-u-300ε}

  set C_fixed : ℝ := (affineLine_packing_constant : ℝ)^2 * ((800 * k) : ℝ)^s * (4 : ℝ)^t + 1
    with hC_fixed_def
  have h_fixed_pos : 0 < C_fixed := by positivity
  have hC_fixed_le : C_fixed ≤ Real.rpow Δ (-ε) := h_const_absorb

  -- C_int * 4^t ≤ C_fixed * Δ^{-132ε}
  have hC_int4t : C_int * (4 : ℝ)^t ≤ C_fixed * Real.rpow Δ (-140 * ε) := by
    dsimp only [C_int, C_T, K_density, M]
    have h1 : Real.rpow Δ (-52 * ε) * Real.rpow Δ (-59 * ε) *
        Real.rpow Δ (-s - 29 * ε) * Real.rpow Δ s = Real.rpow Δ (-140 * ε) := by
      have h11 : Real.rpow Δ (-52 * ε) * Real.rpow Δ (-59 * ε) = Real.rpow Δ (-111 * ε) := by
        rw [← rpow_add_eq hΔ_pos] <;> ring_nf
      have h12 : Real.rpow Δ (-s - 29 * ε) * Real.rpow Δ s = Real.rpow Δ (-29 * ε) := by
        rw [← rpow_add_eq hΔ_pos] <;> ring_nf
      have h13 : Real.rpow Δ (-111 * ε) * Real.rpow Δ (-29 * ε) = Real.rpow Δ (-140 * ε) := by
        rw [← rpow_add_eq hΔ_pos] <;> ring_nf
      have h_assoc : Real.rpow Δ (-52 * ε) * Real.rpow Δ (-59 * ε) *
          Real.rpow Δ (-s - 29 * ε) * Real.rpow Δ s =
          (Real.rpow Δ (-52 * ε) * Real.rpow Δ (-59 * ε)) *
          (Real.rpow Δ (-s - 29 * ε) * Real.rpow Δ s) := by ring
      rw [h_assoc, h11, h12, h13]
    have h_expand : C_int * (4 : ℝ)^t =
        (affineLine_packing_constant : ℝ)^2 * ((800 * k) : ℝ)^s * (4 : ℝ)^t *
        Real.rpow Δ (-140 * ε) := by
      dsimp only [C_int, C_T, K_density, M]
      have h_rpow : Real.rpow Δ (-52 * ε) * Real.rpow Δ (-59 * ε) *
          Real.rpow Δ (-s - 29 * ε) * Real.rpow Δ s = Real.rpow Δ (-140 * ε) := h1
      have h_rearr : (affineLine_packing_constant : ℝ) *
          ((affineLine_packing_constant : ℝ) * Real.rpow Δ (-52 * ε) * Real.rpow Δ (-59 * ε)) *
          ((800 * k) : ℝ)^s * Real.rpow Δ (-s - 29 * ε) * Real.rpow Δ s * (4 : ℝ)^t =
          (affineLine_packing_constant : ℝ)^2 * ((800 * k) : ℝ)^s * (4 : ℝ)^t *
          (Real.rpow Δ (-52 * ε) * Real.rpow Δ (-59 * ε) *
            Real.rpow Δ (-s - 29 * ε) * Real.rpow Δ s) := by ring
      rw [h_rearr, h_rpow] <;> ring
    rw [h_expand]
    have h2 : (affineLine_packing_constant : ℝ)^2 * ((800 * k) : ℝ)^s * (4 : ℝ)^t ≤ C_fixed := by
      simp [hC_fixed_def] <;> linarith
    gcongr <;> exact Real.rpow_nonneg hΔ_pos.le _

  have hQset_upper : (a5.Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε) := a5.hQset_card_upper

  have hI_lower : I ≥ Real.rpow Δ (-(s + t) + 73 * ε) := by
    have h1 : ∀ Q ∈ a5.Qset, (a5Cpi a5 Q).card ≥ Real.rpow Δ (-s + 23 * ε) := by
      intro Q hQ
      have h_eq : a5Cpi a5 Q = (a5.perSquare Q hQ).C_Q_pi ∩ a5.C_global := by
        dsimp only [a5Cpi]
        rw [dif_pos hQ]
      have h2 : Real.rpow Δ (-s + 23 * ε) ≤ ((a5Cpi a5 Q).card : ℝ) := by
        rw [h_eq]
        exact a5.hG3_intersection Q hQ
      exact_mod_cast h2
    have h_sum : I ≥ (a5.Qset.card : ℝ) * Real.rpow Δ (-s + 23 * ε) := by
      rw [hI_def]
      have h_cast : (↑(∑ Q ∈ a5.Qset, (a5Cpi a5 Q).card) : ℝ) =
          ∑ Q ∈ a5.Qset, ((a5Cpi a5 Q).card : ℝ) := by
        rw [Nat.cast_sum]
      rw [h_cast]
      have h : ∑ Q ∈ a5.Qset, ((a5Cpi a5 Q).card : ℝ) ≥
          ∑ Q ∈ a5.Qset, (Real.rpow Δ (-s + 23 * ε) : ℝ) := by
        apply Finset.sum_le_sum
        intro Q hQ
        exact h1 Q hQ
      have h2 : ∑ Q ∈ a5.Qset, (Real.rpow Δ (-s + 23 * ε) : ℝ) =
          (a5.Qset.card : ℝ) * Real.rpow Δ (-s + 23 * ε) := by
        simp [Finset.sum_const] <;> ring
      rw [h2] at h
      exact h
    have hQ_lower : (a5.Qset.card : ℝ) ≥ Real.rpow Δ (-t + 50 * ε) := a5.hQset_card_lower
    have h3 : (a5.Qset.card : ℝ) * Real.rpow Δ (-s + 23 * ε) ≥
        Real.rpow Δ (-t + 50 * ε) * Real.rpow Δ (-s + 23 * ε) := by
      gcongr <;> exact Real.rpow_nonneg hΔ_pos.le _
    have h4 : Real.rpow Δ (-t + 50 * ε) * Real.rpow Δ (-s + 23 * ε) =
        Real.rpow Δ (-(s + t) + 73 * ε) := by
      rw [← rpow_add_eq hΔ_pos] <;> ring_nf
    calc I
      ≥ (a5.Qset.card : ℝ) * Real.rpow Δ (-s + 23 * ε) := h_sum
    _ ≥ Real.rpow Δ (-t + 50 * ε) * Real.rpow Δ (-s + 23 * ε) := h3
    _ = Real.rpow Δ (-(s + t) + 73 * ε) := h4

  -- E ≤ Δ^{-2t-226ε}
  have hE_pre : E ≤ Real.rpow Δ (-2 * t - 226 * ε) := by
    have h_mult : C_int * (4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t ≤
        (C_fixed * Real.rpow Δ (-140 * ε)) * Real.rpow Δ (-3 * ε) := by
      have h_a : C_int * (4 : ℝ)^t ≤ C_fixed * Real.rpow Δ (-140 * ε) := hC_int4t
      have h_b : 0 ≤ 4 * Real.log (3 / Δ) + 1 := by
        have h_pos1 : 1 < (3 : ℝ) / Δ := by
          have h' : 0 < Δ := hΔ_pos
          have h'' : Δ < 3 := by linarith
          exact (one_lt_div h').mpr h''
        have h_log_pos : 0 < Real.log (3 / Δ) := Real.log_pos h_pos1
        linarith
      have h_c : 4 * Real.log (3 / Δ) + 1 ≤ Real.rpow Δ (-3 * ε) := h_log_absorb
      have h_nonneg_cfixed : 0 ≤ C_fixed * Real.rpow Δ (-140 * ε) :=
        mul_nonneg h_fixed_pos.le (Real.rpow_nonneg hΔ_pos.le _)
      calc C_int * (4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t
        = (C_int * (4 : ℝ)^t) * (4 * Real.log (3 / Δ) + 1) := by ring
      _ ≤ (C_fixed * Real.rpow Δ (-140 * ε)) * Real.rpow Δ (-3 * ε) := by
        exact mul_le_mul h_a h_c h_b h_nonneg_cfixed
    have hQ2 : (a5.Qset.card : ℝ)^2 ≤ (Real.rpow Δ (-t - ε))^2 := by
      gcongr <;> exact hQset_upper
    have h_main : C_int * (4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C_Qset * (a5.Qset.card : ℝ)^2 ≤
        Real.rpow Δ (-2 * t - 226 * ε) := by
      have h_pos1 : 0 ≤ C_Qset := by positivity
      have h_pos2 : 0 ≤ (a5.Qset.card : ℝ)^2 := by positivity
      have h1 : C_int * (4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C_Qset * (a5.Qset.card : ℝ)^2 ≤
          (C_fixed * Real.rpow Δ (-140 * ε)) * Real.rpow Δ (-3 * ε) * C_Qset * (a5.Qset.card : ℝ)^2 := by
        have h_pos : 0 ≤ C_Qset * (a5.Qset.card : ℝ)^2 := by positivity
        have h' : (C_int * (4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t) * (C_Qset * (a5.Qset.card : ℝ)^2) ≤
            ((C_fixed * Real.rpow Δ (-140 * ε)) * Real.rpow Δ (-3 * ε)) * (C_Qset * (a5.Qset.card : ℝ)^2) :=
          mul_le_mul_of_nonneg_right h_mult h_pos
        simpa [mul_assoc] using h'
      have h2 : (C_fixed * Real.rpow Δ (-140 * ε)) * Real.rpow Δ (-3 * ε) * C_Qset * (a5.Qset.card : ℝ)^2 ≤
          (C_fixed * Real.rpow Δ (-140 * ε)) * Real.rpow Δ (-3 * ε) * Real.rpow Δ (-80 * ε) * (Real.rpow Δ (-t - ε))^2 := by
        have hC_Qset_eq : C_Qset = Real.rpow Δ (-80 * ε) := by rfl
        rw [hC_Qset_eq]
        have h_pos : 0 ≤ (C_fixed * Real.rpow Δ (-140 * ε)) * Real.rpow Δ (-3 * ε) * Real.rpow Δ (-80 * ε) := by
          apply mul_nonneg
          · apply mul_nonneg
            · apply mul_nonneg
              · exact h_fixed_pos.le
              · exact Real.rpow_nonneg hΔ_pos.le _
            · exact Real.rpow_nonneg hΔ_pos.le _
          · exact Real.rpow_nonneg hΔ_pos.le _
        have h' : ((C_fixed * Real.rpow Δ (-140 * ε)) * Real.rpow Δ (-3 * ε) * Real.rpow Δ (-80 * ε)) * (a5.Qset.card : ℝ)^2 ≤
            ((C_fixed * Real.rpow Δ (-140 * ε)) * Real.rpow Δ (-3 * ε) * Real.rpow Δ (-80 * ε)) * (Real.rpow Δ (-t - ε))^2 :=
          mul_le_mul_of_nonneg_left hQ2 h_pos
        simpa [mul_assoc] using h'
      have h3 : (C_fixed * Real.rpow Δ (-140 * ε)) * Real.rpow Δ (-3 * ε) * Real.rpow Δ (-80 * ε) * (Real.rpow Δ (-t - ε))^2 ≤
          Real.rpow Δ (-ε) * Real.rpow Δ (-140 * ε) * Real.rpow Δ (-3 * ε) * Real.rpow Δ (-80 * ε) * (Real.rpow Δ (-t - ε))^2 := by
        have h_pos_all : 0 ≤ Real.rpow Δ (-140 * ε) * Real.rpow Δ (-3 * ε) * Real.rpow Δ (-80 * ε) * (Real.rpow Δ (-t - ε))^2 := by
          apply mul_nonneg
          · apply mul_nonneg
            · apply mul_nonneg
              · exact Real.rpow_nonneg hΔ_pos.le _
              · exact Real.rpow_nonneg hΔ_pos.le _
            · exact Real.rpow_nonneg hΔ_pos.le _
          · exact sq_nonneg _
        nlinarith [hC_fixed_le]
      have h_sq : (Real.rpow Δ (-t - ε)) ^ 2 = Real.rpow Δ (-2 * t - 2 * ε) := by
        have h1 : (Real.rpow Δ (-t - ε)) ^ 2 = Real.rpow Δ (-t - ε) * Real.rpow Δ (-t - ε) := by ring
        rw [h1]
        have h2 : Real.rpow Δ (-t - ε) * Real.rpow Δ (-t - ε) = Real.rpow Δ ((-t - ε) + (-t - ε)) := by
          rw [← rpow_add_eq hΔ_pos] <;> ring
        rw [h2]
        have h3 : (-t - ε) + (-t - ε) = -2 * t - 2 * ε := by ring
        rw [h3]
      have h4 : Real.rpow Δ (-ε) * Real.rpow Δ (-140 * ε) * Real.rpow Δ (-3 * ε) * Real.rpow Δ (-80 * ε) * (Real.rpow Δ (-t - ε))^2 =
          Real.rpow Δ (-2 * t - 226 * ε) := by
        rw [h_sq]
        have h5 : Real.rpow Δ (-ε) * Real.rpow Δ (-140 * ε) = Real.rpow Δ (-141 * ε) := by
          rw [← rpow_add_eq hΔ_pos] <;> ring_nf
        rw [h5]
        have h6 : Real.rpow Δ (-141 * ε) * Real.rpow Δ (-3 * ε) = Real.rpow Δ (-144 * ε) := by
          rw [← rpow_add_eq hΔ_pos] <;> ring_nf
        rw [h6]
        have h7 : Real.rpow Δ (-144 * ε) * Real.rpow Δ (-80 * ε) = Real.rpow Δ (-224 * ε) := by
          rw [← rpow_add_eq hΔ_pos] <;> ring_nf
        rw [h7]
        have h8 : Real.rpow Δ (-224 * ε) * Real.rpow Δ (-2 * t - 2 * ε) = Real.rpow Δ (-2 * t - 226 * ε) := by
          rw [← rpow_add_eq hΔ_pos] <;> ring_nf
        rw [h8]
      calc _
        ≤ (C_fixed * Real.rpow Δ (-140 * ε)) * Real.rpow Δ (-3 * ε) * C_Qset * (a5.Qset.card : ℝ)^2 := h1
      _ ≤ (C_fixed * Real.rpow Δ (-140 * ε)) * Real.rpow Δ (-3 * ε) * Real.rpow Δ (-80 * ε) * (Real.rpow Δ (-t - ε))^2 := h2
      _ ≤ Real.rpow Δ (-ε) * Real.rpow Δ (-140 * ε) * Real.rpow Δ (-3 * ε) * Real.rpow Δ (-80 * ε) * (Real.rpow Δ (-t - ε))^2 := h3
      _ = Real.rpow Δ (-2 * t - 226 * ε) := h4
    exact le_trans hE_bound h_main

  -- E/I ≤ Δ^{-u-299ε}
  have hE_I_bound : E ≤ Real.rpow Δ (-u - 299 * ε) * I := by
    have h_exp_eq : -u - 299 * ε + (-(s + t) + 73 * ε) = -2 * t - 226 * ε := by
      simp [u] <;> ring
    have h5 : Real.rpow Δ (-2 * t - 226 * ε) =
        Real.rpow Δ (-u - 299 * ε) * Real.rpow Δ (-(s + t) + 73 * ε) := by
      rw [← rpow_add_eq hΔ_pos, h_exp_eq]
    have h_rpow_pos : 0 < Real.rpow Δ (-u - 299 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    calc E
      ≤ Real.rpow Δ (-2 * t - 226 * ε) := hE_pre
    _ = Real.rpow Δ (-u - 299 * ε) * Real.rpow Δ (-(s + t) + 73 * ε) := h5
    _ ≤ Real.rpow Δ (-u - 299 * ε) * I := by
      have h_ge : Real.rpow Δ (-(s + t) + 73 * ε) ≤ I := hI_lower
      exact mul_le_mul_of_nonneg_left h_ge h_rpow_pos.le

  -- Weaken to 4·Δ^{-u-300ε}: since Δ^ε < 1, Δ^{-u-299ε} < Δ^{-u-300ε}
  have h_final : E ≤ 4 * Real.rpow Δ (-u - 300 * ε) * I := by
    have h9 : Real.rpow Δ (-u - 299 * ε) ≤ Real.rpow Δ (-u - 300 * ε) := by
      have h10 : -u - 299 * ε ≥ -u - 300 * ε := by linarith
      exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos (by linarith) h10
    have hI_nonneg : 0 ≤ I := by linarith [hI_pos']
    have h10 : 0 ≤ Real.rpow Δ (-u - 300 * ε) := Real.rpow_nonneg hΔ_pos.le _
    calc E
      ≤ Real.rpow Δ (-u - 299 * ε) * I := hE_I_bound
    _ ≤ Real.rpow Δ (-u - 300 * ε) * I := by
      exact mul_le_mul h9 (le_refl I) hI_nonneg (Real.rpow_nonneg hΔ_pos.le _)
    _ ≤ 4 * Real.rpow Δ (-u - 300 * ε) * I := by
      have h11 : 0 ≤ Real.rpow Δ (-u - 300 * ε) * I := by exact mul_nonneg h10 hI_nonneg
      linarith

  dsimp only
  have h_goal : E ≤ 4 * Real.rpow Δ (-u - 300 * ε) * I := h_final
  rw [←hE_eq]
  exact h_goal

end
end DirecretisedFurstenbergEstimate.AppendixA
