module

/-
  Clean Local Fine S-set Transfer with Explicit Density Factor

  Clean re-export of `local_fine_sset_with_density` using only clean imports:
  - B1InductionDataType (instead of contaminated PerSquareRetention)
  - CleanFineGeometry (instead of contaminated Prop73.InductiveStepBridge)
  - B1ToSection6 (clean, provides b1_sset_transfer_to_fine)

  Chain:
  1. hE : IsDeltaSSet δ_n u C_point config.pointSet
  2. h_density : Ncover δ_n config.pointSet ≤ (9 * K_density * |P₀|) * Ncover δ_n E_ret
  3. thin_preserves_sset_by_density : IsDeltaSSet δ_n u (C_point * K') E_ret
  4. b1_sset_transfer_to_fine : IsDeltaSSet δ_{n-m} u (C_point * K' * δ_m^u) normalized_E_ret
  5. Set equality : normalized_E_ret = fineConfig Q hQ.pointSet

  Output: C_ret = C_point * 9 * K_density * |coarseConfig.P₀| * δ_m^u

  Whiteprint node: local_fine_sset_with_density
  Status: CLEAN RE-EXPORT
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.B1InductionDataType
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CleanFineGeometry
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.B1ToSection6
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence
open DirecretisedFurstenbergEstimate.Section6
open InductionConfigurations

/-- Transfer S-set from global config.pointSet to normalized fine fiber inside Q,
    using an explicit `K_density` factor separate from `data.K`.

    Input `h_density` is produced by `b1_retained_fiber_density` with
    `K_global` as `K_density`.

    The same `Q` selected by `b1_retained_fiber_density` must be passed here.

    Output constant: C_ret = C_point * 9 * K_density * |coarseConfig.P₀| * δ_m^u. -/
lemma local_fine_sset_with_density_clean
    {n m : ℕ} (hnm : m ≤ n)
    {u C_point : ℝ} {M : ℕ}
    {s t C₁ : ℝ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    (data : B1InductionData n m hnm s t C₁ M config)
    (K_density : ℝ)
    (hK_density_pos : 0 < K_density)
    (Q : DyadicSquare m)
    (hQ : Q ∈ data.coarseConfig.P₀)
    (hE : IsDeltaSSet (dyadicDelta n) u C_point config.pointSet)
    (hu_pos : 0 < u)
    (h_density : Ncover (dyadicDelta n) config.pointSet ≤
        ENNReal.ofReal (9 * K_density * (data.coarseConfig.P₀.card : ℝ)) *
        Ncover (dyadicDelta n)
          (⋃ p ∈ (data.P.filter (fun p => squareContained hnm p Q)),
            (DyadicSquare.toSet p : Set EuclideanPlane)))
    (h_fineP_eq : (data.fineConfig Q hQ).P₀ =
        (data.P.filter (fun p => squareContained hnm p Q)).image (squareHomothety hnm Q)) :
    ∃ (C_ret : ℝ), 0 < C_ret ∧
      IsDeltaSSet (dyadicDelta (n - m)) u C_ret (data.fineConfig Q hQ).pointSet ∧
      C_ret = C_point * 9 * K_density * (data.coarseConfig.P₀.card : ℝ) * (dyadicDelta m)^u := by
  let δ_n := dyadicDelta n
  let δ_m := dyadicDelta m
  let K' : ℝ := 9 * K_density * (data.coarseConfig.P₀.card : ℝ)

  let P_Q : Finset (DyadicSquare n) :=
    data.P.filter (fun p => squareContained hnm p Q)

  let E_ret : Set EuclideanPlane :=
    ⋃ p ∈ P_Q, (DyadicSquare.toSet p : Set EuclideanPlane)

  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  have hδm_pos : 0 < δ_m := dyadicDelta_pos m

  have h_coarse_nonempty : data.coarseConfig.P₀.Nonempty := by
    rw [data.h_coarse_P_eq]
    exact data.hP_nonempty.image _
  have h_card_pos : 0 < (data.coarseConfig.P₀.card : ℝ) := by
    exact_mod_cast h_coarse_nonempty.card_pos
  have hK'_pos : 0 < K' := by
    dsimp only [K']
    positivity

  have hCP_pos : 0 < C_point := hE.2.2.1

  have h1_sub : E_ret ⊆ config.pointSet := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxp⟩
    have h_p_in_P0 : p ∈ config.P₀ := data.hP_sub (Finset.mem_filter.mp hp).1
    exact Set.mem_iUnion₂.mpr ⟨p, h_p_in_P0, hxp⟩

  have hPQ_nonempty : P_Q.Nonempty := by
    have h_img : Q ∈ data.P.image (InductionConfigurations.containingSquare hnm) := by
      rw [←data.h_coarse_P_eq] <;> exact hQ
    rcases Finset.mem_image.mp h_img with ⟨p, hp, h_eq⟩
    have h_cont : squareContained hnm p Q :=
      (InductionConfigurations.containingSquare_iff hnm p Q).mp h_eq
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, h_cont⟩⟩

  have hE_ret_nonempty : E_ret.Nonempty := by
    rcases hPQ_nonempty with ⟨p, hp⟩
    have h_p_toSet_nonempty : (DyadicSquare.toSet p : Set EuclideanPlane).Nonempty :=
      DyadicSquare.toSet_nonempty p
    rcases h_p_toSet_nonempty with ⟨x, hx⟩
    exact ⟨x, Set.mem_iUnion₂.mpr ⟨p, hp, hx⟩⟩

  have hE_ret_sset : IsDeltaSSet δ_n u (C_point * K') E_ret :=
    thin_preserves_sset_by_density
      hE h1_sub hE_ret_nonempty hK'_pos h_density

  have h2_sub_Q : E_ret ⊆ Q.toSet := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxp⟩
    have h_cont : squareContained hnm p Q := (Finset.mem_filter.mp hp).2
    have h_p_sub : (DyadicSquare.toSet p) ⊆ Q.toSet := by exact InductionOnScales.squareContained_toSet_subset hnm h_cont
    exact h_p_sub hxp

  have h_trivial_density : Ncover δ_n E_ret ≤
      ENNReal.ofReal (1 : ℝ) * Ncover δ_n (E_ret ∩ Q.toSet) := by
    have h_eq : E_ret ∩ Q.toSet = E_ret := by
      ext x; simp [h2_sub_Q] <;> tauto
    rw [h_eq] <;> simp

  have hE'_nonempty : (E_ret ∩ Q.toSet).Nonempty := by
    have h_eq : E_ret ∩ Q.toSet = E_ret := by
      ext x; simp [h2_sub_Q] <;> tauto
    rw [h_eq]
    exact hE_ret_nonempty

  have h_inter_eq : E_ret ∩ Q.toSet = E_ret := by
    ext x; simp [h2_sub_Q] <;> tauto

  have hE_ret_norm_raw : IsDeltaSSet (δ_n / δ_m) u
      ((C_point * K') * (1 : ℝ) * δ_m ^ u)
      ((fun x : EuclideanPlane => δ_m⁻¹ • (x + -dyadicSquareLowerLeft Q)) '' (E_ret ∩ Q.toSet)) :=
    b1_sset_transfer_to_fine hnm
      (ht_pos := hu_pos)
      (hC_pos := mul_pos hCP_pos hK'_pos)
      (hK_pos := by norm_num)
      hE_ret_sset Q hE'_nonempty h_trivial_density

  have hE_ret_norm_sset : IsDeltaSSet (δ_n / δ_m) u
      ((C_point * K') * (1 : ℝ) * δ_m ^ u)
      ((fun x : EuclideanPlane => δ_m⁻¹ • (x + -dyadicSquareLowerLeft Q)) '' E_ret) := by
    rw [h_inter_eq] at hE_ret_norm_raw
    exact hE_ret_norm_raw

  have h_const_eq : (C_point * K') * (1 : ℝ) * δ_m ^ u = C_point * K' * δ_m ^ u := by ring

  let normMap : EuclideanPlane → EuclideanPlane :=
    fun x => δ_m⁻¹ • (x + -dyadicSquareLowerLeft Q)

  have h_normMap_eq : normMap = homothetyS δ_m Q.i Q.j := by
    funext x
    have hδm : δ_m = dyadicDelta m := by rfl
    simp [normMap, homothetyS, dyadicSquareLowerLeft, hδm]
    <;> ext i <;> fin_cases i <;> simp [sub_eq_add_neg] <;> ring

  have h_contained : ∀ p ∈ P_Q, squareContained hnm p Q := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2

  have h_set_eq1 : (normMap '' E_ret) =
      ⋃ p ∈ P_Q, ((squareHomothety hnm Q p).toSet : Set EuclideanPlane) := by
    rw [h_normMap_eq]
    exact (fine_point_set_homothety_image_clean hnm Q P_Q h_contained).symm

  have h_set_eq2 : (⋃ p ∈ P_Q, ((squareHomothety hnm Q p).toSet : Set EuclideanPlane)) =
      (data.fineConfig Q hQ).pointSet := by
    have hP0eq : (data.fineConfig Q hQ).P₀ = P_Q.image (squareHomothety hnm Q) := h_fineP_eq
    have h : (data.fineConfig Q hQ).pointSet =
        ⋃ q ∈ (data.fineConfig Q hQ).P₀, (DyadicSquare.toSet q : Set EuclideanPlane) := by rfl
    rw [h, hP0eq]
    let f : DyadicSquare n → DyadicSquare (n - m) := squareHomothety hnm Q
    have h_biu : (⋃ q ∈ P_Q.image f, (DyadicSquare.toSet q : Set EuclideanPlane)) =
        (⋃ p ∈ P_Q, (DyadicSquare.toSet (f p) : Set EuclideanPlane)) := by
      ext y
      simp only [Set.mem_iUnion₂]
      constructor
      · rintro ⟨q, hq, hyq⟩
        rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
        exact ⟨p, hp, hyq⟩
      · rintro ⟨p, hp, hyp⟩
        exact ⟨f p, Finset.mem_image.mpr ⟨p, hp, rfl⟩, hyp⟩
    exact h_biu.symm

  have h_set_eq : (normMap '' E_ret) = (data.fineConfig Q hQ).pointSet := by
    rw [h_set_eq1, h_set_eq2]

  have h_scale_eq : δ_n / δ_m = dyadicDelta (n - m) := by
    dsimp only [δ_n, δ_m]
    have h1 : n = m + (n - m) := by omega
    have h_mul : dyadicDelta m * dyadicDelta (n - m) = dyadicDelta n := by
      rw [h1]
      simp [dyadicDelta, pow_add] <;> field_simp <;> ring
    have h_pos : 0 < dyadicDelta m := dyadicDelta_pos m
    field_simp [h_pos.ne'] <;> linarith
  rw [h_set_eq] at hE_ret_norm_sset
  rw [h_const_eq] at hE_ret_norm_sset
  rw [h_scale_eq] at hE_ret_norm_sset
  let C_ret : ℝ := C_point * K' * δ_m ^ u
  have hC_ret_pos : 0 < C_ret := by positivity
  have hC_ret_formula : C_ret = C_point * 9 * K_density * (data.coarseConfig.P₀.card : ℝ) * δ_m ^ u := by
    dsimp only [C_ret, K'] <;> ring
  exact ⟨C_ret, hC_ret_pos, hE_ret_norm_sset, hC_ret_formula⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
