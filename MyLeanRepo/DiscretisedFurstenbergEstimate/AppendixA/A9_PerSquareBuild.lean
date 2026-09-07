module

/-
  A9 per-square construction extracted as a standalone lemma for compilation performance.
  This is the body of perSquare' from A9_Canonical.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A9_Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A9_CFineBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A9_Phase1Geometry
public import MyLeanRepo.OSWPrelude

@[expose] public section

set_option maxHeartbeats 1000000

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate

open LemmaE
open DiscretisedFurstenbergEstimate.CoveringUtils
open TubesAndSlopes

namespace AppendixA

/-- Per-square construction for A9: builds A9_SquareData from A8 data.
    Extracted from A9_Canonical for compilation performance. -/
def A9_buildSquareData
    (Δ δ s t ε : ℝ)
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hδ_eq : δ = Δ ^ 2)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (hε_pos : 0 < ε)
    (hΔ_cover : (10000 : ℝ) ≤ Real.rpow Δ (-2 * s - ε))
    (hΔ_packing : Δ ^ (10 * ε) ≤ 1 / 144)
    (hΔ_small : 7 * Δ ≤ 1)
    (hΔ_coarse_absorb : (2 * 10^13 : ℝ) ≤ Real.rpow Δ (-ε))
    (hΔ_fine_absorb : (16 * (MainAppendix.affineLine_packing_constant : ℝ)^2 *
        (2 * 20 * 1048576 * 256 * (3 / 2 : ℝ) * 256 * 16)) ≤ Real.rpow Δ (-453 * ε))
    (a8 : A8_Output Δ δ s t ε)
    (Q : CoarseSquare Δ) (hQ : Q ∈ a8.Q0) :
    A9_SquareData Δ δ s t ε Q := by
  let phase1 := A9_phase1_geometry Δ δ s t ε hΔ_pos hΔ_lt_half hδ_eq hs hs1 hst hε_pos
    hΔ_cover hΔ_packing hΔ_small a8 Q hQ
  let T0 := phase1.T0
  let hδ_pos : 0 < δ := phase1.hδ_pos
  let sq := phase1.sq
  let σ₀ := tubeSlope T0
  let h₀ := tubeIntercept T0
  let z_Q := phase1.z_Q
  let P_orig_Q := phase1.P_orig_Q
  let P_norm_Q := phase1.P_norm_Q
  let normOfSheared := phase1.normOfSheared
  let squareIndex := phase1.squareIndex
  let c_Q := phase1.c_Q
  have h_c_Q_def : c_Q = z_Q 0 - σ₀ * z_Q 1 - h₀ := by
    have h := phase1.h_c_Q_def
    simpa [σ₀, h₀] using h
  let Pi_Q := phase1.Pi_Q
  have h_Pi_Q_def : Pi_Q = (fun x : ℝ => Δ * x + c_Q) '' sq.proj.Pi := phase1.h_Pi_Q_def
  let fineTubes_norm := phase1.fineTubes_norm
  let fineTubeOfCell := phase1.fineTubeOfCell
  have h_fineTubeOfCell_def : ∀ (p : Plane) (cell : DyadicTubeCell δ),
      fineTubeOfCell p cell = TubesAndSlopes.makeAffineLine
        (paramsOfDyadicCell δ cell).1 (paramsOfDyadicCell δ cell).2 := phase1.h_fineTubeOfCell_def
  let f_cell := phase1.f_cell
  have h_f_cell_def : ∀ (T : FineTube), f_cell T =
      dyadicCellOfParams δ hδ_pos (tubeSlope T - σ₀, tubeIntercept T - h₀) := by
    intro T
    have h := phase1.h_f_cell_def T
    simpa [σ₀, h₀] using h
  let witness := phase1.witness
  have h_σ₀_def : σ₀ = tubeSlope T0 := by rfl
  have h_h₀_def : h₀ = tubeIntercept T0 := by rfl
  let x_Q : ℝ := squareX Δ Q
  let y_Q : ℝ := squareY Δ Q
  have hx_Q_eq : x_Q = squareX Δ Q := by rfl
  have hy_Q_eq : y_Q = squareY Δ Q := by rfl
  have h_norm_mem : ∀ p ∈ P_norm_Q, normOfSheared p ∈ sq.P'_Q := phase1.h_norm_mem
  have hP_phys_sub : (P_orig_Q : Set Plane) ⊆ squareSet Δ Q := phase1.hP_phys_sub
  have hP_phys_card : Real.rpow Δ (-t + 44 * ε) ≤ (P_orig_Q.card : ℝ) := phase1.hP_phys_card
  have hy_Q_bounds : y_Q ∈ Set.Icc (-2 : ℝ) 2 := phase1.hy_Q_bounds
  have hP_in_square : (P_norm_Q : Set Plane) ⊆ Metric.cthickening (2 * Δ) (squareSet Δ squareIndex) := phase1.hP_in_square
  have hPi_Q_bounds : ∀ x ∈ Pi_Q, x ∈ Set.Icc (-6 : ℝ) 6 := phase1.hPi_Q_bounds
  have hPi_Q_sset : IsDeltaSSet Δ s (Real.rpow Δ (-s - 49 * ε)) Pi_Q := phase1.hPi_Q_sset
  have hfine_card_lower : ∀ p ∈ P_norm_Q, Real.rpow Δ (-s + 50 * ε) ≤ (fineTubes_norm p).card := phase1.hfine_card_lower
  have hfine_card_upper : ∀ p ∈ P_norm_Q, (fineTubes_norm p).card ≤ Real.rpow Δ (-s - 7 * ε) := phase1.hfine_card_upper
  have h_fine_def : ∀ p ∈ P_norm_Q,
    fineTubes_norm p = (sq.fineTubes (normOfSheared p)).image f_cell := phase1.h_fine_def
  have hfine_cell_bounds : ∀ p ∈ P_norm_Q, ∀ cell ∈ fineTubes_norm p,
    |(paramsOfDyadicCell δ cell).1| ≤ 7 * Δ ∧ |(paramsOfDyadicCell δ cell).2| ≤ 7 * Δ := phase1.hfine_cell_bounds
  have h_witness : ∀ x ∈ Pi_Q, witness x ∈ P_norm_Q ∧ (witness x) 0 = x := phase1.h_witness
  have h_witness_y_close : ∀ x ∈ Pi_Q, |(witness x) 1 - y_Q| ≤ 3 * Δ := phase1.h_witness_y_close
  have h_residual : ∀ x ∈ Pi_Q, ∀ cell ∈ fineTubes_norm (witness x),
    let T := fineTubeOfCell (witness x) cell
    |x - tubeSlope T * (witness x) 1 - tubeIntercept T| ≤ 6 * δ := phase1.h_residual
  have h_orig_inj : Set.InjOn sq.originalOfNorm (sq.P'_Q : Set Plane) := phase1.h_orig_inj
  let F : Plane → Plane := phase1.F
  have hF_eq : F = AffineNormalization.normalizeMap σ₀ h₀ := by
    simpa [σ₀, h₀] using phase1.hF_def
  let Finv : Plane → Plane := AffineNormalization.denormalizeMap σ₀ h₀
  have hF_inj : Function.Injective F := by
    rw [hF_eq]
    exact AffineNormalization.normalizeMap_injective σ₀ h₀
  have hFinv_inj : Function.Injective Finv :=
    (AffineNormalization.normalizeMap_right_inverse σ₀ h₀).injective

  have h_coord_abs_le_norm : ∀ (p : Plane) (i : Fin 2), |p i| ≤ ‖p‖ := by
    intro p i
    have h_norm_sq : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
      have h : ‖p‖ = Real.sqrt ((p 0) ^ 2 + (p 1) ^ 2) := by
        rw [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> simp
      rw [h]
      rw [Real.sq_sqrt (by positivity)] <;> ring
    have h2 : (p i) ^ 2 ≤ ‖p‖ ^ 2 := by
      rw [h_norm_sq]
      fin_cases i <;> simp [Fin.sum_univ_two] <;> positivity
    have h3 : (|p i|) ^ 2 ≤ (‖p‖) ^ 2 := by
      have h4 : (|p i|) ^ 2 = (p i) ^ 2 := by simp [sq_abs]
      rw [h4] <;> exact h2
    nlinarith [sq_abs (p i), norm_nonneg p]

  -- Fine tube rescalable constant
  let C_fine : ℝ :=
    (max 1 (sq.a4.base.K_pack * Real.rpow δ (-ε)) * sq.a4.base.K_Q *
      (MainAppendix.affineLine_packing_constant : ℝ)) *
    sq.a4.base.M *
    (MainAppendix.affineLine_packing_constant : ℝ) *
    Real.rpow Δ (s - 40 * ε)
  let C_fine_resc : ℝ :=
    C_fine * (20 : ℝ)^s * 1048576 * 256 * (3 / 2 : ℝ)^s * 256 * (16 : ℝ)^s * Δ^s
  -- Extract C_fine positivity from A8's hfine_tubes_sset (which requires 0 < C)
  have hP'_nonempty : (sq.P'_Q).Nonempty := by
    have h1 : 0 < (sq.P'_Q.card : ℝ) := by
      have h2 : 0 < Real.rpow Δ (-t + 44 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      exact lt_of_lt_of_le h2 sq.hP'_Q_card_lower
    exact Finset.card_pos.mp (by exact_mod_cast h1)
  let p_wit := Classical.choose hP'_nonempty
  have hp_wit : p_wit ∈ sq.P'_Q := Classical.choose_spec hP'_nonempty
  have hT_sset_wit : IsDeltaSSet δ s C_fine (sq.fineTubes p_wit : Set FineTube) :=
    sq.hfine_tubes_sset p_wit hp_wit
  have hC_fine_pos : 0 < C_fine := hT_sset_wit.2.2.1
  have hC_fine_resc_pos : 0 < C_fine_resc := by
    have h1 : 0 < C_fine := hC_fine_pos
    have h2 : 0 < (20 : ℝ)^s := by positivity
    have h3 : 0 < (3 / 2 : ℝ)^s := by positivity
    have h4 : 0 < (16 : ℝ)^s := by positivity
    have h5 : 0 < Δ ^ s := by positivity
    positivity
  have hC_fine_resc_le_499 : 16 * C_fine_resc ≤ Real.rpow Δ (-501 * ε) := by
    have hM_pos : 0 < sq.a4.base.M := by
      have h1 : 0 < Real.rpow Δ (-2 * s + 2 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have h2 : 0 < sq.a4.base.K_pack := sq.a4.base.hKpack_pos
      have h3 : 0 < Real.rpow Δ (-2 * s + 2 * ε) / sq.a4.base.K_pack := div_pos h1 h2
      exact lt_of_lt_of_le h3 sq.a4.base.hM_lower
    have hPconst_pos : 0 < (MainAppendix.affineLine_packing_constant : ℝ) := by
      exact Nat.cast_pos.mpr MainAppendix.affineLine_packing_constant_pos
    exact A9_cfine_resc_bound Δ δ s ε hΔ_pos hΔ_small hδ_eq
      (by linarith) hs1 hε_pos
      sq.a4.base.K_pack sq.a4.base.K_Q sq.a4.base.M
      sq.a4.base.hKpack_bound sq.a4.base.hKpack_pos
      sq.a4.base.hK_Q_pos sq.a4.base.hK_Q_loss
      hM_pos sq.a4.base.hM_upper
      hΔ_fine_absorb hPconst_pos

  -- Helper: snapped translated params = dyadic cell params
  have h_set_eq : ∀ (p : Plane), p ∈ P_norm_Q →
      (fun (x : ℝ × ℝ) => (δ * ⌊x.1 / δ⌋, δ * ⌊x.2 / δ⌋)) ''
        ((fun x : ℝ × ℝ => x + (-σ₀, -h₀)) ''
          (LemmaE.affineLineParams '' (sq.fineTubes (normOfSheared p) : Set FineTube))) =
      (fun cell => paramsOfDyadicCell δ cell) '' (fineTubes_norm p : Set (DyadicTubeCell δ)) := by
    intro p hp
    have hft_def : fineTubes_norm p = (sq.fineTubes (normOfSheared p)).image f_cell :=
      h_fine_def p hp
    let snap : ℝ × ℝ → ℝ × ℝ := fun x => (δ * ⌊x.1 / δ⌋, δ * ⌊x.2 / δ⌋)
    let trans : ℝ × ℝ → ℝ × ℝ := fun x => x + (-σ₀, -h₀)
    let Tubes : Set FineTube := (sq.fineTubes (normOfSheared p) : Set FineTube)
    have h_key : ∀ (T : FineTube), T ∈ Tubes →
        snap (trans (LemmaE.affineLineParams T)) = paramsOfDyadicCell δ (f_cell T) := by
      intro T _
      have h_ap : LemmaE.affineLineParams T = (tubeSlope T, tubeIntercept T) := by
        exact Prod.mk.eta.symm
      rw [h_ap]
      dsimp only [snap, trans, dyadicCellOfParams, paramsOfDyadicCell]
      rw [h_f_cell_def T]
      <;> congr <;> ring
    ext z
    constructor
    · intro hz
      rcases hz with ⟨x, hx, rfl⟩
      rcases hx with ⟨y, hy, rfl⟩
      rcases hy with ⟨T, hT, rfl⟩
      have h_fcell_in : f_cell T ∈ fineTubes_norm p := by
        rw [hft_def]
        exact Finset.mem_image_of_mem f_cell hT
      exact ⟨f_cell T, h_fcell_in, h_key T hT⟩
    · intro hz
      rcases hz with ⟨cell, hcell, rfl⟩
      have h_cell_in : cell ∈ (sq.fineTubes (normOfSheared p)).image f_cell := by
        simpa [hft_def] using hcell
      rcases Finset.mem_image.mp h_cell_in with ⟨T, hT, rfl⟩
      refine ⟨trans (LemmaE.affineLineParams T), ?_, ?_⟩
      · exact ⟨LemmaE.affineLineParams T, ⟨T, hT, rfl⟩, rfl⟩
      · exact h_key T hT

  -- Proof of hfine_sum_le: |fineTubes_norm p| ≤ assignedCount at g(p), sum by injectivity
  let T_Q := sq.a4.base.T_Q
  have h_fine_card : ∀ p ∈ P_norm_Q,
      (fineTubes_norm p).card ≤ (sq.fineTubes (normOfSheared p)).card := by
    intro p hp
    rw [h_fine_def p hp]
    exact Finset.card_image_le
  have h_fine_eq : ∀ q ∈ sq.P'_Q,
      (sq.fineTubes q).card = assignedCountDyadic Δ hΔ_pos T_Q (sq.originalOfNorm q) T0 := by
    intro q hq
    have h_pf : sq.fineTubes q = pointFiber Δ hΔ_pos T_Q (sq.originalOfNorm q) T0 :=
      sq.hfine_eq_pointFiber q hq
    rw [h_pf]
    <;> rfl
  let g : Plane → Plane := fun p => sq.originalOfNorm (normOfSheared p)
  have h_g_mem : ∀ p ∈ P_norm_Q, g p ∈ P_orig_Q := by
    intro p hp
    have h1 : normOfSheared p ∈ sq.P'_Q := h_norm_mem p hp
    exact Finset.mem_image_of_mem sq.originalOfNorm h1
  have h_g_inj : Set.InjOn g (P_norm_Q : Set Plane) := by
    intro p1 _ p2 _ h
    have h1 : sq.originalOfNorm (normOfSheared p1) = sq.originalOfNorm (normOfSheared p2) := h
    have h2 : normOfSheared p1 = normOfSheared p2 := by
      have h_inj_orig : Set.InjOn sq.originalOfNorm (sq.P'_Q : Set Plane) := h_orig_inj
      have h3 : normOfSheared p1 ∈ sq.P'_Q := h_norm_mem p1 ‹_›
      have h4 : normOfSheared p2 ∈ sq.P'_Q := h_norm_mem p2 ‹_›
      exact h_inj_orig h3 h4 h1
    have h_norm_inj : Function.Injective normOfSheared := by
      intro x y hxy
      have h : (1 / Δ : ℝ) • (Finv x - z_Q) = (1 / Δ : ℝ) • (Finv y - z_Q) := hxy
      have h' : Finv x - z_Q = Finv y - z_Q := by
        have h5 : (1 / Δ : ℝ)⁻¹ • ((1 / Δ : ℝ) • (Finv x - z_Q)) =
                 (1 / Δ : ℝ)⁻¹ • ((1 / Δ : ℝ) • (Finv y - z_Q)) := by rw [h]
        have h6 : ∀ (v : Plane), (1 / Δ : ℝ)⁻¹ • ((1 / Δ : ℝ) • v) = v := by
          intro v
          rw [smul_smul]
          have h7 : (1 / Δ : ℝ)⁻¹ * (1 / Δ : ℝ) = 1 := by
            field_simp [hΔ_pos.ne'] <;> ring
          rw [h7, one_smul]
        rw [h6 (Finv x - z_Q), h6 (Finv y - z_Q)] at h5
        exact h5
      have h'' : Finv x = Finv y := by simpa [sub_eq_sub_iff_sub_eq_sub] using h'
      exact hFinv_inj h''
    exact h_norm_inj h2
  have h_sum1 : ∑ p ∈ P_norm_Q, (fineTubes_norm p).card ≤
      ∑ p ∈ P_norm_Q, (sq.fineTubes (normOfSheared p)).card := by
    apply Finset.sum_le_sum
    intro p hp
    exact h_fine_card p hp
  have h_sum2 : ∑ p ∈ P_norm_Q, (sq.fineTubes (normOfSheared p)).card =
      ∑ p ∈ P_norm_Q, assignedCountDyadic Δ hΔ_pos T_Q (g p) T0 := by
    apply Finset.sum_congr rfl
    intro p hp
    have hq : normOfSheared p ∈ sq.P'_Q := h_norm_mem p hp
    exact h_fine_eq (normOfSheared p) hq
  have h_sum3 : ∑ p ∈ P_norm_Q, assignedCountDyadic Δ sq.a4.base.hΔ_pos sq.a4.base.T_Q (g p) T0 =
      ∑ x ∈ P_norm_Q.image g, assignedCountDyadic Δ hΔ_pos T_Q x T0 := by
    rw [Finset.sum_image h_g_inj] <;> rfl
  have h_img_sub : P_norm_Q.image g ⊆ P_orig_Q := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    exact h_g_mem p hp
  have h_sum4 : ∑ x ∈ P_norm_Q.image g, assignedCountDyadic Δ sq.a4.base.hΔ_pos sq.a4.base.T_Q x T0 ≤
      ∑ x ∈ P_orig_Q, assignedCountDyadic Δ hΔ_pos T_Q x T0 := by
    let f := fun x => assignedCountDyadic Δ hΔ_pos T_Q x T0
    have h_eq : ∑ x ∈ P_orig_Q, f x =
        ∑ x ∈ P_norm_Q.image g, f x + ∑ x ∈ P_orig_Q \ P_norm_Q.image g, f x := by
      rw [← Finset.sum_sdiff h_img_sub, add_comm]
    rw [h_eq]
    have h_nonneg : 0 ≤ ∑ x ∈ P_orig_Q \ P_norm_Q.image g, f x := by
      exact Finset.sum_nonneg (fun _ _ => Nat.zero_le _)
    linarith
  have hfine_sum_le : ∑ p ∈ P_norm_Q, (fineTubes_norm p).card ≤
      ∑ x ∈ P_orig_Q, assignedCountDyadic Δ hΔ_pos T_Q x T0 := by
    calc _ ≤ ∑ p ∈ P_norm_Q, (sq.fineTubes (normOfSheared p)).card := h_sum1
         _ = ∑ p ∈ P_norm_Q, assignedCountDyadic Δ hΔ_pos T_Q (g p) T0 := h_sum2
         _ = ∑ x ∈ P_norm_Q.image g, assignedCountDyadic Δ hΔ_pos T_Q x T0 := h_sum3
         _ ≤ ∑ x ∈ P_orig_Q, assignedCountDyadic Δ hΔ_pos T_Q x T0 := h_sum4

  have hPi_Q_delta_bounds' : Pi_Q ⊆ Set.Icc (-50 * Δ) (50 * Δ) := by
    intro x' hx'
    have hx'2 : x' ∈ (fun x : ℝ => Δ * x + c_Q) '' sq.proj.Pi := by
      rw [←h_Pi_Q_def]; exact hx'
    rcases hx'2 with ⟨x, hx, rfl⟩
    let w := sq.proj.witness x
    have hw_mem : w ∈ sq.P'_Q := sq.proj.h_witness_mem x hx
    have hproj : sq.proj.projFun w = x := sq.proj.h_witness_proj x hx
    let p_orig := sq.originalOfNorm w
    have h_phys : p_orig = Δ • w + z_Q := sq.h_norm_formula w hw_mem
    have h_x'_eq : Δ * x + c_Q = p_orig 0 - σ₀ * p_orig 1 - h₀ := by
      have hproj_eq : sq.proj.projFun w = w 0 - σ₀ * w 1 := by
        have hσ : sq.proj.σ = σ₀ := by rw [sq.proj.hσ_eq] <;> rfl
        have h1 : sq.proj.projFun = affineProj sq.proj.σ := sq.proj.hprojFun
        rw [h1, hσ] <;> rfl
      have h_eq1 : w 0 - σ₀ * w 1 = x :=
        hproj_eq.symm.trans hproj
      have h_phys2 : p_orig 0 - σ₀ * p_orig 1 - h₀ = Δ * (w 0 - σ₀ * w 1) + c_Q := by
        have h_p0 : p_orig 0 = Δ * w 0 + z_Q 0 := by rw [h_phys] <;> simp
        have h_p1 : p_orig 1 = Δ * w 1 + z_Q 1 := by rw [h_phys] <;> simp
        rw [h_p0, h_p1, h_c_Q_def] <;> ring
      have h : Δ * x + c_Q = Δ * (w 0 - σ₀ * w 1) + c_Q := by
        congr 1
        rw [h_eq1]
      rw [h, ←h_phys2]
    simp only
    rw [h_x'_eq]
    have h_card_pos : 0 < (sq.fineTubes w).card := by
      have h1 : 0 < Real.rpow Δ (-s + 40 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have h2 : Real.rpow Δ (-s + 40 * ε) ≤ (sq.fineTubes w).card :=
        sq.hfine_card_lower w hw_mem
      have h3 : (0 : ℝ) < (sq.fineTubes w).card := lt_of_lt_of_le h1 h2
      exact_mod_cast h3
    rcases Finset.card_pos.mp h_card_pos with ⟨T, hT⟩
    let aT := tubeSlope T
    let bT := tubeIntercept T
    have hp_on_T : p_orig ∈ Metric.cthickening (2 * δ) (T.1 : Set Plane) :=
      sq.hfine_inc w hw_mem T hT
    have h_in_parent : InParent Δ hΔ_pos T T0 := by
      have h_pf : sq.fineTubes w = pointFiber Δ hΔ_pos sq.a4.base.T_Q (sq.originalOfNorm w) T0 :=
        sq.hfine_eq_pointFiber w hw_mem
      rw [h_pf] at hT
      exact (Finset.mem_filter.mp hT).2
    have h_slope_diff : |aT - σ₀| < Δ := by
      have h_floor : ⌊aT / Δ⌋ = ⌊tubeSlope T0 / Δ⌋ := congr_arg Prod.fst h_in_parent
      have h_eq : σ₀ = tubeSlope T0 := h_σ₀_def
      rw [h_eq]
      exact abs_sub_lt_of_same_floor hΔ_pos h_floor
    have h_intercept_diff : |bT - h₀| < Δ := by
      have h_floor : ⌊bT / Δ⌋ = ⌊tubeIntercept T0 / Δ⌋ := congr_arg Prod.snd h_in_parent
      have h_eq : h₀ = tubeIntercept T0 := h_h₀_def
      rw [h_eq]
      exact abs_sub_lt_of_same_floor hΔ_pos h_floor
    have hT_slope_bound : |aT| ≤ 1 := (sq.h_tube_param_bounds w hw_mem T hT).1
    have hT_intercept_bound : |bT| ≤ 3 := (sq.h_tube_param_bounds w hw_mem T hT).2
    have hT_dirV : (LemmaE.getDirV T) 1 ≠ 0 := sq.h_dirV_nonzero w hw_mem T hT
    have hp_in_PQ : p_orig ∈ sq.a4.base.P_Q := sq.h_originalOfNorm w hw_mem
    have hp_in_ball : ‖p_orig‖ ≤ Real.sqrt 2 := by
      simpa [Metric.mem_closedBall] using sq.a4.base.hP_Q_in_ball hp_in_PQ
    have hpy_abs : |p_orig 1| ≤ Real.sqrt 2 := by
      have h_norm_sq : ‖p_orig‖ ^ 2 = (p_orig 0) ^ 2 + (p_orig 1) ^ 2 := by
        have h3 : ‖p_orig‖ = Real.sqrt ((p_orig 0) ^ 2 + (p_orig 1) ^ 2) := by
          rw [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> simp
        rw [h3]
        rw [Real.sq_sqrt (by positivity)] <;> ring
      have h2 : (p_orig 1) ^ 2 ≤ ‖p_orig‖ ^ 2 := by
        rw [h_norm_sq] <;> simp [Fin.sum_univ_two] <;> positivity
      have h3 : (|p_orig 1|) ^ 2 ≤ (‖p_orig‖) ^ 2 := by
        have h4 : (|p_orig 1|) ^ 2 = (p_orig 1) ^ 2 := by simp [sq_abs]
        rw [h4] <;> exact h2
      have h4 : |p_orig 1| ≤ ‖p_orig‖ := by
        nlinarith [sq_abs (p_orig 1), norm_nonneg p_orig]
      linarith
    have hT0_eq : T0 = a8.a7.T0 := a8.hT0_norm_eq
    have hσ0_bound : |σ₀| ≤ 1 := by
      have h4 : |tubeSlope a8.a7.T0| ≤ 1 := a8.a7.hT0_slope_bound
      have h5 : σ₀ = tubeSlope a8.a7.T0 := by rw [h_σ₀_def, hT0_eq]
      rw [h5]; exact h4
    have h0_bound : |h₀| ≤ 3 := by
      have h4 : |tubeIntercept a8.a7.T0| ≤ 3 := a8.a7.hT0_intercept_bound
      have h5 : h₀ = tubeIntercept a8.a7.T0 := by rw [h_h₀_def, hT0_eq]
      rw [h5]; exact h4
    have hT0_dirV : (LemmaE.getDirV T0) 1 ≠ 0 := by
      rw [hT0_eq]; exact a8.a7.hT0_dirV_nonzero
    have hδ_nonneg : 0 ≤ δ := by rw [hδ_eq] <;> positivity
    have h_res_T : |p_orig 0 - aT * p_orig 1 - bT| ≤ Real.sqrt 2 * (2 * δ) := by
      have h1 := residual_from_cthickening_local p_orig T (2 * δ) (by positivity) hT_dirV hp_on_T
      have h2 : Real.sqrt (1 + aT ^ 2) ≤ Real.sqrt 2 := by
        have h3 : 1 + aT ^ 2 ≤ 2 := by
          have h4 : |aT| ≤ 1 := hT_slope_bound
          have h5 : aT ^ 2 ≤ 1 := by
            have h6 : aT ^ 2 = |aT| ^ 2 := by simp [sq_abs]
            rw [h6]
            have h7 : |aT| ^ 2 ≤ 1 ^ 2 := by gcongr
            simpa using h7
          linarith
        exact Real.sqrt_le_sqrt h3
      calc |p_orig 0 - aT * p_orig 1 - bT|
        ≤ Real.sqrt (1 + aT ^ 2) * (2 * δ) := h1
      _ ≤ Real.sqrt 2 * (2 * δ) := by gcongr
    have h_da : |aT - σ₀| ≤ Δ := h_slope_diff.le
    have h_db : |bT - h₀| ≤ Δ := h_intercept_diff.le
    have h_main : |p_orig 0 - σ₀ * p_orig 1 - h₀| ≤
        |p_orig 0 - aT * p_orig 1 - bT| + |aT - σ₀| * |p_orig 1| + |bT - h₀| := by
      calc |p_orig 0 - σ₀ * p_orig 1 - h₀|
        = |(p_orig 0 - aT * p_orig 1 - bT) + (aT - σ₀) * p_orig 1 + (bT - h₀)| := by ring_nf
      _ ≤ |p_orig 0 - aT * p_orig 1 - bT| + |(aT - σ₀) * p_orig 1| + |bT - h₀| := by
        have h : |(p_orig 0 - aT * p_orig 1 - bT) + ((aT - σ₀) * p_orig 1) + (bT - h₀)| ≤
            |p_orig 0 - aT * p_orig 1 - bT| + |(aT - σ₀) * p_orig 1| + |bT - h₀| := by
          calc |(p_orig 0 - aT * p_orig 1 - bT) + ((aT - σ₀) * p_orig 1) + (bT - h₀)|
            = |((p_orig 0 - aT * p_orig 1 - bT) + (aT - σ₀) * p_orig 1) + (bT - h₀)| := by ring
          _ ≤ |(p_orig 0 - aT * p_orig 1 - bT) + (aT - σ₀) * p_orig 1| + |bT - h₀| := abs_add_le _ _
          _ ≤ |p_orig 0 - aT * p_orig 1 - bT| + |(aT - σ₀) * p_orig 1| + |bT - h₀| := by
            gcongr
            <;> exact abs_add_le _ _
        exact h
      _ = |p_orig 0 - aT * p_orig 1 - bT| + |aT - σ₀| * |p_orig 1| + |bT - h₀| := by simp [abs_mul] <;> ring
    have hδ_le_half : δ ≤ Δ := by
      rw [hδ_eq]
      have h1 : Δ < 1 := by linarith
      have h2 : Δ ^ 2 ≤ Δ := by
        calc Δ ^ 2 = Δ * Δ := by ring
          _ ≤ Δ * 1 := by gcongr <;> linarith
          _ = Δ := by ring
      exact h2
    have h_term1 : |aT - σ₀| * |p_orig 1| ≤ 6 * Real.sqrt 2 * Δ := by
      have h1 : |aT - σ₀| ≤ Δ := h_da
      have h2 : |p_orig 1| ≤ Real.sqrt 2 := hpy_abs
      have h3 : |aT - σ₀| * |p_orig 1| ≤ Δ * Real.sqrt 2 :=
        mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
      have h4 : Δ * Real.sqrt 2 ≤ 6 * Real.sqrt 2 * Δ := by
        have h5 : 0 ≤ Δ * Real.sqrt 2 := by positivity
        have h6 : Δ * Real.sqrt 2 ≤ 6 * (Δ * Real.sqrt 2) := by
          exact le_mul_of_one_le_left h5 (by norm_num)
        ring_nf at h6 ⊢ <;> exact h6
      exact le_trans h3 h4
    have h_bound_raw : |p_orig 0 - σ₀ * p_orig 1 - h₀| ≤
        Real.sqrt 2 * (2 * δ) + 6 * Real.sqrt 2 * Δ + 6 * Δ := by
      calc |p_orig 0 - σ₀ * p_orig 1 - h₀|
        ≤ |p_orig 0 - aT * p_orig 1 - bT| + |aT - σ₀| * |p_orig 1| + |bT - h₀| := h_main
      _ ≤ Real.sqrt 2 * (2 * δ) + 6 * Real.sqrt 2 * Δ + 6 * Δ := by linarith [h_res_T, h_term1, h_db]
    have h_bound : |p_orig 0 - σ₀ * p_orig 1 - h₀| ≤
        8 * Real.sqrt 2 * Δ + 6 * Δ := by
      have h10 : Real.sqrt 2 * (2 * δ) ≤ Real.sqrt 2 * (2 * Δ) := by
        gcongr <;> linarith
      have h11 : Real.sqrt 2 * (2 * δ) + 6 * Real.sqrt 2 * Δ + 6 * Δ ≤
          Real.sqrt 2 * (2 * Δ) + 6 * Real.sqrt 2 * Δ + 6 * Δ := by linarith
      have h12 : Real.sqrt 2 * (2 * Δ) + 6 * Real.sqrt 2 * Δ + 6 * Δ =
          8 * Real.sqrt 2 * Δ + 6 * Δ := by ring
      linarith
    have h_sqrt2_le_2 : Real.sqrt 2 ≤ 2 := by
      have h_nonneg : 0 ≤ (2 : ℝ) := by norm_num
      have hsq : (2 : ℝ) ≤ (2 : ℝ) ^ 2 := by norm_num
      exact Real.sqrt_le_iff.mpr ⟨h_nonneg, hsq⟩
    have h_final : |p_orig 0 - σ₀ * p_orig 1 - h₀| ≤ 50 * Δ := by
      calc |p_orig 0 - σ₀ * p_orig 1 - h₀|
        ≤ 8 * Real.sqrt 2 * Δ + 6 * Δ := h_bound
      _ ≤ 8 * 2 * Δ + 6 * Δ := by gcongr <;> exact h_sqrt2_le_2
      _ = 22 * Δ := by ring
      _ ≤ 50 * Δ := by linarith
    have h_final' : -50 * Δ ≤ p_orig 0 - σ₀ * p_orig 1 - h₀ ∧ p_orig 0 - σ₀ * p_orig 1 - h₀ ≤ 50 * Δ := by
      have h := abs_le.mp h_final
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    exact ⟨h_final'.1, h_final'.2⟩

  -- Define proofs before structure literal to avoid field-name shadowing
  have hfineTube_cond_local : ∀ p ∈ P_norm_Q, ∀ cell ∈ fineTubes_norm p,
      (LemmaE.getDirV (fineTubeOfCell p cell)) 1 ≠ 0 ∧
      |tubeSlope (fineTubeOfCell p cell)| ≤ 1 ∧
      |tubeIntercept (fineTubeOfCell p cell)| ≤ 3 := by
    intro p hp cell hcell
    have h_v1 : (LemmaE.getDirV (fineTubeOfCell p cell)) 1 ≠ 0 :=
      makeAffineLine_v1 (paramsOfDyadicCell δ cell).1 (paramsOfDyadicCell δ cell).2
    have h_slope_eq : tubeSlope (fineTubeOfCell p cell) = (paramsOfDyadicCell δ cell).1 := by
      rw [h_fineTubeOfCell_def p cell]
      have h2 := makeAffineLine_params (paramsOfDyadicCell δ cell).1 (paramsOfDyadicCell δ cell).2
      simp [tubeSlope, h2] <;> rfl
    have h_intercept_eq : tubeIntercept (fineTubeOfCell p cell) = (paramsOfDyadicCell δ cell).2 := by
      rw [h_fineTubeOfCell_def p cell]
      have h2 := makeAffineLine_params (paramsOfDyadicCell δ cell).1 (paramsOfDyadicCell δ cell).2
      simp [tubeIntercept, h2] <;> rfl
    have h_bounds := hfine_cell_bounds p hp cell hcell
    exact ⟨h_v1,
      by rw [h_slope_eq] <;> linarith [hΔ_small, h_bounds.1],
      by rw [h_intercept_eq] <;> linarith [hΔ_small, h_bounds.2]⟩
  have hfineTube_params_local : ∀ p ∈ P_norm_Q, ∀ cell ∈ fineTubes_norm p,
      tubeSlope (fineTubeOfCell p cell) = (paramsOfDyadicCell δ cell).1 ∧
      tubeIntercept (fineTubeOfCell p cell) = (paramsOfDyadicCell δ cell).2 := by
    intro p hp cell hcell
    have h_slope_eq : tubeSlope (fineTubeOfCell p cell) = (paramsOfDyadicCell δ cell).1 := by
      rw [h_fineTubeOfCell_def p cell]
      have h2 := makeAffineLine_params (paramsOfDyadicCell δ cell).1 (paramsOfDyadicCell δ cell).2
      simp [tubeSlope, h2] <;> rfl
    have h_intercept_eq : tubeIntercept (fineTubeOfCell p cell) = (paramsOfDyadicCell δ cell).2 := by
      rw [h_fineTubeOfCell_def p cell]
      have h2 := makeAffineLine_params (paramsOfDyadicCell δ cell).1 (paramsOfDyadicCell δ cell).2
      simp [tubeIntercept, h2] <;> rfl
    exact ⟨h_slope_eq, h_intercept_eq⟩

  exact
    { x_Q := x_Q
      y_Q := y_Q
      hx_Q_eq := hx_Q_eq
      hy_Q_eq := hy_Q_eq
      hy_Q_bounds := hy_Q_bounds
      unnormalize := fun p => sq.originalOfNorm (normOfSheared p)
      P_phys := P_orig_Q
      hP_phys_sub := by
        have h_sub : (P_orig_Q : Set Plane) ⊆ squareSet Δ Q := hP_phys_sub
        intro p hp
        have h5 : p ∈ squareSet Δ Q := h_sub hp
        have h_dist : dist p p ≤ 2 * Δ := by
          rw [dist_self]
          have h : 0 ≤ 2 * Δ := by positivity
          exact h
        exact Metric.mem_cthickening_of_dist_le p p (2 * Δ) (squareSet Δ Q) h5 h_dist
      hP_phys_card := hP_phys_card
      P_norm_Q := P_norm_Q
      hP_norm_Q_card := phase1.hP_norm_Q_card
      hP_norm_Q_card_upper := by
        have h2 : (P_norm_Q.card : ℝ) = (P_orig_Q.card : ℝ) := phase1.hP_norm_Q_card
        have h3 : (P_orig_Q.card : ℝ) = (sq.P'_Q.card : ℝ) := phase1.hP_orig_Q_card
        rw [h2, h3]
        exact sq.hP'_Q_card_upper
      squareIndex := squareIndex
      hP_in_square := hP_in_square
      fineTubes_norm := fineTubes_norm
      fineTubeOfCell := fineTubeOfCell
      hfine_card_lower := hfine_card_lower
      hfine_card_upper := hfine_card_upper
      Pi_Q := Pi_Q
      hPi_Q_sset := hPi_Q_sset
      hPi_Q_bounds := hPi_Q_bounds
      hPi_Q_delta_bounds := hPi_Q_delta_bounds'
      witness := witness
      h_witness := h_witness
      h_witness_y_close := h_witness_y_close
      h_residual := h_residual
      hfine_cell_bounds := hfine_cell_bounds
      hfineTube_cond := hfineTube_cond_local
      hfineTube_params := hfineTube_params_local
      Pi_Q_norm := sq.proj.Pi
      hPi_Q_norm_sset := sq.proj.hPi_sset
      c_Q := c_Q
      hPi_Q_rel := by
        have h_eq : Pi_Q = (fun x : ℝ => Δ * x + c_Q) '' sq.proj.Pi := h_Pi_Q_def
        rw [h_eq]
      coarseParams := (fun T : CoarseTube => (tubeSlope T, tubeIntercept T)) '' (sq.a4.C_Q_pi : Set CoarseTube)
      hcoarseParams_sset := coarseParams_sset_bound Δ δ s t ε Q hΔ_pos (by linarith) hs1 hε_pos hΔ_coarse_absorb sq.a4
      C_fine_resc := C_fine_resc
      hC_fine_resc_pos := hC_fine_resc_pos
      hC_fine_resc_le_499 := hC_fine_resc_le_499
      hfine_rescalable_prod := by
        intro p hp
        set p_norm := normOfSheared p with hp_norm_def
        have hp_norm : p_norm ∈ sq.P'_Q := h_norm_mem p hp
        let Tubes : Set FineTube := (sq.fineTubes p_norm : Set FineTube)
        let v : ℝ × ℝ := (-σ₀, -h₀)
        let snap : ℝ × ℝ → ℝ × ℝ := fun x => (δ * ⌊x.1 / δ⌋, δ * ⌊x.2 / δ⌋)
        have hT_sset : IsDeltaSSet δ s C_fine Tubes :=
          sq.hfine_tubes_sset p_norm hp_norm
        have h_bounds : ∀ T ∈ Tubes,
            (LemmaE.getDirV T) 1 ≠ 0 ∧
            |(LemmaE.affineLineParams T).1| ≤ 1 ∧
            |(LemmaE.affineLineParams T).2| ≤ 3 := by
          intro T hT
          exact ⟨sq.h_dirV_nonzero p_norm hp_norm T hT,
            (sq.h_tube_param_bounds p_norm hp_norm T hT).1,
            (sq.h_tube_param_bounds p_norm hp_norm T hT).2⟩
        have hsnap : ∀ (x : ℝ × ℝ), dist x (snap x) ≤ δ :=
          fun x => snap_to_grid_dist_le δ hδ_pos x
        have h_main : IsRescalableDeltaSet δ Δ s C_fine_resc
            (snap '' ((fun x : ℝ × ℝ => x + v) '' (LemmaE.affineLineParams '' Tubes))) :=
          A10.fine_tube_sset_to_cell_rescalable hT_sset h_bounds v snap hsnap hδ_pos hΔ_pos hδ_eq (by linarith)
        rw [← h_set_eq p hp]
        exact h_main
      T_Q := sq.a4.base.T_Q
      T0 := a8.a7.T0
      hΔ_pos := hΔ_pos
      hδ_pos := hδ_pos
      σ₀ := σ₀
      h₀ := h₀
      hT_Q_eq := by rfl
      hσ₀_eq_T0 := congr_arg tubeSlope a8.hT0_norm_eq
      hh₀_eq_T0 := congr_arg tubeIntercept a8.hT0_norm_eq
      hfine_sum_le := by
        have hT0_eq : T0 = a8.a7.T0 := a8.hT0_norm_eq
        exact hT0_eq ▸ hfine_sum_le
      hfine_cell_origin := by
        intro p hp cell hcell
        have h_fine_def : fineTubes_norm p = (sq.fineTubes (normOfSheared p)).image f_cell :=
          h_fine_def p hp
        rw [h_fine_def] at hcell
        rcases Finset.mem_image.mp hcell with ⟨T, hT_in_fine, rfl⟩
        have hp_norm : normOfSheared p ∈ sq.P'_Q := h_norm_mem p hp
        have h_eq : sq.fineTubes (normOfSheared p) =
            pointFiber Δ hΔ_pos sq.a4.base.T_Q (sq.originalOfNorm (normOfSheared p)) T0 :=
          sq.hfine_eq_pointFiber (normOfSheared p) hp_norm
        rw [h_eq] at hT_in_fine
        have hT_in_TQ : T ∈ sq.a4.base.T_Q (sq.originalOfNorm (normOfSheared p)) :=
          (Finset.mem_filter.mp hT_in_fine).1
        have h_in_parent : InParent Δ hΔ_pos T T0 :=
          (Finset.mem_filter.mp hT_in_fine).2
        have h_in_parent' : InParent Δ hΔ_pos T a8.a7.T0 := by
          have hT0_eq : T0 = a8.a7.T0 := a8.hT0_norm_eq
          exact hT0_eq ▸ h_in_parent
        exact ⟨T, hT_in_TQ, h_in_parent', rfl⟩
      a4 := sq.a4
      hunnormalize_in_a4PQ := by
        intro p hp
        have h1 : normOfSheared p ∈ sq.P'_Q := h_norm_mem p hp
        exact sq.h_originalOfNorm (normOfSheared p) h1
      }

end AppendixA
end DirecretisedFurstenbergEstimate
