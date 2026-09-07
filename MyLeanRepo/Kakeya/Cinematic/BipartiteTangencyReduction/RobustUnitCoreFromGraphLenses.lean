import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyInputs
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.RobustUnitCoreHelpers
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.RobustUnitCoreNonoverlap
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.DirectionalFamily
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.LensReparamNonoverlap
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ShiftedPseudoCircleAny
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.IndexedGraphLensCount
import MyLeanRepo.Kakeya.Cinematic.DirectionalLensExistence
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.LensEndpointEnlargementAbsorption
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.UnitTangentRepresentatives

/-!
# Robust unit-multiplicity bipartite tangency from graph lenses

This target contains the geometric heart of PYZ Lemmas 35--38: perturb
tangent pairs to transverse pairs, construct non-overlapping graph lenses,
and apply the Marcus--Tardos lens count.

## Proof outline

1. Promote the finite W ∪ B to an `IsCinematicFamily`.
2. Use finite tangency perturbation + bidirectional shift avoidance to obtain
   `shift0`, `epsilon`, and no-tangency certificates for both directions.
3. Choose one white and one black tangent representative per rectangle.
4. For each rectangle, `directional_lens_existence` yields either an upward
   or a downward graph lens. Partition indices accordingly.
5. For each direction:
   - Build the translated family `F_dir` and transfer no-tangency/shift bounds.
   - Obtain a pseudo-circle family via `shifted_bipartite_pseudo_circle_any`.
   - Widen endpoint localization to the uniform factor `E_abs`.
   - Prove pairwise non-overlap via incomparable rectangles.
   - Reparametrize lenses and transfer non-overlap.
   - Apply the indexed Marcus--Tardos count.
6. Combine the two directional counts.
-/

namespace Kakeya.Cinematic

theorem bipartite_tangency_robust_unit_core_from_graph_lenses :
    BipartiteTangencyRobustUnitCoreFromGraphLensesStatement := by
  intro h_graph_lens_bound _ _ _ _ _ h_pert
  rcases h_graph_lens_bound with ⟨C_mt, hC_mt_pos, h_mt_bound⟩

  intro K hK
  let c₂ : ℝ := 1 / (500 * K ^ 4)
  let C : ℝ := max 100 (max (4 * C_mt) (100000 * K ^ 2))
  have hC1 : 100 ≤ C := le_max_left _ _
  have hC2 : 4 * C_mt ≤ C := by
    have h : 4 * C_mt ≤ max (4 * C_mt) (100000 * K ^ 2) := le_max_left _ _
    exact le_trans h (le_max_right _ _)
  have hC3 : 100000 * K ^ 2 ≤ C := by
    have h : 100000 * K ^ 2 ≤ max (4 * C_mt) (100000 * K ^ 2) := le_max_right _ _
    exact le_trans h (le_max_right _ _)
  have hK_pos : 0 < K := by linarith
  have hc2_pos : 0 < c₂ := by positivity

  refine ⟨c₂, C, hc2_pos, hC1, ?_⟩

  intro tangency htang family hcurv I hI delta t hdelta ht hdelta_le_t _ h_small h_adm
    W B hW hB h_sep R _ hR_central hR_incomp hR_nonempty hcounts

  classical

  let F : FiniteFunctionFamily :=
    { carrier := W.carrier ∪ B.carrier
      finite := W.finite.union B.finite }
  have hF_eq : F.carrier = W.carrier ∪ B.carrier := by rfl

  -- Step 1: finite cinematic family
  have hF_sub : F.carrier ⊆ family := by
    rw [hF_eq]
    exact Set.union_subset hW hB
  rcases finite_cinematic_family hcurv F hF_sub with ⟨D, hD1, hfam⟩

  -- Step 2: perturbation setup
  have hfam' : IsCinematicFamily (W.carrier ∪ B.carrier) K D := by
    rwa [hF_eq] at hfam
  rcases perturbation_setup hK hD1 hI W B (hfam := hfam') (hdelta := hdelta) (htang := htang) h_pert
    with ⟨shift0, epsilon, h_amp, h_pairwise, h_eps_low, h_eps_high, h_no_tang_up, h_no_tang_down⟩

  -- Step 3: unit tangent representatives
  rcases exists_unit_tangent_representatives R W B hcounts with ⟨w_rep, b_rep, hw_rep, hb_rep⟩

  -- Constants
  let V : ℝ := 25 * tangency ^ 10 + 2 * tangency + 2
  let E_abs : ℝ := 12 * K * (V + 1) + Real.sqrt (6 * K * V)
  let Cc : ℝ := C * Real.rpow tangency C

  have hI_short : I.IsShort K := hI.2
  have hI_pos : 0 < I.length := by
    have h : (12 * K)⁻¹ ≤ I.length := hI.1
    have h2 : 0 < (12 * K)⁻¹ := by positivity
    linarith
  have hCc1 : 100 ≤ Cc := unit_core_comparison_ge_hundred hC1 htang
  have hCc_adm : Cc * delta ≤ t := h_adm.2
  have htang_le_Cc : tangency ≤ Cc := tangency_le_unit_core_comparison hC1 htang
  have hE_abs_nonneg : 0 ≤ E_abs := by positivity
  have hE_absorption : (2 + 2 * E_abs) ^ 2 ≤ Cc :=
    lens_endpoint_enlargement_absorption hK htang hC1 hC3

  have hC_ge_50 : (50 : ℝ) ≤ C := by linarith
  have h_tang50_le : (tangency ^ 50 : ℝ) ≤ Real.rpow tangency C := by
    have h2 : (1 : ℝ) ≤ tangency := by linarith
    have h3 : Real.rpow tangency (50 : ℝ) ≤ Real.rpow tangency C :=
      Real.rpow_le_rpow_of_exponent_le h2 hC_ge_50
    have h4 : (tangency ^ 50 : ℝ) = Real.rpow tangency (50 : ℝ) := by simp
    rw [h4]
    exact h3
  have h_small50 : tangency ^ 50 * delta ≤ t / (1000 * K ^ 4) := by
    have h3 : (tangency ^ 50 : ℝ) * delta ≤ Real.rpow tangency C * delta := by
      gcongr
    have h4 : Real.rpow tangency C * delta ≤ c₂ * t / 2 := h_small
    have h5 : c₂ * t / 2 = t / (1000 * K ^ 4) := by
      dsimp only [c₂]
      field_simp [hK_pos.ne'] <;> ring
    have h6 : Real.rpow tangency C * delta ≤ t / (1000 * K ^ 4) := by
      rw [h5] at h4
      exact h4
    exact h3.trans h6
  have h_small2 : tangency ^ 50 * delta ≤ t / (1000 * K ^ 2) := by
    have h7 : (1000 * K ^ 2 : ℝ) ≤ (1000 * K ^ 4 : ℝ) := by
      have h8 : K ^ 2 ≤ K ^ 4 := by
        exact pow_le_pow_right₀ (by linarith) (by norm_num)
      nlinarith
    have h9 : t / (1000 * K ^ 4) ≤ t / (1000 * K ^ 2) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) h7
    exact h_small50.trans h9

  let shiftUp : C2Function → ℝ := fun f =>
    if f ∈ W.toFinset then epsilon + shift0 f else shift0 f
  let shiftDown : C2Function → ℝ := fun f =>
    if f ∈ W.toFinset then -epsilon + shift0 f else shift0 f

  let d (i : Fin R.card) : ℝ := c2Distance (w_rep i) (b_rep i)
  let curvature (i : Fin R.card) : ℝ := d i / (6 * K * t)
  let E_lens (i : Fin R.card) : ℝ :=
    2 * (2 * V + d i / t) / curvature i + Real.sqrt (2 * V / curvature i)

  have h_sep_i : ∀ i, 2 * t ≤ d i := by
    intro i
    exact h_sep (hw_rep i).1 (hb_rep i).1

  have h_wb_ne : ∀ i, w_rep i ≠ b_rep i := by
    intro i
    intro h
    have h0 : 2 * t ≤ d i := h_sep_i i
    dsimp only [d] at h0
    rw [h] at h0
    have h1 : c2Distance (b_rep i) (b_rep i) = 0 := by
      rw [c2Distance_eq_dist, dist_self]
    rw [h1] at h0
    have h2 : 0 < 2 * t := by linarith [ht]
    exact False.elim (not_le.mpr h2 h0)

  have hW_toFinset : ∀ i, w_rep i ∈ W.toFinset := fun i =>
    W.finite.mem_toFinset.mpr (hw_rep i).1
  have hB_notin_W : ∀ i, b_rep i ∉ W.toFinset := fun i => by
    intro h
    have h_in_W : b_rep i ∈ W.carrier := W.finite.mem_toFinset.mp h
    have h_in_B : b_rep i ∈ B.carrier := (hb_rep i).1
    have h_contra : 2 * t ≤ c2Distance (b_rep i) (b_rep i) := h_sep h_in_W h_in_B
    rw [c2Distance_eq_dist, dist_self] at h_contra
    linarith

  -- Define directional lens propositions
  let P_up (i : Fin R.card) : Prop :=
    ∃ (L : GraphLens),
      L.left ∈ I.carrier ∧ L.right ∈ I.carrier ∧
      (L.left : ℝ) ∈ Set.Icc ((R.rectangle i).interval.left - E_lens i * Real.sqrt (delta / t))
                                  ((R.rectangle i).interval.right + E_lens i * Real.sqrt (delta / t)) ∧
      (L.right : ℝ) ∈ Set.Icc ((R.rectangle i).interval.left - E_lens i * Real.sqrt (delta / t))
                                   ((R.rectangle i).interval.right + E_lens i * Real.sqrt (delta / t)) ∧
      L.f = (w_rep i).verticalTranslate (epsilon + shift0 (w_rep i)) ∧
      L.g = (b_rep i).verticalTranslate (shift0 (b_rep i))

  let P_down (i : Fin R.card) : Prop :=
    ∃ (L : GraphLens),
      L.left ∈ I.carrier ∧ L.right ∈ I.carrier ∧
      (L.left : ℝ) ∈ Set.Icc ((R.rectangle i).interval.left - E_lens i * Real.sqrt (delta / t))
                                  ((R.rectangle i).interval.right + E_lens i * Real.sqrt (delta / t)) ∧
      (L.right : ℝ) ∈ Set.Icc ((R.rectangle i).interval.left - E_lens i * Real.sqrt (delta / t))
                                   ((R.rectangle i).interval.right + E_lens i * Real.sqrt (delta / t)) ∧
      L.f = (w_rep i).verticalTranslate (-epsilon + shift0 (w_rep i)) ∧
      L.g = (b_rep i).verticalTranslate (shift0 (b_rep i))

  have h_dir : ∀ i, P_up i ∨ P_down i := by
    intro i
    exact directional_lens_existence hK htang hdelta ht hdelta_le_t h_small50 hcurv
      (h_wb_ne i)
      (hW (hw_rep i).1) (hB (hb_rep i).1) (h_sep_i i)
      (R.rectangle i) (hw_rep i).2 (hb_rep i).2 I hI (hR_central i)
      epsilon h_eps_low h_eps_high
      (shift0 (w_rep i)) (shift0 (b_rep i))
      (h_amp (w_rep i) (by rw [hF_eq]; exact Or.inl (hw_rep i).1))
      (h_amp (b_rep i) (by rw [hF_eq]; exact Or.inr (hb_rep i).1))

  let S_up : Finset (Fin R.card) := Finset.univ.filter P_up
  let S_down : Finset (Fin R.card) := Finset.univ.filter (fun i => ¬P_up i)

  have h_partition1 : S_up ∪ S_down = Finset.univ := by
    ext i; simp [S_up, S_down] <;> tauto
  have h_partition2 : Disjoint S_up S_down := by
    simp [S_up, S_down, Finset.disjoint_left] <;> tauto
  have h_card_sum : S_up.card + S_down.card = R.card := by
    have h : S_up.card + S_down.card = (S_up ∪ S_down).card := by
      rw [Finset.card_union_of_disjoint h_partition2]
    rw [h, h_partition1]; simp

  choose L_up hL_up using fun (i : {i // i ∈ S_up}) =>
    show P_up i.val from (Finset.mem_filter.mp i.property).2

  choose L_down hL_down using fun (i : {i // i ∈ S_down}) =>
    have hnp : ¬P_up i.val := (Finset.mem_filter.mp i.property).2
    have hpd : P_down i.val := (h_dir i.val).resolve_left hnp
    hpd

  -- Extend lenses to all indices for the non-overlap lemma
  let L_up_all : Fin R.card → GraphLens := fun i =>
    if h : i ∈ S_up then L_up ⟨i, h⟩
    else
      have hnp : ¬P_up i := by
        simpa [S_up, Finset.mem_filter] using h
      have hdown : i ∈ S_down := by
        simp [S_down, Finset.mem_filter, hnp]
      L_down ⟨i, hdown⟩
  let L_down_all : Fin R.card → GraphLens := L_up_all

  -- Widen endpoints for up lenses
  have h_up_E_abs : ∀ i ∈ S_up,
      ((L_up_all i).left : ℝ) ∈ Set.Icc ((R.rectangle i).interval.left - E_abs * Real.sqrt (delta / t))
                                      ((R.rectangle i).interval.right + E_abs * Real.sqrt (delta / t)) ∧
      ((L_up_all i).right : ℝ) ∈ Set.Icc ((R.rectangle i).interval.left - E_abs * Real.sqrt (delta / t))
                                       ((R.rectangle i).interval.right + E_abs * Real.sqrt (delta / t)) := by
    intro i hi
    have h_eq : L_up_all i = L_up ⟨i, hi⟩ := by
      simp [L_up_all, hi]
    rw [h_eq]
    have h := hL_up ⟨i, hi⟩
    exact widen_lens_endpoints hK htang hdelta ht (h_sep_i i)
      V E_abs (E_lens i) rfl rfl rfl h.2.2.1 h.2.2.2.1

  -- Widen endpoints for down lenses
  have h_down_E_abs : ∀ i ∈ S_down,
      ((L_down_all i).left : ℝ) ∈ Set.Icc ((R.rectangle i).interval.left - E_abs * Real.sqrt (delta / t))
                                      ((R.rectangle i).interval.right + E_abs * Real.sqrt (delta / t)) ∧
      ((L_down_all i).right : ℝ) ∈ Set.Icc ((R.rectangle i).interval.left - E_abs * Real.sqrt (delta / t))
                                       ((R.rectangle i).interval.right + E_abs * Real.sqrt (delta / t)) := by
    intro i hi
    have hnp : i ∉ S_up :=
      Finset.disjoint_right.mp h_partition2 hi
    have h_eq : L_down_all i = L_down ⟨i, hi⟩ := by
      simp [L_down_all, L_up_all, hnp]
    rw [h_eq]
    have h := hL_down ⟨i, hi⟩
    exact widen_lens_endpoints hK htang hdelta ht (h_sep_i i)
      V E_abs (E_lens i) rfl rfl rfl h.2.2.1 h.2.2.2.1

  -- Shift sum bound
  have h_eps_pos : 0 < epsilon := by
    have h_pos : 0 < (2 * tangency + 2) * delta := by positivity
    linarith [h_eps_low]
  have h_eps_nonneg : 0 ≤ epsilon := le_of_lt h_eps_pos
  have h_shift_sum : epsilon + 2 * delta < t / (3 * K) :=
    shift_sum_lt_dist_sixth (delta' := delta) hK htang hdelta ht h_small2 epsilon
      h_eps_nonneg h_eps_high (le_of_lt hdelta) (le_refl delta)
  have h_eps_lt_t : epsilon + 2 * delta < t := by
    have h7 : t / (3 * K) < t := by
      have h8 : 1 < 3 * K := by linarith
      exact div_lt_self ht h8
    linarith

  -- ======================================================================
  -- UP DIRECTION
  -- ======================================================================
  rcases directional_family hK W B F hF_eq shift0 hdelta ht htang h_small2 h_sep
      (by have h : |epsilon| = epsilon := abs_of_nonneg h_eps_nonneg
          rw [h]; exact h_eps_high)
      h_amp h_pairwise h_no_tang_up
    with ⟨F_up, shift_up', hF_up_W, hF_up_W', hF_up_B, h_amp_up, h_pairwise_up, h_shift'_W_up, h_shift'_B_up, h_no_tang_up'⟩

  let curves_up : Finset C2Function :=
    F_up.toFinset.image (fun f => (f.verticalTranslate (shift_up' f)).reparam I)

  have h_pseudo_up : IsGraphPseudoCircleFamily curves_up :=
    shifted_bipartite_pseudo_circle_any hK hD1 hfam hI_short hI_pos
      (show W.carrier ⊆ F.carrier from by simp [hF_eq])
      (show B.carrier ⊆ F.carrier from by simp [hF_eq])
      hdelta ht htang h_small2 h_sep
      (by have h : |epsilon| = epsilon := abs_of_nonneg h_eps_nonneg
          rw [h]; exact h_eps_high)
      F_up hF_up_W hF_up_W' h_amp_up h_pairwise_up h_no_tang_up'

  -- Reparametrized up lenses
  let L_up' : {i // i ∈ S_up} → GraphLens := fun i =>
    (L_up i).reparam I hI_pos (hL_up i).1 (hL_up i).2.1

  -- Sides in curves_up
  have h_sides_up : ∀ (i : {i // i ∈ S_up}),
      (L_up' i).f ∈ curves_up ∧ (L_up' i).g ∈ curves_up := by
    intro i
    let idx := i.val
    have hwf : (w_rep idx).verticalTranslate epsilon ∈ F_up.carrier := hF_up_W' (w_rep idx) (hw_rep idx).1
    have hbf : b_rep idx ∈ F_up.carrier := hF_up_B (b_rep idx) (hb_rep idx).1
    let f1 := (w_rep idx).verticalTranslate epsilon
    let g1 := b_rep idx
    have hsf : shift_up' f1 = shift0 (w_rep idx) := h_shift'_W_up (w_rep idx) (hw_rep idx).1
    have hsg : shift_up' g1 = shift0 (b_rep idx) := h_shift'_B_up (b_rep idx) (hb_rep idx).1
    have hL_f : (L_up i).f = (w_rep idx).verticalTranslate (epsilon + shift0 (w_rep idx)) := (hL_up i).2.2.2.2.1
    have hL_g : (L_up i).g = (b_rep idx).verticalTranslate (shift0 (b_rep idx)) := (hL_up i).2.2.2.2.2
    have h_eq_f : (L_up i).f = f1.verticalTranslate (shift_up' f1) := by
      rw [hL_f, hsf]
      <;> rw [verticalTranslate_compose] <;> ring
    have h_eq_g : (L_up i).g = g1.verticalTranslate (shift_up' g1) := by
      rw [hL_g, hsg]
    have h1 : (L_up' i).f = (f1.verticalTranslate (shift_up' f1)).reparam I := by
      have h : (L_up' i).f = (L_up i).f.reparam I := by rfl
      rw [h, h_eq_f]
    have h2 : (L_up' i).g = (g1.verticalTranslate (shift_up' g1)).reparam I := by
      have h : (L_up' i).g = (L_up i).g.reparam I := by rfl
      rw [h, h_eq_g]
    constructor
    · rw [h1]; exact Finset.mem_image.mpr ⟨f1, F_up.finite.mem_toFinset.mpr hwf, rfl⟩
    · rw [h2]; exact Finset.mem_image.mpr ⟨g1, F_up.finite.mem_toFinset.mpr hbf, rfl⟩

  -- No-cross up
  have h_no_cross_up : ∀ i ∈ S_up, ∀ j ∈ S_up, (L_up_all i).f ≠ (L_up_all j).g := by
    intro i hi j hj
    have h_eq_f : (L_up_all i).f = (w_rep i).verticalTranslate (epsilon + shift0 (w_rep i)) := by
      have h : L_up_all i = L_up ⟨i, hi⟩ := by simp [L_up_all, hi]
      rw [h]; exact (hL_up ⟨i, hi⟩).2.2.2.2.1
    have h_eq_g : (L_up_all j).g = (b_rep j).verticalTranslate (shift0 (b_rep j)) := by
      have h : L_up_all j = L_up ⟨j, hj⟩ := by simp [L_up_all, hj]
      rw [h]; exact (hL_up ⟨j, hj⟩).2.2.2.2.2
    rw [h_eq_f, h_eq_g]
    intro h_eq
    have h9 : c2Distance (w_rep i) (b_rep j) ≤ epsilon + 2 * delta := by
      calc
        c2Distance (w_rep i) (b_rep j)
          ≤ c2Distance (w_rep i) ((w_rep i).verticalTranslate (epsilon + shift0 (w_rep i)))
            + c2Distance ((w_rep i).verticalTranslate (epsilon + shift0 (w_rep i))) ((b_rep j).verticalTranslate (shift0 (b_rep j)))
            + c2Distance ((b_rep j).verticalTranslate (shift0 (b_rep j))) (b_rep j) := by
          exact dist_triangle4 _ _ _ _
        _ = |epsilon + shift0 (w_rep i)| + 0 + |shift0 (b_rep j)| := by
          have h_first : c2Distance (w_rep i) ((w_rep i).verticalTranslate (epsilon + shift0 (w_rep i))) = |epsilon + shift0 (w_rep i)| :=
            c2Distance_verticalTranslate_self _ _
          have h_middle : c2Distance ((w_rep i).verticalTranslate (epsilon + shift0 (w_rep i))) ((b_rep j).verticalTranslate (shift0 (b_rep j))) = 0 := by
            rw [h_eq, c2Distance_eq_dist, dist_self]
          have h_third : c2Distance ((b_rep j).verticalTranslate (shift0 (b_rep j))) (b_rep j) = |shift0 (b_rep j)| := by
            rw [c2Distance_eq_dist, dist_comm]
            exact c2Distance_verticalTranslate_self _ _
          rw [h_first, h_middle, h_third] <;> ring
        _ ≤ epsilon + delta + delta := by
          have h10 : |epsilon + shift0 (w_rep i)| ≤ |epsilon| + |shift0 (w_rep i)| :=
            abs_add_le epsilon (shift0 (w_rep i))
          have h11 : |epsilon| = epsilon := abs_of_nonneg h_eps_nonneg
          have h12 : |shift0 (w_rep i)| ≤ delta := h_amp (w_rep i) (by rw [hF_eq]; exact Or.inl (hw_rep i).1)
          have h13 : |shift0 (b_rep j)| ≤ delta := h_amp (b_rep j) (by rw [hF_eq]; exact Or.inr (hb_rep j).1)
          rw [h11] at h10
          linarith
        _ = epsilon + 2 * delta := by ring
    have h10 : 2 * t ≤ c2Distance (w_rep i) (b_rep j) := h_sep (hw_rep i).1 (hb_rep j).1
    linarith

  have h_vt_zero : ∀ (f : C2Function), f.verticalTranslate (0 : ℝ) = f := by
    intro f
    apply C2Function.toJet_injective
    dsimp only [C2Function.toJet]
    apply Prod.ext
    · ext x
      change (f.verticalTranslate (0 : ℝ)) x = f x
      simp [verticalTranslate_apply]
    · apply Prod.ext <;> rfl

  -- Common f-side up
  have h_f_common_up : ∀ i ∈ S_up, ∀ j ∈ S_up,
      (L_up_all i).f = (L_up_all j).f →
      ∃ w : C2Function, w ∈ family ∧
        (R.rectangle i).IsLambdaTangent w tangency ∧
        (R.rectangle j).IsLambdaTangent w tangency := by
    intro i hi j hj h_eq
    have h1 : (L_up_all i).f = (w_rep i).verticalTranslate (epsilon + shift0 (w_rep i)) := by
      have h : L_up_all i = L_up ⟨i, hi⟩ := by simp [L_up_all, hi]
      rw [h]; exact (hL_up ⟨i, hi⟩).2.2.2.2.1
    have h2 : (L_up_all j).f = (w_rep j).verticalTranslate (epsilon + shift0 (w_rep j)) := by
      have h : L_up_all j = L_up ⟨j, hj⟩ := by simp [L_up_all, hj]
      rw [h]; exact (hL_up ⟨j, hj⟩).2.2.2.2.1
    have h3 : (w_rep i).verticalTranslate (epsilon + shift0 (w_rep i)) = (w_rep j).verticalTranslate (epsilon + shift0 (w_rep j)) := by
      rw [←h1, h_eq, h2]
    by_cases h4 : w_rep i = w_rep j
    · have h5 : (R.rectangle j).IsLambdaTangent (w_rep i) tangency := by
        rw [h4]
        exact (hw_rep j).2
      exact ⟨w_rep i, hW (hw_rep i).1, (hw_rep i).2, h5⟩
    · let f1 := (w_rep i).verticalTranslate epsilon
      let f2 := (w_rep j).verticalTranslate epsilon
      have hf1 : f1 ∈ F_up.carrier := hF_up_W' (w_rep i) (hw_rep i).1
      have hf2 : f2 ∈ F_up.carrier := hF_up_W' (w_rep j) (hw_rep j).1
      have hne_f : f1 ≠ f2 := by
        intro h_eq_f
        have h1 : f1.verticalTranslate (-epsilon) = f2.verticalTranslate (-epsilon) := by rw [h_eq_f]
        have h2a : f1.verticalTranslate (-epsilon) = w_rep i := by
          rw [verticalTranslate_compose]
          have h_sum : epsilon + (-epsilon) = (0 : ℝ) := by ring
          rw [h_sum]
          exact h_vt_zero (w_rep i)
        have h2b : f2.verticalTranslate (-epsilon) = w_rep j := by
          rw [verticalTranslate_compose]
          have h_sum : epsilon + (-epsilon) = (0 : ℝ) := by ring
          rw [h_sum]
          exact h_vt_zero (w_rep j)
        rw [h2a, h2b] at h1
        exact h4 h1
      have h_eq' : f1.verticalTranslate (shift_up' f1) = f2.verticalTranslate (shift_up' f2) := by
        have hs1 : shift_up' f1 = shift0 (w_rep i) := h_shift'_W_up (w_rep i) (hw_rep i).1
        have hs2 : shift_up' f2 = shift0 (w_rep j) := h_shift'_W_up (w_rep j) (hw_rep j).1
        rw [hs1, hs2, verticalTranslate_compose, verticalTranslate_compose]
        <;> exact h3
      exfalso
      exact no_tangency_no_cross h_no_tang_up' hf1 hf2 hne_f h_eq'

  -- Common g-side up
  have h_g_common_up : ∀ i ∈ S_up, ∀ j ∈ S_up,
      (L_up_all i).g = (L_up_all j).g →
      ∃ b : C2Function, b ∈ family ∧
        (R.rectangle i).IsLambdaTangent b tangency ∧
        (R.rectangle j).IsLambdaTangent b tangency := by
    intro i hi j hj h_eq
    have h1 : (L_up_all i).g = (b_rep i).verticalTranslate (shift0 (b_rep i)) := by
      have h : L_up_all i = L_up ⟨i, hi⟩ := by simp [L_up_all, hi]
      rw [h]; exact (hL_up ⟨i, hi⟩).2.2.2.2.2
    have h2 : (L_up_all j).g = (b_rep j).verticalTranslate (shift0 (b_rep j)) := by
      have h : L_up_all j = L_up ⟨j, hj⟩ := by simp [L_up_all, hj]
      rw [h]; exact (hL_up ⟨j, hj⟩).2.2.2.2.2
    have h3 : (b_rep i).verticalTranslate (shift0 (b_rep i)) = (b_rep j).verticalTranslate (shift0 (b_rep j)) := by
      rw [←h1, h_eq, h2]
    by_cases h4 : b_rep i = b_rep j
    · have h5 : (R.rectangle j).IsLambdaTangent (b_rep i) tangency := by
        rw [h4]
        exact (hb_rep j).2
      exact ⟨b_rep i, hB (hb_rep i).1, (hb_rep i).2, h5⟩
    · have hbf1 : b_rep i ∈ F_up.carrier := hF_up_B (b_rep i) (hb_rep i).1
      have hbf2 : b_rep j ∈ F_up.carrier := hF_up_B (b_rep j) (hb_rep j).1
      have h_eq' : (b_rep i).verticalTranslate (shift_up' (b_rep i)) = (b_rep j).verticalTranslate (shift_up' (b_rep j)) := by
        have hs1 : shift_up' (b_rep i) = shift0 (b_rep i) := h_shift'_B_up (b_rep i) (hb_rep i).1
        have hs2 : shift_up' (b_rep j) = shift0 (b_rep j) := h_shift'_B_up (b_rep j) (hb_rep j).1
        rw [hs1, hs2] <;> exact h3
      exfalso
      exact no_tangency_no_cross h_no_tang_up' hbf1 hbf2 h4 h_eq'

  -- Non-overlap up (original lenses)
  have h_nonoverlap_up_orig : ∀ i ∈ S_up, ∀ j ∈ S_up, i ≠ j → (L_up_all i).Nonoverlap (L_up_all j) :=
    graph_lenses_nonoverlap_on_subset
      hdelta ht hCc1 hCc_adm htang_le_Cc hE_abs_nonneg hE_absorption hR_incomp
      S_up L_up_all h_up_E_abs h_f_common_up h_g_common_up h_no_cross_up

  -- Transfer non-overlap to reparametrized lenses
  have h_nonoverlap_up' : ∀ (i j : {i // i ∈ S_up}), i ≠ j → (L_up' i).Nonoverlap (L_up' j) := by
    intro i j hne
    let idx := i.val
    let jdx := j.val
    let f1 := (w_rep idx).verticalTranslate epsilon
    let g1 := b_rep idx
    let f2 := (w_rep jdx).verticalTranslate epsilon
    let g2 := b_rep jdx
    have hf1 : f1 ∈ F_up.carrier := hF_up_W' (w_rep idx) (hw_rep idx).1
    have hg1 : g1 ∈ F_up.carrier := hF_up_B (b_rep idx) (hb_rep idx).1
    have hf2 : f2 ∈ F_up.carrier := hF_up_W' (w_rep jdx) (hw_rep jdx).1
    have hg2 : g2 ∈ F_up.carrier := hF_up_B (b_rep jdx) (hb_rep jdx).1
    have h_shift_f1 : shift_up' f1 = shift0 (w_rep idx) := h_shift'_W_up (w_rep idx) (hw_rep idx).1
    have h_shift_g1 : shift_up' g1 = shift0 (b_rep idx) := h_shift'_B_up (b_rep idx) (hb_rep idx).1
    have h_shift_f2 : shift_up' f2 = shift0 (w_rep jdx) := h_shift'_W_up (w_rep jdx) (hw_rep jdx).1
    have h_shift_g2 : shift_up' g2 = shift0 (b_rep jdx) := h_shift'_B_up (b_rep jdx) (hb_rep jdx).1
    have hL1f : (L_up ⟨idx, i.property⟩).f = f1.verticalTranslate (shift_up' f1) := by
      have h : (L_up ⟨idx, i.property⟩).f = (w_rep idx).verticalTranslate (epsilon + shift0 (w_rep idx)) :=
        (hL_up ⟨idx, i.property⟩).2.2.2.2.1
      rw [h, h_shift_f1]
      exact (verticalTranslate_compose (w_rep idx) epsilon (shift0 (w_rep idx))).symm
    have hL1g : (L_up ⟨idx, i.property⟩).g = g1.verticalTranslate (shift_up' g1) := by
      have h : (L_up ⟨idx, i.property⟩).g = (b_rep idx).verticalTranslate (shift0 (b_rep idx)) :=
        (hL_up ⟨idx, i.property⟩).2.2.2.2.2
      simpa [g1, h_shift_g1] using h
    have hL2f : (L_up ⟨jdx, j.property⟩).f = f2.verticalTranslate (shift_up' f2) := by
      have h : (L_up ⟨jdx, j.property⟩).f = (w_rep jdx).verticalTranslate (epsilon + shift0 (w_rep jdx)) :=
        (hL_up ⟨jdx, j.property⟩).2.2.2.2.1
      rw [h, h_shift_f2]
      exact (verticalTranslate_compose (w_rep jdx) epsilon (shift0 (w_rep jdx))).symm
    have hL2g : (L_up ⟨jdx, j.property⟩).g = g2.verticalTranslate (shift_up' g2) := by
      have h : (L_up ⟨jdx, j.property⟩).g = (b_rep jdx).verticalTranslate (shift0 (b_rep jdx)) :=
        (hL_up ⟨jdx, j.property⟩).2.2.2.2.2
      simpa [g2, h_shift_g2] using h
    have hne_val : idx ≠ jdx := by
      intro h; apply hne; exact Subtype.ext h
    have h_orig : (L_up ⟨idx, i.property⟩).Nonoverlap (L_up ⟨jdx, j.property⟩) := by
      have h_eq1 : L_up_all idx = L_up ⟨idx, i.property⟩ := by
        unfold L_up_all; rw [dif_pos i.property]
      have h_eq2 : L_up_all jdx = L_up ⟨jdx, j.property⟩ := by
        unfold L_up_all; rw [dif_pos j.property]
      have h : (L_up_all idx).Nonoverlap (L_up_all jdx) := h_nonoverlap_up_orig idx i.property jdx j.property hne_val
      rw [h_eq1, h_eq2] at h
      exact h
    exact GraphLens.nonoverlap_reparam_of_no_tang
      (h_no_tang := h_no_tang_up')
      (hf₁ := hf1) (hg₁ := hg1) (hf₂ := hf2) (hg₂ := hg2)
      (hL₁f := hL1f) (hL₁g := hL1g) (hL₂f := hL2f) (hL₂g := hL2g)
      (h_orig := h_orig)

  -- Count up
  have h_count_up : (S_up.card : ℝ) ≤ C_mt * Real.rpow curves_up.card (3 / 2 : ℝ) * Real.log (curves_up.card + 1) :=
    indexed_graph_lens_count h_mt_bound S_up curves_up h_pseudo_up L_up' h_sides_up h_nonoverlap_up'

  have h_curves_up_le : curves_up.card ≤ W.card + B.card := by
    have h1 : curves_up.card ≤ F_up.toFinset.card := Finset.card_image_le
    have h4 : F_up.carrier ⊆ (W.carrier.image (fun w => w.verticalTranslate epsilon)) ∪ B.carrier := by
      intro f hf
      have h : (∃ w ∈ W.carrier, f = w.verticalTranslate epsilon) ∨ f ∈ B.carrier := hF_up_W f hf
      rcases h with (h | h)
      · rcases h with ⟨w, hw, rfl⟩
        exact Or.inl ⟨w, hw, rfl⟩
      · exact Or.inr h
    have h_fin1 : (W.carrier.image (fun w => w.verticalTranslate epsilon)).Finite := W.finite.image _
    have h_fin2 : ((W.carrier.image (fun w => w.verticalTranslate epsilon)) ∪ B.carrier).Finite := h_fin1.union B.finite
    have h5 : F_up.toFinset.card = F_up.carrier.ncard :=
      (Set.ncard_eq_toFinset_card F_up.carrier F_up.finite).symm
    rw [h5] at h1
    have h6 : F_up.carrier.ncard ≤ ((W.carrier.image (fun w => w.verticalTranslate epsilon)) ∪ B.carrier).ncard :=
      Set.ncard_le_ncard h4 h_fin2
    have h7 : ((W.carrier.image (fun w => w.verticalTranslate epsilon)) ∪ B.carrier).ncard ≤
        (W.carrier.image (fun w => w.verticalTranslate epsilon)).ncard + B.carrier.ncard :=
      Set.ncard_union_le _ _
    have h8 : (W.carrier.image (fun w => w.verticalTranslate epsilon)).ncard = W.carrier.ncard :=
      Set.ncard_image_of_injective W.carrier (fun w1 w2 h => verticalTranslate_inj w1 w2 epsilon h)
    have h9 : W.carrier.ncard = W.card := by rfl
    have h10 : B.carrier.ncard = B.card := by rfl
    rw [h8, h9, h10] at h7
    linarith

  -- ======================================================================
  -- DOWN DIRECTION
  -- ======================================================================
  rcases directional_family hK W B F hF_eq shift0 hdelta ht htang h_small2 h_sep
      (by rw [abs_neg, abs_of_pos h_eps_pos]; exact h_eps_high)
      h_amp h_pairwise h_no_tang_down
    with ⟨F_down, shift_down', hF_down_W, hF_down_W', hF_down_B, h_amp_down, h_pairwise_down, h_shift'_W_down, h_shift'_B_down, h_no_tang_down'⟩

  let curves_down : Finset C2Function :=
    F_down.toFinset.image (fun f => (f.verticalTranslate (shift_down' f)).reparam I)

  have h_pseudo_down : IsGraphPseudoCircleFamily curves_down :=
    shifted_bipartite_pseudo_circle_any hK hD1 hfam hI_short hI_pos
      (show W.carrier ⊆ F.carrier from by simp [hF_eq])
      (show B.carrier ⊆ F.carrier from by simp [hF_eq])
      hdelta ht htang h_small2 h_sep
      (by rw [abs_neg, abs_of_pos h_eps_pos]; exact h_eps_high)
      F_down hF_down_W hF_down_W' h_amp_down h_pairwise_down h_no_tang_down'

  let L_down' : {i // i ∈ S_down} → GraphLens := fun i =>
    (L_down i).reparam I hI_pos (hL_down i).1 (hL_down i).2.1

  have h_sides_down : ∀ (i : {i // i ∈ S_down}),
      (L_down' i).f ∈ curves_down ∧ (L_down' i).g ∈ curves_down := by
    intro i
    let idx := i.val
    let f1 := (w_rep idx).verticalTranslate (-epsilon)
    let g1 := b_rep idx
    have hwf : f1 ∈ F_down.carrier := hF_down_W' (w_rep idx) (hw_rep idx).1
    have hbf : g1 ∈ F_down.carrier := hF_down_B (b_rep idx) (hb_rep idx).1
    have hsf : shift_down' f1 = shift0 (w_rep idx) := h_shift'_W_down (w_rep idx) (hw_rep idx).1
    have hsg : shift_down' g1 = shift0 (b_rep idx) := h_shift'_B_down (b_rep idx) (hb_rep idx).1
    have hL_f : (L_down i).f = (w_rep idx).verticalTranslate (-epsilon + shift0 (w_rep idx)) := (hL_down i).2.2.2.2.1
    have hL_g : (L_down i).g = (b_rep idx).verticalTranslate (shift0 (b_rep idx)) := (hL_down i).2.2.2.2.2
    have h_eq_f : (L_down i).f = f1.verticalTranslate (shift_down' f1) := by
      rw [hL_f, hsf]
      <;> rw [verticalTranslate_compose] <;> ring
    have h_eq_g : (L_down i).g = g1.verticalTranslate (shift_down' g1) := by
      rw [hL_g, hsg]
    have h1 : (L_down' i).f = (f1.verticalTranslate (shift_down' f1)).reparam I := by
      have h : (L_down' i).f = (L_down i).f.reparam I := by rfl
      rw [h, h_eq_f]
    have h2 : (L_down' i).g = (g1.verticalTranslate (shift_down' g1)).reparam I := by
      have h : (L_down' i).g = (L_down i).g.reparam I := by rfl
      rw [h, h_eq_g]
    constructor
    · rw [h1]; exact Finset.mem_image.mpr ⟨f1, F_down.finite.mem_toFinset.mpr hwf, rfl⟩
    · rw [h2]; exact Finset.mem_image.mpr ⟨g1, F_down.finite.mem_toFinset.mpr hbf, rfl⟩

  have h_no_cross_down : ∀ i ∈ S_down, ∀ j ∈ S_down, (L_down_all i).f ≠ (L_down_all j).g := by
    intro i hi j hj
    have hnp_i : i ∉ S_up := Finset.disjoint_right.mp h_partition2 hi
    have hnp_j : j ∉ S_up := Finset.disjoint_right.mp h_partition2 hj
    have h_eq_f : (L_down_all i).f = (w_rep i).verticalTranslate (-epsilon + shift0 (w_rep i)) := by
      have h : L_down_all i = L_down ⟨i, hi⟩ := by simp [L_down_all, L_up_all, hnp_i]
      rw [h]; exact (hL_down ⟨i, hi⟩).2.2.2.2.1
    have h_eq_g : (L_down_all j).g = (b_rep j).verticalTranslate (shift0 (b_rep j)) := by
      have h : L_down_all j = L_down ⟨j, hj⟩ := by simp [L_down_all, L_up_all, hnp_j]
      rw [h]; exact (hL_down ⟨j, hj⟩).2.2.2.2.2
    rw [h_eq_f, h_eq_g]
    intro h_eq
    have h9 : c2Distance (w_rep i) (b_rep j) ≤ epsilon + 2 * delta := by
      calc
        c2Distance (w_rep i) (b_rep j)
          ≤ c2Distance (w_rep i) ((w_rep i).verticalTranslate (-epsilon + shift0 (w_rep i)))
            + c2Distance ((w_rep i).verticalTranslate (-epsilon + shift0 (w_rep i))) ((b_rep j).verticalTranslate (shift0 (b_rep j)))
            + c2Distance ((b_rep j).verticalTranslate (shift0 (b_rep j))) (b_rep j) := by
          exact dist_triangle4 _ _ _ _
        _ = |-epsilon + shift0 (w_rep i)| + 0 + |shift0 (b_rep j)| := by
          have h_first : c2Distance (w_rep i) ((w_rep i).verticalTranslate (-epsilon + shift0 (w_rep i))) = |-epsilon + shift0 (w_rep i)| :=
            c2Distance_verticalTranslate_self _ _
          have h_middle : c2Distance ((w_rep i).verticalTranslate (-epsilon + shift0 (w_rep i))) ((b_rep j).verticalTranslate (shift0 (b_rep j))) = 0 := by
            rw [h_eq, c2Distance_eq_dist, dist_self]
          have h_third : c2Distance ((b_rep j).verticalTranslate (shift0 (b_rep j))) (b_rep j) = |shift0 (b_rep j)| := by
            rw [c2Distance_eq_dist, dist_comm]
            exact c2Distance_verticalTranslate_self _ _
          rw [h_first, h_middle, h_third] <;> ring
        _ ≤ epsilon + delta + delta := by
          have h10 : |-epsilon + shift0 (w_rep i)| ≤ epsilon + delta := by
            calc
              |-epsilon + shift0 (w_rep i)|
                ≤ |(-epsilon : ℝ)| + |shift0 (w_rep i)| := by
                  exact abs_add_le (-epsilon) (shift0 (w_rep i))
              _ = epsilon + |shift0 (w_rep i)| := by
                have h_eps_abs : |(-epsilon : ℝ)| = epsilon := by
                  rw [abs_neg, abs_of_nonneg (by linarith [h_eps_low])]
                rw [h_eps_abs]
              _ ≤ epsilon + delta := by
                gcongr
                exact h_amp (w_rep i) (by rw [hF_eq]; exact Or.inl (hw_rep i).1)
          have h11 : |shift0 (b_rep j)| ≤ delta := h_amp (b_rep j) (by rw [hF_eq]; exact Or.inr (hb_rep j).1)
          linarith
        _ = epsilon + 2 * delta := by ring
    have h10 : 2 * t ≤ c2Distance (w_rep i) (b_rep j) := h_sep (hw_rep i).1 (hb_rep j).1
    linarith

  have h_f_common_down : ∀ i ∈ S_down, ∀ j ∈ S_down,
      (L_down_all i).f = (L_down_all j).f →
      ∃ w : C2Function, w ∈ family ∧
        (R.rectangle i).IsLambdaTangent w tangency ∧
        (R.rectangle j).IsLambdaTangent w tangency := by
    intro i hi j hj h_eq
    have hnp_i : i ∉ S_up := Finset.disjoint_right.mp h_partition2 hi
    have hnp_j : j ∉ S_up := Finset.disjoint_right.mp h_partition2 hj
    have h1 : (L_down_all i).f = (w_rep i).verticalTranslate (-epsilon + shift0 (w_rep i)) := by
      have h : L_down_all i = L_down ⟨i, hi⟩ := by simp [L_down_all, L_up_all, hnp_i]
      rw [h]; exact (hL_down ⟨i, hi⟩).2.2.2.2.1
    have h2 : (L_down_all j).f = (w_rep j).verticalTranslate (-epsilon + shift0 (w_rep j)) := by
      have h : L_down_all j = L_down ⟨j, hj⟩ := by simp [L_down_all, L_up_all, hnp_j]
      rw [h]; exact (hL_down ⟨j, hj⟩).2.2.2.2.1
    have h3 : (w_rep i).verticalTranslate (-epsilon + shift0 (w_rep i)) = (w_rep j).verticalTranslate (-epsilon + shift0 (w_rep j)) := by
      rw [←h1, h_eq, h2]
    by_cases h4 : w_rep i = w_rep j
    · have h5 : (R.rectangle j).IsLambdaTangent (w_rep i) tangency := by
        rw [h4]; exact (hw_rep j).2
      exact ⟨w_rep i, hW (hw_rep i).1, (hw_rep i).2, h5⟩
    · let f1 := (w_rep i).verticalTranslate (-epsilon)
      let f2 := (w_rep j).verticalTranslate (-epsilon)
      have hf1 : f1 ∈ F_down.carrier := hF_down_W' (w_rep i) (hw_rep i).1
      have hf2 : f2 ∈ F_down.carrier := hF_down_W' (w_rep j) (hw_rep j).1
      have hne_f : f1 ≠ f2 := by
        intro h_eq_f
        have h1 : f1.verticalTranslate epsilon = f2.verticalTranslate epsilon := by rw [h_eq_f]
        have h2a : f1.verticalTranslate epsilon = w_rep i := by
          rw [verticalTranslate_compose]
          have h_sum : (-epsilon) + epsilon = (0 : ℝ) := by ring
          rw [h_sum]
          exact h_vt_zero (w_rep i)
        have h2b : f2.verticalTranslate epsilon = w_rep j := by
          rw [verticalTranslate_compose]
          have h_sum : (-epsilon) + epsilon = (0 : ℝ) := by ring
          rw [h_sum]
          exact h_vt_zero (w_rep j)
        rw [h2a, h2b] at h1
        exact h4 h1
      have h_eq' : f1.verticalTranslate (shift_down' f1) = f2.verticalTranslate (shift_down' f2) := by
        have hs1 : shift_down' f1 = shift0 (w_rep i) := h_shift'_W_down (w_rep i) (hw_rep i).1
        have hs2 : shift_down' f2 = shift0 (w_rep j) := h_shift'_W_down (w_rep j) (hw_rep j).1
        rw [hs1, hs2, verticalTranslate_compose, verticalTranslate_compose]
        <;> exact h3
      exfalso
      exact no_tangency_no_cross h_no_tang_down' hf1 hf2 hne_f h_eq'

  have h_g_common_down : ∀ i ∈ S_down, ∀ j ∈ S_down,
      (L_down_all i).g = (L_down_all j).g →
      ∃ b : C2Function, b ∈ family ∧
        (R.rectangle i).IsLambdaTangent b tangency ∧
        (R.rectangle j).IsLambdaTangent b tangency := by
    intro i hi j hj h_eq
    have hnp_i : i ∉ S_up := Finset.disjoint_right.mp h_partition2 hi
    have hnp_j : j ∉ S_up := Finset.disjoint_right.mp h_partition2 hj
    have h1 : (L_down_all i).g = (b_rep i).verticalTranslate (shift0 (b_rep i)) := by
      have h : L_down_all i = L_down ⟨i, hi⟩ := by simp [L_down_all, L_up_all, hnp_i]
      rw [h]; exact (hL_down ⟨i, hi⟩).2.2.2.2.2
    have h2 : (L_down_all j).g = (b_rep j).verticalTranslate (shift0 (b_rep j)) := by
      have h : L_down_all j = L_down ⟨j, hj⟩ := by simp [L_down_all, L_up_all, hnp_j]
      rw [h]; exact (hL_down ⟨j, hj⟩).2.2.2.2.2
    have h3 : (b_rep i).verticalTranslate (shift0 (b_rep i)) = (b_rep j).verticalTranslate (shift0 (b_rep j)) := by
      rw [←h1, h_eq, h2]
    by_cases h4 : b_rep i = b_rep j
    · have h5 : (R.rectangle j).IsLambdaTangent (b_rep i) tangency := by
        rw [h4]; exact (hb_rep j).2
      exact ⟨b_rep i, hB (hb_rep i).1, (hb_rep i).2, h5⟩
    · have hbf1 : b_rep i ∈ F_down.carrier := hF_down_B (b_rep i) (hb_rep i).1
      have hbf2 : b_rep j ∈ F_down.carrier := hF_down_B (b_rep j) (hb_rep j).1
      have h_eq' : (b_rep i).verticalTranslate (shift_down' (b_rep i)) = (b_rep j).verticalTranslate (shift_down' (b_rep j)) := by
        have hs1 : shift_down' (b_rep i) = shift0 (b_rep i) := h_shift'_B_down (b_rep i) (hb_rep i).1
        have hs2 : shift_down' (b_rep j) = shift0 (b_rep j) := h_shift'_B_down (b_rep j) (hb_rep j).1
        rw [hs1, hs2] <;> exact h3
      exfalso
      exact no_tangency_no_cross h_no_tang_down' hbf1 hbf2 h4 h_eq'

  have h_nonoverlap_down_orig : ∀ i ∈ S_down, ∀ j ∈ S_down, i ≠ j → (L_down_all i).Nonoverlap (L_down_all j) :=
    graph_lenses_nonoverlap_on_subset
      hdelta ht hCc1 hCc_adm htang_le_Cc hE_abs_nonneg hE_absorption hR_incomp
      S_down L_down_all h_down_E_abs h_f_common_down h_g_common_down h_no_cross_down

  have h_nonoverlap_down' : ∀ (i j : {i // i ∈ S_down}), i ≠ j → (L_down' i).Nonoverlap (L_down' j) := by
    intro i j hne
    let idx := i.val
    let jdx := j.val
    let f1 := (w_rep idx).verticalTranslate (-epsilon)
    let g1 := b_rep idx
    let f2 := (w_rep jdx).verticalTranslate (-epsilon)
    let g2 := b_rep jdx
    have hf1 : f1 ∈ F_down.carrier := hF_down_W' (w_rep idx) (hw_rep idx).1
    have hg1 : g1 ∈ F_down.carrier := hF_down_B (b_rep idx) (hb_rep idx).1
    have hf2 : f2 ∈ F_down.carrier := hF_down_W' (w_rep jdx) (hw_rep jdx).1
    have hg2 : g2 ∈ F_down.carrier := hF_down_B (b_rep jdx) (hb_rep jdx).1
    have h_shift_f1 : shift_down' f1 = shift0 (w_rep idx) := h_shift'_W_down (w_rep idx) (hw_rep idx).1
    have h_shift_g1 : shift_down' g1 = shift0 (b_rep idx) := h_shift'_B_down (b_rep idx) (hb_rep idx).1
    have h_shift_f2 : shift_down' f2 = shift0 (w_rep jdx) := h_shift'_W_down (w_rep jdx) (hw_rep jdx).1
    have h_shift_g2 : shift_down' g2 = shift0 (b_rep jdx) := h_shift'_B_down (b_rep jdx) (hb_rep jdx).1
    have hL1f : (L_down ⟨idx, i.property⟩).f = f1.verticalTranslate (shift_down' f1) := by
      have h : (L_down ⟨idx, i.property⟩).f = (w_rep idx).verticalTranslate (-epsilon + shift0 (w_rep idx)) :=
        (hL_down ⟨idx, i.property⟩).2.2.2.2.1
      rw [h, h_shift_f1]
      exact (verticalTranslate_compose (w_rep idx) (-epsilon) (shift0 (w_rep idx))).symm
    have hL1g : (L_down ⟨idx, i.property⟩).g = g1.verticalTranslate (shift_down' g1) := by
      have h : (L_down ⟨idx, i.property⟩).g = (b_rep idx).verticalTranslate (shift0 (b_rep idx)) :=
        (hL_down ⟨idx, i.property⟩).2.2.2.2.2
      simpa [g1, h_shift_g1] using h
    have hL2f : (L_down ⟨jdx, j.property⟩).f = f2.verticalTranslate (shift_down' f2) := by
      have h : (L_down ⟨jdx, j.property⟩).f = (w_rep jdx).verticalTranslate (-epsilon + shift0 (w_rep jdx)) :=
        (hL_down ⟨jdx, j.property⟩).2.2.2.2.1
      rw [h, h_shift_f2]
      exact (verticalTranslate_compose (w_rep jdx) (-epsilon) (shift0 (w_rep jdx))).symm
    have hL2g : (L_down ⟨jdx, j.property⟩).g = g2.verticalTranslate (shift_down' g2) := by
      have h : (L_down ⟨jdx, j.property⟩).g = (b_rep jdx).verticalTranslate (shift0 (b_rep jdx)) :=
        (hL_down ⟨jdx, j.property⟩).2.2.2.2.2
      simpa [g2, h_shift_g2] using h
    have hne_val : idx ≠ jdx := by
      intro h; apply hne; exact Subtype.ext h
    have h_orig : (L_down ⟨idx, i.property⟩).Nonoverlap (L_down ⟨jdx, j.property⟩) := by
      have hnp_idx : idx ∉ S_up := Finset.disjoint_right.mp h_partition2 i.property
      have hnp_jdx : jdx ∉ S_up := Finset.disjoint_right.mp h_partition2 j.property
      have h_eq1 : L_down_all idx = L_down ⟨idx, i.property⟩ := by
        unfold L_down_all L_up_all
        rw [dif_neg hnp_idx]
        <;> simp
        <;> rfl
      have h_eq2 : L_down_all jdx = L_down ⟨jdx, j.property⟩ := by
        unfold L_down_all L_up_all
        rw [dif_neg hnp_jdx]
        <;> simp
        <;> rfl
      have h : (L_down_all idx).Nonoverlap (L_down_all jdx) := h_nonoverlap_down_orig idx i.property jdx j.property hne_val
      rw [h_eq1, h_eq2] at h
      exact h
    exact GraphLens.nonoverlap_reparam_of_no_tang
      (h_no_tang := h_no_tang_down')
      (hf₁ := hf1) (hg₁ := hg1) (hf₂ := hf2) (hg₂ := hg2)
      (hL₁f := hL1f) (hL₁g := hL1g) (hL₂f := hL2f) (hL₂g := hL2g)
      (h_orig := h_orig)

  have h_count_down : (S_down.card : ℝ) ≤ C_mt * Real.rpow curves_down.card (3 / 2 : ℝ) * Real.log (curves_down.card + 1) :=
    indexed_graph_lens_count h_mt_bound S_down curves_down h_pseudo_down L_down' h_sides_down h_nonoverlap_down'

  have hF_down_carrier : F_down.carrier = (W.carrier.image (fun w => w.verticalTranslate (-epsilon))) ∪ B.carrier := by
    ext f
    simp only [Set.mem_union, Set.mem_image]
    constructor
    · intro h
      rcases hF_down_W f h with (⟨w, hw, h_eq⟩ | hb)
      · exact Or.inl ⟨w, hw, h_eq.symm⟩
      · exact Or.inr hb
    · rintro (⟨w, hw, rfl⟩ | hb)
      · exact hF_down_W' w hw
      · exact hF_down_B f hb
  have h_curves_down_le : curves_down.card ≤ W.card + B.card := by
    have h1 : curves_down.card ≤ F_down.toFinset.card := Finset.card_image_le
    have h4 : F_down.carrier ⊆ (W.carrier.image (fun w => w.verticalTranslate (-epsilon))) ∪ B.carrier := by
      intro f hf
      have h : (∃ w ∈ W.carrier, f = w.verticalTranslate (-epsilon)) ∨ f ∈ B.carrier := hF_down_W f hf
      rcases h with (h | h)
      · rcases h with ⟨w, hw, rfl⟩
        exact Or.inl ⟨w, hw, rfl⟩
      · exact Or.inr h
    have h_fin1 : (W.carrier.image (fun w => w.verticalTranslate (-epsilon))).Finite := W.finite.image _
    have h_fin2 : ((W.carrier.image (fun w => w.verticalTranslate (-epsilon))) ∪ B.carrier).Finite := h_fin1.union B.finite
    have h5 : F_down.toFinset.card = F_down.carrier.ncard :=
      (Set.ncard_eq_toFinset_card F_down.carrier F_down.finite).symm
    rw [h5] at h1
    have h6 : F_down.carrier.ncard ≤ ((W.carrier.image (fun w => w.verticalTranslate (-epsilon))) ∪ B.carrier).ncard :=
      Set.ncard_le_ncard h4 h_fin2
    have h7 : ((W.carrier.image (fun w => w.verticalTranslate (-epsilon))) ∪ B.carrier).ncard ≤
        (W.carrier.image (fun w => w.verticalTranslate (-epsilon))).ncard + B.carrier.ncard :=
      Set.ncard_union_le _ _
    have h8 : (W.carrier.image (fun w => w.verticalTranslate (-epsilon))).ncard = W.carrier.ncard :=
      Set.ncard_image_of_injective W.carrier (fun w1 w2 h => verticalTranslate_inj w1 w2 (-epsilon) h)
    have h9 : W.carrier.ncard = W.card := by rfl
    have h10 : B.carrier.ncard = B.card := by rfl
    rw [h8, h9, h10] at h7
    linarith

  -- ======================================================================
  -- Combine
  -- ======================================================================
  let N : ℝ := (W.card + B.card : ℝ)
  have hN : 2 ≤ N := by
    have hW_nonempty : 0 < W.card := by
      have h1 : 0 < R.card := hR_nonempty
      let i : Fin R.card := ⟨0, h1⟩
      have hi : w_rep i ∈ W.carrier := (hw_rep i).1
      have h2 : Set.Nonempty W.carrier := ⟨w_rep i, hi⟩
      have h3 : 0 < W.carrier.ncard := (Set.ncard_pos (hs := W.finite)).mpr h2
      simpa [FiniteFunctionFamily.card] using h3
    have hB_nonempty : 0 < B.card := by
      have h1 : 0 < R.card := hR_nonempty
      let i : Fin R.card := ⟨0, h1⟩
      have hi : b_rep i ∈ B.carrier := (hb_rep i).1
      have h2 : Set.Nonempty B.carrier := ⟨b_rep i, hi⟩
      have h3 : 0 < B.carrier.ncard := (Set.ncard_pos (hs := B.finite)).mpr h2
      simpa [FiniteFunctionFamily.card] using h3
    have hW_ge1 : 1 ≤ W.card := by linarith
    have hB_ge1 : 1 ≤ B.card := by linarith
    have h_sum : 2 ≤ (W.card + B.card : ℝ) := by exact_mod_cast (by linarith : (2 : ℕ) ≤ W.card + B.card)
    have hN_eq : N = (W.card + B.card : ℝ) := by rfl
    rw [hN_eq]
    exact h_sum

  have hm_up : (curves_up.card : ℝ) ≤ N := by
    have h : (curves_up.card : ℝ) ≤ (W.card + B.card : ℝ) := by exact_mod_cast h_curves_up_le
    simpa [N] using h
  have hm_down : (curves_down.card : ℝ) ≤ N := by
    have h : (curves_down.card : ℝ) ≤ (W.card + B.card : ℝ) := by exact_mod_cast h_curves_down_le
    simpa [N] using h
  have h_main : ((S_up.card + S_down.card : ℕ) : ℝ) ≤
      C * Real.rpow N (3 / 2 : ℝ) * Real.log N :=
    final_counting_combination hC_mt_pos hC2 hN hm_up hm_down h_count_up h_count_down

  have h_card_eq : (S_up.card + S_down.card : ℕ) = R.card := by
    exact_mod_cast h_card_sum

  rw [h_card_eq] at h_main
  have h_tang_rpow_ge1 : 1 ≤ Real.rpow tangency C := by
    have h1 : 1 ≤ tangency := by linarith
    have h2 : 0 ≤ C := by linarith [hC1]
    exact Real.one_le_rpow h1 h2
  have hN_pos : 0 < N := by linarith [hN]
  have hN_rpow_pos : 0 < Real.rpow N (3 / 2 : ℝ) := Real.rpow_pos_of_pos hN_pos (3 / 2 : ℝ)
  have h1_lt_N : 1 < N := by linarith [hN]
  have hlog_pos : 0 < Real.log N := Real.log_pos h1_lt_N
  have hC_pos : 0 < C := by linarith [hC1]
  have h_weaken : C * Real.rpow N (3 / 2 : ℝ) * Real.log N ≤
      C * Real.rpow tangency C * Real.rpow N (3 / 2 : ℝ) * Real.log N := by
    have h_pos_product : 0 ≤ C * Real.rpow N (3 / 2 : ℝ) * Real.log N := by positivity
    have h5 : (C * Real.rpow N (3 / 2 : ℝ) * Real.log N) * 1 ≤
        (C * Real.rpow N (3 / 2 : ℝ) * Real.log N) * Real.rpow tangency C :=
      mul_le_mul_of_nonneg_left h_tang_rpow_ge1 h_pos_product
    have h6 : (C * Real.rpow N (3 / 2 : ℝ) * Real.log N) * Real.rpow tangency C =
        C * Real.rpow tangency C * Real.rpow N (3 / 2 : ℝ) * Real.log N := by ring
    rw [h6] at h5
    simpa [mul_one] using h5
  have h_main2 : (R.card : ℝ) ≤ C * Real.rpow tangency C *
      Real.rpow N (3 / 2 : ℝ) * Real.log N := h_main.trans h_weaken
  have hN_eq : N = RectangleFamily.bipartiteNormalizedCount W B 1 1 := by
    simp [N, RectangleFamily.bipartiteNormalizedCount] <;> ring
  rw [hN_eq] at h_main2
  exact h_main2

end Kakeya.Cinematic
