import MyLeanRepo.Kakeya.Cinematic.Geometry
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ShiftBound
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.BidirectionalShiftAvoidance
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.UnitCoreConstants
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.PerturbationPreservation
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.BidirectionalGraphLensCount

/-!
# Helper lemmas for the robust unit core proof

Bridging lemmas needed to assemble the robust unit core from graph lenses.
-/

namespace Kakeya.Cinematic

open Finset

noncomputable section

local instance instDecidableEqC2FunctionHelpers : DecidableEq C2Function := Classical.decEq _

/-- Vertical translation by a fixed constant is injective. -/
lemma verticalTranslate_inj (f g : C2Function) (c : ℝ)
    (h : f.verticalTranslate c = g.verticalTranslate c) : f = g := by
  have h_val : f.value = g.value := by
    have h1 := congr_arg (fun h : C2Function => h.value) h
    simpa [C2Function.verticalTranslate] using h1
  have h_deriv1 : f.firstDeriv = g.firstDeriv := by
    have h1 := congr_arg (fun h : C2Function => h.firstDeriv) h
    simpa [C2Function.verticalTranslate] using h1
  have h_deriv2 : f.secondDeriv = g.secondDeriv := by
    have h1 := congr_arg (fun h : C2Function => h.secondDeriv) h
    simpa [C2Function.verticalTranslate] using h1
  have h_jet : f.toJet = g.toJet := by
    simp [C2Function.toJet, h_val, h_deriv1, h_deriv2]
  exact C2Function.toJet_injective h_jet

/--
A finite subfamily of a `HasCinematicCurvature` family is itself an
`IsCinematicFamily`, because every finite set is doubling.
-/
lemma finite_cinematic_family {K : ℝ} {family : Set C2Function}
    (hcurv : HasCinematicCurvature family K)
    (F : FiniteFunctionFamily) (hF : F.carrier ⊆ family) :
    ∃ D : ℝ, 1 ≤ D ∧ IsCinematicFamily F.carrier K D := by
  let D : ℝ := max 1 (F.card : ℝ)
  have hD1 : 1 ≤ D := le_max_left _ _
  have hDcard : (F.card : ℝ) ≤ D := le_max_right _ _
  have h_diam : ∀ ⦃f : C2Function⦄, f ∈ F.carrier →
      ∀ ⦃g : C2Function⦄, g ∈ F.carrier → c2Distance f g ≤ K := by
    intro f hf g hg
    exact hcurv.1 (hF hf) (hF hg)
  have h_curv : ∀ ⦃f : C2Function⦄, f ∈ F.carrier →
      ∀ ⦃g : C2Function⦄, g ∈ F.carrier →
        ∀ x : UnitPoint, K⁻¹ * c2Distance f g ≤ jetGap f g x := by
    intro f hf g hg
    exact hcurv.2 (hF hf) (hF hg)
  have h_doubling : ∀ ⦃f : C2Function⦄, f ∈ F.carrier →
      ∀ r : ℝ, 0 < r →
        ∃ centers : Set C2Function,
          centers.Finite ∧ centers ⊆ F.carrier ∧
          (centers.ncard : ℝ) ≤ D ∧
          ∀ ⦃g : C2Function⦄, g ∈ F.carrier → c2Distance f g ≤ r →
            ∃ h ∈ centers, c2Distance h g ≤ r / 2 := by
    intro f hf r hr
    let centers : Set C2Function := {g ∈ F.carrier | c2Distance f g ≤ r}
    have hcenters_sub : centers ⊆ F.carrier := by
      intro x hx
      simpa [centers] using hx.1
    have hcenters_finite : centers.Finite := F.finite.subset hcenters_sub
    have hcenters_ncard : (centers.ncard : ℝ) ≤ (F.card : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hcenters_sub F.finite
    refine ⟨centers, hcenters_finite, hcenters_sub, hcenters_ncard.trans hDcard, ?_⟩
    intro g hg hdist
    have hg_in_centers : g ∈ centers := by
      exact ⟨hg, hdist⟩
    refine ⟨g, hg_in_centers, ?_⟩
    have h_self : c2Distance g g = 0 := by
      rw [c2Distance_eq_dist, dist_self]
    rw [h_self]
    linarith
  exact ⟨D, hD1, ⟨h_diam, h_doubling, h_curv⟩⟩

/-- Bound the pair-dependent lens enlargement factor by the uniform one. -/
lemma E_lens_le_E_abs
    {K d t : ℝ}
    (hK : 1 ≤ K)
    (ht : 0 < t)
    (hd : 2 * t ≤ d)
    (V : ℝ)
    (hV_nonneg : 0 ≤ V)
    (curvature E_lens E_abs : ℝ)
    (hcurv : curvature = d / (6 * K * t))
    (hE_lens : E_lens = 2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature))
    (hE_abs : E_abs = 12 * K * (V + 1) + Real.sqrt (6 * K * V)) :
    E_lens ≤ E_abs := by
  have hK_pos : 0 < K := by linarith
  have hd_pos : 0 < d := by linarith
  have hcurv_pos : 0 < curvature := by
    rw [hcurv]
    positivity
  have hratio : t / d ≤ 1 / 2 := by
    rw [div_le_iff₀ hd_pos]
    linarith
  have h1 : 2 * (2 * V + d / t) / curvature ≤ 12 * K * (V + 1) := by
    have h_eq1 : 2 * (2 * V + d / t) / curvature =
        24 * K * V * (t / d) + 12 * K := by
      rw [hcurv]
      field_simp [hK_pos.ne', ht.ne', hd_pos.ne']
      ring
    rw [h_eq1]
    have h2 : 24 * K * V * (t / d) ≤ 12 * K * V := by
      have h3 : 24 * K * V * (t / d) ≤ 24 * K * V * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      have h4 : 24 * K * V * (1 / 2 : ℝ) = 12 * K * V := by ring
      exact h3.trans_eq h4
    have h5 : 24 * K * V * (t / d) + 12 * K ≤ 12 * K * V + 12 * K := by
      exact add_le_add h2 (by linarith)
    have h6 : 12 * K * V + 12 * K = 12 * K * (V + 1) := by ring
    exact h5.trans_eq h6
  have h2 : Real.sqrt (2 * V / curvature) ≤ Real.sqrt (6 * K * V) := by
    have h_eq2 : 2 * V / curvature = 12 * K * V * (t / d) := by
      rw [hcurv]
      field_simp [hK_pos.ne', ht.ne', hd_pos.ne']
      ring
    rw [h_eq2]
    have h3 : 12 * K * V * (t / d) ≤ 6 * K * V := by
      have h4 : 12 * K * V * (t / d) ≤ 12 * K * V * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      have h5 : 12 * K * V * (1 / 2 : ℝ) = 6 * K * V := by ring
      exact h4.trans_eq h5
    exact Real.sqrt_le_sqrt h3
  rw [hE_lens, hE_abs]
  exact add_le_add h1 h2

lemma bipartiteNormalizedCount_unit
    (W B : FiniteFunctionFamily) :
    RectangleFamily.bipartiteNormalizedCount W B 1 1 =
      (W.card : ℝ) + (B.card : ℝ) := by
  simp [RectangleFamily.bipartiteNormalizedCount]

lemma image_card_le_sum
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (W B : Finset α) (f : α → β) :
    (image f (W ∪ B)).card ≤ W.card + B.card := by
  have h1 : (image f (W ∪ B)).card ≤ (W ∪ B).card :=
    card_image_le
  have h2 : (W ∪ B).card ≤ W.card + B.card :=
    card_union_le W B
  exact h1.trans h2

/--
Set up perturbation and directional shifts for the bipartite robust unit core.
-/
lemma perturbation_setup
    {K D : ℝ} (hK : 1 ≤ K) (hD : 1 ≤ D)
    {I : ParameterInterval} (hI : I.IsControlled K)
    (W B : FiniteFunctionFamily)
    {hfam : IsCinematicFamily (W.carrier ∪ B.carrier) K D}
    {delta tangency : ℝ}
    (hdelta : 0 < delta) (htang : 5 ≤ tangency)
    (h_pert : FiniteTangencyPerturbationStatement) :
    ∃ (shift0 : C2Function → ℝ) (epsilon : ℝ),
      let F : FiniteFunctionFamily :=
        { carrier := W.carrier ∪ B.carrier
          finite := W.finite.union B.finite }
      let shiftUp : C2Function → ℝ := fun f =>
        if f ∈ W.toFinset then epsilon + shift0 f else shift0 f
      let shiftDown : C2Function → ℝ := fun f =>
        if f ∈ W.toFinset then -epsilon + shift0 f else shift0 f
      (∀ f ∈ F.carrier, |shift0 f| ≤ delta) ∧
      (∀ f ∈ F.carrier, ∀ g ∈ F.carrier, f ≠ g →
        |shift0 f - shift0 g| < c2Distance f g / (6 * K)) ∧
      (2 * tangency + 2) * delta < epsilon ∧
      epsilon ≤ 25 * tangency ^ 10 * delta ∧
      F.HasNoExactTangenciesOn I shiftUp ∧
      F.HasNoExactTangenciesOn I shiftDown := by
  let F : FiniteFunctionFamily :=
    { carrier := W.carrier ∪ B.carrier
      finite := W.finite.union B.finite }
  have hF_eq : F.carrier = W.carrier ∪ B.carrier := by rfl
  rcases exists_epsilon_for_shift_bound F K hK with ⟨epsilon', h_eps'_pos, h_shift_bound⟩
  let eps_pert : ℝ := min delta epsilon' / 2
  have h_eps_pert_pos : 0 < eps_pert := by
    dsimp only [eps_pert]
    have h1 : 0 < min delta epsilon' := lt_min hdelta h_eps'_pos
    linarith
  have h_pert_result := h_pert K D hK hD (W.carrier ∪ B.carrier) hfam I hI F
    (by simp [hF_eq]) eps_pert h_eps_pert_pos
  rcases h_pert_result with ⟨shift0, h_amp, h_no_tang0⟩
  have h_amp_delta : ∀ f ∈ F.carrier, |shift0 f| ≤ delta := by
    intro f hf
    have h : |shift0 f| ≤ eps_pert := h_amp f hf
    dsimp only [eps_pert] at h
    linarith [min_le_left delta epsilon']
  have h_amp_eps' : ∀ f ∈ F.carrier, |shift0 f| ≤ epsilon' := by
    intro f hf
    have h : |shift0 f| ≤ eps_pert := h_amp f hf
    dsimp only [eps_pert] at h
    linarith [min_le_right delta epsilon']
  have h_pairwise : ∀ f ∈ F.carrier, ∀ g ∈ F.carrier, f ≠ g →
      |shift0 f - shift0 g| < c2Distance f g / (6 * K) :=
    h_shift_bound shift0 h_amp_eps'
  let epsilonLow : ℝ := (2 * tangency + 2) * delta
  let epsilonHigh : ℝ := 25 * tangency ^ 10 * delta
  have h_range : epsilonLow < epsilonHigh := by
    dsimp only [epsilonLow, epsilonHigh]
    have h2 : 2 * tangency + 2 < 25 * tangency ^ 10 := by
      have h3 : 1 ≤ tangency := by linarith
      have h4 : 2 * tangency + 2 ≤ 3 * tangency := by linarith
      have h5 : 3 * tangency < 25 * tangency ^ 10 := by
        have h6 : 0 < tangency := by linarith
        have h7 : 1 < tangency ^ 9 := by
          have h8 : 5 ≤ tangency := htang
          have h9 : (1 : ℝ) < (5 : ℝ) ^ 9 := by norm_num
          have h10 : (5 : ℝ) ^ 9 ≤ tangency ^ 9 := by gcongr
          linarith
        nlinarith
      linarith
    nlinarith
  rcases bidirectional_shift_avoidance W B F I shift0
      (by simp [hF_eq]) h_no_tang0 epsilonLow epsilonHigh h_range
    with ⟨epsilon, h_eps_low, h_eps_high, h_no_tang_up, h_no_tang_down⟩
  refine ⟨shift0, epsilon, ?_⟩
  dsimp only
  exact ⟨h_amp_delta, h_pairwise, h_eps_low, le_of_lt h_eps_high, h_no_tang_up, h_no_tang_down⟩

/-- Distinct family members have distinct shifted versions. -/
lemma no_tangency_no_cross
    {F : FiniteFunctionFamily} {I : ParameterInterval}
    {shift : C2Function → ℝ}
    (h_no_tang : F.HasNoExactTangenciesOn I shift)
    {f g : C2Function} (hf : f ∈ F.carrier) (hg : g ∈ F.carrier)
    (hne : f ≠ g) :
    f.verticalTranslate (shift f) ≠ g.verticalTranslate (shift g) := by
  intro h_eq
  have hI_nonempty : I.carrier.Nonempty :=
    ⟨⟨I.left, I.left_mem⟩, by
      simp [ParameterInterval.carrier]
      exact I.left_le_right⟩
  rcases hI_nonempty with ⟨x, hx⟩
  have h := h_no_tang hf hg hne x hx
  have h_val : (f.verticalTranslate (shift f)) x = (g.verticalTranslate (shift g)) x := by
    rw [h_eq]
  have h_deriv : (f.verticalTranslate (shift f)).firstDeriv x =
      (g.verticalTranslate (shift g)).firstDeriv x := by
    rw [h_eq]
  rcases h with (h | h)
  · exact h h_val
  · exact h h_deriv

/--
Widen lens endpoint localization from a pair-dependent enlargement factor
`E_lens` to the uniform factor `E_abs`.
-/
lemma widen_lens_endpoints
    {K tangency delta t : ℝ} (hK : 1 ≤ K) (htang : 5 ≤ tangency)
    (_hdelta : 0 < delta) (ht : 0 < t)
    {w b : C2Function} (hsep : 2 * t ≤ c2Distance w b)
    {R : CurvilinearRectangle delta t}
    {L : GraphLens}
    (V E_abs E_lens : ℝ)
    (hV : V = 25 * tangency ^ 10 + 2 * tangency + 2)
    (hE_abs : E_abs = 12 * K * (V + 1) + Real.sqrt (6 * K * V))
    (hE_lens_def : E_lens = 2 * (2 * V + c2Distance w b / t) /
        (c2Distance w b / (6 * K * t)) +
        Real.sqrt (2 * V / (c2Distance w b / (6 * K * t))))
    (h_left : (L.left : ℝ) ∈ Set.Icc
        (R.interval.left - E_lens * Real.sqrt (delta / t))
        (R.interval.right + E_lens * Real.sqrt (delta / t)))
    (h_right : (L.right : ℝ) ∈ Set.Icc
        (R.interval.left - E_lens * Real.sqrt (delta / t))
        (R.interval.right + E_lens * Real.sqrt (delta / t))) :
    (L.left : ℝ) ∈ Set.Icc
        (R.interval.left - E_abs * Real.sqrt (delta / t))
        (R.interval.right + E_abs * Real.sqrt (delta / t)) ∧
    (L.right : ℝ) ∈ Set.Icc
        (R.interval.left - E_abs * Real.sqrt (delta / t))
        (R.interval.right + E_abs * Real.sqrt (delta / t)) := by
  have hV_nonneg : 0 ≤ V := by
    rw [hV]
    positivity
  set d : ℝ := c2Distance w b with hd_def
  set curvature : ℝ := d / (6 * K * t) with hcurv_def
  have hE_lens_le : E_lens ≤ E_abs :=
    E_lens_le_E_abs hK ht hsep V hV_nonneg curvature E_lens E_abs
      hcurv_def hE_lens_def hE_abs
  have hs_nonneg : 0 ≤ Real.sqrt (delta / t) := Real.sqrt_nonneg _
  exact ⟨
    mem_Icc_widen_factor hE_lens_le hs_nonneg h_left,
    mem_Icc_widen_factor hE_lens_le hs_nonneg h_right
  ⟩

/-- Final counting: combine up/down directional lens counts. -/
lemma final_counting_combination
    {C C_mt N : ℝ}
    {n_up n_down m_up m_down : ℕ}
    (hC_mt_pos : 0 < C_mt)
    (hC_mt_le : 4 * C_mt ≤ C)
    (hN : 2 ≤ N)
    (hm_up : (m_up : ℝ) ≤ N)
    (hm_down : (m_down : ℝ) ≤ N)
    (h_up : (n_up : ℝ) ≤ C_mt * Real.rpow (m_up : ℝ) (3 / 2 : ℝ) * Real.log ((m_up : ℝ) + 1))
    (h_down : (n_down : ℝ) ≤ C_mt * Real.rpow (m_down : ℝ) (3 / 2 : ℝ) * Real.log ((m_down : ℝ) + 1)) :
    ((n_up + n_down : ℕ) : ℝ) ≤ C * Real.rpow N (3 / 2 : ℝ) * Real.log N := by
  have h_main : (n_up : ℝ) + (n_down : ℝ) ≤
      C * Real.rpow N (3 / 2 : ℝ) * Real.log N :=
    bidirectional_graph_lens_count_bound
      hC_mt_pos hC_mt_le hN hm_up hm_down h_up h_down
  simpa using h_main

/-- Curve family cardinality is bounded by the bipartite normalized count at unit multiplicity. -/
lemma curves_card_le_bipartiteNormalizedCount
    {W B : FiniteFunctionFamily} {curves : Finset C2Function}
    (h_curves : curves.card ≤ W.card + B.card) :
    (curves.card : ℝ) ≤ RectangleFamily.bipartiteNormalizedCount W B 1 1 := by
  have h1 : RectangleFamily.bipartiteNormalizedCount W B 1 1 =
      (W.card : ℝ) + (B.card : ℝ) := by
    simp [RectangleFamily.bipartiteNormalizedCount]
  rw [h1]
  exact_mod_cast h_curves

end

end Kakeya.Cinematic
