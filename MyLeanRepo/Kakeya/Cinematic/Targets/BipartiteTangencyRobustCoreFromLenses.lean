import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyInputs
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.Sampling
import Mathlib.Data.Finset.Sort

/-!
# Sample the robust unit core

The graph-lens geometry is isolated in the unit-multiplicity core. This
target uses finite two-sided sampling to recover arbitrary tangency
thresholds `mu,nu`.

## Proof outline

Given the unit-multiplicity core (every rectangle has at least one tangent
of each color), we use `two_sided_sampling` to select subfamilies `W', B'`
of the white and black function families such that:

1. `|W'| ≤ 2|W|/mu` and `|B'| ≤ 2|B|/nu`.
2. A fixed fraction `c = (1 - e^{-1})^2` of rectangles still have at least
   one tangent in both `W'` and `B'`.

We then apply the unit core to the surviving rectangle subfamily and the
sampled function families. The normalized count for the unit core is
`|W'| + |B'| ≤ 2 * (|W|/mu + |B|/nu)`, and the surviving rectangle count
is at least `c * |R|`. Absorbing the fixed sampling losses into a larger
output constant `C` gives the desired bound.

The key geometric lemma is monotonicity of lambda-comparability: if two
rectangles are `λ₁`-comparable and `λ₁ ≤ λ₂`, then they are
`λ₂`-comparable (under admissibility). This lets us transfer the
incomparability hypothesis from the larger output scale `C * tangency^C`
down to the unit-core scale `C₀ * tangency^C₀`.
-/

namespace Kakeya.Cinematic

open Set

section Helpers

/-- Enlarge a parameter interval to a given length `L ≤ 1` while keeping
it inside `[0,1]` and containing the original interval. -/
lemma enlarge_parameter_interval (I : ParameterInterval) {L : ℝ}
    (hL : I.length ≤ L) (hL1 : L ≤ 1) :
    ∃ J : ParameterInterval, J.length = L ∧ I.carrier ⊆ J.carrier := by
  have hL_nonneg : 0 ≤ L := I.length_nonneg.trans hL
  let c := max 0 (I.right - L)
  have hc_nonneg : 0 ≤ c := le_max_left _ _
  have h1 : I.right - L ≤ I.left := by
    have h2 : I.right - I.left = I.length := by rfl
    linarith
  have hc_le_left : c ≤ I.left := by
    have h3 : 0 ≤ I.left := I.left_mem.1
    exact max_le h3 h1
  have hcL_eq : c + L = max L I.right := by
    dsimp only [c]
    by_cases h : 0 ≤ I.right - L
    · have hL_le_right : L ≤ I.right := by linarith
      rw [max_eq_right h, max_eq_right hL_le_right]
      <;> ring
    · have hright_lt_L : I.right < L := by linarith
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      <;> ring
  have hright_le_cL : I.right ≤ c + L := by
    rw [hcL_eq] <;> exact le_max_right _ _
  have hcL_le_one : c + L ≤ 1 := by
    rw [hcL_eq]
    exact max_le hL1 I.right_mem.2
  let J : ParameterInterval :=
    { left := c
      right := c + L
      left_mem := ⟨hc_nonneg, by
        have h : c ≤ I.left := hc_le_left
        have h' : I.left ≤ 1 := I.left_mem.2
        linarith⟩
      right_mem := ⟨by linarith, hcL_le_one⟩
      left_le_right := by linarith }
  have hJ_length : J.length = L := by
    simp [J, ParameterInterval.length] <;> ring
  have hI_sub_J : I.carrier ⊆ J.carrier := by
    intro x hx
    have hleft : c ≤ (x : ℝ) := hc_le_left.trans hx.1
    have hright : (x : ℝ) ≤ c + L := hx.2.trans hright_le_cL
    exact ⟨hleft, hright⟩
  exact ⟨J, hJ_length, hI_sub_J⟩

/-- Comparability is monotone in `λ` under admissibility of the larger
scale: a thicker rectangle can always be enlarged to contain a thinner one
that uses the same defining function. -/
lemma AreLambdaComparable_mono {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t)
    {R S : CurvilinearRectangle δ t} {family : Set C2Function}
    {lam1 lam2 : ℝ} (hlam1 : 0 ≤ lam1) (hlam : lam1 ≤ lam2)
    (hadm2 : IsAdmissibleComparisonScale δ t lam2) :
    CurvilinearRectangle.AreLambdaComparable R S family lam1 →
      CurvilinearRectangle.AreLambdaComparable R S family lam2 := by
  intro h
  rcases h with ⟨U, hUfam, hUcont⟩
  let L₂ := Real.sqrt (lam2 * δ / t)
  have hL2_le_one : L₂ ≤ 1 := by
    have h : lam2 * δ / t ≤ 1 := by
      rw [div_le_one ht] <;> exact hadm2.2
    have h5 : L₂ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h
    rw [Real.sqrt_one] at h5 <;> exact h5
  have hU_len : U.interval.length = Real.sqrt (lam1 * δ / t) := U.interval_length
  have h_len_le : U.interval.length ≤ L₂ := by
    rw [hU_len]
    have h : lam1 * δ / t ≤ lam2 * δ / t := by gcongr
    exact Real.sqrt_le_sqrt h
  rcases enlarge_parameter_interval U.interval h_len_le hL2_le_one with
    ⟨J, hJ_len, hJ_sub⟩
  let U' : CurvilinearRectangle (lam2 * δ) t :=
    { function := U.function
      interval := J
      interval_length := by
        have h : J.length = Real.sqrt (lam2 * δ / t) := by
          simpa [L₂] using hJ_len
        exact h }
  have hU_sub : U.carrier ⊆ U'.carrier := by
    intro p hp
    have h3 : p.1 ∈ J.carrier := hJ_sub hp.1
    have h4 : |p.2 - U'.function p.1| ≤ lam2 * δ := by
      have h5 : |p.2 - U.function p.1| ≤ lam1 * δ := hp.2
      have h6 : lam1 * δ ≤ lam2 * δ := by gcongr
      exact h5.trans h6
    exact ⟨h3, h4⟩
  exact ⟨U', hUfam, hUcont.trans hU_sub⟩

/-- Pairwise incomparability at a larger scale implies pairwise
incomparability at a smaller scale. -/
lemma IsPairwiseIncomparable_mono {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t)
    {R : RectangleFamily δ t} {family : Set C2Function}
    {lam1 lam2 : ℝ} (hlam1 : 0 ≤ lam1) (hlam : lam1 ≤ lam2)
    (hadm2 : IsAdmissibleComparisonScale δ t lam2) :
    R.IsPairwiseIncomparable family lam2 → R.IsPairwiseIncomparable family lam1 := by
  intro h i j hne
  have h' : (R.rectangle i).AreLambdaIncomparable (R.rectangle j) family lam2 :=
    h i j hne
  intro hcomp
  have hcomp2 : (R.rectangle i).AreLambdaComparable (R.rectangle j) family lam2 :=
    AreLambdaComparable_mono hδ ht hlam1 hlam hadm2 hcomp
  exact h' hcomp2

end Helpers

section SubfamilyHelpers

/-- Centers-in is inherited by subfamilies. -/
lemma RectangleSubfamily.centersIn {δ t : ℝ} {R : RectangleFamily δ t}
    (S : RectangleSubfamily R) {family : Set C2Function}
    (h : R.CentersIn family) : S.family.CentersIn family := by
  intro i
  exact h (S.embedding i)

/-- Over-central-quarter is inherited by subfamilies. -/
lemma RectangleSubfamily.isOverCentralQuarterOf {δ t : ℝ}
    {R : RectangleFamily δ t} (S : RectangleSubfamily R)
    {I : ParameterInterval} (h : R.IsOverCentralQuarterOf I) :
    S.family.IsOverCentralQuarterOf I := by
  intro i
  exact h (S.embedding i)

/-- Pairwise incomparability is inherited by subfamilies. -/
lemma RectangleSubfamily.isPairwiseIncomparable {δ t : ℝ}
    {R : RectangleFamily δ t} (S : RectangleSubfamily R)
    {family : Set C2Function} {lambda : ℝ}
    (h : R.IsPairwiseIncomparable family lambda) :
    S.family.IsPairwiseIncomparable family lambda := by
  intro i j hne
  have h_inj : S.embedding i ≠ S.embedding j := by
    intro h_eq
    exact hne (S.embedding.inj' h_eq)
  exact h (S.embedding i) (S.embedding j) h_inj

/-- Build a `FiniteFunctionFamily` from a `Finset C2Function`. -/
def FiniteFunctionFamily.mkFromFinset (s : Finset C2Function) :
    FiniteFunctionFamily :=
  { carrier := (s : Set C2Function)
    finite := s.finite_toSet }

lemma FiniteFunctionFamily.mkFromFinset_card (s : Finset C2Function) :
    (FiniteFunctionFamily.mkFromFinset s).card = s.card := by
  have h : (FiniteFunctionFamily.mkFromFinset s).carrier = (s : Set C2Function) := by rfl
  rw [FiniteFunctionFamily.card, h]
  simp

lemma FiniteFunctionFamily.mkFromFinset_toFinset (s : Finset C2Function) :
    (FiniteFunctionFamily.mkFromFinset s).toFinset = s := by
  apply Finset.coe_injective
  simp [FiniteFunctionFamily.mkFromFinset, FiniteFunctionFamily.toFinset]

/-- Separation is inherited by restricting to subfamilies. -/
lemma FiniteFunctionFamily.AreSeparated.mono
    {W B W' B' : FiniteFunctionFamily} {t : ℝ}
    (h : W.AreSeparated B t)
    (hW : W'.carrier ⊆ W.carrier) (hB : B'.carrier ⊆ B.carrier) :
    W'.AreSeparated B' t := by
  intro w hw b hb
  exact h (hW hw) (hB hb)

end SubfamilyHelpers

theorem bipartite_tangency_robust_core_from_graph_lenses :
    BipartiteTangencyRobustCoreFromUnitStatement := by
  classical
  intro h_unit
  intro K hK
  rcases h_unit K hK with ⟨c₂₀, C₀, hc₂₀_pos, hC₀_100, h_unit_prop⟩

  set c_survive : ℝ := (1 - Real.exp (-1)) ^ 2 with hc_survive_def
  have h_exp_lt_one : Real.exp (-1) < 1 := by
    have h := Real.exp_strictMono (by norm_num : (-1 : ℝ) < 0)
    rwa [Real.exp_zero] at h
  have h_exp_pos : 0 < Real.exp (-1) := Real.exp_pos (-1)
  have hc_survive_pos : 0 < c_survive := by
    rw [hc_survive_def]
    have h1 : 0 < 1 - Real.exp (-1) := by linarith
    positivity
  have hc_survive_lt_one : c_survive < 1 := by
    rw [hc_survive_def]
    have h1 : 0 < 1 - Real.exp (-1) := by linarith
    have h2 : 1 - Real.exp (-1) < 1 := by linarith
    nlinarith

  set K_const : ℝ := (1 / c_survive) * Real.rpow 2 (5 / 2 : ℝ) with hK_const_def
  have hK_const_gt_one : 1 < K_const := by
    rw [hK_const_def]
    have h1 : 1 < 1 / c_survive := by
      apply one_lt_one_div
      · exact hc_survive_pos
      · exact hc_survive_lt_one
    have h2 : 1 < Real.rpow 2 (5 / 2 : ℝ) := by
      have h3 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
      have h4 : (1 : ℝ) < (2 : ℝ) := by norm_num
      have h5 : (0 : ℝ) < (5 / 2 : ℝ) := by norm_num
      have h6 : (1 : ℝ) ^ (5 / 2 : ℝ) < (2 : ℝ) ^ (5 / 2 : ℝ) :=
        Real.rpow_lt_rpow h3 h4 h5
      simpa using h6
    have h5 : 0 < 1 / c_survive := by positivity
    nlinarith

  set C : ℝ := K_const * C₀ with hC_def
  have hC₀_pos : 0 < C₀ := by linarith
  have hC_ge_C₀ : C₀ ≤ C := by
    rw [hC_def]
    have h1 : 1 ≤ K_const := by linarith
    nlinarith
  have hC_100 : 100 ≤ C := by
    rw [hC_def]
    nlinarith
  have hC_pos : 0 < C := by positivity

  set c₂ : ℝ := c₂₀ with hc₂_def

  refine' ⟨c₂, C, hc₂₀_pos, hC_100, _⟩
  intro tangency htangency family hfamily I hI delta t hdelta ht hdt ht1
        hscale hadm W B hWsub hBsub hsep R hRcenters hRquarter hRincomp
        hRnonempty mu nu hmu hnu hcounts

  set lam1 : ℝ := C₀ * Real.rpow tangency C₀ with hlam1_def
  set lam2 : ℝ := C * Real.rpow tangency C with hlam2_def

  have hrpow_nonneg : 0 ≤ Real.rpow tangency C₀ := Real.rpow_nonneg (by linarith) _
  have hlam1_nonneg : 0 ≤ lam1 := by
    rw [hlam1_def]
    exact mul_nonneg (by linarith) hrpow_nonneg
  have hlam_le : lam1 ≤ lam2 := by
    have h1 : Real.rpow tangency C₀ ≤ Real.rpow tangency C :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hC_ge_C₀
    have h2 : C₀ * Real.rpow tangency C₀ ≤ C * Real.rpow tangency C₀ :=
      mul_le_mul_of_nonneg_right hC_ge_C₀ hrpow_nonneg
    have h3 : C * Real.rpow tangency C₀ ≤ C * Real.rpow tangency C :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [hlam1_def, hlam2_def]
    linarith

  have hscale₀ : Real.rpow tangency C₀ * delta ≤ c₂₀ * t / 2 := by
    have h1 : Real.rpow tangency C₀ ≤ Real.rpow tangency C :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hC_ge_C₀
    have h2 : Real.rpow tangency C₀ * delta ≤ Real.rpow tangency C * delta := by gcongr
    rw [hc₂_def] at hscale
    exact h2.trans hscale

  have hadm₀ : IsAdmissibleComparisonScale delta t lam1 := by
    have h1 : 1 ≤ lam1 := by
      rw [hlam1_def]
      have h2 : 1 ≤ C₀ := by linarith
      have h3 : 1 ≤ Real.rpow tangency C₀ := by
        have h4 : (1 : ℝ) ^ C₀ ≤ Real.rpow tangency C₀ :=
          Real.rpow_le_rpow (by norm_num) (by linarith) (by linarith)
        have h5 : (1 : ℝ) ^ C₀ = 1 := by simp
        rw [h5] at h4
        exact h4
      nlinarith
    have h4 : lam1 * delta ≤ t := by
      have h5 : lam1 ≤ lam2 := hlam_le
      have h6 : lam2 * delta ≤ t := hadm.2
      calc lam1 * delta ≤ lam2 * delta := by gcongr
           _ ≤ t := h6
    exact ⟨h1, h4⟩

  have hRincomp₀ : R.IsPairwiseIncomparable family lam1 :=
    IsPairwiseIncomparable_mono hdelta ht hlam1_nonneg hlam_le hadm hRincomp

  let T_W : Fin R.card → Finset C2Function := fun i =>
    W.toFinset.filter (fun f => (R.rectangle i).IsLambdaTangent f tangency)
  let T_B : Fin R.card → Finset C2Function := fun i =>
    B.toFinset.filter (fun f => (R.rectangle i).IsLambdaTangent f tangency)

  have hT_W_card : ∀ i, (T_W i).card =
      RectangleFamily.tangentCount (R.rectangle i) W tangency := by
    intro i
    simp [RectangleFamily.tangentCount, T_W]
  have hT_B_card : ∀ i, (T_B i).card =
      RectangleFamily.tangentCount (R.rectangle i) B tangency := by
    intro i
    simp [RectangleFamily.tangentCount, T_B]

  have hW_card : ∀ i ∈ (Finset.univ : Finset (Fin R.card)), mu ≤ (T_W i).card := by
    intro i _
    rw [hT_W_card i]
    exact (hcounts i).1
  have hB_card : ∀ i ∈ (Finset.univ : Finset (Fin R.card)), nu ≤ (T_B i).card := by
    intro i _
    rw [hT_B_card i]
    exact (hcounts i).2

  have hT_W_sub : ∀ i ∈ (Finset.univ : Finset (Fin R.card)), T_W i ⊆ W.toFinset := by
    intro i _
    exact Finset.filter_subset _ _
  have hT_B_sub : ∀ i ∈ (Finset.univ : Finset (Fin R.card)), T_B i ⊆ B.toFinset := by
    intro i _
    exact Finset.filter_subset _ _

  rcases two_sided_sampling W.toFinset B.toFinset (Finset.univ : Finset (Fin R.card))
      T_W T_B mu nu hmu hnu hW_card hB_card hT_W_sub hT_B_sub
    with ⟨W', B', hW'_sub, hB'_sub, hW'_card, hB'_card, hsurvive⟩

  let R_survive : Finset (Fin R.card) :=
    Finset.univ.filter (fun i => (T_W i ∩ W').Nonempty ∧ (T_B i ∩ B').Nonempty)

  have hsurvive' : c_survive * (R.card : ℝ) ≤ (R_survive.card : ℝ) := by
    simpa [R_survive, c_survive] using hsurvive

  let e : Fin R_survive.card ≃o R_survive := Finset.orderIsoOfFin R_survive rfl
  let R' : RectangleSubfamily R :=
    { card := R_survive.card
      embedding :=
        { toFun := fun j => (e j : Fin R.card)
          inj' := by
            intro j1 j2 h
            have h' : e j1 = e j2 := by
              exact Subtype.ext h
            exact e.injective h' } }

  let W'_fam : FiniteFunctionFamily :=
    FiniteFunctionFamily.mkFromFinset W'
  let B'_fam : FiniteFunctionFamily :=
    FiniteFunctionFamily.mkFromFinset B'

  have hR'_nonempty : 0 < R'.card := by
    have h1 : 0 < (R.card : ℝ) := by exact_mod_cast hRnonempty
    have h2 : 0 < (R_survive.card : ℝ) := by
      calc 0 < c_survive * (R.card : ℝ) := by positivity
           _ ≤ (R_survive.card : ℝ) := hsurvive'
    exact_mod_cast h2

  have hW'_fam_sub : W'_fam.carrier ⊆ family := by
    have h1 : (W' : Set C2Function) ⊆ (W.toFinset : Set C2Function) := by
      exact_mod_cast hW'_sub
    have h2 : (W.toFinset : Set C2Function) = W.carrier := by
      exact Set.Finite.coe_toFinset W.finite
    simpa [W'_fam, FiniteFunctionFamily.mkFromFinset] using h1.trans (h2 ▸ hWsub)

  have hB'_fam_sub : B'_fam.carrier ⊆ family := by
    have h1 : (B' : Set C2Function) ⊆ (B.toFinset : Set C2Function) := by
      exact_mod_cast hB'_sub
    have h2 : (B.toFinset : Set C2Function) = B.carrier := by
      exact Set.Finite.coe_toFinset B.finite
    simpa [B'_fam, FiniteFunctionFamily.mkFromFinset] using h1.trans (h2 ▸ hBsub)

  have hW'_sub_W : W'_fam.carrier ⊆ W.carrier := by
    have h1 : (W' : Set C2Function) ⊆ (W.toFinset : Set C2Function) := by exact_mod_cast hW'_sub
    have h2 : (W.toFinset : Set C2Function) = W.carrier := by
      exact Set.Finite.coe_toFinset W.finite
    have h3 : W'_fam.carrier = (W' : Set C2Function) := by rfl
    rw [h3]
    rw [h2] at h1
    exact h1
  have hB'_sub_B : B'_fam.carrier ⊆ B.carrier := by
    have h1 : (B' : Set C2Function) ⊆ (B.toFinset : Set C2Function) := by exact_mod_cast hB'_sub
    have h2 : (B.toFinset : Set C2Function) = B.carrier := by
      exact Set.Finite.coe_toFinset B.finite
    have h3 : B'_fam.carrier = (B' : Set C2Function) := by rfl
    rw [h3]
    rw [h2] at h1
    exact h1
  have hsep' : W'_fam.AreSeparated B'_fam (2 * t) :=
    hsep.mono hW'_sub_W hB'_sub_B

  have hR'_centers : R'.family.CentersIn family :=
    R'.centersIn hRcenters
  have hR'_quarter : R'.family.IsOverCentralQuarterOf I :=
    R'.isOverCentralQuarterOf hRquarter
  have hR'_incomp : R'.family.IsPairwiseIncomparable family lam1 :=
    R'.isPairwiseIncomparable hRincomp₀

  have hcounts' : ∀ j : Fin R'.card,
      1 ≤ RectangleFamily.tangentCount (R'.family.rectangle j) W'_fam tangency ∧
      1 ≤ RectangleFamily.tangentCount (R'.family.rectangle j) B'_fam tangency := by
    intro j
    let i : Fin R.card := R'.embedding j
    have hi_survive : i ∈ R_survive := (e j).property
    have h_i_def : (T_W i ∩ W').Nonempty ∧ (T_B i ∩ B').Nonempty :=
      (Finset.mem_filter.mp hi_survive).2
    have hW'_toFinset : W'_fam.toFinset = W' :=
      FiniteFunctionFamily.mkFromFinset_toFinset W'
    have hB'_toFinset : B'_fam.toFinset = B' :=
      FiniteFunctionFamily.mkFromFinset_toFinset B'
    have h_rect_eq : R'.family.rectangle j = R.rectangle i := by
      rfl
    constructor
    · rw [h_rect_eq]
      rcases h_i_def.1 with ⟨f, hf⟩
      have hf_in_TW : f ∈ T_W i := (Finset.mem_inter.mp hf).1
      have hf_in_W' : f ∈ W' := (Finset.mem_inter.mp hf).2
      have h_tangent : (R.rectangle i).IsLambdaTangent f tangency :=
        (Finset.mem_filter.mp hf_in_TW).2
      have h_in_filter : f ∈ W'_fam.toFinset.filter
          (fun g => (R.rectangle i).IsLambdaTangent g tangency) := by
        rw [Finset.mem_filter]
        exact ⟨by rwa [hW'_toFinset], h_tangent⟩
      have h_nonempty : (W'_fam.toFinset.filter
          (fun g => (R.rectangle i).IsLambdaTangent g tangency)).Nonempty :=
        ⟨f, h_in_filter⟩
      have h_card_pos : 0 < (W'_fam.toFinset.filter
          (fun g => (R.rectangle i).IsLambdaTangent g tangency)).card :=
        Finset.card_pos.mpr h_nonempty
      simpa [RectangleFamily.tangentCount] using h_card_pos
    · rw [h_rect_eq]
      rcases h_i_def.2 with ⟨f, hf⟩
      have hf_in_TB : f ∈ T_B i := (Finset.mem_inter.mp hf).1
      have hf_in_B' : f ∈ B' := (Finset.mem_inter.mp hf).2
      have h_tangent : (R.rectangle i).IsLambdaTangent f tangency :=
        (Finset.mem_filter.mp hf_in_TB).2
      have h_in_filter : f ∈ B'_fam.toFinset.filter
          (fun g => (R.rectangle i).IsLambdaTangent g tangency) := by
        rw [Finset.mem_filter]
        exact ⟨by rwa [hB'_toFinset], h_tangent⟩
      have h_nonempty : (B'_fam.toFinset.filter
          (fun g => (R.rectangle i).IsLambdaTangent g tangency)).Nonempty :=
        ⟨f, h_in_filter⟩
      have h_card_pos : 0 < (B'_fam.toFinset.filter
          (fun g => (R.rectangle i).IsLambdaTangent g tangency)).card :=
        Finset.card_pos.mpr h_nonempty
      simpa [RectangleFamily.tangentCount] using h_card_pos

  have h_unit_result := h_unit_prop tangency htangency family hfamily I hI
      delta t hdelta ht hdt ht1 hscale₀ hadm₀
      W'_fam B'_fam hW'_fam_sub hB'_fam_sub hsep'
      R'.family hR'_centers hR'_quarter hR'_incomp hR'_nonempty hcounts'

  set X : ℝ := RectangleFamily.bipartiteNormalizedCount W B mu nu with hX_def
  set X₀ : ℝ := RectangleFamily.bipartiteNormalizedCount W'_fam B'_fam 1 1 with hX0_def

  have hX_ge2 : 2 ≤ X := by
    let i : Fin R.card := Classical.choice (Fin.pos_iff_nonempty.mp hRnonempty)
    have h1 : mu ≤ W.card :=
      (hcounts i).1.trans (RectangleFamily.tangentCount_le_card (R.rectangle i) W tangency)
    have h2 : nu ≤ B.card :=
      (hcounts i).2.trans (RectangleFamily.tangentCount_le_card (R.rectangle i) B tangency)
    simp [hX_def, RectangleFamily.bipartiteNormalizedCount]
    have h4 : (mu : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast h1
    have h5 : (nu : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast h2
    have h6 : (0 : ℝ) < (mu : ℝ) := by exact_mod_cast hmu
    have h7 : (0 : ℝ) < (nu : ℝ) := by exact_mod_cast hnu
    have h8 : (1 : ℝ) ≤ (W.card : ℝ) / (mu : ℝ) := by
      rw [le_div_iff₀ h6] <;> linarith
    have h9 : (1 : ℝ) ≤ (B.card : ℝ) / (nu : ℝ) := by
      rw [le_div_iff₀ h7] <;> linarith
    linarith

  have hX0_eq : X₀ = (W'_fam.card : ℝ) + (B'_fam.card : ℝ) := by
    simp [hX0_def, RectangleFamily.bipartiteNormalizedCount] <;> ring

  have hW'_fam_card : W'_fam.card = W'.card :=
    FiniteFunctionFamily.mkFromFinset_card W'
  have hB'_fam_card : B'_fam.card = B'.card :=
    FiniteFunctionFamily.mkFromFinset_card B'

  have hX0_le : X₀ ≤ 2 * X := by
    rw [hX0_eq, hW'_fam_card, hB'_fam_card]
    have hW_eq : (W.toFinset.card : ℝ) = (W.card : ℝ) := by
      have h1 : (W.toFinset : Set C2Function) = W.carrier := Set.Finite.coe_toFinset W.finite
      have h2 : (W.toFinset : Set C2Function).ncard = W.toFinset.card := by simp
      have h3 : W.card = W.carrier.ncard := by rfl
      exact_mod_cast (Eq.trans h2.symm (by rw [h1, h3]))
    have hB_eq : (B.toFinset.card : ℝ) = (B.card : ℝ) := by
      have h1 : (B.toFinset : Set C2Function) = B.carrier := Set.Finite.coe_toFinset B.finite
      have h2 : (B.toFinset : Set C2Function).ncard = B.toFinset.card := by simp
      have h3 : B.card = B.carrier.ncard := by rfl
      exact_mod_cast (Eq.trans h2.symm (by rw [h1, h3]))
    have h1 : (W'.card : ℝ) ≤ 2 * (W.card : ℝ) / (mu : ℝ) := by
      have h4 := hW'_card
      rw [hW_eq] at h4
      exact h4
    have h2 : (B'.card : ℝ) ≤ 2 * (B.card : ℝ) / (nu : ℝ) := by
      have h4 := hB'_card
      rw [hB_eq] at h4
      exact h4
    have hX_expand : X = (W.card : ℝ) / (mu : ℝ) + (B.card : ℝ) / (nu : ℝ) := by
      rw [hX_def, RectangleFamily.bipartiteNormalizedCount]
      <;> rfl
    rw [hX_expand]
    have h3 : (W'.card : ℝ) + (B'.card : ℝ) ≤
        2 * (W.card : ℝ) / (mu : ℝ) + 2 * (B.card : ℝ) / (nu : ℝ) :=
      add_le_add h1 h2
    have h4 : 2 * (W.card : ℝ) / (mu : ℝ) + 2 * (B.card : ℝ) / (nu : ℝ) =
        2 * ((W.card : ℝ) / (mu : ℝ) + (B.card : ℝ) / (nu : ℝ)) := by ring
    rw [h4] at h3
    exact h3

  have hX0_pos : 0 < X₀ := by
    rw [hX0_eq]
    let j : Fin R'.card := Classical.choice (Fin.pos_iff_nonempty.mp hR'_nonempty)
    let i : Fin R.card := R'.embedding j
    have hi_survive : i ∈ R_survive := (e j).property
    have h3 : (T_W i ∩ W').Nonempty := ((Finset.mem_filter.mp hi_survive).2).1
    have h4 : (T_B i ∩ B').Nonempty := ((Finset.mem_filter.mp hi_survive).2).2
    have h5 : W'.Nonempty := h3.mono (by simp)
    have h6 : B'.Nonempty := h4.mono (by simp)
    have h7 : 0 < (W'_fam.card : ℝ) := by
      rw [hW'_fam_card]
      exact_mod_cast Finset.card_pos.mpr h5
    have h8 : 0 < (B'_fam.card : ℝ) := by
      rw [hB'_fam_card]
      exact_mod_cast Finset.card_pos.mpr h6
    exact add_pos h7 h8

  have hX0_ge2 : 2 ≤ X₀ := by
    rw [hX0_eq, hW'_fam_card, hB'_fam_card]
    let j : Fin R'.card := Classical.choice (Fin.pos_iff_nonempty.mp hR'_nonempty)
    let i : Fin R.card := R'.embedding j
    have hi_survive : i ∈ R_survive := (e j).property
    have h3 : (T_W i ∩ W').Nonempty := ((Finset.mem_filter.mp hi_survive).2).1
    have h4 : (T_B i ∩ B').Nonempty := ((Finset.mem_filter.mp hi_survive).2).2
    have h5 : W'.Nonempty := h3.mono (by simp)
    have h6 : B'.Nonempty := h4.mono (by simp)
    have h7 : 1 ≤ (W'.card : ℝ) := by
      have h71 : 0 < W'.card := Finset.card_pos.mpr h5
      exact_mod_cast Nat.succ_le_iff.mpr h71
    have h8 : 1 ≤ (B'.card : ℝ) := by
      have h81 : 0 < B'.card := Finset.card_pos.mpr h6
      exact_mod_cast Nat.succ_le_iff.mpr h81
    linarith

  have hX_pos : 0 < X := by linarith [hX_ge2]

  have h_log2x : Real.log (2 * X) ≤ 2 * Real.log X := by
    have h1 : Real.log (2 * X) = Real.log 2 + Real.log X :=
      Real.log_mul (by norm_num) hX_pos.ne'
    rw [h1]
    have h2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) (by linarith)
    linarith

  have h_rpow2 : Real.rpow (2 * X) (3 / 2 : ℝ) =
      Real.rpow 2 (3 / 2 : ℝ) * Real.rpow X (3 / 2 : ℝ) := by
    have h2pos : 0 ≤ (2 : ℝ) := by norm_num
    have hXnonneg : 0 ≤ X := by linarith
    exact Real.mul_rpow h2pos hXnonneg

  have h_252 : Real.rpow 2 (5 / 2 : ℝ) =
      Real.rpow 2 (3 / 2 : ℝ) * 2 := by
    have h1 : (5 / 2 : ℝ) = (3 / 2 : ℝ) + 1 := by norm_num
    rw [h1]
    have h2 : Real.rpow 2 ((3 / 2 : ℝ) + 1) =
        Real.rpow 2 (3 / 2 : ℝ) * Real.rpow 2 1 :=
      Real.rpow_add (by norm_num) (3 / 2 : ℝ) 1
    rw [h2]
    have h3 : Real.rpow 2 1 = 2 := Real.rpow_one 2
    rw [h3] <;> ring

  have h1 : (R.card : ℝ) ≤ (R_survive.card : ℝ) / c_survive := by
    have h2 : c_survive * (R.card : ℝ) ≤ (R_survive.card : ℝ) := hsurvive'
    have h3 : 0 < c_survive := hc_survive_pos
    calc
      (R.card : ℝ) = (c_survive * (R.card : ℝ)) / c_survive := by
        field_simp [h3.ne'] <;> ring
      _ ≤ (R_survive.card : ℝ) / c_survive := by gcongr

  have h4 : (R_survive.card : ℝ) = (R'.card : ℝ) := by rfl

  have h_main1 : (R.card : ℝ) ≤ (1 / c_survive) * C₀ *
      Real.rpow tangency C₀ * Real.rpow X₀ (3 / 2 : ℝ) * Real.log X₀ := by
    have h1' : (R.card : ℝ) ≤ (R'.card : ℝ) / c_survive := by
      have h5 : (R.card : ℝ) ≤ (R_survive.card : ℝ) / c_survive := h1
      rw [h4] at h5
      exact h5
    calc
      (R.card : ℝ) ≤ (R'.card : ℝ) / c_survive := h1'
      _ = (1 / c_survive) * (R'.card : ℝ) := by ring
      _ ≤ (1 / c_survive) * (C₀ * Real.rpow tangency C₀ *
            Real.rpow X₀ (3 / 2 : ℝ) * Real.log X₀) := by
          have hpos : 0 ≤ (1 / c_survive) := by positivity
          exact mul_le_mul_of_nonneg_left h_unit_result hpos
      _ = (1 / c_survive) * C₀ * Real.rpow tangency C₀ *
            Real.rpow X₀ (3 / 2 : ℝ) * Real.log X₀ := by ring

  have h_X0_rpow : Real.rpow X₀ (3 / 2 : ℝ) ≤
      Real.rpow (2 * X) (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hX0_le (by norm_num)

  have h_X0_log : Real.log X₀ ≤ Real.log (2 * X) :=
    Real.log_le_log hX0_pos (by linarith)

  have h_coeff1_nonneg : 0 ≤ (1 / c_survive) * C₀ * Real.rpow tangency C₀ := by
    have h1 : 0 ≤ 1 / c_survive := by positivity
    have h2 : 0 ≤ C₀ := by linarith
    have h3 : 0 ≤ Real.rpow tangency C₀ := Real.rpow_nonneg (by linarith) _
    positivity

  have h_main2 : (R.card : ℝ) ≤ (1 / c_survive) * C₀ *
      Real.rpow tangency C₀ * Real.rpow (2 * X) (3 / 2 : ℝ) * Real.log (2 * X) := by
    have h4 : Real.rpow X₀ (3 / 2 : ℝ) * Real.log X₀ ≤
        Real.rpow (2 * X) (3 / 2 : ℝ) * Real.log (2 * X) := by
      have h4a : 0 ≤ Real.rpow X₀ (3 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
      have h4b : 0 ≤ Real.log X₀ := Real.log_nonneg (by linarith [hX0_ge2])
      have h4c : 0 ≤ Real.rpow (2 * X) (3 / 2 : ℝ) :=
        Real.rpow_nonneg (by linarith) _
      exact mul_le_mul h_X0_rpow h_X0_log h4b h4c
    calc
      (R.card : ℝ) ≤ (1 / c_survive) * C₀ * Real.rpow tangency C₀ *
          Real.rpow X₀ (3 / 2 : ℝ) * Real.log X₀ := h_main1
      _ = (1 / c_survive) * C₀ * Real.rpow tangency C₀ *
          (Real.rpow X₀ (3 / 2 : ℝ) * Real.log X₀) := by ring
      _ ≤ (1 / c_survive) * C₀ * Real.rpow tangency C₀ *
          (Real.rpow (2 * X) (3 / 2 : ℝ) * Real.log (2 * X)) := by
        exact mul_le_mul_of_nonneg_left h4 h_coeff1_nonneg
      _ = (1 / c_survive) * C₀ * Real.rpow tangency C₀ *
          Real.rpow (2 * X) (3 / 2 : ℝ) * Real.log (2 * X) := by ring

  have h_rpow23_nonneg :
      0 ≤ Real.rpow 2 (3 / 2 : ℝ) * Real.rpow X (3 / 2 : ℝ) := by
    have h1 : 0 ≤ Real.rpow 2 (3 / 2 : ℝ) :=
      Real.rpow_nonneg (by norm_num) _
    have h2 : 0 ≤ Real.rpow X (3 / 2 : ℝ) :=
      Real.rpow_nonneg (by linarith) _
    positivity

  have h_main3 : (R.card : ℝ) ≤ K_const * C₀ *
      Real.rpow tangency C₀ * Real.rpow X (3 / 2 : ℝ) * Real.log X := by
    have h5 : Real.log (2 * X) ≤ 2 * Real.log X := h_log2x
    have h7 : 0 ≤ (1 / c_survive) * C₀ * Real.rpow tangency C₀ *
          (Real.rpow 2 (3 / 2 : ℝ) * Real.rpow X (3 / 2 : ℝ)) := by positivity
    have h6 : (1 / c_survive) * C₀ * Real.rpow tangency C₀ *
          (Real.rpow 2 (3 / 2 : ℝ) * Real.rpow X (3 / 2 : ℝ)) * Real.log (2 * X) ≤
        (1 / c_survive) * C₀ * Real.rpow tangency C₀ *
          (Real.rpow 2 (3 / 2 : ℝ) * Real.rpow X (3 / 2 : ℝ)) *
          (2 * Real.log X) :=
      mul_le_mul_of_nonneg_left h5 h7
    calc
      (R.card : ℝ) ≤ (1 / c_survive) * C₀ * Real.rpow tangency C₀ *
          Real.rpow (2 * X) (3 / 2 : ℝ) * Real.log (2 * X) := h_main2
      _ = (1 / c_survive) * C₀ * Real.rpow tangency C₀ *
          (Real.rpow 2 (3 / 2 : ℝ) * Real.rpow X (3 / 2 : ℝ)) *
          Real.log (2 * X) := by rw [h_rpow2] <;> ring
      _ ≤ (1 / c_survive) * C₀ * Real.rpow tangency C₀ *
          (Real.rpow 2 (3 / 2 : ℝ) * Real.rpow X (3 / 2 : ℝ)) *
          (2 * Real.log X) := h6
      _ = ((1 / c_survive) * Real.rpow 2 (3 / 2 : ℝ) * 2) * C₀ *
          Real.rpow tangency C₀ * Real.rpow X (3 / 2 : ℝ) * Real.log X := by ring
      _ = K_const * C₀ * Real.rpow tangency C₀ *
          Real.rpow X (3 / 2 : ℝ) * Real.log X := by
            have h_eq1 : (1 / c_survive) * Real.rpow 2 (3 / 2 : ℝ) * 2 =
                (1 / c_survive) * Real.rpow 2 (5 / 2 : ℝ) := by
              rw [h_252] <;> ring
            have h_eq2 : (1 / c_survive) * Real.rpow 2 (5 / 2 : ℝ) = K_const := by
              rw [hK_const_def]
            rw [h_eq1, h_eq2] <;> ring

  have h_rpow_le : Real.rpow tangency C₀ ≤ Real.rpow tangency C :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hC_ge_C₀

  have h_pos_rpowX : 0 < Real.rpow X (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hX_pos _
  have h_pos_logX : 0 < Real.log X := Real.log_pos (by linarith)
  have h_pos_C : 0 < C := hC_pos

  have h_final : (R.card : ℝ) ≤ C * Real.rpow tangency C *
      Real.rpow X (3 / 2 : ℝ) * Real.log X := by
    have h9 : K_const * C₀ = C := by
      rw [hC_def] <;> ring
    have h10 : C * Real.rpow tangency C₀ * Real.rpow X (3 / 2 : ℝ) * Real.log X ≤
        C * Real.rpow tangency C * Real.rpow X (3 / 2 : ℝ) * Real.log X := by
      have h11 : 0 ≤ C * Real.rpow X (3 / 2 : ℝ) * Real.log X := by positivity
      have h12 : (C * Real.rpow X (3 / 2 : ℝ) * Real.log X) *
          Real.rpow tangency C₀ ≤
          (C * Real.rpow X (3 / 2 : ℝ) * Real.log X) *
            Real.rpow tangency C :=
        mul_le_mul_of_nonneg_left h_rpow_le h11
      have h13 : C * Real.rpow tangency C₀ * Real.rpow X (3 / 2 : ℝ) * Real.log X =
          (C * Real.rpow X (3 / 2 : ℝ) * Real.log X) * Real.rpow tangency C₀ := by ring
      have h14 : C * Real.rpow tangency C * Real.rpow X (3 / 2 : ℝ) * Real.log X =
          (C * Real.rpow X (3 / 2 : ℝ) * Real.log X) * Real.rpow tangency C := by ring
      rw [h13, h14]
      exact h12
    calc
      (R.card : ℝ) ≤ K_const * C₀ * Real.rpow tangency C₀ *
          Real.rpow X (3 / 2 : ℝ) * Real.log X := h_main3
      _ = C * Real.rpow tangency C₀ * Real.rpow X (3 / 2 : ℝ) * Real.log X := by
            rw [h9] <;> ring
      _ ≤ C * Real.rpow tangency C * Real.rpow X (3 / 2 : ℝ) * Real.log X := h10

  have h_lam2_eq : lam2 = C * Real.rpow tangency C := by
    simp [lam2, hlam2_def]
  have h_goal : (R.card : ℝ) ≤ lam2 * Real.rpow X (3 / 2 : ℝ) * Real.log X := by
    rw [h_lam2_eq]
    exact h_final
  exact h_goal

end Kakeya.Cinematic
