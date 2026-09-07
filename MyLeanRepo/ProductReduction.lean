module

/-
# Product-Like Structure Reduction

This module reduces the target theorem `product_like_incidence_sum_product` to a
key incidence lemma that uses `WeakTwoEndsSumProduct`.

## Proof outline

1. **Duality**: Map the tube union 𝒯 to a parameter set P in (a,b)-space via
   canonical parameter cubes.
2. **Covering number = cardinality**: The map T ↦ canonical parameter cube is
   injective, and δ-dyadic cubes are disjoint, so `dyadicCoveringNumber δ P =
   𝒯.encard`.
3. **Fiber condition**: For each incidence point z=(x,y), the parameter set P_z
   of tubes through z is a (δ,s,C)-set contained in P, and every point of P_z
   lies within 2δ of the dual line {p | p₀*y + p₁ = x}.
4. **Key lemma**: A parameter set P with this product-like fiber structure must
   have covering number ≥ δ^{-2s-η}, using WeakTwoEndsSumProduct.
5. **Conclusion**: Since covering number equals tube encard, the tube union is
   large.

## Dependencies

- `MyLeanRepo.CoreDefinitions`
- `MyLeanRepo.ProductLikeBasic`
- `MyLeanRepo.DualityBridge`
- `MyLeanRepo.ProjectionBasic`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.DualityBridge
public import MyLeanRepo.TauMonotonicity
public import MyLeanRepo.ProductLikeIncidence.KeyLemmaIncidence
public import MyLeanRepo.ProductLikeIncidence.EnergyCauchySchwarz
public import MyLeanRepo.ProductLikeIncidence.IncidenceToRingInput
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV3
public import MyLeanRepo.ProductLikeIncidence.PopularityThresholds
public import MyLeanRepo.ProductLikeIncidence.FrostmanFromDeltaSet
public import MyLeanRepo.ThreeDirectionBSG
public import MyLeanRepo.Lemma51Corollary
public import MyLeanRepo.OSWPrelude
public import MyLeanRepo.ProductLikeIncidence.Phase0Absorption
public import MyLeanRepo.ProductLikeIncidence.ExtractionNumericConditions
public import MyLeanRepo.ProductLikeIncidence.LogAbsorbThreshold
public import MyLeanRepo.ProductLikeIncidence.BoxBoundThreshold
public import MyLeanRepo.ProductLikeIncidence.ProductReductionHelpers

@[expose] public section

set_option maxHeartbeats 500000

open Set Bornology ENNReal MeasureTheory

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-! ## WeakTwoEndsSumProduct

Uses the lower-free root-namespace definition from `ProjectionBasic.lean`.
The Ring theorem has NO lower-size premise; only an upper bound is required.

Local helpers `Nreal` and `IsDirectionFrostman` are defined below for
convenience in this namespace. -/

/-- Covering number of a real set at scale δ. -/
noncomputable def Nreal (δ : ℝ) (A : Set ℝ) : ENNReal :=
  ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A))

/-- A Frostman-type measure condition: μ has mass 1 on [0,1] and
    μ(I) ≤ C * r^κ for intervals of radius r. -/
def IsDirectionFrostman (δ κ C : ℝ) (μ : Measure ℝ) : Prop :=
  μ Set.univ = 1 ∧
    μ.support ⊆ Set.Icc 0 1 ∧
    ∀ (a r : ℝ), δ ≤ r → r ≤ 1 →
      μ (Set.Icc (a - r) (a + r)) ≤
        ENNReal.ofReal (C * r ^ κ)


/-! ## Energy and Cauchy-Schwarz -/

/-- General double-counting + Cauchy-Schwarz energy bound.

Given finite sets `s`, `t` and a relation `R`, let `f a = |{b ∈ t : R a b}|`
and `g b = |{a ∈ s : R a b}|`. Then `(Σ f)^2 ≤ |t| · Σ g²`.

This is the standard incidence energy bound. -/
lemma cauchy_schwarz_energy {α β : Type*} (s : Finset α) (t : Finset β)
    (R : α → β → Prop) [DecidableRel R] :
    (∑ a ∈ s, (t.filter (R a)).card) ^ 2 ≤
      t.card * ∑ b ∈ t, (s.filter (fun a => R a b)).card ^ 2 := by
  have h_double : (∑ a ∈ s, (t.filter (R a)).card) =
      ∑ b ∈ t, (s.filter (fun a => R a b)).card := by
    have h : ∀ a ∈ s, (t.filter (R a)).card = ∑ b ∈ t, if R a b then 1 else 0 := by
      intro a _
      simp [Finset.filter_eq']
      <;> rfl
    rw [Finset.sum_congr rfl h]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    have h2 : (s.filter (fun a => R a b)).card = ∑ a ∈ s, if R a b then 1 else 0 := by
      simp [Finset.filter_eq'] <;> rfl
    rw [h2]
  rw [h_double]
  exact sq_sum_le_card_mul_sum_sq (s := t) (f := fun b => (s.filter (fun a => R a b)).card)

/-- **Ring theorem contradiction.**

Given the Ring theorem conclusion at specific `εnc`, `εgain`, if `A ⊆ [1,2]` is a
`(δ, κ0, K·δ^{-εnc})`-set with covering number in the right range, and `μ` is a
Frostman measure, then it is impossible that `|A + x·A|_δ < δ^{-εgain} · |A|_δ`
for all `x ∈ supp μ`.

This is the contrapositive of the Ring theorem, packaged for use in the
incidence contradiction. -/
lemma ring_contradiction
    {s κ0 εnc εgain δ K : ℝ}
    (h_ring : ∀ (A : Set ℝ) (μ : Measure ℝ),
      A ⊆ Set.Icc 1 2 →
      IsProductLikeRealDeltaSCSet δ κ0 (K * δ ^ (-εnc)) A →
      Nreal δ A ≤ ENNReal.ofReal (K * δ ^ (-(s + εnc))) →
      IsDirectionFrostman δ κ0 (K * δ ^ (-εnc)) μ →
      ∃ x ∈ μ.support,
        ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ A ≤
          Nreal δ (Set.image2 (fun a b => a + x * b) A A))
    (hK_ge1 : 1 ≤ K) (hδ_pos : 0 < δ)
    {A : Set ℝ} {μ : Measure ℝ}
    (hA_sub : A ⊆ Set.Icc 1 2)
    (hA_delta : IsProductLikeRealDeltaSCSet δ κ0 (K * δ ^ (-εnc)) A)
    (hA_upper : Nreal δ A ≤ ENNReal.ofReal (K * δ ^ (-(s + εnc))))
    (hμ_frostman : IsDirectionFrostman δ κ0 (K * δ ^ (-εnc)) μ)
    (h_small : ∀ x ∈ μ.support,
      Nreal δ (Set.image2 (fun a b => a + x * b) A A) <
      ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ A) : False := by
  rcases h_ring A μ hA_sub hA_delta hA_upper hμ_frostman with ⟨x, hx, h_ge⟩
  have h_lt := h_small x hx
  exact not_le.mpr h_lt h_ge

/-! ## Three-direction incidence-to-ring bridge -/

-- The authoritative `incidence_to_ring_contradiction` lives in
-- `MyLeanRepo.ProductLikeIncidence.IncidenceToRingInput`.
-- It is imported below and called at the end of the key lemma.

/-! ## Extracted contradiction wrapper

This lemma exists ONLY to keep the `incidence_to_ring_contradiction` application
in a small, clean context. The key lemma's proof context contains hundreds of
intermediate hypotheses, which caused Lean's isDefEq to time out when applying
the contradiction lemma with ~40 explicit arguments. By forwarding through this
thin wrapper, the application happens in a focused scope. -/

lemma key_lemma_contradiction
    {δ s τ κ0 η η_work ε L_exp p_projective C C_work K_ring K_diff εnc εgain rho_sel rho_sep : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hδ_le_one : δ ≤ 1)
    (hs_pos : 0 < s) (hs_lt_one : s < 1) (hτ_pos : 0 < τ)
    (hkappa_pos : 0 < κ0) (hkappa_lt_s : κ0 < s) (h2kappa_lt_tau : 2 * κ0 < τ)
    (hη_pos : 0 < η)
    (hη_work_pos : 0 < η_work)
    (hη_lt_work : η < η_work)
    (hη_work_eq_two : η_work = 2 * η)
    (hε_pos : 0 < ε)
    (h10ε_lt_η_work : 10 * ε < η_work)
    (h5η_work_lt : 5 * η_work < 2 * (s - κ0))
    (h4η_work_lt_tau : 4 * η_work < τ)
    (hL_exp_pos : 0 < L_exp)
    (hL_exp_eq_seven : L_exp = 7)
    (hη_work_le_kappa0 : η_work ≤ κ0)
    (hp_ge_10 : 10 ≤ p_projective)
    (hC_ge1 : 1 ≤ C)
    (hC_le_target : C ≤ δ ^ (-η))
    (hC_work_eq : C_work = 35 * C)
    (hC_work_ge1 : 1 ≤ C_work)
    (hC_work_le : C_work ≤ δ ^ (-η_work))
    (hK_ring_ge1 : 1 ≤ K_ring)
    (hK_diff_pos : 0 < K_diff)
    (hK_diff_le : K_diff ≤ δ ^ (-qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep))
    (h_budget : εgain > qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep)
    (h_frostman_gap : 2 * η_work < τ * rho_sep)
    (hG_eta_work_le : gapCoefficientV4 L_exp κ0 p_projective τ * η_work ≤ εnc / 2)
    (h_qTotal_le_enc : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc)
    (h_proj_absorb : (126 : ℝ) * Real.sqrt 98 * (35 : ℝ)^2 ≤ δ ^ (-η))
    (c_sel : ℝ)
    (hc_sel_pos : 0 < c_sel)
    (hδ_rho_sel_le_c_sel2 : δ ^ rho_sel ≤ c_sel / 2)
    (hδ_rho_sel_le_c_sel8 : δ ^ rho_sel ≤ c_sel / 8)
    (h_small_neighborhood : 2 * (3 * C * 2 ^ τ) * (δ ^ rho_sep) ^ τ ≤ c_sel / 8)
    (h_dir_64 : δ ^ (εgain - qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep) ≤ 1 / 64)
    (hc_sel_eq : c_sel = cPhase0 δ η (35 * C) / 2)
    (h_pbar_98 : (98 : ℝ) ≤ δ ^ (-(2 * s - 2 * κ0 - 5 * η_work)))
    (h_extract_128 : (128 : ℝ) ≤ δ ^ (-κ0))
    (h_box_bound : (2 ^ 20 : ℝ) ≤ δ ^ (-(η_work / 100)))
    (hrho_sel_eq : rho_sel = rhoSelDefault η_work)
    (hrho_sep_le : rho_sep ≤ η_work / κ0)
    (h_plan_absorb : planConstant s κ0 ≤ δ ^ (-(qPlan η_work - 5 * η_work)))
    (h_Kauf_absorb : kaufmanConstant τ κ0 ≤ δ ^ (-(51 * η_work / 100)))
    (h_KBSG_absorb : (81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80 ≤ δ ^ (-(qAbsorb η_work)))
    (hδ_box_small : δ ^ (-(qBox η_work τ)) ≥ 8 * (1 + (1 + 12 * δ) *
        ((6 * (35 * C) * 2 ^ τ) /
         (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2))) ^ (1 / τ) + 6 * δ))
    (h_small_bsg : η_work ≤ εnc / (2 * bsgOverheadCoefficientV4 L_exp κ0 p_projective))
    (h_qTotalV4_le_enc4 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc / 4)
    (h_qbox_lt_one : qBox η_work τ < 1)
    (h_sumset_absorb : (3 : ℝ) * Real.sqrt 2 ≤
        δ ^ (-(qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep -
                 (L_exp * η + (qMassV4 η_work rho_sep + 3 * rho_sel) / 2))))
    (h_extract_log_absorb : extractLogAbsorbHyp δ εnc η_work τ κ0
        (qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep))
    (h_c_dense_exp_le : 3 * rho_sel + 2 * rho_sep + qAbsorb η_work + L_exp * η_work ≤
        qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep)
    {Y : Set ℝ} {X : ℝ → Set ℝ}
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hY_sub : Y ⊆ productLikeUnitGrid δ)
    (hY_delta : IsProductLikeRealDeltaSCSet δ τ C Y)
    (hXy_delta : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ ∧
      IsProductLikeRealDeltaSCSet δ s C (X y))
    (hP_bdd : Bornology.IsBounded P)
    (h_fiber : ∀ z ∈ productLikeIncidenceSet Y X,
      ∃ (Pz : Set (EuclideanSpace ℝ (Fin 2))),
        Pz ⊆ P ∧ IsDeltaSCSet δ s C Pz ∧
          ∀ p ∈ Pz, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hP_small : ENat.toENNReal (dyadicCoveringNumber δ P) <
      ENNReal.ofReal (δ ^ (-(2 * s + η))))
    {Zf : Finset (EuclideanSpace ℝ (Fin 2))}
    {Pz : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    {P_cubes_fin : Finset (Set (EuclideanSpace ℝ (Fin 2)))}
    (hZf : (Zf : Set _) = productLikeIncidenceSet Y X)
    (hPz : ∀ z ∈ Zf, Pz z ⊆ P ∧ IsDeltaSCSet δ s C (Pz z) ∧
      ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hP_cubes : (P_cubes_fin : Set _) = dyadicCubesMeeting δ P)
    (h_energy : ENNReal.ofReal (C⁻¹ ^ 6 * δ ^ (-(2 * τ + 2 * s - η))) ≤
      ∑ Q ∈ P_cubes_fin,
        ((Zf.filter (fun z => (Pz z ∩ Q).Nonempty)).card : ENNReal) ^ 2)
    (h_ring_spec :
      ∀ (A : Set ℝ) (μ : Measure ℝ),
        A ⊆ Set.Icc 1 2 →
        IsProductLikeRealDeltaSCSet δ κ0 (K_ring * δ ^ (-εnc)) A →
        Nreal δ A ≤ ENNReal.ofReal (K_ring * δ ^ (-(s + εnc))) →
        IsDirectionFrostman δ κ0 (K_ring * δ ^ (-εnc)) μ →
        ∃ x ∈ μ.support,
          ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ A ≤
            Nreal δ (Set.image2 (fun a b => a + x * b) A A)) :
    False :=
  incidence_to_ring_contradiction
    (hδ_pos := hδ_pos) (hδ_dyadic := hδ_dyadic) (hδ_le_one := hδ_le_one)
    (hs_pos := hs_pos) (hs_lt_one := hs_lt_one) (hτ_pos := hτ_pos)
    (hkappa_pos := hkappa_pos) (hkappa_lt_s := hkappa_lt_s)
    (h2kappa_lt_tau := h2kappa_lt_tau)
    (hη_pos := hη_pos) (hη_work_pos := hη_work_pos) (hη_lt_work := hη_lt_work)
    (hε_pos := hε_pos) (h10ε_lt_η_work := h10ε_lt_η_work)
    (h5η_work_lt := h5η_work_lt) (h4η_work_lt_tau := h4η_work_lt_tau)
    (hη_work_eq_two := hη_work_eq_two)
    (hL_exp_pos := hL_exp_pos) (hL_exp_eq_seven := hL_exp_eq_seven)
    (hη_work_le_kappa0 := hη_work_le_kappa0) (hp_ge_10 := hp_ge_10)
    (hC_ge1 := hC_ge1) (hC_le_target := hC_le_target)
    (hC_work_eq := hC_work_eq) (hC_work_ge1 := hC_work_ge1) (hC_work_le := hC_work_le)
    (hK_ring_ge1 := hK_ring_ge1) (hK_diff_pos := hK_diff_pos) (hK_diff_le := hK_diff_le)
    (h_budget := h_budget) (h_frostman_gap := h_frostman_gap)
    (hG_eta_work_le := hG_eta_work_le) (h_qTotal_le_enc := h_qTotal_le_enc)
    (h_proj_absorb := h_proj_absorb)
    (c_sel := c_sel) (hc_sel_pos := hc_sel_pos)
    (hδ_rho_sel_le_c_sel2 := hδ_rho_sel_le_c_sel2)
    (hδ_rho_sel_le_c_sel8 := hδ_rho_sel_le_c_sel8)
    (h_small_neighborhood := h_small_neighborhood) (h_dir_64 := h_dir_64)
    (hc_sel_eq := hc_sel_eq) (h_pbar_98 := h_pbar_98) (h_extract_128 := h_extract_128)
    (h_box_bound := h_box_bound)
    (hrho_sel_eq := hrho_sel_eq) (hrho_sep_le := hrho_sep_le)
    (h_plan_absorb := h_plan_absorb) (h_Kauf_absorb := h_Kauf_absorb)
    (h_KBSG_absorb := h_KBSG_absorb) (hδ_box_small := hδ_box_small)
    (h_small_bsg := h_small_bsg) (h_qTotalV4_le_enc4 := h_qTotalV4_le_enc4)
    (h_qbox_lt_one := h_qbox_lt_one) (h_sumset_absorb := h_sumset_absorb)
    (h_extract_log_absorb := h_extract_log_absorb)
    (h_c_dense_exp_le := h_c_dense_exp_le)
    (hY_sub := hY_sub) (hY_delta := hY_delta) (hXy_delta := hXy_delta)
    (hP_bdd := hP_bdd) (h_fiber := h_fiber) (hP_small := hP_small)
    (hZf := hZf) (hPz := hPz) (hP_cubes := hP_cubes)
    (h_energy := h_energy) (h_ring_spec := h_ring_spec)

/-- Helper: convert energy sum from `Z_Q` set-encard form to `Zf.filter` finset-card form. -/
lemma energy_bridge_conversion_decomposed
    {Z : Set (EuclideanSpace ℝ (Fin 2))}
    {Zf : Finset (EuclideanSpace ℝ (Fin 2))}
    {Pz : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    {P_cubes_fin : Finset (Set (EuclideanSpace ℝ (Fin 2)))}
    {δ τ s η C : ℝ}
    (hZf_eq : (Zf : Set _) = Z)
    (E : ENNReal)
    (hE_def : E = ∑ Q ∈ P_cubes_fin, ENat.toENNReal ({z ∈ Z | (Pz z ∩ Q).Nonempty}).encard ^ 2)
    (h_energy_lower : ENNReal.ofReal (C⁻¹ ^ 6 * δ ^ (-(2 * τ + 2 * s - η))) ≤ E) :
    ENNReal.ofReal (C⁻¹ ^ 6 * δ ^ (-(2 * τ + 2 * s - η))) ≤
      ∑ Q ∈ P_cubes_fin, ((Zf.filter (fun z => (Pz z ∩ Q).Nonempty)).card : ENNReal) ^ 2 := by
  have h_per_Q : ∀ Q ∈ P_cubes_fin,
      ENat.toENNReal ({z ∈ Z | (Pz z ∩ Q).Nonempty}).encard =
      ((Zf.filter (fun z => (Pz z ∩ Q).Nonempty)).card : ENNReal) := by
    intro Q _
    have h1 : {z ∈ Z | (Pz z ∩ Q).Nonempty} = (Zf.filter (fun z => (Pz z ∩ Q).Nonempty) : Set _) := by
      ext z
      have hz : z ∈ (Zf : Set _) ↔ z ∈ Z := by rw [hZf_eq]
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
      <;> exact ⟨fun ⟨h1, h2⟩ => ⟨hz.mpr h1, h2⟩, fun ⟨h1, h2⟩ => ⟨hz.mp h1, h2⟩⟩
    have h2 : ({z ∈ Z | (Pz z ∩ Q).Nonempty}).encard = (↑(Zf.filter (fun z => (Pz z ∩ Q).Nonempty)).card : ENat) := by
      rw [h1]
      exact Set.encard_coe_eq_coe_finsetCard _
    rw [h2] <;> simp
  have hE_eq : E = ∑ Q ∈ P_cubes_fin, ((Zf.filter (fun z => (Pz z ∩ Q).Nonempty)).card : ENNReal) ^ 2 := by
    rw [hE_def]
    apply Finset.sum_congr rfl
    intro Q hQ
    exact congr_arg (fun x : ENNReal => x ^ 2) (h_per_Q Q hQ)
  rw [hE_eq] at h_energy_lower
  exact h_energy_lower

lemma final_contradiction
    {δ s τ κ0 η η_work ε L_exp p_projective C K_work εnc εgain rho_sel rho_sep d_terminal δ₀ : ℝ}
    {Y : Set ℝ} {X : ℝ → Set ℝ}
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    {Z : Set (EuclideanSpace ℝ (Fin 2))}
    {Zf : Finset (EuclideanSpace ℝ (Fin 2))}
    {Pz : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    {P_cubes_fin : Finset (Set (EuclideanSpace ℝ (Fin 2)))}
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales) (hδ_le_one : δ ≤ 1)
    (hs_pos : 0 < s) (hs_lt_one : s < 1) (hτ_pos : 0 < τ)
    (hkappa_pos : 0 < κ0) (hkappa_lt_s : κ0 < s) (h2kappa_lt_tau : 2 * κ0 < τ)
    (hη_pos : 0 < η) (hη_work_pos : 0 < η_work) (hη_work_eq_two : η_work = 2 * η)
    (hε_pos : 0 < ε)
    (h10ε_lt_η_work : 10 * ε < η_work)
    (h5η_work_lt : 5 * η_work < 2 * (s - κ0)) (h4η_work_lt_tau : 4 * η_work < τ)
    (hL_exp_pos : 0 < L_exp) (hL_exp_eq_seven : L_exp = 7)
    (hη_work_le_kappa0 : η_work ≤ κ0)
    (hp_ge_10 : 10 ≤ p_projective)
    (hC_ge1 : 1 ≤ C) (hC_le : C ≤ δ ^ (-η))
    (hK_work_ge1 : 1 ≤ K_work)
    (h_budget : εgain > qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep)
    (h_frostman_gap : 2 * η_work < τ * rho_sep)
    (hG_eta_work_le : gapCoefficientV4 L_exp κ0 p_projective τ * η_work ≤ εnc / 2)
    (h_qTotal_le_enc : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc)
    (hY_sub : Y ⊆ productLikeUnitGrid δ)
    (hY_delta : IsProductLikeRealDeltaSCSet δ τ C Y)
    (hXy_delta : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ ∧ IsProductLikeRealDeltaSCSet δ s C (X y))
    (hP_bdd : Bornology.IsBounded P)
    (h_fiber : ∀ z ∈ productLikeIncidenceSet Y X,
      ∃ (Pz : Set (EuclideanSpace ℝ (Fin 2))),
        Pz ⊆ P ∧ IsDeltaSCSet δ s C Pz ∧ ∀ p ∈ Pz, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (h_contra : ENat.toENNReal (dyadicCoveringNumber δ P) < ENNReal.ofReal (δ ^ (-(2 * s + η))))
    (hZ_finite : Z.Finite) (hZ_eq : Z = productLikeIncidenceSet Y X) (hZf_eq : (Zf : Set _) = Z)
    (hPz_prop : ∀ z ∈ Z, Pz z ⊆ P ∧ IsDeltaSCSet δ s C (Pz z) ∧ ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hP_cubes_finite : (dyadicCubesMeeting δ P).Finite)
    (hP_cubes_eq : (P_cubes_fin : Set _) = dyadicCubesMeeting δ P)
    (h_energy_bridge : ENNReal.ofReal (C⁻¹ ^ 6 * δ ^ (-(2 * τ + 2 * s - η))) ≤
        ∑ Q ∈ P_cubes_fin, ((Zf.filter (fun z => (Pz z ∩ Q).Nonempty)).card : ENNReal) ^ 2)
    (h_ring_spec : ∀ (A : Set ℝ) (μ : Measure ℝ),
      A ⊆ Set.Icc 1 2 →
      IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc)) A →
      Nreal δ A ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) →
      IsDirectionFrostman δ κ0 (K_work * δ ^ (-εnc)) μ →
      ∃ x ∈ μ.support, ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ A ≤ Nreal δ (Set.image2 (fun a b => a + x * b) A A))
    (h35_bound : ∀ (x : ℝ), 0 < x → x ≤ d_terminal → (35 : ℝ) ≤ x ^ (-η))
    (hδ_le₀ : δ ≤ δ₀)
    (hδ₀_le_dterminal : δ₀ ≤ d_terminal)
    (c_sel : ℝ)
    (hc_sel_pos : 0 < c_sel)
    (hδ_rho_sel_le_c_sel2 : δ ^ rho_sel ≤ c_sel / 2)
    (hδ_rho_sel_le_c_sel8 : δ ^ rho_sel ≤ c_sel / 8)
    (h_small_neighborhood : 2 * (3 * C * 2 ^ τ) * (δ ^ rho_sep) ^ τ ≤ c_sel / 8)
    (h_dir_64 : δ ^ (εgain - qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep) ≤ 1 / 64)
    (hc_sel_eq : c_sel = cPhase0 δ η (35 * C) / 2)
    (h_pbar_98 : (98 : ℝ) ≤ δ ^ (-(2 * s - 2 * κ0 - 5 * η_work)))
    (h_extract_128 : (128 : ℝ) ≤ δ ^ (-κ0))
    (h_proj_absorb : (126 : ℝ) * Real.sqrt 98 * (35 : ℝ)^2 ≤ δ ^ (-η))
    (h_box_bound : (2 ^ 20 : ℝ) ≤ δ ^ (-(η_work / 100)))
    -- V4 additional hypotheses
    (hrho_sel_eq : rho_sel = rhoSelDefault η_work)
    (hrho_sep_le : rho_sep ≤ η_work / κ0)
    (h_plan_absorb : planConstant s κ0 ≤ δ ^ (-(qPlan η_work - 5 * η_work)))
    (h_Kauf_absorb : kaufmanConstant τ κ0 ≤ δ ^ (-(51 * η_work / 100)))
    (h_KBSG_absorb : (81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80 ≤ δ ^ (-(qAbsorb η_work)))
    (hδ_box_small : δ ^ (-(qBox η_work τ)) ≥ 8 * (1 + (1 + 12 * δ) *
        ((6 * (35 * C) * 2 ^ τ) /
         (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2))) ^ (1 / τ) + 6 * δ))
    (h_small_bsg : η_work ≤ εnc / (2 * bsgOverheadCoefficientV4 L_exp κ0 p_projective))
    (h_qTotalV4_le_enc4 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc / 4)
    (h_qbox_lt_one : qBox η_work τ < 1)
    (h_sumset_absorb : (3 : ℝ) * Real.sqrt 2 ≤
        δ ^ (-(qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep -
                 (L_exp * η + (qMassV4 η_work rho_sep + 3 * rho_sel) / 2))))
    (h_extract_log_absorb : extractLogAbsorbHyp δ εnc η_work τ κ0
        (qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep))
    (h_c_dense_exp_le : 3 * rho_sel + 2 * rho_sep + qAbsorb η_work + L_exp * η_work ≤
        qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep) :
    False := by
  let C_work : ℝ := 35 * C
  have hC_work_eq : C_work = 35 * C := by rfl
  have hC_work_ge1 : 1 ≤ C_work := by
    dsimp only [C_work]
    have h1 : (1 : ℝ) ≤ 35 := by norm_num
    have hnonneg : (0 : ℝ) ≤ 35 := by norm_num
    have h2 : 35 * (1 : ℝ) ≤ 35 * C := mul_le_mul_of_nonneg_left hC_ge1 hnonneg
    have h3 : 35 * (1 : ℝ) = (35 : ℝ) := by ring
    rw [h3] at h2
    exact le_trans h1 h2
  let K_diff : ℝ := δ ^ (-qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep)
  have hK_diff_pos : 0 < K_diff := Real.rpow_pos_of_pos hδ_pos _
  have hK_diff_le : K_diff ≤ δ ^ (-qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep) := le_refl _
  have hη_lt_work : η < η_work :=
    lt_of_lt_of_eq (lt_two_mul_self hη_pos) hη_work_eq_two.symm
  have hδ_le_dterminal : δ ≤ d_terminal := le_trans hδ_le₀ hδ₀_le_dterminal
  have h35_absorb : (35 : ℝ) ≤ δ ^ (-η) := h35_bound δ hδ_pos hδ_le_dterminal
  have hC_work_le : C_work ≤ δ ^ (-η_work) := by
    dsimp only [C_work]
    have hC_pos : 0 < C := by linarith
    have h_rpow_eta_pos : 0 < δ ^ (-η) := by positivity
    have h_mult : (35 : ℝ) * C ≤ (δ ^ (-η)) * (δ ^ (-η)) :=
      mul_le_mul h35_absorb hC_le hC_pos.le h_rpow_eta_pos.le
    have h_rpow : (δ ^ (-η)) * (δ ^ (-η)) = δ ^ (-(2 * η)) := by
      rw [← Real.rpow_add hδ_pos] <;> ring_nf
    rw [h_rpow] at h_mult
    rw [hη_work_eq_two]
    exact h_mult
  let K_ring : ℝ := K_work
  have hK_ring_ge1 : 1 ≤ K_ring := hK_work_ge1
  have hPz' : ∀ z ∈ Zf, Pz z ⊆ P ∧ IsDeltaSCSet δ s C (Pz z) ∧
      ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ := by
    intro z hz
    have h' : z ∈ (Zf : Set _) := hz
    have h : z ∈ Z := by
      rw [hZf_eq] at h'
      exact h'
    exact hPz_prop z h
  exact key_lemma_contradiction
    (K_ring := K_ring)
    hδ_pos hδ_dyadic hδ_le_one
    hs_pos hs_lt_one hτ_pos
    hkappa_pos hkappa_lt_s h2kappa_lt_tau
    hη_pos hη_work_pos hη_lt_work hη_work_eq_two
    hε_pos h10ε_lt_η_work h5η_work_lt h4η_work_lt_tau
    hL_exp_pos hL_exp_eq_seven hη_work_le_kappa0 hp_ge_10 hC_ge1 hC_le
    hC_work_eq hC_work_ge1 hC_work_le
    hK_ring_ge1 hK_diff_pos hK_diff_le
    h_budget h_frostman_gap hG_eta_work_le h_qTotal_le_enc
    h_proj_absorb
    (c_sel := c_sel) (hc_sel_pos := hc_sel_pos)
    (hδ_rho_sel_le_c_sel2 := hδ_rho_sel_le_c_sel2)
    (hδ_rho_sel_le_c_sel8 := hδ_rho_sel_le_c_sel8)
    (h_small_neighborhood := h_small_neighborhood)
    (h_dir_64 := h_dir_64)
    (hc_sel_eq := hc_sel_eq)
    (h_pbar_98 := h_pbar_98)
    (h_extract_128 := h_extract_128)
    (h_box_bound := h_box_bound)
    hrho_sel_eq hrho_sep_le h_plan_absorb h_Kauf_absorb h_KBSG_absorb
    hδ_box_small h_small_bsg h_qTotalV4_le_enc4 h_qbox_lt_one
    h_sumset_absorb h_extract_log_absorb h_c_dense_exp_le
    hY_sub hY_delta hXy_delta hP_bdd h_fiber
    h_contra
    (Eq.trans hZf_eq hZ_eq)
    hPz'
    hP_cubes_eq
    h_energy_bridge h_ring_spec

/-- V4 version of product_like_incidence_key_lemma.

Uses `exists_budgetV4` directly (no scaling step) and V4 wire budgets.
Replaces the V3 budget selection with V4, adds 5 new δ₀ thresholds,
and calls `final_contradiction`. -/
lemma product_like_incidence_key_lemma
    (s τ κ0 η_nc : ℝ)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hτ_pos : 0 < τ) (hkappa_pos : 0 < κ0)
    (hkappa_lt_s : κ0 < s) (h2kappa_lt_tau : 2 * κ0 < τ)
    (hη_nc_pos : 0 < η_nc)
    (h_weaktwoends : WeakTwoEndsSumProduct s κ0) :
    ∃ η : ℝ, 0 < η ∧ η ≤ η_nc ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
        ∀ {δ : ℝ}, δ ∈ dyadicScales → 0 < δ → δ ≤ δ₀ →
          ∀ (Y : Set ℝ) (X : ℝ → Set ℝ)
            (P : Set (EuclideanSpace ℝ (Fin 2))) (C : ℝ),
            1 ≤ C →
            C ≤ δ ^ (-η) →
            Y ⊆ productLikeUnitGrid δ →
              IsProductLikeRealDeltaSCSet δ τ C Y →
                (∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ ∧
                  IsProductLikeRealDeltaSCSet δ s C (X y)) →
                Bornology.IsBounded P →
                (∀ z ∈ productLikeIncidenceSet Y X,
                  ∃ (Pz : Set (EuclideanSpace ℝ (Fin 2))),
                    Pz ⊆ P ∧
                    IsDeltaSCSet δ s C Pz ∧
                    ∀ p ∈ Pz, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ) →
                ENNReal.ofReal (δ ^ (-(2 * s + η))) ≤
                  ENat.toENNReal (dyadicCoveringNumber δ P) := by
  -- Step 0: Extract expansion parameters from WeakTwoEndsSumProduct
  rcases h_weaktwoends with ⟨εnc, εgain_ring, hεnc_pos, hεnc_bound, hεgain_ring_pos, h_ring⟩

  -- Step 0b: Choose budget parameters via exists_budgetV4.
  let L_exp : ℝ := 7
  let p_projective : ℝ := 10
  have hL_exp_nonneg : 0 ≤ L_exp := by norm_num
  have hL_exp_pos : 0 < L_exp := by norm_num
  have hp_ge_10 : 10 ≤ p_projective := by norm_num
  have hp_pos : 0 < p_projective := by norm_num
  have hp_nonneg : 0 ≤ p_projective := by norm_num

  rcases exists_budgetV4
      (s := s) (τ := τ) (κ0 := κ0) (εnc := εnc) (η_nc := η_nc)
      (L_exp := L_exp) (p_projective := p_projective)
      (hεgain_ring_pos := hεgain_ring_pos)
      hτ_pos hkappa_pos hkappa_lt_s h2kappa_lt_tau hεnc_pos hη_nc_pos
      hL_exp_nonneg hp_ge_10
    with ⟨η_work, ε, rho_sel, rho_sep, εgain,
      hη_work_pos, hε_pos, hεgain_pos, hεgain_le_ring, h10ε_lt_η, h_ε_le_three_halves,
      h5η_work_lt, h4η_work_lt_tau, hη_work_le_kappa0, hη_work_le_2ηnc,
      hrho_sel_eq, hrho_sep_eq, hrho_sel_le, hrho_sep_le, h_frostman,
      h_small_total, h_small_extract, h_small_bsg, h_small_qbox, h_εgain_gt⟩

  let η : ℝ := η_work / 2
  have hη_pos : 0 < η := by positivity
  have hη_work_eq_two : η_work = 2 * η := by dsimp only [η]; ring
  have hη_le_nc : η ≤ η_nc := by
    dsimp only [η]
    linarith [hη_work_le_2ηnc]
  have hL_exp_eq_seven : L_exp = 7 := by rfl

  have hrho_sel_nonneg : 0 ≤ rho_sel := by
    rw [hrho_sel_eq]; dsimp only [rhoSelDefault, qAbsorb]; linarith
  have hrho_sep_nonneg : 0 ≤ rho_sep := by
    rw [hrho_sep_eq]; dsimp only [rhoSepDefault]; positivity

  -- V4 feasibility from budgetV4_feasible
  have hV4 := budgetV4_feasible
    (hεnc_pos := hεnc_pos)
    (hL_nonneg := hL_exp_nonneg)
    (hη_work_pos := hη_work_pos)
    (hε_pos := hε_pos)
    (hκ0_pos := hkappa_pos)
    (hp_nonneg := hp_nonneg)
    (hτ_pos := hτ_pos)
    (h_ε_le_three_halves := h_ε_le_three_halves)
    (hrho_sel_eq := hrho_sel_eq)
    (hrho_sep_eq := hrho_sep_eq)
    (hrho_sel_le := hrho_sel_le)
    (hrho_sep_le := hrho_sep_le)
    (h_small_total := h_small_total)
    (h_small_extract := h_small_extract)
    (h_small_bsg := h_small_bsg)
    (h_small_qbox := h_small_qbox)

  have h_qTotal_le_enc4 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc / 4 :=
    hV4.1
  have h_qBox_lt_one : qBox η_work τ < 1 := hV4.2.2.2

  have hG_eta_work_le : gapCoefficientV4 L_exp κ0 p_projective τ * η_work ≤ εnc / 2 := by
    have h1 : gapCoefficientV4 L_exp κ0 p_projective τ * η_work ≤ εnc / 4 := by
      have hC_pos : 0 < gapCoefficientV4 L_exp κ0 p_projective τ :=
        gapCoefficientV4_pos hL_exp_nonneg hkappa_pos hp_nonneg hτ_pos
      calc
        gapCoefficientV4 L_exp κ0 p_projective τ * η_work
          ≤ gapCoefficientV4 L_exp κ0 p_projective τ * (εnc / (4 * gapCoefficientV4 L_exp κ0 p_projective τ)) :=
            by gcongr
        _ = εnc / 4 := by field_simp [hC_pos.ne'] <;> ring
    linarith

  have h_qTotal_le_enc : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc := by
    calc qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
      ≤ εnc / 4 := h_qTotal_le_enc4
    _ ≤ εnc := by linarith [hεnc_pos]

  have h_c_dense_exp_le :
      3 * rho_sel + 2 * rho_sep + qAbsorb η_work + L_exp * η_work ≤
        qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep :=
    c_dense_exp_le_qKV4 hη_work_pos hε_pos hkappa_pos hp_pos

  refine ⟨η, hη_pos, hη_le_nc, ?_⟩

  -- Step 1: Choose Ring prefactor and extract threshold.
  let K0 : ℝ := 126 * Real.sqrt 98 * 35 ^ 2
  let MG : ℝ := (2 * Real.sqrt 2 + 6) ^ 2
  let inner352 : ℝ := max 35 2
  let inner128 : ℝ := max 128 inner352
  let inner98 : ℝ := max 98 inner128
  let mid : ℝ := max MG inner98
  let C_fixed_all : ℝ := max K0 mid
  have hC_fixed_all_ge1 : 1 ≤ C_fixed_all := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
    have h2 : (2 : ℝ) ≤ inner352 := le_max_right _ _
    have h3 : inner352 ≤ inner128 := le_max_right _ _
    have h4 : inner128 ≤ inner98 := le_max_right _ _
    have h5 : inner98 ≤ mid := le_max_right _ _
    have h6 : mid ≤ C_fixed_all := le_max_right _ _
    exact le_trans h1 (le_trans h2 (le_trans h3 (le_trans h4 (le_trans h5 h6))))
  have hK0_le : K0 ≤ C_fixed_all := le_max_left _ _
  have h98_le : (98 : ℝ) ≤ C_fixed_all := by
    have h1 : (98 : ℝ) ≤ inner98 := le_max_left _ _
    have h2 : inner98 ≤ mid := le_max_right _ _
    have h3 : mid ≤ C_fixed_all := le_max_right _ _
    exact le_trans h1 (le_trans h2 h3)
  have h128_le : (128 : ℝ) ≤ C_fixed_all := by
    have h1 : (128 : ℝ) ≤ inner128 := le_max_left _ _
    have h2 : inner128 ≤ inner98 := le_max_right _ _
    have h3 : inner98 ≤ mid := le_max_right _ _
    have h4 : mid ≤ C_fixed_all := le_max_right _ _
    exact le_trans h1 (le_trans h2 (le_trans h3 h4))
  have h35_le : (35 : ℝ) ≤ C_fixed_all := by
    have h1 : (35 : ℝ) ≤ inner352 := le_max_left _ _
    have h2 : inner352 ≤ inner128 := le_max_right _ _
    have h3 : inner128 ≤ inner98 := le_max_right _ _
    have h4 : inner98 ≤ mid := le_max_right _ _
    have h5 : mid ≤ C_fixed_all := le_max_right _ _
    exact le_trans h1 (le_trans h2 (le_trans h3 (le_trans h4 h5)))

  let K_work : ℝ := max (3 * 2 ^ τ) C_fixed_all
  have hK_work_ge1 : 1 ≤ K_work := by
    have h1 : (1 : ℝ) ≤ 3 * (2 : ℝ) ^ τ := by
      have h2 : (0 : ℝ) < τ := by linarith
      have h3 : (1 : ℝ) < (2 : ℝ) ^ τ := Real.one_lt_rpow (by norm_num) h2
      linarith
    exact le_max_iff.mpr (Or.inl h1)
  rcases h_ring K_work hK_work_ge1 with ⟨δ₀_ring, hδ₀_ring_pos, hδ₀_ring_le_one, h_ring_at_K⟩

  -- Step 1b: δ₀ thresholds.
  -- Existing thresholds (same pattern as V3)
  have hq_pbar_pos : 0 < 2 * s - 2 * κ0 - 5 * η_work := by
    have h : 5 * η_work < 2 * (s - κ0) := h5η_work_lt
    have h2 : 2 * (s - κ0) = 2 * s - 2 * κ0 := by ring
    rw [h2] at h; exact sub_pos.mpr h
  rcases constant_absorption_threshold (C := 98) (by norm_num) hq_pbar_pos with ⟨d_pbar, _, _, h_pbar_bound⟩

  rcases constant_absorption_threshold (C := 128) (by norm_num) hkappa_pos with ⟨d_extract, _, _, h_extract_bound⟩

  let q_absorb : ℝ := qAbsorb η_work
  have hq_absorb_pos : 0 < q_absorb := by dsimp only [q_absorb, qAbsorb]; positivity
  rcases constant_absorption_threshold hC_fixed_all_ge1 hq_absorb_pos with ⟨d_const, _, _, h_const_bound⟩

  rcases constant_absorption_threshold (C := 35) (by norm_num) hη_pos with ⟨d_terminal, hd_term_pos, hd_term_le_one, h35_bound⟩

  let q_pop : ℝ := rho_sel - 3 * η_work / 2
  have hq_pop_pos : 0 < q_pop := by
    have h : q_pop = rho_sel - 3 * η_work / 2 := by rfl
    rw [h, hrho_sel_eq]
    dsimp only [rhoSelDefault, qAbsorb]
    linarith
  rcases constant_absorption_threshold (C := 16 * 7 * 35 ^ 2) (by norm_num) hq_pop_pos
    with ⟨d_pop, _, _, h_pop_bound⟩

  let q_dir : ℝ := εgain - qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
  have hq_dir_pos : 0 < q_dir := by
    dsimp only [q_dir]; linarith [h_εgain_gt]
  rcases constant_absorption_threshold (C := 64) (by norm_num) hq_dir_pos
    with ⟨d_dir, _, _, h_dir_bound⟩

  let q_box_gap : ℝ := η_work / 100
  have hq_box_gap_pos : 0 < q_box_gap := by positivity
  rcases constant_absorption_threshold (C := 2 ^ 20) (by norm_num) hq_box_gap_pos
    with ⟨d_box, _, _, h_box_bound⟩

  let q_frost_gap : ℝ := τ * rho_sep - 2 * η_work
  have hq_frost_gap_pos : 0 < q_frost_gap := by
    dsimp only [q_frost_gap]; linarith [h_frostman]
  have h_frost_C_ge1 : (1 : ℝ) ≤ 6 * 2 ^ τ * 16 * 7 * 35 ^ 2 := by
    have h1 : 0 ≤ τ := by linarith [hτ_pos]
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ τ := Real.one_le_rpow (by norm_num) h1
    calc (1 : ℝ)
      ≤ 6 * (1 : ℝ) * 16 * 7 * 35 ^ 2 := by norm_num
    _ ≤ 6 * ((2 : ℝ) ^ τ) * 16 * 7 * 35 ^ 2 := by gcongr
  rcases constant_absorption_threshold h_frost_C_ge1 hq_frost_gap_pos
    with ⟨d_frost, _, _, h_frost_bound⟩

  rcases constant_absorption_threshold (C := (81 : ℝ) * (2 : ℝ) ^ 39 * (3 : ℝ) ^ 80)
    (by norm_num) hq_absorb_pos
    with ⟨d_KBSG, _, _, h_KBSG_bound⟩

  -- NEW V4 threshold: plan constant
  let q_plan : ℝ := qPlan η_work - 5 * η_work
  have hq_plan_pos : 0 < q_plan := by
    have h : q_plan = qPlan η_work - 5 * η_work := by rfl
    rw [h]
    dsimp only [qPlan, qAbsorb]
    linarith
  have h_plan_const_ge1 : 1 ≤ planConstant s κ0 := by
    dsimp only [planConstant]
    have h11 : 2 * (κ0 - s) < 0 := by linarith
    have h12 : (2 : ℝ) ^ (2 * (κ0 - s)) < 1 := by
      have h : (2 : ℝ) ^ (2 * (κ0 - s)) < (2 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h11
      simpa using h
    have h1 : 0 < 1 - (2 : ℝ) ^ (2 * (κ0 - s)) := by linarith
    have h2 : 0 ≤ 9 * (1 - (2 : ℝ) ^ (2 * (κ0 - s)) + (2 : ℝ) ^ (2 * κ0)) := by positivity
    have h3 : 0 ≤ 9 * (1 - (2 : ℝ) ^ (2 * (κ0 - s)) + (2 : ℝ) ^ (2 * κ0)) / (1 - (2 : ℝ) ^ (2 * (κ0 - s))) := by
      apply div_nonneg <;> linarith
    linarith
  rcases constant_absorption_threshold h_plan_const_ge1 hq_plan_pos
    with ⟨d_plan, _, _, h_plan_bound⟩

  -- NEW V4 threshold: Kaufman constant
  let q_Kauf : ℝ := 51 * η_work / 100
  have hq_Kauf_pos : 0 < q_Kauf := by positivity
  have h_Kauf_const_ge1 : 1 ≤ kaufmanConstant τ κ0 := by
    dsimp only [kaufmanConstant]
    have h1 : 0 < τ - 2 * κ0 := by linarith
    have h2 : 0 ≤ (3 * (2 : ℝ)^τ + 1) * τ / (τ - 2 * κ0) := by positivity
    linarith
  rcases constant_absorption_threshold h_Kauf_const_ge1 hq_Kauf_pos
    with ⟨d_Kauf, _, _, h_Kauf_bound⟩

  -- NEW V4 threshold: sumset absorption
  let q_sumset : ℝ := qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep -
      (L_exp * η + (qMassV4 η_work rho_sep + 3 * rho_sel) / 2)
  have hq_sumset_pos : 0 < q_sumset := by
    have h1 : 3 * rho_sel + 2 * rho_sep + qAbsorb η_work + L_exp * η_work ≤
        qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := h_c_dense_exp_le
    have h_qMass : qMassV4 η_work rho_sep = 2 * rho_sep + qAbsorb η_work := by rfl
    have h_absorb_pos : 0 < qAbsorb η_work := by dsimp only [qAbsorb]; positivity
    have h_pos : 0 < (3 : ℝ) / 2 * rho_sel + rho_sep + (1 : ℝ) / 2 * qAbsorb η_work + (1 : ℝ) / 2 * L_exp * η_work := by
      have h1 : 0 < (1 : ℝ) / 2 * qAbsorb η_work := by positivity
      have h2 : 0 ≤ (3 : ℝ) / 2 * rho_sel := by positivity
      have h3 : 0 ≤ rho_sep := hrho_sep_nonneg
      have h4 : 0 ≤ (1 : ℝ) / 2 * L_exp * η_work := by positivity
      linarith
    have h2 : L_exp * η + (qMassV4 η_work rho_sep + 3 * rho_sel) / 2 <
        3 * rho_sel + 2 * rho_sep + qAbsorb η_work + L_exp * η_work := by
      rw [show η = η_work / 2 from rfl, h_qMass]
      have h_eq : (3 * rho_sel + 2 * rho_sep + qAbsorb η_work + L_exp * η_work) -
          (L_exp * (η_work / 2) + ((2 * rho_sep + qAbsorb η_work) + 3 * rho_sel) / 2) =
          (3 : ℝ) / 2 * rho_sel + rho_sep + (1 : ℝ) / 2 * qAbsorb η_work + (1 : ℝ) / 2 * L_exp * η_work := by
        ring
      have h5 : 0 < (3 * rho_sel + 2 * rho_sep + qAbsorb η_work + L_exp * η_work) -
          (L_exp * (η_work / 2) + ((2 * rho_sep + qAbsorb η_work) + 3 * rho_sel) / 2) := by
        rw [h_eq]; exact h_pos
      exact sub_pos.mp h5
    have h3 : L_exp * η + (qMassV4 η_work rho_sep + 3 * rho_sel) / 2 <
        qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep :=
      lt_of_lt_of_le h2 h1
    dsimp only [q_sumset]
    exact sub_pos.mpr h3
  have hC_sqrt_ge1 : 1 ≤ (3 : ℝ) * Real.sqrt 2 := by
    have h : 1 ≤ Real.sqrt 2 := by
      apply Real.le_sqrt_of_sq_le
      norm_num
    linarith
  rcases constant_absorption_threshold hC_sqrt_ge1 hq_sumset_pos
    with ⟨d_sumset, _, _, h_sumset_bound⟩

  -- NEW V4 threshold: extract log absorption
  let q_norm_energy : ℝ := qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep
  let q_box : ℝ := qBox η_work τ
  let α_log : ℝ := (εnc / 2) / (1 + q_box) - q_norm_energy
  have hα_log_pos : 0 < α_log := by
    have h1 : q_norm_energy ≤ qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep :=
      qNormEnergyV3_le_qTotalV4 hL_exp_nonneg hη_work_pos hε_pos hkappa_pos hp_nonneg
        hτ_pos hrho_sel_nonneg hrho_sep_nonneg
    have h2 : q_box < 1 := h_qBox_lt_one
    have hq_box_pos : 0 < q_box := by
      dsimp only [q_box, qBox, qAbsorb]
      positivity
    have h3 : 0 < 1 + q_box := by linarith
    have h4 : (εnc / 2) / (1 + q_box) > εnc / 4 := by
      have h5 : 1 + q_box < 2 := by linarith
      have h6 : (εnc / 2) / (1 + q_box) > (εnc / 2) / 2 := by
        gcongr
        <;> linarith
      have h7 : (εnc / 2) / 2 = εnc / 4 := by ring
      rw [h7] at h6
      exact h6
    have h8 : q_norm_energy ≤ εnc / 4 := le_trans h1 h_qTotal_le_enc4
    linarith
  let C_log : ℝ := extractLogConstant κ0 * (1 + q_box) ^ 2
  have hC_log_pos : 0 < C_log := by
    dsimp only [C_log]
    have h1 : 0 < extractLogConstant κ0 := by
      dsimp only [extractLogConstant]
      have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    have h2 : 0 < (1 + q_box) ^ 2 := by
      have h3 : 0 < 1 + q_box := by
        dsimp only [q_box, qBox, qAbsorb]
        positivity
      positivity
    positivity
  rcases log_pow_const_le_rpow hC_log_pos hα_log_pos
    with ⟨d_extract_log, hd_extract_log_pos, h_extract_log_bound⟩

  -- NEW V4 threshold: box small condition (uniform in C)
  rcases box_bound_threshold_uniform hη_work_pos hτ_pos
    with ⟨d_box_uniform, hd_box_uniform_pos, h_box_uniform_bound⟩

  -- δ₀ = finite minimum of ALL thresholds
  let δ₀ : ℝ := min 1 (min δ₀_ring (min d_pbar (min d_extract (min d_const
    (min d_terminal (min d_pop (min d_dir (min d_box (min d_frost (min d_KBSG
    (min d_plan (min d_Kauf (min d_sumset (min d_extract_log d_box_uniform))))))))))))))
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_le_ring : δ₀ ≤ δ₀_ring := by
    dsimp only [δ₀]
    exact le_trans (min_le_right 1 _) (min_le_left δ₀_ring _)
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro δ hδ_dyadic hδ_pos hδ_le₀ Y X P C hC_ge1 hC_le hY_sub hY_delta hXy_delta hP_bdd h_fiber
  have hδ_le_ring : δ ≤ δ₀_ring := by
    have h1 : δ ≤ δ₀ := hδ_le₀
    have h2 : δ₀ ≤ δ₀_ring := hδ₀_le_ring
    exact le_trans h1 h2
  have hδ_le_one : δ ≤ 1 := by
    have h : δ ≤ δ₀ := hδ_le₀
    exact le_trans h (min_le_left _ _)
  have h_ring_spec_strong : ∀ (A : Set ℝ) (μ : Measure ℝ),
      A ⊆ Set.Icc 1 2 →
      IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc)) A →
      Nreal δ A ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) →
      IsDirectionFrostman δ κ0 (K_work * δ ^ (-εnc)) μ →
      ∃ x ∈ μ.support,
        ENNReal.ofReal (δ ^ (-εgain_ring)) * Nreal δ A ≤
          Nreal δ (Set.image2 (fun a b => a + x * b) A A) :=
    h_ring_at_K (δ := δ) hδ_dyadic hδ_le_ring
  have h_ring_spec : ∀ (A : Set ℝ) (μ : Measure ℝ),
      A ⊆ Set.Icc 1 2 →
      IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc)) A →
      Nreal δ A ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) →
      IsDirectionFrostman δ κ0 (K_work * δ ^ (-εnc)) μ →
      ∃ x ∈ μ.support,
        ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ A ≤
          Nreal δ (Set.image2 (fun a b => a + x * b) A A) := by
    intro A μ hA hA_delta hNreal hFrost
    have h_main := h_ring_spec_strong A μ hA hA_delta hNreal hFrost
    have h1 : ENNReal.ofReal (δ ^ (-εgain)) ≤ ENNReal.ofReal (δ ^ (-εgain_ring)) := by
      have h11 : -εgain_ring ≤ -εgain := by linarith
      have h12 : δ ^ (-εgain) ≤ δ ^ (-εgain_ring) :=
        Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h11
      exact ENNReal.ofReal_le_ofReal h12
    rcases h_main with ⟨x, hx, h_ineq⟩
    refine ⟨x, hx, ?_⟩
    have h2 : ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ A ≤
        ENNReal.ofReal (δ ^ (-εgain_ring)) * Nreal δ A :=
      mul_le_mul_right' h1 (Nreal δ A)
    exact le_trans h2 h_ineq

  -- Contradiction assumption
  by_cases h_contra : ENat.toENNReal (dyadicCoveringNumber δ P) <
      ENNReal.ofReal (δ ^ (-(2 * s + η)))
  · -- Step 2: Incidence counting and energy lower bound
    let Z := productLikeIncidenceSet Y X
    let Pz (z : EuclideanSpace ℝ (Fin 2)) :=
      if hz : z ∈ Z then Classical.choose (h_fiber z hz) else ∅
    have hPz_prop : ∀ z ∈ Z,
        (Pz z) ⊆ P ∧
        IsDeltaSCSet δ s C (Pz z) ∧
        ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ := by
      intro z hz
      have hPz_eq : Pz z = Classical.choose (h_fiber z hz) := by
        unfold Pz; rw [dif_pos hz]
      rw [hPz_eq]
      exact Classical.choose_spec (h_fiber z hz)
    have hX_grid : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ :=
      fun y hy => (hXy_delta y hy).1
    have hX_delta : ∀ y ∈ Y, IsProductLikeRealDeltaSCSet δ s C (X y) :=
      fun y hy => (hXy_delta y hy).2
    have hPz_delta : ∀ z ∈ Z, IsDeltaSCSet δ s C (Pz z) :=
      fun z hz => (hPz_prop z hz).2.1
    have hZ_finite : Z.Finite :=
      incidence_set_finite hδ_pos hY_sub hX_grid
    let Zf := hZ_finite.toFinset
    have hI_lower : ENNReal.ofReal (C⁻¹ ^ 3 * δ ^ (-(τ + 2 * s))) ≤
        ∑ z ∈ Zf, ENat.toENNReal (dyadicCoveringNumber δ (Pz z)) :=
      have hC_pos : 0 < C := by linarith
      incidence_count_lower_bound hδ_pos hC_pos hY_sub hY_delta hX_grid hX_delta hPz_delta
    let I : ENNReal := ∑ z ∈ Zf, ENat.toENNReal (dyadicCoveringNumber δ (Pz z))
    let P_cubes := dyadicCubesMeeting δ P
    have hP_cubes_finite : P_cubes.Finite := by
      have h1 : ENat.toENNReal P_cubes.encard ≠ ⊤ := by
        have h2 : ENat.toENNReal P_cubes.encard < ENNReal.ofReal (δ ^ (-(2 * s + η))) := h_contra
        exact ne_top_of_lt h2
      have h3 : P_cubes.encard ≠ ⊤ := by
        intro h4; rw [h4] at h1; simp at h1
      exact Set.encard_lt_top_iff.mp (lt_top_iff_ne_top.mpr h3)
    let P_cubes_fin := hP_cubes_finite.toFinset
    let Z_Q (Q : Set (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z ∈ Z | ((Pz z) ∩ Q).Nonempty}
    let E : ENNReal := ∑ Q ∈ P_cubes_fin, ENat.toENNReal (Z_Q Q).encard ^ 2
    have h_energy_lower : ENNReal.ofReal (C⁻¹ ^ 6 * δ ^ (-(2 * τ + 2 * s - η))) ≤ E := by
      have hPz_sub_P : ∀ z, Pz z ⊆ P := by
        intro z
        by_cases hz : z ∈ Z
        · exact (hPz_prop z hz).1
        · unfold Pz; rw [dif_neg hz] <;> simp
      have h_sub : ∀ z, dyadicCubesMeeting δ (Pz z) ⊆ P_cubes := by
        intro z Q hQ
        have hQ1 : Q ∈ dyadicCubes 2 δ := hQ.1
        have hQ2 : (Q ∩ Pz z).Nonempty := hQ.2
        have hQ3 : (Q ∩ P).Nonempty := by
          rcases hQ2 with ⟨p, hpQ, hpPz⟩
          have hpP : p ∈ P := hPz_sub_P z hpPz
          exact ⟨p, hpQ, hpP⟩
        exact ⟨hQ1, hQ3⟩
      have hZQ_sub_Z : ∀ Q, Z_Q Q ⊆ Z := by
        intro Q z hz; exact hz.1
      let R (z : EuclideanSpace ℝ (Fin 2)) (Q : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
        (Pz z ∩ Q).Nonempty
      let Cubes_z (z : EuclideanSpace ℝ (Fin 2)) :=
        P_cubes_fin.filter (fun Q => R z Q)
      let Z_Q_fin (Q : Set (EuclideanSpace ℝ (Fin 2))) :=
        Zf.filter (fun z => R z Q)
      have hCubes_eq : ∀ z, Cubes_z z =
          (hP_cubes_finite.subset (h_sub z)).toFinset := by
        intro z; ext Q
        simp only [Cubes_z, Finset.mem_filter, Set.Finite.mem_toFinset]
        constructor
        · rintro ⟨hQ_P, hR⟩
          have hQ1 : Q ∈ dyadicCubes 2 δ := (hP_cubes_finite.mem_toFinset.mp hQ_P).1
          have hR' : (Q ∩ Pz z).Nonempty := by simpa [R, inter_comm] using hR
          exact ⟨hQ1, hR'⟩
        · rintro ⟨hQ1, hR⟩
          have hR' : (Pz z ∩ Q).Nonempty := by simpa [R, inter_comm] using hR
          have hQ_P : Q ∈ P_cubes := h_sub z ⟨hQ1, hR⟩
          exact ⟨hP_cubes_finite.mem_toFinset.mpr hQ_P, hR'⟩
      have hZQ_eq : ∀ Q, Z_Q_fin Q =
          (hZ_finite.subset (hZQ_sub_Z Q)).toFinset := by
        intro Q; ext z
        simp only [Z_Q_fin, Z_Q, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
        have hZf_mem : z ∈ Zf ↔ z ∈ Z := by simp [Zf, hZ_finite.mem_toFinset]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨hZf_mem.mp h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨hZf_mem.mpr h1, h2⟩
      have h_double : ∑ z ∈ Zf, (Cubes_z z).card = ∑ Q ∈ P_cubes_fin, (Z_Q_fin Q).card :=
        double_counting Zf P_cubes_fin R
      let f (Q : Set (EuclideanSpace ℝ (Fin 2))) : ℕ := (Z_Q_fin Q).card
      have h_f1 : ∀ Q ∈ P_cubes_fin, ENat.toENNReal (Z_Q Q).encard = (f Q : ENNReal) := by
        intro Q _
        have h_eq : Z_Q Q = (Z_Q_fin Q : Set _) := by
          ext z; simp only [Z_Q, Z_Q_fin, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq]
          have hZf_mem : z ∈ Zf ↔ z ∈ Z := by simp [Zf, hZ_finite.mem_toFinset]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨hZf_mem.mpr h1, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨hZf_mem.mp h1, h2⟩
        have h_encard : (Z_Q Q).encard = ↑(Z_Q_fin Q).card := by
          rw [h_eq]; exact Set.encard_coe_eq_coe_finsetCard _
        rw [h_encard] <;> simp [f] <;> rfl
      have hI_eq : I = ∑ Q ∈ P_cubes_fin, (f Q : ENNReal) := by
        have h1 : I = ∑ z ∈ Zf, ENat.toENNReal (dyadicCoveringNumber δ (Pz z)) := rfl
        rw [h1]
        have h2 : ∀ z ∈ Zf, ENat.toENNReal (dyadicCoveringNumber δ (Pz z)) =
            ((Cubes_z z).card : ENNReal) := by
          intro z _
          have h_eq3 : dyadicCubesMeeting δ (Pz z) = (Cubes_z z : Set _) := by
            ext Q; simp only [dyadicCubesMeeting, Cubes_z, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq]
            have hQ_in_P : Q ∈ P_cubes_fin ↔ Q ∈ P_cubes := by
              simp [P_cubes_fin, hP_cubes_finite.mem_toFinset]
            constructor
            · rintro ⟨hQ1, hR⟩
              have hR' : (Pz z ∩ Q).Nonempty := by simpa [R, inter_comm] using hR
              have hQ_P : Q ∈ P_cubes := h_sub z ⟨hQ1, hR⟩
              exact ⟨hQ_in_P.mpr hQ_P, hR'⟩
            · rintro ⟨hQ_P, hR⟩
              have hQ1 : Q ∈ dyadicCubes 2 δ := (hP_cubes_finite.mem_toFinset.mp hQ_P).1
              have hR' : (Q ∩ Pz z).Nonempty := by simpa [R, inter_comm] using hR
              exact ⟨hQ1, hR'⟩
          have h_encard : (dyadicCoveringNumber δ (Pz z)) = ↑(Cubes_z z).card := by
            dsimp only [dyadicCoveringNumber]; rw [h_eq3]; exact Set.encard_coe_eq_coe_finsetCard _
          rw [h_encard] <;> simp <;> rfl
        have h3 : ∑ z ∈ Zf, ENat.toENNReal (dyadicCoveringNumber δ (Pz z)) =
            ∑ z ∈ Zf, ((Cubes_z z).card : ENNReal) := by
          apply Finset.sum_congr rfl; intro z hz; exact h2 z hz
        rw [h3]
        have h4 : ∑ z ∈ Zf, ((Cubes_z z).card : ENNReal) =
            ↑(∑ z ∈ Zf, (Cubes_z z).card) := by rw [Nat.cast_sum] <;> rfl
        rw [h4, h_double]
        have h5 : ↑(∑ Q ∈ P_cubes_fin, (Z_Q_fin Q).card) =
            ∑ Q ∈ P_cubes_fin, ((Z_Q_fin Q).card : ENNReal) := by
          rw [Nat.cast_sum] <;> rfl
        rw [h5] <;> rfl
      have hE_eq : E = ∑ Q ∈ P_cubes_fin, ((f Q : ENNReal) ^ 2) := by
        dsimp only [E]; apply Finset.sum_congr rfl; intro Q hQ; rw [h_f1 Q hQ]
      have h_cs : I ^ 2 ≤ (P_cubes_fin.card : ENNReal) * E := by
        rw [hI_eq, hE_eq]; exact cauchy_schwarz_ennreal_of_nat
      have hK_eq : (P_cubes_fin.card : ENNReal) = ENat.toENNReal (dyadicCoveringNumber δ P) := by
        have h1 : (P_cubes_fin : Set _) = P_cubes := hP_cubes_finite.coe_toFinset
        have h2 : P_cubes.encard = ↑P_cubes_fin.card := by
          rw [← h1]; exact Set.encard_coe_eq_coe_finsetCard _
        have h3 : dyadicCoveringNumber δ P = P_cubes.encard := by rfl
        rw [h3, h2] <;> simp
      let L : ENNReal := ENNReal.ofReal (δ ^ (-(2 * s + η)))
      have hL_pos : 0 < L := by dsimp only [L]; apply ENNReal.ofReal_pos.mpr; positivity
      have hL_ne_top : L ≠ ⊤ := ENNReal.ofReal_ne_top
      have hK_lt : (P_cubes_fin.card : ENNReal) < L := by
        rw [hK_eq]; exact h_contra
      have hI2_le : I ^ 2 ≤ L * E := by
        calc I ^ 2 ≤ (P_cubes_fin.card : ENNReal) * E := h_cs
             _ ≤ L * E := by gcongr <;> exact le_of_lt hK_lt
      have h_energy : I ^ 2 * L⁻¹ ≤ E := by
        have h : I ^ 2 * L⁻¹ ≤ L * E * L⁻¹ := by gcongr
        have h2 : L * E * L⁻¹ = E := by
          have h3 : L * L⁻¹ = 1 := by
            rw [ENNReal.mul_inv_cancel (ne_of_gt hL_pos) hL_ne_top]
          calc L * E * L⁻¹ = E * (L * L⁻¹) := by ring
               _ = E := by rw [h3] <;> ring
        rw [h2] at h; exact h
      have hC_pos : 0 < C := by linarith
      have hI2_lower : ENNReal.ofReal (C⁻¹ ^ 6 * δ ^ (-2 * (τ + 2 * s))) ≤ I ^ 2 := by
        have h4 : ENNReal.ofReal (C⁻¹ ^ 3 * δ ^ (-(τ + 2 * s))) ≤ I := hI_lower
        have h5 : (ENNReal.ofReal (C⁻¹ ^ 3 * δ ^ (-(τ + 2 * s)))) ^ 2 ≤ I ^ 2 := by gcongr
        have h6 : (ENNReal.ofReal (C⁻¹ ^ 3 * δ ^ (-(τ + 2 * s)))) ^ 2 =
            ENNReal.ofReal ((C⁻¹ ^ 3 * δ ^ (-(τ + 2 * s))) ^ 2) := by
          rw [ENNReal.ofReal_pow] <;> positivity
        rw [h6] at h5
        have h7 : (C⁻¹ ^ 3 * δ ^ (-(τ + 2 * s))) ^ 2 =
            C⁻¹ ^ 6 * δ ^ (-2 * (τ + 2 * s)) := by
          have h_rpow : (δ ^ (-(τ + 2 * s))) * (δ ^ (-(τ + 2 * s))) = δ ^ (-2 * (τ + 2 * s)) := by
            rw [← Real.rpow_add hδ_pos] <;> ring_nf
          have h : (C⁻¹ ^ 3 * δ ^ (-(τ + 2 * s))) ^ 2 =
              (C⁻¹ ^ 3) ^ 2 * ((δ ^ (-(τ + 2 * s))) * (δ ^ (-(τ + 2 * s)))) := by ring
          rw [h, h_rpow] <;> ring
        rw [h7] at h5; exact h5
      have hL_inv : L⁻¹ = ENNReal.ofReal (δ ^ (2 * s + η)) := by
        dsimp only [L]
        have hx_pos : 0 < δ ^ (-(2 * s + η)) := by positivity
        have h_pos2 : 0 < δ ^ (2 * s + η) := by positivity
        have h_eq1 : δ ^ (-(2 * s + η)) = (δ ^ (2 * s + η))⁻¹ := by
          rw [← Real.rpow_neg hδ_pos.le] <;> ring
        have h_inv : (δ ^ (-(2 * s + η)))⁻¹ = δ ^ (2 * s + η) := by
          rw [h_eq1, inv_inv]
        rw [← ENNReal.ofReal_inv_of_pos hx_pos, h_inv]
      have h_final : ENNReal.ofReal (C⁻¹ ^ 6 * δ ^ (-2 * (τ + 2 * s))) * L⁻¹ ≤ I ^ 2 * L⁻¹ := by
        exact mul_le_mul_right' hI2_lower L⁻¹
      have h_pos1 : 0 ≤ C⁻¹ ^ 6 * δ ^ (-2 * (τ + 2 * s)) := by positivity
      have h_add : -2 * (τ + 2 * s) + (2 * s + η) = -(2 * τ + 2 * s - η) := by ring
      have h_rpow_mul : ∀ (y z : ℝ), δ ^ y * δ ^ z = δ ^ (y + z) := by
        intro y z; exact (Real.rpow_add hδ_pos y z).symm
      have h_real_eq : C⁻¹ ^ 6 * δ ^ (-2 * (τ + 2 * s)) * δ ^ (2 * s + η) =
          C⁻¹ ^ 6 * δ ^ (-(2 * τ + 2 * s - η)) := by
        have h_assoc : C⁻¹ ^ 6 * δ ^ (-2 * (τ + 2 * s)) * δ ^ (2 * s + η) =
            C⁻¹ ^ 6 * (δ ^ (-2 * (τ + 2 * s)) * δ ^ (2 * s + η)) := by exact mul_assoc _ _ _
        rw [h_assoc]
        rw [h_rpow_mul (-2 * (τ + 2 * s)) (2 * s + η), h_add]
      have h_key : ENNReal.ofReal (C⁻¹ ^ 6 * δ ^ (-2 * (τ + 2 * s))) * L⁻¹ =
          ENNReal.ofReal (C⁻¹ ^ 6 * δ ^ (-(2 * τ + 2 * s - η))) := by
        rw [hL_inv, ← ENNReal.ofReal_mul h_pos1, h_real_eq]
      have h_final2 : ENNReal.ofReal (C⁻¹ ^ 6 * δ ^ (-(2 * τ + 2 * s - η))) ≤ I ^ 2 * L⁻¹ := by
        rw [← h_key]; exact h_final
      exact le_trans h_final2 h_energy
    have hZf_eq : (Zf : Set _) = Z := hZ_finite.coe_toFinset
    have hE_def : E = ∑ Q ∈ P_cubes_fin, ENat.toENNReal (Z_Q Q).encard ^ 2 := by rfl
    have h_energy_bridge := energy_bridge_conversion_decomposed
      (hZf_eq := hZf_eq) (E := E) (hE_def := hE_def) (h_energy_lower := h_energy_lower)

    -- Threshold accessors and derivations
    have hδ₀_le_dterminal : δ₀ ≤ d_terminal := by
      dsimp only [δ₀]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _)
              (le_trans (min_le_right _ _)
                (min_le_left _ _)))))
    have hδ_le_pop : δ ≤ d_pop := by
      have h : δ ≤ δ₀ := hδ_le₀
      have h2 : δ₀ ≤ d_pop := by
        dsimp only [δ₀]
        exact le_trans (min_le_right 1 _)
          (le_trans (min_le_right δ₀_ring _)
            (le_trans (min_le_right d_pbar _)
              (le_trans (min_le_right d_extract _)
                (le_trans (min_le_right d_const _)
                  (le_trans (min_le_right d_terminal _)
                    (min_le_left d_pop _))))))
      exact le_trans h h2
    have hδ_le_frost : δ ≤ d_frost := by
      have h : δ ≤ δ₀ := hδ_le₀
      have h2 : δ₀ ≤ d_frost := by
        dsimp only [δ₀]
        exact le_trans (min_le_right 1 _)
          (le_trans (min_le_right δ₀_ring _)
            (le_trans (min_le_right d_pbar _)
              (le_trans (min_le_right d_extract _)
                (le_trans (min_le_right d_const _)
                  (le_trans (min_le_right d_terminal _)
                    (le_trans (min_le_right d_pop _)
                      (le_trans (min_le_right d_dir _)
                        (le_trans (min_le_right d_box _)
                          (min_le_left d_frost _)))))))))
      exact le_trans h h2
    have hδ_le_KBSG : δ ≤ d_KBSG := by
      have h : δ ≤ δ₀ := hδ_le₀
      have h2 : δ₀ ≤ d_KBSG := by
        dsimp only [δ₀]
        exact le_trans (min_le_right 1 _)
          (le_trans (min_le_right δ₀_ring _)
            (le_trans (min_le_right d_pbar _)
              (le_trans (min_le_right d_extract _)
                (le_trans (min_le_right d_const _)
                  (le_trans (min_le_right d_terminal _)
                    (le_trans (min_le_right d_pop _)
                      (le_trans (min_le_right d_dir _)
                        (le_trans (min_le_right d_box _)
                          (le_trans (min_le_right d_frost _)
                            (min_le_left d_KBSG _))))))))))
      exact le_trans h h2
    have hδ_le_pbar : δ ≤ d_pbar := by
      have h : δ ≤ δ₀ := hδ_le₀
      have h2 : δ₀ ≤ d_pbar := by
        dsimp only [δ₀]
        exact le_trans (min_le_right 1 _)
          (le_trans (min_le_right δ₀_ring _) (min_le_left d_pbar _))
      exact le_trans h h2
    have hδ_le_extract : δ ≤ d_extract := by
      have h : δ ≤ δ₀ := hδ_le₀
      have h2 : δ₀ ≤ d_extract := by
        dsimp only [δ₀]
        exact le_trans (min_le_right 1 _)
          (le_trans (min_le_right δ₀_ring _)
            (le_trans (min_le_right d_pbar _) (min_le_left d_extract _)))
      exact le_trans h h2
    have hδ_le_const : δ ≤ d_const := by
      have h : δ ≤ δ₀ := hδ_le₀
      have h2 : δ₀ ≤ d_const := by
        dsimp only [δ₀]
        exact le_trans (min_le_right 1 _)
          (le_trans (min_le_right δ₀_ring _)
            (le_trans (min_le_right d_pbar _)
              (le_trans (min_le_right d_extract _) (min_le_left d_const _))))
      exact le_trans h h2
    have hδ_le_box : δ ≤ d_box := by
      have h : δ ≤ δ₀ := hδ_le₀
      have h2 : δ₀ ≤ d_box := by
        dsimp only [δ₀]
        exact le_trans (min_le_right 1 _)
          (le_trans (min_le_right δ₀_ring _)
            (le_trans (min_le_right d_pbar _)
              (le_trans (min_le_right d_extract _)
                (le_trans (min_le_right d_const _)
                  (le_trans (min_le_right d_terminal _)
                    (le_trans (min_le_right d_pop _)
                      (le_trans (min_le_right d_dir _)
                        (min_le_left d_box _))))))))
      exact le_trans h h2
    have hδ_le_dir : δ ≤ d_dir := by
      have h : δ ≤ δ₀ := hδ_le₀
      have h2 : δ₀ ≤ d_dir := by
        dsimp only [δ₀]
        exact le_trans (min_le_right 1 _)
          (le_trans (min_le_right δ₀_ring _)
            (le_trans (min_le_right d_pbar _)
              (le_trans (min_le_right d_extract _)
                (le_trans (min_le_right d_const _)
                  (le_trans (min_le_right d_terminal _)
                    (le_trans (min_le_right d_pop _)
                      (min_le_left d_dir _)))))))
      exact le_trans h h2
    have hδ_le_plan : δ ≤ d_plan := by
      have h : δ ≤ δ₀ := hδ_le₀
      have h2 : δ₀ ≤ d_plan := by
        dsimp only [δ₀]
        exact le_trans (min_le_right 1 _)
          (le_trans (min_le_right δ₀_ring _)
            (le_trans (min_le_right d_pbar _)
              (le_trans (min_le_right d_extract _)
                (le_trans (min_le_right d_const _)
                  (le_trans (min_le_right d_terminal _)
                    (le_trans (min_le_right d_pop _)
                      (le_trans (min_le_right d_dir _)
                        (le_trans (min_le_right d_box _)
                          (le_trans (min_le_right d_frost _)
                            (le_trans (min_le_right d_KBSG _)
                              (min_le_left d_plan _)))))))))))
      exact le_trans h h2
    have hδ_le_Kauf : δ ≤ d_Kauf := by
      have h : δ ≤ δ₀ := hδ_le₀
      have h2 : δ₀ ≤ d_Kauf := by
        dsimp only [δ₀]
        exact le_trans (min_le_right 1 _)
          (le_trans (min_le_right δ₀_ring _)
            (le_trans (min_le_right d_pbar _)
              (le_trans (min_le_right d_extract _)
                (le_trans (min_le_right d_const _)
                  (le_trans (min_le_right d_terminal _)
                    (le_trans (min_le_right d_pop _)
                      (le_trans (min_le_right d_dir _)
                        (le_trans (min_le_right d_box _)
                          (le_trans (min_le_right d_frost _)
                            (le_trans (min_le_right d_KBSG _)
                              (le_trans (min_le_right d_plan _)
                                (min_le_left d_Kauf _))))))))))))
      exact le_trans h h2
    have hδ_le_sumset : δ ≤ d_sumset := by
      have h : δ ≤ δ₀ := hδ_le₀
      have h2 : δ₀ ≤ d_sumset := by
        dsimp only [δ₀]
        exact le_trans (min_le_right 1 _)
          (le_trans (min_le_right δ₀_ring _)
            (le_trans (min_le_right d_pbar _)
              (le_trans (min_le_right d_extract _)
                (le_trans (min_le_right d_const _)
                  (le_trans (min_le_right d_terminal _)
                    (le_trans (min_le_right d_pop _)
                      (le_trans (min_le_right d_dir _)
                        (le_trans (min_le_right d_box _)
                          (le_trans (min_le_right d_frost _)
                            (le_trans (min_le_right d_KBSG _)
                              (le_trans (min_le_right d_plan _)
                                (le_trans (min_le_right d_Kauf _)
                                  (min_le_left d_sumset _)))))))))))))
      exact le_trans h h2
    have hδ_le_extract_log : δ ≤ d_extract_log := by
      have h : δ ≤ δ₀ := hδ_le₀
      have h2 : δ₀ ≤ d_extract_log := by
        dsimp only [δ₀]
        exact le_trans (min_le_right 1 _)
          (le_trans (min_le_right δ₀_ring _)
            (le_trans (min_le_right d_pbar _)
              (le_trans (min_le_right d_extract _)
                (le_trans (min_le_right d_const _)
                  (le_trans (min_le_right d_terminal _)
                    (le_trans (min_le_right d_pop _)
                      (le_trans (min_le_right d_dir _)
                        (le_trans (min_le_right d_box _)
                          (le_trans (min_le_right d_frost _)
                            (le_trans (min_le_right d_KBSG _)
                              (le_trans (min_le_right d_plan _)
                                (le_trans (min_le_right d_Kauf _)
                                  (le_trans (min_le_right d_sumset _)
                                    (min_le_left d_extract_log _))))))))))))))
      exact le_trans h h2
    have hδ_le_box_uniform : δ ≤ d_box_uniform := by
      have h : δ ≤ δ₀ := hδ_le₀
      have h2 : δ₀ ≤ d_box_uniform := by
        dsimp only [δ₀]
        exact le_trans (min_le_right 1 _)
          (le_trans (min_le_right δ₀_ring _)
            (le_trans (min_le_right d_pbar _)
              (le_trans (min_le_right d_extract _)
                (le_trans (min_le_right d_const _)
                  (le_trans (min_le_right d_terminal _)
                    (le_trans (min_le_right d_pop _)
                      (le_trans (min_le_right d_dir _)
                        (le_trans (min_le_right d_box _)
                          (le_trans (min_le_right d_frost _)
                            (le_trans (min_le_right d_KBSG _)
                              (le_trans (min_le_right d_plan _)
                                (le_trans (min_le_right d_Kauf _)
                                  (le_trans (min_le_right d_sumset _)
                                    (min_le_right d_extract_log _))))))))))))))
      exact le_trans h h2

    -- Derive threshold facts
    have h_pbar_98 : (98 : ℝ) ≤ δ ^ (-(2 * s - 2 * κ0 - 5 * η_work)) :=
      h_pbar_bound δ hδ_pos hδ_le_pbar
    have h_extract_128 : (128 : ℝ) ≤ δ ^ (-κ0) :=
      h_extract_bound δ hδ_pos hδ_le_extract
    have h_box_fact : (2 ^ 20 : ℝ) ≤ δ ^ (-(η_work / 100)) :=
      h_box_bound δ hδ_pos hδ_le_box
    have h_pop_fact : 16 * 7 * 35 ^ 2 ≤ δ ^ (-(rho_sel - 3 * η)) := by
      have hq_eq : rho_sel - 3 * η = rho_sel - 3 * η_work / 2 := by
        rw [hη_work_eq_two] <;> ring
      rw [hq_eq]
      exact h_pop_bound δ hδ_pos hδ_le_pop
    have h_frost_fact : 6 * 2 ^ τ * 16 * 7 * 35 ^ 2 ≤ δ ^ (-(τ * rho_sep - 2 * η_work)) :=
      h_frost_bound δ hδ_pos hδ_le_frost
    have h_absorb_KBSG_fact : (81 : ℝ) * (2 : ℝ) ^ 39 * (3 : ℝ) ^ 80 ≤ δ ^ (-(qAbsorb η_work)) :=
      h_KBSG_bound δ hδ_pos hδ_le_KBSG
    have h_plan_absorb : planConstant s κ0 ≤ δ ^ (-(qPlan η_work - 5 * η_work)) :=
      h_plan_bound δ hδ_pos hδ_le_plan
    have h_Kauf_absorb : kaufmanConstant τ κ0 ≤ δ ^ (-(51 * η_work / 100)) :=
      h_Kauf_bound δ hδ_pos hδ_le_Kauf
    have h_sumset_absorb : (3 : ℝ) * Real.sqrt 2 ≤
        δ ^ (-(qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep -
                 (L_exp * η + (qMassV4 η_work rho_sep + 3 * rho_sel) / 2))) :=
      h_sumset_bound δ hδ_pos hδ_le_sumset
    have h_extract_log_absorb : extractLogAbsorbHyp δ εnc η_work τ κ0
        (qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep) := by
      dsimp only [extractLogAbsorbHyp]
      exact h_extract_log_bound δ hδ_pos hδ_le_extract_log

    -- Box small condition (using uniform threshold lemma)
    have hC_pos : 0 < C := by linarith
    have hC_bound_uniform : C ≤ δ ^ (-η_work / 2) := by
      have h_eta_eq : η = η_work / 2 := by linarith
      have h2 : δ ^ (-η) = δ ^ (-η_work / 2) := by
        congr 1
        <;> linarith
      rw [← h2]
      exact hC_le
    have hδ_box_small : δ ^ (-(qBox η_work τ)) ≥ 8 * (1 + (1 + 12 * δ) *
        ((6 * (35 * C) * 2 ^ τ) /
         (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2))) ^ (1 / τ) + 6 * δ) :=
      h_box_uniform_bound δ hδ_pos hδ_le_box_uniform C hC_pos hC_bound_uniform

    -- Projection absorption
    have hδ_lt_one : δ < 1 := by
      by_contra h
      have hδ_ge_one : 1 ≤ δ := by linarith
      have h35 : (35 : ℝ) ≤ δ ^ (-η) :=
        h35_bound δ hδ_pos (le_trans hδ_le₀ hδ₀_le_dterminal)
      have h1 : -η ≤ 0 := by linarith [hη_pos]
      have h2 : δ ^ (-η) ≤ δ ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hδ_ge_one h1
      have h3 : δ ^ (0 : ℝ) = 1 := by simp
      rw [h3] at h2; linarith
    have h_proj_absorb : 126 * Real.sqrt 98 * 35 ^ 2 ≤ δ ^ (-η) := by
      have hK0 : 126 * Real.sqrt 98 * 35 ^ 2 ≤ C_fixed_all := by
        dsimp only [C_fixed_all]; exact le_max_left _ _
      have h1 : C_fixed_all ≤ δ ^ (-(η_work / 100)) := h_const_bound δ hδ_pos hδ_le_const
      have h2 : 126 * Real.sqrt 98 * 35 ^ 2 ≤ δ ^ (-(η_work / 100)) := le_trans hK0 h1
      have h3 : η_work / 100 < η := by
        rw [hη_work_eq_two] <;> linarith
      have h4 : δ ^ (-(η_work / 100)) ≤ δ ^ (-η) := by
        have h5 : -(η_work / 100) ≥ -η := by linarith
        exact Real.rpow_le_rpow_of_exponent_ge hδ_pos (by linarith) h5
      exact le_trans h2 h4

    -- c_sel and neighborhood conditions
    have hC_pos : 0 < C := by linarith
    let c_sel : ℝ := cPhase0 δ η (35 * C) / 2
    have hc_sel_eq : c_sel = cPhase0 δ η (35 * C) / 2 := by dsimp only [c_sel] <;> rfl
    have hc_sel_pos : 0 < c_sel := by
      dsimp only [c_sel]
      have h_pos : 0 < cPhase0 δ η (35 * C) := by
        have h_low : cPhase0 δ η (35 * C) ≥ δ ^ (3 * η) / (7 * 35 ^ 2) :=
          cPhase0_lower_bound hδ_pos hδ_lt_one (by linarith) hC_pos hC_le (by ring)
        have h_pos2 : 0 < δ ^ (3 * η) / (7 * 35 ^ 2) := by positivity
        exact lt_of_lt_of_le h_pos2 h_low
      linarith
    have h_lower_cphase : cPhase0 δ η (35 * C) ≥ δ ^ (3 * η) / (7 * 35 ^ 2) :=
      cPhase0_lower_bound hδ_pos hδ_lt_one (by linarith) hC_pos hC_le (by ring)
    have h_gap_pos : 0 < rho_sel - 3 * η := by
      have h_eq : rho_sel - 3 * η = rho_sel - 3 * η_work / 2 := by
        rw [hη_work_eq_two] <;> ring
      rw [h_eq]
      rw [hrho_sel_eq]
      dsimp only [rhoSelDefault, qAbsorb] <;> linarith
    have h_small16 : δ ^ (rho_sel - 3 * η) ≤ 1 / (16 * 7 * 35 ^ 2) := by
      have h_eq : δ ^ (-(rho_sel - 3 * η)) = (δ ^ (rho_sel - 3 * η))⁻¹ := by
        rw [← Real.rpow_neg hδ_pos.le] <;> ring
      rw [h_eq] at h_pop_fact
      have h_pos : 0 < δ ^ (rho_sel - 3 * η) := by positivity
      field_simp [h_pos.ne'] at h_pop_fact ⊢ <;> linarith
    have hδ_rho_sel_le_c_sel2 : δ ^ rho_sel ≤ c_sel / 2 := by
      dsimp only [c_sel]
      have h : δ ^ rho_sel ≤ cPhase0 δ η (35 * C) / 4 :=
        selection_retention_condition hδ_pos (by linarith) (by positivity) h_gap_pos
          (show δ ^ (rho_sel - 3 * η) ≤ 1 / (4 * 7 * 35 ^ 2) from
            le_trans h_small16 (by norm_num)) h_lower_cphase
      have h2 : cPhase0 δ η (35 * C) / 4 = (cPhase0 δ η (35 * C) / 2) / 2 := by ring
      rw [h2] at h; exact h
    have hδ_rho_sel_le_c_sel8 : δ ^ rho_sel ≤ c_sel / 8 := by
      dsimp only [c_sel]
      have h : δ ^ rho_sel ≤ cPhase0 δ η (35 * C) / 16 :=
        kaufman_mass_condition hδ_pos (by linarith) (by positivity) h_gap_pos h_small16 h_lower_cphase
      have h2 : cPhase0 δ η (35 * C) / 16 = (cPhase0 δ η (35 * C) / 2) / 8 := by ring
      rw [h2] at h; exact h
    set gap : ℝ := τ * rho_sep - 2 * η_work with hgap_def
    have hgap_pos : 0 < gap := by linarith [h_frostman]
    have h1_rpow : (δ ^ rho_sep) ^ τ = δ ^ (τ * rho_sep) := by
      have h : (δ ^ rho_sep) ^ τ = δ ^ (rho_sep * τ) := (Real.rpow_mul hδ_pos.le rho_sep τ).symm
      have h2 : rho_sep * τ = τ * rho_sep := by ring
      rw [h, h2]
    have h_eta_eq : η = η_work / 2 := by linarith [hη_work_eq_two]
    have h3 : 2 * (3 * C * 2 ^ τ) * δ ^ (τ * rho_sep) ≤
        (6 * 2 ^ τ) * δ ^ (τ * rho_sep - η) := by
      have hC : C ≤ δ ^ (-η) := hC_le
      have h : (6 * 2 ^ τ) * C * δ ^ (τ * rho_sep) ≤
          (6 * 2 ^ τ) * (δ ^ (-η)) * δ ^ (τ * rho_sep) := by gcongr
      have h21 : δ ^ (-η) * δ ^ (τ * rho_sep) = δ ^ (-η + τ * rho_sep) :=
        (Real.rpow_add hδ_pos (-η) (τ * rho_sep)).symm
      have h22 : -η + τ * rho_sep = τ * rho_sep - η := by ring
      have h23 : (6 * 2 ^ τ) * (δ ^ (-η)) * δ ^ (τ * rho_sep) =
          (6 * 2 ^ τ) * (δ ^ (-η) * δ ^ (τ * rho_sep)) := by
        exact mul_assoc (6 * 2 ^ τ) (δ ^ (-η)) (δ ^ (τ * rho_sep))
      have h2 : (6 * 2 ^ τ) * (δ ^ (-η)) * δ ^ (τ * rho_sep) =
          (6 * 2 ^ τ) * δ ^ (τ * rho_sep - η) := by
        rw [h23, h21, h22]
      have h3' : 2 * (3 * C * 2 ^ τ) * δ ^ (τ * rho_sep) =
          (6 * 2 ^ τ) * C * δ ^ (τ * rho_sep) := by ring
      rw [h3']; exact le_trans h h2.le
    have h4 : τ * rho_sep - η = 3 * η_work / 2 + gap := by
      simp [hgap_def, hη_work_eq_two] <;> ring
    have h5 : (6 * 2 ^ τ) * δ ^ (τ * rho_sep - η) =
        δ ^ (3 * η_work / 2) * ((6 * 2 ^ τ) * δ ^ gap) := by
      have h51 : δ ^ (τ * rho_sep - η) = δ ^ (3 * η_work / 2 + gap) := by rw [h4]
      have h52 : δ ^ (3 * η_work / 2 + gap) = δ ^ (3 * η_work / 2) * δ ^ gap :=
        Real.rpow_add hδ_pos (3 * η_work / 2) gap
      calc
        (6 * 2 ^ τ) * δ ^ (τ * rho_sep - η)
          = (6 * 2 ^ τ) * δ ^ (3 * η_work / 2 + gap) := by rw [h51]
        _ = (6 * 2 ^ τ) * (δ ^ (3 * η_work / 2) * δ ^ gap) := by rw [h52]
        _ = δ ^ (3 * η_work / 2) * ((6 * 2 ^ τ) * δ ^ gap) := by ring
    have h6 : (6 * 2 ^ τ) * δ ^ gap ≤ 1 / (16 * 7 * 35 ^ 2) := by
      have h7 : δ ^ (-gap) = (δ ^ gap)⁻¹ := by
        rw [← Real.rpow_neg hδ_pos.le] <;> ring
      rw [h7] at h_frost_fact
      have h9 : 0 < δ ^ gap := by positivity
      field_simp [h9.ne'] at h_frost_fact ⊢ <;> linarith
    have h10 : c_sel / 8 ≥ δ ^ (3 * η_work / 2) / (16 * 7 * 35 ^ 2) := by
      dsimp only [c_sel]
      have h11 : cPhase0 δ η (35 * C) ≥ δ ^ (3 * η) / (7 * 35 ^ 2) := h_lower_cphase
      have h12 : 3 * η = 3 * η_work / 2 := by rw [hη_work_eq_two] <;> ring
      have h_div : cPhase0 δ η (35 * C) / 2 / 8 = cPhase0 δ η (35 * C) / 16 := by
        have h1 : (2 : ℝ) * 8 = 16 := by norm_num
        have h2 : ∀ (x : ℝ), x / 2 / 8 = x / 16 := by
          intro x; calc x / 2 / 8 = x / ((2 : ℝ) * 8) := by simp [div_eq_mul_inv] <;> ring
                        _ = x / 16 := by rw [h1]
        exact h2 _
      have h13 : cPhase0 δ η (35 * C) / 16 ≥ (δ ^ (3 * η) / (7 * 35 ^ 2)) / 16 := by
        apply div_le_div_of_nonneg_right h11; positivity
      have h14 : (δ ^ (3 * η) / (7 * 35 ^ 2)) / 16 = δ ^ (3 * η) / (16 * 7 * 35 ^ 2) := by ring
      rw [h_div]; rw [h14, h12] at h13; exact h13
    have h_small_neighborhood : 2 * (3 * C * 2 ^ τ) * (δ ^ rho_sep) ^ τ ≤ c_sel / 8 :=
      calc
        2 * (3 * C * 2 ^ τ) * (δ ^ rho_sep) ^ τ
          = 2 * (3 * C * 2 ^ τ) * δ ^ (τ * rho_sep) := by rw [h1_rpow]
        _ ≤ (6 * 2 ^ τ) * δ ^ (τ * rho_sep - η) := h3
        _ = δ ^ (3 * η_work / 2) * ((6 * 2 ^ τ) * δ ^ gap) := h5
        _ ≤ δ ^ (3 * η_work / 2) * (1 / (16 * 7 * 35 ^ 2)) := by gcongr
        _ = δ ^ (3 * η_work / 2) / (16 * 7 * 35 ^ 2) := by ring
        _ ≤ c_sel / 8 := h10
    have h_dir_64 : δ ^ (εgain - qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep) ≤ 1 / 64 := by
      have h_bound : 64 ≤ δ ^ (-(εgain - qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep)) :=
        h_dir_bound δ hδ_pos hδ_le_dir
      have h_pos : 0 < δ ^ (εgain - qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep) := by positivity
      have h9 : δ ^ (-(εgain - qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep)) =
          (δ ^ (εgain - qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep))⁻¹ := by
        rw [← Real.rpow_neg hδ_pos.le] <;> ring
      rw [h9] at h_bound
      field_simp [h_pos.ne'] at h_bound ⊢ <;> linarith

    exfalso
    exact final_contradiction
      (hδ_pos := hδ_pos) (hδ_dyadic := hδ_dyadic) (hδ_le_one := hδ_le_one)
      (hs_pos := hs_pos) (hs_lt_one := hs_lt_one) (hτ_pos := hτ_pos)
      (hkappa_pos := hkappa_pos) (hkappa_lt_s := hkappa_lt_s) (h2kappa_lt_tau := h2kappa_lt_tau)
      (hη_pos := hη_pos) (hη_work_pos := hη_work_pos) (hη_work_eq_two := hη_work_eq_two)
      (hε_pos := hε_pos) (h10ε_lt_η_work := h10ε_lt_η)
      (h5η_work_lt := h5η_work_lt) (h4η_work_lt_tau := h4η_work_lt_tau)
      (hL_exp_pos := hL_exp_pos) (hL_exp_eq_seven := hL_exp_eq_seven)
      (hη_work_le_kappa0 := hη_work_le_kappa0) (hp_ge_10 := hp_ge_10)
      (hC_ge1 := hC_ge1) (hC_le := hC_le)
      (hK_work_ge1 := hK_work_ge1)
      (h_budget := h_εgain_gt) (h_frostman_gap := h_frostman)
      (hG_eta_work_le := hG_eta_work_le) (h_qTotal_le_enc := h_qTotal_le_enc)
      (hY_sub := hY_sub) (hY_delta := hY_delta) (hXy_delta := hXy_delta)
      (hP_bdd := hP_bdd) (h_fiber := h_fiber)
      (h_contra := h_contra)
      (hZ_finite := hZ_finite) (hZ_eq := rfl) (hZf_eq := hZ_finite.coe_toFinset)
      (hPz_prop := hPz_prop)
      (hP_cubes_finite := hP_cubes_finite)
      (hP_cubes_eq := hP_cubes_finite.coe_toFinset)
      (h_energy_bridge := h_energy_bridge)
      (h_ring_spec := h_ring_spec)
      (h35_bound := h35_bound)
      (hδ_le₀ := hδ_le₀)
      (hδ₀_le_dterminal := hδ₀_le_dterminal)
      (c_sel := c_sel)
      (hc_sel_pos := hc_sel_pos)
      (hδ_rho_sel_le_c_sel2 := hδ_rho_sel_le_c_sel2)
      (hδ_rho_sel_le_c_sel8 := hδ_rho_sel_le_c_sel8)
      (h_small_neighborhood := h_small_neighborhood)
      (h_dir_64 := h_dir_64)
      (hc_sel_eq := hc_sel_eq)
      (h_pbar_98 := h_pbar_98)
      (h_extract_128 := h_extract_128)
      (h_proj_absorb := h_proj_absorb)
      (h_box_bound := h_box_fact)
      (hrho_sel_eq := hrho_sel_eq)
      (hrho_sep_le := hrho_sep_le)
      (h_plan_absorb := h_plan_absorb)
      (h_Kauf_absorb := h_Kauf_absorb)
      (h_KBSG_absorb := h_absorb_KBSG_fact)
      (hδ_box_small := hδ_box_small)
      (h_small_bsg := h_small_bsg)
      (h_qTotalV4_le_enc4 := h_qTotal_le_enc4)
      (h_qbox_lt_one := h_qBox_lt_one)
      (h_sumset_absorb := h_sumset_absorb)
      (h_extract_log_absorb := h_extract_log_absorb)
      (h_c_dense_exp_le := h_c_dense_exp_le)

  · -- If not the strict inequality, we already have the desired bound.
    exact le_of_not_gt h_contra

/-- Reduction of `product_like_incidence_sum_product` to the key incidence lemma.

Maps the tube union to its parameter set P, verifies the fiber conditions
using the duality bridge lemmas, proves boundedness of P, applies the key
lemma, and transfers the bound from covering number to tube cardinality. -/
theorem product_like_incidence_sum_product_of_key_lemma
    (s τ κ0 η_nc : ℝ)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hτ_pos : 0 < τ) (hkappa_pos : 0 < κ0)
    (hkappa_lt_s : κ0 < s) (h2kappa_lt_tau : 2 * κ0 < τ)
    (hη_nc_pos : 0 < η_nc)
    (h_weaktwoends : WeakTwoEndsSumProduct s κ0) :
    ∃ η : ℝ, 0 < η ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
        ∀ {δ : ℝ}, δ ∈ dyadicScales → 0 < δ → δ ≤ δ₀ →
          ∀ (Y : Set ℝ) (X : ℝ → Set ℝ)
            (𝒯z : EuclideanSpace ℝ (Fin 2) → Set (Set (EuclideanSpace ℝ (Fin 2)))),
            Y ⊆ productLikeUnitGrid δ →
              IsProductLikeRealDeltaSCSet δ τ (δ ^ (-η)) Y →
                (∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ ∧
                  IsProductLikeRealDeltaSCSet δ s (δ ^ (-η)) (X y)) →
              (∀ z ∈ productLikeIncidenceSet Y X,
                IsProductLikeAppendixDeltaSCSetOfDyadicTubes δ s (δ ^ (-η)) (𝒯z z) ∧
                  ∀ T ∈ 𝒯z z, z ∈ T) →
                let 𝒯 : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
                  ⋃ z ∈ productLikeIncidenceSet Y X, 𝒯z z
                ENNReal.ofReal (δ ^ (-(2 * s + η))) ≤ ENat.toENNReal 𝒯.encard := by
  rcases product_like_incidence_key_lemma s τ κ0 η_nc hs_pos hs_lt_one hτ_pos
    hkappa_pos hkappa_lt_s h2kappa_lt_tau hη_nc_pos h_weaktwoends
    with ⟨η, hη_pos, hη_le_nc, δ₀, hδ₀_pos, h_main⟩
  refine ⟨η, hη_pos, δ₀, hδ₀_pos, ?_⟩
  intro δ hδ_dyadic hδ_pos hδ_le₀ Y X 𝒯z hY_sub hY_delta hXy_delta hTubes
  let 𝒯 : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
    ⋃ z ∈ productLikeIncidenceSet Y X, 𝒯z z
  let P : Set (EuclideanSpace ℝ (Fin 2)) :=
    productLikeAppendixDyadicTubeParameterSet δ 𝒯
  let C : ℝ := δ ^ (-η)
  have hC_pos : 0 < C := by positivity
  have hδ_le_one : δ ≤ 1 := by
    rcases hδ_dyadic with ⟨n, rfl⟩
    have h4 : (2 : ℝ) ^ (-(n : ℤ)) ≤ 1 := by
      have h5 : (n : ℤ) ≥ 0 := by exact_mod_cast Nat.zero_le n
      have h6 : (2 : ℝ) ^ (n : ℤ) ≥ 1 := by
        have h7 : ∀ (k : ℕ), (2 : ℝ) ^ (k : ℤ) ≥ 1 := by
          intro k
          induction k with
          | zero => norm_num
          | succ k ih => simp [zpow_add₀, mul_assoc] at * <;> linarith
        exact h7 n
      have h8 : (2 : ℝ) ^ (-(n : ℤ)) = ((2 : ℝ) ^ (n : ℤ))⁻¹ := by
        simp [zpow_neg]
        <;> ring
      rw [h8]
      have h9 : 0 < (2 : ℝ) ^ (n : ℤ) := by positivity
      have h10 : ((2 : ℝ) ^ (n : ℤ))⁻¹ ≤ 1 := by
        have h11 : 1 / ((2 : ℝ) ^ (n : ℤ)) ≤ 1 := (div_le_one h9).mpr h6
        simpa [one_div] using h11
      exact h10
    exact h4
  have hC_one : 1 ≤ C := by
    dsimp only [C]
    have h5 : -η ≤ 0 := by linarith [hη_pos]
    have h6 : δ ^ (0 : ℝ) ≤ δ ^ (-η) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h5
    simpa using h6
  have hC_le : C ≤ δ ^ (-η) := by
    dsimp only [C] <;> rfl
  -- P is bounded
  have hP_bdd : Bornology.IsBounded P :=
    parameter_set_bounded (s := s) hδ_pos hY_sub (fun y hy => (hXy_delta y hy).1) hTubes
  -- For each z, Pz = parameter set of 𝒯z z is a δ-set near the dual line
  have h_fiber : ∀ z ∈ productLikeIncidenceSet Y X,
      ∃ (Pz : Set (EuclideanSpace ℝ (Fin 2))),
        Pz ⊆ P ∧ IsDeltaSCSet δ s C Pz ∧
        ∀ p ∈ Pz, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ := by
    intro z hz
    let Pz := productLikeAppendixDyadicTubeParameterSet δ (𝒯z z)
    have h1 : Pz ⊆ P := by
      intro x hx
      simp only [Pz, P, productLikeAppendixDyadicTubeParameterSet, Set.mem_sUnion] at hx ⊢
      rcases hx with ⟨Q, hQ, hxQ⟩
      rcases hQ with ⟨T, hT, hQeq⟩
      have hT_in_𝒯 : T ∈ 𝒯 := by
        simp only [𝒯, Set.mem_iUnion]
        exact ⟨z, hz, hT⟩
      exact ⟨Q, ⟨T, hT_in_𝒯, hQeq⟩, hxQ⟩
    have h2 : IsDeltaSCSet δ s C Pz := (hTubes z hz).1.2.2.2
    have h3 : ∀ T ∈ 𝒯z z, z ∈ T := (hTubes z hz).2
    have h4 : 𝒯z z ⊆ appendixDyadicTubes δ := (hTubes z hz).1.1
    -- Extract z coordinate bounds
    have hz_simp : z 0 ∈ X (z 1) ∧ z 1 ∈ Y := by
      simpa [productLikeIncidenceSet, Set.mem_iUnion] using hz
    have hzY : z 1 ∈ Y := hz_simp.2
    have hz1 : 0 ≤ z 1 := (hY_sub hzY).2.1
    have hz2 : z 1 ≤ 1 := (hY_sub hzY).2.2
    have h5 : ∀ p ∈ Pz, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ := by
      intro p hp
      simp only [Pz, productLikeAppendixDyadicTubeParameterSet, Set.mem_sUnion] at hp
      rcases hp with ⟨Q, hQ, hpQ⟩
      rcases hQ with ⟨T, hT, rfl⟩
      have hT_tube : T ∈ appendixDyadicTubes δ := h4 hT
      have hzT : z ∈ T := h3 T hT
      exact parameter_set_within_2delta hδ_pos hT_tube hzT hz1 hz2 p hpQ
    exact ⟨Pz, h1, h2, h5⟩
  -- Apply key lemma
  have h_result := h_main hδ_dyadic hδ_pos hδ_le₀ Y X P C
    hC_one hC_le hY_sub hY_delta hXy_delta hP_bdd h_fiber
  -- Covering number equals tube encard
  have h𝒯_sub : 𝒯 ⊆ appendixDyadicTubes δ := by
    intro T hT
    simp only [𝒯, Set.mem_iUnion] at hT
    rcases hT with ⟨z, hz, hT⟩
    exact (hTubes z hz).1.1 hT
  have h_eq : dyadicCoveringNumber δ P = 𝒯.encard :=
    covering_number_eq_encard hδ_pos 𝒯 h𝒯_sub
  rw [h_eq] at h_result
  dsimp only
  exact h_result

end ProductLikeIncidence.ProductReduction
