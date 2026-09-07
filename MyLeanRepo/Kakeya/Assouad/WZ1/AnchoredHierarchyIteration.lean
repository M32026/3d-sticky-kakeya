import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredHierarchyHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.OneScaleToSource

/-!
# Anchored hierarchy iteration

Constructs `WZ1Corollary26AnchoredHierarchyConclusion` from a
generalized one-scale locally-linear producer.

The hard multi-scale iteration is abstracted into `iterate_anchored_hierarchy`.
This module provides the loss schedule, source weakening, and package
assembly wiring.
-/

namespace Kakeya.Assouad

open WZ1VerticalTrapezoid

/-! ## Active set and endpoint proximity -/

/-- The set of heights z at which the horizontal slice of Z is nonempty. -/
def activeSet {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Z : Kakeya.Streamlined.TubeShading F) : Set ℝ :=
  {z | horizontalSlice Z.union z ≠ ∅}

/--
Endpoint proximity guarantee: for each trapezoid, the active set intersects
both endpoint neighborhoods of width `slack = (t.length - min_length) / 2`.

This is the additional hypothesis that enables core shrinking to active endpoints.
-/
def HasEndpointProximity
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Z : Kakeya.Streamlined.TubeShading F)
    (T : Finset WZ1VerticalTrapezoid)
    (min_length : ℝ) : Prop :=
  ∀ t ∈ T,
    let slack := (t.length - min_length) / 2
    (∃ a' ∈ activeSet Z, t.left ≤ a' ∧ a' ≤ t.left + slack) ∧
    (∃ b' ∈ activeSet Z, t.right - slack ≤ b' ∧ b' ≤ t.right)

/-- Weaken endpoint proximity to a smaller min_length (more slack). -/
lemma HasEndpointProximity.weaken
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Z : Kakeya.Streamlined.TubeShading F}
    {T : Finset WZ1VerticalTrapezoid}
    {min1 min2 : ℝ}
    (h : HasEndpointProximity Z T min1)
    (hmin : min2 ≤ min1) :
    HasEndpointProximity Z T min2 := by
  intro t ht
  have h1 := h t ht
  have hlen : min2 ≤ t.length := by
    have h2 : min1 ≤ t.length := by
      let slack := (t.length - min1) / 2
      have h3 := h1.1
      rcases h3 with ⟨a', _, h4, _⟩
      linarith
    linarith
  have h_slack : (t.length - min2) / 2 ≥ (t.length - min1) / 2 := by linarith
  rcases h1 with ⟨⟨a', haA, ha1, ha2⟩, b', hbA, hb1, hb2⟩
  exact ⟨⟨a', haA, ha1, by linarith⟩, b', hbA, by linarith, hb2⟩

/-- The set of heights z at which the horizontal slice of a set is nonempty. -/
def activeSetOf (E : Set Point3) : Set ℝ :=
  {z | horizontalSlice E z ≠ ∅}

/--
Universal active-extremes guarantee: for any subset E' of the output union
that preserves trapezoid coverage, every trapezoid's core contains extreme
active points spanning at least `min_length`.
-/
def UniversalActiveExtremes
    (Z_out_union : Set Point3)
    (T : Finset WZ1VerticalTrapezoid)
    (min_length : ℝ) : Prop :=
  ∀ (E' : Set Point3),
    E' ⊆ Z_out_union →
    (∀ z ∈ Set.Icc (-1 : ℝ) 1, horizontalSlice E' z ≠ ∅ → ∃ t ∈ T, z ∈ t.core) →
    ∀ t ∈ T,
      ∃ (a b : ℝ), a ∈ activeSetOf E' ∩ t.core ∧
        b ∈ activeSetOf E' ∩ t.core ∧
        (∀ z ∈ activeSetOf E' ∩ t.core, a ≤ z ∧ z ≤ b) ∧
        b - a ≥ min_length

/-- Weaken universal active-extremes to a smaller min_length. -/
lemma UniversalActiveExtremes.weaken
    {Z_out_union : Set Point3}
    {T : Finset WZ1VerticalTrapezoid}
    {min1 min2 : ℝ}
    (h : UniversalActiveExtremes Z_out_union T min1)
    (hmin : min2 ≤ min1) :
    UniversalActiveExtremes Z_out_union T min2 := by
  intro E' hsub hcov t ht
  rcases h E' hsub hcov t ht with ⟨a, b, ha, hb, hbound, hlen⟩
  exact ⟨a, b, ha, hb, hbound, by linarith⟩

/-! ## Generalized one-scale producer -/

/--
A one-scale producer working for any source with inputLoss ≤ outputLoss / 100.

Additionally guarantees endpoint proximity of the active set to each
trapezoid, enabling core shrinking to active endpoints.
-/
def GeneralizedOneScaleProducer : Prop :=
  ∀ sigma outputLoss : ℝ, 0 < sigma → sigma < 1 → 0 < outputLoss →
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ inputLoss : ℝ, 0 < inputLoss → inputLoss ≤ outputLoss / 100 →
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ source : WZ1PlaninessGraininessPackage sigma inputLoss delta,
            ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
              ∃ (data : WZ1LocallyLinearOneScaleData source outputLoss rho),
                HasEndpointProximity data.shading data.trapezoids
                  (Real.rpow rho.1 (1 / 2 + outputLoss)) ∧
                UniversalActiveExtremes data.shading.union data.trapezoids
                  (Real.rpow rho.1 (1 / 2 + outputLoss))

/-! ## Loss schedule -/

noncomputable def outputLossFun (hierarchyLoss : ℝ) (N : ℕ) (j : ℕ) : ℝ :=
  hierarchyLoss / (100 : ℝ) ^ (N - 1 - j)

noncomputable def inputLossFun (hierarchyLoss : ℝ) (N : ℕ) (j : ℕ) : ℝ :=
  match j with
  | 0 => hierarchyLoss / (100 : ℝ) ^ N
  | j + 1 => outputLossFun hierarchyLoss N j

lemma inputLoss_next_eq_outputLoss_prev
    (hierarchyLoss : ℝ) (N : ℕ) (j : ℕ) :
    inputLossFun hierarchyLoss N (j + 1) = outputLossFun hierarchyLoss N j := by
  simp [inputLossFun]

lemma inputLoss_pos
    (hierarchyLoss : ℝ) (hhierarchyLoss : 0 < hierarchyLoss)
    (N : ℕ) (j : ℕ) : 0 < inputLossFun hierarchyLoss N j := by
  cases j <;> simp [inputLossFun, outputLossFun] <;> positivity

lemma outputLoss_pos
    (hierarchyLoss : ℝ) (hhierarchyLoss : 0 < hierarchyLoss)
    (N : ℕ) (j : ℕ) (hj : j < N) : 0 < outputLossFun hierarchyLoss N j := by
  have h : 0 < (100 : ℝ) ^ (N - 1 - j) := by positivity
  have h' : 0 < hierarchyLoss := hhierarchyLoss
  exact div_pos h' h

lemma sourceLossCeiling_le_hierarchyLoss_div_100
    (hierarchyLoss : ℝ) (N : ℕ) (hN_two : 2 ≤ N)
    (hhierarchyLoss : 0 < hierarchyLoss) :
    inputLossFun hierarchyLoss N 0 ≤ hierarchyLoss / 100 := by
  have h1 : inputLossFun hierarchyLoss N 0 = hierarchyLoss / (100 : ℝ) ^ N := by
    simp [inputLossFun]
  rw [h1]
  have h3 : N ≥ 2 := hN_two
  have h2 : (100 : ℝ) ^ N ≥ 100 := by
    have h4 : N ≥ 2 := h3
    have h5 : ∀ n : ℕ, n ≥ 2 → (100 : ℝ) ^ n ≥ 100 := by
      intro n hn
      induction' hn with n hn ih
      · norm_num
      · simp [pow_succ] at * <;> linarith
    exact h5 N h4
  exact div_le_div_of_nonneg_left (by linarith) (by positivity) h2

/-! ## Source loss weakening -/

/-- Weaken a source package from epsilon₁ to epsilon₂ (epsilon₁ ≤ epsilon₂). -/
def weakenSourcePackage
    {sigma epsilon₁ epsilon₂ delta : ℝ}
    (source : WZ1PlaninessGraininessPackage sigma epsilon₁ delta)
    (hepsilon : epsilon₁ ≤ epsilon₂)
    (hdelta_pos : 0 < delta)
    (hdelta_one : delta ≤ 1) :
    WZ1PlaninessGraininessPackage sigma epsilon₂ delta :=
  let h_rpow_mono : Kakeya.realRpowENN delta (-epsilon₁) ≤ Kakeya.realRpowENN delta (-epsilon₂) := by
    simp only [Kakeya.realRpowENN]
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one (by linarith)
  { family := source.family
    uniform := source.uniform
    shading := source.shading
    vertical_chart := source.vertical_chart
    constant := source.constant
    extremal := source.extremal.mono_epsilon hepsilon
    constant_one := source.constant_one
    constant_ne_top := source.constant_ne_top
    constant_bound := source.constant_bound.trans h_rpow_mono
    global_grains := source.global_grains
    local_grains := source.local_grains
    slope_lipschitz_bound := source.slope_lipschitz_bound.trans h_rpow_mono
    slope_one_lipschitz := source.slope_one_lipschitz
    slope_bound := source.slope_bound
    planeMap_vertical_bound := source.planeMap_vertical_bound
    planeMap_lipschitz_bound := source.planeMap_lipschitz_bound.trans h_rpow_mono
    planeMap_one_lipschitz := source.planeMap_one_lipschitz }

/-! ## Hierarchy scale utilities -/

/-- The scale at hierarchy level j: `rho_j = delta^((j+1)/N)`. -/
noncomputable def hierarchyScale (delta : ℝ) (N : ℕ) (j : ℕ) : ℝ :=
  Real.rpow delta (((j : ℝ) + 1) / (N : ℝ))

/-- `hierarchyScale delta N (j : ℕ) = wz1Corollary26Scale delta N j`. -/
lemma hierarchyScale_eq_wz1Scale {delta : ℝ} {N : ℕ} (j : Fin N) :
    hierarchyScale delta N (j : ℕ) = wz1Corollary26Scale delta N j := by
  simp [hierarchyScale, wz1Corollary26Scale]

/-- Construct an admissible scale at hierarchy level j. -/
noncomputable def hierarchyAdmissibleScale
    {delta : ℝ} {N : ℕ} (hN_pos : 0 < N)
    (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (j : ℕ) (hj : j < N) :
    Kakeya.Streamlined.AdmissibleScale delta := by
  have hN_pos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have h1 : ((j : ℝ) + 1) / (N : ℝ) ≤ 1 := by
    have h2 : (j : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast (by omega)
    exact (div_le_one hN_pos').mpr h2
  have h0 : 0 ≤ ((j : ℝ) + 1) / (N : ℝ) := by positivity
  refine ⟨hierarchyScale delta N j, ?_, ?_⟩
  · have h4 : Real.rpow delta 1 ≤ hierarchyScale delta N j := by
      simpa [hierarchyScale] using Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one h1
    simpa using h4
  · have h4 : hierarchyScale delta N j ≤ Real.rpow delta 0 := by
      simpa [hierarchyScale] using Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one h0
    simpa using h4

/-! ## Hierarchy-level producer -/

/-- A one-scale producer specialized to a fixed delta and all hierarchy levels.

Additionally guarantees endpoint proximity at the final hierarchy loss. -/
def HierarchyLevelProducer (sigma hierarchyLoss delta : ℝ) (N : ℕ) : Prop :=
  ∀ (j : ℕ), j < N →
    ∀ (source : WZ1PlaninessGraininessPackage sigma (inputLossFun hierarchyLoss N j) delta),
      ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
        ∃ (data : WZ1LocallyLinearOneScaleData source (outputLossFun hierarchyLoss N j) rho),
          HasEndpointProximity data.shading data.trapezoids
            (Real.rpow rho.1 (1 / 2 + hierarchyLoss)) ∧
          UniversalActiveExtremes data.shading.union data.trapezoids
            (Real.rpow rho.1 (1 / 2 + hierarchyLoss))

/-- Intersect finitely many tube shadings. -/
def intersectShadings {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ} {N : ℕ}
    (hN_pos : 0 < N)
    (shadings : Fin N → Kakeya.Streamlined.TubeShading F) :
    Kakeya.Streamlined.TubeShading F :=
  let j0 : Fin N := ⟨0, hN_pos⟩
  { carrier := fun i => ⋂ j : Fin N, (shadings j).carrier i
    measurable_carrier := fun i =>
      MeasurableSet.iInter (fun j : Fin N => (shadings j).measurable_carrier i)
    subset_body := fun i =>
      Set.Subset.trans
        (Set.iInter_subset (fun j : Fin N => (shadings j).carrier i) j0)
        ((shadings j0).subset_body i) }

lemma intersectShadings_sub {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ} {N : ℕ}
    {hN_pos : 0 < N} {shadings : Fin N → Kakeya.Streamlined.TubeShading F} (j : Fin N) :
    IsSubshading (intersectShadings hN_pos shadings) (shadings j) := by
  intro i
  exact Set.iInter_subset (fun k : Fin N => (shadings k).carrier i) j

/-! ## Loss schedule relationship -/

lemma inputLoss_le_outputLoss_div_100
    (hierarchyLoss : ℝ) (N : ℕ) (j : ℕ) (hj : j < N) :
    inputLossFun hierarchyLoss N j ≤ outputLossFun hierarchyLoss N j / 100 := by
  have h_eq : inputLossFun hierarchyLoss N j = outputLossFun hierarchyLoss N j / 100 := by
    cases j with
    | zero =>
      have hN_pos : 0 < N := hj
      have h_pow : (100 : ℝ) ^ N = (100 : ℝ) ^ (N - 1) * 100 := by
        cases N with
        | zero => contradiction
        | succ N' => simp [pow_succ] <;> ring
      simp [inputLossFun, outputLossFun]
      <;> rw [h_pow] <;> field_simp <;> ring
    | succ j' =>
      have h1 : inputLossFun hierarchyLoss N (j' + 1) = outputLossFun hierarchyLoss N j' :=
        by simp [inputLossFun]
      have h_j'_lt : j' + 1 < N := hj
      have h_pow2 : (100 : ℝ) ^ (N - 1 - (j' + 1)) * 100 = (100 : ℝ) ^ (N - 1 - j') := by
        have h5 : N - 1 - (j' + 1) + 1 = N - 1 - j' := by omega
        rw [← h5, pow_succ] <;> ring
      have h2 : outputLossFun hierarchyLoss N (j' + 1) / 100 = outputLossFun hierarchyLoss N j' := by
        simp only [outputLossFun]
        calc (hierarchyLoss / (100 : ℝ) ^ (N - 1 - (j' + 1))) / 100
          = hierarchyLoss / ((100 : ℝ) ^ (N - 1 - (j' + 1)) * 100) := by field_simp
        _ = hierarchyLoss / (100 : ℝ) ^ (N - 1 - j') := by rw [h_pow2]
      rw [h1, h2]
  exact h_eq.le

/-! ## Conversion from GeneralizedOneScaleProducer -/

/--
Given a `GeneralizedOneScaleProducer`, find a uniform `delta₀ > 0` such that
for any `delta ≤ delta₀`, we obtain a `HierarchyLevelProducer` working at all
N hierarchy levels simultaneously.

For each level j, the generalized producer gives `delta₀_j`. We take the
minimum over the finite set `{0, ..., N-1}`.
-/
lemma gen_to_hierarchy_producer
    (h_gen : GeneralizedOneScaleProducer)
    {sigma hierarchyLoss : ℝ} (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    {N : ℕ} (hN_pos : 0 < N) :
    ∃ (delta₀ : ℝ), 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
        HierarchyLevelProducer sigma hierarchyLoss delta N := by
  have h_each : ∀ (j : Fin N), ∃ (d : ℝ), 0 < d ∧ d ≤ 1 ∧
      ∀ (inputLoss : ℝ), 0 < inputLoss → inputLoss ≤ outputLossFun hierarchyLoss N j / 100 →
        ∀ (delta : ℝ), 0 < delta → delta ≤ d →
          ∀ (source : WZ1PlaninessGraininessPackage sigma inputLoss delta),
            ∀ (rho : Kakeya.Streamlined.AdmissibleScale delta),
              ∃ (data : WZ1LocallyLinearOneScaleData source (outputLossFun hierarchyLoss N j) rho),
                HasEndpointProximity data.shading data.trapezoids
                  (Real.rpow rho.1 (1 / 2 + outputLossFun hierarchyLoss N j)) ∧
                UniversalActiveExtremes data.shading.union data.trapezoids
                  (Real.rpow rho.1 (1 / 2 + outputLossFun hierarchyLoss N j)) := by
    intro j
    exact h_gen sigma (outputLossFun hierarchyLoss N j) hsigma hsigma1
      (outputLoss_pos hierarchyLoss hhierarchyLoss N j j.isLt)
  choose delta₀_j hdelta₀_j_pos hdelta₀_j_one h_producer_j using h_each
  let S : Finset (Fin N) := Finset.univ
  let delta₀s : Finset ℝ := S.image delta₀_j
  have hS_nonempty : delta₀s.Nonempty := by
    refine ⟨delta₀_j ⟨0, hN_pos⟩, Finset.mem_image.mpr ⟨⟨0, hN_pos⟩, Finset.mem_univ _, rfl⟩⟩
  let delta₀ : ℝ := delta₀s.min' hS_nonempty
  have hdelta₀_in : delta₀ ∈ delta₀s := Finset.min'_mem delta₀s hS_nonempty
  rcases Finset.mem_image.mp hdelta₀_in with ⟨j0, _hj0, h_eq⟩
  have hdelta₀_pos : 0 < delta₀ := by
    have h : delta₀ = delta₀_j j0 := h_eq.symm
    rw [h]; exact hdelta₀_j_pos j0
  have hdelta₀_one : delta₀ ≤ 1 := by
    have h : delta₀ = delta₀_j j0 := h_eq.symm
    rw [h]; exact hdelta₀_j_one j0
  have hdelta₀_le : ∀ (j : Fin N), delta₀ ≤ delta₀_j j := by
    intro j
    exact Finset.min'_le delta₀s (delta₀_j j)
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta hdelta hdelta_small
  intro j hj source rho
  have h_inputLoss_le : inputLossFun hierarchyLoss N j ≤ outputLossFun hierarchyLoss N j / 100 :=
    inputLoss_le_outputLoss_div_100 hierarchyLoss N j hj
  rcases h_producer_j ⟨j, hj⟩ (inputLossFun hierarchyLoss N j)
    (inputLoss_pos hierarchyLoss hhierarchyLoss N j) h_inputLoss_le delta hdelta
    (hdelta_small.trans (hdelta₀_le ⟨j, hj⟩)) source rho with
    ⟨data, h_prox, h_extremes⟩
  -- Weaken proximity and extremes from outputLoss_j to hierarchyLoss
  have h_out_le_hier : outputLossFun hierarchyLoss N j ≤ hierarchyLoss := by
    have h : outputLossFun hierarchyLoss N j = hierarchyLoss / (100 : ℝ) ^ (N - 1 - j) := by
      rfl
    rw [h]
    have h2 : N - 1 - j ≥ 0 := by omega
    have h3 : (100 : ℝ) ^ (N - 1 - j) ≥ 1 := by
      have h4 : ∀ n : ℕ, (100 : ℝ) ^ n ≥ 1 := by
        intro n
        induction n with
        | zero => norm_num
        | succ n ih => simp [pow_succ] at * <;> linarith
      exact h4 (N - 1 - j)
    exact div_le_self (by linarith) h3
  have h_rho_pos : 0 < rho.1 := lt_of_lt_of_le hdelta rho.2.1
  have h_rpow_le : Real.rpow rho.1 (1 / 2 + hierarchyLoss) ≤
      Real.rpow rho.1 (1 / 2 + outputLossFun hierarchyLoss N j) := by
    exact Real.rpow_le_rpow_of_exponent_ge h_rho_pos rho.2.2 (by linarith)
  exact ⟨data, h_prox.weaken h_rpow_le, h_extremes.weaken h_rpow_le⟩

/-! ## Sequential level construction -/

/-- Admissible scale at hierarchy level j. -/
noncomputable def rhoAt
    {delta : ℝ} {N : ℕ}
    (hN_pos : 0 < N) (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (j : ℕ) (hj : j < N) : Kakeya.Streamlined.AdmissibleScale delta :=
  hierarchyAdmissibleScale hN_pos hdelta_pos hdelta_one j hj

/-- Build source, data, proximity, and universal extremes for level j by sequential refinement. -/
noncomputable def buildLevelData
    {sigma hierarchyLoss delta : ℝ} {N : ℕ}
    (hN_pos : 0 < N) (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (h_prod : HierarchyLevelProducer sigma hierarchyLoss delta N)
    (source0 : WZ1PlaninessGraininessPackage sigma (inputLossFun hierarchyLoss N 0) delta)
    (j : ℕ) (hj : j < N) :
    Σ (src : WZ1PlaninessGraininessPackage sigma (inputLossFun hierarchyLoss N j) delta),
      Σ (data : WZ1LocallyLinearOneScaleData src (outputLossFun hierarchyLoss N j)
          (rhoAt hN_pos hdelta_pos hdelta_one j hj)),
        PLift (HasEndpointProximity data.shading data.trapezoids
          (Real.rpow (rhoAt hN_pos hdelta_pos hdelta_one j hj).1 (1 / 2 + hierarchyLoss)) ∧
        UniversalActiveExtremes data.shading.union data.trapezoids
          (Real.rpow (rhoAt hN_pos hdelta_pos hdelta_one j hj).1 (1 / 2 + hierarchyLoss))) :=
  match j with
  | 0 =>
    let h_data := h_prod 0 (by omega) source0 (rhoAt hN_pos hdelta_pos hdelta_one 0 (by omega))
    let data := Classical.choose h_data
    let spec := Classical.choose_spec h_data
    ⟨source0, data, ⟨spec.1, spec.2⟩⟩
  | j'+1 =>
    let prev := buildLevelData hN_pos hdelta_pos hdelta_one hhierarchyLoss h_prod source0 j' (by omega)
    have h_inc : inputLossFun hierarchyLoss N j' ≤ outputLossFun hierarchyLoss N j' := by
      have h1 : inputLossFun hierarchyLoss N j' ≤ outputLossFun hierarchyLoss N j' / 100 :=
        inputLoss_le_outputLoss_div_100 hierarchyLoss N j' (by omega)
      have hpos : 0 < outputLossFun hierarchyLoss N j' :=
        outputLoss_pos hierarchyLoss hhierarchyLoss N j' (by omega)
      linarith
    let sourceNext := prev.2.1.toPlaninessGraininessPackage h_inc hdelta_pos hdelta_one
    let h_data := h_prod (j'+1) hj sourceNext (rhoAt hN_pos hdelta_pos hdelta_one (j'+1) hj)
    let data := Classical.choose h_data
    let spec := Classical.choose_spec h_data
    ⟨sourceNext, data, ⟨spec.1, spec.2⟩⟩

/-- At level k+1, source.shading equals data_k.shading. -/
lemma buildLevelData_source_shading
    {sigma hierarchyLoss delta : ℝ} {N : ℕ}
    (hN_pos : 0 < N) (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (h_prod : HierarchyLevelProducer sigma hierarchyLoss delta N)
    (source0 : WZ1PlaninessGraininessPackage sigma (inputLossFun hierarchyLoss N 0) delta)
    {k : ℕ} (hk1 : k + 1 < N) :
    (buildLevelData hN_pos hdelta_pos hdelta_one hhierarchyLoss h_prod source0 (k + 1) hk1).1.shading =
    (buildLevelData hN_pos hdelta_pos hdelta_one hhierarchyLoss h_prod source0 k (by omega)).2.1.shading := by
  simp [buildLevelData, WZ1LocallyLinearOneScaleData.toPlaninessGraininessPackage] <;> rfl

/-- Subshading chain: data_k.shading.union ⊆ data_j.shading.union for j ≤ k. -/
lemma buildLevelData_chain
    {sigma hierarchyLoss delta : ℝ} {N : ℕ}
    (hN_pos : 0 < N) (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (h_prod : HierarchyLevelProducer sigma hierarchyLoss delta N)
    (source0 : WZ1PlaninessGraininessPackage sigma (inputLossFun hierarchyLoss N 0) delta)
    {j k : ℕ} (hj : j < N) (hk : k < N) (hjk : j ≤ k) :
    (buildLevelData hN_pos hdelta_pos hdelta_one hhierarchyLoss h_prod source0 k hk).2.1.shading.union ⊆
    (buildLevelData hN_pos hdelta_pos hdelta_one hhierarchyLoss h_prod source0 j hj).2.1.shading.union := by
  induction k with
  | zero =>
    have h_j0 : j = 0 := by omega
    subst h_j0
    exact Set.Subset.refl _
  | succ k ih =>
    by_cases h_jk : j = k + 1
    · subst h_jk
      exact Set.Subset.refl _
    · have h_j_le_k : j ≤ k := by omega
      set b_k1 := buildLevelData hN_pos hdelta_pos hdelta_one hhierarchyLoss h_prod source0 (k + 1) (by omega) with hb_k1
      set b_k := buildLevelData hN_pos hdelta_pos hdelta_one hhierarchyLoss h_prod source0 k (by omega) with hb_k
      have h1 : b_k1.2.1.shading.union ⊆ b_k1.1.shading.union :=
        IsSubshading.union_subset b_k1.2.1.subshading
      have h_src_eq : b_k1.1.shading = b_k.2.1.shading :=
        buildLevelData_source_shading hN_pos hdelta_pos hdelta_one hhierarchyLoss h_prod source0 (by omega)
      have h2 : b_k1.1.shading.union = b_k.2.1.shading.union := by
        exact congr_arg (fun (s : Kakeya.Streamlined.TubeShading _) => s.union) h_src_eq
      rw [h2] at h1
      exact Set.Subset.trans h1 (ih (by omega) h_j_le_k)

lemma hierarchyScale_strict_mono
    {delta : ℝ} {N : ℕ} (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1)
    {j k : ℕ} (hjk : j < k) (hk : k < N) :
    hierarchyScale delta N k < hierarchyScale delta N j := by
  have h_exp_lt : ((j : ℝ) + 1) / (N : ℝ) < ((k : ℝ) + 1) / (N : ℝ) := by
    have hN_pos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N from by omega)
    gcongr
    <;> linarith
  have h := Real.rpow_lt_rpow_of_exponent_gt hdelta_pos hdelta_lt_one h_exp_lt
  simpa [hierarchyScale] using h

lemma anchored_active_height_in_Icc
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Z : Kakeya.Streamlined.TubeShading F}
    {z : ℝ} (hZ_ball : Z.union ⊆ Metric.closedBall (0 : Point3) 1)
    (hactive : horizontalSlice Z.union z ≠ ∅) :
    z ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases Set.nonempty_iff_ne_empty.mpr hactive with ⟨p, hp⟩
  have h1 : p ∈ Z.union := hp.1
  have h2 : p ∈ Metric.closedBall (0 : Point3) 1 := hZ_ball h1
  have h3 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using h2
  have h4 : |p (2 : Fin 3)| ≤ ‖p‖ := by
    have h5 : ‖p‖ = Real.sqrt (|p 0| ^ 2 + |p 1| ^ 2 + |p 2| ^ 2) := by
      simp [Point3, EuclideanSpace.norm_eq, Fin.sum_univ_three] <;> ring_nf
    rw [h5]
    have h6 : |p 2| ^ 2 ≤ |p 0| ^ 2 + |p 1| ^ 2 + |p 2| ^ 2 := by
      have h7 : 0 ≤ |p 0| ^ 2 + |p 1| ^ 2 := by positivity
      linarith
    have h7 : 0 ≤ |p 2| := abs_nonneg _
    exact Real.le_sqrt_of_sq_le h6
  have h5 : p (2 : Fin 3) = z := hp.2
  rw [h5] at h4
  exact ⟨by linarith [abs_le.mp h4], by linarith [abs_le.mp h4]⟩

/-! ## Shrinking helper with function exposure -/

/--
Shrink each trapezoid to extreme active points, exposing the shrinking function.

The function exposure is needed for the separated-cores proof: if two shrunk
trapezoids are distinct, their originals must be distinct (since the image of
a single element under a function is a singleton).
-/
lemma shrink_to_extreme_active_points_with_fn
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Z : Kakeya.Streamlined.TubeShading F}
    {T : Finset WZ1VerticalTrapezoid} {min_length : ℝ}
    [DecidableEq WZ1VerticalTrapezoid]
    (hmin_pos : 0 < min_length)
    (h_extremes : ∀ t ∈ T,
      ∃ (a b : ℝ), a ∈ activeSet Z ∩ t.core ∧ b ∈ activeSet Z ∩ t.core ∧
        (∀ z ∈ activeSet Z ∩ t.core, a ≤ z ∧ z ≤ b) ∧
        b - a ≥ min_length) :
    ∃ (f : WZ1VerticalTrapezoid → WZ1VerticalTrapezoid),
      (∀ t ∈ T,
        (f t).left ∈ activeSet Z ∧
        (f t).right ∈ activeSet Z ∧
        min_length ≤ (f t).length ∧
        (f t).core ⊆ t.core ∧
        (f t).slope = t.slope ∧
        (f t).height = t.height ∧
        (f t).intercept = t.intercept ∧
        ∀ z ∈ activeSet Z ∩ t.core, z ∈ (f t).core) ∧
      (∀ z ∈ activeSet Z, (∃ t ∈ T, z ∈ t.core) →
        ∃ t' ∈ T.image f, z ∈ t'.core) := by
  classical
  have h_main : ∀ (t : WZ1VerticalTrapezoid), ∃ (t' : WZ1VerticalTrapezoid),
      t ∈ T → (t'.left ∈ activeSet Z ∧ t'.right ∈ activeSet Z ∧
                 min_length ≤ t'.length ∧ t'.core ⊆ t.core ∧
                 t'.slope = t.slope ∧ t'.height = t.height ∧
                 t'.intercept = t.intercept ∧
                 ∀ z ∈ activeSet Z ∩ t.core, z ∈ t'.core) := by
    intro t
    by_cases ht : t ∈ T
    · rcases h_extremes t ht with ⟨a, b, ha_in, hb_in, h_bound, h_len⟩
      have ha_active : a ∈ activeSet Z := ha_in.1
      have ha_core : a ∈ t.core := ha_in.2
      have hb_active : b ∈ activeSet Z := hb_in.1
      have hb_core : b ∈ t.core := hb_in.2
      have h_ab : a < b := by linarith
      let t' : WZ1VerticalTrapezoid :=
        { left := a, right := b, left_lt_right := h_ab,
          slope := t.slope, intercept := t.intercept,
          height := t.height, height_pos := t.height_pos }
      have h_core_sub : t'.core ⊆ t.core := by
        intro z hz
        have h1 : a ≤ z := (Set.mem_Icc.mp hz).1
        have h2 : z ≤ b := (Set.mem_Icc.mp hz).2
        have h3 : t.left ≤ a := (Set.mem_Icc.mp ha_core).1
        have h4 : b ≤ t.right := (Set.mem_Icc.mp hb_core).2
        exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
      have h_coverage : ∀ z ∈ activeSet Z ∩ t.core, z ∈ t'.core := by
        intro z hz
        have h1 : a ≤ z := (h_bound z hz).1
        have h2 : z ≤ b := (h_bound z hz).2
        exact Set.mem_Icc.mpr ⟨h1, h2⟩
      refine ⟨t', fun _ => ⟨ha_active, hb_active, h_len, h_core_sub, rfl, rfl, rfl, h_coverage⟩⟩
    · exact ⟨t, fun h => False.elim (ht h)⟩
  choose f hf using h_main
  refine ⟨f, ?_⟩
  constructor
  · intro t ht
    exact hf t ht
  · intro z hz_active h
    rcases h with ⟨t, ht, hz_core⟩
    have hz_in_A : z ∈ activeSet Z ∩ t.core := ⟨hz_active, hz_core⟩
    refine ⟨f t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
    exact (hf t ht).2.2.2.2.2.2.2 z hz_in_A

/-! ## Affine endpoint bound helper -/

/-- An affine function on an interval attains its max absolute value at an endpoint. -/
lemma abs_affine_le_max (m c a b z : ℝ) (ha : a ≤ z) (hz : z ≤ b) :
    |m * z + c| ≤ max (|m * a + c|) (|m * b + c|) := by
  by_cases hab : a < b
  · let t : ℝ := (z - a) / (b - a)
    have ht0 : 0 ≤ t := by apply div_nonneg <;> linarith
    have ht1 : t ≤ 1 := by
      dsimp only [t]
      have h : z - a ≤ b - a := by linarith
      have hpos : 0 < b - a := by linarith
      have h' : (z - a) / (b - a) ≤ (b - a) / (b - a) := by gcongr
      have h'' : (b - a) / (b - a) = 1 := by field_simp [hpos.ne']
      rw [h''] at h'
      exact h'
    have hz_eq : z = (1 - t) * a + t * b := by
      have h : (1 - t) * a + t * b = a + t * (b - a) := by ring
      rw [h]
      have h2 : a + t * (b - a) = z := by
        simp only [t]
        field_simp [show b - a ≠ 0 by linarith] <;> ring
      exact h2.symm
    have h_eq : m * z + c = (1 - t) * (m * a + c) + t * (m * b + c) := by
      rw [hz_eq] <;> ring
    rw [h_eq]
    set M := max (|m * a + c|) (|m * b + c|) with hM
    have hM1 : |m * a + c| ≤ M := le_max_left _ _
    have hM2 : |m * b + c| ≤ M := le_max_right _ _
    have h_tri : |(1 - t) * (m * a + c) + t * (m * b + c)| ≤
        |(1 - t) * (m * a + c)| + |t * (m * b + c)| :=
      abs_add_le _ _
    have h_abs1 : |(1 - t) * (m * a + c)| = (1 - t) * |m * a + c| := by
      rw [abs_mul, abs_of_nonneg (by linarith)]
    have h_abs2 : |t * (m * b + c)| = t * |m * b + c| := by
      rw [abs_mul, abs_of_nonneg ht0]
    rw [h_abs1, h_abs2] at h_tri
    have h_final : (1 - t) * |m * a + c| + t * |m * b + c| ≤ M := by
      calc (1 - t) * |m * a + c| + t * |m * b + c|
        ≤ (1 - t) * M + t * M := by gcongr <;> linarith
      _ = M := by ring
    exact h_tri.trans h_final
  · have h_ab : a = b := by linarith
    have h_z : z = a := by linarith
    rw [h_z, h_ab] <;> exact le_max_left _ _

/--
Prove numerical nesting using slope approximations only at the child endpoints.

Since `child.affine z - parent.affine z` is affine in `z`, its absolute value
on `child.core` attains its maximum at an endpoint. The child endpoints are
active, so the conditional slope approximation applies there.
-/
lemma numerical_nesting_from_endpoint_approximations
    {sourceSlope : ℝ → ℝ}
    {child parent : WZ1VerticalTrapezoid}
    {rho_child rho_parent : ℝ}
    (h_child_height : child.height = rho_child)
    (h_parent_height : parent.height = rho_parent)
    (h_core_sub : child.core ⊆ parent.core)
    (h_child_approx_left : |sourceSlope child.left - child.affine child.left| ≤ rho_child)
    (h_child_approx_right : |sourceSlope child.right - child.affine child.right| ≤ rho_child)
    (h_parent_approx_left : |sourceSlope child.left - parent.affine child.left| ≤ rho_parent)
    (h_parent_approx_right : |sourceSlope child.right - parent.affine child.right| ≤ rho_parent) :
    WZ1VerticalTrapezoid.IsNumericallyNestedIn child parent := by
  let d (z : ℝ) := child.affine z - parent.affine z
  have h_d_linear : ∃ (m c : ℝ), ∀ z, d z = m * z + c := by
    refine ⟨child.slope - parent.slope, child.intercept - parent.intercept, fun z => ?_⟩
    simp [d, WZ1VerticalTrapezoid.affine] <;> ring
  rcases h_d_linear with ⟨m, c, h_eq⟩
  have h_left : |d child.left| ≤ rho_child + rho_parent := by
    have h1 : d child.left =
        (sourceSlope child.left - parent.affine child.left) -
        (sourceSlope child.left - child.affine child.left) := by
      simp [d] <;> ring
    rw [h1]
    have h2 : |(sourceSlope child.left - parent.affine child.left) -
              (sourceSlope child.left - child.affine child.left)| ≤
        |sourceSlope child.left - parent.affine child.left| +
        |sourceSlope child.left - child.affine child.left| :=
      abs_sub _ _
    linarith
  have h_right : |d child.right| ≤ rho_child + rho_parent := by
    have h1 : d child.right =
        (sourceSlope child.right - parent.affine child.right) -
        (sourceSlope child.right - child.affine child.right) := by
      simp [d] <;> ring
    rw [h1]
    have h2 : |(sourceSlope child.right - parent.affine child.right) -
              (sourceSlope child.right - child.affine child.right)| ≤
        |sourceSlope child.right - parent.affine child.right| +
        |sourceSlope child.right - child.affine child.right| :=
      abs_sub _ _
    linarith
  refine ⟨h_core_sub, fun z hz => ?_⟩
  have hz1 : child.left ≤ z := (Set.mem_Icc.mp hz).1
  have hz2 : z ≤ child.right := (Set.mem_Icc.mp hz).2
  have h_bound : |d z| ≤ max (|d child.left|) (|d child.right|) := by
    rw [h_eq z, h_eq child.left, h_eq child.right]
    exact abs_affine_le_max m c child.left child.right z hz1 hz2
  have h_final : |d z| ≤ rho_child + rho_parent := by
    calc |d z| ≤ max (|d child.left|) (|d child.right|) := h_bound
         _ ≤ rho_child + rho_parent := by apply max_le <;> linarith
  rw [h_child_height, h_parent_height]
  exact h_final

/-! ## Family transport helpers -/

lemma transport_union {δ : ℝ} {F F' : Kakeya.Streamlined.TubeFamily δ}
    (h : F = F') (Z : Kakeya.Streamlined.TubeShading F) :
    ((h ▸ Z : Kakeya.Streamlined.TubeShading F')).union = Z.union := by
  subst h; rfl

lemma transport_isSubshading {δ : ℝ} {F F' : Kakeya.Streamlined.TubeFamily δ}
    (h : F = F') {Z1 Z2 : Kakeya.Streamlined.TubeShading F}
    (hsub : IsSubshading Z1 Z2) :
    IsSubshading (h ▸ Z1 : Kakeya.Streamlined.TubeShading F')
      (h ▸ Z2 : Kakeya.Streamlined.TubeShading F') := by
  subst h; exact hsub

lemma transport_extremal {δ sigma epsilon : ℝ} {F F' : Kakeya.Streamlined.TubeFamily δ}
    {U : Kakeya.Streamlined.UniformTubeStructure F} {Z : Kakeya.Streamlined.TubeShading F}
    {U' : Kakeya.Streamlined.UniformTubeStructure F'} {Z' : Kakeya.Streamlined.TubeShading F'}
    (hF : F = F') (hU : hF ▸ U = U') (hZ : hF ▸ Z = Z')
    (h : WZ1ExtremalPair sigma epsilon F U Z) :
    WZ1ExtremalPair sigma epsilon F' U' Z' := by
  subst hF; simp [hU, hZ] at * <;> exact h

/-- When all trapezoids have length 1, separated cores, and cores in [-1,1], at most one. -/
lemma at_most_one_trapezoid_delta_one
    {T : Finset WZ1VerticalTrapezoid}
    (h_length_one : ∀ t ∈ T, t.length = 1)
    (h_separated : ∀ t ∈ T, ∀ s ∈ T, t ≠ s →
      ∀ z ∈ t.core, ∀ w ∈ s.core, (1 : ℝ) ≤ |z - w|)
    (h_cores_in_Icc : ∀ t ∈ T, t.core ⊆ Set.Icc (-1 : ℝ) 1) :
    ∀ t ∈ T, ∀ s ∈ T, t = s := by
  intro t ht s hs
  by_contra hne
  have h_strict_left : ∀ (a b : WZ1VerticalTrapezoid), a ∈ T → b ∈ T → a ≠ b →
      a.left ≤ b.left → a.right < b.left := by
    intro a b ha hb hne' h_order
    by_contra h
    have h' : b.left ≤ a.right := by linarith
    have h1 : b.left ∈ a.core := Set.mem_Icc.mpr ⟨h_order, h'⟩
    have h2 : b.left ∈ b.core := Set.left_mem_Icc.mpr b.left_lt_right.le
    have h3 := h_separated a ha b hb hne' b.left h1 b.left h2
    norm_num at h3
  by_cases h_order : t.left ≤ s.left
  · have h_tr : t.right < s.left := h_strict_left t s ht hs hne h_order
    have h_t_right_nonneg : 0 ≤ t.right := by
      have h_len : t.length = 1 := h_length_one t ht
      have h_left_ge : -1 ≤ t.left := by
        have h : t.left ∈ t.core := Set.left_mem_Icc.mpr t.left_lt_right.le
        exact (Set.mem_Icc.mp (h_cores_in_Icc t ht h)).1
      simp [WZ1VerticalTrapezoid.length] at h_len; linarith
    have h_s_left_nonpos : s.left ≤ 0 := by
      have h_len : s.length = 1 := h_length_one s hs
      have h_right_le : s.right ≤ 1 := by
        have h : s.right ∈ s.core := Set.right_mem_Icc.mpr s.left_lt_right.le
        exact (Set.mem_Icc.mp (h_cores_in_Icc s hs h)).2
      simp [WZ1VerticalTrapezoid.length] at h_len; linarith
    linarith
  · have h_order' : s.left ≤ t.left := by linarith
    have h_sr : s.right < t.left := h_strict_left s t hs ht (Ne.symm hne) h_order'
    have h_s_right_nonneg : 0 ≤ s.right := by
      have h_len : s.length = 1 := h_length_one s hs
      have h_left_ge : -1 ≤ s.left := by
        have h : s.left ∈ s.core := Set.left_mem_Icc.mpr s.left_lt_right.le
        exact (Set.mem_Icc.mp (h_cores_in_Icc s hs h)).1
      simp [WZ1VerticalTrapezoid.length] at h_len; linarith
    have h_t_left_nonpos : t.left ≤ 0 := by
      have h_len : t.length = 1 := h_length_one t ht
      have h_right_le : t.right ≤ 1 := by
        have h : t.right ∈ t.core := Set.right_mem_Icc.mpr t.left_lt_right.le
        exact (Set.mem_Icc.mp (h_cores_in_Icc t ht h)).2
      simp [WZ1VerticalTrapezoid.length] at h_len; linarith
    linarith

/-! ## Full construction -/

/--
Construct the full anchored hierarchy from a hierarchy-level producer.

This is the main geometric + dependent-recursion work. Returns the final
shading, extremality, per-level trapezoid data, and unique-parent verification.

# Proof outline

The proof follows these steps:

1. **Dependent recursion**: Build source_j → data_j → source_{j+1} for all
   `j < N` using `HierarchyLevelProducer` and
   `WZ1LocallyLinearOneScaleData.toPlaninessGraininessPackage`. Key:
   `inputLossFun N (j+1)` is definitionally equal to
   `outputLossFun N j`.

2. **Final shading**: Set `Z := data_{N-1}.shading`. Prove `IsSubshading Z source.shading`
   via the chain `data_k.shading.union ⊆ data_j.shading.union` for `j ≤ k`,
   then `data_0.shading ⊆ source.shading`.

3. **Extremality**: `data_{N-1}.extremal` with `outputLossFun N (N-1) = hierarchyLoss`.

4. **Transfer coverage/approximation**: Since `Z.union ⊆ data_j.shading.union`,
   any active height in Z is active in data_j, so `data_j.active_height_coverage`
   and `data_j.slope_approximation` transfer to Z.

5. **Shrink to active endpoints**: The producer provides
   `UniversalActiveExtremes data_j.shading.union data_j.trapezoids min_length_j`.
   Instantiate with `E' = Z.union` (which is a subset and preserves coverage)
   to obtain `HasExtremeActivePoints Z data_j.trapezoids min_length_j`.
   Then apply `shrink_to_extreme_active_points` (ExtremeShrinking.lean) to get
   trapezoids with active endpoints, length ≥ min_length, core containment,
   and preserved coverage.

6. **Unique parent**: For `delta < 1`, scales strictly decrease
   (`hierarchyScale_strict_mono`). Use `child_nests_in_unique_parent_conditional`
   (ConditionalNesting.lean) with active-endpoint slope approximation extended
   via the affine endpoint argument. The `delta = 1` boundary case requires
   separate handling (all scales = 1, all lengths = 1).

# Supporting infrastructure (all proved)

- `ExtremeShrinking.shrink_to_extreme_active_points` — core shrinking
- `ConditionalNesting.child_nests_in_unique_parent_conditional` — unique parent
- `AnchoredHierarchyHelpers.unique_parent_core_containment` — core uniqueness
- `AnchoredHierarchyHelpers.child_nests_in_unique_parent` — non-conditional version
- `OneScaleToSource.toPlaninessGraininessPackage` — source advancement
- `hierarchyScale_strict_mono`, `anchored_active_height_in_Icc` —
  scale/geometry utilities
-/
lemma construct_hierarchy_full
    {sigma hierarchyLoss delta : ℝ} {N : ℕ}
    (hN_two : 2 ≤ N)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (h_prod : HierarchyLevelProducer sigma hierarchyLoss delta N)
    (source : WZ1PlaninessGraininessPackage sigma (inputLossFun hierarchyLoss N 0) delta) :
    ∃ (Z : Kakeya.Streamlined.TubeShading source.family)
      (hZ_sub : IsSubshading Z source.shading)
      (hZ_extremal : WZ1ExtremalPair sigma hierarchyLoss source.family source.uniform Z)
      (trapezoids : Fin N → Finset WZ1VerticalTrapezoid)
      (h_level_nonempty : ∀ j, (trapezoids j).Nonempty)
      (h_height_eq : ∀ j, ∀ t ∈ trapezoids j,
          t.height = wz1Corollary26Scale delta N j)
      (h_slope_bound : ∀ j, ∀ t ∈ trapezoids j, |t.slope| ≤ 2)
      (h_length_bounds : ∀ j, ∀ t ∈ trapezoids j,
          Real.rpow (wz1Corollary26Scale delta N j) (1 / 2 + hierarchyLoss) ≤ t.length ∧
          t.length ≤ Real.sqrt (wz1Corollary26Scale delta N j))
      (h_separated_cores : ∀ j, ∀ t ∈ trapezoids j, ∀ s ∈ trapezoids j, t ≠ s →
          ∀ z ∈ t.core, ∀ w ∈ s.core,
            Real.sqrt (wz1Corollary26Scale delta N j) ≤ |z - w|)
      (h_active_endpoints : ∀ j, ∀ t ∈ trapezoids j,
          horizontalSlice Z.union t.left ≠ ∅ ∧
          horizontalSlice Z.union t.right ≠ ∅)
      (h_slope_approximation : ∀ j, ∀ t ∈ trapezoids j, ∀ z ∈ t.core,
          horizontalSlice Z.union z ≠ ∅ →
            |source.global_grains.slope z - t.affine z| ≤ wz1Corollary26Scale delta N j)
      (h_active_height_coverage : ∀ j, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
          horizontalSlice Z.union z ≠ ∅ → ∃ t ∈ trapezoids j, z ∈ t.core)
      (h_unique_parent : ∀ parentLevel childLevel : Fin N,
          (parentLevel : ℕ) + 1 = (childLevel : ℕ) →
            ∀ child ∈ trapezoids childLevel,
              ∃! parent, parent ∈ trapezoids parentLevel ∧
                child.IsNumericallyNestedIn parent),
      True := by
  have hN_pos : 0 < N := by linarith
  let last : ℕ := N - 1
  have hlast_lt : last < N := by omega
  let build := buildLevelData hN_pos hdelta_pos hdelta_one hhierarchyLoss h_prod source
  have h_family_eq : ∀ (j : ℕ) (hj : j < N),
      (build j hj).1.family = source.family := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j' ih =>
      simp [build, buildLevelData, WZ1LocallyLinearOneScaleData.toPlaninessGraininessPackage] <;> exact ih (by omega)
  have h_uniform_transport : ∀ (j : ℕ) (hj : j < N),
      (h_family_eq j hj) ▸ (build j hj).1.uniform = source.uniform := by
    intro j hj
    induction j with
    | zero =>
      dsimp only [build, buildLevelData] <;> rfl
    | succ j' ih =>
      have h1 : (build (j'+1) (by omega)).1.uniform = (build j' (by omega)).1.uniform := by
        simp [build, buildLevelData, WZ1LocallyLinearOneScaleData.toPlaninessGraininessPackage] <;> rfl
      rw [h1]
      have h2 : (h_family_eq (j'+1) (by omega)) ▸ (build j' (by omega)).1.uniform =
               (h_family_eq j' (by omega)) ▸ (build j' (by omega)).1.uniform := by
        congr <;> simp [build, buildLevelData, WZ1LocallyLinearOneScaleData.toPlaninessGraininessPackage] <;> rfl
      rw [h2]; exact ih (by omega)
  have h_slope_eq : ∀ (j : ℕ) (hj : j < N),
      (build j hj).1.global_grains.slope = source.global_grains.slope := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j' ih =>
      simp [build, buildLevelData, WZ1LocallyLinearOneScaleData.toPlaninessGraininessPackage] <;> exact ih (by omega)
  let shading_j (j : ℕ) (hj : j < N) : Kakeya.Streamlined.TubeShading source.family :=
    h_family_eq j hj ▸ (build j hj).2.1.shading
  let Z : Kakeya.Streamlined.TubeShading source.family := shading_j last hlast_lt
  have hZ_union_eq : Z.union = (build last hlast_lt).2.1.shading.union :=
    transport_union (h_family_eq last hlast_lt) (build last hlast_lt).2.1.shading
  have h_outputLast_eq : outputLossFun hierarchyLoss N last = hierarchyLoss := by
    simp [outputLossFun, last] <;> omega
  have h_ext_raw : WZ1ExtremalPair sigma (outputLossFun hierarchyLoss N last)
      (build last hlast_lt).1.family (build last hlast_lt).1.uniform
      (build last hlast_lt).2.1.shading := (build last hlast_lt).2.1.extremal
  have h_ext_raw2 : WZ1ExtremalPair sigma hierarchyLoss
      (build last hlast_lt).1.family (build last hlast_lt).1.uniform
      (build last hlast_lt).2.1.shading := by
    simpa [WZ1ExtremalPair, h_outputLast_eq] using h_ext_raw
  have hZ' : h_family_eq last hlast_lt ▸ (build last hlast_lt).2.1.shading = Z := by rfl
  have hZ_extremal : WZ1ExtremalPair sigma hierarchyLoss source.family source.uniform Z :=
    transport_extremal (h_family_eq last hlast_lt)
      (h_uniform_transport last hlast_lt) hZ' h_ext_raw2
  have hZ_ball : Z.union ⊆ Metric.closedBall (0 : Point3) 1 := hZ_extremal.2.2.2.1
  have h_chain_shading : ∀ (j k : ℕ) (hj : j < N) (hk : k < N) (hjk : j ≤ k),
      IsSubshading (shading_j k hk) (shading_j j hj) := by
    intro j k hj hk hjk
    induction k with
    | zero =>
      have h_j0 : j = 0 := by omega
      subst h_j0
      exact fun _ => Set.Subset.refl _
    | succ k ih =>
      by_cases h_jk : j = k + 1
      · subst h_jk
        exact fun _ => Set.Subset.refl _
      · have h_j_le_k : j ≤ k := by omega
        have h_data_sub : IsSubshading (build (k + 1) hk).2.1.shading (build (k + 1) hk).1.shading :=
          (build (k + 1) hk).2.1.subshading
        have h_src_eq : (build (k + 1) hk).1.shading = (build k (by omega)).2.1.shading :=
          buildLevelData_source_shading hN_pos hdelta_pos hdelta_one hhierarchyLoss h_prod source hk
        have hsub' : IsSubshading (build (k + 1) hk).2.1.shading (build k (by omega)).2.1.shading := by
          rw [h_src_eq] at h_data_sub
          exact h_data_sub
        have h1 : IsSubshading (shading_j (k + 1) hk) (shading_j k (by omega)) :=
          transport_isSubshading (h_family_eq (k + 1) hk) hsub'
        have h2 := ih (by omega) h_j_le_k
        exact fun i => Set.Subset.trans (h1 i) (h2 i)
  have hZ_sub : IsSubshading Z source.shading := by
    have h1 : IsSubshading Z (shading_j 0 (by omega)) :=
      h_chain_shading 0 last (by omega) hlast_lt (by omega)
    have h_data_sub : IsSubshading (build 0 (by omega)).2.1.shading (build 0 (by omega)).1.shading :=
      (build 0 (by omega)).2.1.subshading
    have h2 : IsSubshading (shading_j 0 (by omega)) source.shading :=
      transport_isSubshading (h_family_eq 0 (by omega)) h_data_sub
    exact fun i => Set.Subset.trans (h1 i) (h2 i)
  have h_chain : ∀ (j : Fin N), Z.union ⊆ (build (j : ℕ) j.isLt).2.1.shading.union := by
    intro j
    rw [hZ_union_eq]
    exact buildLevelData_chain hN_pos hdelta_pos hdelta_one hhierarchyLoss h_prod source j.isLt hlast_lt (by omega)
  let origTrapezoids (j : Fin N) : Finset WZ1VerticalTrapezoid :=
    (build (j : ℕ) j.isLt).2.1.trapezoids
  let rho_j (j : Fin N) : ℝ := wz1Corollary26Scale delta N j
  have h_rho_eq : ∀ (j : Fin N), rho_j j = (rhoAt hN_pos hdelta_pos hdelta_one j j.isLt).1 := by
    intro j
    simp [rho_j, rhoAt, hierarchyScale_eq_wz1Scale, hierarchyScale] <;> rfl
  have h_transfer_coverage : ∀ (j : Fin N), ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice Z.union z ≠ ∅ → ∃ t ∈ origTrapezoids j, z ∈ t.core := by
    intro j z hz hactive
    have h_union : Z.union ⊆ (build (j : ℕ) j.isLt).2.1.shading.union := h_chain j
    have h_slice_sub : horizontalSlice Z.union z ⊆ horizontalSlice (build (j : ℕ) j.isLt).2.1.shading.union z := by
      intro p hp; exact ⟨h_union hp.1, hp.2⟩
    have h : horizontalSlice (build (j : ℕ) j.isLt).2.1.shading.union z ≠ ∅ :=
      Set.Nonempty.mono h_slice_sub (Set.nonempty_iff_ne_empty.mpr hactive) |>.ne_empty
    exact (build (j : ℕ) j.isLt).2.1.active_height_coverage z hz h
  have h_transfer_approx : ∀ (j : Fin N), ∀ t ∈ origTrapezoids j, ∀ z ∈ t.core,
      horizontalSlice Z.union z ≠ ∅ → |source.global_grains.slope z - t.affine z| ≤ rho_j j := by
    intro j t ht z hz hactive
    have h_union : Z.union ⊆ (build (j : ℕ) j.isLt).2.1.shading.union := h_chain j
    have h_slice_sub : horizontalSlice Z.union z ⊆ horizontalSlice (build (j : ℕ) j.isLt).2.1.shading.union z := by
      intro p hp; exact ⟨h_union hp.1, hp.2⟩
    have h : horizontalSlice (build (j : ℕ) j.isLt).2.1.shading.union z ≠ ∅ :=
      Set.Nonempty.mono h_slice_sub (Set.nonempty_iff_ne_empty.mpr hactive) |>.ne_empty
    have h_approx_raw := (build (j : ℕ) j.isLt).2.1.slope_approximation t ht z hz h
    have h_slope : (build (j : ℕ) j.isLt).1.global_grains.slope = source.global_grains.slope :=
      h_slope_eq (j : ℕ) j.isLt
    rw [h_slope] at h_approx_raw
    have h_rho : (rhoAt hN_pos hdelta_pos hdelta_one (j : ℕ) j.isLt).1 = rho_j j := (h_rho_eq j).symm
    rw [h_rho] at h_approx_raw
    exact h_approx_raw
  have h_extremes_j : ∀ (j : Fin N), ∀ t ∈ origTrapezoids j,
      ∃ (a b : ℝ), a ∈ activeSet Z ∩ t.core ∧ b ∈ activeSet Z ∩ t.core ∧
        (∀ z ∈ activeSet Z ∩ t.core, a ≤ z ∧ z ≤ b) ∧
        b - a ≥ Real.rpow (rho_j j) (1 / 2 + hierarchyLoss) := by
    intro j
    let extremes := (build (j : ℕ) j.isLt).2.2.down.2
    have h_min_eq : Real.rpow (rho_j j) (1 / 2 + hierarchyLoss) =
        Real.rpow (rhoAt hN_pos hdelta_pos hdelta_one j j.isLt).1 (1 / 2 + hierarchyLoss) := by
      rw [h_rho_eq j]
    have h_activeSet_eq : activeSet Z = activeSetOf Z.union := by rfl
    rw [h_min_eq]
    intro t ht
    have h := extremes Z.union (h_chain j) (h_transfer_coverage j) t ht
    simpa [h_activeSet_eq] using h
  have hmin_pos_j : ∀ (j : Fin N), 0 < Real.rpow (rho_j j) (1 / 2 + hierarchyLoss) := by
    intro j
    have h_rho_pos : 0 < rho_j j := by
      rw [h_rho_eq j]
      exact lt_of_lt_of_le hdelta_pos (rhoAt hN_pos hdelta_pos hdelta_one j j.isLt).2.1
    exact Real.rpow_pos_of_pos h_rho_pos _
  classical
  let f (j : Fin N) : WZ1VerticalTrapezoid → WZ1VerticalTrapezoid :=
    Classical.choose (shrink_to_extreme_active_points_with_fn
      (hmin_pos := hmin_pos_j j) (h_extremes_j j))
  have h_main : ∀ (j : Fin N),
      (∀ t ∈ origTrapezoids j,
        (f j t).left ∈ activeSet Z ∧ (f j t).right ∈ activeSet Z ∧
        Real.rpow (rho_j j) (1 / 2 + hierarchyLoss) ≤ (f j t).length ∧
        (f j t).core ⊆ t.core ∧ (f j t).slope = t.slope ∧
        (f j t).height = t.height ∧ (f j t).intercept = t.intercept ∧
        ∀ z ∈ activeSet Z ∩ t.core, z ∈ (f j t).core) ∧
      (∀ z ∈ activeSet Z, (∃ t ∈ origTrapezoids j, z ∈ t.core) →
        ∃ t' ∈ (origTrapezoids j).image (f j), z ∈ t'.core) := by
    intro j
    exact Classical.choose_spec (shrink_to_extreme_active_points_with_fn
      (hmin_pos := hmin_pos_j j) (h_extremes_j j))
  let h_props := fun j => (h_main j).1
  let h_cov := fun j => (h_main j).2
  let trapezoids (j : Fin N) : Finset WZ1VerticalTrapezoid :=
    (origTrapezoids j).image (f j)
  have h_active : ∀ (j : Fin N), ∀ t ∈ trapezoids j,
      t.left ∈ activeSet Z ∧ t.right ∈ activeSet Z := by
    intro j t ht
    rcases Finset.mem_image.mp ht with ⟨t0, ht0, rfl⟩
    exact ⟨(h_props j t0 ht0).1, (h_props j t0 ht0).2.1⟩
  have h_len_lower : ∀ (j : Fin N), ∀ t ∈ trapezoids j,
      Real.rpow (rho_j j) (1 / 2 + hierarchyLoss) ≤ t.length := by
    intro j t ht
    rcases Finset.mem_image.mp ht with ⟨t0, ht0, rfl⟩
    exact (h_props j t0 ht0).2.2.1
  have h_orig : ∀ (j : Fin N), ∀ t ∈ trapezoids j,
      ∃ (t0 : WZ1VerticalTrapezoid), t0 ∈ origTrapezoids j ∧
        t.core ⊆ t0.core ∧ t.slope = t0.slope ∧ t.height = t0.height ∧ t.intercept = t0.intercept := by
    intro j t ht
    rcases Finset.mem_image.mp ht with ⟨t0, ht0, rfl⟩
    have h := h_props j t0 ht0
    exact ⟨t0, ht0, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩
  have h_nonempty : ∀ (j : Fin N), (trapezoids j).Nonempty := by
    intro j
    have h_orig_nonempty : (origTrapezoids j).Nonempty :=
      (build (j : ℕ) j.isLt).2.1.trapezoids_nonempty
    exact h_orig_nonempty.image _
  have h_height : ∀ (j : Fin N), ∀ t ∈ trapezoids j, t.height = rho_j j := by
    intro j t ht
    rcases h_orig j t ht with ⟨s, hs, _, _, hheight, _⟩
    have h_orig_height : s.height = (rhoAt hN_pos hdelta_pos hdelta_one j j.isLt).1 :=
      (build (j : ℕ) j.isLt).2.1.height_eq s hs
    have h_rho : (rhoAt hN_pos hdelta_pos hdelta_one j j.isLt).1 = rho_j j := (h_rho_eq j).symm
    rw [hheight, h_orig_height, h_rho]
  have h_slope : ∀ (j : Fin N), ∀ t ∈ trapezoids j, |t.slope| ≤ 2 := by
    intro j t ht
    rcases h_orig j t ht with ⟨s, hs, _, hslope, _, _⟩
    have h_orig_slope : |s.slope| ≤ 2 := (build (j : ℕ) j.isLt).2.1.slope_bound s hs
    rw [hslope] at * <;> exact h_orig_slope
  have h_length : ∀ (j : Fin N), ∀ t ∈ trapezoids j,
      Real.rpow (rho_j j) (1 / 2 + hierarchyLoss) ≤ t.length ∧
      t.length ≤ Real.sqrt (rho_j j) := by
    intro j t ht
    have h_lower := h_len_lower j t ht
    rcases h_orig j t ht with ⟨s, hs, hcore_sub, _, _, _⟩
    have h_upper_orig : s.length ≤ Real.sqrt (rho_j j) := by
      have h := (build (j : ℕ) j.isLt).2.1.length_bounds s hs
      have h_rho : (rhoAt hN_pos hdelta_pos hdelta_one j j.isLt).1 = rho_j j := (h_rho_eq j).symm
      rw [h_rho] at h
      exact h.2
    have h_t_len_le_s : t.length ≤ s.length := by
      have h1 : t.left ∈ t.core := Set.left_mem_Icc.mpr t.left_lt_right.le
      have h2 : t.right ∈ t.core := Set.right_mem_Icc.mpr t.left_lt_right.le
      have h3 : t.left ∈ s.core := hcore_sub h1
      have h4 : t.right ∈ s.core := hcore_sub h2
      have h5 : s.left ≤ t.left := (Set.mem_Icc.mp h3).1
      have h6 : t.right ≤ s.right := (Set.mem_Icc.mp h4).2
      simp [WZ1VerticalTrapezoid.length] <;> linarith
    exact ⟨h_lower, h_t_len_le_s.trans h_upper_orig⟩
  have h_sep : ∀ (j : Fin N), ∀ t ∈ trapezoids j, ∀ s ∈ trapezoids j, t ≠ s →
      ∀ z ∈ t.core, ∀ w ∈ s.core, Real.sqrt (rho_j j) ≤ |z - w| := by
    intro j t ht s hs hne z hz w hw
    rcases Finset.mem_image.mp ht with ⟨t0, ht0, rfl⟩
    rcases Finset.mem_image.mp hs with ⟨s0, hs0, h_eq_s⟩
    have h_t0_ne_s0 : t0 ≠ s0 := by
      intro h_eq
      have h_t_eq_s : f j t0 = f j s0 := by rw [h_eq]
      exact hne (h_t_eq_s.trans h_eq_s)
    have hz' : z ∈ t0.core := (h_props j t0 ht0).2.2.2.1 hz
    have hw_fs0 : w ∈ (f j s0).core := h_eq_s.symm ▸ hw
    have hw' : w ∈ s0.core := (h_props j s0 hs0).2.2.2.1 hw_fs0
    have h_sep_orig := (build (j : ℕ) j.isLt).2.1.separated_cores t0 ht0 s0 hs0 h_t0_ne_s0 z hz' w hw'
    have h_rho : (rhoAt hN_pos hdelta_pos hdelta_one j j.isLt).1 = rho_j j := (h_rho_eq j).symm
    rw [h_rho] at h_sep_orig
    exact h_sep_orig
  have h_active_ep : ∀ (j : Fin N), ∀ t ∈ trapezoids j,
      horizontalSlice Z.union t.left ≠ ∅ ∧ horizontalSlice Z.union t.right ≠ ∅ := by
    intro j t ht
    have h1 : t.left ∈ activeSet Z := (h_active j t ht).1
    have h2 : t.right ∈ activeSet Z := (h_active j t ht).2
    exact ⟨h1, h2⟩
  have h_approx : ∀ (j : Fin N), ∀ t ∈ trapezoids j, ∀ z ∈ t.core,
      horizontalSlice Z.union z ≠ ∅ → |source.global_grains.slope z - t.affine z| ≤ rho_j j := by
    intro j t ht z hz hactive
    rcases h_orig j t ht with ⟨s, hs, hcore_sub, hslope, _, hintercept⟩
    have hz' : z ∈ s.core := hcore_sub hz
    have h1 : |source.global_grains.slope z - s.affine z| ≤ rho_j j :=
      h_transfer_approx j s hs z hz' hactive
    have h2 : t.affine z = s.affine z := by
      simp [WZ1VerticalTrapezoid.affine, hslope, hintercept] <;> ring
    rw [h2] at * <;> exact h1
  have h_cov' : ∀ (j : Fin N), ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice Z.union z ≠ ∅ → ∃ t ∈ trapezoids j, z ∈ t.core := by
    intro j z hz hactive
    have h1 : ∃ t ∈ origTrapezoids j, z ∈ t.core := h_transfer_coverage j z hz hactive
    have hz_active : z ∈ activeSet Z := hactive
    exact h_cov j z hz_active h1
  have h_unique_parent : ∀ (parentLevel childLevel : Fin N),
      (parentLevel : ℕ) + 1 = (childLevel : ℕ) →
        ∀ child ∈ trapezoids childLevel,
          ∃! parent, parent ∈ trapezoids parentLevel ∧ child.IsNumericallyNestedIn parent := by
    intro parentLevel childLevel h_adj child hchild
    by_cases hdelta_lt_one : delta < 1
    · have h_child_lt_parent : rho_j childLevel < rho_j parentLevel := by
        have h1 : (parentLevel : ℕ) < (childLevel : ℕ) := by omega
        have h_raw := hierarchyScale_strict_mono hdelta_pos hdelta_lt_one h1 childLevel.isLt
        have h_eq_c := hierarchyScale_eq_wz1Scale (delta := delta) (N := N) (j := childLevel)
        have h_eq_p := hierarchyScale_eq_wz1Scale (delta := delta) (N := N) (j := parentLevel)
        rw [h_eq_c, h_eq_p] at h_raw
        exact h_raw
      have h_rho_parent_pos : 0 < rho_j parentLevel := Real.rpow_pos_of_pos hdelta_pos _
      have h_rho_child_pos : 0 < rho_j childLevel := Real.rpow_pos_of_pos hdelta_pos _
      have h_left_in_Icc : child.left ∈ Set.Icc (-1 : ℝ) 1 :=
        anchored_active_height_in_Icc hZ_ball
          (h_active_ep childLevel child hchild).1
      have h_right_in_Icc : child.right ∈ Set.Icc (-1 : ℝ) 1 :=
        anchored_active_height_in_Icc hZ_ball
          (h_active_ep childLevel child hchild).2
      have h_left_covered : ∃ p ∈ trapezoids parentLevel, child.left ∈ p.core :=
        h_cov' parentLevel child.left h_left_in_Icc (h_active_ep childLevel child hchild).1
      have h_right_covered : ∃ p ∈ trapezoids parentLevel, child.right ∈ p.core :=
        h_cov' parentLevel child.right h_right_in_Icc (h_active_ep childLevel child hchild).2
      have h_unique_core := unique_parent_core_containment
        h_rho_parent_pos h_rho_child_pos (h_sep parentLevel)
        (h_length childLevel child hchild |>.2) h_child_lt_parent
        h_left_covered h_right_covered
      rcases h_unique_core with ⟨parent, ⟨hp_mem, h_core_sub⟩, h_uniq_core⟩
      have h_child_left_active : horizontalSlice Z.union child.left ≠ ∅ :=
        (h_active_ep childLevel child hchild).1
      have h_child_right_active : horizontalSlice Z.union child.right ≠ ∅ :=
        (h_active_ep childLevel child hchild).2
      have h_child_approx_left := h_approx childLevel child hchild child.left
        (Set.left_mem_Icc.mpr child.left_lt_right.le) h_child_left_active
      have h_child_approx_right := h_approx childLevel child hchild child.right
        (Set.right_mem_Icc.mpr child.left_lt_right.le) h_child_right_active
      have h_parent_approx_left := h_approx parentLevel parent hp_mem child.left
        (h_core_sub (Set.left_mem_Icc.mpr child.left_lt_right.le)) h_child_left_active
      have h_parent_approx_right := h_approx parentLevel parent hp_mem child.right
        (h_core_sub (Set.right_mem_Icc.mpr child.left_lt_right.le)) h_child_right_active
      have h_nesting := numerical_nesting_from_endpoint_approximations
        (h_height childLevel child hchild) (h_height parentLevel parent hp_mem)
        h_core_sub h_child_approx_left h_child_approx_right
        h_parent_approx_left h_parent_approx_right
      refine ⟨parent, ⟨hp_mem, h_nesting⟩, ?_⟩
      intro q hq
      have hq_core_sub : child.core ⊆ q.core := hq.2.1
      exact h_uniq_core q ⟨hq.1, hq_core_sub⟩
    · have hdelta_eq : delta = 1 := by linarith
      have h_rho_eq1 : ∀ (j : Fin N), rho_j j = 1 := by
        intro j
        have h : rho_j j = wz1Corollary26Scale delta N j := by rfl
        rw [h, hdelta_eq]
        simp [wz1Corollary26Scale] <;> norm_num
      have h_len1 : ∀ (j : Fin N), ∀ t ∈ trapezoids j, t.length = 1 := by
        intro j t ht
        have hlb := h_length j t ht
        have hr : rho_j j = 1 := h_rho_eq1 j
        rw [hr] at hlb
        have h1 : Real.rpow (1 : ℝ) (1 / 2 + hierarchyLoss) = 1 := by simp
        have h2 : Real.sqrt (1 : ℝ) = 1 := by simp
        rw [h1, h2] at hlb <;> linarith
      have h_cores_in_Icc : ∀ (j : Fin N), ∀ t ∈ trapezoids j, t.core ⊆ Set.Icc (-1 : ℝ) 1 := by
        intro j t ht
        have h_left_Icc : t.left ∈ Set.Icc (-1 : ℝ) 1 :=
          anchored_active_height_in_Icc hZ_ball (h_active_ep j t ht).1
        have h_right_Icc : t.right ∈ Set.Icc (-1 : ℝ) 1 :=
          anchored_active_height_in_Icc hZ_ball (h_active_ep j t ht).2
        intro z hz
        have h1 : t.left ≤ z := (Set.mem_Icc.mp hz).1
        have h2 : z ≤ t.right := (Set.mem_Icc.mp hz).2
        exact Set.mem_Icc.mpr ⟨by linarith [(Set.mem_Icc.mp h_left_Icc).1, (Set.mem_Icc.mp h_right_Icc).2],
          by linarith [(Set.mem_Icc.mp h_left_Icc).1, (Set.mem_Icc.mp h_right_Icc).2]⟩
      have h_sep1 : ∀ (j : Fin N), ∀ t ∈ trapezoids j, ∀ s ∈ trapezoids j, t ≠ s →
          ∀ z ∈ t.core, ∀ w ∈ s.core, (1 : ℝ) ≤ |z - w| := by
        intro j t ht s hs hne z hz w hw
        have h := h_sep j t ht s hs hne z hz w hw
        have hr : rho_j j = 1 := h_rho_eq1 j
        rw [hr] at h
        have hsqrt1 : Real.sqrt (1 : ℝ) = 1 := by norm_num
        rw [hsqrt1] at h
        exact h
      have h_at_most_one : ∀ (j : Fin N), ∀ t ∈ trapezoids j, ∀ s ∈ trapezoids j, t = s :=
        fun j => at_most_one_trapezoid_delta_one (h_len1 j) (h_sep1 j) (h_cores_in_Icc j)
      rcases h_nonempty parentLevel with ⟨parent, hp_mem⟩
      have h_parent_unique : ∀ q ∈ trapezoids parentLevel, q = parent :=
        fun q hq => h_at_most_one parentLevel q hq parent hp_mem
      have h_left_covered : ∃ p ∈ trapezoids parentLevel, child.left ∈ p.core :=
        h_cov' parentLevel child.left
          (anchored_active_height_in_Icc hZ_ball
            (h_active_ep childLevel child hchild).1)
          (h_active_ep childLevel child hchild).1
      rcases h_left_covered with ⟨p_left, hp_left_mem, h_left_in⟩
      have hp_left_eq : p_left = parent := h_parent_unique p_left hp_left_mem
      have h_core_sub : child.core ⊆ parent.core := by
        rw [hp_left_eq] at h_left_in
        intro z hz
        have h1 : child.left ≤ z := (Set.mem_Icc.mp hz).1
        have h2 : z ≤ child.right := (Set.mem_Icc.mp hz).2
        have h3 : parent.left ≤ child.left := (Set.mem_Icc.mp h_left_in).1
        have h4 : child.right ≤ parent.right := by
          rcases h_cov' parentLevel child.right
            (anchored_active_height_in_Icc hZ_ball
              (h_active_ep childLevel child hchild).2)
            (h_active_ep childLevel child hchild).2 with ⟨p_right, hp_right_mem, h_right_in⟩
          have hp_right_eq : p_right = parent := h_parent_unique p_right hp_right_mem
          rw [hp_right_eq] at h_right_in
          exact (Set.mem_Icc.mp h_right_in).2
        exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
      have h_child_left_active : horizontalSlice Z.union child.left ≠ ∅ :=
        (h_active_ep childLevel child hchild).1
      have h_child_right_active : horizontalSlice Z.union child.right ≠ ∅ :=
        (h_active_ep childLevel child hchild).2
      have h_child_approx_left := h_approx childLevel child hchild child.left
        (Set.left_mem_Icc.mpr child.left_lt_right.le) h_child_left_active
      have h_child_approx_right := h_approx childLevel child hchild child.right
        (Set.right_mem_Icc.mpr child.left_lt_right.le) h_child_right_active
      have h_parent_approx_left := h_approx parentLevel parent hp_mem child.left
        (h_core_sub (Set.left_mem_Icc.mpr child.left_lt_right.le)) h_child_left_active
      have h_parent_approx_right := h_approx parentLevel parent hp_mem child.right
        (h_core_sub (Set.right_mem_Icc.mpr child.left_lt_right.le)) h_child_right_active
      have h_nesting := numerical_nesting_from_endpoint_approximations
        (h_height childLevel child hchild) (h_height parentLevel parent hp_mem)
        h_core_sub h_child_approx_left h_child_approx_right
        h_parent_approx_left h_parent_approx_right
      refine ⟨parent, ⟨hp_mem, h_nesting⟩, ?_⟩
      intro q hq
      exact h_parent_unique q hq.1
  exact ⟨Z, hZ_sub, hZ_extremal, trapezoids, h_nonempty, h_height, h_slope,
    h_length, h_sep, h_active_ep, h_approx, h_cov', h_unique_parent, trivial⟩

/-! ## Main iteration lemma — proved assembly from construct_hierarchy_full -/

/--
Iterate the one-scale producer across all N hierarchy levels, producing
a final shading, extremality, and full anchored hierarchy data.

The data assembly and geometric construction are both proved in
`construct_hierarchy_full` above.
-/
lemma iterate_anchored_hierarchy
    {sigma hierarchyLoss delta : ℝ} {N : ℕ}
    (hN_two : 2 ≤ N)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (h_prod : HierarchyLevelProducer sigma hierarchyLoss delta N)
    (source : WZ1PlaninessGraininessPackage sigma (inputLossFun hierarchyLoss N 0) delta) :
    ∃ (Z : Kakeya.Streamlined.TubeShading source.family)
      (hZ_sub : IsSubshading Z source.shading)
      (hZ_extremal : WZ1ExtremalPair sigma hierarchyLoss source.family source.uniform Z)
      (h_hierarchy : WZ1Corollary26AnchoredHierarchyData Z source.global_grains.slope hierarchyLoss),
      h_hierarchy.levelCount = N := by
  rcases construct_hierarchy_full hN_two hhierarchyLoss hdelta_pos hdelta_one h_prod source with
    ⟨Z, hZ_sub, hZ_extremal, trapezoids, h_level_nonempty, h_height_eq, h_slope_bound,
     h_length_bounds, h_separated_cores, h_active_endpoints, h_slope_approximation,
     h_active_height_coverage, h_unique_parent, _⟩
  let h_hierarchy : WZ1Corollary26AnchoredHierarchyData Z source.global_grains.slope hierarchyLoss :=
    { levelCount := N
      levelCount_two := hN_two
      trapezoids := trapezoids
      level_nonempty := h_level_nonempty
      height_eq := h_height_eq
      slope_bound := h_slope_bound
      length_bounds := h_length_bounds
      separated_cores := h_separated_cores
      active_endpoints := h_active_endpoints
      slope_approximation := h_slope_approximation
      active_height_coverage := h_active_height_coverage
      unique_parent := h_unique_parent }
  exact ⟨Z, hZ_sub, hZ_extremal, h_hierarchy, rfl⟩

/-! ## Main theorem -/

/-- Build the anchored hierarchy conclusion from a generalized producer. -/
lemma anchored_hierarchy_from_gen_producer
    (h_gen : GeneralizedOneScaleProducer) :
    WZ1Corollary26AnchoredHierarchyConclusion := by
  intro sigma hierarchyLoss hsigma hsigma1 hhierarchyLoss
  intro _hFloor
  intro levelCount hlevelCount
  let N := levelCount
  have hN_pos : 0 < N := by linarith
  have hN_two : 2 ≤ N := hlevelCount
  -- Get uniform delta₀ working for all hierarchy levels
  rcases gen_to_hierarchy_producer h_gen hsigma hsigma1 hhierarchyLoss hN_pos with
    ⟨delta₀, hdelta₀_pos, hdelta₀_one, h_prod_for_delta⟩
  let sourceLossCeiling := inputLossFun hierarchyLoss N 0
  have hsrc_pos : 0 < sourceLossCeiling :=
    inputLoss_pos hierarchyLoss hhierarchyLoss N 0
  have hsrc_le : sourceLossCeiling ≤ hierarchyLoss / 100 :=
    sourceLossCeiling_le_hierarchyLoss_div_100 hierarchyLoss N hN_two hhierarchyLoss
  refine ⟨sourceLossCeiling, delta₀, hsrc_pos, hsrc_le, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro inputLoss hinputLoss hinputLossCeiling
  intro delta hdelta hdelta₀_small source
  let hdelta_one : delta ≤ 1 := hdelta₀_small.trans hdelta₀_one
  -- Weaken source to the schedule's level-0 input loss
  let initialSource : WZ1PlaninessGraininessPackage sigma (inputLossFun hierarchyLoss N 0) delta :=
    weakenSourcePackage source hinputLossCeiling hdelta hdelta_one
  -- Get hierarchy-level producer for this delta
  let h_prod : HierarchyLevelProducer sigma hierarchyLoss delta N :=
    h_prod_for_delta delta hdelta hdelta₀_small
  -- Run the iteration
  rcases iterate_anchored_hierarchy hN_two hhierarchyLoss hdelta hdelta_one h_prod initialSource with
    ⟨Z, hZ_sub, hZ_extremal, h_hierarchy, h_levelCount⟩
  -- Assemble final package
  have h_inputLoss_le_hierarchy : inputLoss ≤ hierarchyLoss := by
    calc inputLoss ≤ sourceLossCeiling := hinputLossCeiling
         _ ≤ hierarchyLoss / 100 := hsrc_le
         _ ≤ hierarchyLoss := by linarith
  let finalPackage := packageAssembly source h_inputLoss_le_hierarchy Z hZ_sub hZ_extremal h_hierarchy
  refine ⟨finalPackage, ?_⟩
  have h_eq : finalPackage.hierarchy.levelCount = levelCount := by
    have h1 : finalPackage.hierarchy = h_hierarchy := by rfl
    rw [h1, h_levelCount] <;> rfl
  exact h_eq

end Kakeya.Assouad
