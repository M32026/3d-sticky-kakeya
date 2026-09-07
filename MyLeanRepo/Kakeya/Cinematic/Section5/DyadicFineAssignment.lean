import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.LocalAssembly.Infrastructure
import MyLeanRepo.Kakeya.Cinematic.Section5.LocalAssembly.TwoEndsBridge
import MyLeanRepo.Kakeya.Cinematic.Section5.PointwiseFineRectangle
import MyLeanRepo.Kakeya.Cinematic.Section5.FineShadings
import MyLeanRepo.Kakeya.Cinematic.Section5.RectangleShorteningInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.RectangleShortening
import MyLeanRepo.Kakeya.Cinematic.Section5.PointwiseRectangleShortening
import MyLeanRepo.Kakeya.Cinematic.Section5.FiniteMeasurableCoverRetainedMass
import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicFineAssignmentData
import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicRepresentative

/-!
# Dyadic fine assignment with retained mass

Given a cinematic family, a finite subfamily F, and a level set E₀ with high
multiplicity, pre-compute two-ends certificates per exact fiber, bin points by
dyadic scales of `t_fine = 4*t` and `Delta`, select a retained-mass bin, and
construct a common-scale `FineRectangleAssignmentData` using
`pointwise_rectangle_shortening`.

This module removes the old `t ≤ 1` restriction: with the updated
`FineRectangleAssignmentStatement`, fine rectangles exist at arbitrary scales.
The dyadic range covers up to `4*K` using the hypothesis
`2^N * δ_vert ≥ 4*K`, so every fiber fits into a regular bin (no sentinel).

Whiteprint node: `dyadic-fine-assignment`
Dependencies: `rectangle-shortening`, `pointwise-rectangle-shortening`,
  `finite-measurable-cover-retained-mass`
-/

attribute [local instance] Classical.propDecidable

open MeasureTheory Set Metric

namespace Kakeya.Cinematic

/-- Type of the pointwise fine-rectangle assigner after fixing `C_R`. -/
def PointwiseFineRectangleAssigner (K D C_R : ℝ) : Prop :=
  ∀ (family : Set C2Function), IsCinematicFamily family K D →
    ∀ (I : ParameterInterval), I.IsControlled K →
      ∀ (delta t Delta : ℝ), 0 < delta → delta ≤ Delta → Delta ≤ t →
        ∀ (p : UnitPoint × ℝ), p.1 ∈ I.centeredCarrier (1 / 8) →
          ∀ (k : C2Function), k ∈ family → |p.2 - k p.1| ≤ delta →
            ∀ (G : FiniteFunctionFamily), G.carrier ⊆ family →
              (∀ f ∈ G.carrier,
                c2Distance f k ≤ 6 * t ∧
                tangencyParameterOn I f k ≤ Delta ∧
                |p.2 - f p.1| ≤ delta) →
              ∃ R : CurvilinearRectangle delta (C_R * t * Delta / delta),
                R.function = k ∧
                R.interval.midpoint = (p.1 : ℝ) ∧
                p ∈ R.carrier ∧
                R.IsOverCentralQuarterOf I ∧
                ∀ f ∈ G.carrier, R.IsLambdaTangent f 5

/--
Dyadic binning + retained mass + common-scale fine rectangle assignment.

Pre-computes two-ends output per exact fiber, bins by dyadic scales, selects
a retained-mass bin, and uses `pointwise_rectangle_shortening` to produce a
`FineRectangleAssignmentData` at representative scales.
-/
lemma dyadic_fine_assignment_at_fixed_constant_core
    (hTwoEnds : TwoEndsSelectionStatement)
    (hTangencyTwoEnds : TangencyTwoEndsSelectionStatement)
    {K D : ℝ} (hK : 1 ≤ K) (hD : 1 ≤ D)
    (C_R : ℝ) (hC_R_large : 9216 * K^2 ≤ C_R)
    (hFine_main : PointwiseFineRectangleAssigner K D C_R)
    {family : Set C2Function} (hfamily : IsCinematicFamily family K D)
    {F : FiniteFunctionFamily} (hF : F.carrier ⊆ family)
    {I : ParameterInterval} (hI : I.IsControlled K)
    {δ_base : ℝ} (hδ_base_pos : 0 < δ_base)
    {separationScale : ℝ} (hseparationScale_pos : 0 < separationScale)
    (hF_separated : F.IsDeltaSeparated separationScale)
    {μ : ℕ} (hmu : 0 < μ)
    (L : ℝ) (hL_nonneg : 0 ≤ L)
    (hbounds : ∀ f ∈ family, ∀ z : UnitPoint, |f.firstDeriv z| ≤ L)
    (hδ_vert_le_K : (1 + L) * δ_base ≤ K)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (eta : ℝ) (heta : 0 < eta)
    {c : ℝ}
    {E₀ : Set (ℝ × ℝ)}
    (hE₀_meas : MeasurableSet E₀)
    (hE₀_nonempty : E₀.Nonempty)
    (hE₀_sub : E₀ ⊆ I.realCenteredCarrier (1 / 16) ×ˢ Set.Icc c (c + 1))
    (hmult : ∀ p ∈ E₀, (μ : ℝ) ≤ multiplicity F δ_base p)
    (logLoss : ℝ) (hlogLoss : 1 ≤ logLoss)
    (N : ℕ) (hN2 : 2 ≤ N)
    (hN_scale : (2 : ℝ)^N * (1 + L) * δ_base ≥ 4 * K)
    (hN_card : (N * N : ℝ) ≤ logLoss) :
    ∃ (E₂ : Set (ℝ × ℝ)) (t_rep Delta_rep : ℝ)
      (data : DyadicFineAssignmentData
        family E₂ K ((1 + L) * δ_base) K epsilon eta t_rep Delta_rep C_R),
      data.mu = μ ∧
      data.ambientSource = F ∧
      (∀ p : E₂,
        data.source p =
          finsetToFFF
            (functionsNearPoint F δ_base (p : ℝ × ℝ))) ∧
      MeasurableSet E₂ ∧ E₂ ⊆ E₀ ∧
      volume E₀ ≤ ENNReal.ofReal logLoss * volume E₂ := by
  let δ_vert := (1 + L) * δ_base
  have hδ_vert_pos : 0 < δ_vert := by
    have h1 : 0 < 1 + L := by linarith
    positivity
  have hδ_vert_le_K' : δ_vert ≤ K := hδ_vert_le_K
  have hN_scale' : (2 : ℝ)^N * δ_vert ≥ 4 * K := by
    have h_assoc : (2 : ℝ)^N * (1 + L) * δ_base =
        (2 : ℝ)^N * ((1 + L) * δ_base) := by
      ring
    have h' : (2 : ℝ)^N * ((1 + L) * δ_base) ≥ 4 * K := by
      rw [← h_assoc]
      exact hN_scale
    have hδ : δ_vert = (1 + L) * δ_base := by rfl
    rw [hδ]
    exact h'

  let zeroC2 : C2Function :=
    { value := 0
      firstDeriv := 0
      secondDeriv := 0
      hasExtension := by
        use fun _ => 0
        exact ⟨contDiff_const, by simp, by simp, by simp⟩ }

  have hC_R_pos : 0 < C_R := by
    have h : 9216 * K^2 ≤ C_R := hC_R_large
    nlinarith

  rcases hE₀_nonempty with ⟨p0, hp0⟩
  have hF_nonempty : F.carrier.Nonempty := by
    have hmult0 : (μ : ℝ) ≤ multiplicity F δ_base p0 := hmult p0 hp0
    have hS : (functionsNearPoint F δ_base p0).Nonempty :=
      functionsNearPoint_nonempty hmu hmult0
    rcases hS with ⟨f, hf⟩
    have hfF : f ∈ F.toFinset := (Finset.mem_filter.mp hf).1
    exact ⟨f, F.finite.mem_toFinset.mp hfF⟩
  let defaultC2 : C2Function := hF_nonempty.some

  let P : Finset C2Function → Prop := fun S => S.Nonempty ∧ S ⊆ F.toFinset
  have h_exists : ∀ (S : Finset C2Function), P S →
      ∃ (t Delta : ℝ) (center k : C2Function) (G H : FiniteFunctionFamily),
        TwoEndsCertificate I δ_vert K epsilon eta t Delta
          (finsetToFFF S) G H center k := by
    intro S hS
    let S_FFF := finsetToFFF S
    have hS_nonempty : S_FFF.carrier.Nonempty := by
      exact_mod_cast hS.1
    have hS_diameter : S_FFF.DiameterLE K := by
      intro f hf g hg
      have hf_F : f ∈ F.carrier := by
        have h2 : f ∈ S := by exact_mod_cast hf
        have h3 : f ∈ F.toFinset := hS.2 h2
        exact F.finite.mem_toFinset.mp h3
      have hg_F : g ∈ F.carrier := by
        have h2 : g ∈ S := by exact_mod_cast hg
        have h3 : g ∈ F.toFinset := hS.2 h2
        exact F.finite.mem_toFinset.mp h3
      exact hfamily.1 (hF hf_F) (hF hg_F)
    have h_main : ∃ (t : ℝ) (center : C2Function) (G : FiniteFunctionFamily)
        (Delta : ℝ) (k : C2Function) (H : FiniteFunctionFamily),
        TwoEndsCertificate I δ_vert K epsilon eta t Delta S_FFF G H center k :=
      localAssembly_two_ends_bridge_with_certificate
        hTwoEnds hTangencyTwoEnds
        hepsilon heta hδ_vert_pos hδ_vert_le_K' I S_FFF
        hS_nonempty hS_diameter
    rcases h_main with ⟨t, center, G, Delta, k, H, hcert⟩
    exact ⟨t, Delta, center, k, G, H, hcert⟩

  choose tP DeltaP centerP kP GP HP hcertP using h_exists

  let t (S : Finset C2Function) : ℝ := if h : P S then tP S h else 0
  let Delta (S : Finset C2Function) : ℝ := if h : P S then DeltaP S h else 0
  let center (S : Finset C2Function) : C2Function :=
    if h : P S then centerP S h else defaultC2
  let k (S : Finset C2Function) : C2Function :=
    if h : P S then kP S h else defaultC2
  let G (S : Finset C2Function) : FiniteFunctionFamily :=
    if h : P S then GP S h else {carrier := ∅, finite := Set.finite_empty}
  let H (S : Finset C2Function) : FiniteFunctionFamily :=
    if h : P S then HP S h else {carrier := ∅, finite := Set.finite_empty}

  let dyadicIdx (x : ℝ) (hx : x ≤ (2 : ℝ)^N * δ_vert) : Fin N :=
    let Q : ℕ → Prop := fun k => x ≤ (2 : ℝ)^(k + 1) * δ_vert
    have hQN1 : Q (N - 1) := by
      dsimp only [Q]
      have h_exp : (N - 1) + 1 = N := by omega
      rw [h_exp]
      exact hx
    have hQ : ∃ k : ℕ, Q k := ⟨N - 1, hQN1⟩
    let k := Nat.find hQ
    have h_k_lt : k < N := by
      have h_k_le : k ≤ N - 1 := Nat.find_min' hQ hQN1
      omega
    ⟨k, h_k_lt⟩

  have h_dyadicIdx_spec : ∀ (x : ℝ) (hx : x ≤ (2 : ℝ)^N * δ_vert),
      x ≤ (2 : ℝ)^((dyadicIdx x hx).val + 1) * δ_vert := by
    intro x hx
    let Q : ℕ → Prop := fun k => x ≤ (2 : ℝ)^(k + 1) * δ_vert
    have hQN1 : Q (N - 1) := by
      dsimp only [Q]
      have h_exp : (N - 1) + 1 = N := by omega
      rw [h_exp]
      exact hx
    have hQ : ∃ k : ℕ, Q k := ⟨N - 1, hQN1⟩
    have h : (dyadicIdx x hx).val = Nat.find hQ := by
      unfold dyadicIdx
      rfl
    rw [h]
    exact Nat.find_spec hQ

  have h_dyadicIdx_minimal :
      ∀ (x : ℝ) (hx : x ≤ (2 : ℝ)^N * δ_vert),
        ∀ j < (dyadicIdx x hx).val,
          ¬ x ≤ (2 : ℝ)^(j + 1) * δ_vert := by
    intro x hx j hj
    let Q : ℕ → Prop :=
      fun k => x ≤ (2 : ℝ)^(k + 1) * δ_vert
    have hQN1 : Q (N - 1) := by
      dsimp only [Q]
      have h_exp : (N - 1) + 1 = N := by omega
      rw [h_exp]
      exact hx
    have hQ : ∃ k : ℕ, Q k := ⟨N - 1, hQN1⟩
    have hidx : (dyadicIdx x hx).val = Nat.find hQ := by
      unfold dyadicIdx
      rfl
    rw [hidx] at hj
    exact Nat.find_min hQ hj

  let label (S : Finset C2Function) : Fin N × Fin N :=
    if h : P S then
      let t_metric := tP S h
      let Delta_val := DeltaP S h
      let t_fine := 4 * t_metric
      have h_tfine_bound : t_fine ≤ (2 : ℝ)^N * δ_vert := by
        have h_t_le_K : t_metric ≤ K := (hcertP S h).t_le_diameter
        have h2 : t_fine ≤ 4 * K := by linarith
        linarith [hN_scale']
      have h_Delta_bound : Delta_val ≤ (2 : ℝ)^N * δ_vert := by
        have h_t_le_K : t_metric ≤ K := (hcertP S h).t_le_diameter
        have h1 : Delta_val ≤ 4 * t_metric := (hcertP S h).Delta_le_four_t
        have h2 : Delta_val ≤ 4 * K := by linarith
        linarith [hN_scale']
      (dyadicIdx t_fine h_tfine_bound, dyadicIdx Delta_val h_Delta_bound)
    else
      (⟨0, by omega⟩, ⟨0, by omega⟩)

  let binSet (b : Fin N × Fin N) : Set (ℝ × ℝ) :=
    {p | label (functionsNearPoint F δ_base p) = b}

  have h_bin_meas : ∀ b : Fin N × Fin N, MeasurableSet (binSet b) := by
    intro b
    exact measurableSet_functionsNearPoint_label_eq F δ_base label b

  have h_cover : E₀ ⊆ ⋃ b : Fin N × Fin N, binSet b := by
    intro p hp
    let b := label (functionsNearPoint F δ_base p)
    have h : p ∈ binSet b := by
      simp only [binSet, Set.mem_setOf_eq]
      rfl
    exact Set.mem_iUnion.mpr ⟨b, h⟩

  have hE₀_finite : volume E₀ < ⊤ := by
    have h1 : I.realCenteredCarrier (1 / 16) ⊆ Set.Icc (0 : ℝ) 1 := by
      intro x hx
      exact hx.1
    have h2 : E₀ ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c (c + 1) := by
      calc
        E₀ ⊆ I.realCenteredCarrier (1 / 16) ×ˢ Set.Icc c (c + 1) := hE₀_sub
        _ ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c (c + 1) := by gcongr
    have h3 : volume (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c (c + 1)) = 1 := by
      rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
      rw [MeasureTheory.Measure.prod_prod (Set.Icc (0 : ℝ) 1) (Set.Icc c (c + 1))]
      rw [Real.volume_Icc, Real.volume_Icc] <;> norm_num
    have h4 : volume E₀ ≤ volume (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c (c + 1)) :=
      measure_mono h2
    rw [h3] at h4
    exact lt_of_le_of_lt h4 (by norm_num)

  letI : Nonempty (Fin N × Fin N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩

  have h_card : (Fintype.card (Fin N × Fin N) : ℝ) ≤ logLoss := by
    simp [Fintype.card_prod, hN_card] <;> ring

  rcases finite_measurable_cover_retained_mass E₀ binSet logLoss
      hE₀_meas hE₀_finite h_bin_meas h_cover (by linarith) h_card
    with ⟨b, hE2_meas, hE2_sub, h_retention⟩

  let E₂ := E₀ ∩ binSet b
  let i := b.1
  let j := b.2
  let t_bin := (2 : ℝ)^(i.val + 1) * δ_vert
  let D_rep := (2 : ℝ)^(j.val + 1) * δ_vert
  let t_rep := max t_bin D_rep

  have hD_rep_pos : 0 < D_rep := by
    dsimp only [D_rep]
    positivity
  have ht_rep_pos : 0 < t_rep := by
    exact hD_rep_pos.trans_le (le_max_right t_bin D_rep)
  have hD_rep_le_t_rep : D_rep ≤ t_rep :=
    le_max_right t_bin D_rep
  have hdelta_le_D_rep : δ_vert ≤ D_rep := by
    dsimp only [D_rep]
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (j.val + 1) := by
      exact one_le_pow₀ (by norm_num)
    nlinarith

  have h_normal_all : ∀ (p : E₂),
      P (functionsNearPoint F δ_base (p : ℝ × ℝ)) := by
    intro p
    let S := functionsNearPoint F δ_base (p : ℝ × ℝ)
    have hS_nonempty : S.Nonempty := functionsNearPoint_nonempty hmu
      (hmult p.val p.property.1)
    have hS_sub : S ⊆ F.toFinset := Finset.filter_subset _ _
    exact ⟨hS_nonempty, hS_sub⟩

  have h_tfine_le_rep : ∀ (p : E₂),
      4 * t (functionsNearPoint F δ_base (p : ℝ × ℝ)) ≤ t_rep := by
    intro p
    let S := functionsNearPoint F δ_base (p : ℝ × ℝ)
    have hP : P S := h_normal_all p
    have h_label : label S = b := p.property.2
    have h_t_eq : t S = tP S hP := by simp [t, hP]
    let t_fine := 4 * tP S hP
    have h_tfine_bound : t_fine ≤ (2 : ℝ)^N * δ_vert := by
      have h1 : tP S hP ≤ K := (hcertP S hP).t_le_diameter
      have h2 : t_fine ≤ 4 * K := by linarith
      linarith [hN_scale']
    have h_i_eq : i = dyadicIdx t_fine h_tfine_bound := by
      have h1 : (label S).1 = i := by
        have h2 : label S = b := p.property.2
        rw [h2] <;> rfl
      have h3 : (label S).1 = dyadicIdx t_fine h_tfine_bound := by
        unfold label
        rw [dif_pos hP] <;> rfl
      exact h1.symm.trans h3
    have h4 : t_fine ≤ t_bin := by
      rw [show t_bin = (2 : ℝ)^(i.val + 1) * δ_vert from rfl, h_i_eq]
      exact h_dyadicIdx_spec t_fine h_tfine_bound
    have h5 : 4 * t S = t_fine := by
      rw [h_t_eq] <;> ring
    rw [h5]
    exact h4.trans (le_max_left t_bin D_rep)

  have h_Delta_le_rep : ∀ (p : E₂),
      Delta (functionsNearPoint F δ_base (p : ℝ × ℝ)) ≤ D_rep := by
    intro p
    let S := functionsNearPoint F δ_base (p : ℝ × ℝ)
    have hP : P S := h_normal_all p
    have h_label : label S = b := p.property.2
    have h_Delta_eq : Delta S = DeltaP S hP := by simp [Delta, hP]
    let Delta_val := DeltaP S hP
    have h_Delta_bound : Delta_val ≤ (2 : ℝ)^N * δ_vert := by
      have h_t_le_K : tP S hP ≤ K := (hcertP S hP).t_le_diameter
      have h1 : Delta_val ≤ 4 * tP S hP := (hcertP S hP).Delta_le_four_t
      have h2 : Delta_val ≤ 4 * K := by linarith
      linarith [hN_scale']
    have h_j_eq : j = dyadicIdx Delta_val h_Delta_bound := by
      have h1 : (label S).2 = j := by
        have h2 : label S = b := p.property.2
        rw [h2] <;> rfl
      have h3 : (label S).2 = dyadicIdx Delta_val h_Delta_bound := by
        unfold label
        rw [dif_pos hP] <;> rfl
      exact h1.symm.trans h3
    have h4 : Delta_val ≤ D_rep := by
      rw [show D_rep = (2 : ℝ)^(j.val + 1) * δ_vert from rfl, h_j_eq]
      exact h_dyadicIdx_spec Delta_val h_Delta_bound
    rw [h_Delta_eq]
    exact h4

  have h_tbin_le_eight_exact : ∀ (p : E₂),
      t_bin ≤ 8 * t (functionsNearPoint F δ_base (p : ℝ × ℝ)) := by
    intro p
    let S := functionsNearPoint F δ_base (p : ℝ × ℝ)
    have hP : P S := h_normal_all p
    have h_t_eq : t S = tP S hP := by simp [t, hP]
    let t_fine := 4 * tP S hP
    have h_tfine_bound : t_fine ≤ (2 : ℝ)^N * δ_vert := by
      have h1 : tP S hP ≤ K := (hcertP S hP).t_le_diameter
      have h2 : t_fine ≤ 4 * K := by linarith
      linarith [hN_scale']
    have h_i_eq : i = dyadicIdx t_fine h_tfine_bound := by
      have h1 : (label S).1 = i := by
        rw [p.property.2] <;> rfl
      have h2 :
          (label S).1 = dyadicIdx t_fine h_tfine_bound := by
        unfold label
        rw [dif_pos hP] <;> rfl
      exact h1.symm.trans h2
    have hdelta_le_tfine : δ_vert ≤ t_fine := by
      have hdelta_t := (hcertP S hP).delta_le_t
      dsimp only [t_fine]
      linarith
    have hrep :
        (2 : ℝ)^((dyadicIdx t_fine h_tfine_bound).val + 1) *
            δ_vert ≤
          2 * t_fine :=
      dyadic_upper_representative hδ_vert_pos hdelta_le_tfine
        (dyadicIdx t_fine h_tfine_bound).isLt
        (h_dyadicIdx_spec t_fine h_tfine_bound)
        (h_dyadicIdx_minimal t_fine h_tfine_bound)
    rw [← h_i_eq] at hrep
    have htbin :
        t_bin ≤ 2 * t_fine := by
      simpa [t_bin] using hrep
    rw [h_t_eq]
    dsimp only [t_fine] at htbin
    linarith

  have h_Drep_le_two_exact : ∀ (p : E₂),
      D_rep ≤
        2 * Delta (functionsNearPoint F δ_base (p : ℝ × ℝ)) := by
    intro p
    let S := functionsNearPoint F δ_base (p : ℝ × ℝ)
    have hP : P S := h_normal_all p
    have h_Delta_eq : Delta S = DeltaP S hP := by simp [Delta, hP]
    let Delta_val := DeltaP S hP
    have h_Delta_bound : Delta_val ≤ (2 : ℝ)^N * δ_vert := by
      have h_t_le_K : tP S hP ≤ K := (hcertP S hP).t_le_diameter
      have h1 : Delta_val ≤ 4 * tP S hP :=
        (hcertP S hP).Delta_le_four_t
      have h2 : Delta_val ≤ 4 * K := by linarith
      linarith [hN_scale']
    have h_j_eq : j = dyadicIdx Delta_val h_Delta_bound := by
      have h1 : (label S).2 = j := by
        rw [p.property.2] <;> rfl
      have h2 :
          (label S).2 = dyadicIdx Delta_val h_Delta_bound := by
        unfold label
        rw [dif_pos hP] <;> rfl
      exact h1.symm.trans h2
    have hdelta_le_Delta : δ_vert ≤ Delta_val :=
      (hcertP S hP).delta_le_Delta
    have hrep :
        (2 : ℝ)^((dyadicIdx Delta_val h_Delta_bound).val + 1) *
            δ_vert ≤
          2 * Delta_val :=
      dyadic_upper_representative hδ_vert_pos hdelta_le_Delta
        (dyadicIdx Delta_val h_Delta_bound).isLt
        (h_dyadicIdx_spec Delta_val h_Delta_bound)
        (h_dyadicIdx_minimal Delta_val h_Delta_bound)
    rw [← h_j_eq] at hrep
    rw [h_Delta_eq]
    simpa [D_rep, Delta_val] using hrep

  have h_trep_le_eight_exact : ∀ (p : E₂),
      t_rep ≤ 8 * t (functionsNearPoint F δ_base (p : ℝ × ℝ)) := by
    intro p
    have htbin := h_tbin_le_eight_exact p
    have hDrep := h_Drep_le_two_exact p
    let S := functionsNearPoint F δ_base (p : ℝ × ℝ)
    have hP : P S := h_normal_all p
    have hDelta_four :
        Delta S ≤ 4 * t S := by
      have hD : Delta S = DeltaP S hP := by simp [Delta, hP]
      have ht' : t S = tP S hP := by simp [t, hP]
      rw [hD, ht']
      exact (hcertP S hP).Delta_le_four_t
    dsimp only [t_rep]
    exact max_le htbin (by linarith)

  let point (p : E₂) : UnitPoint × ℝ :=
    let p' := (p : ℝ × ℝ)
    have h1 : p'.1 ∈ unitInterval := (hE₀_sub p.property.1).1.1
    (⟨p'.1, h1⟩, p'.2)

  have hpoint_coe : ∀ (p : E₂),
      (((point p).1 : ℝ), (point p).2) = (p : ℝ × ℝ) := by
    intro p
    rfl

  have hS_sub_F : ∀ (q : ℝ × ℝ),
      (finsetToFFF (functionsNearPoint F δ_base q)).carrier ⊆ F.carrier := by
    intro q f hf
    have h1 : f ∈ functionsNearPoint F δ_base q := by
      simpa [finsetToFFF] using hf
    have h2 : f ∈ F.toFinset := (Finset.filter_subset _ _) h1
    simpa [FiniteFunctionFamily.toFinset] using h2

  let exactScale (p : E₂) : ℝ :=
    let S := functionsNearPoint F δ_base (p : ℝ × ℝ)
    C_R * (4 * t S) * (Delta S) / δ_vert

  have h_common_pos : 0 < C_R * t_rep * D_rep / δ_vert := by positivity

  have h_per_point : ∀ (p : E₂),
      ∃ (R : CurvilinearRectangle δ_vert (exactScale p)),
        R.function = k (functionsNearPoint F δ_base (p : ℝ × ℝ)) ∧
        R.interval.midpoint = (p : ℝ × ℝ).1 ∧
        point p ∈ R.carrier ∧
        R.IsOverCentralQuarterOf I ∧
        ∀ f ∈ (H (functionsNearPoint F δ_base (p : ℝ × ℝ))).carrier,
          R.IsLambdaTangent f 5 := by
    intro p
    let S := functionsNearPoint F δ_base (p : ℝ × ℝ)
    have hP : P S := h_normal_all p
    let t_metric := tP S hP
    let t_fine := 4 * t S
    let Delta_val := Delta S
    let k_val := kP S hP
    let G_val := GP S hP
    let H_val := HP S hP
    let hcert := hcertP S hP
    have h_t_eq : t S = t_metric := by
      unfold t
      rw [dif_pos hP]
    have h_Delta_eq : Delta S = Delta_val := by rfl
    have h_tfine_eq : t_fine = 4 * t S := by
      simp [t_fine, t] <;> ring
    have hδ_vert_le_t : δ_vert ≤ t S := by
      rw [h_t_eq]
      exact hcert.delta_le_t
    have hδ_vert_le_Delta : δ_vert ≤ Delta_val := by
      have h : δ_vert ≤ DeltaP S hP := hcert.delta_le_Delta
      have h2 : Delta_val = DeltaP S hP := by
        unfold Delta_val Delta
        rw [dif_pos hP]
      rw [h2]
      exact h
    have hDelta_le_tfine : Delta_val ≤ t_fine := by
      have h : DeltaP S hP ≤ 4 * t_metric := hcert.Delta_le_four_t
      have h2 : Delta_val = DeltaP S hP := by
        unfold Delta_val Delta
        rw [dif_pos hP]
      have h3 : t_fine = 4 * t S := by simp [t_fine]
      have h4 : t S = t_metric := by
        have h5 : t S = tP S hP := by
          unfold t
          rw [dif_pos hP]
        exact h5.trans rfl
      linarith
    have h_tfine_pos : 0 < t_fine := by
      have h5 : δ_vert ≤ t S := by
        rw [h_t_eq]
        exact hcert.delta_le_t
      have h6 : 0 < δ_vert := hδ_vert_pos
      have h7 : t_fine = 4 * t S := by simp [t_fine]
      linarith
    have hDelta_pos : 0 < Delta_val := by
      have h5 : δ_vert ≤ DeltaP S hP := hcert.delta_le_Delta
      have h6 : 0 < δ_vert := hδ_vert_pos
      have h7 : Delta_val = DeltaP S hP := by
        unfold Delta_val Delta
        rw [dif_pos hP]
      rw [h7]
      linarith

    let p_up : UnitPoint × ℝ := point p
    have hp_centered : p_up.1 ∈ I.centeredCarrier (1 / 8) := by
      have h1 : (p_up.1 : ℝ) ∈ I.realCenteredCarrier (1 / 16) :=
        (hE₀_sub p.property.1).1
      have h2 : |(p_up.1 : ℝ) - I.midpoint| ≤
          (1 / 16 : ℝ) * I.length / 2 := h1.2
      simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq]
      have h3 : (1 / 16 : ℝ) * I.length / 2 ≤
          (1 / 8 : ℝ) * I.length / 2 := by
        gcongr <;> norm_num <;> exact I.length_nonneg
      linarith

    have hk_in_G : k_val ∈ G_val.carrier := hcert.tangencyCenter_mem
    have hk_in_source : k_val ∈ (finsetToFFF S).carrier :=
      (hcert.metric_subset hk_in_G).1
    have hk_in_family : k_val ∈ family :=
      hF (hS_sub_F (p : ℝ × ℝ) hk_in_source)
    have hk_in_S : k_val ∈ S := by exact_mod_cast hk_in_source
    have hk_graph : (p : ℝ × ℝ) ∈ graphNeighborhood k_val δ_base :=
      (Finset.mem_filter.mp hk_in_S).2
    have hk_vert : |p_up.2 - k_val p_up.1| ≤ δ_vert := by
      exact localAssembly_graphNeighborhood_to_vertical
        (fun z => hbounds k_val hk_in_family z) p_up.1.property hk_graph

    have hH_sub_family : H_val.carrier ⊆ family := by
      intro f hf
      have h1 : f ∈ G_val.carrier := by
        rw [hcert.tangencyFiber_eq] at hf
        exact hf.1
      have h2 : f ∈ (finsetToFFF S).carrier := (hcert.metric_subset h1).1
      exact hF (hS_sub_F (p : ℝ × ℝ) h2)

    have hH_bounds : ∀ f ∈ H_val.carrier,
        c2Distance f k_val ≤ 6 * t_fine ∧
        tangencyParameterOn I f k_val ≤ Delta_val ∧
        |p_up.2 - f p_up.1| ≤ δ_vert := by
      intro f hf
      have hf_in_G : f ∈ G_val.carrier := by
        rw [hcert.tangencyFiber_eq] at hf
        exact hf.1
      have hf_in_source : f ∈ (finsetToFFF S).carrier :=
        (hcert.metric_subset hf_in_G).1
      have hf_in_S : f ∈ S := by exact_mod_cast hf_in_source
      have hf_in_family : f ∈ family :=
        hF (hS_sub_F (p : ℝ × ℝ) hf_in_source)
      have hf_graph : (p : ℝ × ℝ) ∈ graphNeighborhood f δ_base :=
        (Finset.mem_filter.mp hf_in_S).2
      have hf_ball : f ∈ c2Ball (centerP S hP) t_metric :=
        (hcert.metric_subset hf_in_G).2
      have hk_ball : k_val ∈ c2Ball (centerP S hP) t_metric :=
        (hcert.metric_subset hk_in_G).2
      have hdist : c2Distance f k_val ≤ 2 * t_metric :=
        localAssembly_dist_le_two_mul_of_mem_ball hf_ball hk_ball
      have hdist6 : c2Distance f k_val ≤ 6 * t_fine := by linarith
      have htang : tangencyParameterOn I f k_val ≤ Delta_val := by
        have hf' : f ∈ H_val.carrier := hf
        rw [hcert.tangencyFiber_eq] at hf'
        have h_set : f ∈
            {f | tangencyParameterOn I f (kP S hP) ≤ DeltaP S hP} := hf'.2
        have h_prop : tangencyParameterOn I f (kP S hP) ≤ DeltaP S hP := by
          simpa using h_set
        have hkv : k_val = kP S hP := by rfl
        have hDv : Delta_val = DeltaP S hP := by
          unfold Delta_val Delta
          rw [dif_pos hP]
        rw [hkv, hDv]
        exact h_prop
      have hvert : |p_up.2 - f p_up.1| ≤ δ_vert := by
        exact localAssembly_graphNeighborhood_to_vertical
          (fun z => hbounds f hf_in_family z) p_up.1.property hf_graph
      exact ⟨hdist6, htang, hvert⟩

    rcases hFine_main family hfamily I hI
        δ_vert t_fine Delta_val
        hδ_vert_pos hδ_vert_le_Delta hDelta_le_tfine
        p_up hp_centered
        k_val hk_in_family hk_vert
        H_val hH_sub_family hH_bounds
      with ⟨R_orig, hR_func, hR_mid, hR_p, hR_over, hR_tangent⟩

    have h_k_eq : k_val = k S := by simp [k, hP] <;> rfl
    have h_H_eq : H_val = H S := by simp [H, hP] <;> rfl
    have h_exactScale_eq :
        exactScale p = C_R * t_fine * Delta_val / δ_vert := by
      simp [exactScale, t_fine, Delta_val] <;> ring

    have hR_tangent' : ∀ f ∈ (H S).carrier,
        R_orig.IsLambdaTangent f 5 := by
      rw [← h_H_eq]
      exact hR_tangent

    have h_main : ∃ (R : CurvilinearRectangle δ_vert (exactScale p)),
        R.function = k S ∧
        R.interval.midpoint = (p : ℝ × ℝ).1 ∧
        point p ∈ R.carrier ∧
        R.IsOverCentralQuarterOf I ∧
        ∀ f ∈ (H S).carrier, R.IsLambdaTangent f 5 := by
      rw [h_exactScale_eq]
      exact ⟨R_orig,
        by rw [hR_func, h_k_eq],
        hR_mid, hR_p, hR_over, hR_tangent'⟩
    exact h_main

  choose rectangle hrect using h_per_point

  have hrect_func : ∀ (p : E₂),
      (rectangle p).function =
        k (functionsNearPoint F δ_base (p : ℝ × ℝ)) :=
    fun p => (hrect p).1
  have hrect_mid : ∀ (p : E₂),
      (rectangle p).interval.midpoint = (p : ℝ × ℝ).1 :=
    fun p => (hrect p).2.1
  have hrect_p : ∀ (p : E₂), point p ∈ (rectangle p).carrier :=
    fun p => (hrect p).2.2.1
  have hrect_over : ∀ (p : E₂),
      (rectangle p).IsOverCentralQuarterOf I :=
    fun p => (hrect p).2.2.2.1
  have hrect_tangent : ∀ (p : E₂),
      ∀ f ∈ (H (functionsNearPoint F δ_base (p : ℝ × ℝ))).carrier,
      (rectangle p).IsLambdaTangent f 5 :=
    fun p => (hrect p).2.2.2.2

  have hrect_central : ∀ (p : E₂),
      |(rectangle p).interval.midpoint - I.midpoint| ≤ I.length / 16 := by
    intro p
    have h1 : (rectangle p).interval.midpoint = (p : ℝ × ℝ).1 :=
      hrect_mid p
    rw [h1]
    have h2 : (p : ℝ × ℝ).1 ∈ I.realCenteredCarrier (1 / 16) :=
      (hE₀_sub p.property.1).1
    have h3 : |(p : ℝ × ℝ).1 - I.midpoint| ≤
        (1 / 16 : ℝ) * I.length / 2 := h2.2
    have h4 : (1 / 16 : ℝ) * I.length / 2 ≤ I.length / 16 := by
      ring_nf
      linarith [I.length_nonneg]
    linarith

  have hexact_pos : ∀ (p : E₂), 0 < exactScale p := by
    intro p
    let S := functionsNearPoint F δ_base (p : ℝ × ℝ)
    have hP : P S := h_normal_all p
    have h_t_pos : 0 < t S := by
      have h_eq : t S = tP S hP := by simp [t, hP]
      rw [h_eq]
      have h2 : δ_vert ≤ tP S hP := (hcertP S hP).delta_le_t
      linarith
    have h_Delta_pos : 0 < Delta S := by
      have h_eq : Delta S = DeltaP S hP := by simp [Delta, hP]
      rw [h_eq]
      have h2 : δ_vert ≤ DeltaP S hP :=
        (hcertP S hP).delta_le_Delta
      linarith
    simp [exactScale]
    positivity

  have hexact_le : ∀ (p : E₂),
      exactScale p ≤ C_R * t_rep * D_rep / δ_vert := by
    intro p
    let S := functionsNearPoint F δ_base (p : ℝ × ℝ)
    have hP : P S := h_normal_all p
    set t_fine : ℝ := 4 * t S with ht_fine_def
    set Delta_val : ℝ := Delta S with hDelta_val_def
    have h_t_pos : 0 < t_fine := by
      have h_eq : t S = tP S hP := by simp [t, hP]
      rw [ht_fine_def, h_eq]
      have h2 : δ_vert ≤ tP S hP := (hcertP S hP).delta_le_t
      linarith
    have h_Delta_pos : 0 < Delta_val := by
      have h_eq : Delta S = DeltaP S hP := by simp [Delta, hP]
      rw [hDelta_val_def, h_eq]
      have h2 : δ_vert ≤ DeltaP S hP :=
        (hcertP S hP).delta_le_Delta
      linarith
    have h1 : t_fine ≤ t_rep := h_tfine_le_rep p
    have h2 : Delta_val ≤ D_rep := h_Delta_le_rep p
    have h_exactScale_eq :
        exactScale p = C_R * t_fine * Delta_val / δ_vert := by
      simp [exactScale, t_fine, Delta_val] <;> ring
    rw [h_exactScale_eq]
    have h3 : C_R * t_fine * Delta_val / δ_vert ≤
        C_R * t_rep * D_rep / δ_vert := by
      apply div_le_div_of_nonneg_right
      · gcongr <;> linarith
      · positivity
    exact h3

  let centerFn (p : E₂) : C2Function :=
    k (functionsNearPoint F δ_base (p : ℝ × ℝ))
  let fiberFn (p : E₂) : FiniteFunctionFamily :=
    H (functionsNearPoint F δ_base (p : ℝ × ℝ))

  have hcenter_mem : ∀ (p : E₂), centerFn p ∈ family := by
    intro p
    let S := functionsNearPoint F δ_base (p : ℝ × ℝ)
    have hP : P S := h_normal_all p
    have h_k_eq : k S = kP S hP := by simp [k, hP] <;> rfl
    have hk_in_G : kP S hP ∈ (GP S hP).carrier :=
      (hcertP S hP).tangencyCenter_mem
    have hk_in_source : k S ∈ (finsetToFFF S).carrier := by
      have h : kP S hP ∈ (finsetToFFF S).carrier :=
        ((hcertP S hP).metric_subset hk_in_G).1
      rw [h_k_eq]
      exact h
    have hk_in_F : k S ∈ F.carrier :=
      hS_sub_F (p : ℝ × ℝ) hk_in_source
    exact hF hk_in_F

  have hfiber_subset : ∀ (p : E₂), (fiberFn p).carrier ⊆ family := by
    intro p
    let S := functionsNearPoint F δ_base (p : ℝ × ℝ)
    have hP : P S := h_normal_all p
    have h_H_eq : (H S).carrier = (HP S hP).carrier := by
      simp [H, hP] <;> rfl
    have hH_sub : (H S).carrier ⊆ family := by
      intro f hf
      have hf' : f ∈ (HP S hP).carrier := by
        rw [← h_H_eq]
        exact hf
      have h1 : f ∈ (GP S hP).carrier := by
        rw [(hcertP S hP).tangencyFiber_eq] at hf'
        exact hf'.1
      have h2 : f ∈ (finsetToFFF S).carrier :=
        ((hcertP S hP).metric_subset h1).1
      have h3 : f ∈ F.carrier := hS_sub_F (p : ℝ × ℝ) h2
      exact hF h3
    exact hH_sub

  rcases pointwise_rectangle_shortening rectangle_shortening
      (I := I) hI
      point hpoint_coe
      centerFn hcenter_mem
      fiberFn hfiber_subset
      exactScale
      hδ_vert_pos h_common_pos
      hexact_pos hexact_le
      rectangle
      hrect_func hrect_mid hrect_central hrect_p hrect_over hrect_tangent
    with ⟨data, hdata_I, hdata_center, hdata_fiber⟩

  have h_cert : ∀ (p : E₂),
      TwoEndsCertificate I δ_vert K epsilon eta
        (t (functionsNearPoint F δ_base (p : ℝ × ℝ)))
        (Delta (functionsNearPoint F δ_base (p : ℝ × ℝ)))
        (finsetToFFF (functionsNearPoint F δ_base (p : ℝ × ℝ)))
        (G (functionsNearPoint F δ_base (p : ℝ × ℝ)))
        (H (functionsNearPoint F δ_base (p : ℝ × ℝ)))
        (center (functionsNearPoint F δ_base (p : ℝ × ℝ)))
        (k (functionsNearPoint F δ_base (p : ℝ × ℝ))) := by
    intro p
    let S := functionsNearPoint F δ_base (p : ℝ × ℝ)
    have hP : P S := h_normal_all p
    have h_t_eq : t S = tP S hP := by simp [t, hP]
    have h_Delta_eq : Delta S = DeltaP S hP := by simp [Delta, hP]
    have h_center_eq : center S = centerP S hP := by simp [center, hP]
    have h_k_eq : k S = kP S hP := by simp [k, hP]
    have h_G_eq : G S = GP S hP := by simp [G, hP]
    have h_H_eq : H S = HP S hP := by simp [H, hP]
    rw [h_t_eq, h_Delta_eq, h_center_eq, h_k_eq, h_G_eq, h_H_eq]
    exact hcertP S hP

  let dyadicData : DyadicFineAssignmentData
      family E₂ K δ_vert K epsilon eta t_rep D_rep C_R :=
    { interval := I
      assignment := data
      assignment_interval := hdata_I
      exactT := fun p => t (functionsNearPoint F δ_base (p : ℝ × ℝ))
      exactDelta := fun p => Delta (functionsNearPoint F δ_base (p : ℝ × ℝ))
      ambientSource := F
      ambientSource_subset := hF
      separationScale := separationScale
      separationScale_pos := hseparationScale_pos
      ambientSource_separated := hF_separated
      source := fun p => finsetToFFF (functionsNearPoint F δ_base (p : ℝ × ℝ))
      source_subset_ambient := by
        intro p
        exact hS_sub_F p
      metricFiber := fun p => G (functionsNearPoint F δ_base (p : ℝ × ℝ))
      tangencyFiber := fun p => H (functionsNearPoint F δ_base (p : ℝ × ℝ))
      metricCenter := fun p => center (functionsNearPoint F δ_base (p : ℝ × ℝ))
      tangencyCenter := fun p => k (functionsNearPoint F δ_base (p : ℝ × ℝ))
      tangencyCenter_ball_measurable := by
        intro center₀ radius
        have hlabel :
            MeasurableSet
              {q : ℝ × ℝ |
                k (functionsNearPoint F δ_base q) ∈
                  c2Ball center₀ radius} :=
          measurableSet_functionsNearPoint_label_mem
            F δ_base k (c2Ball center₀ radius)
        have hset :
            {q : ℝ × ℝ | ∃ hq : q ∈ E₂,
                k (functionsNearPoint F δ_base
                  ((⟨q, hq⟩ : E₂) : ℝ × ℝ)) ∈
                    c2Ball center₀ radius} =
              E₂ ∩
                {q : ℝ × ℝ |
                  k (functionsNearPoint F δ_base q) ∈
                    c2Ball center₀ radius} := by
          ext q
          constructor
          · rintro ⟨hq, hmem⟩
            exact ⟨hq, by simpa using hmem⟩
          · rintro ⟨hq, hmem⟩
            exact ⟨hq, by simpa using hmem⟩
        rw [hset]
        exact hE2_meas.inter hlabel
      epsilon_pos := hepsilon
      eta_pos := heta
      mu := μ
      mu_pos := hmu
      mu_le_source := by
        intro p
        let S := functionsNearPoint F δ_base (p : ℝ × ℝ)
        have hreal : (μ : ℝ) ≤ (S.card : ℝ) := by
          rw [functionsNearPoint_card_eq_multiplicity]
          exact hmult p p.property.1
        have hcard : (finsetToFFF S).card = S.card := by
          simp [FiniteFunctionFamily.card, finsetToFFF]
        rw [hcard]
        exact_mod_cast hreal
      certificate := h_cert
      delta_le_DeltaRep := hdelta_le_D_rep
      DeltaRep_le_tRep := hD_rep_le_t_rep
      tRep_pos := ht_rep_pos
      four_exactT_le_rep := h_tfine_le_rep
      exactDelta_le_rep := h_Delta_le_rep
      rep_le_eight_exactT := h_trep_le_eight_exact
      repDelta_le_two_exactDelta := h_Drep_le_two_exact
      assignment_center := hdata_center
      assignment_fiber := hdata_fiber }

  exact ⟨E₂, t_rep, D_rep, dyadicData,
    rfl, rfl, fun _ => rfl, hE2_meas, hE2_sub, h_retention⟩

lemma dyadic_fine_assignment_at_fixed_constant_with_ambient_source
    (hTwoEnds : TwoEndsSelectionStatement)
    (hTangencyTwoEnds : TangencyTwoEndsSelectionStatement)
    {K D : ℝ} (hK : 1 ≤ K) (hD : 1 ≤ D)
    (C_R : ℝ) (hC_R_large : 9216 * K^2 ≤ C_R)
    (hFine_main : PointwiseFineRectangleAssigner K D C_R)
    {family : Set C2Function} (hfamily : IsCinematicFamily family K D)
    {F : FiniteFunctionFamily} (hF : F.carrier ⊆ family)
    {I : ParameterInterval} (hI : I.IsControlled K)
    {δ_base : ℝ} (hδ_base_pos : 0 < δ_base)
    {separationScale : ℝ} (hseparationScale_pos : 0 < separationScale)
    (hF_separated : F.IsDeltaSeparated separationScale)
    {μ : ℕ} (hmu : 0 < μ)
    (L : ℝ) (hL_nonneg : 0 ≤ L)
    (hbounds : ∀ f ∈ family, ∀ z : UnitPoint, |f.firstDeriv z| ≤ L)
    (hδ_vert_le_K : (1 + L) * δ_base ≤ K)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (eta : ℝ) (heta : 0 < eta)
    {c : ℝ}
    {E₀ : Set (ℝ × ℝ)}
    (hE₀_meas : MeasurableSet E₀)
    (hE₀_nonempty : E₀.Nonempty)
    (hE₀_sub : E₀ ⊆ I.realCenteredCarrier (1 / 16) ×ˢ Set.Icc c (c + 1))
    (hmult : ∀ p ∈ E₀, (μ : ℝ) ≤ multiplicity F δ_base p)
    (logLoss : ℝ) (hlogLoss : 1 ≤ logLoss)
    (N : ℕ) (hN2 : 2 ≤ N)
    (hN_scale : (2 : ℝ)^N * (1 + L) * δ_base ≥ 4 * K)
    (hN_card : (N * N : ℝ) ≤ logLoss) :
    ∃ (E₂ : Set (ℝ × ℝ)) (t_rep Delta_rep : ℝ)
      (data : DyadicFineAssignmentData
        family E₂ K ((1 + L) * δ_base) K epsilon eta t_rep Delta_rep C_R),
      data.mu = μ ∧
      data.ambientSource = F ∧
      MeasurableSet E₂ ∧ E₂ ⊆ E₀ ∧
      volume E₀ ≤ ENNReal.ofReal logLoss * volume E₂ := by
  rcases dyadic_fine_assignment_at_fixed_constant_core
      hTwoEnds hTangencyTwoEnds hK hD C_R hC_R_large hFine_main
      hfamily hF hI hδ_base_pos hseparationScale_pos hF_separated
      hmu L hL_nonneg hbounds hδ_vert_le_K epsilon hepsilon eta heta
      hE₀_meas hE₀_nonempty hE₀_sub hmult logLoss hlogLoss N hN2
      hN_scale hN_card with
    ⟨E₂, t_rep, Delta_rep, data, hmu_data, hambientSource, _,
      hE₂_meas, hE₂_sub, hretention⟩
  exact
    ⟨E₂, t_rep, Delta_rep, data, hmu_data, hambientSource,
      hE₂_meas, hE₂_sub, hretention⟩

lemma dyadic_fine_assignment_at_fixed_constant_with_level_bounds
    (hTwoEnds : TwoEndsSelectionStatement)
    (hTangencyTwoEnds : TangencyTwoEndsSelectionStatement)
    {K D : ℝ} (hK : 1 ≤ K) (hD : 1 ≤ D)
    (C_R : ℝ) (hC_R_large : 9216 * K^2 ≤ C_R)
    (hFine_main : PointwiseFineRectangleAssigner K D C_R)
    {family : Set C2Function} (hfamily : IsCinematicFamily family K D)
    {F : FiniteFunctionFamily} (hF : F.carrier ⊆ family)
    {I : ParameterInterval} (hI : I.IsControlled K)
    {δ_base : ℝ} (hδ_base_pos : 0 < δ_base)
    {separationScale : ℝ} (hseparationScale_pos : 0 < separationScale)
    (hF_separated : F.IsDeltaSeparated separationScale)
    {μ : ℕ} (hmu : 0 < μ)
    (L : ℝ) (hL_nonneg : 0 ≤ L)
    (hbounds : ∀ f ∈ family, ∀ z : UnitPoint, |f.firstDeriv z| ≤ L)
    (hδ_vert_le_K : (1 + L) * δ_base ≤ K)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (eta : ℝ) (heta : 0 < eta)
    {c : ℝ}
    {E₀ : Set (ℝ × ℝ)}
    (hE₀_meas : MeasurableSet E₀)
    (hE₀_nonempty : E₀.Nonempty)
    (hE₀_sub : E₀ ⊆ I.realCenteredCarrier (1 / 16) ×ˢ Set.Icc c (c + 1))
    (hmult : ∀ p ∈ E₀,
      (μ : ℝ) ≤ multiplicity F δ_base p ∧
        multiplicity F δ_base p < 2 * μ)
    (logLoss : ℝ) (hlogLoss : 1 ≤ logLoss)
    (N : ℕ) (hN2 : 2 ≤ N)
    (hN_scale : (2 : ℝ)^N * (1 + L) * δ_base ≥ 4 * K)
    (hN_card : (N * N : ℝ) ≤ logLoss) :
    ∃ (E₂ : Set (ℝ × ℝ)) (t_rep Delta_rep : ℝ)
      (data : DyadicFineAssignmentData
        family E₂ K ((1 + L) * δ_base) K epsilon eta t_rep Delta_rep C_R),
      data.mu = μ ∧
      data.ambientSource = F ∧
      (∀ p : E₂, ((data.source p).card : ℝ) < 2 * μ) ∧
      (∀ p : E₂,
        ((data.assignment.fiber p).card : ℝ) < 2 * μ) ∧
      MeasurableSet E₂ ∧ E₂ ⊆ E₀ ∧
      volume E₀ ≤ ENNReal.ofReal logLoss * volume E₂ := by
  rcases dyadic_fine_assignment_at_fixed_constant_core
      hTwoEnds hTangencyTwoEnds hK hD C_R hC_R_large hFine_main
      hfamily hF hI hδ_base_pos hseparationScale_pos hF_separated
      hmu L hL_nonneg hbounds hδ_vert_le_K epsilon hepsilon eta heta
      hE₀_meas hE₀_nonempty hE₀_sub
      (fun p hp => (hmult p hp).1)
      logLoss hlogLoss N hN2 hN_scale hN_card with
    ⟨E₂, t_rep, Delta_rep, data, hmu_data, hambientSource,
      hsource, hE₂_meas, hE₂_sub, hretention⟩
  have hsourceUpper :
      ∀ p : E₂, ((data.source p).card : ℝ) < 2 * μ := by
    intro p
    rw [hsource p]
    have hcard :
        (finsetToFFF
          (functionsNearPoint F δ_base (p : ℝ × ℝ))).card =
            (functionsNearPoint F δ_base
              (p : ℝ × ℝ)).card := by
      simp [FiniteFunctionFamily.card, finsetToFFF]
    rw [hcard, functionsNearPoint_card_eq_multiplicity]
    exact
      (hmult (p : ℝ × ℝ)
        (hE₂_sub p.property)).2
  have hfiberUpper :
      ∀ p : E₂,
        ((data.assignment.fiber p).card : ℝ) < 2 * μ := by
    intro p
    exact (data.fiber_card_cast_le_source p).trans_lt
      (hsourceUpper p)
  exact
    ⟨E₂, t_rep, Delta_rep, data, hmu_data, hambientSource,
      hsourceUpper, hfiberUpper, hE₂_meas, hE₂_sub, hretention⟩

lemma dyadic_fine_assignment_at_fixed_constant
    (hTwoEnds : TwoEndsSelectionStatement)
    (hTangencyTwoEnds : TangencyTwoEndsSelectionStatement)
    {K D : ℝ} (hK : 1 ≤ K) (hD : 1 ≤ D)
    (C_R : ℝ) (hC_R_large : 9216 * K^2 ≤ C_R)
    (hFine_main : PointwiseFineRectangleAssigner K D C_R)
    {family : Set C2Function} (hfamily : IsCinematicFamily family K D)
    {F : FiniteFunctionFamily} (hF : F.carrier ⊆ family)
    {I : ParameterInterval} (hI : I.IsControlled K)
    {δ_base : ℝ} (hδ_base_pos : 0 < δ_base)
    {separationScale : ℝ} (hseparationScale_pos : 0 < separationScale)
    (hF_separated : F.IsDeltaSeparated separationScale)
    {μ : ℕ} (hmu : 0 < μ)
    (L : ℝ) (hL_nonneg : 0 ≤ L)
    (hbounds : ∀ f ∈ family, ∀ z : UnitPoint, |f.firstDeriv z| ≤ L)
    (hδ_vert_le_K : (1 + L) * δ_base ≤ K)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (eta : ℝ) (heta : 0 < eta)
    {c : ℝ}
    {E₀ : Set (ℝ × ℝ)}
    (hE₀_meas : MeasurableSet E₀)
    (hE₀_nonempty : E₀.Nonempty)
    (hE₀_sub : E₀ ⊆ I.realCenteredCarrier (1 / 16) ×ˢ Set.Icc c (c + 1))
    (hmult : ∀ p ∈ E₀, (μ : ℝ) ≤ multiplicity F δ_base p)
    (logLoss : ℝ) (hlogLoss : 1 ≤ logLoss)
    (N : ℕ) (hN2 : 2 ≤ N)
    (hN_scale : (2 : ℝ)^N * (1 + L) * δ_base ≥ 4 * K)
    (hN_card : (N * N : ℝ) ≤ logLoss) :
    ∃ (E₂ : Set (ℝ × ℝ)) (t_rep Delta_rep : ℝ)
      (data : DyadicFineAssignmentData
        family E₂ K ((1 + L) * δ_base) K epsilon eta t_rep Delta_rep C_R),
      data.mu = μ ∧
      MeasurableSet E₂ ∧ E₂ ⊆ E₀ ∧
      volume E₀ ≤ ENNReal.ofReal logLoss * volume E₂ := by
  rcases dyadic_fine_assignment_at_fixed_constant_with_ambient_source
      hTwoEnds hTangencyTwoEnds hK hD C_R hC_R_large hFine_main
      hfamily hF hI hδ_base_pos hseparationScale_pos hF_separated
      hmu L hL_nonneg hbounds hδ_vert_le_K epsilon hepsilon eta heta
      hE₀_meas hE₀_nonempty hE₀_sub hmult logLoss hlogLoss N hN2
      hN_scale hN_card with
    ⟨E₂, t_rep, Delta_rep, data, hmu_data, _,
      hE₂_meas, hE₂_sub, hretention⟩
  exact
    ⟨E₂, t_rep, Delta_rep, data,
      hmu_data, hE₂_meas, hE₂_sub, hretention⟩

/--
Compatibility wrapper that chooses the common rectangle constant from the
paper-facing assignment statement.
-/
lemma dyadic_fine_assignment
    (hTwoEnds : TwoEndsSelectionStatement)
    (hTangencyTwoEnds : TangencyTwoEndsSelectionStatement)
    (hFine : FineRectangleAssignmentStatement)
    {K D : ℝ} (hK : 1 ≤ K) (hD : 1 ≤ D)
    {family : Set C2Function} (hfamily : IsCinematicFamily family K D)
    {F : FiniteFunctionFamily} (hF : F.carrier ⊆ family)
    {I : ParameterInterval} (hI : I.IsControlled K)
    {δ_base : ℝ} (hδ_base_pos : 0 < δ_base)
    {separationScale : ℝ} (hseparationScale_pos : 0 < separationScale)
    (hF_separated : F.IsDeltaSeparated separationScale)
    {μ : ℕ} (hmu : 0 < μ)
    (L : ℝ) (hL_nonneg : 0 ≤ L)
    (hbounds : ∀ f ∈ family, ∀ z : UnitPoint, |f.firstDeriv z| ≤ L)
    (hδ_vert_le_K : (1 + L) * δ_base ≤ K)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (eta : ℝ) (heta : 0 < eta)
    {c : ℝ}
    {E₀ : Set (ℝ × ℝ)}
    (hE₀_meas : MeasurableSet E₀)
    (hE₀_nonempty : E₀.Nonempty)
    (hE₀_sub : E₀ ⊆ I.realCenteredCarrier (1 / 16) ×ˢ Set.Icc c (c + 1))
    (hmult : ∀ p ∈ E₀, (μ : ℝ) ≤ multiplicity F δ_base p)
    (logLoss : ℝ) (hlogLoss : 1 ≤ logLoss)
    (N : ℕ) (hN2 : 2 ≤ N)
    (hN_scale : (2 : ℝ)^N * (1 + L) * δ_base ≥ 4 * K)
    (hN_card : (N * N : ℝ) ≤ logLoss) :
    ∃ (E₂ : Set (ℝ × ℝ)) (t_rep Delta_rep C_R : ℝ)
      (data : DyadicFineAssignmentData
        family E₂ K ((1 + L) * δ_base) K epsilon eta t_rep Delta_rep C_R),
      MeasurableSet E₂ ∧ E₂ ⊆ E₀ ∧
      volume E₀ ≤ ENNReal.ofReal logLoss * volume E₂ := by
  rcases hFine K D hK hD with ⟨C_R, hC_R_large, hFine_main⟩
  rcases dyadic_fine_assignment_at_fixed_constant
      hTwoEnds hTangencyTwoEnds hK hD C_R hC_R_large hFine_main
      hfamily hF hI hδ_base_pos hseparationScale_pos hF_separated
      hmu L hL_nonneg hbounds hδ_vert_le_K epsilon hepsilon eta heta
      hE₀_meas hE₀_nonempty hE₀_sub hmult logLoss hlogLoss N hN2
      hN_scale hN_card with
    ⟨E₂, t_rep, Delta_rep, data, _, hE₂_meas, hE₂_sub, hretention⟩
  exact
    ⟨E₂, t_rep, Delta_rep, C_R, data,
      hE₂_meas, hE₂_sub, hretention⟩

end Kakeya.Cinematic
