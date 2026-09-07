import MyLeanRepo.Kakeya.Assouad.PureWZ2.BalancedSelectionPureCWA
import Mathlib.Tactic

/-!
# Degree-uniform pure CWA restriction

This module discretizes the requested scale interval by a geometric schedule,
regularizes parent degrees simultaneously on a pre-selected family, and then
uses the actual nearby-scale witnesses of the ambient pure CWA to transfer
pure CWA to the selected family.
-/

noncomputable section

namespace Kakeya.Assouad

open Finset Classical

attribute [local instance] Classical.propDecidable

/-- Geometric scale `s_k = delta * delta ^ (-epsilon * k)`. -/
def geometricScale (delta epsilon : ℝ) (k : ℕ) : ℝ :=
  delta * Real.rpow delta (-epsilon * (k : ℝ))

/-- Consecutive geometric scales differ by `delta ^ (-epsilon)`. -/
lemma geometricScale_succ
    {delta epsilon : ℝ}
    (hdelta_pos : 0 < delta)
    (k : ℕ) :
    geometricScale delta epsilon (k + 1) =
      geometricScale delta epsilon k * Real.rpow delta (-epsilon) := by
  have h_exp :
      -epsilon * ((k + 1 : ℕ) : ℝ) =
        -epsilon * (k : ℝ) + (-epsilon) := by
    simp [Nat.cast_add, mul_add] <;> ring
  simp only [geometricScale, h_exp]
  have h_add :
      Real.rpow delta (-epsilon * (k : ℝ) + (-epsilon)) =
        Real.rpow delta (-epsilon * (k : ℝ)) *
          Real.rpow delta (-epsilon) :=
    Real.rpow_add hdelta_pos _ _
  rw [h_add]
  ring

/-- Number of geometric scales needed to cover `[delta, 1]`. -/
def geometricScaleCount (epsilon : ℝ) : ℕ :=
  Nat.ceil (1 / epsilon) + 1

/--
Every requested scale is rounded upward to a geometric scale with ratio less
than `delta ^ (-epsilon)`.
-/
lemma geometricScale_rounding
    {delta epsilon : ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_lt_one : delta < 1)
    (hepsilon_pos : 0 < epsilon)
    (rho₀ : ℝ)
    (h1 : delta ≤ rho₀)
    (h2 : rho₀ ≤ 1) :
    ∃ k : ℕ, k < geometricScaleCount epsilon ∧
      rho₀ ≤ geometricScale delta epsilon k ∧
      geometricScale delta epsilon k <
        Real.rpow delta (-epsilon) * rho₀ := by
  let M := geometricScaleCount epsilon
  have hM_def : M = Nat.ceil (1 / epsilon) + 1 := by
    rfl
  have hM1 : M - 1 = Nat.ceil (1 / epsilon) := by
    simp [hM_def] <;> omega
  have h3 : (1 / epsilon : ℝ) ≤ (↑(M - 1) : ℝ) := by
    rw [hM1]
    exact Nat.le_ceil (1 / epsilon)
  have h4 : 1 ≤ geometricScale delta epsilon (M - 1) := by
    have h5 : -epsilon * ((M - 1 : ℕ) : ℝ) ≤ -1 := by
      have h7 : (1 : ℝ) ≤ epsilon * ((M - 1 : ℕ) : ℝ) := by
        calc
          (1 : ℝ) = epsilon * (1 / epsilon) := by
            field_simp [hepsilon_pos.ne'] <;> ring
          _ ≤ epsilon * ((M - 1 : ℕ) : ℝ) := by
            gcongr
      linarith
    have h8 :
        Real.rpow delta (-1 : ℝ) ≤
          Real.rpow delta (-epsilon * ((M - 1 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge
        hdelta_pos hdelta_lt_one.le h5
    have h9 : delta * Real.rpow delta (-1 : ℝ) = 1 := by
      have h10 : Real.rpow delta (-1 : ℝ) = delta⁻¹ := by
        simpa using Real.rpow_neg_one delta
      rw [h10]
      field_simp [hdelta_pos.ne']
    calc
      (1 : ℝ) = delta * Real.rpow delta (-1 : ℝ) := h9.symm
      _ ≤ delta *
          Real.rpow delta (-epsilon * ((M - 1 : ℕ) : ℝ)) := by
            gcongr
      _ = geometricScale delta epsilon (M - 1) := by
            rfl
  let P : ℕ → Prop := fun n => rho₀ ≤ geometricScale delta epsilon n
  have hP_M1 : P (M - 1) := by
    dsimp only [P]
    exact h2.trans h4
  have h_exists : ∃ n : ℕ, P n := ⟨M - 1, hP_M1⟩
  let iMin : ℕ := Nat.find h_exists
  have hiP_min : P iMin := Nat.find_spec h_exists
  have hi_le_M1 : iMin ≤ M - 1 :=
    Nat.find_min' h_exists hP_M1
  have hi_lt_M : iMin < M := by
    omega
  have h_i_min : ∀ j < iMin, ¬ P j :=
    fun j hj => Nat.find_min h_exists hj
  have h_rho0_pos : 0 < rho₀ := by
    linarith
  have h_R_gt_one : (1 : ℝ) < Real.rpow delta (-epsilon) := by
    have h_neg : -epsilon < 0 := by
      linarith
    simpa using
      Real.rpow_lt_rpow_of_exponent_gt
        hdelta_pos hdelta_lt_one h_neg
  by_cases h_i0 : iMin = 0
  · have hP0 : P 0 := by
      simpa [h_i0] using hiP_min
    have h_rho0_eq_delta : rho₀ = delta := by
      dsimp only [P] at hP0
      simp [geometricScale] at hP0
      linarith
    have h_scale_zero : geometricScale delta epsilon 0 = delta := by
      simp [geometricScale]
    refine ⟨0, by omega, ?_, ?_⟩
    · rw [h_scale_zero, h_rho0_eq_delta]
    · rw [h_scale_zero, h_rho0_eq_delta]
      simpa [mul_comm] using
        mul_lt_mul_of_pos_left h_R_gt_one hdelta_pos
  · have h_i_pos : 0 < iMin := Nat.pos_of_ne_zero h_i0
    set previous : ℕ := iMin - 1 with hprevious
    have h_previous_lt : previous < iMin := by
      simp [hprevious, h_i_pos] <;> omega
    have h_previous_scale :
        geometricScale delta epsilon previous < rho₀ := by
      have hnot : ¬ P previous :=
        h_i_min previous h_previous_lt
      simpa [P] using hnot
    have h_scale_eq :
        geometricScale delta epsilon iMin =
          geometricScale delta epsilon previous *
            Real.rpow delta (-epsilon) := by
      have hi : iMin = previous + 1 := by
        simp [hprevious, h_i_pos]
        omega
      rw [hi]
      exact geometricScale_succ hdelta_pos previous
    have hR_pos : 0 < Real.rpow delta (-epsilon) :=
      Real.rpow_pos_of_pos hdelta_pos _
    have h_upper :
        geometricScale delta epsilon previous *
            Real.rpow delta (-epsilon) <
          Real.rpow delta (-epsilon) * rho₀ := by
      have hmul :=
        mul_lt_mul_of_pos_right h_previous_scale hR_pos
      simpa [mul_comm] using hmul
    refine ⟨iMin, hi_lt_M, hiP_min, ?_⟩
    rw [h_scale_eq]
    exact h_upper

/--
Simultaneously regularize the ambient nearby-witness parent maps on a
pre-selected subfamily.
-/
theorem pure_cwa_balanced_selection_preselected
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    (ambient : WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (preSelected : WZ2PaperPureTubeSubfamily fine)
    (hPreNonempty : preSelected.family.Nonempty)
    (k : ℕ)
    (hk : 0 < k)
    (scales : Fin k → WZ2PaperRequestedScale delta) :
    ∃ (selected : WZ2PaperPureTubeSubfamily fine)
      (selectedPre : WZ2PaperPureTubeSubfamily preSelected.family)
      (degreeConstant retentionConstant : ENNReal),
      selected.family.Nonempty ∧
      degreeConstant ≠ ⊤ ∧
      retentionConstant ≠ ⊤ ∧
      selected.family.card = selectedPre.family.card ∧
      (∃ f : Fin selected.family.card → Fin selectedPre.family.card,
        ∀ i,
          selected.embedding i =
            preSelected.embedding (selectedPre.embedding (f i))) ∧
      preSelected.family.enncard ≤
        retentionConstant * selected.family.enncard ∧
      degreeConstant =
        16 * (k : ENNReal) *
          (Nat.log 2 (2 * preSelected.family.card) + 1 : ENNReal) ^ k ∧
      retentionConstant =
        8 * (Nat.log 2 (2 * preSelected.family.card) + 1 : ENNReal) ^
          (k + 1) ∧
      (∀ i : Fin k,
        let nearby := Classical.choice (ambient.2.2.2 (scales i))
        ∀ first second : Fin nearby.scaleData.coarse.card,
          0 < ((Finset.univ : Finset (Fin selected.family.card)).filter
                 fun source =>
                   nearby.scaleData.cover.parent
                     (selected.embedding source) = first).card →
          0 < ((Finset.univ : Finset (Fin selected.family.card)).filter
                 fun source =>
                   nearby.scaleData.cover.parent
                     (selected.embedding source) = second).card →
          (((Finset.univ : Finset (Fin selected.family.card)).filter
              fun source =>
                nearby.scaleData.cover.parent
                  (selected.embedding source) = first).card : ENNReal) ≤
            degreeConstant *
            (((Finset.univ : Finset (Fin selected.family.card)).filter
                fun source =>
                  nearby.scaleData.cover.parent
                    (selected.embedding source) = second).card : ENNReal)) := by
  let coverData :
      ∀ i, WZ2PaperPureNearbyScaleCoverData
        fine (scales i) ambientConstant :=
    fun i => Classical.choice (ambient.2.2.2 (scales i))
  let Vertex : Fin k → Type :=
    fun i => Fin (coverData i).scaleData.coarse.card
  let parent : ∀ i, Fin preSelected.family.card → Vertex i :=
    fun i source =>
      (coverData i).scaleData.cover.parent (preSelected.embedding source)
  let weight : Fin preSelected.family.card → ENNReal := fun _ => 1
  have hSelection :
      Nonempty
        (WZ2FiniteWeightedDegreeSelectionData k Vertex parent weight) :=
    wz2_finite_weighted_degree_selection k Vertex parent weight hk
  rcases hSelection with ⟨data⟩
  let selectedFinset := data.selected
  let selectedPre :=
    WZ2PaperPureTubeSubfamily.fromFinset
      preSelected.family selectedFinset
  let selected : WZ2PaperPureTubeSubfamily fine :=
    { family := selectedPre.family
      embedding :=
        { toFun := fun i =>
            preSelected.embedding (selectedPre.embedding i)
          inj' :=
            Function.Injective.comp
              preSelected.embedding.inj' selectedPre.embedding.inj' }
      tube_eq := fun i =>
        (selectedPre.tube_eq i).trans
          (preSelected.tube_eq (selectedPre.embedding i)) }
  let N := Fintype.card (Fin preSelected.family.card)
  let degreeConstant : ENNReal :=
    16 * (k : ENNReal) *
      (Nat.log 2 (2 * N) + 1 : ENNReal) ^ k
  let retentionConstant : ENNReal :=
    8 * (Nat.log 2 (2 * N) + 1 : ENNReal) ^ (k + 1)
  have hSelectedFinsetNonempty : selectedFinset.Nonempty := by
    by_contra h
    have hEmpty : selectedFinset = ∅ := by
      simpa using h
    have hRetained := data.retained_weight
    have hSelectedWeight :
        (∑ index ∈ selectedFinset, weight index) = 0 := by
      rw [hEmpty]
      simp
    rw [hSelectedWeight] at hRetained
    have hPreCardPos : 0 < preSelected.family.card := by
      simpa [Kakeya.Streamlined.TubeFamily.Nonempty] using
        hPreNonempty
    have hTotal :
        (∑ index : Fin preSelected.family.card, weight index) =
          (preSelected.family.card : ENNReal) := by
      simp [weight, Finset.sum_const] <;> norm_cast
    have hTotalPos :
        0 < (∑ index : Fin preSelected.family.card, weight index) := by
      rw [hTotal]
      exact_mod_cast hPreCardPos
    have hZero :
        (∑ index : Fin preSelected.family.card, weight index) ≤ 0 := by
      simpa using hRetained
    exact (not_le.mpr hTotalPos) hZero
  have hSelectedNonempty : selected.family.Nonempty := by
    have hCardPos : 0 < selected.family.card := by
      change 0 < selectedFinset.card
      exact hSelectedFinsetNonempty.card_pos
    simpa [Kakeya.Streamlined.TubeFamily.Nonempty] using hCardPos
  have hDegreeTop : degreeConstant ≠ ⊤ :=
    ENNReal.coe_ne_top
  have hRetentionTop : retentionConstant ≠ ⊤ :=
    ENNReal.coe_ne_top
  have hRetention :
      preSelected.family.enncard ≤
        retentionConstant * selected.family.enncard := by
    have hRetained :
        (∑ index : Fin preSelected.family.card, weight index) ≤
          (8 : ENNReal) *
            (Nat.log 2 (2 * N) + 1 : ENNReal) ^ (k + 1) *
            ∑ index ∈ selectedFinset, weight index :=
      data.retained_weight
    have h1 :
        (∑ index : Fin preSelected.family.card, weight index) =
          (preSelected.family.card : ENNReal) := by
      simp [weight, Finset.sum_const] <;> norm_cast
    have h2 :
        (∑ index ∈ selectedFinset, weight index) =
          (selected.family.card : ENNReal) := by
      simp [weight, Finset.sum_const]
      norm_cast
    rw [h1, h2] at hRetained
    exact hRetained
  have hEmbeddingMem :
      ∀ source : Fin selectedPre.family.card,
        selectedPre.embedding source ∈ selectedFinset := by
    intro source
    exact Finset.orderEmbOfFin_mem selectedFinset rfl source
  have hImage :
      Finset.image selectedPre.embedding
          (Finset.univ : Finset (Fin selectedPre.family.card)) =
        selectedFinset := by
    have hSubset :
        Finset.image selectedPre.embedding
            (Finset.univ : Finset (Fin selectedPre.family.card)) ⊆
          selectedFinset := by
      intro source hsource
      rcases Finset.mem_image.mp hsource with ⟨index, _, rfl⟩
      exact hEmbeddingMem index
    have hCard :
        (Finset.image selectedPre.embedding
          (Finset.univ : Finset (Fin selectedPre.family.card))).card =
            selectedFinset.card := by
      rw [Finset.card_image_of_injective _
        selectedPre.embedding.injective]
      simp [selectedPre, Kakeya.Streamlined.TubeSubfamily.fromFinset] <;> rfl
    exact Finset.eq_of_subset_of_card_le hSubset (by rw [hCard])
  have hSurjective :
      ∀ source : Fin preSelected.family.card,
        source ∈ selectedFinset →
        ∃ index : Fin selectedPre.family.card,
          selectedPre.embedding index = source := by
    intro source hsource
    have hsource' :
        source ∈
          Finset.image selectedPre.embedding
            (Finset.univ : Finset (Fin selectedPre.family.card)) := by
      rw [hImage]
      exact hsource
    rcases Finset.mem_image.mp hsource' with ⟨index, _, rfl⟩
    exact ⟨index, rfl⟩
  have hFilterCard :
      ∀ (i : Fin k)
        (first : Fin (coverData i).scaleData.coarse.card),
        (selectedFinset.filter
          fun source => parent i source = first).card =
        ((Finset.univ : Finset (Fin selectedPre.family.card)).filter
          fun source =>
            parent i (selectedPre.embedding source) = first).card := by
    intro i first
    let left :=
      selectedFinset.filter fun source => parent i source = first
    let right :=
      (Finset.univ : Finset (Fin selectedPre.family.card)).filter
        fun source =>
          parent i (selectedPre.embedding source) = first
    have hFilterImage : Finset.image selectedPre.embedding right = left := by
      ext source
      simp only [left, right, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨index, hparent, rfl⟩
        exact ⟨hEmbeddingMem index, hparent⟩
      · rintro ⟨hsource, hparent⟩
        rcases hSurjective source hsource with ⟨index, hindex⟩
        refine ⟨index, ?_, hindex⟩
        rwa [hindex]
    have hCard :
        (Finset.image selectedPre.embedding right).card = right.card :=
      Finset.card_image_of_injective
        right selectedPre.embedding.injective
    have hFinal : left.card = right.card := by
      rw [← hFilterImage, hCard]
    exact hFinal
  have hDegreeUniform :
      ∀ i : Fin k,
        ∀ first second : Fin (coverData i).scaleData.coarse.card,
          0 < ((Finset.univ :
              Finset (Fin selected.family.card)).filter
                fun source =>
                  (coverData i).scaleData.cover.parent
                    (selected.embedding source) = first).card →
          0 < ((Finset.univ :
              Finset (Fin selected.family.card)).filter
                fun source =>
                  (coverData i).scaleData.cover.parent
                    (selected.embedding source) = second).card →
          (((Finset.univ :
              Finset (Fin selected.family.card)).filter
                fun source =>
                  (coverData i).scaleData.cover.parent
                    (selected.embedding source) = first).card : ENNReal) ≤
            degreeConstant *
            (((Finset.univ :
                Finset (Fin selected.family.card)).filter
                  fun source =>
                    (coverData i).scaleData.cover.parent
                      (selected.embedding source) = second).card : ENNReal) := by
    intro i first second hfirst hsecond
    have hfirst' :
        0 < (selectedFinset.filter
          fun source => parent i source = first).card := by
      rw [hFilterCard i first]
      exact hfirst
    have hsecond' :
        0 < (selectedFinset.filter
          fun source => parent i source = second).card := by
      rw [hFilterCard i second]
      exact hsecond
    have hMain :=
      data.degree_uniform i first second hfirst' hsecond'
    rw [hFilterCard i first, hFilterCard i second] at hMain
    exact hMain
  have hN : N = preSelected.family.card := by
    simp [N, Fintype.card_fin]
  exact ⟨selected, selectedPre, degreeConstant, retentionConstant,
    hSelectedNonempty, hDegreeTop, hRetentionTop, rfl,
    ⟨fun i => i, fun i => rfl⟩, hRetention,
    by simp [degreeConstant, hN],
    by simp [retentionConstant, hN],
    hDegreeUniform⟩

/-- Geometric requested scales, capped at `1`. -/
def geometricRequestedScales
    (delta epsilon : ℝ)
    (hdelta_pos : 0 < delta)
    (hdelta_lt_one : delta < 1)
    (hepsilon_pos : 0 < epsilon)
    (M : ℕ)
    (i : Fin M) :
    WZ2PaperRequestedScale delta :=
  let scale := geometricScale delta epsilon i
  have h_exp : -epsilon * (i : ℝ) ≤ 0 := by
    have h_i : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
    nlinarith
  have h_rpow :
      1 ≤ Real.rpow delta (-epsilon * (i : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hdelta_pos (by linarith) h_exp
  have h_ge_delta : delta ≤ scale := by
    change delta ≤
      delta * Real.rpow delta (-epsilon * (i : ℝ))
    have h :
        delta * 1 ≤
          delta * Real.rpow delta (-epsilon * (i : ℝ)) := by
      gcongr
    simpa using h
  have h_delta_le_one : delta ≤ 1 := hdelta_lt_one.le
  ⟨min scale 1, le_min h_ge_delta h_delta_le_one, min_le_right _ _⟩

@[simp]
lemma geometricRequestedScales_val
    (delta epsilon : ℝ)
    (hdelta_pos : 0 < delta)
    (hdelta_lt_one : delta < 1)
    (hepsilon_pos : 0 < epsilon)
    (M : ℕ)
    (i : Fin M) :
    (geometricRequestedScales delta epsilon hdelta_pos
      hdelta_lt_one hepsilon_pos M i).1 =
        min (geometricScale delta epsilon i) 1 := by
  rfl

/-- Rounding property for the capped geometric requested scales. -/
lemma geometricRequestedScale_rounding
    {delta epsilon : ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_lt_one : delta < 1)
    (hepsilon_pos : 0 < epsilon)
    {M : ℕ}
    (hM : M = geometricScaleCount epsilon)
    (rho₀ : WZ2PaperRequestedScale delta) :
    ∃ i : Fin M,
      rho₀.1 ≤
        (geometricRequestedScales delta epsilon hdelta_pos
          hdelta_lt_one hepsilon_pos M i).1 ∧
      ENNReal.ofReal
          (geometricRequestedScales delta epsilon hdelta_pos
            hdelta_lt_one hepsilon_pos M i).1 <
        ENNReal.ofReal (Real.rpow delta (-epsilon)) *
          ENNReal.ofReal rho₀.1 := by
  rcases geometricScale_rounding hdelta_pos hdelta_lt_one
      hepsilon_pos rho₀.1 rho₀.2.1 rho₀.2.2 with
    ⟨k, hk, hle, hlt⟩
  have hkM : k < M := by
    rw [hM]
    exact hk
  let i : Fin M := ⟨k, hkM⟩
  let schedule :=
    geometricRequestedScales delta epsilon hdelta_pos
      hdelta_lt_one hepsilon_pos M
  have hR_pos : 0 < Real.rpow delta (-epsilon) :=
    Real.rpow_pos_of_pos hdelta_pos _
  have hrho_pos : 0 < rho₀.1 := by
    linarith [rho₀.2.1]
  have hprod_pos :
      0 < Real.rpow delta (-epsilon) * rho₀.1 :=
    mul_pos hR_pos hrho_pos
  by_cases hscale : geometricScale delta epsilon k ≤ 1
  · have hvalue : (schedule i).1 =
        geometricScale delta epsilon k := by
      rw [geometricRequestedScales_val, min_eq_left hscale]
    have hlt' :
        ENNReal.ofReal (geometricScale delta epsilon k) <
          ENNReal.ofReal
            (Real.rpow delta (-epsilon) * rho₀.1) :=
      (ENNReal.ofReal_lt_ofReal_iff hprod_pos).mpr hlt
    have hmul :
        ENNReal.ofReal
            (Real.rpow delta (-epsilon) * rho₀.1) =
          ENNReal.ofReal (Real.rpow delta (-epsilon)) *
            ENNReal.ofReal rho₀.1 := by
      rw [ENNReal.ofReal_mul hR_pos.le]
    refine ⟨i, ?_, ?_⟩
    · rw [hvalue]
      exact hle
    · rw [hvalue]
      exact hlt'.trans_eq hmul
  · have hscale' : 1 < geometricScale delta epsilon k := by
      linarith
    have hvalue : (schedule i).1 = 1 := by
      rw [geometricRequestedScales_val,
        min_eq_right hscale'.le]
    have hone : (1 : ℝ) <
        Real.rpow delta (-epsilon) * rho₀.1 := by
      linarith
    have hlt' :
        ENNReal.ofReal (1 : ℝ) <
          ENNReal.ofReal
            (Real.rpow delta (-epsilon) * rho₀.1) :=
      (ENNReal.ofReal_lt_ofReal_iff hprod_pos).mpr hone
    have hmul :
        ENNReal.ofReal
            (Real.rpow delta (-epsilon) * rho₀.1) =
          ENNReal.ofReal (Real.rpow delta (-epsilon)) *
            ENNReal.ofReal rho₀.1 := by
      rw [ENNReal.ofReal_mul hR_pos.le]
    refine ⟨i, ?_, ?_⟩
    · rw [hvalue]
      exact rho₀.2.2
    · rw [hvalue]
      exact hlt'.trans_eq hmul

/--
Select a degree-uniform subfamily of a pre-selected family and transfer the
ambient pure CWA to it at `outputConstant`.
-/
theorem degree_uniform_restricted_cwa
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    (ambient : WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (preSelected : WZ2PaperPureTubeSubfamily fine)
    (hPreNonempty : preSelected.family.Nonempty)
    (preSelectedRetention : ENNReal)
    (hPreRetention :
      fine.enncard ≤
        preSelectedRetention * preSelected.family.enncard)
    (hPreRetentionTop : preSelectedRetention ≠ ⊤)
    (epsilon : ℝ)
    (hepsilon_pos : 0 < epsilon)
    (hdelta_pos : 0 < delta)
    (hdelta_lt_one : delta < 1)
    (houtputTop : outputConstant ≠ ⊤)
    (h_R_ambient_le_output :
      ENNReal.ofReal (Real.rpow delta (-epsilon)) *
          ambientConstant ≤
        outputConstant)
    (h_restricted_ok :
      ∀ degreeConstant balancedRetention : ENNReal,
        degreeConstant ≠ ⊤ →
        balancedRetention ≠ ⊤ →
        wz2PaperPureNearbyRestrictionConstant
            ambientConstant 1 degreeConstant
              (preSelectedRetention * balancedRetention) ≤
          outputConstant) :
    ∃ (selected : WZ2PaperPureTubeSubfamily fine)
      (degreeConstant balancedRetention : ENNReal),
      selected.family.Nonempty ∧
      degreeConstant ≠ ⊤ ∧
      balancedRetention ≠ ⊤ ∧
      WZ2PaperPureCWAAtNearbyScales
        selected.family outputConstant ∧
      fine.enncard ≤
        (preSelectedRetention * balancedRetention) *
          selected.family.enncard := by
  let M := geometricScaleCount epsilon
  have hM_pos : 0 < M := Nat.succ_pos _
  let scales : Fin M → WZ2PaperRequestedScale delta :=
    geometricRequestedScales delta epsilon hdelta_pos
      hdelta_lt_one hepsilon_pos M
  rcases pure_cwa_balanced_selection_preselected
      ambient preSelected hPreNonempty M hM_pos scales with
    ⟨selected, selectedPre, degreeConstant, balancedRetention,
      hSelectedNonempty, hDegreeTop, hRetentionTop, _,
      _, hBalancedRetention, _, _, hDegreeUniform⟩
  let totalRetention :=
    preSelectedRetention * balancedRetention
  have hTotalRetentionTop : totalRetention ≠ ⊤ :=
    ENNReal.mul_ne_top hPreRetentionTop hRetentionTop
  have hCombinedRetention :
      fine.enncard ≤ totalRetention * selected.family.enncard := by
    calc
      fine.enncard ≤
          preSelectedRetention * preSelected.family.enncard :=
        hPreRetention
      _ ≤ preSelectedRetention *
          (balancedRetention * selected.family.enncard) := by
            gcongr
      _ = totalRetention * selected.family.enncard := by
            simp [totalRetention]
            ring
  have hGlobalRetention :
      (1 : ENNReal) * fine.enncard ≤
        totalRetention * selected.family.enncard := by
    simpa using hCombinedRetention
  let R : ENNReal :=
    ENNReal.ofReal (Real.rpow delta (-epsilon))
  have hR_pos : (0 : ENNReal) < R := by
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hdelta_pos _)
  have hR_top : R ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hR_one : (1 : ENNReal) ≤ R := by
    have h :
        (1 : ℝ) < Real.rpow delta (-epsilon) := by
      exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg
        hdelta_pos hdelta_lt_one (by linarith)
    simpa [R] using ENNReal.ofReal_le_ofReal h.le
  have hRounding :
      ∀ rho₀ : WZ2PaperRequestedScale delta,
        ∃ i : Fin M,
          rho₀.1 ≤ (scales i).1 ∧
          ENNReal.ofReal (scales i).1 <
            R * ENNReal.ofReal rho₀.1 := by
    exact geometricRequestedScale_rounding
      hdelta_pos hdelta_lt_one hepsilon_pos
      (rfl : M = geometricScaleCount epsilon)
  have hRestricted :
      wz2PaperPureNearbyRestrictionConstant
          ambientConstant 1 degreeConstant totalRetention ≤
        outputConstant := by
    exact h_restricted_ok degreeConstant balancedRetention
      hDegreeTop hRetentionTop
  have hSelectedCWA :
      WZ2PaperPureCWAAtNearbyScales
        selected.family outputConstant :=
    pure_cwa_restrict_with_rounding
      ambient selected hSelectedNonempty M hM_pos scales
      degreeConstant totalRetention 1
      (by simp) (by simp) hTotalRetentionTop hDegreeTop
      hGlobalRetention hDegreeUniform
      hR_pos hR_top hR_one hRounding
      h_R_ambient_le_output houtputTop hRestricted
  exact ⟨selected, degreeConstant, balancedRetention,
    hSelectedNonempty, hDegreeTop, hRetentionTop,
    hSelectedCWA, hCombinedRetention⟩

end Kakeya.Assouad

end
