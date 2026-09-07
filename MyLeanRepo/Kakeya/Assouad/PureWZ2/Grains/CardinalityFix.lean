import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ConstantMultiplicityRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BroadSetMultilinearKakeya
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountPhase2
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import Mathlib.Tactic

/-!
# Cardinality fix: restrict constant-multiplicity subshading to a subfamily

## Problem

`constant_multiplicity_refinement` produces a SUBSHADING (same family F, full N),
but the paper applies multilinear Kakeya to a SUBFAMILY with effective cardinality
#𝕋₂ < N. The CV bound `(δ²·N)^(3/2)` is too loose; we need `(δ²·#𝕋₂)^(3/2)`.

## Fix

After constant multiplicity refinement, restrict to the subfamily F₂ of tubes
with NONEMPTY carriers. Then:
- F₂.enncard = #𝕋₂ ≤ N
- Multiplicity bounds are preserved (empty carriers don't contribute)
- Mass is preserved
- Multilinear Kakeya applied to F₂ gives the tighter bound

## Key lemma

`restrict_shading_to_nonempty_subfamily`:
Given S' : WZ1PaperTubeShading F, produce
  F₂ : TubeSubfamily F
  S₂ : WZ1PaperTubeShading F₂.family
such that S₂.mass = S'.mass and multiplicity is preserved.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set ENNReal Finset Classical
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- Restrict a paper shading to the subfamily of tubes with nonempty carriers.

The resulting shading has the same mass and same pointwise multiplicity,
but uses a smaller family (effective cardinality #𝕋₂). -/
lemma restrict_shading_to_nonempty_subfamily
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hcub : WZ1PaperIsCubicalShading S) :
    ∃ (F₂ : Kakeya.Streamlined.TubeSubfamily F)
      (S₂ : WZ1PaperTubeShading F₂.family),
      (∀ (p : Point3), S₂.pointMultiplicity p = S.pointMultiplicity p) ∧
      S₂.mass = S.mass ∧
      WZ1PaperIsCubicalShading S₂ ∧
      (∀ i, (S₂.carrier i).Nonempty) ∧
      (∀ (i : Fin F₂.family.card), S₂.carrier i = S.carrier (F₂.embedding i)) := by
  let selectedIndices : Finset (Fin F.card) :=
    Finset.univ.filter fun i => (S.carrier i).Nonempty
  let F₂ : Kakeya.Streamlined.TubeSubfamily F :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset F selectedIndices
  let S₂ : WZ1PaperTubeShading F₂.family :=
    { carrier := fun i => S.carrier (F₂.embedding i)
      measurable_carrier := fun i => S.measurable_carrier (F₂.embedding i)
      subset_body := fun i x hx => S.subset_body (F₂.embedding i) hx }
  have h_emb_mem : ∀ (i : Fin F₂.family.card), F₂.embedding i ∈ selectedIndices := by
    intro i
    exact Finset.orderEmbOfFin_mem selectedIndices rfl i
  have h_selected : ∀ (i : Fin F₂.family.card),
      (S.carrier (F₂.embedding i)).Nonempty := by
    intro i
    have h_in : F₂.embedding i ∈ selectedIndices := h_emb_mem i
    simpa [selectedIndices, Finset.mem_filter] using h_in
  have h_inj : Function.Injective F₂.embedding := F₂.embedding.inj'
  have h_img_subset : Finset.image F₂.embedding Finset.univ ⊆ selectedIndices := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact h_emb_mem i
  have h_img_card : (Finset.image F₂.embedding Finset.univ).card = selectedIndices.card := by
    have h1 : (Finset.image F₂.embedding Finset.univ).card =
        (Finset.univ : Finset (Fin F₂.family.card)).card :=
      Finset.card_image_of_injective Finset.univ h_inj
    have h2 : (Finset.univ : Finset (Fin F₂.family.card)).card = F₂.family.card := by simp
    have h3 : F₂.family.card = selectedIndices.card := by
      simp [F₂, Kakeya.Streamlined.TubeSubfamily.fromFinset]
    rw [h1, h2, h3]
  have h_img : Finset.image F₂.embedding Finset.univ = selectedIndices :=
    Finset.eq_of_subset_of_card_le h_img_subset (by rw [h_img_card])
  have h_mult : ∀ (p : Point3),
      S₂.pointMultiplicity p = S.pointMultiplicity p := by
    intro p
    let A : Finset (Fin F₂.family.card) :=
      Finset.univ.filter fun i => p ∈ S.carrier (F₂.embedding i)
    let B : Finset (Fin F.card) :=
      Finset.univ.filter fun j => p ∈ S.carrier j
    have h1 : S₂.pointMultiplicity p = A.card := by rfl
    have h2 : S.pointMultiplicity p = B.card := by rfl
    rw [h1, h2]
    have hAB : Finset.image F₂.embedding A = B := by
      ext j
      simp only [A, B, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, _, rfl⟩
        exact ‹_›
      · intro hj
        have h_nonempty : (S.carrier j).Nonempty := ⟨p, hj⟩
        have h_j_in : j ∈ selectedIndices := by
          simpa [selectedIndices, Finset.mem_filter] using h_nonempty
        have h_in_img : j ∈ Finset.image F₂.embedding Finset.univ := by
          rw [h_img] <;> exact h_j_in
        rcases Finset.mem_image.mp h_in_img with ⟨i, _, rfl⟩
        exact ⟨i, by simpa using hj, rfl⟩
    have h_card : (Finset.image F₂.embedding A).card = A.card :=
      Finset.card_image_of_injective A h_inj
    rw [← h_card, hAB]
  have h_inj_on : Set.InjOn F₂.embedding (Finset.univ : Finset (Fin F₂.family.card)) :=
    fun x _ y _ h => h_inj h
  let g : Fin F.card → ENNReal := fun j => volume (S.carrier j)
  have h_mass : S₂.mass = S.mass := by
    have h1 : S₂.mass = ∑ i : Fin F₂.family.card, g (F₂.embedding i) := by
      rfl
    rw [h1]
    have h2 : (∑ i : Fin F₂.family.card, g (F₂.embedding i)) =
        ∑ j ∈ Finset.image F₂.embedding Finset.univ, g j :=
      (Finset.sum_image h_inj_on).symm
    rw [h2, h_img]
    have h3 : ∑ j ∈ selectedIndices, volume (S.carrier j) =
        ∑ j : Fin F.card, volume (S.carrier j) := by
      apply Finset.sum_subset (Finset.subset_univ selectedIndices)
      intro j _ hnot
      have h_empty : ¬(S.carrier j).Nonempty := by
        simpa [selectedIndices, Finset.mem_filter] using hnot
      have h_vol : volume (S.carrier j) = 0 := by
        have h : S.carrier j = ∅ := by
          simpa [Set.not_nonempty_iff_eq_empty] using h_empty
        rw [h]
        exact measure_empty
      rw [h_vol]
    rw [h3] <;> rfl
  have h_cub : WZ1PaperIsCubicalShading S₂ := by
    intro i p hp
    have h : wz1PaperGridCube delta (wz1PaperGridIndex delta p) ⊆ S.carrier (F₂.embedding i) :=
      hcub (F₂.embedding i) p hp
    exact h
  have h_carrier_eq : ∀ (i : Fin F₂.family.card), S₂.carrier i = S.carrier (F₂.embedding i) := by
    intro i
    rfl
  exact ⟨F₂, S₂, h_mult, h_mass, h_cub, h_selected, h_carrier_eq⟩

/-- Broad set smallness via constant-multiplicity loophole, using a SUBFAMILY.

This is the same as `broad_set_small_constant_multiplicity` but the CV bound
uses `F₂.enncard` (the effective cardinality #𝕋₂) instead of the full family
cardinality N. This gives the tighter bound `(δ²·#𝕋₂)^(3/2)`. -/
theorem broad_set_small_constant_multiplicity_subfamily
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {F₂ : Kakeya.Streamlined.TubeSubfamily F}
    {S : WZ1PaperTubeShading F₂.family}
    -- Universal CV estimate
    (C : ENNReal)
    (hC_ne_top : C ≠ ⊤)
    (hCV_univ : ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
      ∀ (F : Kakeya.Streamlined.TubeFamily delta),
      ∀ (Y : WZ1PaperTubeShading F),
      ∀ (E : Set Point3) (L : ENNReal),
        MeasurableSet E →
        (∀ x ∈ E, L ≤ paperShadingTrilinearMultiplicity Y x ^ (1 / 2 : ℝ)) →
        L * volume E ≤ C * (ENNReal.ofReal (delta ^ 2) * F.enncard) ^ (3 / 2 : ℝ))
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    -- Constant multiplicity bounds
    (mu0 : ENNReal)
    (hmu0_ne_top : mu0 ≠ ⊤)
    (hmult_lower : ∀ p ∈ S.union, mu0 ≤ (S.pointMultiplicity p : ENNReal))
    (hmult_upper : ∀ p ∈ S.union, (S.pointMultiplicity p : ENNReal) < 2 * mu0)
    -- Broad-set parameters
    (Q : ℕ)
    (tau : ℝ)
    (hQ_pos : 0 < Q)
    (htau_pos : 0 < tau)
    -- Geometric volume lower bound using #𝕋₂ = F₂.family.enncard
    (hvol_lower : (4 : ENNReal) * C *
        (ENNReal.ofReal (delta ^ 2) * F₂.family.enncard) ^ (3 / 2 : ℝ) ≤
      (((Q : ENNReal) * ENNReal.ofReal tau) ^ (1 / 2 : ℝ)) * volume S.union) :
    2 * (∫⁻ p in paperCountedBroadSet S tau Q,
          (S.pointMultiplicity p : ENNReal)) ≤ S.mass :=
  broad_set_small_constant_multiplicity
    (F := F₂.family) (S := S)
    C hC_ne_top hCV_univ hdelta_pos hdelta_le_one
    mu0 hmu0_ne_top hmult_lower hmult_upper
    Q tau hQ_pos htau_pos hvol_lower

/-- Combined pipeline: constant multiplicity refinement → subfamily restriction →
broad set smallness.

This is the paper's Lemma 11 route:
1. Constant multiplicity refinement on the full shading
2. Restrict to subfamily of tubes with nonempty carriers (#𝕋₂)
3. Apply multilinear Kakeya with the tighter cardinality #𝕋₂

Note: The output S₂ is over F₂.family (not F), so it cannot be a `PaperIsSubshading`
of S. Instead, we provide carrier-wise inclusion via the embedding. -/
theorem constant_multiplicity_broad_small_pipeline
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hcub : WZ1PaperIsCubicalShading S)
    -- Universal CV estimate
    (C : ENNReal)
    (hC_ne_top : C ≠ ⊤)
    (hCV_univ : ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
      ∀ (F : Kakeya.Streamlined.TubeFamily delta),
      ∀ (Y : WZ1PaperTubeShading F),
      ∀ (E : Set Point3) (L : ENNReal),
        MeasurableSet E →
        (∀ x ∈ E, L ≤ paperShadingTrilinearMultiplicity Y x ^ (1 / 2 : ℝ)) →
        L * volume E ≤ C * (ENNReal.ofReal (delta ^ 2) * F.enncard) ^ (3 / 2 : ℝ))
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    -- Broad-set parameters
    (Q : ℕ)
    (tau : ℝ)
    (hQ_pos : 0 < Q)
    (htau_pos : 0 < tau)
    -- Geometric condition with effective cardinality
    (h_geometric :
      ∀ (F₂ : Kakeya.Streamlined.TubeSubfamily F)
        (S₂ : WZ1PaperTubeShading F₂.family)
        (mu0 : ENNReal),
        (∀ p ∈ S₂.union, mu0 ≤ (S₂.pointMultiplicity p : ENNReal)) →
        (∀ p ∈ S₂.union, (S₂.pointMultiplicity p : ENNReal) < 2 * mu0) →
        S.mass / ((Nat.log 2 F.card + 1 : ℕ) : ENNReal) ≤ S₂.mass →
        (4 : ENNReal) * C *
          (ENNReal.ofReal (delta ^ 2) * F₂.family.enncard) ^ (3 / 2 : ℝ) ≤
        (((Q : ENNReal) * ENNReal.ofReal tau) ^ (1 / 2 : ℝ)) * volume S₂.union) :
    ∃ (level : ℕ) (F₂ : Kakeya.Streamlined.TubeSubfamily F)
      (S₂ : WZ1PaperTubeShading F₂.family),
      let mu0 : ENNReal := (2 ^ level : ENNReal)
      WZ1PaperIsCubicalShading S₂ ∧
      (∀ p ∈ S₂.union, mu0 ≤ (S₂.pointMultiplicity p : ENNReal)) ∧
      (∀ p ∈ S₂.union, (S₂.pointMultiplicity p : ENNReal) < 2 * mu0) ∧
      S.mass / ((Nat.log 2 F.card + 1 : ℕ) : ENNReal) ≤ S₂.mass ∧
      2 * (∫⁻ p in paperCountedBroadSet S₂ tau Q,
            (S₂.pointMultiplicity p : ENNReal)) ≤ S₂.mass := by
  rcases Kakeya.Assouad.constant_multiplicity_refinement hcub with
    ⟨level, S', hsub, hcub', hlower, hupper, hmass⟩
  let mu0 : ENNReal := (2 ^ level : ENNReal)
  rcases restrict_shading_to_nonempty_subfamily (S := S') hcub' with
    ⟨F₂, S₂, hmult_eq, hmass_eq, hcub₂, _, hcarrier_eq⟩
  have hlower₂ : ∀ p ∈ S₂.union, mu0 ≤ (S₂.pointMultiplicity p : ENNReal) := by
    intro p hp
    have h_eq : S₂.pointMultiplicity p = S'.pointMultiplicity p := hmult_eq p
    rw [h_eq]
    have h_in_S' : p ∈ S'.union := by
      rcases hp with ⟨i, hi⟩
      have h1 : S₂.carrier i = S'.carrier (F₂.embedding i) := hcarrier_eq i
      rw [h1] at hi
      exact ⟨F₂.embedding i, hi⟩
    exact hlower p h_in_S'
  have hupper₂ : ∀ p ∈ S₂.union, (S₂.pointMultiplicity p : ENNReal) < 2 * mu0 := by
    intro p hp
    have h_eq : S₂.pointMultiplicity p = S'.pointMultiplicity p := hmult_eq p
    rw [h_eq]
    have h_in_S' : p ∈ S'.union := by
      rcases hp with ⟨i, hi⟩
      have h1 : S₂.carrier i = S'.carrier (F₂.embedding i) := hcarrier_eq i
      rw [h1] at hi
      exact ⟨F₂.embedding i, hi⟩
    exact hupper p h_in_S'
  have hmass₂ : S.mass / ((Nat.log 2 F.card + 1 : ℕ) : ENNReal) ≤ S₂.mass := by
    rw [hmass_eq]
    exact hmass
  have hvol := h_geometric F₂ S₂ mu0 hlower₂ hupper₂ hmass₂
  have hmu0_ne_top : mu0 ≠ ⊤ := by
    simp [mu0] <;> exact ENNReal.pow_ne_top (by simp)
  have hbroad := broad_set_small_constant_multiplicity_subfamily
    (F₂ := F₂) (S := S₂)
    C hC_ne_top hCV_univ hdelta_pos hdelta_le_one
    mu0 hmu0_ne_top hlower₂ hupper₂
    Q tau hQ_pos htau_pos hvol
  exact ⟨level, F₂, S₂, hcub₂, hlower₂, hupper₂, hmass₂, hbroad⟩

/-- Mass upper bound from pointwise multiplicity upper bound.

If `pointMultiplicity p < M` for all p in the union, then
`mass ≤ M * volume(union)`. -/
lemma mass_le_multiplicity_vol
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    {M : ENNReal}
    (hM_ne_top : M ≠ ⊤)
    (hmult_upper : ∀ p ∈ S.union, (S.pointMultiplicity p : ENNReal) < M) :
    S.mass ≤ M * volume S.union := by
  let one : Point3 → ENNReal := fun _ => 1
  let multFun : Point3 → ENNReal := fun p => (S.pointMultiplicity p : ENNReal)
  have h_multFun_eq : multFun = fun p =>
      ∑ i : Fin (wz1PaperBodyFamily F).card, Set.indicator (S.carrier i) one p := by
    funext p
    simp [multFun, Kakeya.Streamlined.Shading.pointMultiplicity, one, Set.indicator_apply]
    <;> norm_cast
  have h1 : ∫⁻ p, multFun p = S.mass := by
    rw [h_multFun_eq]
    have h_meas : ∀ i ∈ Finset.univ, Measurable (Set.indicator (S.carrier i) one) := by
      intro i _
      exact (measurable_const).indicator (S.measurable_carrier i)
    rw [MeasureTheory.lintegral_finsetSum Finset.univ h_meas]
    have h2 : ∑ i : Fin (wz1PaperBodyFamily F).card,
        ∫⁻ p, Set.indicator (S.carrier i) one p =
        ∑ i : Fin (wz1PaperBodyFamily F).card, volume (S.carrier i) := by
      apply Finset.sum_congr rfl
      intro i _
      have h3 : ∫⁻ p, Set.indicator (S.carrier i) one p = volume (S.carrier i) := by
        rw [lintegral_indicator (S.measurable_carrier i)]
        <;> simp [one]
      exact h3
    rw [h2] <;> rfl
  have h_union_meas : MeasurableSet S.union := by
    have h : S.union = ⋃ i : Fin (wz1PaperBodyFamily F).card, S.carrier i := by
      ext x
      simp [Kakeya.Streamlined.Shading.union]
      <;> tauto
    rw [h]
    exact MeasurableSet.iUnion (fun i => S.measurable_carrier i)
  have h3 : ∀ p, multFun p ≤ M * Set.indicator S.union one p := by
    intro p
    by_cases h : p ∈ S.union
    · have h4 : multFun p < M := hmult_upper p h
      have h5 : Set.indicator S.union one p = 1 := by
        rw [Set.indicator_apply]
        <;> simp [h, one]
      rw [h5]
      <;> simpa using h4.le
    · have h5 : multFun p = 0 := by
        simp [multFun, Kakeya.Streamlined.Shading.pointMultiplicity, h] <;> tauto
      have h6 : Set.indicator S.union one p = 0 := by
        rw [Set.indicator_apply] <;> simp [h, one]
      rw [h5, h6] <;> simp
  have h4 : ∫⁻ p, multFun p ≤ ∫⁻ p, M * Set.indicator S.union one p :=
    MeasureTheory.lintegral_mono h3
  have h5 : ∫⁻ p, M * Set.indicator S.union one p = M * volume S.union := by
    have h6 : (fun p => M * Set.indicator S.union one p) =
        Set.indicator S.union (fun _ => M) := by
      funext p
      rw [Set.indicator_apply]
      <;> split_ifs <;> simp [one] <;> aesop
    rw [h6]
    rw [lintegral_indicator h_union_meas]
    <;> simp
  rw [← h1]
  exact le_trans h4 (by rw [h5])

/-- Effective cardinality upper bound from cubicality (δ³ version).

Each nonempty cubical carrier contains at least one grid cube of volume δ³,
so `mass ≥ #𝕋₂ * δ³`. Combined with `mass ≤ 2μ₀ * V`, we get
`#𝕋₂ ≤ 2μ₀ * V / δ³`.

Note: This gives δ^{-3}, not δ^{-2}. For the tighter δ^{-2} bound,
a body-mass lower bound per carrier is needed (see ember's work). -/
lemma nonempty_subfamily_card_le_delta_cubed
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {F₂ : Kakeya.Streamlined.TubeSubfamily F}
    {S₂ : WZ1PaperTubeShading F₂.family}
    (hdelta_pos : 0 < delta)
    (hcub : WZ1PaperIsCubicalShading S₂)
    (hnonempty : ∀ i, (S₂.carrier i).Nonempty)
    {mu0 : ENNReal}
    (hmu0_ne_top : mu0 ≠ ⊤)
    (hmult_upper : ∀ p ∈ S₂.union, (S₂.pointMultiplicity p : ENNReal) < 2 * mu0) :
    (F₂.family.enncard : ENNReal) * ENNReal.ofReal (delta ^ 3) ≤
      (2 * mu0) * volume S₂.union := by
  have h2mu_ne_top : (2 * mu0) ≠ ⊤ := ENNReal.mul_ne_top (by simp) hmu0_ne_top
  have h_mass_upper : S₂.mass ≤ (2 * mu0) * volume S₂.union :=
    mass_le_multiplicity_vol h2mu_ne_top hmult_upper
  have h_cube_vol : ∀ (cell : ℤ × ℤ × ℤ),
      volume (wz1PaperGridCube delta cell) = ENNReal.ofReal (delta ^ 3) := by
    intro cell
    rw [wz1PaperGridCube_volume_eq hdelta_pos cell (0, 0, 0)]
    exact wz1PaperGridCube_volume_exact hdelta_pos
  have h_mass_lower : S₂.mass ≥
      (F₂.family.enncard : ENNReal) * ENNReal.ofReal (delta ^ 3) := by
    let I := Fin (wz1PaperBodyFamily F₂.family).card
    have h1 : ∀ (i : I), volume (S₂.carrier i) ≥ ENNReal.ofReal (delta ^ 3) := by
      intro i
      rcases hnonempty i with ⟨p, hp⟩
      let cell := wz1PaperGridIndex delta p
      have h_cube_in : wz1PaperGridCube delta cell ⊆ S₂.carrier i := hcub i p hp
      have h_vol : volume (wz1PaperGridCube delta cell) ≤ volume (S₂.carrier i) :=
        measure_mono h_cube_in
      rw [h_cube_vol cell] at h_vol
      exact h_vol
    have h_card1 : Fintype.card I = (wz1PaperBodyFamily F₂.family).card := by
      simp [I, Fintype.card_fin]
    have h_card2 : (wz1PaperBodyFamily F₂.family).card = F₂.family.card := by rfl
    have h_card3 : Fintype.card I = F₂.family.card := by
      rw [h_card1, h_card2]
    have h_card : (Fintype.card I : ENNReal) = F₂.family.enncard := by
      rw [h_card3] <;> rfl
    calc
      S₂.mass
        = ∑ i : I, volume (S₂.carrier i) := by
          dsimp only [I, Kakeya.Streamlined.Shading.mass] <;> rfl
      _ ≥ ∑ i : I, ENNReal.ofReal (delta ^ 3) :=
          Finset.sum_le_sum (fun i _ => h1 i)
      _ = (Fintype.card I : ENNReal) * ENNReal.ofReal (delta ^ 3) := by
          have h1 : ∑ i : I, ENNReal.ofReal (delta ^ 3) =
              ENNReal.ofReal (delta ^ 3) * ∑ i : I, (1 : ENNReal) := by
            have h : ENNReal.ofReal (delta ^ 3) * ∑ i : I, (1 : ENNReal) =
                ∑ i : I, ENNReal.ofReal (delta ^ 3) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              simp
            exact h.symm
          rw [h1]
          have h2 : ∑ i : I, (1 : ENNReal) = (Fintype.card I : ENNReal) := by
            simpa using Finset.sum_ones
          rw [h2] <;> ring
      _ = F₂.family.enncard * ENNReal.ofReal (delta ^ 3) := by
          rw [h_card] <;> simp [mul_comm]
  exact le_trans h_mass_lower h_mass_upper

/-- Conditional effective cardinality upper bound (δ² version).

If each carrier has volume at least `c * δ²` (body-mass lower bound), then
`#𝕋₂ ≤ 2μ₀ * V / (c * δ²)`.

This is the bound needed for the μ₀ cancellation in the broad-set condition.
The body-mass lower bound `c * δ²` per carrier must be supplied separately
(e.g., from ember's body-mass bound or full-carrier assumption). -/
lemma nonempty_subfamily_card_le_delta_squared
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {F₂ : Kakeya.Streamlined.TubeSubfamily F}
    {S₂ : WZ1PaperTubeShading F₂.family}
    {c : ENNReal}
    (hc_ne_top : c ≠ ⊤)
    (h_carrier_vol : ∀ i, c * ENNReal.ofReal (delta ^ 2) ≤ volume (S₂.carrier i))
    {mu0 : ENNReal}
    (hmu0_ne_top : mu0 ≠ ⊤)
    (hmult_upper : ∀ p ∈ S₂.union, (S₂.pointMultiplicity p : ENNReal) < 2 * mu0) :
    (F₂.family.enncard : ENNReal) * (c * ENNReal.ofReal (delta ^ 2)) ≤
      (2 * mu0) * volume S₂.union := by
  have h2mu_ne_top : (2 * mu0) ≠ ⊤ := ENNReal.mul_ne_top (by simp) hmu0_ne_top
  have h_mass_upper : S₂.mass ≤ (2 * mu0) * volume S₂.union :=
    mass_le_multiplicity_vol h2mu_ne_top hmult_upper
  let I := Fin (wz1PaperBodyFamily F₂.family).card
  have h_card : (Fintype.card I : ENNReal) = F₂.family.enncard := by
    simp [I] <;> rfl
  have h_mass_lower : S₂.mass ≥
      F₂.family.enncard * (c * ENNReal.ofReal (delta ^ 2)) := by
    calc
      S₂.mass
        = ∑ i : I, volume (S₂.carrier i) := by
          dsimp only [I, Kakeya.Streamlined.Shading.mass] <;> rfl
      _ ≥ ∑ i : I, c * ENNReal.ofReal (delta ^ 2) :=
          Finset.sum_le_sum (fun i _ => h_carrier_vol i)
      _ = (Fintype.card I : ENNReal) * (c * ENNReal.ofReal (delta ^ 2)) := by
          have h1 : ∑ i : I, c * ENNReal.ofReal (delta ^ 2) =
              (c * ENNReal.ofReal (delta ^ 2)) * ∑ i : I, (1 : ENNReal) := by
            have h : (c * ENNReal.ofReal (delta ^ 2)) * ∑ i : I, (1 : ENNReal) =
                ∑ i : I, c * ENNReal.ofReal (delta ^ 2) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              simp
            exact h.symm
          rw [h1]
          have h2 : ∑ i : I, (1 : ENNReal) = (Fintype.card I : ENNReal) := by
            simpa using Finset.sum_ones
          rw [h2] <;> ring
      _ = F₂.family.enncard * (c * ENNReal.ofReal (delta ^ 2)) := by
          rw [h_card] <;> simp [mul_comm]
  exact le_trans h_mass_lower h_mass_upper

/-- Exponent arithmetic for the broad-set condition with δ² #𝕋₂ bound.

Given `#𝕋₂ ≤ 2μ₀·V/δ²`, the geometric condition
`4·C·(δ²·#𝕋₂)^(3/2) ≤ √(Q·τ)·V`
reduces to
`4·C·(2μ₀)^{3/2}·V^{1/2} ≤ √(Q·τ)`
(after μ₀ cancellation in the broad-mass proof).

This is a pure real-arithmetic condition independent of δ.

With the weaker δ³ bound `#𝕋₂ ≤ 2μ₀·V/δ³`, the condition becomes
`4·C·(2μ₀)^{3/2}·V^{1/2} ≤ √(Q·τ)·δ^{3/2}`
which requires V to be O(δ³), typically too restrictive.

Hence the δ² body-mass bound is essential for the broad-set deletion to work
at arbitrary union volume. -/
lemma exponent_arithmetic_reduction
    (delta : ℝ)
    (mu0 C V Q tau : ENNReal)
    (hmu0_ne_top : mu0 ≠ ⊤)
    (hC_ne_top : C ≠ ⊤)
    (hV_ne_top : V ≠ ⊤)
    (N : ENNReal)
    (hN_bound : N * ENNReal.ofReal (delta ^ 2) ≤ 2 * mu0 * V)
    (h_final : 4 * C * (2 * mu0) ^ (3 / 2 : ℝ) * V ^ (1 / 2 : ℝ) ≤
        (Q * tau) ^ (1 / 2 : ℝ)) :
    4 * C * (ENNReal.ofReal (delta ^ 2) * N) ^ (3 / 2 : ℝ) ≤
      (Q * tau) ^ (1 / 2 : ℝ) * V := by
  have h2mu_ne_top : (2 * mu0) ≠ ⊤ := ENNReal.mul_ne_top (by simp) hmu0_ne_top
  have h1 : ENNReal.ofReal (delta ^ 2) * N ≤ 2 * mu0 * V := by
    simpa [mul_comm] using hN_bound
  have h2 : (ENNReal.ofReal (delta ^ 2) * N) ^ (3 / 2 : ℝ) ≤
      (2 * mu0 * V) ^ (3 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow h1 (by norm_num)
  have h3 : (2 * mu0 * V) ^ (3 / 2 : ℝ) =
      (2 * mu0) ^ (3 / 2 : ℝ) * V ^ (3 / 2 : ℝ) :=
    ENNReal.mul_rpow_of_nonneg (2 * mu0) V (by norm_num)
  by_cases hV0 : V = 0
  · subst hV0
    have h_eq : ENNReal.ofReal (delta ^ 2) * N = 0 := by
      simpa using h1
    rw [h_eq]
    <;> simp
  have h4 : V ^ (3 / 2 : ℝ) = V ^ (1 / 2 : ℝ) * V := by
    have h5 : (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 := by norm_num
    rw [h5]
    rw [ENNReal.rpow_add (1 / 2 : ℝ) 1 hV0 hV_ne_top]
    <;> simp
  have h_goal : 4 * C * (2 * mu0) ^ (3 / 2 : ℝ) * V ^ (1 / 2 : ℝ) * V ≤
      (Q * tau) ^ (1 / 2 : ℝ) * V := by
    have h6 : 4 * C * (2 * mu0) ^ (3 / 2 : ℝ) * V ^ (1 / 2 : ℝ) ≤
        (Q * tau) ^ (1 / 2 : ℝ) := h_final
    have h7 : 4 * C * (2 * mu0) ^ (3 / 2 : ℝ) * V ^ (1 / 2 : ℝ) * V ≤
        (Q * tau) ^ (1 / 2 : ℝ) * V := by
      calc
        4 * C * (2 * mu0) ^ (3 / 2 : ℝ) * V ^ (1 / 2 : ℝ) * V
          = (4 * C * (2 * mu0) ^ (3 / 2 : ℝ) * V ^ (1 / 2 : ℝ)) * V := by ring
        _ ≤ (Q * tau) ^ (1 / 2 : ℝ) * V := by
          gcongr
          <;> exact h6
    exact h7
  calc
    4 * C * (ENNReal.ofReal (delta ^ 2) * N) ^ (3 / 2 : ℝ)
      ≤ 4 * C * ((2 * mu0 * V) ^ (3 / 2 : ℝ)) := by gcongr
    _ = 4 * C * (2 * mu0) ^ (3 / 2 : ℝ) * V ^ (3 / 2 : ℝ) := by
      rw [h3] <;> ring
    _ = 4 * C * (2 * mu0) ^ (3 / 2 : ℝ) * V ^ (1 / 2 : ℝ) * V := by
      rw [h4] <;> ring
    _ ≤ (Q * tau) ^ (1 / 2 : ℝ) * V := h_goal

/-- Subfamily cardinality ≤ full family cardinality. -/
lemma subfamily_card_le_full
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {F₂ : Kakeya.Streamlined.TubeSubfamily F} :
    F₂.family.enncard ≤ (F.card : ENNReal) := by
  have h_inj : Function.Injective F₂.embedding := F₂.embedding.inj'
  have h_card : Fintype.card (Fin F₂.family.card) ≤ Fintype.card (Fin F.card) :=
    Fintype.card_le_of_injective F₂.embedding h_inj
  have h1 : Fintype.card (Fin F₂.family.card) = F₂.family.card := by simp
  have h2 : Fintype.card (Fin F.card) = F.card := by simp
  rw [h1, h2] at h_card
  have h_card' : (F₂.family.card : ENNReal) ≤ (F.card : ENNReal) := by
    exact Nat.cast_le.mpr h_card
  have h_goal : F₂.family.enncard ≤ (F.card : ENNReal) := by
    have h_unfold : F₂.family.enncard = (F₂.family.card : ENNReal) := by
      simp [Kakeya.Streamlined.TubeFamily.enncard]
    rw [h_unfold]
    exact h_card'
  exact h_goal

/-- Exponent arithmetic with loss factor.

Given `N · δ^(loss+2) ≤ 2μ₀ · V`, the geometric condition
`4·C·(δ²·N)^(3/2) ≤ √(Q·τ)·V`
follows from
`4·C·(2μ₀)^{3/2}·V^{1/2} ≤ √(Q·τ)·δ^{3loss/2}`.

The loss factor `δ^{-3loss/2}` is the paper's integral bound exponent. -/
lemma exponent_arithmetic_reduction_with_loss
    (delta loss : ℝ)
    (hdelta_pos : 0 < delta)
    (mu0 C V Q tau : ENNReal)
    (hmu0_ne_top : mu0 ≠ ⊤)
    (hC_ne_top : C ≠ ⊤)
    (hV_ne_top : V ≠ ⊤)
    (N : ENNReal)
    (hN_bound : N * Kakeya.realRpowENN delta (loss + 2) ≤ 2 * mu0 * V)
    (h_final : 4 * C * (2 * mu0) ^ (3 / 2 : ℝ) * V ^ (1 / 2 : ℝ) ≤
        (Q * tau) ^ (1 / 2 : ℝ) * Kakeya.realRpowENN delta (3 * loss / 2)) :
    4 * C * (ENNReal.ofReal (delta ^ 2) * N) ^ (3 / 2 : ℝ) ≤
      (Q * tau) ^ (1 / 2 : ℝ) * V := by
  set d2 := ENNReal.ofReal (delta ^ 2) with hd2
  set dloss := Kakeya.realRpowENN delta loss with hdloss
  set d3loss2 := Kakeya.realRpowENN delta (3 * loss / 2) with hd3loss2

  have h_dloss_ne_zero : dloss ≠ 0 := by
    simp [dloss, Kakeya.realRpowENN, hdelta_pos.ne'] <;> positivity
  have h_dloss_ne_top : dloss ≠ ⊤ := by
    simp [dloss, Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top

  have h_loss2 : dloss * d2 = Kakeya.realRpowENN delta (loss + 2) := by
    have h_pos1 : 0 ≤ delta.rpow loss := Real.rpow_nonneg hdelta_pos.le loss
    have h1 : ENNReal.ofReal (delta.rpow loss) * ENNReal.ofReal (delta ^ 2) =
        ENNReal.ofReal (delta.rpow loss * delta ^ 2) := by
      rw [← ENNReal.ofReal_mul] <;> positivity
    have h2 : delta.rpow loss * delta ^ 2 = delta.rpow (loss + 2) := by
      have h3 : delta ^ 2 = delta.rpow 2 := by
        have h4 : delta.rpow 2 = delta ^ 2 := Real.rpow_two delta
        exact h4.symm
      rw [h3]
      have h5 : delta.rpow loss * delta.rpow 2 = delta.rpow (loss + 2) := by
        have h_add : delta ^ (loss + (2 : ℝ)) = delta ^ loss * delta ^ (2 : ℝ) :=
          Real.rpow_add hdelta_pos loss (2 : ℝ)
        exact h_add.symm
      exact h5
    have h6 : dloss * d2 = Kakeya.realRpowENN delta (loss + 2) := by
      dsimp only [dloss, d2, Kakeya.realRpowENN]
      exact h1.trans (by rw [h2])
    exact h6

  have h3loss2 : dloss ^ (3 / 2 : ℝ) = d3loss2 := by
    have h_nonneg : 0 ≤ delta.rpow loss := Real.rpow_nonneg hdelta_pos.le loss
    have h1 : (ENNReal.ofReal (delta.rpow loss)) ^ (3 / 2 : ℝ) =
        ENNReal.ofReal ((delta.rpow loss) ^ (3 / 2 : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg h_nonneg (by norm_num)
    have h2 : (delta.rpow loss) ^ (3 / 2 : ℝ) = delta.rpow (3 * loss / 2) := by
      have h3 : (delta.rpow loss) ^ (3 / 2 : ℝ) = delta.rpow (loss * (3 / 2 : ℝ)) := by
        have h_mul : delta ^ (loss * (3 / 2 : ℝ)) = (delta ^ loss) ^ (3 / 2 : ℝ) :=
          Real.rpow_mul hdelta_pos.le loss (3 / 2 : ℝ)
        exact h_mul.symm
      rw [h3]
      have h4 : loss * (3 / 2 : ℝ) = 3 * loss / 2 := by ring
      rw [h4]
    have h4 : dloss ^ (3 / 2 : ℝ) = d3loss2 := by
      dsimp only [dloss, d3loss2, Kakeya.realRpowENN]
      exact h1.trans (by rw [h2])
    exact h4

  have h1 : d2 * N ≤ (2 * mu0 * V) / dloss := by
    have h3 : N * (dloss * d2) ≤ 2 * mu0 * V := by
      have h4 : N * Kakeya.realRpowENN delta (loss + 2) = N * (dloss * d2) := by
        rw [h_loss2]
      rw [h4] at hN_bound
      exact hN_bound
    have h4 : (d2 * N) * dloss ≤ 2 * mu0 * V := by
      have h5 : (d2 * N) * dloss = N * (dloss * d2) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      rw [h5]
      exact h3
    rw [ENNReal.le_div_iff_mul_le (Or.inl h_dloss_ne_zero) (Or.inl h_dloss_ne_top)]
    exact h4

  by_cases hV0 : V = 0
  · subst hV0
    have h_eq : d2 * N = 0 := by simpa using h1
    rw [h_eq] <;> simp

  have h2 : (d2 * N) ^ (3 / 2 : ℝ) ≤
      ((2 * mu0 * V) / dloss) ^ (3 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow h1 (by norm_num)

  have h3 : ((2 * mu0 * V) / dloss) ^ (3 / 2 : ℝ) =
      (2 * mu0 * V) ^ (3 / 2 : ℝ) / dloss ^ (3 / 2 : ℝ) :=
    ENNReal.div_rpow_of_nonneg (2 * mu0 * V) dloss (by norm_num)

  have h4 : (2 * mu0 * V) ^ (3 / 2 : ℝ) =
      (2 * mu0) ^ (3 / 2 : ℝ) * V ^ (3 / 2 : ℝ) :=
    ENNReal.mul_rpow_of_nonneg (2 * mu0) V (by norm_num)

  have h5 : V ^ (3 / 2 : ℝ) = V ^ (1 / 2 : ℝ) * V := by
    have h6 : (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 := by norm_num
    rw [h6]
    rw [ENNReal.rpow_add (1 / 2 : ℝ) 1 hV0 hV_ne_top] <;> simp

  have h7_ne_zero : d3loss2 ≠ 0 := by
    simp [d3loss2, Kakeya.realRpowENN, hdelta_pos.ne'] <;> positivity
  have h7_ne_top : d3loss2 ≠ ⊤ := by
    simp [d3loss2, Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top

  set A := 4 * C * (2 * mu0) ^ (3 / 2 : ℝ) * V ^ (1 / 2 : ℝ) with hA
  have h_final2 : A ≤ (Q * tau) ^ (1 / 2 : ℝ) * d3loss2 := by
    simpa [A] using h_final

  calc
    4 * C * (d2 * N) ^ (3 / 2 : ℝ)
      ≤ 4 * C * (((2 * mu0 * V) / dloss) ^ (3 / 2 : ℝ)) := by gcongr
    _ = 4 * C * ((2 * mu0 * V) ^ (3 / 2 : ℝ) / dloss ^ (3 / 2 : ℝ)) := by
      rw [h3]
    _ = (4 * C * (2 * mu0 * V) ^ (3 / 2 : ℝ)) / dloss ^ (3 / 2 : ℝ) := by
      rw [mul_div]
    _ = (4 * C * (2 * mu0) ^ (3 / 2 : ℝ) * V ^ (3 / 2 : ℝ)) / dloss ^ (3 / 2 : ℝ) := by
      rw [h4] <;> simp [mul_assoc]
    _ = (4 * C * (2 * mu0) ^ (3 / 2 : ℝ) * V ^ (1 / 2 : ℝ) * V) / d3loss2 := by
      rw [h5, h3loss2] <;> simp [mul_assoc]
    _ = A * V / d3loss2 := by
      simp [A, mul_assoc]
    _ ≤ ((Q * tau) ^ (1 / 2 : ℝ) * d3loss2) * V / d3loss2 := by gcongr
    _ = (Q * tau) ^ (1 / 2 : ℝ) * V := by
      have h9 : ((Q * tau) ^ (1 / 2 : ℝ) * d3loss2) * V / d3loss2 =
          (Q * tau) ^ (1 / 2 : ℝ) * V := by
        have h10 : ((Q * tau) ^ (1 / 2 : ℝ) * d3loss2) * V / d3loss2 =
            ((Q * tau) ^ (1 / 2 : ℝ) * V) * d3loss2 / d3loss2 := by
          simp [mul_assoc, mul_comm, mul_left_comm]
        rw [h10]
        exact ENNReal.mul_div_cancel_right h7_ne_zero h7_ne_top
      exact h9

end Kakeya.Assouad

end
