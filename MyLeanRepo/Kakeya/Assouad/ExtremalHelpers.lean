import MyLeanRepo.Kakeya.Assouad.ExtremalInfrastructure
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement

/-!
# Helper lemmas for the WZ2 extremal extraction

Elementary order-theoretic and structural-parameter lemmas used by the
critical-exponent construction in `ExtremalCounterexamplesFromFailure`.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- For `0 < δ ≤ 1`, `δ^b ≤ δ^a` in `ENNReal` when `a ≤ b`. -/
lemma realRpowENN_antitone {δ a b : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : a ≤ b) :
    Kakeya.realRpowENN δ b ≤ Kakeya.realRpowENN δ a := by
  simp only [Kakeya.realRpowENN]
  apply ENNReal.ofReal_mono
  exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 h

/-- Strict version: `a < b` implies `δ^b < δ^a` for `0 < δ < 1`. -/
lemma realRpowENN_strict_antitone {δ a b : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (h : a < b) :
    Kakeya.realRpowENN δ b < Kakeya.realRpowENN δ a := by
  simp only [Kakeya.realRpowENN]
  have h1 : Real.rpow δ b < Real.rpow δ a :=
    Real.rpow_lt_rpow_of_exponent_gt hδ hδ1 h
  have h_pos2 : 0 < Real.rpow δ a := Real.rpow_pos_of_pos hδ a
  have h_result : ENNReal.ofReal (Real.rpow δ b) < ENNReal.ofReal (Real.rpow δ a) := by
    rw [ENNReal.ofReal_lt_ofReal_iff h_pos2]
    exact h1
  simpa [Kakeya.realRpowENN] using h_result

/--
If a configuration satisfies the structural conditions at parameter `η₁`,
and `η₁ ≤ η₂`, then it satisfies them at parameter `η₂` (weaker conditions).

For `0 < δ ≤ 1` and `η₁ ≤ η₂`:
- `δ^(-η₁) ≤ δ^(-η₂)`, so uniformity at `η₁` implies uniformity at `η₂`.
- Frostman at a smaller constant implies Frostman at a larger constant.
- `δ^η₁ ≥ δ^η₂`, so `δ^η₁`-density implies `δ^η₂`-density.
-/
lemma weaken_structural_parameter {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {η₁ η₂ : ℝ} (hη : η₁ ≤ η₂)
    {F : Kakeya.Streamlined.TubeFamily δ}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hU_uniform : U.uniformity ≤ Kakeya.realRpowENN δ (-η₁))
    (hU_frostman : U.IsFrostmanAtEveryScale (Kakeya.realRpowENN δ (-η₁)))
    (hY_dense : Y.IsLambdaDense (Kakeya.realRpowENN δ η₁)) :
    U.uniformity ≤ Kakeya.realRpowENN δ (-η₂) ∧
    U.IsFrostmanAtEveryScale (Kakeya.realRpowENN δ (-η₂)) ∧
    Y.IsLambdaDense (Kakeya.realRpowENN δ η₂) := by
  have h1 : Kakeya.realRpowENN δ (-η₁) ≤ Kakeya.realRpowENN δ (-η₂) :=
    realRpowENN_antitone hδ hδ1 (by linarith)
  have h2 : Kakeya.realRpowENN δ η₂ ≤ Kakeya.realRpowENN δ η₁ :=
    realRpowENN_antitone hδ hδ1 hη
  have h_frostman' : U.IsFrostmanAtEveryScale (Kakeya.realRpowENN δ (-η₂)) := by
    intro rho j K hK_convex hK_subset
    have h_old := hU_frostman rho j K hK_convex hK_subset
    exact h_old.trans (by gcongr)
  have h_dense' : Y.IsLambdaDense (Kakeya.realRpowENN δ η₂) := by
    have h : Kakeya.realRpowENN δ η₂ * F.toBodyFamily.mass ≤
        Kakeya.realRpowENN δ η₁ * F.toBodyFamily.mass := by gcongr
    exact h.trans hY_dense
  exact ⟨hU_uniform.trans h1, h_frostman', h_dense'⟩

/-- A downward-closed set contains every element strictly below its supremum. -/
lemma sSup_lt_mem {S : Set ℝ}
    (hS : ∀ x ∈ S, ∀ y ≤ x, y ∈ S)
    (h_nonempty : S.Nonempty)
    (_h_bdd : BddAbove S)
    {s : ℝ} (hs : s < sSup S) : s ∈ S := by
  by_contra h
  have h1 : ∀ x ∈ S, x ≤ s := by
    intro x hx
    by_contra h2
    have h3 : s < x := by linarith
    have h4 : s ∈ S := hS x hx s (by linarith)
    exact h h4
  have h2 : sSup S ≤ s := csSup_le h_nonempty h1
  linarith

/-- The admissible set is downward closed. -/
lemma Admissible.mono {s t : ℝ} (h : Admissible s) (hst : t ≤ s) :
    Admissible t := by
  intro eta heta delta₀ hdelta₀
  rcases h eta heta delta₀ hdelta₀ with
    ⟨delta, hdelta_pos, hdelta_le, F, U, Y, hdelta_pos', hdelta_one,
      hF_nonempty, hF_ball, hF_distinct, hU_uniform, hU_frostman,
      hY_dense, hY_volume⟩
  refine ⟨delta, hdelta_pos, hdelta_le, F, U, Y, hdelta_pos', hdelta_one,
    hF_nonempty, hF_ball, hF_distinct, hU_uniform, hU_frostman, hY_dense, ?_⟩
  have h_power : Kakeya.realRpowENN delta s ≤ Kakeya.realRpowENN delta t := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one hst
  exact hY_volume.trans h_power

/-- The Wolff floor implies `1/2 + ε` is not admissible for any `ε > 0`. -/
lemma wolff_not_admissible (h_wolff : WolffVolumeFloorInput) {ε : ℝ} (hε : 0 < ε) :
    ¬ Admissible (1 / 2 + ε) := by
  have hε2 : 0 < ε / 2 := by linarith
  rcases h_wolff (ε / 2) hε2 with
    ⟨eta, delta₀, heta, hdelta₀_pos, hdelta₀_one, h_floor⟩
  intro h_adm
  let delta₀' := min delta₀ (1 / 2)
  have hdelta₀'_pos : 0 < delta₀' := by positivity
  rcases h_adm eta heta delta₀' hdelta₀'_pos with
    ⟨delta, hdelta_pos, hdelta_le, F, U, Y, hdelta_pos', hdelta_one,
      hF_nonempty, hF_ball, hF_distinct, hU_uniform, hU_frostman,
      hY_dense, hY_volume⟩
  have hdelta_lt_one : delta < 1 := by
    have h : delta ≤ 1 / 2 := hdelta_le.trans (min_le_right _ _)
    linarith
  have h_lower : Kakeya.realRpowENN delta (1 / 2 + ε / 2) ≤
      MeasureTheory.volume Y.union :=
    h_floor delta hdelta_pos (hdelta_le.trans (min_le_left _ _)) F hF_nonempty hF_ball hF_distinct
      U hU_uniform hU_frostman Y hY_dense
  have h_real_power : Real.rpow delta (1 / 2 + ε) <
      Real.rpow delta (1 / 2 + ε / 2) :=
    Real.rpow_lt_rpow_of_exponent_gt hdelta_pos hdelta_lt_one (by linarith)
  have h_pos2 : 0 < Real.rpow delta (1 / 2 + ε / 2) :=
    Real.rpow_pos_of_pos hdelta_pos (1 / 2 + ε / 2)
  have h_power : Kakeya.realRpowENN delta (1 / 2 + ε) <
      Kakeya.realRpowENN delta (1 / 2 + ε / 2) := by
    simp only [Kakeya.realRpowENN]
    rw [ENNReal.ofReal_lt_ofReal_iff h_pos2]
    exact h_real_power
  have h_contra : Kakeya.realRpowENN delta (1 / 2 + ε / 2) ≤
      Kakeya.realRpowENN delta (1 / 2 + ε) := by
    calc
      Kakeya.realRpowENN delta (1 / 2 + ε / 2) ≤ volume Y.union := h_lower
      _ ≤ Kakeya.realRpowENN delta (1 / 2 + ε) := hY_volume
  exact not_le.mpr h_power h_contra

/-- Sticky failure gives some `ε₀ > 0` that is admissible. -/
lemma sticky_failure_admissible (h_not_sticky : ¬Kakeya.Streamlined.StickyInput) :
    ∃ (ε₀ : ℝ), 0 < ε₀ ∧ Admissible ε₀ := by
  have h_neg : ∃ (ε₀ : ℝ), 0 < ε₀ ∧
      ∀ (eta : ℝ), 0 < eta →
        ∀ (delta₀ : ℝ), 0 < delta₀ → delta₀ ≤ 1 →
          ∃ (delta : ℝ), 0 < delta ∧ delta ≤ delta₀ ∧
            ∃ (F : Kakeya.Streamlined.TubeFamily delta),
              ∃ (U : Kakeya.Streamlined.UniformTubeStructure F),
                ∃ (Y : Kakeya.Streamlined.TubeShading F),
                  F.Nonempty ∧ F.IsInUnitBall ∧ F.IsEssentiallyDistinct ∧
                  U.uniformity ≤ Kakeya.realRpowENN delta (-eta) ∧
                  U.IsFrostmanAtEveryScale (Kakeya.realRpowENN delta (-eta)) ∧
                  Y.IsLambdaDense (Kakeya.realRpowENN delta eta) ∧
                  MeasureTheory.volume Y.union < Kakeya.realRpowENN delta ε₀ := by
    simpa [Kakeya.Streamlined.StickyInput, Kakeya.Streamlined.StickyKakeyaHypothesis]
      using h_not_sticky
  rcases h_neg with ⟨ε₀, hε₀_pos, h_failure⟩
  refine ⟨ε₀, hε₀_pos, ?_⟩
  intro eta heta delta₀ hdelta₀
  let delta₀' := min delta₀ (1 / 2)
  have hdelta₀'_pos : 0 < delta₀' := by positivity
  have hdelta₀'_one : delta₀' ≤ 1 := by
    exact (min_le_right _ _).trans (by norm_num)
  have hdelta₀'_le : delta₀' ≤ delta₀ := min_le_left _ _
  rcases h_failure eta heta delta₀' hdelta₀'_pos hdelta₀'_one with
    ⟨delta, hdelta_pos, hdelta_le, F, U, Y, hF_nonempty, hF_ball, hF_distinct,
      hU_uniform, hU_frostman, hY_dense, hY_volume_lt⟩
  refine ⟨delta, hdelta_pos, hdelta_le.trans hdelta₀'_le, F, U, Y,
    hdelta_pos, by linarith [hdelta_le], hF_nonempty, hF_ball, hF_distinct,
    hU_uniform, hU_frostman, hY_dense, ?_⟩
  exact le_of_lt hY_volume_lt

/-- Non-admissibility of `s` gives a structural parameter `η₀` and scale
threshold `δ₀ ≤ 1` where all configs have volume `> δ^s`. -/
lemma non_admissible_spec {s : ℝ} (h : ¬ Admissible s) :
    ∃ (eta₀ : ℝ), 0 < eta₀ ∧
      ∃ (delta₀ : ℝ), 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
          ∀ (F : Kakeya.Streamlined.TubeFamily delta),
            ∀ (U : Kakeya.Streamlined.UniformTubeStructure F),
              ∀ (Y : Kakeya.Streamlined.TubeShading F),
                F.Nonempty → F.IsInUnitBall → F.IsEssentiallyDistinct →
                U.uniformity ≤ Kakeya.realRpowENN delta (-eta₀) →
                U.IsFrostmanAtEveryScale (Kakeya.realRpowENN delta (-eta₀)) →
                Y.IsLambdaDense (Kakeya.realRpowENN delta eta₀) →
                  Kakeya.realRpowENN delta s < MeasureTheory.volume Y.union := by
  by_contra h_main
  push Not at h_main
  have h_adm : Admissible s := by
    intro eta heta delta₀ hdelta₀
    let delta₀' := min delta₀ 1
    have hdelta₀'_pos : 0 < delta₀' := by positivity
    have hdelta₀'_one : delta₀' ≤ 1 := min_le_right _ _
    have h_from_main : ∃ (delta : ℝ), 0 < delta ∧ delta ≤ delta₀' ∧
        ∃ (F : Kakeya.Streamlined.TubeFamily delta),
          ∃ (U : Kakeya.Streamlined.UniformTubeStructure F),
            ∃ (Y : Kakeya.Streamlined.TubeShading F),
              F.Nonempty ∧ F.IsInUnitBall ∧ F.IsEssentiallyDistinct ∧
              U.uniformity ≤ Kakeya.realRpowENN delta (-eta) ∧
              U.IsFrostmanAtEveryScale (Kakeya.realRpowENN delta (-eta)) ∧
              Y.IsLambdaDense (Kakeya.realRpowENN delta eta) ∧
              MeasureTheory.volume Y.union ≤ Kakeya.realRpowENN delta s :=
      h_main eta heta delta₀' hdelta₀'_pos hdelta₀'_one
    rcases h_from_main with ⟨delta, hdelta_pos, hdelta_le, F, U, Y,
      hF_nonempty, hF_ball, hF_distinct, hU_uniform, hU_frostman, hY_dense, h_volume⟩
    refine ⟨delta, hdelta_pos, hdelta_le.trans (min_le_left _ _), F, U, Y,
      hdelta_pos, hdelta_le.trans hdelta₀'_one, hF_nonempty, hF_ball, hF_distinct,
      hU_uniform, hU_frostman, hY_dense, h_volume⟩
  exact h h_adm

/--
A `loss`-dense subshading has mass at least `δ^loss * F.mass`.
Combined with a lower bound on `F.mass`, this gives a lower bound on `Z.mass`.
-/
lemma dense_subshading_mass_lower {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    {Z : Kakeya.Streamlined.TubeShading F}
    {loss sigma : ℝ} (hdelta : 0 < δ)
    (hZ_dense : Z.IsLambdaDense (Kakeya.realRpowENN δ loss))
    (hF_mass : Kakeya.realRpowENN δ sigma ≤ F.toBodyFamily.mass) :
    Kakeya.realRpowENN δ (sigma + loss) ≤ Z.mass := by
  have h1 : Kakeya.realRpowENN δ (sigma + loss) =
      Kakeya.realRpowENN δ sigma * Kakeya.realRpowENN δ loss := by
    simp only [Kakeya.realRpowENN]
    have hreal : Real.rpow δ (sigma + loss) =
        Real.rpow δ sigma * Real.rpow δ loss :=
      Real.rpow_add hdelta sigma loss
    rw [hreal]
    have hpos : 0 ≤ Real.rpow δ sigma := Real.rpow_nonneg hdelta.le sigma
    exact ENNReal.ofReal_mul hpos
  have h2 : Kakeya.realRpowENN δ sigma * Kakeya.realRpowENN δ loss ≤
      F.toBodyFamily.mass * Kakeya.realRpowENN δ loss := by
    exact mul_le_mul_right' hF_mass (Kakeya.realRpowENN δ loss)
  have h3 : F.toBodyFamily.mass * Kakeya.realRpowENN δ loss ≤ Z.mass := by
    have h4 : Kakeya.realRpowENN δ loss * F.toBodyFamily.mass ≤ Z.mass := hZ_dense
    have h5 : F.toBodyFamily.mass * Kakeya.realRpowENN δ loss =
        Kakeya.realRpowENN δ loss * F.toBodyFamily.mass := by ring
    rw [h5]
    exact h4
  rw [h1]
  exact h2.trans h3

/--
Trivial multiplicity bound: the total shaded mass is at most the number of
tubes times the union volume, since each shaded piece is contained in the union.
-/
lemma shading_mass_le_card_mul_union {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    {Z : Kakeya.Streamlined.TubeShading F} :
    Z.mass ≤ F.enncard * MeasureTheory.volume Z.union := by
  have h1 : ∀ i : Fin F.card, MeasureTheory.volume (Z.carrier i) ≤
      MeasureTheory.volume Z.union := by
    intro i
    apply MeasureTheory.measure_mono
    intro x hx
    exact ⟨i, hx⟩
  calc Z.mass
    = ∑ i : Fin F.card, MeasureTheory.volume (Z.carrier i) := by rfl
  _ ≤ ∑ i : Fin F.card, MeasureTheory.volume Z.union := by
      apply Finset.sum_le_sum
      intro i _
      exact h1 i
  _ = (F.card : ENNReal) * MeasureTheory.volume Z.union := by
      rw [Finset.sum_const, Finset.card_fin]
      <;> simp [nsmul_eq_mul]
      <;> ring
  _ = F.enncard * MeasureTheory.volume Z.union := by
      have hcard : (F.card : ENNReal) = F.enncard := by
        simp [Kakeya.Streamlined.TubeFamily.enncard]
        <;> rfl
      rw [hcard]

/--
Convert a mass lower bound to a union volume lower bound using a
multiplicity bound `Z.mass ≤ M * volume(Z.union)`.
-/
lemma mass_to_union_via_multiplicity {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    {Z : Kakeya.Streamlined.TubeShading F}
    {L M : ENNReal}
    (h_mass_lower : L ≤ Z.mass)
    (h_mult : Z.mass ≤ M * MeasureTheory.volume Z.union) :
    L / M ≤ MeasureTheory.volume Z.union := by
  by_cases hM0 : M = 0
  · -- M = 0: then Z.mass ≤ 0, so L = 0, and L / M = 0
    have hZ : Z.mass = 0 := by simpa [hM0] using h_mult
    have hL : L = 0 := by simpa [hZ] using h_mass_lower
    rw [hL, hM0]
    <;> simp
  · by_cases hMtop : M = ⊤
    · -- M = ⊤: L / ⊤ = 0
      rw [hMtop]
      <;> simp
    · -- 0 < M < ⊤
      have h : L ≤ M * MeasureTheory.volume Z.union :=
        h_mass_lower.trans h_mult
      have h2 : L / M ≤ (M * MeasureTheory.volume Z.union) / M := by gcongr
      have h3 : (M * MeasureTheory.volume Z.union) / M = MeasureTheory.volume Z.union := by
        have hcomm : M * MeasureTheory.volume Z.union =
            MeasureTheory.volume Z.union * M := by ring
        rw [hcomm]
        exact ENNReal.mul_div_cancel_right hM0 hMtop
      rw [h3] at h2
      exact h2

/--
Conditional hereditary volume floor from a pointwise multiplicity bound.

If every point in `Y` has multiplicity at most `δ^(2-σ) * #F`, and
`deltaTubeVolume δ ≥ δ²`, then every `loss`-dense subshading `Z` has
union volume at least `δ^(σ+loss)`.

This reduces the hereditary floor to proving the multiplicity bound, which
is the multi-scale Wolff / balanced-cover result.
-/
lemma hereditary_floor_from_multiplicity_bound
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y Z : Kakeya.Streamlined.TubeShading F}
    (sigma loss : ℝ)
    (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (hZY : IsSubshading Z Y)
    (hF_nonempty : F.Nonempty)
    (hF_mass : F.toBodyFamily.mass = F.enncard * Kakeya.deltaTubeVolume delta)
    (hV_lower : Kakeya.deltaTubeVolume delta ≥ Kakeya.realRpowENN delta 2)
    (hZ_mass : Z.mass ≥ Kakeya.realRpowENN delta loss * F.toBodyFamily.mass)
    (hM : ∀ p, (Y.pointMultiplicity p : ENNReal) ≤
        Kakeya.realRpowENN delta (2 - sigma) * F.enncard) :
    Kakeya.realRpowENN delta (sigma + loss) ≤ MeasureTheory.volume Z.union := by
  have hZM_le : ∀ p, (Z.pointMultiplicity p : ENNReal) ≤
      Kakeya.realRpowENN delta (2 - sigma) * F.enncard := by
    intro p
    have h1 : Z.pointMultiplicity p ≤ Y.pointMultiplicity p := by
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hZY i hi
    have h2 : (Z.pointMultiplicity p : ENNReal) ≤ (Y.pointMultiplicity p : ENNReal) := by
      exact_mod_cast h1
    exact h2.trans (hM p)
  let M : ENNReal := Kakeya.realRpowENN delta (2 - sigma) * F.enncard
  have h_mass_le : Z.mass ≤ M * MeasureTheory.volume Z.union := by
    have h_lint : Z.mass = ∫⁻ p, (Z.pointMultiplicity p : ENNReal) :=
      (lintegral_pointMultiplicity Z).symm
    rw [h_lint]
    have h_indic : ∀ p, (Z.pointMultiplicity p : ENNReal) ≤
        M * Set.indicator Z.union (fun _ => (1 : ENNReal)) p := by
      intro p
      by_cases hp : p ∈ Z.union
      · have h_ind : Set.indicator Z.union (fun _ => (1 : ENNReal)) p = 1 := by
          rw [Set.indicator_of_mem hp] <;> simp
        rw [h_ind]
        simpa using hZM_le p
      · have h_none : ∀ i : Fin F.toBodyFamily.card, p ∉ Z.carrier i := by
          intro i
          intro h
          exact hp ⟨i, h⟩
        have h0 : Z.pointMultiplicity p = 0 := by
          simp [Kakeya.Streamlined.Shading.pointMultiplicity, h_none]
          <;> aesop
        have h_ind : Set.indicator Z.union (fun _ => (1 : ENNReal)) p = 0 := by
          simp [Set.indicator, hp]
        rw [h_ind, h0] <;> simp
    calc
      (∫⁻ p, (Z.pointMultiplicity p : ENNReal))
        ≤ ∫⁻ p, M * Set.indicator Z.union (fun _ => (1 : ENNReal)) p :=
          lintegral_mono h_indic
      _ = M * MeasureTheory.volume Z.union := by
        have h_union_meas : MeasurableSet Z.union := by
          have h : Z.union = ⋃ i : Fin F.toBodyFamily.card, Z.carrier i := by
            ext x
            simp [Kakeya.Streamlined.Shading.union]
            <;> tauto
          rw [h]
          exact MeasurableSet.iUnion (fun i => Z.measurable_carrier i)
        have h_meas : Measurable (Set.indicator Z.union (fun _ => (1 : ENNReal))) :=
          measurable_const.indicator h_union_meas
        have h1 : (∫⁻ p, M * Set.indicator Z.union (fun _ => (1 : ENNReal)) p) =
            M * (∫⁻ p, Set.indicator Z.union (fun _ => (1 : ENNReal)) p) := by
          exact MeasureTheory.lintegral_const_mul M h_meas
        rw [h1]
        have h2 : (∫⁻ p, Set.indicator Z.union (fun _ => (1 : ENNReal)) p) =
            MeasureTheory.volume Z.union :=
          MeasureTheory.lintegral_indicator_one h_union_meas
        rw [h2]
  have h_main : Kakeya.realRpowENN delta loss * F.toBodyFamily.mass / M ≤
      MeasureTheory.volume Z.union :=
    mass_to_union_via_multiplicity hZ_mass h_mass_le
  have h_calc : Kakeya.realRpowENN delta loss * F.toBodyFamily.mass / M =
      Kakeya.realRpowENN delta (loss + sigma - 2) * Kakeya.deltaTubeVolume delta := by
    have h_enncard_ne_zero : F.enncard ≠ 0 := by
      have h_card_pos : 0 < F.card := hF_nonempty
      have h : (F.card : ENNReal) ≠ 0 := by exact_mod_cast h_card_pos.ne'
      simpa [Kakeya.Streamlined.TubeFamily.enncard] using h
    have h_enncard_ne_top : F.enncard ≠ ⊤ := by
      simp [Kakeya.Streamlined.TubeFamily.enncard] <;> exact ENNReal.natCast_ne_top _
    set a := Kakeya.realRpowENN delta loss with ha
    set b := Kakeya.realRpowENN delta (2 - sigma) with hb
    set d := Kakeya.deltaTubeVolume delta with hd
    have h_b_ne_zero : b ≠ 0 := by
      simp [Kakeya.realRpowENN, hb] <;> positivity
    have h_b_ne_top : b ≠ ⊤ := ENNReal.ofReal_ne_top
    set denom := b * F.enncard with hdenom
    have h_denom_ne_zero : denom ≠ 0 := mul_ne_zero h_b_ne_zero h_enncard_ne_zero
    have h_denom_ne_top : denom ≠ ⊤ := ENNReal.mul_ne_top h_b_ne_top h_enncard_ne_top
    set rhs := Kakeya.realRpowENN delta (loss + sigma - 2) * d with hrhs
    have h_rpow_mul : rhs * denom = a * (F.enncard * d) := by
      simp only [hrhs, hdenom, ha, hb, hd]
      have h1 : Kakeya.realRpowENN delta (loss + sigma - 2) * Kakeya.realRpowENN delta (2 - sigma) = a := by
        simp only [Kakeya.realRpowENN, ha, hb]
        have h_nonneg : 0 ≤ Real.rpow delta (loss + sigma - 2) := Real.rpow_nonneg hdelta_pos.le _
        have h_sum : (loss + sigma - 2) + (2 - sigma) = loss := by ring
        have h_mul_real : Real.rpow delta (loss + sigma - 2) * Real.rpow delta (2 - sigma) =
            Real.rpow delta loss := by
          have h : Real.rpow delta ((loss + sigma - 2) + (2 - sigma)) =
              Real.rpow delta (loss + sigma - 2) * Real.rpow delta (2 - sigma) :=
            Real.rpow_add hdelta_pos (loss + sigma - 2) (2 - sigma)
          have h_sum2 : (loss + sigma - 2) + (2 - sigma) = loss := by ring
          rw [h_sum2] at h
          exact h.symm
        have h_enn : ENNReal.ofReal (Real.rpow delta (loss + sigma - 2)) *
            ENNReal.ofReal (Real.rpow delta (2 - sigma)) =
            ENNReal.ofReal (Real.rpow delta (loss + sigma - 2) * Real.rpow delta (2 - sigma)) := by
          exact (ENNReal.ofReal_mul (p := Real.rpow delta (loss + sigma - 2))
            (q := Real.rpow delta (2 - sigma)) h_nonneg).symm
        rw [h_enn, h_mul_real]
      calc
        (Kakeya.realRpowENN delta (loss + sigma - 2) * d) * (b * F.enncard)
          = Kakeya.realRpowENN delta (loss + sigma - 2) * b * (d * F.enncard) := by ring
        _ = a * (d * F.enncard) := by rw [h1] <;> ring
        _ = a * (F.enncard * d) := by ring
    have h_exp : a * (F.enncard * d) / denom = rhs := by
      have h2 : a * (F.enncard * d) = rhs * denom := h_rpow_mul.symm
      rw [h2]
      exact ENNReal.mul_div_cancel_right h_denom_ne_zero h_denom_ne_top
    have hM_def : M = denom := by rfl
    rw [hF_mass, hM_def]
    exact h_exp
  rw [h_calc] at h_main
  have h_final : Kakeya.realRpowENN delta (sigma + loss) ≤
      Kakeya.realRpowENN delta (loss + sigma - 2) * Kakeya.deltaTubeVolume delta := by
    have h_sum : (loss + sigma - 2) + (2 : ℝ) = sigma + loss := by ring
    have h_eq : Kakeya.realRpowENN delta (sigma + loss) =
        Kakeya.realRpowENN delta (loss + sigma - 2) * Kakeya.realRpowENN delta 2 := by
      simp only [Kakeya.realRpowENN]
      have h_nonneg1 : 0 ≤ Real.rpow delta (loss + sigma - 2) := Real.rpow_nonneg hdelta_pos.le _
      have h_nonneg2 : 0 ≤ Real.rpow delta (2 : ℝ) := Real.rpow_nonneg hdelta_pos.le _
      have h_mul : Real.rpow delta (loss + sigma - 2) * Real.rpow delta (2 : ℝ) =
          Real.rpow delta (sigma + loss) := by
        have h : Real.rpow delta (loss + sigma - 2) * Real.rpow delta (2 : ℝ) =
            Real.rpow delta ((loss + sigma - 2) + (2 : ℝ)) :=
          (Real.rpow_add hdelta_pos (loss + sigma - 2) (2 : ℝ)).symm
        rw [h, h_sum]
      have h_enn : ENNReal.ofReal (Real.rpow delta (loss + sigma - 2)) *
          ENNReal.ofReal (Real.rpow delta (2 : ℝ)) =
          ENNReal.ofReal (Real.rpow delta (loss + sigma - 2) * Real.rpow delta (2 : ℝ)) := by
        exact (ENNReal.ofReal_mul (p := Real.rpow delta (loss + sigma - 2))
          (q := Real.rpow delta (2 : ℝ)) h_nonneg1).symm
      rw [h_enn, h_mul]
    rw [h_eq]
    gcongr
  exact h_final.trans h_main

end Kakeya.Assouad
