/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.RigidBadProb
public import Kakeya.RandomTranslation.RigidEDGood

/-!
# The ED-good event for the corrected failure count

`Kakeya.rigid_ed_bad_prob_lt` in `RigidEDGood.lean` controls `Kakeya.edBadCount`, the number of
rigid copies **contained** in the `99δ`-thickening of a test tube. As established in
`RigidBadProb.lean`,
that is not the count the deterministic essential-distinctness bridge can consume: the bridge
`Kakeya.badAgainstSet_of_notED_subset_cthickening` produces a *volume-fraction* condition, and
containment is strictly stronger. Two parallel `δ`-tubes of length `1` offset by `1/2` along their
axis overlap in half their volume — so they are not essentially distinct — yet neither lies in any
`O(δ)`-thickening of the other.

This file redoes the ED conjunct for `Kakeya.edFailCount`, the volume-fraction count. Nothing in the
probabilistic architecture changes: the Chernoff chain depends on its random variable only through

* measurability — `Kakeya.measurable_edFailCount`;
* a deterministic pointwise cap — `Kakeya.edFailCount_le`;
* the `J · 𝔼[X_j] ≤ C_ED` cancellation — ported below from `lintegral_edFailCount_le`.

All three are already proved, the third being the `BadAgainstSet` form of GWZ (106). The union bound
over the test-tube net is `Kakeya.net_union_bound_lt`, reused verbatim, so the threshold is again
`rigidMED C_EDlog δ = O(log (1/δ))` and remains free of the Frostman constant.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## The Frostman cancellation for the failure count -/

/-- **`J · 𝔼[X_j] ≤ C_ED` for the failure count**, with `J = ⌈C_F⌉₊` determined by the *actual*
canonical Frostman constant. The bound is dimensional: independent of `C_F`, of `δ` and of `|s|`.
This is the port of `Kakeya.ceil_frostmanConstant_mul_lintegral_edBadCount_le`. -/
theorem ceil_frostmanConstant_mul_lintegral_edFailCount_le [Nontrivial E]
    (hn : 1 < Module.finrank ℝ E) :
    ∃ (C_ED : ENNReal) (δ₀ : NNReal), C_ED ≠ ⊤ ∧ 0 < δ₀ ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ {ι : Type*} (s : Finset ι) (T : ι → Tube δ E) (T₀ : Tube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        T₀.carrier ⊆ Metric.closedBall (0 : E) (7 / 2) →
        (⌈(ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall).toReal⌉₊ : ENNReal)
            * ∫⁻ ω, (edFailCount s T T₀ ω : ENNReal) ∂(rigidMeasure E)
          ≤ C_ED := by
  classical
  obtain ⟨C₁, δ₀₁, hC₁, hδ₀₁, hMain1⟩ := frostmanConstant_mul_card_mul_pow_le (E := E) hn
  obtain ⟨C₂, δ₀₂, hC₂, hδ₀₂, hMain2⟩ := lintegral_edFailCount_le (E := E) hn
  let cn : ENNReal := ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
  let CED : ENNReal := C₂ * (C₁ / cn) + C₂ * (C₁ / cn)
  have hcn0 : cn ≠ 0 := by
    dsimp [cn]
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt (Tube.le_volume.c_pos (Module.finrank ℝ E)))
  have hcnt : cn ≠ ⊤ := by
    dsimp [cn]
    exact ENNReal.coe_ne_top
  have hdivtop : C₁ / cn ≠ ⊤ := ENNReal.div_ne_top hC₁ hcn0
  have htermtop : C₂ * (C₁ / cn) ≠ ⊤ := ENNReal.mul_ne_top hC₂ hdivtop
  have hCEDtop : CED ≠ ⊤ := by
    dsimp [CED]
    exact ENNReal.add_ne_top.mpr ⟨htermtop, htermtop⟩
  refine ⟨CED, min δ₀₁ δ₀₂, hCEDtop, ?_, ?_⟩
  · exact lt_min hδ₀₁ hδ₀₂
  · intro δ hδ hδ_le
    have hδ₁ : δ ≤ δ₀₁ := le_trans hδ_le (min_le_left _ _)
    have hδ₂ : δ ≤ δ₀₂ := le_trans hδ_le (min_le_right _ _)
    intro ι s T T₀ hB hED hT0B
    let CF : ENNReal :=
      ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall
    let J : ENNReal := (⌈CF.toReal⌉₊ : ENNReal)
    let sc : ENNReal := (s.card : ENNReal)
    let P2 : ENNReal := (δ : ENNReal) ^ (2 * (Module.finrank ℝ E - 1))
    let I : ENNReal := ∫⁻ ω, (edFailCount s T T₀ ω : ENNReal) ∂(rigidMeasure E)
    have hCF_ne_top : CF ≠ ⊤ := by
      dsimp [CF]
      exact Tube.frostmanConstant_ne_top hδ s T hB
    have hJ : J ≤ CF + 1 := by
      dsimp [J]
      have hceil : (⌈CF.toReal⌉₊ : ℝ) ≤ CF.toReal + 1 :=
        (Nat.ceil_lt_add_one ENNReal.toReal_nonneg).le
      calc
        (⌈CF.toReal⌉₊ : ENNReal) = ENNReal.ofReal (⌈CF.toReal⌉₊ : ℝ) := by
          rw [← ENNReal.ofReal_natCast (Nat.ceil CF.toReal)]
        _ ≤ ENNReal.ofReal (CF.toReal + 1) := ENNReal.ofReal_mono hceil
        _ = ENNReal.ofReal CF.toReal + 1 := by
          rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_one]
        _ = CF + 1 := by rw [ENNReal.ofReal_toReal hCF_ne_top]
    have hb : I ≤ C₂ * sc * P2 := by
      dsimp [I, sc, P2]
      exact hMain2 hδ hδ₂ s T T₀ hT0B
    by_cases hsc0 : s.card = 0
    · have hle0 : I ≤ 0 := by
        simpa [sc, hsc0] using hb
      have hI0 : I = 0 := le_antisymm hle0 zero_le
      simp [I, hI0]
    · have hsne : s.Nonempty := Finset.card_ne_zero.mp hsc0
      let W : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody
      let B1 : ConvexSpaceBody E := ConvexSpaceBody.closedUnitBall
      have hDpos : 0 < Kakeya.densityIn s W B1 := by
        rw [Kakeya.densityIn_pos_iff]
        obtain ⟨i, hi⟩ := hsne
        refine ⟨i, hi, ?_, ?_⟩
        · have hP0 : (δ : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ 0 :=
            pow_ne_zero (Module.finrank ℝ E - 1)
              (ENNReal.coe_ne_zero.mpr (ne_of_gt hδ))
          have hcp0 : (0 : ENNReal) <
              ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
                * (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
            lt_of_le_of_ne zero_le (mul_ne_zero
              (ENNReal.coe_ne_zero.mpr (ne_of_gt (Tube.le_volume.c_pos (Module.finrank ℝ E))))
              hP0).symm
          exact lt_of_lt_of_le hcp0 (by
            simpa [W] using (Tube.le_volume (T i)))
        · exact SetLike.coe_subset_coe.mp (by
            calc
              (W i : Set E) = (T i).carrier := rfl
              _ ⊆ Metric.closedBall (0 : E) 1 := hB i hi
              _ = (B1 : Set E) := rfl)
      have hCF_one : (1 : ENNReal) ≤ CF := by
        have hFC : (1 : ENNReal) ≤ ConvexSpaceBody.frostmanConstant s W B1 :=
          ConvexSpaceBody.one_le_frostmanConstant hDpos
        simpa [CF, W, B1] using hFC
      have hsc_cf : sc ≤ CF * sc := by
        calc
          sc = (1 : ENNReal) * sc := by rw [one_mul]
          _ ≤ CF * sc := mul_le_mul hCF_one le_rfl zero_le zero_le
      have hscP : sc * P2 ≤ CF * sc * P2 := by
        calc
          sc * P2 ≤ (CF * sc) * P2 := mul_le_mul hsc_cf le_rfl zero_le zero_le
          _ = CF * sc * P2 := rfl
      have hfin : CF * sc * P2 ≤ C₁ / cn := by
        rw [ENNReal.le_div_iff_mul_le (h0 := Or.inl hcn0) (ht := Or.inl hcnt)]
        calc
          (CF * sc * P2) * cn = cn * (CF * sc * P2) := by ring
          _ ≤ C₁ := by
            simpa [CF, cn, sc, P2] using (hMain1 hδ hδ₁ s T hB hED)
      have hsc_div : sc * P2 ≤ C₁ / cn := hscP.trans hfin
      have h1 : C₂ * (CF * sc * P2) ≤ C₂ * (C₁ / cn) :=
        mul_le_mul le_rfl hfin zero_le zero_le
      have h2 : C₂ * (sc * P2) ≤ C₂ * (C₁ / cn) :=
        mul_le_mul le_rfl hsc_div zero_le zero_le
      calc
        J * I ≤ (CF + 1) * I := mul_le_mul hJ le_rfl zero_le zero_le
        _ ≤ (CF + 1) * (C₂ * sc * P2) := mul_le_mul le_rfl hb zero_le zero_le
        _ = C₂ * (CF * sc * P2) + C₂ * (sc * P2) := by ring
        _ ≤ C₂ * (C₁ / cn) + C₂ * (C₁ / cn) := add_le_add h1 h2
        _ = CED := rfl

/-! ## The Chernoff chain for the failure count -/

/-- The failure count read off the `j`-th coordinate of the product sample space. -/
def edFailCountAt {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E) (T₀ : Tube δ E)
    (J : ℕ) (j : Fin J) (ω : Fin J → unitary (E →L[ℝ] E) × E) : ℝ :=
  (edFailCount s T T₀ (ω j) : ℝ)

theorem measurable_edFailCountAt {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (T₀ : Tube δ E) (J : ℕ) (j : Fin J) :
    Measurable (edFailCountAt s T T₀ J j) :=
  (measurable_edFailCount s T T₀).comp (measurable_pi_apply j)

theorem iIndepFun_edFailCountAt {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (T₀ : Tube δ E) (J : ℕ) :
    ProbabilityTheory.iIndepFun (fun j => edFailCountAt s T T₀ J j) (rigidPiMeasure E J) := by
  unfold rigidPiMeasure edFailCountAt
  exact ProbabilityTheory.iIndepFun_pi
    (μ := fun _ : Fin J => rigidMeasure E)
    (X := fun _ : Fin J => fun y : unitary (E →L[ℝ] E) × E => (edFailCount s T T₀ y : ℝ))
    (fun _ => (measurable_edFailCount s T T₀).aemeasurable)

theorem identDistrib_edFailCountAt {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (T₀ : Tube δ E) (J : ℕ) (j₁ j₂ : Fin J) :
    ProbabilityTheory.IdentDistrib (edFailCountAt s T T₀ J j₁) (edFailCountAt s T T₀ J j₂)
      (rigidPiMeasure E J) (rigidPiMeasure E J) := by
  have hg : Measurable (fun y : unitary (E →L[ℝ] E) × E => (edFailCount s T T₀ y : ℝ)) :=
    measurable_edFailCount s T T₀
  have hmap_eval : ∀ j : Fin J, (rigidPiMeasure E J).map (Function.eval j) = rigidMeasure E := by
    intro j
    rw [rigidPiMeasure]
    exact (measurePreserving_eval (μ := fun _ : Fin J => rigidMeasure E) j).map_eq
  refine ⟨(measurable_edFailCountAt s T T₀ J j₁).aemeasurable,
          (measurable_edFailCountAt s T T₀ J j₂).aemeasurable, ?_⟩
  rw [show edFailCountAt s T T₀ J j₁ =
        (fun y : unitary (E →L[ℝ] E) × E => (edFailCount s T T₀ y : ℝ)) ∘ Function.eval j₁ by rfl]
  rw [show edFailCountAt s T T₀ J j₂ =
        (fun y : unitary (E →L[ℝ] E) × E => (edFailCount s T T₀ y : ℝ)) ∘ Function.eval j₂ by rfl]
  rw [← Measure.map_map hg (measurable_pi_apply j₁)]
  rw [← Measure.map_map hg (measurable_pi_apply j₂)]
  rw [hmap_eval j₁, hmap_eval j₂]

theorem integral_edFailCountAt {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (T₀ : Tube δ E) {J : ℕ} [NeZero J] (j : Fin J) :
    ∫ ω, edFailCountAt s T T₀ J j ω ∂(rigidPiMeasure E J)
      = ∫ y, (edFailCount s T T₀ y : ℝ) ∂(rigidMeasure E) := by
  have hg : Measurable (fun y : unitary (E →L[ℝ] E) × E => (edFailCount s T T₀ y : ℝ)) :=
    measurable_edFailCount s T T₀
  have hmap_eval : (rigidPiMeasure E J).map (Function.eval j) = rigidMeasure E := by
    rw [rigidPiMeasure]
    exact (measurePreserving_eval (μ := fun _ : Fin J => rigidMeasure E) j).map_eq
  have hmap_int :
    ∫ y, (edFailCount s T T₀ y : ℝ)
        ∂((rigidPiMeasure E J).map (Function.eval j))
      = ∫ ω, (edFailCount s T T₀ (Function.eval j ω) : ℝ)
          ∂(rigidPiMeasure E J) := by
    exact MeasureTheory.integral_map (measurable_pi_apply j).aemeasurable
      hg.aestronglyMeasurable
  change ∫ ω, (edFailCount s T T₀ (Function.eval j ω) : ℝ) ∂(rigidPiMeasure E J)
      = ∫ y, (edFailCount s T T₀ y : ℝ) ∂(rigidMeasure E)
  rw [← hmap_int]
  rw [hmap_eval]

/-- **The Chernoff tail for the failure count.** Port of `Kakeya.edBadCount_chernoff_tail`; the cap
`M` is dimensional and the hypothesis on `J` is that it does not exceed `⌈C_F⌉₊`. -/
theorem edFailCount_chernoff_tail [Nontrivial E] (hn : 1 < Module.finrank ℝ E) :
    ∃ (M : ℝ) (δ₀ : NNReal), 0 < M ∧ 0 < δ₀ ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ {ι : Type*} (s : Finset ι) (T : ι → Tube δ E) (T₀ : Tube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        T₀.carrier ⊆ Metric.closedBall (0 : E) (7 / 2) →
        ∀ (J : ℕ), 0 < J →
          (J : ℝ) ≤ (⌈(ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall).toReal⌉₊ : ℝ) →
        ∀ (S : ℝ),
          ((rigidPiMeasure E J)
              {ω | ∑ j : Fin J, edFailCountAt s T T₀ J j ω > S}).toReal
            ≤ Real.exp (10 * Real.exp 1 - S / M) := by
  classical
  obtain ⟨Cpack, δ₁, hCpack_pos, hδ₁, hCap⟩ := edFailCount_le (E := E) hn
  obtain ⟨CED, δ₂, hCED_ne_top, hδ₂, hCanc⟩ :=
    ceil_frostmanConstant_mul_lintegral_edFailCount_le (E := E) hn
  let M : ℝ := CED.toReal + (Cpack : ℝ) + 1
  have hCED_nonneg : 0 ≤ CED.toReal := by exact ENNReal.toReal_nonneg (a := CED)
  have hCpack_nonneg : 0 ≤ (Cpack : ℝ) := by exact_mod_cast (Nat.zero_le Cpack)
  have hM_pos : 0 < M := by
    dsimp [M]
    nlinarith [hCED_nonneg, hCpack_nonneg]
  refine ⟨M, min δ₁ δ₂, hM_pos, lt_min hδ₁ hδ₂, ?_⟩
  intro δ hδ hδle ι s T T₀ hSub hED hB J hJ hJle S
  have hδle₁ : δ ≤ δ₁ := le_trans hδle (min_le_left δ₁ δ₂)
  have hδle₂ : δ ≤ δ₂ := le_trans hδle (min_le_right δ₁ δ₂)
  haveI : NeZero J := ⟨hJ.ne'⟩
  have hCpm : (Cpack : ℝ) ≤ M := by
    dsimp [M]
    nlinarith [hCED_nonneg, hCpack_nonneg]
  set m : ℝ := ∫ y, (edFailCount s T T₀ y : ℝ) ∂(rigidMeasure E) with hm_def
  set X : Fin J → (Fin J → (unitary (E →L[ℝ] E) × E)) → ℝ :=
      fun j ω => edFailCountAt s T T₀ J j ω with hX
  have hmeas : ∀ j : Fin J, Measurable (X j) := fun j => by
    simpa [X] using measurable_edFailCountAt s T T₀ J j
  have hnonneg : ∀ (j : Fin J) ω, 0 ≤ X j ω := by
    intro j ω
    dsimp [X]
    exact Nat.cast_nonneg _
  have hup : ∀ (j : Fin J) ω, X j ω ≤ M := by
    intro j ω
    have hcard : edFailCount s T T₀ (ω j) ≤ Cpack := hCap hδ hδle₁ s T T₀ hB hED (ω j)
    have hcardR : (edFailCount s T T₀ (ω j) : ℝ) ≤ (Cpack : ℝ) := by exact_mod_cast hcard
    have heq : X j ω = (edFailCount s T T₀ (ω j) : ℝ) := rfl
    rw [heq]
    exact le_trans hcardR hCpm
  have hbound : ∀ j : Fin J, ∀ᵐ ω ∂(rigidPiMeasure E J),
      0 ≤ X j ω ∧ X j ω ≤ M := fun j => by
    exact Filter.Eventually.of_forall fun ω => ⟨hnonneg j ω, hup j ω⟩
  have hmean : ∫ ω, X 0 ω ∂(rigidPiMeasure E J) = m := by
    rw [hX, hm_def]
    exact integral_edFailCountAt s T T₀ (0 : Fin J)
  have hindep : ProbabilityTheory.iIndepFun X (rigidPiMeasure E J) := by
    simpa [X] using iIndepFun_edFailCountAt s T T₀ J
  have hid : ∀ j : Fin J,
      ProbabilityTheory.IdentDistrib (X j) (X 0) (rigidPiMeasure E J)
        (rigidPiMeasure E J) := fun j => by
    simpa [X] using identDistrib_edFailCountAt s T T₀ J j 0
  let I : ENNReal := ∫⁻ x, (edFailCount s T T₀ x : ENNReal) ∂(rigidMeasure E)
  let CF : ENNReal := ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall
  let CFn : ℕ := ⌈CF.toReal⌉₊
  have hJle2 : (J : ℝ) ≤ (CFn : ℝ) := by
    simpa [CFn] using hJle
  have hcanc1 : (CFn : ENNReal) * I ≤ CED := by
    simpa [CFn] using hCanc hδ hδle₂ s T T₀ hSub hED hB
  have hm_nonneg : 0 ≤ m := by
    dsimp [m]
    exact MeasureTheory.integral_nonneg fun Z => Nat.cast_nonneg _
  have hint_ae : 0 ≤ᵐ[rigidMeasure E] (fun r : unitary (E →L[ℝ] E) × E =>
      (edFailCount s T T₀ r : ℝ)) :=
    Filter.Eventually.of_forall fun r => Nat.cast_nonneg _
  have hint_int : Integrable (fun y : unitary (E →L[ℝ] E) × E => (edFailCount s T T₀ y : ℝ))
      (rigidMeasure E) := by
    refine MeasureTheory.Integrable.of_bound
      (f := fun y : unitary (E →L[ℝ] E) × E => (edFailCount s T T₀ y : ℝ)) ?_ (Cpack : ℝ) ?_
    · exact (measurable_edFailCount s T T₀).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y => by
        have hv : edFailCount s T T₀ y ≤ Cpack := hCap hδ hδle₁ s T T₀ hB hED y
        have hvR : (edFailCount s T T₀ y : ℝ) ≤ (Cpack : ℝ) := by exact_mod_cast hv
        have hnn0 : 0 ≤ (edFailCount s T T₀ y : ℝ) := Nat.cast_nonneg _
        simpa [abs_of_nonneg hnn0] using hvR
  have hbridge : ENNReal.ofReal m = I := by
    calc
      ENNReal.ofReal m
          = ∫⁻ y, ENNReal.ofReal ((edFailCount s T T₀ y : ℝ)) ∂(rigidMeasure E) := by
              rw [hm_def]
              exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_int hint_ae
      _ = I := by
              dsimp [I]
              apply lintegral_congr
              intro y
              rw [ENNReal.ofReal_natCast]
  have hof : ENNReal.ofReal ((CFn : ℝ) * m) ≤ CED := by
    calc
      ENNReal.ofReal ((CFn : ℝ) * m)
          = ENNReal.ofReal (CFn : ℝ) * ENNReal.ofReal m := by
              rw [ENNReal.ofReal_mul (by exact_mod_cast (Nat.zero_le CFn))]
      _ = (CFn : ENNReal) * ENNReal.ofReal m := by rw [ENNReal.ofReal_natCast]
      _ = (CFn : ENNReal) * I := by rw [hbridge]
      _ ≤ CED := hcanc1
  have h_real : (CFn : ℝ) * m ≤ CED.toReal := by
    have hmono := ENNReal.toReal_mono hCED_ne_top hof
    rw [ENNReal.toReal_ofReal (mul_nonneg (by exact_mod_cast (Nat.zero_le CFn)) hm_nonneg)] at hmono
    exact hmono
  have hJle_mul : (J : ℝ) * m ≤ (CFn : ℝ) * m :=
    (mul_le_mul_of_nonneg_right hJle2 hm_nonneg)
  have hJm : (J : ℝ) * m < M := by
    have hCedR : CED.toReal < M := by
      dsimp [M]
      nlinarith [hCpack_nonneg]
    nlinarith [hJle_mul, h_real, hCedR]
  have hmM : m ≤ M := by
    have h1 : (1 : ℝ) ≤ (J : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne J))
    have hle_m : m ≤ (J : ℝ) * m := by
      have htmp := mul_le_mul_of_nonneg_right h1 hm_nonneg
      simpa using htmp
    linarith [hJm, hle_m]
  simpa [X, M] using
    Probability.lemma_A1_case_lt (P := rigidPiMeasure E J) (N := J) (X := X)
      hmeas M hM_pos m hm_nonneg hmM hbound hmean hindep hid S hJm

/-! ## The ED-good event for the failure count -/

/-- **The ED failure-bad event has probability below `1/4`.**

Port of `Kakeya.rigid_ed_bad_prob_lt` to `Kakeya.edFailCount`. The threshold
`rigidMED C_EDlog δ` is `O(log (1/δ))` and free of the Frostman constant. This is the version the
deterministic bridge `Kakeya.isEDUpToMult_rigidProduct_of_net_good` consumes. -/
theorem rigid_edFail_bad_prob_lt [Nontrivial E] (hn : 1 < Module.finrank ℝ E) :
    ∃ C_EDlog : ℝ, 0 < C_EDlog ∧
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type*} (s : Finset ι) (T : ι → Tube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        ∀ (J : ℕ), 0 < J →
          (J : ℝ) ≤ (⌈(ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall).toReal⌉₊ : ℝ) →
          ∃ NetT : Finset (Tube δ E),
            (∀ T₀ ∈ NetT, T₀.carrier ⊆ Metric.closedBall (0 : E) (7 / 2)) ∧
            (∀ T₀ : Tube δ E, T₀.carrier ⊆ Metric.closedBall (0 : E) 2 →
              ∃ T₀' ∈ NetT,
                T₀.carrier ⊆ Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier) ∧
            rigidPiMeasure E J
                {ω : Fin J → unitary (E →L[ℝ] E) × E |
                  ∃ T₀ ∈ NetT, ((rigidMED C_EDlog δ : ℕ) : ℝ)
                    < ∑ j : Fin J, edFailCountAt s T T₀ J j ω}
              < ENNReal.ofReal (1 / 4) := by
  classical
  obtain ⟨M, δ₀, hM, hδ₀, hTail⟩ := edFailCount_chernoff_tail (E := E) hn
  refine ⟨M * edNetCalibration E, mul_pos hM edNetCalibration_pos, ?_⟩
  have hδ₀pos : (0 : ℝ) < (δ₀ : ℝ) := by exact_mod_cast hδ₀
  have hlt1 : ∀ᶠ (x : ℝ) in 𝓝[>] (0 : ℝ), x < (1 : ℝ) := by
    refine Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)) ?_
    intro x hx
    exact hx.2
  have hle₀ : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), δ ≤ δ₀ := by
    have hx : ∀ᶠ (x : ℝ) in 𝓝[>] (0 : ℝ), x ≤ (δ₀ : ℝ) := by
      refine Filter.eventually_of_mem (Ioo_mem_nhdsGT hδ₀pos) ?_
      intro x hx
      exact le_of_lt hx.2
    filter_upwards [nnreal_eventually_of_real_eventually hx] with δ hx
    exact_mod_cast hx
  filter_upwards [self_mem_nhdsWithin, nnreal_eventually_of_real_eventually hlt1,
      hle₀] with δ hδpos hδlt hδle₀
  intro ι s T hSub hPairwise_J J hJ hJle
  have hδltOne : δ < 1 := by exact_mod_cast hδlt
  have hδleOneR : (δ : ℝ) ≤ 1 := le_of_lt hδlt
  obtain ⟨NetT, hcard, hNetB, _hvol, happrox⟩ :=
    Kakeya.exists_thin_tube_net (E := E) hδpos hδltOne
  let S : ℝ := ((rigidMED (M * edNetCalibration E) δ : ℕ) : ℝ)
  let Ω := Fin J → (unitary (E →L[ℝ] E) × E)
  let μ : Measure Ω := rigidPiMeasure E J
  have hμuniv : μ Set.univ = 1 := by
    simpa [μ] using
      (inferInstance : IsProbabilityMeasure (rigidPiMeasure E J)).measure_univ
  haveI : IsFiniteMeasure μ := by
    constructor
    rw [hμuniv]
    exact ENNReal.coe_lt_top
  let BadOf : Tube δ E → Set Ω :=
    fun T₀ => {ω | S < ∑ j : Fin J, edFailCountAt s T T₀ J j ω}
  let B : Set Ω := ⋃ T₀ ∈ NetT, BadOf T₀
  let EXP : ℝ := Real.exp (10 * Real.exp 1 - S / M)
  have hTailB : ∀ T₀ ∈ NetT, (μ (BadOf T₀)).toReal ≤ EXP := by
    intro T₀ hT₀
    have h7 : T₀.carrier ⊆ Metric.closedBall (0 : E) (7 / 2) := hNetB T₀ hT₀
    simpa [μ, BadOf, EXP] using
      (hTail hδpos hδle₀ s T T₀ hSub hPairwise_J h7 J hJ hJle S)
  have hsum : (∑ T₀ ∈ NetT, (μ (BadOf T₀)).toReal) ≤ (NetT.card : ℝ) * EXP := by
    calc
      (∑ T₀ ∈ NetT, (μ (BadOf T₀)).toReal) ≤ ∑ T₀ ∈ NetT, EXP := by
        exact Finset.sum_le_sum (fun T₀ hT₀ => hTailB T₀ hT₀)
      _ = (NetT.card : ℝ) * EXP := by
        simp [Finset.sum_const]
  have htoRealB : (μ B).toReal ≤ (NetT.card : ℝ) * EXP := by
    have hBunion : μ B ≤ ∑ T₀ ∈ NetT, μ (BadOf T₀) :=
      measure_biUnion_finset_le NetT BadOf
    have hSn : (∑ T₀ ∈ NetT, μ (BadOf T₀)) ≠ (⊤ : ENNReal) := by
      rw [ENNReal.sum_ne_top]
      intro T₀ hT₀
      exact measure_ne_top μ (BadOf T₀)
    calc
      (μ B).toReal ≤ (∑ T₀ ∈ NetT, μ (BadOf T₀)).toReal :=
        ENNReal.toReal_mono hSn hBunion
      _ = ∑ T₀ ∈ NetT, (μ (BadOf T₀)).toReal := by
        exact ENNReal.toReal_sum (fun T₀ hT₀ => measure_ne_top μ (BadOf T₀))
      _ ≤ (NetT.card : ℝ) * EXP := hsum
  have hbelow : (NetT.card : ℝ) * EXP < 1 / 10 := by
    have hmono : (NetT.card : ℝ) * EXP ≤
        (netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E))) * EXP :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    have hU : (netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E))) * EXP < 1 / 10 := by
      simpa [S, EXP] using
        (net_union_bound_lt (M := M) (A := edNetCalibration E) hM le_rfl hδpos hδleOneR)
    exact lt_of_le_of_lt hmono hU
  have h1_10 : (μ B).toReal < 1 / 10 := lt_of_le_of_lt htoRealB hbelow
  refine ⟨NetT, hNetB, happrox, ?_⟩
  have hset : {ω : Ω | ∃ T₀ ∈ NetT, S < ∑ j : Fin J, edFailCountAt s T T₀ J j ω} = B := by
    ext ω
    simp [B, BadOf]
  rw [hset]
  have hBnt : μ B ≠ (⊤ : ENNReal) := measure_ne_top μ B
  have hB_eq : ENNReal.ofReal (μ B).toReal = μ B := ENNReal.ofReal_toReal hBnt
  rw [← hB_eq]
  have hq : (1 / 10 : ℝ) < 1 / 4 := by norm_num
  have hmu14 : (μ B).toReal < 1 / 4 := lt_trans h1_10 hq
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 4)).mpr hmu14

end

end Kakeya

end
