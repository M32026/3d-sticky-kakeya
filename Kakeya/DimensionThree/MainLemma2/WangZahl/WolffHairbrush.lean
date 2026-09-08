/-
Wolff's hairbrush argument: Wang--Zahl Proposition 1.10 (`WolffHairbrush`).

Source: `blueprint/src/WZ2/250224e_K3.tex`, Appendix `WolffHairbrushSec`
(lines 5730--5765), where the proposition is restated in the *expanded* form

  For all `eps > 0` there exist `kappa, eta > 0` such that for all `delta > 0`:
  if `(T,Y)_delta` is `delta^eta`-dense with `CKT(T) <= delta^{-eta}` and
  `FS(T) <= delta^{-eta}`, then

      |union of Y(T)| >= kappa * delta^{3/2 + eps} * (#T)^{1/2}.        (*)

`WolffHairbrushEstimate` below is exactly (*), restricted to `delta <= 1`
(for `delta > 1` and nonempty `T` the hypotheses are already contradictory,
see `assertionD_half_zero_of_hairbrush`).

This file proves the bridge `(*) => AssertionD (1/2) 0`, i.e. that the source's
expanded form really is Assertion `D(1/2, 0)` in the sense of Definition 1.5.
The bridge is the two-sided comparison `|T| ~ delta^2` for a `delta`-tube of
`R^3`, via `Tube.volume_carrier_le`.
-/
module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.SigmaCalculus
public import Kakeya.DimensionThree.Plank.SlabTube
public import Kakeya.DimensionThree.MainLemma2.WangZahl.SlabGeometry
public import Kakeya.DimensionThree.MainLemma2.WangZahl.EquivDE

@[expose] public section

open MeasureTheory Metric

namespace Kakeya.WangZahl

noncomputable section

universe u

/-! ### The source's expanded form of Proposition 1.10 -/

/-- Wang--Zahl Proposition 1.10 in the expanded form stated in Appendix
`WolffHairbrushSec` of the source:

`|∪ Y(T)| ≥ κ δ^{3/2+ε} (#T)^{1/2}`

for every `δ^η`-dense family of essentially distinct `δ`-tubes in the unit ball
of `R^3` whose Katz--Tao convex Wolff and Frostman slab Wolff constants are at
most `δ^{-η}`.

The source says "for all `δ > 0`"; we only ask for `δ ≤ 1`, which is no loss:
a `δ`-tube contained in the unit ball forces `δ ≤ 1` once the family is
nonempty, and the `δ > 1` case of Assertion `D` is vacuous for the same
reason. -/
def WolffHairbrushEstimate : Prop :=
  ∀ ε > (0 : ℝ), ∃ κ : NNReal, ∃ η : ℝ, 0 < κ ∧ 0 < η ∧
    ∀ (δ : NNReal), 0 < δ → δ ≤ 1 →
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        IsTubeShadingFamily s T →
        IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ →
        katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        frostmanSlabWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        (κ : ENNReal) * (δ : ENNReal) ^ ((3 : ℝ) / 2 + ε) *
            (s.card : ENNReal) ^ ((1 : ℝ) / 2) ≤
          volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)

/-! ### `|T| ≤ 12 δ²` for a `δ`-tube of `R^3` with `δ ≤ 1` -/

/-- The common tube volume of Definition 1.5 obeys `|T| ≤ 12 δ²` for `δ ≤ 1`.
This is `Tube.volume_carrier_le` (`|T| ≤ 8δ²(1/2+δ)`) applied to the model
tube. -/
lemma tubeVolume_le {δ : NNReal} (hδ1 : δ ≤ 1) :
    tubeVolume δ ≤ 16 * (δ : ENNReal) ^ 2 := by
  have hδ1E : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  refine (Tube.volume_carrier_le (modelTube δ)).trans ?_
  have hhalf : (1 / 2 : ENNReal) ≤ 1 := by simp
  have hb : (1 / 2 + (δ : ENNReal)) ≤ 2 := by
    calc (1 / 2 + (δ : ENNReal)) ≤ 1 + 1 := add_le_add hhalf hδ1E
      _ = 2 := by norm_num
  calc 8 * (δ : ENNReal) ^ 2 * (1 / 2 + (δ : ENNReal))
      ≤ 8 * (δ : ENNReal) ^ 2 * 2 := by gcongr
    _ = 16 * (δ : ENNReal) ^ 2 := by ring

/-- `|T|^{3/4} ≤ 7 δ^{3/2}` for `δ ≤ 1`: the exact power of the tube volume
that appears in Assertion `D(1/2, ω)`.  The constant is `12^{3/4} ≤ 7`
(`12³ = 1728 ≤ 2401 = 7⁴`). -/
lemma tubeVolume_rpow_three_quarters_le {δ : NNReal} (hδ1 : δ ≤ 1) :
    (tubeVolume δ) ^ ((3 : ℝ) / 4) ≤ 8 * (δ : ENNReal) ^ ((3 : ℝ) / 2) := by
  have h1 : (tubeVolume δ) ^ ((3 : ℝ) / 4) ≤ (16 * (δ : ENNReal) ^ 2) ^ ((3 : ℝ) / 4) :=
    ENNReal.rpow_le_rpow (tubeVolume_le hδ1) (by norm_num)
  refine h1.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 3 / 4)]
  have hpow : ((δ : ENNReal) ^ 2) ^ ((3 : ℝ) / 4) = (δ : ENNReal) ^ ((3 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast (δ : ENNReal) 2, ← ENNReal.rpow_mul]
    norm_num
  rw [hpow]
  gcongr
  -- `16 ^ (3/4) = 8`.
  have e16 : (16 : ENNReal) ^ ((3 : ℝ) / 4) = ((2 : ENNReal) ^ (3 : ℕ)) := by
    have h2 : (16 : ENNReal) = (2 : ENNReal) ^ (4 : ℕ) := by norm_num
    rw [h2, ← ENNReal.rpow_natCast (2 : ENNReal) 4, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_natCast (2 : ENNReal) 3]
    norm_num
  rw [e16]
  norm_num

/-! ### The bridge: the source's expanded form is `D(1/2, 0)` -/

/-- The algebraic identity behind the bridge: the `sigma = 1/2` currency factor
of Assertion `D` turns `(#T)|T|` into `(#T)^{1/2}|T|^{3/4}`. -/
lemma card_mul_vol_mul_currency_rpow {N V : ENNReal} (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (hV0 : V ≠ 0) (hVtop : V ≠ ⊤) :
    N * V * ((N * V ^ ((1 : ℝ) / 2)) ^ (-(1 / 2) : ℝ))
      = N ^ ((1 : ℝ) / 2) * V ^ ((3 : ℝ) / 4) := by
  have hVh0 : V ^ ((1 : ℝ) / 2) ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hV0) hVtop).ne'
  rw [ENNReal.mul_rpow_of_ne_zero hN0 hVh0]
  have hVV : (V ^ ((1 : ℝ) / 2)) ^ (-(1 / 2) : ℝ) = V ^ (-(1 / 4) : ℝ) := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hVV]
  have hN : N = N ^ (1 : ℝ) := by simp
  have hV : V = V ^ (1 : ℝ) := by simp
  calc N * V * (N ^ (-(1 / 2) : ℝ) * V ^ (-(1 / 4) : ℝ))
      = (N ^ (1 : ℝ) * N ^ (-(1 / 2) : ℝ)) * (V ^ (1 : ℝ) * V ^ (-(1 / 4) : ℝ)) := by
        rw [← hN, ← hV]; ring
    _ = N ^ ((1 : ℝ) + -(1 / 2)) * V ^ ((1 : ℝ) + -(1 / 4)) := by
        rw [ENNReal.rpow_add _ _ hN0 hNtop, ENNReal.rpow_add _ _ hV0 hVtop]
    _ = N ^ ((1 : ℝ) / 2) * V ^ ((3 : ℝ) / 4) := by norm_num

/-- **Wang--Zahl Proposition 1.10 implies `D(1/2, 0)`.**

The only content beyond bookkeeping is the tube-volume comparison
`|T|^{3/4} ≤ 8 δ^{3/2}` for `δ ≤ 1` (`tubeVolume_rpow_three_quarters_le`),
which is what turns the source's `δ^{3/2+ε}(#T)^{1/2}` into the
`(#T)|T| X^{-1/2}` of Definition 1.5, `X = (#T)|T|^{1/2}`. -/
theorem assertionD_half_zero_of_hairbrush (H : WolffHairbrushEstimate.{u}) :
    AssertionD.{u} (1 / 2) 0 := by
  intro ε hε
  obtain ⟨κ, η, hκ, hη, hH⟩ := H ε hε
  refine ⟨κ / 8, η, by positivity, hη, ?_⟩
  intro δ hδ ι s T hfamily hdense hm hell
  by_cases hs : s.Nonempty
  · by_cases hδ1 : δ ≤ 1
    · have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
      have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
      have hV := tubeVolume_pos_and_ne_top hδ
      set N : ENNReal := (s.card : ENNReal) with hNdef
      have hN0 : N ≠ 0 := by
        simpa [hNdef] using (Finset.card_pos.mpr hs).ne'
      have hNtop : N ≠ ⊤ := by simp [hNdef]
      have hkey := card_mul_vol_mul_currency_rpow (V := tubeVolume δ) hN0 hNtop
        hV.1.ne' hV.2
      have hmain := hH δ hδ hδ1 s T hfamily hdense hm hell
      have hcoe : ((κ / 8 : NNReal) : ENNReal) * 8 = (κ : ENNReal) := by
        rw [show ((8 : ENNReal)) = ((8 : NNReal) : ENNReal) by simp, ← ENNReal.coe_mul]
        norm_num
      calc ((κ / 8 : NNReal) : ENNReal) * (δ : ENNReal) ^ (0 + ε) * N * tubeVolume δ *
              ((N * (tubeVolume δ) ^ (1 / 2 : ℝ)) ^ (-(1 / 2) : ℝ))
          = ((κ / 8 : NNReal) : ENNReal) * (δ : ENNReal) ^ ε *
              (N ^ ((1 : ℝ) / 2) * (tubeVolume δ) ^ ((3 : ℝ) / 4)) := by
            rw [zero_add, ← hkey]; ring
        _ ≤ ((κ / 8 : NNReal) : ENNReal) * (δ : ENNReal) ^ ε *
              (N ^ ((1 : ℝ) / 2) * (8 * (δ : ENNReal) ^ ((3 : ℝ) / 2))) := by
            gcongr
            exact tubeVolume_rpow_three_quarters_le hδ1
        _ = (((κ / 8 : NNReal) : ENNReal) * 8) *
              ((δ : ENNReal) ^ ε * (δ : ENNReal) ^ ((3 : ℝ) / 2)) * N ^ ((1 : ℝ) / 2) := by
            ring
        _ = (κ : ENNReal) * (δ : ENNReal) ^ ((3 : ℝ) / 2 + ε) * N ^ ((1 : ℝ) / 2) := by
            rw [hcoe, ← ENNReal.rpow_add _ _ hδ0E hδtopE]
            rw [show ε + (3 : ℝ) / 2 = (3 : ℝ) / 2 + ε by ring]
        _ ≤ volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := hmain
    · have hm1 : 1 ≤ katzTaoConvexWolffConstant s T :=
        one_le_katzTaoConvexWolffConstant_of_nonempty hδ s T hs
      have hδ_gt : (1 : ENNReal) < (δ : ENNReal) := by
        exact_mod_cast lt_of_not_ge hδ1
      have hpow_lt : (δ : ENNReal) ^ (-η) < 1 :=
        ENNReal.rpow_lt_one_of_one_lt_of_neg hδ_gt (by linarith)
      exact ((not_lt_of_ge (hm1.trans hm)) hpow_lt).elim
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst hs0
    simp [iUnionShade_empty]

/-! ### The geometric decomposition supplied by the hairbrush argument -/

/-- The output of the geometric half of the source proof of Proposition 1.10
(Appendix `WolffHairbrushSec`), stripped of the exponent bookkeeping.

After the standard reductions the source produces a scale `θ ∈ [δ, 1]`, a
`δ^{Cη}`-dense refinement `T' ⊆ T`, and a *balanced partitioning cover* `T_θ`
of `T'` by `θ`-tubes.  Writing `part j ⊆ T'` for the class of the `θ`-tube
`parent j` and `cnt j = #(part j)`, the source establishes

* `part j ⊆ {T ∈ 𝕋 : T ⊆ parent j}`
  (the class of a `θ`-tube consists of `δ`-tubes it contains);
* `#T ⪅ δ^{-Cη} ∑_j cnt j`
  (the classes cover the refinement, and the refinement keeps a
  `δ^{Cη}`-fraction of the family);
* `|∪ Y(T)| = ∑_j |∪_{T ∈ part j} Y(T)| ⪆ δ^{Cη} δ^{3/2} θ^{1/2}
   ∑_j (cnt j)^{1/2}`
  (the displayed equation `broadAtScaleTheta` combined with Wolff's hairbrush
  bound for the `2`-broad rescaled family `T^{T_θ}` of `δ/θ`-tubes).

Note that only an *inequality* `#T ≤ δ^{-ε/8} ∑_j cnt j` is demanded, not the
partition identity: the source's cover partitions the refinement `T'`, not `T`.

The `δ^{Cη}` losses are recorded here as the fixed budgets `δ^{-(ε/8)}` and
`δ^{ε/2}`; this is no loss of generality, since `η` may be taken as small as
one likes (shrinking `η` only strengthens the hypotheses of the assertion).

**Note on the source.** The displayed hairbrush bound in `WolffHairbrushSec`
reads `|∪ Y^{T_θ}| ≳ δ^{5η}(δ/θ)^{1/2}((δ/θ)(#T^{T_θ}))^{1/2}`, whose right
side is `(δ/θ)(#T^{T_θ})^{1/2}`; at the extremal count `#T^{T_θ} = (δ/θ)^{-2}`
that is `≍ 1`, which is false.  The intended factor is the tube *volume*
`(δ/θ)^2`, giving `(δ/θ)^{3/2}(#T^{T_θ})^{1/2}`; only with that reading does
the source's *next* display, `δ^{3/2}θ^{1/2}∑(#T^{T_θ})^{1/2}`, follow after
undoing the `θ`-rescaling (which multiplies volumes by `θ^2`).  The form
recorded above is the corrected one. -/
def HairbrushDecomposition : Prop :=
  ∀ ε > (0 : ℝ), ∃ κ : NNReal, ∃ η : ℝ, 0 < κ ∧ 0 < η ∧
    ∀ (δ : NNReal), 0 < δ → δ ≤ 1 →
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        IsTubeShadingFamily s T →
        IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ →
        katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        frostmanSlabWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        ∃ θ : NNReal, 0 < θ ∧ θ ≤ 1 ∧
          ∃ (J : Type u) (P : Finset J) (parent : J → Tube θ Space3) (part : J → Finset ι),
            (∀ j ∈ P, part j ⊆
              @Finset.filter ι (fun i => (T i).carrier ⊆ (parent j).carrier)
                (Classical.decPred _) s) ∧
            (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 8)) *
              (∑ j ∈ P, ((part j).card : ENNReal)) ∧
            (κ : ENNReal) * (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
                (θ : ENNReal) ^ ((1 : ℝ) / 2) *
                (∑ j ∈ P, ((part j).card : ENNReal) ^ ((1 : ℝ) / 2)) ≤
              volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)

/-- **The slab count.**  The last sentence of the source proof of Proposition
1.10: a `θ`-tube `R` sits inside a slab `W` of thickness `θ` (intersected with
the unit ball, so `|W| ≲ θ`), and the Frostman slab Wolff constant counts the
tubes of the family contained in `W`.  Hence

`#{T ∈ 𝕋 : T ⊆ R} ≤ C θ FS(𝕋) (#𝕋)`.

This is the same missing construction that blocks `exists_currencyLowerBound`
in `SourcePropositions.lean`: a `SlabTestSet` containing a prescribed tube of
the unit ball, together with the volume bound `|W| ≲ W.thickness`. -/
def SlabTubeCount : Prop :=
  ∃ C : NNReal, 1 ≤ C ∧
    ∀ {δ : NNReal}, 0 < δ → δ ≤ 1 →
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        IsTubeShadingFamily s T →
        ∀ {θ : NNReal}, 0 < θ → θ ≤ 1 → ∀ R : Tube θ Space3,
          ((@Finset.filter ι (fun i => (T i).carrier ⊆ R.carrier)
            (Classical.decPred _) s).card : ENNReal) ≤
            (C : ENNReal) * (θ : ENNReal) * frostmanSlabWolffConstant s T *
              (s.card : ENNReal)

/-- `a ≤ a^{1/2} b^{1/2}` whenever `a ≤ b` and `a ≠ ⊤`. -/
lemma le_rpow_half_mul_rpow_half {a b : ENNReal} (hab : a ≤ b) (ha : a ≠ ⊤) :
    a ≤ a ^ ((1 : ℝ) / 2) * b ^ ((1 : ℝ) / 2) := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  · calc a = a ^ ((1 : ℝ) / 2) * a ^ ((1 : ℝ) / 2) := by
          rw [← ENNReal.rpow_add _ _ ha0 ha]; norm_num
      _ ≤ a ^ ((1 : ℝ) / 2) * b ^ ((1 : ℝ) / 2) := by gcongr

/-- The exponent bookkeeping of the source proof of Proposition 1.10: the
`θ`-dependence cancels between the class-count bound and the hairbrush bound,
leaving `δ^{3/2+ε}(#T)^{1/2}`.

The cancellation is the elementary
`∑_j (cnt j)^{1/2} ≥ (∑_j cnt j) / (max_j cnt j)^{1/2}` applied with
`∑_j cnt j = #T` and `cnt j ≤ C θ FS(T)(#T) ≤ C δ^{-ε/2} θ (#T)`. -/
theorem wolffHairbrushEstimate_of_decomposition
    (HD : HairbrushDecomposition.{u}) (SC : SlabTubeCount.{u}) :
    WolffHairbrushEstimate.{u} := by
  intro ε hε
  obtain ⟨κ, η, hκ, hη, hH⟩ := HD ε hε
  obtain ⟨C, hC1, hSC⟩ := SC
  have hC0 : (0 : NNReal) < C := lt_of_lt_of_le zero_lt_one hC1
  have hC1E : (1 : ENNReal) ≤ (C : ENNReal) := by exact_mod_cast hC1
  set η' : ℝ := min η (ε / 8) with hη'def
  have hη' : 0 < η' := lt_min hη (by linarith)
  have hη'η : η' ≤ η := min_le_left _ _
  have hη'ε : η' ≤ ε / 8 := min_le_right _ _
  refine ⟨κ / C, η', by positivity, hη', ?_⟩
  intro δ hδ hδ1 ι s T hfamily hdense hm hell
  have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
  have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1E : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  -- weaken the hypotheses from `η'` to `η`
  have hdense₀ : IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ := by
    rw [IsDense] at hdense ⊢
    refine (mul_le_mul_right' ?_ _).trans hdense
    exact_mod_cast Real.rpow_le_rpow_of_exponent_ge (NNReal.coe_pos.mpr hδ) hδ1R hη'η
  have hpowη : (δ : ENNReal) ^ (-η') ≤ (δ : ENNReal) ^ (-η) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδ1E (by linarith)
  obtain ⟨θ, hθ0, hθ1, J, P, parent, part, hpart, hdeficit, hvol⟩ :=
    hH δ hδ hδ1 s T hfamily hdense₀ (hm.trans hpowη) (hell.trans hpowη)
  rcases Nat.eq_zero_or_pos s.card with hcard0 | hcard
  · simp [hcard0]
  set N : ENNReal := (s.card : ENNReal) with hNdef
  have hN0 : N ≠ 0 := by simpa [hNdef] using hcard.ne'
  have hNtop : N ≠ ⊤ := by simp [hNdef]
  set S : ENNReal := ∑ j ∈ P, ((part j).card : ENNReal) ^ ((1 : ℝ) / 2) with hSdef
  set M : ENNReal := (C : ENNReal) * (δ : ENNReal) ^ (-(ε / 8)) * (θ : ENNReal) * N with hMdef
  -- the class-count bound, from the slab count and the Frostman slab hypothesis
  have hcnt : ∀ j ∈ P, ((part j).card : ENNReal) ≤ M := by
    intro j hj
    have h1 : ((part j).card : ENNReal) ≤
        ((@Finset.filter ι (fun i => (T i).carrier ⊆ (parent j).carrier)
          (Classical.decPred _) s).card : ENNReal) := by
      exact_mod_cast Finset.card_le_card (hpart j hj)
    have h2 := hSC hδ hδ1 s T hfamily hθ0 hθ1 (parent j)
    have h3 : (δ : ENNReal) ^ (-η') ≤ (δ : ENNReal) ^ (-(ε / 8)) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδ1E (by linarith)
    calc ((part j).card : ENNReal) ≤ _ := h1
      _ ≤ (C : ENNReal) * (θ : ENNReal) * frostmanSlabWolffConstant s T * N := h2
      _ ≤ (C : ENNReal) * (θ : ENNReal) * ((δ : ENNReal) ^ (-(ε / 8))) * N := by
          gcongr
          exact hell.trans h3
      _ = M := by rw [hMdef]; ring
  -- `M^{1/2} = C^{1/2} δ^{-ε/4} θ^{1/2} N^{1/2}`
  have hMhalf : M ^ ((1 : ℝ) / 2)
      = (C : ENNReal) ^ ((1 : ℝ) / 2) * ((δ : ENNReal) ^ (-(ε / 16)) *
          ((θ : ENNReal) ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2))) := by
    have h : M = (C : ENNReal) *
        ((δ : ENNReal) ^ (-(ε / 8)) * ((θ : ENNReal) * N)) := by rw [hMdef]; ring
    rw [h, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2), ← ENNReal.rpow_mul]
    congr 3
    ring
  -- `N = ∑ cnt j ≤ M^{1/2} * S`
  have hstep : N ≤ (δ : ENNReal) ^ (-(ε / 8)) * (M ^ ((1 : ℝ) / 2) * S) := by
    refine hdeficit.trans ?_
    refine mul_le_mul_left' ?_ _
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    calc ((part j).card : ENNReal)
        ≤ ((part j).card : ENNReal) ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) :=
          le_rpow_half_mul_rpow_half (hcnt j hj) (by simp)
      _ = M ^ ((1 : ℝ) / 2) * ((part j).card : ENNReal) ^ ((1 : ℝ) / 2) := by ring
  -- cancel one factor of `N^{1/2}`
  have hNhalf0 : N ^ ((1 : ℝ) / 2) ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hN0) hNtop).ne'
  have hNhalftop : N ^ ((1 : ℝ) / 2) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hNtop
  have hNN : N ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2) = N := by
    rw [← ENNReal.rpow_add _ _ hN0 hNtop]; norm_num
  have hcancel : N ^ ((1 : ℝ) / 2)
      ≤ (C : ENNReal) ^ ((1 : ℝ) / 2) * ((δ : ENNReal) ^ (-(ε / 8)) *
        ((δ : ENNReal) ^ (-(ε / 16)) * ((θ : ENNReal) ^ ((1 : ℝ) / 2) * S))) := by
    have h' : N ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2)
        ≤ N ^ ((1 : ℝ) / 2) * ((C : ENNReal) ^ ((1 : ℝ) / 2) * ((δ : ENNReal) ^ (-(ε / 8)) *
            ((δ : ENNReal) ^ (-(ε / 16)) * ((θ : ENNReal) ^ ((1 : ℝ) / 2) * S)))) := by
      rw [hNN]
      calc N ≤ (δ : ENNReal) ^ (-(ε / 8)) * (M ^ ((1 : ℝ) / 2) * S) := hstep
        _ = N ^ ((1 : ℝ) / 2) * ((C : ENNReal) ^ ((1 : ℝ) / 2) * ((δ : ENNReal) ^ (-(ε / 8)) *
              ((δ : ENNReal) ^ (-(ε / 16)) * ((θ : ENNReal) ^ ((1 : ℝ) / 2) * S)))) := by
              rw [hMhalf]; ring
    exact (ENNReal.mul_le_mul_iff_right hNhalf0 hNhalftop).mp h'
  -- the constant: `(κ/C) * C^{1/2} ≤ κ`
  have hconst : ((κ / C : NNReal) : ENNReal) * (C : ENNReal) ^ ((1 : ℝ) / 2)
      ≤ (κ : ENNReal) := by
    have hCle : (C : ENNReal) ^ ((1 : ℝ) / 2) ≤ (C : ENNReal) := by
      calc (C : ENNReal) ^ ((1 : ℝ) / 2)
          ≤ (C : ENNReal) ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le hC1E (by norm_num)
        _ = (C : ENNReal) := by simp
    calc ((κ / C : NNReal) : ENNReal) * (C : ENNReal) ^ ((1 : ℝ) / 2)
        ≤ ((κ / C : NNReal) : ENNReal) * (C : ENNReal) := by gcongr
      _ = ((κ / C * C : NNReal) : ENNReal) := by rw [ENNReal.coe_mul]
      _ = (κ : ENNReal) := by rw [div_mul_cancel₀ _ hC0.ne']
  -- assemble
  refine le_trans ?_ hvol
  have hδpow : (δ : ENNReal) ^ ((3 : ℝ) / 2 + ε)
      = (δ : ENNReal) ^ ((3 : ℝ) / 2) * (δ : ENNReal) ^ (ε / 2) *
          (δ : ENNReal) ^ (5 * ε / 16) *
          ((δ : ENNReal) ^ (ε / 8) * (δ : ENNReal) ^ (ε / 16)) := by
    rw [← ENNReal.rpow_add _ _ hδ0E hδtopE, ← ENNReal.rpow_add _ _ hδ0E hδtopE,
      ← ENNReal.rpow_add _ _ hδ0E hδtopE, ← ENNReal.rpow_add _ _ hδ0E hδtopE]
    congr 1
    ring
  have hc8 : (δ : ENNReal) ^ (ε / 8) * (δ : ENNReal) ^ (-(ε / 8)) = 1 := by
    rw [← ENNReal.rpow_add _ _ hδ0E hδtopE]; norm_num
  have hc16 : (δ : ENNReal) ^ (ε / 16) * (δ : ENNReal) ^ (-(ε / 16)) = 1 := by
    rw [← ENNReal.rpow_add _ _ hδ0E hδtopE]; norm_num
  have hδsmall : (δ : ENNReal) ^ (5 * ε / 16) ≤ 1 :=
    ENNReal.rpow_le_one hδ1E (by positivity)
  set A : ENNReal := ((κ / C : NNReal) : ENNReal) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
    (δ : ENNReal) ^ (ε / 2) with hAdef
  calc ((κ / C : NNReal) : ENNReal) * (δ : ENNReal) ^ ((3 : ℝ) / 2 + ε) * N ^ ((1 : ℝ) / 2)
      = A * (δ : ENNReal) ^ (5 * ε / 16) *
          ((δ : ENNReal) ^ (ε / 8) * (δ : ENNReal) ^ (ε / 16) * N ^ ((1 : ℝ) / 2)) := by
        rw [hAdef, hδpow]; ring
    _ ≤ A * (δ : ENNReal) ^ (5 * ε / 16) *
          ((δ : ENNReal) ^ (ε / 8) * (δ : ENNReal) ^ (ε / 16) *
            ((C : ENNReal) ^ ((1 : ℝ) / 2) * ((δ : ENNReal) ^ (-(ε / 8)) *
              ((δ : ENNReal) ^ (-(ε / 16)) * ((θ : ENNReal) ^ ((1 : ℝ) / 2) * S))))) := by
        gcongr
    _ = A * (δ : ENNReal) ^ (5 * ε / 16) *
          (((δ : ENNReal) ^ (ε / 8) * (δ : ENNReal) ^ (-(ε / 8))) *
            ((δ : ENNReal) ^ (ε / 16) * (δ : ENNReal) ^ (-(ε / 16))) *
            ((C : ENNReal) ^ ((1 : ℝ) / 2) * ((θ : ENNReal) ^ ((1 : ℝ) / 2) * S))) := by
        ring
    _ = A * (δ : ENNReal) ^ (5 * ε / 16) *
          ((C : ENNReal) ^ ((1 : ℝ) / 2) * ((θ : ENNReal) ^ ((1 : ℝ) / 2) * S)) := by
        rw [hc8, hc16, one_mul, one_mul]
    _ = (((κ / C : NNReal) : ENNReal) * (C : ENNReal) ^ ((1 : ℝ) / 2)) *
          ((δ : ENNReal) ^ (5 * ε / 16) *
            ((δ : ENNReal) ^ ((3 : ℝ) / 2) * (δ : ENNReal) ^ (ε / 2) *
              (θ : ENNReal) ^ ((1 : ℝ) / 2) * S)) := by
        rw [hAdef]; ring
    _ ≤ (κ : ENNReal) *
          (1 * ((δ : ENNReal) ^ ((3 : ℝ) / 2) * (δ : ENNReal) ^ (ε / 2) *
            (θ : ENNReal) ^ ((1 : ℝ) / 2) * S)) := by
        gcongr
    _ = (κ : ENNReal) * (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
          (θ : ENNReal) ^ ((1 : ℝ) / 2) * S := by ring

/-! ### Hereditary properties of the Katz--Tao convex Wolff constant

An earlier form of the second geometric leaf (`WolffHairbrushBroad` below)
carried no Katz--Tao hypothesis and was **refuted**; see
`Kakeya.DimensionThree.MainLemma2.WangZahl.WolffHairbrushGuardrails`, which keeps
the refutation in the build as a tripwire.  The repair hands the hypothesis
`CKT(𝕋) ≤ δ^{-η}` down from `HairbrushCover` to `WolffHairbrushBroad`, and the
lemmas of this section are what make that legitimate: unlike
`frostmanSlabWolffConstant`, the definition of `katzTaoConvexWolffConstant`
carries **no `#𝕋` normalization**, so it is monotone under passing to a
subfamily and the classes `part j ⊆ 𝕋` of the cover inherit the hypothesis
verbatim.

On the Frostman side the `#𝕋` normalization is present, so a class only
inherits `FS(part j) ≤ FS(𝕋) · (#𝕋 / #(part j))`, and the *normalized* bound
`FS(part j) ≤ δ^{-ν}` is in fact **false** for a class: the class sits inside a
single `θ`-tube, hence inside a slab of thickness `θ` and volume `≍ θ`, which
already forces `FS(part j) ≥ c θ^{-1}`.  Handing the normalized Frostman
hypothesis down would therefore have created an *inconsistent* hypothesis
bundle at every `θ ≪ δ^{ν}` — green in the compiler, vacuous in content.  It is
not handed down; what the class needs in its place (a slab count) follows from
its Katz--Tao hypothesis, since the class is confined to a `θ`-tube.  The
ambient Frostman hypothesis is still used, at the ambient level, by
`slabTubeCount_holds`. -/

/-- **The Katz--Tao convex Wolff constant is monotone under subfamilies.**

Its defining counting estimate `#{T ∈ 𝕋 : T ⊆ W} ≤ C |W| |T|⁻¹` has no `#𝕋` on
the right, so every admissible constant for `s` is admissible for `s' ⊆ s`, and
the infimum is taken over a larger set. -/
theorem katzTaoConvexWolffConstant_mono {δ : NNReal} {ι : Type u}
    {s s' : Finset ι} (hss : s' ⊆ s) (T : ι → ShadedTube δ Space3) :
    katzTaoConvexWolffConstant s' T ≤ katzTaoConvexWolffConstant s T := by
  refine sInf_le_sInf ?_
  rintro C ⟨hC0, hC⟩
  refine ⟨hC0, fun W => le_trans ?_ (hC W)⟩
  have hsub : (@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
      (Classical.decPred _) s') ⊆
      (@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s) := by
    intro i hi
    have hi' := (@Finset.mem_filter ι (fun i => (T i).carrier ⊆ W.carrier)
      (Classical.decPred _) s' i).mp hi
    exact (@Finset.mem_filter ι (fun i => (T i).carrier ⊆ W.carrier)
      (Classical.decPred _) s i).mpr ⟨hss hi'.1, hi'.2⟩
  exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hsub)

/-- The same monotonicity in the form the repaired split would use: a class of
the cover inherits the Katz--Tao hypothesis of the ambient family. -/
theorem katzTaoConvexWolffConstant_le_of_subset {δ : NNReal} {ι : Type u}
    {s s' : Finset ι} (hss : s' ⊆ s) (T : ι → ShadedTube δ Space3) {η : ℝ}
    (h : katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η)) :
    katzTaoConvexWolffConstant s' T ≤ (δ : ENNReal) ^ (-η) :=
  le_trans (katzTaoConvexWolffConstant_mono hss T) h

/-- The Katz--Tao convex Wolff constant of a family with at most one member is
at most `1`: a convex set containing the single tube has volume at least `|T|`,
so `C = 1` is admissible. -/
theorem katzTaoConvexWolffConstant_le_one_of_card_le_one {δ : NNReal} (hδ : 0 < δ)
    {ι : Type u} {s : Finset ι} (hs : s.card ≤ 1) (T : ι → ShadedTube δ Space3) :
    katzTaoConvexWolffConstant s T ≤ 1 := by
  obtain ⟨hV0, hVtop⟩ := tubeVolume_pos_and_ne_top hδ
  refine sInf_le ⟨zero_lt_one, fun W => ?_⟩
  set F := @Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
    (Classical.decPred _) s with hF
  rcases Finset.eq_empty_or_nonempty F with hemp | ⟨i, hi⟩
  · simp [hemp]
  · have hFsub : F ⊆ s := hF ▸ (@Finset.filter_subset ι
      (fun i => (T i).carrier ⊆ W.carrier) (Classical.decPred _) s)
    have hcard : (F.card : ENNReal) ≤ 1 := by
      exact_mod_cast le_trans (Finset.card_le_card hFsub) hs
    refine le_trans hcard ?_
    have hi' := (@Finset.mem_filter ι (fun i => (T i).carrier ⊆ W.carrier)
      (Classical.decPred _) s i).mp hi
    have hvol : tubeVolume δ ≤ volume W.carrier := by
      rw [← volume_carrier_eq_tubeVolume T i]
      exact measure_mono hi'.2
    calc (1 : ENNReal) = tubeVolume δ * (tubeVolume δ)⁻¹ :=
          (ENNReal.mul_inv_cancel hV0.ne' hVtop).symm
      _ ≤ volume W.carrier * (tubeVolume δ)⁻¹ := by gcongr
      _ = 1 * volume W.carrier * (tubeVolume δ)⁻¹ := by rw [one_mul]

/-- `1 ≤ δ^{-ν}` for `0 < δ ≤ 1` and `0 ≤ ν`: the Katz--Tao budget of the
repaired leaf is never vacuous. -/
theorem one_le_rpow_neg {δ : NNReal} (hδ1 : δ ≤ 1) {ν : ℝ} (hν : 0 ≤ ν) :
    (1 : ENNReal) ≤ (δ : ENNReal) ^ (-ν) := by
  have hδ1E : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have := ENNReal.rpow_le_rpow_of_exponent_ge hδ1E (by linarith : -ν ≤ (0:ℝ))
  simpa using this

/-! ### Shading refinements: the source's missing degree of freedom

The source's covering step does **not** keep the shading fixed.  Immediately
after producing the cover it says (`blueprint/src/WZ2/250224e_K3.tex:5748`)

> After a further refinement, we may suppose that each set `𝕋^{T_θ}` is
> `δ^{3η}`-dense.

That "further refinement" *shrinks the shadings*, once per class of the cover,
and it is what pays for both the density and the broadness of the class.  A
statement whose only shaded family is the fixed input `T` cannot express it,
and this missing degree of freedom is exactly what made the fixed-shading form
of the covering leaf **false**
(`Kakeya.DimensionThree.MainLemma2.WangZahl.WolffHairbrushGuardrails.not_balancedBroadCover`:
two orthogonal fully shaded `δ`-tubes at `θ = δ`, where no `δ`-tube contains
both, so two classes are forced and their *fixed* shadings overlap in
`closedBall 0 δ`).  With per-class shadings that witness is no longer a
refutation: the cover may hand out `Y₀ = A \ B` and `Y₁ = B`, whose volumes add
up to exactly `|A ∪ B|`.

Note also the density bookkeeping the source performs here: the input is
`δ^η`-dense and the output only `δ^{3η}`-dense.  The leaves below record that
loss the way the file already records the loss in the broadness quality — the
target quality `ν` is an *input* and the admissible input quality `η ≤ ν` is
handed out existentially by the leaf — rather than by inventing a numeral for
the exponent.

**On `IsBroadAtScale` itself.**  The predicate is a verbatim transcription of
the source's display and is *not* changed here.  What was wrong was every place
it was applied: `IsBroadAtScale s T θ ν` tested at `r = δ` and `w = dir T_{i₀}`
puts `T_{i₀}` into its own left-hand count
(`WolffHairbrushGuardrails.rpow_le_multiplicity_of_isBroadAtScale`), so it
demands that *every* point of *every* shading be covered by at least
`(θ/δ)^ν` tubes.  The source has the same consequence, but only for the shading
it has already refined; asking it of the fixed input shading `Y(T)` is the
over-demand, since the far end of a tube of a bush has multiplicity `1`.  The
repair is therefore to apply the predicate to `Y j`, not to `T`, which is what
the restated leaves below do. -/

/-- **`T'` refines the shadings of `T` on `s`:** same underlying tubes, smaller
shadings.  This is the source's "further refinement" of `250224e_K3.tex:5748`,
as a relation between shaded families. -/
def IsShadingRefinement {δ : NNReal} {ι : Type u} (s : Finset ι)
    (T' T : ι → ShadedTube δ Space3) : Prop :=
  ∀ i ∈ s, (T' i).toTube = (T i).toTube ∧ (T' i).shade ⊆ (T i).shade

/-- A shading refinement does not move the carriers. -/
theorem IsShadingRefinement.carrier_eq {δ : NNReal} {ι : Type u} {s : Finset ι}
    {T' T : ι → ShadedTube δ Space3} (h : IsShadingRefinement s T' T) {i : ι} (hi : i ∈ s) :
    (T' i).carrier = (T i).carrier := by
  have hT := (h i hi).1
  rw [show (T' i).carrier = (T' i).toTube.carrier from rfl,
    show (T i).carrier = (T i).toTube.carrier from rfl, hT]

/-- Every family refines itself: the fixed-shading statements are the special
case `Y j = T` of the refined ones. -/
theorem IsShadingRefinement.rfl' {δ : NNReal} {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ Space3) : IsShadingRefinement s T T :=
  fun _ _ => ⟨rfl, subset_rfl⟩

theorem IsShadingRefinement.mono {δ : NNReal} {ι : Type u} {s s' : Finset ι}
    {T' T : ι → ShadedTube δ Space3} (h : IsShadingRefinement s T' T) (hss : s' ⊆ s) :
    IsShadingRefinement s' T' T :=
  fun i hi => h i (hss hi)

theorem IsShadingRefinement.trans {δ : NNReal} {ι : Type u} {s : Finset ι}
    {T'' T' T : ι → ShadedTube δ Space3} (h1 : IsShadingRefinement s T'' T')
    (h2 : IsShadingRefinement s T' T) : IsShadingRefinement s T'' T :=
  fun i hi => ⟨(h1 i hi).1.trans (h2 i hi).1, (h1 i hi).2.trans (h2 i hi).2⟩

/-- A shading refinement of a tube shading family is a tube shading family:
`IsTubeShadingFamily` constrains only the carriers. -/
theorem IsShadingRefinement.isTubeShadingFamily {δ : NNReal} {ι : Type u} {s : Finset ι}
    {T' T : ι → ShadedTube δ Space3} (h : IsShadingRefinement s T' T)
    (hfam : IsTubeShadingFamily s T) : IsTubeShadingFamily s T' := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [h.carrier_eq hi]; exact hfam.1 i hi
  · intro i hi j hj hij
    rw [h.carrier_eq (by exact_mod_cast hi), h.carrier_eq (by exact_mod_cast hj)]
    exact hfam.2 hi hj hij

/-- The Katz--Tao convex Wolff constant depends only on the carriers. -/
theorem katzTaoConvexWolffConstant_congr {δ : NNReal} {ι : Type u} {s : Finset ι}
    {T' T : ι → ShadedTube δ Space3} (h : ∀ i ∈ s, (T' i).carrier = (T i).carrier) :
    katzTaoConvexWolffConstant s T' = katzTaoConvexWolffConstant s T := by
  have hfil : ∀ W : ConvexTestSet,
      (@Finset.filter ι (fun i => (T' i).carrier ⊆ W.carrier) (Classical.decPred _) s) =
      (@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier) (Classical.decPred _) s) := by
    intro W
    refine Finset.ext fun i => ?_
    constructor
    · intro hi
      have hi' := (@Finset.mem_filter ι (fun i => (T' i).carrier ⊆ W.carrier)
        (Classical.decPred _) s i).mp hi
      refine (@Finset.mem_filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s i).mpr ⟨hi'.1, ?_⟩
      rw [← h i hi'.1]; exact hi'.2
    · intro hi
      have hi' := (@Finset.mem_filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s i).mp hi
      refine (@Finset.mem_filter ι (fun i => (T' i).carrier ⊆ W.carrier)
        (Classical.decPred _) s i).mpr ⟨hi'.1, ?_⟩
      rw [h i hi'.1]; exact hi'.2
  unfold katzTaoConvexWolffConstant
  congr 1
  ext C
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hC0, hC⟩; exact ⟨hC0, fun W => by rw [← hfil W]; exact hC W⟩
  · rintro ⟨hC0, hC⟩; exact ⟨hC0, fun W => by rw [hfil W]; exact hC W⟩

/-- A class of a cover inherits the ambient Katz--Tao bound even after its
shadings have been refined: `CKT` sees only carriers, and it is monotone under
subfamilies (`katzTaoConvexWolffConstant_le_of_subset`). -/
theorem IsShadingRefinement.katzTao_le {δ : NNReal} {ι : Type u} {s s' : Finset ι}
    {T' T : ι → ShadedTube δ Space3} (h : IsShadingRefinement s' T' T) (hss : s' ⊆ s)
    {ν : ℝ} (hm : katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-ν)) :
    katzTaoConvexWolffConstant s' T' ≤ (δ : ENNReal) ^ (-ν) := by
  rw [katzTaoConvexWolffConstant_congr (fun i hi => h.carrier_eq hi)]
  exact katzTaoConvexWolffConstant_le_of_subset hss T hm

/-- **The canonical shading refinement**: intersect every shading with a fixed
measurable set.  This is `ShadedBody.restrictShade` at the level of shaded
tubes, and it is how a cover hands out its per-class shadings. -/
def restrictShadedTube {δ : NNReal} (T : ShadedTube δ Space3) (S : Set Space3)
    (hS : MeasurableSet S) : ShadedTube δ Space3 where
  toTube := T.toTube
  shade := T.shade ∩ S
  measurableSet_shade := T.measurableSet_shade.inter hS
  shade_subset := fun _ hx => T.shade_subset hx.1

@[simp]
theorem shade_restrictShadedTube {δ : NNReal} (T : ShadedTube δ Space3) (S : Set Space3)
    (hS : MeasurableSet S) : (restrictShadedTube T S hS).shade = T.shade ∩ S := rfl

theorem isShadingRefinement_restrict {δ : NNReal} {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ Space3) (S : Set Space3) (hS : MeasurableSet S) :
    IsShadingRefinement s (fun i => restrictShadedTube (T i) S hS) T :=
  fun _ _ => ⟨rfl, Set.inter_subset_left⟩

/-- Refining the shadings can only shrink the shaded union. -/
theorem IsShadingRefinement.volume_iUnionShade_le {δ : NNReal} {ι : Type u} {s : Finset ι}
    {T' T : ι → ShadedTube δ Space3} (h : IsShadingRefinement s T' T) :
    volume (ShadedBody.iUnionShade s fun i => (T' i).toShadedBody) ≤
      volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
  refine measure_mono ?_
  intro x hx
  simp only [ShadedBody.iUnionShade, Set.mem_iUnion, exists_prop] at hx ⊢
  obtain ⟨i, hi, hxi⟩ := hx
  exact ⟨i, hi, (h i hi).2 hxi⟩

/-- **Disjointification of the shadings of a finite shaded family.**

Every finite shaded family has a shading refinement whose shadings are pairwise
disjoint, cover the same union, and therefore have volumes summing *exactly* to
the volume of that union.  Concretely `Y(T_i) = Y(T_i) \ ⋃_{k < i} Y(T_k)` for
an arbitrary well-ordering of the index type.

This is the mechanism by which the covering leaf meets its
essential-disjointness conjunct with constant `1`; it is the general form of
the two-line construction `Y₀ = A \ B`, `Y₁ = B` that
`WolffHairbrushGuardrails.exists_refinedCover_crossedFamily` uses at the
refuting witness.  What it does *not* supply is the density of the disjointified
shadings, which is where the covering leaf's remaining content sits. -/
theorem exists_disjointed_shading {δ : NNReal} {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ Space3) :
    ∃ Y : ι → ShadedTube δ Space3, IsShadingRefinement s Y T ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Y i).shade (Y j).shade) ∧
      (⋃ i ∈ s, (Y i).shade) = ⋃ i ∈ s, (T i).shade ∧
      ∑ i ∈ s, volume (Y i).shade
        = volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
  classical
  letI : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  set A : ι → Set Space3 :=
    fun i => (T i).shade \ ⋃ k ∈ s.filter (fun k => k < i), (T k).shade with hA
  have hAmeas : ∀ i, MeasurableSet (A i) := by
    intro i
    refine (T i).measurableSet_shade.diff ?_
    exact Finset.measurableSet_biUnion _ (fun k _ => (T k).measurableSet_shade)
  have hAsub : ∀ i, A i ⊆ (T i).shade := fun i => Set.sdiff_subset
  refine ⟨fun i => restrictShadedTube (T i) (A i) (hAmeas i), fun i _ => ⟨rfl, ?_⟩, ?_, ?_, ?_⟩
  · exact Set.inter_subset_left
  · -- pairwise disjoint
    intro i _ j _ hij
    have hshade : ∀ k, (restrictShadedTube (T k) (A k) (hAmeas k)).shade = A k := by
      intro k
      rw [shade_restrictShadedTube]
      exact Set.inter_eq_self_of_subset_right (hAsub k)
    rw [hshade i, hshade j]
    rcases lt_or_gt_of_ne hij with h | h
    · refine Set.disjoint_left.mpr fun x hxi hxj => ?_
      exact absurd hxi.1 (fun hx => hxj.2 (by
        simp only [Set.mem_iUnion, exists_prop]
        exact ⟨i, Finset.mem_filter.mpr ⟨‹i ∈ s›, h⟩, hx⟩))
    · refine Set.disjoint_left.mpr fun x hxi hxj => ?_
      exact absurd hxj.1 (fun hx => hxi.2 (by
        simp only [Set.mem_iUnion, exists_prop]
        exact ⟨j, Finset.mem_filter.mpr ⟨‹j ∈ s›, h⟩, hx⟩))
  · -- the union is unchanged
    have hshade : ∀ k, (restrictShadedTube (T k) (A k) (hAmeas k)).shade = A k := by
      intro k
      rw [shade_restrictShadedTube]
      exact Set.inter_eq_self_of_subset_right (hAsub k)
    refine Set.Subset.antisymm ?_ ?_
    · refine Set.iUnion₂_subset fun i hi => ?_
      rw [hshade i]
      intro x hx
      exact Set.mem_biUnion hi (hAsub i hx)
    · intro x hx
      simp only [Set.mem_iUnion, exists_prop] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      set s' : Finset ι := s.filter (fun k => x ∈ (T k).shade) with hs'
      have hne : s'.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hxi⟩⟩
      set m : ι := s'.min' hne with hm
      have hmem : m ∈ s' := s'.min'_mem hne
      have hms := Finset.mem_filter.mp hmem
      simp only [Set.mem_iUnion, exists_prop]
      refine ⟨m, hms.1, ?_⟩
      rw [hshade m]
      refine ⟨hms.2, ?_⟩
      simp only [Set.mem_iUnion, exists_prop, not_exists, not_and]
      intro k hk hxk
      have hk' := Finset.mem_filter.mp hk
      have : m ≤ k := s'.min'_le k (Finset.mem_filter.mpr ⟨hk'.1, hxk⟩)
      exact absurd hk'.2 (not_lt.mpr this)
  · -- the volumes add up
    have hshade : ∀ k, (restrictShadedTube (T k) (A k) (hAmeas k)).shade = A k := by
      intro k
      rw [shade_restrictShadedTube]
      exact Set.inter_eq_self_of_subset_right (hAsub k)
    have hdisj : (s : Set ι).Pairwise (Function.onFun Disjoint A) := by
      intro i hi j hj hij
      have hi' : i ∈ s := hi
      have hj' : j ∈ s := hj
      simp only [Function.onFun]
      rcases lt_or_gt_of_ne hij with h | h
      · refine Set.disjoint_left.mpr fun x hxi hxj => ?_
        exact absurd hxi.1 (fun hx => hxj.2 (by
          simp only [Set.mem_iUnion, exists_prop]
          exact ⟨i, Finset.mem_filter.mpr ⟨hi', h⟩, hx⟩))
      · refine Set.disjoint_left.mpr fun x hxi hxj => ?_
        exact absurd hxj.1 (fun hx => hxi.2 (by
          simp only [Set.mem_iUnion, exists_prop]
          exact ⟨j, Finset.mem_filter.mpr ⟨hj', h⟩, hx⟩))
    have hbi := measure_biUnion_finset (μ := (volume : Measure Space3)) hdisj
      (fun i _ => hAmeas i)
    have hUeq : (⋃ i ∈ s, A i) = ShadedBody.iUnionShade s (fun i => (T i).toShadedBody) := by
      refine Set.Subset.antisymm ?_ ?_
      · refine Set.iUnion₂_subset fun i hi => ?_
        intro x hx
        exact Set.mem_biUnion hi (hAsub i hx)
      · intro x hx
        simp only [ShadedBody.iUnionShade, Set.mem_iUnion, exists_prop] at hx
        obtain ⟨i, hi, hxi⟩ := hx
        set s' : Finset ι := s.filter (fun k => x ∈ (T k).shade) with hs'
        have hne : s'.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hxi⟩⟩
        set m : ι := s'.min' hne with hm
        have hmem : m ∈ s' := s'.min'_mem hne
        have hms := Finset.mem_filter.mp hmem
        simp only [Set.mem_iUnion, exists_prop]
        refine ⟨m, hms.1, hms.2, ?_⟩
        simp only [Set.mem_iUnion, exists_prop, not_exists, not_and]
        intro k hk hxk
        have hk' := Finset.mem_filter.mp hk
        have : m ≤ k := s'.min'_le k (Finset.mem_filter.mpr ⟨hk'.1, hxk⟩)
        exact absurd hk'.2 (not_lt.mpr this)
    calc ∑ i ∈ s, volume (restrictShadedTube (T i) (A i) (hAmeas i)).shade
        = ∑ i ∈ s, volume (A i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hshade i]
      _ = volume (⋃ i ∈ s, A i) := hbi.symm
      _ = volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by rw [hUeq]

/-! ### The two geometric leaves of the source proof -/

/-- **The source's non-concentration ("`2`-broad at scale `θ`") condition.**

Source: `blueprint/src/WZ2/250224e_K3.tex`, Appendix `WolffHairbrushSec`, the
display following "Applying standard reductions": for each `x`, each unit vector
`w` and each `r ∈ [δ, θ]`,

`#{T ∈ 𝕋_Y(x) : ∠(w, dir T) ≤ r} ≤ (r/θ)^η (#𝕋_Y(x))`.

Here `𝕋_Y(x)` is the set of tubes of the family whose *shading* contains `x`,
and the angle `∠(w, dir T)` is measured by the chordal distance between unit
vectors, made insensitive to the sign ambiguity `dir T ↦ -dir T` of an unoriented
tube.  Chordal distance and angle agree to within a factor `2` on `[0, π/2]`, so
this is the source's condition up to the harmless rescaling of `η` that the
source itself leaves implicit.

Note that the condition gets *stronger* as `η` increases (because `r/θ ≤ 1`),
which is why `HairbrushCover` below is stated with `ν` as an input. -/
def IsBroadAtScale {δ : NNReal} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) (θ : NNReal) (ν : ℝ) : Prop :=
  ∀ (x : Space3) (w : Space3), ‖w‖ = 1 → ∀ r : NNReal, δ ≤ r → r ≤ θ →
    ((@Finset.filter ι
        (fun i => x ∈ (T i).shade ∧
          min ‖w - (T i).toTube.direction‖ ‖w + (T i).toTube.direction‖ ≤ (r : ℝ))
        (Classical.decPred _) s).card : ENNReal) ≤
      ((r / θ : NNReal) : ENNReal) ^ ν *
        ((@Finset.filter ι (fun i => x ∈ (T i).shade)
          (Classical.decPred _) s).card : ENNReal)

/-- Broadness at a higher quality implies broadness at a lower one: the factor
`(r/θ)^ν` is at most `(r/θ)^η` when `η ≤ ν`, because `r ≤ θ`.  This is the
direction in which the two qualities of `HairbrushCover` are *not* symmetric:
`δ^η`-density gets stronger as `η` shrinks, `η`-broadness as `η` grows. -/
theorem IsBroadAtScale.mono_quality {δ : NNReal} {ι : Type u} {s : Finset ι}
    {T : ι → ShadedTube δ Space3} {θ : NNReal} {η ν : ℝ} (h : IsBroadAtScale s T θ ν)
    (hην : η ≤ ν) : IsBroadAtScale s T θ η := by
  intro x w hw r hrδ hrθ
  refine (h x w hw r hrδ hrθ).trans ?_
  have hq : ((r / θ : NNReal) : ENNReal) ≤ 1 := by
    have : r / θ ≤ 1 := by
      rcases eq_or_ne θ 0 with hθ | hθ
      · simp [hθ]
      · exact (div_le_one (pos_iff_ne_zero.mpr hθ)).mpr hrθ
    exact_mod_cast this
  exact mul_le_mul_right' (ENNReal.rpow_le_rpow_of_exponent_ge hq hην) _

/-- **Leaf 1: the standard reductions and the balanced partitioning cover.**

Source: `WolffHairbrushSec`, everything from "Applying standard reductions" up
to and including "After a further refinement, we may suppose that each set
`𝕋^{T_θ}` is `δ^{3η}`-dense", i.e.

* the robust-transversality reduction producing the scale `θ ∈ [δ,1]` and a
  `δ^{Cη}`-dense refinement whose tubes through a typical point obey the
  `(r/θ)^η` non-concentration bound;
* the balanced partitioning cover `𝕋_θ` at scale `θ`, whose classes
  `𝕋[T_θ]` consist of the `δ`-tubes contained in the `θ`-tube `T_θ`;
* the displayed identity `broadAtScaleTheta`, of which only the inequality
  `∑_{T_θ} |∪_{T ∈ 𝕋[T_θ]} Y(T)| ≤ |∪_{T ∈ 𝕋} Y(T)|` is used (this is the
  substantive half: it is the essential disjointness of the shadings of distinct
  classes).

The target quality `ν` of the refinement is an *input*: the source fixes `η`
"to be chosen below" and then spends it, so the reduction must be able to
deliver any prescribed `ν` at the cost of a smaller input `η`.  Both the density
of the classes and their broadness are delivered at that `ν`; this is what makes
Leaf 1 and Leaf 2 composable (see `hairbrushDecomposition_of_cover_of_broad`).

As in `HairbrushDecomposition`, only the inequality `#𝕋 ≤ δ^{-ε/8} ∑_j cnt j`
is asserted, not a partition identity: the cover partitions the refinement.

**Two conditions restored in the repair of the split** (see
`Kakeya.DimensionThree.MainLemma2.WangZahl.WolffHairbrushGuardrails` for the
refutation of the pre-repair Leaf 2, and the before/after text):

* `η ≤ ν`.  This costs nothing: `η` only occurs in the *hypotheses* of the leaf
  (`δ^η`-density, `CKT ≤ δ^{-η}`, `FS ≤ δ^{-η}`), all three of which get
  stronger as `η` shrinks, so any admissible `η` may be replaced by `min η ν`.
  What it buys is that a class inherits the ambient Katz--Tao bound *at the
  quality `ν` that Leaf 2 asks for*:
  `CKT(part j) ≤ CKT(𝕋) ≤ δ^{-η} ≤ δ^{-ν}` by
  `katzTaoConvexWolffConstant_le_of_subset` and `δ ≤ 1`.

* **Balancedness** of the cover, `cnt j' ≤ 2 cnt j` for all `j, j' ∈ P`.  This
  is part of what "balanced partitioning cover" means in the source, and it is
  what dyadic pigeonholing on `cnt j` delivers (at the cost of the `δ^{-ε/8}`
  already budgeted in the class-count inequality).  It is recorded here because
  the source's Cauchy--Schwarz step at `250224e_K3.tex:5760` — which passes from
  `∑_j (cnt j)^{1/2}` to `(∑_j cnt j)/(max_j cnt j)^{1/2}` — is valid only for a
  balanced cover; it is *not* used by
  `hairbrushDecomposition_of_cover_of_broad`, which needs only the Katz--Tao
  inheritance above.

The Frostman slab hypothesis is deliberately **not** handed down to the class;
see the discussion above `katzTaoConvexWolffConstant_mono`.

**Restated 2026-08: the per-class shading refinement `Y`.**  The statement now
returns, alongside the cover, a shaded family `Y j` for each class, refining the
input shadings on that class (`IsShadingRefinement (part j) (Y j) T`); the
density and broadness conjuncts are asked of the *refined* shadings, and the
essential-disjointness conjunct compares `∑_j |∪_{i ∈ part j} Y j i|` with
`|∪_{i ∈ s} Y(T i)|`.  This is the source's "After a further refinement, we may
suppose that each set `𝕋^{T_θ}` is `δ^{3η}`-dense"
(`blueprint/src/WZ2/250224e_K3.tex:5748`), which the previous fixed-shading form
could not express; see the section "Shading refinements" above and
`WolffHairbrushGuardrails.hairbrushCover_of_fixedShading` for the tripwire and
for the fact that the restatement only *weakens* the leaf.  The density loss of
the refinement is not given a numeral: it is carried by the existing convention
that the target quality `ν` is an input and the admissible input quality
`η ≤ ν` is handed out by the leaf. -/
def HairbrushCover : Prop :=
  ∀ ε > (0 : ℝ), ∀ ν > (0 : ℝ), ∃ η : ℝ, 0 < η ∧ η ≤ ν ∧
    ∀ (δ : NNReal), 0 < δ → δ ≤ 1 →
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        IsTubeShadingFamily s T →
        IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ →
        katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        frostmanSlabWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        ∃ θ : NNReal, 0 < θ ∧ θ ≤ 1 ∧
          ∃ (J : Type u) (P : Finset J) (parent : J → Tube θ Space3) (part : J → Finset ι)
            (Y : J → ι → ShadedTube δ Space3),
            (∀ j ∈ P, part j ⊆
              @Finset.filter ι (fun i => (T i).carrier ⊆ (parent j).carrier)
                (Classical.decPred _) s) ∧
            (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 8)) *
              (∑ j ∈ P, ((part j).card : ENNReal)) ∧
            (∀ j ∈ P, ∀ j' ∈ P, ((part j').card : ENNReal) ≤ 2 * ((part j).card : ENNReal)) ∧
            (∀ j ∈ P, IsShadingRefinement (part j) (Y j) T) ∧
            (∀ j ∈ P,
              IsDense (part j) (Y j) ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩) ∧
            (∀ j ∈ P, IsBroadAtScale (part j) (Y j) θ ν) ∧
            (∑ j ∈ P, volume (ShadedBody.iUnionShade (part j)
                fun i => (Y j i).toShadedBody)) ≤
              volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)

/-- **Leaf 2: Wolff's hairbrush bound for one class of the cover.**

Source: `WolffHairbrushSec`, the sentence "Thus a standard application of
Wolff's hairbrush argument \cite{Wol95} for `2`-broad tubes shows that ...",
together with the `θ`-rescaling that precedes it.

A class of the cover is a family of `δ`-tubes all contained in a single
`θ`-tube `R`, dense and broad at scale `θ`.  Rescaling the two transverse
directions of `R` by `θ^{-1}` turns it into a `δ/θ`-tube family in the unit
ball which is `2`-broad in the source's sense (the range `r ∈ [δ,θ]` with
factor `(r/θ)^ν` becomes `r' ∈ [δ/θ,1]` with factor `r'^ν`), so Wolff's bound
gives `|∪Y'| ≳ (δ/θ)^{3/2}(#𝕋)^{1/2}`; undoing the rescaling multiplies
volumes by `θ^2` and yields the bound below.

**On the source.** The source's display prints
`(δ/θ)^{1/2}((δ/θ)(#𝕋^{T_θ}))^{1/2}`, i.e. `(δ/θ)(#𝕋^{T_θ})^{1/2}`, whose
value at the extremal count `#𝕋^{T_θ} = (δ/θ)^{-2}` is `≍ 1` — impossible
inside the unit ball.  The intended factor is the tube volume `(δ/θ)^2`, giving
`(δ/θ)^{3/2}(#𝕋^{T_θ})^{1/2}`; only with that reading does the source's next
display follow.  The corrected form is what is recorded here.

**The Katz--Tao hypothesis `CKT(𝕋) ≤ δ^{-ν}` is not optional.**  Without it this
statement is *false*: see
`Kakeya.DimensionThree.MainLemma2.WangZahl.WolffHairbrushGuardrails`, where
`not_wolffHairbrushBroad_of_packing` refutes the hypothesis-free form from the
standard `δ`-tube packing of the unit ball.  The reason is that Wolff's theorem
`\cite{Wol95}` bounds families of `δ`-**separated directions**, i.e. `#𝕋 ≲ δ^{-2}`
after the `θ`-rescaling, whereas an arbitrary essentially distinct family in a
`θ`-tube can have `≍ (θ/δ)^4` members.  `CKT(𝕋) ≤ δ^{-ν}` is exactly the
separation hypothesis in the source's currency: tested against the `θ`-tube `R`
it reads `#𝕋 ≤ δ^{-ν}|R|/|T| ≍ δ^{-ν}(θ/δ)^2`.  The class of the cover of
`HairbrushCover` inherits it verbatim (`katzTaoConvexWolffConstant_le_of_subset`,
using `η ≤ ν`), so restoring it does not make the split harder to compose.

`wolffHairbrushBroad_hypotheses_satisfiable` certifies that the repaired
hypothesis bundle is still satisfiable by a nonempty family, so the leaf cannot
be discharged vacuously. -/
def WolffHairbrushBroad : Prop :=
  ∀ ε > (0 : ℝ), ∃ κ : NNReal, ∃ ν : ℝ, 0 < κ ∧ 0 < ν ∧
    ∀ (δ : NNReal), 0 < δ → δ ≤ 1 → ∀ (θ : NNReal), 0 < θ → θ ≤ 1 →
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        IsTubeShadingFamily s T →
        ∀ R : Tube θ Space3, (∀ i ∈ s, (T i).carrier ⊆ R.carrier) →
        IsDense s T ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ →
        katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-ν) →
        IsBroadAtScale s T θ ν →
        (κ : ENNReal) * (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
            (θ : ENNReal) ^ ((1 : ℝ) / 2) * ((s.card : ENNReal) ^ ((1 : ℝ) / 2)) ≤
          volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)

/-- **Leaf 1 + Leaf 2 = the hairbrush decomposition.**

The only content is the summation of the per-class bound of Leaf 2 over the
classes of the cover of Leaf 1, followed by the essential-disjointness
inequality (the used half of `broadAtScaleTheta`). -/
theorem hairbrushDecomposition_of_cover_of_broad
    (HC : HairbrushCover.{u}) (HW : WolffHairbrushBroad.{u}) :
    HairbrushDecomposition.{u} := by
  intro ε hε
  obtain ⟨κ, ν, hκ, hν, hW⟩ := HW ε hε
  obtain ⟨η, hη, hην, hC⟩ := HC ε hε ν hν
  refine ⟨κ, η, hκ, hη, ?_⟩
  intro δ hδ hδ1 ι s T hfamily hdense hm hell
  obtain ⟨θ, hθ0, hθ1, J, P, parent, part, Y, hpart, hcount, _hbal, href, hdens, hbroad,
    hadd⟩ := hC δ hδ hδ1 s T hfamily hdense hm hell
  refine ⟨θ, hθ0, hθ1, J, P, parent, part, hpart, hcount, ?_⟩
  have hsub : ∀ j ∈ P, part j ⊆ s := by
    intro j hj
    exact (hpart j hj).trans
      (@Finset.filter_subset ι (fun i => (T i).carrier ⊆ (parent j).carrier)
        (Classical.decPred _) s)
  have hper : ∀ j ∈ P,
      (κ : ENNReal) * (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
          (θ : ENNReal) ^ ((1 : ℝ) / 2) * (((part j).card : ENNReal) ^ ((1 : ℝ) / 2)) ≤
        volume (ShadedBody.iUnionShade (part j) fun i => (Y j i).toShadedBody) := by
    intro j hj
    have hfamT : IsTubeShadingFamily (part j) T := by
      refine ⟨fun i hi => hfamily.1 i (hsub j hj hi), ?_⟩
      exact hfamily.2.mono (by exact_mod_cast hsub j hj)
    have hfam' : IsTubeShadingFamily (part j) (Y j) :=
      (href j hj).isTubeShadingFamily hfamT
    have hckt : katzTaoConvexWolffConstant (part j) (Y j) ≤ (δ : ENNReal) ^ (-ν) := by
      refine (href j hj).katzTao_le (hsub j hj) ?_
      exact hm.trans (ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1)
        (by linarith : -ν ≤ -η))
    refine hW δ hδ hδ1 θ hθ0 hθ1 (part j) (Y j) hfam' (parent j) ?_
      (hdens j hj) hckt (hbroad j hj)
    intro i hi
    rw [(href j hj).carrier_eq hi]
    exact ((@Finset.mem_filter ι (fun i => (T i).carrier ⊆ (parent j).carrier)
      (Classical.decPred _) s i).mp (hpart j hj hi)).2
  calc (κ : ENNReal) * (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
        (θ : ENNReal) ^ ((1 : ℝ) / 2) *
        (∑ j ∈ P, ((part j).card : ENNReal) ^ ((1 : ℝ) / 2))
      = ∑ j ∈ P, ((κ : ENNReal) * (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
          (θ : ENNReal) ^ ((1 : ℝ) / 2) * (((part j).card : ENNReal) ^ ((1 : ℝ) / 2))) :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ P, volume (ShadedBody.iUnionShade (part j) fun i => (Y j i).toShadedBody) :=
        Finset.sum_le_sum hper
    _ ≤ volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := hadd

/-! ### Non-vacuity of the two leaves -/

/-- At `θ ≤ δ` the broadness condition is automatic: the range `r ∈ [δ, θ]`
collapses to the single value `r = θ`, where the bound reads
`#{...} ≤ 1 · #𝕋_Y(x)`. -/
theorem isBroadAtScale_of_le_delta {δ : NNReal} {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ Space3) {θ : NNReal} (hθ0 : 0 < θ) (hθδ : θ ≤ δ) (ν : ℝ) :
    IsBroadAtScale s T θ ν := by
  intro x w hw r hr1 hr2
  have hrθ : r = θ := le_antisymm hr2 (hθδ.trans hr1)
  subst hrθ
  rw [div_self hθ0.ne', ENNReal.coe_one, ENNReal.one_rpow, one_mul]
  refine Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro i hi
  have hi' := (@Finset.mem_filter ι
    (fun i => x ∈ (T i).shade ∧
      min ‖w - (T i).toTube.direction‖ ‖w + (T i).toTube.direction‖ ≤ ((r : NNReal) : ℝ))
    (Classical.decPred _) s i).mp hi
  exact (@Finset.mem_filter ι (fun i => x ∈ (T i).shade)
    (Classical.decPred _) s i).mpr ⟨hi'.1, hi'.2.1⟩

/-- The unit segment centred at the origin, as a `δ`-tube. -/
def centredTube (δ : NNReal) : Tube δ Space3 :=
  Tube.mk' δ (x := -((1 : ℝ) / 2) • EuclideanSpace.single 0 (1 : ℝ))
    (y := ((1 : ℝ) / 2) • EuclideanSpace.single 0 (1 : ℝ)) (by
      have h : (-((1 : ℝ) / 2) • EuclideanSpace.single 0 (1 : ℝ) -
          ((1 : ℝ) / 2) • EuclideanSpace.single 0 (1 : ℝ) : Space3) =
          -(EuclideanSpace.single 0 (1 : ℝ)) := by module
      rw [dist_eq_norm, h, norm_neg, PiLp.norm_single, norm_one])

theorem centredTube_subset_ball {δ : NNReal} (hδ : δ ≤ 1 / 2) :
    (centredTube δ).carrier ⊆ closedBall (0 : Space3) 1 := by
  have hδR : (δ : ℝ) ≤ 1 / 2 := by exact_mod_cast hδ
  have hseg : segment ℝ (centredTube δ).x (centredTube δ).y ⊆
      closedBall (0 : Space3) (1 / 2) := by
    refine (convex_closedBall (0 : Space3) (1 / 2)).segment_subset ?_ ?_ <;>
      simp [centredTube, Metric.mem_closedBall, dist_eq_norm, norm_smul, PiLp.norm_single]
  rw [(centredTube δ).carrier_eq_cthickening]
  refine (cthickening_subset_of_subset _ hseg).trans ?_
  rw [cthickening_closedBall (by positivity) (by norm_num)]
  exact closedBall_subset_closedBall (by linarith)

/-- The fully shaded tube: shading equal to the whole carrier. -/
def fullShadedTube {δ : NNReal} (Tb : Tube δ Space3) : ShadedTube δ Space3 where
  toTube := Tb
  shade := Tb.carrier
  measurableSet_shade := by
    rw [Tb.carrier_eq_cthickening]
    exact isClosed_cthickening.measurableSet
  shade_subset := subset_rfl

/-- **Non-vacuity certificate for `WolffHairbrushBroad`.**

The hypothesis bundle of `WolffHairbrushBroad` is satisfiable with a *nonempty*
family, so the leaf cannot be discharged by an inconsistent bundle: take
`θ = δ`, the single fully shaded tube centred at the origin, and `R` that same
tube.  (For this witness the conclusion asks for
`κ δ^{ε/2} δ^{3/2} δ^{1/2} ≤ |T|`, i.e. `κ δ^{ε/2} δ² ≲ δ²`, which holds for
small `κ`; the leaf therefore has real content at this witness as well.) -/
theorem wolffHairbrushBroad_hypotheses_satisfiable {δ : NNReal} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) {ν : ℝ} (hν : 0 ≤ ν) :
    ∃ (s : Finset (Fin 1)) (T : Fin 1 → ShadedTube δ Space3) (R : Tube δ Space3),
      s.Nonempty ∧ IsTubeShadingFamily s T ∧
      (∀ i ∈ s, (T i).carrier ⊆ R.carrier) ∧
      IsDense s T ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ ∧
      katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-ν) ∧
      IsBroadAtScale s T δ ν := by
  have hδ1' : δ ≤ 1 := le_trans hδ1 (by norm_num)
  refine ⟨Finset.univ, fun _ => fullShadedTube (centredTube δ), centredTube δ,
    ⟨0, Finset.mem_univ 0⟩, ⟨fun i _ => centredTube_subset_ball hδ1, ?_⟩,
    fun i _ => subset_rfl, ?_,
    le_trans (katzTaoConvexWolffConstant_le_one_of_card_le_one hδ
      (by simp) _) (one_le_rpow_neg hδ1' hν),
    isBroadAtScale_of_le_delta _ _ hδ le_rfl ν⟩
  · intro i _ j _ hij
    exact absurd (Subsingleton.elim i j) hij
  · rw [IsDense]
    set d : NNReal := ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ with hd
    have hδ1R : (δ : ℝ) ≤ 1 := by
      have : (δ : ℝ) ≤ 1 / 2 := by exact_mod_cast hδ1
      linarith
    have hd1 : d ≤ 1 := by
      have h : (d : ℝ) ≤ (1 : ℝ) := Real.rpow_le_one δ.coe_nonneg hδ1R hν
      exact_mod_cast h
    have hone : (d : ENNReal) ≤ 1 := by exact_mod_cast hd1
    calc (d : ENNReal) * ∑ _i ∈ (Finset.univ : Finset (Fin 1)),
            volume (fullShadedTube (centredTube δ)).carrier
        ≤ 1 * ∑ _i ∈ (Finset.univ : Finset (Fin 1)),
            volume (fullShadedTube (centredTube δ)).carrier := by gcongr
      _ = ∑ _i ∈ (Finset.univ : Finset (Fin 1)),
            volume (fullShadedTube (centredTube δ)).shade := by
          rw [one_mul]
          rfl

/-! ### No `δ`-tube with `δ > 1/2` fits in the unit ball

A `δ`-tube has diameter `1 + 2δ`, so a family of `δ`-tubes of the unit ball is
empty unless `δ ≤ 1/2`.  This delimits the "large `δ`" end of every statement in
this file: at `δ` above `1/2` all of them are vacuous, and at `δ = 1/2` the
`δ^{-ε/8}`-type counting budgets are within a factor `2^{ε/8}` of `1`. -/

/-- **A `δ`-tube contained in the unit ball forces `δ ≤ 1/2`.**

The tube contains `y + δ·u` and `x - δ·u`, where `u = y - x` is the unit
direction, and these are at distance `1 + 2δ`; two points of the unit ball are
at distance at most `2`. -/
theorem le_half_of_tube_subset_closedBall {δ : NNReal} (R : Tube δ Space3)
    (h : R.carrier ⊆ closedBall (0 : Space3) 1) : δ ≤ 1 / 2 := by
  set u : Space3 := R.y - R.x with hu
  have hnu : ‖u‖ = 1 := R.norm_direction
  have hmem : ∀ z ∈ segment ℝ R.x R.y, ∀ p : Space3, dist p z ≤ (δ : ℝ) → p ∈ R.carrier := by
    intro z hz p hp
    rw [R.carrier_eq]
    exact Set.mem_biUnion hz (by simpa [Metric.mem_closedBall] using hp)
  have hp : R.y + (δ : ℝ) • u ∈ R.carrier := by
    refine hmem R.y (right_mem_segment ℝ _ _) _ ?_
    simp [norm_smul, hnu, abs_of_nonneg δ.coe_nonneg]
  have hq : R.x - (δ : ℝ) • u ∈ R.carrier := by
    refine hmem R.x (left_mem_segment ℝ _ _) _ ?_
    simp [norm_smul, hnu, abs_of_nonneg δ.coe_nonneg]
  have hdist : dist (R.y + (δ : ℝ) • u) (R.x - (δ : ℝ) • u) = 1 + 2 * (δ : ℝ) := by
    have he : (R.y + (δ : ℝ) • u) - (R.x - (δ : ℝ) • u) = (1 + 2 * (δ : ℝ)) • u := by
      rw [hu]; module
    rw [dist_eq_norm, he, norm_smul, hnu, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 + 2 * (δ : ℝ))]
  have h1 : dist (R.y + (δ : ℝ) • u) (0 : Space3) ≤ 1 := by
    simpa [Metric.mem_closedBall] using h hp
  have h2 : dist (R.x - (δ : ℝ) • u) (0 : Space3) ≤ 1 := by
    simpa [Metric.mem_closedBall] using h hq
  have := dist_triangle (R.y + (δ : ℝ) • u) (0 : Space3) (R.x - (δ : ℝ) • u)
  rw [hdist] at this
  rw [dist_comm (0 : Space3)] at this
  have hle : 1 + 2 * (δ : ℝ) ≤ 2 := le_trans this (by linarith)
  have : (δ : ℝ) ≤ 1 / 2 := by linarith
  exact_mod_cast this

/-- A nonempty family of `δ`-tubes of the unit ball forces `δ ≤ 1/2`. -/
theorem le_half_of_isTubeShadingFamily {δ : NNReal} {ι : Type u} {s : Finset ι}
    {T : ι → ShadedTube δ Space3} (hfam : IsTubeShadingFamily s T) (hs : s.Nonempty) :
    δ ≤ 1 / 2 := by
  obtain ⟨i, hi⟩ := hs
  exact le_half_of_tube_subset_closedBall (T i).toTube (hfam.1 i hi)

/-! ### The Frostman slab hypothesis forces a large family

Two facts recorded here because they are what makes the ambient hypothesis
bundle of `HairbrushCover` (and of `WolffHairbrushEstimate`) *quantitatively*
non-trivial: a nonempty family with `FS(𝕋) ≤ δ^{-η}` must have `#𝕋 ≳ δ^{η-1}`
members.  In particular no bounded family satisfies the ambient bundle, which
is why the non-vacuity certificates of this file certify the *class-level*
bundles (`WolffHairbrushBroad`, `BalancedBroadCover`), where `FS` is absent, and
not the ambient one. -/

/-- **A slab of thickness `δ` through one tube bounds `FS` from below.**

Any single tube of the family lies in a slab of thickness `δ`
(`exists_slabTestSet_containing_tube`), whose volume is at most `δ |B(0,2)|`
(`volume_slabTestSet_le`).  The defining inequality of
`frostmanSlabWolffConstant` tested against that slab reads
`1 ≤ FS · |W| · #𝕋 ≤ FS · δ|B(0,2)| · #𝕋`. -/
theorem one_le_frostmanSlabWolffConstant_mul {δ : NNReal} (hδ : 0 < δ) {ι : Type u}
    {s : Finset ι} (hs : s.Nonempty) (T : ι → ShadedTube δ Space3)
    (hfam : IsTubeShadingFamily s T) :
    (1 : ENNReal) ≤ frostmanSlabWolffConstant s T *
      ((δ : ENNReal) * volume (closedBall (0 : Space3) 2)) * (s.card : ENNReal) := by
  obtain ⟨i₀, hi₀⟩ := hs
  obtain ⟨W, hWt, hWsub⟩ :=
    exists_slabTestSet_containing_tube (T i₀).toTube (hfam.1 i₀ hi₀) (le_refl δ)
  set B : ENNReal := volume (closedBall (0 : Space3) 2) with hB
  have hB0 : B ≠ 0 := (measure_closedBall_pos volume (0 : Space3) (by norm_num)).ne'
  have hBtop : B ≠ ⊤ := measure_closedBall_lt_top.ne
  have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
  have hNpos : 0 < s.card := Finset.card_pos.mpr ⟨i₀, hi₀⟩
  have hN0 : (s.card : ENNReal) ≠ 0 := by simpa using hNpos.ne'
  have hNtop : (s.card : ENNReal) ≠ ⊤ := by simp
  set K : ENNReal := (δ : ENNReal) * B * (s.card : ENNReal) with hK
  have hK0 : K ≠ 0 := by
    rw [hK]; exact mul_ne_zero (mul_ne_zero hδ0E hB0) hN0
  have hKtop : K ≠ ⊤ := by
    rw [hK]; exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hBtop) hNtop
  have hWvol : volume W.carrier ≤ (δ : ENNReal) * B := by
    have h := volume_slabTestSet_le W
    rwa [hWt] at h
  have hmem : i₀ ∈ (@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
      (Classical.decPred _) s) :=
    (@Finset.mem_filter ι (fun i => (T i).carrier ⊆ W.carrier)
      (Classical.decPred _) s i₀).mpr ⟨hi₀, hWsub⟩
  have hone : (1 : ENNReal) ≤ ((@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
      (Classical.decPred _) s).card : ENNReal) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Finset.card_ne_zero_of_mem hmem)
  have hdiv : 1 / K ≤ frostmanSlabWolffConstant s T := by
    refine le_sInf ?_
    rintro C ⟨-, hC⟩
    have hCW := hC W
    have h1 : (1 : ENNReal) ≤ C * volume W.carrier * (s.card : ENNReal) := hone.trans hCW
    have h2 : (1 : ENNReal) ≤ C * K := by
      refine h1.trans ?_
      rw [hK]
      calc C * volume W.carrier * (s.card : ENNReal)
          ≤ C * ((δ : ENNReal) * B) * (s.card : ENNReal) := by gcongr
        _ = C * ((δ : ENNReal) * B * (s.card : ENNReal)) := by ring
    exact ENNReal.div_le_of_le_mul h2
  calc (1 : ENNReal) = 1 / K * K := (ENNReal.div_mul_cancel hK0 hKtop).symm
    _ ≤ frostmanSlabWolffConstant s T * K := by gcongr
    _ = frostmanSlabWolffConstant s T * ((δ : ENNReal) * B) * (s.card : ENNReal) := by
        rw [hK]; ring

/-- **The Frostman slab hypothesis forces `#𝕋 ≳ δ^{η-1}`.**

Consequence of `one_le_frostmanSlabWolffConstant_mul`: a nonempty family
satisfying the ambient hypothesis `FS(𝕋) ≤ δ^{-η}` of `HairbrushCover` has at
least `δ^{η-1}/|B(0,2)|` members. -/
theorem rpow_le_card_of_frostmanSlabWolffConstant {δ : NNReal} (hδ : 0 < δ)
    {ι : Type u} {s : Finset ι} (hs : s.Nonempty) (T : ι → ShadedTube δ Space3)
    (hfam : IsTubeShadingFamily s T) {η : ℝ}
    (hell : frostmanSlabWolffConstant s T ≤ (δ : ENNReal) ^ (-η)) :
    (δ : ENNReal) ^ (η - 1) ≤
      volume (closedBall (0 : Space3) 2) * (s.card : ENNReal) := by
  set B : ENNReal := volume (closedBall (0 : Space3) 2) with hB
  have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
  have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hkey := one_le_frostmanSlabWolffConstant_mul hδ hs T hfam
  have hstep : (1 : ENNReal) ≤ (δ : ENNReal) ^ (1 - η) * (B * (s.card : ENNReal)) := by
    refine hkey.trans ?_
    have hd : (δ : ENNReal) ^ (-η) * (δ : ENNReal) = (δ : ENNReal) ^ (1 - η) := by
      rw [show (1 - η : ℝ) = -η + 1 by ring, ENNReal.rpow_add _ _ hδ0E hδtopE,
        ENNReal.rpow_one]
    calc frostmanSlabWolffConstant s T * ((δ : ENNReal) * B) * (s.card : ENNReal)
        ≤ (δ : ENNReal) ^ (-η) * ((δ : ENNReal) * B) * (s.card : ENNReal) := by gcongr
      _ = ((δ : ENNReal) ^ (-η) * (δ : ENNReal)) * (B * (s.card : ENNReal)) := by ring
      _ = (δ : ENNReal) ^ (1 - η) * (B * (s.card : ENNReal)) := by rw [hd]
  have hmul : (δ : ENNReal) ^ (η - 1) * (δ : ENNReal) ^ (1 - η) = 1 := by
    rw [← ENNReal.rpow_add _ _ hδ0E hδtopE]
    norm_num
  calc (δ : ENNReal) ^ (η - 1) = (δ : ENNReal) ^ (η - 1) * 1 := by rw [mul_one]
    _ ≤ (δ : ENNReal) ^ (η - 1) * ((δ : ENNReal) ^ (1 - η) * (B * (s.card : ENNReal))) := by
        gcongr
    _ = ((δ : ENNReal) ^ (η - 1) * (δ : ENNReal) ^ (1 - η)) * (B * (s.card : ENNReal)) := by
        ring
    _ = B * (s.card : ENNReal) := by rw [hmul, one_mul]

/-! ### The two halves of Leaf 1

`HairbrushCover` bundles two steps of the source which are logically
independent and are proved by different arguments:

* the *scale selection*: the standard reductions produce the scale `θ` and a
  refinement of the family which is non-concentrated at that scale
  (`BroadScaleRefinement`);
* the *balanced partitioning cover* at the scale so produced, together with the
  essential disjointness of the shadings of distinct classes
  (`BalancedBroadCover`).

`hairbrushCover_of_refinement_of_cover` recombines them.  The `δ^{-ε/8}`
counting budget of `HairbrushCover` is split evenly, `δ^{-ε/16}` to each half.

Note that the class-level broadness demanded by `BalancedBroadCover` really has
to be an *output* of the cover step, not something derived afterwards from the
ambient broadness: broadness is a ratio, so it is not inherited by subfamilies.
What makes it available to the cover step is that the shadings of distinct
classes are essentially disjoint, so a point of the shading of a class sees only
tubes of that class, and the ambient count at that point *is* the class count. -/

/-- **Leaf 1a: the standard reductions.**

Not refuted, but no longer used: the companion half `BalancedBroadCover` is
false, so `hairbrushCover_holds` is left as a single obligation rather than
being derived from this one plus a false one.

Source: `blueprint/src/WZ2/250224e_K3.tex`, Appendix `WolffHairbrushSec`, the
sentence beginning "Applying standard reductions" together with the display
that follows it.

Out of a family satisfying the hypotheses of Wang--Zahl Proposition 1.10 the
reductions produce a scale `θ ∈ [δ, 1]` and a refinement `𝕋' ⊆ 𝕋` retaining a
`δ^{ε/16}`-fraction of the tubes, which is still `δ^ν`-dense and which is
non-concentrated ("broad") at the scale `θ`: through any point of a shading, the
directions of the tubes do not cluster in a cap of radius `r ∈ [δ, θ]` more than
the factor `(r/θ)^ν` allows.

As in `HairbrushCover` the target quality `ν` is an input: the source fixes `η`
"to be chosen below" and then spends it, so the reduction must deliver any
prescribed `ν` at the cost of a smaller input `η`.

**Restated 2026-08: the refinement is of the shadings too.**  The "`≥ δ^η` dense
refinement" of the source is a refinement of the *shaded* family: it discards
tubes **and** shrinks shadings.  The reduction therefore returns a shaded family
`T'` with `IsShadingRefinement s' T' T`, and both the density and the broadness
are asserted of `T'`.  Keeping the input shading fixed here was the second
fidelity defect of the split: `IsBroadAtScale s' T θ ν` forces every point of
every *input* shading to be covered by at least `(θ/δ)^ν` tubes
(`WolffHairbrushGuardrails.rpow_le_multiplicity_of_isBroadAtScale`), which the
far end of a tube of a bush fails; the source obtains its broadness only after
passing to the high-multiplicity part of the shading. -/
def BroadScaleRefinement : Prop :=
  ∀ ε > (0 : ℝ), ∀ ν > (0 : ℝ), ∃ η : ℝ, 0 < η ∧ η ≤ ν ∧
    ∀ (δ : NNReal), 0 < δ → δ ≤ 1 →
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        IsTubeShadingFamily s T →
        IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ →
        katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        frostmanSlabWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        ∃ θ : NNReal, δ ≤ θ ∧ θ ≤ 1 ∧
          ∃ (s' : Finset ι) (T' : ι → ShadedTube δ Space3), s' ⊆ s ∧
            IsShadingRefinement s' T' T ∧
            (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 16)) * (s'.card : ENNReal) ∧
            IsDense s' T' ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ ∧
            IsBroadAtScale s' T' θ ν

/-- **Leaf 1b: the balanced partitioning cover at a given scale.  REFUTED.**

**This statement is false**; see
`Kakeya.DimensionThree.MainLemma2.WangZahl.WolffHairbrushGuardrails.not_balancedBroadCover`
for the compiler-checked refutation and for the discussion of what a faithful
replacement has to say.  It is kept as the record of a rejected split of
`HairbrushCover`, and is *not* used to prove `hairbrushCover_holds`.  The defect
is the last conjunct, the constant-`1` essential disjointness: because `θ` is an
input here, the statement must also hold at `θ = δ`, and it does not.

Source: `blueprint/src/WZ2/250224e_K3.tex`, Appendix `WolffHairbrushSec`, from
"we may cover `𝕋` by `θ`-tubes" to "After a further refinement, we may suppose
that each set `𝕋^{T_θ}` is `δ^{3η}`-dense", together with the displayed
identity `broadAtScaleTheta` (of which only the inequality
`∑_{T_θ} |∪_{T ∈ 𝕋[T_θ]} Y(T)| ≤ |∪_{T ∈ 𝕋} Y(T)|` is used).

Given a `δ^ν`-dense family which is non-concentrated at the scale `θ ∈ [δ, 1]`,
the covering step produces a family of `θ`-tubes whose classes consist of
`δ`-tubes they contain, are *balanced* (`cnt j' ≤ 2 cnt j`, the output of dyadic
pigeonholing), retain a `δ^{ε/16}`-fraction of the family, are individually
`δ^ν`-dense and non-concentrated at scale `θ`, and have essentially disjoint
shadings.

The ambient Katz--Tao hypothesis is kept, at the quality `ν`.  It costs nothing
in the recombination -- `katzTaoConvexWolffConstant` is monotone under
subfamilies (`katzTaoConvexWolffConstant_le_of_subset`), so the refinement
produced by `BroadScaleRefinement` inherits it verbatim -- and it must not be
dropped: without it the counting budget `δ^{-ε/16}` has no slack at the largest
admissible scales, where every tube of the family has to be classified and the
shadings of distinct classes must therefore be genuinely disjoint.  Dropping a
hypothesis that the recombination hands down for free is exactly the defect that
made the pre-repair Leaf 2 false (see
`Kakeya.DimensionThree.MainLemma2.WangZahl.WolffHairbrushGuardrails`).

The Frostman slab hypothesis is *not* an input: it is not inherited by a
subfamily (its definition carries the `#𝕋` normalization), so a leaf carrying it
would not compose with `BroadScaleRefinement` without a further loss, and no
bounded family satisfies it (`rpow_le_card_of_frostmanSlabWolffConstant`), so
carrying it would leave the leaf's bundle without a satisfiability witness. -/
def BalancedBroadCover : Prop :=
  ∀ ε > (0 : ℝ), ∀ ν > (0 : ℝ),
    ∀ (δ : NNReal), 0 < δ → ∀ (θ : NNReal), δ ≤ θ → θ ≤ 1 →
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        IsTubeShadingFamily s T →
        IsDense s T ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ →
        katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-ν) →
        IsBroadAtScale s T θ ν →
        ∃ (J : Type u) (P : Finset J) (parent : J → Tube θ Space3) (part : J → Finset ι),
          (∀ j ∈ P, part j ⊆
            @Finset.filter ι (fun i => (T i).carrier ⊆ (parent j).carrier)
              (Classical.decPred _) s) ∧
          (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 16)) *
            (∑ j ∈ P, ((part j).card : ENNReal)) ∧
          (∀ j ∈ P, ∀ j' ∈ P, ((part j').card : ENNReal) ≤ 2 * ((part j).card : ENNReal)) ∧
          (∀ j ∈ P,
            IsDense (part j) T ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩) ∧
          (∀ j ∈ P, IsBroadAtScale (part j) T θ ν) ∧
          (∑ j ∈ P, volume (ShadedBody.iUnionShade (part j)
              fun i => (T i).toShadedBody)) ≤
            volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)

/-- **Leaf 1b, corrected: the balanced partitioning cover with the source's
per-class shading refinement.**

This replaces the refuted `BalancedBroadCover` above.  The only change is the
degree of freedom the source actually uses and the fixed-shading form could not
express: the cover returns, for each class `j`, a shaded family `Y j` refining
the input shadings on that class, and

* the density conjunct is asked of `Y j`, at the target quality `ν`, while the
  *input* is `δ^η`-dense at an `η ≤ ν` handed out by the leaf — this is the
  source's "After a further refinement, we may suppose that each set
  `𝕋^{T_θ}` is `δ^{3η}`-dense" (`blueprint/src/WZ2/250224e_K3.tex:5748`), whose
  density loss is carried by `η ≤ ν` rather than by an invented exponent;
* the broadness conjunct is asked of `Y j`, at quality `ν`, the input broadness
  being at the weaker quality `η`;
* the essential-disjointness conjunct compares `∑_j |∪_{i ∈ part j} Y j i|
  with `|∪_{i ∈ s} Y(T i)|` — the *refined* shadings on the left.

That last change is what removes the refutation.  At `θ = δ` the witness of
`WolffHairbrushGuardrails.not_balancedBroadCover` (two orthogonal fully shaded
`δ`-tubes `A`, `B` through the origin, no `δ`-tube containing both, so the two
tubes must land in different classes) forced `2|A| ≤ |A ∪ B| < 2|A|` for the
fixed shadings.  With per-class shadings the cover may return `Y₀ = A \ B` and
`Y₁ = B`, and then `|A \ B| + |B| = |A ∪ B|` exactly.

Everything else is verbatim from `BalancedBroadCover`: the classes consist of
`δ`-tubes contained in their `θ`-tube, they retain a `δ^{ε/16}`-fraction of the
family, they are balanced (`cnt j' ≤ 2 cnt j`, the output of dyadic
pigeonholing), and the ambient Katz--Tao hypothesis is kept — it is inherited by
a class verbatim even after the shadings are refined
(`IsShadingRefinement.katzTao_le`), since `katzTaoConvexWolffConstant` sees only
carriers and carries no `#𝕋` normalization.  The Frostman slab hypothesis is
still **not** an input, for the reasons recorded above
`katzTaoConvexWolffConstant_mono`.

`refinedBalancedBroadCover_of_balancedBroadCover` records that this is a
*weakening*: the refuted statement implies it (take `Y j = T`), so nothing that
the broken split would have supplied is lost. -/
def RefinedBalancedBroadCover : Prop :=
  ∀ ε > (0 : ℝ), ∀ ν > (0 : ℝ), ∃ η : ℝ, 0 < η ∧ η ≤ ν ∧
    ∀ (δ : NNReal), 0 < δ → ∀ (θ : NNReal), δ ≤ θ → θ ≤ 1 →
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        IsTubeShadingFamily s T →
        IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ →
        katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        IsBroadAtScale s T θ η →
        ∃ (J : Type u) (P : Finset J) (parent : J → Tube θ Space3) (part : J → Finset ι)
          (Y : J → ι → ShadedTube δ Space3),
          (∀ j ∈ P, part j ⊆
            @Finset.filter ι (fun i => (T i).carrier ⊆ (parent j).carrier)
              (Classical.decPred _) s) ∧
          (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 16)) *
            (∑ j ∈ P, ((part j).card : ENNReal)) ∧
          (∀ j ∈ P, ∀ j' ∈ P, ((part j').card : ENNReal) ≤ 2 * ((part j).card : ENNReal)) ∧
          (∀ j ∈ P, IsShadingRefinement (part j) (Y j) T) ∧
          (∀ j ∈ P,
            IsDense (part j) (Y j) ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩) ∧
          (∀ j ∈ P, IsBroadAtScale (part j) (Y j) θ ν) ∧
          (∑ j ∈ P, volume (ShadedBody.iUnionShade (part j)
              fun i => (Y j i).toShadedBody)) ≤
            volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)

/-- **The corrected Leaf 1b is a weakening of the refuted one.**

`BalancedBroadCover` is false, so this implication has no positive content; it
is recorded to certify that the restatement did not smuggle in a *new* demand.
Take `η = ν` and `Y j = T`: the refuted statement's fixed shadings are their own
refinement. -/
theorem refinedBalancedBroadCover_of_balancedBroadCover
    (H : BalancedBroadCover.{u}) : RefinedBalancedBroadCover.{u} := by
  intro ε hε ν hν
  refine ⟨ν, hν, le_rfl, ?_⟩
  intro δ hδ θ hδθ hθ1 ι s T hfam hdens hckt hbroad
  obtain ⟨J, P, parent, part, hpart, hcount, hbal, hdensj, hbroadj, hadd⟩ :=
    H ε hε ν hν δ hδ θ hδθ hθ1 s T hfam hdens hckt hbroad
  exact ⟨J, P, parent, part, fun _ => T, hpart, hcount, hbal,
    fun j _ => IsShadingRefinement.rfl' _ T, hdensj, hbroadj, hadd⟩

/-- The shaded union is monotone in the index family. -/
theorem volume_iUnionShade_mono {δ : NNReal} {ι : Type u} {s' s : Finset ι}
    (hss : s' ⊆ s) (T : ι → ShadedTube δ Space3) :
    volume (ShadedBody.iUnionShade s' fun i => (T i).toShadedBody) ≤
      volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
  refine measure_mono ?_
  intro x hx
  simp only [Set.mem_iUnion, exists_prop] at hx ⊢
  obtain ⟨i, hi, hxi⟩ := hx
  exact ⟨i, hss hi, hxi⟩

/-- A subfamily of a tube shading family is a tube shading family. -/
theorem IsTubeShadingFamily.subset {δ : NNReal} {ι : Type u} {s' s : Finset ι}
    {T : ι → ShadedTube δ Space3} (hfam : IsTubeShadingFamily s T) (hss : s' ⊆ s) :
    IsTubeShadingFamily s' T :=
  ⟨fun i hi => hfam.1 i (hss hi), hfam.2.mono (by exact_mod_cast hss)⟩

/-- **Leaf 1a + Leaf 1b = Leaf 1**, with the corrected Leaf 1b.

The scale `θ` and the refined family `(𝕋', Y')` come from
`BroadScaleRefinement`; the cover of `𝕋'` at that scale, together with the
per-class shading refinements, comes from `RefinedBalancedBroadCover`.  The
arithmetic is the composition of the two `δ^{-ε/16}` counting budgets into the
`δ^{-ε/8}` of `HairbrushCover`, the transitivity of shading refinement
(`IsShadingRefinement.trans`), and the two monotonicities of the shaded union
(`IsShadingRefinement.volume_iUnionShade_le` along `Y' ⊆ Y`, and
`volume_iUnionShade_mono` along `𝕋' ⊆ 𝕋`).

The quality bookkeeping: `RefinedBalancedBroadCover` is asked for the target
`ν` and hands out an admissible input quality `η₂ ≤ ν`; `BroadScaleRefinement`
is then asked for the target `η₂` and hands out `η₁ ≤ η₂`, which is the `η` of
`HairbrushCover`.  This is the only order that works, because the two qualities
are monotone in *opposite* directions: `δ^η`-density gets stronger as `η`
shrinks, while `η`-broadness gets stronger as `η` grows. -/
theorem hairbrushCover_of_refinement_of_cover
    (HR : BroadScaleRefinement.{u}) (HB : RefinedBalancedBroadCover.{u}) :
    HairbrushCover.{u} := by
  intro ε hε ν hν
  obtain ⟨η₂, hη₂, hη₂ν, hB⟩ := HB ε hε ν hν
  obtain ⟨η₁, hη₁, hη₁₂, hR⟩ := HR ε hε η₂ hη₂
  refine ⟨η₁, hη₁, le_trans hη₁₂ hη₂ν, ?_⟩
  intro δ hδ hδ1 ι s T hfamily hdense hm hell
  have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
  have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1E : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  obtain ⟨θ, hδθ, hθ1, s', T', hss, href1, hcount, hdens', hbroad'⟩ :=
    hR δ hδ hδ1 s T hfamily hdense hm hell
  have hθ0 : 0 < θ := lt_of_lt_of_le hδ hδθ
  have hckt' : katzTaoConvexWolffConstant s' T' ≤ (δ : ENNReal) ^ (-η₂) := by
    refine href1.katzTao_le hss ?_
    exact hm.trans (ENNReal.rpow_le_rpow_of_exponent_ge hδ1E (by linarith : -η₂ ≤ -η₁))
  obtain ⟨J, P, parent, part, Y, hpart, hcount', hbal, href2, hdensj, hbroadj, hadd⟩ :=
    hB δ hδ θ hδθ hθ1 s' T' (href1.isTubeShadingFamily (hfamily.subset hss)) hdens'
      hckt' hbroad'
  have hpartsub : ∀ j ∈ P, part j ⊆ s' := by
    intro j hj
    exact (hpart j hj).trans
      (@Finset.filter_subset ι (fun i => (T' i).carrier ⊆ (parent j).carrier)
        (Classical.decPred _) s')
  refine ⟨θ, hθ0, hθ1, J, P, parent, part, Y, ?_, ?_, hbal, ?_, hdensj, hbroadj, ?_⟩
  · intro j hj i hi
    have hi' := (@Finset.mem_filter ι (fun i => (T' i).carrier ⊆ (parent j).carrier)
      (Classical.decPred _) s' i).mp (hpart j hj hi)
    refine (@Finset.mem_filter ι (fun i => (T i).carrier ⊆ (parent j).carrier)
      (Classical.decPred _) s i).mpr ⟨hss hi'.1, ?_⟩
    rw [← href1.carrier_eq hi'.1]
    exact hi'.2
  · have hpow : (δ : ENNReal) ^ (-(ε / 16)) * (δ : ENNReal) ^ (-(ε / 16))
        = (δ : ENNReal) ^ (-(ε / 8)) := by
      rw [← ENNReal.rpow_add _ _ hδ0E hδtopE]
      congr 1
      ring
    calc (s.card : ENNReal)
        ≤ (δ : ENNReal) ^ (-(ε / 16)) * (s'.card : ENNReal) := hcount
      _ ≤ (δ : ENNReal) ^ (-(ε / 16)) *
            ((δ : ENNReal) ^ (-(ε / 16)) * (∑ j ∈ P, ((part j).card : ENNReal))) := by
          gcongr
      _ = ((δ : ENNReal) ^ (-(ε / 16)) * (δ : ENNReal) ^ (-(ε / 16))) *
            (∑ j ∈ P, ((part j).card : ENNReal)) := by ring
      _ = (δ : ENNReal) ^ (-(ε / 8)) * (∑ j ∈ P, ((part j).card : ENNReal)) := by
          rw [hpow]
  · intro j hj
    exact (href2 j hj).trans (href1.mono (hpartsub j hj))
  · refine hadd.trans (le_trans href1.volume_iUnionShade_le ?_)
    exact volume_iUnionShade_mono hss T

/-- **Non-vacuity certificate for `BalancedBroadCover`.**

The hypothesis bundle of `BalancedBroadCover` is satisfiable with a *nonempty*
family: take `θ = δ`, where broadness is automatic
(`isBroadAtScale_of_le_delta`), and the single fully shaded tube centred at the
origin.  So the leaf cannot be discharged from an inconsistent bundle. -/
theorem balancedBroadCover_hypotheses_satisfiable {δ : NNReal} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) {ν : ℝ} (hν : 0 ≤ ν) :
    ∃ (s : Finset (Fin 1)) (T : Fin 1 → ShadedTube δ Space3),
      s.Nonempty ∧ IsTubeShadingFamily s T ∧
      IsDense s T ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ ∧
      katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-ν) ∧
      IsBroadAtScale s T δ ν := by
  obtain ⟨s, T, R, hne, hfam, -, hdens, hckt, hbroad⟩ :=
    wolffHairbrushBroad_hypotheses_satisfiable hδ hδ1 hν
  exact ⟨s, T, hne, hfam, hdens, hckt, hbroad⟩

/-! ### The Katz--Tao hypothesis of Leaf 2, in counting form

The repair of Leaf 2 restored the hypothesis `CKT(𝕋) ≤ δ^{-ν}`.  Tested against
the `θ`-tube `R` that contains the whole class, that hypothesis *is* the
source's `δ`-separation of directions, in the currency of Definition 1.5:
`#𝕋 ≤ δ^{-ν} |R|/|T| ≍ δ^{-ν}(θ/δ)²`.  The first theorem below is that test;
the second settles Leaf 2 in the degenerate regime `θ ≤ δ`, where the class is
confined to a single `δ`-tube and the counting bound alone already beats the
required volume.  All the content of Leaf 2 therefore sits at `θ ≫ δ`. -/

/-- **The Katz--Tao constant tested against a `θ`-tube containing the family.**

`#𝕋 · |T| ≤ CKT(𝕋) · |R|` for any family of `δ`-tubes all contained in the
`θ`-tube `R`; the carrier of a tube is convex, so `R` is an admissible convex
test set.  With `CKT(𝕋) ≤ δ^{-ν}` this is the quantitative content of the
hypothesis restored by the repair of `WolffHairbrushBroad`. -/
theorem card_mul_tubeVolume_le_katzTao_of_subset_tube
    {δ : NNReal} (hδ : 0 < δ) {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3)
    {θ : NNReal} (hθ : 0 < θ) (R : Tube θ Space3)
    (hsub : ∀ i ∈ s, (T i).carrier ⊆ R.carrier) :
    (s.card : ENNReal) * tubeVolume δ ≤
      katzTaoConvexWolffConstant s T * volume R.carrier := by
  obtain ⟨hV0, hVtop⟩ := tubeVolume_pos_and_ne_top hδ
  set B : ENNReal := volume R.carrier with hB
  have hc3 : (0 : ENNReal) < ((Tube.le_volume.c 3 : NNReal) : ENNReal) := by
    exact_mod_cast Tube.le_volume.c_pos 3
  have hθE : (0 : ENNReal) < (θ : ENNReal) := by exact_mod_cast hθ
  have hlow : ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (θ : ENNReal) ^ (3 - 1 : ℕ) ≤ B := by
    simpa using Tube.le_volume R
  have hB0 : B ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le ?_ hlow)
    exact ENNReal.mul_pos hc3.ne' (pow_ne_zero _ hθE.ne')
  have hBtop : B ≠ ⊤ := (R.isCompact'.measure_lt_top).ne
  set W : ConvexTestSet := ⟨R.carrier, R.convex'.convex⟩ with hW
  have hfilter : (@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
      (Classical.decPred _) s) = s := by
    refine @Finset.filter_true_of_mem ι (fun i => (T i).carrier ⊆ W.carrier)
      (Classical.decPred _) s ?_
    intro i hi
    exact hsub i hi
  have key : ∀ C ∈ {C : ENNReal | 0 < C ∧ ∀ W : ConvexTestSet,
      ((@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s).card : ENNReal) ≤
        C * volume W.carrier * (tubeVolume δ)⁻¹},
      (s.card : ENNReal) * tubeVolume δ / B ≤ C := by
    rintro C ⟨-, hC⟩
    have hCB := hC W
    rw [hfilter] at hCB
    refine ENNReal.div_le_of_le_mul ?_
    calc (s.card : ENNReal) * tubeVolume δ
        ≤ (C * B * (tubeVolume δ)⁻¹) * tubeVolume δ := mul_le_mul_right' hCB _
      _ = C * B * ((tubeVolume δ)⁻¹ * tubeVolume δ) := by ring
      _ = C * B := by rw [ENNReal.inv_mul_cancel hV0.ne' hVtop, mul_one]
  have hdiv : (s.card : ENNReal) * tubeVolume δ / B ≤ katzTaoConvexWolffConstant s T :=
    le_sInf key
  have h := mul_le_mul_right' hdiv B
  refine le_trans (le_of_eq ?_) h
  rw [ENNReal.div_mul_cancel hB0 hBtop]


/-! ### Leaf 2 in the degenerate regime `θ ≤ δ` -/

/-- The constant of `wolffHairbrushBroad_of_theta_le_delta`: `c^{3/2}/4`, where
`c = Tube.le_volume.c 3` is the dimensional constant of the tube volume lower
bound `c δ² ≤ |T|`. -/
noncomputable def smallScaleHairbrushConstant : NNReal :=
  (Tube.le_volume.c 3) ^ ((3 : ℝ) / 2) / 4

/-- **Leaf 2 holds in the whole window `θ ≤ δ^{ν+1-ε/3}`.**

The trivial route to `WolffHairbrushBroad` — the Katz--Tao count
`#𝕋 ≤ δ^{-ν}|R|/|T|` for a family confined to the `θ`-tube `R`, against the
one-tube volume bound `|∪Y| ≥ δ^ν|T|` — closes the leaf exactly when

`θ^{3/2} ≤ (c^{3/2}/(4κ)) δ^{3ν/2 + 3/2 - ε/2)}`, i.e. `θ ≤ δ^{ν + 1 - ε/3}`

at the constant `κ = smallScaleHairbrushConstant = c^{3/2}/4`.  Since `ν` is
existential in `WolffHairbrushBroad`, taking `ν` small widens the closed window
to `θ ≤ δ^{1 - ε/3 + ν}`, i.e. a factor `δ^{-(ε/3 - ν)}` beyond `θ = δ`.
`wolffHairbrushBroad_of_theta_le_delta` is the case `ν = ε/3`, where the window
is exactly `θ ≤ δ`.

Neither the essential distinctness of the family nor its broadness is used, so
this locates the content of Leaf 2 at `θ ≫ δ^{1-ε/3}`, where the count
`δ^{-ν}(θ/δ)^2` is too weak for the trivial bound and Wolff's hairbrush
argument `\cite{Wol95}` is needed. -/
theorem wolffHairbrushBroad_of_theta_le {ε ν : ℝ}
    {δ : NNReal} (hδ : 0 < δ) {θ : NNReal} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hwin : (θ : ENNReal) ≤ (δ : ENNReal) ^ (ν + 1 - ε / 3))
    {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3)
    (R : Tube θ Space3) (hsub : ∀ i ∈ s, (T i).carrier ⊆ R.carrier)
    (hdense : IsDense s T ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩)
    (hckt : katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-ν)) :
    (smallScaleHairbrushConstant : ENNReal) * (δ : ENNReal) ^ (ε / 2) *
        (δ : ENNReal) ^ ((3 : ℝ) / 2) * (θ : ENNReal) ^ ((1 : ℝ) / 2) *
        ((s.card : ENNReal) ^ ((1 : ℝ) / 2)) ≤
      volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
  classical
  rcases Finset.eq_empty_or_nonempty s with rfl | hs
  · simp
  obtain ⟨hV0, hVtop⟩ := tubeVolume_pos_and_ne_top hδ
  set V : ENNReal := tubeVolume δ with hVdef
  set N : ENNReal := (s.card : ENNReal) with hNdef
  set U : ENNReal := volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) with hUdef
  set c : ENNReal := ((Tube.le_volume.c 3 : NNReal) : ENNReal) with hcdef
  have hc0 : c ≠ 0 := by
    simp only [hcdef, ne_eq, ENNReal.coe_eq_zero]
    exact (Tube.le_volume.c_pos 3).ne'
  have hctop : c ≠ ⊤ := ENNReal.coe_ne_top
  have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
  have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  -- the density hypothesis, in `rpow` form
  have hdens : (δ : ENNReal) ^ ν * V ≤ U := by
    have hd : (⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ : NNReal) = δ ^ ν := rfl
    have h := tubeVolume_mul_le_volume_iUnionShade s T hs hdense
    rw [hd, ENNReal.coe_rpow_of_ne_zero hδ.ne'] at h
    exact h
  -- the volume of the `θ`-tube
  have hsq2 : ∀ x : NNReal, (x : ENNReal) ^ (2 : ℕ) = (x : ENNReal) ^ (2 : ℝ) := by
    intro x
    rw [← ENNReal.rpow_natCast (x : ENNReal) 2]
    norm_num
  have hB16 : volume R.carrier ≤ 16 * (θ : ENNReal) ^ (2 : ℝ) := by
    refine (Tube.volume_carrier_le R).trans ?_
    have hθ1E : (θ : ENNReal) ≤ 1 := by exact_mod_cast hθ1
    have hb : (1 / 2 + (θ : ENNReal)) ≤ 2 := by
      calc (1 / 2 + (θ : ENNReal)) ≤ 1 + 1 := add_le_add (by simp) hθ1E
        _ = 2 := by norm_num
    calc 8 * (θ : ENNReal) ^ (2 : ℕ) * (1 / 2 + (θ : ENNReal))
        ≤ 8 * (θ : ENNReal) ^ (2 : ℕ) * 2 := by gcongr
      _ = 16 * (θ : ENNReal) ^ (2 : ℕ) := by ring
      _ = 16 * (θ : ENNReal) ^ (2 : ℝ) := by rw [hsq2]
  -- the Katz--Tao count
  have hcount : N * V ≤ 16 * (δ : ENNReal) ^ (-ν) * (θ : ENNReal) ^ (2 : ℝ) := by
    refine (card_mul_tubeVolume_le_katzTao_of_subset_tube hδ s T hθ0 R hsub).trans ?_
    calc katzTaoConvexWolffConstant s T * volume R.carrier
        ≤ (δ : ENNReal) ^ (-ν) * (16 * (θ : ENNReal) ^ (2 : ℝ)) := by gcongr
      _ = 16 * (δ : ENNReal) ^ (-ν) * (θ : ENNReal) ^ (2 : ℝ) := by ring
  -- square roots
  have hsqrt : N ^ ((1 : ℝ) / 2) * V ^ ((1 : ℝ) / 2)
      ≤ 4 * (δ : ENNReal) ^ (-ν / 2) * (θ : ENNReal) := by
    have h := ENNReal.rpow_le_rpow hcount hhalf
    rw [ENNReal.mul_rpow_of_nonneg _ _ hhalf] at h
    refine h.trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ hhalf, ENNReal.mul_rpow_of_nonneg _ _ hhalf]
    have e16 : (16 : ENNReal) ^ ((1 : ℝ) / 2) = 4 := by
      have h2 : (16 : ENNReal) = (4 : ENNReal) ^ (2 : ℕ) := by norm_num
      rw [h2, ← ENNReal.rpow_natCast (4 : ENNReal) 2, ← ENNReal.rpow_mul]
      norm_num
    have eδ : ((δ : ENNReal) ^ (-ν)) ^ ((1 : ℝ) / 2) = (δ : ENNReal) ^ (-ν / 2) := by
      rw [← ENNReal.rpow_mul]; congr 1; ring
    have eθ : ((θ : ENNReal) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = (θ : ENNReal) := by
      rw [← ENNReal.rpow_mul]; norm_num
    rw [e16, eδ, eθ]
  -- cancel one factor of `V^{1/2}`
  set A : ENNReal := V ^ ((1 : ℝ) / 2) with hAdef
  have hA0 : A ≠ 0 := (ENNReal.rpow_pos hV0 hVtop).ne'
  have hAtop : A ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hhalf hVtop
  set κ : ENNReal := (smallScaleHairbrushConstant : ENNReal) with hκdef
  have hκ4 : κ * 4 = c ^ ((3 : ℝ) / 2) := by
    rw [hκdef, hcdef, smallScaleHairbrushConstant]
    rw [show ((4 : ENNReal)) = ((4 : NNReal) : ENNReal) by simp, ← ENNReal.coe_mul,
      ← ENNReal.coe_rpow_of_ne_zero (Tube.le_volume.c_pos 3).ne']
    congr 1
    field_simp
  refine (ENNReal.mul_le_mul_iff_right hA0 hAtop).mp ?_
  rw [mul_comm A, mul_comm A U]
  -- step 1: use the count to remove `N`
  have hstep1 : κ * (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
      (θ : ENNReal) ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2) * A
      ≤ (κ * 4) * (δ : ENNReal) ^ (ε / 2 - ν / 2 + (3 : ℝ) / 2) *
        (θ : ENNReal) ^ ((3 : ℝ) / 2) := by
    have hmul : κ * (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
        (θ : ENNReal) ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2) * A
        = (κ * (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
            (θ : ENNReal) ^ ((1 : ℝ) / 2)) * (N ^ ((1 : ℝ) / 2) * A) := by ring
    rw [hmul]
    refine le_trans (mul_le_mul_right hsqrt _) (le_of_eq ?_)
    have eδ : (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
        (δ : ENNReal) ^ (-ν / 2) = (δ : ENNReal) ^ (ε / 2 - ν / 2 + (3 : ℝ) / 2) := by
      rw [← ENNReal.rpow_add _ _ hδ0E hδtopE, ← ENNReal.rpow_add _ _ hδ0E hδtopE]
      congr 1
      ring
    have eθ : (θ : ENNReal) ^ ((1 : ℝ) / 2) * (θ : ENNReal) = (θ : ENNReal) ^ ((3 : ℝ) / 2) := by
      rw [show ((3 : ℝ) / 2) = 1 / 2 + 1 by norm_num,
        ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hθ0.ne') ENNReal.coe_ne_top,
        ENNReal.rpow_one]
    calc κ * (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
          (θ : ENNReal) ^ ((1 : ℝ) / 2) * (4 * (δ : ENNReal) ^ (-ν / 2) * (θ : ENNReal))
        = (κ * 4) * ((δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
            (δ : ENNReal) ^ (-ν / 2)) *
            ((θ : ENNReal) ^ ((1 : ℝ) / 2) * (θ : ENNReal)) := by ring
      _ = (κ * 4) * (δ : ENNReal) ^ (ε / 2 - ν / 2 + (3 : ℝ) / 2) *
            (θ : ENNReal) ^ ((3 : ℝ) / 2) := by rw [eδ, eθ]
  refine hstep1.trans ?_
  -- step 2: use the window on `θ`
  have hθwin : (θ : ENNReal) ^ ((3 : ℝ) / 2) ≤
      (δ : ENNReal) ^ ((3 : ℝ) / 2 * ν + (3 : ℝ) / 2 - ε / 2) := by
    refine le_trans (ENNReal.rpow_le_rpow hwin (by norm_num : (0:ℝ) ≤ 3 / 2)) (le_of_eq ?_)
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  -- step 3: assemble
  have hVlow : c * (δ : ENNReal) ^ (2 : ℝ) ≤ V := tubeVolume_lower
  have hVpow : c ^ ((3 : ℝ) / 2) * ((δ : ENNReal) ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) ≤ V * A := by
    have h := ENNReal.rpow_le_rpow hVlow (by norm_num : (0:ℝ) ≤ 3 / 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 3 / 2)] at h
    refine h.trans (le_of_eq ?_)
    rw [hAdef, show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num,
      ENNReal.rpow_add _ _ hV0.ne' hVtop, ENNReal.rpow_one]
  have hpowsum : (δ : ENNReal) ^ (ε / 2 - ν / 2 + (3 : ℝ) / 2) *
      (δ : ENNReal) ^ ((3 : ℝ) / 2 * ν + (3 : ℝ) / 2 - ε / 2)
      = (δ : ENNReal) ^ ν * ((δ : ENNReal) ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) := by
    rw [← ENNReal.rpow_add _ _ hδ0E hδtopE, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add _ _ hδ0E hδtopE]
    congr 1
    ring
  calc (κ * 4) * (δ : ENNReal) ^ (ε / 2 - ν / 2 + (3 : ℝ) / 2) * (θ : ENNReal) ^ ((3 : ℝ) / 2)
      ≤ (κ * 4) * (δ : ENNReal) ^ (ε / 2 - ν / 2 + (3 : ℝ) / 2) *
        (δ : ENNReal) ^ ((3 : ℝ) / 2 * ν + (3 : ℝ) / 2 - ε / 2) := by gcongr
    _ = c ^ ((3 : ℝ) / 2) * ((δ : ENNReal) ^ ν * ((δ : ENNReal) ^ (2 : ℝ)) ^ ((3 : ℝ) / 2)) := by
        rw [hκ4, mul_assoc, hpowsum]
    _ = (δ : ENNReal) ^ ν * (c ^ ((3 : ℝ) / 2) * ((δ : ENNReal) ^ (2 : ℝ)) ^ ((3 : ℝ) / 2)) := by
        ring
    _ ≤ (δ : ENNReal) ^ ν * (V * A) := by gcongr
    _ = ((δ : ENNReal) ^ ν * V) * A := by ring
    _ ≤ U * A := by gcongr

/-- **Leaf 2 holds when `θ ≤ δ`.**

At `θ ≤ δ` the class is confined to a single `δ`-tube, so the Katz--Tao count
`#𝕋 ≤ δ^{-ν}|R|/|T|` is strong enough that the *trivial* volume bound
`|∪ Y| ≥ δ^ν|T|` (one tube of a `δ^ν`-dense family) already exceeds the
conclusion of `WolffHairbrushBroad`, with `ν = ε/3` and the explicit constant
`smallScaleHairbrushConstant`.  Note `ε/3 ≤ ε/2`, as
`nu_le_half_of_wolffHairbrushBroadAtKT` requires of any proof of the leaf.

Neither the essential distinctness of the family nor its broadness is used.
The theorem is recorded to locate the content of Leaf 2: it all sits at
`θ ≫ δ`, where the count `δ^{-ν}(θ/δ)²` is too weak for the trivial bound and
Wolff's hairbrush argument `\cite{Wol95}` is needed. -/
theorem wolffHairbrushBroad_of_theta_le_delta {ε : ℝ}
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {θ : NNReal} (hθ0 : 0 < θ) (hθδ : θ ≤ δ)
    {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3)
    (R : Tube θ Space3) (hsub : ∀ i ∈ s, (T i).carrier ⊆ R.carrier)
    (hdense : IsDense s T ⟨(δ : ℝ) ^ (ε / 3), Real.rpow_nonneg δ.coe_nonneg (ε / 3)⟩)
    (hckt : katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-(ε / 3))) :
    (smallScaleHairbrushConstant : ENNReal) * (δ : ENNReal) ^ (ε / 2) *
        (δ : ENNReal) ^ ((3 : ℝ) / 2) * (θ : ENNReal) ^ ((1 : ℝ) / 2) *
        ((s.card : ENNReal) ^ ((1 : ℝ) / 2)) ≤
      volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
  refine wolffHairbrushBroad_of_theta_le hδ hθ0 (hθδ.trans hδ1) ?_ s T R hsub hdense hckt
  rw [show ε / 3 + 1 - ε / 3 = (1 : ℝ) by ring, ENNReal.rpow_one]
  exact_mod_cast hθδ

/-! ### The missing conjunct of the source's reduction: the `θ`-cap

The split `BroadScaleRefinement` + `RefinedBalancedBroadCover` above transcribes
only the *second* half of the source's display at `250224e_K3.tex:5741`.  The
sentence there reads, in full:

> There exists a number `θ ∈ [δ,1]` so that for each `x ∈ ⋃_T Y(T)`, **there is
> a vector `v = v(x)` so that `∠(v, dir T) ≤ θ` for each `T ∈ 𝕋` with
> `x ∈ Y(T)`**, and for each unit vector `w` and each `r ∈ [δ,θ]`, we have
> `#{T ∈ 𝕋_Y(x) : ∠(w, dir T) ≤ r} ≤ (r/θ)^η #𝕋_Y(x)`.

`IsBroadAtScale` is the second clause.  The first clause — every tube whose
shading contains `x` has direction in a single `θ`-cap — was dropped, and
dropping it is what makes `RefinedBalancedBroadCover` useless as a leaf:

* `RefinedBalancedBroadCover` takes `θ` as a universal input, so it must hold at
  `θ = δ`, where broadness is vacuous (`isBroadAtScale_of_le_delta`) and a class
  is confined to a single `δ`-tube, hence has boundedly many members
  (`Kakeya.card_le_of_EssDistinct_in_tube_six` at `ρ = δ`).
* Its density conjunct forces `∑_{i ∈ part j} |Y j i| ≥ δ^ν ∑_{i ∈ part j}|T_i|`,
  so `|⋃_{i ∈ part j} Y j i| ≥ δ^ν |T|` (a maximum dominates an average), and its
  counting conjunct forces `#P ≳ δ^{ε/16}(#𝕋)` classes.
* The essential-disjointness conjunct then reads
  `δ^{ε/16}(#𝕋) δ^ν |T| ≲ |⋃_{i ∈ 𝕋} Y(T_i)|`, i.e. a bound of the form
  "multiplicity `≲ δ^{-ν-ε/16-η}`" for an arbitrary `δ^η`-dense, Katz--Tao
  bounded family of essentially distinct `δ`-tubes.  That is a Kakeya-strength
  statement: it is *implied* by, not a step towards, the estimate this appendix
  is proving.

With the cap restored the arithmetic closes with room to spare.  Cap
concentration confines the tubes whose shading contains `x` to directions in a
single `θ`-cap, hence (as `δ ≤ θ`) to `δ`-tubes lying in one `≍ θ`-tube, whose
number the Katz--Tao hypothesis bounds by `≍ δ^{-η}(θ/δ)²`; the multiplicity is
therefore `≲ δ^{-η}(θ/δ)²`, the union is `≳ δ^{2η}(δ/θ)²(#𝕋)|T|`, the classes
now have up to `≍ δ^{-η}(θ/δ)²` members each so `#P ≳ δ^{ε/16+η}(δ/θ)²(#𝕋)`,
and the disjointness conjunct asks `δ^{ε/16 + ν - η} ≲ 1`, which holds for
`δ` small because `η ≤ ν`.

The capped leaves below are therefore the ones the source actually offers.
`broadScaleRefinement_of_capped` and `cappedBalancedBroadCover_of_refined`
record that the change moves work from Leaf 1b to Leaf 1a and nowhere else:
the capped Leaf 1a is *stronger* than `BroadScaleRefinement` and the capped
Leaf 1b is *weaker* than `RefinedBalancedBroadCover`. -/

/-- **The source's directional concentration condition at scale `θ`.**

Source: `blueprint/src/WZ2/250224e_K3.tex:5741`, the clause "for each
`x ∈ ⋃_T Y(T)` there is a vector `v = v(x)` so that `∠(v, dir(T)) ≤ θ` for each
`T ∈ 𝕋` with `x ∈ Y(T)`".

As in `IsBroadAtScale`, the angle is measured by chordal distance between unit
vectors, made insensitive to the sign ambiguity `dir T ↦ -dir T`, and the
quantifier over `x` ranges over all of `Space3`: off the shadings the inner
condition is vacuous, so nothing is demanded there. -/
def IsCapConcentrated {δ : NNReal} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) (θ : NNReal) : Prop :=
  ∀ x : Space3, ∃ v : Space3, ‖v‖ = 1 ∧
    ∀ i ∈ s, x ∈ (T i).shade →
      min ‖v - (T i).toTube.direction‖ ‖v + (T i).toTube.direction‖ ≤ (θ : ℝ)

/-- A family in which no point lies in two shadings is cap-concentrated at every
scale: take `v = dir T` for the unique tube through the point. -/
theorem isCapConcentrated_of_subsingleton {δ : NNReal} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) (θ : NNReal)
    (h : ∀ x : Space3, ∀ i ∈ s, ∀ j ∈ s, x ∈ (T i).shade → x ∈ (T j).shade → i = j) :
    IsCapConcentrated s T θ := by
  classical
  intro x
  by_cases hx : ∃ i ∈ s, x ∈ (T i).shade
  · obtain ⟨i, hi, hxi⟩ := hx
    refine ⟨(T i).toTube.direction, (T i).toTube.norm_direction, ?_⟩
    intro j hj hxj
    have : i = j := h x i hi j hj hxi hxj
    subst this
    refine le_trans (min_le_left _ _) ?_
    simp
  · refine ⟨EuclideanSpace.single 0 (1 : ℝ), by rw [PiLp.norm_single, norm_one], ?_⟩
    intro i hi hxi
    exact absurd ⟨i, hi, hxi⟩ hx

/-- Cap concentration is monotone in the scale. -/
theorem IsCapConcentrated.mono_scale {δ : NNReal} {ι : Type u} {s : Finset ι}
    {T : ι → ShadedTube δ Space3} {θ θ' : NNReal} (h : IsCapConcentrated s T θ)
    (hθ : θ ≤ θ') : IsCapConcentrated s T θ' := by
  intro x
  obtain ⟨v, hv, hcap⟩ := h x
  exact ⟨v, hv, fun i hi hxi => (hcap i hi hxi).trans (by exact_mod_cast hθ)⟩

/-- Cap concentration passes to subfamilies. -/
theorem IsCapConcentrated.subset {δ : NNReal} {ι : Type u} {s s' : Finset ι}
    {T : ι → ShadedTube δ Space3} {θ : NNReal} (h : IsCapConcentrated s T θ)
    (hss : s' ⊆ s) : IsCapConcentrated s' T θ := by
  intro x
  obtain ⟨v, hv, hcap⟩ := h x
  exact ⟨v, hv, fun i hi hxi => hcap i (hss hi) hxi⟩

/-- Cap concentration passes to shading refinements: a refinement moves no
direction and only shrinks the set of points at which the condition is tested. -/
theorem IsShadingRefinement.isCapConcentrated {δ : NNReal} {ι : Type u} {s : Finset ι}
    {T' T : ι → ShadedTube δ Space3} (h : IsShadingRefinement s T' T) {θ : NNReal}
    (hcap : IsCapConcentrated s T θ) : IsCapConcentrated s T' θ := by
  intro x
  obtain ⟨v, hv, hc⟩ := hcap x
  refine ⟨v, hv, fun i hi hxi => ?_⟩
  rw [(h i hi).1]
  exact hc i hi ((h i hi).2 hxi)

/-! ### Cap concentration bounds the multiplicity

The three geometric lemmas below turn `IsCapConcentrated` into the counting
statement that the covering leaf needs, and are the compiler-checked form of
the arithmetic recorded above `IsCapConcentrated`. -/

/-- `x + u • v` for `u ∈ [-1,1]` lies on the segment from `x - v` to `x + v`. -/
theorem mem_segment_add_smul {x v : Space3} {u : ℝ} (hu : |u| ≤ 1) :
    x + u • v ∈ segment ℝ (x - v) (x + v) := by
  rw [segment_eq_image]
  refine ⟨(u + 1) / 2, ⟨by cases abs_le.mp hu; linarith, by cases abs_le.mp hu; linarith⟩, ?_⟩
  have : (1 - (u + 1) / 2) • (x - v) + ((u + 1) / 2) • (x + v) = x + u • v := by
    module
  exact this

/-- The segment from `x - v` to `x + v` is covered by its two unit halves. -/
theorem segment_subset_union_halves (x v : Space3) :
    segment ℝ (x - v) (x + v) ⊆ segment ℝ (x - v) x ∪ segment ℝ x (x + v) := by
  intro y hy
  rw [segment_eq_image] at hy
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hy
  rcases le_total t (1/2) with h | h
  · left
    rw [segment_eq_image]
    refine ⟨2 * t, ⟨by linarith, by linarith⟩, ?_⟩
    module
  · right
    rw [segment_eq_image]
    refine ⟨2 * t - 1, ⟨by linarith, by linarith⟩, ?_⟩
    module

/-- The `ρ`-neighbourhood of the length-`2` segment centred at `x` in direction
`v` has volume at most `16 ρ² (1/2 + ρ)`: it is covered by two `ρ`-tubes. -/
theorem volume_cthickening_double_segment {x v : Space3} (hv : ‖v‖ = 1) {ρ : NNReal}
    :
    volume (cthickening (ρ : ℝ) (segment ℝ (x - v) (x + v)))
      ≤ 16 * (ρ : ENNReal) ^ 2 * (1 / 2 + (ρ : ENNReal)) := by
  have hd1 : dist (x - v) x = 1 := by
    rw [dist_eq_norm]; simpa using hv
  have hd2 : dist x (x + v) = 1 := by
    rw [dist_eq_norm]; simpa using hv
  set R₁ : Tube ρ Space3 := Tube.mk' ρ hd1 with hR₁
  set R₂ : Tube ρ Space3 := Tube.mk' ρ hd2 with hR₂
  have hc₁ : R₁.carrier = cthickening (ρ : ℝ) (segment ℝ (x - v) x) := by
    rw [R₁.carrier_eq_cthickening]; rfl
  have hc₂ : R₂.carrier = cthickening (ρ : ℝ) (segment ℝ x (x + v)) := by
    rw [R₂.carrier_eq_cthickening]; rfl
  have hsub : cthickening (ρ : ℝ) (segment ℝ (x - v) (x + v)) ⊆ R₁.carrier ∪ R₂.carrier := by
    rw [hc₁, hc₂, ← cthickening_union]
    exact cthickening_subset_of_subset _ (segment_subset_union_halves x v)
  have hbound : ∀ R : Tube ρ Space3,
      volume R.carrier ≤ 8 * (ρ : ENNReal) ^ 2 * (1 / 2 + (ρ : ENNReal)) :=
    fun R => Tube.volume_carrier_le R
  calc volume (cthickening (ρ : ℝ) (segment ℝ (x - v) (x + v)))
      ≤ volume (R₁.carrier ∪ R₂.carrier) := measure_mono hsub
    _ ≤ volume R₁.carrier + volume R₂.carrier := measure_union_le _ _
    _ ≤ 8 * (ρ : ENNReal) ^ 2 * (1 / 2 + (ρ : ENNReal))
          + 8 * (ρ : ENNReal) ^ 2 * (1 / 2 + (ρ : ENNReal)) := add_le_add (hbound _) (hbound _)
    _ = 16 * (ρ : ENNReal) ^ 2 * (1 / 2 + (ρ : ENNReal)) := by ring


/-- **A `δ`-tube through `x` whose direction is within `θ` of `v` lies in the
`(θ + 2δ)`-neighbourhood of the unit-speed segment through `x` in direction
`v`.** -/
theorem carrier_subset_cthickening_of_cap {δ θ : NNReal} (Tb : Tube δ Space3)
    {x v : Space3} (hx : x ∈ Tb.carrier)
    (hcap : min ‖v - Tb.direction‖ ‖v + Tb.direction‖ ≤ (θ : ℝ)) :
    Tb.carrier ⊆ cthickening ((θ : ℝ) + 2 * (δ : ℝ)) (segment ℝ (x - v) (x + v)) := by
  obtain ⟨σ, hσ, hσle⟩ :
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ‖v - σ • Tb.direction‖ ≤ (θ : ℝ) := by
    rcases min_le_iff.mp hcap with h | h
    · exact ⟨1, Or.inl rfl, by simpa using h⟩
    · exact ⟨-1, Or.inr rfl, by rw [neg_one_smul, sub_neg_eq_add]; exact h⟩
  have hσsq : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have habsσ : |σ| = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  -- decompose `x`
  rw [Tb.carrier_eq] at hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨zx, hzx, hxzx⟩ := hx
  rw [segment_eq_image] at hzx
  obtain ⟨tx, ⟨htx0, htx1⟩, rfl⟩ := hzx
  intro p hp
  rw [Tb.carrier_eq] at hp
  simp only [Set.mem_iUnion, exists_prop] at hp
  obtain ⟨zp, hzp, hpzp⟩ := hp
  rw [segment_eq_image] at hzp
  obtain ⟨tp, ⟨htp0, htp1⟩, rfl⟩ := hzp
  set u : ℝ := σ * (tp - tx) with hu
  have hu1 : |u| ≤ 1 := by
    rw [hu, abs_mul, habsσ, one_mul, abs_le]
    constructor <;> linarith
  refine Metric.mem_cthickening_of_dist_le p (x + u • v) _ _
    (mem_segment_add_smul hu1) ?_
  have hkey : ((1 - tp) • Tb.x + tp • Tb.y : Space3) - ((1 - tx) • Tb.x + tx • Tb.y)
      - u • v = (tp - tx) • (Tb.direction - σ • v) := by
    have hd : Tb.direction = Tb.y - Tb.x := rfl
    rw [hd, hu]
    module
  have hnorm : ‖Tb.direction - σ • v‖ ≤ (θ : ℝ) := by
    have hss : (-σ) * σ = -1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
    have : Tb.direction - σ • v = (-σ) • (v - σ • Tb.direction) := by
      rw [smul_sub, smul_smul, hss]
      module
    rw [this, norm_smul, norm_neg, Real.norm_eq_abs, habsσ, one_mul]
    exact hσle
  have hcoef : |tp - tx| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  rw [dist_eq_norm, mem_closedBall, dist_eq_norm] at *
  calc ‖p - (x + u • v)‖
      = ‖(p - ((1 - tp) • Tb.x + tp • Tb.y))
          + ((((1 - tp) • Tb.x + tp • Tb.y : Space3) - ((1 - tx) • Tb.x + tx • Tb.y))
            - u • v)
          + (((1 - tx) • Tb.x + tx • Tb.y : Space3) - x)‖ := by
        congr 1; abel
    _ ≤ ‖p - ((1 - tp) • Tb.x + tp • Tb.y)‖
          + ‖(((1 - tp) • Tb.x + tp • Tb.y : Space3) - ((1 - tx) • Tb.x + tx • Tb.y))
            - u • v‖
          + ‖((1 - tx) • Tb.x + tx • Tb.y : Space3) - x‖ := norm_add₃_le
    _ ≤ (δ : ℝ) + (θ : ℝ) + (δ : ℝ) := by
        refine add_le_add (add_le_add hpzp ?_) ?_
        · rw [hkey, norm_smul, Real.norm_eq_abs]
          calc |tp - tx| * ‖Tb.direction - σ • v‖ ≤ 1 * (θ : ℝ) := by
                refine mul_le_mul hcoef hnorm (norm_nonneg _) (by norm_num)
            _ = (θ : ℝ) := one_mul _
        · rw [← norm_neg]
          simpa using hxzx
    _ = (θ : ℝ) + 2 * (δ : ℝ) := by ring

/-- **The Katz--Tao constant tested against an arbitrary convex set.**

`#{i ∈ s' } · |T| ≤ CKT(𝕋) · |W|` whenever every tube of the subfamily `s' ⊆ s`
is contained in the convex set `W`.  This is
`card_mul_tubeVolume_le_katzTao_of_subset_tube` with the `θ`-tube replaced by a
general convex test set and the whole family by a subfamily. -/
theorem card_mul_tubeVolume_le_katzTao_of_subset_convex
    {δ : NNReal} (hδ : 0 < δ) {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3)
    (W : ConvexTestSet) (hW0 : volume W.carrier ≠ 0) (hWtop : volume W.carrier ≠ ⊤)
    {s' : Finset ι} (hs' : s' ⊆ s) (hsub : ∀ i ∈ s', (T i).carrier ⊆ W.carrier) :
    (s'.card : ENNReal) * tubeVolume δ ≤
      katzTaoConvexWolffConstant s T * volume W.carrier := by
  classical
  obtain ⟨hV0, hVtop⟩ := tubeVolume_pos_and_ne_top hδ
  set B : ENNReal := volume W.carrier with hB
  have hfil : s' ⊆ @Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
      (Classical.decPred _) s := by
    intro i hi
    exact (@Finset.mem_filter ι (fun i => (T i).carrier ⊆ W.carrier)
      (Classical.decPred _) s i).mpr ⟨hs' hi, hsub i hi⟩
  have hcard : (s'.card : ENNReal) ≤
      ((@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s).card : ENNReal) := by
    exact_mod_cast Finset.card_le_card hfil
  have key : ∀ C ∈ {C : ENNReal | 0 < C ∧ ∀ W : ConvexTestSet,
      ((@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s).card : ENNReal) ≤
        C * volume W.carrier * (tubeVolume δ)⁻¹},
      (s'.card : ENNReal) * tubeVolume δ / B ≤ C := by
    rintro C ⟨-, hC⟩
    have hCB := hcard.trans (hC W)
    refine ENNReal.div_le_of_le_mul ?_
    calc (s'.card : ENNReal) * tubeVolume δ
        ≤ (C * B * (tubeVolume δ)⁻¹) * tubeVolume δ := mul_le_mul_right' hCB _
      _ = C * B * ((tubeVolume δ)⁻¹ * tubeVolume δ) := by ring
      _ = C * B := by rw [ENNReal.inv_mul_cancel hV0.ne' hVtop, mul_one]
  have hdiv : (s'.card : ENNReal) * tubeVolume δ / B ≤ katzTaoConvexWolffConstant s T :=
    le_sInf key
  have h := mul_le_mul_right' hdiv B
  refine le_trans (le_of_eq ?_) h
  rw [ENNReal.div_mul_cancel hW0 hWtop]

/-- **Cap concentration bounds the multiplicity, via Katz--Tao.**

This is the reason the `θ`-cap clause of `250224e_K3.tex:5741` cannot be
dropped.  If every tube whose shading contains `x` has direction within `θ` of
one vector `v = v(x)`, then all those tubes lie in the `(θ + 2δ)`-neighbourhood
of the unit-speed line through `x` in direction `v`
(`carrier_subset_cthickening_of_cap`), which is a convex set of volume
`≤ 576 θ²` for `δ ≤ θ ≤ 1` (`volume_cthickening_double_segment`).  Testing the
Katz--Tao convex Wolff constant against it gives

`#{i : x ∈ Y(T_i)} · |T| ≤ CKT(𝕋) · 576 θ²`,

i.e. multiplicity `≲ CKT(𝕋) (θ/δ)²` — with `CKT(𝕋) ≤ δ^{-η}` this is the
`δ^{-η}(θ/δ)²` used in the arithmetic recorded above `IsCapConcentrated`.
Without the cap no such bound is available at all: the tubes through `x` may
point in every direction, and bounding their number is a Kakeya-strength
problem. -/
theorem multiplicity_mul_tubeVolume_le_of_isCapConcentrated
    {δ θ : NNReal} (hδ : 0 < δ) (hδθ : δ ≤ θ) (hθ1 : θ ≤ 1) {ι : Type u} {s : Finset ι}
    {T : ι → ShadedTube δ Space3} (hcap : IsCapConcentrated s T θ) (x : Space3) :
    ((@Finset.filter ι (fun i => x ∈ (T i).shade) (Classical.decPred _) s).card : ENNReal)
        * tubeVolume δ ≤
      katzTaoConvexWolffConstant s T * (576 * (θ : ENNReal) ^ 2) := by
  classical
  obtain ⟨v, hv, hc⟩ := hcap x
  set ρ : NNReal := θ + 2 * δ with hρ
  have hρ0 : 0 < ρ := by
    have : (0 : NNReal) < θ := lt_of_lt_of_le hδ hδθ
    simp only [hρ]
    positivity
  set S : Set Space3 := cthickening (ρ : ℝ) (segment ℝ (x - v) (x + v)) with hS
  have hxS : x ∈ S := by
    have hx0 : x + (0 : ℝ) • v ∈ segment ℝ (x - v) (x + v) :=
      mem_segment_add_smul (by norm_num)
    rw [zero_smul, add_zero] at hx0
    exact self_subset_cthickening _ hx0
  set W : ConvexTestSet :=
    ⟨S, (convex_segment _ _).cthickening _⟩ with hW
  have hball : closedBall x (ρ : ℝ) ⊆ S := by
    intro y hy
    refine mem_cthickening_of_dist_le y x _ _ ?_ (by simpa using hy)
    have hx0 : x + (0 : ℝ) • v ∈ segment ℝ (x - v) (x + v) :=
      mem_segment_add_smul (by norm_num)
    rw [zero_smul, add_zero] at hx0
    exact hx0
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hW0 : volume W.carrier ≠ 0 := by
    have hpos : 0 < volume (closedBall x (ρ : ℝ)) := measure_closedBall_pos _ _ hρR
    exact ne_of_gt (lt_of_lt_of_le hpos (measure_mono hball))
  have hρ3 : (ρ : ENNReal) ≤ 3 * (θ : ENNReal) := by
    have : ρ ≤ 3 * θ := by
      simp only [hρ]
      have : 2 * δ ≤ 2 * θ := by gcongr
      calc θ + 2 * δ ≤ θ + 2 * θ := by gcongr
        _ = 3 * θ := by ring
    exact_mod_cast this
  have hθ1E : (θ : ENNReal) ≤ 1 := by exact_mod_cast hθ1
  have hvol : volume W.carrier ≤ 576 * (θ : ENNReal) ^ 2 := by
    refine (volume_cthickening_double_segment (x := x) (v := v) hv (ρ := ρ)).trans ?_
    calc 16 * (ρ : ENNReal) ^ 2 * (1 / 2 + (ρ : ENNReal))
        ≤ 16 * (3 * (θ : ENNReal)) ^ 2 * (1 / 2 + 3 * (θ : ENNReal)) := by gcongr
      _ ≤ 16 * (3 * (θ : ENNReal)) ^ 2 * (1 + 3) := by
          have h3 : 3 * (θ : ENNReal) ≤ 3 := by
            calc 3 * (θ : ENNReal) ≤ 3 * 1 := by gcongr
              _ = 3 := by norm_num
          have hh : (1 / 2 : ENNReal) ≤ 1 := by simp
          exact mul_le_mul_left' (add_le_add hh h3) _
      _ = 576 * (θ : ENNReal) ^ 2 := by ring
  have hWtop : volume W.carrier ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) hvol
  refine le_trans (card_mul_tubeVolume_le_katzTao_of_subset_convex hδ s T W hW0 hWtop
    (Finset.filter_subset _ _) ?_) ?_
  · intro i hi
    have hi' := (@Finset.mem_filter ι (fun i => x ∈ (T i).shade)
      (Classical.decPred _) s i).mp hi
    have hxc : x ∈ (T i).carrier := (T i).shade_subset hi'.2
    exact carrier_subset_cthickening_of_cap (T i).toTube hxc (hc i hi'.1 hi'.2)
  · gcongr

/-- **A pointwise multiplicity bound turns the sum of the shadings into the
volume of their union.**  `∑_i |Y(T_i)| = ∫ #{i : x ∈ Y(T_i)} ≤ M |⋃_i Y(T_i)|`. -/
theorem sum_volume_shade_le_of_multiplicity_le {δ : NNReal} {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ Space3) {M : ENNReal}
    (hM : ∀ x : Space3,
      ((@Finset.filter ι (fun i => x ∈ (T i).shade) (Classical.decPred _) s).card : ENNReal)
        ≤ M) :
    ∑ i ∈ s, volume (T i).shade ≤
      M * volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
  classical
  set U : Set Space3 := ShadedBody.iUnionShade s (fun i => (T i).toShadedBody) with hU
  have hUmeas : MeasurableSet U := by
    rw [hU]
    exact Finset.measurableSet_biUnion _ (fun i _ => (T i).measurableSet_shade)
  have hsum : ∑ i ∈ s, volume (T i).shade
      = ∫⁻ x, ∑ i ∈ s, Set.indicator (T i).shade (fun _ => (1 : ENNReal)) x := by
    rw [MeasureTheory.lintegral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [MeasureTheory.lintegral_indicator (T i).measurableSet_shade]
      simp
    · intro i _
      exact (measurable_const.indicator (T i).measurableSet_shade)
  rw [hsum]
  have hptw : ∀ x : Space3,
      ∑ i ∈ s, Set.indicator (T i).shade (fun _ => (1 : ENNReal)) x
        ≤ Set.indicator U (fun _ => M) x := by
    intro x
    have hcount : ∑ i ∈ s, Set.indicator (T i).shade (fun _ => (1 : ENNReal)) x
        = ((@Finset.filter ι (fun i => x ∈ (T i).shade)
            (Classical.decPred _) s).card : ENNReal) := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : x ∈ (T i).shade <;> simp [h]
    rw [hcount]
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx]
      exact hM x
    · rw [Set.indicator_of_notMem hx]
      have : (@Finset.filter ι (fun i => x ∈ (T i).shade) (Classical.decPred _) s) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
        have hi' := (@Finset.mem_filter ι (fun i => x ∈ (T i).shade)
          (Classical.decPred _) s i).mp hi
        exact hx (Set.mem_biUnion hi'.1 hi'.2)
      simp [this]
  calc ∫⁻ x, ∑ i ∈ s, Set.indicator (T i).shade (fun _ => (1 : ENNReal)) x
      ≤ ∫⁻ x, Set.indicator U (fun _ => M) x := lintegral_mono hptw
    _ = M * volume U := by
        rw [MeasureTheory.lintegral_indicator hUmeas]
        simp

/-- **What the cap buys: a lower bound on the shaded union.**

Combining the multiplicity bound of
`multiplicity_mul_tubeVolume_le_of_isCapConcentrated` with
`sum_volume_shade_le_of_multiplicity_le` and the density hypothesis:

`λ (∑_i |T_i|) |T| ≤ C · 576 θ² · |⋃_i Y(T_i)|`,

i.e. `|⋃ Y| ≳ λ (δ/θ)² C^{-1} ∑_i |T_i|`.  This is the quantitative content of
the `θ`-cap clause of `250224e_K3.tex:5741`, and it is exactly the input the
essential-disjointness conjunct of the covering leaf needs; nothing of the kind
is available for a family that is merely broad. -/
theorem volume_iUnionShade_ge_of_isCapConcentrated
    {δ θ : NNReal} (hδ : 0 < δ) (hδθ : δ ≤ θ) (hθ1 : θ ≤ 1) {ι : Type u} {s : Finset ι}
    {T : ι → ShadedTube δ Space3} (hcap : IsCapConcentrated s T θ)
    {C : ENNReal} (hckt : katzTaoConvexWolffConstant s T ≤ C)
    {lam : NNReal} (hdense : IsDense s T lam) :
    (lam : ENNReal) * (∑ i ∈ s, volume (T i).carrier) * tubeVolume δ ≤
      C * (576 * (θ : ENNReal) ^ 2) *
        volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
  classical
  obtain ⟨hV0, hVtop⟩ := tubeVolume_pos_and_ne_top hδ
  set V : ENNReal := tubeVolume δ with hVdef
  set K : ENNReal := C * (576 * (θ : ENNReal) ^ 2) with hK
  set M : ENNReal := K / V with hM
  have hMV : M * V = K := ENNReal.div_mul_cancel hV0.ne' hVtop
  have hmult : ∀ x : Space3,
      ((@Finset.filter ι (fun i => x ∈ (T i).shade) (Classical.decPred _) s).card : ENNReal)
        ≤ M := by
    intro x
    rw [hM, ENNReal.le_div_iff_mul_le (Or.inl hV0.ne') (Or.inl hVtop)]
    refine (multiplicity_mul_tubeVolume_le_of_isCapConcentrated hδ hδθ hθ1 hcap x).trans ?_
    rw [hK]
    gcongr
  have hsum := sum_volume_shade_le_of_multiplicity_le s T hmult
  calc (lam : ENNReal) * (∑ i ∈ s, volume (T i).carrier) * V
      ≤ (∑ i ∈ s, volume (T i).shade) * V := by gcongr; exact hdense
    _ ≤ (M * volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)) * V := by
        gcongr
    _ = (M * V) * volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by ring
    _ = K * volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by rw [hMV]

/-- **Threshold splitting.**  Splitting a finite sum of `ENNReal`s at a
threshold `β`: the terms above `β` are at most `Vmax` each, the rest below `β`. -/
theorem sum_le_card_filter_mul_add {ι : Type u} (s : Finset ι) (f : ι → ENNReal)
    (β Vmax : ENNReal) (hVmax : ∀ i ∈ s, f i ≤ Vmax) :
    ∑ i ∈ s, f i ≤
      ((s.filter (fun i => β ≤ f i)).card : ENNReal) * Vmax + β * (s.card : ENNReal) := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => β ≤ f i) f]
  refine add_le_add ?_ ?_
  · calc ∑ i ∈ s.filter (fun i => β ≤ f i), f i
        ≤ ∑ _i ∈ s.filter (fun i => β ≤ f i), Vmax :=
          Finset.sum_le_sum fun i hi => hVmax i (Finset.mem_of_mem_filter i hi)
      _ = ((s.filter (fun i => β ≤ f i)).card : ENNReal) * Vmax := by
          rw [Finset.sum_const, nsmul_eq_mul]
  · calc ∑ i ∈ s.filter (fun i => ¬ β ≤ f i), f i
        ≤ ∑ _i ∈ s.filter (fun i => ¬ β ≤ f i), β := by
          refine Finset.sum_le_sum fun i hi => ?_
          exact le_of_lt (not_le.mp (Finset.mem_filter.mp hi).2)
      _ = ((s.filter (fun i => ¬ β ≤ f i)).card : ENNReal) * β := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (s.card : ENNReal) * β := by
          have h : ((s.filter (fun i => ¬ β ≤ f i)).card : ENNReal) ≤ (s.card : ENNReal) := by
            exact_mod_cast Finset.card_filter_le s _
          exact mul_le_mul_right' h _
      _ = β * (s.card : ENNReal) := by ring

/-- **The counting core of the covering leaf, at the scale `θ` supplied by the
cap.**

Disjointify the shadings (`exists_disjointed_shading`), so that their volumes
sum exactly to `|⋃ Y|`; bound that sum above by splitting at a threshold `β`
(`sum_le_card_filter_mul_add`, using `|Y(T_i)| ≤ |T_i| ≤ 16δ²`); and bound
`|⋃ Y|` below by what the cap buys
(`volume_iUnionShade_ge_of_isCapConcentrated`).  The result is a lower bound on
the number of tubes that keep a *private* shading of volume at least `β`:

`λ (∑_i |T_i|) |T| ≤ C · 576 θ² · (#{i : |Y_i| ≥ β} · 16δ² + β #𝕋)`.

At `θ = δ`, `C = δ^{-η}`, `λ = δ^η` and `β = δ^ν |T|` with `2η < ν` this reads
`#{i : |Y_i| ≥ β} ≳ δ^{2η} #𝕋` for all small `δ`, which is the counting
conjunct of `CappedBalancedBroadCover` with the singleton classes
`part i = {i}`, `parent i = (T i).toTube`.  For `θ ≫ δ` the singleton classes
are no longer admissible — a one-tube class is not broad at scale `θ` — and
what is missing is the grouping of the tubes through a point into classes, i.e.
the `θ`-tube cover itself. -/
theorem exists_disjointed_counting_of_isCapConcentrated
    {δ θ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδθ : δ ≤ θ) (hθ1 : θ ≤ 1)
    {ι : Type u} {s : Finset ι} {T : ι → ShadedTube δ Space3}
    (hcap : IsCapConcentrated s T θ)
    {C : ENNReal} (hckt : katzTaoConvexWolffConstant s T ≤ C)
    {lam : NNReal} (hdense : IsDense s T lam) (β : ENNReal) :
    ∃ Y : ι → ShadedTube δ Space3, IsShadingRefinement s Y T ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Y i).shade (Y j).shade) ∧
      (∑ i ∈ s, volume (Y i).shade
        = volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)) ∧
      (lam : ENNReal) * (∑ i ∈ s, volume (T i).carrier) * tubeVolume δ ≤
        C * (576 * (θ : ENNReal) ^ 2) *
          (((s.filter (fun i => β ≤ volume (Y i).shade)).card : ENNReal)
              * (16 * (δ : ENNReal) ^ 2)
            + β * (s.card : ENNReal)) := by
  classical
  obtain ⟨Y, href, hdisj, -, hsum⟩ := exists_disjointed_shading s T
  refine ⟨Y, href, hdisj, hsum, ?_⟩
  have hδ1E : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hVmax : ∀ i ∈ s, volume (Y i).shade ≤ 16 * (δ : ENNReal) ^ 2 := by
    intro i hi
    refine (measure_mono (Y i).shade_subset).trans ?_
    refine (Tube.volume_carrier_le (Y i).toTube).trans ?_
    have hb : (1 / 2 + (δ : ENNReal)) ≤ 2 := by
      calc (1 / 2 + (δ : ENNReal)) ≤ 1 + 1 := add_le_add (by simp) hδ1E
        _ = 2 := by norm_num
    calc 8 * (δ : ENNReal) ^ 2 * (1 / 2 + (δ : ENNReal))
        ≤ 8 * (δ : ENNReal) ^ 2 * 2 := by gcongr
      _ = 16 * (δ : ENNReal) ^ 2 := by ring
  have hthr := sum_le_card_filter_mul_add s (fun i => volume (Y i).shade) β
    (16 * (δ : ENNReal) ^ 2) hVmax
  have hlow := volume_iUnionShade_ge_of_isCapConcentrated hδ hδθ hθ1 hcap hckt hdense
  refine hlow.trans ?_
  gcongr
  rw [← hsum]
  exact hthr

/-- **Leaf 1a, with the cap: the robust-transversality reduction.**

This is `BroadScaleRefinement` together with the clause of
`250224e_K3.tex:5741` that the uncapped form dropped: the refined family is
cap-concentrated at the produced scale `θ`.  The `δ^{-ε/16}` counting budget is
verbatim from `BroadScaleRefinement`.

**Two quality targets, not one.**  `BroadScaleRefinement` used a single `ν` for
both the output density and the output broadness, which forced the covering
leaf to *upgrade* the broadness quality it was handed (see
`CappedBalancedBroadCover`).  The two qualities move in opposite directions
(`IsBroadAtScale.mono_quality`: `δ^μ`-density gets stronger as `μ` shrinks,
`ν`-broadness as `ν` grows), so they are separated here: the leaf is asked for
density `μ` and broadness `ν` and hands out an admissible input quality
`η ≤ μ`.  `broadScaleRefinement_of_capped` is the case `μ = ν`, and records
that this implies the uncapped form. -/
def CappedBroadScaleRefinement : Prop :=
  ∀ ε > (0 : ℝ), ∀ μ > (0 : ℝ), ∀ ν > (0 : ℝ), ∃ η : ℝ, 0 < η ∧ η ≤ μ ∧
    ∀ (δ : NNReal), 0 < δ → δ ≤ 1 →
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        IsTubeShadingFamily s T →
        IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ →
        katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        frostmanSlabWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        ∃ θ : NNReal, δ ≤ θ ∧ θ ≤ 1 ∧
          ∃ (s' : Finset ι) (T' : ι → ShadedTube δ Space3), s' ⊆ s ∧
            IsShadingRefinement s' T' T ∧
            (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 16)) * (s'.card : ENNReal) ∧
            IsDense s' T' ⟨(δ : ℝ) ^ μ, Real.rpow_nonneg δ.coe_nonneg μ⟩ ∧
            IsCapConcentrated s' T' θ ∧
            IsBroadAtScale s' T' θ ν

/-- **Leaf 1b, with the cap: the balanced partitioning cover.**

This is `RefinedBalancedBroadCover` with two changes, both weakenings
(`cappedBalancedBroadCover_of_refined`):

* the cap-concentration clause of `250224e_K3.tex:5741` is added as a
  *hypothesis*;
* the input broadness is asked at the *output* quality `ν`, not at the weaker
  `η`.  `RefinedBalancedBroadCover` demanded that the covering step turn
  `η`-broadness into `ν`-broadness for `η ≤ ν`, i.e. that it *improve* the
  transversality of the family.  Nothing in the source's covering step does
  that: the source obtains the broadness once, in the standard reductions, and
  the covering step only has to preserve it.  Improving it is a second
  induction on scales, and belongs to Leaf 1a, which now carries a separate
  broadness target for exactly this reason.

It is the form in which the source
actually uses the covering step: the cover `𝕋_θ` is built from the vectors
`v(x)`, and the essential disjointness of the classes' shadings
(`broadAtScaleTheta`) is exactly the statement that the `θ`-tube through `x`
determined by `v(x)` is unique up to bounded overlap.

Without the cap the statement is not a usable leaf: see the discussion above
`IsCapConcentrated`, where the uncapped form at `θ = δ` is shown to entail a
Kakeya-strength multiplicity bound.

`cappedBalancedBroadCover_hypotheses_satisfiable` certifies the bundle is
satisfiable by a nonempty family, so the leaf cannot be discharged vacuously. -/
def CappedBalancedBroadCover : Prop :=
  ∀ ε > (0 : ℝ), ∀ ν > (0 : ℝ), ∃ η : ℝ, 0 < η ∧ η ≤ ν ∧
    ∀ (δ : NNReal), 0 < δ → ∀ (θ : NNReal), δ ≤ θ → θ ≤ 1 →
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        IsTubeShadingFamily s T →
        IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ →
        katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        IsCapConcentrated s T θ →
        IsBroadAtScale s T θ ν →
        ∃ (J : Type u) (P : Finset J) (parent : J → Tube θ Space3) (part : J → Finset ι)
          (Y : J → ι → ShadedTube δ Space3),
          (∀ j ∈ P, part j ⊆
            @Finset.filter ι (fun i => (T i).carrier ⊆ (parent j).carrier)
              (Classical.decPred _) s) ∧
          (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 16)) *
            (∑ j ∈ P, ((part j).card : ENNReal)) ∧
          (∀ j ∈ P, ∀ j' ∈ P, ((part j').card : ENNReal) ≤ 2 * ((part j).card : ENNReal)) ∧
          (∀ j ∈ P, IsShadingRefinement (part j) (Y j) T) ∧
          (∀ j ∈ P,
            IsDense (part j) (Y j) ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩) ∧
          (∀ j ∈ P, IsBroadAtScale (part j) (Y j) θ ν) ∧
          (∑ j ∈ P, volume (ShadedBody.iUnionShade (part j)
              fun i => (Y j i).toShadedBody)) ≤
            volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)

/-- **Leaf 1a + Leaf 1b = Leaf 1**, in the capped form.

Identical bookkeeping to `hairbrushCover_of_refinement_of_cover` — the two
`δ^{-ε/16}` budgets compose into `δ^{-ε/8}`, refinements compose by
`IsShadingRefinement.trans`, and the shaded union shrinks twice — with the cap
produced by Leaf 1a handed straight to Leaf 1b. -/
theorem hairbrushCover_of_capped
    (HR : CappedBroadScaleRefinement.{u}) (HB : CappedBalancedBroadCover.{u}) :
    HairbrushCover.{u} := by
  intro ε hε ν hν
  obtain ⟨η₂, hη₂, hη₂ν, hB⟩ := HB ε hε ν hν
  obtain ⟨η₁, hη₁, hη₁₂, hR⟩ := HR ε hε η₂ hη₂ ν hν
  refine ⟨η₁, hη₁, le_trans hη₁₂ hη₂ν, ?_⟩
  intro δ hδ hδ1 ι s T hfamily hdense hm hell
  have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
  have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1E : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  obtain ⟨θ, hδθ, hθ1, s', T', hss, href1, hcount, hdens', hcap', hbroad'⟩ :=
    hR δ hδ hδ1 s T hfamily hdense hm hell
  have hθ0 : 0 < θ := lt_of_lt_of_le hδ hδθ
  have hckt' : katzTaoConvexWolffConstant s' T' ≤ (δ : ENNReal) ^ (-η₂) := by
    refine href1.katzTao_le hss ?_
    exact hm.trans (ENNReal.rpow_le_rpow_of_exponent_ge hδ1E (by linarith : -η₂ ≤ -η₁))
  obtain ⟨J, P, parent, part, Y, hpart, hcount', hbal, href2, hdensj, hbroadj, hadd⟩ :=
    hB δ hδ θ hδθ hθ1 s' T' (href1.isTubeShadingFamily (hfamily.subset hss)) hdens'
      hckt' hcap' hbroad'
  have hpartsub : ∀ j ∈ P, part j ⊆ s' := by
    intro j hj
    exact (hpart j hj).trans
      (@Finset.filter_subset ι (fun i => (T' i).carrier ⊆ (parent j).carrier)
        (Classical.decPred _) s')
  refine ⟨θ, hθ0, hθ1, J, P, parent, part, Y, ?_, ?_, hbal, ?_, hdensj, hbroadj, ?_⟩
  · intro j hj i hi
    have hi' := (@Finset.mem_filter ι (fun i => (T' i).carrier ⊆ (parent j).carrier)
      (Classical.decPred _) s' i).mp (hpart j hj hi)
    refine (@Finset.mem_filter ι (fun i => (T i).carrier ⊆ (parent j).carrier)
      (Classical.decPred _) s i).mpr ⟨hss hi'.1, ?_⟩
    rw [← href1.carrier_eq hi'.1]
    exact hi'.2
  · have hpow : (δ : ENNReal) ^ (-(ε / 16)) * (δ : ENNReal) ^ (-(ε / 16))
        = (δ : ENNReal) ^ (-(ε / 8)) := by
      rw [← ENNReal.rpow_add _ _ hδ0E hδtopE]
      congr 1
      ring
    calc (s.card : ENNReal)
        ≤ (δ : ENNReal) ^ (-(ε / 16)) * (s'.card : ENNReal) := hcount
      _ ≤ (δ : ENNReal) ^ (-(ε / 16)) *
            ((δ : ENNReal) ^ (-(ε / 16)) * (∑ j ∈ P, ((part j).card : ENNReal))) := by
          gcongr
      _ = ((δ : ENNReal) ^ (-(ε / 16)) * (δ : ENNReal) ^ (-(ε / 16))) *
            (∑ j ∈ P, ((part j).card : ENNReal)) := by ring
      _ = (δ : ENNReal) ^ (-(ε / 8)) * (∑ j ∈ P, ((part j).card : ENNReal)) := by
          rw [hpow]
  · intro j hj
    exact (href2 j hj).trans (href1.mono (hpartsub j hj))
  · refine hadd.trans (le_trans href1.volume_iUnionShade_le ?_)
    exact volume_iUnionShade_mono hss T

/-- **The capped Leaf 1a is stronger than the uncapped one**: forget the cap. -/
theorem broadScaleRefinement_of_capped (H : CappedBroadScaleRefinement.{u}) :
    BroadScaleRefinement.{u} := by
  intro ε hε ν hν
  obtain ⟨η, hη, hην, h⟩ := H ε hε ν hν ν hν
  refine ⟨η, hη, hην, ?_⟩
  intro δ hδ hδ1 ι s T hfam hdens hckt hFS
  obtain ⟨θ, hδθ, hθ1, s', T', hss, href, hcount, hdens', _, hbroad⟩ :=
    h δ hδ hδ1 s T hfam hdens hckt hFS
  exact ⟨θ, hδθ, hθ1, s', T', hss, href, hcount, hdens', hbroad⟩

/-- **The capped Leaf 1b is weaker than the uncapped one**: ignore the cap
hypothesis.  Together with `broadScaleRefinement_of_capped` this certifies that
restoring the cap moved work from Leaf 1b to Leaf 1a and added none. -/
theorem cappedBalancedBroadCover_of_refined (H : RefinedBalancedBroadCover.{u}) :
    CappedBalancedBroadCover.{u} := by
  intro ε hε ν hν
  obtain ⟨η, hη, hην, h⟩ := H ε hε ν hν
  refine ⟨η, hη, hην, ?_⟩
  intro δ hδ θ hδθ hθ1 ι s T hfam hdens hckt _ hbroad
  exact h δ hδ θ hδθ hθ1 s T hfam hdens hckt (hbroad.mono_quality hην)

/-- **Non-vacuity certificate for `CappedBalancedBroadCover`.**

The hypothesis bundle of the capped Leaf 1b is satisfiable with a *nonempty*
family: at `θ = δ` the single fully shaded tube centred at the origin is
`δ^ν`-dense, Katz--Tao bounded, cap-concentrated (only one direction occurs)
and broad (`isBroadAtScale_of_le_delta`).  So the leaf cannot be discharged
from an inconsistent bundle.

A *non-degenerate* witness (`θ > δ`) cannot have exactly two tubes: broadness
at quality `ν`, applied at `r < θ`, forbids any unit vector `w` from being
within `r` of both directions, so the two directions are at chordal distance
`≥ 2θ`, while cap concentration puts them within `θ` of a common **unit**
vector `v`, which forces distance `< 2θ` (the midpoint of a chord of length
`2θ` has norm `< 1`).  This is why
`not_isCapConcentrated_crossedBallFamily` in
`Kakeya.DimensionThree.MainLemma2.WangZahl.WolffHairbrushGuardrails` refutes the
cap for the two-tube witness of `crossedBall_hypotheses_satisfiable_nondegenerate`.

The smallest design satisfying both is three directions forming an equilateral
triangle inscribed in a `θ`-cap, at `θ ∈ [3δ/2, 3δ]` and `ν = 1`: the pairwise
distances are then `≍ √3 θ ≥ (4/3)θ`, so no `w` catches two of them below
`r = 2θ/3`, where `(r/θ)^1 · 3 = 2`; the circumradius is `θ`, so no `w` catches
all three below `r = θ`; and the one-tube count `1 ≤ 3(r/θ)` holds down to
`r = δ ≥ θ/3`.  Building it is a separate steps, of the same size as
`crossedBall_hypotheses_satisfiable_nondegenerate`. -/
theorem cappedBalancedBroadCover_hypotheses_satisfiable {δ : NNReal} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) {ν : ℝ} (hν : 0 ≤ ν) :
    ∃ (s : Finset (Fin 1)) (T : Fin 1 → ShadedTube δ Space3),
      s.Nonempty ∧ IsTubeShadingFamily s T ∧
      IsDense s T ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ ∧
      katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-ν) ∧
      IsCapConcentrated s T δ ∧
      IsBroadAtScale s T δ ν := by
  obtain ⟨s, T, R, hne, hfam, -, hdens, hckt, hbroad⟩ :=
    wolffHairbrushBroad_hypotheses_satisfiable hδ hδ1 hν
  refine ⟨s, T, hne, hfam, hdens, hckt, ?_, hbroad⟩
  exact isCapConcentrated_of_subsingleton s T δ
    (fun _ i _ j _ _ _ => Subsingleton.elim i j)

/-! ### Leaf 1b at `θ = δ`

The two theorems below settle `CappedBalancedBroadCover` in the degenerate
regime `θ = δ`, exactly as `wolffHairbrushBroad_of_theta_le_delta` settles Leaf
2 there, and for the same purpose: to locate the content of the leaf.  They are
the place where the cap actually gets spent, through
`exists_disjointed_counting_of_isCapConcentrated`.

At `θ = δ` broadness is free (`isBroadAtScale_of_le_delta`) and a class may be a
single tube, so the cover can be taken to be the *singleton* cover
`part i = {i}`, `parent i = (T i).toTube`, with `Y` the disjointification of the
shadings (`exists_disjointed_shading`).  Then the essential-disjointness
conjunct holds with equality and the only thing to prove is the counting
conjunct: that at least `δ^{ε/16}` of the tubes keep a private shading of volume
`≥ δ^ν |T_i|`.  That is what the cap buys.

The window is the two hypotheses `hwin1`, `hwin2`, in the style of
`wolffHairbrushBroad_of_theta_le`: with `c = Tube.le_volume.c 3` they read

`2 · 9216 δ^ν ≤ c² δ^{2η}`  and  `18432 ≤ c² δ^{2η - ε/16}`,

both of which hold for all small `δ` as soon as `2η < min (ν, ε/16)` — that is,
as soon as the input density quality `η` is small compared with the output
density quality `ν` and with the counting budget `ε/16`, which is exactly the
freedom the leaf has in choosing `η`.  Nothing here works at `θ ≫ δ`: a
one-tube class is not broad at scale `θ`, so the singleton cover becomes
inadmissible and the `θ`-tube cover has to be built.
-/

/-- **The counting conjunct of Leaf 1b at `θ = δ`.** -/
theorem count_of_theta_eq_delta {ε ν η : ℝ}
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ι : Type u} {s : Finset ι} {T : ι → ShadedTube δ Space3}
    (hcap : IsCapConcentrated s T δ)
    (hckt : katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η))
    (hdense : IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩)
    (hwin1 : 2 * 9216 * (δ : ENNReal) ^ ν
      ≤ ((Tube.le_volume.c 3 : NNReal) : ENNReal) ^ 2 * (δ : ENNReal) ^ (2 * η))
    (hwin2 : 18432 ≤ ((Tube.le_volume.c 3 : NNReal) : ENNReal) ^ 2
      * (δ : ENNReal) ^ (2 * η - ε / 16)) :
    ∃ Y : ι → ShadedTube δ Space3, IsShadingRefinement s Y T ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Y i).shade (Y j).shade) ∧
      ∑ i ∈ s, volume (Y i).shade
        = volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) ∧
      (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 16)) *
        (((s.filter (fun i =>
            (δ : ENNReal) ^ ν * (16 * (δ : ENNReal) ^ 2) ≤ volume (Y i).shade)).card :
          ENNReal)) := by
  classical
  set c : ENNReal := ((Tube.le_volume.c 3 : NNReal) : ENNReal) with hcdef
  have hcnn : (Tube.le_volume.c 3 : NNReal) ≠ 0 := (Tube.le_volume.c_pos 3).ne'
  have hc0 : c ≠ 0 := by
    simp only [hcdef, ne_eq, ENNReal.coe_eq_zero]
    exact hcnn
  have hctop : c ≠ ⊤ := ENNReal.coe_ne_top
  have hδne : δ ≠ 0 := hδ.ne'
  have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδne
  have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsq2 : (δ : ENNReal) ^ (2 : ℕ) = (δ : ENNReal) ^ (2 : ℝ) := by
    rw [← ENNReal.rpow_natCast (δ : ENNReal) 2]; norm_num
  obtain ⟨Y, href, hdisj, hsum, hcore⟩ :=
    exists_disjointed_counting_of_isCapConcentrated hδ hδ1 le_rfl hδ1 hcap hckt hdense
      ((δ : ENNReal) ^ ν * (16 * (δ : ENNReal) ^ 2))
  refine ⟨Y, href, hdisj, hsum, ?_⟩
  set N : ENNReal := (s.card : ENNReal) with hN
  set Pc : ENNReal := ((s.filter (fun i =>
    (δ : ENNReal) ^ ν * (16 * (δ : ENNReal) ^ 2) ≤ volume (Y i).shade)).card : ENNReal) with hPc
  have hd : (⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ : NNReal) = δ ^ η := rfl
  rw [hd, ENNReal.coe_rpow_of_ne_zero hδne, hsq2] at hcore
  -- lower bound for the left-hand side
  have hcar : ∀ i ∈ s, c * (δ : ENNReal) ^ (2 : ℝ) ≤ volume (T i).carrier := by
    intro i _
    have h : c * (δ : ENNReal) ^ (3 - 1 : ℕ) ≤ volume (T i).carrier := by
      simpa [hcdef] using Tube.le_volume (T i).toTube
    rwa [show (3 - 1 : ℕ) = 2 from rfl, hsq2] at h
  have hsumcar : N * (c * (δ : ENNReal) ^ (2 : ℝ)) ≤ ∑ i ∈ s, volume (T i).carrier := by
    calc N * (c * (δ : ENNReal) ^ (2 : ℝ))
        = ∑ _i ∈ s, c * (δ : ENNReal) ^ (2 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, hN]
      _ ≤ ∑ i ∈ s, volume (T i).carrier := Finset.sum_le_sum hcar
  have hVlow : c * (δ : ENNReal) ^ (2 : ℝ) ≤ tubeVolume δ := tubeVolume_lower
  set D : ENNReal := (δ : ENNReal) ^ ((4 : ℝ) - η) with hD
  have hD0 : D ≠ 0 := by rw [hD]; positivity
  have hDtop : D ≠ ⊤ := by rw [hD]; finiteness
  have hLHS : c ^ 2 * (δ : ENNReal) ^ (2 * η) * N * D
      ≤ (δ : ENNReal) ^ η * (∑ i ∈ s, volume (T i).carrier) * tubeVolume δ := by
    have hrw : c ^ 2 * (δ : ENNReal) ^ (2 * η) * N * D
        = (δ : ENNReal) ^ η * (N * (c * (δ : ENNReal) ^ (2 : ℝ))) *
            (c * (δ : ENNReal) ^ (2 : ℝ)) := by
      rw [hD,
        show c ^ 2 * (δ : ENNReal) ^ (2 * η) * N * (δ : ENNReal) ^ ((4:ℝ) - η)
            = c ^ 2 * N * ((δ : ENNReal) ^ (2 * η) * (δ : ENNReal) ^ ((4:ℝ) - η)) by ring,
        show (δ : ENNReal) ^ η * (N * (c * (δ : ENNReal) ^ (2:ℝ))) *
            (c * (δ : ENNReal) ^ (2:ℝ))
            = c ^ 2 * N * ((δ : ENNReal) ^ η * ((δ : ENNReal) ^ (2:ℝ) *
              (δ : ENNReal) ^ (2:ℝ))) by ring,
        ← ENNReal.rpow_add _ _ hδ0E hδtopE, ← ENNReal.rpow_add _ _ hδ0E hδtopE,
        ← ENNReal.rpow_add _ _ hδ0E hδtopE]
      congr 2
      ring
    rw [hrw]
    gcongr
  -- upper bound for the right-hand side
  have hRHS : (δ : ENNReal) ^ (-η) * (576 * (δ : ENNReal) ^ (2:ℝ)) *
      (Pc * (16 * (δ : ENNReal) ^ (2:ℝ))
        + (δ : ENNReal) ^ ν * (16 * (δ : ENNReal) ^ (2:ℝ)) * N)
      = 9216 * (Pc + (δ : ENNReal) ^ ν * N) * D := by
    have hexp : (δ : ENNReal) ^ (-η) * ((δ : ENNReal) ^ (2:ℝ) * (δ : ENNReal) ^ (2:ℝ))
        = (δ : ENNReal) ^ ((4:ℝ) - η) := by
      rw [← ENNReal.rpow_add _ _ hδ0E hδtopE, ← ENNReal.rpow_add _ _ hδ0E hδtopE]
      congr 1
      ring
    rw [hD,
      show (δ : ENNReal) ^ (-η) * (576 * (δ : ENNReal) ^ (2:ℝ)) *
          (Pc * (16 * (δ : ENNReal) ^ (2:ℝ))
            + (δ : ENNReal) ^ ν * (16 * (δ : ENNReal) ^ (2:ℝ)) * N)
          = 9216 * (Pc + (δ : ENNReal) ^ ν * N) *
              ((δ : ENNReal) ^ (-η) * ((δ : ENNReal) ^ (2:ℝ) * (δ : ENNReal) ^ (2:ℝ))) by ring,
      hexp]
  rw [hRHS] at hcore
  have hstep : c ^ 2 * (δ : ENNReal) ^ (2 * η) * N ≤ 9216 * (Pc + (δ : ENNReal) ^ ν * N) := by
    have h' := hLHS.trans hcore
    rw [mul_comm (c ^ 2 * (δ : ENNReal) ^ (2 * η) * N) D,
      mul_comm (9216 * (Pc + (δ : ENNReal) ^ ν * N)) D] at h'
    exact (ENNReal.mul_le_mul_iff_right hD0 hDtop).mp h'
  set X : ENNReal := c ^ 2 * (δ : ENNReal) ^ (2 * η) * N with hX
  have hXtop : X ≠ ⊤ := by
    rw [hX, hN, hcdef]
    finiteness
  have hsmall : 2 * (9216 * ((δ : ENNReal) ^ ν * N)) ≤ X := by
    rw [hX]
    calc 2 * (9216 * ((δ : ENNReal) ^ ν * N))
        = (2 * 9216 * (δ : ENNReal) ^ ν) * N := by ring
      _ ≤ (c ^ 2 * (δ : ENNReal) ^ (2 * η)) * N := by gcongr
      _ = c ^ 2 * (δ : ENNReal) ^ (2 * η) * N := by ring
  have hbig : X ≤ 18432 * Pc := by
    have h2 : X + X ≤ 18432 * Pc + X := by
      calc X + X ≤ (9216 * (Pc + (δ : ENNReal) ^ ν * N)) + X := add_le_add hstep le_rfl
        _ = 9216 * Pc + (9216 * ((δ : ENNReal) ^ ν * N) + X) := by ring
        _ ≤ 9216 * Pc + (9216 * ((δ : ENNReal) ^ ν * N) +
              (9216 * (Pc + (δ : ENNReal) ^ ν * N))) :=
          add_le_add le_rfl (add_le_add le_rfl hstep)
        _ = 9216 * Pc + 9216 * Pc + 2 * (9216 * ((δ : ENNReal) ^ ν * N)) := by ring
        _ ≤ 9216 * Pc + 9216 * Pc + X := add_le_add le_rfl hsmall
        _ = 18432 * Pc + X := by ring
    exact (ENNReal.add_le_add_iff_right hXtop).mp h2
  have hfinal : (c ^ 2 * (δ : ENNReal) ^ (2 * η)) * N ≤
      (c ^ 2 * (δ : ENNReal) ^ (2 * η)) * ((δ : ENNReal) ^ (-(ε / 16)) * Pc) := by
    rw [← mul_assoc]
    refine hbig.trans ?_
    calc (18432 : ENNReal) * Pc
        ≤ (c ^ 2 * (δ : ENNReal) ^ (2 * η - ε / 16)) * Pc := by gcongr
      _ = c ^ 2 * (δ : ENNReal) ^ (2 * η) * (δ : ENNReal) ^ (-(ε / 16)) * Pc := by
          rw [show (2 * η - ε / 16 : ℝ) = 2 * η + -(ε / 16) by ring,
            ENNReal.rpow_add _ _ hδ0E hδtopE]
          ring
  have hcancel : (c ^ 2 * (δ : ENNReal) ^ (2 * η)) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ hc0) ?_
    positivity
  have hcanceltop : (c ^ 2 * (δ : ENNReal) ^ (2 * η)) ≠ ⊤ := by
    rw [hcdef]; finiteness
  exact (ENNReal.mul_le_mul_iff_right hcancel hcanceltop).mp hfinal

/-- **`CappedBalancedBroadCover` holds at `θ = δ`**, in the window
`hwin1`/`hwin2`, with the singleton cover `part i = {i}`,
`parent i = (T i).toTube` and `Y` the disjointified shadings.

This is the exact conclusion of `CappedBalancedBroadCover` at `θ := δ`; see the
section header for what it locates and for why it does not extend to
`θ ≫ δ`. -/
theorem cappedBalancedBroadCover_conclusion_of_theta_eq_delta {ε ν η : ℝ}
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ι : Type u} {s : Finset ι} {T : ι → ShadedTube δ Space3}
    (hcap : IsCapConcentrated s T δ)
    (hckt : katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η))
    (hdense : IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩)
    (hwin1 : 2 * 9216 * (δ : ENNReal) ^ ν
      ≤ ((Tube.le_volume.c 3 : NNReal) : ENNReal) ^ 2 * (δ : ENNReal) ^ (2 * η))
    (hwin2 : 18432 ≤ ((Tube.le_volume.c 3 : NNReal) : ENNReal) ^ 2
      * (δ : ENNReal) ^ (2 * η - ε / 16)) :
    ∃ (J : Type u) (P : Finset J) (parent : J → Tube δ Space3) (part : J → Finset ι)
      (Y : J → ι → ShadedTube δ Space3),
      (∀ j ∈ P, part j ⊆
        @Finset.filter ι (fun i => (T i).carrier ⊆ (parent j).carrier)
          (Classical.decPred _) s) ∧
      (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 16)) *
        (∑ j ∈ P, ((part j).card : ENNReal)) ∧
      (∀ j ∈ P, ∀ j' ∈ P, ((part j').card : ENNReal) ≤ 2 * ((part j).card : ENNReal)) ∧
      (∀ j ∈ P, IsShadingRefinement (part j) (Y j) T) ∧
      (∀ j ∈ P, IsDense (part j) (Y j) ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩) ∧
      (∀ j ∈ P, IsBroadAtScale (part j) (Y j) δ ν) ∧
      (∑ j ∈ P, volume (ShadedBody.iUnionShade (part j)
          fun i => (Y j i).toShadedBody)) ≤
        volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
  classical
  obtain ⟨Y, href, hdisj, hsum, hcount⟩ :=
    count_of_theta_eq_delta hδ hδ1 hcap hckt hdense hwin1 hwin2
  set P : Finset ι := s.filter (fun i =>
    (δ : ENNReal) ^ ν * (16 * (δ : ENNReal) ^ 2) ≤ volume (Y i).shade) with hP
  have hPs : P ⊆ s := Finset.filter_subset _ _
  have hδ1E : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hcarle : ∀ i, volume (Y i).carrier ≤ 16 * (δ : ENNReal) ^ 2 := by
    intro i
    refine (Tube.volume_carrier_le (Y i).toTube).trans ?_
    have hb : (1 / 2 + (δ : ENNReal)) ≤ 2 := by
      calc (1 / 2 + (δ : ENNReal)) ≤ 1 + 1 := add_le_add (by simp) hδ1E
        _ = 2 := by norm_num
    calc 8 * (δ : ENNReal) ^ 2 * (1 / 2 + (δ : ENNReal))
        ≤ 8 * (δ : ENNReal) ^ 2 * 2 := by gcongr
      _ = 16 * (δ : ENNReal) ^ 2 := by ring
  have hdν : (⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ : NNReal) = δ ^ ν := rfl
  refine ⟨ι, P, fun j => (T j).toTube, fun j => {j}, fun _ => Y,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact (@Finset.mem_filter ι _ (Classical.decPred _) s _).mpr ⟨hPs hj, subset_rfl⟩
  · have hsimp : ∑ j ∈ P, (({j} : Finset ι).card : ENNReal) = (P.card : ENNReal) := by
      simp
    rw [hsimp]
    exact hcount
  · intro j _ j' _
    simp
  · intro j hj
    exact href.mono (Finset.singleton_subset_iff.mpr (hPs hj))
  · intro j hj
    have hjP : (δ : ENNReal) ^ ν * (16 * (δ : ENNReal) ^ 2) ≤ volume (Y j).shade := by
      have h := hj
      rw [hP, Finset.mem_filter] at h
      exact h.2
    rw [IsDense, Finset.sum_singleton, Finset.sum_singleton, hdν,
      ENNReal.coe_rpow_of_ne_zero hδ.ne']
    calc (δ : ENNReal) ^ ν * volume (Y j).carrier
        ≤ (δ : ENNReal) ^ ν * (16 * (δ : ENNReal) ^ 2) := by gcongr; exact hcarle j
      _ ≤ volume (Y j).shade := hjP
  · intro j _
    exact isBroadAtScale_of_le_delta _ _ hδ le_rfl ν
  · have hsimp : ∀ j : ι, volume (ShadedBody.iUnionShade ({j} : Finset ι)
        fun i => (Y i).toShadedBody) = volume (Y j).shade := by
      intro j
      congr 1
      simp [ShadedBody.iUnionShade]
    calc ∑ j ∈ P, volume (ShadedBody.iUnionShade ({j} : Finset ι)
          fun i => (Y i).toShadedBody)
        = ∑ j ∈ P, volume (Y j).shade := Finset.sum_congr rfl (fun j _ => hsimp j)
      _ ≤ ∑ j ∈ s, volume (Y j).shade :=
          Finset.sum_le_sum_of_subset hPs
      _ = volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := hsum

/-! ### The remaining geometric obligation -/











/-- The defining property of `frostmanSlabWolffConstant` is inherited by the
infimum itself, provided the infimum is finite (equivalently, provided some
admissible constant exists) and the slab has finite volume.

The infimum is over a set of constants, so the bound has to be transported
across `sInf`; the transport is done by dividing, which is legitimate because
the budget `|W| (#s)` is finite. -/
theorem count_le_frostmanSlabWolffConstant {δ : NNReal} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) (W : SlabTestSet)
    (hWtop : volume W.carrier ≠ ⊤)
    (hFS : frostmanSlabWolffConstant s T ≠ ⊤) :
    ((@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
      (Classical.decPred _) s).card : ENNReal) ≤
      frostmanSlabWolffConstant s T * volume W.carrier * (s.card : ENNReal) := by
  set n : ENNReal := ((@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
    (Classical.decPred _) s).card : ENNReal) with hn
  set S : Set ENNReal :=
    {C : ENNReal | 0 < C ∧ ∀ W : SlabTestSet,
      ((@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s).card : ENNReal) ≤
        C * volume W.carrier * (s.card : ENNReal)} with hS
  have hFSeq : frostmanSlabWolffConstant s T = sInf S := rfl
  -- `S` is nonempty, since otherwise the infimum would be `⊤`.
  have hSne : S.Nonempty := by
    rcases Set.eq_empty_or_nonempty S with hemp | hne
    · exact absurd (by rw [hFSeq, hemp, sInf_empty]) hFS
    · exact hne
  set k : ENNReal := volume W.carrier * (s.card : ENNReal) with hk
  have hktop : k ≠ ⊤ := ENNReal.mul_ne_top hWtop (by simp)
  have hassoc : ∀ C : ENNReal, C * volume W.carrier * (s.card : ENNReal) = C * k := by
    intro C; rw [hk, mul_assoc]
  rw [hassoc]
  rcases eq_or_ne k 0 with hk0 | hk0
  · obtain ⟨C, hC⟩ := hSne
    have := hC.2 W
    rw [hassoc, hk0, mul_zero] at this
    exact this.trans bot_le
  · have hdiv : n / k ≤ frostmanSlabWolffConstant s T := by
      rw [hFSeq]
      refine le_sInf ?_
      rintro C hC
      have hCW := hC.2 W
      rw [hassoc] at hCW
      exact ENNReal.div_le_of_le_mul hCW
    calc n = n / k * k := (ENNReal.div_mul_cancel hk0 hktop).symm
      _ ≤ frostmanSlabWolffConstant s T * k := by gcongr

/-- **The slab count, proved.**

The elementary counting step at the end of the source proof of Proposition
1.10.  A `θ`-tube `R` is swallowed, on the unit ball, by a slab `W` of thickness
`θ` (`exists_slabTestSet_swallowing_tube`), whose volume is at most
`θ |B(0,2)|` (`volume_slabTestSet_le`); the Frostman slab Wolff constant then
counts the tubes of the family inside `W`. -/
theorem slabTubeCount_holds : SlabTubeCount.{u} := by
  set B : ENNReal := volume (closedBall (0 : Space3) 2) with hB
  have hBtop : B ≠ ⊤ := measure_closedBall_lt_top.ne
  refine ⟨max 1 B.toNNReal, le_max_left _ _, ?_⟩
  set C : ENNReal := ((max 1 B.toNNReal : NNReal) : ENNReal) with hC
  have hBle : B ≤ C := by
    rw [hC]
    conv_lhs => rw [← ENNReal.coe_toNNReal hBtop]
    exact_mod_cast le_max_right (1 : NNReal) B.toNNReal
  have hC1 : (1 : ENNReal) ≤ C := by
    rw [hC]; exact_mod_cast le_max_left (1 : NNReal) B.toNNReal
  intro δ hδ hδ1 ι s T hfamily θ hθ0 hθ1 R
  have hfilt_le : ((@Finset.filter ι (fun i => (T i).carrier ⊆ R.carrier)
      (Classical.decPred _) s).card : ENNReal) ≤ (s.card : ENNReal) := by
    exact_mod_cast Finset.card_le_card
      (@Finset.filter_subset ι (fun i => (T i).carrier ⊆ R.carrier) (Classical.decPred _) s)
  rcases Nat.eq_zero_or_pos s.card with hc0 | hcpos
  · refine hfilt_le.trans ?_
    simp [hc0]
  have hcard0 : (s.card : ENNReal) ≠ 0 := by
    simpa using hcpos.ne'
  have hθ0E : (θ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hθ0.ne'
  -- If the Frostman constant is infinite there is nothing to prove.
  by_cases hFS : frostmanSlabWolffConstant s T = ⊤
  · have hCθ : C * (θ : ENNReal) ≠ 0 := by
      refine mul_ne_zero ?_ hθ0E
      exact (lt_of_lt_of_le zero_lt_one hC1).ne'
    have : C * (θ : ENNReal) * frostmanSlabWolffConstant s T * (s.card : ENNReal) = ⊤ := by
      rw [hFS, ENNReal.mul_top hCθ, ENNReal.top_mul hcard0]
    rw [this]
    exact le_top
  -- Put the `θ`-tube `R` inside a slab of thickness `θ`.
  obtain ⟨W, hWt, hWsub⟩ := exists_slabTestSet_swallowing_tube R (le_refl θ)
  have hWvol : volume W.carrier ≤ (θ : ENNReal) * B := by
    have h := volume_slabTestSet_le W
    rwa [hWt] at h
  have hWtop : volume W.carrier ≠ ⊤ :=
    (lt_of_le_of_lt hWvol (ENNReal.mul_lt_top ENNReal.coe_lt_top hBtop.lt_top)).ne
  have hmono : (@Finset.filter ι (fun i => (T i).carrier ⊆ R.carrier)
      (Classical.decPred _) s) ⊆
      (@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s) := by
    intro i hi
    have hi' := (@Finset.mem_filter ι (fun i => (T i).carrier ⊆ R.carrier)
      (Classical.decPred _) s i).mp hi
    exact (@Finset.mem_filter ι (fun i => (T i).carrier ⊆ W.carrier)
      (Classical.decPred _) s i).mpr ⟨hi'.1, hWsub _ (hfamily.1 i hi'.1) hi'.2⟩
  have hstep : ((@Finset.filter ι (fun i => (T i).carrier ⊆ R.carrier)
      (Classical.decPred _) s).card : ENNReal) ≤
      frostmanSlabWolffConstant s T * volume W.carrier * (s.card : ENNReal) := by
    refine le_trans ?_ (count_le_frostmanSlabWolffConstant s T W hWtop hFS)
    exact_mod_cast Finset.card_le_card hmono
  refine hstep.trans ?_
  calc frostmanSlabWolffConstant s T * volume W.carrier * (s.card : ENNReal)
      ≤ frostmanSlabWolffConstant s T * ((θ : ENNReal) * B) * (s.card : ENNReal) := by
        gcongr
    _ ≤ frostmanSlabWolffConstant s T * ((θ : ENNReal) * C) * (s.card : ENNReal) := by
        gcongr
    _ = C * (θ : ENNReal) * frostmanSlabWolffConstant s T * (s.card : ENNReal) := by ring




end

end Kakeya.WangZahl
