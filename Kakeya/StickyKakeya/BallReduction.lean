/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.StickyKakeya.FibreCounts
public import Kakeya.StickyKakeya.Fullness
public import Kakeya.StickyKakeya.Constants

/-!
  # Moving a shaded family into the unit ball: the volume lower bound

  With the fibre comparison of `Kakeya.StickyKakeya.FibreCounts` in hand, the transports of
  the hypotheses of GWZ Theorem 7.3(A) across a translation and across a discard are assembled into
  the reduction itself: a family living in `B_R` for a `δ`-independent `R > 1` is pigeonholed into a
  subfamily lying in a single unit ball, translated into `B_1`, fed to (A) there, and the resulting
  volume lower bound is carried back by translation invariance of Lebesgue measure.

  What has to move across the translation is only the *hypotheses* of (A) and its conclusion, never
  the bundle: the bundle is built on the translated family, where it is legitimate, (A) is applied
  there, and the volume lower bound is carried back.

  The packaged statement is `Kakeya.StickyKakeya.exists_union_volume_ge_of_ball`, built on the
  unpackaged `Kakeya.StickyKakeya.union_volume_ge_of_ball_core`.
-/

@[expose] public section

open MeasureTheory
open Tube
open ShadedTube

namespace Kakeya

open MultiScaleFac

namespace StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-! ### Auxiliary transports for the reduction

The reduction moves the family by a single fixed vector and then twice passes to a subfamily, so
every hypothesis of (A) has to be carried across a translation and across a discard.  The pieces are
collected here. -/

omit [Nontrivial E] in
/-- Translating a shaded `δ`-tube translates its underlying `δ`-tube. -/
theorem shadedTube_translate_toTube {δ : NNReal} (S : ShadedTube δ E) (v : E) :
    (S.translate v).toTube = (S.toTube).translate v := by
  refine Tube.ext ?_ rfl rfl
  rfl

omit [Nontrivial E] in
/-- A translated shaded tube has the translated carrier. -/
theorem shadedTube_translate_carrier {δ : NNReal} (S : ShadedTube δ E) (v : E) :
    ((S.translate v)).carrier = (v + ·) '' S.carrier := rfl

omit [Nontrivial E] in
/-- A translated shaded tube has the translated shade. -/
theorem shadedTube_translate_shade {δ : NNReal} (S : ShadedTube δ E) (v : E) :
    ((S.translate v)).shade = (v + ·) '' S.shade := rfl

omit [Nontrivial E] in
/-- `Kakeya.maxDensity` of a family of `δ`-tubes is invariant under a common translation.  This is
the `Tube`-level reading of `Kakeya.maxDensity_translate`, which is the statement for families of
convex bodies. -/
theorem maxDensity_tube_translate {κ : Type*} {δ : NNReal} (t : Finset κ) (T : κ → Tube δ E)
    (v : E) :
    Kakeya.maxDensity t (fun p => ((T p).translate v).toConvexSpaceBody)
      = Kakeya.maxDensity t (fun p => (T p).toConvexSpaceBody) := by
  simpa [Tube.translate] using
    (Kakeya.maxDensity_translate t (fun p => (T p).toConvexSpaceBody) v)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Pigeonhole over a finite net.**  If every member of `t` carries a label in the finite nonempty
set `xs`, some single label is carried by a subfamily of proportion `1/#xs`. -/
theorem exists_pigeonhole_subfamily {κ : Type*} (t : Finset κ) (xs : Finset E)
    (hxs : xs.Nonempty) (g : κ → E) (hg : ∀ p ∈ t, g p ∈ xs) :
    ∃ x₀ ∈ xs, ∃ t₀ ⊆ t, (∀ p ∈ t₀, g p = x₀) ∧
      (t.card : ℝ) ≤ (xs.card : ℝ) * (t₀.card : ℝ) := by
  classical
  let f : E → ℝ := fun b => ((t.filter (fun p => g p = b)).card : ℝ)
  let g₀ : E → ℝ := fun _ => (t.card : ℝ) / (xs.card : ℝ)
  have hm : 0 < (xs.card : ℝ) := by exact_mod_cast (Finset.card_pos.mpr hxs)
  have hsumf : (∑ b ∈ xs, f b) = (t.card : ℝ) := by
    dsimp [f]
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise hg).symm
  have hsumg : (∑ b ∈ xs, g₀ b) = (t.card : ℝ) := by
    dsimp [g₀]
    rw [Finset.sum_const]
    rw [nsmul_eq_mul]
    field_simp [hm.ne']
  have hsumle : (∑ b ∈ xs, g₀ b) ≤ (∑ b ∈ xs, f b) := by
    rw [hsumg, hsumf]
  obtain ⟨x₀, hx₀, hle⟩ := Finset.exists_le_of_sum_le hxs hsumle
  refine ⟨x₀, hx₀, t.filter (fun p => g p = x₀), Finset.filter_subset _ t, ?hprop, ?hineq⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · rw [div_le_iff₀ hm] at hle
    simpa [f, mul_comm] using hle

omit [Nontrivial E] in
/-- **Step 1 of the reduction.**  For a `δ`-independent radius `R ≥ 1` there is a `δ`-independent
cardinality loss `M` such that every family of shaded `δ`-tubes in `B_R` has a subfamily of
proportion `1/M` that one *fixed* translation carries into `B_1`.  `M` is quantified before `δ`. -/
theorem exists_translate_subfamily_unit_ball.{uκ} (R : ℝ) (hR : 1 ≤ R) :
    ∃ M : ℕ, 0 < M ∧
      ∀ {δ : NNReal}, (δ : ℝ) ≤ 1 / 4 →
        ∀ {κ : Type uκ} (t : Finset κ) (W : κ → ShadedTube δ E),
          (∀ p ∈ t, (W p).carrier ⊆ Metric.closedBall (0 : E) R) →
          ∃ (v : E) (t₀ : Finset κ), t₀ ⊆ t ∧
            (t.card : ℝ) ≤ (M : ℝ) * (t₀.card : ℝ) ∧
            ∀ p ∈ t₀, ((W p).translate v).carrier ⊆ Metric.closedBall (0 : E) 1 := by
  classical
  obtain ⟨xs, hxs_ne, hxs_norm, hnet⟩ := exists_ball_assignment (E := E) R hR
  refine ⟨xs.card, Finset.card_pos.mpr hxs_ne, ?_⟩
  intro δ hδ κ t W hball
  let x₀ : E := hxs_ne.choose
  have hx₀ : x₀ ∈ xs := hxs_ne.choose_spec
  let g : κ → E := fun p =>
    if h : ∃ x ∈ xs, ((W p).toTube).carrier ⊆ Metric.closedBall x 1 then h.choose else x₀
  have hg : ∀ p ∈ t, g p ∈ xs := by
    intro p hp
    dsimp [g]
    by_cases h : ∃ x ∈ xs, ((W p).toTube).carrier ⊆ Metric.closedBall x 1
    · rw [dif_pos h]
      exact h.choose_spec.1
    · rw [dif_neg h]
      exact hx₀
  have hgball : ∀ p ∈ t, ((W p).toTube).carrier ⊆ Metric.closedBall (g p) 1 := by
    intro p hp
    have hcond : ∃ x ∈ xs, ((W p).toTube).carrier ⊆ Metric.closedBall x 1 := by
      refine hnet hδ ((W p).toTube) ?_
      simpa using hball p hp
    dsimp [g]
    rw [dif_pos hcond]
    exact hcond.choose_spec.2
  obtain ⟨x₁, hx₁, t₀, ht₀, hlabel, hcard⟩ :=
    exists_pigeonhole_subfamily t xs hxs_ne g hg
  let v : E := -x₁
  refine ⟨v, t₀, ht₀, hcard, ?_⟩
  intro p hp
  have hsub : (W p).carrier ⊆ Metric.closedBall (x₁ : E) 1 := by
    simpa [hlabel p hp] using hgball p (ht₀ hp)
  rw [shadedTube_translate_carrier]
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc
    ‖(-x₁ + z) - 0‖ = ‖z - x₁‖ := by
      rw [show (-x₁ + z) - 0 = z - x₁ by abel]
    _ ≤ 1 := by simpa [dist_eq_norm] using (Metric.mem_closedBall.mp (hsub hz))

/-- The total carrier volume of a nonempty finite family of `δ`-tubes is positive and finite. -/
theorem sum_volume_carrier_pos_ne_top {κ : Type*} {δ : NNReal} (hδ : 0 < δ)
    (s : Finset κ) (V : κ → ShadedTube δ E) (hne : s.Nonempty) :
    0 < ∑ i ∈ s, MeasureTheory.volume (V i).carrier ∧
      (∑ i ∈ s, MeasureTheory.volume (V i).carrier) ≠ ⊤ := by
  obtain ⟨i₀, hi₀⟩ := hne
  have hpos : (0 : ENNReal) < MeasureTheory.volume (V i₀).carrier := by
    refine lt_of_lt_of_le ?_ (V i₀).toTube.le_volume
    have := Tube.le_volume.c_pos (Module.finrank ℝ E)
    positivity
  constructor
  · exact lt_of_lt_of_le hpos (Finset.single_le_sum
      (f := fun i => MeasureTheory.volume (V i).carrier) (fun i _ => bot_le) hi₀)
  · refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun i _ => ?_))
    exact (V i).toTube.isCompact.measure_lt_top

omit [Nontrivial E] in
/-- **Step 6 of the reduction.**  The shades of the refined, translated subfamily sit inside the
translate of the shade union of the original family, and Lebesgue measure is translation
invariant. -/
theorem volume_biUnion_shade_le_of_translate {κ : Type*} {δ : NNReal} {t₁ t : Finset κ}
    (ht : t₁ ⊆ t) (W V' : κ → ShadedTube δ E) (v : E)
    (hsub : ∀ p, (V' p).shade ⊆ ((W p).translate v).shade) :
    MeasureTheory.volume (⋃ p ∈ t₁, (V' p).shade)
      ≤ MeasureTheory.volume (⋃ p ∈ t, (W p).shade) := by
  have hsubset : (⋃ p ∈ t₁, (V' p).shade) ⊆ (v + ·) '' (⋃ p ∈ t, (W p).shade) := by
    intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨p, hp₁, hpx⟩ := hx
    have hxW : x ∈ (v + ·) '' (W p).shade := by
      rw [← shadedTube_translate_shade]
      exact hsub p hpx
    obtain ⟨a, ha, rfl⟩ := hxW
    exact Set.mem_image_of_mem (v + ·)
      (Set.mem_iUnion₂.mpr ⟨p, ht hp₁, ha⟩)
  calc
    MeasureTheory.volume (⋃ p ∈ t₁, (V' p).shade)
        ≤ MeasureTheory.volume ((v + ·) '' (⋃ p ∈ t, (W p).shade)) := measure_mono hsubset
    _ = MeasureTheory.volume (⋃ p ∈ t, (W p).shade) :=
        MeasureTheory.measure_image_add _ v (⋃ p ∈ t, (W p).shade)

/-- **Step 4 of the reduction**, in the exponent bookkeeping the consumer uses.  This is
`MultiScaleFac.isFrostmanAtEveryScale_nodes_of_ambient_fibre` with the ambient Frostman constant,
the ambient `maxDensity` bound and the retained proportion all read as powers of `δ`, and with the
resulting constant already weakened to `δ^{-η₁}`.  Only the cardinality proportion `Λ` is paid. -/
theorem isFrostmanAtEveryScale_nodes_ofReal {κ : Type*} {δ : NNReal} {s t₁ : Finset κ}
    {T : κ → Tube δ E} {N : ℕ} {Cu : NNReal} {η_F η_D η₁ Λ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N) (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ)))
    (hts : t₁ ⊆ s) (htne : t₁.Nonempty) (𝒰 : UniformTubeSet t₁ T N Cu)
    (hFro : IsFrostmanAtGridScales s T N (ENNReal.ofReal ((δ : ℝ) ^ (-η_F))))
    (hD : Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η_D)))
    (hΛ : 0 ≤ Λ) (hprop : (s.card : ℝ) ≤ Λ * (t₁.card : ℝ))
    (hbudget : ((nodeClassConst (E := E) * fibreCoverConst (E := E)
            * frostmanFibreConst (Module.finrank ℝ E) * Cu ^ 3 : NNReal) : ℝ)
          * Λ * (δ : ℝ) ^ (-(2 * η_F)) * (δ : ℝ) ^ (-η_D)
        ≤ (δ : ℝ) ^ (-η₁))
    (htvr : ((tubeVolRatio (E := E) : NNReal) : ℝ) ≤ (δ : ℝ) ^ (-η₁)) :
    𝒰.IsFrostmanAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-η₁))) := by
  have hΛcoef : (Real.toNNReal Λ : ℝ) = Λ := Real.coe_toNNReal Λ hΛ
  have hu : (Real.toNNReal ((δ : ℝ) ^ (-η_F)) : ℝ) = (δ : ℝ) ^ (-η_F) :=
    Real.coe_toNNReal _ (Real.rpow_nonneg (le_of_lt hδ) _)
  have hv : (Real.toNNReal ((δ : ℝ) ^ (-η_D)) : ℝ) = (δ : ℝ) ^ (-η_D) :=
    Real.coe_toNNReal _ (Real.rpow_nonneg (le_of_lt hδ) _)
  have hδr : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast (le_of_lt hδ)
  have hτ : ((Real.toNNReal ((δ : ℝ) ^ (-η_F)) : ℝ) ^ 2) = (δ : ℝ) ^ (-(2 * η_F)) := by
    calc
      ((Real.toNNReal ((δ : ℝ) ^ (-η_F)) : ℝ) ^ 2) = ((δ : ℝ) ^ (-η_F)) ^ 2 := by rw [hu]
      _ = (δ : ℝ) ^ ((-η_F) * 2) := (Real.rpow_mul_natCast hδr (-η_F) 2).symm
      _ = (δ : ℝ) ^ (-(2 * η_F)) := by
        congr 1
        ring
  have hmain := isFrostmanAtEveryScale_nodes_of_ambient_fibre (E := E)
      (A := Real.toNNReal ((δ : ℝ) ^ (-η_F)))
      (D := Real.toNNReal ((δ : ℝ) ^ (-η_D)))
      (Λ := Real.toNNReal Λ)
      hδ hδ1 hN hδN hts htne 𝒰 hFro hD (by simpa [hΛcoef] using hprop)
  refine hmain.mono ?_
  rw [max_le_iff]
  constructor
  · rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (by
      change (↑(nodeClassConst (E := E) * fibreCoverConst (E := E)
                  * frostmanFibreConst (Module.finrank ℝ E) * Cu ^ 3 : NNReal) : ℝ)
                * (Real.toNNReal Λ : ℝ)
                * (Real.toNNReal ((δ : ℝ) ^ (-η_F)) : ℝ) ^ 2
                * (Real.toNNReal ((δ : ℝ) ^ (-η_D)) : ℝ)
            ≤ (δ : ℝ) ^ (-η₁)
      rw [hΛcoef, hτ, hv]
      exact hbudget)
  · rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal htvr

/-- Any constant is eventually dominated by a negative power of `δ`. -/
theorem exists_threshold_const_le_rpow_neg (c β : ℝ) (hβ : 0 < β) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : NNReal, 0 < δ → (δ : ℝ) ≤ δ₀ → c ≤ (δ : ℝ) ^ (-β) := by
  set C := max c 1 with hC_def
  have h1leC : 1 ≤ C := by
    dsimp [C]
    exact le_max_right c 1
  have hcleC : c ≤ C := by
    dsimp [C]
    exact le_max_left c 1
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one h1leC
  set δ₀ := C ^ (-(1 / β)) with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := by
    dsimp [δ₀]
    exact Real.rpow_pos_of_pos hC_pos _
  refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_le => ?_⟩
  have hδ_nonneg : 0 ≤ (δ : ℝ) := by exact_mod_cast hδ_pos.le
  have hδβ_le : (δ : ℝ) ^ β ≤ δ₀ ^ β := by
    dsimp [δ₀]
    exact Real.rpow_le_rpow hδ_nonneg hδ_le (le_of_lt hβ)
  have hδβ_pos : 0 < (δ : ℝ) ^ β := Real.rpow_pos_of_pos (by exact_mod_cast hδ_pos) β
  have hδ₀_eval : δ₀ ^ β = C⁻¹ := by
    dsimp [δ₀]
    rw [← Real.rpow_mul hC_pos.le]
    have hprod : -(1 / β) * β = -1 := by field_simp [hβ.ne']
    have hnegone : C ^ (-1 : ℝ) = C⁻¹ := by
      rw [Real.rpow_neg hC_pos.le]
      rw [Real.rpow_one]
    rw [hprod, hnegone]
  calc
    c ≤ C := hcleC
    _ = (C⁻¹)⁻¹ := by rw [inv_inv]
    _ = (δ₀ ^ β)⁻¹ := by rw [hδ₀_eval]
    _ ≤ (δ : ℝ) ^ (-β) := by
      rw [Real.rpow_neg hδ_nonneg]
      have hδ₀β_pos : 0 < δ₀ ^ β := Real.rpow_pos_of_pos hδ₀_pos β
      field_simp [hδβ_pos.ne', hδ₀β_pos.ne']
      exact hδβ_le

/-- **The reduction at a fixed `δ`.**  Every piece of `δ`-smallness is an explicit hypothesis here,
so the outer statement only has to assemble a threshold: `hnet` is Step 1, `hssf` is Step 2 and `hA`
is part (A).  The input family only has to lie in `Metric.closedBall 0 R`, `hnet` translating a
large subfamily into the unit ball, which is why `hA` carries no radius parameter of its own. -/
theorem union_volume_ge_of_ball_core.{uκ}
    (η₁ ε_A η_L η_F η_D γ Kc R : ℝ) (_hγ_pos : 0 < γ)
    (hγF : γ + (2 * η_F + 2 * η_D) ≤ η₁) (hγL : γ + η_L ≤ η₁)
    (M : ℕ) (hM : 0 < M)
    {δ : NNReal} (hδ_pos : 0 < δ) (hδ_le_one : (δ : ℝ) ≤ 1)
    (hN : 0 < ssfGridLen δ) (hδN : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)))
    (habs_const : ((nodeClassConst (E := E) * fibreCoverConst (E := E)
            * frostmanFibreConst (Module.finrank ℝ E)
            * ssfUniformConst (Module.finrank ℝ E) ^ 3 : NNReal) : ℝ)
          * (Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E)).toReal * (M : ℝ)
        ≤ (δ : ℝ) ^ (-(γ / 2)))
    (habs_tvr : ((tubeVolRatio (E := E) : NNReal) : ℝ) ≤ (δ : ℝ) ^ (-η₁))
    (habs_two : (2 : ℝ) ≤ (δ : ℝ) ^ (-(γ / 2)))
    {κ : Type uκ}
    (hnet : ∀ (t : Finset κ) (W : κ → ShadedTube δ E),
        (∀ p ∈ t, (W p).carrier ⊆ Metric.closedBall (0 : E) R) →
        ∃ (v : E) (t₀ : Finset κ), t₀ ⊆ t ∧
          (t.card : ℝ) ≤ (M : ℝ) * (t₀.card : ℝ) ∧
          ∀ p ∈ t₀, ((W p).translate v).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hssf : ∀ (s : Finset κ) (V : κ → ShadedTube δ E),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-Kc) →
        ∃ s' ⊆ s, ∃ V' : κ → ShadedTube δ E,
          (∀ i, (V' i).toTube = (V i).toTube) ∧
          (∀ i, (V' i).shade ⊆ (V i).shade) ∧
          (s.card : ℝ) ≤ (δ : ℝ) ^ (-(γ / 2)) * (s'.card : ℝ) ∧
          ShadedBody.fullness' s' (fun i => (V i).toShadedBody)
              ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(γ / 2)))
                * ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) ∧
          Nonempty (ShadedUniformTubeSet s' V' (ssfGridLen δ)
            (ssfUniformConst (Module.finrank ℝ E))))
    (hA : ∀ (t : Finset κ) (W : κ → ShadedTube δ E),
        (∀ p ∈ t, (W p).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (t : Set κ).Pairwise
          (fun i j => IsEssentiallyDistinct (W i).carrier (W j).carrier) →
        ∀ {C : NNReal}, C ≤ ssfUniformConst (Module.finrank ℝ E) →
        ∀ (𝒱 : ShadedUniformTubeSet t W (ssfGridLen δ) C),
        ENNReal.ofReal ((δ : ℝ) ^ η₁)
            ≤ ShadedBody.fullness' t (fun p => (W p).toShadedBody) →
        𝒱.tubeUniform.IsFrostmanAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-η₁))) →
        ENNReal.ofReal ((δ : ℝ) ^ ε_A)
          ≤ MeasureTheory.volume (⋃ p ∈ t, (W p).shade))
    (t : Finset κ) (W : κ → ShadedTube δ E) (htne : t.Nonempty)
    (hball : ∀ p ∈ t, (W p).carrier ⊆ Metric.closedBall (0 : E) R)
    (hcard : (t.card : ℝ) ≤ (δ : ℝ) ^ (-Kc))
    (hheavy : ∀ p ∈ t, ENNReal.ofReal ((δ : ℝ) ^ η_L / 2)
        * MeasureTheory.volume (W p).carrier ≤ MeasureTheory.volume (W p).shade)
    (hfro : IsFrostmanAtGridScales t (fun p => (W p).toTube) (ssfGridLen δ)
        (ENNReal.ofReal ((δ : ℝ) ^ (-η_F))))
    (hmd : Kakeya.maxDensity t (fun p => ((W p).toTube).toConvexSpaceBody)
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η_D))) :
    ENNReal.ofReal ((δ : ℝ) ^ ε_A)
      ≤ MeasureTheory.volume (⋃ p ∈ t, (W p).shade) := by
  classical
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hδR0 : (0 : ℝ) ≤ (δ : ℝ) := le_of_lt hδR
  have hδ1nn : δ ≤ 1 := by exact_mod_cast hδ_le_one
  obtain ⟨u, hut, hEDu, hcardu⟩ :=
    Tube.refineToEssDistinctLeaves hδ_pos hδ1nn t (fun p => (W p).toTube) hmd
  have hune : u.Nonempty := by
    by_contra hu
    rw [Finset.not_nonempty_iff_eq_empty] at hu
    rw [hu, Finset.card_empty, Nat.cast_zero, mul_zero] at hcardu
    have htcard_pos : (0 : ENNReal) < (t.card : ENNReal) := by
      exact_mod_cast Finset.card_pos.mpr htne
    exact (not_lt_of_ge hcardu) htcard_pos
  obtain ⟨v, t₀, ht₀u, ht₀card, ht₀ball⟩ :=
    hnet u W (fun p hp => hball p (hut hp))
  have ht₀t : t₀ ⊆ t := ht₀u.trans hut
  set Wv : κ → ShadedTube δ E := fun p => (W p).translate v with hWv
  have htube : (fun p => (Wv p).toTube) = fun p => ((W p).toTube).translate v :=
    funext (fun p => shadedTube_translate_toTube (W p) v)
  have hfro_v : IsFrostmanAtGridScales t (fun p => (Wv p).toTube) (ssfGridLen δ)
      (ENNReal.ofReal ((δ : ℝ) ^ (-η_F))) := by
    rw [htube]
    exact (isFrostmanAtGridScales_translate t (fun p => (W p).toTube) _ _ v).mpr hfro
  have hmd_v : Kakeya.maxDensity t (fun p => ((Wv p).toTube).toConvexSpaceBody)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η_D)) := by
    have hEqF : (fun p => ((Wv p).toTube).toConvexSpaceBody)
        = fun p => (((W p).toTube).translate v).toConvexSpaceBody := by
      funext p
      exact congrArg (fun T : Tube δ E => T.toConvexSpaceBody)
        (shadedTube_translate_toTube (W p) v)
    calc
      Kakeya.maxDensity t (fun p => ((Wv p).toTube).toConvexSpaceBody)
          = Kakeya.maxDensity t (fun p => (((W p).toTube).translate v).toConvexSpaceBody) := by
            rw [hEqF]
      _ = Kakeya.maxDensity t (fun p => ((W p).toTube).toConvexSpaceBody) :=
            (maxDensity_tube_translate t (fun p => (W p).toTube) v)
      _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η_D)) := hmd
  have hvolc : ∀ p, MeasureTheory.volume (Wv p).carrier = MeasureTheory.volume (W p).carrier := by
    intro p
    rw [show (Wv p).carrier = (v + ·) '' (W p).carrier by
      rw [hWv]
      exact shadedTube_translate_carrier (W p) v]
    exact MeasureTheory.measure_image_add _ v (W p).carrier
  have hvols : ∀ p, MeasureTheory.volume (Wv p).shade = MeasureTheory.volume (W p).shade := by
    intro p
    rw [show (Wv p).shade = (v + ·) '' (W p).shade by
      rw [hWv]
      exact shadedTube_translate_shade (W p) v]
    exact MeasureTheory.measure_image_add _ v (W p).shade
  have hheavy_v : ∀ p ∈ t, ENNReal.ofReal ((δ : ℝ) ^ η_L / 2)
      * MeasureTheory.volume (Wv p).carrier ≤ MeasureTheory.volume (Wv p).shade := by
    intro p hp
    rw [hvolc p, hvols p]
    exact hheavy p hp
  have hEDv : (t₀ : Set κ).Pairwise
      (fun i j => IsEssentiallyDistinct (Wv i).carrier (Wv j).carrier) := by
    intro i hi j hj hij
    have hsource := hEDu (ht₀u hi) (ht₀u hj) hij
    change IsEssentiallyDistinct ((W i).toTube.translate v).carrier
      ((W j).toTube.translate v).carrier
    exact (Kakeya.isEssentiallyDistinct_translate _ _ v).mpr hsource
  have hcard₀ : (t₀.card : ℝ) ≤ (δ : ℝ) ^ (-Kc) :=
    le_trans (by exact_mod_cast Finset.card_le_card ht₀t) hcard
  obtain ⟨t₁, ht₁t₀, V', hVto, hVsh, hcard₁, hfull₁, h𝒱⟩ := hssf t₀ Wv ht₀ball hcard₀
  obtain ⟨𝒱⟩ := h𝒱
  have ht₁t : t₁ ⊆ t := ht₁t₀.trans ht₀t
  have ht₀card_pos : 0 < (t₀.card : ℝ) := by
    have hle0 : (0 : ℝ) ≤ (t₀.card : ℝ) := by positivity
    have hpos0 : (0 : ℝ) < (M : ℝ) * (t₀.card : ℝ) :=
      lt_of_lt_of_le (by exact_mod_cast (Finset.card_pos.mpr hune)) ht₀card
    by_contra h
    have hx0 : (t₀.card : ℝ) = 0 := by
      have hle : (t₀.card : ℝ) ≤ 0 := le_of_not_gt h
      exact le_antisymm hle hle0
    have : (M : ℝ) * (t₀.card : ℝ) = 0 := by rw [hx0, mul_zero]
    rw [this] at hpos0
    exact (lt_irrefl (0 : ℝ)) hpos0
  have ht₁card_pos : 0 < (t₁.card : ℝ) := by
    have hle1 : (0 : ℝ) ≤ (t₁.card : ℝ) := by positivity
    by_contra h
    have hx1 : (t₁.card : ℝ) = 0 := by
      have hle : (t₁.card : ℝ) ≤ 0 := le_of_not_gt h
      exact le_antisymm hle hle1
    have hle0' : (t₀.card : ℝ) ≤ 0 := by
      rw [hx1, mul_zero] at hcard₁
      simpa using hcard₁
    linarith
  have ht₁ne : t₁.Nonempty := Finset.card_pos.mp (by exact_mod_cast ht₁card_pos)
  have hfam : (fun p => (V' p).toTube) = fun p => (Wv p).toTube := funext hVto
  have hED₁ : (t₁ : Set κ).Pairwise
      (fun i j => IsEssentiallyDistinct (V' i).carrier (V' j).carrier) := by
    intro i hi j hj hij
    change IsEssentiallyDistinct ((V' i).toTube).carrier ((V' j).toTube).carrier
    rw [hVto i, hVto j]
    exact hEDv (ht₁t₀ hi) (ht₁t₀ hj) hij
  let Ced : ℝ := edRefineC (E := E)
  have hCed_nonneg : 0 ≤ Ced := le_trans zero_le_one (one_le_edRefineC (E := E))
  have hD_nonneg : 0 ≤ (δ : ℝ) ^ (-η_D) := Real.rpow_nonneg hδR0 _
  have hcardu_real : (t.card : ℝ) ≤ Ced * (δ : ℝ) ^ (-η_D) * (u.card : ℝ) := by
    have hcardu' := hcardu
    rw [← ofReal_edRefineC (E := E)] at hcardu'
    have htop : ENNReal.ofReal Ced * ENNReal.ofReal ((δ : ℝ) ^ (-η_D))
          * (u.card : ENNReal) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.natCast_ne_top _)
    have hreal := ENNReal.toReal_mono htop hcardu'
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCed_nonneg,
      ENNReal.toReal_ofReal hD_nonneg, ENNReal.toReal_natCast] using hreal
  let Λ : ℝ := Ced * (δ : ℝ) ^ (-η_D) * (M : ℝ) * (δ : ℝ) ^ (-(γ / 2))
  have hΛ0 : 0 ≤ Λ := by
    dsimp [Λ]
    positivity
  have hprop : (t.card : ℝ) ≤ Λ * (t₁.card : ℝ) := by
    calc
      (t.card : ℝ) ≤ Ced * (δ : ℝ) ^ (-η_D) * (u.card : ℝ) := hcardu_real
      _ ≤ Ced * (δ : ℝ) ^ (-η_D) * ((M : ℝ) * (t₀.card : ℝ)) := by
        exact mul_le_mul_of_nonneg_left ht₀card (mul_nonneg hCed_nonneg hD_nonneg)
      _ ≤ Ced * (δ : ℝ) ^ (-η_D) *
            ((M : ℝ) * ((δ : ℝ) ^ (-(γ / 2)) * (t₁.card : ℝ))) := by
        gcongr
      _ = Λ * (t₁.card : ℝ) := by simp only [Λ]; ring
  have hbudget : ((nodeClassConst (E := E) * fibreCoverConst (E := E)
          * frostmanFibreConst (Module.finrank ℝ E)
          * ssfUniformConst (Module.finrank ℝ E) ^ 3 : NNReal) : ℝ)
        * Λ * (δ : ℝ) ^ (-(2 * η_F)) * (δ : ℝ) ^ (-η_D)
      ≤ (δ : ℝ) ^ (-η₁) := by
    set Cdim : ℝ := ((nodeClassConst (E := E) * fibreCoverConst (E := E)
          * frostmanFibreConst (Module.finrank ℝ E)
          * ssfUniformConst (Module.finrank ℝ E) ^ 3 : NNReal) : ℝ)
    have hCdim_le : Cdim * Ced * (M : ℝ) ≤ (δ : ℝ) ^ (-(γ / 2)) := by
      change Cdim * edRefineC (E := E) * (M : ℝ) ≤ (δ : ℝ) ^ (-(γ / 2))
      rw [edRefineC]
      simpa [Cdim] using habs_const
    have hX : (0 : ℝ) ≤ (δ : ℝ) ^ (-(γ / 2)) * (δ : ℝ) ^ (-η_D)
        * (δ : ℝ) ^ (-(2 * η_F)) * (δ : ℝ) ^ (-η_D) := by positivity
    have hB0 : (0 : ℝ) ≤ (δ : ℝ) ^ (-(γ / 2)) := Real.rpow_nonneg hδR0 _
    have hmerge : (δ : ℝ) ^ (-(γ / 2)) * (δ : ℝ) ^ (-(γ / 2))
        * (δ : ℝ) ^ (-η_D) * (δ : ℝ) ^ (-(2 * η_F)) * (δ : ℝ) ^ (-η_D)
        = (δ : ℝ) ^ (-(γ + (2 * η_F + 2 * η_D))) := by
      rw [← Real.rpow_add hδR]
      rw [← Real.rpow_add hδR]
      rw [← Real.rpow_add hδR]
      rw [← Real.rpow_add hδR]
      congr 1
      ring
    have hmain : Cdim * Λ * (δ : ℝ) ^ (-(2 * η_F)) * (δ : ℝ) ^ (-η_D)
        ≤ (δ : ℝ) ^ (-(γ + (2 * η_F + 2 * η_D))) := by
      calc
        Cdim * Λ * (δ : ℝ) ^ (-(2 * η_F)) * (δ : ℝ) ^ (-η_D)
            = (Cdim * Ced * (M : ℝ)) * ((δ : ℝ) ^ (-(γ / 2)) * (δ : ℝ) ^ (-η_D)
                * (δ : ℝ) ^ (-(2 * η_F)) * (δ : ℝ) ^ (-η_D)) := by
              simp only [Λ]
              ring
            _ ≤ (δ : ℝ) ^ (-(γ / 2)) * ((δ : ℝ) ^ (-(γ / 2))
                * (δ : ℝ) ^ (-η_D) * (δ : ℝ) ^ (-(2 * η_F)) * (δ : ℝ) ^ (-η_D)) := by
              exact mul_le_mul hCdim_le (le_rfl) hX hB0
            _ = (δ : ℝ) ^ (-(γ / 2)) * (δ : ℝ) ^ (-(γ / 2))
                * (δ : ℝ) ^ (-η_D) * (δ : ℝ) ^ (-(2 * η_F)) * (δ : ℝ) ^ (-η_D) := by ring
            _ = (δ : ℝ) ^ (-(γ + (2 * η_F + 2 * η_D))) := hmerge
    calc
      Cdim * Λ * (δ : ℝ) ^ (-(2 * η_F)) * (δ : ℝ) ^ (-η_D)
          ≤ (δ : ℝ) ^ (-(γ + (2 * η_F + 2 * η_D))) := hmain
      _ ≤ (δ : ℝ) ^ (-η₁) := by
        exact Real.rpow_le_rpow_of_exponent_ge hδR hδ_le_one (by linarith [hγF])
  have hnodes := isFrostmanAtEveryScale_nodes_ofReal (E := E)
      (Λ := Λ)
      hδ_pos hδ1nn hN hδN ht₁t ht₁ne 𝒱.tubeUniform
      (by rw [hfam]; exact hfro_v)
      (by
        have hEqV : (fun i => ((V' i).toTube).toConvexSpaceBody)
            = fun p => ((Wv p).toTube).toConvexSpaceBody := by
          funext p
          exact congrArg (fun T : Tube δ E => T.toConvexSpaceBody) (hVto p)
        calc
          Kakeya.maxDensity t (fun i => ((V' i).toTube).toConvexSpaceBody)
              = Kakeya.maxDensity t (fun p => ((Wv p).toTube).toConvexSpaceBody) := by
                rw [hEqV]
          _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η_D)) := hmd_v)
      hΛ0 hprop hbudget habs_tvr
  have hspos_fin : 0 < ∑ i ∈ t₁, MeasureTheory.volume (Wv i).carrier ∧
      (∑ i ∈ t₁, MeasureTheory.volume (Wv i).carrier) ≠ ⊤ :=
    sum_volume_carrier_pos_ne_top hδ_pos t₁ Wv ht₁ne
  have hfullWv : ENNReal.ofReal ((δ : ℝ) ^ η_L / 2)
      ≤ ShadedBody.fullness' t₁ (fun p => (Wv p).toShadedBody) :=
    fullness'_ge_of_per_body t₁ (fun p => (Wv p).toShadedBody) (ENNReal.ofReal ((δ : ℝ) ^ η_L / 2))
      hspos_fin.1 hspos_fin.2 (fun p hp => hheavy_v p (ht₁t hp))
  have hnonnegγ2 : (0 : ℝ) ≤ (δ : ℝ) ^ (γ / 2) := Real.rpow_nonneg hδR0 _
  have hδγ2 : (δ : ℝ) ^ (γ / 2) * (δ : ℝ) ^ (-(γ / 2)) = 1 := by
    rw [← Real.rpow_add hδR]
    have he : (γ / 2 : ℝ) + (-(γ / 2)) = 0 := by ring
    rw [he]
    exact Real.rpow_zero _
  have hmul1 : ENNReal.ofReal ((δ : ℝ) ^ (γ / 2)) * ENNReal.ofReal ((δ : ℝ) ^ (-(γ / 2))) = 1 := by
    rw [← ENNReal.ofReal_mul hnonnegγ2]
    rw [hδγ2]
    norm_num
  have hfull₁' : ENNReal.ofReal ((δ : ℝ) ^ (γ / 2))
      * ShadedBody.fullness' t₁ (fun i => (Wv i).toShadedBody)
      ≤ ShadedBody.fullness' t₁ (fun i => (V' i).toShadedBody) := by
    calc
      ENNReal.ofReal ((δ : ℝ) ^ (γ / 2)) * ShadedBody.fullness' t₁ (fun i => (Wv i).toShadedBody)
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (γ / 2))
              * (ENNReal.ofReal ((δ : ℝ) ^ (-(γ / 2)))
              * ShadedBody.fullness' t₁ (fun i => (V' i).toShadedBody)) := by
            gcongr
      _ = (ENNReal.ofReal ((δ : ℝ) ^ (γ / 2)) * ENNReal.ofReal ((δ : ℝ) ^ (-(γ / 2))))
          * ShadedBody.fullness' t₁ (fun i => (V' i).toShadedBody) := by ring
      _ = 1 * ShadedBody.fullness' t₁ (fun i => (V' i).toShadedBody) := by rw [hmul1]
      _ = ShadedBody.fullness' t₁ (fun i => (V' i).toShadedBody) := by simp
  have hγL_ge : γ / 2 + η_L - η₁ ≤ -(γ / 2) := by linarith [hγL]
  have hpow_ge : (δ : ℝ) ^ (-(γ / 2)) ≤ (δ : ℝ) ^ (γ / 2 + η_L - η₁) := by
    exact Real.rpow_le_rpow_of_exponent_ge hδR hδ_le_one hγL_ge
  have htwo_le : (2 : ℝ) ≤ (δ : ℝ) ^ (γ / 2 + η_L - η₁) :=
    le_trans habs_two hpow_ge
  have hnum' : (2 : ℝ) * (δ : ℝ) ^ η₁ ≤ (δ : ℝ) ^ (γ / 2 + η_L) := by
    calc
      (2 : ℝ) * (δ : ℝ) ^ η₁ ≤ (δ : ℝ) ^ (γ / 2 + η_L - η₁) * (δ : ℝ) ^ η₁ := by
        exact mul_le_mul_of_nonneg_right htwo_le (Real.rpow_nonneg hδR0 _)
      _ = (δ : ℝ) ^ (γ / 2 + η_L) := by
        rw [← Real.rpow_add hδR]
        ring_nf
  have hnum : (δ : ℝ) ^ η₁ ≤ (δ : ℝ) ^ (γ / 2) * ((δ : ℝ) ^ η_L / 2) := by
    have hstep : (2 : ℝ) * (δ : ℝ) ^ η₁ ≤ (δ : ℝ) ^ (γ / 2) * (δ : ℝ) ^ η_L := by
      calc
        (2 : ℝ) * (δ : ℝ) ^ η₁ ≤ (δ : ℝ) ^ (γ / 2 + η_L) := hnum'
        _ = (δ : ℝ) ^ (γ / 2) * (δ : ℝ) ^ η_L := by rw [Real.rpow_add hδR]
    have hdiv : (δ : ℝ) ^ η₁ ≤ ((δ : ℝ) ^ (γ / 2) * (δ : ℝ) ^ η_L) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      calc
        (δ : ℝ) ^ η₁ * 2 = 2 * (δ : ℝ) ^ η₁ := by ring
        _ ≤ (δ : ℝ) ^ (γ / 2) * (δ : ℝ) ^ η_L := hstep
    have hEq : ((δ : ℝ) ^ (γ / 2) * (δ : ℝ) ^ η_L) / 2 = (δ : ℝ) ^ (γ / 2)
        * ((δ : ℝ) ^ η_L / 2) := by
      ring
    rwa [← hEq]
  have hfullness : ENNReal.ofReal ((δ : ℝ) ^ η₁)
      ≤ ShadedBody.fullness' t₁ (fun p => (V' p).toShadedBody) := by
    calc
      ENNReal.ofReal ((δ : ℝ) ^ η₁)
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (γ / 2)
              * ((δ : ℝ) ^ η_L / 2)) := ENNReal.ofReal_le_ofReal hnum
      _ = ENNReal.ofReal ((δ : ℝ) ^ (γ / 2)) * ENNReal.ofReal ((δ : ℝ) ^ η_L / 2) := by
        rw [ENNReal.ofReal_mul hnonnegγ2]
      _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (γ / 2))
          * ShadedBody.fullness' t₁ (fun p => (Wv p).toShadedBody) := by
        gcongr
      _ ≤ ShadedBody.fullness' t₁ (fun p => (V' p).toShadedBody) := hfull₁'
  have hcarr₁ : ∀ p ∈ t₁, (V' p).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro p hp
    have hEq : (V' p).carrier = (Wv p).carrier := by
      rw [hVto p]
    rw [hEq]
    exact ht₀ball p (ht₁t₀ hp)
  exact (hA t₁ V' hcarr₁ hED₁ le_rfl 𝒱 hfullness hnodes).trans
    (volume_biUnion_shade_le_of_translate ht₁t W V' v hVsh)

/-! ### Applying part (A) to a family that only lies in a large ball

This is the whole reduction, packaged so that the consumer never sees the translation.  Part (A) is
taken as a hypothesis at the fixed scale `δ` — that is enough, since it is applied to a *different*
family at the *same* `δ` — and the threshold `δ₀` produced here depends only on the numeric
parameters, so a consumer can fold it into its own smallness threshold exactly as it folds `δ₀_A`.

The three exponents `η_L`, `η_F`, `η_D` are the ones the producer of the family actually delivers:
per-tube heaviness at `η_L`, leaf-anchored Frostman at `η_F`, and `Δ_max ≤ δ^{-η_D}`.  The budget is

  `η_L < η₁`  and  `2·η_F + 2·η_D < η₁`,

the Frostman exponent entering *twice* because the leaf-anchored-to-node bridge
(`MultiScaleFac.isFrostmanAtEveryScale_nodes_of_ambient_fibre`) spends it once on the fibre
comparability driving the dual count and once on the Frostman step itself.  The exponent `η_D`
enters twice: once for the paper-required essentially-distinct refinement before the spatial
pigeonhole, and once because the leaf-to-node bridge consumes the ambient `maxDensity` bound.

The remaining gap pays for four `δ`-independent constants: the cardinality of the net used by the
pigeonhole, the factor `2` in the heaviness hypothesis, the shading loss of the shaded
uniformization, and the dimensional constants of the bridge.

The radius `R` is a genuine parameter of *this* statement: the whole bridge from `Metric.closedBall
0 R` down to the unit ball lives in this layer.  Part (A), by contrast, is only ever invoked on
`B_1`, so the hypothesis `hA` below carries no radius; it also only ever needs bundles whose
uniformity constant is the closed dimensional term
`ShadedTube.ssfUniformConst (Module.finrank ℝ E)` delivered by the shaded uniformization, which is
why `hA` may demand `C ≤ ssfUniformConst (Module.finrank ℝ E)`. -/
theorem exists_union_volume_ge_of_ball.{uκ}
    (η₁ ε_A : ℝ) (hη₁ : 0 < η₁)
    (η_L η_F η_D : ℝ) (_hη_L : 0 < η_L) (hη_L_lt : η_L < η₁)
    (_hη_F : 0 < η_F) (_hη_D : 0 < η_D)
    (hbudget : 2 * η_F + 2 * η_D < η₁)
    (K₀ : ℝ) (R : ℝ) (hR : 1 ≤ R) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ δ₀ →
      ∀ {κ : Type uκ},
      (∀ (t : Finset κ) (W : κ → ShadedTube δ E),
          (∀ p ∈ t, (W p).carrier ⊆ Metric.closedBall (0 : E) 1) →
          (t : Set κ).Pairwise
            (fun i j => IsEssentiallyDistinct (W i).carrier (W j).carrier) →
          ∀ {C : NNReal}, C ≤ ssfUniformConst (Module.finrank ℝ E) →
          ∀ (𝒱 : ShadedUniformTubeSet t W (ssfGridLen δ) C),
          ENNReal.ofReal ((δ : ℝ) ^ η₁)
              ≤ ShadedBody.fullness' t (fun p => (W p).toShadedBody) →
          𝒱.tubeUniform.IsFrostmanAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-η₁))) →
          ENNReal.ofReal ((δ : ℝ) ^ ε_A)
            ≤ MeasureTheory.volume (⋃ p ∈ t, (W p).shade)) →
      ∀ (t : Finset κ) (W : κ → ShadedTube δ E), t.Nonempty →
        (∀ p ∈ t, (W p).carrier ⊆ Metric.closedBall (0 : E) R) →
        (t.card : ℝ) ≤ (δ : ℝ) ^ (-K₀) →
        (∀ p ∈ t, ENNReal.ofReal ((δ : ℝ) ^ η_L / 2)
            * MeasureTheory.volume (W p).carrier
          ≤ MeasureTheory.volume (W p).shade) →
        IsFrostmanAtGridScales t (fun p => (W p).toTube) (ssfGridLen δ)
            (ENNReal.ofReal ((δ : ℝ) ^ (-η_F))) →
        Kakeya.maxDensity t (fun p => ((W p).toTube).toConvexSpaceBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η_D)) →
        ENNReal.ofReal ((δ : ℝ) ^ ε_A)
          ≤ MeasureTheory.volume (⋃ p ∈ t, (W p).shade) := by
  classical
  set γ : ℝ := min (η₁ - (2 * η_F + 2 * η_D)) (η₁ - η_L) with hγdef
  have hγ_pos : 0 < γ := by
    rw [hγdef]
    exact lt_min (by linarith) (by linarith)
  have hγF : γ + (2 * η_F + 2 * η_D) ≤ η₁ := by
    have hmin : γ ≤ η₁ - (2 * η_F + 2 * η_D) := by
      rw [hγdef]
      exact min_le_left (η₁ - (2 * η_F + 2 * η_D)) (η₁ - η_L)
    linarith
  have hγL : γ + η_L ≤ η₁ := by
    have hmin : γ ≤ η₁ - η_L := by
      rw [hγdef]
      exact min_le_right (η₁ - (2 * η_F + 2 * η_D)) (η₁ - η_L)
    linarith
  obtain ⟨M, hM_pos, hnet⟩ := exists_translate_subfamily_unit_ball (E := E) R hR
  obtain ⟨δ₀_ssf, hssf_pos, hssf_le1, hssf⟩ :=
    exists_shadedUniformTubeSet_subfamily_ssf (E := E) ⌈K₀⌉₊ (γ / 2) (γ / 2)
      (by linarith) (by linarith)
  obtain ⟨δ₀_grid, hgrid_pos, hgrid_le1, hgrid⟩ :=
    exists_threshold_polylog_pow_ssfGridLen_le 1 le_rfl 0 1 1 one_pos
  obtain ⟨δ₀_c1, hc1_pos, hc1⟩ := exists_threshold_const_le_rpow_neg
    (((nodeClassConst (E := E) * fibreCoverConst (E := E)
        * frostmanFibreConst (Module.finrank ℝ E)
        * ssfUniformConst (Module.finrank ℝ E) ^ 3 : NNReal) : ℝ)
      * (Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E)).toReal * (M : ℝ))
    (γ / 2) (by linarith)
  obtain ⟨δ₀_c2, hc2_pos, hc2⟩ := exists_threshold_const_le_rpow_neg
    ((tubeVolRatio (E := E) : NNReal) : ℝ) η₁ hη₁
  obtain ⟨δ₀_c3, hc3_pos, hc3⟩ := exists_threshold_const_le_rpow_neg (2 : ℝ) (γ / 2) (by linarith)
  refine ⟨min (min (min δ₀_c1 δ₀_c2) (min δ₀_c3 (1 / 4)))
          (min (δ₀_ssf : ℝ) (δ₀_grid : ℝ)), ?_, ?_⟩
  · have hc12 : (0 : ℝ) < min δ₀_c1 δ₀_c2 := lt_min hc1_pos hc2_pos
    have hc34 : (0 : ℝ) < min δ₀_c3 (1 / 4) := lt_min hc3_pos (by norm_num)
    have hleft : (0 : ℝ) < min (min δ₀_c1 δ₀_c2) (min δ₀_c3 (1 / 4)) := lt_min hc12 hc34
    have hright : (0 : ℝ) < min (δ₀_ssf : ℝ) (δ₀_grid : ℝ) :=
      lt_min (by exact_mod_cast hssf_pos) (by exact_mod_cast hgrid_pos)
    exact lt_min hleft hright
  · intro δ hδpos hδle κ hA t W htne hball hcard hheavy hfro hmd
    have hδA : (δ : ℝ) ≤ min (min δ₀_c1 δ₀_c2) (min δ₀_c3 (1 / 4)) :=
      le_trans hδle
        (min_le_left (min (min δ₀_c1 δ₀_c2) (min δ₀_c3 (1 / 4))) (min (δ₀_ssf : ℝ) (δ₀_grid : ℝ)))
    have hδB : (δ : ℝ) ≤ min (δ₀_ssf : ℝ) (δ₀_grid : ℝ) :=
      le_trans hδle
        (min_le_right (min (min δ₀_c1 δ₀_c2) (min δ₀_c3 (1 / 4))) (min (δ₀_ssf : ℝ) (δ₀_grid : ℝ)))
    have hδ_c1 : (δ : ℝ) ≤ δ₀_c1 := by
      exact le_trans (le_trans hδA (min_le_left (min δ₀_c1 δ₀_c2) (min δ₀_c3 (1 / 4))))
        (min_le_left δ₀_c1 δ₀_c2)
    have hδ_c2 : (δ : ℝ) ≤ δ₀_c2 := by
      exact le_trans (le_trans hδA (min_le_left (min δ₀_c1 δ₀_c2) (min δ₀_c3 (1 / 4))))
        (min_le_right δ₀_c1 δ₀_c2)
    have hδ_c3 : (δ : ℝ) ≤ δ₀_c3 := by
      exact le_trans (le_trans hδA (min_le_right (min δ₀_c1 δ₀_c2) (min δ₀_c3 (1 / 4))))
        (min_le_left δ₀_c3 (1 / 4))
    have hδ_quarter : (δ : ℝ) ≤ 1 / 4 :=
      le_trans (le_trans hδA (min_le_right (min δ₀_c1 δ₀_c2) (min δ₀_c3 (1 / 4))))
        (min_le_right δ₀_c3 (1 / 4))
    have hδ_one : (δ : ℝ) ≤ 1 := le_trans hδ_quarter (by norm_num)
    have hδ_ssf : δ ≤ δ₀_ssf := by
      exact_mod_cast (le_trans hδB (min_le_left (δ₀_ssf : ℝ) (δ₀_grid : ℝ)))
    have hδ_grid : δ ≤ δ₀_grid := by
      exact_mod_cast (le_trans hδB (min_le_right (δ₀_ssf : ℝ) (δ₀_grid : ℝ)))
    obtain ⟨hN, hδN, -⟩ := hgrid hδpos hδ_grid
    have hcard' : (t.card : ℝ) ≤ (δ : ℝ) ^ (-((⌈K₀⌉₊ : ℕ) : ℝ)) :=
      hcard.trans (Real.rpow_le_rpow_of_exponent_ge (x := δ) (y := -K₀)
        (z := -((⌈K₀⌉₊ : ℕ) : ℝ)) (by exact_mod_cast hδpos) hδ_one
        (by simpa using neg_le_neg (Nat.le_ceil K₀)))
    exact union_volume_ge_of_ball_core (E := E) η₁ ε_A η_L η_F η_D γ ((⌈K₀⌉₊ : ℕ) : ℝ) R
      hγ_pos hγF hγL M hM_pos hδpos hδ_one hN hδN
      (hc1 δ hδpos hδ_c1) (hc2 δ hδpos hδ_c2) (hc3 δ hδpos hδ_c3)
      (hnet (δ := δ) hδ_quarter (κ := κ))
      (hssf (ι := κ) (δ := δ) hδpos hδ_ssf)
      hA t W htne hball hcard' hheavy hfro hmd

end StickyKakeya

end Kakeya
