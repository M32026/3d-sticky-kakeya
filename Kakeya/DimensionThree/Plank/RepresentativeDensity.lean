/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.DimensionThree.AffineTransport
public import Kakeya.Thickness.Lemmas

/-!
# Maximal density of the thickened representatives

GWZ Lemma 6.1 needs the maximal density of the slab-local family of thickened representatives
produced by Lemma 6.13 to be smaller than the maximal density of the original `a × b × 1` plank
family, by the factor `θ * b / (a * N)`.  This file proves that transfer.

Two independent inputs produce the two factors:

* the **volume ratio** `θ * b / a`.  A representative is a `θb × b × 1` thickened plank and an
  original plank is `a × b × 1`, so `a * |Q| = θ * b * |P|` exactly (`Plank.mul_volume_thickened`,
  or here the two `Prism3D.volume_carrier` computations).  Every member of either family has the
  same volume, so no pigeonholing is needed for this step;

* the **gain `1 / N`**.  This is the substantial input, and it is *not* a cardinality bound on the
  representatives: it comes from the fibres.  Each representative `Q` carries at least `N / cN`
  original planks with `R.repr i = Q`, and the fibres of `R.repr` are pairwise disjoint
  (`Plank.ThickenedRepr.fibres_partition`), so a set of `m` representatives accounts for at least
  `m * N / cN` *distinct* original indices.  Hence `#{Q ⊆ K} ≤ cN / N * #{i : P i ⊆ K⁺}`, which is
  where the `1 / N` is created.

The remaining difficulty is that `Kakeya.maxDensity` tests containment in an *arbitrary* convex
body `K`, while the fibre planks of a representative `Q ⊆ K` are only known to lie in the
`cThk`-dilation of `Q` (`Plank.ThickenedRepr.subset_repr`), which need not lie in `K`.  The test
body therefore has to be enlarged, and the enlargement must be uniform in `Q`.  That is
`Plank.exists_prism_enlargement`: replace `K` by its outer prism (a bounded volume loss,
`Metric.volume_outerPrism_le_volume_self`) and dilate the outer prism by `1 + 2 * cThk`
(`PrismNDim.dilation_carrier_subset_dilation_of_subset`, whose factor `1 + 2 * c` is exactly the
price of dilating about each prism's own centre).  The resulting body is again a prism, so its
volume is `(1 + 2 * cThk) ^ 3` times that of the outer prism.

Affine normalization is *not* re-proved here: `Kakeya.maxDensity_mapAffine` already says a maximal
density is invariant under an affine equivalence, so the transfer survives the slab-to-unit-ball
normalization verbatim (`Plank.ThickenedRepr.maxDensity_repr_mapAffine_le`).
-/

@[expose] public section

open MeasureTheory Metric Kakeya

noncomputable section

namespace Plank

open scoped NNReal

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk : ℝ≥0}
  {ι : Type*} {s : Finset ι} {V : ι → Plank a b hab hb1}

/-! ### Controlled enlargement of a convex test body -/

/-- The constant of `Plank.exists_prism_enlargement`: the convex-body-to-prism volume comparison
constant `Metric.volume_comparison.C 3 = 4 ³ / c₃` times the cost `(1 + 2 * c) ³` of dilating the
outer prism far enough to swallow the `c`-dilation of every prism inside the body. -/
noncomputable def enlargementConst (c : ℝ≥0) : ℝ≥0 :=
  Metric.volume_comparison.C 3 * (1 + 2 * c) ^ 3

theorem enlargementConst_pos (c : ℝ≥0) : 0 < enlargementConst c := by
  have := Metric.volume_comparison.C_pos 3
  have h1 : (0 : ℝ≥0) < (1 + 2 * c) ^ 3 := by positivity
  exact mul_pos this h1

/-- **Controlled enlargement of a convex test body.**  For every convex body `K` in `ℝ³` and every
dilation factor `c` there is a *prism* `P` which contains the `c`-dilation of every prism inside
`K`, and whose volume is at most `enlargementConst c` times the volume of `K`.

This is the form the maximal-density transfer needs: the enlargement is chosen once for `K`,
uniformly in the prisms it has to absorb, and the volume loss is an absolute constant. -/
theorem exists_prism_enlargement (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (c : ℝ≥0) :
    ∃ P : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)),
      (∀ Q : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)),
          (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ K.carrier →
          ((Q.dilation c).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ P.carrier) ∧
        volume P.carrier ≤ (enlargementConst c : ENNReal) * volume K.carrier := by
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  let P0 : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
    outerPrism hn K.isCompact' K.nonempty'
  let P : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
    P0.dilation (1 + 2 * c)
  refine ⟨P, ?_, ?_⟩
  · intro Q hQK
    exact (PrismNDim.dilation_carrier_subset_dilation_of_subset
      (hQK.trans (outerPrism.self_subset hn K.isCompact' K.nonempty')) c).trans (by rfl)
  · have hvol0 : volume P0.carrier ≤
        (Metric.volume_comparison.C 3 : ENNReal) * volume K.carrier := by
      simpa [P0] using
        (Metric.volume_outerPrism_le_volume_self (E := EuclideanSpace ℝ (Fin 3)) hn
          K.convex'.convex K.isCompact' K.nonempty')
    calc
      volume P.carrier = ((1 + 2 * c : ℝ≥0) : ENNReal) ^ 3 * volume P0.carrier := by
        change volume (P0.dilation (1 + 2 * c)).carrier =
          ((1 + 2 * c : ℝ≥0) : ENNReal) ^ 3 * volume P0.carrier
        exact PrismNDim.volume_dilation P0 (1 + 2 * c)
      _ ≤ ((1 + 2 * c : ℝ≥0) : ENNReal) ^ 3 *
          ((Metric.volume_comparison.C 3 : ENNReal) * volume K.carrier) := by
        gcongr
      _ = (enlargementConst c : ENNReal) * volume K.carrier := by
        rw [enlargementConst]
        simp [ENNReal.coe_mul, ENNReal.coe_pow]
        ring

/-- **Inclusion and volume ratio for a representative inside its anchor's dilated thickening.**

A `θ`-thickened representative `Q` that lies in the `cThk`-dilated thickening of an anchor plank
`P₀` (which is what `Plank.ThickenedRepr.repr_subset_thickened` supplies) also lies in the
`Cdil`-dilation for any `cThk ≤ Cdil`, and that larger body has volume *exactly* `Cdil³` times
`Q`'s: both `Q` and `P₀.thickened θ` are `θb × b × 1` prisms, so their undilated volumes coincide
and only the dilation contributes.

These are the two pointwise inputs of `Kakeya.maxDensity_le_of_subset_of_volume_le` in the
max-density chain of GWZ (42). Note there is no reverse inclusion: the anchor's thickening is
genuinely larger than the representative. -/
theorem anchorDilation_facts {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk Cdil : ℝ≥0} (hcd : cThk ≤ Cdil)
    (P₀ : Plank a b hab hb1) (Q : ThickenedPlank θ b hθ1 hb1)
    (hQ : (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ ((P₀.thickened θ hθ1).toPrismNDim.dilation cThk).carrier) :
    (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ ((P₀.thickened θ hθ1).toPrismNDim.dilation Cdil).carrier ∧
      volume (((P₀.thickened θ hθ1).toPrismNDim.dilation Cdil).carrier :
          Set (EuclideanSpace ℝ (Fin 3)))
        = (Cdil : ENNReal) ^ 3 * volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  refine ⟨hQ.trans (PrismNDim.dilation_carrier_mono _ hcd), ?_⟩
  have hbase : volume ((P₀.thickened θ hθ1).toPrismNDim.carrier)
      = volume (Q.toPrismNDim.carrier) := by
    rw [PrismNDim.volume_carrier, PrismNDim.volume_carrier,
      Prism3D.thicknesses_eq (P₀.thickened θ hθ1), Prism3D.thicknesses_eq Q]
  rw [PrismNDim.volume_dilation, hbase]

/-! ### The fibre count -/

namespace ThickenedRepr

open scoped Classical in
/-- **Disjoint fibres create the `1 / N`.**  A set `T` of representatives each of whose fibres has
at least `N / cN` members accounts for at least `N / cN * #T` *distinct* original indices, because
the fibres of `R.repr` are pairwise disjoint. -/
theorem card_mul_le_card_biUnion_fibre (R : ThickenedRepr s V θ hθ1 cThk)
    {T : Finset (ThickenedPlank θ b hθ1 hb1)} (hT : T ⊆ R.indexSet)
    {N : ℕ} {cN : ℝ≥0} (hcN : 0 < cN)
    (hfib : ∀ Q ∈ T, (N : ℝ) / (cN : ℝ) ≤ ((s.filter fun i => R.repr i = Q).card : ℝ)) :
    (N : ℝ) * (T.card : ℝ) ≤
      (cN : ℝ) * ((T.biUnion fun Q => s.filter fun i => R.repr i = Q).card : ℝ) := by
  classical
  have hdisj : (T : Set (ThickenedPlank θ b hθ1 hb1)).PairwiseDisjoint
      (fun Q => s.filter fun i => R.repr i = Q) := by
    intro Q hQ Q' hQ' hne
    exact R.fibres_partition.1 Q (hT hQ) Q' (hT hQ') hne
  have hcard : (T.biUnion fun Q => s.filter fun i => R.repr i = Q).card =
      ∑ Q ∈ T, (s.filter fun i => R.repr i = Q).card := by
    exact Finset.card_biUnion hdisj
  have hsum_const : (∑ Q ∈ T, ((N : ℝ) / (cN : ℝ))) = (T.card : ℝ) * ((N : ℝ) / (cN : ℝ)) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hsum : ∑ Q ∈ T, ((N : ℝ) / (cN : ℝ)) ≤
      ∑ Q ∈ T, ((s.filter fun i => R.repr i = Q).card : ℝ) := by
    exact Finset.sum_le_sum fun Q hQ => hfib Q hQ
  have htarget : (N : ℝ) / (cN : ℝ) * (T.card : ℝ) ≤
      ((T.biUnion fun Q => s.filter fun i => R.repr i = Q).card : ℝ) := by
    calc
      (N : ℝ) / (cN : ℝ) * (T.card : ℝ) = ∑ Q ∈ T, ((N : ℝ) / (cN : ℝ)) := by
        rw [hsum_const, mul_comm]
      _ ≤ ∑ Q ∈ T, ((s.filter fun i => R.repr i = Q).card : ℝ) := hsum
      _ = ((∑ Q ∈ T, (s.filter fun i => R.repr i = Q).card) : ℝ) := by
        simp
      _ = ((T.biUnion fun Q => s.filter fun i => R.repr i = Q).card : ℝ) := by
        exact_mod_cast hcard.symm
  have hcN0 : (cN : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hcN)
  have hmul : (cN : ℝ) * (((N : ℝ) / (cN : ℝ)) * (T.card : ℝ)) = (N : ℝ) * (T.card : ℝ) := by
    field_simp [hcN0]
  calc
    (N : ℝ) * (T.card : ℝ) = (cN : ℝ) * (((N : ℝ) / (cN : ℝ)) * (T.card : ℝ)) := by
      rw [hmul]
    _ ≤ (cN : ℝ) * ((T.biUnion fun Q => s.filter fun i => R.repr i = Q).card : ℝ) := by
      exact mul_le_mul_of_nonneg_left htarget (le_of_lt (by exact_mod_cast hcN))

open scoped Classical in
/-- The original planks indexed by the fibres of a set of representatives all lie in a single
enlargement of any convex body containing those representatives. -/
theorem fibre_subset_of_repr_subset (R : ThickenedRepr s V θ hθ1 cThk)
    {T : Finset (ThickenedPlank θ b hθ1 hb1)}
    {P : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))}
    (hP : ∀ Q ∈ T, ((Q.toPrismNDim.dilation cThk).carrier :
        Set (EuclideanSpace ℝ (Fin 3))) ⊆ P.carrier)
    {i : ι} (hi : i ∈ T.biUnion fun Q => s.filter fun j => R.repr j = Q) :
    ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ P.carrier := by
  classical
  rcases Finset.mem_biUnion.mp hi with ⟨Q, hQ, hif⟩
  rcases Finset.mem_filter.mp hif with ⟨hi_s, hieq⟩
  exact Set.Subset.trans (R.subset_repr i hi_s) (by simpa [hieq] using hP Q hQ)

open scoped Classical in
/-- **The maximal-density transfer, division-free form.**  For every convex test body `K`, the
total volume of the representatives in `T` lying inside `K` is at most
`enlargementConst cThk * cN * (θ * b / (a * N)) * Δ_max(𝒫) * |K|`, written without the division.

This is the workhorse: `Kakeya.maxDensity_le_of_forall_sum_le` turns it into the maximal-density
statement. -/
theorem mul_sum_volume_le (R : ThickenedRepr s V θ hθ1 cThk)
    {T : Finset (ThickenedPlank θ b hθ1 hb1)} (hT : T ⊆ R.indexSet)
    {N : ℕ} {cN : ℝ≥0} (hcN : 0 < cN)
    (hfib : ∀ Q ∈ T, (N : ℝ) / (cN : ℝ) ≤ ((s.filter fun i => R.repr i = Q).card : ℝ))
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    (a : ENNReal) * (N : ENNReal) *
        ∑ Q ∈ familyIn T (fun Q => Q.toConvexSpaceBody) K,
          volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ (enlargementConst cThk : ENNReal) * (cN : ENNReal) * ((θ : ENNReal) * (b : ENNReal)) *
          maxDensity s (fun i => (V i).toConvexSpaceBody) * volume K.carrier := by
  classical
  rcases exists_prism_enlargement K cThk with ⟨P, hP_abs, hvolP⟩
  set u := familyIn T (fun Q => Q.toConvexSpaceBody) K with hu
  set F := u.biUnion fun Q => s.filter fun i => R.repr i = Q with hFdef
  -- Every `Q ∈ u` lies in `K`, so its `cThk`-dilated prism lies in `P`.
  have hP : ∀ Q ∈ u, ((Q.toPrismNDim.dilation cThk).carrier :
      Set (EuclideanSpace ℝ (Fin 3))) ⊆ P.carrier := by
    intro Q hQ
    refine hP_abs Q.toPrismNDim ?_
    have hQK : Q.carrier ⊆ K.carrier := by
      have hle : Q.toConvexSpaceBody ≤ K := (Finset.mem_filter.mp hQ).2
      exact hle
    simpa using hQK
  -- The planks indexed by the fibres of `u` all lie in `P`.
  have hFsub : F ⊆ s := by
    dsimp [F]
    exact Finset.biUnion_subset.2 (fun Q _ => Finset.filter_subset _ _)
  have hF : ∀ i ∈ F, ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ P.carrier := by
    intro i hi
    exact fibre_subset_of_repr_subset (R := R) (T := u) (P := P) hP (i := i) hi
  -- Constant volumes.
  have hQvol (Q : ThickenedPlank θ b hθ1 hb1) :
      volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) = 8 * (θ : ENNReal) * b * b := by
    rw [Prism3D.volume_carrier Q]
    push_cast
    ring
  have hVvol (i : ι) :
      volume ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) = 8 * (a : ENNReal) * b := by
    rw [Prism3D.volume_carrier (V i)]
    simp
  have hsumQ : ∑ Q ∈ u, volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (u.card : ENNReal) * (8 * (θ : ENNReal) * b * b) := by
    calc
      ∑ Q ∈ u, volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
          = ∑ _Q ∈ u, (8 * (θ : ENNReal) * b * b) := by
            refine Finset.sum_congr rfl ?_
            intro Q hQ
            exact hQvol Q
      _ = (u.card : ENNReal) * (8 * (θ : ENNReal) * b * b) := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have hsumV : ∑ i ∈ F, volume ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (F.card : ENNReal) * (8 * (a : ENNReal) * b) := by
    calc
      ∑ i ∈ F, volume ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          = ∑ _i ∈ F, (8 * (a : ENNReal) * b) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact hVvol i
      _ = (F.card : ENNReal) * (8 * (a : ENNReal) * b) := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have hidentity : (a : ENNReal) * (8 * (θ : ENNReal) * b * b)
      = (θ : ENNReal) * b * (8 * (a : ENNReal) * b) := by
    ring
  -- Counting: `N * u.card ≤ cN * F.card`.
  have hT_u : u ⊆ R.indexSet := fun Q hQ => hT ((Finset.mem_filter.mp hQ).1)
  have hfib_u : ∀ Q ∈ u, (N : ℝ) / (cN : ℝ) ≤ ((s.filter fun i => R.repr i = Q).card : ℝ) :=
    fun Q hQ => hfib Q ((Finset.mem_filter.mp hQ).1)
  have hcard_real : (N : ℝ) * (u.card : ℝ) ≤ (cN : ℝ) * (F.card : ℝ) := by
    exact card_mul_le_card_biUnion_fibre R hT_u hcN hfib_u
  have hcard_enn : (N : ENNReal) * (u.card : ENNReal) ≤ (cN : ENNReal) * (F.card : ENNReal) := by
    have hnn : (N : ℝ≥0) * (u.card : ℝ≥0) ≤ cN * (F.card : ℝ≥0) := by
      exact_mod_cast hcard_real
    simpa using (ENNReal.coe_le_coe.mpr hnn)
  -- The volume of the fibre family is controlled by the maximal density of `s` at `P`.
  have hFfam : F ⊆ (s.filter fun i => (V i).toConvexSpaceBody ≤ P.toConvexSpaceBody) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨hFsub hi, hF i hi⟩
  have hsumF : ∑ i ∈ F, volume ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ maxDensity s (fun i => (V i).toConvexSpaceBody) * volume P.carrier := by
    calc
      ∑ i ∈ F, volume ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ≤ ∑ i ∈ s.filter (fun i => (V i).toConvexSpaceBody ≤ P.toConvexSpaceBody),
              volume ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hFfam ?_
            intro i _ _
            positivity
      _ ≤ maxDensity s (fun i => (V i).toConvexSpaceBody) * volume P.carrier := by
            simpa using (sum_volume_le_maxDensity_mul_volume s (fun i => (V i).toConvexSpaceBody)
              P.toConvexSpaceBody)
  -- Main chain.
  calc
    (a : ENNReal) * (N : ENNReal) * ∑ Q ∈ u, volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = (a : ENNReal) * (N : ENNReal) * ((u.card : ENNReal) * (8 * (θ : ENNReal) * b * b)) := by
            rw [hsumQ]
    _ = (N : ENNReal) * (u.card : ENNReal) * ((a : ENNReal) * (8 * (θ : ENNReal) * b * b)) := by
            ring
    _ = (N : ENNReal) * (u.card : ENNReal) * ((θ : ENNReal) * b * (8 * (a : ENNReal) * b)) := by
            rw [hidentity]
    _ ≤ (cN : ENNReal) * (F.card : ENNReal) * ((θ : ENNReal) * b * (8 * (a : ENNReal) * b)) := by
            gcongr
    _ = ((θ : ENNReal) * b) *
          ((cN : ENNReal) * ((F.card : ENNReal) * (8 * (a : ENNReal) * b))) := by
            ring
    _ = ((θ : ENNReal) * b) *
          ((cN : ENNReal) * ∑ i ∈ F, volume ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
            rw [hsumV]
    _ ≤ ((θ : ENNReal) * b) * ((cN : ENNReal) *
          (maxDensity s (fun i => (V i).toConvexSpaceBody) * volume P.carrier)) := by
            gcongr
    _ = (θ : ENNReal) * b * (cN : ENNReal) *
          maxDensity s (fun i => (V i).toConvexSpaceBody) * volume P.carrier := by
            ring
    _ ≤ (θ : ENNReal) * b * (cN : ENNReal) *
          maxDensity s (fun i => (V i).toConvexSpaceBody) *
            ((enlargementConst cThk : ENNReal) * volume K.carrier) := by
            gcongr
    _ = (enlargementConst cThk : ENNReal) * (cN : ENNReal) * ((θ : ENNReal) * (b : ENNReal)) *
          maxDensity s (fun i => (V i).toConvexSpaceBody) * volume K.carrier := by
            ring

open scoped Classical in
/-- **The maximal-density transfer.**  Division-free form: `a * N * Δ_max(𝒬) ≤ C * cN * θ * b *
Δ_max(𝒫)`, where `𝒬` is any set `T` of thickened representatives whose fibres have at least
`N / cN` members each. -/
theorem mul_maxDensity_repr_le (R : ThickenedRepr s V θ hθ1 cThk)
    {T : Finset (ThickenedPlank θ b hθ1 hb1)} (hT : T ⊆ R.indexSet)
    {N : ℕ} {cN : ℝ≥0} (hcN : 0 < cN)
    (hfib : ∀ Q ∈ T, (N : ℝ) / (cN : ℝ) ≤ ((s.filter fun i => R.repr i = Q).card : ℝ)) :
    (a : ENNReal) * (N : ENNReal) * maxDensity T (fun Q => Q.toConvexSpaceBody) ≤
      (enlargementConst cThk : ENNReal) * (cN : ENNReal) * ((θ : ENNReal) * (b : ENNReal)) *
        maxDensity s (fun i => (V i).toConvexSpaceBody) := by
  classical
  let D : ENNReal := (enlargementConst cThk : ENNReal) * (cN : ENNReal) *
      ((θ : ENNReal) * (b : ENNReal)) * maxDensity s (fun i => (V i).toConvexSpaceBody)
  let aN : ENNReal := (a : ENNReal) * (N : ENNReal)
  have haN_ne_top : aN ≠ ⊤ := by
    dsimp [aN]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.natCast_ne_top N)
  by_cases haN0 : aN = 0
  · change aN * maxDensity T (fun Q => Q.toConvexSpaceBody) ≤ D
    simp [haN0]
  · have hmd : maxDensity T (fun Q => Q.toConvexSpaceBody) ≤ D / aN := by
      apply Kakeya.maxDensity_le_of_forall_sum_le
      intro K
      rw [← ENNReal.mul_div_right_comm]
      rw [ENNReal.le_div_iff_mul_le (Or.inl haN0) (Or.inl haN_ne_top)]
      rw [mul_comm]
      simpa [aN, D, Kakeya.familyIn] using mul_sum_volume_le R hT hcN hfib K
    calc
      aN * maxDensity T (fun Q => Q.toConvexSpaceBody) ≤ aN * (D / aN) := by
        exact mul_le_mul_right hmd aN
      _ = D := by
        rw [ENNReal.mul_div_cancel haN0 haN_ne_top]

open scoped Classical in
/-- **The maximal-density transfer, in the `θ * b / (a * N)` form used by GWZ Lemma 6.1.** -/
theorem maxDensity_repr_le (R : ThickenedRepr s V θ hθ1 cThk)
    {T : Finset (ThickenedPlank θ b hθ1 hb1)} (hT : T ⊆ R.indexSet)
    {N : ℕ} {cN : ℝ≥0} (hcN : 0 < cN) (ha : 0 < a) (hN : 0 < N)
    (hfib : ∀ Q ∈ T, (N : ℝ) / (cN : ℝ) ≤ ((s.filter fun i => R.repr i = Q).card : ℝ)) :
    maxDensity T (fun Q => Q.toConvexSpaceBody) ≤
      ((enlargementConst cThk * cN : ℝ≥0) : ENNReal) *
          ((θ * b / (a * (N : ℝ≥0)) : ℝ≥0) : ENNReal) *
        maxDensity s (fun i => (V i).toConvexSpaceBody) := by
  classical
  have hle := Plank.ThickenedRepr.mul_maxDensity_repr_le R hT hcN hfib
  have ha_ne : (a : ENNReal) ≠ 0 := (ENNReal.coe_ne_zero.mpr (ne_of_gt ha))
  have hN0 : (N : ℝ≥0) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hN_ne : (N : ENNReal) ≠ 0 := by
    rw [← ENNReal.coe_natCast]
    exact ENNReal.coe_ne_zero.mpr hN0
  have han_ne : (a : ENNReal) * (N : ENNReal) ≠ 0 := mul_ne_zero ha_ne hN_ne
  have han_ne_top : (a : ENNReal) * (N : ENNReal) ≠ ⊤ :=
    WithTop.mul_ne_top ENNReal.coe_ne_top (ENNReal.natCast_ne_top N)
  have hden0 : (a * (N : ℝ≥0) : ℝ≥0) ≠ 0 := mul_ne_zero (ne_of_gt ha) hN0
  calc
    maxDensity T (fun Q => Q.toConvexSpaceBody) ≤
        ((enlargementConst cThk : ENNReal) * (cN : ENNReal) * ((θ : ENNReal) * (b : ENNReal)) *
          maxDensity s (fun i => (V i).toConvexSpaceBody)) / ((a : ENNReal) * (N : ENNReal)) := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl han_ne) (Or.inl han_ne_top)]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hle
    _ = ((enlargementConst cThk * cN : ℝ≥0) : ENNReal) *
          ((θ * b / (a * (N : ℝ≥0)) : ℝ≥0) : ENNReal) *
        maxDensity s (fun i => (V i).toConvexSpaceBody) := by
      rw [ENNReal.coe_mul, ENNReal.coe_div hden0, ENNReal.coe_mul, ENNReal.coe_mul]
      simp [mul_assoc, mul_comm, mul_left_comm, ENNReal.div_eq_inv_mul]

open scoped Classical in
/-- **The transfer survives the slab normalization.**  `Kakeya.maxDensity_mapAffine` makes a
maximal density invariant under an affine equivalence, so mapping both families through the
slab-to-unit-ball normalization `f` (`Kakeya.Slab.normalizeScaled`) leaves the estimate unchanged.
This is the form a Section 6 consumer uses after normalizing the ambient slab. -/
theorem maxDensity_repr_mapAffine_le (R : ThickenedRepr s V θ hθ1 cThk)
    {T : Finset (ThickenedPlank θ b hθ1 hb1)} (hT : T ⊆ R.indexSet)
    {N : ℕ} {cN : ℝ≥0} (hcN : 0 < cN) (ha : 0 < a) (hN : 0 < N)
    (hfib : ∀ Q ∈ T, (N : ℝ) / (cN : ℝ) ≤ ((s.filter fun i => R.repr i = Q).card : ℝ))
    (f : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    maxDensity T (fun Q => (Q.toConvexSpaceBody).mapAffine f) ≤
      ((enlargementConst cThk * cN : ℝ≥0) : ENNReal) *
          ((θ * b / (a * (N : ℝ≥0)) : ℝ≥0) : ENNReal) *
        maxDensity s (fun i => ((V i).toConvexSpaceBody).mapAffine f) := by
  rw [Kakeya.maxDensity_mapAffine T (fun Q => Q.toConvexSpaceBody) f]
  rw [Kakeya.maxDensity_mapAffine s (fun i => (V i).toConvexSpaceBody) f]
  exact Plank.ThickenedRepr.maxDensity_repr_le R hT hcN ha hN hfib

end ThickenedRepr

end Plank

end

end
