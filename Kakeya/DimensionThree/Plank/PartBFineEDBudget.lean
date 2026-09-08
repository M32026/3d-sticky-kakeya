/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.PartBFineEssDistinct
public import Kakeya.DimensionThree.Plank.Prop66ARepaired

/-!
# The essential-distinctness loss in Proposition 6.6(B)

GWZ's factor `Δmax(T) ^ (1 - β)` pays the loss from extracting an essentially
distinct subfamily. The equality case makes this accounting explicit.

`Kakeya.PartBFineED.duplicatedTube δ` repeats one fully shaded central tube
`N` times. The family lies in the unit ball, has fullness one and satisfies
the shading-uniformity bounds at constant one. Any essentially distinct
subfamily contains at most one tube, so its mass-retention loss is `N`.
With `|u| = 1`, `|q| = N`, and `Δmax(q) = N`, the budget is exactly
`N ^ (1 - β) * N ^ β = N`, proved by `Kakeya.rpow_one_sub_mul_rpow`.
This is the equality case of `Kakeya.multiplicity_bound_transfer_of_massShare`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

namespace PartBFineED

/-! ### Half two: the density budget is not free, and the shortfall is exactly the density -/

variable {δ : ℝ≥0}

/-- **The `N`-fold repetition of one `δ`-tube, fully shaded.**  Every member is the same shaded
tube; only the index set grows. -/
def duplicatedTube (δ : ℝ≥0) : ℕ → ShadedTube δ (EuclideanSpace ℝ (Fin 3)) :=
  fun _ => fullyShadedTube (centralUnitTube δ)

@[simp] theorem duplicatedTube_carrier (δ : ℝ≥0) (i : ℕ) :
    ((duplicatedTube δ i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ((centralUnitTube δ).carrier : Set (EuclideanSpace ℝ (Fin 3))) := rfl

@[simp] theorem duplicatedTube_shade (δ : ℝ≥0) (i : ℕ) :
    (duplicatedTube δ i).shade = ((centralUnitTube δ).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
  rfl

/-- The common carrier has positive volume. -/
theorem volume_centralUnitTube_pos (hδ0 : 0 < δ) :
    0 < volume ((centralUnitTube δ).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  refine lt_of_lt_of_le ?_ (Tube.le_volume (centralUnitTube δ))
  have hc : (0 : ℝ≥0) < Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
    Tube.le_volume.c_pos _
  refine zero_lt_iff.mpr (mul_ne_zero (ENNReal.coe_ne_zero.mpr hc.ne') ?_)
  exact pow_ne_zero _ (ENNReal.coe_ne_zero.mpr hδ0.ne')

/-- …and finite volume. -/
theorem volume_centralUnitTube_ne_top (δ : ℝ≥0) :
    volume ((centralUnitTube δ).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ ⊤ :=
  (centralUnitTube δ).isCompact'.measure_lt_top.ne

/-- **The duplicated family lies in the unit ball**, which is the window hypothesis of
Proposition 6.6(B). -/
theorem duplicated_ball (hδ : δ ≤ 1 / 2) (N : ℕ) :
    ∀ i ∈ Finset.range N,
      ((duplicatedTube δ i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ Metric.closedBall 0 1 :=
  fun _ _ => centralUnitTube_carrier_subset_closedBall hδ

/-- **The duplicated family has fullness `1`**, so it satisfies `δ ^ η ≤ λ` for every `η ≥ 0`
whenever `δ ≤ 1`.  Every shade is the whole carrier. -/
theorem duplicated_fullness (hδ0 : 0 < δ) {N : ℕ} (hN : 0 < N) :
    ShadedBody.fullness (Finset.range N)
      (fun i => (duplicatedTube δ i).toShadedBody) = 1 := by
  have hv0 : volume ((centralUnitTube δ).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ 0 :=
    (volume_centralUnitTube_pos hδ0).ne'
  have hvtop := volume_centralUnitTube_ne_top δ
  have hsum : (∑ _i ∈ Finset.range N,
      volume ((centralUnitTube δ).carrier : Set (EuclideanSpace ℝ (Fin 3))))
      = (N : ℝ≥0∞) * volume ((centralUnitTube δ).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hne : (N : ℝ≥0∞) * volume ((centralUnitTube δ).carrier
      : Set (EuclideanSpace ℝ (Fin 3))) ≠ 0 := by
    refine mul_ne_zero ?_ hv0
    exact_mod_cast hN.ne'
  have htop : (N : ℝ≥0∞) * volume ((centralUnitTube δ).carrier
      : Set (EuclideanSpace ℝ (Fin 3))) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hvtop
  have : ShadedBody.fullness' (Finset.range N)
      (fun i => (duplicatedTube δ i).toShadedBody) = 1 := by
    show (∑ _i ∈ Finset.range N, volume ((centralUnitTube δ).carrier
            : Set (EuclideanSpace ℝ (Fin 3))))
          / (∑ _i ∈ Finset.range N, volume ((centralUnitTube δ).carrier
            : Set (EuclideanSpace ℝ (Fin 3)))) = 1
    rw [hsum]
    exact ENNReal.div_self hne htop
  have hc := ShadedBody.coe_fullness (Finset.range N)
    (fun i => (duplicatedTube δ i).toShadedBody)
  rw [this] at hc
  exact_mod_cast hc

/-- **The maximal density of the duplicated family is at least `N`.**

Test the density against the common carrier itself: all `N` bodies lie in it, so the numerator is
`N` times its volume. -/
theorem le_maxDensity_duplicated (hδ0 : 0 < δ) (N : ℕ) :
    (N : ℝ≥0∞) ≤ Kakeya.maxDensity (Finset.range N)
      (fun i => (duplicatedTube δ i).toConvexSpaceBody) := by
  classical
  set K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := (centralUnitTube δ).toConvexSpaceBody
    with hK
  have hv0 : volume (K.carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ 0 :=
    (volume_centralUnitTube_pos hδ0).ne'
  have hvtop : volume (K.carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ ⊤ :=
    volume_centralUnitTube_ne_top δ
  have hfilter : ({i ∈ Finset.range N | (duplicatedTube δ i).toConvexSpaceBody ≤ K}
      : Finset ℕ) = Finset.range N := by
    refine Finset.filter_eq_self.mpr ?_
    intro i _
    exact le_rfl
  have hdens : Kakeya.densityIn (Finset.range N)
      (fun i => (duplicatedTube δ i).toConvexSpaceBody) K = (N : ℝ≥0∞) := by
    show (∑ i ∈ Finset.range N with (duplicatedTube δ i).toConvexSpaceBody ≤ K,
        volume ((duplicatedTube δ i).toConvexSpaceBody).carrier)
        / volume K.carrier = (N : ℝ≥0∞)
    rw [hfilter]
    simp only [duplicatedTube_carrier]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_assoc,
      ENNReal.div_self hv0 hvtop, mul_one]
  calc (N : ℝ≥0∞) = Kakeya.densityIn (Finset.range N)
        (fun i => (duplicatedTube δ i).toConvexSpaceBody) K := hdens.symm
    _ ≤ Kakeya.maxDensity (Finset.range N)
        (fun i => (duplicatedTube δ i).toConvexSpaceBody) :=
      Kakeya.le_maxDensity _ _ K

/-- **Every pairwise essentially distinct subfamily of the duplicated family has at most one
member.**  Two distinct indices carry the *same* carrier, and a body of positive finite volume is
never essentially distinct from itself. -/
theorem card_le_one_of_pairwise_ED (hδ0 : 0 < δ) {N : ℕ} {u : Finset ℕ}
    (_hu : u ⊆ Finset.range N)
    (hED : (u : Set ℕ).Pairwise
      (fun i j => _root_.IsEssentiallyDistinct
        ((duplicatedTube δ i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ((duplicatedTube δ j).carrier : Set (EuclideanSpace ℝ (Fin 3))))) :
    u.card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr ?_
  intro i hi j hj
  by_contra hne
  have h := hED (by exact_mod_cast hi) (by exact_mod_cast hj) hne
  exact not_isEssentiallyDistinct_self
    (volume_centralUnitTube_pos hδ0).ne' (volume_centralUnitTube_ne_top δ) h

/-- **The sharpness statement: every mass-share constant for every essentially distinct refinement
of the duplicated family is at least `N`.**

This is the exact price of the essential-distinctness route, and it is not an artefact of the
constant in `Kakeya.exists_pairwise_ED_subfamily_of_maxDensity`: the retained subfamily can hold at
most one of the `N` equal shades, so the mass ratio is `N` however the subfamily is chosen. -/
theorem le_of_massShare_duplicated (hδ0 : 0 < δ) {N : ℕ} {u : Finset ℕ}
    (hu : u ⊆ Finset.range N)
    (hED : (u : Set ℕ).Pairwise
      (fun i j => _root_.IsEssentiallyDistinct
        ((duplicatedTube δ i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ((duplicatedTube δ j).carrier : Set (EuclideanSpace ℝ (Fin 3)))))
    {L : ℝ≥0∞}
    (hmass : (∑ i ∈ Finset.range N, volume (duplicatedTube δ i).shade)
      ≤ L * ∑ i ∈ u, volume (duplicatedTube δ i).shade) :
    (N : ℝ≥0∞) ≤ L := by
  classical
  set v : ℝ≥0∞ := volume ((centralUnitTube δ).carrier : Set (EuclideanSpace ℝ (Fin 3))) with hv
  have hv0 : v ≠ 0 := (volume_centralUnitTube_pos hδ0).ne'
  have hvtop : v ≠ ⊤ := volume_centralUnitTube_ne_top δ
  have hL : (∑ i ∈ Finset.range N, volume (duplicatedTube δ i).shade) = (N : ℝ≥0∞) * v := by
    simp only [duplicatedTube_shade, hv]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hR : (∑ i ∈ u, volume (duplicatedTube δ i).shade) = (u.card : ℝ≥0∞) * v := by
    simp only [duplicatedTube_shade, hv]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (u.card : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast card_le_one_of_pairwise_ED hδ0 hu hED
  rw [hL, hR] at hmass
  have hstep : v * (N : ℝ≥0∞) ≤ v * L := by
    have h0 : (N : ℝ≥0∞) * v ≤ L * v := by
      refine hmass.trans ?_
      calc L * ((u.card : ℝ≥0∞) * v) = (L * (u.card : ℝ≥0∞)) * v := by ring
        _ ≤ (L * 1) * v := by gcongr
        _ = L * v := by rw [mul_one]
    calc v * (N : ℝ≥0∞) = (N : ℝ≥0∞) * v := by ring
      _ ≤ L * v := h0
      _ = v * L := by ring
  exact (ENNReal.mul_le_mul_iff_right hv0 hvtop).mp hstep

/-- **The density budget is not implied by the window and fullness hypotheses of GWZ Proposition
6.6(B).**

For every scale `δ ∈ (0, 1/2]` and every exponent `θ`, there is a family of shaded `δ`-tubes inside
the unit ball, of fullness `1`, whose maximal density exceeds `δ ^ (-θ)`.  So no `θ` fixed before
the configuration bounds the density, and the `M` of
`Kakeya.exists_inner_plank_conflict_degree_bound_of_edUpToMult` cannot be supplied from
Proposition 6.6(B)'s own hypotheses. -/
theorem exists_family_not_maxDensity_le (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (θ : ℝ) :
    ∃ N : ℕ, 0 < N ∧
      (∀ i ∈ Finset.range N,
        ((duplicatedTube δ i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ Metric.closedBall 0 1) ∧
      ShadedBody.fullness (Finset.range N)
        (fun i => (duplicatedTube δ i).toShadedBody) = 1 ∧
      ¬ (Kakeya.maxDensity (Finset.range N)
          (fun i => (duplicatedTube δ i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-θ)) := by
  have hδtop : ((δ : ℝ≥0∞)) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ0' : ((δ : ℝ≥0∞)) ≠ 0 := by simpa using hδ0.ne'
  have hfin : (δ : ℝ≥0∞) ^ (-θ) ≠ ⊤ := by
    simp [ENNReal.rpow_eq_top_iff, hδ0', hδtop]
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hfin
  refine ⟨max 1 N, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    duplicated_ball hδ _, duplicated_fullness hδ0 (lt_of_lt_of_le zero_lt_one (le_max_left _ _)),
    ?_⟩
  intro hcon
  have h1 : ((max 1 N : ℕ) : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-θ) :=
    le_trans (le_maxDensity_duplicated hδ0 _) hcon
  have h2 : ((N : ℕ) : ℝ≥0∞) ≤ ((max 1 N : ℕ) : ℝ≥0∞) := by
    exact_mod_cast Nat.le_max_right 1 N
  exact absurd (h2.trans h1) (not_le.2 hN)

/-! ### The Definition-2.2 clause does not bound `N` either -/

/-- **The duplicated family is uniform in the sense of GWZ Definition 2.2, at the constant `1`,
for every `N`.**

The witness is the *one-node* cover: at every grid scale the single node is the common tube
rescaled to that scale, every member is assigned to it, and the branching number is `N` itself.
Bounded overlap is then a count over a singleton, and both class brackets and both branching
brackets are equalities.

`Kakeya.nonempty_shadedUniformTubeSet_of_card_le` cannot be used here — it assigns each member its
own node, which forces `s.card ≤ C` — and that is precisely the reading under which one might have
hoped Definition 2.2 bounds the family.  It does not: the one-node cover satisfies every clause at
`C = 1`, uniformly in `N`.  So the clause
`∃ C ≤ δ ^ (-η), Nonempty (ShadedTube.ShadedUniformTubeSet q T (Tube.ssfGridLen δ) C)` of
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` places no bound on the fine family's maximal
density.  (Since  the statement carries fine-family pairwise essential distinctness beside
its window, and *that* binder excludes this witness: it is the clause of GWZ Definition 2.1(ii) at
`ρ = δ` that the grid uniformity was shown here not to render.) -/
theorem nonempty_shadedUniformTubeSet_duplicated (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (N Ngrid : ℕ) :
    Nonempty (ShadedTube.ShadedUniformTubeSet (Finset.range N) (duplicatedTube δ) Ngrid 1) := by
  classical
  let gcs : Tube.GridCoverSystem (Finset.range N)
      (fun i => (duplicatedTube δ i).toTube) Ngrid :=
    { indexSet := fun _ => ({0} : Finset ℕ)
      assign := fun _ _ => 0
      tube := fun k _ => (centralUnitTube δ).rescale (Tube.gridScale δ Ngrid k)
      assign_mem := by intro k hk i hi; exact Finset.mem_singleton_self 0
      le_tube_assign := by
        intro k hk i hi
        exact Tube.le_rescale (centralUnitTube δ) (le_gridScale_of_le hδ0 hδ1 hk)
      nested := by intro k hk i hi j hj h; rfl
      tube_nested := by
        intro k hk i hi
        exact Tube.rescale_le_rescale_of_radius_le (centralUnitTube δ)
          (Tube.gridScale_antitone hδ0 hδ1 Ngrid (Nat.le_succ k)) }
  have hclass0 : ∀ k : ℕ,
      Tube.coverClass (Finset.range N) (gcs.assign k) 0 = Finset.range N := by
    intro k
    ext i
    simp [Tube.coverClass, gcs]
  let utu : Tube.UniformTubeSet (Finset.range N)
      (fun i => (duplicatedTube δ i).toTube) Ngrid 1 :=
    { cover := gcs
      branchingN := fun _ => (N : ℝ≥0)
      tube_injOn := by
        intro k hk a ha b hb _
        have ha0 : a = 0 := by simpa [gcs] using ha
        have hb0 : b = 0 := by simpa [gcs] using hb
        rw [ha0, hb0]
      boundedOverlap := by
        intro k hk W
        have hcard : ∀ t : Finset ℕ, t ⊆ gcs.indexSet k → (t.card : ℝ≥0) ≤ 1 := by
          intro t ht
          have hle : t.card ≤ (gcs.indexSet k).card := Finset.card_le_card ht
          have h1 : (gcs.indexSet k).card = 1 := by simp [gcs]
          rw [h1] at hle
          exact_mod_cast hle
        exact hcard _ (Finset.filter_subset _ _)
      card_class_le := by
        intro k hk j hj
        have hj0 : j = 0 := by simpa [gcs] using hj
        subst hj0
        rw [hclass0 k]
        simp
      le_card_class := by
        intro k hk j hj
        have hj0 : j = 0 := by simpa [gcs] using hj
        subst hj0
        rw [hclass0 k]
        simp }
  have hshade : ∀ (k : ℕ) (x : EuclideanSpace ℝ (Fin 3)) (i : ℕ),
      x ∈ (duplicatedTube δ i).shade →
      ShadedTube.shadeClass (Finset.range N) (duplicatedTube δ) (utu.cover.assign k)
        (utu.cover.assign k i) x = Finset.range N := by
    intro k x i hxi
    show ((Tube.coverClass (Finset.range N) (gcs.assign k) (gcs.assign k i)).filter
      (fun z => x ∈ (duplicatedTube δ z).shade)) = Finset.range N
    rw [show gcs.assign k i = 0 from rfl, hclass0 k]
    refine Finset.filter_eq_self.mpr ?_
    intro z _
    exact hxi
  refine ⟨{ tubeUniform := utu
            branchingN := fun _ => (N : ℝ≥0)
            localN := fun _ _ => (N : ℝ≥0)
            card_shadeClass_le := ?_
            le_card_shadeClass := ?_
            branchingN_le := ?_
            le_branchingN := ?_ }⟩
  · intro x hx k hk i hi hxi
    rw [hshade k x i hxi]
    simp
  · intro x hx k hk i hi hxi
    rw [hshade k x i hxi]
    simp
  · intro x hx k hk; simp
  · intro x hx k hk; simp


/-! ### The capstone: the quantified shortfall -/

/-- **The shortfall of the essential-distinctness route, in one statement.**

For every scale `δ ∈ (0, 1/2]`, every grid length, and every candidate density exponent `θ`, there
is a family of shaded `δ`-tubes which

* lies in the unit ball — the window hypothesis of `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`;
* has fullness `1`, so it meets that theorem's fullness hypothesis at every exponent;
* satisfies GWZ Definition 2.2 at the constant `1`, so it meets that theorem's uniformity clause
  at every budget;
* has maximal density **exceeding** `δ ^ (-θ)`; and
* forces **every** mass-share constant of **every** pairwise essentially distinct refinement to be
  at least `N`, which is that same unbounded quantity.

So the `M` that `Kakeya.exists_inner_plank_conflict_degree_bound_of_edUpToMult` needs is not
available from the hypotheses of Proposition 6.6(B), and the gap is not an artefact of the
particular extraction: it is the density itself.  Conversely
`Kakeya.PartBFineED.eventually_degraded_degree_le` shows that a sub-polynomial density budget is
*sufficient*.  **The leaf-scale essential-distinctness gap of GWZ Proposition 6.6(B), as the
statement stood before, was exactly a sub-polynomial maximal-density budget on the fine
family, neither more nor less.**   closed that gap on the other side: the family below
is not GWZ-uniform (Definition 2.1(ii) at `ρ = δ`), and the live statement now carries the
fine-family essential-distinctness binder that excludes it. -/
theorem exists_prop66B_admissible_family_with_massShare_ge
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (θ : ℝ) (Ngrid : ℕ) :
    ∃ N : ℕ, 0 < N ∧
      (∀ i ∈ Finset.range N,
        ((duplicatedTube δ i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ Metric.closedBall 0 1) ∧
      ShadedBody.fullness (Finset.range N)
        (fun i => (duplicatedTube δ i).toShadedBody) = 1 ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet (Finset.range N) (duplicatedTube δ) Ngrid 1) ∧
      ¬ (Kakeya.maxDensity (Finset.range N)
          (fun i => (duplicatedTube δ i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-θ)) ∧
      (∀ u ⊆ Finset.range N,
        (u : Set ℕ).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct
            ((duplicatedTube δ i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            ((duplicatedTube δ j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        ∀ L : ℝ≥0∞,
          (∑ i ∈ Finset.range N, volume (duplicatedTube δ i).shade)
            ≤ L * ∑ i ∈ u, volume (duplicatedTube δ i).shade →
          (N : ℝ≥0∞) ≤ L) := by
  have hδ1 : δ ≤ 1 := le_trans hδ (by norm_num)
  obtain ⟨N, hN0, hball, hfull, hdens⟩ := exists_family_not_maxDensity_le hδ0 hδ θ
  exact ⟨N, hN0, hball, hfull,
    nonempty_shadedUniformTubeSet_duplicated hδ0 hδ1 N Ngrid, hdens,
    fun u hu hED L hmass => le_of_massShare_duplicated hδ0 hu hED hmass⟩

end PartBFineED

end Kakeya

end

end
