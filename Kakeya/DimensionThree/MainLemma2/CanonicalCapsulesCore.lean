/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.CanonicalCapsulesDilation
public import Kakeya.DimensionThree.MainLemma2.BallDataGeneral
public import Kakeya.DimensionThree.MainLemma2.BallMarginLoss
public import Kakeya.DimensionThree.MainLemma2.BallCoreEDComparable

/-!
# C7-b: the canonical-capsule `BallDataCore` of a given ball cover

The refined `propvnslocalization` (refined text l.3700–3724, l.5354–5473; map row C7-b,
) builds the per-ball segments **not** as one capsule per
tube (T3, `Kakeya.VeryNotSticky.ballDataCoreOfCover`) but as one capsule per point of a canonical
net of the tubes meeting the piece, each carrying the **fibre** of tubes assigned to it, and it
regularises the fibre count on the working shading by a dyadic pigeonhole (l.3735–3743).  This
file assembles that core, `Kakeya.VeryNotSticky.CoverData.capsuleCore`, at the tree's objects:

* `CoverData` bundles the eight clauses of a given `r₁`-ball cover together with the radius floor
  `32 δ ≤ r₁` (the general branch has `edRadiusConstant · δ ≤ r₁`, `edRadiusConstant ≥ 32`);
* per ball `B`: the index set `idx B` of tubes whose shading meets the piece, the capsule net
  `net B : CapsuleNet (idx B) … (ctr B) (r₁/4) δ` (`CanonicalCapsules.lean`), the fibres, the
  capsules `caps B ν = capsuleAt (T ν) (ctr B) (2δ) (r₁/4)`;
* the level-`m` working shading `Yg m i`: on each piece the truncation of the shading of `i` to
  the points of its fibre's level-`m` bin at which `i` is among the first `m` fibre members
  (`CanonicalCapsulesFibre.lean`), so that **exactly `m`** fibre tubes shade every point of a
  segment's shade — `Cm = 1`, `m` the chosen dyadic level;
* the segments at level `m`: the net points whose bin is nonempty, on the balls that have one.

The two non-local inputs of the core — the ball set being nonempty at the level and the working
shading retaining `Cg⁻¹` of the mass — are hypotheses of the `def`; the level selection that
supplies them (a two-constraint pigeonhole over the dyadic levels: mass-heavy **and** full) is the
business of `CanonicalCapsulesMass.lean`.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace Kakeya.VeryNotSticky

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open scoped Classical in
/-- A linear order on the index type, chosen classically; only `firstM` reads it. -/
@[reducible] noncomputable def indexOrder (cfg : VeryNotSticky.{u}) : LinearOrder cfg.ι :=
  linearOrderOfSTO WellOrderingRel

/-- The capsule half-length `r₁ / 4` of the canonical-capsule core (T3's half-length; the
dilation twin `le_capsuleDilationConstant_mul` is measured at `4 L = r₁`). -/
noncomputable def capL (cfg : VeryNotSticky.{u}) : ℝ := (cfg.r₁ : ℝ) / 4

/-- The capsule radius `2δ` of the canonical-capsule core. -/
noncomputable def capρ (cfg : VeryNotSticky.{u}) : NNReal := 2 * cfg.δ

theorem capL_pos (cfg : VeryNotSticky.{u}) : 0 < capL cfg := by
  unfold capL
  have : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  positivity

theorem capL_nonneg (cfg : VeryNotSticky.{u}) : 0 ≤ capL cfg := (capL_pos cfg).le

theorem capL_le_half (cfg : VeryNotSticky.{u}) : capL cfg ≤ 1 / 2 := by
  unfold capL; have := r₁_le_one cfg; linarith

theorem two_mul_capL_le_one (cfg : VeryNotSticky.{u}) : 2 * capL cfg ≤ 1 := by
  have := capL_le_half cfg; linarith

theorem coe_capρ (cfg : VeryNotSticky.{u}) : ((capρ cfg : NNReal) : ℝ) = 2 * (cfg.δ : ℝ) := by
  simp [capρ]

theorem capρ_pos (cfg : VeryNotSticky.{u}) : 0 < capρ cfg := by
  unfold capρ; have := cfg.hδ; positivity

/-- **The eight clauses of a given `r₁`-ball cover**, bundled with the radius floor `32 δ ≤ r₁`. -/
structure CoverData (cfg : VeryNotSticky.{u}) (bι : Type u) where
  bs : Finset bι
  ctr : bι → E3
  P : bι → Set E3
  bs_nonempty : bs.Nonempty
  Pball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16)
  Pball : ∀ B ∈ bs, P B ⊆ closedBall (ctr B) (cfg.r₁ : ℝ)
  Pdisj : (bs : Set bι).PairwiseDisjoint P
  Pmeas : ∀ B, MeasurableSet (P B)
  Pcov : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B
  overlap : ∀ (x : E3) (t : Finset bι), t ⊆ bs →
    (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant
  Pne : ∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty
  δr : 32 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)

namespace CoverData

variable {cfg : VeryNotSticky.{u}} {bι : Type u} (cd : CoverData cfg bι)

theorem δ_le (cd : CoverData cfg bι) : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) := by
  have := cd.δr; have := (cfg.δ).coe_nonneg; linarith

open scoped Classical in
/-- The tubes whose shading meets the piece `P B`. -/
noncomputable def idx (B : bι) : Finset cfg.ι :=
  cfg.s.filter fun i => ((cfg.T i).shade ∩ cd.P B).Nonempty

open scoped Classical in
theorem mem_idx {B : bι} {i : cfg.ι} :
    i ∈ cd.idx B ↔ i ∈ cfg.s ∧ ((cfg.T i).shade ∩ cd.P B).Nonempty := by
  simp [idx]

open scoped Classical in
theorem idx_subset (B : bι) : cd.idx B ⊆ cfg.s := Finset.filter_subset _ _

open scoped Classical in
theorem card_idx_le (B : bι) : (cd.idx B).card ≤ cfg.s.card :=
  Finset.card_le_card (cd.idx_subset B)

open scoped Classical in
/-- The canonical capsule net of the piece: `ε = δ`, half-length `r₁/4`, centred at `ctr B`. -/
noncomputable def net (B : bι) :
    CapsuleNet (cd.idx B) (fun i => (cfg.T i).toTube) (cd.ctr B) (capL cfg) (cfg.δ : ℝ) :=
  Classical.choice (exists_capsuleNet _ _ _ _ (by exact_mod_cast cfg.hδ))

/-- The piece of the shading of `i` in `P B`. -/
def S (B : bι) (i : cfg.ι) : Set E3 := (cfg.T i).shade ∩ cd.P B

theorem S_subset_shade (B : bι) (i : cfg.ι) : cd.S B i ⊆ (cfg.T i).shade :=
  Set.inter_subset_left

theorem S_subset_P (B : bι) (i : cfg.ι) : cd.S B i ⊆ cd.P B := Set.inter_subset_right

theorem measurableSet_S (B : bι) (i : cfg.ι) : MeasurableSet (cd.S B i) :=
  (cfg.T i).measurableSet_shade.inter (cd.Pmeas B)

open scoped Classical in
theorem S_eq_empty_of_not_mem_idx {B : bι} {i : cfg.ι} (hi : i ∈ cfg.s) (h : i ∉ cd.idx B) :
    cd.S B i = ∅ := by
  by_contra hne
  exact h ((cd.mem_idx).2 ⟨hi, Set.nonempty_iff_ne_empty.2 hne⟩)

open scoped Classical in
/-- The fibre of a net point. -/
noncomputable def fib (B : bι) (ν : cfg.ι) : Finset cfg.ι := (cd.net B).fibre ν

open scoped Classical in
theorem fib_subset_idx (B : bι) (ν : cfg.ι) : cd.fib B ν ⊆ cd.idx B := (cd.net B).fibre_subset ν

open scoped Classical in
theorem fib_subset_s (B : bι) (ν : cfg.ι) : cd.fib B ν ⊆ cfg.s :=
  (cd.fib_subset_idx B ν).trans (cd.idx_subset B)

open scoped Classical in
theorem mem_fib_iff {B : bι} {i ν : cfg.ι} :
    i ∈ cd.fib B ν ↔ i ∈ cd.idx B ∧ (cd.net B).assign i = ν := (cd.net B).mem_fibre_iff

open scoped Classical in
theorem mem_fib_assign {B : bι} {i : cfg.ι} (hi : i ∈ cd.idx B) :
    i ∈ cd.fib B ((cd.net B).assign i) := (cd.net B).mem_fibre_assign hi

open scoped Classical in
theorem net_mem_of_mem_fib {B : bι} {i ν : cfg.ι} (hi : i ∈ cd.fib B ν) : ν ∈ (cd.net B).net := by
  obtain ⟨hI, hν⟩ := cd.mem_fib_iff.1 hi
  rw [← hν]; exact (cd.net B).assign_mem i hI

open scoped Classical in
theorem fib_disjoint {B : bι} {ν μ : cfg.ι} (hν : ν ∈ (cd.net B).net) (hμ : μ ∈ (cd.net B).net)
    (h : ν ≠ μ) : Disjoint (cd.fib B ν) (cd.fib B μ) :=
  (cd.net B).fibre_disjoint hν hμ h

open scoped Classical in
/-- The level-`m` bin of a net point. -/
def bin (B : bι) (ν : cfg.ι) (m : ℕ) : Set E3 := levelBin (cd.fib B ν) (cd.S B) (cd.P B) m

open scoped Classical in
/-- The level-`m` truncation of the shading of `i` inside the fibre of `ν` on the piece `B`. -/
noncomputable def trunc (B : bι) (ν : cfg.ι) (m : ℕ) (i : cfg.ι) : Set E3 :=
  letI := indexOrder cfg
  truncated (cd.fib B ν) (cd.S B) (cd.P B) m i

/-- The capsule of a net point: radius `2δ`, half-length `r₁/4`, centred at `ctr B`. -/
noncomputable def caps (B : bι) (ν : cfg.ι) : Set E3 :=
  capsuleAt (cfg.T ν).toTube (cd.ctr B) (capρ cfg) (capL cfg)

theorem bin_subset_P (B : bι) (ν : cfg.ι) (m : ℕ) : cd.bin B ν m ⊆ cd.P B := fun _ hx => hx.1

open scoped Classical in
theorem measurableSet_bin (B : bι) (ν : cfg.ι) (m : ℕ) : MeasurableSet (cd.bin B ν m) :=
  measurableSet_levelBin _ _ (fun i _ => cd.measurableSet_S B i) (cd.Pmeas B) m

open scoped Classical in
theorem trunc_subset_S (B : bι) (ν : cfg.ι) (m : ℕ) (i : cfg.ι) : cd.trunc B ν m i ⊆ cd.S B i :=
  fun _ hx => hx.1.1

open scoped Classical in
theorem trunc_subset_bin (B : bι) (ν : cfg.ι) (m : ℕ) (i : cfg.ι) :
    cd.trunc B ν m i ⊆ cd.bin B ν m := fun _ hx => hx.1.2

open scoped Classical in
theorem trunc_subset_P (B : bι) (ν : cfg.ι) (m : ℕ) (i : cfg.ι) : cd.trunc B ν m i ⊆ cd.P B :=
  (cd.trunc_subset_bin B ν m i).trans (cd.bin_subset_P B ν m)

open scoped Classical in
theorem trunc_eq_empty_of_not_mem {B : bι} {ν : cfg.ι} (m : ℕ) {i : cfg.ι}
    (hi : i ∉ cd.fib B ν) : cd.trunc B ν m i = ∅ := by
  letI := indexOrder cfg
  ext x
  simp only [trunc, truncated, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro _ hfirst
  exact hi (Finset.filter_subset _ _ (firstM_subset _ _ hfirst))

open scoped Classical in
theorem measurableSet_trunc (B : bι) (ν : cfg.ι) (m : ℕ) (i : cfg.ι) :
    MeasurableSet (cd.trunc B ν m i) := by
  by_cases hi : i ∈ cd.fib B ν
  · letI := indexOrder cfg
    exact measurableSet_truncated _ _ (fun j _ => cd.measurableSet_S B j) (cd.Pmeas B) m hi
  · rw [cd.trunc_eq_empty_of_not_mem m hi]; exact MeasurableSet.empty

open scoped Classical in
/-- A point of a positive level's bin lies in the shading of some fibre member. -/
theorem exists_mem_fib_of_mem_bin {B : bι} {ν : cfg.ι} {m : ℕ} (hm : 0 < m) {x : E3}
    (hx : x ∈ cd.bin B ν m) : ∃ i ∈ cd.fib B ν, x ∈ cd.S B i := by
  have hw : 0 < fibreWeight (cd.fib B ν) (cd.S B) x := lt_of_lt_of_le hm hx.2.1
  obtain ⟨i, hi⟩ := Finset.card_pos.1 hw
  rw [Finset.mem_filter] at hi
  exact ⟨i, hi.1, hi.2⟩

open scoped Classical in
/-- A point of a positive level's bin lies in the truncation of some fibre member. -/
theorem exists_mem_trunc_of_mem_bin {B : bι} {ν : cfg.ι} {m : ℕ} (hm : 0 < m) {x : E3}
    (hx : x ∈ cd.bin B ν m) : ∃ i ∈ cd.fib B ν, x ∈ cd.trunc B ν m i := by
  letI := indexOrder cfg
  have hcard := card_filter_truncated (cd.fib B ν) (cd.S B) (cd.P B) m hx
  have hpos :
      0 < ((cd.fib B ν).filter fun i => x ∈ truncated (cd.fib B ν) (cd.S B) (cd.P B) m i).card := by
    rw [hcard]; exact hm
  obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
  rw [Finset.mem_filter] at hi
  exact ⟨i, hi.1, hi.2⟩

/-! ### Geometry of the pieces -/

open scoped Classical in
theorem meets_of_mem_idx {B : bι} (hB : B ∈ cd.bs) {i : cfg.ι} (hi : i ∈ cd.idx B) :
    ((cfg.T i).toTube.carrier ∩ ball (cd.ctr B) ((cfg.r₁ : ℝ) / 16)).Nonempty := by
  obtain ⟨x, hx1, hx2⟩ := (cd.mem_idx.1 hi).2
  exact ⟨x, (cfg.T i).shade_subset hx1, cd.Pball16 B hB hx2⟩

theorem r16_add_δ_le_capL (cd : CoverData cfg bι) :
    (cfg.r₁ : ℝ) / 16 + (cfg.δ : ℝ) ≤ capL cfg := by
  have := cd.δ_le; unfold capL; linarith

open scoped Classical in
theorem norm_foot_sub_le_capL {B : bι} (hB : B ∈ cd.bs) {i : cfg.ι} (hi : i ∈ cd.idx B) :
    ‖foot (cfg.T i).toTube (cd.ctr B) - cd.ctr B‖ ≤ capL cfg :=
  le_trans (norm_foot_sub_le_of_meets _ _ (cd.meets_of_mem_idx hB hi)) cd.r16_add_δ_le_capL

open scoped Classical in
/-- The shading piece of a fibre member lies in the capsule of its net point. -/
theorem S_subset_caps {B : bι} (hB : B ∈ cd.bs) {i ν : cfg.ι} (hi : i ∈ cd.fib B ν) :
    cd.S B i ⊆ cd.caps B ν := by
  intro x hx
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  refine (cd.net B).tube_inter_ball_subset_capsuleAt_of_mem_fibre hi (r := (cfg.r₁ : ℝ) / 16)
    (ρ := capρ cfg) (capL_nonneg cfg) (capL_le_half cfg) cd.r16_add_δ_le_capL ?_
    ⟨(cfg.T i).shade_subset hx.1, cd.Pball16 B hB hx.2⟩
  rw [coe_capρ]; linarith

open scoped Classical in
theorem bin_subset_caps {B : bι} (hB : B ∈ cd.bs) {ν : cfg.ι} {m : ℕ} (hm : 0 < m) :
    cd.bin B ν m ⊆ cd.caps B ν := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := cd.exists_mem_fib_of_mem_bin hm hx
  exact cd.S_subset_caps hB hi hxi

/-! ### The working shading, the segments and the balls at level `m` -/

open scoped Classical in
/-- The level-`m` working shading of `i`: on each piece, the truncation inside its own fibre. -/
noncomputable def Yg (m : ℕ) (i : cfg.ι) : Set E3 :=
  ⋃ B ∈ cd.bs, cd.trunc B ((cd.net B).assign i) m i

open scoped Classical in
theorem Yg_subset_shade (m : ℕ) (i : cfg.ι) : cd.Yg m i ⊆ (cfg.T i).shade := by
  intro x hx
  obtain ⟨B, -, hxB⟩ := Set.mem_iUnion₂.1 hx
  exact cd.S_subset_shade B i (cd.trunc_subset_S B _ m i hxB)

open scoped Classical in
theorem measurableSet_Yg (m : ℕ) (i : cfg.ι) : MeasurableSet (cd.Yg m i) :=
  Finset.measurableSet_biUnion _ fun B _ => cd.measurableSet_trunc B _ m i

open scoped Classical in
/-- On a piece the working shading is the truncation there. -/
theorem Yg_inter_P {B : bι} (hB : B ∈ cd.bs) (m : ℕ) (i : cfg.ι) :
    cd.Yg m i ∩ cd.P B = cd.trunc B ((cd.net B).assign i) m i := by
  ext x
  constructor
  · rintro ⟨hx, hxP⟩
    obtain ⟨B', hB', hxB'⟩ := Set.mem_iUnion₂.1 hx
    have hxP' : x ∈ cd.P B' := cd.trunc_subset_P B' _ m i hxB'
    have hBB : B' = B := by
      by_contra hne
      exact Set.disjoint_left.1 (cd.Pdisj hB' hB hne) hxP' hxP
    subst hBB
    exact hxB'
  · intro hx
    exact ⟨Set.mem_iUnion₂.2 ⟨B, hB, hx⟩, cd.trunc_subset_P B _ m i hx⟩

open scoped Classical in
/-- The segments of level `m` on the ball `B`: the net points with a nonempty level-`m` bin. -/
noncomputable def segs (m : ℕ) (B : bι) : Finset (cfg.ι × bι) :=
  ((cd.net B).net.filter fun ν => (cd.bin B ν m).Nonempty).image fun ν => (ν, B)

open scoped Classical in
theorem mem_segs {m : ℕ} {B : bι} {p : cfg.ι × bι} :
    p ∈ cd.segs m B ↔ ∃ ν ∈ (cd.net B).net, (cd.bin B ν m).Nonempty ∧ (ν, B) = p := by
  simp only [segs, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨ν, ⟨hν, hne⟩, rfl⟩; exact ⟨ν, hν, hne, rfl⟩
  · rintro ⟨ν, hν, hne, rfl⟩; exact ⟨ν, ⟨hν, hne⟩, rfl⟩

open scoped Classical in
theorem mem_segs_self {m : ℕ} {B : bι} {ν : cfg.ι} (hν : ν ∈ (cd.net B).net)
    (hne : (cd.bin B ν m).Nonempty) : (ν, B) ∈ cd.segs m B :=
  cd.mem_segs.2 ⟨ν, hν, hne, rfl⟩

open scoped Classical in
theorem card_segs_le (m : ℕ) (B : bι) : (cd.segs m B).card ≤ cfg.s.card :=
  Finset.card_image_le.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans
    ((Finset.card_le_card (cd.net B).net_subset).trans (cd.card_idx_le B)))

open scoped Classical in
/-- The balls carrying a level-`m` segment. -/
noncomputable def bs' (m : ℕ) : Finset bι := cd.bs.filter fun B => (cd.segs m B).Nonempty

open scoped Classical in
theorem mem_bs' {m : ℕ} {B : bι} : B ∈ cd.bs' m ↔ B ∈ cd.bs ∧ (cd.segs m B).Nonempty := by
  simp [bs']

open scoped Classical in
theorem bs'_subset (m : ℕ) : cd.bs' m ⊆ cd.bs := Finset.filter_subset _ _

open scoped Classical in
/-- The working shading lives on the pieces of the level's balls. -/
theorem Yg_subset_biUnion_P (m : ℕ) (i : cfg.ι) :
    cd.Yg m i ⊆ ⋃ B ∈ cd.bs' m, cd.P B := by
  intro x hx
  obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.1 hx
  have hne : (cd.trunc B ((cd.net B).assign i) m i).Nonempty := ⟨x, hxB⟩
  have hiF : i ∈ cd.fib B ((cd.net B).assign i) := by
    by_contra h
    rw [cd.trunc_eq_empty_of_not_mem m h] at hne
    exact Set.not_nonempty_empty hne
  have hν : (cd.net B).assign i ∈ (cd.net B).net := cd.net_mem_of_mem_fib hiF
  have hbin : (cd.bin B ((cd.net B).assign i) m).Nonempty :=
    ⟨x, cd.trunc_subset_bin B _ m i hxB⟩
  refine Set.mem_iUnion₂.2 ⟨B, cd.mem_bs'.2 ⟨hB, ⟨_, cd.mem_segs_self hν hbin⟩⟩, ?_⟩
  exact cd.trunc_subset_P B _ m i hxB

open scoped Classical in
/-- The shaded body of a segment: the capsule, shaded by the level-`m` bin (inside the capsule). -/
noncomputable def Y (m : ℕ) (p : cfg.ι × bι) : ShadedBody E3 where
  toConvexSpaceBody := capsuleAtBody (cfg.T p.1).toTube (cd.ctr p.2) (capρ cfg) (capL_nonneg cfg)
  shade := cd.bin p.2 p.1 m ∩ cd.caps p.2 p.1
  measurableSet_shade :=
    (cd.measurableSet_bin _ _ _).inter (isClosed_segCarrierSet _ _ _).measurableSet
  shade_subset := Set.inter_subset_right

open scoped Classical in
@[simp] theorem Y_carrier (m : ℕ) (p : cfg.ι × bι) : (cd.Y m p).carrier = cd.caps p.2 p.1 := rfl

open scoped Classical in
@[simp] theorem Y_shade (m : ℕ) (p : cfg.ι × bι) :
    (cd.Y m p).shade = cd.bin p.2 p.1 m ∩ cd.caps p.2 p.1 := rfl

open scoped Classical in
theorem Y_shade_eq_bin {m : ℕ} (hm : 0 < m) {B : bι} (hB : B ∈ cd.bs) (ν : cfg.ι) :
    (cd.Y m (ν, B)).shade = cd.bin B ν m := by
  rw [Y_shade]
  exact Set.inter_eq_left.2 (cd.bin_subset_caps hB hm)

end CoverData

end Kakeya.VeryNotSticky

/-! ### Thickness, dimensions, core lines and localisation of the capsules -/

namespace Kakeya.VeryNotSticky

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Weakening the constant of a thickness profile (a nonnegative profile). -/
theorem hasThicknesses_of_const_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {A : Set E} {C C' : NNReal} {t : Fin n → ℝ} (hC : 0 < C) (hCC' : C ≤ C')
    (ht : ∀ k, 0 ≤ t k) (h : Kakeya.HasThicknesses A C t) : Kakeya.HasThicknesses A C' t := by
  intro k
  obtain ⟨h1, h2⟩ := h k
  have hCR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hCC'R : (C : ℝ) ≤ (C' : ℝ) := by exact_mod_cast hCC'
  exact ⟨le_trans (mul_le_mul_of_nonneg_right (inv_anti₀ hCR hCC'R) (ht k)) h1,
    le_trans h2 (mul_le_mul_of_nonneg_right hCC'R (ht k))⟩

namespace CoverData

variable {cfg : VeryNotSticky.{u}} {bι : Type u} (cd : CoverData cfg bι)

theorem capρ_le_capL (cd : CoverData cfg bι) : ((capρ cfg : NNReal) : ℝ) ≤ capL cfg := by
  rw [coe_capρ]; unfold capL; have := cd.δ_le; linarith

theorem δ_le_capρ (cfg : VeryNotSticky.{u}) : (cfg.δ : ℝ) ≤ ((capρ cfg : NNReal) : ℝ) := by
  rw [coe_capρ]; have := (cfg.δ).coe_nonneg; linarith

/-- The capsules of a ball have the `(r₁, δ, δ)` thickness profile at any `C₀ ≥ 8`. -/
theorem hasThicknesses_caps {C₀ : NNReal} (hC₀ : 8 ≤ C₀) (B : bι) (ν : cfg.ι) :
    Kakeya.HasThicknesses (cd.caps B ν) C₀ ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] := by
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  have hr0 : (0 : ℝ) ≤ (cfg.r₁ : ℝ) := (cfg.r₁).coe_nonneg
  have h4 := hasThicknesses_capsuleAt (cfg.T ν).toTube (cd.ctr B) (capρ cfg) (capL_nonneg cfg)
    (two_mul_capL_le_one cfg) cd.capρ_le_capL
  have h8 := h4.of_profile_le (t' := ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)]) (K₁ := 2)
    (by norm_num) (by norm_num) (by
      intro k
      have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
      rcases hk with rfl | rfl | rfl
      · simp only [Matrix.cons_val_zero]
        unfold capL
        constructor <;> push_cast <;> linarith
      · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [coe_capρ]
        constructor <;> push_cast <;> linarith
      · simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        rw [coe_capρ]
        constructor <;> push_cast <;> linarith)
  refine hasThicknesses_of_const_le (by norm_num)
    (le_of_eq_of_le (by norm_num : (4 : NNReal) * 2 = 8) hC₀) ?_ h8
  intro k
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl <;> simp [hr0, hδ0]

/-- Two capsules of a ball have comparable thickness profiles. -/
theorem thickness_caps_le_two_nsmul (B : bι) (ν μ : cfg.ι) :
    Metric.thickness ℝ (cd.caps B ν) ≤ 2 • Metric.thickness ℝ (cd.caps B μ) :=
  thickness_segCarrierSet_le_two_nsmul (centredTube (cfg.T ν).toTube (cd.ctr B) (capρ cfg))
    (centredTube (cfg.T μ).toTube (cd.ctr B) (capρ cfg)) (cd.ctr B) (cd.ctr B) (capL_nonneg cfg)
    (two_mul_capL_le_one cfg) cd.capρ_le_capL

open scoped Classical in
/-- The capsule of a net point lies along the core line of every tube of its fibre, at `3δ`. -/
theorem caps_subset_cthickening_line {B : bι} {i ν : cfg.ι} (hi : i ∈ cd.fib B ν) {C : ℝ}
    (hC : 3 * (cfg.δ : ℝ) ≤ C) :
    cd.caps B ν ⊆ cthickening C
      (AffineSubspace.mk' (foot (cfg.T i).toTube (cd.ctr B))
        (Submodule.span ℝ {(cfg.T i).toTube.direction}) : Set E3) :=
  (cd.net B).capsuleAt_subset_cthickening_line_of_mem_fibre hi (capL_nonneg cfg)
    (capL_le_half cfg) (by rw [coe_capρ]; linarith)

/-- The capsule of a net point of `B` lies in the closed ball of radius `5r₁/8` about `ctr B`. -/
theorem caps_subset_closedBall {B : bι} (hB : B ∈ cd.bs) {ν : cfg.ι} (hν : ν ∈ cd.idx B) {R : ℝ}
    (hR : 5 * (cfg.r₁ : ℝ) / 8 ≤ R) : cd.caps B ν ⊆ closedBall (cd.ctr B) R := by
  refine capsuleAt_subset_closedBall (cfg.T ν).toTube (cd.ctr B) (capρ cfg) (capL_nonneg cfg)
    (capL_le_half cfg) ?_
  have h1 := norm_foot_sub_le_of_meets _ _ (cd.meets_of_mem_idx hB hν)
  have h2 := cd.δr
  rw [coe_capρ]
  unfold capL
  linarith

theorem net_subset_idx (B : bι) : (cd.net B).net ⊆ cd.idx B := (cd.net B).net_subset

/-! ### The core -/

open scoped Classical in
/-- **The canonical-capsule `BallDataCore` of a cover at the dyadic level `m`** (refined
`propvnslocalization`, l.3700–3724, l.5354–5473; map row C7-b).  The two non-local inputs — the
level has a ball, and the level-`m` working shading keeps `Cg⁻¹` of the mass — are hypotheses;
`CanonicalCapsulesMass.lean` supplies them by the two-constraint level selection. -/
noncomputable def capsuleCore (m : ℕ) (hm : 0 < m) (hne : (cd.bs' m).Nonempty)
    {C₀ : NNReal} (hC₀ : 16 ≤ C₀) {D : ℕ} (hD : ballCoverConstant ≤ D)
    (Cg : NNReal) (hCg : 1 ≤ Cg)
    (hYg : (Cg : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (cfg.T i).shade ≤
      ∑ i ∈ cfg.s, volume (cd.Yg m i)) :
    BallDataCore cfg where
  C₀ := C₀
  hC₀ := le_trans (by norm_num) hC₀
  D := D
  Yg := cd.Yg m
  Yg_subset := fun i _ => cd.Yg_subset_shade m i
  Yg_measurable := fun i _ => cd.measurableSet_Yg m i
  Cg := Cg
  hCg := hCg
  Yg_mass := hYg
  bι := bι
  σ := cfg.ι × bι
  bs := cd.bs' m
  bs_nonempty := hne
  ctr := cd.ctr
  P := cd.P
  P_subset_ball := fun B hB => cd.Pball B (cd.bs'_subset m hB)
  P_disjoint := cd.Pdisj.subset (by exact_mod_cast cd.bs'_subset m)
  P_measurable := fun B _ => cd.Pmeas B
  P_cover := fun i _ => cd.Yg_subset_biUnion_P m i
  ballOverlap := fun x t hts hball =>
    le_trans (cd.overlap x t (hts.trans (cd.bs'_subset m)) hball) hD
  segs := cd.segs m
  Y := cd.Y m
  fam := fun p => cd.fib p.2 p.1
  segs_nonempty := fun B hB => (cd.mem_bs'.1 hB).2
  fam_subset := fun B _ p _ => cd.fib_subset_s p.2 p.1
  fam_disjoint := by
    intro B hB p hp q hq hpq
    rw [Finset.mem_coe] at hp hq
    obtain ⟨ν, hν, -, rfl⟩ := cd.mem_segs.1 hp
    obtain ⟨μ, hμ, -, rfl⟩ := cd.mem_segs.1 hq
    have hνμ : ν ≠ μ := fun h => hpq (by rw [h])
    exact cd.fib_disjoint hν hμ hνμ
  Y_piece := by
    intro B hB p hp x hx
    obtain ⟨ν, -, -, rfl⟩ := cd.mem_segs.1 hp
    exact cd.bin_subset_P B ν m hx.1
  segs_thickness := by
    intro B hB p hp
    obtain ⟨ν, -, -, rfl⟩ := cd.mem_segs.1 hp
    exact cd.hasThicknesses_caps (le_trans (by norm_num) hC₀) B ν
  segs_dims := by
    intro B hB p hp q hq
    obtain ⟨ν, -, -, rfl⟩ := cd.mem_segs.1 hp
    obtain ⟨μ, -, -, rfl⟩ := cd.mem_segs.1 hq
    exact cd.thickness_caps_le_two_nsmul B ν μ
  parent := by
    intro B hB i hi hne'
    have hB' : B ∈ cd.bs := cd.bs'_subset m hB
    rw [cd.Yg_inter_P hB' m i] at hne'
    have hiF : i ∈ cd.fib B ((cd.net B).assign i) := by
      by_contra h
      rw [cd.trunc_eq_empty_of_not_mem m h] at hne'
      exact Set.not_nonempty_empty hne'
    have hν : (cd.net B).assign i ∈ (cd.net B).net := cd.net_mem_of_mem_fib hiF
    obtain ⟨x, hx⟩ := hne'
    exact ⟨((cd.net B).assign i, B),
      cd.mem_segs_self hν ⟨x, cd.trunc_subset_bin B _ m i hx⟩, hiF⟩
  into := by
    intro B hB p hp i hi
    obtain ⟨ν, hν, -, rfl⟩ := cd.mem_segs.1 hp
    have hB' : B ∈ cd.bs := cd.bs'_subset m hB
    have hassign : (cd.net B).assign i = ν := (cd.mem_fib_iff.1 hi).2
    rw [cd.Yg_inter_P hB' m i, hassign, Y_shade]
    exact Set.subset_inter (cd.trunc_subset_bin B ν m i)
      ((cd.trunc_subset_S B ν m i).trans (cd.S_subset_caps hB' hi))
  back := by
    intro B hB p hp x hx
    obtain ⟨ν, hν, -, rfl⟩ := cd.mem_segs.1 hp
    have hB' : B ∈ cd.bs := cd.bs'_subset m hB
    obtain ⟨i, hi, hxi⟩ := cd.exists_mem_trunc_of_mem_bin hm hx.1
    have hassign : (cd.net B).assign i = ν := (cd.mem_fib_iff.1 hi).2
    refine Set.mem_biUnion hi ?_
    refine Set.mem_iUnion₂.2 ⟨B, hB', ?_⟩
    rw [hassign]; exact hxi
  segs_core := by
    intro B hB p hp i hi
    obtain ⟨ν, -, -, rfl⟩ := cd.mem_segs.1 hp
    have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
    have hC₀R : (16 : ℝ) ≤ ((C₀ : NNReal) : ℝ) := by exact_mod_cast hC₀
    refine ⟨foot (cfg.T i).toTube (cd.ctr B), ?_⟩
    exact cd.caps_subset_cthickening_line hi (by nlinarith)
  m := (m : NNReal)
  Cm := 1
  hCm := le_rfl
  fibre := by
    intro B hB p hp x hx
    obtain ⟨ν, hν, -, rfl⟩ := cd.mem_segs.1 hp
    have hB' : B ∈ cd.bs := cd.bs'_subset m hB
    have hxbin : x ∈ cd.bin B ν m := hx.1
    have hxP : x ∈ cd.P B := cd.bin_subset_P B ν m hxbin
    letI := indexOrder cfg
    have hfilt : (cd.fib B ν).filter (fun i => x ∈ cd.Yg m i) =
        (cd.fib B ν).filter (fun i => x ∈ truncated (cd.fib B ν) (cd.S B) (cd.P B) m i) := by
      refine Finset.filter_congr ?_
      intro i hi
      have hassign : (cd.net B).assign i = ν := (cd.mem_fib_iff.1 hi).2
      have h1 : x ∈ cd.Yg m i ↔ x ∈ cd.Yg m i ∩ cd.P B := by
        constructor
        · exact fun h => ⟨h, hxP⟩
        · exact fun h => h.1
      rw [h1, cd.Yg_inter_P hB' m i, hassign]
      rfl
    rw [hfilt, card_filter_truncated (cd.fib B ν) (cd.S B) (cd.P B) m hxbin]
    simp
  γ := (exists_deltaCovers cfg.hδ (cd.Y m)).choose
  cov := (exists_deltaCovers cfg.hδ (cd.Y m)).choose_spec.choose
  covCtr := (exists_deltaCovers cfg.hδ (cd.Y m)).choose_spec.choose_spec.choose
  cov_isCover := fun _ _ p _ =>
    ⟨((exists_deltaCovers cfg.hδ (cd.Y m)).choose_spec.choose_spec.choose_spec.1 p).subset_iUnion,
      fun x => le_trans (((exists_deltaCovers cfg.hδ
        (cd.Y m)).choose_spec.choose_spec.choose_spec.1 p).card_filter_le x) hD⟩
  cov_meets := fun _ _ p _ =>
    (exists_deltaCovers cfg.hδ (cd.Y m)).choose_spec.choose_spec.choose_spec.2 p
  segs_subset_ball := by
    intro B hB p hp
    obtain ⟨ν, hν, -, rfl⟩ := cd.mem_segs.1 hp
    have hr0 : (0 : ℝ) ≤ (cfg.r₁ : ℝ) := (cfg.r₁).coe_nonneg
    exact cd.caps_subset_closedBall (cd.bs'_subset m hB) (cd.net_subset_idx B hν) (by linarith)
  segs_scale := by
    intro B hB p hp
    obtain ⟨ν, -, -, rfl⟩ := cd.mem_segs.1 hp
    refine le_trans ?_ (le_ethickness_scale_capsuleAt (cfg.T ν).toTube (cd.ctr B) (capρ cfg)
      (capL_nonneg cfg))
    exact_mod_cast δ_le_capρ cfg

end CoverData

end Kakeya.VeryNotSticky
