/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallTierCore

/-!
# Restricting a `BallDataCore` to a subfamily of its balls

General-branch steps **G4b**. GWZ §9.3 deletes balls twice — the heavy-ball (fullness) cut of `gwz.txt`
l.2029–2030 and the dimensions pigeonhole of l.2039–2041 — and both deletions must be
performed *on the `BallDataCore`*, not merely on an abstract ball index set, because
`Kakeya.VeryNotSticky.BallDataCore.toBallData` reads every (C4) clause on `core.bs` while the
producers of those clauses (`Kakeya.VeryNotSticky.exists_dimsClass_heavy`) deliver them only on
a subset `bs' ⊆ core.bs`.

## Why this file exists and `tierCore` cannot do its work

`Kakeya.VeryNotSticky.tierCore` refines the *segments* and **copies the ball set**
(`Kakeya.VeryNotSticky.tierCore_bs : (tierCore …).bs = core.bs`); its `hne` binder
(`∀ B ∈ core.bs, (tier B).Nonempty`) in fact *forbids* emptying a ball's tier, so it cannot be
repurposed as a ball deletion. This file supplies the missing operation.

## The construction

`Kakeya.VeryNotSticky.BallDataCore.restrictBalls` takes `bs' ⊆ core.bs`, its non-emptiness, and
a **retention factor** `K` with

  `K⁻¹ ∑_{T ∈ 𝕋} |Y_g(T)| ≤ ∑_{T ∈ 𝕋} |Y_g(T) ∩ ⋃_{B ∈ bs'} B̂|`,

and returns a `BallDataCore` with `bs := bs'` and the working shading

  `Y_g'(T) = Y_g(T) ∩ ⋃_{B ∈ bs'} B̂`  (`Kakeya.VeryNotSticky.restrictYg`),

at the **explicit** loss `Cg' = Cg · K`. There is no `Cm` factor: unlike the tier, this
refinement does not change the segments and so never passes through
`Kakeya.ThinCase.lift`; the fibre count is unchanged because on the shading of a segment of a
*retained* ball the two fibres are literally the same `Finset`
(`Kakeya.VeryNotSticky.restrictYg_fibre_filter_eq`, the device of `BallTierCore` §4.1).

Everything except `P_cover`, `back`, `fibre` and `Yg_mass` is inherited by restriction along
`bs' ⊆ core.bs`. The four that are not:

* `P_cover` becomes trivial — the new shading is by construction inside `⋃_{B ∈ bs'} B̂`;
* `back` needs the retained ball's own piece: for `p ∈ segs B` with `B ∈ bs'`, `Y_B(p) ⊆ B̂`
  (`Y_piece`) already puts the shade in `⋃_{B ∈ bs'} B̂`, so intersecting `Y_g` with that union
  loses nothing on `Y_B(p)`;
* `fibre` is the filter identity above;
* `Yg_mass` is the input `hret` composed with `core.Yg_mass`.

## The retention is a mass identity, not an estimate

`Kakeya.VeryNotSticky.ballYgMass core B = ∑_{T ∈ 𝕋} |Y_g(T) ∩ B̂|` is the per-ball working mass.
Because the pieces are pairwise disjoint and measurable and cover `Y_g`,

  `∑_{T} |Y_g'(T)| = ∑_{B ∈ bs'} ballYgMass core B`   and
  `∑_{T} |Y_g(T)| = ∑_{B ∈ 𝔅} ballYgMass core B`

(`Kakeya.VeryNotSticky.sum_volume_restrictYg_eq_sum_ballYgMass`,
`Kakeya.VeryNotSticky.sum_volume_Yg_eq_sum_ballYgMass`), so
`Kakeya.VeryNotSticky.restrictYg_mass_of_retention` converts a retention stated on the *ball*
mass functional — which is the shape `Kakeya.VeryNotSticky.exists_dimsClass_heavy` and
`Kakeya.VeryNotSticky.exists_heavyBalls_at` deliver — into the `hret` binder verbatim. This is
the bridge G5 consumes; without it the pigeonhole's `∑ B ∈ bs', Sm B` output does not meet the
structure's `∑ i ∈ cfg.s` input.

Nothing here changes a existing statement.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

universe u

namespace Kakeya.VeryNotSticky

section RestrictBalls

variable {cfg : VeryNotSticky.{u}}

/-- The working shading a **restricted ball family** carries: the old working shading cut down
to the union of the retained pieces. -/
noncomputable def restrictYg (core : BallDataCore cfg) (bs' : Finset core.bι) (i : cfg.ι) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  core.Yg i ∩ ⋃ B ∈ bs', core.P B

/-- The per-ball working mass `∑_{T ∈ 𝕋} |Y_g(T) ∩ B̂|`: the functional the two ball deletions
of GWZ §9.3 retain. -/
noncomputable def ballYgMass (core : BallDataCore cfg) (B : core.bι) : ENNReal :=
  ∑ i ∈ cfg.s, volume (core.Yg i ∩ core.P B)

variable (core : BallDataCore cfg) (bs' : Finset core.bι)

theorem restrictYg_subset (i : cfg.ι) : restrictYg core bs' i ⊆ core.Yg i :=
  Set.inter_subset_left

theorem restrictYg_subset_biUnion (i : cfg.ι) :
    restrictYg core bs' i ⊆ ⋃ B ∈ bs', core.P B := Set.inter_subset_right

/-- The restricted shading, written termwise over the retained balls. -/
theorem restrictYg_eq_biUnion (i : cfg.ι) :
    restrictYg core bs' i = ⋃ B ∈ bs', (core.Yg i ∩ core.P B) := by
  rw [restrictYg, Set.inter_iUnion₂]

theorem measurableSet_restrictYg (hsub : bs' ⊆ core.bs) {i : cfg.ι} (hi : i ∈ cfg.s) :
    MeasurableSet (restrictYg core bs' i) :=
  (core.Yg_measurable i hi).inter
    (Finset.measurableSet_biUnion _ fun B hB => core.P_measurable B (hsub hB))

/-- The retained pieces are pairwise disjoint. -/
theorem restrict_P_disjoint (hsub : bs' ⊆ core.bs) : (bs' : Set core.bι).PairwiseDisjoint core.P :=
  core.P_disjoint.subset (Finset.coe_subset.2 hsub)

/-- **The mass of the restricted shading of one tube is the sum of its pieces' masses.** -/
theorem volume_restrictYg (hsub : bs' ⊆ core.bs) {i : cfg.ι} (hi : i ∈ cfg.s) :
    volume (restrictYg core bs' i) = ∑ B ∈ bs', volume (core.Yg i ∩ core.P B) := by
  rw [restrictYg_eq_biUnion]
  refine measure_biUnion_finset ?_ ?_
  · exact (restrict_P_disjoint core bs' hsub).mono fun B => Set.inter_subset_right
  · exact fun B hB => (core.Yg_measurable i hi).inter (core.P_measurable B (hsub hB))

/-- **The restricted mass is the ball mass functional summed over the retained balls.** -/
theorem sum_volume_restrictYg_eq_sum_ballYgMass (hsub : bs' ⊆ core.bs) :
    ∑ i ∈ cfg.s, volume (restrictYg core bs' i) = ∑ B ∈ bs', ballYgMass core B := by
  rw [Finset.sum_congr rfl fun i hi => volume_restrictYg core bs' hsub hi]
  exact Finset.sum_comm

/-- **The total working mass is the ball mass functional summed over all the balls.** This is
where `P_cover` pays for itself: the pieces cover `Y_g`, so nothing is lost. -/
theorem sum_volume_Yg_eq_sum_ballYgMass :
    ∑ i ∈ cfg.s, volume (core.Yg i) = ∑ B ∈ core.bs, ballYgMass core B := by
  have h : ∀ i ∈ cfg.s, restrictYg core core.bs i = core.Yg i := fun i hi =>
    Set.inter_eq_self_of_subset_left (core.P_cover i hi)
  calc ∑ i ∈ cfg.s, volume (core.Yg i)
      = ∑ i ∈ cfg.s, volume (restrictYg core core.bs i) :=
        Finset.sum_congr rfl fun i hi => by rw [h i hi]
    _ = ∑ B ∈ core.bs, ballYgMass core B :=
        sum_volume_restrictYg_eq_sum_ballYgMass core core.bs Finset.Subset.rfl

/-- **The bridge from the ball-mass retention to the `hret` binder of
`Kakeya.VeryNotSticky.BallDataCore.restrictBalls`.** The two ball deletions of GWZ §9.3
(`Kakeya.VeryNotSticky.exists_heavyBalls_at`, `Kakeya.VeryNotSticky.exists_dimsClass_heavy`)
retain a `K⁻¹` fraction of an abstract per-ball mass functional; read at
`Kakeya.VeryNotSticky.ballYgMass` that is exactly the retention of the working shading. -/
theorem restrictYg_mass_of_retention (hsub : bs' ⊆ core.bs) {K : NNReal}
    (hret : (K : ENNReal)⁻¹ * ∑ B ∈ core.bs, ballYgMass core B ≤
      ∑ B ∈ bs', ballYgMass core B) :
    (K : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (core.Yg i) ≤
      ∑ i ∈ cfg.s, volume (restrictYg core bs' i) := by
  rw [sum_volume_Yg_eq_sum_ballYgMass core,
    sum_volume_restrictYg_eq_sum_ballYgMass core bs' hsub]
  exact hret

/-- (C2) `P_cover` for the restricted shading: trivial by construction. -/
theorem restrictYg_cover (i : cfg.ι) : restrictYg core bs' i ⊆ ⋃ B ∈ bs', core.P B :=
  Set.inter_subset_right

/-- (C5) `parent` for the restricted shading. -/
theorem restrictYg_parent (hsub : bs' ⊆ core.bs) {B : core.bι} (hB : B ∈ bs') (i : cfg.ι)
    (hi : i ∈ cfg.s) (hne : (restrictYg core bs' i ∩ core.P B).Nonempty) :
    ∃ p ∈ core.segs B, i ∈ core.fam p :=
  core.parent B (hsub hB) i hi
    (hne.mono (Set.inter_subset_inter_left (core.P B) (restrictYg_subset core bs' i)))

/-- (C5) `into` for the restricted shading: monotone in the shading. -/
theorem restrictYg_into (hsub : bs' ⊆ core.bs) {B : core.bι} (hB : B ∈ bs') {p : core.σ}
    (hp : p ∈ core.segs B) {i : cfg.ι} (hip : i ∈ core.fam p) :
    restrictYg core bs' i ∩ core.P B ⊆ (core.Y p).shade :=
  (Set.inter_subset_inter_left (core.P B) (restrictYg_subset core bs' i)).trans
    (core.into B (hsub hB) p hp i hip)

/-- (C5) `back` for the restricted shading. The shade of a segment of a **retained** ball lies
in that ball's piece, hence in the union of the retained pieces, so the cut loses nothing. -/
theorem restrictYg_back (hsub : bs' ⊆ core.bs) {B : core.bι} (hB : B ∈ bs') {p : core.σ}
    (hp : p ∈ core.segs B) : (core.Y p).shade ⊆ ⋃ i ∈ core.fam p, restrictYg core bs' i := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (core.back B (hsub hB) p hp hx)
  exact Set.mem_iUnion₂.2
    ⟨i, hi, hxi, Set.mem_biUnion hB (core.Y_piece B (hsub hB) p hp hx)⟩

open scoped Classical in
/-- On the shade of a segment of a retained ball the fibre of the restricted shading **is** the
fibre of the original working shading — the same `Finset`, so the fibre count is unchanged in
both directions and no `Cm` is spent. -/
theorem restrictYg_fibre_filter_eq (hsub : bs' ⊆ core.bs) {B : core.bι} (hB : B ∈ bs')
    {p : core.σ} (hp : p ∈ core.segs B) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ (core.Y p).shade) :
    {i ∈ core.fam p | x ∈ restrictYg core bs' i} = {i ∈ core.fam p | x ∈ core.Yg i} := by
  classical
  refine Finset.filter_congr fun i _ => ?_
  constructor
  · intro hxi; exact restrictYg_subset core bs' i hxi
  · intro hxi
    exact ⟨hxi, Set.mem_biUnion hB (core.Y_piece B (hsub hB) p hp hx)⟩

open scoped Classical in
/-- (C5) `fibre` for the restricted shading, at the core's own `m` and `Cm`. -/
theorem restrictYg_fibre (hsub : bs' ⊆ core.bs) {B : core.bι} (hB : B ∈ bs') {p : core.σ}
    (hp : p ∈ core.segs B) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ (core.Y p).shade) :
    (core.m : ENNReal) ≤ core.Cm * {i ∈ core.fam p | x ∈ restrictYg core bs' i}.card ∧
      (({i ∈ core.fam p | x ∈ restrictYg core bs' i}.card : ℕ) : ENNReal) ≤
        core.Cm * core.m := by
  classical
  rw [restrictYg_fibre_filter_eq core bs' hsub hB hp hx]
  exact core.fibre B (hsub hB) p hp x hx

open scoped Classical in
/-- **The restricted core.** A `BallDataCore` restricted to a subfamily `bs' ⊆ 𝔅` of its balls,
with the working shading cut down to the union of the retained pieces. Only the subfamily's own
data — the inclusion, its non-emptiness, and the working-mass retention factor `K` — is taken
as input; all forty-two fields, in particular `P_cover`, `back`, `fibre` and `Yg_mass`, are
re-established. The loss of the working shading is the **explicit** `Cg' = Cg · K`, with **no**
`Cm` factor (the segments are untouched, so `Kakeya.ThinCase.lift` is never invoked). -/
noncomputable def BallDataCore.restrictBalls (core : BallDataCore cfg) (bs' : Finset core.bι)
    (hsub : bs' ⊆ core.bs) (hne : bs'.Nonempty) {K : NNReal} (hK : 1 ≤ K)
    (hret : (K : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (core.Yg i) ≤
      ∑ i ∈ cfg.s, volume (restrictYg core bs' i)) :
    BallDataCore cfg where
  C₀ := core.C₀
  hC₀ := core.hC₀
  D := core.D
  Yg := restrictYg core bs'
  Yg_subset := fun i hi => (restrictYg_subset core bs' i).trans (core.Yg_subset i hi)
  Yg_measurable := fun i hi => measurableSet_restrictYg core bs' hsub hi
  Cg := core.Cg * K
  hCg := by
    calc (1 : NNReal) = 1 * 1 := by norm_num
      _ ≤ core.Cg * K := mul_le_mul' core.hCg hK
  Yg_mass := by
    have hCg0 : (core.Cg : ENNReal) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one core.hCg))
    have hCgtop : (core.Cg : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hsplit : ((core.Cg * K : NNReal) : ENNReal)⁻¹ =
        ((K : NNReal) : ENNReal)⁻¹ * ((core.Cg : ENNReal))⁻¹ := by
      have hmul : ((core.Cg * K : NNReal) : ENNReal) =
          (core.Cg : ENNReal) * ((K : NNReal) : ENNReal) := by push_cast; ring
      rw [hmul, ENNReal.mul_inv (Or.inl hCg0) (Or.inl hCgtop), mul_comm]
    rw [hsplit, mul_assoc]
    exact le_trans (mul_le_mul_of_nonneg_left core.Yg_mass zero_le) hret
  bι := core.bι
  σ := core.σ
  bs := bs'
  bs_nonempty := hne
  ctr := core.ctr
  P := core.P
  P_subset_ball := fun B hB => core.P_subset_ball B (hsub hB)
  P_disjoint := restrict_P_disjoint core bs' hsub
  P_measurable := fun B hB => core.P_measurable B (hsub hB)
  P_cover := fun i _ => restrictYg_cover core bs' i
  ballOverlap := fun x t ht hmem => core.ballOverlap x t (ht.trans hsub) hmem
  segs := core.segs
  Y := core.Y
  fam := core.fam
  segs_nonempty := fun B hB => core.segs_nonempty B (hsub hB)
  fam_subset := fun B hB => core.fam_subset B (hsub hB)
  fam_disjoint := fun B hB => core.fam_disjoint B (hsub hB)
  Y_piece := fun B hB => core.Y_piece B (hsub hB)
  segs_thickness := fun B hB => core.segs_thickness B (hsub hB)
  segs_dims := fun B hB => core.segs_dims B (hsub hB)
  parent := fun B hB i hi hnee => restrictYg_parent core bs' hsub hB i hi hnee
  into := fun B hB p hp i hip =>
    (Set.inter_subset_inter_left (core.P B) (restrictYg_subset core bs' i)).trans
      (core.into B (hsub hB) p hp i hip)
  back := fun B hB p hp => restrictYg_back core bs' hsub hB hp
  segs_core := fun B hB => core.segs_core B (hsub hB)
  m := core.m
  Cm := core.Cm
  hCm := core.hCm
  fibre := fun B hB p hp x hx => restrictYg_fibre core bs' hsub hB hp hx
  γ := core.γ
  cov := core.cov
  covCtr := core.covCtr
  cov_isCover := fun B hB => core.cov_isCover B (hsub hB)
  cov_meets := fun B hB => core.cov_meets B (hsub hB)
  segs_subset_ball := fun B hB => core.segs_subset_ball B (hsub hB)
  segs_scale := fun B hB => core.segs_scale B (hsub hB)

section Proj

variable (hsub : bs' ⊆ core.bs) (hne : bs'.Nonempty) {K : NNReal} (hK : 1 ≤ K)
  (hret : (K : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (core.Yg i) ≤
    ∑ i ∈ cfg.s, volume (restrictYg core bs' i))

@[simp] theorem restrictBalls_bs :
    (BallDataCore.restrictBalls core bs' hsub hne hK hret).bs = bs' := rfl
@[simp] theorem restrictBalls_segs :
    (BallDataCore.restrictBalls core bs' hsub hne hK hret).segs = core.segs := rfl
@[simp] theorem restrictBalls_Y :
    (BallDataCore.restrictBalls core bs' hsub hne hK hret).Y = core.Y := rfl
@[simp] theorem restrictBalls_fam :
    (BallDataCore.restrictBalls core bs' hsub hne hK hret).fam = core.fam := rfl
@[simp] theorem restrictBalls_Yg :
    (BallDataCore.restrictBalls core bs' hsub hne hK hret).Yg = restrictYg core bs' := rfl
@[simp] theorem restrictBalls_Cg :
    (BallDataCore.restrictBalls core bs' hsub hne hK hret).Cg = core.Cg * K := rfl
@[simp] theorem restrictBalls_C₀ :
    (BallDataCore.restrictBalls core bs' hsub hne hK hret).C₀ = core.C₀ := rfl
@[simp] theorem restrictBalls_D :
    (BallDataCore.restrictBalls core bs' hsub hne hK hret).D = core.D := rfl
@[simp] theorem restrictBalls_ctr :
    (BallDataCore.restrictBalls core bs' hsub hne hK hret).ctr = core.ctr := rfl
@[simp] theorem restrictBalls_P :
    (BallDataCore.restrictBalls core bs' hsub hne hK hret).P = core.P := rfl
@[simp] theorem restrictBalls_m :
    (BallDataCore.restrictBalls core bs' hsub hne hK hret).m = core.m := rfl
@[simp] theorem restrictBalls_Cm :
    (BallDataCore.restrictBalls core bs' hsub hne hK hret).Cm = core.Cm := rfl

/-- **`segs_dilation` transports to the restricted core**: the segments are untouched and the
ball family is smaller. -/
theorem restrictBalls_segs_dilation {Cdil : NNReal}
    (hdil : ∀ B ∈ core.bs, (cfg.r₁ : ENNReal) ^ 2 *
        maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) ≤
      (Cdil : ENNReal) * maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)) :
    ∀ B ∈ (BallDataCore.restrictBalls core bs' hsub hne hK hret).bs,
      (cfg.r₁ : ENNReal) ^ 2 *
          maxDensity ((BallDataCore.restrictBalls core bs' hsub hne hK hret).segs B)
            (fun p ↦ ((BallDataCore.restrictBalls core bs' hsub hne hK hret).Y p).toConvexSpaceBody)
        ≤ (Cdil : ENNReal) * maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody) :=
  fun B hB => hdil B (hsub hB)

/-- **`segs_density` transports to the restricted core**: it is a per-segment property of a
retained ball. -/
theorem restrictBalls_segs_density {c₁ : NNReal}
    (hdens : ∀ B ∈ core.bs, ∀ p ∈ core.segs B,
      (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier ≤
        volume (core.Y p).shade) :
    ∀ B ∈ (BallDataCore.restrictBalls core bs' hsub hne hK hret).bs,
      ∀ p ∈ (BallDataCore.restrictBalls core bs' hsub hne hK hret).segs B,
        (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) *
            volume ((BallDataCore.restrictBalls core bs' hsub hne hK hret).Y p).carrier ≤
          volume ((BallDataCore.restrictBalls core bs' hsub hne hK hret).Y p).shade :=
  fun B hB => hdens B (hsub hB)

end Proj

end RestrictBalls

end Kakeya.VeryNotSticky
