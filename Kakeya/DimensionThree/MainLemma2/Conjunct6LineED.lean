/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Conjunct6EssDistinct
public import Kakeya.Tube.Nets
public import Kakeya.Mathlib.Analysis.IsSeparated
public import Kakeya.DimensionThree.MainLemma2.CanonicalCentredCover
public import Kakeya.DimensionThree.MainLemma2.Conjunct6OptionETripwire
public import Kakeya.DimensionThree.MainLemma2.SplitInputsProduce
public import Kakeya.DimensionThree.MainLemma2.SplitInputsLoose

/-!
# Conjunct 6 from **line-based** essential distinctness of the levels

## The source

The professor's refined proof
(`260115_kakeyadetailedproofv3_revised_detailed.tex`, source versions `5fc1000a…`) replaces the tree's
*pairwise*, volume-based `Kakeya.IsEssentiallyDistinct` by a *family-level, line-based*
notion (l.153–157, verbatim):

> For a line `L ⊂ ℝⁿ`, write `N_{5δ}(L)` for its closed `5δ`-neighbourhood.  A finite family
> `𝕋` of `δ`-tubes is `A`-**essentially distinct** if
> `#{T ∈ 𝕋 : T ⊂ N_{5δ}(L)} ≤ A` for every line `L ⊂ ℝⁿ`.
> This is deliberately a condition on complete lines rather than on unit segments: axial
> translates of one unit segment have the same line parameters.

and proves the angular count from it (`lem:ml2-angular-count`, l.3462–3493, verbatim):

> Let `(𝕋,Y)` be prepared at the radii `σ_k = δ^{k/M}` with parameters
> `(C_r, A₁, λ₁, Λ_ν)` and multiplicity levels `ν_k`.  If `k < M`, `σ_k ≤ 1/100`, `x ∈ ℝ³`,
> and `v` is a unit vector, then
> `#{T ∈ 𝕋_Y(x) : ∠(dir T, v) ≤ σ_k} ≤ 4·600⁶ A₁ ν_k`.
> *Proof.*  Let `L = x + ℝv`.  If `T ∈ 𝕋_Y(x)` has direction within `σ_k` of `v`, its unit
> core lies in the `(δ+σ_k)`-neighbourhood of `L`.  Since `T ⊂ π_k(T)`, comparison of the two
> unit cores shows `π_k(T) ⊂ N_{6σ_k}(L)`. …  Line-based `A₁`-essential distinctness, applied
> at thickness `6σ_k`, bounds the possible parents by `600⁶ A₁`.  For each such parent `S`,
> preparation gives `m_{𝕋⟨S⟩,Y}(x) < 4ν_k`.  The assigned cells are disjoint, so summing over
> the possible parents proves it.  Notice that this argument counts complete lines rather than
> unit-segment translates; there is no fifth axial parameter.

## What this file does

`Kakeya.VeryNotSticky.Conjunct6EssDistinct` already contains the *asymmetry* the refined proof
uses, compiled:

* `tube_le_dilate_of_mem_angularFibre` — every `σ`-tube **containing** a member of the angular
  cone at `(x, v)` has its direction pinned to `8σ` of one fixed direction `u` (up to sign) and
  passes through `x`;
* `angularFibre_card_le_of_nodeCount` — whatever bounds the number `Q` of level-`k` nodes the
  cone meets bounds the cone at `Q · C² · branchingN k`;
* `angularFibre_card_le_fibreMult_of_essDistinct`, `eventually_conjunct6_of_essDistinct` — the
  assembly of conjunct 6 at `Cang = Q · C₀⁴` with the `δ^{-η}` budget discharged by
  `coe_C₀_pow_four_le_rpow_neg_half_eta`.

The **only** thing this file replaces is the *count* `Q`: the pairwise-ED count
`card_le_essDistinctConstant_of_edFamily` is replaced by the line-based
`card_le_lineEDConstant_of_lineEDFamily`.  That is the keystone, and everything else is the
existing chain re-run against it.

## The constant, derived

The refined proof spends `600⁶` on the `6σ_k`-versus-`5σ_k` thickness gap (its line-ED
condition is stated at `5δ`, but the containment it proves is at `6δ`).  The same gap is paid
here by an explicit `L¹`-box packing in the **line** parameters `(c, d)` — a foot point on the
node's core and its (sign-normalised) direction — and the compiled constant is *smaller*:

* the direction parameter `d j` lies in the ball `B(u, 8σ)` (`tube_le_dilate_of_mem_angularFibre`'s
  own direction estimate, extracted here as `exists_sign_dir_of_mem_angularFibre`);
* the position parameter `c j` lies in the ball `B(x, σ)` (the node contains a cone member, which
  shades `x`, so `x` is within `σ` of the node's core);
* a maximal `σ`-separated subset `S` of `t` in the `L¹` metric on `(c, d)` therefore has
  `#S ≤ ((8σ + σ/4)/(σ/4))^(2·3) = 33⁶` by `Tube.card_le_of_L1_separated_in_box`;
* every `j ∈ t` is `σ`-close to some `w ∈ S` in both parameters, and then
  `carrier_subset_lineNbhd` gives `P j ⊂ N_{3σ}(L_w) ⊆ N_{5σ}(L_w)` for the line `L_w` through
  `c w` in the direction `d w` — so `IsLineEssDistinct A₁` charges at most `A₁` members to each
  `w`.

Hence `Q ≤ 33⁶ · A₁` and

`#angularFibre x v ρ_k ≤ (33⁶ · A₁ · C⁴) · multiplicity (tubeFibre k j)`,
`33⁶ = 1291467969 < 4·600⁶`.

Every `⪅` of the source is rendered at this explicit absolute constant ; no
constant is `1`.

## Provenance of `IsLineEssDistinct`

Row **E0** of the map assigns `IsLineEssDistinct`/`edDegree` to a separate owner
(`MainLemma2/LineEssDistinct.lean`). If E0
lands first, delete the `def` block below (and `lineSet`/`lineNbhd`) and import E0's file; no
proof in this file reads the definition except through `IsLineEssDistinct` and
`carrier_subset_lineNbhd`.

**Nothing here changes, weakens or restates any existing declaration**: every statement below is
new, and no protected or pinned text is touched.  `SetupSideData.lean`, the general boundary and
the uniformiser are untouched — this is the consumer-side theorem only.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

open scoped NNReal ENNReal

namespace Kakeya

namespace VeryNotSticky

universe u

/-! ### The line-based essential-distinctness notion (refined l.153–157) -/

section LineED

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

open scoped Classical in
omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Line-based essential distinctness passes to subfamilies. -/
theorem IsLineEssDistinct.mono {A : ℕ} {ι : Type*} {δ : NNReal} {s t : Finset ι}
    {T : ι → Tube δ E} (h : IsLineEssDistinct A s T) (hts : t ⊆ s) :
    IsLineEssDistinct A t T := by
  intro p d hd
  exact le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hts)) (h p d hd)

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A foot on the core.**  A point of a `σ`-tube's carrier is within `σ` of a point of its core
segment. -/
theorem exists_foot_of_mem_carrier {σ : NNReal} (P : Tube σ E) {x : E} (hx : x ∈ P.carrier) :
    ∃ c ∈ segment ℝ P.x P.y, ‖c - x‖ ≤ (σ : ℝ) := by
  rw [P.carrier_eq] at hx
  obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hx
  refine ⟨c, hc, ?_⟩
  rw [← dist_eq_norm, dist_comm]
  simpa [Metric.mem_closedBall] using hxc

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The containment step.**  If `c` lies on the core segment of the `σ`-tube `Q`, `d` is
`±Q.direction`, and the line `(p, dp)` has `‖c - p‖ ≤ εp` and `‖d - dp‖ ≤ εd`, then
`Q ⊂ N_r(p, dp)` as soon as `σ + εp + εd ≤ r`.

This is the refined proof's "comparison of the two unit cores"; the numerical factor allows for
the tube radius, the displacement between the foot points, and the direction error over the unit
core. -/
theorem carrier_subset_lineNbhd {σ : NNReal} (Q : Tube σ E) {c p d dp : E} {εp εd r : ℝ}
    (hc : c ∈ segment ℝ Q.x Q.y) (hd : d = Q.direction ∨ d = -Q.direction)
    (hp : ‖c - p‖ ≤ εp) (hdd : ‖d - dp‖ ≤ εd) (hr : (σ : ℝ) + εp + εd ≤ r) :
    Q.carrier ⊆ lineNbhd p dp r := by
  have hεd0 : 0 ≤ εd := le_trans (norm_nonneg _) hdd
  -- write the core segment as `Q.x + θ • Q.direction`, `θ ∈ [0,1]`
  have hseg : segment ℝ Q.x Q.y = (fun θ : ℝ => Q.x + θ • (Q.y - Q.x)) '' Set.Icc 0 1 :=
    segment_eq_image' ℝ Q.x Q.y
  rw [hseg] at hc
  obtain ⟨θc, hθc, hceq⟩ := hc
  intro y hy
  rw [Q.carrier_eq] at hy
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp hy
  rw [hseg] at hz
  obtain ⟨θz, hθz, hzeq⟩ := hz
  -- `z = c + (θz - θc) • Q.direction`, and `|θz - θc| ≤ 1`
  have hzc : z = c + (θz - θc) • Q.direction := by
    simp only [Tube.direction, ← hzeq, ← hceq]
    module
  have habs : |θz - θc| ≤ 1 := by
    simp only [Set.mem_Icc] at hθc hθz
    rw [abs_le]; constructor <;> [linarith [hθc.1, hθc.2, hθz.1, hθz.2];
      linarith [hθc.1, hθc.2, hθz.1, hθz.2]]
  -- transport the coefficient to `d`
  obtain ⟨s, hs, hsd⟩ : ∃ s : ℝ, |s| ≤ 1 ∧ z = c + s • d := by
    rcases hd with hd | hd
    · exact ⟨θz - θc, habs, by rw [hzc, hd]⟩
    · refine ⟨-(θz - θc), by rwa [abs_neg], ?_⟩
      rw [hzc, hd]; module
  refine mem_lineNbhd_of_dist_le s ?_
  have hyz' : ‖y - z‖ ≤ (σ : ℝ) := by
    rw [← dist_eq_norm]; simpa [Metric.mem_closedBall] using hyz
  have hkey : z - (p + s • dp) = (c - p) + s • (d - dp) := by rw [hsd]; module
  have hz' : ‖z - (p + s • dp)‖ ≤ εp + εd := by
    rw [hkey]
    calc ‖(c - p) + s • (d - dp)‖ ≤ ‖c - p‖ + ‖s • (d - dp)‖ := norm_add_le _ _
      _ = ‖c - p‖ + |s| * ‖d - dp‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ εp + 1 * εd := by gcongr
      _ = εp + εd := by ring
  rw [dist_eq_norm]
  calc ‖y - (p + s • dp)‖ ≤ ‖y - z‖ + ‖z - (p + s • dp)‖ := by
        simpa using norm_sub_le_norm_sub_add_norm_sub y z (p + s • dp)
    _ ≤ (σ : ℝ) + (εp + εd) := add_le_add hyz' hz'
    _ ≤ r := by linarith

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A `σ`-tube lies in the `5σ`-neighbourhood of its own core line. -/
theorem carrier_subset_own_lineNbhd {σ : NNReal} (Q : Tube σ E) :
    Q.carrier ⊆ lineNbhd Q.x Q.direction (5 * (σ : ℝ)) :=
  carrier_subset_lineNbhd Q (left_mem_segment ℝ Q.x Q.y) (Or.inl rfl)
    (εp := 0) (εd := 0) (by simp) (by simp) (by have := σ.coe_nonneg; linarith)

open scoped Classical in
omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Firing control for `IsLineEssDistinct`.**  The condition is not vacuously true: a family
all of whose members are one and the same tube is charged in full, so `IsLineEssDistinct A`
forces `#t ≤ A` there.  (Contrast the pairwise, volume-based notion, which is *also* violated by
such a family — the two notions differ on **axial translates**, not on repetitions;
`Kakeya.LooseUniform.bush_obstruction`'s axially spread bush is line-ED with `A = 1` for each of
its members' own lines and defeats only the pairwise notion.) -/
theorem card_le_of_isLineEssDistinct_const {A : ℕ} {σ : NNReal} {ι : Type*} (t : Finset ι)
    (T : ι → Tube σ E) (Q : Tube σ E) (hconst : ∀ i ∈ t, T i = Q)
    (h : IsLineEssDistinct A t T) : t.card ≤ A := by
  have hfil := h Q.x Q.direction (Tube.norm_direction Q)
  rwa [Finset.filter_true_of_mem
    (fun i hi => by rw [hconst i hi]; exact carrier_subset_own_lineNbhd Q)] at hfil

end LineED

/-! ### The keystone: the line-based node count -/

open Kakeya.LooseUniform

/-- **The direction pin, extracted.**  This is the estimate inside the existing
`tube_le_dilate_of_mem_angularFibre`: any `σ`-tube `P` (`ρ ≤ σ`) *containing* a member `i` of the
angular cone at `(x, v)` of radius `ρ` has its direction within `8σ` of the fixed direction
`u = dir(T i₀)` of any other cone member, up to sign.  Six of the `8σ` come from
`Tube.endpoints_close_of_body_le` (`exists_sign_norm_direction_sub_le_of_body_le`) and two from
the cone's own angular width.

The dilate form is what the pairwise-ED count needed; the line-based count needs the raw
direction estimate, because the line parameter it separates is `(foot, direction)`, not a
container. -/
theorem exists_sign_dir_of_mem_angularFibre (cfg : VeryNotSticky.{u}) {σ : NNReal} {ρ : ℝ}
    (hρ : ρ ≤ (σ : ℝ))
    (x v : EuclideanSpace ℝ (Fin 3)) {i₀ : cfg.ι} (hi₀ : i₀ ∈ cfg.angularFibre x v ρ)
    {i : cfg.ι} (hi : i ∈ cfg.angularFibre x v ρ)
    (P : Tube σ (EuclideanSpace ℝ (Fin 3)))
    (hP : ((cfg.T i).toTube).toConvexSpaceBody ≤ P.toConvexSpaceBody) :
    ∃ ε : ℝ, |ε| = 1 ∧ ‖ε • P.direction - (cfg.T i₀).direction‖ ≤ 8 * (σ : ℝ) := by
  classical
  set u : E3 := (cfg.T i₀).direction with hu
  have hu1 : ‖u‖ = 1 := Tube.norm_direction (cfg.T i₀).toTube
  obtain ⟨-, -, hiang⟩ := Finset.mem_filter.mp hi
  obtain ⟨-, -, hi₀ang⟩ := Finset.mem_filter.mp hi₀
  have hang2 : NonSlab.lineAngle (cfg.T i).direction u ≤ 2 * ρ := by
    have := NonSlab.lineAngle_le_add (cfg.T i).direction v u
    have h2 : NonSlab.lineAngle v u ≤ ρ := (NonSlab.lineAngle_comm v u).trans_le hi₀ang
    linarith
  obtain ⟨s₂, hs₂, hd₂⟩ := exists_sign_norm_sub_le_of_lineAngle_le
    (Tube.norm_direction (cfg.T i).toTube) hu1 hang2
  obtain ⟨s₁, hs₁, hd₁⟩ := exists_sign_norm_direction_sub_le_of_body_le
    ((cfg.T i).toTube) P hP
  have hsq2 : s₂ * s₂ = 1 := by
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp hs₂ with h | h <;> rw [h] <;> norm_num
  refine ⟨s₂ * s₁, by rw [abs_mul, hs₁, hs₂]; norm_num, ?_⟩
  have hkey : (s₂ * s₁) • P.direction - u
      = s₂ • ((s₁ • P.direction - (cfg.T i).direction) + ((cfg.T i).direction - s₂ • u)) := by
    have h1 : s₂ • ((s₁ • P.direction - (cfg.T i).direction) + ((cfg.T i).direction - s₂ • u))
        = (s₂ * s₁) • P.direction - (s₂ * s₂) • u := by module
    rw [h1, hsq2, one_smul]
  rw [hkey, norm_smul, Real.norm_eq_abs, hs₂, one_mul]
  have hfirst : ‖s₁ • P.direction - (cfg.T i).direction‖ ≤ 6 * (σ : ℝ) := by
    rw [show s₁ • P.direction - (cfg.T i).direction
        = -((cfg.T i).direction - s₁ • P.direction) by module, norm_neg]
    exact hd₁
  calc ‖(s₁ • P.direction - (cfg.T i).direction) + ((cfg.T i).direction - s₂ • u)‖
      ≤ ‖s₁ • P.direction - (cfg.T i).direction‖ + ‖(cfg.T i).direction - s₂ • u‖ :=
        norm_add_le _ _
    _ ≤ 6 * (σ : ℝ) + 2 * ρ := add_le_add hfirst hd₂
    _ ≤ 8 * (σ : ℝ) := by linarith

open scoped Classical in
/-- **The keystone count, on an arbitrary line-essentially-distinct family.**  This is the
replacement for `card_le_essDistinctConstant_of_edFamily`: at most `33⁶ · A` members of an
`A`-line-essentially-distinct family of `σ`-tubes (`ρ ≤ σ`) can contain a member of the angular
cone at `(x, v)` of radius `ρ`.

`33⁶ = 1291467969`.  The refined proof (l.3486–3489) charges `600⁶ A₁` for the same step; the
constant here is smaller because the packing is done directly in the two **line** parameters
(a foot point on the node's core, and the sign-normalised direction), each pinned to a ball of
radius `8σ`, and separated at `σ`:
`((8σ + σ/4)/(σ/4))^(2·3) = 33⁶` by `Tube.card_le_of_L1_separated_in_box`.

The whole point of the line-based notion is visible in the proof: the foot point is a point of
the node's core **near `x`**, so the "fifth axial parameter" — the slide of the core along its
supporting line, which is what makes an axially spread bush defeat the pairwise notion
(`Kakeya.LooseUniform.bush_obstruction`) — is never a coordinate. -/
theorem card_le_lineEDConstant_of_lineEDFamily (cfg : VeryNotSticky.{u}) {κ : Type*}
    {σ : NNReal} (hσ0 : 0 < σ) {ρ : ℝ} (hρ : ρ ≤ (σ : ℝ))
    (x v : EuclideanSpace ℝ (Fin 3)) {A : ℕ}
    (t : Finset κ) (P : κ → Tube σ (EuclideanSpace ℝ (Fin 3)))
    (hED : IsLineEssDistinct A t P)
    (hmeet : ∀ j ∈ t, ∃ i ∈ cfg.angularFibre x v ρ,
      ((cfg.T i).toTube).toConvexSpaceBody ≤ (P j).toConvexSpaceBody) :
    t.card ≤ 33 ^ 6 * A := by
  classical
  have hσR : (0 : ℝ) < (σ : ℝ) := by exact_mod_cast hσ0
  rcases t.eq_empty_or_nonempty with hemp | ⟨j₀, hj₀⟩
  · simp [hemp]
  obtain ⟨i₀, hi₀, -⟩ := hmeet j₀ hj₀
  set u : E3 := (cfg.T i₀).direction with hu
  -- the line parameters of every node meeting the cone
  have hex : ∀ j ∈ t, ∃ cj dj : E3, cj ∈ segment ℝ (P j).x (P j).y ∧ ‖cj - x‖ ≤ (σ : ℝ) ∧
      (dj = (P j).direction ∨ dj = -(P j).direction) ∧ ‖dj - u‖ ≤ 8 * (σ : ℝ) := by
    intro j hj
    obtain ⟨i, hi, hiP⟩ := hmeet j hj
    obtain ⟨ε, hε, hεd⟩ := cfg.exists_sign_dir_of_mem_angularFibre hρ x v hi₀ hi (P j) hiP
    have hxT : x ∈ (cfg.T i).carrier :=
      (cfg.T i).shade_subset (Finset.mem_filter.mp hi).2.1
    have hxP : x ∈ (P j).carrier := hiP hxT
    obtain ⟨cj, hcj, hcjx⟩ := exists_foot_of_mem_carrier (P j) hxP
    refine ⟨cj, ε • (P j).direction, hcj, hcjx, ?_, hεd⟩
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp hε with h | h
    · exact Or.inl (by rw [h, one_smul])
    · exact Or.inr (by rw [h, neg_one_smul])
  choose! c d hseg hcx hsign hdu using hex
  have hdnorm : ∀ w ∈ t, ‖d w‖ = 1 := by
    intro w hw
    rcases hsign w hw with h | h
    · rw [h]; exact Tube.norm_direction (P w)
    · rw [h, norm_neg]; exact Tube.norm_direction (P w)
  -- a maximal `σ`-separated set of line parameters
  obtain ⟨S, hSsub, hSsep, hScov⟩ := exists_maximal_separated_finset t
    (fun a b => ‖d a - d b‖ + ‖c a - c b‖) (ε := (σ : ℝ))
    (fun a => by simpa using hσR)
    (fun a b => by rw [norm_sub_rev (d a), norm_sub_rev (c a)])
  -- (1) the packing bound `#S ≤ 33⁶`
  have hScard : (S.card : ℝ) ≤ 33 ^ 6 := by
    have h := Tube.card_le_of_L1_separated_in_box (E := E3) S d c u x
      (R := 8 * (σ : ℝ)) (r := (σ : ℝ)) hσR
      (fun a ha b hb hab => hSsep a ha b hb hab)
      (fun a ha => hdu a (hSsub ha))
      (fun a ha => le_trans (hcx a (hSsub ha)) (by linarith))
    have hfr : Module.finrank ℝ E3 = 3 := by simp
    rw [hfr] at h
    have hval : ((8 * (σ : ℝ) + (σ : ℝ) / 4) / ((σ : ℝ) / 4)) = 33 := by
      field_simp; ring
    rw [hval] at h
    norm_num at h ⊢
    exact h
  have hScardN : S.card ≤ 33 ^ 6 := by exact_mod_cast hScard
  -- (2) every node is charged to a line through one of the `S`-parameters
  have hcover : t ⊆ S.biUnion (fun w => t.filter (fun j =>
      (P j).carrier ⊆ lineNbhd (c w) (d w) (5 * (σ : ℝ)))) := by
    intro j hj
    obtain ⟨w, hw, hlt⟩ := hScov j hj
    refine Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_filter.mpr ⟨hj, ?_⟩⟩
    have hlt' : ‖d j - d w‖ + ‖c j - c w‖ < (σ : ℝ) := hlt
    have hnn1 : (0:ℝ) ≤ ‖d j - d w‖ := norm_nonneg _
    have hnn2 : (0:ℝ) ≤ ‖c j - c w‖ := norm_nonneg _
    exact carrier_subset_lineNbhd (P j) (εp := (σ : ℝ)) (εd := (σ : ℝ)) (r := 5 * (σ : ℝ))
      (hseg j hj) (hsign j hj) (by linarith) (by linarith) (by linarith)
  -- (3) line-based essential distinctness charges at most `A` to each
  have hterm : ∀ w ∈ S, (t.filter (fun j =>
      (P j).carrier ⊆ lineNbhd (c w) (d w) (5 * (σ : ℝ)))).card ≤ A := fun w hw =>
    hED (c w) (d w) (hdnorm w (hSsub hw))
  calc t.card
      ≤ (S.biUnion (fun w => t.filter (fun j =>
          (P j).carrier ⊆ lineNbhd (c w) (d w) (5 * (σ : ℝ))))).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ w ∈ S, (t.filter (fun j =>
          (P j).carrier ⊆ lineNbhd (c w) (d w) (5 * (σ : ℝ)))).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ S, A := Finset.sum_le_sum hterm
    _ = S.card * A := by simp [Finset.sum_const, smul_eq_mul]
    _ ≤ 33 ^ 6 * A := by gcongr

/-! ### The datum `LineEDLevels`, and the angular-count theorem -/

open scoped Classical in
/-- **The keystone count, specialised to a hierarchy whose level-`k` nodes are line-essentially
distinct.**  This is the exact analogue of `card_image_assign_angularFibre_le_of_essDistinct`,
with the pairwise, volume-based hypothesis replaced by the refined text's family-level,
line-based one — and, unlike that one, the hypothesis is **not** known to be uninhabitable: the
centred-net cover of `lemcanonicalcover` (refined l.4774–4800, map row **U1**) produces exactly
it, with the absolute `A₁ = 2·641⁶`. -/
theorem card_image_assign_angularFibre_le_of_lineED (cfg : VeryNotSticky.{u}) {N : ℕ}
    {C : NNReal} (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C)
    {k : ℕ} (hk : k ≤ N) (hδ0 : 0 < cfg.δ) {A₁ : ℕ}
    (hED : IsLineEssDistinct A₁ (𝒰.cover.indexSet k) (𝒰.cover.tube k))
    {ρ : ℝ} (hρ : ρ ≤ (Tube.gridScale cfg.δ N k : ℝ))
    (x v : EuclideanSpace ℝ (Fin 3)) :
    ((cfg.angularFibre x v ρ).image (𝒰.cover.assign k)).card ≤ 33 ^ 6 * A₁ := by
  classical
  have hJsub : (cfg.angularFibre x v ρ).image (𝒰.cover.assign k) ⊆ 𝒰.cover.indexSet k := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact 𝒰.cover.assign_mem k hk i (Finset.mem_filter.mp hi).1
  refine cfg.card_le_lineEDConstant_of_lineEDFamily (Tube.gridScale_pos hδ0 N k) hρ x v
    _ (𝒰.cover.tube k) (hED.mono hJsub) ?_
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact ⟨i, hi, 𝒰.cover.le_tube_assign k hk i (Finset.mem_filter.mp hi).1⟩

open scoped Classical in
/-- **The angular cone, counted through line-essentially-distinct nodes.**  The refined text's
`lem:ml2-angular-count` (l.3462–3493) in the tree's vocabulary: the cone meets at most `33⁶·A₁`
level-`k` nodes, and each contributes at most `C · localN x k ≤ C² · branchingN k` members
shading `x` (Definition 2.2, `ShadedUniform.lean:343–355`, the "pointwise levels (iv)" of the
refined preparation). -/
theorem angularFibre_card_le_of_lineED (cfg : VeryNotSticky.{u}) {N : ℕ} {C : NNReal}
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T N C)
    {k : ℕ} (hk : k ≤ N) (hδ0 : 0 < cfg.δ) {A₁ : ℕ}
    (hED : IsLineEssDistinct A₁ (𝒱.tubeUniform.cover.indexSet k) (𝒱.tubeUniform.cover.tube k))
    {ρ : ℝ} (hρ : ρ ≤ (Tube.gridScale cfg.δ N k : ℝ))
    (x v : EuclideanSpace ℝ (Fin 3)) :
    (((cfg.angularFibre x v ρ).card : ℕ) : ENNReal) ≤
      (((33 ^ 6 * A₁ : ℕ) : NNReal) : ENNReal) * (C : ENNReal) ^ 2 *
        ((𝒱.branchingN k : NNReal) : ENNReal) := by
  classical
  refine cfg.angularFibre_card_le_of_nodeCount 𝒱 hk x v ?_
  have h := cfg.card_image_assign_angularFibre_le_of_lineED 𝒱.tubeUniform hk hδ0 hED hρ x v
  exact_mod_cast h

open scoped Classical in
/-- **The angular-count theorem, row C6-a.**  For a `ShadedUniformTubeSet` whose levels are
`A₁`-line-essentially distinct,

`#angularFibre x v ρ ≤ (33⁶ · A₁ · C⁴) · multiplicity (tubeFibre k j)`

for every active level-`k` node `j`.  This is the refined `eq:ml2-angular-count`
`≤ 4·600⁶ A₁ ν_k` with the tree's `C⁴` in the role of the refined bracket `4 ν_k`
(`branchingN k ≤ C² · multiplicity`, `branchingN_le_multiplicity_of_shadedUniform`) and with the
smaller compiled constant `33⁶ = 1291467969` in the role of `600⁶`. -/
theorem angularFibre_card_le_fibreMult_of_lineED (cfg : VeryNotSticky.{u}) {N : ℕ}
    {C : NNReal} (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T N C) (hC : 1 ≤ C)
    {k : ℕ} (hk : k ≤ N) (hkN : k < N) (hδ0 : 0 < cfg.δ) {A₁ : ℕ}
    (hED : LineEDLevels A₁ 𝒱.tubeUniform)
    {ρ : ℝ} (hρ : ρ ≤ (Tube.gridScale cfg.δ N k : ℝ))
    (x v : EuclideanSpace ℝ (Fin 3))
    {j : cfg.ι} (hj : j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k) :
    (((cfg.angularFibre x v ρ).card : ℕ) : ENNReal) ≤
      ((((33 ^ 6 * A₁ : ℕ) : NNReal) * C ^ 4 : NNReal) : ENNReal) *
        ShadedBody.multiplicity (cfg.tubeFibre 𝒱.tubeUniform k j)
          (fun i ↦ (cfg.T i).toShadedBody) := by
  classical
  have h1 := cfg.angularFibre_card_le_of_lineED 𝒱 hk hδ0 (hED k hkN) hρ x v
  calc (((cfg.angularFibre x v ρ).card : ℕ) : ENNReal)
      ≤ (((33 ^ 6 * A₁ : ℕ) : NNReal) : ENNReal) * (C : ENNReal) ^ 2 *
          ((𝒱.branchingN k : NNReal) : ENNReal) := h1
    _ ≤ (((33 ^ 6 * A₁ : ℕ) : NNReal) : ENNReal) * (C : ENNReal) ^ 2 *
          ((C : ENNReal) ^ 2 *
            ShadedBody.multiplicity (cfg.tubeFibre 𝒱.tubeUniform k j)
              (fun i ↦ (cfg.T i).toShadedBody)) := by
        gcongr
        exact cfg.branchingN_le_multiplicity_of_shadedUniform 𝒱 hC hk hj
    _ = ((((33 ^ 6 * A₁ : ℕ) : NNReal) * C ^ 4 : NNReal) : ENNReal) *
          ShadedBody.multiplicity (cfg.tubeFibre 𝒱.tubeUniform k j)
            (fun i ↦ (cfg.T i).toShadedBody) := by push_cast; ring

/-! ### (b)(c)(d) — the after-texts proposed 

(b) `LineEDLevels` quantifies over `k < N` (imported from `CanonicalCentredCover.lean`, where the
before/after source versions are recorded); the window level is below the bottom level because
`ρ₂* > δ` (`lt_gridLen_of_rho2Star_le`).  (c) the datum's constant carries the hierarchy's constant
`C`: `A₁ = ⌈C · K⌉₊` with `K` absolute, and the budget is `33⁶ (K+1) C⁵ ≤ δ^{-η}` — `C⁵ ≤ δ^{-5η/8}`
from the configuration's own `C₀⁸ ≤ δ^{-η}` and `33⁶ (K+1) ≤ δ^{-3η/8}` at a `δ`-only threshold.
(d) the `∀ᶠ` wrapper is stated for the active restriction of the configuration's own bundle,
`activeShadedHierarchy cfg`, not for the `Classical.choice` `cfg.splitHierarchy` whose inactive
nodes no producer controls; it produces Option E clause
(`conjunct6OptionEClause_of_lineEDLevels_active`), and — with the keystone
`Tube.forall_isLineEssDistinct_activeRestrict_of_centred` — Option E from **centredness of the members
alone** (`conjunct6OptionEClause_of_centred`, `eventually_conjunct6OptionEClause_of_centred`). -/

/-- The active restriction of the configuration's own Def 2.2 bundle — the `𝒱` of Option E: one hierarchy (C-C4), nothing after the chain (C-C1). -/
noncomputable def activeShadedHierarchy (cfg : VeryNotSticky.{u}) :
    ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀ :=
  cfg.uniform.some.activeRestrict

/-- `δ ≤ ρ₂ = b / r₁` from `cfg.hdims` and `r₁ ≤ 1`.  Local twin of
`Kakeya.VeryNotSticky.delta_le_rho2_general` (`SplitInputsGeneral.lean`), whose module sits *above*
`SetupSideData` in the import order (`SplitInputsGeneral → SplitInputsFibreCount → SetupSideData`)
and so cannot be imported by this leaf, which `SetupSideData` imports; the name is distinct so
that the two coexist downstream. -/
theorem delta_le_rho2_c6 (cfg : VeryNotSticky.{u}) : cfg.δ ≤ cfg.rho2 := by
  have hr₁0 : 0 < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  have hr₁1 : cfg.r₁ ≤ 1 := NNReal.rpow_le_one cfg.hδ1 cfg.hexscal.le
  have hb : cfg.b ≤ cfg.rho2 := by
    rw [VeryNotSticky.rho2, le_div_iff₀ hr₁0]
    calc cfg.b * cfg.r₁ ≤ cfg.b * 1 := by gcongr
      _ = cfg.b := mul_one _
  exact le_trans (cfg.hdims.1.trans cfg.hdims.2.1) hb

/-- `δ < ρ₂*`: `ρ₂* = 2 · C_bodyAngle · ρ₂ ≥ 2ρ₂ ≥ 2δ`. -/
theorem delta_lt_rho2Star (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    cfg.δ < cfg.rho2Star C₀ := by
  have h1 : cfg.δ ≤ cfg.rho2 := delta_le_rho2_c6 cfg
  have hb : 1 ≤ NonSlab.bodyAngleConstant C₀ := NonSlab.one_le_bodyAngleConstant hC₀
  have hδ : 0 < cfg.δ := cfg.hδ
  unfold rho2Star
  calc cfg.δ < 2 * cfg.δ := by
        have : (0 : NNReal) < cfg.δ := hδ
        calc cfg.δ = 1 * cfg.δ := (one_mul _).symm
          _ < 2 * cfg.δ := by gcongr; norm_num
    _ ≤ 2 * cfg.rho2 := by gcongr
    _ = 2 * 1 * cfg.rho2 := by ring
    _ ≤ 2 * NonSlab.bodyAngleConstant C₀ * cfg.rho2 := by gcongr

/-- **The window level is below the bottom level**: at `k = N` the node radius is `δ < ρ₂*`. -/
theorem lt_gridLen_of_rho2Star_le (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {k : ℕ}
    (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k) :
    k < Tube.ssfGridLen cfg.δ := by
  rcases lt_or_eq_of_le hk with h | h
  · exact h
  · exfalso
    rw [h, Tube.gridScale_self cfg.δ (ssfGridLen_pos cfg)] at hge
    exact absurd (lt_of_lt_of_le (delta_lt_rho2Star cfg bd.hC₀) hge) (lt_irrefl _)

open scoped Classical in
/-- **(c) Conjunct 6's `∃ Cang` clause from `LineEDLevels` at a constant carrying the hierarchy's
`C`, budget included**, for an arbitrary Def 2.2 bundle `𝒱` at constant `C` on the grid.
`Cang = 33⁶ · ⌈C K⌉₊ · C⁴ ≤ 33⁶ (K+1) C⁵ ≤ δ^{-3η/8} · δ^{-5η/8} = δ^{-η}`. -/
theorem exists_Cang_angularFibre_le_of_lineEDLevels_hier (cfg : VeryNotSticky.{u})
    (bd : BallData cfg) {C : NNReal}
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) C) (hC : 1 ≤ C)
    (hC8 : (C : ENNReal) ^ 8 ≤ (cfg.δ : ENNReal) ^ (-cfg.η))
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ) {K : ℝ} (hK : 0 ≤ K)
    (hED : LineEDLevels ⌈(C : ℝ) * K⌉₊ 𝒱.tubeUniform)
    (hρ : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k)
    (hthr : ENNReal.ofReal (33 ^ 6 * (K + 1)) ≤ (cfg.δ : ENNReal) ^ (-(3 * cfg.η / 8))) :
    ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
      ∀ j ∈ cfg.pbActiveTubeNodes 𝒱.tubeUniform.toPartitionBrackets k,
        ∀ x v : EuclideanSpace ℝ (Fin 3),
          (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
            (Cang : ENNReal) *
              ShadedBody.multiplicity (cfg.pbTubeFibre 𝒱.tubeUniform.toPartitionBrackets k j)
                (fun i ↦ (cfg.T i).toShadedBody) := by
  classical
  have hkN := lt_gridLen_of_rho2Star_le cfg bd hk hρ
  set A₁ : ℕ := ⌈(C : ℝ) * K⌉₊ with hA₁
  have hδ0 : (cfg.δ : ENNReal) ≠ 0 := by simpa using (ne_of_gt cfg.hδ)
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- `A₁ ≤ (K + 1) C`
  have hA₁R : (A₁ : ℝ) ≤ (K + 1) * (C : ℝ) := by
    have hCK : 0 ≤ (C : ℝ) * K := mul_nonneg C.coe_nonneg hK
    have h1 : (A₁ : ℝ) < (C : ℝ) * K + 1 := Nat.ceil_lt_add_one hCK
    have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
    nlinarith
  have hA₁E : (A₁ : ENNReal) ≤ ENNReal.ofReal (K + 1) * (C : ENNReal) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal hA₁R
  -- `C⁵ ≤ δ^{-5η/8}`
  have hC5 : (C : ENNReal) ^ 5 ≤ (cfg.δ : ENNReal) ^ (-(5 * cfg.η / 8)) := by
    have h := ENNReal.rpow_le_rpow hC8 (by norm_num : (0 : ℝ) ≤ 5 / 8)
    have hl : ((C : ENNReal) ^ 8) ^ ((5 : ℝ) / 8) = (C : ENNReal) ^ 5 := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        show ((8 : ℕ) : ℝ) * (5 / 8) = ((5 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    have hr : ((cfg.δ : ENNReal) ^ (-cfg.η)) ^ ((5 : ℝ) / 8) =
        (cfg.δ : ENNReal) ^ (-(5 * cfg.η / 8)) := by
      rw [← ENNReal.rpow_mul]; congr 1; ring
    rwa [hl, hr] at h
  -- the budget
  have hbud : ((((33 ^ 6 * A₁ : ℕ) : NNReal) * C ^ 4 : NNReal) : ENNReal)
      ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := by
    have hsum : (cfg.δ : ENNReal) ^ (-(3 * cfg.η / 8)) * (cfg.δ : ENNReal) ^ (-(5 * cfg.η / 8))
        = (cfg.δ : ENNReal) ^ (-cfg.η) := by
      rw [← ENNReal.rpow_add _ _ hδ0 hδtop]; congr 1; ring
    have h336 : ENNReal.ofReal (33 ^ 6 * (K + 1)) =
        (33 : ENNReal) ^ 6 * ENNReal.ofReal (K + 1) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat]
    calc ((((33 ^ 6 * A₁ : ℕ) : NNReal) * C ^ 4 : NNReal) : ENNReal)
        = (33 : ENNReal) ^ 6 * (A₁ : ENNReal) * (C : ENNReal) ^ 4 := by push_cast; ring
      _ ≤ (33 : ENNReal) ^ 6 * (ENNReal.ofReal (K + 1) * (C : ENNReal)) * (C : ENNReal) ^ 4 :=
          mul_le_mul' (mul_le_mul' le_rfl hA₁E) le_rfl
      _ = ((33 : ENNReal) ^ 6 * ENNReal.ofReal (K + 1)) * (C : ENNReal) ^ 5 := by ring
      _ = ENNReal.ofReal (33 ^ 6 * (K + 1)) * (C : ENNReal) ^ 5 := by rw [h336]
      _ ≤ (cfg.δ : ENNReal) ^ (-(3 * cfg.η / 8)) * (cfg.δ : ENNReal) ^ (-(5 * cfg.η / 8)) :=
          mul_le_mul' hthr hC5
      _ = (cfg.δ : ENNReal) ^ (-cfg.η) := hsum
  refine ⟨((33 ^ 6 * A₁ : ℕ) : NNReal) * C ^ 4, hbud, ?_⟩
  intro j hj x v
  rw [← activeTubeNodes_eq_pbActiveTubeNodes] at hj
  rw [← tubeFibre_eq_pbTubeFibre]
  exact cfg.angularFibre_card_le_fibreMult_of_lineED 𝒱 hC hk hkN cfg.hδ hED
    (by exact_mod_cast hρ) x v hj

open scoped Classical in
/-- **(d) The `∀ᶠ` wrapper over the active restriction of the configuration's own bundle.**
The clause is inner clause at `𝒱 := activeShadedHierarchy cfg`, `C := cfg.C₀`;
the only hypothesis is the datum on that bundle. -/
theorem eventually_conjunct6_of_lineEDLevels_active {exscal ϱ η : ℝ} (hη : 0 < η)
    (C₀bd : NNReal) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = d → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      LineEDLevels ⌈(cfg.C₀ : ℝ) * K⌉₊ (activeShadedHierarchy cfg).tubeUniform →
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
          ∀ j ∈ cfg.pbActiveTubeNodes (activeShadedHierarchy cfg).tubeUniform.toPartitionBrackets k,
            ∀ x v : EuclideanSpace ℝ (Fin 3),
              (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
                (Cang : ENNReal) *
                  ShadedBody.multiplicity
                    (cfg.pbTubeFibre (activeShadedHierarchy cfg).tubeUniform.toPartitionBrackets
                      k j)
                    (fun i ↦ (cfg.T i).toShadedBody) := by
  filter_upwards [eventually_ennreal_le_rpow_neg (K := ENNReal.ofReal (33 ^ 6 * (K + 1)))
    ENNReal.ofReal_ne_top (by positivity : (0 : ℝ) < 3 * η / 8)] with d hthr
  intro cfg bd hδd hηc _ _ _ _ hED k hk hge _
  have hthr' : ENNReal.ofReal (33 ^ 6 * (K + 1)) ≤ (cfg.δ : ENNReal) ^ (-(3 * cfg.η / 8)) := by
    rw [hδd, hηc]; exact hthr
  exact exists_Cang_angularFibre_le_of_lineEDLevels_hier cfg bd (activeShadedHierarchy cfg)
    cfg.hC₀ (coe_C₀_pow_eight_le_rpow_neg_eta cfg) hk hK hED hge hthr'

open scoped Classical in
/-- **Option E clause from the datum on the active restriction of `cfg.uniform`.**
`C := cfg.C₀` (`1 ≤ C₀`, `C₀ ≤ C₀⁸ ≤ δ^{-η}`), `𝒱 := activeShadedHierarchy cfg`. -/
theorem conjunct6OptionEClause_of_lineEDLevels_active (cfg : VeryNotSticky.{u})
    (bd : BallData cfg) {K : ℝ} (hK : 0 ≤ K)
    (hED : LineEDLevels ⌈(cfg.C₀ : ℝ) * K⌉₊ (activeShadedHierarchy cfg).tubeUniform)
    (hthr : ENNReal.ofReal (33 ^ 6 * (K + 1)) ≤ (cfg.δ : ENNReal) ^ (-(3 * cfg.η / 8))) :
    conjunct6OptionEClause cfg bd := by
  refine ⟨cfg.C₀, activeShadedHierarchy cfg, cfg.hC₀, ?_, ?_⟩
  · have h1 : (1 : ENNReal) ≤ (cfg.C₀ : ENNReal) := by exact_mod_cast cfg.hC₀
    calc (cfg.C₀ : ENNReal) ≤ (cfg.C₀ : ENNReal) ^ 8 := le_self_pow h1 (by norm_num)
      _ ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := coe_C₀_pow_eight_le_rpow_neg_eta cfg
  · intro k hk hge _
    exact exists_Cang_angularFibre_le_of_lineEDLevels_hier cfg bd (activeShadedHierarchy cfg)
      cfg.hC₀ (coe_C₀_pow_eight_le_rpow_neg_eta cfg) hk hK hED hge hthr

/-- **Option E from centredness of the members alone** (the keystone
`Tube.forall_isLineEssDistinct_activeRestrict_of_centred` feeding (c)/(d)).  `K` is the absolute
`Tube.activeLineConstant 3 1`; `h4` is the grid separation `4δ ≤ ρ_k` below the bottom level. -/
theorem conjunct6OptionEClause_of_centred (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (hcen : ∀ i ∈ cfg.s, (cfg.T i).toTube.IsCentred)
    (h4 : ∀ k, k < Tube.ssfGridLen cfg.δ →
      4 * (cfg.δ : ℝ) ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k)
    (hthr : ENNReal.ofReal (33 ^ 6 *
        (Tube.activeLineConstant (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) 1 + 1)) ≤
      (cfg.δ : ENNReal) ^ (-(3 * cfg.η / 8))) :
    conjunct6OptionEClause cfg bd := by
  refine conjunct6OptionEClause_of_lineEDLevels_active cfg bd
    (K := Tube.activeLineConstant (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) 1)
    (by unfold Tube.activeLineConstant; positivity) ?_ hthr
  exact Tube.forall_isLineEssDistinct_activeRestrict_of_centred cfg.hδ cfg.uniform.some.tubeUniform hcen
    (by norm_num)
    (fun i hi ↦ Tube.norm_midpoint_le_of_subset_ball cfg.hδ (cfg.T i).toTube (cfg.contained i hi))
    h4

/-- **The `∀ᶠ` form of the centred headline**: below a `δ`-threshold depending on `η` alone,
every centred configuration satisfies Option E clause. -/
theorem eventually_conjunct6OptionEClause_of_centred {exscal ϱ η : ℝ} (hη : 0 < η)
    (C₀bd : NNReal) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = d → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      (∀ i ∈ cfg.s, (cfg.T i).toTube.IsCentred) →
      conjunct6OptionEClause cfg bd := by
  obtain ⟨δ₀, hδ₀pos, -, hthr₀⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le 1 le_rfl 0 1 1 one_pos
  have hle : ∀ᶠ d : NNReal in 𝓝[>] 0, d ≤ δ₀ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ₀pos)] with d hd
    exact le_of_lt hd
  filter_upwards [eventually_ennreal_le_rpow_neg
    (K := ENNReal.ofReal (33 ^ 6 *
      (Tube.activeLineConstant (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) 1 + 1)))
    ENNReal.ofReal_ne_top (by positivity : (0 : ℝ) < 3 * η / 8), hle] with d hthr hd
  intro cfg bd hδd hηc _ _ _ _ hcen
  have hthr' : ENNReal.ofReal (33 ^ 6 *
      (Tube.activeLineConstant (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) 1 + 1)) ≤
      (cfg.δ : ENNReal) ^ (-(3 * cfg.η / 8)) := by
    rw [hδd, hηc]; exact hthr
  refine conjunct6OptionEClause_of_centred cfg bd hcen ?_ hthr'
  intro k hk
  obtain ⟨-, hδ16, -⟩ := hthr₀ cfg.hδ (by rw [hδd]; exact hd)
  have h8 := Tube.eight_delta_le_gridScale cfg.hδ cfg.hδ1 hk hδ16
  have h8R : 8 * (cfg.δ : ℝ) ≤ (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ) := by
    exact_mod_cast h8
  have := cfg.δ.coe_nonneg
  linarith

/-- **D10's `hAngular` binder of the general boundary, discharged for centred configurations.**

The statement below is, line for line, the `hAngular` hypothesis of
`Kakeya.VeryNotSticky.exists_setup_caseSideData_general` / `sideDataResidue_of_obligations_general`
(`SetupSideDataGeneral.lean`, D10 after-text `5117be00…`), so the general boundary can consume it
by `exact` (tripwire below).  Proof: the thresholds of `eventually_conjunct6OptionEClause_of_centred`
(none of them reads `b`; the guard `b ≤ δ^{2·exscal}` is unused), the line-ED datum of the
configuration's own hierarchy from centredness (`Tube.forall_isLineEssDistinct_activeRestrict_of_centred`),
C6-a's `exists_Cang_angularFibre_le_of_lineEDLevels_hier` at `activeShadedHierarchy cfg`, and the
bridge from that hierarchy's `pbActiveTubeNodes`/`pbTubeFibre` to `cfg.splitHierarchy`'s
`activeTubeNodes`/`tubeFibre`: a node of `cfg.splitHierarchy` with a nonempty fibre is an active
node, and the active restriction keeps the assignment, so the fibres are definitionally the same.
 R1 said "no producer" for this binder; with D10's centredness hypothesis there is one. -/
theorem eventually_hAngular_general_of_centred {exscal ϱ η : ℝ} (hη : 0 < η) (C₀bd : NNReal) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) → bd.C₀ = C₀bd →
      (∀ j ∈ cfg.s, (cfg.T j).toTube.IsCentred) →
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
          ∀ j ∈ cfg.activeTubeNodes cfg.splitHierarchy k,
            ∀ x v : E3,
              (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
                (Cang : ENNReal) *
                  ShadedBody.multiplicity (cfg.tubeFibre cfg.splitHierarchy k j)
                    (fun i ↦ (cfg.T i).toShadedBody) := by
  classical
  obtain ⟨δ₀, hδ₀pos, -, hthr₀⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le 1 le_rfl 0 1 1 one_pos
  have hle : ∀ᶠ d : NNReal in 𝓝[>] 0, d ≤ δ₀ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ₀pos)] with d hd
    exact le_of_lt hd
  filter_upwards [eventually_ennreal_le_rpow_neg
    (K := ENNReal.ofReal (33 ^ 6 *
      (Tube.activeLineConstant (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) 1 + 1)))
    ENNReal.ofReal_ne_top (by positivity : (0 : ℝ) < 3 * η / 8), hle] with d hthr hd
  intro cfg bd hδd hηc _ _ _ _ hcen k hk hge _
  have hthr' : ENNReal.ofReal (33 ^ 6 *
      (Tube.activeLineConstant (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) 1 + 1)) ≤
      (cfg.δ : ENNReal) ^ (-(3 * cfg.η / 8)) := by
    rw [hδd, hηc]; exact hthr
  have h4 : ∀ k, k < Tube.ssfGridLen cfg.δ →
      4 * (cfg.δ : ℝ) ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k := by
    intro k hk
    obtain ⟨-, hδ16, -⟩ := hthr₀ cfg.hδ (by rw [hδd]; exact hd)
    have h8 := Tube.eight_delta_le_gridScale cfg.hδ cfg.hδ1 hk hδ16
    have h8R : 8 * (cfg.δ : ℝ) ≤ (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ) := by
      exact_mod_cast h8
    have := cfg.δ.coe_nonneg
    linarith
  have hK : (0 : ℝ) ≤ Tube.activeLineConstant (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) 1 := by
    unfold Tube.activeLineConstant; positivity
  have hED : LineEDLevels
      ⌈(cfg.C₀ : ℝ) * Tube.activeLineConstant (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) 1⌉₊
      (activeShadedHierarchy cfg).tubeUniform :=
    Tube.forall_isLineEssDistinct_activeRestrict_of_centred cfg.hδ cfg.uniform.some.tubeUniform hcen
      (by norm_num)
      (fun i hi ↦ Tube.norm_midpoint_le_of_subset_ball cfg.hδ (cfg.T i).toTube (cfg.contained i hi))
      h4
  obtain ⟨Cang, hCang, hang⟩ := exists_Cang_angularFibre_le_of_lineEDLevels_hier cfg bd
    (activeShadedHierarchy cfg) cfg.hC₀ (coe_C₀_pow_eight_le_rpow_neg_eta cfg) hk hK hED hge hthr'
  refine ⟨Cang, hCang, fun j hj x v ↦ ?_⟩
  -- the bridge: an active node of `cfg.splitHierarchy` is an active node of its active restriction
  have hj' : j ∈ cfg.pbActiveTubeNodes (activeShadedHierarchy cfg).tubeUniform.toPartitionBrackets k := by
    simp only [activeTubeNodes, Finset.mem_filter] at hj
    obtain ⟨hj1, i, hi⟩ := hj
    have hi' : i ∈ cfg.s ∧ cfg.splitHierarchy.cover.assign k i = j := by
      simpa only [tubeFibre, Tube.coverClass, Finset.mem_filter] using hi
    simp only [pbActiveTubeNodes, Finset.mem_filter]
    refine ⟨?_, i, hi⟩
    exact (Tube.GridCoverSystem.mem_activeIndexSet cfg.splitHierarchy.cover).mpr ⟨hj1, i, hi'.1, hi'.2⟩
  exact hang j hj' x v

/-- **Tripwire**: the theorem above closes D10's `hAngular` binder by `exact` — its statement is
that binder's text.  Fails to elaborate if either moves. -/
example {exscal ϱ η : ℝ} (hη : 0 < η) (C₀bd : NNReal) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) → bd.C₀ = C₀bd →
      (∀ j ∈ cfg.s, (cfg.T j).toTube.IsCentred) →
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
          ∀ j ∈ cfg.activeTubeNodes cfg.splitHierarchy k,
            ∀ x v : E3,
              (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
                (Cang : ENNReal) *
                  ShadedBody.multiplicity (cfg.tubeFibre cfg.splitHierarchy k j)
                    (fun i ↦ (cfg.T i).toShadedBody) :=
  eventually_hAngular_general_of_centred hη C₀bd

open scoped Classical in
/-- **The exact step-8 plug for centred configurations** (the twin of
`eventually_exists_pbSplitInputs_of_conjunct6`): `PBSplitInputs` from the active restriction of the
configuration's own bundle, its line-ED datum (`Tube.forall_isLineEssDistinct_activeRestrict_of_centred`, from
centredness), the angular clause ((c) above), the count clause supplied by the retyped conjunct 5
 at `C := cfg.C₀`, and `fibreConstant_of_threshold` at `cfg.C₀`.  Conjunct 6 is not
consulted: with centredness it is a theorem (`eventually_conjunct6OptionEClause_of_centred`), and
its licensed bracket `C ≤ δ^{-η}` would not feed `PBSplitInputs.fibreConstant` anyway. -/
theorem eventually_exists_pbSplitInputs_of_centred (C₀ : NNReal) (hC₀ : 1 ≤ C₀)
    {exscal ϱ η : ℝ} (hη : 0 < η) (hexscal0 : 0 < exscal) (hexscal : exscal ≤ 1 / 2)
    (hϱ1 : ϱ ≤ 1) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
        cfg.δ = d → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → bd.C₀ = C₀ →
        cfg.b = cfg.δ →
        (∀ j ∈ cfg.s, (cfg.T j).toTube.IsCentred) →
        (∀ C : NNReal, 1 ≤ C → (C : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) →
          ∀ 𝒰s : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) C,
          ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
            cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
            Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
                cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
            ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
              (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
                (Ccnt : ℝ) * ((𝒰s.cover.indexSet k).card : ℝ)) →
        Nonempty (PBSplitInputs cfg bd) := by
  have hpos : (0 : NNReal) < (2 * NonSlab.bodyAngleConstant C₀)⁻¹ := by
    have h1 : (1 : NNReal) ≤ 2 * NonSlab.bodyAngleConstant C₀ :=
      one_le_mul_of_one_le_of_one_le (by norm_num) (NonSlab.one_le_bodyAngleConstant hC₀)
    exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one h1)
  have hKtop : ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ENNReal) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.coe_ne_top
  set K : ℝ := Tube.activeLineConstant (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) 1 with hKdef
  have hK : 0 ≤ K := by rw [hKdef]; unfold Tube.activeLineConstant; positivity
  obtain ⟨δ₀, hδ₀pos, -, hthr₀⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le 1 le_rfl 0 1 1 one_pos
  have hle : ∀ᶠ d : NNReal in 𝓝[>] 0, d ≤ δ₀ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ₀pos)] with d hd
    exact le_of_lt hd
  filter_upwards [eventually_nnreal_mul_rpow_le_const 1 _ hpos hexscal0,
    eventually_ennreal_le_rpow_neg hKtop (by positivity : (0 : ℝ) < 3 * η / 4),
    eventually_ennreal_le_rpow_neg (K := ENNReal.ofReal (33 ^ 6 * (K + 1)))
      ENNReal.ofReal_ne_top (by positivity : (0 : ℝ) < 3 * η / 8), hle]
    with d hscale hthr hthrK hd
  intro cfg bd hδ hη' hexs hϱ' hC₀' hb hcen hconj5
  subst hδ hη' hexs hϱ' hC₀'
  rw [one_mul] at hscale
  obtain ⟨k, hk, hge, hle'⟩ := exists_splitLevel cfg bd.hC₀ hexscal hscale hb
  have h4 : ∀ k, k < Tube.ssfGridLen cfg.δ →
      4 * (cfg.δ : ℝ) ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k := by
    intro k hk
    obtain ⟨-, hδ16, -⟩ := hthr₀ cfg.hδ hd
    have h8 := Tube.eight_delta_le_gridScale cfg.hδ cfg.hδ1 hk hδ16
    have h8R : 8 * (cfg.δ : ℝ) ≤ (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ) := by
      exact_mod_cast h8
    have := cfg.δ.coe_nonneg
    linarith
  have hED := Tube.forall_isLineEssDistinct_activeRestrict_of_centred cfg.hδ cfg.uniform.some.tubeUniform hcen
    (R₀ := 1) (by norm_num)
    (fun i hi ↦ Tube.norm_midpoint_le_of_subset_ball cfg.hδ (cfg.T i).toTube (cfg.contained i hi))
    h4
  obtain ⟨Cang, hCang, hang⟩ := exists_Cang_angularFibre_le_of_lineEDLevels_hier cfg bd
    (activeShadedHierarchy cfg) cfg.hC₀ (coe_C₀_pow_eight_le_rpow_neg_eta cfg) hk hK hED hge hthrK
  have hC₀δ : (cfg.C₀ : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := by
    have h1 : (1 : ENNReal) ≤ (cfg.C₀ : ENNReal) := by exact_mod_cast cfg.hC₀
    calc (cfg.C₀ : ENNReal) ≤ (cfg.C₀ : ENNReal) ^ 8 := le_self_pow h1 (by norm_num)
      _ ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := coe_C₀_pow_eight_le_rpow_neg_eta cfg
  obtain ⟨Ccnt, hCcnt, hfsc⟩ := hconj5 cfg.C₀ cfg.hC₀ hC₀δ (activeShadedHierarchy cfg).tubeUniform
    k hk hge hle'
  exact ⟨PBSplitInputs.ofLevel cfg bd (activeShadedHierarchy cfg).tubeUniform.toPartitionBrackets
    hk hge hle' (ktScaleData_of_ckt cfg hexscal hϱ1) (fibreConstant_of_threshold cfg hthr)
    Cang hCang hang Ccnt hCcnt hfsc⟩

end VeryNotSticky

end Kakeya
