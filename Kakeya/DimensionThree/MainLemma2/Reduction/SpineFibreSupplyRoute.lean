/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFibreStoppingRun
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineWindowLowerBoundOwner

/-!
# The dichotomy of `dividingScalesLemma` (B), and the hoisted supply row

Source: `260115_kakeyadetailedproofv3_revised_detailed.tex` **l.2733-2753** — Part (B) of
`dividingScalesLemma` in full: the array `Z(k,l) = max_{S∈𝕋_k} Δ_max(𝕋_l⟨S⟩)` on thread cells
(l.2733), the transposition `X̃(k,l) = Z(M-l,M-k)` (l.2735-2737), submultiplicativity at
**`300⁹C₂`** and the crude exponent **`d = 4`** from the assumed cardinality estimate
(l.2739-2741), the scale hypothesis `δ ≤ ρ_M/ρ_0 ≤ δ^{ε²}` (l.2743-2746), and — the sentence this
file rests on —

> *"In particular the witness again comes from an attained maximum; no assertion about every cell
> is made. This also explains why Part (B) is not merely Part (A) with names changed."*
> (l.2749-2753)

That is the source's **own condition** for `eqdividingKwitness` being existential, which is what
makes `Kakeya.ML2Core.le_mul_maxDensity_nodesUnder_of_lt_towerDensityArrayFibre` — an existential
fibre witness upgraded by the regularization band — the right shape for the lower-bound field, and
it is why the witness must be produced on the **fibre** array.

`SpineFibreStoppingRun.lean` ran the stopping time on the fibre array.  This file closes the two
conclusions the run does not itself deliver and assembles the dichotomy.

## 1. The tail, `eqdividingKfirst` — chained submultiplicativity, telescoped

`lemabstractstopping`'s tail is proved by *"submultiplicativity over the pieces after it"*.
`chain_le_of_submultiplicative` is that induction, abstract in the array: over a cut set `S ∋ 0`,
with the array submultiplicative at pairs of `S` and admissible on adjacent pairs,

  `Z(0,x) ≤ B^{(#pieces below x)} · bnd(0,x)`   for every `x ∈ S`,

the piece bound telescoping through `htel`.  On the fibre array
(`towerDensityArrayFibre_zero_le_of_cuts`) the telescoping is exact — `sourceBound_mul_le`:
`(ρ_0/ρ_p)^θ · (ρ_p/ρ_c)^θ = (ρ_0/ρ_c)^θ` — and the base case is
`towerDensityArrayFibre_self_le_one`, `Z_fib(k,k) ≤ 1`, because a thread cell read at its own level
is the singleton `{S}`.  With `ρ_0 = 1` (`Tube.gridScale_zero`) the output is
`Z_fib(0,a) ≤ B^{|S|} · ρ_a^{-η_m}` (`sourceBound_zero_eq`), which is `eqdividingKfirst` and, after
`maxDensity_indexSet_le_mul_towerDensityArrayFibre`, the window's `coarse_maxDensity_le`.

**The gap hypothesis is discharged, not assumed.**  `towerDensityArrayFibre_submultiplicative`
needs `4·ρ_c ≤ ρ_p`.  `gridScale_gap_of_step` derives it for **every** `p < c` from the single
scale condition `4·ρ_1 ≤ 1`, i.e. `4·δ^{1/L} ≤ 1`; at `L = ssfGridLen δ = ⌈log log(1/δ)⌉₊` one grid
step is `δ^{1/L}`, which is far below `1/4` for small `δ`, so this is a scale threshold and enters
no exponent account.

**The constant is NAMED.**  `fibreChainConst` is `max 1 (C₀'(E)²)`; the existing constant sits below
it (`twoScaleSubsetConst_sq_le_fibreChainConst`) and `1 ≤ fibreChainConst`, which is what lets the
piece count be over-counted by `|S| ≤ N+1`.  `C₀'(E)²` is the Lean form of the source's `300⁹C₂`
(`SpineTowerArrayFibre.lean`: the source's `C₂` is the geometric-competitor constant, the analogue
of the `Cu` only the containment reading needs).

## 2. The every-scale alternative, `eqstoppingallscales`, and **which existing statement it is**

`isKatzTaoAtEveryScale_of_allShort` produces the existing
**`Tube.UniformTubeSet.IsKatzTaoAtEveryScale`** (`Sticky.lean:115`), i.e. GWZ Definition 7.1(B):
`∀ k ≤ L, Δ_max(𝒰.cover.indexSet k) ≤ A`.

**No Condition-R cost arises, and no `nodesUnder` appears.**  The existing every-scale predicate is
on the **node family** `indexSet k`, each node counted once — exactly the object
`maxDensity_indexSet_le_mul_towerDensityArrayFibre` bounds by `Cu · Z_fib(0,k)`.  So the bridge
from the fibre array to the existing statement is that one lemma, at one factor `Cu` (δ-free), and
`towerDensityArrayFibre_le_towerDensityArray` is **not** used: it runs the other way and would be
the wrong direction here.  Nothing is stated on the containment set at all.

The proof is the source's: *"combine (H1), the crude bound on the single partial piece containing
`k`, and the admissible bounds on all later pieces"*.  `exists_pred_short` produces the cut point
`p ≤ l` and the shortness `l - p ≤ ε_d·L` of the partial piece; the chain covers `[0,p]`; the
crude exponent `d = 4` covers `(p,l]`; `gridScale_tail_bound` multiplies the two grid factors into
`δ^{-(η_m + 4ε_d)}`, and `η_m ≤ ε_d` turns that into the source's `δ^{-5ε}`.  The constant is
`Cu · fibreChainConst^{N+2} · D · δ^{-5ε_d}`, the shape of the source's `B_K^{N+1}δ^{-5ε}`.

## 3. The dichotomy, and the order of the two alternatives 

`isKatzTaoAtEveryScale_or_dividingWindow` is `dividingScalesLemma` (B) on a fixed tower: **either**
the every-scale bound **or** a dividing window, from the one run on the one array.  The case split
is on whether some adjacent piece is Long; `SpineFibreStoppingRun.lean`'s module docstring records
the measurement that the pigeonhole does not force one, which is why the source states an
either/or.

(checked against l.4365-4376 and l.4396): the every-scale output goes to the sticky Kakeya
theorem and terminates as `(G)`; the window refinement is entered only from the non-sticky side.
So the every-scale alternative **never** enters the floor route, `RefinedFloorSupplyAt` correctly
offers only `(F)`, and `DefectBranchAt` is an *output* of the window refinement, not this.

## 4. The hoisted payload row

`RefinedSupplyAt` has the following shape: **one** refinement `S'`, then the dichotomy **on that
same `S'`** —

  `∃ S' ⊆ S (+ hhom + hW), IsKatzTaoAtEveryScale (refinedHierarchy …) ∨ ⟨the (F) data⟩`

— not two independently quantified disjuncts.  `refinedSupplyAt_of_dichotomy` produces it from
exactly that datum; `refinedFloorSupplyAt_of_refinedSupplyAt` is the retarget bridge to the existing
`Kakeya.ML2Core.RefinedFloorSupplyAt` once the every-scale side is excluded, and
`floorDataAtTrichotomy_of_refinedSupplyAt` composes with the existing
`floorDataAtTrichotomy_of_refinedFloorSupply`.  The right disjunct is `RefinedFloorHypothesis`'s
body verbatim with its `∃ S'` hoisted, which is what makes the bridge a re-association and not a
re-proof.

## Named rows that remain

* **`hwindow`** — `le_window_maxDensity`.  `window_field_of_card` reduces it, at the field's own
  quantifiers, to the **count** of `nodesUnder b a j` plus a containing body `K` and a per-tube
  volume floor `v₀`.  The tube
  geometry supplying `K`, `v₀` and the numerical inequality is not spent here.
* **`hflo`** — `FloorHypothesisAt` on the refined tower (`ParentAdmissible`, `FillAt`, the four
  scalar rows).
* **`href`** and the band — A1's one joint pass on each `S`
  (`exists_refinement_classHomogeneous_levelDensityBand`,
  `exists_shadedRefinement_of_joint_bin`), which must produce **one** `S'` for both.
* The margin separation `p + w ≤ q` between distinct cut points is established inside
  `Kakeya.MultiScaleFac.exists_maximal_cuts_abstract_state_margin_aux` (`Stopping.lean`, `hgap'`)
  but is **not exported** by `exists_maximal_cuts_abstract_state_margin`'s conclusion.  This file
  does not need it — `gridScale_gap_of_step` supplies every gap from the scale threshold — but a
  future hand wanting it must export it, which is a change to a existing statement.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `exists_pred_of_mem_cut`, `chain_le_of_submultiplicative` | none — combinatorial | the cut set |
| `gridScale_gap_of_step`, `gridScale_tail_bound`, `exists_pred_short` | none — grid | `(p,c)` |
| `towerDensityArrayFibre_self_le_one` | the tower's `s`, `T`; no shading | `(k,k)` |
| `sourceBound_mul_le`, `sourceBound_zero_eq` | none | `(0,p,c)` |
| `towerDensityArrayFibre_zero_le_of_cuts(')` | the tower's `s`, `T`; no shading | `(0,x)` |
| `isKatzTaoAtEveryScale_of_allShort` | as above | every `(0,l)` |
| `isKatzTaoDividingWindowLevels_of_fibreRun_band` | as above | the window `(a,b,m)` |
| `isKatzTaoAtEveryScale_or_dividingWindow` | as above | the cut set; the window `(a,b,m)` |
| `window_field_of_card` | as above | `(a,b)` at radius `ρ` |
| `RefinedSupplyAt` and its three theorems | ambient `u` refined to `S'`; shading `W` | `(a,b,m)` |

## A1-a

No `GridUniformCore` is named anywhere.  No `(F)`-branch interface statement is defined or
altered: `IsKatzTaoDividingWindowLevels` is inhabited through the existing
`isKatzTaoDividingWindowLevels_of_fields`, `IsKatzTaoAtEveryScale` is the existing `def` used as
printed, and `RefinedSupplyAt` is a **new proof-internal** `def` that no §2.2 statement mentions.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory Tube

namespace Kakeya.ML2Core

section CutChain

/-- **The predecessor of a cut point.** -/
theorem exists_pred_of_mem_cut {S : Finset ℕ} (h0 : 0 ∈ S) {x : ℕ} (hx : x ∈ S) (hx0 : x ≠ 0) :
    ∃ p ∈ S, p < x ∧ (∀ y ∈ S, ¬(p < y ∧ y < x)) ∧
      S.filter (fun y => y ≤ x) = insert x (S.filter (fun y => y ≤ p)) := by
  classical
  have hne : (S.filter (fun y => y < x)).Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨h0, Nat.pos_of_ne_zero hx0⟩⟩
  set p := (S.filter (fun y => y < x)).max' hne with hp
  have hpmem : p ∈ S.filter (fun y => y < x) := (S.filter (fun y => y < x)).max'_mem hne
  have hpS : p ∈ S := (Finset.mem_filter.mp hpmem).1
  have hpx : p < x := (Finset.mem_filter.mp hpmem).2
  refine ⟨p, hpS, hpx, ?_, ?_⟩
  · rintro y hy ⟨hpy, hyx⟩
    have : y ≤ p := Finset.le_max' _ y (Finset.mem_filter.mpr ⟨hy, hyx⟩)
    omega
  · ext y
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hyS, hyx⟩
      rcases eq_or_lt_of_le hyx with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨hyS, Finset.le_max' _ y (Finset.mem_filter.mpr ⟨hyS, hlt⟩)⟩
    · rintro (rfl | ⟨hyS, hyp⟩)
      · exact ⟨hx, le_rfl⟩
      · exact ⟨hyS, by omega⟩

/-- **Chained submultiplicativity along a cut set.** -/
theorem chain_le_of_submultiplicative {Z bnd : ℕ → ℕ → ENNReal} {B : ENNReal} {S : Finset ℕ}
    (h0 : 0 ∈ S)
    (hsubm : ∀ p ∈ S, ∀ c ∈ S, p < c → Z 0 c ≤ B * Z 0 p * Z p c)
    (hbase : Z 0 0 ≤ bnd 0 0)
    (htel : ∀ p ∈ S, ∀ c ∈ S, p < c → bnd 0 p * bnd p c ≤ bnd 0 c)
    (hgood : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) → Z a b ≤ bnd a b) :
    ∀ x ∈ S, Z 0 x ≤ B ^ ((S.filter (fun y => y ≤ x)).card - 1) * bnd 0 x := by
  classical
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    rcases eq_or_ne x 0 with rfl | hx0
    · have hfil : S.filter (fun y => y ≤ 0) = {0} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨-, hy⟩; omega
        · rintro rfl; exact ⟨h0, le_rfl⟩
      rw [hfil]
      simpa using hbase
    · obtain ⟨p, hpS, hpx, hadj, hfil⟩ := exists_pred_of_mem_cut h0 hx hx0
      have hcardp : 1 ≤ (S.filter (fun y => y ≤ p)).card :=
        Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨h0, Nat.zero_le _⟩⟩
      have hnot : x ∉ S.filter (fun y => y ≤ p) := by
        simp only [Finset.mem_filter, not_and]
        intro _; omega
      have hcardx : (S.filter (fun y => y ≤ x)).card
          = (S.filter (fun y => y ≤ p)).card + 1 := by
        rw [hfil, Finset.card_insert_of_notMem hnot]
      have hIH := ih p hpx hpS
      calc Z 0 x ≤ B * Z 0 p * Z p x := hsubm p hpS x hx hpx
        _ ≤ B * (B ^ ((S.filter (fun y => y ≤ p)).card - 1) * bnd 0 p) * bnd p x :=
            mul_le_mul' (mul_le_mul' le_rfl hIH) (hgood p hpS x hx hpx hadj)
        _ = B ^ (((S.filter (fun y => y ≤ p)).card - 1) + 1) * (bnd 0 p * bnd p x) := by
            rw [pow_succ]; ring
        _ ≤ B ^ ((S.filter (fun y => y ≤ x)).card - 1) * bnd 0 x := by
            refine mul_le_mul' (le_of_eq ?_) (htel p hpS x hx hpx)
            congr 1
            omega

end CutChain

section GridArithmetic

/-- **One grid step of separation gives every separation.** -/
theorem gridScale_gap_of_step {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (h4 : 4 * Tube.gridScale δ (Tube.ssfGridLen δ) 1 ≤ 1) {p c : ℕ} (hpc : p < c) :
    4 * Tube.gridScale δ (Tube.ssfGridLen δ) c ≤ Tube.gridScale δ (Tube.ssfGridLen δ) p := by
  set L := Tube.ssfGridLen δ with hL
  have hLpos : 0 < L := by
    by_contra h
    have hL0 : L = 0 := by omega
    rw [hL0] at h4
    simp [Tube.gridScale] at h4
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hexp : ((p : ℝ) / (L : ℝ)) + (((c : ℝ) - (p : ℝ)) / (L : ℝ)) = (c : ℝ) / (L : ℝ) := by
    field_simp
    ring
  have hsplit : Tube.gridScale δ L c
      = Tube.gridScale δ L p * δ ^ (((c : ℝ) - (p : ℝ)) / (L : ℝ)) := by
    rw [Tube.gridScale, Tube.gridScale, ← NNReal.rpow_add (ne_of_gt hδ0), hexp]
  have hone : (1 : ℝ) / (L : ℝ) ≤ ((c : ℝ) - (p : ℝ)) / (L : ℝ) := by
    have h1 : (p : ℝ) + 1 ≤ (c : ℝ) := by exact_mod_cast hpc
    gcongr
    linarith
  have hstep : δ ^ (((c : ℝ) - (p : ℝ)) / (L : ℝ)) ≤ Tube.gridScale δ L 1 := by
    rw [Tube.gridScale, Nat.cast_one]
    exact NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hone
  calc 4 * Tube.gridScale δ L c
      = Tube.gridScale δ L p * (4 * δ ^ (((c : ℝ) - (p : ℝ)) / (L : ℝ))) := by
        rw [hsplit]; ring
    _ ≤ Tube.gridScale δ L p * (4 * Tube.gridScale δ L 1) := by
        exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hstep)
    _ ≤ Tube.gridScale δ L p * 1 := mul_le_mul' le_rfl h4
    _ = Tube.gridScale δ L p := mul_one _

/-- **The predecessor cut of an arbitrary level, and the shortness of the partial piece.** -/
theorem exists_pred_short {S : Finset ℕ} (h0 : 0 ∈ S) {L l : ℕ} (hLS : L ∈ S) (hl : l ≤ L)
    {εd : ℝ} (hεd : 0 ≤ εd)
    (hshort : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) →
      (b : ℝ) - (a : ℝ) ≤ εd * (L : ℝ)) :
    ∃ p ∈ S, p ≤ l ∧ ((l : ℝ) - (p : ℝ)) ≤ εd * (L : ℝ) := by
  classical
  have hne : (S.filter (fun y => y ≤ l)).Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨h0, Nat.zero_le _⟩⟩
  obtain ⟨p, hpS, hpl, hpmax⟩ : ∃ p ∈ S, p ≤ l ∧ ∀ y ∈ S, y ≤ l → y ≤ p := by
    refine ⟨(S.filter (fun y => y ≤ l)).max' hne, ?_, ?_, ?_⟩
    · exact (Finset.mem_filter.mp ((S.filter (fun y => y ≤ l)).max'_mem hne)).1
    · exact (Finset.mem_filter.mp ((S.filter (fun y => y ≤ l)).max'_mem hne)).2
    · exact fun y hy hyl => Finset.le_max' _ y (Finset.mem_filter.mpr ⟨hy, hyl⟩)
  refine ⟨p, hpS, hpl, ?_⟩
  rcases eq_or_lt_of_le hpl with hpe | hplt
  · rw [hpe, sub_self]
    positivity
  · have hlL : l < L := by
      rcases eq_or_lt_of_le hl with hlLe | h
      · exact absurd (hpmax L hLS hlLe.ge) (by omega)
      · exact h
    have hqne : (S.filter (fun y => l < y)).Nonempty :=
      ⟨L, Finset.mem_filter.mpr ⟨hLS, hlL⟩⟩
    obtain ⟨q, hqS, hlq, hqmin⟩ : ∃ q ∈ S, l < q ∧ ∀ y ∈ S, l < y → q ≤ y := by
      refine ⟨(S.filter (fun y => l < y)).min' hqne, ?_, ?_, ?_⟩
      · exact (Finset.mem_filter.mp ((S.filter (fun y => l < y)).min'_mem hqne)).1
      · exact (Finset.mem_filter.mp ((S.filter (fun y => l < y)).min'_mem hqne)).2
      · exact fun y hy hly => Finset.min'_le _ y (Finset.mem_filter.mpr ⟨hy, hly⟩)
    have hadj : ∀ y ∈ S, ¬(p < y ∧ y < q) := by
      rintro y hy ⟨hpy, hyq⟩
      rcases le_or_gt y l with hyl | hly
      · exact absurd (hpmax y hy hyl) (by omega)
      · exact absurd (hqmin y hy hly) (by omega)
    have hqp : (q : ℝ) - (p : ℝ) ≤ εd * (L : ℝ) := hshort p hpS q hqS (by omega) hadj
    have hlqR : (l : ℝ) ≤ (q : ℝ) := by exact_mod_cast hlq.le
    linarith

/-- **The two grid factors of the partial piece, combined.** -/
theorem gridScale_tail_bound {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {θ εd : ℝ}
    (hθ : 0 ≤ θ) {p l : ℕ} (hpL : p ≤ Tube.ssfGridLen δ) (hLpos : 0 < Tube.ssfGridLen δ)
    (hshort : ((l : ℝ) - (p : ℝ)) / (Tube.ssfGridLen δ : ℝ) ≤ εd) :
    ((Tube.gridScale δ (Tube.ssfGridLen δ) 0 : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)) ^ θ
        * (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) l : ℝ)) ^ (4 : ℕ))
      ≤ (δ : ℝ) ^ (-(θ + 4 * εd)) := by
  set L := Tube.ssfGridLen δ with hLdef
  have hu0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hu1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hg : ∀ k : ℕ, (Tube.gridScale δ L k : ℝ) = (δ : ℝ) ^ ((k : ℝ) / (L : ℝ)) := by
    intro k
    rw [Tube.gridScale]
    exact NNReal.coe_rpow _ _
  have e1 : (Tube.gridScale δ L 0 : ℝ) / (Tube.gridScale δ L p : ℝ)
      = (δ : ℝ) ^ (-((p : ℝ) / (L : ℝ))) := by
    rw [hg, hg, ← Real.rpow_sub hu0]
    congr 1
    simp
  have e2 : (Tube.gridScale δ L p : ℝ) / (Tube.gridScale δ L l : ℝ)
      = (δ : ℝ) ^ (((p : ℝ) - (l : ℝ)) / (L : ℝ)) := by
    rw [hg, hg, ← Real.rpow_sub hu0]
    congr 1
    ring
  rw [e1, e2, ← Real.rpow_natCast ((δ : ℝ) ^ (((p : ℝ) - (l : ℝ)) / (L : ℝ))) 4,
    ← Real.rpow_mul hu0.le, ← Real.rpow_mul hu0.le, ← Real.rpow_add hu0]
  refine Real.rpow_le_rpow_of_exponent_ge hu0 hu1 ?_
  have hp1 : (p : ℝ) / (L : ℝ) ≤ 1 := by
    rw [div_le_one hLR]
    exact_mod_cast hpL
  have hA : -θ ≤ -((p : ℝ) / (L : ℝ)) * θ := by nlinarith
  have hB : -(4 * εd) ≤ ((p : ℝ) - (l : ℝ)) / (L : ℝ) * (4 : ℕ) := by
    have : ((l : ℝ) - (p : ℝ)) / (L : ℝ) ≤ εd := hshort
    have h2 : ((p : ℝ) - (l : ℝ)) / (L : ℝ) = -(((l : ℝ) - (p : ℝ)) / (L : ℝ)) := by ring
    rw [h2]
    push_cast
    nlinarith
  linarith

end GridArithmetic

section FibreChain

/-- **The chain constant, named**: `C₀'(E)²` bracketed below by `1` so that the number of pieces
may be over-counted.  's naming rule — a constant that differs from the existing one is a
NAMED `max`, with the comparison recorded. -/
noncomputable def fibreChainConst.{u} : ENNReal :=
  max 1 (ENNReal.ofReal (twoScaleSubsetConst.{u, 0} (EuclideanSpace ℝ (Fin 3))) ^ 2)

theorem one_le_fibreChainConst.{u} : 1 ≤ fibreChainConst.{u} := le_max_left _ _

/-- **The `_eq` the naming rule asks for**: wherever the existing constant is already at least `1`,
the named constant *is* the existing one, so nothing has been silently enlarged. -/
theorem fibreChainConst_eq_of_one_le.{u}
    (h : 1 ≤ ENNReal.ofReal (twoScaleSubsetConst.{u, 0} (EuclideanSpace ℝ (Fin 3))) ^ 2) :
    fibreChainConst.{u}
      = ENNReal.ofReal (twoScaleSubsetConst.{u, 0} (EuclideanSpace ℝ (Fin 3))) ^ 2 :=
  max_eq_right h

/-- The existing submultiplicativity constant sits below the named one. -/
theorem twoScaleSubsetConst_sq_le_fibreChainConst.{u} :
    ENNReal.ofReal (twoScaleSubsetConst.{u, 0} (EuclideanSpace ℝ (Fin 3))) ^ 2
      ≤ fibreChainConst.{u} := le_max_right _ _

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **The array is at most `1` on the diagonal.** -/
theorem towerDensityArrayFibre_self_le_one
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (k : ℕ) :
    towerDensityArrayFibre 𝒰 k k ≤ 1 := by
  classical
  refine towerDensityArrayFibre_le_of_card_le 𝒰 (fun j _ => ?_)
  have hsub : 𝒰.assignFibre k k j ⊆ {j} := by
    intro x hx
    simp only [Tube.UniformTubeSet.assignFibre, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [coverClass, Finset.mem_filter] at hi
    simp [hi.2]
  have : (𝒰.assignFibre k k j).card ≤ 1 := by
    simpa using Finset.card_le_card hsub
  exact_mod_cast this

/-- **The source's piece bound telescopes**: `r(0,p)^{-θ} · r(p,c)^{-θ} = r(0,c)^{-θ}`. -/
theorem sourceBound_mul_le (hδ0 : 0 < δ) {rinv : ℕ → ℕ → ℝ} {η : ℕ → ℝ} {j : ℕ}
    (hrinv : ∀ p c : ℕ, rinv p c = (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) (p c : ℕ) :
    sourceBound rinv η j 0 p * sourceBound rinv η j p c ≤ sourceBound rinv η j 0 c := by
  have hpos : ∀ k : ℕ, (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ) := by
    intro k
    exact_mod_cast Tube.gridScale_pos hδ0 _ k
  have h0 : (0 : ℝ) ≤ rinv 0 p := by
    rw [hrinv]; positivity
  have h1 : (0 : ℝ) ≤ rinv p c := by
    rw [hrinv]; positivity
  have hne : ∀ k : ℕ, (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ) ≠ 0 :=
    fun k => ne_of_gt (hpos k)
  have hmul : rinv 0 p * rinv p c = rinv 0 c := by
    rw [hrinv, hrinv, hrinv]
    field_simp [hne p, hne c]
  refine le_of_eq ?_
  rw [sourceBound, sourceBound, sourceBound, ← ENNReal.ofReal_mul (by positivity),
    ← Real.mul_rpow h0 h1, hmul]

open scoped Classical in
/-- **The tail conclusion `eqdividingKfirst`**: `Z_fib(0,x)` at every cut point. -/
theorem towerDensityArrayFibre_zero_le_of_cuts (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {S : Finset ℕ} (h0 : 0 ∈ S) (hSL : ∀ x ∈ S, x ≤ Tube.ssfGridLen δ)
    (hgapS : ∀ p ∈ S, ∀ c ∈ S, p < c →
      4 * Tube.gridScale δ (Tube.ssfGridLen δ) c ≤ Tube.gridScale δ (Tube.ssfGridLen δ) p)
    {rinv : ℕ → ℕ → ℝ} {η : ℕ → ℝ} {m : ℕ}
    (hrinv : ∀ p c : ℕ, rinv p c = (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ))
    (hgood : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) →
      towerDensityArrayFibre 𝒰 a b ≤ sourceBound rinv η m a b) :
    ∀ x ∈ S, towerDensityArrayFibre 𝒰 0 x
      ≤ (ENNReal.ofReal (twoScaleSubsetConst.{u, 0} (EuclideanSpace ℝ (Fin 3))) ^ 2)
          ^ ((S.filter (fun y => y ≤ x)).card - 1) * sourceBound rinv η m 0 x := by
  classical
  refine chain_le_of_submultiplicative (Z := fun a b => towerDensityArrayFibre 𝒰 a b)
    (bnd := fun a b => sourceBound rinv η m a b) h0 ?_ ?_ ?_ hgood
  · intro p hp c hc hpc
    exact towerDensityArrayFibre_submultiplicative hδ0 hδ1 𝒰 hs hball (Nat.zero_le p) hpc.le
      (hSL c hc) (hgapS p hp c hc hpc)
  · refine le_trans (towerDensityArrayFibre_self_le_one 𝒰 0) ?_
    rw [sourceBound, hrinv]
    have : ((Tube.gridScale δ (Tube.ssfGridLen δ) 0 : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) 0 : ℝ)) = 1 := by
      have := Tube.gridScale_pos hδ0 (Tube.ssfGridLen δ) 0
      field_simp
    rw [this, Real.one_rpow, ENNReal.ofReal_one]
  · intro p _ c _ _
    exact sourceBound_mul_le hδ0 hrinv p c

open scoped Classical in
/-- **The tail conclusion at the named constant**, with the piece count over-counted by `S.card`. -/
theorem towerDensityArrayFibre_zero_le_of_cuts' (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {S : Finset ℕ} (h0 : 0 ∈ S) (hSL : ∀ x ∈ S, x ≤ Tube.ssfGridLen δ)
    (hgapS : ∀ p ∈ S, ∀ c ∈ S, p < c →
      4 * Tube.gridScale δ (Tube.ssfGridLen δ) c ≤ Tube.gridScale δ (Tube.ssfGridLen δ) p)
    {rinv : ℕ → ℕ → ℝ} {η : ℕ → ℝ} {m : ℕ}
    (hrinv : ∀ p c : ℕ, rinv p c = (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ))
    (hgood : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) →
      towerDensityArrayFibre 𝒰 a b ≤ sourceBound rinv η m a b)
    {x : ℕ} (hx : x ∈ S) :
    towerDensityArrayFibre 𝒰 0 x
      ≤ fibreChainConst.{u} ^ S.card * sourceBound rinv η m 0 x := by
  classical
  refine le_trans (towerDensityArrayFibre_zero_le_of_cuts hδ0 hδ1 𝒰 hs hball h0 hSL hgapS
    hrinv hgood x hx) (mul_le_mul' ?_ le_rfl)
  have hcard : (S.filter (fun y => y ≤ x)).card - 1 ≤ S.card :=
    le_trans (Nat.sub_le _ 1) (Finset.card_le_card (Finset.filter_subset _ _))
  calc (ENNReal.ofReal (twoScaleSubsetConst.{u, 0} (EuclideanSpace ℝ (Fin 3))) ^ 2)
        ^ ((S.filter (fun y => y ≤ x)).card - 1)
      ≤ fibreChainConst.{u} ^ ((S.filter (fun y => y ≤ x)).card - 1) :=
        pow_le_pow_left' twoScaleSubsetConst_sq_le_fibreChainConst.{u} _
    _ ≤ fibreChainConst.{u} ^ S.card := pow_le_pow_right' one_le_fibreChainConst.{u} hcard

open scoped Classical in
/-- **`eqstoppingallscales` on the fibre array, delivered as the existing
`Tube.UniformTubeSet.IsKatzTaoAtEveryScale`.** -/
theorem isKatzTaoAtEveryScale_of_allShort (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (h4 : 4 * Tube.gridScale δ (Tube.ssfGridLen δ) 1 ≤ 1)
    (hLpos : 0 < Tube.ssfGridLen δ)
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {S : Finset ℕ} (h0 : 0 ∈ S) (hSL : ∀ x ∈ S, x ≤ Tube.ssfGridLen δ)
    (hLS : Tube.ssfGridLen δ ∈ S)
    {rinv : ℕ → ℕ → ℝ} {η : ℕ → ℝ} {m : ℕ}
    (hrinv : ∀ p c : ℕ, rinv p c = (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ))
    (hθ : 0 ≤ η m) {εd : ℝ} (hεd : 0 ≤ εd)
    (hgood : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) →
      towerDensityArrayFibre 𝒰 a b ≤ sourceBound rinv η m a b)
    (hshort : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) →
      (b : ℝ) - (a : ℝ) ≤ εd * (Tube.ssfGridLen δ : ℝ))
    {D : ENNReal} (hD1 : 1 ≤ D)
    (hcrude : ∀ p c : ℕ, p ≤ c → c ≤ Tube.ssfGridLen δ →
      towerDensityArrayFibre 𝒰 p c ≤ D * ENNReal.ofReal
        (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ (4 : ℕ))) :
    𝒰.IsKatzTaoAtEveryScale ((Cu : ENNReal) * (fibreChainConst.{u} ^ (S.card + 1)
      * (D * ENNReal.ofReal ((δ : ℝ) ^ (-(η m + 4 * εd)))))) := by
  classical
  have hgapS : ∀ p ∈ S, ∀ c ∈ S, p < c →
      4 * Tube.gridScale δ (Tube.ssfGridLen δ) c ≤ Tube.gridScale δ (Tube.ssfGridLen δ) p :=
    fun p _ c _ hpc => gridScale_gap_of_step hδ0 hδ1 h4 hpc
  have hLR : (0 : ℝ) < (Tube.ssfGridLen δ : ℝ) := by exact_mod_cast hLpos
  intro l hl
  refine le_trans (maxDensity_indexSet_le_mul_towerDensityArrayFibre 𝒰 hs hball hl) ?_
  refine mul_le_mul' le_rfl ?_
  obtain ⟨p, hpS, hpl, hshortp⟩ :=
    exists_pred_short h0 hLS hl hεd hshort
  have hpL : p ≤ Tube.ssfGridLen δ := hSL p hpS
  have hchain := towerDensityArrayFibre_zero_le_of_cuts' hδ0 hδ1 𝒰 hs hball h0 hSL hgapS
    hrinv hgood hpS
  have hshortdiv : ((l : ℝ) - (p : ℝ)) / (Tube.ssfGridLen δ : ℝ) ≤ εd := by
    rw [div_le_iff₀ hLR]
    linarith [hshortp]
  have hreal := gridScale_tail_bound hδ0 hδ1 (θ := η m) (εd := εd) hθ hpL hLpos hshortdiv
  have hnn1 : (0 : ℝ) ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) 0 : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)) ^ η m := by positivity
  have hnn2 : (0 : ℝ) ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) l : ℝ)) ^ (4 : ℕ) := by positivity
  have hprod : sourceBound rinv η m 0 p * ENNReal.ofReal
        (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) l : ℝ)) ^ (4 : ℕ))
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η m + 4 * εd))) := by
    rw [sourceBound, hrinv, ← ENNReal.ofReal_mul hnn1]
    exact ENNReal.ofReal_le_ofReal hreal
  rcases eq_or_lt_of_le hpl with hpe | hplt
  · -- `l` is itself a cut point
    have hone : ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) l : ℝ)) ^ (4 : ℕ) = 1 := by
      rw [hpe]
      have := Tube.gridScale_pos hδ0 (Tube.ssfGridLen δ) l
      field_simp
    have hstep : sourceBound rinv η m 0 p
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η m + 4 * εd))) := by
      simpa [hone] using hprod
    calc towerDensityArrayFibre 𝒰 0 l
        = towerDensityArrayFibre 𝒰 0 p := by rw [hpe]
      _ ≤ fibreChainConst.{u} ^ S.card * sourceBound rinv η m 0 p := hchain
      _ ≤ fibreChainConst.{u} ^ (S.card + 1)
            * (D * ENNReal.ofReal ((δ : ℝ) ^ (-(η m + 4 * εd)))) := by
          refine mul_le_mul' (pow_le_pow_right' one_le_fibreChainConst.{u} (by omega)) ?_
          exact le_trans hstep (le_mul_of_one_le_left (by simp) hD1)
  · -- `l` sits strictly inside the partial piece starting at `p`
    have hsubm := towerDensityArrayFibre_submultiplicative hδ0 hδ1 𝒰 hs hball
      (Nat.zero_le p) hplt.le hl (gridScale_gap_of_step hδ0 hδ1 h4 hplt)
    calc towerDensityArrayFibre 𝒰 0 l
        ≤ ENNReal.ofReal (twoScaleSubsetConst.{u, 0} (EuclideanSpace ℝ (Fin 3))) ^ 2
            * towerDensityArrayFibre 𝒰 0 p * towerDensityArrayFibre 𝒰 p l := hsubm
      _ ≤ fibreChainConst.{u}
            * (fibreChainConst.{u} ^ S.card * sourceBound rinv η m 0 p)
            * (D * ENNReal.ofReal
                (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) l : ℝ)) ^ (4 : ℕ))) :=
          mul_le_mul' (mul_le_mul' twoScaleSubsetConst_sq_le_fibreChainConst.{u} hchain)
            (hcrude p l hplt.le hl)
      _ = fibreChainConst.{u} ^ (S.card + 1) * (D * (sourceBound rinv η m 0 p
            * ENNReal.ofReal
                (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) l : ℝ)) ^ (4 : ℕ)))) := by
          rw [pow_succ]; ring
      _ ≤ fibreChainConst.{u} ^ (S.card + 1)
            * (D * ENNReal.ofReal ((δ : ℝ) ^ (-(η m + 4 * εd)))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hprod)

end FibreChain

section WindowFromRun

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **The twin from one Long adjacent piece, with the band in the shape A1's refinement produces.**
-/
theorem isKatzTaoDividingWindowLevels_of_fibreRun_band (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {Cstar : ENNReal} (hCuCstar : (Cu : ENNReal) ≤ Cstar)
    {η : ℕ → ℝ} {εd : ℝ} {N a b m w : ℕ} {rinv : ℕ → ℕ → ℝ}
    (hrinv : ∀ p c : ℕ, rinv p c = (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ))
    (hmN : m < N) (hab : a < b) (hbL : b ≤ Tube.ssfGridLen δ)
    (hwidth : εd * (Tube.ssfGridLen δ : ℝ) + (a : ℝ) ≤ (b : ℝ))
    (hwmargin : w ≤ ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊)
    (hgood : towerDensityArrayFibre 𝒰 a b ≤ sourceBound rinv η m a b)
    (hwit : ∀ c : ℕ, a + w ≤ c → c + w ≤ b →
      sourceBound rinv η (m + 1) a c < towerDensityArrayFibre 𝒰 a c)
    (hcoarse : (Cu : ENNReal) * towerDensityArrayFibre 𝒰 0 a
      ≤ Cstar * ENNReal.ofReal ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) ^ (-η m)))
    (hwindow : ∀ ρ : NNReal,
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ εd ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ εd →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
          ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder b a j)
              (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody))
    {Φ : ℕ → ℕ → ENNReal}
    (hband : ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ, ∀ j ∈ 𝒰.cover.indexSet p,
      Φ p c ≤ Kakeya.maxDensity (𝒰.assignFibre c p j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity (𝒰.assignFibre c p j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤ Cstar * Φ p c) :
    ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar η εd N a b m := by
  classical
  have haL : a ≤ Tube.ssfGridLen δ := le_trans hab.le hbL
  have hmiddle : ∀ j ∈ 𝒰.cover.indexSet a,
      Kakeya.maxDensity (𝒰.nodesUnder b a j) (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
        ≤ Cstar * ENNReal.ofReal
            (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
              / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ η m) := by
    intro j hj
    refine le_trans (maxDensity_nodesUnder_le_mul_towerDensityArrayFibre 𝒰 hs haL hbL hj) ?_
    refine le_trans (mul_le_mul' le_rfl hgood) ?_
    rw [sourceBound, hrinv a b]
    exact mul_le_mul' hCuCstar le_rfl
  have hcoarse' : Kakeya.maxDensity (𝒰.cover.indexSet a)
      (fun j => (𝒰.cover.tube a j).toConvexSpaceBody)
      ≤ Cstar * ENNReal.ofReal ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) ^ (-η m)) :=
    le_trans (maxDensity_indexSet_le_mul_towerDensityArrayFibre 𝒰 hs hball haL) hcoarse
  have hbandA : ∀ c ≤ Tube.ssfGridLen δ, ∀ j ∈ 𝒰.cover.indexSet a,
      Φ a c ≤ Kakeya.maxDensity (𝒰.assignFibre c a j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity (𝒰.assignFibre c a j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤ Cstar * Φ a c :=
    fun c hc j hj => hband a haL c hc j hj
  have hlevel := le_level_maxDensity_of_fibre_witness (εd := εd) (η := η) (m := m) 𝒰 hbL hbandA
    (fun c h1 h2 => by
      have := hwit c (by omega) (by omega)
      rwa [sourceBound, hrinv a c] at this)
  exact isKatzTaoDividingWindowLevels_of_fields
    (isKatzTaoDividingWindow_of_fields hδ0 hδ1 hmN hab hbL hwidth hcoarse' hmiddle hwindow)
    hlevel ⟨Φ, hband⟩

/-- The piece bound at the coarse end, in the window field's own shape. -/
theorem sourceBound_zero_eq (hδ0 : 0 < δ) {rinv : ℕ → ℕ → ℝ}
    (hrinv : ∀ p c : ℕ, rinv p c = (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ))
    (η : ℕ → ℝ) (m a : ℕ) :
    sourceBound rinv η m 0 a
      = ENNReal.ofReal ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) ^ (-η m)) := by
  have hpos : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) := by
    exact_mod_cast Tube.gridScale_pos hδ0 _ a
  rw [sourceBound, hrinv, Tube.gridScale_zero]
  congr 1
  push_cast
  rw [Real.div_rpow zero_le_one hpos.le, Real.one_rpow, Real.rpow_neg hpos.le, one_div]

/-- **The dichotomy of `dividingScalesLemma` (B), on a fixed tower and the fibre array.** -/
theorem isKatzTaoAtEveryScale_or_dividingWindow (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h4 : 4 * Tube.gridScale δ (Tube.ssfGridLen δ) 1 ≤ 1) (hLpos : 0 < Tube.ssfGridLen δ)
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ} (hεd : 0 ≤ εd) {N w : ℕ}
    {rinv : ℕ → ℕ → ℝ}
    (hrinv : ∀ p c : ℕ, rinv p c = (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ))
    (hr : ∀ a b : ℕ, 1 ≤ rinv a b) (hηmono : ∀ j j' : ℕ, j ≤ j' → η j ≤ η j')
    (hη0 : ∀ j : ℕ, 0 ≤ η j) (hηεd : ∀ j : ℕ, η j ≤ εd)
    {Efac : ℝ} (hE : 1 ≤ Efac)
    (hcal : ∀ j a c b : ℕ, ENNReal.ofReal Efac * sourceBound rinv η j a b
      ≤ sourceBound rinv η (j + 1) c b)
    (hw : 0 < w) (hwM : w ≤ Tube.ssfGridLen δ) (hwN : Tube.ssfGridLen δ ≤ w * N)
    (hwmar : w ≤ ⌈εd * ((⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ : ℕ) : ℝ)⌉₊)
    (hGood : towerDensityArrayFibre 𝒰 0 (Tube.ssfGridLen δ)
      ≤ sourceBound rinv η 0 0 (Tube.ssfGridLen δ))
    {D : ENNReal} (hD1 : 1 ≤ D)
    (hcrude : ∀ p c : ℕ, p ≤ c → c ≤ Tube.ssfGridLen δ →
      towerDensityArrayFibre 𝒰 p c ≤ D * ENNReal.ofReal
        (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ (4 : ℕ)))
    (hCstarChain : (Cu : ENNReal) * fibreChainConst.{u} ^ (N + 1) ≤ Cstar)
    (hwindow : ∀ a b m : ℕ, ∀ ρ : NNReal,
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ εd ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ εd →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
          ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder b a j)
              (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody))
    {Φ : ℕ → ℕ → ENNReal}
    (hband : ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ, ∀ j ∈ 𝒰.cover.indexSet p,
      Φ p c ≤ Kakeya.maxDensity (𝒰.assignFibre c p j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity (𝒰.assignFibre c p j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤ Cstar * Φ p c) :
    𝒰.IsKatzTaoAtEveryScale ((Cu : ENNReal) * (fibreChainConst.{u} ^ (N + 2)
        * (D * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * εd))))))
      ∨ ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar η εd N a b m := by
  classical
  have hδ1' : δ ≤ 1 := hδ1.le
  have hLR : (0 : ℝ) ≤ (Tube.ssfGridLen δ : ℝ) := Nat.cast_nonneg _
  obtain ⟨S, m, hmN, h0, hLmem, hsubr, hcard, hpieces⟩ :=
    exists_fibreStoppingRun 𝒰 hs hE hr hηmono hcal N w hw hwM hwN
      (fun a b => ⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ + a ≤ b) hGood
  have hSL : ∀ x ∈ S, x ≤ Tube.ssfGridLen δ := by
    intro x hx
    have := Finset.mem_range.mp (hsubr hx)
    omega
  by_cases hex : ∃ a ∈ S, ∃ b ∈ S, a < b ∧ (∀ y ∈ S, ¬(a < y ∧ y < b)) ∧
      ⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ + a ≤ b
  · right
    obtain ⟨a, ha, b, hb, hab, hadj, hlong⟩ := hex
    obtain ⟨hgood, halt⟩ := hpieces a ha b hb hab hadj
    have hwit := halt.resolve_left (not_not_intro hlong)
    have hbL : b ≤ Tube.ssfGridLen δ := hSL b hb
    have hceil : εd * (Tube.ssfGridLen δ : ℝ) ≤ (⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hbaR : ((⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ : ℕ) : ℝ) ≤ (b : ℝ) - (a : ℝ) := by
      have : ((⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ : ℕ) : ℝ) + (a : ℝ) ≤ (b : ℝ) := by
        exact_mod_cast hlong
      linarith
    have hwidth : εd * (Tube.ssfGridLen δ : ℝ) + (a : ℝ) ≤ (b : ℝ) := by linarith
    have hwmargin : w ≤ ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ :=
      le_trans hwmar (Nat.ceil_le_ceil (by nlinarith))
    have hchain := towerDensityArrayFibre_zero_le_of_cuts' hδ0 hδ1' 𝒰 hs hball h0 hSL
      (fun p _ c _ hpc => gridScale_gap_of_step hδ0 hδ1' h4 hpc) hrinv
      (fun x hx y hy hxy hadj' => (hpieces x hx y hy hxy hadj').1) ha
    have hcoarse : (Cu : ENNReal) * towerDensityArrayFibre 𝒰 0 a
        ≤ Cstar * ENNReal.ofReal
            ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) ^ (-η m)) := by
      calc (Cu : ENNReal) * towerDensityArrayFibre 𝒰 0 a
          ≤ (Cu : ENNReal) * (fibreChainConst.{u} ^ S.card * sourceBound rinv η m 0 a) :=
            mul_le_mul' le_rfl hchain
        _ = ((Cu : ENNReal) * fibreChainConst.{u} ^ S.card) * sourceBound rinv η m 0 a := by
            ring
        _ ≤ ((Cu : ENNReal) * fibreChainConst.{u} ^ (N + 1)) * sourceBound rinv η m 0 a := by
            refine mul_le_mul' (mul_le_mul' le_rfl ?_) le_rfl
            exact pow_le_pow_right' (a := fibreChainConst.{u}) one_le_fibreChainConst.{u}
              (show S.card ≤ N + 1 by omega)
        _ ≤ Cstar * sourceBound rinv η m 0 a := mul_le_mul' hCstarChain le_rfl
        _ = Cstar * ENNReal.ofReal
              ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) ^ (-η m)) := by
            rw [sourceBound_zero_eq hδ0 hrinv]
    exact ⟨a, b, m, isKatzTaoDividingWindowLevels_of_fibreRun_band hδ0 hδ1 𝒰 hs hball
      (le_trans (le_mul_of_one_le_right (by simp) (one_le_pow₀ one_le_fibreChainConst.{u}))
        hCstarChain)
      hrinv hmN hab hbL hwidth hwmargin hgood hwit hcoarse (hwindow a b m) hband⟩
  · left
    have hshort : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) →
        (b : ℝ) - (a : ℝ) ≤ εd * (Tube.ssfGridLen δ : ℝ) := by
      intro a ha b hb hab hadj
      have hlt : b < ⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ + a := by
        by_contra hcon
        exact hex ⟨a, ha, b, hb, hab, hadj, by omega⟩
      have h1 : (b : ℝ) + 1 ≤ ((⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ : ℕ) : ℝ) + (a : ℝ) := by
        exact_mod_cast hlt
      have h2 : ((⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ : ℕ) : ℝ)
          < εd * (Tube.ssfGridLen δ : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
      linarith
    refine Tube.UniformTubeSet.IsKatzTaoAtEveryScale.mono
      (isKatzTaoAtEveryScale_of_allShort hδ0 hδ1' h4 hLpos 𝒰 hs hball h0 hSL hLmem hrinv
        (hη0 m) hεd (fun x hx y hy hxy hadj' => (hpieces x hx y hy hxy hadj').1) hshort hD1
        hcrude) ?_
    refine mul_le_mul' le_rfl (mul_le_mul' ?_ (mul_le_mul' le_rfl ?_))
    · exact pow_le_pow_right' (a := fibreChainConst.{u}) one_le_fibreChainConst.{u}
        (show S.card + 1 ≤ N + 2 by omega)
    · refine ENNReal.ofReal_le_ofReal ?_
      have hu0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
      have hu1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1'
      refine Real.rpow_le_rpow_of_exponent_ge hu0 hu1 ?_
      have := hηεd m
      linarith

open scoped Classical in
/-- **`le_window_maxDensity` reduced to the count of `nodesUnder b a j`** — `the estimate` item 2,
in the exact shape `isKatzTaoAtEveryScale_or_dividingWindow`'s `hwindow` hypothesis asks for. -/
theorem window_field_of_card (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ} {a b m : ℕ}
    (hdata : ∀ ρ : NNReal,
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ εd ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ εd →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ∃ (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (v₀ : ENNReal),
          volume K.carrier ≠ 0 ∧ volume K.carrier ≠ ⊤ ∧
          (∀ j' ∈ 𝒰.nodesUnder b a j,
            ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody ≤ K) ∧
          (∀ j' ∈ 𝒰.nodesUnder b a j,
            v₀ ≤ volume ((𝒰.cover.tube b j').rescale ρ).carrier) ∧
          ENNReal.ofReal
              (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
              * volume K.carrier
            ≤ Cstar * (((𝒰.nodesUnder b a j).card : ENNReal) * v₀)) :
    ∀ ρ : NNReal,
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ εd ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ εd →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
          ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder b a j)
              (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody) := by
  intro ρ h1 h2 j hj
  obtain ⟨K, v₀, hK0, hKtop, hsub, hv₀, hx⟩ := hdata ρ h1 h2 j hj
  exact le_window_maxDensity_of_card 𝒰 K hK0 hKtop hsub hv₀ hx

end WindowFromRun

section HoistedSupply

open MeasureTheory Tube

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **The payload row with the refinement hoisted above the dichotomy.** -/
def RefinedSupplyAt (β ϖ ε₁ η' : ℝ) (gain dens : ℝ → ℝ) {C : NNReal} {Kl cl : ℕ}
    (Λf A : ℝ≥0∞)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu) : Prop :=
  ∀ (S : Finset ι) (hS : S ⊆ u), S.Nonempty →
    ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S),
      ∃ (S' : Finset ι) (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (hS' : S' ⊆ S)
        (hhom : IsClassHomogeneousOn ((𝒰.restrictOccupied hS hh).retube (funext ht)) S')
        (hW : (fun i => (W i).toTube) = (fun i => (Z i).toTube)),
        (refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht)) hS' hhom hW
            ).IsKatzTaoAtEveryScale A
          ∨ (IsShadedRefinementOf ((𝒰.restrictOccupied hS hh).retube (funext ht)) Λf S Z S' W ∧
              ∃ a b m : ℕ,
                ML2Reduction.IsKatzTaoDividingWindowLevels
                  (refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht)) hS' hhom hW)
                  ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
                  (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
                  (ML2Spine.spineCount ϖ ε₁) a b m ∧
                FloorHypothesisAt β ϖ ε₁ gain dens η'
                  (refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht)) hS' hhom hW)
                  a b m)

/-- **One refinement, then the dichotomy on it** — the hoisted shape, produced. -/
theorem refinedSupplyAt_of_dichotomy {β ϖ ε₁ η' : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Λf A : ℝ≥0∞}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hstep : ∀ (S : Finset ι) (hS : S ⊆ u), S.Nonempty →
      ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S),
      ∃ (S' : Finset ι) (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (hS' : S' ⊆ S)
        (hhom : IsClassHomogeneousOn ((𝒰.restrictOccupied hS hh).retube (funext ht)) S')
        (hW : (fun i => (W i).toTube) = (fun i => (Z i).toTube)),
        IsShadedRefinementOf ((𝒰.restrictOccupied hS hh).retube (funext ht)) Λf S Z S' W ∧
          ((refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht))
                hS' hhom hW).IsKatzTaoAtEveryScale A
            ∨ ∃ a b m : ℕ,
                ML2Reduction.IsKatzTaoDividingWindowLevels
                  (refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht)) hS' hhom hW)
                  ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
                  (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
                  (ML2Spine.spineCount ϖ ε₁) a b m ∧
                FloorHypothesisAt β ϖ ε₁ gain dens η'
                  (refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht)) hS' hhom hW)
                  a b m)) :
    RefinedSupplyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf A 𝒰 := by
  intro S hS hne Z ht hh
  obtain ⟨S', W, hS', hhom, hW, href, hdich⟩ := hstep S hS hne Z ht hh
  exact ⟨S', W, hS', hhom, hW, hdich.imp id (fun h => ⟨href, h⟩)⟩

/-- **The retarget bridge**: with the every-scale side excluded, the hoisted row is the existing
`Kakeya.ML2Core.RefinedFloorSupplyAt`. -/
theorem refinedFloorSupplyAt_of_refinedSupplyAt {β ϖ ε₁ η' : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Λf A : ℝ≥0∞}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hsupply : RefinedSupplyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf A 𝒰)
    (hno : ∀ {S' : Finset ι} {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
      (V : Tube.UniformTubeSet S' (fun i => (W i).toTube) (Tube.ssfGridLen δ) Cu),
      ¬ V.IsKatzTaoAtEveryScale A) :
    RefinedFloorSupplyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf 𝒰 := by
  intro S hS hne Z ht hh
  obtain ⟨S', W, hS', hhom, hW, hdich⟩ := hsupply S hS hne Z ht hh
  rcases hdich with hev | ⟨href, a, b, m, hwin, hflo⟩
  · exact absurd hev (hno _)
  · exact ⟨a, b, m, S', W, hS', hhom, hW, href, hwin, hflo⟩

/-- **The payload, end to end**, through the hoisted row. -/
theorem floorDataAtTrichotomy_of_refinedSupplyAt {β ϖ ε₁ η' h : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Λf A : ℝ≥0∞}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hsupply : RefinedSupplyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf A 𝒰)
    (hno : ∀ {S' : Finset ι} {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
      (V : Tube.UniformTubeSet S' (fun i => (W i).toTube) (Tube.ssfGridLen δ) Cu),
      ¬ V.IsKatzTaoAtEveryScale A) :
    FloorDataAtTrichotomy (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens Λf 𝒰 :=
  floorDataAtTrichotomy_of_refinedFloorSupply
    (refinedFloorSupplyAt_of_refinedSupplyAt hsupply hno)

/-! ### Firing controls -/

/-- **Firing control: `ε_d` is load-bearing in the every-scale branch.**  Read at `ε_d = 0` the
shortness hypothesis says every piece has `b ≤ a`, which no adjacent pair of a cut set satisfies;
so the branch is not reached vacuously and the `δ^{-5ε_d}` in its constant is not decoration. -/
theorem allShort_vacuous_at_zero {δ : NNReal} {a b : ℕ} (hab : a < b)
    (hshort : (b : ℝ) - (a : ℝ) ≤ 0 * (Tube.ssfGridLen δ : ℝ)) : False := by
  have : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  simp only [zero_mul] at hshort
  linarith

/-- **Firing control: the chain's base case is load-bearing.**  `chain_le_of_submultiplicative`
reads its bound family at the degenerate pair `(0,0)`; on the fibre array that value is `≤ 1`
(`towerDensityArrayFibre_self_le_one`), and a bound family with `bnd 0 0 = 0` would make the
hypothesis unsatisfiable unless the array vanishes at `(0,0)` — recorded so that a caller cannot
supply `hbase` by accident. -/
theorem chain_base_forces_zero {Z : ℕ → ℕ → ENNReal} (hbase : Z 0 0 ≤ 0) : Z 0 0 = 0 :=
  nonpos_iff_eq_zero.mp hbase

end HoistedSupply

end Kakeya.ML2Core

end
