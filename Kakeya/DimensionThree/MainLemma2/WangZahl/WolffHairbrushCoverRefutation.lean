/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.WolffHairbrushGuardrails

/-!
# The `θ`-tube cover leaf cannot manufacture broad classes

`Kakeya.WangZahl.CappedBalancedBroadCover` (Leaf 1b of the Wang--Zahl
Proposition 1.10 decomposition) asks: given a `δ^η`-dense, Katz--Tao bounded
family that is cap-concentrated and `ν`-broad at a scale `θ ∈ [δ, 1]`, produce a
balanced cover of the family by `θ`-tubes together with per-class shadings so
that *each class is again `ν`-broad at scale `θ`*.

This file records the obstruction, and it is a *fourth* instance of the defect
class that already produced `not_balancedBroadCover` and the two repairs of
`WolffHairbrushBroad`: **the transcription kept one half of a source clause and
dropped the other.**

## The source

`blueprint/src/WZ2/250224e_K3.tex:5744-5748` says

> Furthermore, there exists a balanced partitioning cover `𝕋_θ` of `𝕋`, so that
> `|⋃_{T ∈ 𝕋} Y(T)| = ∑_{T_θ ∈ 𝕋_θ} |⋃_{T ∈ 𝕋[T_θ]} Y(T)|`.  (broadAtScaleTheta)
> After a further refinement, we may suppose that each set `𝕋^{T_θ}` is
> `δ^{3η}`-dense.  Note that `𝕋^{T_θ}` [...] satisfies the broadness condition
> [...].

and `250224e_K3.tex:928` defines *partitioning cover*: a cover in which each
`U ∈ 𝒰` lies in exactly one `𝒰[W]`.  So `broadAtScaleTheta` carries **two**
statements: the cover partitions the *tubes*, and — this is the content of the
displayed equality, not of the word "cover" — each *point* of `⋃ Y(T)` is
counted once, i.e. the tubes through a typical point are captured by a single
`θ`-tube of the cover.  The Lean transcription rendered the display as the
output inequality

`∑_j |⋃_{i ∈ part j} Y_j(i)| ≤ |⋃_{i ∈ s} Y(i)|`,

which is satisfiable by *shrinking* the shadings and therefore no longer says
that a point's tubes lie in one class.  With that clause gone, the leaf demands
per-class broadness while granting nothing that ties a point's tubes to a
single class — and it is then false.

## The obstruction

Broadness at scale `θ > δ` is a pointwise multiplicity lower bound
(`rpow_le_multiplicity_of_isBroadAtScale`): every point of every shading of a
`ν`-broad family must lie in at least `(θ/δ)^ν > 1` tubes *of its own class*.
A class of the cover, however, is a set of `δ`-tubes contained in one *unit
length* `θ`-tube (`parent j : Tube θ Space3`), so two tubes of a class have
carriers inside a common set of diameter `1 + 2θ`.  Nothing in the hypotheses
of Leaf 1b prevents the tubes through a point from having pairwise *axial*
offsets `≫ θ`: cap concentration constrains only their **directions**.  A family
in which no two tubes share a `θ`-tube therefore has only singleton classes,
and a singleton class is never broad at a scale `θ > δ`.

`not_cappedBalancedBroadCover_of_axiallySpread` is that argument.  It reduces
the refutation of Leaf 1b to the construction of one witness family, which is
`Kakeya.WangZahl.axialFamily` below.
-/

@[expose] public section

open MeasureTheory Metric

namespace Kakeya.WangZahl

noncomputable section

universe u

/-! ### A class holding at most one tube is never broad above `δ` -/

/-- **A `δ^ν`-dense family has a nonempty shading.**  `IsDense` is a statement
about the *sums*, so it does not force every shading to be nonempty; it does
force one of them to be, because a `δ`-tube has positive volume. -/
theorem exists_shade_nonempty_of_isDense {δ : NNReal} (hδ : 0 < δ) {ι : Type u}
    {s : Finset ι} {Y : ι → ShadedTube δ Space3} {c : NNReal} (hc : 0 < c)
    (hdens : IsDense s Y c) (hne : s.Nonempty) :
    ∃ i ∈ s, ((Y i).shade).Nonempty := by
  classical
  obtain ⟨i₀, hi₀⟩ := hne
  -- the carriers have positive total volume
  have hcarr : 0 < ∑ i ∈ s, volume (Y i).carrier := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun i => volume (Y i).carrier) (fun i _ => zero_le) hi₀)
    refine lt_of_lt_of_le ?_ (Tube.le_volume (Y i₀).toTube)
    have hc3 : (0 : NNReal) < Tube.le_volume.c (Module.finrank ℝ Space3) :=
      Tube.le_volume.c_pos _
    have hpow : (0 : NNReal) < δ ^ (Module.finrank ℝ Space3 - 1) := pow_pos hδ _
    exact_mod_cast mul_pos hc3 hpow
  have hpos : 0 < ∑ i ∈ s, volume (Y i).shade := by
    refine lt_of_lt_of_le ?_ hdens
    exact ENNReal.mul_pos (by exact_mod_cast hc.ne') hcarr.ne'
  -- so some shading has positive volume
  by_contra hcon
  push Not at hcon
  have : ∑ i ∈ s, volume (Y i).shade = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [hcon i hi, measure_empty]
  exact absurd this hpos.ne'

/-- **A class with at most one tube is not broad at any scale `θ > δ`**, provided
it is `δ^ν`-dense with `ν > 0`: density gives a point of a shading, and
`rpow_le_multiplicity_of_isBroadAtScale` demands `(θ/δ)^ν` tubes of the class
through that point. -/
theorem not_isBroadAtScale_of_card_le_one {δ θ : NNReal} (hδ : 0 < δ) (hδθ : δ < θ)
    {ν : ℝ} (hν : 0 < ν) {ι : Type u} {p : Finset ι} {Y : ι → ShadedTube δ Space3}
    (hcard : p.card ≤ 1) (hne : p.Nonempty) {c : NNReal} (hc : 0 < c)
    (hdens : IsDense p Y c) :
    ¬ IsBroadAtScale p Y θ ν := by
  classical
  intro hbroad
  obtain ⟨i₀, hi₀, hshade⟩ := exists_shade_nonempty_of_isDense hδ hc hdens hne
  have hkey := rpow_le_card_of_isBroadAtScale hδ hδθ.le hbroad hi₀ hshade
  have hcard' : (p.card : ENNReal) ≤ 1 := by exact_mod_cast hcard
  have hlt : (((θ / δ : NNReal)) : ENNReal) ^ ν > 1 := by
    have h1 : (1 : ENNReal) < ((θ / δ : NNReal) : ENNReal) := by
      refine ENNReal.coe_lt_coe.mpr ?_
      exact (one_lt_div hδ).mpr hδθ
    exact ENNReal.one_lt_rpow h1 hν
  exact absurd (hkey.trans hcard') (not_le.mpr hlt)

/-! ### Two tubes in a common `θ`-tube are close

A `Tube θ` has diameter at most `1 + 2θ`: its carrier is the `θ`-thickening of a
segment of length one. -/

/-- Any two points of a `θ`-tube are at distance at most `1 + 2θ`. -/
theorem Tube.dist_le_of_mem_carrier {θ : NNReal} (W : Tube θ Space3) {p q : Space3}
    (hp : p ∈ W.carrier) (hq : q ∈ W.carrier) : ‖p - q‖ ≤ 1 + 2 * (θ : ℝ) := by
  rw [W.carrier_eq] at hp hq
  obtain ⟨zp, hzp, hp'⟩ := Set.mem_iUnion₂.mp hp
  obtain ⟨zq, hzq, hq'⟩ := Set.mem_iUnion₂.mp hq
  rw [mem_closedBall] at hp' hq'
  have hzz : ‖zp - zq‖ ≤ 1 := by
    rw [segment_eq_image'] at hzp hzq
    obtain ⟨a, ha, rfl⟩ := hzp
    obtain ⟨b, hb, rfl⟩ := hzq
    have hxy : ‖W.y - W.x‖ = 1 := by
      rw [← dist_eq_norm, dist_comm]; exact W.dist_eq_one
    have hab : |a - b| ≤ 1 := by
      rw [abs_le]
      constructor <;> [linarith [ha.1, ha.2, hb.1, hb.2]; linarith [ha.1, ha.2, hb.1, hb.2]]
    calc ‖W.x + a • (W.y - W.x) - (W.x + b • (W.y - W.x))‖
        = |a - b| * ‖W.y - W.x‖ := by
          rw [show W.x + a • (W.y - W.x) - (W.x + b • (W.y - W.x))
            = (a - b) • (W.y - W.x) by module, norm_smul, Real.norm_eq_abs]
      _ ≤ 1 := by rw [hxy, mul_one]; exact hab
  calc ‖p - q‖ = ‖(p - zp) + (zp - zq) + (zq - q)‖ := by congr 1; abel
    _ ≤ ‖p - zp‖ + ‖zp - zq‖ + ‖zq - q‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ (θ : ℝ) + 1 + (θ : ℝ) := by
        gcongr
        · rw [← dist_eq_norm]; exact hp'
        · rw [← dist_eq_norm, dist_comm]; exact hq'
    _ = 1 + 2 * (θ : ℝ) := by ring

/-! ### The reduction: an axially spread family refutes Leaf 1b -/

/-- **The hypothesis bundle of `CappedBalancedBroadCover` at one pair of scales,
plus axial spread.**  The last clause is the geometric content: no `θ`-tube
holds two tubes of the family.  Cap concentration says nothing about it — it
constrains directions only. -/
def IsAxiallySpreadWitness {δ : NNReal} (θ : NNReal) {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ Space3) (η ν : ℝ) : Prop :=
  s.Nonempty ∧ IsTubeShadingFamily s T ∧
    IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ ∧
    katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η) ∧
    IsCapConcentrated s T θ ∧ IsBroadAtScale s T θ ν ∧
    (∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → ∀ W : Tube θ Space3,
      (T i).carrier ⊆ W.carrier → ¬ (T i').carrier ⊆ W.carrier)

/-- **Leaf 1b is false as stated, given one axially spread witness family per
input quality `η`.**

Every class of the produced cover sits inside a single unit-length `θ`-tube
`parent j`, so axial spread forces `#(part j) ≤ 1`; the counting conjunct forces
some class to be nonempty; and a nonempty class with at most one tube cannot
satisfy the leaf's own output conjuncts `IsDense (part j) (Y j) δ^ν` and
`IsBroadAtScale (part j) (Y j) θ ν` at `θ > δ`
(`not_isBroadAtScale_of_card_le_one`).

The witness is only needed for *one* `ε` (here `ε = 1`) and *one* `ν`, but for
every `η > 0`, because the leaf chooses `η` after seeing `ε` and `ν`. -/
theorem not_cappedBalancedBroadCover_of_axiallySpread {ν : ℝ} (hν : 0 < ν)
    (H : ∀ η : ℝ, 0 < η → η ≤ ν → ∃ (δ θ : NNReal) (ι : Type u) (s : Finset ι)
        (T : ι → ShadedTube δ Space3),
        0 < δ ∧ δ < θ ∧ θ ≤ 1 ∧ IsAxiallySpreadWitness θ s T η ν) :
    ¬ CappedBalancedBroadCover.{u} := by
  classical
  intro HB
  obtain ⟨η, hη0, hην, hbody⟩ := HB 1 one_pos ν hν
  obtain ⟨δ, θ, ι, s, T, hδ0, hδθ, hθ1, hsne, hfam, hdens, hckt, hcap, hbroad, hspread⟩ :=
    H η hη0 hην
  obtain ⟨J, P, parent, part, Y, hpart, hcount, -, -, hdensj, hbroadj, -⟩ :=
    hbody δ hδ0 θ hδθ.le hθ1 s T hfam hdens hckt hcap hbroad
  -- some class is nonempty, by the counting conjunct
  have hscard : (0 : ENNReal) < (s.card : ENNReal) := by
    exact_mod_cast Finset.card_pos.mpr hsne
  have hsum : ∃ j ∈ P, (part j).Nonempty := by
    by_contra hcon
    push Not at hcon
    have : ∑ j ∈ P, ((part j).card : ENNReal) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [hcon j hj]
      simp
    rw [this, mul_zero] at hcount
    exact absurd (le_antisymm hcount zero_le) hscard.ne'
  obtain ⟨j, hj, hjne⟩ := hsum
  -- axial spread forces the class to be a singleton
  have hsub : ∀ i ∈ part j, i ∈ s ∧ (T i).carrier ⊆ (parent j).carrier := by
    intro i hi
    have := (@Finset.mem_filter ι (fun i => (T i).carrier ⊆ (parent j).carrier)
      (Classical.decPred _) s i).mp (hpart j hj hi)
    exact this
  have hcard1 : (part j).card ≤ 1 := by
    by_contra hcon
    obtain ⟨i, hi, i', hi', hne⟩ := Finset.one_lt_card.mp (not_le.mp hcon)
    obtain ⟨his, hiW⟩ := hsub i hi
    obtain ⟨his', hiW'⟩ := hsub i' hi'
    exact hspread i his i' his' hne (parent j) hiW hiW'
  -- but a singleton class is not broad at `θ > δ`
  have hcpos : (0 : NNReal) < ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_zero]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hδ0) ν
  exact not_isBroadAtScale_of_card_le_one hδ0 hδθ hν hcard1 hjne hcpos
    (hdensj j hj) (hbroadj j hj)

/-! ### Four directions on the boundary of a `θ`-cap -/

/-- The axial component of the four witness directions. -/
def capA (θ : NNReal) : ℝ := 1 - (θ : ℝ) ^ 2 / 2

/-- The transverse component of the four witness directions. -/
def capB (θ : NNReal) : ℝ := (θ : ℝ) * Real.sqrt (1 - (θ : ℝ) ^ 2 / 4)

/-- First transverse coefficient of the `k`-th witness direction. -/
def capC : Fin 4 → ℝ := ![1, -1, 0, 0]

/-- Second transverse coefficient of the `k`-th witness direction. -/
def capS : Fin 4 → ℝ := ![0, 0, 1, -1]

/-- The four unit vectors at chordal distance exactly `θ` from `capAxis`, forming
a square inscribed in the boundary circle of the `θ`-cap. -/
def capDir (θ : NNReal) (k : Fin 4) : Space3 :=
  !₂[capA θ, capB θ * capC k, capB θ * capS k]

/-- The centre of the cap: the unit vector `v` of the source's cap clause. -/
def capAxis : Space3 := !₂[1, 0, 0]

theorem norm_coord (x y z : ℝ) : ‖(!₂[x, y, z] : Space3)‖ = Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_three, sq_abs]

theorem sub_coord (x y z x' y' z' : ℝ) :
    (!₂[x, y, z] : Space3) - !₂[x', y', z'] = !₂[x - x', y - y', z - z'] := by
  ext i; fin_cases i <;> simp

theorem add_coord (x y z x' y' z' : ℝ) :
    (!₂[x, y, z] : Space3) + !₂[x', y', z'] = !₂[x + x', y + y', z + z'] := by
  ext i; fin_cases i <;> simp

theorem norm_capAxis : ‖capAxis‖ = 1 := by
  rw [capAxis, norm_coord]; norm_num

theorem capCS_sq (k : Fin 4) : capC k ^ 2 + capS k ^ 2 = 1 := by
  fin_cases k <;> norm_num [capC, capS]

theorem sum_capC : ∑ k : Fin 4, capC k = 0 := by
  simp [Fin.sum_univ_four, capC]

theorem sum_capS : ∑ k : Fin 4, capS k = 0 := by
  simp [Fin.sum_univ_four, capS]

variable {θ : NNReal}

theorem capB_sq (hθ : (θ : ℝ) ≤ 2) : capB θ ^ 2 = (θ : ℝ) ^ 2 * (1 - (θ : ℝ) ^ 2 / 4) := by
  have hnn : (0 : ℝ) ≤ 1 - (θ : ℝ) ^ 2 / 4 := by nlinarith [θ.coe_nonneg]
  rw [capB, mul_pow, Real.sq_sqrt hnn]

theorem capA_sq_add_capB_sq (hθ : (θ : ℝ) ≤ 2) : capA θ ^ 2 + capB θ ^ 2 = 1 := by
  rw [capB_sq hθ, capA]; ring

theorem capB_nonneg : 0 ≤ capB θ :=
  mul_nonneg θ.coe_nonneg (Real.sqrt_nonneg _)

theorem capB_le (hθ : (θ : ℝ) ≤ 2) : capB θ ≤ (θ : ℝ) := by
  rw [capB]
  have h1 : Real.sqrt (1 - (θ : ℝ) ^ 2 / 4) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by nlinarith [θ.coe_nonneg])
  nlinarith [θ.coe_nonneg, Real.sqrt_nonneg (1 - (θ : ℝ) ^ 2 / 4)]

theorem le_capB (hθ : (θ : ℝ) ≤ 1) : (θ : ℝ) / 2 ≤ capB θ := by
  rw [capB]
  have h1 : Real.sqrt (3 / 4 : ℝ) ≤ Real.sqrt (1 - (θ : ℝ) ^ 2 / 4) :=
    Real.sqrt_le_sqrt (by nlinarith [θ.coe_nonneg])
  have h2 : (1 / 2 : ℝ) ≤ Real.sqrt (3 / 4) := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  nlinarith [θ.coe_nonneg]

theorem le_capA (hθ : (θ : ℝ) ≤ 1) : (1 : ℝ) / 2 ≤ capA θ := by
  rw [capA]; nlinarith [θ.coe_nonneg]

theorem capA_le_one : capA θ ≤ 1 := by
  rw [capA]; nlinarith [θ.coe_nonneg]

theorem norm_capDir (hθ : (θ : ℝ) ≤ 2) (k : Fin 4) : ‖capDir θ k‖ = 1 := by
  rw [capDir, norm_coord]
  have h : capA θ ^ 2 + (capB θ * capC k) ^ 2 + (capB θ * capS k) ^ 2 = 1 := by
    have h1 := capCS_sq k
    have h2 := capA_sq_add_capB_sq (θ := θ) hθ
    nlinarith [h1, h2]
  rw [h, Real.sqrt_one]

theorem norm_capAxis_sub_capDir (hθ : (θ : ℝ) ≤ 2) (k : Fin 4) :
    ‖capAxis - capDir θ k‖ = (θ : ℝ) := by
  rw [capAxis, capDir, sub_coord, norm_coord]
  have h : (1 - capA θ) ^ 2 + (0 - capB θ * capC k) ^ 2 + (0 - capB θ * capS k) ^ 2
      = (θ : ℝ) ^ 2 := by
    have h1 := capCS_sq k
    have h2 := capB_sq (θ := θ) hθ
    rw [capA]
    nlinarith [h1, h2]
  rw [h, Real.sqrt_sq θ.coe_nonneg]

theorem sum_capDir : ∑ k : Fin 4, capDir θ k = (4 * capA θ) • capAxis := by
  ext i
  have hsum : ∀ j : Fin 3, (∑ k : Fin 4, capDir θ k) j = ∑ k : Fin 4, (capDir θ k) j := by
    intro j; simp
  rw [hsum i]
  fin_cases i <;>
    simp [Fin.sum_univ_four, capDir, capAxis, capC, capS] <;> ring

/-- Two distinct witness directions are at distance at least `capB θ`; in fact at
least `√2 capB θ`, but `capB θ` is all the counting argument needs. -/
theorem capB_le_norm_capDir_sub (hθ : (θ : ℝ) ≤ 2) {k l : Fin 4} (hkl : k ≠ l) :
    capB θ ≤ ‖capDir θ k - capDir θ l‖ := by
  rw [capDir, capDir, sub_coord, norm_coord]
  have hcs : 1 ≤ (capC k - capC l) ^ 2 + (capS k - capS l) ^ 2 := by
    fin_cases k <;> fin_cases l <;> simp_all [capC, capS] <;> norm_num
  have hb := capB_nonneg (θ := θ)
  have h : capB θ ^ 2 ≤ (capA θ - capA θ) ^ 2 + (capB θ * capC k - capB θ * capC l) ^ 2
      + (capB θ * capS k - capB θ * capS l) ^ 2 := by
    nlinarith [sq_nonneg (capB θ), hcs]
  calc capB θ = Real.sqrt (capB θ ^ 2) := (Real.sqrt_sq hb).symm
    _ ≤ _ := Real.sqrt_le_sqrt h

/-- Two witness directions, added rather than subtracted, are far apart: this is
what excludes mixed signs in the broadness count. -/
theorem two_capA_le_norm_capDir_add (k l : Fin 4) :
    2 * capA θ ≤ ‖capDir θ k + capDir θ l‖ := by
  have h1 : ‖capDir θ k + capDir θ l‖ = Real.sqrt ((2 * capA θ) ^ 2
      + (capB θ * capC k + capB θ * capC l) ^ 2 + (capB θ * capS k + capB θ * capS l) ^ 2) := by
    rw [capDir, capDir, add_coord, norm_coord]
    congr 2
    ring
  rw [h1]
  calc 2 * capA θ ≤ |2 * capA θ| := le_abs_self _
    _ = Real.sqrt ((2 * capA θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ _ := by
        refine Real.sqrt_le_sqrt ?_
        have h2 := sq_nonneg (capB θ * capC k + capB θ * capC l)
        have h3 := sq_nonneg (capB θ * capS k + capB θ * capS l)
        nlinarith [h2, h3]

/-! ### The direction count of the witness family

`capDirCount θ w r` is the number of witness directions within chordal distance
`r` of `± w`.  The two lemmas below are the only geometric input to the
broadness verification. -/

theorem inner_ge_of_norm_sub_le {w u : Space3} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) {r : ℝ}
    (h : ‖w - u‖ ≤ r) : 1 - r ^ 2 / 2 ≤ inner ℝ w u := by
  have h1 : ‖w - u‖ ^ 2 = ‖w‖ ^ 2 - 2 * inner ℝ w u + ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, inner_sub_sub_self]
    ring_nf
    rw [real_inner_comm u w]
    ring
  have h2 : ‖w - u‖ ^ 2 ≤ r ^ 2 := by
    have := norm_nonneg (w - u)
    nlinarith
  rw [hw, hu] at h1
  nlinarith

/-- **The exact endpoint of the count: if all four directions are within `r` of
`w`, then `r ≥ θ`.**  Equivalently: the smallest cap centred at a *unit* vector
containing the four witness directions has radius exactly `θ`.  This is the
knife-edge that makes the family simultaneously cap-concentrated at `θ` and
`ν`-broad at `θ`. -/
theorem theta_le_of_forall_norm_sub_le (hθ : (θ : ℝ) ≤ 1) {w : Space3} (hw : ‖w‖ = 1)
    {r : ℝ} (h : ∀ k : Fin 4, ‖w - capDir θ k‖ ≤ r) : (θ : ℝ) ≤ r := by
  have hθ2 : (θ : ℝ) ≤ 2 := by linarith
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) (h 0)
  have hinner : ∀ k : Fin 4, 1 - r ^ 2 / 2 ≤ inner ℝ w (capDir θ k) := fun k =>
    inner_ge_of_norm_sub_le hw (norm_capDir hθ2 k) (h k)
  have hsum : (4 : ℝ) * (1 - r ^ 2 / 2) ≤ inner ℝ w (∑ k : Fin 4, capDir θ k) := by
    rw [inner_sum]
    calc (4 : ℝ) * (1 - r ^ 2 / 2) = ∑ _k : Fin 4, (1 - r ^ 2 / 2) := by
          simp [Finset.sum_const]; ring
      _ ≤ ∑ k : Fin 4, inner ℝ w (capDir θ k) := Finset.sum_le_sum fun k _ => hinner k
  rw [sum_capDir, real_inner_smul_right] at hsum
  have haxis : inner ℝ w capAxis ≤ 1 := by
    have := real_inner_le_norm w capAxis
    rw [hw, norm_capAxis] at this; linarith
  have ha0 : (0 : ℝ) ≤ 4 * capA θ := by
    have := le_capA (θ := θ) hθ; linarith
  have hstep : 4 * capA θ * inner ℝ w capAxis ≤ 4 * capA θ * 1 :=
    mul_le_mul_of_nonneg_left haxis ha0
  rw [mul_one] at hstep
  have hkey : (4 : ℝ) * (1 - r ^ 2 / 2) ≤ 4 * capA θ := le_trans hsum hstep
  rw [capA] at hkey
  nlinarith [θ.coe_nonneg]

/-- **Two directions within `r` of `±w` force `r² ≥ (3/8) θ²`.**  The mixed-sign
case is excluded outright: `‖u_k + u_l‖ ≥ 2 capA θ ≥ 1`, so it would force
`r ≥ 1/2 > θ`. -/
theorem sq_le_of_two_norm_le (hθ : (θ : ℝ) ≤ 1 / 4) {w : Space3} {r : ℝ} (hrθ : r ≤ (θ : ℝ))
    {k l : Fin 4} (hkl : k ≠ l)
    (hk : min ‖w - capDir θ k‖ ‖w + capDir θ k‖ ≤ r)
    (hl : min ‖w - capDir θ l‖ ‖w + capDir θ l‖ ≤ r) :
    (3 / 8 : ℝ) * (θ : ℝ) ^ 2 ≤ r ^ 2 := by
  have hθ1 : (θ : ℝ) ≤ 1 := by linarith
  have hθ2 : (θ : ℝ) ≤ 2 := by linarith
  have hb2 : (3 / 4 : ℝ) * (θ : ℝ) ^ 2 ≤ capB θ ^ 2 := by
    rw [capB_sq hθ2]
    have h1 : (0 : ℝ) ≤ (θ : ℝ) ^ 2 := sq_nonneg _
    have h2 : (θ : ℝ) ^ 2 ≤ 1 := by nlinarith [θ.coe_nonneg]
    nlinarith [mul_nonneg h1 (by linarith : (0 : ℝ) ≤ 1 - (θ : ℝ) ^ 2)]
  have hcs : 2 * capB θ ^ 2 ≤ ‖capDir θ k - capDir θ l‖ ^ 2 := by
    rw [capDir, capDir, sub_coord, norm_coord]
    have hcs2 : 2 ≤ (capC k - capC l) ^ 2 + (capS k - capS l) ^ 2 := by
      fin_cases k <;> fin_cases l <;> simp_all [capC, capS] <;> norm_num
    have hnn : (0 : ℝ) ≤ (capA θ - capA θ) ^ 2 + (capB θ * capC k - capB θ * capC l) ^ 2
        + (capB θ * capS k - capB θ * capS l) ^ 2 := by positivity
    rw [Real.sq_sqrt hnn]
    nlinarith [sq_nonneg (capB θ), hcs2]
  -- the mixed-sign case cannot occur
  have hmixed : ∀ m n : Fin 4, ‖w - capDir θ m‖ ≤ r → ‖w + capDir θ n‖ ≤ r → False := by
    intro m n hm hn
    have h1 : ‖capDir θ m + capDir θ n‖ ≤ 2 * r := by
      calc ‖capDir θ m + capDir θ n‖ = ‖(w + capDir θ n) - (w - capDir θ m)‖ := by
            congr 1; abel
        _ ≤ ‖w + capDir θ n‖ + ‖w - capDir θ m‖ := norm_sub_le _ _
        _ ≤ 2 * r := by linarith
    have h2 := two_capA_le_norm_capDir_add (θ := θ) m n
    have h3 := le_capA (θ := θ) hθ1
    linarith
  have hdist : ‖capDir θ k - capDir θ l‖ ≤ 2 * r := by
    rcases min_le_iff.mp hk with hk1 | hk2
    · rcases min_le_iff.mp hl with hl1 | hl2
      · calc ‖capDir θ k - capDir θ l‖ = ‖(w - capDir θ l) - (w - capDir θ k)‖ := by
              congr 1; abel
          _ ≤ ‖w - capDir θ l‖ + ‖w - capDir θ k‖ := norm_sub_le _ _
          _ ≤ 2 * r := by linarith
      · exact absurd (hmixed k l hk1 hl2) not_false
    · rcases min_le_iff.mp hl with hl1 | hl2
      · exact absurd (hmixed l k hl1 hk2) not_false
      · calc ‖capDir θ k - capDir θ l‖ = ‖(w + capDir θ k) - (w + capDir θ l)‖ := by
              congr 1; abel
          _ ≤ ‖w + capDir θ k‖ + ‖w + capDir θ l‖ := norm_sub_le _ _
          _ ≤ 2 * r := by linarith
  have hr0 : 0 ≤ r := le_trans (le_min (norm_nonneg _) (norm_nonneg _)) hk
  nlinarith [hdist, hcs, hb2, norm_nonneg (capDir θ k - capDir θ l)]

/-! ### The witness family: four `δ`-tubes with `θ = 100 δ` -/

/-- The scale of the witness: `θ = 200 δ`, truncated at `1` so that the
directions are unconditionally unit vectors. -/
def capTheta (δ : NNReal) : NNReal := min (200 * δ) 1

theorem capTheta_le_one (δ : NNReal) : (capTheta δ : ℝ) ≤ 1 := by
  rw [capTheta]
  exact_mod_cast min_le_right (200 * δ) 1

theorem capTheta_eq {δ : NNReal} (h : δ ≤ 1 / 200) : capTheta δ = 200 * δ := by
  rw [capTheta, min_eq_left]
  calc (200 : NNReal) * δ ≤ 200 * (1 / 200) := by gcongr
    _ = 1 := by rw [← NNReal.coe_inj]; push_cast; norm_num

theorem lt_capTheta {δ : NNReal} (hδ : 0 < δ) (h : δ ≤ 1 / 200) : δ < capTheta δ := by
  rw [capTheta_eq h]
  calc δ = 1 * δ := (one_mul _).symm
    _ < 200 * δ := by
        refine mul_lt_mul_of_pos_right ?_ hδ
        rw [← NNReal.coe_lt_coe]; push_cast; norm_num

/-- The `k`-th direction of the witness family. -/
def axialDir (δ : NNReal) (k : Fin 4) : Space3 := capDir (capTheta δ) k

theorem norm_axialDir (δ : NNReal) (k : Fin 4) : ‖axialDir δ k‖ = 1 :=
  norm_capDir (le_trans (capTheta_le_one δ) (by norm_num)) k

/-- The axial offsets: the origin sits at parameter `capLam k` along the `k`-th
axis, and the four offsets are `1/5` apart. -/
def capLam : Fin 4 → ℝ := ![1/10, 3/10, 5/10, 7/10]

theorem capLam_lb (k : Fin 4) : 1 / 10 ≤ capLam k := by fin_cases k <;> norm_num [capLam]

theorem capLam_ub (k : Fin 4) : capLam k ≤ 7 / 10 := by fin_cases k <;> norm_num [capLam]

theorem capLam_gap {k l : Fin 4} (hkl : k ≠ l) :
    1 / 5 ≤ |capLam k - capLam l| := by
  fin_cases k <;> fin_cases l <;> simp_all [capLam] <;> norm_num [abs_le, le_abs]

/-- The `k`-th tube of the witness family: the `δ`-tube whose axis is the unit
segment through the origin in direction `axialDir δ k`, with the origin at
parameter `capLam k`. -/
def axialTube (δ : NNReal) (k : Fin 4) : Tube δ Space3 :=
  Tube.mk' δ (x := -(capLam k) • axialDir δ k) (y := (1 - capLam k) • axialDir δ k)
    (by
      rw [dist_eq_norm,
        show -(capLam k) • axialDir δ k - (1 - capLam k) • axialDir δ k
          = -axialDir δ k by module, norm_neg]
      exact norm_axialDir δ k)

theorem axialTube_x (δ : NNReal) (k : Fin 4) :
    (axialTube δ k).x = -(capLam k) • axialDir δ k := rfl

theorem axialTube_y (δ : NNReal) (k : Fin 4) :
    (axialTube δ k).y = (1 - capLam k) • axialDir δ k := rfl

theorem direction_axialTube (δ : NNReal) (k : Fin 4) :
    (axialTube δ k).direction = axialDir δ k := by
  rw [Tube.direction, axialTube_x, axialTube_y]; module

/-- A point `t • axialDir δ k` with `|t| ≤ 1/10` lies on the `k`-th axis. -/
theorem smul_axialDir_mem_segment {δ : NNReal} {k : Fin 4} {t : ℝ} (ht : |t| ≤ 1 / 10) :
    t • axialDir δ k ∈ segment ℝ (axialTube δ k).x (axialTube δ k).y := by
  obtain ⟨ht1, ht2⟩ := abs_le.mp ht
  refine ⟨1 - t - capLam k, t + capLam k, ?_, ?_, by ring, ?_⟩
  · have := capLam_ub k; linarith
  · have := capLam_lb k; linarith
  · rw [axialTube_x, axialTube_y]; module

/-! ### The shading: one box inside all four tubes -/

/-- The axis-aligned box of half-widths `(1/1000, δ/4, δ/4)` centred at the
origin.  It is the common shading of the four tubes. -/
def capBox (δ : NNReal) : PrismNDim 3 Space3 Space3 :=
  PrismNDim.mk' (0 : Space3) (EuclideanSpace.basisFun (Fin 3) ℝ) ![1/1000, δ/4, δ/4]

theorem volume_capBox (δ : NNReal) :
    volume (capBox δ).carrier = (δ : ENNReal) ^ 2 / 2000 := by
  rw [capBox, PrismNDim.volume_carrier, finrank_euclideanSpace_fin, Fin.prod_univ_three]
  simp only [PrismNDim.thicknesses_mk', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, ENNReal.coe_div,
    ENNReal.coe_ofNat]
  have hN : (2 : NNReal) ^ 3 * ((1 / 1000) * (δ / 4) * (δ / 4)) = δ ^ 2 / 2000 := by
    rw [← NNReal.coe_inj]; push_cast; ring
  calc (2 : ENNReal) ^ 3 * (((1 / 1000 : NNReal) : ENNReal) * ((δ / 4 : NNReal) : ENNReal)
        * ((δ / 4 : NNReal) : ENNReal))
      = (((2 : NNReal) ^ 3 * ((1 / 1000) * (δ / 4) * (δ / 4)) : NNReal) : ENNReal) := by
        push_cast; ring
    _ = (((δ ^ 2 / 2000 : NNReal)) : ENNReal) := by rw [hN]
    _ = (δ : ENNReal) ^ 2 / 2000 := by
        rw [ENNReal.coe_div (by norm_num), ENNReal.coe_pow]; norm_num

theorem mem_capBox_iff {δ : NNReal} {x : Space3} :
    x ∈ (capBox δ).carrier ↔
      (|x 0| ≤ 1 / 1000 ∧ |x 1| ≤ (δ : ℝ) / 4 ∧ |x 2| ≤ (δ : ℝ) / 4) := by
  rw [capBox, PrismNDim.mem_carrier_iff]
  simp only [PrismNDim.basis_mk', PrismNDim.thicknesses_mk', PrismNDim.center_mk',
    vsub_eq_sub, sub_zero, EuclideanSpace.basisFun_repr]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have := h 0
      simp only [Matrix.cons_val_zero] at this
      push_cast at this
      linarith
    · have := h 1
      simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at this
      push_cast at this
      linarith
    · have := h 2
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        Matrix.cons_val_one, Matrix.cons_val_zero] at this
      push_cast at this
      linarith
  · intro h i
    obtain ⟨h0, h1, h2⟩ := h
    fin_cases i <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] <;> push_cast <;> [linarith; linarith; linarith]

/-- **The box lies in every tube of the family.**  A point `x` of the box is
within `δ/2` of `x₀ • capAxis` and `|x₀| ‖capAxis - axialDir δ k‖ ≤ θ/1000 = δ/5`
of the `k`-th axis. -/
theorem capBox_subset_axialTube {δ : NNReal} (hδ : δ ≤ 1 / 200) (k : Fin 4) :
    (capBox δ).carrier ⊆ (axialTube δ k).carrier := by
  intro x hx
  obtain ⟨h0, h1, h2⟩ := mem_capBox_iff.mp hx
  rw [(axialTube δ k).carrier_eq]
  refine Set.mem_biUnion (smul_axialDir_mem_segment (δ := δ) (k := k) (t := x 0)
    (le_trans h0 (by norm_num))) ?_
  rw [mem_closedBall, dist_eq_norm]
  -- split `x - x₀ • u` into a transverse part and an axial tilt
  have hsplit : x - (x 0) • axialDir δ k
      = (x - (x 0) • capAxis) - (x 0) • (axialDir δ k - capAxis) := by
    module
  have hperp : ‖x - (x 0) • capAxis‖ ≤ (δ : ℝ) / 2 := by
    have hco : x - (x 0) • capAxis = !₂[0, x 1, x 2] := by
      ext i; fin_cases i <;> simp [capAxis]
    rw [hco, norm_coord]
    have hb : (0 : ℝ) ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≤ ((δ : ℝ) / 2) ^ 2 := by
      have e1 : x 1 ^ 2 ≤ ((δ : ℝ) / 4) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have e2 : x 2 ^ 2 ≤ ((δ : ℝ) / 4) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      nlinarith [δ.coe_nonneg]
    calc Real.sqrt ((0 : ℝ) ^ 2 + x 1 ^ 2 + x 2 ^ 2)
        ≤ Real.sqrt (((δ : ℝ) / 2) ^ 2) := Real.sqrt_le_sqrt hb
      _ = (δ : ℝ) / 2 := Real.sqrt_sq (by positivity)
  have htilt : ‖(x 0) • (axialDir δ k - capAxis)‖ ≤ (δ : ℝ) / 5 := by
    rw [norm_smul, Real.norm_eq_abs, axialDir,
      show capDir (capTheta δ) k - capAxis = -(capAxis - capDir (capTheta δ) k) by module,
      norm_neg, norm_capAxis_sub_capDir (le_trans (capTheta_le_one δ) (by norm_num)) k,
      capTheta_eq hδ]
    have : ((200 * δ : NNReal) : ℝ) = 200 * (δ : ℝ) := by push_cast; ring
    rw [this]
    calc |x 0| * (200 * (δ : ℝ)) ≤ (1 / 1000) * (200 * (δ : ℝ)) := by
          have := δ.coe_nonneg; nlinarith [abs_nonneg (x 0)]
      _ = (δ : ℝ) / 5 := by ring
  calc ‖x - (x 0) • axialDir δ k‖
      = ‖(x - (x 0) • capAxis) - (x 0) • (axialDir δ k - capAxis)‖ := by rw [hsplit]
    _ ≤ ‖x - (x 0) • capAxis‖ + ‖(x 0) • (axialDir δ k - capAxis)‖ := norm_sub_le _ _
    _ ≤ (δ : ℝ) / 2 + (δ : ℝ) / 5 := by gcongr
    _ ≤ (δ : ℝ) := by have := δ.coe_nonneg; linarith

/-! ### The witness family as a shaded family -/

/-- **The witness family.**  Four `δ`-tubes with concurrent axes, directions the
four `capDir`s at `θ = 200δ`, axial offsets `1/5` apart, and all four shaded by
the same box.  The shading is intersected with the carrier so that the
definition needs no smallness hypothesis; `shade_axialFamily` identifies it with
the box for `δ ≤ 1/200`. -/
def axialFamily (δ : NNReal) : ULift.{u} (Fin 4) → ShadedTube δ Space3 := fun i =>
  { toTube := axialTube δ i.down
    shade := (capBox δ).carrier ∩ (axialTube δ i.down).carrier
    measurableSet_shade :=
      ((capBox δ).measurableSet_carrier).inter
        (axialTube δ i.down).isCompact.isClosed.measurableSet
    shade_subset := Set.inter_subset_right }

theorem carrier_axialFamily (δ : NNReal) (i : ULift.{u} (Fin 4)) :
    (axialFamily.{u} δ i).carrier = (axialTube δ i.down).carrier := rfl

theorem direction_axialFamily (δ : NNReal) (i : ULift.{u} (Fin 4)) :
    (axialFamily.{u} δ i).toTube.direction = axialDir δ i.down :=
  direction_axialTube δ i.down

theorem shade_axialFamily {δ : NNReal} (hδ : δ ≤ 1 / 200) (i : ULift.{u} (Fin 4)) :
    (axialFamily.{u} δ i).shade = (capBox δ).carrier :=
  Set.inter_eq_left.mpr (capBox_subset_axialTube hδ i.down)

/-! ### Cap concentration holds with equality -/

/-- **The family is cap-concentrated at `θ`**, with `v = capAxis` for every point
and with equality in every instance: `‖capAxis - capDir θ k‖ = θ`. -/
theorem isCapConcentrated_axialFamily (δ : NNReal) :
    IsCapConcentrated (Finset.univ : Finset (ULift.{u} (Fin 4))) (axialFamily.{u} δ)
      (capTheta δ) := by
  intro x
  refine ⟨capAxis, norm_capAxis, fun i _ _ => ?_⟩
  rw [direction_axialFamily]
  refine le_trans (min_le_left _ _) (le_of_eq ?_)
  exact norm_capAxis_sub_capDir (le_trans (capTheta_le_one δ) (by norm_num)) i.down

/-! ### No `θ`-tube holds two tubes of the family -/

theorem x_mem_carrier {δ : NNReal} (hδ : 0 < δ) (T : Tube δ Space3) : T.x ∈ T.carrier := by
  rw [T.carrier_eq]
  exact Set.mem_iUnion₂.mpr ⟨T.x, left_mem_segment ℝ T.x T.y,
    Metric.mem_closedBall_self (NNReal.coe_pos.mpr hδ).le⟩

theorem y_mem_carrier {δ : NNReal} (hδ : 0 < δ) (T : Tube δ Space3) : T.y ∈ T.carrier := by
  rw [T.carrier_eq]
  exact Set.mem_iUnion₂.mpr ⟨T.y, right_mem_segment ℝ T.x T.y,
    Metric.mem_closedBall_self (NNReal.coe_pos.mpr hδ).le⟩

/-- The far end of the `k`-th tube and the near end of the `l`-th tube are at
distance more than `1 + 2θ` when `capLam k < capLam l`: the axial offsets are
`≥ 1/5` apart while the directions differ by at most `2θ = 400δ`. -/
theorem lt_dist_endpoints {δ : NNReal} (hδ : δ ≤ 1 / 4000) {k l : Fin 4}
    (hlt : capLam k < capLam l) :
    1 + 2 * (capTheta δ : ℝ) < ‖(axialTube δ k).y - (axialTube δ l).x‖ := by
  have hδ200 : δ ≤ 1 / 200 := le_trans hδ (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have hθ : (capTheta δ : ℝ) = 200 * (δ : ℝ) := by
    rw [capTheta_eq hδ200]; push_cast; ring
  have hgap : 1 / 5 ≤ capLam l - capLam k := by
    have := capLam_gap (k := k) (l := l) (by
      intro h; rw [h] at hlt; exact absurd hlt (lt_irrefl _))
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ capLam l - capLam k)] at this
    linarith
  have hdirdist : ‖axialDir δ k - axialDir δ l‖ ≤ 2 * (capTheta δ : ℝ) := by
    calc ‖axialDir δ k - axialDir δ l‖
        = ‖(axialDir δ k - capAxis) - (axialDir δ l - capAxis)‖ := by congr 1; abel
      _ ≤ ‖axialDir δ k - capAxis‖ + ‖axialDir δ l - capAxis‖ := norm_sub_le _ _
      _ = 2 * (capTheta δ : ℝ) := by
          have hk : ‖axialDir δ k - capAxis‖ = (capTheta δ : ℝ) := by
            rw [axialDir, show capDir (capTheta δ) k - capAxis
              = -(capAxis - capDir (capTheta δ) k) by module, norm_neg]
            exact norm_capAxis_sub_capDir (le_trans (capTheta_le_one δ) (by norm_num)) k
          have hl : ‖axialDir δ l - capAxis‖ = (capTheta δ : ℝ) := by
            rw [axialDir, show capDir (capTheta δ) l - capAxis
              = -(capAxis - capDir (capTheta δ) l) by module, norm_neg]
            exact norm_capAxis_sub_capDir (le_trans (capTheta_le_one δ) (by norm_num)) l
          rw [hk, hl]; ring
  have hlb : (1 - capLam k) + capLam l - capLam l * (2 * (capTheta δ : ℝ))
      ≤ ‖(axialTube δ k).y - (axialTube δ l).x‖ := by
    rw [axialTube_y, axialTube_x]
    have hrw : (1 - capLam k) • axialDir δ k - -(capLam l) • axialDir δ l
        = ((1 - capLam k) + capLam l) • axialDir δ k
          - capLam l • (axialDir δ k - axialDir δ l) := by module
    rw [hrw]
    have h1 : ‖((1 - capLam k) + capLam l) • axialDir δ k‖ = (1 - capLam k) + capLam l := by
      rw [norm_smul, Real.norm_eq_abs, norm_axialDir, mul_one, abs_of_nonneg]
      have := capLam_ub k; have := capLam_lb l; linarith
    have h2 : ‖capLam l • (axialDir δ k - axialDir δ l)‖
        ≤ capLam l * (2 * (capTheta δ : ℝ)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [capLam_lb l])]
      exact mul_le_mul_of_nonneg_left hdirdist (by linarith [capLam_lb l])
    calc (1 - capLam k) + capLam l - capLam l * (2 * (capTheta δ : ℝ))
        ≤ ‖((1 - capLam k) + capLam l) • axialDir δ k‖
            - ‖capLam l • (axialDir δ k - axialDir δ l)‖ := by rw [h1]; linarith
      _ ≤ _ := norm_sub_norm_le _ _
  refine lt_of_lt_of_le ?_ hlb
  have hl7 := capLam_ub l
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hδ' : (δ : ℝ) ≤ 1 / 4000 := by
    have := NNReal.coe_le_coe.mpr hδ; push_cast at this; linarith
  rw [hθ]
  nlinarith [hgap, hl7, hδ0, hδ']

/-- **No `θ`-tube contains two tubes of the family.**  A `Tube θ` has diameter
`1 + 2θ`, and two tubes of the family have endpoints further apart than that. -/
theorem not_common_parent_axialFamily {δ : NNReal} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4000)
    (i : ULift.{u} (Fin 4)) (_ : i ∈ (Finset.univ : Finset (ULift.{u} (Fin 4))))
    (i' : ULift.{u} (Fin 4)) (_ : i' ∈ (Finset.univ : Finset (ULift.{u} (Fin 4))))
    (hne : i ≠ i') (W : Tube (capTheta δ) Space3)
    (hi : (axialFamily.{u} δ i).carrier ⊆ W.carrier) :
    ¬ (axialFamily.{u} δ i').carrier ⊆ W.carrier := by
  intro hi'
  have hdown : i.down ≠ i'.down := fun h => hne (by cases i; cases i'; simpa using h)
  have hlam : capLam i.down ≠ capLam i'.down := by
    intro h
    have := capLam_gap (k := i.down) (l := i'.down) hdown
    rw [h] at this
    simp at this
    linarith
  rw [carrier_axialFamily] at hi hi'
  rcases lt_or_gt_of_ne hlam with hlt | hlt
  · have h1 : (axialTube δ i.down).y ∈ W.carrier := hi (y_mem_carrier hδ0 _)
    have h2 : (axialTube δ i'.down).x ∈ W.carrier := hi' (x_mem_carrier hδ0 _)
    exact absurd (Tube.dist_le_of_mem_carrier W h1 h2)
      (not_le.mpr (lt_dist_endpoints hδ hlt))
  · have h1 : (axialTube δ i'.down).y ∈ W.carrier := hi' (y_mem_carrier hδ0 _)
    have h2 : (axialTube δ i.down).x ∈ W.carrier := hi (x_mem_carrier hδ0 _)
    exact absurd (Tube.dist_le_of_mem_carrier W h1 h2)
      (not_le.mpr (lt_dist_endpoints hδ hlt))

/-! ### Broadness of the witness family at quality `1/4` -/

variable {θ : NNReal}

/-- Mixed signs are impossible in the direction count: `‖u_m + u_n‖ ≥ 2 capA θ ≥ 1`
would force `r ≥ 1/2 > θ`. -/
theorem no_mixed_signs (hθ : (θ : ℝ) ≤ 1 / 4) {w : Space3} {r : ℝ} (hrθ : r ≤ (θ : ℝ))
    {m n : Fin 4} (hm : ‖w - capDir θ m‖ ≤ r) (hn : ‖w + capDir θ n‖ ≤ r) : False := by
  have h1 : ‖capDir θ m + capDir θ n‖ ≤ 2 * r := by
    calc ‖capDir θ m + capDir θ n‖ = ‖(w + capDir θ n) - (w - capDir θ m)‖ := by
          congr 1; abel
      _ ≤ ‖w + capDir θ n‖ + ‖w - capDir θ m‖ := norm_sub_le _ _
      _ ≤ 2 * r := by linarith
  have h2 := two_capA_le_norm_capDir_add (θ := θ) m n
  have h3 := le_capA (θ := θ) (by linarith : (θ : ℝ) ≤ 1)
  linarith

/-- **If all four directions are within `r` of `±w`, then `r ≥ θ`.**  The signs
must agree (`no_mixed_signs`), and then `theta_le_of_forall_norm_sub_le` applies
to `w` or to `-w`. -/
theorem theta_le_of_four_min (hθ : (θ : ℝ) ≤ 1 / 4) {w : Space3} (hw : ‖w‖ = 1) {r : ℝ}
    (hrθ : r ≤ (θ : ℝ))
    (h : ∀ k : Fin 4, min ‖w - capDir θ k‖ ‖w + capDir θ k‖ ≤ r) : (θ : ℝ) ≤ r := by
  have hθ1 : (θ : ℝ) ≤ 1 := by linarith
  rcases min_le_iff.mp (h 0) with h0 | h0
  · refine theta_le_of_forall_norm_sub_le hθ1 hw (fun k => ?_)
    rcases min_le_iff.mp (h k) with hk | hk
    · exact hk
    · exact absurd (no_mixed_signs hθ hrθ h0 hk) not_false
  · have hwneg : ‖-w‖ = 1 := by rw [norm_neg]; exact hw
    refine theta_le_of_forall_norm_sub_le hθ1 hwneg (fun k => ?_)
    rw [show -w - capDir θ k = -(w + capDir θ k) by module, norm_neg]
    rcases min_le_iff.mp (h k) with hk | hk
    · exact absurd (no_mixed_signs hθ hrθ hk h0) not_false
    · exact hk

/-! ### The `ENNReal` arithmetic of the count -/

theorem le_rpow_quarter {c q : ENNReal} (h : c ^ (4 : ℕ) ≤ q) : c ≤ q ^ (1 / 4 : ℝ) := by
  have h1 : (c ^ (4 : ℕ)) ^ (1 / 4 : ℝ) ≤ q ^ (1 / 4 : ℝ) :=
    ENNReal.rpow_le_rpow h (by norm_num)
  rw [← ENNReal.rpow_natCast c 4, ← ENNReal.rpow_mul] at h1
  norm_num at h1
  exact h1

theorem count_le_of_rpow {m : ℕ} {c q : ENNReal} (hc4 : c ^ (4 : ℕ) ≤ q)
    (hm : (m : ENNReal) ≤ 4 * c) : (m : ENNReal) ≤ q ^ (1 / 4 : ℝ) * 4 := by
  refine hm.trans ?_
  rw [mul_comm]
  exact mul_le_mul_right' (le_rpow_quarter hc4) 4

/-- The `NNReal` form of the ratio bound: `c⁴ θ ≤ r` gives `c⁴ ≤ r/θ`. -/
theorem pow_le_div {c r : NNReal} (hθ : 0 < θ) (h : c ^ 4 * θ ≤ r) :
    ((c : ENNReal)) ^ (4 : ℕ) ≤ ((r / θ : NNReal) : ENNReal) := by
  rw [← ENNReal.coe_pow]
  refine ENNReal.coe_le_coe.mpr ?_
  exact (le_div_iff₀ hθ).mpr h

/-- **The witness family is `1/4`-broad at scale `θ = 200 δ`.**

At a point of the box all four tubes are shaded, so the reference count is `4`,
and the requirement `#F ≤ 4 (r/θ)^{1/4}` reads `r/θ ≥ (#F/4)^4`.  The four cases:

* `#F ≤ 1`: `r ≥ δ = θ/200 ≥ θ/256 = (1/4)^4 θ`;
* `2 ≤ #F ≤ 3`: `sq_le_of_two_norm_le` gives `r² ≥ (3/8)θ²`, so
  `r ≥ (81/256) θ = (3/4)^4 θ`;
* `#F = 4`: `theta_le_of_four_min` gives `r ≥ θ`, the exact endpoint.

Off the box no tube is shaded and both counts are `0`. -/
theorem isBroadAtScale_axialFamily {δ : NNReal} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4000) :
    IsBroadAtScale (Finset.univ : Finset (ULift.{u} (Fin 4))) (axialFamily.{u} δ)
      (capTheta δ) (1 / 4) := by
  classical
  intro x w hw r hrδ hrθ
  have hδ200 : δ ≤ 1 / 200 := le_trans hδ (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have hδR : (δ : ℝ) ≤ 1 / 4000 := by
    have := NNReal.coe_le_coe.mpr hδ; push_cast at this; linarith
  have hθeq : ((capTheta δ : NNReal) : ℝ) = 200 * (δ : ℝ) := by
    rw [capTheta_eq hδ200]; push_cast; ring
  have hθ0 : 0 < capTheta δ := lt_of_lt_of_le hδ0 (lt_capTheta hδ0 hδ200).le
  have hθ4 : ((capTheta δ : NNReal) : ℝ) ≤ 1 / 4 := by rw [hθeq]; linarith
  have hrθR : (r : ℝ) ≤ ((capTheta δ : NNReal) : ℝ) := by exact_mod_cast hrθ
  have hrδR : (δ : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrδ
  set T := axialFamily.{u} δ with hT
  set F := @Finset.filter (ULift.{u} (Fin 4))
    (fun i => x ∈ (T i).shade ∧
      min ‖w - (T i).toTube.direction‖ ‖w + (T i).toTube.direction‖ ≤ (r : ℝ))
    (Classical.decPred _) Finset.univ with hF
  set G := @Finset.filter (ULift.{u} (Fin 4)) (fun i => x ∈ (T i).shade)
    (Classical.decPred _) Finset.univ with hG
  -- membership in `F` gives the direction condition
  have hFmin : ∀ i ∈ F, min ‖w - capDir (capTheta δ) i.down‖ ‖w + capDir (capTheta δ) i.down‖
      ≤ (r : ℝ) := by
    intro i hi
    have := ((@Finset.mem_filter (ULift.{u} (Fin 4)) _ (Classical.decPred _) _ i).mp hi).2.2
    rwa [direction_axialFamily, axialDir] at this
  by_cases hx : x ∈ (capBox δ).carrier
  · -- all four tubes are shaded at `x`
    have hGuniv : G = Finset.univ := by
      refine Finset.eq_univ_of_forall fun i => ?_
      refine (@Finset.mem_filter (ULift.{u} (Fin 4)) _ (Classical.decPred _) _ i).mpr
        ⟨Finset.mem_univ _, ?_⟩
      rw [hT, shade_axialFamily hδ200]
      exact hx
    have hGcard : ((G.card : ENNReal)) = 4 := by
      rw [hGuniv]; simp
    rw [hGcard]
    have hFsub : F ⊆ Finset.univ := Finset.subset_univ _
    have hFle : F.card ≤ 4 := by
      have := Finset.card_le_card hFsub
      simpa using this
    rcases le_or_gt F.card 1 with hcase1 | hcase2
    · -- `#F ≤ 1`
      refine count_le_of_rpow (c := ((1 / 4 : NNReal) : ENNReal)) ?_ ?_
      · refine pow_le_div hθ0 ?_
        rw [← NNReal.coe_le_coe]
        push_cast
        rw [hθeq]
        linarith
      · calc ((F.card : ENNReal)) ≤ 1 := by exact_mod_cast hcase1
          _ = 4 * ((1 / 4 : NNReal) : ENNReal) := by
              rw [show (4 : ENNReal) = ((4 : NNReal) : ENNReal) by simp, ← ENNReal.coe_mul,
                show (4 : NNReal) * (1 / 4) = 1 by
                  rw [← NNReal.coe_inj]; push_cast; norm_num]
              simp
    · -- two distinct members: `r² ≥ (3/8) θ²`
      obtain ⟨i, hi, i', hi', hne⟩ := Finset.one_lt_card.mp hcase2
      have hdown : i.down ≠ i'.down := fun h => hne (by cases i; cases i'; simpa using h)
      have hsq := sq_le_of_two_norm_le (θ := capTheta δ) hθ4 hrθR hdown
        (hFmin i hi) (hFmin i' hi')
      have hr0 : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
      have hbig : (81 / 256 : ℝ) * ((capTheta δ : NNReal) : ℝ) ≤ (r : ℝ) := by
        nlinarith [hsq, hr0, (capTheta δ).coe_nonneg]
      rcases eq_or_lt_of_le hFle with hcase4 | hcase3
      · -- `#F = 4`: all four directions are within `r` of `± w`
        have hFuniv : F = Finset.univ :=
          Finset.eq_of_subset_of_card_le hFsub (by
            rw [hcase4]; simp)
        have hall : ∀ k : Fin 4,
            min ‖w - capDir (capTheta δ) k‖ ‖w + capDir (capTheta δ) k‖ ≤ (r : ℝ) := by
          intro k
          exact hFmin ⟨k⟩ (by rw [hFuniv]; exact Finset.mem_univ _)
        have hrge := theta_le_of_four_min (θ := capTheta δ) hθ4 hw hrθR hall
        refine count_le_of_rpow (c := ((1 : NNReal) : ENNReal)) ?_ ?_
        · refine pow_le_div hθ0 ?_
          rw [← NNReal.coe_le_coe]
          push_cast
          linarith
        · simp [hcase4]
      · -- `#F ≤ 3`
        refine count_le_of_rpow (c := ((3 / 4 : NNReal) : ENNReal)) ?_ ?_
        · refine pow_le_div hθ0 ?_
          rw [← NNReal.coe_le_coe]
          push_cast
          linarith
        · have h3 : F.card ≤ 3 := by omega
          calc ((F.card : ENNReal)) ≤ 3 := by exact_mod_cast h3
            _ = 4 * ((3 / 4 : NNReal) : ENNReal) := by
                rw [show (4 : ENNReal) = ((4 : NNReal) : ENNReal) by simp, ← ENNReal.coe_mul,
                  show (4 : NNReal) * (3 / 4) = 3 by
                    rw [← NNReal.coe_inj]; push_cast; norm_num]
                simp
  · -- off the box nothing is shaded
    have hFempty : F = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
      have := ((@Finset.mem_filter (ULift.{u} (Fin 4)) _ (Classical.decPred _) _ i).mp hi).2.1
      rw [hT, shade_axialFamily hδ200] at this
      exact hx this
    rw [hFempty]
    simp

/-! ### Essential distinctness of the four tubes -/

theorem abs_coord_le_norm (x : Space3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x i
  simpa using this

theorem sq_add_sq_le_norm_sq (x : Space3) : x 1 ^ 2 + x 2 ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg (x 0)]

/-- Every point of the `k`-th axis is `t • axialDir δ k` for `t ∈ [-λ_k, 1-λ_k]`. -/
theorem exists_param_of_mem_segment {δ : NNReal} {k : Fin 4} {z : Space3}
    (hz : z ∈ segment ℝ (axialTube δ k).x (axialTube δ k).y) :
    ∃ t : ℝ, -capLam k ≤ t ∧ t ≤ 1 - capLam k ∧ z = t • axialDir δ k := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hsum, hz⟩ := hz
  refine ⟨c₂ - capLam k, by linarith, by linarith, ?_⟩
  rw [← hz, axialTube_x, axialTube_y, show c₁ = 1 - c₂ by linarith]
  module

/-- A point of the `k`-th tube is within `δ` of `t • axialDir δ k` for some
admissible `t`. -/
theorem exists_param_of_mem_axialTube {δ : NNReal} {k : Fin 4} {x : Space3}
    (hx : x ∈ (axialTube δ k).carrier) :
    ∃ t : ℝ, |t| ≤ 9 / 10 ∧ ‖x - t • axialDir δ k‖ ≤ (δ : ℝ) := by
  rw [(axialTube δ k).carrier_eq] at hx
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨t, ht1, ht2, rfl⟩ := exists_param_of_mem_segment hz
  refine ⟨t, ?_, ?_⟩
  · rw [abs_le]
    have := capLam_lb k; have := capLam_ub k
    constructor <;> linarith
  · rw [mem_closedBall, dist_eq_norm] at hxz
    exact hxz

/-- The algebraic separation of the four transverse coefficient pairs. -/
theorem sq_le_transverse (t s : ℝ) {k l : Fin 4} (hkl : k ≠ l) :
    t ^ 2 ≤ (t * capC k - s * capC l) ^ 2 + (t * capS k - s * capS l) ^ 2 + (t - s) ^ 2 := by
  fin_cases k <;> fin_cases l <;> simp_all [capC, capS] <;>
    nlinarith [sq_nonneg (t - s), sq_nonneg (t + s), sq_nonneg s, sq_nonneg t]

/-- **The arithmetic of the parameter bound**, in abstract reals: `A ≈ capA θ`,
`B ≈ capB θ`, `D = δ`, `u = P² + Q²` the transverse discrepancy. -/
theorem param_arith {A B D t s u : ℝ} (hD0 : 0 < D) (hD : D ≤ 1 / 4000)
    (hA : 998 / 1000 ≤ A) (hBub : B ≤ 200 * D) (hBlb : 199 * D ≤ B)
    (haxial : A * |t - s| ≤ 2 * D) (hsq : t ^ 2 ≤ u + (t - s) ^ 2)
    (hu : B ^ 2 * u ≤ 4 * D ^ 2) :
    B * |t| ≤ 201 / 100 * D ∧ |t| ≤ 104 / 10000 := by
  have hB0 : 0 < B := by linarith
  have hts : |t - s| ≤ 201 / 100 * D := by
    nlinarith [abs_nonneg (t - s), haxial, hA, hD0]
  have hD2 : D ^ 2 ≤ D / 4000 := by nlinarith [hD0, hD]
  have hprod : B * |t - s| ≤ D / 9 := by
    have h1 : B * |t - s| ≤ (200 * D) * (201 / 100 * D) :=
      mul_le_mul hBub hts (abs_nonneg _) (by linarith)
    have h2 : (200 * D) * (201 / 100 * D) = 402 * D ^ 2 := by ring
    rw [h2] at h1
    nlinarith [h1, hD2, hD0]
  have hlast : B ^ 2 * (t - s) ^ 2 ≤ D ^ 2 / 50 := by
    have habs : B ^ 2 * (t - s) ^ 2 = (B * |t - s|) ^ 2 := by
      rw [mul_pow, sq_abs]
    rw [habs]
    nlinarith [hprod, mul_nonneg hB0.le (abs_nonneg (t - s)), hD0]
  have hkey : (B * |t|) ^ 2 ≤ (201 / 100 * D) ^ 2 := by
    have hexp : (B * |t|) ^ 2 = B ^ 2 * t ^ 2 := by rw [mul_pow, sq_abs]
    have hstep : B ^ 2 * t ^ 2 ≤ B ^ 2 * u + B ^ 2 * (t - s) ^ 2 := by
      have : B ^ 2 * u + B ^ 2 * (t - s) ^ 2 = B ^ 2 * (u + (t - s) ^ 2) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    have hval : (201 / 100 * D) ^ 2 = 40401 / 10000 * D ^ 2 := by ring
    rw [hexp, hval]
    linarith [hstep, hu, hlast, sq_nonneg D]
  have hb3 : B * |t| ≤ 201 / 100 * D := by
    nlinarith [hkey, mul_nonneg hB0.le (abs_nonneg t), hD0]
  refine ⟨hb3, ?_⟩
  have h1 : 199 * D * |t| ≤ 201 / 100 * D :=
    le_trans (mul_le_mul_of_nonneg_right hBlb (abs_nonneg t)) hb3
  nlinarith [h1, hD0, abs_nonneg t]

/-- **The parameter of a common point is small.**  If `x` lies in both the `k`-th
and the `l`-th tube, its parameter `t` along the `k`-th axis satisfies
`capB θ |t| ≤ 2.01 δ` and `|t| ≤ 0.0104`: the two axes separate at rate
`≥ capB θ ≈ 200 δ`, so they run within `2δ` of each other only near the origin. -/
theorem param_small {δ : NNReal} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4000) {k l : Fin 4}
    (hkl : k ≠ l) {x : Space3} (hk : x ∈ (axialTube δ k).carrier)
    (hl : x ∈ (axialTube δ l).carrier) :
    ∃ t : ℝ, |t| ≤ 104 / 10000 ∧ capB (capTheta δ) * |t| ≤ 201 / 100 * (δ : ℝ) ∧
      ‖x - t • axialDir δ k‖ ≤ (δ : ℝ) := by
  obtain ⟨t, ht1, hxt⟩ := exists_param_of_mem_axialTube hk
  obtain ⟨s, hs1, hxs⟩ := exists_param_of_mem_axialTube hl
  have hδR : (δ : ℝ) ≤ 1 / 4000 := by
    have := NNReal.coe_le_coe.mpr hδ; push_cast at this; linarith
  have hδ0R : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ0
  have hδ200 : δ ≤ 1 / 200 := le_trans hδ (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have hθeq : ((capTheta δ : NNReal) : ℝ) = 200 * (δ : ℝ) := by
    rw [capTheta_eq hδ200]; push_cast; ring
  have hθ1 : ((capTheta δ : NNReal) : ℝ) ≤ 1 := capTheta_le_one δ
  -- the two nearest points on the axes are within `2δ`
  have hclose : ‖t • axialDir δ k - s • axialDir δ l‖ ≤ 2 * (δ : ℝ) := by
    calc ‖t • axialDir δ k - s • axialDir δ l‖
        = ‖(x - s • axialDir δ l) - (x - t • axialDir δ k)‖ := by congr 1; abel
      _ ≤ ‖x - s • axialDir δ l‖ + ‖x - t • axialDir δ k‖ := norm_sub_le _ _
      _ ≤ 2 * (δ : ℝ) := by linarith
  have hcoord : t • axialDir δ k - s • axialDir δ l
      = !₂[capA (capTheta δ) * (t - s),
           capB (capTheta δ) * (t * capC k - s * capC l),
           capB (capTheta δ) * (t * capS k - s * capS l)] := by
    ext i
    fin_cases i <;> simp [axialDir, capDir] <;> ring
  have hc0 : (t • axialDir δ k - s • axialDir δ l) 0 = capA (capTheta δ) * (t - s) := by
    rw [hcoord]; simp
  have hc1 : (t • axialDir δ k - s • axialDir δ l) 1
      = capB (capTheta δ) * (t * capC k - s * capC l) := by rw [hcoord]; simp
  have hc2 : (t • axialDir δ k - s • axialDir δ l) 2
      = capB (capTheta δ) * (t * capS k - s * capS l) := by rw [hcoord]; simp
  -- the axial coordinate
  have haxial : capA (capTheta δ) * |t - s| ≤ 2 * (δ : ℝ) := by
    have hA0 : (0 : ℝ) ≤ capA (capTheta δ) := by
      have := le_capA (θ := capTheta δ) hθ1; linarith
    have h1 : |capA (capTheta δ) * (t - s)| ≤ 2 * (δ : ℝ) := by
      rw [← hc0]
      exact le_trans (abs_coord_le_norm _ 0) hclose
    rw [abs_mul, abs_of_nonneg hA0] at h1
    exact h1
  -- the transverse coordinates
  have hu : capB (capTheta δ) ^ 2 *
      ((t * capC k - s * capC l) ^ 2 + (t * capS k - s * capS l) ^ 2) ≤ 4 * (δ : ℝ) ^ 2 := by
    have h1 := sq_add_sq_le_norm_sq (t • axialDir δ k - s • axialDir δ l)
    rw [hc1, hc2] at h1
    have hnormsq : ‖t • axialDir δ k - s • axialDir δ l‖ ^ 2 ≤ 4 * (δ : ℝ) ^ 2 := by
      nlinarith [hclose, norm_nonneg (t • axialDir δ k - s • axialDir δ l), hδ0R]
    have hexp : capB (capTheta δ) ^ 2 *
        ((t * capC k - s * capC l) ^ 2 + (t * capS k - s * capS l) ^ 2)
        = (capB (capTheta δ) * (t * capC k - s * capC l)) ^ 2
          + (capB (capTheta δ) * (t * capS k - s * capS l)) ^ 2 := by ring
    rw [hexp]
    linarith
  -- the bounds on `capA` and `capB`
  have haA : (998 : ℝ) / 1000 ≤ capA (capTheta δ) := by
    rw [capA, hθeq]; nlinarith [hδ0R, hδR]
  have hbub : capB (capTheta δ) ≤ 200 * (δ : ℝ) := by
    rw [← hθeq]; exact capB_le (by linarith)
  have hblb : (199 : ℝ) * (δ : ℝ) ≤ capB (capTheta δ) := by
    have h1 : capB (capTheta δ) ^ 2
        = ((capTheta δ : NNReal) : ℝ) ^ 2 * (1 - ((capTheta δ : NNReal) : ℝ) ^ 2 / 4) :=
      capB_sq (by linarith)
    have h2 : (0 : ℝ) ≤ capB (capTheta δ) := capB_nonneg
    rw [hθeq] at h1
    have hD2 : (δ : ℝ) ^ 2 ≤ (δ : ℝ) / 4000 := by nlinarith [hδ0R, hδR]
    have hb2 : (199 * (δ : ℝ)) ^ 2 ≤ capB (capTheta δ) ^ 2 := by
      rw [h1]; nlinarith [hδ0R, hD2]
    by_contra hcon
    push Not at hcon
    have : capB (capTheta δ) ^ 2 < (199 * (δ : ℝ)) ^ 2 := by nlinarith [h2, hcon, hδ0R]
    linarith
  obtain ⟨hb3, htle⟩ := param_arith hδ0R hδR haA hbub hblb haxial
    (sq_le_transverse t s hkl) hu
  exact ⟨t, htle, hb3, hxt⟩

/-! ### Axis-aligned coordinate boxes -/

/-- The axis-aligned box of half-widths `h` centred at the origin. -/
def coordBox (h : Fin 3 → NNReal) : PrismNDim 3 Space3 Space3 :=
  PrismNDim.mk' (0 : Space3) (EuclideanSpace.basisFun (Fin 3) ℝ) h

theorem mem_coordBox {h : Fin 3 → NNReal} {x : Space3} (hx : ∀ i, |x i| ≤ (h i : ℝ)) :
    x ∈ (coordBox h).carrier := by
  rw [coordBox, PrismNDim.mem_carrier_iff]
  simp only [PrismNDim.basis_mk', PrismNDim.thicknesses_mk', PrismNDim.center_mk',
    vsub_eq_sub, sub_zero, EuclideanSpace.basisFun_repr]
  exact hx

theorem mem_coordBox₃ {a b c : NNReal} {x : Space3} (h0 : |x 0| ≤ (a : ℝ))
    (h1 : |x 1| ≤ (b : ℝ)) (h2 : |x 2| ≤ (c : ℝ)) :
    x ∈ (coordBox ![a, b, c]).carrier := by
  refine mem_coordBox (fun i => ?_)
  fin_cases i <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] <;> [exact h0; exact h1; exact h2]

theorem coordBox₃_bounds {a b c : NNReal} {x : Space3}
    (hx : x ∈ (coordBox ![a, b, c]).carrier) :
    |x 0| ≤ (a : ℝ) ∧ |x 1| ≤ (b : ℝ) ∧ |x 2| ≤ (c : ℝ) := by
  rw [coordBox, PrismNDim.mem_carrier_iff] at hx
  simp only [PrismNDim.basis_mk', PrismNDim.thicknesses_mk', PrismNDim.center_mk',
    vsub_eq_sub, sub_zero, EuclideanSpace.basisFun_repr] at hx
  refine ⟨?_, ?_, ?_⟩
  · have := hx 0; simpa using this
  · have := hx 1
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at this
    exact this
  · have := hx 2
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Matrix.cons_val_one, Matrix.cons_val_zero] at this
    exact this

theorem volume_coordBox (h : Fin 3 → NNReal) :
    volume (coordBox h).carrier = ((8 * h 0 * h 1 * h 2 : NNReal) : ENNReal) := by
  rw [coordBox, PrismNDim.volume_carrier, finrank_euclideanSpace_fin, Fin.prod_univ_three]
  simp only [PrismNDim.thicknesses_mk']
  rw [show (2 : ENNReal) ^ 3 = ((8 : NNReal) : ENNReal) by
    rw [show (8 : NNReal) = 2 ^ 3 by norm_num, ENNReal.coe_pow]; norm_num]
  rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
  congr 1
  ring

/-! ### A wide box inside a `δ`-tube: `tubeVolume δ ≥ 1.96 δ²` -/

theorem coordBox_subset_centredTube (δ : NNReal) :
    (coordBox ![1/2, 7*δ/10, 7*δ/10]).carrier ⊆ (centredTube δ).carrier := by
  intro x hx
  obtain ⟨h0', h1', h2'⟩ := coordBox₃_bounds hx
  have h0 : |x 0| ≤ (1 : ℝ)/2 := by
    rw [show ((1/2 : NNReal) : ℝ) = 1/2 by push_cast; ring] at h0'; exact h0'
  have h1 : |x 1| ≤ 7*(δ : ℝ)/10 := by
    rw [show ((7*δ/10 : NNReal) : ℝ) = 7*(δ:ℝ)/10 by push_cast; ring] at h1'; exact h1'
  have h2 : |x 2| ≤ 7*(δ : ℝ)/10 := by
    rw [show ((7*δ/10 : NNReal) : ℝ) = 7*(δ:ℝ)/10 by push_cast; ring] at h2'; exact h2'
  rw [(centredTube δ).carrier_eq]
  refine Set.mem_biUnion (show ((x 0) • EuclideanSpace.single (0 : Fin 3) (1:ℝ)) ∈
      segment ℝ (centredTube δ).x (centredTube δ).y from ?_) ?_
  · refine ⟨1/2 - x 0, 1/2 + x 0, ?_, ?_, by ring, ?_⟩
    · cases abs_le.mp h0; linarith
    · cases abs_le.mp h0; linarith
    · show (1/2 - x 0) • (centredTube δ).x + (1/2 + x 0) • (centredTube δ).y = _
      simp only [centredTube, Tube.mk']
      module
  · rw [mem_closedBall, dist_eq_norm]
    have hco : x - (x 0) • EuclideanSpace.single (0 : Fin 3) (1:ℝ) = !₂[0, x 1, x 2] := by
      ext i; fin_cases i <;> simp
    rw [hco, norm_coord]
    have hb : (0:ℝ)^2 + x 1 ^ 2 + x 2 ^ 2 ≤ (δ : ℝ)^2 := by
      have e1 : x 1 ^ 2 ≤ (7*(δ : ℝ)/10) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have e2 : x 2 ^ 2 ≤ (7*(δ : ℝ)/10) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      nlinarith [δ.coe_nonneg]
    calc Real.sqrt ((0:ℝ)^2 + x 1 ^ 2 + x 2 ^ 2)
        ≤ Real.sqrt ((δ : ℝ)^2) := Real.sqrt_le_sqrt hb
      _ = (δ : ℝ) := Real.sqrt_sq δ.coe_nonneg

/-- **`tubeVolume δ ≥ 1.96 δ²`.**  The box of half-widths `(1/2, 0.7δ, 0.7δ)`
lies inside the centred `δ`-tube.  A single box cannot beat `2δ²`, the inscribed
square of the disc, and `1.96 δ²` is what the essential-distinctness margin
needs. -/
theorem tubeVolume_ge (δ : NNReal) : ((196/100 * δ^2 : NNReal) : ENNReal) ≤ tubeVolume δ := by
  have h1 : volume (coordBox ![1/2, 7*δ/10, 7*δ/10]).carrier ≤ tubeVolume δ := by
    rw [tubeVolume, ← Tube.volume_carrier_eq_volume_carrier (centredTube δ) (modelTube δ)]
    exact measure_mono (coordBox_subset_centredTube δ)
  refine le_trans (le_of_eq ?_) h1
  rw [volume_coordBox]
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [← NNReal.coe_inj]; push_cast; ring

/-! ### The intersection of two tubes of the family is thin -/

theorem abs_capC_le_one (k : Fin 4) : |capC k| ≤ 1 := by fin_cases k <;> norm_num [capC]

theorem abs_capS_le_one (k : Fin 4) : |capS k| ≤ 1 := by fin_cases k <;> norm_num [capS]

/-- **The intersection of two tubes of the family lies in a box of half-widths
`(0.0107, 3.01δ, 3.01δ)`.**  Axially it is confined by `param_small`; the
transverse confinement is `capB θ |t| ≤ 2.01δ` plus the tube width `δ`. -/
theorem inter_subset_coordBox {δ : NNReal} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4000) {k l : Fin 4}
    (hkl : k ≠ l) :
    (axialTube δ k).carrier ∩ (axialTube δ l).carrier
      ⊆ (coordBox ![107/10000, 301*δ/100, 301*δ/100]).carrier := by
  intro x hx
  obtain ⟨t, htle, hb3, hxt⟩ := param_small hδ0 hδ hkl hx.1 hx.2
  have hδR : (δ : ℝ) ≤ 1 / 4000 := by
    have := NNReal.coe_le_coe.mpr hδ; push_cast at this; linarith
  have hδ0R : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ0
  have hθ1 : ((capTheta δ : NNReal) : ℝ) ≤ 1 := capTheta_le_one δ
  have hd : ∀ i, |(x - t • axialDir δ k) i| ≤ (δ : ℝ) := fun i =>
    le_trans (abs_coord_le_norm _ i) hxt
  have hsplit : ∀ i : Fin 3, x i = (x - t • axialDir δ k) i + (t • axialDir δ k) i := by
    intro i; simp
  have hu0 : (t • axialDir δ k) 0 = t * capA (capTheta δ) := by
    simp [axialDir, capDir]
  have hu1 : (t • axialDir δ k) 1 = capB (capTheta δ) * t * capC k := by
    simp [axialDir, capDir]; try ring
  have hu2 : (t • axialDir δ k) 2 = capB (capTheta δ) * t * capS k := by
    simp [axialDir, capDir]; try ring
  have hA1 : |capA (capTheta δ)| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [le_capA (θ := capTheta δ) hθ1] : (0:ℝ) ≤ capA (capTheta δ))]
    exact capA_le_one
  refine mem_coordBox₃ ?_ ?_ ?_
  · rw [show ((107/10000 : NNReal) : ℝ) = 107/10000 by push_cast; ring]
    calc |x 0| ≤ |(x - t • axialDir δ k) 0| + |(t • axialDir δ k) 0| := by
          rw [hsplit 0]; exact abs_add_le _ _
      _ ≤ (δ : ℝ) + |t| := by
          refine add_le_add (hd 0) ?_
          rw [hu0, abs_mul]
          calc |t| * |capA (capTheta δ)| ≤ |t| * 1 :=
                mul_le_mul_of_nonneg_left hA1 (abs_nonneg t)
            _ = |t| := by ring
      _ ≤ 107/10000 := by linarith
  · rw [show ((301*δ/100 : NNReal) : ℝ) = 301*(δ:ℝ)/100 by push_cast; ring]
    calc |x 1| ≤ |(x - t • axialDir δ k) 1| + |(t • axialDir δ k) 1| := by
          rw [hsplit 1]; exact abs_add_le _ _
      _ ≤ (δ : ℝ) + 201/100 * (δ : ℝ) := by
          refine add_le_add (hd 1) ?_
          rw [hu1, abs_mul, abs_mul, abs_of_nonneg (capB_nonneg (θ := capTheta δ))]
          calc capB (capTheta δ) * |t| * |capC k|
              ≤ capB (capTheta δ) * |t| * 1 :=
                mul_le_mul_of_nonneg_left (abs_capC_le_one k)
                  (mul_nonneg (capB_nonneg (θ := capTheta δ)) (abs_nonneg t))
            _ = capB (capTheta δ) * |t| := by ring
            _ ≤ 201/100 * (δ : ℝ) := hb3
      _ ≤ 301*(δ:ℝ)/100 := by linarith
  · rw [show ((301*δ/100 : NNReal) : ℝ) = 301*(δ:ℝ)/100 by push_cast; ring]
    calc |x 2| ≤ |(x - t • axialDir δ k) 2| + |(t • axialDir δ k) 2| := by
          rw [hsplit 2]; exact abs_add_le _ _
      _ ≤ (δ : ℝ) + 201/100 * (δ : ℝ) := by
          refine add_le_add (hd 2) ?_
          rw [hu2, abs_mul, abs_mul, abs_of_nonneg (capB_nonneg (θ := capTheta δ))]
          calc capB (capTheta δ) * |t| * |capS k|
              ≤ capB (capTheta δ) * |t| * 1 :=
                mul_le_mul_of_nonneg_left (abs_capS_le_one k)
                  (mul_nonneg (capB_nonneg (θ := capTheta δ)) (abs_nonneg t))
            _ = capB (capTheta δ) * |t| := by ring
            _ ≤ 201/100 * (δ : ℝ) := hb3
      _ ≤ 301*(δ:ℝ)/100 := by linarith

/-- **The four tubes are pairwise essentially distinct.**  Their intersection has
volume at most `8 · 0.0107 · (3.01δ)² < 0.776 δ²`, while each has volume at least
`1.96 δ²` (`tubeVolume_ge`), and `0.776 < 1.96/2 = 0.98`. -/
theorem isEssentiallyDistinct_axialTube {δ : NNReal} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4000)
    {k l : Fin 4} (hkl : k ≠ l) :
    IsEssentiallyDistinct (axialTube δ k).carrier (axialTube δ l).carrier := by
  have hvolA : volume (axialTube δ k).carrier = tubeVolume δ :=
    Tube.volume_carrier_eq_volume_carrier _ (modelTube δ)
  have hbox : volume ((axialTube δ k).carrier ∩ (axialTube δ l).carrier)
      ≤ ((8 * (107/10000) * (301*δ/100) * (301*δ/100) : NNReal) : ENNReal) := by
    refine le_trans (measure_mono (inter_subset_coordBox hδ0 hδ hkl)) (le_of_eq ?_)
    rw [volume_coordBox]
    congr 1
  rw [IsEssentiallyDistinct]
  refine le_trans hbox ?_
  have hstep : ((8 * (107/10000) * (301*δ/100) * (301*δ/100) : NNReal) : ENNReal)
      ≤ ((1/2 : NNReal) : ENNReal) * ((196/100 * δ^2 : NNReal) : ENNReal) := by
    rw [← ENNReal.coe_mul]
    refine ENNReal.coe_le_coe.mpr ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith [δ.coe_nonneg, sq_nonneg ((δ : ℝ))]
  refine le_trans hstep ?_
  rw [show ((1/2 : NNReal) : ENNReal) = 1/2 by
    rw [ENNReal.coe_div (by norm_num)]; norm_num]
  have hmax : ((196/100 * δ^2 : NNReal) : ENNReal)
      ≤ max (volume (axialTube δ k).carrier) (volume (axialTube δ l).carrier) := by
    calc ((196/100 * δ^2 : NNReal) : ENNReal) ≤ tubeVolume δ := tubeVolume_ge δ
      _ = volume (axialTube δ k).carrier := hvolA.symm
      _ ≤ max (volume (axialTube δ k).carrier) (volume (axialTube δ l).carrier) :=
          le_max_left _ _
  exact mul_le_mul_of_nonneg_left hmax (by norm_num)

/-! ### The remaining hypotheses of Leaf 1b -/

theorem axialTube_subset_ball {δ : NNReal} (hδ : δ ≤ 1 / 10) (k : Fin 4) :
    (axialTube δ k).carrier ⊆ closedBall (0 : Space3) 1 := by
  intro x hx
  obtain ⟨t, ht1, hxt⟩ := exists_param_of_mem_axialTube hx
  have hδR : (δ : ℝ) ≤ 1 / 10 := by
    have := NNReal.coe_le_coe.mpr hδ; push_cast at this; linarith
  rw [mem_closedBall, dist_zero_right]
  calc ‖x‖ = ‖(x - t • axialDir δ k) + t • axialDir δ k‖ := by congr 1; abel
    _ ≤ ‖x - t • axialDir δ k‖ + ‖t • axialDir δ k‖ := norm_add_le _ _
    _ ≤ (δ : ℝ) + 9 / 10 := by
        refine add_le_add hxt ?_
        rw [norm_smul, Real.norm_eq_abs, norm_axialDir, mul_one]
        exact ht1
    _ ≤ 1 := by linarith

theorem isTubeShadingFamily_axialFamily {δ : NNReal} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4000) :
    IsTubeShadingFamily (Finset.univ : Finset (ULift.{u} (Fin 4))) (axialFamily.{u} δ) := by
  have hδ10 : δ ≤ 1 / 10 := le_trans hδ (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [carrier_axialFamily]
    exact axialTube_subset_ball hδ10 i.down
  · intro i _ i' _ hne
    have hdown : i.down ≠ i'.down := fun h => hne (by cases i; cases i'; simpa using h)
    rw [carrier_axialFamily, carrier_axialFamily]
    exact isEssentiallyDistinct_axialTube hδ0 hδ hdown

/-- **The witness is `c`-dense for every `c ≤ 1/32000`.**  The shading is a fixed
constant fraction of a tube, `|capBox δ| = δ²/2000` against `|T| ≤ 16 δ²`, so the
density holds at `c = δ^η` for *every* `η > 0` once `δ` is small — which a ball
shading cannot do (`|B(0,δ)| ≍ δ³` forces `η ≥ 1`).  This is why the shading has
to be a box. -/
theorem isDense_axialFamily {δ : NNReal} (hδ : δ ≤ 1 / 4000) {c : NNReal}
    (hc : c ≤ 1 / 32000) :
    IsDense (Finset.univ : Finset (ULift.{u} (Fin 4))) (axialFamily.{u} δ) c := by
  classical
  have hδ1 : δ ≤ 1 := le_trans hδ (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have hδ200 : δ ≤ 1 / 200 := le_trans hδ (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  rw [IsDense]
  have hcarr : ∀ i : ULift.{u} (Fin 4), volume (axialFamily.{u} δ i).carrier = tubeVolume δ :=
    fun i => Tube.volume_carrier_eq_volume_carrier _ (modelTube δ)
  have hshade : ∀ i : ULift.{u} (Fin 4),
      volume (axialFamily.{u} δ i).shade = (δ : ENNReal) ^ 2 / 2000 := by
    intro i
    rw [shade_axialFamily hδ200, volume_capBox]
  rw [Finset.sum_congr rfl (fun i _ => hcarr i), Finset.sum_congr rfl (fun i _ => hshade i),
    Finset.sum_const, Finset.sum_const, Finset.card_univ]
  have hcard : Fintype.card (ULift.{u} (Fin 4)) = 4 := by simp
  rw [hcard, nsmul_eq_mul, nsmul_eq_mul]
  have hone : (c : ENNReal) * tubeVolume δ ≤ (δ : ENNReal) ^ 2 / 2000 := by
    have hV : tubeVolume δ ≤ ((16 * δ ^ 2 : NNReal) : ENNReal) := by
      refine (tubeVolume_le hδ1).trans (le_of_eq ?_)
      rw [ENNReal.coe_mul, ENNReal.coe_pow]
      norm_num
    calc (c : ENNReal) * tubeVolume δ ≤ (c : ENNReal) * ((16 * δ ^ 2 : NNReal) : ENNReal) := by
          gcongr
      _ = ((c * (16 * δ ^ 2) : NNReal) : ENNReal) := by push_cast; ring
      _ ≤ ((δ ^ 2 / 2000 : NNReal) : ENNReal) := by
          refine ENNReal.coe_le_coe.mpr ?_
          rw [← NNReal.coe_le_coe]
          push_cast
          have hcR : (c : ℝ) ≤ 1 / 32000 := by
            have := NNReal.coe_le_coe.mpr hc; push_cast at this; linarith
          nlinarith [c.coe_nonneg, sq_nonneg ((δ : ℝ)), hcR]
      _ = (δ : ENNReal) ^ 2 / 2000 := by
          rw [ENNReal.coe_div (by norm_num), ENNReal.coe_pow]; norm_num
  calc (c : ENNReal) * (4 * tubeVolume δ) = 4 * ((c : ENNReal) * tubeVolume δ) := by ring
    _ ≤ 4 * ((δ : ENNReal) ^ 2 / 2000) := by gcongr

/-- `4 ≤ δ^{-η}` whenever `δ^η ≤ 1/4`: the Katz--Tao budget of the leaf covers a
four-element family at every small `δ`. -/
theorem four_le_rpow_neg {δ : NNReal} {η : ℝ} (hη : 0 ≤ η) (h : ((δ : ℝ) ^ η) ≤ 1 / 4) :
    (4 : ENNReal) ≤ (δ : ENNReal) ^ (-η) := by
  have hle : (δ : ENNReal) ^ η ≤ 1 / 4 := by
    rw [← ENNReal.coe_rpow_of_nonneg _ hη,
      show (1 / 4 : ENNReal) = ((1 / 4 : NNReal) : ENNReal) by
        rw [ENNReal.coe_div (by norm_num)]; norm_num]
    refine ENNReal.coe_le_coe.mpr ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
    push_cast
    exact h
  rw [ENNReal.rpow_neg]
  calc (4 : ENNReal) = ((1 : ENNReal) / 4)⁻¹ := by
        rw [ENNReal.inv_div (by norm_num) (by norm_num)]; norm_num
    _ ≤ ((δ : ENNReal) ^ η)⁻¹ := ENNReal.inv_le_inv.mpr hle

theorem katzTao_axialFamily {δ : NNReal} (hδ0 : 0 < δ) {η : ℝ} (hη : 0 ≤ η)
    (hsmall : ((δ : ℝ) ^ η) ≤ 1 / 32000) :
    katzTaoConvexWolffConstant (Finset.univ : Finset (ULift.{u} (Fin 4)))
      (axialFamily.{u} δ) ≤ (δ : ENNReal) ^ (-η) := by
  refine (katzTaoConvexWolffConstant_le_card hδ0 ⟨⟨0⟩, Finset.mem_univ _⟩ _).trans ?_
  have hcard : (((Finset.univ : Finset (ULift.{u} (Fin 4))).card : ENNReal)) = 4 := by simp
  rw [hcard]
  exact four_le_rpow_neg hη (by linarith)

/-! ### The witness exists at every input quality, and Leaf 1b is false -/

theorem capTheta_le_one' (δ : NNReal) : capTheta δ ≤ 1 := by
  rw [capTheta]; exact min_le_right _ _

/-- **The witness family, at a scale small enough for the given input quality
`η`.**  All seven conjuncts of `IsAxiallySpreadWitness` hold at `ν = 1/4` and
`θ = 200 δ`: the family meets every hypothesis of
`Kakeya.WangZahl.CappedBalancedBroadCover` and no `θ`-tube holds two of its
tubes. -/
theorem exists_axiallySpreadWitness {η : ℝ} (hη : 0 < η) :
    ∃ δ : NNReal, 0 < δ ∧ δ < capTheta δ ∧ capTheta δ ≤ 1 ∧
      IsAxiallySpreadWitness (capTheta δ) (Finset.univ : Finset (ULift.{u} (Fin 4)))
        (axialFamily.{u} δ) η (1 / 4) := by
  classical
  set A : NNReal := ⟨(1 / 32000 : ℝ) ^ (1 / η), Real.rpow_nonneg (by norm_num) _⟩ with hA
  have hA0 : 0 < A := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_zero, hA]
    exact Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨min (1 / 4000) A, lt_min (by rw [← NNReal.coe_lt_coe]; push_cast; norm_num) hA0,
    ?_, capTheta_le_one' _, ?_⟩
  · exact lt_capTheta (lt_min (by rw [← NNReal.coe_lt_coe]; push_cast; norm_num) hA0)
      (le_trans (min_le_left _ _) (by rw [← NNReal.coe_le_coe]; push_cast; norm_num))
  set δ : NNReal := min (1 / 4000) A with hδdef
  have hδ0 : 0 < δ := lt_min (by rw [← NNReal.coe_lt_coe]; push_cast; norm_num) hA0
  have hδ : δ ≤ 1 / 4000 := min_le_left _ _
  -- the smallness of `δ^η`
  have hsmall : ((δ : ℝ) ^ η) ≤ 1 / 32000 := by
    have hle : (δ : ℝ) ≤ (1 / 32000 : ℝ) ^ (1 / η) := by
      have := NNReal.coe_le_coe.mpr (min_le_right (1 / 4000 : NNReal) A)
      rw [hA] at this
      exact this
    calc (δ : ℝ) ^ η ≤ ((1 / 32000 : ℝ) ^ (1 / η)) ^ η :=
          Real.rpow_le_rpow δ.coe_nonneg hle (le_of_lt hη)
      _ = (1 / 32000 : ℝ) ^ ((1 / η) * η) := (Real.rpow_mul (by norm_num) _ _).symm
      _ = 1 / 32000 := by
          rw [one_div_mul_cancel (ne_of_gt hη), Real.rpow_one]
  refine ⟨⟨⟨0⟩, Finset.mem_univ _⟩, isTubeShadingFamily_axialFamily hδ0 hδ, ?_,
    katzTao_axialFamily hδ0 (le_of_lt hη) hsmall, isCapConcentrated_axialFamily δ,
    isBroadAtScale_axialFamily hδ0 hδ, not_common_parent_axialFamily hδ0 hδ⟩
  refine isDense_axialFamily hδ ?_
  rw [← NNReal.coe_le_coe]
  push_cast
  exact hsmall

/-- **Leaf 1b of the Wang--Zahl Proposition 1.10 decomposition is false.**

`Kakeya.WangZahl.CappedBalancedBroadCover` fails at `ε = 1`, `ν = 1/4`, for every
input quality `η > 0` the leaf might choose: `axialFamily δ` at `θ = 200δ`
satisfies all five hypotheses, and no `θ`-tube holds two of its four tubes, so
every class of any admissible cover is a singleton — and a singleton class cannot
be both `δ^ν`-dense and `ν`-broad at `θ > δ`.

**Consequence for the ledger.**  `Kakeya.WangZahl.cappedBalancedBroadCover_holds`
is not merely open, it is *unprovable*: the covering leaf must be restated before
any proof effort is spent on it.  The clause to restore is the one the display
`broadAtScaleTheta` of `250224e_K3.tex:5744` carries and the current encoding
dropped: **the tubes through a typical point of `⋃ Y(T)` are captured by a single
`θ`-tube of the cover.**  As a hypothesis on the input family that reads: for
each `x` there is a `θ`-tube `W` holding a fixed fraction of the tubes through
`x` — the axial counterpart of `IsCapConcentrated`, which constrains directions
only.  With it the grouping is forced to be essentially unique and the classes
inherit the ambient broadness up to a bounded pigeonhole loss; without it the
leaf asks the covering step to manufacture broad classes out of nothing. -/
theorem not_cappedBalancedBroadCover : ¬ CappedBalancedBroadCover.{u} := by
  refine not_cappedBalancedBroadCover_of_axiallySpread (ν := 1 / 4) (by norm_num) ?_
  intro η hη _
  obtain ⟨δ, hδ0, hlt, hθ1, hbundle⟩ := exists_axiallySpreadWitness.{u} hη
  exact ⟨δ, capTheta δ, ULift.{u} (Fin 4), Finset.univ, axialFamily.{u} δ,
    hδ0, hlt, hθ1, hbundle⟩

end

end Kakeya.WangZahl
