/-
**Step 3 of Wang--Zahl Proposition `factoringConvexSetsProp` (:1123), for
boxes.**

Step 3 of the source's proof (`blueprint/src/WZ2/250224e_K3.tex:1123`) takes the
greedily selected convex sets `W in W_0` of Step 2, reads off the axis lengths
`l_1 <= ... <= l_n` of the *John ellipsoid* of each one, dyadically pigeonholes
those lengths into a common class `(a_1,...,a_n)`, and replaces each `W` by a
congruent copy of the single model set with axes `a_1,...,a_n`.  The output of
the proposition is congruent because of this step, and nothing else in the
proof produces congruence.

Neither Mathlib nor this project has the John ellipsoid, so Step 3 cannot be
run on an arbitrary convex `W`.  This file isolates and proves the part of
Step 3 that does *not* need it: **once the covering sets are already boxes**,
their axis lengths are the frame's own `Frame3.len`, the dyadic pigeonhole is
elementary, and the replacement by a congruent model box is a `Frame3` update
that leaves the centre and the axes alone.  The result,
`exists_congruent_box_refinement`, is exactly the shape of Step 3's output that
`factoringConvexSetsProp`'s conclusion asks for:

* a subfamily `w'` of controlled density inside `w`;
* one length vector `a` shared by every member of `w'`, which is the
  proposition's `(exists len, forall k in w, (F k).len = len)`;
* every original box contained in its replacement, so no incidence `U ⊆ W` is
  lost;
* every replacement of volume at most `8` times the original, so the counting
  inequality `lotsOfUinW` survives with a bounded loss --- the source's own
  "the first inequality has been weakened by a factor of `2^n`" (:1130).

What is *not* proved here, and is the remaining obstruction, is the passage
from an arbitrary convex `W` to a box: the statement recorded below as
`HasBoundingBoxes`.  It is strictly weaker than John's theorem --- it asks only
for a circumscribed box of comparable volume, not for the extremal ellipsoid.
`katzTaoConvexWolffConstantSets_le_of_hasBoundingBoxes` shows precisely what it
buys: it is what makes the Katz--Tao constant taken over *boxes* comparable to
the one taken over all convex test sets, which is what lets Step 2's maximiser
be chosen as a box in the first place.
-/
module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.FactoringConvexSets
public import Kakeya.Thickness.BoundingBox

@[expose] public section

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

namespace Frame3

/-! ### Changing the half-widths of a frame -/

/-- The frame with the same centre and axes as `F` but half-widths `a`.  This
is the source's "replace `W` by a congruent copy of `W_0`" (:1130): the
replacement keeps `W`'s position and orientation and only rounds its
half-widths up to the class representative. -/
def withLen (F : Frame3) (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) : Frame3 where
  center := F.center
  basis := F.basis
  len := a
  len_pos := ha

@[simp] theorem withLen_center (F : Frame3) (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    (F.withLen a ha).center = F.center := rfl

@[simp] theorem withLen_basis (F : Frame3) (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    (F.withLen a ha).basis = F.basis := rfl

@[simp] theorem withLen_len (F : Frame3) (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    (F.withLen a ha).len = a := rfl

/-- Enlarging the half-widths enlarges the box. -/
theorem box_subset_withLen (F : Frame3) {a : Fin 3 → ℝ} (ha : ∀ i, 0 < a i)
    (h : ∀ i, F.len i ≤ a i) : F.box ⊆ (F.withLen a ha).box := by
  intro z hz i
  exact le_trans (hz i) (h i)

/-! ### The volume of a box -/

/-- The box of a frame has volume `8 * l_1 l_2 l_3`: it is the preimage of the
cube `[-1,1]^3`, whose volume is `8`, under `phi_W`. -/
theorem volume_box (F : Frame3) :
    volume F.box = 8 * ENNReal.ofReal (∏ i, F.len i) := by
  have hcube : F.volumeFactor * volume F.box = 8 := by
    rw [← F.volume_image_map' F.box, F.map_image_box, volume_unitCube]
  have hprod : ENNReal.ofReal (∏ i, F.len i) * F.volumeFactor = 1 := by
    have hnn : (0 : ℝ) ≤ ∏ i, F.len i :=
      le_of_lt (Finset.prod_pos fun i _ => F.len_pos i)
    rw [volumeFactor, ← ENNReal.ofReal_mul hnn, ← Finset.prod_mul_distrib]
    have : ∀ i ∈ (Finset.univ : Finset (Fin 3)), F.len i * (F.len i)⁻¹ = 1 :=
      fun i _ => mul_inv_cancel₀ (F.len_pos i).ne'
    rw [Finset.prod_congr rfl this, Finset.prod_const_one, ENNReal.ofReal_one]
  calc volume F.box = ENNReal.ofReal (∏ i, F.len i) * F.volumeFactor * volume F.box := by
        rw [hprod, one_mul]
    _ = ENNReal.ofReal (∏ i, F.len i) * (F.volumeFactor * volume F.box) := by
        rw [mul_assoc]
    _ = 8 * ENNReal.ofReal (∏ i, F.len i) := by rw [hcube, mul_comm]

theorem volume_box_ne_zero (F : Frame3) : volume F.box ≠ 0 := by
  rw [volume_box]
  refine mul_ne_zero (by norm_num) ?_
  rw [← pos_iff_ne_zero, ENNReal.ofReal_pos]
  exact Finset.prod_pos fun i _ => F.len_pos i

theorem volume_box_ne_top (F : Frame3) : volume F.box ≠ ⊤ := by
  rw [volume_box]
  exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top

/-- Rounding the half-widths up by at most a factor `2` costs at most a factor
`8` of volume.  This is the source's `2^n` loss at :1130, with `n = 3`. -/
theorem volume_withLen_le (F : Frame3) {a : Fin 3 → ℝ} (ha : ∀ i, 0 < a i)
    (h : ∀ i, a i ≤ 2 * F.len i) :
    volume (F.withLen a ha).box ≤ 8 * volume F.box := by
  have hprod : ∏ i, a i ≤ 8 * ∏ i, F.len i := by
    have h2 : ∏ i, a i ≤ ∏ i, (2 * F.len i) :=
      Finset.prod_le_prod (fun i _ => (ha i).le) (fun i _ => h i)
    calc ∏ i, a i ≤ ∏ i, (2 * F.len i) := h2
      _ = 8 * ∏ i, F.len i := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
          norm_num
  rw [volume_box, volume_box, withLen_len]
  calc (8 : ENNReal) * ENNReal.ofReal (∏ i, a i)
      ≤ 8 * ENNReal.ofReal (8 * ∏ i, F.len i) := by gcongr
    _ = 8 * (8 * ENNReal.ofReal (∏ i, F.len i)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8)]
        norm_num

end Frame3

/-! ### A pigeonhole -/

/-- Some fibre of `f` over `t` carries at least a `(#t)^{-1}` fraction of `s`. -/
theorem exists_large_fiber {α β : Type*} [DecidableEq β] (s : Finset α)
    (t : Finset β) (f : α → β) (hf : ∀ a ∈ s, f a ∈ t) (ht : t.Nonempty) :
    ∃ b ∈ t, s.card ≤ t.card * (s.filter fun x => f x = b).card := by
  classical
  by_contra hcon
  push Not at hcon
  have hsum : s.card = ∑ b ∈ t, (s.filter fun x => f x = b).card :=
    Finset.card_eq_sum_card_fiberwise hf
  have hlt : ∑ b ∈ t, t.card * (s.filter fun x => f x = b).card
      < ∑ _b ∈ t, s.card :=
    Finset.sum_lt_sum_of_nonempty ht fun b hb => hcon b hb
  rw [← Finset.mul_sum, ← hsum, Finset.sum_const, smul_eq_mul] at hlt
  exact absurd hlt (lt_irrefl _)

/-! ### The dyadic pigeonhole on axis lengths

This is the elementary half of the source's Step 3 (:1123).  For a *box* the
"axes of the John ellipsoid" are the frame's own half-widths `Frame3.len`, so
the dyadic pigeonhole is a pigeonhole on `floor (log_2 (len i))`, which takes
finitely many values once `delta <= len i <= 2`.
-/

/-- The dyadic class of a positive real: the integer `k` with
`2^k <= x < 2^(k+1)`. -/
def dyadicClass (x : ℝ) : ℤ := ⌊Real.logb 2 x⌋

theorem rpow_dyadicClass_le {x : ℝ} (hx : 0 < x) :
    (2 : ℝ) ^ ((dyadicClass x : ℝ)) ≤ x :=
  (Real.le_logb_iff_rpow_le one_lt_two hx).mp (Int.floor_le _)

theorem lt_rpow_dyadicClass_add_one {x : ℝ} (hx : 0 < x) :
    x < (2 : ℝ) ^ ((dyadicClass x : ℝ) + 1) :=
  (Real.logb_lt_iff_lt_rpow one_lt_two hx).mp (Int.lt_floor_add_one _)

theorem dyadicClass_le_dyadicClass {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    dyadicClass x ≤ dyadicClass y :=
  Int.floor_le_floor (Real.logb_le_logb_of_le one_lt_two hx hxy)

theorem dyadicClass_le_one {x : ℝ} (hx : 0 < x) (h : x ≤ 2) : dyadicClass x ≤ 1 := by
  have h1 : Real.logb 2 x ≤ 1 := by
    refine (Real.logb_le_iff_le_rpow one_lt_two hx).mpr ?_
    rw [Real.rpow_one]; exact h
  calc dyadicClass x ≤ ⌊(1 : ℝ)⌋ := Int.floor_le_floor h1
    _ = 1 := Int.floor_one

/-- The set of dyadic classes available to a triple of half-widths lying in
`[delta, 2]`. -/
def dyadicClassSet (δ : ℝ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (dyadicClass δ) 1

/-- The pigeonhole loss of Step 3: the number of dyadic classes a triple of
half-widths in `[delta, 2]` can occupy.  The source writes it as
`(100 |log delta|)^n` (:1133). -/
def dyadicBoxClassCount (δ : ℝ) : ℕ := (dyadicClassSet δ).card

theorem dyadicBoxClassCount_eq (δ : ℝ) :
    dyadicBoxClassCount δ = (Finset.Icc (dyadicClass δ) 1).card ^ 3 := by
  rw [dyadicBoxClassCount, dyadicClassSet, Fintype.card_piFinset, Finset.prod_const]
  simp

theorem dyadicClassSet_nonempty {δ : ℝ} (hδ0 : 0 < δ) (hδ2 : δ ≤ 2) :
    (dyadicClassSet δ).Nonempty := by
  refine Fintype.piFinset_nonempty.mpr fun _ => ⟨dyadicClass δ, ?_⟩
  exact Finset.mem_Icc.mpr ⟨le_rfl, dyadicClass_le_one hδ0 hδ2⟩

/-! ### Step 3 for boxes

`exists_congruent_box_refinement` is Step 3 of the source's proof of
Proposition `factoringConvexSetsProp` (:1123--:1133), restricted to the case
its John-ellipsoid appeal is unnecessary: the sets being pigeonholed are
already boxes.
-/

/-- **Step 3 of `factoringConvexSetsProp` (:1123), for boxes.**

Given a finite family of boxes whose half-widths all lie in `[delta, 2]`, there
is one length vector `a` and a subfamily `w'` with
`#w >= (number of dyadic classes)^{-1} #w'` such that, for each member of `w'`,
replacing its frame's half-widths by `a` keeps the same centre and axes,
*enlarges* the box (so no incidence `U ⊆ W` is lost), and multiplies its volume
by at most `8` (the source's `2^n`, :1130).  Every replacement box has the same
half-widths `a`, hence is congruent to every other: they are translates of
rotations of the single model box `W_0`.

This is the exact shape `factoringConvexSetsProp`'s conclusion asks of its
cover, whose congruence it records as `exists len, forall k in w, (F k).len =
len`. -/
theorem exists_congruent_box_refinement {κ : Type u} (w : Finset κ)
    (F : κ → Frame3) {δ : ℝ} (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    (hlo : ∀ k ∈ w, ∀ i, δ ≤ (F k).len i)
    (hhi : ∀ k ∈ w, ∀ i, (F k).len i ≤ 2) :
    ∃ (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) (w' : Finset κ),
      w' ⊆ w ∧
      w.card ≤ dyadicBoxClassCount δ * w'.card ∧
      (∀ k ∈ w', (F k).box ⊆ ((F k).withLen a ha).box) ∧
      (∀ k ∈ w', volume ((F k).withLen a ha).box ≤ 8 * volume (F k).box) ∧
      (∀ k ∈ w', ((F k).withLen a ha).len = a) := by
  classical
  set cls : κ → (Fin 3 → ℤ) := fun k i => dyadicClass ((F k).len i) with hcls
  have hmaps : ∀ k ∈ w, cls k ∈ dyadicClassSet δ := by
    intro k hk
    refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · exact dyadicClass_le_dyadicClass hδ0 (hlo k hk i)
    · exact dyadicClass_le_one ((F k).len_pos i) (hhi k hk i)
  obtain ⟨c, -, hcard⟩ :=
    exists_large_fiber w (dyadicClassSet δ) cls hmaps (dyadicClassSet_nonempty hδ0 hδ2)
  refine ⟨fun i => (2 : ℝ) ^ ((c i : ℝ) + 1), fun i => Real.rpow_pos_of_pos two_pos _,
    w.filter fun k => cls k = c, Finset.filter_subset _ _, hcard, ?_, ?_, fun _ _ => rfl⟩
  · intro k hk
    obtain ⟨hkw, hkc⟩ := Finset.mem_filter.mp hk
    refine Frame3.box_subset_withLen _ _ fun i => le_of_lt ?_
    have := lt_rpow_dyadicClass_add_one ((F k).len_pos i)
    rwa [show dyadicClass ((F k).len i) = c i from congrFun hkc i] at this
  · intro k hk
    obtain ⟨hkw, hkc⟩ := Finset.mem_filter.mp hk
    refine Frame3.volume_withLen_le _ _ fun i => ?_
    have hlow : (2 : ℝ) ^ ((c i : ℝ)) ≤ (F k).len i := by
      have := rpow_dyadicClass_le ((F k).len_pos i)
      rwa [show dyadicClass ((F k).len i) = c i from congrFun hkc i] at this
    calc (2 : ℝ) ^ ((c i : ℝ) + 1) = 2 ^ ((c i : ℝ)) * 2 := by
          rw [Real.rpow_add two_pos, Real.rpow_one]
      _ ≤ (F k).len i * 2 := by gcongr
      _ = 2 * (F k).len i := mul_comm _ _

/-! ### The remaining obstruction

Everything above is about boxes.  What Step 3 needs, and what is *not* proved
here, is the step that produces a box in the first place out of the arbitrary
convex maximiser Step 2 (:1102) hands over.  The source does it with the John
ellipsoid; the property below is what is actually used, and it is strictly
weaker: it asks only for a *circumscribed box of comparable volume*, not for an
extremal ellipsoid.
-/

/-- **`HasBoundingBoxes c`**: every convex set of finite nonzero volume is
contained in a box of at most `c` times its volume.  True in `R^3` with an
absolute `c` (it follows from John's theorem, and also from the elementary
maximal-volume-simplex argument), but neither is available in Mathlib; this is
the single named obstruction left in Step 3 of `factoringConvexSetsProp`. -/
def HasBoundingBoxes (c : ENNReal) : Prop :=
  ∀ W : Set Space3, Convex ℝ W → volume W ≠ 0 → volume W ≠ ⊤ →
    ∃ F : Frame3, W ⊆ F.box ∧ volume F.box ≤ c * volume W

/-- **The Katz--Tao convex Wolff constant with *box* test sets.**  Step 2's
greedy maximiser (:1102) selects a test set realising this infimum; if the test
sets are boxes then Step 3 is `exists_congruent_box_refinement` and needs no
John ellipsoid. -/
noncomputable def katzTaoBoxWolffConstantSets {ι : Type u} (s : Finset ι)
    (U : ι → Set Space3) : ENNReal :=
  @sInf ENNReal _
    {C : ENNReal | 0 < C ∧ ∀ F : Frame3,
      ∑ i ∈ subfamilyIn s U F.box, volume (U i) ≤ C * volume F.box}

/-- Boxes are convex, so the box constant is at most the convex one.  This
direction is free. -/
theorem katzTaoBoxWolffConstantSets_le {ι : Type u} (s : Finset ι)
    (U : ι → Set Space3) :
    katzTaoBoxWolffConstantSets s U ≤ katzTaoConvexWolffConstantSets s U :=
  sInf_le_sInf fun _C hC =>
    ⟨hC.1, fun F => hC.2 ⟨F.box, F.convex_box⟩⟩

/-- **What `HasBoundingBoxes` buys.**  The reverse comparison: a bound on every
*box* test set upgrades, at the cost of the factor `c`, to a bound on the
Katz--Tao convex Wolff constant, which takes *all* convex test sets.

This is the precise sense in which `HasBoundingBoxes` is the only thing
separating Step 2's maximiser from being a box. -/
theorem katzTaoConvexWolffConstantSets_le_of_hasBoundingBoxes {ι : Type u}
    {s : Finset ι} {U : ι → Set Space3} {c C : ENNReal} (hc0 : c ≠ 0)
    (hc : HasBoundingBoxes c) (hC0 : 0 < C)
    (hbox : ∀ F : Frame3, ∑ i ∈ subfamilyIn s U F.box, volume (U i)
      ≤ C * volume F.box) :
    katzTaoConvexWolffConstantSets s U ≤ c * C := by
  refine sInf_le ⟨ENNReal.mul_pos hc0 hC0.ne', fun W => ?_⟩
  rcases eq_or_ne (volume W.carrier) 0 with hz | hz
  · have hzero : ∀ i ∈ subfamilyIn s U W.carrier, volume (U i) = 0 := by
      intro i hi
      exact measure_mono_null (mem_subfamilyIn.mp hi).2 hz
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    exact zero_le
  rcases eq_or_ne (volume W.carrier) ⊤ with ht | ht
  · rw [ht, ENNReal.mul_top (by simp [hc0, hC0.ne'])]
    exact le_top
  obtain ⟨F, hWF, hvol⟩ := hc W.carrier W.convex_carrier hz ht
  calc ∑ i ∈ subfamilyIn s U W.carrier, volume (U i)
      ≤ ∑ i ∈ subfamilyIn s U F.box, volume (U i) := by
        refine Finset.sum_le_sum_of_subset ?_
        intro i hi
        exact mem_subfamilyIn.mpr ⟨(mem_subfamilyIn.mp hi).1,
          (mem_subfamilyIn.mp hi).2.trans hWF⟩
    _ ≤ C * volume F.box := hbox F
    _ ≤ C * (c * volume W.carrier) := by gcongr
    _ = c * C * volume W.carrier := by ring

/-- **Step 2's maximiser, as a box** (:1102, `sizeOfWmCalU`).  Granted
`HasBoundingBoxes c`, the greedy selection of Step 2 can be made among *boxes*
at the cost of the factor `c`: below the Katz--Tao convex Wolff constant there
is always a `Frame3` whose box already carries more than its share of the
family.

Together with `exists_congruent_box_refinement`, this discharges every use of
the John ellipsoid in Steps 2 and 3 of the source's proof of
`factoringConvexSetsProp`, leaving `HasBoundingBoxes` as the only unproved
ingredient of those two steps. -/
theorem exists_boxTestSet_of_lt_katzTao {ι : Type u} (s : Finset ι)
    (U : ι → Set Space3) {c C : ENNReal} (hc0 : c ≠ 0) (hc : HasBoundingBoxes c)
    (hC0 : 0 < C) (hlt : c * C < katzTaoConvexWolffConstantSets s U) :
    ∃ F : Frame3, C * volume F.box < ∑ i ∈ subfamilyIn s U F.box, volume (U i) := by
  by_contra hcon
  push Not at hcon
  exact absurd (katzTaoConvexWolffConstantSets_le_of_hasBoundingBoxes hc0 hc hC0 hcon)
    (not_le.mpr hlt)

/-! ### `HasBoundingBoxes` is not vacuous

`HasBoundingBoxes c` is a hypothesis this file cannot discharge, so the two
theorems above would be worthless if it were *false* for every `c`.  It is not:
the certificate below proves it outright for closed balls, with `c = 6`, by
sandwiching the ball between the cube of half-width `r` and the cube of
half-width `r / sqrt 3`.  That is a class of convex sets of positive finite
volume, so the property is genuinely satisfiable on a nonempty class and the
open question is only its uniformity over all convex sets --- which is what
John's theorem supplies. -/

/-- The cube of half-width `r` centred at `x`, in the standard axes. -/
def cubeFrameAt (x : Space3) (r : ℝ) (hr : 0 < r) : Frame3 where
  center := x
  basis := EuclideanSpace.basisFun (Fin 3) ℝ
  len := fun _ => r
  len_pos := fun _ => hr

@[simp] theorem cubeFrameAt_len (x : Space3) (r : ℝ) (hr : 0 < r) :
    (cubeFrameAt x r hr).len = fun _ => r := rfl

theorem mem_cubeFrameAt_box_iff (x : Space3) {r : ℝ} (hr : 0 < r) (z : Space3) :
    z ∈ (cubeFrameAt x r hr).box ↔ ∀ i, |(z - x) i| ≤ r := by
  simp [Frame3.box, cubeFrameAt, EuclideanSpace.basisFun_repr]

theorem volume_cubeFrameAt_box (x : Space3) {r : ℝ} (hr : 0 < r) :
    volume (cubeFrameAt x r hr).box = 8 * ENNReal.ofReal (r ^ 3) := by
  rw [Frame3.volume_box]
  simp [cubeFrameAt, Finset.prod_const]

theorem closedBall_subset_cubeFrameAt_box (x : Space3) {r : ℝ} (hr : 0 < r) :
    Metric.closedBall x r ⊆ (cubeFrameAt x r hr).box := by
  intro z hz
  rw [mem_cubeFrameAt_box_iff]
  intro i
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  calc |(z - x) i| = ‖(z - x) i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖z - x‖ := PiLp.norm_apply_le _ i
    _ ≤ r := hz

theorem cubeFrameAt_box_subset_closedBall (x : Space3) {r : ℝ} (hr : 0 < r) :
    (cubeFrameAt x (r / Real.sqrt 3) (by positivity)).box ⊆ Metric.closedBall x r := by
  intro z hz
  rw [mem_cubeFrameAt_box_iff] at hz
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq : (r / Real.sqrt 3) ^ 2 = r ^ 2 / 3 := by
    rw [div_pow, hs2]
  rw [Metric.mem_closedBall, dist_eq_norm, EuclideanSpace.norm_eq]
  rw [show r = Real.sqrt (r ^ 2) from (Real.sqrt_sq hr.le).symm]
  refine Real.sqrt_le_sqrt ?_
  have hbound : ∀ i : Fin 3, ‖(z - x) i‖ ^ 2 ≤ r ^ 2 / 3 := by
    intro i
    have h1 : ‖(z - x) i‖ ≤ r / Real.sqrt 3 := (Real.norm_eq_abs _ ▸ hz i)
    have h0 : (0 : ℝ) ≤ ‖(z - x) i‖ := norm_nonneg _
    nlinarith [hsq]
  calc ∑ i : Fin 3, ‖(z - x) i‖ ^ 2 ≤ ∑ _i : Fin 3, r ^ 2 / 3 :=
        Finset.sum_le_sum fun i _ => hbound i
    _ = r ^ 2 := by simp; ring

/-- **`HasBoundingBoxes` holds for closed balls, with `c = 6`.**  A nonvacuity
certificate for the hypothesis of
`katzTaoConvexWolffConstantSets_le_of_hasBoundingBoxes` and
`exists_boxTestSet_of_lt_katzTao`. -/
theorem exists_boundingBox_closedBall (x : Space3) {r : ℝ} (hr : 0 < r) :
    ∃ F : Frame3, Metric.closedBall x r ⊆ F.box ∧
      volume F.box ≤ 6 * volume (Metric.closedBall x r) := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hr' : (0 : ℝ) < r / Real.sqrt 3 := by positivity
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs_le : Real.sqrt 3 ≤ 2 := by nlinarith [Real.sqrt_nonneg 3]
  have hcube : Real.sqrt 3 ^ 3 ≤ 6 := by nlinarith [Real.sqrt_nonneg 3]
  have hkey : r ^ 3 ≤ 6 * (r / Real.sqrt 3) ^ 3 := by
    rw [div_pow, ← mul_div_assoc,
      le_div_iff₀ (by positivity : (0:ℝ) < Real.sqrt 3 ^ 3)]
    nlinarith [pow_pos hr 3]
  refine ⟨cubeFrameAt x r hr, closedBall_subset_cubeFrameAt_box x hr, ?_⟩
  calc volume (cubeFrameAt x r hr).box
      = 8 * ENNReal.ofReal (r ^ 3) := volume_cubeFrameAt_box x hr
    _ ≤ 8 * ENNReal.ofReal (6 * (r / Real.sqrt 3) ^ 3) := by gcongr
    _ = 6 * (8 * ENNReal.ofReal ((r / Real.sqrt 3) ^ 3)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 6)]
        norm_num
        ring
    _ = 6 * volume (cubeFrameAt x (r / Real.sqrt 3) hr').box := by
        rw [volume_cubeFrameAt_box]
    _ ≤ 6 * volume (Metric.closedBall x r) := by
        gcongr
        exact cubeFrameAt_box_subset_closedBall x hr

/-! ### Non-vacuity

`exists_congruent_box_refinement` is proved, so it is certainly satisfiable;
the certificate below exhibits a *nonempty* family for which its conclusion
holds with the identity replacement, so that no reader has to wonder whether
the density bound is vacuous. -/
theorem exists_congruent_box_refinement_nonempty {δ : ℝ} (hδ0 : 0 < δ)
    (hδ2 : δ ≤ 2) :
    ∃ (w : Finset Unit) (F : Unit → Frame3),
      w.Nonempty ∧ (∀ k ∈ w, ∀ i, δ ≤ (F k).len i) ∧
      (∀ k ∈ w, ∀ i, (F k).len i ≤ 2) ∧
      ∃ (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) (w' : Finset Unit),
        w'.Nonempty ∧ w' ⊆ w ∧
        w.card ≤ dyadicBoxClassCount δ * w'.card ∧
        (∀ k ∈ w', (F k).box ⊆ ((F k).withLen a ha).box) ∧
        (∀ k ∈ w', volume ((F k).withLen a ha).box ≤ 8 * volume (F k).box) := by
  classical
  refine ⟨{()}, fun _ => cubeFrame δ hδ0, ⟨(), Finset.mem_singleton_self _⟩,
    fun _ _ _ => le_rfl, fun _ _ _ => hδ2, ?_⟩
  obtain ⟨a, ha, w', hsub, hcard, hbox, hvol, -⟩ :=
    exists_congruent_box_refinement ({()} : Finset Unit) (fun _ => cubeFrame δ hδ0)
      hδ0 hδ2 (fun _ _ _ => le_rfl) (fun _ _ _ => hδ2)
  have hw' : w'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty w' with he | hne
    · rw [he] at hcard; simp at hcard
    · exact hne
  exact ⟨a, ha, w', hw', hsub, hcard, hbox, hvol⟩


section BoundingBoxes

open Metric

/-! ### `HasBoundingBoxes` holds, with `c = 48`

The obstruction recorded above is now discharged, and without the John
ellipsoid.  The work is done by `Convex.exists_boundingBox`
(`Kakeya/Thickness/BoundingBox.lean`), which composes two devices this project
already had:

* `outerPrism` (`Kakeya/Thickness/OuterPrism.lean`) circumscribes a nonempty
  compact set by the axis-aligned box whose half-widths are exactly the set's
  `Metric.thickness`es, in a frame it constructs itself.  Its `exists_limit` is
  a `Frame3` in all but name, so the box below is *read off* rather than built.
* `Convex.ethickness_prod_le_volume` (`Kakeya/Thickness/Volume.lean`), whose
  own proof runs through the maximal inscribed simplex of
  `Kakeya.exists_simplex_of_lt_ethickness`, is the matching lower bound
  `(n !)⁻¹ * prod_i thickness_i <= |W|`.

The box therefore has volume `2 ^ 3 * prod thickness_i <= 8 * 3! * |W|`, and the
constant is `48`.  This is the elementary route recorded for Step 3, with the
inscribed-simplex device supplied by `Convex.ethickness_prod_le_volume` instead
of rebuilt. -/

/-- **Every convex set of finite nonzero volume in `R^3` has a circumscribed
`Frame3` box of comparable volume**, with the absolute constant `48`. -/
theorem exists_boundingBox_of_convex {W : Set Space3} (hW : Convex ℝ W)
    (h0 : volume W ≠ 0) (htop : volume W ≠ ⊤) :
    ∃ F : Frame3, W ⊆ F.box ∧ volume F.box ≤ 48 * volume W := by
  have hfr : Module.finrank ℝ Space3 = 3 := by simp
  obtain ⟨c, b, len, hlen, hsub, hvol⟩ := hW.exists_boundingBox h0 htop hfr
  have hfac : ((Nat.factorial 3 : NNReal) : ENNReal) = 6 := by
    norm_num [Nat.factorial]
  refine ⟨⟨c, b, len, hlen⟩, fun z hz i => hsub z hz i, ?_⟩
  rw [Frame3.volume_box]
  show (8 : ENNReal) * ENNReal.ofReal (∏ i, len i) ≤ 48 * volume W
  calc (8 : ENNReal) * ENNReal.ofReal (∏ i, len i)
      ≤ 8 * (((Nat.factorial 3 : NNReal) : ENNReal) * volume W) := by gcongr
    _ = 48 * volume W := by rw [hfac, ← mul_assoc]; norm_num

/-- **`HasBoundingBoxes 48`**: the obstruction of Step 3 of `factoringConvexSetsProp`
is discharged. -/
theorem hasBoundingBoxes_fortyEight : HasBoundingBoxes 48 :=
  fun _W hW h0 htop => exists_boundingBox_of_convex hW h0 htop

/-! ### The unconditional consequences

Every statement in this file that was conditional on `HasBoundingBoxes` is now
unconditional, with `c = 48`. -/

/-- **Boxes suffice for the Katz--Tao convex Wolff constant** (unconditional
form of `katzTaoConvexWolffConstantSets_le_of_hasBoundingBoxes`): a bound over
all *box* test sets upgrades to a bound over all convex test sets at the cost
of the absolute factor `48`. -/
theorem katzTaoConvexWolffConstantSets_le_of_box {ι : Type u} {s : Finset ι}
    {U : ι → Set Space3} {C : ENNReal} (hC0 : 0 < C)
    (hbox : ∀ F : Frame3, ∑ i ∈ subfamilyIn s U F.box, volume (U i)
      ≤ C * volume F.box) :
    katzTaoConvexWolffConstantSets s U ≤ 48 * C :=
  katzTaoConvexWolffConstantSets_le_of_hasBoundingBoxes (by norm_num)
    hasBoundingBoxes_fortyEight hC0 hbox

/-- **The box and convex Katz--Tao Wolff constants are comparable**, with the
absolute factor `48`.  Together with the free direction
`katzTaoBoxWolffConstantSets_le` this pins the two constants to within `48`,
which is what licenses Step 2 of `factoringConvexSetsProp` to select its
maximiser among boxes. -/
theorem katzTaoConvexWolffConstantSets_le_fortyEight_mul_box {ι : Type u}
    (s : Finset ι) (U : ι → Set Space3) :
    katzTaoConvexWolffConstantSets s U ≤ 48 * katzTaoBoxWolffConstantSets s U := by
  rw [mul_comm, ← ENNReal.div_le_iff_le_mul (Or.inl (by norm_num))
    (Or.inl (by norm_num))]
  refine le_sInf ?_
  intro C hC
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num)),
    mul_comm]
  exact katzTaoConvexWolffConstantSets_le_of_box hC.1 hC.2

/-- **Step 2's maximiser is a box**, unconditionally (unconditional form of
`exists_boxTestSet_of_lt_katzTao`). -/
theorem exists_boxTestSet_of_lt_katzTao_fortyEight {ι : Type u} (s : Finset ι)
    (U : ι → Set Space3) {C : ENNReal} (hC0 : 0 < C)
    (hlt : 48 * C < katzTaoConvexWolffConstantSets s U) :
    ∃ F : Frame3, C * volume F.box < ∑ i ∈ subfamilyIn s U F.box, volume (U i) :=
  exists_boxTestSet_of_lt_katzTao s U (by norm_num) hasBoundingBoxes_fortyEight
    hC0 hlt

end BoundingBoxes

end

end Kakeya.WangZahl

#print axioms Kakeya.WangZahl.Frame3.volume_box
#print axioms Kakeya.WangZahl.Frame3.volume_withLen_le
#print axioms Kakeya.WangZahl.Frame3.box_subset_withLen
#print axioms Kakeya.WangZahl.exists_large_fiber
#print axioms Kakeya.WangZahl.dyadicBoxClassCount_eq
#print axioms Kakeya.WangZahl.exists_congruent_box_refinement
#print axioms Kakeya.WangZahl.katzTaoBoxWolffConstantSets_le
#print axioms Kakeya.WangZahl.katzTaoConvexWolffConstantSets_le_of_hasBoundingBoxes
#print axioms Kakeya.WangZahl.exists_boxTestSet_of_lt_katzTao
#print axioms Kakeya.WangZahl.exists_boundingBox_closedBall
#print axioms Kakeya.WangZahl.exists_congruent_box_refinement_nonempty
#print axioms Kakeya.WangZahl.exists_boundingBox_of_convex
#print axioms Kakeya.WangZahl.hasBoundingBoxes_fortyEight
#print axioms Kakeya.WangZahl.katzTaoConvexWolffConstantSets_le_of_box
#print axioms Kakeya.WangZahl.katzTaoConvexWolffConstantSets_le_fortyEight_mul_box
#print axioms Kakeya.WangZahl.exists_boxTestSet_of_lt_katzTao_fortyEight
