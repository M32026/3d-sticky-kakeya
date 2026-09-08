/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RelativePlank
public import Kakeya.DimensionThree.Volume
public import Kakeya.DimensionThree.Plank.PlankFactorizationEstimate
public import Kakeya.DimensionThree.FrostmanEstimateOne

/-!
# `Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation` is refutable

`Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation` (`Kakeya/RelativePlank.lean`) is the
persistent-hypothesis variant of GWZ Proposition 6.6(A) in the regime `δ ≤ ρ ≤ a ≤ b ≤ 1`.  Its
hypothesis list carries **no essential-distinctness clause** on the fine family `(T i)_{i ∈ q}`,
and no upper bound on `#q`.  Every other form of the same estimate in the development does carry
one:

* `Kakeya.FrostmanEstimate.multiplicity_bound_of_mem` (the canonical Frostman multiplicity
  estimate, `Kakeya/PartialEstimates.lean`) takes
  `(s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier)`;
* `Kakeya.IsFlatPrismFamily` — the family package of
  `Kakeya.FlatPrisms.multiplicity_le_of_factorsThroughFlatPrisms'`, the surviving general form of
  6.6(A) — carries it as the field `essDistinct`.

Without it the statement is false, and this file proves it false, unconditionally in `β`: the
witness is `N` **copies of one fully shaded `δ`-tube**, at `ρ = a = b = δ`.  Every hypothesis is
`N`-independent — uniformity holds at constant `1`, the Frostman constant is `|B₁| / |T|`, and the
plank-factorisation constant is `8 / c₃` where `c₃` is `Tube.le_volume.c 3` — while the
multiplicity is exactly `N` and the right-hand side grows like `N ^ (1 - β / 2)`.  Taking `N` large
breaks the inequality.

## What is proved here

* `Kakeya.PersistPlankCE.Payload` is the target's conclusion copied verbatim, with the index
  universe fixed at `Type`; `Kakeya.PersistPlankCE.payload_of_target` is the one-line check that
  the copy is exact (it is the target, applied). * `Kakeya.PersistPlankCE.not_payload` refutes it, for every `β ∈ (0, 1]`. * `Kakeya.PersistPlankCE.not_katzTaoEstimate_and_frostmanEstimate` combines the two: the target as
  stated implies `¬ (K_KT(β) ∧ K_F(β))`. It cites the sorried target and therefore carries
  `sorryAx`; that is the point of the statement, not a defect of it.

## The witness

`ι = ℕ`, `q = Finset.range N`, `T i = ` one fixed fully shaded `δ`-tube along `e₂`
(`Kakeya.PersistPlankCE.ST`), and `ρ = a = b = δ`.  The outer plank is the `δ × δ × 1` prism
around the same axis (`Kakeya.PersistPlankCE.P`), the coarse tube is the tube itself, and the
factor family has one block and one parent (`Kakeya.PersistPlankCE.CEfam`).

Every hypothesis holds, and every constant is independent of `N`:

* two-sided shaded uniformity at constant `1` (`Kakeya.PersistPlankCE.CEshadedUnif`) — one node at
  every grid scale, all branching numbers equal to `N`;
* fullness `1` (`Kakeya.PersistPlankCE.CEfullness`);
* `IsFrostmanIn` at `C_F = |B₁| / |T|` (`Kakeya.PersistPlankCE.isFrostman`) — both densities scale
  linearly in `N`, so the ratio does not see `N`;
* `PersistentPlankFactorization` at `C₀ = max 1 (8 / c₃)` with `c₃ = Tube.le_volume.c 3`
  (`Kakeya.PersistPlankCE.CEpersistent`) — the density clause reduces to
  `|δ × δ × 1 plank| ≤ C₀ · |δ-tube|`, which is `8 δ² ≤ C₀ · c₃ δ²`.

The multiplicity is exactly `N` (`Kakeya.PersistPlankCE.CEmultiplicity`) while the right-hand side
is `A · N ^ (1 - β/2)` with `A = Kakeya.PersistPlankCE.Aconst β δ` finite and `N`-free, so `N`
beyond `A ^ (2/β)` breaks it.

## Why the density clause does not save the statement

`PersistentPlankFactorization.maxDensity_le_mul` is what stops the *aspect-ratio* free lunch: with
all inner tubes of a block inside one `ρ`-tube, `|hull(fibre)| ≤ C ρ²`, so the clause forces
`8ab = |plank| ≤ C₀ · C ρ² ≤ C₀ · C a²`, i.e. `b / a ≲ C₀ ≤ δ ^ (-η)`, and the claimed gain
`(a/b) ^ (3β/2)` is at most a `δ ^ (-ε)`-absorbable loss.  It does **not** stop the *cardinality*
free lunch, because it is a statement about ratios of densities and every density in the witness
is homogeneous of degree one in `N`.

## The minimal repair

Add the clause every sibling form carries:

`(q : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)`

to `Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation`.  It kills this witness outright
(the `N` copies are not pairwise essentially distinct) and it is what
`Kakeya.FrostmanEstimate.multiplicity_bound_of_mem` — the estimate any proof of the target must
eventually reach — demands.  Its intended producer,
`Kakeya.multiplicity_le_of_relativePlankSelection`, can supply it, since the selection only ever
shrinks the index set.
-/

@[expose] public section

open MeasureTheory Metric Kakeya Convexity ConvexSpaceBody
open Tube (gridScale gridScale_self gridScale_antitone GridCoverSystem)
open scoped NNReal ENNReal

noncomputable section

namespace Kakeya.PersistPlankCE

/-! ### The witness geometry: one tube, one plank -/

abbrev E3 := EuclideanSpace ℝ (Fin 3)

def e2 : E3 := EuclideanSpace.single 2 (1:ℝ)

theorem norm_e2 : ‖e2‖ = 1 := by simp [e2]

theorem dist_pts : dist (-(1/2:ℝ) • e2) ((1/2:ℝ) • e2) = 1 := by
  rw [dist_eq_norm]
  have h : -(1/2:ℝ) • e2 - (1/2:ℝ) • e2 = (-1:ℝ) • e2 := by module
  rw [h, norm_smul]
  simp [norm_e2]

def T (δ : ℝ≥0) : Tube δ E3 := Tube.mk' δ dist_pts

/-- Every point of the segment is `c • e2` with `|c| ≤ 1/2`. -/
theorem mem_segment_iff {z : E3} :
    z ∈ segment ℝ (-(1/2:ℝ) • e2) ((1/2:ℝ) • e2) → ∃ c : ℝ, |c| ≤ 1/2 ∧ z = c • e2 := by
  rintro ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨(b - a)/2, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · module

theorem coord_e2 (c : ℝ) (i : Fin 3) : (c • e2) i = if i = 2 then c else 0 := by
  simp [e2]

theorem T_mem {δ : ℝ≥0} {x : E3} (hx : x ∈ (T δ).carrier) :
    ∃ c : ℝ, |c| ≤ 1/2 ∧ ‖x - c • e2‖ ≤ (δ:ℝ) := by
  rw [Tube.carrier_eq] at hx
  simp only [Set.mem_iUnion, Metric.mem_closedBall, exists_prop] at hx
  obtain ⟨z, hz, hd⟩ := hx
  obtain ⟨c, hc, rfl⟩ := mem_segment_iff hz
  exact ⟨c, hc, by rwa [← dist_eq_norm]⟩

theorem T_ball {δ : ℝ≥0} (hδ : δ ≤ 1/2) : (T δ).carrier ⊆ closedBall (0:E3) 1 := by
  intro x hx
  obtain ⟨c, hc, hd⟩ := T_mem hx
  have hδ' : (δ:ℝ) ≤ 1/2 := by exact_mod_cast hδ
  have : ‖c • e2‖ = |c| := by rw [norm_smul, norm_e2]; simp
  simp only [Metric.mem_closedBall, dist_zero_right]
  calc ‖x‖ = ‖(x - c • e2) + c • e2‖ := by congr 1; abel
    _ ≤ ‖x - c • e2‖ + ‖c • e2‖ := norm_add_le _ _
    _ ≤ 1/2 + 1/2 := by rw [this]; linarith
    _ = 1 := by norm_num


def P (δ : ℝ≥0) (hδ1 : δ ≤ 1) : Plank δ δ le_rfl hδ1 where
  toPrismNDim := PrismNDim.mk' (0 : E3) (EuclideanSpace.basisFun (Fin 3) ℝ) ![δ, δ, 1]
  thicknesses_eq := rfl

theorem mem_P_iff (δ : ℝ≥0) (hδ1 : δ ≤ 1) (x : E3) :
    x ∈ (P δ hδ1).carrier ↔ ∀ i, |x i| ≤ ((![δ,δ,1] i : ℝ≥0) : ℝ) := by
  rw [(P δ hδ1).mem_carrier_iff]
  simp [P, PrismNDim.mk']

theorem T_le_P {δ : ℝ≥0} (hδ : δ ≤ 1/2) (hδ1 : δ ≤ 1) :
    (T δ).toConvexSpaceBody ≤ (P δ hδ1).toConvexSpaceBody := by
  intro x hx
  obtain ⟨c, hc, hd⟩ := T_mem hx
  have hδ' : (δ:ℝ) ≤ 1/2 := by exact_mod_cast hδ
  refine (mem_P_iff δ hδ1 x).mpr ?_
  intro i
  have hstep : |x i| ≤ ‖x - c • e2‖ + |(c • e2) i| := by
    have h1 : |x i - (c • e2) i| ≤ ‖x - c • e2‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (x - c • e2) i
    calc |x i| = |(x i - (c • e2) i) + (c • e2) i| := by ring_nf
      _ ≤ |x i - (c • e2) i| + |(c • e2) i| := abs_add_le _ _
      _ ≤ _ := by linarith
  rw [coord_e2] at hstep
  by_cases hi : i = 2
  · subst hi
    rw [if_pos rfl] at hstep
    have hval : ((![δ,δ,1] (2 : Fin 3) : ℝ≥0) : ℝ) = 1 := by
      simp [Matrix.cons_val_two, Matrix.tail_cons]
    rw [hval]
    linarith
  · rw [if_neg hi] at hstep
    have hval : ((![δ,δ,1] i : ℝ≥0) : ℝ) = (δ : ℝ) := by
      have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl <;> norm_num
    rw [hval]
    simp only [abs_zero, add_zero] at hstep
    linarith


/-! ### Volumes -/

/-- The volume of the witness tube. -/
def m (δ : ℝ≥0) : ENNReal := volume (T δ).carrier

theorem m_ne_top (δ : ℝ≥0) : m δ ≠ ⊤ := (T δ).isCompact'.measure_ne_top

theorem finrank_E3 : Module.finrank ℝ E3 = 3 := by simp

theorem c3_mul_le (δ : ℝ≥0) :
    ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) * (δ : ENNReal) ^ 2 ≤ m δ := by
  have h := Tube.le_volume (T δ)
  rw [finrank_E3] at h
  exact (by simpa using h : _)

theorem m_pos {δ : ℝ≥0} (hδ : 0 < δ) : 0 < m δ := by
  refine lt_of_lt_of_le ?_ (c3_mul_le δ)
  have h1 : ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos 3).ne'
  have h2 : (δ : ENNReal) ^ 2 ≠ 0 := pow_ne_zero _ (ENNReal.coe_ne_zero.mpr hδ.ne')
  exact pos_iff_ne_zero.mpr (mul_ne_zero h1 h2)

/-- The plank-to-tube volume ratio constant. -/
def C0 : ℝ≥0 := max 1 (8 / Tube.le_volume.c 3)

theorem one_le_C0 : 1 ≤ C0 := le_max_left _ _

theorem volume_P_le (δ : ℝ≥0) (hδ1 : δ ≤ 1) :
    volume (P δ hδ1).carrier ≤ (C0 : ENNReal) * m δ := by
  have hc : Tube.le_volume.c 3 ≠ 0 := (Tube.le_volume.c_pos 3).ne'
  have key : (8 : ENNReal) = ((8 / Tube.le_volume.c 3 : ℝ≥0) : ENNReal) *
      ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) := by
    rw [← ENNReal.coe_mul, div_mul_cancel₀ _ hc]
    norm_num
  calc volume (P δ hδ1).carrier = 8 * (δ:ENNReal)^2 := by
        rw [Prism3D.volume_carrier]; simp; ring
    _ = ((8 / Tube.le_volume.c 3 : ℝ≥0) : ENNReal) *
          (((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) * (δ:ENNReal)^2) := by
        rw [key, mul_assoc]
    _ ≤ ((8 / Tube.le_volume.c 3 : ℝ≥0) : ENNReal) * m δ := by gcongr; exact c3_mul_le δ
    _ ≤ (C0 : ENNReal) * m δ := by
        gcongr
        exact_mod_cast le_max_right (1 : ℝ≥0) (8 / Tube.le_volume.c 3)


/-! ### The shaded family -/

def ST (δ : ℝ≥0) : ShadedTube δ E3 where
  toTube := T δ
  shade := (T δ).carrier
  measurableSet_shade := (T δ).isCompact'.measurableSet
  shade_subset := subset_rfl

theorem ST_shade (δ : ℝ≥0) : (ST δ).shade = (T δ).carrier := rfl
theorem ST_carrier (δ : ℝ≥0) : (ST δ).carrier = (T δ).carrier := rfl
theorem ST_toTube (δ : ℝ≥0) : (ST δ).toTube = T δ := rfl


/-! ### Density bookkeeping for a constant family -/

variable {ι : Type*}

open scoped Classical in
theorem const_sum_le (B : ConvexSpaceBody E3) (s : Finset ι) (K : ConvexSpaceBody E3) :
    ∑ i ∈ s with (fun _ : ι => B) i ≤ K, volume ((fun _ : ι => B) i).carrier
      ≤ (s.card : ENNReal) * volume K.carrier := by
  classical
  rcases Finset.eq_empty_or_nonempty (s.filter (fun i : ι => (fun _ : ι => B) i ≤ K)) with he | ⟨i0, hi0⟩
  · simp [he]
  · have hBK : B ≤ K := (Finset.mem_filter.mp hi0).2
    have hvol : volume B.carrier ≤ volume K.carrier := measure_mono hBK
    have hcard : (s.filter (fun i : ι => (fun _ : ι => B) i ≤ K)).card ≤ s.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    calc ∑ i ∈ s with (fun _ : ι => B) i ≤ K, volume ((fun _ : ι => B) i).carrier
        = ((s.filter (fun i : ι => (fun _ : ι => B) i ≤ K)).card : ENNReal) * volume B.carrier := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (s.card : ENNReal) * volume K.carrier := by
          refine mul_le_mul' ?_ hvol
          exact_mod_cast hcard

theorem const_maxDensity_le (B : ConvexSpaceBody E3) (s : Finset ι) :
    maxDensity s (fun _ : ι => B) ≤ (s.card : ENNReal) :=
  (isKatzTao_iff s (fun _ : ι => B) _).mpr (fun K => const_sum_le B s K)

theorem const_densityIn_eq (B : ConvexSpaceBody E3) (s : Finset ι) {K : ConvexSpaceBody E3}
    (h : B ≤ K) :
    densityIn s (fun _ : ι => B) K = (s.card : ENNReal) * volume B.carrier / volume K.carrier := by
  classical
  rw [densityIn_of_all_le (fun i _ => h), Finset.sum_const, nsmul_eq_mul]


/-! ### Uniformity of the witness family -/

theorem T_mono {δ ρ : ℝ≥0} (h : δ ≤ ρ) :
    (T δ).toConvexSpaceBody ≤ (T ρ).toConvexSpaceBody := by
  intro x hx
  have hx' : x ∈ (T δ).carrier := hx
  show x ∈ (T ρ).carrier
  rw [Tube.carrier_eq] at hx' ⊢
  simp only [Set.mem_iUnion, Metric.mem_closedBall, exists_prop] at hx' ⊢
  obtain ⟨z, hz, hd⟩ := hx'
  exact ⟨z, hz, hd.trans (by exact_mod_cast h)⟩

theorem delta_le_gridScale {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {M k : ℕ} (hk : k ≤ M) :
    δ ≤ gridScale δ M k := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have : k = 0 := Nat.le_zero.mp hk
    subst this
    simpa using hδ1
  · calc δ = gridScale δ M M := (gridScale_self δ hM).symm
      _ ≤ gridScale δ M k := gridScale_antitone hδ0 hδ1 M hk

open scoped Classical in
/-- The grid hierarchy of the witness family: one node at every scale. -/
def CEgrid (δ : ℝ≥0) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (Nn M : ℕ) :
    GridCoverSystem (Finset.range Nn) (fun _ : ℕ => (ST δ).toTube) M where
  indexSet := fun _ => {0}
  assign := fun _ _ => 0
  tube := fun k _ => T (gridScale δ M k)
  assign_mem := fun _ _ _ _ => Finset.mem_singleton_self 0
  le_tube_assign := fun k hk _ _ => T_mono (delta_le_gridScale hδ0 hδ1 hk)
  nested := fun _ _ _ _ _ _ _ => rfl
  tube_nested := fun k _ _ _ => T_mono (gridScale_antitone hδ0 hδ1 M (Nat.le_succ k))


section ClassicalBlock
open scoped Classical

theorem coverClass_eq (Nn : ℕ) :
    Tube.coverClass (Finset.range Nn) (fun _ : ℕ => (0:ℕ)) 0 = Finset.range Nn := by
  simp [Tube.coverClass]

theorem CEgrid_indexSet (δ : ℝ≥0) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (Nn M k : ℕ) :
    (CEgrid δ hδ0 hδ1 Nn M).indexSet k = {0} := rfl

theorem CEgrid_assign (δ : ℝ≥0) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (Nn M k : ℕ) :
    (CEgrid δ hδ0 hδ1 Nn M).assign k = fun _ : ℕ => (0:ℕ) := rfl

def CEunif (δ : ℝ≥0) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (Nn M : ℕ) :
    Tube.UniformTubeSet (Finset.range Nn) (fun _ : ℕ => (ST δ).toTube) M 1 where
  cover := CEgrid δ hδ0 hδ1 Nn M
  branchingN := fun _ => (Nn : ℝ≥0)
  tube_injOn := by
    intro k hk a ha b hb _
    simp only [CEgrid_indexSet, Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
  boundedOverlap := by
    intro k hk V
    rw [CEgrid_indexSet]
    have h : (({0} : Finset ℕ).filter (fun j => ∃ i ∈ Finset.range Nn,
        (ST δ).toConvexSpaceBody ≤ ((CEgrid δ hδ0 hδ1 Nn M).tube k j).toConvexSpaceBody ∧
        (ST δ).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤ ({0} : Finset ℕ).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have h2 : (({0} : Finset ℕ)).card = 1 := rfl
    rw [h2] at h
    exact_mod_cast h
  card_class_le := by
    intro k hk j hj
    have hj0 : j = 0 := Finset.mem_singleton.mp (by rwa [CEgrid_indexSet] at hj)
    subst hj0
    rw [CEgrid_assign, coverClass_eq]
    simp
  le_card_class := by
    intro k hk j hj
    have hj0 : j = 0 := Finset.mem_singleton.mp (by rwa [CEgrid_indexSet] at hj)
    subst hj0
    rw [CEgrid_assign, coverClass_eq]
    simp


theorem shadeClass_eq (δ : ℝ≥0) (Nn : ℕ) {x : E3} (hx : x ∈ (T δ).carrier) :
    ShadedTube.shadeClass (Finset.range Nn) (fun _ : ℕ => ST δ) (fun _ : ℕ => (0:ℕ)) 0 x
      = Finset.range Nn := by
  show (Tube.coverClass (Finset.range Nn) (fun _ : ℕ => (0:ℕ)) 0).filter
      (fun i => x ∈ ((fun _ : ℕ => ST δ) i).shade) = Finset.range Nn
  rw [coverClass_eq]
  exact Finset.filter_true_of_mem (fun i _ => hx)

def CEshadedUnif (δ : ℝ≥0) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (Nn M : ℕ) :
    ShadedTube.ShadedUniformTubeSet (Finset.range Nn) (fun _ : ℕ => ST δ) M 1 where
  tubeUniform := CEunif δ hδ0 hδ1 Nn M
  branchingN := fun _ => (Nn : ℝ≥0)
  localN := fun _ _ => (Nn : ℝ≥0)
  card_shadeClass_le := by
    intro x hx k hk i hi hxi
    have hxc : x ∈ (T δ).carrier := hxi
    rw [show (CEunif δ hδ0 hδ1 Nn M).cover.assign k = (fun _ : ℕ => (0:ℕ)) from rfl,
      shadeClass_eq δ Nn hxc]
    simp
  le_card_shadeClass := by
    intro x hx k hk i hi hxi
    have hxc : x ∈ (T δ).carrier := hxi
    rw [show (CEunif δ hδ0 hδ1 Nn M).cover.assign k = (fun _ : ℕ => (0:ℕ)) from rfl,
      shadeClass_eq δ Nn hxc]
    simp
  branchingN_le := by intro x hx k hk; simp
  le_branchingN := by intro x hx k hk; simp



end ClassicalBlock

/-! ### Frostman constant, factor family, and the plank factorisation -/

/-- The volume of the unit ball. -/
def vB : ENNReal := volume (ConvexSpaceBody.closedUnitBall (E := E3)).carrier

theorem vB_pos : 0 < vB := ConvexSpaceBody.closedUnitBall_volume_pos
theorem vB_ne_top : vB ≠ ⊤ := (ConvexSpaceBody.closedUnitBall (E := E3)).isCompact'.measure_ne_top

theorem ST_le_ball {δ : ℝ≥0} (hδ : δ ≤ 1/2) :
    (ST δ).toConvexSpaceBody ≤ (ConvexSpaceBody.closedUnitBall (E := E3)) :=
  T_ball hδ

theorem m_le_vB {δ : ℝ≥0} (hδ : δ ≤ 1/2) : m δ ≤ vB := measure_mono (T_ball hδ)

/-- The Frostman constant of the witness family. -/
def CF (δ : ℝ≥0) : ENNReal := vB / m δ

theorem one_le_CF {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ : δ ≤ 1/2) : 1 ≤ CF δ := by
  rw [CF, ENNReal.le_div_iff_mul_le (Or.inl (m_pos hδ0).ne') (Or.inl (m_ne_top δ)), one_mul]
  exact m_le_vB hδ

theorem CF_ne_top {δ : ℝ≥0} (hδ0 : 0 < δ) : CF δ ≠ ⊤ :=
  ENNReal.div_ne_top vB_ne_top (m_pos hδ0).ne'



theorem isFrostman (δ : ℝ≥0) (hδ0 : 0 < δ) (hδ : δ ≤ 1/2) (Nn : ℕ) :
    IsFrostmanIn (Finset.range Nn) (fun _ : ℕ => (ST δ).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall (CF δ) := by
  have hm0 : m δ ≠ 0 := (m_pos hδ0).ne'
  have hmt : m δ ≠ ⊤ := m_ne_top δ
  have hv0 : vB ≠ 0 := vB_pos.ne'
  have hvt : vB ≠ ⊤ := vB_ne_top
  have hdens : densityIn (Finset.range Nn) (fun _ : ℕ => (ST δ).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall = (Nn : ENNReal) * m δ / vB := by
    rw [const_densityIn_eq _ _ (ST_le_ball hδ)]
    simp only [Finset.card_range, vB, m, ST_carrier]
  have hkey : (Nn : ENNReal) ≤ CF δ * densityIn (Finset.range Nn)
      (fun _ : ℕ => (ST δ).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall := by
    rw [hdens, CF]
    have hone : vB / m δ * (m δ / vB) = 1 := by
      rw [← mul_div_assoc, ENNReal.div_mul_cancel hm0 hmt, ENNReal.div_self hv0 hvt]
    have : vB / m δ * ((Nn : ENNReal) * m δ / vB) = (Nn : ENNReal) := by
      rw [mul_div_assoc, ← mul_assoc, mul_comm (vB / m δ), mul_assoc, hone, mul_one]
    rw [this]
  intro K' hK'
  refine le_trans ?_ hkey
  refine ENNReal.div_le_of_le_mul ?_
  simpa [Finset.card_range] using
    const_sum_le ((ST δ).toConvexSpaceBody) (Finset.range Nn) K'


/-- The factor family: one block, one outer plank. -/
def CEfam (δ : ℝ≥0) (hδ : δ ≤ 1/2) (hδ1 : δ ≤ 1) (Nn : ℕ) :
    ConvexSpaceBody.FactorFamily E3 ℕ (Finset ℕ) where
  innerSet := Finset.range Nn
  innerBody := fun _ => (ST δ).toConvexSpaceBody
  outerSet := {Finset.range Nn}
  outerBody := fun _ => (P δ hδ1).toConvexSpaceBody
  parent := fun _ => Finset.range Nn
  parent_mem := fun _ _ => Finset.mem_singleton_self _
  inner_le_parent := fun _ _ => T_le_P hδ hδ1

theorem CEfam_image (δ : ℝ≥0) (hδ : δ ≤ 1/2) (hδ1 : δ ≤ 1) {Nn : ℕ} (hNn : 0 < Nn) :
    (CEfam δ hδ hδ1 Nn).innerSet.image (CEfam δ hδ hδ1 Nn).parent = {Finset.range Nn} := by
  have : (Finset.range Nn).Nonempty := Finset.nonempty_range_iff.mpr hNn.ne'
  simp [CEfam, Finset.image_const this]

theorem CEfam_fiber (δ : ℝ≥0) (hδ : δ ≤ 1/2) (hδ1 : δ ≤ 1) (Nn : ℕ) :
    (CEfam δ hδ hδ1 Nn).fiber (Finset.range Nn) = Finset.range Nn := by
  classical
  simp [ConvexSpaceBody.FactorFamily.fiber, CEfam]


theorem CEpersistent (δ : ℝ≥0) (hδ0 : 0 < δ) (hδ : δ ≤ 1/2) (hδ1 : δ ≤ 1) {Nn : ℕ}
    (_hNn : 0 < Nn) :
    PersistentPlankFactorization (CEfam δ hδ hδ1 Nn) δ δ le_rfl hδ1 C0 where
  outer_are_planks := fun j _ => ⟨P δ hδ1, rfl⟩
  outer_isKatzTao := by
    letI : DecidableEq (Finset ℕ) := fun a b => Classical.propDecidable (a = b)
    rw [IsKatzTao_def]
    refine le_trans (const_maxDensity_le ((P δ hδ1).toConvexSpaceBody) _) ?_
    have hgen : ∀ s : Finset (Finset ℕ), s ⊆ {Finset.range Nn} →
        ((s.card : ENNReal) ≤ (C0 : ENNReal)) := by
      intro s hs
      have hc : s.card ≤ 1 := by simpa using Finset.card_le_card hs
      calc ((s.card : ENNReal)) ≤ 1 := by exact_mod_cast hc
        _ ≤ (C0 : ENNReal) := by exact_mod_cast one_le_C0
    exact hgen _ (Finset.image_subset_iff.mpr (fun i _ => Finset.mem_singleton_self _))
  maxDensity_le_mul := by
    letI : DecidableEq (Finset ℕ) := fun a b => Classical.propDecidable (a = b)
    intro j hj
    have hjeq : j = Finset.range Nn := by
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hj
      exact hi.symm
    subst hjeq
    have hvP0 : volume (P δ hδ1).carrier ≠ 0 := (Prism3D.volume_pos_of_pos _ hδ0).ne'
    have hvPt : volume (P δ hδ1).carrier ≠ ⊤ := (P δ hδ1).isCompact'.measure_ne_top
    have hden : densityIn ((CEfam δ hδ hδ1 Nn).fiber (Finset.range Nn))
        (CEfam δ hδ hδ1 Nn).innerBody ((CEfam δ hδ hδ1 Nn).outerBody (Finset.range Nn))
        = (Nn : ENNReal) * m δ / volume (P δ hδ1).carrier := by
      rw [CEfam_fiber,
        show (CEfam δ hδ hδ1 Nn).innerBody = fun _ : ℕ => (ST δ).toConvexSpaceBody from rfl,
        show (CEfam δ hδ hδ1 Nn).outerBody (Finset.range Nn)
          = (P δ hδ1).toConvexSpaceBody from rfl,
        const_densityIn_eq ((ST δ).toConvexSpaceBody) (Finset.range Nn)
          (show (ST δ).toConvexSpaceBody ≤ (P δ hδ1).toConvexSpaceBody from T_le_P hδ hδ1)]
      simp only [Finset.card_range, m, ST_carrier]
    refine le_trans (const_maxDensity_le ((ST δ).toConvexSpaceBody)
      (CEfam δ hδ hδ1 Nn).innerSet) ?_
    rw [show (CEfam δ hδ hδ1 Nn).innerSet = Finset.range Nn from rfl, Finset.card_range, hden,
      ← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hvP0) (Or.inl hvPt)]
    calc (Nn : ENNReal) * volume (P δ hδ1).carrier
        ≤ (Nn : ENNReal) * ((C0 : ENNReal) * m δ) := by gcongr; exact volume_P_le δ hδ1
      _ = (C0 : ENNReal) * ((Nn : ENNReal) * m δ) := by ring


/-! ### Multiplicity and fullness of the witness family -/

theorem sum_shade (δ : ℝ≥0) (Nn : ℕ) :
    ∑ i ∈ Finset.range Nn, volume ((fun _ : ℕ => (ST δ).toShadedBody) i).shade
      = (Nn : ENNReal) * m δ := by
  simp [ST_shade, m]

theorem iUnion_shade (δ : ℝ≥0) {Nn : ℕ} (hNn : 0 < Nn) :
    (⋃ i ∈ Finset.range Nn, ((fun _ : ℕ => (ST δ).toShadedBody) i).shade) = (T δ).carrier := by
  ext x
  simp only [Set.mem_iUnion, exists_prop, ST_shade]
  exact ⟨fun ⟨_, _, hx⟩ => hx, fun hx => ⟨0, Finset.mem_range.mpr hNn, hx⟩⟩

theorem CEmultiplicity (δ : ℝ≥0) (hδ0 : 0 < δ) {Nn : ℕ} (hNn : 0 < Nn) :
    ShadedBody.multiplicity (Finset.range Nn) (fun _ : ℕ => (ST δ).toShadedBody)
      = (Nn : ENNReal) := by
  rw [ShadedBody.multiplicity_eq_div, sum_shade, iUnion_shade δ hNn]
  rw [show volume (T δ).carrier = m δ from rfl, mul_div_assoc,
    ENNReal.div_self (m_pos hδ0).ne' (m_ne_top δ), mul_one]

theorem CEfullness (δ : ℝ≥0) (hδ0 : 0 < δ) {Nn : ℕ} (hNn : 0 < Nn) :
    ShadedBody.fullness (Finset.range Nn) (fun _ : ℕ => (ST δ).toShadedBody) = 1 := by
  have hNe : ((Nn : ENNReal) * m δ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hNn.ne') (m_pos hδ0).ne'
  have hNt : ((Nn : ENNReal) * m δ) ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top Nn) (m_ne_top δ)
  have hc : ∑ i ∈ Finset.range Nn, volume ((fun _ : ℕ => (ST δ).toShadedBody) i).carrier
      = (Nn : ENNReal) * m δ := by simp [m]; rfl
  have : ShadedBody.fullness' (Finset.range Nn) (fun _ : ℕ => (ST δ).toShadedBody) = 1 := by
    rw [show ShadedBody.fullness' (Finset.range Nn) (fun _ : ℕ => (ST δ).toShadedBody)
      = (∑ i ∈ Finset.range Nn, volume ((fun _ : ℕ => (ST δ).toShadedBody) i).shade) /
        (∑ i ∈ Finset.range Nn, volume ((fun _ : ℕ => (ST δ).toShadedBody) i).carrier) from rfl,
      sum_shade, hc, ENNReal.div_self hNe hNt]
  rw [ShadedBody.fullness, this]
  rfl


/-! ### The payload, and its refutation -/

open Classical in
/-- The conclusion of `Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation`, verbatim,
with the index universe fixed at `Type`. -/
def Payload (β : ℝ) : Prop :=
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0),
      ∀ {ι : Type} (q : Finset ι) {δ : ℝ≥0} (_hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        δ ≤ δ₀ →
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∃ C : ℝ≥0, C ≤ δ ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet q T
            (Tube.ssfGridLen δ) C)) →
        (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
          {κ : Type} (r : Finset κ)
          (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (assign : ι → κ),
          δ ≤ ρ → ρ ≤ a →
          (∀ i ∈ q, assign i ∈ r ∧
            (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody) →
          ∀ (C₀ : ℝ≥0), C₀ ≤ δ ^ (-η) →
            ∀ (F : κ → ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι (Finset ι)),
              (∀ k ∈ r, (F k).innerSet = {i ∈ q | assign i = k}) →
              (∀ k ∈ r, (F k).innerBody = fun i => (T i).toConvexSpaceBody) →
              (∀ k ∈ r, PersistentPlankFactorization (F k) a b hab hb1 C₀) →
          ∀ (CF : ENNReal), 1 ≤ CF → CF ≠ ⊤ →
            IsFrostmanIn q (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall CF →
            ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
              (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2)
                * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
                * (δ : ENNReal) ^ (-2 * β)
                * ((δ : ENNReal) ^ 2 * (q.card : ENNReal)) ^ (1 - β / 2)

/-- **The pre-repair shape of `Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation`.**

`Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation` has since been repaired --- it now
carries the essential-distinctness clause `(q : Set ι).Pairwise (fun i j =>
IsEssentiallyDistinct (T i).carrier (T j).carrier)` and no longer takes `K_KT(β)` or the two-sided
`ShadedTube.ShadedUniformTubeSet` --- so it no longer *has* this shape and this file can no longer
cite it.  It does not need to: the refutation is about the **shape**, not about any one
declaration bearing it, and the shape is spelled out verbatim here.

This is deliberately a hypothesis rather than an application, following
`Kakeya.WolffHairbrush.…` and `Kakeya.FrostmanOrDone.…`: the file stays a permanent compatibility.  Any
future declaration of the pre-repair shape can be fed to
`Kakeya.PersistPlankCE.not_target_shape` or `Kakeya.PersistPlankCE.false_of_target` and yields
`False`. -/
def TargetShape.{w₁, w₂} (β : ℝ) : Prop :=
    0 < β → β ≤ 1 →
      KatzTaoEstimate.{w₁} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{w₂} (EuclideanSpace ℝ (Fin 3)) β → Payload β

/-- The payload is what the pre-repair shape delivers. -/
theorem payload_of_targetShape.{w₁, w₂} {β : ℝ} (target : TargetShape.{w₁, w₂} β)
    (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate.{w₁} (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate.{w₂} (EuclideanSpace ℝ (Fin 3)) β) : Payload β :=
  target hβpos hβle hKKT hKF


/-- The `N`-independent constant of the witness configuration. -/
def Aconst (β : ℝ) (δ : ℝ≥0) : ENNReal :=
  (δ : ENNReal) ^ (-(1:ℝ)) * CF δ ^ (1 - β / 2)
    * ((δ : ENNReal) / (δ : ENNReal)) ^ (3 * β / 2)
    * (δ : ENNReal) ^ (-2 * β) * (((δ : ENNReal) ^ 2) ^ (1 - β / 2))

theorem not_payload {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1) : ¬ Payload β := by
  intro hP
  obtain ⟨η, hη, δ₀, hδ₀, hbound⟩ := hP 1 one_pos
  obtain ⟨δ₁, hδ₁pos, hthr⟩ := exists_threshold_le_rpow_neg C0 one_le_C0 hη
  set δ : ℝ≥0 := min (min δ₀ δ₁) (1/2) with hδdef
  have hδ0 : 0 < δ := lt_min (lt_min hδ₀ hδ₁pos) (by norm_num)
  have hδδ₀ : δ ≤ δ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδδ₁ : δ ≤ δ₁ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδhalf : δ ≤ 1/2 := min_le_right _ _
  have hδ1 : δ ≤ 1 := le_trans hδhalf (by norm_num)
  have hC0δ : C0 ≤ δ ^ (-η) := hthr δ hδ0 hδδ₁
  have hone : (1:ℝ≥0) ≤ δ ^ (-η) := by
    calc (1:ℝ≥0) = δ ^ (0:ℝ) := (NNReal.rpow_zero δ).symm
      _ ≤ δ ^ (-η) := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  have hfullthr : δ ^ η ≤ 1 := NNReal.rpow_le_one hδ1 hη.le
  -- the instance bound, for every `N`
  have key : ∀ Nn : ℕ, 0 < Nn →
      (Nn : ENNReal) ≤ Aconst β δ * (Nn : ENNReal) ^ (1 - β / 2) := by
    intro Nn hNn
    have hres := hbound (ι := ℕ) (Finset.range Nn) (δ := δ) hδ0 (fun _ => ST δ) hδδ₀
      (fun i _ => T_ball hδhalf)
      ⟨1, hone, ⟨CEshadedUnif δ hδ0 hδ1 Nn (Tube.ssfGridLen δ)⟩⟩
      (by rw [CEfullness δ hδ0 hNn]; exact hfullthr)
      δ δ δ le_rfl hδ1 (κ := Unit) {()} (fun _ => T δ) (fun _ => ()) le_rfl le_rfl
      (fun i _ => ⟨Finset.mem_singleton_self _, le_rfl⟩)
      C0 hC0δ (fun _ => CEfam δ hδhalf hδ1 Nn)
      (by intro k _; simp [CEfam])
      (by intro k _; rfl)
      (fun k _ => CEpersistent δ hδ0 hδhalf hδ1 hNn)
      (CF δ) (one_le_CF hδ0 hδhalf) (CF_ne_top hδ0) (isFrostman δ hδ0 hδhalf Nn)
    rw [CEmultiplicity δ hδ0 hNn, Finset.card_range] at hres
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0:ℝ) ≤ 1 - β / 2)] at hres
    calc (Nn : ENNReal) ≤ _ := hres
      _ = Aconst β δ * (Nn : ENNReal) ^ (1 - β / 2) := by rw [Aconst]; ring
  -- the constant is finite
  have hδE0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδEt : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hexp : (0:ℝ) ≤ 1 - β / 2 := by linarith
  have hAtop : Aconst β δ ≠ ⊤ := by
    rw [Aconst, ENNReal.div_self hδE0 hδEt, ENNReal.one_rpow, mul_one]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ?_) ?_
    · rw [← ENNReal.coe_rpow_of_ne_zero hδ0.ne']; exact ENNReal.coe_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg hexp (CF_ne_top hδ0)
    · rw [← ENNReal.coe_rpow_of_ne_zero hδ0.ne']; exact ENNReal.coe_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg hexp (by simp [ENNReal.pow_ne_top hδEt])
  have hAmaxtop : Aconst β δ ^ (2 / β) ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg (by positivity) hAtop
  obtain ⟨Nn0, hNn0⟩ := ENNReal.exists_nat_gt hAmaxtop
  set Nn : ℕ := max Nn0 1 with hNndef
  have hNn : 0 < Nn := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlt : Aconst β δ ^ (2 / β) < (Nn : ENNReal) := by
    refine lt_of_lt_of_le hNn0 ?_
    exact_mod_cast Nat.cast_le.mpr (le_max_left Nn0 1)
  have hNe0 : (Nn : ENNReal) ≠ 0 := by exact_mod_cast hNn.ne'
  have hNet : (Nn : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top Nn
  have hk := key Nn hNn
  have hk2 : (Nn : ENNReal) ^ (β/2) * (Nn : ENNReal) ^ (1 - β/2)
      ≤ Aconst β δ * (Nn : ENNReal) ^ (1 - β/2) := by
    rw [← ENNReal.rpow_add _ _ hNe0 hNet, show β/2 + (1 - β/2) = 1 by ring, ENNReal.rpow_one]
    exact hk
  have hcancel : (Nn : ENNReal) ^ (β/2) ≤ Aconst β δ := by
    have hc0 : (Nn : ENNReal) ^ (1 - β/2) ≠ 0 := by
      simp [ENNReal.rpow_eq_zero_iff, hNe0, hNet]
    have hct : (Nn : ENNReal) ^ (1 - β/2) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg hexp hNet
    exact (ENNReal.mul_le_mul_iff_left hc0 hct).mp hk2
  have hfinal : (Nn : ENNReal) ≤ Aconst β δ ^ (2 / β) := by
    have := ENNReal.rpow_le_rpow hcancel (by positivity : (0:ℝ) ≤ 2 / β)
    rwa [← ENNReal.rpow_mul, show β / 2 * (2 / β) = 1 by field_simp, ENNReal.rpow_one] at this
  exact absurd hfinal (not_le.mpr hlt)

/-- **The target as stated can only be proved by refuting its own hypotheses.**

`Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation` yields
`Kakeya.PersistPlankCE.Payload β` from `K_KT(β)` and `K_F(β)`
(`Kakeya.PersistPlankCE.payload_of_target`), and the payload is false
(`Kakeya.PersistPlankCE.not_payload`).  So the two partial estimates cannot both hold at any
`β ∈ (0, 1]` — which is not a theorem anyone wants, and is the precise sense in which the target
is broken. -/
theorem not_katzTaoEstimate_and_frostmanEstimate.{w₁, w₂} {β : ℝ}
    (target : TargetShape.{w₁, w₂} β) (hβpos : 0 < β) (hβle : β ≤ 1) :
    ¬ (KatzTaoEstimate.{w₁} (EuclideanSpace ℝ (Fin 3)) β ∧
        FrostmanEstimate.{w₂} (EuclideanSpace ℝ (Fin 3)) β) := by
  rintro ⟨hKKT, hKF⟩
  exact not_payload hβpos hβle (payload_of_targetShape target hβpos hβle hKKT hKF)


/-- **The local persistent-plank implication yields `False`.**

Its estimate assumptions are satisfiable: at `β = 1`, they follow from
`Kakeya.KatzTao_one` in `Kakeya/PartialEstimates.lean` and
`Kakeya.frostmanEstimate_one` in
`Kakeya/DimensionThree/FrostmanEstimateOne.lean`. Thus the implication
refuted by `Kakeya.PersistPlankCE.not_katzTaoEstimate_and_frostmanEstimate`
is false, rather than vacuously true. See `Kakeya/RelativePlankRepair.lean`
for the corrected condition. -/
theorem false_of_target
    (target : ∀ {β : ℝ}, 0 < β → β ≤ 1 →
      KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β → Payload β) : False :=
  not_payload one_pos le_rfl (target one_pos le_rfl KatzTao_one frostmanEstimate_one)

end Kakeya.PersistPlankCE

namespace Kakeya

/-! ### The repaired statement is not vacuous

The failure mode this guards against is closing a goal from an unsatisfiable hypothesis bundle: an
inconsistent bundle compiles green and `#print axioms` cannot see it.  Every hypothesis of
`Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation` (and of its stronger form
`Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation_of_essDistinct`) is met simultaneously,
with `q` nonempty, by the configuration of this file taken at **one**
tube instead of `N` — at which the essential-distinctness clause is vacuous but everything else is
unchanged, since none of the other constants ever saw `N`.
-/

open PersistPlankCE in
/-- **Every hypothesis of the repaired proposition is simultaneously satisfiable, with `q`
nonempty.** -/
theorem persistentPlank_hypotheses_satisfiable {δ : ℝ≥0} (hδ0 : 0 < δ) (hδhalf : δ ≤ 1/2)
    (hδ1 : δ ≤ 1) :
    (Finset.range 1).Nonempty ∧
    (∀ i ∈ Finset.range 1, ((fun _ : ℕ => ST δ) i).carrier ⊆ Metric.closedBall 0 1) ∧
    ((Finset.range 1 : Finset ℕ) : Set ℕ).Pairwise
      (fun i j => IsEssentiallyDistinct
        (((fun _ : ℕ => ST δ) i).carrier) (((fun _ : ℕ => ST δ) j).carrier)) ∧
    ShadedBody.fullness (Finset.range 1) (fun _ : ℕ => (ST δ).toShadedBody) = 1 ∧
    (∀ i ∈ Finset.range 1, ((fun _ : ℕ => ST δ) i).toConvexSpaceBody
      ≤ (T δ).toConvexSpaceBody) ∧
    (CEfam δ hδhalf hδ1 1).innerSet = {i ∈ Finset.range 1 | (fun _ : ℕ => ()) i = ()} ∧
    ((CEfam δ hδhalf hδ1 1).innerBody
      = fun i => ((fun _ : ℕ => ST δ) i).toConvexSpaceBody) ∧
    PersistentPlankFactorization (CEfam δ hδhalf hδ1 1) δ δ le_rfl hδ1 C0 ∧
    IsFrostmanIn (Finset.range 1) (fun _ : ℕ => (ST δ).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall (CF δ) := by
  refine ⟨⟨0, by simp⟩, fun i _ => T_ball hδhalf, ?_, CEfullness δ hδ0 one_pos,
    fun i _ => le_rfl, ?_, rfl, CEpersistent δ hδ0 hδhalf hδ1 one_pos,
    isFrostman δ hδ0 hδhalf 1⟩
  · intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    omega
  · simp [CEfam]

end Kakeya
