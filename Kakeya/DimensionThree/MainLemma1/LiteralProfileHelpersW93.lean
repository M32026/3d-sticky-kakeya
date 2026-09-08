module

public import Mathlib
public import Kakeya.Uniform
public import Kakeya.ShadedUniform
public import Kakeya.DimensionThree.MainLemma1.Setup
public import Kakeya.DimensionThree.Plank.PlankFactorizationEstimate
public import Kakeya.FibreCommon
public import Kakeya.MultiScaleFac
public import Kakeya.DimensionThree.Plank.InnerEDAssembly

@[expose] public section

namespace Kakeya.ml1Boot.RevisedInnerTrialRestartW74

def profilePotential (M : Nat) (p : Fin (M + 1) → Fin (M + 1) → Real) : Real :=
  ∑ a : Fin (M + 1), ∑ b : Fin (M + 1), p a b

structure ProfileStateW74 (M : Nat) where
  coord : Fin (M + 1) → Fin (M + 1) → Real
  coord_nonneg : ∀ a b, 0 ≤ coord a b
  coord_upper : ∀ a b, coord a b ≤ 7
  /-- The finite profile budget, recorded at construction time. -/
  potential_bound : profilePotential M coord ≤
    (7 : Real) * (((M + 1 : Nat) : Real) ^ 2)

end Kakeya.ml1Boot.RevisedInnerTrialRestartW74

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology Set
open scoped NNReal ENNReal BigOperators

namespace Kakeya.ml1Boot.RevisedLiteralProfileInterfaceFormalizerW87

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

universe uE uI uP

variable {E : Type uE}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [ProperSpace E]
  [MeasurableSpace E] [BorelSpace E]

open Kakeya.ml1Boot.RevisedInnerTrialRestartW74

abbrev CanonicalProfileNetW87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    (base : Finset iota) (T : iota -> Tube delta E)
    (M : Nat) (C : NNReal) :=
  Tube.UniformTubeSet base T M C

noncomputable def canonicalAncestorFamilyW87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} (U : CanonicalProfileNetW87 base T M C)
    (F : Finset iota) (q : Fin (M + 1)) : Finset iota :=
  F.image (U.cover.assign q.val)

/-- A level-`q` canonical node, distinguished in the type from a fine leaf. -/

abbrev CanonicalQNodeW87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} (U : CanonicalProfileNetW87 base T M C)
    (current : Finset iota) (q : Fin (M + 1)) :=
  {w : iota // w ∈ canonicalAncestorFamilyW87 U current q}

/-- The complete finite type of canonical `q`-nodes realized by `current`. -/

noncomputable def canonicalQNodeFinsetW87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} (U : CanonicalProfileNetW87 base T M C)
    (current : Finset iota) (q : Fin (M + 1)) :
    Finset (CanonicalQNodeW87 U current q) :=
  (canonicalAncestorFamilyW87 U current q).attach

/-- Forget the node subtype only at the legal bridge back to hierarchy labels. -/

noncomputable def canonicalQNodeValuesW87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base current : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} {U : CanonicalProfileNetW87 base T M C}
    {q : Fin (M + 1)}
    (nodes : Finset (CanonicalQNodeW87 U current q)) : Finset iota :=
  nodes.image Subtype.val

noncomputable def saturatedFineLiftW87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} (U : CanonicalProfileNetW87 base T M C)
    (current : Finset iota) (q : Fin (M + 1))
    (keptNodes : Finset iota) : Finset iota :=
  current.filter fun i => U.cover.assign q.val i ∈ keptNodes

theorem saturatedFineLift_subset_w87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base current keptNodes : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} (U : CanonicalProfileNetW87 base T M C)
    (q : Fin (M + 1)) :
    saturatedFineLiftW87 U current q keptNodes <= current := by
  intro i hi
  exact (Finset.mem_filter.mp hi).1


/-! ## Exact full-pass weighted mass and same-witness output -/

theorem exists_heaviestFiber_ennreal_w87
    {alpha nu : Type*} [Fintype nu] [DecidableEq nu] [Nonempty nu]
    (A : Finset alpha) (weight : alpha -> ENNReal)
    (label : alpha -> nu) (hpos : 0 < ∑ a ∈ A, weight a) :
    exists v : nu,
      (∑ a ∈ A, weight a) <=
        (Fintype.card nu : ENNReal) *
          (∑ a ∈ A.filter (fun a => label a = v), weight a) := by
  classical
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image Finset.univ
    (fun v : nu => ∑ a ∈ A.filter (fun a => label a = v), weight a)
    Finset.univ_nonempty
  refine ⟨v, ?_⟩
  calc
    (∑ a ∈ A, weight a) =
        ∑ v : nu, ∑ a ∈ A.filter (fun a => label a = v), weight a :=
      (Finset.sum_fiberwise A label weight).symm
    _ <= ∑ _v : nu, ∑ a ∈ A.filter (fun a => label a = v), weight a := by
      exact Finset.sum_le_sum hv
    _ = _ := by simp [nsmul_eq_mul]

noncomputable def sourceLambdaMNatW87 (delta : NNReal) (CM : Nat) : Nat :=
  Nat.ceil ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ CM)

noncomputable def sourceLambdaINatW87 (delta : NNReal) (CM : Nat) : Nat :=
  Nat.ceil ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ CM)

noncomputable def sourceLambdaBalNatW87 (delta : NNReal) (CM : Nat) : Nat :=
  Nat.ceil ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ CM)

abbrev FullPassLabelW87 (delta : NNReal) (M CM : Nat) :=
  Fin 4 × Fin (M + 1) × Fin (sourceLambdaMNatW87 delta CM) ×
    Fin (sourceLambdaINatW87 delta CM) ×
      Fin (sourceLambdaBalNatW87 delta CM)

noncomputable def fullPassDenominatorW87
    (delta : NNReal) (M CM : Nat) : ENNReal :=
  4 * ((M + 1 : Nat) : ENNReal) * (sourceLambdaMNatW87 delta CM : ENNReal) *
    (sourceLambdaINatW87 delta CM : ENNReal) *
      (sourceLambdaBalNatW87 delta CM : ENNReal)

noncomputable def dropAtomPartW87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base current : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} (U : CanonicalProfileNetW87 base T M C)
    (q : Fin (M + 1)) (w : CanonicalQNodeW87 U current q) : Finset iota :=
  Tube.coverClass current (U.cover.assign q.val) w.val

noncomputable def dropAtomWeightW87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base current : Finset iota} {T : iota -> ShadedTube delta E}
    {M : Nat} {C : NNReal}
    (U : CanonicalProfileNetW87 base (fun i => (T i).toTube) M C)
    (q : Fin (M + 1)) (Y : iota -> ShadedTube delta E)
    (w : CanonicalQNodeW87 U current q) : ENNReal :=
  ∑ i ∈ dropAtomPartW87 U q w, volume (Y i).shade

structure FullPassSelectionInputW87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base : Finset iota} {T : iota -> ShadedTube delta E}
    {M CM : Nat} {C : NNReal} (current : Finset iota)
    (U : CanonicalProfileNetW87 base
      (fun i => (T i).toTube) M C)
    (q : Fin (M + 1)) where
  current_subset : current <= base
  current_nonempty : current.Nonempty
  Ydagger : iota -> ShadedTube delta E
  same_tube : ∀ i ∈ current,
    (Ydagger i).toTube = (T i).toTube
  subshading : ∀ i ∈ current, (Ydagger i).shade <= (T i).shade
  current_mass_pos : 0 < ∑ i ∈ current, volume (Ydagger i).shade
  branchBucket : CanonicalQNodeW87 U current q -> Fin 4
  scaleBucket : CanonicalQNodeW87 U current q -> Fin (M + 1)
  towerBucket : CanonicalQNodeW87 U current q ->
    Fin (sourceLambdaMNatW87 delta CM)
  innerBucket : CanonicalQNodeW87 U current q ->
    Fin (sourceLambdaINatW87 delta CM)
  balancedBucket : CanonicalQNodeW87 U current q ->
    Fin (sourceLambdaBalNatW87 delta CM)
  Ktr : Nat
  Ktr_pos : 0 < Ktr
  Ktr_le_CM : Ktr <= CM

noncomputable def fullPassJointLabelW87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base current : Finset iota} {T : iota -> ShadedTube delta E}
    {M CM : Nat} {C : NNReal}
    {U : CanonicalProfileNetW87 base (fun i => (T i).toTube) M C}
    {q : Fin (M + 1)}
    (I : FullPassSelectionInputW87 (CM := CM) current U q)
    (w : CanonicalQNodeW87 U current q) : FullPassLabelW87 delta M CM :=
  (I.branchBucket w, I.scaleBucket w, I.towerBucket w,
    I.innerBucket w, I.balancedBucket w)

/-- The source's full-pass shaded-mass selection is a theorem, not an input field. -/

theorem exists_fullPass_saturated_selection_w87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base current : Finset iota} {T : iota -> ShadedTube delta E}
    {M CM : Nat} {C : NNReal}
    (U : CanonicalProfileNetW87 base (fun i => (T i).toTube) M C)
    (q : Fin (M + 1))
    (I : FullPassSelectionInputW87 (CM := CM) current U q)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hM : 0 < M) (hCM : 0 < CM) :
    exists selected : FullPassLabelW87 delta M CM,
    exists keptNodes : Finset (CanonicalQNodeW87 U current q),
    exists next : Finset iota, exists YPlus : iota -> ShadedTube delta E,
      keptNodes = (canonicalQNodeFinsetW87 U current q).filter
        (fun w => fullPassJointLabelW87 I w = selected) /\
      next = saturatedFineLiftW87 U current q
        (canonicalQNodeValuesW87 keptNodes) /\
      next.Nonempty /\
      next <= current /\
      (∀ i ∈ next,
        (YPlus i).toTube = (T i).toTube /\
          (YPlus i).shade <= (I.Ydagger i).shade) /\
      (fullPassDenominatorW87 delta M CM) ^ (-1 : Int) *
          (∑ i ∈ current, volume (I.Ydagger i).shade) <=
        ∑ i ∈ next, volume (YPlus i).shade := by
  classical
  obtain ⟨i0, hi0⟩ := I.current_nonempty
  let w0 : CanonicalQNodeW87 U current q :=
    ⟨U.cover.assign q.val i0, Finset.mem_image_of_mem _ hi0⟩
  letI : Nonempty (FullPassLabelW87 delta M CM) :=
    ⟨fullPassJointLabelW87 I w0⟩
  have hmass (nodes : Finset (CanonicalQNodeW87 U current q)) :
      (∑ w ∈ nodes, dropAtomWeightW87 U q I.Ydagger w) =
        ∑ i ∈ saturatedFineLiftW87 U current q
          (canonicalQNodeValuesW87 nodes), volume (I.Ydagger i).shade := by
    unfold dropAtomWeightW87 dropAtomPartW87 saturatedFineLiftW87
      canonicalQNodeValuesW87 Tube.coverClass
    rw [← Finset.sum_fiberwise_eq_sum_filter current (nodes.image Subtype.val)
      (U.cover.assign q.val) (fun i => volume (I.Ydagger i).shade)]
    symm
    convert Finset.sum_image (s := nodes) (g := Subtype.val)
      (f := fun j : iota => ∑ i ∈ current.filter
        (fun i => U.cover.assign q.val i = j), volume (I.Ydagger i).shade)
      (fun a _ b _ h => Subtype.ext h) using 1
    apply Finset.sum_congr rfl
    intro w _
    congr 1
    ext i
    simp only [Finset.mem_filter]
  have hall : canonicalQNodeValuesW87 (canonicalQNodeFinsetW87 U current q) =
      canonicalAncestorFamilyW87 U current q := by
    simp [canonicalQNodeValuesW87, canonicalQNodeFinsetW87]
  have hlift : saturatedFineLiftW87 U current q
      (canonicalQNodeValuesW87 (canonicalQNodeFinsetW87 U current q)) = current := by
    rw [hall]
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact Finset.mem_image_of_mem _ hi
  have htotal : (∑ w ∈ canonicalQNodeFinsetW87 U current q,
      dropAtomWeightW87 U q I.Ydagger w) =
      ∑ i ∈ current, volume (I.Ydagger i).shade := by
    rw [hmass, hlift]
  obtain ⟨selected, hselected⟩ := exists_heaviestFiber_ennreal_w87
    (canonicalQNodeFinsetW87 U current q) (dropAtomWeightW87 U q I.Ydagger)
    (fullPassJointLabelW87 I) (htotal.symm ▸ I.current_mass_pos)
  let keptNodes := (canonicalQNodeFinsetW87 U current q).filter
    (fun w => fullPassJointLabelW87 I w = selected)
  let next := saturatedFineLiftW87 U current q (canonicalQNodeValuesW87 keptNodes)
  have hcard : (Fintype.card (FullPassLabelW87 delta M CM) : ENNReal) =
      fullPassDenominatorW87 delta M CM := by
    simp [FullPassLabelW87, fullPassDenominatorW87, mul_assoc]
  have hpaid : (∑ i ∈ current, volume (I.Ydagger i).shade) <=
      fullPassDenominatorW87 delta M CM *
        ∑ i ∈ next, volume (I.Ydagger i).shade := by
    simpa only [htotal, hcard, hmass] using hselected
  have hnext : next.Nonempty := by
    by_contra h
    have hempty : next = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hempty, Finset.sum_empty, mul_zero] at hpaid
    exact (not_le_of_gt I.current_mass_pos) hpaid
  have hD0 : fullPassDenominatorW87 delta M CM ≠ 0 := by
    rw [← hcard]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (FullPassLabelW87 delta M CM)).ne'
  have hDtop : fullPassDenominatorW87 delta M CM ≠ ⊤ := by
    unfold fullPassDenominatorW87
    finiteness
  refine ⟨selected, keptNodes, next, I.Ydagger, rfl, rfl, hnext,
    saturatedFineLift_subset_w87 U q, ?_, ?_⟩
  · intro i hi
    exact ⟨I.same_tube i (saturatedFineLift_subset_w87 U q hi), le_rfl⟩
  · calc
      _ <= (fullPassDenominatorW87 delta M CM) ^ (-1 : Int) *
          (fullPassDenominatorW87 delta M CM *
            ∑ i ∈ next, volume (I.Ydagger i).shade) :=
        mul_le_mul_left' hpaid _
      _ = _ := by
        rw [← mul_assoc, zpow_neg_one, ENNReal.inv_mul_cancel hD0 hDtop, one_mul]

theorem fullPass_mass_payment_w87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {M CM : Nat} {current next : Finset iota}
    {Y YPlus : iota -> ShadedTube delta E}
    (hretained :
      (fullPassDenominatorW87 delta M CM) ^ (-1 : Int) *
          (∑ i ∈ current, volume (Y i).shade) <=
        ∑ i ∈ next, volume (YPlus i).shade)
    (hone : 1 <= fullPassDenominatorW87 delta M CM) :
    (∑ i ∈ current, volume (Y i).shade) <=
      fullPassDenominatorW87 delta M CM *
        (∑ i ∈ next, volume (YPlus i).shade) := by
  let D := fullPassDenominatorW87 delta M CM
  let A := ∑ i ∈ current, volume (Y i).shade
  let B := ∑ i ∈ next, volume (YPlus i).shade
  have hD0 : D ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hone)
  have hDtop : D ≠ ⊤ := by
    dsimp [D, fullPassDenominatorW87]
    finiteness
  have hinv : D * D ^ (-1 : Int) = 1 := by
    rw [zpow_neg_one]
    simpa using ENNReal.mul_inv_cancel hD0 hDtop
  change A <= D * B
  change D ^ (-1 : Int) * A <= B at hretained
  calc
    A = D * (D ^ (-1 : Int) * A) := by rw [← mul_assoc, hinv, one_mul]
    _ <= D * B := mul_le_mul_left' hretained D

noncomputable def exactTubeCellW87
    {iota : Type uI} [DecidableEq iota] {r s : NNReal}
    (F : Finset iota) (W : iota -> Tube r E) (R : Tube s E) : Finset iota := by
  classical
  exact F.filter fun i =>
    (W i).toConvexSpaceBody <= R.toConvexSpaceBody

/--
The finite quotient of all nonempty exact `s`-tube cells.  The existential
still ranges over every `Tube s E`; `F.powerset` only deduplicates exact tubes
which realize the same finite cell.
-/

noncomputable def realizedExactTubeCellsW87
    {iota : Type uI} [DecidableEq iota] {r : NNReal}
    (F : Finset iota) (W : iota -> Tube r E) (s : NNReal) :
    Finset (Finset iota) := by
  classical
  exact F.powerset.filter fun A =>
    A.Nonempty /\ exists R : Tube s E, A = exactTubeCellW87 F W R

/--
The source quantity `N_s(F)`: the maximum `Delta_max` over all nonempty cells
realized by exact `s`-tubes.  It is a finite supremum because a finite family
has only finitely many distinct cells.
-/

noncomputable def allExactTubeNsW87
    {iota : Type uI} [DecidableEq iota] {r : NNReal}
    (F : Finset iota) (W : iota -> Tube r E) (s : NNReal) : ENNReal :=
  (realizedExactTubeCellsW87 F W s).sup fun A =>
    Kakeya.maxDensity A (fun i => (W i).toConvexSpaceBody)

theorem exactTubeCell_subset_w87
    {iota : Type uI} [DecidableEq iota] {r s : NNReal}
    (F : Finset iota) (W : iota -> Tube r E) (R : Tube s E) :
    exactTubeCellW87 F W R <= F := by
  intro i hi
  exact (Finset.mem_filter.mp hi).1

theorem exactTubeCell_mono_family_w87
    {iota : Type uI} [DecidableEq iota] {r s : NNReal}
    {F F' : Finset iota} (hsub : F' <= F)
    (W : iota -> Tube r E) (R : Tube s E) :
    exactTubeCellW87 F' W R <= exactTubeCellW87 F W R := by
  intro i hi
  exact Finset.mem_filter.mpr
    ⟨hsub (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩

theorem mem_realizedExactTubeCells_w87
    {iota : Type uI} [DecidableEq iota] {r : NNReal}
    {F : Finset iota} {W : iota -> Tube r E} {s : NNReal}
    {A : Finset iota} :
    A ∈ realizedExactTubeCellsW87 F W s <->
      A.Nonempty /\ exists R : Tube s E, A = exactTubeCellW87 F W R := by
  classical
  constructor
  · intro hA
    exact (Finset.mem_filter.mp hA).2
  · intro hA
    refine Finset.mem_filter.mpr ⟨?_, hA⟩
    rcases hA.2 with ⟨R, rfl⟩
    exact Finset.mem_powerset.mpr (exactTubeCell_subset_w87 F W R)

theorem realized_cell_of_exact_w87
    {iota : Type uI} [DecidableEq iota] {r s : NNReal}
    {F : Finset iota} {W : iota -> Tube r E} (R : Tube s E)
    (hne : (exactTubeCellW87 F W R).Nonempty) :
    exactTubeCellW87 F W R ∈ realizedExactTubeCellsW87 F W s := by
  exact mem_realizedExactTubeCells_w87.mpr ⟨hne, R, rfl⟩

theorem maxDensity_exactTubeCell_le_allExactTubeNs_w87
    {iota : Type uI} [DecidableEq iota] {r s : NNReal}
    {F : Finset iota} {W : iota -> Tube r E} (R : Tube s E)
    (hne : (exactTubeCellW87 F W R).Nonempty) :
    Kakeya.maxDensity (exactTubeCellW87 F W R)
        (fun i => (W i).toConvexSpaceBody) <=
      allExactTubeNsW87 F W s := by
  unfold allExactTubeNsW87
  exact Finset.le_sup
    (f := fun A : Finset iota =>
      Kakeya.maxDensity A (fun i => (W i).toConvexSpaceBody))
    (realized_cell_of_exact_w87 R hne)

theorem allExactTubeNs_le_w87
    {iota : Type uI} [DecidableEq iota] {r s : NNReal}
    {F : Finset iota} {W : iota -> Tube r E} {A : ENNReal}
    (hbound : forall R : Tube s E,
      (exactTubeCellW87 F W R).Nonempty ->
      Kakeya.maxDensity (exactTubeCellW87 F W R)
          (fun i => (W i).toConvexSpaceBody) <= A) :
    allExactTubeNsW87 F W s <= A := by
  apply Finset.sup_le
  intro cell hcell
  rcases mem_realizedExactTubeCells_w87.mp hcell with ⟨hne, R, rfl⟩
  exact hbound R hne

theorem allExactTubeNs_ne_top_w87
    {iota : Type uI} [DecidableEq iota] {r : NNReal}
    (F : Finset iota) (W : iota -> Tube r E) (s : NNReal) :
    allExactTubeNsW87 F W s ≠ ⊤ := by
  apply ne_top_of_le_ne_top
    (Kakeya.maxDensity_ne_top F (fun i => (W i).toConvexSpaceBody))
  apply allExactTubeNs_le_w87
  intro R _hne
  exact Kakeya.maxDensity_mono _ (exactTubeCell_subset_w87 F W R)

theorem allExactTubeNs_mono_w87
    {iota : Type uI} [DecidableEq iota] {r s : NNReal}
    {F F' : Finset iota} (hsub : F' <= F) (W : iota -> Tube r E) :
    allExactTubeNsW87 F' W s <= allExactTubeNsW87 F W s := by
  apply allExactTubeNs_le_w87
  intro R hne
  have hcell : exactTubeCellW87 F' W R <= exactTubeCellW87 F W R :=
    exactTubeCell_mono_family_w87 hsub W R
  have hne' : (exactTubeCellW87 F W R).Nonempty := hne.mono hcell
  exact (Kakeya.maxDensity_mono _ hcell).trans
    (maxDensity_exactTubeCell_le_allExactTubeNs_w87 R hne')

theorem one_le_allExactTubeNs_of_nonempty_w87
    {iota : Type uI} [DecidableEq iota] {r s : NNReal}
    {F : Finset iota} (W : iota -> Tube r E)
    (hF : F.Nonempty) (hr : 0 < r) (hr1 : r <= 1) (hrs : r <= s) :
    1 <= allExactTubeNsW87 F W s := by
  rcases hF with ⟨i, hi⟩
  let R : Tube s E := (W i).rescale s
  have hiCell : i ∈ exactTubeCellW87 F W R := by
    exact Finset.mem_filter.mpr ⟨hi, Tube.le_rescale (W i) hrs⟩
  have hcell : (exactTubeCellW87 F W R).Nonempty := ⟨i, hiCell⟩
  have hvol : 0 < volume (W i).toConvexSpaceBody.carrier :=
    (Tube.volume_pos_and_lt_top hr hr1 (W i)).1
  exact (Kakeya.one_le_maxDensity ⟨i, hiCell, hvol⟩).trans
    (maxDensity_exactTubeCell_le_allExactTubeNs_w87 R hcell)

theorem max_one_toReal_allExactTubeNs_eq_w87
    {iota : Type uI} [DecidableEq iota] {r s : NNReal}
    {F : Finset iota} {W : iota -> Tube r E}
    (h1 : 1 <= allExactTubeNsW87 F W s) :
    max 1 (allExactTubeNsW87 F W s).toReal =
      (allExactTubeNsW87 F W s).toReal := by
  apply max_eq_right
  simpa only [ENNReal.toReal_one] using
    ENNReal.toReal_mono (allExactTubeNs_ne_top_w87 F W s) h1

theorem canonicalAncestorFamily_mono_w87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base F F' : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} (U : CanonicalProfileNetW87 base T M C)
    (hsub : F' <= F) (q : Fin (M + 1)) :
    canonicalAncestorFamilyW87 U F' q <=
      canonicalAncestorFamilyW87 U F q := by
  exact Finset.image_subset_image hsub

noncomputable def literalCanonicalDW87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} (U : CanonicalProfileNetW87 base T M C)
    (F : Finset iota) (q ell : Fin (M + 1)) : ENNReal :=
  allExactTubeNsW87 (canonicalAncestorFamilyW87 U F q)
    (fun w => U.cover.tube q.val w) (Tube.gridScale delta M ell.val)

noncomputable def literalProfileCoordW87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} (U : CanonicalProfileNetW87 base T M C)
    (F : Finset iota) (q ell : Fin (M + 1)) : Real :=
  Real.log (max 1 (literalCanonicalDW87 U F q ell).toReal) /
    Real.log ((delta : Real) ^ (-1 : Real))

theorem literalCanonicalD_mono_w87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base F F' : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} (U : CanonicalProfileNetW87 base T M C)
    (hsub : F' <= F) (q ell : Fin (M + 1)) :
    literalCanonicalDW87 U F' q ell <= literalCanonicalDW87 U F q ell := by
  exact allExactTubeNs_mono_w87 (canonicalAncestorFamily_mono_w87 U hsub q) _

theorem literalProfileCoord_mono_w87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base F F' : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} (U : CanonicalProfileNetW87 base T M C)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hsub : F' <= F) (q ell : Fin (M + 1)) :
    literalProfileCoordW87 U F' q ell <=
      literalProfileCoordW87 U F q ell := by
  unfold literalProfileCoordW87
  apply div_le_div_of_nonneg_right _ (by
    apply Real.log_nonneg
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta1.le (by norm_num))
  apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  apply max_le_max_left
  exact ENNReal.toReal_mono (allExactTubeNs_ne_top_w87 _ _ _)
    (literalCanonicalD_mono_w87 U hsub q ell)

theorem literalProfileCoord_nonneg_w87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base F : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} (U : CanonicalProfileNetW87 base T M C)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (q ell : Fin (M + 1)) :
    0 <= literalProfileCoordW87 U F q ell := by
  unfold literalProfileCoordW87
  apply div_nonneg (Real.log_nonneg (le_max_left _ _))
  apply Real.log_nonneg
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta1.le (by norm_num)

theorem literalProfileCoord_le_seven_w87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base F : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} (U : CanonicalProfileNetW87 base T M C)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hF : F <= base)
    (hcard7 : (base.card : Real) <= (delta : Real) ^ (-7 : Real))
    (q ell : Fin (M + 1)) :
    literalProfileCoordW87 U F q ell <= 7 := by
  have hdeltaR : 0 < (delta : Real) := hdelta
  have hdeltaR1 : (delta : Real) < 1 := hdelta1
  have hDcard : literalCanonicalDW87 U F q ell <= (base.card : ENNReal) := by
    apply allExactTubeNs_le_w87
    intro R _
    calc
      _ <= ((exactTubeCellW87 (canonicalAncestorFamilyW87 U F q)
        (fun w => U.cover.tube q.val w) R).card : ENNReal) :=
          Kakeya.maxDensity_le_card _ _
      _ <= ((canonicalAncestorFamilyW87 U F q).card : ENNReal) := by
        exact_mod_cast Finset.card_le_card (exactTubeCell_subset_w87 _ _ R)
      _ <= (F.card : ENNReal) := by
        exact_mod_cast Finset.card_image_le
      _ <= (base.card : ENNReal) := by
        exact_mod_cast Finset.card_le_card hF
  have hreal : (literalCanonicalDW87 U F q ell).toReal <= (base.card : Real) := by
    simpa only [ENNReal.toReal_natCast] using
      ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hDcard
  have hmax : max 1 (literalCanonicalDW87 U F q ell).toReal <=
      (delta : Real) ^ (-7 : Real) :=
    max_le (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdeltaR hdeltaR1.le
      (by norm_num)) (hreal.trans hcard7)
  have hlog : 0 < Real.log ((delta : Real) ^ (-1 : Real)) :=
    Real.log_pos (Real.one_lt_rpow_of_pos_of_lt_one_of_neg hdeltaR hdeltaR1
      (by norm_num))
  unfold literalProfileCoordW87
  apply (div_le_iff₀ hlog).mpr
  calc
    _ <= Real.log ((delta : Real) ^ (-7 : Real)) :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hmax
    _ = _ := by rw [Real.log_rpow hdeltaR, Real.log_rpow hdeltaR]; ring

/-- A profile state whose coordinates are exactly the literal source profile. -/

structure LiteralProfileStateWitnessW87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} (U : CanonicalProfileNetW87 base T M C)
    (F : Finset iota) where
  state : ProfileStateW74 M
  coord_eq : forall q ell,
    state.coord q ell = literalProfileCoordW87 U F q ell

theorem exists_literalProfileState_w87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base F : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} (U : CanonicalProfileNetW87 base T M C)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hF : F <= base)
    (hcard7 : (base.card : Real) <= (delta : Real) ^ (-7 : Real)) :
    Nonempty (LiteralProfileStateWitnessW87 U F) := by
  refine ⟨⟨{
    coord := literalProfileCoordW87 U F
    coord_nonneg := literalProfileCoord_nonneg_w87 U hdelta hdelta1
    coord_upper := literalProfileCoord_le_seven_w87 U hdelta hdelta1 hF hcard7
    potential_bound := ?_ }, fun _ _ => rfl⟩⟩
  unfold profilePotential
  calc
    _ <= ∑ _a : Fin (M + 1), ∑ _b : Fin (M + 1), (7 : Real) := by
      exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum
        (fun b _ => literalProfileCoord_le_seven_w87 U hdelta hdelta1 hF hcard7 a b))
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

/-- Parameters selected before the running scale and tied to `Params`. -/

structure RevisedProfileParametersW87 (p : Params) where
  M : Nat
  CM : Nat
  canonicalC : NNReal
  M_pos : 0 < M
  CM_pos : 0 < CM
  canonicalC_one : 1 <= canonicalC
  epsilon_pos : 0 < p.ε
  zeta0_pos : 0 < p.η 0
  zeta_mono : Monotone p.η
  reciprocal_M_small :
    (1 : Real) / (M : Real) <= p.ε ^ 2 * p.η 0 / 192

/-- The exact fixed comparison constant: G7 times the canonical overlap. -/

noncomputable def sourceCgeomW87
    {p : Params} (P : RevisedProfileParametersW87 p) : Real :=
  2 * 25 ^ (6 : Nat) * 4 ^ (6 : Nat) * (P.canonicalC : Real)

noncomputable def sourceCFlatW87 (p : Params) : Real :=
  p.ε ^ 2 * p.η 0 / 32

noncomputable def canonicalComparisonFactorW87
    {p : Params} (P : RevisedProfileParametersW87 p)
    (delta d : NNReal) (zetaJ : Real) : Real :=
  sourceCgeomW87 P * (delta : Real) ^ (-6 / (P.M : Real)) *
    (d : Real) ^ (p.ε * zetaJ / 8)

theorem exists_deltaProfileAbsorb_w87
    {p : Params} (P : RevisedProfileParametersW87 p) :
    exists delta0 : NNReal, 0 < delta0 /\ delta0 < 1 /\
      forall delta : NNReal, 0 < delta -> delta <= delta0 ->
      forall d : NNReal, forall zetaJ : Real,
        0 < d -> d <= 1 ->
        (d : Real) <= (delta : Real) ^ p.ε ->
        p.η 0 <= zetaJ ->
        canonicalComparisonFactorW87 P delta d zetaJ <=
          (delta : Real) ^ sourceCFlatW87 p := by
  have hflat : 0 < sourceCFlatW87 p := by
    unfold sourceCFlatW87
    exact div_pos (mul_pos (sq_pos_of_pos P.epsilon_pos) P.zeta0_pos) (by norm_num)
  have hgeom : 1 <= sourceCgeomW87 P := by
    have hC : (1 : Real) <= P.canonicalC := P.canonicalC_one
    unfold sourceCgeomW87
    nlinarith
  let K : NNReal := ⟨sourceCgeomW87 P, le_trans zero_le_one hgeom⟩
  obtain ⟨delta1, hdelta1pos, hconstant⟩ :=
    Kakeya.exists_threshold_le_rpow_neg K hgeom hflat
  refine ⟨min delta1 (1 / 2), lt_min hdelta1pos (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro delta hdelta hsmall d zetaJ hd hd1 hdscale hzeta
  have hdeltaR : 0 < (delta : Real) := hdelta
  have hdeltaR1 : (delta : Real) <= 1 := by
    have hhalf : delta <= 1 / 2 := hsmall.trans (min_le_right _ _)
    exact_mod_cast le_trans hhalf (by norm_num : (1 / 2 : NNReal) <= 1)
  have hconstantR : sourceCgeomW87 P <=
      (delta : Real) ^ (-sourceCFlatW87 p) := by
    exact_mod_cast hconstant delta hdelta (hsmall.trans (min_le_left _ _))
  have he0 : 0 <= p.ε * p.η 0 / 8 :=
    div_nonneg (mul_nonneg P.epsilon_pos.le P.zeta0_pos.le) (by norm_num)
  have he : p.ε * p.η 0 / 8 <= p.ε * zetaJ / 8 := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hzeta
      P.epsilon_pos.le) (by norm_num)
  have hdpow : (d : Real) ^ (p.ε * zetaJ / 8) <=
      (delta : Real) ^ (p.ε ^ 2 * p.η 0 / 8) := by
    calc
      _ <= (d : Real) ^ (p.ε * p.η 0 / 8) :=
        Real.rpow_le_rpow_of_exponent_ge hd hd1 he
      _ <= ((delta : Real) ^ p.ε) ^ (p.ε * p.η 0 / 8) :=
        Real.rpow_le_rpow hd.le hdscale he0
      _ = _ := by rw [← Real.rpow_mul delta.coe_nonneg]; congr 1; ring
  have hloss : 6 / (P.M : Real) <= sourceCFlatW87 p := by
    have hM := P.reciprocal_M_small
    unfold sourceCFlatW87
    calc
      6 / (P.M : Real) = 6 * (1 / (P.M : Real)) := by ring
      _ <= 6 * (p.ε ^ 2 * p.η 0 / 192) := mul_le_mul_of_nonneg_left hM (by norm_num)
      _ = _ := by ring
  unfold canonicalComparisonFactorW87
  calc
    _ <= (delta : Real) ^ (-sourceCFlatW87 p) *
        (delta : Real) ^ (-6 / (P.M : Real)) *
          (delta : Real) ^ (p.ε ^ 2 * p.η 0 / 8) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hconstantR (Real.rpow_nonneg delta.coe_nonneg _)
      · exact hdpow
      · exact Real.rpow_nonneg d.coe_nonneg _
      · positivity
    _ = (delta : Real) ^
        (-sourceCFlatW87 p + (-6 / (P.M : Real)) + p.ε ^ 2 * p.η 0 / 8) := by
      rw [← Real.rpow_add hdeltaR, ← Real.rpow_add hdeltaR]
    _ <= _ := by
      apply Real.rpow_le_rpow_of_exponent_ge hdeltaR hdeltaR1
      dsimp [sourceCFlatW87] at hloss hflat ⊢
      rw [neg_div]
      linarith

theorem max_one_literalCanonicalD_drop_w87
    {iota : Type uI} [DecidableEq iota]
    {delta : NNReal} {base current next : Finset iota}
    {T : iota -> Tube delta E} {M : Nat} {C : NNReal}
    (U : CanonicalProfileNetW87 base T M C)
    (q ell : Fin (M + 1)) (cFlat : Real)
    (hbefore1 : 1 <= literalCanonicalDW87 U current q ell)
    (hafter1 : 1 <= literalCanonicalDW87 U next q ell)
    (hraw : literalCanonicalDW87 U next q ell <=
      ENNReal.ofReal ((delta : Real) ^ cFlat) *
        literalCanonicalDW87 U current q ell) :
    max 1 (literalCanonicalDW87 U next q ell).toReal <=
      (delta : Real) ^ cFlat *
        max 1 (literalCanonicalDW87 U current q ell).toReal := by
  unfold literalCanonicalDW87 at hbefore1 hafter1 hraw ⊢
  rw [max_one_toReal_allExactTubeNs_eq_w87 hbefore1,
    max_one_toReal_allExactTubeNs_eq_w87 hafter1]
  have hfinite : ENNReal.ofReal ((delta : Real) ^ cFlat) *
      literalCanonicalDW87 U current q ell ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (allExactTubeNs_ne_top_w87 _ _ _)
  have hreal := ENNReal.toReal_mono hfinite hraw
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg delta.coe_nonneg _),
    literalCanonicalDW87]
    using hreal

theorem allExactTubeNs_coarse_le_fine_w87
    {iota : Type uI} [DecidableEq iota]
    {r sFine sCoarse : NNReal} (F : Finset iota)
    (W : iota -> Tube r E)
    (hdim : Module.finrank Real E = 3)
    (hr : 0 < r) (hmember : 2 * r <= sFine)
    (hsc : sFine <= sCoarse) :
    allExactTubeNsW87 F W sCoarse <=
      ENNReal.ofReal
        (2 * 25 ^ (6 : Nat) *
          (4 * (sCoarse : Real) / (sFine : Real)) ^ (6 : Nat)) *
        allExactTubeNsW87 F W sFine := by
  classical
  have hrf : r <= sFine := (by nlinarith : r <= 2 * r).trans hmember
  have hf : 0 < sFine := hr.trans_le hrf
  apply allExactTubeNs_le_w87
  intro R hne
  obtain ⟨i0, hi0⟩ := hne
  have hR : R.toConvexSpaceBody <=
      ((W i0).rescale (4 * sCoarse)).toConvexSpaceBody :=
    Tube.rescale_le_of_le (W i0) R (Finset.mem_filter.mp hi0).2
  obtain ⟨A, hAF, hcard, hcover⟩ :=
    Kakeya.MultiScaleFac.exists_gapFibre_cover_of_ratio
      (s := F) (T := W) (δ := r) (σ := r)
      (ρ := sFine) (ρ' := 4 * sCoarse) hf le_rfl hmember
      (hsc.trans (by nlinarith)) i0
  have hsub : exactTubeCellW87 F W R <=
      A.biUnion (fun a => exactTubeCellW87 F W ((W a).rescale sFine)) := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hiFibre : i ∈ Kakeya.StickyKakeya.fibreIndex F W r (4 * sCoarse) i0 := by
      rw [Kakeya.StickyKakeya.fibreIndex_self]
      exact Finset.mem_filter.mpr ⟨hi'.1, hi'.2.trans hR⟩
    obtain ⟨a, ha, hia⟩ := hcover i hiFibre
    apply Finset.mem_biUnion.mpr
    refine ⟨a, ha, ?_⟩
    simpa only [Kakeya.StickyKakeya.fibreIndex_self, exactTubeCellW87] using hia
  have hterm : ∀ a ∈ A,
      Kakeya.maxDensity (exactTubeCellW87 F W ((W a).rescale sFine))
        (fun i => (W i).toConvexSpaceBody) <= allExactTubeNsW87 F W sFine := by
    intro a ha
    apply maxDensity_exactTubeCell_le_allExactTubeNs_w87
    exact ⟨a, Finset.mem_filter.mpr ⟨hAF ha, Tube.le_rescale (W a) hrf⟩⟩
  have hcardE : (A.card : ENNReal) <=
      ENNReal.ofReal (2 * 25 ^ (6 : Nat) *
        (4 * (sCoarse : Real) / (sFine : Real)) ^ (6 : Nat)) := by
    have hcardR : (A.card : Real) <= 2 * 25 ^ (6 : Nat) *
        (4 * (sCoarse : Real) / (sFine : Real)) ^ (6 : Nat) := by
      simpa only [hdim, NNReal.coe_mul, NNReal.coe_ofNat] using hcard
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcardR
  calc
    Kakeya.maxDensity (exactTubeCellW87 F W R) (fun i => (W i).toConvexSpaceBody)
        <= ∑ a ∈ A, Kakeya.maxDensity (exactTubeCellW87 F W ((W a).rescale sFine))
          (fun i => (W i).toConvexSpaceBody) :=
      Kakeya.maxDensity_le_sum_of_subset_biUnion _ hsub
    _ <= ∑ _a ∈ A, allExactTubeNsW87 F W sFine := Finset.sum_le_sum hterm
    _ = (A.card : ENNReal) * allExactTubeNsW87 F W sFine := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ <= _ := mul_le_mul_left hcardE _

noncomputable def blockThetaW87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {sPrime : Finset iota} {T : iota -> ShadedTube delta E}
    {Cds : NNReal} (U : Tube.UniformTubeSet sPrime
      (fun i => (T i).toTube) (Tube.ssfGridLen delta) Cds)
    (a : Nat) : NNReal :=
  Tube.gridScale delta (Tube.ssfGridLen delta) a

noncomputable def blockTauW87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {sPrime : Finset iota} {T : iota -> ShadedTube delta E}
    {Cds : NNReal} (U : Tube.UniformTubeSet sPrime
      (fun i => (T i).toTube) (Tube.ssfGridLen delta) Cds)
    (b : Nat) : NNReal :=
  Tube.gridScale delta (Tube.ssfGridLen delta) b

noncomputable def blockRatioW87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {sPrime : Finset iota} {T : iota -> ShadedTube delta E}
    {Cds : NNReal} (U : Tube.UniformTubeSet sPrime
      (fun i => (T i).toTube) (Tube.ssfGridLen delta) Cds)
    (a b : Nat) : NNReal :=
  blockTauW87 U b / blockThetaW87 U a

structure CanonicalDropCoordinateW87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {sPrime : Finset iota} {T : iota -> ShadedTube delta E}
    {Cds : NNReal} (U : Tube.UniformTubeSet sPrime
      (fun i => (T i).toTube) (Tube.ssfGridLen delta) Cds)
    {p : Params} (P : RevisedProfileParametersW87 p)
    (a b m : Nat) (working : NNReal) where
  q : Fin (P.M + 1)
  ell : Fin (P.M + 1)
  ell_pos : 0 < ell.val
  ellPred : Fin (P.M + 1)
  ellPred_eq : ellPred.val = ell.val - 1
  ell_le_q : ell <= q
  label : Fin p.N
  label_eq_block : label.val = m
  theta_eq : blockThetaW87 U a =
    Tube.gridScale delta (Tube.ssfGridLen delta) a
  tau_eq : blockTauW87 U b =
    Tube.gridScale delta (Tube.ssfGridLen delta) b
  ratio_eq : blockRatioW87 U a b = blockTauW87 U b / blockThetaW87 U a
  ratio_pos : 0 < blockRatioW87 U a b
  ratio_le_one : blockRatioW87 U a b <= 1
  ratio_le_delta_epsilon :
    (blockRatioW87 U a b : Real) <= (delta : Real) ^ p.ε
  q_round : Tube.gridScale delta P.M q.val <= blockTauW87 U b
  q_round_pred : q.val = 0 \/
    blockTauW87 U b < Tube.gridScale delta P.M (q.val - 1)
  ell_round : Tube.gridScale delta P.M ell.val <= working
  ell_round_pred : working < Tube.gridScale delta P.M ellPred.val

theorem exists_canonicalDropCoordinate_w87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {p : Params} {Kds cds : Nat} {CdsR : NNReal}
    {sPrime : Finset iota} {T : iota -> ShadedTube delta E}
    (U : Tube.UniformTubeSet sPrime (fun i => (T i).toTube)
      (Tube.ssfGridLen delta) CdsR)
    (P : RevisedProfileParametersW87 p)
    {a b m : Nat}
    (hblock : StickyKakeya.IsFrostmanDividingBlock U CdsR Kds cds
      p.η p.ε a b m p.N)
    {working : NNReal}
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hworkLower : blockTauW87 U b <= working)
    (hworkUpper : working <= blockThetaW87 U a)
    (hworking_lt_one : working < 1) :
    Nonempty (CanonicalDropCoordinateW87 U P a b m working) := by
  classical
  have hgridLen : 0 < Tube.ssfGridLen delta :=
    (Nat.zero_le a).trans_lt (hblock.coarse_lt_fine.trans_le hblock.fine_le)
  have hdeltaTau : delta <= blockTauW87 U b := by
    calc
      delta = Tube.gridScale delta (Tube.ssfGridLen delta) (Tube.ssfGridLen delta) :=
        (Tube.gridScale_self delta hgridLen).symm
      _ <= blockTauW87 U b :=
        Tube.gridScale_antitone hdelta hdelta1.le _ hblock.fine_le
  have hqExists : ∃ k : Nat, Tube.gridScale delta P.M k <= blockTauW87 U b :=
    ⟨P.M, (Tube.gridScale_self delta P.M_pos).le.trans hdeltaTau⟩
  let qn := Nat.find hqExists
  have hqn : qn <= P.M := Nat.find_min' hqExists
    ((Tube.gridScale_self delta P.M_pos).le.trans hdeltaTau)
  have hqRound : Tube.gridScale delta P.M qn <= blockTauW87 U b :=
    Nat.find_spec hqExists
  have hellExists : ∃ k : Nat, Tube.gridScale delta P.M k <= working :=
    ⟨qn, hqRound.trans hworkLower⟩
  let elln := Nat.find hellExists
  have hellq : elln <= qn := Nat.find_min' hellExists (hqRound.trans hworkLower)
  have hellRound : Tube.gridScale delta P.M elln <= working := Nat.find_spec hellExists
  have hellPos : 0 < elln := by
    by_contra h
    have he0 : elln = 0 := by omega
    rw [he0, Tube.gridScale_zero] at hellRound
    exact (not_le_of_gt hworking_lt_one) hellRound
  have hthetaPos : 0 < blockThetaW87 U a := Tube.gridScale_pos hdelta _ _
  have htauPos : 0 < blockTauW87 U b := Tube.gridScale_pos hdelta _ _
  have htauTheta : blockTauW87 U b <= blockThetaW87 U a :=
    Tube.gridScale_antitone hdelta hdelta1.le _ hblock.coarse_lt_fine.le
  refine ⟨{
    q := ⟨qn, by omega⟩
    ell := ⟨elln, by omega⟩
    ell_pos := hellPos
    ellPred := ⟨elln - 1, by omega⟩
    ellPred_eq := rfl
    ell_le_q := hellq
    label := ⟨m, hblock.exponent_lt⟩
    label_eq_block := rfl
    theta_eq := rfl
    tau_eq := rfl
    ratio_eq := rfl
    ratio_pos := div_pos htauPos hthetaPos
    ratio_le_one := (div_le_one hthetaPos).mpr htauTheta
    ratio_le_delta_epsilon := ?_
    q_round := hqRound
    q_round_pred := ?_
    ell_round := hellRound
    ell_round_pred := ?_
  }⟩
  · change (blockTauW87 U b : Real) / (blockThetaW87 U a : Real) <= _
    exact (div_le_iff₀ (by exact_mod_cast hthetaPos)).mpr hblock.separated
  · by_cases hq0 : qn = 0
    · exact Or.inl hq0
    · exact Or.inr (lt_of_not_ge (Nat.find_min hqExists (by dsimp [qn] at *; omega)))
  · exact lt_of_not_ge (Nat.find_min hellExists (by dsimp [elln] at *; omega))

theorem allExactTubeNs_le_of_assignedCover_w87
    {iota : Type uI} [DecidableEq iota] {pi : Type uP}
    [DecidableEq pi] {r s : NNReal}
    {before after : Finset iota} {W : iota -> Tube r E}
    (parents : Finset pi) (part : pi -> Finset iota)
    (kappa CoverC : ENNReal)
    (hcover : after <= parents.biUnion part)
    (hlocal : ∀ P ∈ parents,
      Kakeya.maxDensity (part P) (fun i => (W i).toConvexSpaceBody) <=
        kappa * allExactTubeNsW87 before W s)
    (hmeeting : forall R : Tube s E,
      (((parents.filter fun P =>
        (part P ∩ exactTubeCellW87 after W R).Nonempty).card : Nat) : ENNReal) <=
        CoverC) :
    allExactTubeNsW87 after W s <=
      CoverC * kappa * allExactTubeNsW87 before W s := by
  classical
  apply allExactTubeNs_le_w87
  intro R _hcellNe
  let meeting : Finset pi := parents.filter fun P =>
    (part P ∩ exactTubeCellW87 after W R).Nonempty
  have hcoverR : exactTubeCellW87 after W R <= meeting.biUnion part := by
    intro i hi
    rcases Finset.mem_biUnion.mp (hcover (exactTubeCell_subset_w87 after W R hi)) with
      ⟨P, hP, hiP⟩
    refine Finset.mem_biUnion.mpr ⟨P, ?_, hiP⟩
    exact Finset.mem_filter.mpr ⟨hP, ⟨i, Finset.mem_inter.mpr ⟨hiP, hi⟩⟩⟩
  have hmax := Kakeya.maxDensity_le_sum_of_subset_biUnion
    (W := fun i => (W i).toConvexSpaceBody) hcoverR
  calc
    Kakeya.maxDensity (exactTubeCellW87 after W R)
        (fun i => (W i).toConvexSpaceBody)
        <= ∑ P ∈ meeting,
          Kakeya.maxDensity (part P) (fun i => (W i).toConvexSpaceBody) := hmax
    _ <= ∑ _P ∈ meeting, kappa * allExactTubeNsW87 before W s := by
      apply Finset.sum_le_sum
      intro P hP
      exact hlocal P (Finset.mem_filter.mp hP).1
    _ = (meeting.card : ENNReal) *
        (kappa * allExactTubeNsW87 before W s) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ <= CoverC * (kappa * allExactTubeNsW87 before W s) := by
      exact mul_le_mul_right' (by simpa [meeting] using hmeeting R) _
    _ = CoverC * kappa * allExactTubeNsW87 before W s := by
      rw [mul_assoc]

/-! ## Literal canonical D_(q,ell) and profile -/

theorem image_saturatedFineLift_eq_w87
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {base current : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} (U : CanonicalProfileNetW87 base T M C)
    (q : Fin (M + 1))
    (keptNodes : Finset (CanonicalQNodeW87 U current q)) :
    canonicalAncestorFamilyW87 U
      (saturatedFineLiftW87 U current q
        (canonicalQNodeValuesW87 keptNodes)) q =
      canonicalQNodeValuesW87 keptNodes := by
  classical
  apply Finset.Subset.antisymm
  · intro w hw
    rcases Finset.mem_image.mp hw with ⟨i, hi, rfl⟩
    exact (Finset.mem_filter.mp hi).2
  · intro w hw
    rcases Finset.mem_image.mp hw with ⟨wnode, hwnode, rfl⟩
    rcases Finset.mem_image.mp wnode.property with ⟨i, hiCurrent, hiAssign⟩
    refine Finset.mem_image.mpr ⟨i, ?_, hiAssign⟩
    exact Finset.mem_filter.mpr
      ⟨hiCurrent, Finset.mem_image.mpr ⟨wnode, hwnode, hiAssign.symm⟩⟩

structure LiteralInnerDropOutputW87
    {iota : Type uI} [DecidableEq iota] {delta working : NNReal}
    {base current : Finset iota} {T : iota -> Tube delta E}
    {M : Nat} {C : NNReal} (U : CanonicalProfileNetW87 base T M C)
    (q : Fin (M + 1))
    (Y : CanonicalQNodeW87 U current q ->
      ShadedTube (Tube.gridScale delta M q.val) E)
    (nodeFamily : Finset iota) (nodeTube : iota -> Tube working E)
    (part : iota -> Finset (CanonicalQNodeW87 U current q))
    (d : NNReal) (epsilon zetaJ : Real) (Ktr : Nat) where
  FPlus : Finset (CanonicalQNodeW87 U current q)
  YPlus : CanonicalQNodeW87 U current q ->
    ShadedTube (Tube.gridScale delta M q.val) E
  FPlus_nonempty : FPlus.Nonempty
  FPlus_subset : FPlus <= canonicalQNodeFinsetW87 U current q
  middle_same_tube : forall w, (Y w).toTube = U.cover.tube q.val w.val
  subshading : ∀ w ∈ FPlus,
    (YPlus w).toTube = (Y w).toTube /\ (YPlus w).shade <= (Y w).shade
  assigned_cover : FPlus = nodeFamily.biUnion part
  assigned_disjoint : Set.Pairwise (nodeFamily : Set iota) fun P Q =>
    Disjoint (part P) (part Q)
  part_subset : ∀ P ∈ nodeFamily, part P <= FPlus
  part_parent_containment : ∀ P ∈ nodeFamily, ∀ w ∈ part P,
    (YPlus w).toConvexSpaceBody <= (nodeTube P).toConvexSpaceBody
  parent_boundedOverlap : Tube.HasBoundedOverlap
    (canonicalQNodeFinsetW87 U current q) (fun w => (Y w).toTube)
      nodeFamily nodeTube C
  member_twice_le_working : 2 * Tube.gridScale delta M q.val <= working
  per_cell_density_drop : ∀ P ∈ nodeFamily,
    Kakeya.maxDensity (part P)
        (fun w => (YPlus w).toConvexSpaceBody) <=
      (d : ENNReal) ^ (epsilon * zetaJ / 4) *
        allExactTubeNsW87 (canonicalQNodeFinsetW87 U current q)
          (fun w => (Y w).toTube) working
  Ktr_pos : 0 < Ktr
  mass_retention :
    ENNReal.ofReal
        ((1 + Real.log (1 / (d : Real))) ^ (-(Ktr : Real))) *
      (∑ w ∈ canonicalQNodeFinsetW87 U current q, volume (Y w).shade) <=
        ∑ w ∈ FPlus, volume (YPlus w).shade

private theorem allExactTubeNs_map_w90
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    {r s : NNReal} (A : Finset alpha) (e : alpha ↪ beta)
    (W : beta -> Tube r E) :
    allExactTubeNsW87 (A.map e) W s =
      allExactTubeNsW87 A (fun a => W (e a)) s := by
  classical
  have hcell (R : Tube s E) :
      exactTubeCellW87 (A.map e) W R =
        (exactTubeCellW87 A (fun a => W (e a)) R).map e := by
    ext b
    simp only [exactTubeCellW87, Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hbody⟩
      exact ⟨a, ⟨ha, hbody⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hbody⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, hbody⟩
  apply le_antisymm
  · apply allExactTubeNs_le_w87
    intro R hne
    rw [hcell R, Kakeya.maxDensity_map]
    apply maxDensity_exactTubeCell_le_allExactTubeNs_w87 R
    simpa [hcell R] using hne
  · apply allExactTubeNs_le_w87
    intro R hne
    rw [← Kakeya.maxDensity_map
      (exactTubeCellW87 A (fun a => W (e a)) R) e
        (fun b => (W b).toConvexSpaceBody), ← hcell R]
    apply maxDensity_exactTubeCell_le_allExactTubeNs_w87 R
    rw [hcell R]
    exact Finset.map_nonempty.mpr hne

theorem inner_literal_Ns_drop_w87
    {iota : Type uI} [DecidableEq iota] {delta working d : NNReal}
    {base current : Finset iota} {T : iota -> Tube delta E}
    {M Ktr : Nat} {C : NNReal}
    (U : CanonicalProfileNetW87 base T M C) (q : Fin (M + 1))
    {Y : CanonicalQNodeW87 U current q ->
      ShadedTube (Tube.gridScale delta M q.val) E}
    {nodeFamily : Finset iota} {nodeTube : iota -> Tube working E}
    {part : iota -> Finset (CanonicalQNodeW87 U current q)}
    {epsilon zetaJ : Real}
    (inner : LiteralInnerDropOutputW87 U q Y nodeFamily nodeTube part
      d epsilon zetaJ Ktr)
    (hd : 0 < d) (hd1 : d <= 1) (hexp : 0 <= epsilon * zetaJ) :
    allExactTubeNsW87 (canonicalQNodeValuesW87 inner.FPlus)
        (fun w => U.cover.tube q.val w) working <=
      (C : ENNReal) * (d : ENNReal) ^ (epsilon * zetaJ / 8) *
        allExactTubeNsW87 (canonicalAncestorFamilyW87 U current q)
          (fun w => U.cover.tube q.val w) working := by
  classical
  let rawPart : iota -> Finset iota := fun P => canonicalQNodeValuesW87 (part P)
  let valEmbedding : CanonicalQNodeW87 U current q ↪ iota :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hcover : canonicalQNodeValuesW87 inner.FPlus <=
      nodeFamily.biUnion rawPart := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨wnode, hwPlus, rfl⟩
    rw [inner.assigned_cover] at hwPlus
    rcases Finset.mem_biUnion.mp hwPlus with ⟨P, hP, hwPart⟩
    exact Finset.mem_biUnion.mpr
      ⟨P, hP, Finset.mem_image.mpr ⟨wnode, hwPart, rfl⟩⟩
  have hlocal : ∀ P ∈ nodeFamily,
      Kakeya.maxDensity (rawPart P)
          (fun w => (U.cover.tube q.val w).toConvexSpaceBody) <=
        (d : ENNReal) ^ (epsilon * zetaJ / 4) *
          allExactTubeNsW87 (canonicalAncestorFamilyW87 U current q)
            (fun w => U.cover.tube q.val w) working := by
    intro P hP
    calc
      Kakeya.maxDensity (rawPart P)
          (fun w => (U.cover.tube q.val w).toConvexSpaceBody)
          = Kakeya.maxDensity (part P)
              (fun w => (U.cover.tube q.val w.val).toConvexSpaceBody) := by
            have hmap :=
              Kakeya.maxDensity_map (part P) valEmbedding
                (fun w => (U.cover.tube q.val w).toConvexSpaceBody)
            rw [Finset.map_eq_image] at hmap
            convert hmap using 1 <;> simp [rawPart, valEmbedding,
              canonicalQNodeValuesW87]
      _ = Kakeya.maxDensity (part P)
            (fun w => (inner.YPlus w).toConvexSpaceBody) := by
          apply Kakeya.maxDensity_congr
          intro w hw
          have hwPlus := inner.part_subset P hP hw
          rw [(inner.subshading w hwPlus).1, inner.middle_same_tube w]
      _ <= (d : ENNReal) ^ (epsilon * zetaJ / 4) *
          allExactTubeNsW87 (canonicalQNodeFinsetW87 U current q)
            (fun w => (Y w).toTube) working := inner.per_cell_density_drop P hP
      _ = (d : ENNReal) ^ (epsilon * zetaJ / 4) *
          allExactTubeNsW87 (canonicalAncestorFamilyW87 U current q)
            (fun w => U.cover.tube q.val w) working := by
          congr 1
          have hY : (fun w => (Y w).toTube) =
              (fun w => U.cover.tube q.val w.val) := by
            funext w
            exact inner.middle_same_tube w
          rw [hY]
          have hvalues : canonicalQNodeValuesW87
              (canonicalQNodeFinsetW87 U current q) =
              canonicalAncestorFamilyW87 U current q := by
            ext w
            simp [canonicalQNodeValuesW87, canonicalQNodeFinsetW87]
          calc
            allExactTubeNsW87 (canonicalQNodeFinsetW87 U current q)
                (fun w => U.cover.tube q.val w.val) working =
              allExactTubeNsW87 (canonicalQNodeValuesW87
                  (canonicalQNodeFinsetW87 U current q))
                (fun w => U.cover.tube q.val w) working := by
                  have hmap :=
                    (allExactTubeNs_map_w90 (s := working)
                      (canonicalQNodeFinsetW87 U current q)
                      valEmbedding
                      (fun w => U.cover.tube q.val w)).symm
                  rw [Finset.map_eq_image] at hmap
                  convert hmap using 1 <;> simp [valEmbedding,
                    canonicalQNodeValuesW87]
            _ = allExactTubeNsW87 (canonicalAncestorFamilyW87 U current q)
                (fun w => U.cover.tube q.val w) working := by rw [hvalues]
  have hmeeting : forall R : Tube working E,
      (((nodeFamily.filter fun P =>
        (rawPart P ∩ exactTubeCellW87 (canonicalQNodeValuesW87 inner.FPlus)
          (fun w => U.cover.tube q.val w) R).Nonempty).card : Nat) : ENNReal) <= C := by
    intro R
    have hfilter :
        nodeFamily.filter (fun P =>
          (rawPart P ∩ exactTubeCellW87 (canonicalQNodeValuesW87 inner.FPlus)
            (fun w => U.cover.tube q.val w) R).Nonempty) <=
        nodeFamily.filter (fun P => ∃ w ∈ canonicalQNodeFinsetW87 U current q,
          (Y w).toConvexSpaceBody <= (nodeTube P).toConvexSpaceBody /\
          (Y w).toConvexSpaceBody <= R.toConvexSpaceBody) := by
      intro P hP
      have hP' := Finset.mem_filter.mp hP
      rcases hP'.2 with ⟨w, hw⟩
      have hwPart' := Finset.mem_inter.mp hw
      rcases Finset.mem_image.mp hwPart'.1 with ⟨wnode, hwnodePart, rfl⟩
      have hwPlus := inner.part_subset P hP'.1 hwnodePart
      have hwAll := inner.FPlus_subset hwPlus
      have hparent := inner.part_parent_containment P hP'.1 wnode hwnodePart
      have hsub := (inner.subshading wnode hwPlus).1
      have hmiddle := inner.middle_same_tube wnode
      refine Finset.mem_filter.mpr ⟨hP'.1, wnode, hwAll, ?_, ?_⟩
      · simpa [hsub] using hparent
      · have hcellBody := (Finset.mem_filter.mp hwPart'.2).2
        simpa [hmiddle] using hcellBody
    have hcard :
        (((nodeFamily.filter fun P =>
          (rawPart P ∩ exactTubeCellW87 (canonicalQNodeValuesW87 inner.FPlus)
            (fun w => U.cover.tube q.val w) R).Nonempty).card : Nat) : ENNReal) <=
        (((nodeFamily.filter fun P => ∃ w ∈ canonicalQNodeFinsetW87 U current q,
          (Y w).toConvexSpaceBody <= (nodeTube P).toConvexSpaceBody /\
          (Y w).toConvexSpaceBody <= R.toConvexSpaceBody).card : Nat) : ENNReal) := by
      exact_mod_cast Finset.card_le_card hfilter
    exact hcard.trans (by
      simpa [Tube.HasBoundedOverlap] using inner.parent_boundedOverlap R)
  have hdrop := allExactTubeNs_le_of_assignedCover_w87
    nodeFamily rawPart ((d : ENNReal) ^ (epsilon * zetaJ / 4)) (C : ENNReal)
    hcover hlocal hmeeting
  refine hdrop.trans ?_
  have hpow : (d : ENNReal) ^ (epsilon * zetaJ / 4) <=
      (d : ENNReal) ^ (epsilon * zetaJ / 8) := by
    apply ENNReal.rpow_le_rpow_of_exponent_ge
    · exact_mod_cast hd1
    · linarith
  exact mul_le_mul_right' (mul_le_mul_left' hpow (C : ENNReal)) _

theorem inner_before_le_canonical_before_w87
    {iota : Type uI} [DecidableEq iota]
    {delta : NNReal} {base current : Finset iota}
    {T : iota -> Tube delta E} {M : Nat} {C : NNReal}
    (U : CanonicalProfileNetW87 base T M C)
    (q ellPred : Fin (M + 1))
    (working : NNReal)
    (hscale : working <= Tube.gridScale delta M ellPred.val) :
    allExactTubeNsW87 (canonicalAncestorFamilyW87 U current q)
        (fun w => U.cover.tube q.val w) working <=
      literalCanonicalDW87 U current q ellPred := by
  unfold literalCanonicalDW87
  apply allExactTubeNs_le_w87
  intro R hne
  let R' : Tube (Tube.gridScale delta M ellPred.val) E :=
    R.rescale (Tube.gridScale delta M ellPred.val)
  have hcell : exactTubeCellW87 (canonicalAncestorFamilyW87 U current q)
      (fun w => U.cover.tube q.val w) R <=
      exactTubeCellW87 (canonicalAncestorFamilyW87 U current q)
        (fun w => U.cover.tube q.val w) R' := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr
      ⟨hi'.1, hi'.2.trans (Tube.le_rescale R hscale)⟩
  have hne' : (exactTubeCellW87 (canonicalAncestorFamilyW87 U current q)
      (fun w => U.cover.tube q.val w) R').Nonempty := hne.mono hcell
  exact (Kakeya.maxDensity_mono _ hcell).trans
    (maxDensity_exactTubeCell_le_allExactTubeNs_w87 R' hne')

theorem canonical_after_le_inner_after_w87
    {iota : Type uI} [DecidableEq iota]
    {delta : NNReal} {base current : Finset iota}
    {T : iota -> Tube delta E} {C : NNReal} {p : Params}
    (P : RevisedProfileParametersW87 p)
    (U : CanonicalProfileNetW87 base T P.M C)
    (hdim : Module.finrank Real E = 3)
    (hdelta : 0 < delta)
    (hcurrent : current <= base)
    (q ellPred : Fin (P.M + 1)) (working : NNReal)
    (keptNodes : Finset (CanonicalQNodeW87 U current q))
    (hworking : 0 < working)
    (hmember : 2 * Tube.gridScale delta P.M q.val <= working)
    (hround_lower : Tube.gridScale delta P.M (ellPred.val + 1) <= working)
    (hround : working < Tube.gridScale delta P.M ellPred.val) :
    literalCanonicalDW87 U
        (saturatedFineLiftW87 U current q
          (canonicalQNodeValuesW87 keptNodes)) q ellPred <=
      ENNReal.ofReal
          (2 * 25 ^ (6 : Nat) * 4 ^ (6 : Nat) *
            (delta : Real) ^ (-6 / (P.M : Real))) *
        allExactTubeNsW87 (canonicalQNodeValuesW87 keptNodes)
          (fun w => U.cover.tube q.val w) working := by
  have hratio : (Tube.gridScale delta P.M ellPred.val : Real) / (working : Real) <=
      (delta : Real) ^ (-1 / (P.M : Real)) := by
    calc
      (Tube.gridScale delta P.M ellPred.val : Real) / (working : Real) <=
          (Tube.gridScale delta P.M ellPred.val : Real) /
            (Tube.gridScale delta P.M (ellPred.val + 1) : Real) :=
        div_le_div_of_nonneg_left (NNReal.coe_nonneg _)
          (by exact_mod_cast Tube.gridScale_pos hdelta P.M (ellPred.val + 1))
          (by exact_mod_cast hround_lower)
      _ = (delta : Real) ^ (-1 / (P.M : Real)) := by
        rw [← NNReal.coe_div, Tube.gridScale_div_gridScale hdelta, NNReal.coe_rpow]
        congr 1
        push_cast
        ring
  have hconstant :
      2 * 25 ^ (6 : Nat) *
          (4 * (Tube.gridScale delta P.M ellPred.val : Real) / (working : Real)) ^ (6 : Nat) <=
        2 * 25 ^ (6 : Nat) * 4 ^ (6 : Nat) *
          (delta : Real) ^ (-6 / (P.M : Real)) := by
    calc
      2 * 25 ^ (6 : Nat) *
          (4 * (Tube.gridScale delta P.M ellPred.val : Real) / (working : Real)) ^ (6 : Nat) =
          (2 * 25 ^ (6 : Nat) * 4 ^ (6 : Nat)) *
            ((Tube.gridScale delta P.M ellPred.val : Real) / (working : Real)) ^ (6 : Nat) := by
        ring
      _ <= (2 * 25 ^ (6 : Nat) * 4 ^ (6 : Nat)) *
          ((delta : Real) ^ (-1 / (P.M : Real))) ^ (6 : Nat) := by
        gcongr
      _ = _ := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg delta)]
        congr 1
        ring
  unfold literalCanonicalDW87
  rw [image_saturatedFineLift_eq_w87]
  exact (allExactTubeNs_coarse_le_fine_w87
    (canonicalQNodeValuesW87 keptNodes) (fun w => U.cover.tube q.val w)
    hdim (Tube.gridScale_pos hdelta P.M q.val) hmember hround.le).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal hconstant) _)

theorem raw_literalCanonicalD_drop_w87
    {iota : Type uI} [DecidableEq iota]
    {delta working d : NNReal} {base current next : Finset iota}
    {T : iota -> Tube delta E} {p : Params}
    (P : RevisedProfileParametersW87 p)
    (U : CanonicalProfileNetW87 base T P.M P.canonicalC)
    (q ellPred : Fin (P.M + 1)) (zetaJ : Real)
    {Y : CanonicalQNodeW87 U current q ->
      ShadedTube (Tube.gridScale delta P.M q.val) E}
    {nodeFamily : Finset iota} {nodeTube : iota -> Tube working E}
    {part : iota -> Finset (CanonicalQNodeW87 U current q)} {Ktr : Nat}
    (inner : LiteralInnerDropOutputW87 U q Y nodeFamily nodeTube part
      d p.ε zetaJ Ktr)
    (hdim : Module.finrank Real E = 3)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hd : 0 < d) (hd1 : d <= 1) (hexp : 0 <= p.ε * zetaJ)
    (hcurrent : current <= base)
    (hnext : next = saturatedFineLiftW87 U current q
      (canonicalQNodeValuesW87 inner.FPlus))
    (hround_lower : Tube.gridScale delta P.M (ellPred.val + 1) <= working)
    (hround : working < Tube.gridScale delta P.M ellPred.val) :
    literalCanonicalDW87 U next q ellPred <=
      ENNReal.ofReal (canonicalComparisonFactorW87 P delta d zetaJ) *
        literalCanonicalDW87 U current q ellPred := by
  let A : Real := 2 * 25 ^ (6 : Nat) * 4 ^ (6 : Nat) *
    (delta : Real) ^ (-6 / (P.M : Real))
  have hworking : 0 < working :=
    (mul_pos (by norm_num) (Tube.gridScale_pos hdelta P.M q.val)).trans_le
      inner.member_twice_le_working
  have hcanonical := canonical_after_le_inner_after_w87 P U hdim hdelta hcurrent
    q ellPred working inner.FPlus hworking inner.member_twice_le_working hround_lower hround
  have hinner := inner_literal_Ns_drop_w87 U q inner hd hd1 hexp
  have hbefore := inner_before_le_canonical_before_w87
    (current := current) U q ellPred working hround.le
  have hcoefficient : ENNReal.ofReal A * (P.canonicalC : ENNReal) *
      (d : ENNReal) ^ (p.ε * zetaJ / 8) =
        ENNReal.ofReal (canonicalComparisonFactorW87 P delta d zetaJ) := by
    have hA : 0 <= A := by dsimp [A]; positivity
    have hdR : (0 : Real) < (d : Real) := by exact_mod_cast hd
    have hfactor : canonicalComparisonFactorW87 P delta d zetaJ =
        A * (P.canonicalC : Real) * (d : Real) ^ (p.ε * zetaJ / 8) := by
      dsimp [canonicalComparisonFactorW87, sourceCgeomW87, A]
      ring
    rw [hfactor, ENNReal.ofReal_mul (mul_nonneg hA (NNReal.coe_nonneg _)),
      ENNReal.ofReal_mul hA, ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_rpow_of_pos hdR, ENNReal.ofReal_coe_nnreal]
  rw [hnext]
  calc
    literalCanonicalDW87 U
        (saturatedFineLiftW87 U current q (canonicalQNodeValuesW87 inner.FPlus)) q ellPred <=
        ENNReal.ofReal A * allExactTubeNsW87 (canonicalQNodeValuesW87 inner.FPlus)
          (fun w => U.cover.tube q.val w) working := hcanonical
    _ <= ENNReal.ofReal A * ((P.canonicalC : ENNReal) *
        (d : ENNReal) ^ (p.ε * zetaJ / 8) *
          allExactTubeNsW87 (canonicalAncestorFamilyW87 U current q)
            (fun w => U.cover.tube q.val w) working) := mul_le_mul_right hinner _
    _ = (ENNReal.ofReal A * (P.canonicalC : ENNReal) *
        (d : ENNReal) ^ (p.ε * zetaJ / 8)) *
          allExactTubeNsW87 (canonicalAncestorFamilyW87 U current q)
            (fun w => U.cover.tube q.val w) working := by ring
    _ <= (ENNReal.ofReal A * (P.canonicalC : ENNReal) *
        (d : ENNReal) ^ (p.ε * zetaJ / 8)) *
          literalCanonicalDW87 U current q ellPred := mul_le_mul_right hbefore _
    _ = _ := by rw [hcoefficient]

theorem raw_literalCanonicalD_drop_of_coordinate_w93
    {iota : Type uI} [DecidableEq iota]
    {delta working : NNReal} {base current next sPrime : Finset iota}
    {T : iota -> ShadedTube delta E} {p : Params} {Cds : NNReal}
    (P : RevisedProfileParametersW87 p)
    (Ublock : Tube.UniformTubeSet sPrime (fun i => (T i).toTube)
      (Tube.ssfGridLen delta) Cds)
    (U : CanonicalProfileNetW87 base (fun i => (T i).toTube) P.M P.canonicalC)
    {a b m : Nat}
    (coordinate : CanonicalDropCoordinateW87 Ublock P a b m working)
    {Y : CanonicalQNodeW87 U current coordinate.q ->
      ShadedTube (Tube.gridScale delta P.M coordinate.q.val) E}
    {nodeFamily : Finset iota} {nodeTube : iota -> Tube working E}
    {part : iota -> Finset (CanonicalQNodeW87 U current coordinate.q)} {Ktr : Nat}
    (inner : LiteralInnerDropOutputW87 U coordinate.q Y nodeFamily nodeTube part
      (blockRatioW87 Ublock a b) p.ε (p.η m) Ktr)
    (hdim : Module.finrank Real E = 3)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hcurrent : current <= base)
    (hnext : next = saturatedFineLiftW87 U current coordinate.q
      (canonicalQNodeValuesW87 inner.FPlus)) :
    literalCanonicalDW87 U next coordinate.q coordinate.ellPred <=
      ENNReal.ofReal
          (canonicalComparisonFactorW87 P delta (blockRatioW87 Ublock a b) (p.η m)) *
        literalCanonicalDW87 U current coordinate.q coordinate.ellPred := by
  have hsuccessor : coordinate.ellPred.val + 1 = coordinate.ell.val := by
    have hpred := coordinate.ellPred_eq
    have hpos := coordinate.ell_pos
    omega
  have hlower : Tube.gridScale delta P.M (coordinate.ellPred.val + 1) <= working := by
    simpa only [hsuccessor] using coordinate.ell_round
  have heta : 0 <= p.η m :=
    (P.zeta0_pos.trans_le (P.zeta_mono (Nat.zero_le m))).le
  exact raw_literalCanonicalD_drop_w87 P U coordinate.q coordinate.ellPred (p.η m)
    inner hdim hdelta hdelta1 coordinate.ratio_pos coordinate.ratio_le_one
    (mul_nonneg P.epsilon_pos.le heta) hcurrent hnext hlower coordinate.ell_round_pred

end

end Kakeya.ml1Boot.RevisedLiteralProfileInterfaceFormalizerW87
