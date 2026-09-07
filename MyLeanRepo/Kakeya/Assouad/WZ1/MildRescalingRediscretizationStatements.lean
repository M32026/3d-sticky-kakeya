import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements

/-!
# Raw isotropic rediscretization for WZ1 Proposition 9

An isotropic dilation by a factor `S ≥ 1` sends a unit tube axis segment to a
segment of length `S`.  It therefore cannot be represented by one target
`DeltaTube`, whose axis segment still has length one.  The paper-faithful
first step is to cover the long image by finitely many unit target tubes on
the same axis.

This module freezes that raw geometric boundary.  It deliberately does not
assert that the target family is essentially distinct and does not construct
a target `UniformTubeStructure`; those require a subsequent weighted cleanup
and transport argument.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The positive isotropic similarity used in the mild rescaling. -/
def wz1IsotropicRescalingMap
    (center : Point3) (scale : ℝ) (p : Point3) : Point3 :=
  scale • (p - center)

/--
The canonical axial offset of slot `k` in an `n`-child isotropic
rediscretization.

All nonterminal children start at the integer offsets `0, 1, ...`; the final
child starts at `scale - 1`.  In particular, the final offset need not be an
integer when `scale` is not an integer, so downstream constructions should
match children by `k`, not by rounding their real base displacement.
-/
def wz1IsotropicChildOffset
    (n : ℕ) (scale : ℝ) (k : Fin n) : ℝ :=
  if (k : ℕ) + 1 < n then (k : ℝ) else scale - 1

/--
Raw multi-child rediscretization of an isotropically dilated tube family.

Every source tube has exactly `ceil scale` unit-length target children.  Their
canonical slot labels and exact bases are retained so that a later uniform
structure can match children produced from fine and coarse source tubes at the
same axial slot.  Their axis lines agree with the dilated source axis, their
full carriers lie in the dilated source carrier, and together they cover that
carrier.  The target shading is the exact restriction of the source shading
image to each child, so its union is exactly the image of the source shaded
union.
-/
structure WZ1IsotropicTubeRediscretizationData
    {sourceDelta scale : ℝ}
    (F : Kakeya.Streamlined.TubeFamily sourceDelta)
    (Y : Kakeya.Streamlined.TubeShading F)
    (center : Point3) where
  childCount : ℕ
  childCount_pos : 0 < childCount
  childCount_eq : childCount = Nat.ceil scale
  family :
    Kakeya.Streamlined.TubeFamily (scale * sourceDelta)
  shading :
    Kakeya.Streamlined.TubeShading family
  sourceParent :
    Fin family.card → Fin F.card
  childSlot :
    Fin family.card → Fin (Nat.ceil scale)
  childAt :
    Fin F.card → Fin (Nat.ceil scale) → Fin family.card
  sourceParent_childAt :
    ∀ i k, sourceParent (childAt i k) = i
  childSlot_childAt :
    ∀ i k, childSlot (childAt i k) = k
  childAt_sourceParent_childSlot :
    ∀ j, childAt (sourceParent j) (childSlot j) = j
  sourceParent_surjective :
    Function.Surjective sourceParent
  source_fiber_card :
    ∀ i,
      (Finset.univ.filter
        (fun j => sourceParent j = i)).card = childCount
  base_provenance :
    ∀ j,
      (family.tube j).base =
        wz1IsotropicRescalingMap center scale
            (F.tube (sourceParent j)).base +
          wz1IsotropicChildOffset
              (Nat.ceil scale) scale (childSlot j) •
            (F.tube (sourceParent j)).direction
  direction_provenance :
    ∀ j,
      (family.tube j).direction =
        (F.tube (sourceParent j)).direction
  axis_provenance :
    ∀ j,
      tubeAxisLine (family.tube j) =
        wz1IsotropicRescalingMap center scale ''
          tubeAxisLine (F.tube (sourceParent j))
  carrier_in_source_image :
    ∀ j,
      (family.tube j).carrier ⊆
        wz1IsotropicRescalingMap center scale ''
          (F.tube (sourceParent j)).carrier
  source_carrier_covered :
    ∀ i,
      wz1IsotropicRescalingMap center scale ''
          (F.tube i).carrier ⊆
        ⋃ j ∈
          Finset.univ.filter (fun j => sourceParent j = i),
            (family.tube j).carrier
  shading_carrier_eq :
    ∀ j,
      shading.carrier j =
        (family.tube j).carrier ∩
          wz1IsotropicRescalingMap center scale ''
            Y.carrier (sourceParent j)
  source_shading_covered :
    ∀ i,
      wz1IsotropicRescalingMap center scale '' Y.carrier i ⊆
        ⋃ j ∈
          Finset.univ.filter (fun j => sourceParent j = i),
            shading.carrier j
  shading_union_eq :
    shading.union =
      wz1IsotropicRescalingMap center scale '' Y.union

/-- Children of the same source parent have identical axis lines, hence identical
paper tube carriers. This is the key fact enabling CWA transport under isotropic
rediscretization: the contained count scales linearly by `childCount`. -/
lemma child_axisLine_eq
    {sourceDelta scale : ℝ}
    {F : Kakeya.Streamlined.TubeFamily sourceDelta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {center : Point3}
    (raw : WZ1IsotropicTubeRediscretizationData F Y center)
    {i : Fin F.card}
    {k1 k2 : Fin (Nat.ceil scale)} :
    tubeAxisLine (raw.family.tube (raw.childAt i k1)) =
    tubeAxisLine (raw.family.tube (raw.childAt i k2)) := by
  have h1 := raw.axis_provenance (raw.childAt i k1)
  have h2 := raw.axis_provenance (raw.childAt i k2)
  have h3 : raw.sourceParent (raw.childAt i k1) = i := raw.sourceParent_childAt i k1
  have h4 : raw.sourceParent (raw.childAt i k2) = i := raw.sourceParent_childAt i k2
  rw [h1, h2, h3, h4]

/--
Construct the raw unit-tube rediscretization of an isotropic image.

The upper bound on the target radius is included because all later WZ1 and
WZ2 tube APIs work at scales at most one.
-/
def WZ1IsotropicTubeRediscretizationStatement : Prop :=
  ∀ sourceDelta scale : ℝ,
    0 < sourceDelta →
    1 ≤ scale →
    scale * sourceDelta ≤ 1 →
      ∀ F : Kakeya.Streamlined.TubeFamily sourceDelta,
        F.Nonempty →
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            ∀ center : Point3,
              Nonempty
                (WZ1IsotropicTubeRediscretizationData
                  (scale := scale) F Y center)

/-- Children of the same source parent have identical WZ1 paper tube carriers,
since they share the same axis line and target scale. -/
lemma child_paper_carrier_eq
    {sourceDelta scale : ℝ}
    {F : Kakeya.Streamlined.TubeFamily sourceDelta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {center : Point3}
    (raw : WZ1IsotropicTubeRediscretizationData F Y center)
    {i : Fin F.card}
    {k1 k2 : Fin (Nat.ceil scale)} :
    wz1PaperTubeCarrier (raw.family.tube (raw.childAt i k1)) =
    wz1PaperTubeCarrier (raw.family.tube (raw.childAt i k2)) := by
  have h_axis : tubeAxisLine (raw.family.tube (raw.childAt i k1)) =
      tubeAxisLine (raw.family.tube (raw.childAt i k2)) :=
    child_axisLine_eq raw (i := i) (k1 := k1) (k2 := k2)
  simp [wz1PaperTubeCarrier, h_axis]

end Kakeya.Assouad
