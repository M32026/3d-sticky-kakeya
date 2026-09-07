import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions

/-!
# The four-cycle count in WZ1 Lemma 23

The locally-linear argument first counts ordered pairs of cubes in one local
grain.  It then groups those pairs by the three pieces of data

* the height of the first cube;
* the height of the second cube;
* the global-grain bin of the second cube.

Two pairs with the same signature give a closed four-step path: local,
global, local, and finally equal base height.  The paper applies
Cauchy--Schwarz to obtain many such paths.  This module freezes exactly that
finite combinatorial step, independently of the later geometric construction
of the projection-theorem sets `F`, `G`, and `H`.
-/

namespace Kakeya.Assouad

/-- Ordered pairs of active cubes lying in one local grain. -/
def wz1Lemma23LocalPairs
    {Cube : Type*} [DecidableEq Cube]
    (cubes : Finset Cube) (sameLocalGrain : Cube → Cube → Prop)
    [DecidableRel sameLocalGrain] : Finset (Cube × Cube) :=
  (cubes.product cubes).filter fun pair =>
    sameLocalGrain pair.1 pair.2

/--
The collision key used in Step 4 of the proof of WZ1 Lemma 23.

The third coordinate is the discretized global-grain value of the second
cube, not an arbitrary label attached to the pair.
-/
def wz1Lemma23PairSignature
    {Cube Height GlobalBin : Type*}
    (height : Cube → Height) (globalBin : Cube → GlobalBin)
    (pair : Cube × Cube) : Height × Height × GlobalBin :=
  (height pair.1, height pair.2, globalBin pair.2)

/--
The actual closed four-step paths produced by a signature collision.

The tuple is ordered as `(Q₁,Q₂,Q₃,Q₄)`.  It records:

* `Q₁,Q₂` in one local grain;
* `Q₃,Q₄` in one local grain;
* `Q₁,Q₄` at the same base height;
* `Q₂,Q₃` at the same height and in the same global-grain bin.
-/
def wz1Lemma23FourCycles
    {Cube Height GlobalBin : Type*}
    [DecidableEq Cube] [DecidableEq Height] [DecidableEq GlobalBin]
    (cubes : Finset Cube) (sameLocalGrain : Cube → Cube → Prop)
    [DecidableRel sameLocalGrain]
    (height : Cube → Height) (globalBin : Cube → GlobalBin) :
    Finset (Cube × Cube × Cube × Cube) :=
  (cubes.product (cubes.product (cubes.product cubes))).filter fun path =>
    sameLocalGrain path.1 path.2.1 ∧
      sameLocalGrain path.2.2.2 path.2.2.1 ∧
      height path.1 = height path.2.2.2 ∧
      height path.2.1 = height path.2.2.1 ∧
      globalBin path.2.1 = globalBin path.2.2.1

/--
The Cauchy--Schwarz collision count used in WZ1 Lemma 23.

If the local-pair signature takes at most `signatureBound` values, then
`#localPairs² ≤ signatureBound * #fourCycles`.  The conclusion counts actual
ordered four-cube paths, rather than pairs in an abstract fiber.
-/
def WZ1Lemma23FourCycleCountingStatement : Prop :=
  ∀ (Cube Height GlobalBin : Type*)
    [DecidableEq Cube] [DecidableEq Height] [DecidableEq GlobalBin],
    ∀ (cubes : Finset Cube)
      (sameLocalGrain : Cube → Cube → Prop)
      [DecidableRel sameLocalGrain]
      (height : Cube → Height)
      (globalBin : Cube → GlobalBin)
      (signatureBound : ℕ),
      let localPairs :=
        wz1Lemma23LocalPairs cubes sameLocalGrain
      let signatures :=
        localPairs.image
          (wz1Lemma23PairSignature height globalBin)
      let fourCycles :=
        wz1Lemma23FourCycles
          cubes sameLocalGrain height globalBin
      signatures.card ≤ signatureBound →
        localPairs.card ^ 2 ≤ signatureBound * fourCycles.card

end Kakeya.Assouad
