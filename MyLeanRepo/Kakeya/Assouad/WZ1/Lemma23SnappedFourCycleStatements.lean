import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23FourCycleDotDifference
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23FourCycleStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedCellStatements

/-!
# Snapped local-global four-cycles for WZ1 Lemma 23

After snapping to canonical spatial-cell centers, the paper's combinatorial
keys have literal geometric meaning:

* the local key stores the exact y-index and a `rho`-mesh local-coordinate
  bin;
* the height key is the exact z-index;
* the global key is a `rho`-mesh global-coordinate bin.

Consequently a signature collision gives exact y/z equalities and three
grain-coordinate errors smaller than `rho`.  The closed four-cycle telescope
then places the associated dot difference within `4 * rho` of the selected
base global-grain value.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Canonical snapped point attached to one integer spatial-cell index. -/
abbrev wz1Lemma23SnappedPoint
    (rho : ℝ) (idx : ℤ × ℤ × ℤ) : Point3 :=
  wz1Lemma23CellCenter rho idx

/-- Exact height key of a snapped spatial cell. -/
def wz1Lemma23SnappedHeight
    (idx : ℤ × ℤ × ℤ) : ℤ :=
  idx.2.2

/-- Local-grain key: exact y-layer and local scalar-coordinate bin. -/
def wz1Lemma23SnappedLocalKey
    (rho : ℝ) (g : ℝ → ℝ)
    (idx : ℤ × ℤ × ℤ) : ℤ × ℤ :=
  (idx.2.1,
    Int.floor
      (wz1Lemma23LocalCoordinate g
        (wz1Lemma23SnappedPoint rho idx) / rho))

/-- Two snapped cells belong to the same discretized local grain. -/
def wz1Lemma23SameSnappedLocalGrain
    (rho : ℝ) (g : ℝ → ℝ)
    (first second : ℤ × ℤ × ℤ) : Prop :=
  wz1Lemma23SnappedLocalKey rho g first =
    wz1Lemma23SnappedLocalKey rho g second

/-- Global-grain scalar-coordinate bin of one snapped cell. -/
def wz1Lemma23SnappedGlobalBin
    (rho : ℝ) (f : ℝ → ℝ)
    (idx : ℤ × ℤ × ℤ) : ℤ :=
  Int.floor
    (wz1Lemma23GlobalCoordinate f
      (wz1Lemma23SnappedPoint rho idx) / rho)

/-- Ordered snapped four-cycles produced by the local-pair signatures. -/
def wz1Lemma23SnappedFourCycles
    (rho : ℝ) (f g : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ)) :
    Finset
      ((ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ)) :=
  by
    classical
    exact
      wz1Lemma23FourCycles cells
        (wz1Lemma23SameSnappedLocalGrain rho g)
        wz1Lemma23SnappedHeight
        (wz1Lemma23SnappedGlobalBin rho f)

/-- The paper's Step 4 skew transform centered at the selected base height. -/
def wz1Lemma23SkewPoint
    (baseHeight : ℝ) (f g : ℝ → ℝ) (p : Point3) : Point3 :=
  point3
    (p 0 + f baseHeight * p 1 + g 0 * (p 2 - baseHeight))
    (p 1)
    (p 2 - baseHeight)

/-- Global slope after centering the selected base height. -/
def wz1Lemma23CenteredSlope
    (baseHeight : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  f (z + baseHeight) - f baseHeight

/-- Local-plane graph function after removing its constant skew. -/
def wz1Lemma23CenteredLocal
    (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  g y - g 0

/--
Every snapped signature collision satisfies the exact hypotheses of the
closed four-cycle dot-difference telescope after the faithful Step 4 skew
transform.
-/
def WZ1Lemma23SnappedFourCycleDotContainmentStatement : Prop :=
  ∀ (rho w : ℝ) (f g : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (path :
      (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ)),
    0 < rho →
    path ∈ wz1Lemma23SnappedFourCycles rho f g cells →
    |wz1Lemma23GlobalCoordinate f
        (wz1Lemma23SnappedPoint rho path.1) - w| ≤ rho →
      let baseHeight :=
        (wz1Lemma23SnappedPoint rho path.1) 2
      let p₁ :=
        wz1Lemma23SkewPoint baseHeight f g
          (wz1Lemma23SnappedPoint rho path.1)
      let p₂ :=
        wz1Lemma23SkewPoint baseHeight f g
          (wz1Lemma23SnappedPoint rho path.2.1)
      let p₃ :=
        wz1Lemma23SkewPoint baseHeight f g
          (wz1Lemma23SnappedPoint rho path.2.2.1)
      let p₄ :=
        wz1Lemma23SkewPoint baseHeight f g
          (wz1Lemma23SnappedPoint rho path.2.2.2)
      let centeredSlope :=
        wz1Lemma23CenteredSlope baseHeight f
      let centeredLocal :=
        wz1Lemma23CenteredLocal g
      |inner ℝ
          (wz1Lemma23HeightGraphPoint centeredSlope (p₂ 2))
          (wz1Lemma23LocalGraphPoint centeredLocal (p₁ 1) -
            wz1Lemma23LocalGraphPoint centeredLocal (p₃ 1)) -
        (p₄ 0 - w)| ≤
      4 * rho

end

end Kakeya.Assouad
