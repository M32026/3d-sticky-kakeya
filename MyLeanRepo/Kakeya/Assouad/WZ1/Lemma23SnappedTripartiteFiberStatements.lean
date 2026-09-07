import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedFourCycleStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23TripartiteEncoding

/-!
# Bounded fibers of the snapped Lemma 23 tripartite encoding

After the paper fixes the base height and base global-grain bin, the
tripartite edge records the intermediate height and the two local y-layers.
The local/global/local grain relations then determine each successive
spatial cell up to at most two choices for its x-index.  Thus every edge has
at most `2^4 = 16` four-cycle preimages.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Real base height associated to one snapped integer z-index. -/
def wz1Lemma23SnappedBaseHeight
    (rho : ℝ) (baseHeightIndex : ℤ) : ℝ :=
  ((baseHeightIndex : ℝ) + 1 / 2) *
    gridSide (rho / 2)

/-- Four-cycles surviving the paper's base-height/global-bin pigeonhole. -/
def wz1Lemma23SnappedBaseCycles
    (rho : ℝ) (f g : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (baseHeightIndex baseGlobalBin : ℤ) :
    Finset
      ((ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ)) :=
  (wz1Lemma23SnappedFourCycles rho f g cells).filter
    fun path =>
      wz1Lemma23SnappedHeight path.1 = baseHeightIndex ∧
        wz1Lemma23SnappedGlobalBin rho f path.1 =
          baseGlobalBin

/-- Height-graph vertex after centering the selected base height. -/
def wz1Lemma23SnappedHeightPoint
    (rho : ℝ) (f : ℝ → ℝ)
    (baseHeightIndex : ℤ)
    (idx : ℤ × ℤ × ℤ) : Point2 :=
  let baseHeight :=
    wz1Lemma23SnappedBaseHeight rho baseHeightIndex
  wz1Lemma23HeightGraphPoint
    (wz1Lemma23CenteredSlope baseHeight f)
    ((wz1Lemma23SnappedPoint rho idx) 2 - baseHeight)

/-- Local-graph vertex after removing the harmless constant skew. -/
def wz1Lemma23SnappedLocalPoint
    (rho : ℝ) (g : ℝ → ℝ)
    (idx : ℤ × ℤ × ℤ) : Point2 :=
  wz1Lemma23LocalGraphPoint
    (wz1Lemma23CenteredLocal g)
    ((wz1Lemma23SnappedPoint rho idx) 1)

/-- The actual centered tripartite edge attached to one snapped four-cycle. -/
def wz1Lemma23SnappedTripartiteEdge
    (rho : ℝ) (f g : ℝ → ℝ)
    (baseHeightIndex : ℤ)
    (path :
      (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ)) :
    Point2 × Point2 × Point2 :=
  wz1Lemma23TripartiteEdge
    (wz1Lemma23SnappedHeightPoint
      rho f baseHeightIndex)
    (wz1Lemma23SnappedLocalPoint rho g)
    path

/--
Every actual centered tripartite edge has at most sixteen preimages after
fixing the base height and base global bin.  Consequently the edge image
retains at least one sixteenth of the four-cycle cardinality.
-/
def WZ1Lemma23SnappedTripartiteFiberStatement : Prop :=
  ∀ (rho : ℝ) (f g : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (baseHeightIndex baseGlobalBin : ℤ),
    0 < rho →
      let cycles :=
        wz1Lemma23SnappedBaseCycles
          rho f g cells baseHeightIndex baseGlobalBin
      let edge :=
        wz1Lemma23SnappedTripartiteEdge
          rho f g baseHeightIndex
      let edges := cycles.image edge
      (∀ value ∈ edges,
        (cycles.filter fun path => edge path = value).card ≤ 16) ∧
      cycles.card ≤ 16 * edges.card

end

end Kakeya.Assouad
