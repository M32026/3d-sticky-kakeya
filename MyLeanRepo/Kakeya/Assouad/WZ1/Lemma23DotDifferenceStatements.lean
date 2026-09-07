import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions

/-!
# Dot-difference geometry for WZ1 Lemma 23

Step 5 of the proof follows one four-cycle through two local grains and one
global grain.  The three grain errors telescope and place one dot-difference
value within `4 * rho` of the selected base global-grain value.

The planar coordinates below include the harmless quarter-turn needed for
the literal algebra:

* the height graph is represented by `(z, f z)`;
* the local-plane graph is represented by `(-g y, y)`.

Their dot difference is
`-z * (g y₁ - g y₃) + (y₁ - y₃) * f z`, exactly the expression obtained by
telescoping the local--global--local path.  This fixes the sign mismatch in
the displayed formula in the paper while preserving the projection theorem
under an orthogonal coordinate change.
-/

namespace Kakeya.Assouad

noncomputable section

/-- A point of the normalized height graph used as the first vertex class. -/
def wz1Lemma23HeightGraphPoint (f : ℝ → ℝ) (z : ℝ) : Point2 :=
  z • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
    f z • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

/--
A point of the normalized local-plane graph after the fixed quarter-turn
`(y,g(y)) ↦ (-g(y),y)`.
-/
def wz1Lemma23LocalGraphPoint (g : ℝ → ℝ) (y : ℝ) : Point2 :=
  (-g y) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
    y • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

/-- The scalar coordinate that is constant up to `rho` in one local grain. -/
def wz1Lemma23LocalCoordinate (g : ℝ → ℝ) (p : Point3) : ℝ :=
  p 0 + g (p 1) * p 2

/-- The scalar coordinate that is constant up to `rho` in one global grain. -/
def wz1Lemma23GlobalCoordinate (f : ℝ → ℝ) (p : Point3) : ℝ :=
  p 0 + f (p 2) * p 1

/--
The algebraic Step 5 of WZ1 Lemma 23.

`p₁--p₂` and `p₄--p₃` are local-grain edges, while `p₂--p₃` is a
global-grain edge.  The first and fourth points lie at the selected base
height.  The resulting projection-theorem dot difference is within `4 rho`
of `p₄.x - w`.
-/
def WZ1Lemma23FourCycleDotDifferenceStatement : Prop :=
  ∀ (rho w : ℝ) (f g : ℝ → ℝ) (p₁ p₂ p₃ p₄ : Point3),
    0 ≤ rho →
    p₁ 2 = 0 →
    p₄ 2 = 0 →
    p₂ 1 = p₁ 1 →
    p₄ 1 = p₃ 1 →
    p₃ 2 = p₂ 2 →
    |p₁ 0 - w| ≤ rho →
    |wz1Lemma23LocalCoordinate g p₁ -
        wz1Lemma23LocalCoordinate g p₂| ≤ rho →
    |wz1Lemma23GlobalCoordinate f p₂ -
        wz1Lemma23GlobalCoordinate f p₃| ≤ rho →
    |wz1Lemma23LocalCoordinate g p₃ -
        wz1Lemma23LocalCoordinate g p₄| ≤ rho →
      |inner ℝ
          (wz1Lemma23HeightGraphPoint f (p₂ 2))
          (wz1Lemma23LocalGraphPoint g (p₁ 1) -
            wz1Lemma23LocalGraphPoint g (p₃ 1)) -
        (p₄ 0 - w)| ≤
      4 * rho

end

end Kakeya.Assouad
