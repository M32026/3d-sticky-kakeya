import MyLeanRepo.Kakeya.Assouad.PropStickyLeafStatements

/-!
# Loss-normalized multiplicity for WZ2 `prop: sticky`

This is the exponent arithmetic weakening the strong relative caps to the
output loss in items (iii) and (iv).
-/

namespace Kakeya.Assouad

private lemma realRpowENN_add
    {base first second : ℝ} (hbase : 0 < base) :
    Kakeya.realRpowENN base first *
        Kakeya.realRpowENN base second =
      Kakeya.realRpowENN base (first + second) := by
  simp only [Kakeya.realRpowENN]
  have hfirst : 0 ≤ Real.rpow base first :=
    Real.rpow_nonneg hbase.le first
  calc
    ENNReal.ofReal (Real.rpow base first) *
          ENNReal.ofReal (Real.rpow base second) =
        ENNReal.ofReal
          (Real.rpow base first * Real.rpow base second) :=
      (ENNReal.ofReal_mul hfirst).symm
    _ = ENNReal.ofReal (Real.rpow base (first + second)) := by
      exact congrArg ENNReal.ofReal
        (Real.rpow_add hbase first second).symm

private lemma realRpowENN_antitone
    {base first second : ℝ}
    (hbase : 0 < base) (hbase_one : base ≤ 1)
    (h : first ≤ second) :
    Kakeya.realRpowENN base second ≤
      Kakeya.realRpowENN base first := by
  apply ENNReal.ofReal_mono
  exact Real.rpow_le_rpow_of_exponent_ge hbase hbase_one h

theorem wz2_prop_sticky_multiplicity_normalization :
    WZ2FormalCarrierPropStickyMultiplicityNormalizationStatement := by
  intro delta rho sigma strongLoss outputLoss
    hrho hrho_one hratio hratio_one hbudget
    coarse coarseShading hcoarseCap hcoarseCard
  constructor
  · intro point
    calc
      (coarseShading.pointMultiplicity point : ENNReal)
          ≤ Kakeya.realRpowENN rho
              (-sigma - strongLoss) :=
        hcoarseCap point
      _ = Kakeya.realRpowENN rho
            (2 - sigma - outputLoss) *
          Kakeya.realRpowENN rho
            (-2 + outputLoss - strongLoss) := by
        rw [realRpowENN_add hrho]
        congr 1
        ring
      _ ≤ Kakeya.realRpowENN rho
            (2 - sigma - outputLoss) *
          Kakeya.realRpowENN rho
            (-2 + 2 * strongLoss) := by
        gcongr
        exact realRpowENN_antitone hrho hrho_one (by linarith)
      _ ≤ Kakeya.realRpowENN rho
            (2 - sigma - outputLoss) *
          coarse.enncard := by
        gcongr
  · intro fine refined parent hfiberCard hfiberCap point
    calc
      (wz2FullFiberPointMultiplicity
          coarse refined parent point : ENNReal)
          ≤ Kakeya.realRpowENN (delta / rho)
              (-sigma - strongLoss) :=
        hfiberCap point
      _ = Kakeya.realRpowENN (delta / rho)
            (2 - sigma - outputLoss) *
          Kakeya.realRpowENN (delta / rho)
            (-2 + outputLoss - strongLoss) := by
        rw [realRpowENN_add hratio]
        congr 1
        ring
      _ ≤ Kakeya.realRpowENN (delta / rho)
            (2 - sigma - outputLoss) *
          wz2FullFiberCount fine coarse parent := by
        gcongr

/--
Cardinality-normalized multiplicity in the active cropped-paper model.
-/
theorem wz2_prop_sticky_paper_multiplicity_normalization :
    WZ2PropStickyPaperMultiplicityNormalizationStatement := by
  intro delta sigma strongLoss outputLoss
    hdelta hdelta_one hstrong_nonneg hbudget
    family shading hcap point
  have hstrong_output : strongLoss ≤ outputLoss := by
    linarith
  calc
    (shading.pointMultiplicity point : ENNReal)
        ≤ Kakeya.realRpowENN delta
              (2 - sigma - strongLoss) *
            family.enncard :=
      hcap point
    _ ≤ Kakeya.realRpowENN delta
          (2 - sigma - outputLoss) *
        family.enncard := by
      gcongr
      exact
        realRpowENN_antitone hdelta hdelta_one
          (by linarith)

end Kakeya.Assouad
