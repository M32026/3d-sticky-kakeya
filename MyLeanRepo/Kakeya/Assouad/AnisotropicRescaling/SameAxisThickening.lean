import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Same-axis tube thickening

Change only the radius parameter of a tube or indexed tube family.  The axis,
basepoint, and direction remain fixed.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Reinterpret a tube at a new radius without changing its axis segment. -/
def sameAxisTube {delta rho : ℝ}
    (T : Kakeya.DeltaTube delta) : Kakeya.DeltaTube rho where
  base := T.base
  direction := T.direction
  direction_unit := T.direction_unit

@[simp] lemma sameAxisTube_base {delta rho : ℝ}
    (T : Kakeya.DeltaTube delta) :
    (sameAxisTube (rho := rho) T).base = T.base := rfl

@[simp] lemma sameAxisTube_direction {delta rho : ℝ}
    (T : Kakeya.DeltaTube delta) :
    (sameAxisTube (rho := rho) T).direction = T.direction := rfl

lemma sameAxisTube_carrier_mono {delta rho : ℝ}
    (hdelta_rho : delta ≤ rho)
    (T : Kakeya.DeltaTube delta) :
    T.carrier ⊆ (sameAxisTube (rho := rho) T).carrier := by
  exact Metric.cthickening_mono hdelta_rho
    (Kakeya.unitSegment T.base T.direction)

/-- Change every tube radius in an indexed family while preserving indices. -/
def sameAxisTubeFamily {delta rho : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta) :
    Kakeya.Streamlined.TubeFamily rho where
  card := F.card
  tube i := sameAxisTube (rho := rho) (F.tube i)

@[simp] lemma sameAxisTubeFamily_card {delta rho : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta) :
    (sameAxisTubeFamily (rho := rho) F).card = F.card := rfl

@[simp] lemma sameAxisTubeFamily_tube {delta rho : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (i : Fin F.card) :
    (sameAxisTubeFamily (rho := rho) F).tube i =
      sameAxisTube (rho := rho) (F.tube i) := rfl

lemma sameAxisTubeFamily_isInVerticalChart {delta rho : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (hvertical : IsInVerticalChart F) :
    IsInVerticalChart (sameAxisTubeFamily (rho := rho) F) := by
  intro i
  exact hvertical i

lemma sameAxisTubeFamily_hasBoundedBase {delta rho R : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (hbase : HasBoundedBase F R) :
    HasBoundedBase (sameAxisTubeFamily (rho := rho) F) R := by
  intro i
  exact hbase i

/-- The identity assignment is a tube cover after increasing the radius. -/
def sameAxisTubeCover {delta rho : ℝ}
    (hdelta_rho : delta ≤ rho)
    (F : Kakeya.Streamlined.TubeFamily delta) :
    Kakeya.Streamlined.TubeCover F (sameAxisTubeFamily (rho := rho) F) where
  parent := id
  parent_surjective := Function.surjective_id
  nested i := sameAxisTube_carrier_mono hdelta_rho (F.tube i)

@[simp] lemma sameAxisTubeCover_parent {delta rho : ℝ}
    (hdelta_rho : delta ≤ rho)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (i : Fin F.card) :
    (sameAxisTubeCover hdelta_rho F).parent i = i := rfl

end Kakeya.Assouad
