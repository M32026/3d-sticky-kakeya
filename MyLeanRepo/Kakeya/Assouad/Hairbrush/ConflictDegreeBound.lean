import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling

/-!
# Conflict degree bound via Katz--Tao convex Wolff bound

Given a geometric containment lemma showing all tubes conflicting with a fixed
tube T lie in a single convex set W of controlled volume, the Katz--Tao bound
implies the number of conflicting tubes is at most `125 * C`.
-/

noncomputable section

open Finset Set MeasureTheory

namespace Kakeya.Assouad

/--
Degree bound: the number of tubes conflicting with a fixed tube T is at most
`125 * ENNReal.ofReal C`, using the Katz--Tao convex Wolff bound and a
geometric containment lemma.
-/
lemma conflict_degree_bound
    {δ : ℝ} {F : Kakeya.TubeFamily δ} {C : ℝ}
    (hdelta : 0 < δ) (hdelta_one : δ ≤ 1)
    (hKT : Kakeya.KatzTaoConvexWolffBound F C)
    (hF_ball : F.IsInUnitBall)
    (T : Kakeya.DeltaTube δ) (hT : T ∈ F)
    (h_geom : ∀ (T' : Kakeya.DeltaTube δ), T'.IsInUnitBall →
      ∃ (W : Set Point3), Convex ℝ W ∧ W ⊆ Kakeya.DeltaTube.unitBall ∧
        volume W ≤ 125 * Kakeya.deltaTubeVolume δ ∧
        ∀ (U : Kakeya.DeltaTube δ), U.IsInUnitBall →
          T'.carrier ∩ U.carrier ≠ ∅ → hairbrushAcuteAngle T' U < δ → U.carrier ⊆ W) :
    Kakeya.TubeFamily.enncard (F.filter (fun U => T.carrier ∩ U.carrier ≠ ∅ ∧ hairbrushAcuteAngle T U < δ)) ≤
      125 * ENNReal.ofReal C := by
  classical
  have hT_ball : T.IsInUnitBall := by
    exact hF_ball (hT)
  rcases h_geom T hT_ball with ⟨W, hW_convex, hW_ball, hW_vol, hW_contain⟩
  let conflictSet := F.filter (fun U => T.carrier ∩ U.carrier ≠ ∅ ∧ hairbrushAcuteAngle T U < δ)
  have h1 : ∀ U ∈ conflictSet, U.carrier ⊆ W := by
    intro U hU
    have hU_in_F : U ∈ F := (Finset.mem_filter.mp hU).1
    have h_conf := (Finset.mem_filter.mp hU).2
    have hU_ball : U.IsInUnitBall := hF_ball hU_in_F
    exact hW_contain U hU_ball h_conf.1 h_conf.2
  have h2 : conflictSet ⊆ F.filter (fun U => U.carrier ⊆ W) := by
    intro U hU
    have hU_in_F : U ∈ F := (Finset.mem_filter.mp hU).1
    exact Finset.mem_filter.mpr ⟨hU_in_F, h1 U hU⟩
  have h3 : Kakeya.TubeFamily.enncard conflictSet ≤ F.containedCount W := by
    have h4 : (↑conflictSet.card : ENNReal) ≤ (↑(F.filter (fun U => U.carrier ⊆ W)).card : ENNReal) := by
      exact_mod_cast Finset.card_le_card h2
    simpa [Kakeya.TubeFamily.containedCount, Kakeya.TubeFamily.enncard] using h4
  have h5 : F.containedCount W ≤
      ENNReal.ofReal C * volume W * (Kakeya.deltaTubeVolume δ)⁻¹ :=
    hKT W hW_convex
  have hvol_pos_finite : 0 < Kakeya.deltaTubeVolume δ ∧ Kakeya.deltaTubeVolume δ ≠ ⊤ :=
    tube_volume_scaling.2.1 δ hdelta hdelta_one
  have hvol_ne_zero : Kakeya.deltaTubeVolume δ ≠ 0 := hvol_pos_finite.1.ne'
  have hvol_ne_top : Kakeya.deltaTubeVolume δ ≠ ⊤ := hvol_pos_finite.2
  have h_mul_inv : Kakeya.deltaTubeVolume δ * (Kakeya.deltaTubeVolume δ)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hvol_ne_zero hvol_ne_top
  have h6 : ENNReal.ofReal C * volume W * (Kakeya.deltaTubeVolume δ)⁻¹ ≤
      125 * ENNReal.ofReal C := by
    calc
      ENNReal.ofReal C * volume W * (Kakeya.deltaTubeVolume δ)⁻¹
        ≤ ENNReal.ofReal C * (125 * Kakeya.deltaTubeVolume δ) * (Kakeya.deltaTubeVolume δ)⁻¹ := by
          gcongr
      _ = 125 * (ENNReal.ofReal C * (Kakeya.deltaTubeVolume δ * (Kakeya.deltaTubeVolume δ)⁻¹)) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
      _ = 125 * ENNReal.ofReal C := by
          rw [h_mul_inv, mul_one]
  exact le_trans (le_trans h3 h5) h6

end Kakeya.Assouad
