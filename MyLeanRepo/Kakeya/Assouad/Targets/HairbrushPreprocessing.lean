import MyLeanRepo.Kakeya.Assouad.Multiplicity.PerTubePruning
import MyLeanRepo.Kakeya.Assouad.Hairbrush.AngleSeparation
import MyLeanRepo.Kakeya.Assouad.Hairbrush.ConflictDegreeBound
import MyLeanRepo.Kakeya.Assouad.Hairbrush.GeometricContainment
import MyLeanRepo.Kakeya.Assouad.Hairbrush.AssemblyHelpers
import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements

/-!
# Final assembly of hairbrush_preprocessing

Wires together all proved lemmas:
1. per_tube_pruning — aggregate to per-tube density
2. maximal_angle_separated_subset — select maximal angle-separated subfamily
3. conflict_degree_bound — degree bound via Katz-Tao + geometric containment
4. angle_separated_cardinality — cardinality retention from angle separation
5. card_retention_transfer, frostman_transfer — ENNReal algebra helpers
6. hairbrush_delta₀_exists — exponent threshold existence
-/

noncomputable section

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

theorem hairbrush_preprocessing : HairbrushPreprocessingStatement := by
  intro outputEta h_outputEta_pos
  rcases hairbrush_delta₀_exists outputEta h_outputEta_pos with
    ⟨inputEta, delta₀, h_inputEta_pos, h_eq, hdelta₀_pos, hdelta₀_half, hdelta₀_one, h_ineqs⟩
  let pruningEtaOut : ℝ := 3 * inputEta / 2

  refine ⟨inputEta, delta₀, h_inputEta_pos, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro δ hδ hδle₀ F hF_nonempty hF_ball hF_ed Y hY_dense hKT hFrostman

  have hineqs := h_ineqs δ hδ hδle₀
  have h_small_pruning := hineqs.1
  have h_conflict_ineq := hineqs.2.1
  have h_ineq3 := hineqs.2.2.1
  have h_ineq4 := hineqs.2.2.2

  have h_pruningEtaOut_pos : 0 < pruningEtaOut := by
    dsimp only [pruningEtaOut]; linarith
  have h_pruning_ineq : inputEta < pruningEtaOut := by
    dsimp only [pruningEtaOut]; linarith
  have hδle_one : δ ≤ 1 := le_trans hδle₀ hdelta₀_one
  have hδ_half : δ ≤ 1 / 2 := le_trans hδle₀ hdelta₀_half

  -- Step 1: Per-tube density pruning
  rcases per_tube_pruning hδ hδle_one
      (eta_in := inputEta) (eta_out := pruningEtaOut)
      h_inputEta_pos h_pruningEtaOut_pos h_pruning_ineq
      hY_dense h_small_pruning hF_nonempty hF_ball hF_ed with
    ⟨F1, Y1, hF1_sub, hF1_nonempty, hF1_ball, hF1_ed, hY1_union_sub,
      hY1_carrier_sub, hF1_card, hF1_per_tube⟩

  -- Step 2: Katz-Tao bound transfers to F1
  have hKT1 : Kakeya.KatzTaoConvexWolffBound F1 (Real.rpow δ (-inputEta)) := by
    intro W hW
    have h : F1.containedCount W ≤ F.containedCount W := by
      simp [Kakeya.TubeFamily.containedCount]; gcongr
    exact h.trans (hKT W hW)

  -- Step 3: Maximal angle-separated subset
  rcases maximal_angle_separated_subset hF1_nonempty with
    ⟨F2, hF2_sub, hF2_nonempty, hF2_angle_sep, hF2_maximal⟩

  -- Geometric containment: cobalt's lemma gives volume bound 125 directly
  let h_geom : ∀ (T' : Kakeya.DeltaTube δ), T'.IsInUnitBall →
      ∃ (W : Set Point3), Convex ℝ W ∧ W ⊆ Kakeya.DeltaTube.unitBall ∧
        volume W ≤ 125 * Kakeya.deltaTubeVolume δ ∧
        ∀ (U : Kakeya.DeltaTube δ), U.IsInUnitBall →
          T'.carrier ∩ U.carrier ≠ ∅ → hairbrushAcuteAngle T' U < δ → U.carrier ⊆ W := by
    intro T' hT'_ball
    exact conflicting_tubes_contained_in_convex_set hδ hδ_half T' hT'_ball

  -- Step 4: Conflict degree bound for all T ∈ F1
  let D : ENNReal := 125 * Kakeya.realRpowENN δ (-inputEta)
  have h_conflict_bound : ∀ T ∈ F1,
      (↑(F1.filter (fun U => T.carrier ∩ U.carrier ≠ ∅ ∧ hairbrushAcuteAngle T U < δ)).card : ENNReal) ≤ D := by
    intro T hT
    have h := conflict_degree_bound hδ hδle_one hKT1 hF1_ball T hT h_geom
    simpa [Kakeya.TubeFamily.enncard, D, Kakeya.realRpowENN] using h

  -- Step 5: Cardinality bound from angle separation
  have h_card_bound : F1.enncard ≤ (D + 1) * F2.enncard :=
    angle_separated_cardinality hF2_sub hF2_maximal D h_conflict_bound

  have h_card_bound2 : F1.enncard ≤
      (128 : ENNReal) * Kakeya.realRpowENN δ (-inputEta) * F2.enncard := by
    calc
      F1.enncard
        ≤ (D + 1) * F2.enncard := h_card_bound
      _ = ((125 : ENNReal) * Kakeya.realRpowENN δ (-inputEta) + 1) * F2.enncard := by rfl
      _ ≤ (128 * Kakeya.realRpowENN δ (-inputEta)) * F2.enncard :=
        mul_le_mul_of_nonneg_right h_conflict_ineq (by positivity)

  -- Step 6: Card retention at outputEta
  have hF2_card_retention :
      Kakeya.realRpowENN δ outputEta * F.enncard ≤ F2.enncard :=
    card_retention_transfer hδ hF1_card h_card_bound2 h_ineq3

  -- Card retention at outputEta - inputEta for Frostman transfer
  have hF2_card_frostman :
      Kakeya.realRpowENN δ (outputEta - inputEta) * F.enncard ≤ F2.enncard :=
    card_retention_transfer hδ hF1_card h_card_bound2 h_ineq4

  -- Step 7: Define shading Y2 on F2
  let Y2 : Kakeya.Shading F2 :=
    { carrier := Y1.carrier
      measurable_carrier := fun T hT => Y1.measurable_carrier (hF2_sub hT)
      subset_tube := fun T hT => Y1.subset_tube (hF2_sub hT) }

  -- Per-tube density at outputEta
  have hF2_per_tube : HairbrushPerTubeDense Y2 (Kakeya.realRpowENN δ outputEta) := by
    intro T hT
    have h1 : Kakeya.realRpowENN δ pruningEtaOut * T.volume ≤
        MeasureTheory.volume (Y2.carrier T) := hF1_per_tube T (hF2_sub hT)
    have h3 : Kakeya.realRpowENN δ outputEta ≤ Kakeya.realRpowENN δ pruningEtaOut := by
      apply ENNReal.ofReal_le_ofReal
      have h_exp : pruningEtaOut ≤ outputEta := by
        dsimp only [pruningEtaOut]
        linarith [h_eq, h_inputEta_pos]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδle_one h_exp
    calc
      Kakeya.realRpowENN δ outputEta * T.volume
        ≤ Kakeya.realRpowENN δ pruningEtaOut * T.volume := by gcongr
      _ ≤ MeasureTheory.volume (Y2.carrier T) := h1

  -- Union and carrier containment
  have hY2_union_sub : Y2.union ⊆ Y.union := by
    intro x hx
    rcases hx with ⟨T, hT, hxT⟩
    have hT1 : T ∈ F1 := hF2_sub hT
    refine ⟨T, hF1_sub hT1, ?_⟩
    exact hY1_carrier_sub T hT1 hxT

  have hY2_carrier_sub : ∀ (T : Kakeya.DeltaTube δ) (hT : T ∈ F2),
      Y2.carrier T ⊆ Y.carrier T := by
    intro T hT
    exact hY1_carrier_sub T (hF2_sub hT)

  -- Step 8: Katz-Tao transfer to F2
  have hKT2 : Kakeya.KatzTaoConvexWolffBound F2 (Real.rpow δ (-outputEta)) := by
    intro W hW
    have h1 : F2.containedCount W ≤ F1.containedCount W := by
      simp [Kakeya.TubeFamily.containedCount]; gcongr
    have h2 : F1.containedCount W ≤
        ENNReal.ofReal (Real.rpow δ (-inputEta)) * MeasureTheory.volume W *
          (Kakeya.deltaTubeVolume δ)⁻¹ := hKT1 W hW
    have h3 : ENNReal.ofReal (Real.rpow δ (-inputEta)) ≤
        ENNReal.ofReal (Real.rpow δ (-outputEta)) := by
      apply ENNReal.ofReal_le_ofReal
      have h_exp : -outputEta ≤ -inputEta := by linarith [h_eq, h_inputEta_pos]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδle_one h_exp
    calc
      F2.containedCount W
        ≤ F1.containedCount W := h1
      _ ≤ ENNReal.ofReal (Real.rpow δ (-inputEta)) * MeasureTheory.volume W *
            (Kakeya.deltaTubeVolume δ)⁻¹ := h2
      _ ≤ ENNReal.ofReal (Real.rpow δ (-outputEta)) * MeasureTheory.volume W *
            (Kakeya.deltaTubeVolume δ)⁻¹ := by gcongr

  -- Step 9: Frostman transfer
  have hF2_sub_F : F2 ⊆ F := hF2_sub.trans hF1_sub
  have hFrostman2 : Kakeya.FrostmanSlabWolffBound F2 (Real.rpow δ (-outputEta)) :=
    frostman_transfer hδ hF2_sub_F hFrostman hF2_card_frostman

  -- Inherited properties
  have hF2_ball : F2.IsInUnitBall := by
    intro T hT; exact hF1_ball (hF2_sub hT)
  have hF2_ed : F2.IsEssentiallyDistinct := by
    intro T hT U hU hne; exact hF1_ed (hF2_sub hT) (hF2_sub hU) hne

  -- Assemble
  let data : HairbrushPreparedData F Y outputEta :=
    { family := F2
      family_subset := hF2_sub_F
      shading := Y2
      shading_subset := hY2_carrier_sub
      nonempty := hF2_nonempty
      in_unit_ball := hF2_ball
      essentially_distinct := hF2_ed
      union_subset := hY2_union_sub
      card_retention := hF2_card_retention
      per_tube_dense := hF2_per_tube
      angle_separated := hF2_angle_sep
      katz_tao := hKT2
      frostman_slab := hFrostman2 }

  exact ⟨data⟩

end Kakeya.Assouad
