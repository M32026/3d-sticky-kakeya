module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.NormalizationGridAssemblyW103

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

open RevisedLiteralProfileInterfaceFormalizerW87

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

universe uE uI
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem lineED_subset_w103 {iota : Type uI} {r : NNReal} {F G : Finset iota}
    (hFG : F ⊆ G) (T : iota -> Tube r E) {C D : NNReal}
    (hline : lineEssentiallyDistinctW94 G T C) (hCD : C <= D) :
    lineEssentiallyDistinctW94 F T D := by
  intro o v hv
  refine le_trans ?_ ((hline o v hv).trans hCD)
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hFG)

theorem tube_volume_ne_zero_w103 {r : NNReal} (hr : 0 < r) (T : Tube r E) :
    volume T.carrier ≠ 0 := by
  have hc := Tube.le_volume.c_pos (Module.finrank Real E)
  exact (lt_of_lt_of_le (by positivity) (Tube.le_volume T)).ne'

theorem tube_center_norm_of_ball_w103 {r : NNReal} (hr : 0 < r) (T : Tube r E) (B : Real)
    (hball : T.carrier ⊆ Metric.closedBall 0 B) : ‖T.center‖ <= B := by
  have hmid : T.midpoint = T.center := by
    simp only [Tube.midpoint, Tube.center, midpoint_eq_smul_add]
    norm_num
  simpa only [Metric.mem_closedBall, dist_zero_right, hmid] using hball (Tube.midpoint_mem_carrier hr T)

theorem actual_fibre_data_w103
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan Ctw Ccell : NNReal}
    (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
    (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan)
    (restriction : VisibleExtendedRestrictionW97 U Uext)
    (reg : SourceRegularizedWorkingTowerW95 Uext Ctw Ccell)
    (hM : 1 <= M) (a b : Nat) (hab : a < b) (hb : b <= M)
    (R : iota) (hR : R ∈ U.cover.indexSet a) :
    let F := actualDescendantsW95 A U.cover.assign a b R
    let c := quotientGridIndexW97 M a b
    let parent := fun l => Kakeya.ML2Reduction.coarseNode Uext.cover.toChain (c l) (b * M)
    let D := fun l => if l < M then reg.countBand (c l) (b * M) else 1
    (F ⊆ U.cover.indexSet b) ∧
    (∀ l, l <= M -> 0 < D l) ∧
    (∀ l, l <= M -> ∀ S ∈ F.image (parent l),
      D l <= ((completeFibreW94 F (parent l) S).card : NNReal) ∧
      ((completeFibreW94 F (parent l) S).card : NNReal) < 2 * D l) ∧
    (∀ l, l <= M -> ∀ S ∈ F.image (parent l), ∀ Q ∈ completeFibreW94 F (parent l) S,
      (U.cover.tube b Q).toConvexSpaceBody <= (Uext.cover.tube (c l) S).toConvexSpaceBody) := by
  let F := actualDescendantsW95 A U.cover.assign a b R
  let c := quotientGridIndexW97 M a b
  let parent := fun l => Kakeya.ML2Reduction.coarseNode Uext.cover.toChain (c l) (b * M)
  let D := fun l => if l < M then reg.countBand (c l) (b * M) else 1
  obtain ⟨hFne, hF, himage, hfibre, hcf, hcount, hbottom⟩ :=
    extended_middle_fibres_w97 U Uext restriction reg hM a b hab hb R hR
  have hend : c M = b * M := by
    dsimp only [c, quotientGridIndexW97]
    rw [← Nat.add_mul, Nat.add_sub_of_le hab.le]
  have hbound : ∀ l, l <= M -> c l <= b * M := by
    intro l hl
    rw [← hend]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _
  have hstrict : ∀ l, l < M -> c l < b * M := by
    intro l hl
    rw [← hend]
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hl (Nat.sub_pos_of_lt hab)) _
  have hbottomF : ∀ S ∈ F.image (parent M), S ∈ F := by
    intro S hS
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hS
    change parent M Q ∈ F
    have heq : parent M Q = Q := (hbottom Q hQ).1
    rwa [heq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
    exact U.cover.assign_mem b hb i (Finset.mem_filter.mp hi).1
  · intro l hl
    dsimp only [D]
    split_ifs with hlt
    · exact reg.countBand_pos (c l) (b * M) (hstrict l hlt) (Nat.mul_le_mul_right M hb)
    · exact zero_lt_one
  · intro l hl S hS
    by_cases hlt : l < M
    · simpa only [D, if_pos hlt] using hcount l hlt S hS
    · have hlM : l = M := by omega
      subst l
      have hS' := hbottomF S hS
      rw [(hbottom S hS').2]
      norm_num [D]
  · intro l hl S hS Q hQ
    rw [hfibre l hl S hS] at hQ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨hiA, hiS⟩ := Finset.mem_filter.mp hi
    have hbody : ∀ {r s : NNReal} (T : Tube r E) (V : Tube s E),
        r = s -> HEq T V -> T.toConvexSpaceBody = V.toConvexSpaceBody := by
      intro r s T V hrs hTV
      subst s
      exact congrArg Tube.toConvexSpaceBody (eq_of_heq hTV)
    rw [hbody _ _ (restriction.radius b hb) (restriction.tube b hb _), ← hiS]
    exact Uext.cover.toChain.tube_assign_le (hbound l hl) (Nat.mul_le_mul_right M hb) hiA

end
end Kakeya.ml1Boot.TrialRestartW94
