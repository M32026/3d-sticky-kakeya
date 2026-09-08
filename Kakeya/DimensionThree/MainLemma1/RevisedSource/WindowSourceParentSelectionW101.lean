module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceWindowTrialW98

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

/-- Within one old normalized cell, only a fixed number of source Drop
parents occur. Each counted incidence has an actual common fine tube. -/
theorem actual_window_source_parent_degree_w101
    (hdim : Module.finrank Real E = 3)
    {iota : Type uI} [DecidableEq iota] {d : NNReal}
    {F : Finset iota} {Y : iota -> ShadedTube d E} {L : Nat}
    {rho : Nat -> NNReal} {Ctw Ccell : NNReal}
    (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell)
    {epsilon zeta : Real} {Ktr : Nat}
    (drop : WindowDetailedTrialDropW98 cells epsilon zeta Ktr)
    (hd : 0 < d) (hd1 : d <= 1) (hepsilon : 0 < epsilon) (hCtw : 1 <= Ctw)
    (hball : ∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1)
    (H : Finset iota) (hH : H ⊆ drop.Fplus) :
    ∀ S : iota,
      ((completeFibreW94 H (cells.assign drop.level.val) S).image drop.assignPlus).card <=
        trialNearbyParentCountW96 Ctw := by
  have hl : drop.level.val <= L := Nat.le_of_lt_succ drop.level.isLt
  have hdr : d <= rho drop.level.val := by
    apply ENNReal.coe_le_coe.mp
    calc
      (d : ENNReal) = (d : ENNReal) ^ (1 : Real) := (ENNReal.rpow_one _).symm
      _ <= (d : ENNReal) ^ (1 - 3 * epsilon / 2) :=
        ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd1) (by linarith)
      _ <= _ := drop.window_lower
  have hr1 : rho drop.level.val <= 1 := by
    apply ENNReal.coe_le_coe.mp
    exact drop.window_upper.trans
      (ENNReal.rpow_le_one (by exact_mod_cast hd1) (by linarith))
  intro S
  let sourceParents := (completeFibreW94 H (cells.assign drop.level.val) S).image drop.assignPlus
  let meeting := commonFineMeetingParentsW96 F (fun Q => (Y Q).toTube)
    (cells.parentSet drop.level.val) (cells.parentTube drop.level.val)
    (cells.parentTube drop.level.val S)
  have hsub : sourceParents ⊆ meeting := by
    intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨hQH, hQS⟩ := Finset.mem_filter.mp hQ
    have hQD : Q ∈ drop.Fplus := hH hQH
    have hQF : Q ∈ F := drop.Fplus_subset hQD
    have hPnode : drop.assignPlus Q ∈ drop.nodes :=
      drop.assignPlus_image ▸ Finset.mem_image_of_mem _ hQD
    have hQsource := drop.assigned_containment (drop.assignPlus Q) hPnode
      (Finset.mem_filter.mpr ⟨hQD, rfl⟩)
    exact Finset.mem_filter.mpr ⟨drop.nodes_subset hPnode, Q, hQF,
      (Finset.mem_filter.mp hQsource).2,
      hQS ▸ cells.assigned_containment drop.level.val hl Q hQF⟩
  have hcount := card_assigned_parents_meeting_exact_cell_w96 hdim hd hdr hdr hr1
    F (fun Q => (Y Q).toTube) (cells.parentSet drop.level.val)
    (cells.parentTube drop.level.val) (cells.parentTube drop.level.val S)
    Ctw hCtw hball (cells.parent_ball drop.level.val hl) (cells.parent_line_ed drop.level.val hl)
  have hrzero : (rho drop.level.val : Real) ≠ 0 := by
    exact_mod_cast (cells.rho_pos drop.level.val hl).ne'
  simp only [div_self hrzero, max_self, one_pow, mul_one] at hcount
  exact (Finset.card_le_card hsub).trans (by exact_mod_cast hcount)

/-- The actual old/source-parent incidence bound pays a single fixed loss
for making the source Drop parent constant in every surviving old cell. -/
theorem exists_window_single_source_parent_refinement_w101
    (hdim : Module.finrank Real E = 3)
    {iota : Type uI} [DecidableEq iota] {d : NNReal}
    {F : Finset iota} {Y : iota -> ShadedTube d E} {L : Nat}
    {rho : Nat -> NNReal} {Ctw Ccell : NNReal}
    (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell)
    {epsilon zeta : Real} {Ktr : Nat}
    (drop : WindowDetailedTrialDropW98 cells epsilon zeta Ktr)
    (hd : 0 < d) (hd1 : d <= 1) (hepsilon : 0 < epsilon) (hCtw : 1 <= Ctw)
    (hball : ∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1)
    (H : Finset iota) (hH : H ⊆ drop.Fplus)
    (weight : iota -> ENNReal) (hmass : 0 < ∑ Q ∈ H, weight Q) :
    ∃ G : Finset iota, G.Nonempty ∧ G ⊆ H ∧
      ((trialNearbyParentCountW96 Ctw : Nat) : ENNReal)⁻¹ * (∑ Q ∈ H, weight Q) <=
        ∑ Q ∈ G, weight Q ∧
      (∀ Q ∈ G, ∀ Q' ∈ G, cells.assign drop.level.val Q = cells.assign drop.level.val Q' ->
        drop.assignPlus Q = drop.assignPlus Q') := by
  let old := cells.assign drop.level.val
  let nodes := H.image old
  let fibre := completeFibreW94 H old
  let parents := fun S => (fibre S).image drop.assignPlus
  let N := trialNearbyParentCountW96 Ctw
  have hdegree : ∀ S, (parents S).card <= N :=
    actual_window_source_parent_degree_w101 hdim cells drop hd hd1 hepsilon hCtw hball H hH
  have hparentsNonempty : ∀ S ∈ nodes, (parents S).Nonempty := by
    intro S hS
    obtain ⟨Q, hQ, hQS⟩ := Finset.mem_image.mp hS
    exact ⟨drop.assignPlus Q, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hQ, hQS⟩)⟩
  have hHne : H.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hmass
    exact lt_irrefl _ hmass
  obtain ⟨default, hdefault⟩ := hHne
  have hN : 0 < N :=
    (Finset.card_pos.mpr (hparentsNonempty (old default) (Finset.mem_image_of_mem _ hdefault))).trans_le
      (hdegree _)
  let contribution := fun S P => ∑ Q ∈ (fibre S).filter (fun Q => drop.assignPlus Q = P), weight Q
  have hbest : ∀ S ∈ nodes, ∃ P ∈ parents S,
      (∑ Q ∈ fibre S, weight Q) <= (N : ENNReal) * contribution S P := by
    intro S hS
    obtain ⟨P, hP, hmax⟩ := Finset.exists_max_image (parents S) (contribution S) (hparentsNonempty S hS)
    refine ⟨P, hP, ?_⟩
    have hsum : (∑ P ∈ parents S, contribution S P) = ∑ Q ∈ fibre S, weight Q :=
      Finset.sum_fiberwise_of_maps_to (fun Q hQ => Finset.mem_image_of_mem _ hQ) weight
    calc
      _ = ∑ P ∈ parents S, contribution S P := hsum.symm
      _ <= ∑ _P ∈ parents S, contribution S P := Finset.sum_le_sum (fun P' hP' => hmax P' hP')
      _ = ((parents S).card : ENNReal) * contribution S P := by rw [Finset.sum_const, nsmul_eq_mul]
      _ <= (N : ENNReal) * contribution S P := mul_le_mul_right' (by exact_mod_cast hdegree S) _
  choose selected selectedMem selectedMass using hbest
  let choice := fun S => if hS : S ∈ nodes then selected S hS else drop.assignPlus default
  let G := H.filter (fun Q => drop.assignPlus Q = choice (old Q))
  have hGH : G ⊆ H := Finset.filter_subset _ _
  have hfibre : ∀ S,
      completeFibreW94 G old S = (fibre S).filter (fun Q => drop.assignPlus Q = choice S) := by
    intro S
    ext Q
    simp only [completeFibreW94, G, fibre, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hQ, hQP⟩, hQS⟩
      rw [hQS] at hQP
      exact ⟨⟨hQ, hQS⟩, hQP⟩
    · rintro ⟨⟨hQ, hQS⟩, hQP⟩
      exact ⟨⟨hQ, by simpa only [hQS] using hQP⟩, hQS⟩
  have hpay : (∑ Q ∈ H, weight Q) <= (N : ENNReal) * ∑ Q ∈ G, weight Q := by
    have hsumH := Finset.sum_fiberwise_of_maps_to
      (fun Q (hQ : Q ∈ H) => Finset.mem_image_of_mem old hQ) weight
    have hsumG := Finset.sum_fiberwise_of_maps_to
      (fun Q (hQ : Q ∈ G) => Finset.mem_image_of_mem old (hGH hQ)) weight
    calc
      _ = ∑ S ∈ nodes, ∑ Q ∈ fibre S, weight Q := hsumH.symm
      _ <= ∑ S ∈ nodes, (N : ENNReal) * contribution S (choice S) := by
        apply Finset.sum_le_sum
        intro S hS
        simpa only [choice, dif_pos hS] using selectedMass S hS
      _ = (N : ENNReal) * ∑ Q ∈ G, weight Q := by
        rw [← hsumG, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        congr 1
        dsimp only [contribution]
        change (∑ Q ∈ (fibre S).filter (fun Q => drop.assignPlus Q = choice S), weight Q) =
          ∑ Q ∈ completeFibreW94 G old S, weight Q
        rw [hfibre S]
  have hGne : G.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty, mul_zero] at hpay
    exact (not_le_of_gt hmass) hpay
  refine ⟨G, hGne, hGH, ?_, ?_⟩
  · exact (ENNReal.inv_mul_le_iff (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top _)).mpr hpay
  · intro Q hQ Q' hQ' hQQ'
    obtain ⟨_, hQP⟩ := Finset.mem_filter.mp hQ
    obtain ⟨_, hQ'P⟩ := Finset.mem_filter.mp hQ'
    exact hQP.trans ((congrArg choice hQQ').trans hQ'P.symm)

 /-- The retained old-cell partition inherits the actual stronger Window
 Drop estimate through its selected source parent. -/
theorem exists_window_old_cell_density_refinement_w101
    (hdim : Module.finrank Real E = 3)
    {iota : Type uI} [DecidableEq iota] {d : NNReal}
    {F : Finset iota} {Y : iota -> ShadedTube d E} {L : Nat}
    {rho : Nat -> NNReal} {Ctw Ccell : NNReal}
    (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell)
    {epsilon zeta : Real} {Ktr : Nat}
    (drop : WindowDetailedTrialDropW98 cells epsilon zeta Ktr)
    (hd : 0 < d) (hd1 : d <= 1) (hepsilon : 0 < epsilon) (hCtw : 1 <= Ctw)
    (hball : ∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1)
    (H : Finset iota) (hH : H ⊆ drop.Fplus)
    (weight : iota -> ENNReal) (hmass : 0 < ∑ Q ∈ H, weight Q) :
    ∃ G : Finset iota, G.Nonempty ∧ G ⊆ H ∧
      ((trialNearbyParentCountW96 Ctw : Nat) : ENNReal)⁻¹ * (∑ Q ∈ H, weight Q) <=
        ∑ Q ∈ G, weight Q ∧
      (∀ S ∈ G.image (cells.assign drop.level.val),
        ∃ P ∈ drop.nodes,
          completeFibreW94 G (cells.assign drop.level.val) S ⊆
            completeFibreW94 drop.Fplus drop.assignPlus P ∧
          Kakeya.maxDensity (completeFibreW94 G (cells.assign drop.level.val) S)
            (fun Q => (drop.Yplus Q).toConvexSpaceBody) <=
              (d : ENNReal) ^ (epsilon * zeta / 2) *
                allExactTubeNsW87 F (fun Q => (Y Q).toTube) (rho drop.level.val)) := by
  obtain ⟨G, hGne, hGH, hpay, hconstant⟩ :=
    exists_window_single_source_parent_refinement_w101 hdim cells drop hd hd1
      hepsilon hCtw hball H hH weight hmass
  refine ⟨G, hGne, hGH, hpay, ?_⟩
  intro S hS
  obtain ⟨Q, hQ, hQS⟩ := Finset.mem_image.mp hS
  have hQD : Q ∈ drop.Fplus := hH (hGH hQ)
  have hP : drop.assignPlus Q ∈ drop.nodes :=
    drop.assignPlus_image ▸ Finset.mem_image_of_mem _ hQD
  have hsub : completeFibreW94 G (cells.assign drop.level.val) S ⊆
      completeFibreW94 drop.Fplus drop.assignPlus (drop.assignPlus Q) := by
    intro Q' hQ'
    obtain ⟨hQ'G, hQ'S⟩ := Finset.mem_filter.mp hQ'
    exact Finset.mem_filter.mpr ⟨hH (hGH hQ'G),
      hconstant Q' hQ'G Q hQ (hQ'S.trans hQS.symm)⟩
  exact ⟨drop.assignPlus Q, hP, hsub,
    (Kakeya.maxDensity_mono _ hsub).trans (drop.stronger_per_cell _ hP)⟩

end

end Kakeya.ml1Boot.TrialRestartW94
