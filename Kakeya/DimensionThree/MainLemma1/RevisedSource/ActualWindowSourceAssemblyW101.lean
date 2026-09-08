module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceDropPreparationW101
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceCanonicalAssignedGeometryW101
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.WindowSourceParentSelectionW101

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

private theorem exists_weighted_constant_fibre_refinement_w101
    {iota : Type uI} [DecidableEq iota]
    (F : Finset iota) (parent source : iota -> iota) (weight : iota -> ENNReal)
    (N : Nat) (hN : 0 < N)
    (hdegree : ∀ P, ((completeFibreW94 F parent P).image source).card <= N)
    (hmass : 0 < ∑ i ∈ F, weight i) :
    ∃ G : Finset iota, G.Nonempty ∧ G ⊆ F ∧
      (N : ENNReal)⁻¹ * (∑ i ∈ F, weight i) <= ∑ i ∈ G, weight i ∧
      (∀ i ∈ G, ∀ j ∈ G, parent i = parent j -> source i = source j) := by
  let nodes := F.image parent
  let fibre := completeFibreW94 F parent
  let sources := fun P => (fibre P).image source
  let contribution := fun P S => ∑ i ∈ (fibre P).filter (fun i => source i = S), weight i
  have hnonempty : ∀ P ∈ nodes, (sources P).Nonempty := by
    intro P hP
    obtain ⟨i, hi, hiP⟩ := Finset.mem_image.mp hP
    exact ⟨source i, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hi, hiP⟩)⟩
  have hbest : ∀ P ∈ nodes, ∃ S ∈ sources P,
      (∑ i ∈ fibre P, weight i) <= (N : ENNReal) * contribution P S := by
    intro P hP
    obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image _ (contribution P) (hnonempty P hP)
    refine ⟨S, hS, ?_⟩
    have hsum : (∑ S ∈ sources P, contribution P S) = ∑ i ∈ fibre P, weight i :=
      Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi) weight
    calc
      _ = ∑ S ∈ sources P, contribution P S := hsum.symm
      _ <= ∑ _S ∈ sources P, contribution P S := Finset.sum_le_sum (fun S' hS' => hmax S' hS')
      _ = ((sources P).card : ENNReal) * contribution P S := by rw [Finset.sum_const, nsmul_eq_mul]
      _ <= (N : ENNReal) * contribution P S := mul_le_mul_left (by exact_mod_cast hdegree P) _
  have hFne : F.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hmass
    exact lt_irrefl _ hmass
  obtain ⟨default, hdefault⟩ := hFne
  choose selected selectedMem selectedMass using hbest
  let choice := fun P => if hP : P ∈ nodes then selected P hP else default
  let G := F.filter (fun i => source i = choice (parent i))
  have hGF : G ⊆ F := Finset.filter_subset _ _
  have hfibre : ∀ P, completeFibreW94 G parent P =
      (fibre P).filter (fun i => source i = choice P) := by
    intro P
    ext i
    simp only [completeFibreW94, G, fibre, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hi, hiS⟩, hiP⟩
      rw [hiP] at hiS
      exact ⟨⟨hi, hiP⟩, hiS⟩
    · rintro ⟨⟨hi, hiP⟩, hiS⟩
      exact ⟨⟨hi, by simpa only [hiP] using hiS⟩, hiP⟩
  have hsumF := Finset.sum_fiberwise_of_maps_to
    (fun i (hi : i ∈ F) => Finset.mem_image_of_mem parent hi) weight
  have hsumG := Finset.sum_fiberwise_of_maps_to
    (fun i (hi : i ∈ G) => Finset.mem_image_of_mem parent (hGF hi)) weight
  have hpay : (∑ i ∈ F, weight i) <= (N : ENNReal) * ∑ i ∈ G, weight i := by
    calc
      _ = ∑ P ∈ nodes, ∑ i ∈ fibre P, weight i := hsumF.symm
      _ <= ∑ P ∈ nodes, (N : ENNReal) * contribution P (choice P) := by
        apply Finset.sum_le_sum
        intro P hP
        simpa only [choice, dif_pos hP] using selectedMass P hP
      _ = (N : ENNReal) * ∑ i ∈ G, weight i := by
        rw [← hsumG, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro P hP
        congr 1
        change (∑ i ∈ (fibre P).filter (fun i => source i = choice P), weight i) =
          ∑ i ∈ completeFibreW94 G parent P, weight i
        rw [hfibre P]
  have hGne : G.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty, mul_zero] at hpay
    exact (not_le_of_gt hmass) hpay
  refine ⟨G, hGne, hGF,
    (ENNReal.inv_mul_le_iff (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top _)).mpr hpay, ?_⟩
  intro i hi j hj hij
  exact (Finset.mem_filter.mp hi).2.trans
    ((congrArg choice hij).trans (Finset.mem_filter.mp hj).2.symm)

/-- Across all eligible calls, one physical extended-tree parent determines
one old coarse fibre. The actual Window incidence bound therefore pays only
a fixed source-parent selection loss on the fine family. -/
theorem exists_actual_window_physical_source_refinement_w101
    (hdim : Module.finrank Real E = 3)
    {p : Params} {xi : Fin (p.N + 1) -> Real} {gamma : Real}
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat}
    {Cwork BF loss : NNReal}
    (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Cwork)
    (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Cwork)
    (restriction : VisibleExtendedRestrictionW97 U Uext)
    (block : ActualSourceDividingBlockW95 U p BF)
    (selections : ActualSameMassSelectionsW95 block loss)
    {Rnorm Cext Cnorm CtwNorm CcellNorm : NNReal}
    (aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M)
    (calls : ActualEligibleTrialCallsW97 Uext block selections xi gamma
      Rnorm Cext Cnorm CtwNorm CcellNorm aux)
    (drops : ∀ R (hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)),
      WindowDetailedTrialDropW98 (calls.normalization R hR).cells p.ε
        (p.η (block.label.val + 1) / 2) (aux.Ktr block.label))
    (hd : 0 < delta) (hd1 : delta <= 1) (hepsilon : 0 < p.ε) (hCtw : 1 <= CtwNorm)
    (level : Fin (M + 1)) (F : Finset iota) (hFA : F ⊆ A)
    (origin : iota -> {R // R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)})
    (hdrop : ∀ i ∈ F,
      U.cover.assign block.b.val i ∈ (drops (origin i).val (origin i).property).Fplus ∧
        (drops (origin i).val (origin i).property).level = level)
    (weight : iota -> ENNReal) (hmass : 0 < ∑ i ∈ F, weight i) :
    ∃ G : Finset iota, G.Nonempty ∧ G ⊆ F ∧
      ((trialNearbyParentCountW96 CtwNorm : Nat) : ENNReal)⁻¹ *
        (∑ i ∈ F, weight i) <= ∑ i ∈ G, weight i ∧
      (∀ i ∈ G, ∀ j ∈ G,
        Uext.cover.assign (quotientGridIndexW97 M block.a.val block.b.val level.val) i =
          Uext.cover.assign (quotientGridIndexW97 M block.a.val block.b.val level.val) j ->
        origin i = origin j ∧
          (drops (origin i).val (origin i).property).assignPlus (U.cover.assign block.b.val i) =
            (drops (origin j).val (origin j).property).assignPlus (U.cover.assign block.b.val j)) := by
  let c := quotientGridIndexW97 M block.a.val block.b.val level.val
  let physical := Uext.cover.assign c
  let middle := U.cover.assign block.b.val
  let source := fun i => (drops (origin i).val (origin i).property).assignPlus (middle i)
  have hb : block.b.val <= M := Nat.le_of_lt_succ block.b.isLt
  have ha : block.a.val <= M := block.a_lt_b.le.trans hb
  have hl : level.val <= M := Nat.le_of_lt_succ level.isLt
  have hac : block.a.val * M <= c := Nat.le_add_right _ _
  have hcb : c <= block.b.val * M := by
    dsimp only [c, quotientGridIndexW97]
    calc
      _ <= block.a.val * M + (block.b.val - block.a.val) * M :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _
      _ = _ := by rw [← Nat.add_mul, Nat.add_sub_of_le block.a_lt_b.le]
  have hcM : c <= M * M := hcb.trans (Nat.mul_le_mul_right M hb)
  have horigin : ∀ i ∈ F, (origin i).val = U.cover.assign block.a.val i := by
    intro i hi
    have hfull := (drops (origin i).val (origin i).property).Fplus_subset (hdrop i hi).1
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hfull
    obtain ⟨hjA, hjR⟩ := Finset.mem_filter.mp hj
    exact hjR.symm.trans (U.cover.assign_eq_of_le block.a_lt_b.le hb hjA (hFA hi) hji)
  have horiginEq : ∀ i ∈ F, ∀ j ∈ F, physical i = physical j -> origin i = origin j := by
    intro i hi j hj hij
    apply Subtype.ext
    rw [horigin i hi, horigin j hj, restriction.assign block.a.val ha]
    exact Uext.cover.assign_eq_of_le hac hcM (hFA hi) (hFA hj) hij
  have hdpos : 0 < Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val :=
    div_pos (Tube.gridScale_pos hd M _) (Tube.gridScale_pos hd M _)
  have hdsmall : Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val <= 1 :=
    (div_le_one (Tube.gridScale_pos hd M _)).mpr
      (Tube.gridScale_antitone hd hd1 M block.a_lt_b.le)
  let N := trialNearbyParentCountW96 CtwNorm
  have hdegree : ∀ P, ((completeFibreW94 F physical P).image source).card <= N := by
    intro P
    let fibre := completeFibreW94 F physical P
    by_cases hfibre : fibre.Nonempty
    · obtain ⟨i0, hi0⟩ := hfibre
      obtain ⟨hi0F, hi0P⟩ := Finset.mem_filter.mp hi0
      let R := origin i0
      let normal := calls.normalization R.val R.property
      let drop := drops R.val R.property
      let H := fibre.image middle
      have hHdrop : H ⊆ drop.Fplus := by
        intro Q hQ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨hiF, hiP⟩ := Finset.mem_filter.mp hi
        have hR : origin i = R := horiginEq i hiF i0 hi0F (hiP.trans hi0P.symm)
        exact (congrArg (fun r => (drops r.val r.property).Fplus) hR) ▸ (hdrop i hiF).1
      have hlevel : drop.level.val = level.val := congrArg Fin.val (hdrop i0 hi0F).2
      have hparent : ∀ i ∈ fibre, normal.cells.assign drop.level.val (middle i) = P := by
        intro i hi
        obtain ⟨hiF, hiP⟩ := Finset.mem_filter.mp hi
        rw [hlevel]
        exact (actual_normalized_old_parent_thread_w101 U Uext restriction block.a.val block.b.val
          block.a_lt_b hb R.val (actualSecondAmbientW97 selections) normal level.val hl i (hFA hiF)).1.trans hiP
      have hsource : ∀ i ∈ fibre, source i = drop.assignPlus (middle i) := by
        intro i hi
        obtain ⟨hiF, hiP⟩ := Finset.mem_filter.mp hi
        have hR : origin i = R := horiginEq i hiF i0 hi0F (hiP.trans hi0P.symm)
        exact congrFun (congrArg (fun r => (drops r.val r.property).assignPlus) hR) (middle i)
      have hsub : fibre.image source ⊆
          (completeFibreW94 H (normal.cells.assign drop.level.val) P).image drop.assignPlus := by
        intro S hS
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hS
        exact Finset.mem_image.mpr ⟨middle i,
          Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hi, hparent i hi⟩, (hsource i hi).symm⟩
      exact (Finset.card_le_card hsub).trans
        (actual_window_source_parent_degree_w101 hdim normal.cells drop hdpos hdsmall hepsilon
          hCtw normal.ball H hHdrop P)
    · change (fibre.image source).card <= N
      simp only [Finset.not_nonempty_iff_eq_empty.mp hfibre, Finset.image_empty, Finset.card_empty,
        Nat.zero_le]
  have hFne : F.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hmass
    exact lt_irrefl _ hmass
  obtain ⟨i0, hi0⟩ := hFne
  have hnonempty : ((completeFibreW94 F physical (physical i0)).image source).Nonempty :=
    ⟨source i0, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hi0, rfl⟩)⟩
  have hN : 0 < N := (Finset.card_pos.mpr hnonempty).trans_le (hdegree (physical i0))
  obtain ⟨G, hGne, hGF, hpay, hconstant⟩ :=
    exists_weighted_constant_fibre_refinement_w101 F physical source weight N hN hdegree hmass
  refine ⟨G, hGne, hGF, hpay, ?_⟩
  intro i hi j hj hij
  exact ⟨horiginEq i (hGF hi) j (hGF hj) hij, hconstant i hi j hj hij⟩

/-- The actual canonical/working incidence selection, source-parent
selection, and full-canonical conflict colour are combined on one fine family. -/
theorem exists_actual_window_assigned_fine_geometry_w102
    (hdim : Module.finrank Real E = 3)
    (Ccan CbaseTw CbaseCell Cwork Ctw Ccell Lgeom : NNReal)
    (hCbaseTw : 1 <= CbaseTw) (hCtw : 1 <= Ctw) (hLgeom : 1 <= Lgeom) (M : Nat) :
    ∃ (Cdegree : NNReal) (Dgeom : Nat), 1 <= Cdegree ∧ 1 <= Dgeom ∧
      ∀ {p : Params} {xi : Fin (p.N + 1) -> Real} {gamma : Real}
        {iota : Type uI} [DecidableEq iota] {delta : NNReal}
        {B : Finset iota} {V : iota -> ShadedTube delta E}
        (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
        (current : RetainedStateW94 B V) (A : Finset iota)
        (U : CanonicalProfileNetW87 A (fun i => (current.shading i).toTube) M Cwork)
        (Uext : CanonicalProfileNetW87 A (fun i => (current.shading i).toTube) (M * M) Cwork)
        (restriction : VisibleExtendedRestrictionW97 U Uext),
        A ⊆ current.active ->
        SourceRegularizedWorkingTowerW95 U0 CbaseTw CbaseCell ->
        SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        SourceRegularizedWorkingTowerW95 Uext Ctw Ccell ->
      ∀ {BF loss : NNReal} (block : ActualSourceDividingBlockW95 U p BF)
        (selections : ActualSameMassSelectionsW95 block loss)
        {Rnorm Cext Cnorm CtwNorm CcellNorm : NNReal}
        (aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M)
        (calls : ActualEligibleTrialCallsW97 Uext block selections xi gamma
          Rnorm Cext Cnorm CtwNorm CcellNorm aux)
        (drops : ∀ R (hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)),
          WindowDetailedTrialDropW98 (calls.normalization R hR).cells p.ε
            (p.η (block.label.val + 1) / 2) (aux.Ktr block.label)),
        0 < delta -> delta <= 1 -> 0 < p.ε -> 1 <= CtwNorm ->
      ∀ (level : Fin (M + 1)) (F : Finset iota), F ⊆ A ->
      ∀ (origin : iota -> {R // R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)}),
        (∀ i ∈ F,
          U.cover.assign block.b.val i ∈ (drops (origin i).val (origin i).property).Fplus ∧
            (drops (origin i).val (origin i).property).level = level) ->
      ∀ (Z : iota -> ShadedTube delta E), (0 < ∑ i ∈ F, volume (Z i).shade) ->
        Lgeom * Tube.gridScale delta (M * M)
          (quotientGridIndexW97 M block.a.val block.b.val level.val) <= 1 ->
        ∃ G : Finset iota, G.Nonempty ∧ G ⊆ F ∧
          ((Dgeom + 1 : Nat) : ENNReal)⁻¹ *
            ((trialNearbyParentCountW96 CtwNorm : Nat) : ENNReal)⁻¹ * (Cdegree : ENNReal)⁻¹ *
              (∑ i ∈ F, volume (Z i).shade) <= ∑ i ∈ G, volume (Z i).shade ∧
          (∀ i ∈ G, ∀ j ∈ G, U0.cover.assign block.b.val i = U0.cover.assign block.b.val j ->
            U.cover.assign block.b.val i = U.cover.assign block.b.val j ∧
              Uext.cover.assign (quotientGridIndexW97 M block.a.val block.b.val level.val) i =
                Uext.cover.assign (quotientGridIndexW97 M block.a.val block.b.val level.val) j) ∧
          (∀ i ∈ G, ∀ j ∈ G,
            Uext.cover.assign (quotientGridIndexW97 M block.a.val block.b.val level.val) i =
              Uext.cover.assign (quotientGridIndexW97 M block.a.val block.b.val level.val) j ->
            origin i = origin j ∧
              (drops (origin i).val (origin i).property).assignPlus (U.cover.assign block.b.val i) =
                (drops (origin j).val (origin j).property).assignPlus (U.cover.assign block.b.val j)) ∧
          Tube.HasBoundedOverlap (canonicalQNodeFinsetW87 U0 current.active block.b)
            (fun w => U0.cover.tube block.b.val w.val)
            (G.image (Uext.cover.assign (quotientGridIndexW97 M block.a.val block.b.val level.val)))
            (fun P => (Uext.cover.tube (quotientGridIndexW97 M block.a.val block.b.val level.val) P).rescale
              (Lgeom * Tube.gridScale delta (M * M)
                (quotientGridIndexW97 M block.a.val block.b.val level.val))) 1 := by
  obtain ⟨Cdegree, hCdegree, hcanonical⟩ := exists_canonical_assignment_refinement_w101
    (E := E) (M := M) Ccan CbaseTw CbaseCell Cwork Ctw Ccell hCbaseTw hCtw
  obtain ⟨Dgeom, hDgeom, hcolour⟩ :=
    exists_fine_refinement_full_canonical_overlap_w101 (E := E) Ctw Lgeom hCtw hLgeom
  refine ⟨Cdegree, Dgeom, hCdegree, hDgeom, ?_⟩
  intro p xi gamma iota inst delta B V U0 current A U Uext restriction hA reg0 reg regext
    BF loss block selections Rnorm Cext Cnorm CtwNorm CcellNorm aux calls drops hd hd1 heps hCtwNorm
    level F hFA origin hdrop Z hmass hwide
  let c := quotientGridIndexW97 M block.a.val block.b.val level.val
  let physical := Uext.cover.assign c
  have hb : block.b.val <= M := Nat.le_of_lt_succ block.b.isLt
  have hl : level.val <= M := Nat.le_of_lt_succ level.isLt
  have hcb : c <= block.b.val * M := by
    dsimp only [c, quotientGridIndexW97]
    calc
      _ <= block.a.val * M + (block.b.val - block.a.val) * M :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _
      _ = _ := by rw [← Nat.add_mul, Nat.add_sub_of_le block.a_lt_b.le]
  have hbM : block.b.val * M <= M * M := Nat.mul_le_mul_right M hb
  have hcM : c <= M * M := hcb.trans hbM
  have hscale : Tube.gridScale delta M block.b.val <= Tube.gridScale delta (M * M) c :=
    (restriction.radius block.b.val hb).le.trans (Tube.gridScale_antitone hd hd1 (M * M) hcb)
  obtain ⟨F1, hF1ne, hF1F, hpay1, hconstant1⟩ :=
    hcanonical hd hd1 U0 current A U hA reg0 reg block.b F (fun i => volume (Z i).shade) id hFA hmass
  have hmass1 : 0 < ∑ i ∈ F1, volume (Z i).shade :=
    (ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top) hmass.ne').trans_le hpay1
  obtain ⟨F2, hF2ne, hF2F1, hpay2, hconstant2⟩ :=
    exists_actual_window_physical_source_refinement_w101 hdim U Uext restriction block selections
      aux calls drops hd hd1 heps hCtwNorm level F1 (hF1F.trans hFA) origin
      (fun i hi => hdrop i (hF1F hi)) (fun i => volume (Z i).shade) hmass1
  have hmass2 : 0 < ∑ i ∈ F2, volume (Z i).shade :=
    (ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)) hmass1.ne').trans_le hpay2
  have hparents : F2.image physical ⊆ Uext.cover.indexSet c := by
    intro P hP
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
    exact Uext.cover.assign_mem c hcM i (hFA (hF1F (hF2F1 hi)))
  have hline : lineEssentiallyDistinctW94 (F2.image physical) (Uext.cover.tube c) Ctw := by
    intro o v hv
    exact (show (((F2.image physical).filter (fun P => liesInFiveDeltaLineTubeW94
      (Uext.cover.tube c P) o v)).card : NNReal) <=
        (((Uext.cover.indexSet c).filter (fun P => liesInFiveDeltaLineTubeW94
          (Uext.cover.tube c P) o v)).card : NNReal) by
            exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hparents)).trans
      (regext.parent_line_ed c hcM o v hv)
  obtain ⟨G, hGne, hGF2, hpay3, hoverlap⟩ := hcolour hd hd1 U0 current.active block.b
    current.active_subset hscale hwide F2 Z physical (Uext.cover.tube c)
    (fun P hP => regext.parent_ball c hcM P (hparents hP)) hline hmass2
  have hGF1 : G ⊆ F1 := hGF2.trans hF2F1
  refine ⟨G, hGne, hGF1.trans hF1F, ?_, ?_, ?_, hoverlap⟩
  · have h12 := (mul_le_mul_right hpay1
      (((trialNearbyParentCountW96 CtwNorm : Nat) : ENNReal)⁻¹)).trans hpay2
    have h123 := (mul_le_mul_right h12 (((Dgeom + 1 : Nat) : ENNReal)⁻¹)).trans hpay3
    simpa only [mul_assoc] using h123
  · intro i hi j hj hij
    have hworking := hconstant1 i (hGF1 hi) j (hGF1 hj) hij
    change U.cover.assign block.b.val i = U.cover.assign block.b.val j at hworking
    refine ⟨hworking, ?_⟩
    rw [restriction.assign block.b.val hb] at hworking
    exact Uext.cover.assign_eq_of_le hcb hbM (hFA (hF1F (hGF1 hi)))
      (hFA (hF1F (hGF1 hj))) hworking
  · intro i hi j hj hij
    exact hconstant2 i (hGF2 hi) j (hGF2 hj) hij

/-- Canonical parts of the final fine family inherit the stronger density
drop from their single actual source parent, with one fixed transport cost. -/
theorem exists_actual_window_assigned_density_transfer_w102
    (hdim : Module.finrank Real E = 3)
    (CbaseTw Ctw Ccell Rnorm Cext Cnorm CtwNorm CcellNorm : NNReal)
    (hCbaseTw : 1 <= CbaseTw) (hCtw : 1 <= Ctw) (hCcell : 1 <= Ccell)
    (hRnorm : 1 <= Rnorm) (hCext : 1 <= Cext) (hCnorm : 1 <= Cnorm) :
    ∃ Cden : NNReal, 1 <= Cden ∧
      ∀ {p : Params} {xi : Fin (p.N + 1) -> Real} {gamma : Real}
        {iota : Type uI} [DecidableEq iota] {delta : NNReal}
        {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat}
        {Ccan CbaseCell Cwork : NNReal}
        (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
        (current : RetainedStateW94 B V) (A : Finset iota)
        (U : CanonicalProfileNetW87 A (fun i => (current.shading i).toTube) M Cwork)
        (Uext : CanonicalProfileNetW87 A (fun i => (current.shading i).toTube) (M * M) Cwork),
        0 < delta -> delta < 1 -> 1 <= M -> A.Nonempty -> A ⊆ current.active ->
        (∀ i ∈ B, (V i).carrier ⊆ Metric.closedBall 0 1) ->
        SourceRegularizedWorkingTowerW95 U0 CbaseTw CbaseCell ->
        SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        SourceRegularizedWorkingTowerW95 Uext Ctw Ccell ->
        VisibleExtendedRestrictionW97 U Uext ->
        ActualTreeParameterMarginW98 Uext.cover normalizationParameterMarginW98 ->
      ∀ {BF loss : NNReal} (block : ActualSourceDividingBlockW95 U p BF)
        (selections : ActualSameMassSelectionsW95 block loss)
        (aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M)
        (calls : ActualEligibleTrialCallsW97 Uext block selections xi gamma
          Rnorm Cext Cnorm CtwNorm CcellNorm aux)
        (drops : ∀ R (hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)),
          WindowDetailedTrialDropW98 (calls.normalization R hR).cells p.ε
            (p.η (block.label.val + 1) / 2) (aux.Ktr block.label))
        (level : Fin (M + 1)) (G nodeFamily : Finset iota)
        (part : iota -> Finset (CanonicalQNodeW87 U0 current.active block.b)),
        G ⊆ A ->
      ∀ (origin : iota -> {R // R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)}),
        (∀ i ∈ G,
          U.cover.assign block.b.val i ∈ (drops (origin i).val (origin i).property).Fplus ∧
            (drops (origin i).val (origin i).property).level = level) ->
        nodeFamily = G.image (Uext.cover.assign (quotientGridIndexW97 M block.a.val block.b.val level.val)) ->
        (∀ P ∈ nodeFamily, ∀ w ∈ part P, ∃ i ∈ G,
          U0.cover.assign block.b.val i = w.val ∧
            Uext.cover.assign (quotientGridIndexW97 M block.a.val block.b.val level.val) i = P) ->
        (∀ i ∈ G, ∀ j ∈ G,
          Uext.cover.assign (quotientGridIndexW97 M block.a.val block.b.val level.val) i =
            Uext.cover.assign (quotientGridIndexW97 M block.a.val block.b.val level.val) j ->
          origin i = origin j ∧
            (drops (origin i).val (origin i).property).assignPlus (U.cover.assign block.b.val i) =
              (drops (origin j).val (origin j).property).assignPlus (U.cover.assign block.b.val j)) ->
        ∀ P ∈ nodeFamily,
          ∃ R, ∃ hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label),
            (drops R hR).level = level ∧
              Kakeya.maxDensity (part P) (fun w => (U0.cover.tube block.b.val w.val).toConvexSpaceBody) <=
                (Cden : ENNReal) *
                  ((Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val : NNReal) : ENNReal) ^
                    (p.ε * (p.η (block.label.val + 1) / 2) / 2) *
                  allExactTubeNsW87 (actualDescendantsW95 A U.cover.assign block.a.val block.b.val R)
                    (fun Q => ((calls.normalization R hR).normalized Q).toTube)
                    (Tube.gridScale (Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val)
                      M level.val) := by
  obtain ⟨Cden, hCden, htransfer⟩ := exists_actual_canonical_selected_density_comparison_w101
    hdim CbaseTw Ctw Ccell Rnorm Cext Cnorm CtwNorm CcellNorm
      hCbaseTw hCtw hCcell hRnorm hCext hCnorm
  refine ⟨Cden, hCden, ?_⟩
  intro p xi gamma iota inst delta B V M Ccan CbaseCell Cwork U0 current A U Uext
    hd hd1 hM hAne hA hball reg0 reg regext restriction margin BF loss block selections
    aux calls drops level G nodeFamily part hGA origin hdrop hnode hpart hconstant P hP
  obtain ⟨i0, hi0, hi0P⟩ := Finset.mem_image.mp (hnode ▸ hP)
  let R := origin i0
  let drop := drops R.val R.property
  let normal := calls.normalization R.val R.property
  let sourceParent := drop.assignPlus (U.cover.assign block.b.val i0)
  let selected := completeFibreW94 drop.Fplus drop.assignPlus sourceParent
  have hsourceParent : sourceParent ∈ drop.nodes :=
    drop.assignPlus_image ▸ Finset.mem_image_of_mem _ (hdrop i0 hi0).1
  have hselected : selected ⊆ actualDescendantsW95 A U.cover.assign block.a.val block.b.val R.val :=
    (Finset.filter_subset _ _).trans drop.Fplus_subset
  have hwitness : ∀ w ∈ part P, ∃ i ∈ A,
      U0.cover.assign block.b.val i = w.val ∧ U.cover.assign block.b.val i ∈ selected := by
    intro w hw
    obtain ⟨i, hi, hiw, hiP⟩ := hpart P hP w hw
    obtain ⟨hR, hsource⟩ := hconstant i hi i0 hi0 (hiP.trans hi0P.symm)
    have hiDrop : U.cover.assign block.b.val i ∈ drop.Fplus :=
      (congrArg (fun r => (drops r.val r.property).Fplus) hR) ▸ (hdrop i hi).1
    refine ⟨i, hGA hi, hiw, Finset.mem_filter.mpr ⟨hiDrop, ?_⟩⟩
    exact (congrFun (congrArg (fun r => (drops r.val r.property).assignPlus) hR)
      (U.cover.assign block.b.val i)).symm.trans hsource
  have hcompare := htransfer hd hd1 U0 current A U Uext hM hAne hA hball reg0 reg regext
    restriction margin block.a block.b block.a_lt_b R.val (Finset.mem_filter.mp R.property).1
    (actualSecondAmbientW97 selections) normal selected (part P) hselected hwitness
  have hbody : Kakeya.maxDensity selected (fun Q => (normal.normalized Q).toConvexSpaceBody) =
      Kakeya.maxDensity selected (fun Q => (drop.Yplus Q).toConvexSpaceBody) := by
    apply Kakeya.maxDensity_congr
    intro Q hQ
    exact (congrArg Tube.toConvexSpaceBody (drop.same_tube Q (Finset.mem_filter.mp hQ).1)).symm
  rw [hbody] at hcompare
  have hfinal := hcompare.trans (mul_le_mul_right (drop.stronger_per_cell sourceParent hsourceParent)
    (Cden : ENNReal))
  refine ⟨R.val, R.property, (hdrop i0 hi0).2, ?_⟩
  have hlevel : drop.level.val = level.val := congrArg Fin.val (hdrop i0 hi0).2
  simpa only [hlevel, mul_assoc] using hfinal

end

end Kakeya.ml1Boot.TrialRestartW94
