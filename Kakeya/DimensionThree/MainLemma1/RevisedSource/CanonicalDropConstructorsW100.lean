module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceCanonicalTransportW97
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

/-- The canonical shadings and exact support constructed from a positive fine
lift retain the same mass fraction as that lift. -/
theorem exists_canonical_drop_support_and_mass_w100
    {iota : Type uI} [DecidableEq iota] {delta : NNReal} (hd : 0 < delta)
    {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat} {Ccan : NNReal}
    (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
    (current : RetainedStateW94 B V) (q : Fin (M + 1))
    (F G : Finset iota) (Y Z : iota -> ShadedTube delta E)
    (hF : F ⊆ current.active) (hG : G ⊆ F) (hGne : G.Nonempty)
    (hY : ∀ i ∈ F, (Y i).toTube = (current.shading i).toTube)
    (hZ : ∀ i ∈ G, (Z i).toTube = (Y i).toTube ∧ (Z i).shade ⊆ (Y i).shade)
    (hZpos : ∀ i ∈ G, 0 < volume (Z i).shade)
    (r : ENNReal)
    (hret : r * (∑ i ∈ F, volume (Y i).shade) <= ∑ i ∈ G, volume (Z i).shade) :
    ∃ (c : NNReal)
      (W Wplus : CanonicalQNodeW87 U0 current.active q ->
        ShadedTube (Tube.gridScale delta M q.val) E)
      (Fplus : Finset (CanonicalQNodeW87 U0 current.active q)),
      0 < c ∧ Fplus.Nonempty ∧ Fplus ⊆ canonicalQNodeFinsetW87 U0 current.active q ∧
      G.image (U0.cover.assign q.val) = Fplus.image Subtype.val ∧
      (∀ w ∈ Fplus, ∃ i ∈ G, U0.cover.assign q.val i = w.val ∧
        0 < volume (Z i).shade) ∧
      (∀ w, (W w).toTube = U0.cover.tube q.val w.val ∧
        (Wplus w).toTube = U0.cover.tube q.val w.val ∧ (Wplus w).shade ⊆ (W w).shade) ∧
      (∀ w, (W w).shade ⊆
        ⋃ i ∈ completeFibreW94 F (U0.cover.assign q.val) w.val, (Y i).shade) ∧
      (∀ w, (Wplus w).shade ⊆
        ⋃ i ∈ completeFibreW94 G (U0.cover.assign q.val) w.val, (Z i).shade) ∧
      (∀ w, volume (W w).shade = (c : ENNReal) *
        ∑ i ∈ completeFibreW94 F (U0.cover.assign q.val) w.val, volume (Y i).shade) ∧
      (∀ w, volume (Wplus w).shade = (c : ENNReal) *
        ∑ i ∈ completeFibreW94 G (U0.cover.assign q.val) w.val, volume (Z i).shade) ∧
      (∀ w ∈ Fplus, 0 < volume (Wplus w).shade) ∧
      r * (∑ w ∈ canonicalQNodeFinsetW87 U0 current.active q, volume (W w).shade) <=
        ∑ w ∈ Fplus, volume (Wplus w).shade := by
  have hpos : 0 < ∑ i ∈ G, volume (Z i).shade := by
    obtain ⟨i, hi⟩ := hGne
    exact (hZpos i hi).trans_le
      (Finset.single_le_sum (f := fun i => volume (Z i).shade) (fun _ _ => bot_le) hi)
  obtain ⟨c, W, Wplus, hc, htube, hWsub, hWplusSub, hWvol, hWplusVol, hplusPos⟩ :=
    exists_actual_canonical_induced_shadings_w97 hd U0 current q F G Y Z hF hG hY hZ hpos
  let nodes := canonicalQNodeFinsetW87 U0 current.active q
  let Fplus := nodes.filter (fun w => w.val ∈ G.image (U0.cover.assign q.val))
  have hFplus : Fplus ⊆ nodes := Finset.filter_subset _ _
  have hmemNodes : ∀ w : CanonicalQNodeW87 U0 current.active q, w ∈ nodes := by
    intro w
    exact Finset.mem_attach _ _
  have himage : G.image (U0.cover.assign q.val) = Fplus.image Subtype.val := by
    ext w
    constructor
    · intro hw
      have hwcurrent : w ∈ canonicalAncestorFamilyW87 U0 current.active q :=
        Finset.image_mono _ (hG.trans hF) hw
      let v : CanonicalQNodeW87 U0 current.active q := ⟨w, hwcurrent⟩
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hmemNodes v, hw⟩, rfl⟩
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hv).2
  have hsupport : ∀ w ∈ Fplus, ∃ i ∈ G, U0.cover.assign q.val i = w.val ∧
      0 < volume (Z i).shade := by
    intro w hw
    obtain ⟨i, hi, hiw⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hw).2
    exact ⟨i, hi, hiw, hZpos i hi⟩
  have hplusne : Fplus.Nonempty := by
    have hne : (Fplus.image Subtype.val).Nonempty := himage ▸ hGne.image _
    exact Finset.image_nonempty.mp hne
  have htotal (H : Finset iota) (T : iota -> ShadedTube delta E)
      (hH : H ⊆ current.active) :
      (∑ w ∈ nodes, ∑ i ∈ completeFibreW94 H (U0.cover.assign q.val) w.val,
        volume (T i).shade) = ∑ i ∈ H, volume (T i).shade := by
    change (∑ w ∈ (canonicalAncestorFamilyW87 U0 current.active q).attach,
      ∑ i ∈ H.filter (fun i => U0.cover.assign q.val i = w.val), volume (T i).shade) = _
    exact (Finset.sum_attach _ _).trans
      (Finset.sum_fiberwise_of_maps_to
        (fun i hi => Finset.mem_image_of_mem _ (hH hi)) (fun i => volume (T i).shade))
  have htotalW : (∑ w ∈ nodes, volume (W w).shade) =
      (c : ENNReal) * ∑ i ∈ F, volume (Y i).shade := by
    calc
      _ = ∑ w ∈ nodes, (c : ENNReal) *
          ∑ i ∈ completeFibreW94 F (U0.cover.assign q.val) w.val, volume (Y i).shade :=
        Finset.sum_congr rfl (fun w hw => hWvol w)
      _ = _ := by rw [← Finset.mul_sum, htotal F Y hF]
  have htotalPlus : (∑ w ∈ Fplus, volume (Wplus w).shade) =
      (c : ENNReal) * ∑ i ∈ G, volume (Z i).shade := by
    have hfullsum : (∑ w ∈ Fplus, volume (Wplus w).shade) =
        ∑ w ∈ nodes, volume (Wplus w).shade := by
      apply Finset.sum_subset hFplus
      intro w hw hwnot
      rw [hWplusVol]
      have hempty : completeFibreW94 G (U0.cover.assign q.val) w.val = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨hiG, hiw⟩ := Finset.mem_filter.mp hi
        exact hwnot (Finset.mem_filter.mpr ⟨hw, Finset.mem_image.mpr ⟨i, hiG, hiw⟩⟩)
      rw [hempty, Finset.sum_empty, mul_zero]
    rw [hfullsum]
    calc
      _ = ∑ w ∈ nodes, (c : ENNReal) *
          ∑ i ∈ completeFibreW94 G (U0.cover.assign q.val) w.val, volume (Z i).shade :=
        Finset.sum_congr rfl (fun w hw => hWplusVol w)
      _ = _ := by rw [← Finset.mul_sum, htotal G Z (hG.trans hF)]
  refine ⟨c, W, Wplus, Fplus, hc, hplusne, hFplus, himage, hsupport, htube,
    hWsub, hWplusSub, hWvol, hWplusVol, ?_, ?_⟩
  · intro w hw
    obtain ⟨i, hi, hiw, hzi⟩ := hsupport w hw
    rw [hWplusVol]
    apply ENNReal.mul_pos (ENNReal.coe_pos.mpr hc).ne'
    exact (hzi.trans_le (Finset.single_le_sum (f := fun i => volume (Z i).shade) (fun _ _ => bot_le)
      (Finset.mem_filter.mpr ⟨hi, hiw⟩))).ne'
  · rw [htotalW, htotalPlus, mul_left_comm]
    exact mul_le_mul_left' hret _

/-- A synchronized fine assignment descends to a disjoint partition of the
canonical support, with every part retaining its actual fine witnesses. -/
theorem exists_canonical_drop_partition_w100
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat} {Ccan : NNReal}
    (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
    (current : RetainedStateW94 B V) (q : Fin (M + 1))
    (G : Finset iota) (hGne : G.Nonempty)
    (Fplus : Finset (CanonicalQNodeW87 U0 current.active q))
    (himage : G.image (U0.cover.assign q.val) = Fplus.image Subtype.val)
    (parent : iota -> iota)
    (hconsistent : ∀ i ∈ G, ∀ j ∈ G, U0.cover.assign q.val i = U0.cover.assign q.val j ->
      parent i = parent j) :
    ∃ (nodeFamily : Finset iota)
      (part : iota -> Finset (CanonicalQNodeW87 U0 current.active q)),
      nodeFamily = G.image parent ∧ nodeFamily.Nonempty ∧
      Fplus = nodeFamily.biUnion part ∧
      (nodeFamily : Set iota).Pairwise (fun P Q => Disjoint (part P) (part Q)) ∧
      (∀ P ∈ nodeFamily, part P ⊆ Fplus ∧ (part P).Nonempty) ∧
      (∀ P ∈ nodeFamily, ∀ w ∈ part P,
        (∃ i ∈ G, U0.cover.assign q.val i = w.val ∧ parent i = P) ∧
        (∀ i ∈ G, U0.cover.assign q.val i = w.val -> parent i = P)) := by
  have hfine : ∀ w ∈ Fplus, ∃ i ∈ G, U0.cover.assign q.val i = w.val := by
    intro w hw
    have h := Finset.mem_image_of_mem Subtype.val hw
    rw [← himage] at h
    exact Finset.mem_image.mp h
  choose representative representativeMem representativeEq using hfine
  obtain ⟨default, hdefault⟩ := hGne
  let assignment := fun w : CanonicalQNodeW87 U0 current.active q =>
    if hw : w ∈ Fplus then parent (representative w hw) else parent default
  let part := fun P => Fplus.filter (fun w => assignment w = P)
  let nodeFamily := G.image parent
  have hrepresentative : ∀ w ∈ Fplus, ∀ i ∈ G,
      U0.cover.assign q.val i = w.val -> parent i = assignment w := by
    intro w hw i hi hiw
    dsimp only [assignment]
    rw [dif_pos hw]
    exact hconsistent i hi (representative w hw) (representativeMem w hw)
      (hiw.trans (representativeEq w hw).symm)
  have hassignment : ∀ w ∈ Fplus, assignment w ∈ nodeFamily := by
    intro w hw
    dsimp only [assignment]
    rw [dif_pos hw]
    exact Finset.mem_image_of_mem parent (representativeMem w hw)
  have hcover : Fplus = nodeFamily.biUnion part := by
    ext w
    constructor
    · intro hw
      exact Finset.mem_biUnion.mpr ⟨assignment w, hassignment w hw,
        Finset.mem_filter.mpr ⟨hw, rfl⟩⟩
    · intro hw
      obtain ⟨P, hP, hwP⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp hwP).1
  refine ⟨nodeFamily, part, rfl, Finset.Nonempty.image ⟨default, hdefault⟩ _, hcover, ?_, ?_, ?_⟩
  · intro P hP Q hQ hPQ
    apply Finset.disjoint_left.mpr
    intro w hwP hwQ
    exact hPQ ((Finset.mem_filter.mp hwP).2.symm.trans (Finset.mem_filter.mp hwQ).2)
  · intro P hP
    refine ⟨Finset.filter_subset _ _, ?_⟩
    obtain ⟨i, hi, hiP⟩ := Finset.mem_image.mp hP
    have hwi : U0.cover.assign q.val i ∈ Fplus.image Subtype.val :=
      himage ▸ Finset.mem_image_of_mem _ hi
    obtain ⟨w, hw, hwi⟩ := Finset.mem_image.mp hwi
    exact ⟨w, Finset.mem_filter.mpr ⟨hw,
      (hrepresentative w hw i hi hwi.symm).symm.trans hiP⟩⟩
  · intro P hP w hwP
    obtain ⟨hw, hwP⟩ := Finset.mem_filter.mp hwP
    refine ⟨⟨representative w hw, representativeMem w hw, representativeEq w hw, ?_⟩, ?_⟩
    · exact (hrepresentative w hw _ (representativeMem w hw) (representativeEq w hw)).trans hwP
    · intro i hi hiw
      exact (hrepresentative w hw i hi hiw).trans hwP

/-- Actual window-trial drops construct positive fine and canonical shadings
on the same supports, retaining the affine provenance and proportional masses. -/
theorem exists_actual_window_drop_canonical_shadings_w100
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat}
    {Ccan Cwork Ctw Ccell : NNReal}
    (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
    (current : RetainedStateW94 B V) (A : Finset iota)
    (U : CanonicalProfileNetW87 A (fun i => (current.shading i).toTube) M Cwork)
    (Uext : CanonicalProfileNetW87 A (fun i => (current.shading i).toTube) (M * M) Cwork)
    (hd : 0 < delta) (hd1 : delta < 1) (hM : 1 <= M) (hA : A.Nonempty)
    (hAcurrent : A ⊆ current.active)
    (reg : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
    {p : Params} {BF loss : NNReal} (hepsilon : 0 < p.ε)
    (block : ActualSourceDividingBlockW95 U p BF)
    (selections : ActualSameMassSelectionsW95 block loss)
    (xi : Fin (p.N + 1) -> Real) (gamma : Real)
    (Rnorm Cext Cnorm CtwNorm CcellNorm : NNReal)
    (aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M)
    (calls : ActualEligibleTrialCallsW97 Uext block selections xi gamma
      Rnorm Cext Cnorm CtwNorm CcellNorm aux)
    (drops : ∀ R (hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)),
      WindowDetailedTrialDropW98 (calls.normalization R hR).cells p.ε
        (p.η (block.label.val + 1) / 2) (aux.Ktr block.label))
    (hpos : 0 < ∑ i ∈ selections.fineFamily, volume (selections.fineShading i).shade) :
    let d := Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val
    let retained := (1 / 2 : ENNReal) * trialRetainedFractionW94 d (aux.Ktr block.label)
    ∃ (G : Finset iota) (Z : iota -> ShadedTube delta E)
      (Zplus : iota -> ShadedTube (Tube.gridScale delta M block.b.val) E)
      (c : NNReal)
      (W Wplus : CanonicalQNodeW87 U0 current.active block.b ->
        ShadedTube (Tube.gridScale delta M block.b.val) E)
      (Fplus : Finset (CanonicalQNodeW87 U0 current.active block.b)),
      G.Nonempty ∧ G ⊆ selections.fineFamily ∧
      (∀ i ∈ G, (Z i).toTube = (current.shading i).toTube ∧
        (Z i).shade ⊆ (selections.fineShading i).shade ∧ 0 < volume (Z i).shade) ∧
      G.image (U.cover.assign block.b.val) ⊆ selections.secondFamily ∧
      (∀ Q ∈ G.image (U.cover.assign block.b.val),
        (Zplus Q).toTube = U.cover.tube block.b.val Q ∧
        (Zplus Q).shade ⊆ (selections.secondShading Q).shade ∧
        ∃ R, ∃ hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label),
          Q ∈ (drops R hR).Fplus ∧
          (Zplus Q).shade ⊆ ((U.cover.tube block.a.val R).rescaleMap (Rnorm : Real)) ⁻¹'
            ((drops R hR).Yplus Q).shade) ∧
      (∀ Q ∈ G.image (U.cover.assign block.b.val),
        (∑ i ∈ completeFibreW94 G (U.cover.assign block.b.val) Q, volume (Z i).shade) =
          (selections.commonMass : ENNReal)⁻¹ * volume (Zplus Q).shade) ∧
      retained * (∑ i ∈ selections.fineFamily, volume (selections.fineShading i).shade) <=
        ∑ i ∈ G, volume (Z i).shade ∧
      0 < c ∧ Fplus.Nonempty ∧ Fplus ⊆ canonicalQNodeFinsetW87 U0 current.active block.b ∧
      G.image (U0.cover.assign block.b.val) = Fplus.image Subtype.val ∧
      (∀ w ∈ Fplus, ∃ i ∈ G, U0.cover.assign block.b.val i = w.val ∧ 0 < volume (Z i).shade) ∧
      (∀ w, (W w).toTube = U0.cover.tube block.b.val w.val ∧
        (Wplus w).toTube = U0.cover.tube block.b.val w.val ∧ (Wplus w).shade ⊆ (W w).shade) ∧
      (∀ w, (W w).shade ⊆
        ⋃ i ∈ completeFibreW94 selections.fineFamily (U0.cover.assign block.b.val) w.val,
          (selections.fineShading i).shade) ∧
      (∀ w, (Wplus w).shade ⊆
        ⋃ i ∈ completeFibreW94 G (U0.cover.assign block.b.val) w.val, (Z i).shade) ∧
      (∀ w, volume (W w).shade = (c : ENNReal) *
        ∑ i ∈ completeFibreW94 selections.fineFamily (U0.cover.assign block.b.val) w.val,
          volume (selections.fineShading i).shade) ∧
      (∀ w, volume (Wplus w).shade = (c : ENNReal) *
        ∑ i ∈ completeFibreW94 G (U0.cover.assign block.b.val) w.val, volume (Z i).shade) ∧
      (∀ w ∈ Fplus, 0 < volume (Wplus w).shade) ∧
      retained * (∑ w ∈ canonicalQNodeFinsetW87 U0 current.active block.b, volume (W w).shade) <=
        ∑ w ∈ Fplus, volume (Wplus w).shade := by
  dsimp only
  let d := Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val
  let retained := (1 / 2 : ENNReal) * trialRetainedFractionW94 d (aux.Ktr block.label)
  let ordinary := fun R hR => (drops R hR).toDetailedTrialDropW94
  obtain ⟨middle0, F0, Z0, Y0, hmiddle0, hmiddleSub, hZ0, hAll, hOrigin,
    hF0eq, hF0ne, hF0sub, hF0image, hY0, hF0mass, hret0⟩ :=
    exists_actual_trial_drop_fine_lift_w97 Uext block selections xi gamma
      Rnorm Cext Cnorm CtwNorm CcellNorm aux calls ordinary hd hd1 hM hA reg hpos
  let G := F0.filter (fun i => 0 < volume (Y0 i).shade)
  have hGF0 : G ⊆ F0 := Finset.filter_subset _ _
  have hGsub : G ⊆ selections.fineFamily := hGF0.trans hF0sub
  have hsum : (∑ i ∈ G, volume (Y0 i).shade) = ∑ i ∈ F0, volume (Y0 i).shade := by
    apply Finset.sum_subset hGF0
    intro i hi hin
    apply le_antisymm _ bot_le
    exact le_of_not_gt (fun h => hin (Finset.mem_filter.mpr ⟨hi, h⟩))
  have hretG : retained * (∑ i ∈ selections.fineFamily, volume (selections.fineShading i).shade) <=
      ∑ i ∈ G, volume (Y0 i).shade := by
    rw [hsum]
    exact hret0
  have hdpos : 0 < d := div_pos (Tube.gridScale_pos hd M _) (Tube.gridScale_pos hd M _)
  have hdsmall : d < 1 := by
    apply block.block_long.trans_lt
    simpa only [NNReal.one_rpow] using NNReal.rpow_lt_rpow hd1 hepsilon
  have hlog : 0 <= Real.log (1 / (d : Real)) :=
    Real.log_nonneg ((le_div_iff₀ (show (0 : Real) < d from hdpos)).mpr
      (by simpa only [one_mul] using (show (d : Real) <= 1 from hdsmall.le)))
  have hretainedPos : 0 < retained := ENNReal.mul_pos (by norm_num)
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)).ne'
  have hGmass : 0 < ∑ i ∈ G, volume (Y0 i).shade :=
    (ENNReal.mul_pos hretainedPos.ne' hpos.ne').trans_le hretG
  have hGne : G.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at hGmass
    exact lt_irrefl _ hGmass
  have hselectedCurrent : selections.fineFamily ⊆ current.active :=
    (selections.fine_subset.trans selections.first.child_subset).trans hAcurrent
  have hYsub : ∀ i ∈ G,
      (Y0 i).toTube = (selections.fineShading i).toTube ∧
      (Y0 i).shade ⊆ (selections.fineShading i).shade := fun i hi => hY0 i (hGF0 hi)
  have hYpos : ∀ i ∈ G, 0 < volume (Y0 i).shade := fun i hi => (Finset.mem_filter.mp hi).2
  obtain ⟨c, W, Wplus, Fplus, hc, hFplusNe, hFplusSub, hcanonicalImage,
    hcanonicalSupport, hWtubes, hWsub, hWplusSub, hWvol, hWplusVol, hWplusPos, hWret⟩ :=
    exists_canonical_drop_support_and_mass_w100 hd U0 current block.b
      selections.fineFamily G selections.fineShading Y0 hselectedCurrent hGsub hGne
      selections.fine_same_tube hYsub hYpos retained hretG
  have hmiddle : G.image (U.cover.assign block.b.val) ⊆ middle0 := by
    rw [← hF0image]
    exact Finset.image_subset_image hGF0
  refine ⟨G, Y0, Z0, c, W, Wplus, Fplus, hGne, hGsub, ?_,
    hmiddle.trans hmiddleSub, ?_, ?_, hretG, hc, hFplusNe, hFplusSub, hcanonicalImage,
    hcanonicalSupport, hWtubes, hWsub, hWplusSub, hWvol, hWplusVol, hWplusPos, hWret⟩
  · intro i hi
    exact ⟨(hYsub i hi).1.trans (selections.fine_same_tube i (hGsub hi)),
      (hYsub i hi).2, hYpos i hi⟩
  · intro Q hQ
    obtain ⟨R, hR, hQD, hQpos, hQvol⟩ := hOrigin Q (hmiddle hQ)
    refine ⟨(hZ0 Q (hmiddle hQ)).1, (hZ0 Q (hmiddle hQ)).2, R, hR, hQD, ?_⟩
    rw [(hAll R hR Q hQD hQpos).2]
    exact Set.inter_subset_right
  · intro Q hQ
    rw [← hF0mass Q (hmiddle hQ)]
    apply Finset.sum_subset (Finset.filter_subset_filter _ hGF0)
    intro i hi hin
    obtain ⟨hi0, hiQ⟩ := Finset.mem_filter.mp hi
    apply le_antisymm _ bot_le
    apply le_of_not_gt
    intro hipos
    exact hin (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hi0, hipos⟩, hiQ⟩)

/-- Canonical parts sharing actual fine members with a threaded parent lie
inside its fixed-radius enlargement, including the full finite tube caps. -/
theorem canonical_drop_part_parent_containment_w100
    {iota : Type uI} [DecidableEq iota] {delta sigma : NNReal}
    {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat} {Ccan : NNReal}
    (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
    (current : RetainedStateW94 B V) (q : Fin (M + 1))
    (hd : 0 < delta) (hd1 : delta <= 1) (hM : 1 <= M)
    (hscale : Tube.gridScale delta M q.val <= sigma)
    (G parents : Finset iota) (hG : G ⊆ current.active)
    (parent : iota -> iota) (parentTube : iota -> Tube sigma E)
    (hparent : ∀ i ∈ G,
      (current.shading i).toConvexSpaceBody <= (parentTube (parent i)).toConvexSpaceBody)
    (part : iota -> Finset (CanonicalQNodeW87 U0 current.active q))
    (hpart : ∀ P ∈ parents, ∀ w ∈ part P,
      ∃ i ∈ G, U0.cover.assign q.val i = w.val ∧ parent i = P)
    (Wplus : CanonicalQNodeW87 U0 current.active q -> ShadedTube (Tube.gridScale delta M q.val) E)
    (hWplus : ∀ P ∈ parents, ∀ w ∈ part P, (Wplus w).toTube = U0.cover.tube q.val w.val) :
    ∀ P ∈ parents, ∀ w ∈ part P,
      (Wplus w).toConvexSpaceBody <= ((parentTube P).rescale (5 * sigma)).toConvexSpaceBody := by
  have hdeltaTau : delta <= Tube.gridScale delta M q.val := by
    simpa only [Tube.gridScale_self delta hM] using
      Tube.gridScale_antitone hd hd1 M (Nat.le_of_lt_succ q.isLt)
  intro P hP w hw
  obtain ⟨i, hi, hiw, hiP⟩ := hpart P hP w hw
  have hfine : (current.shading i).toConvexSpaceBody <=
      (U0.cover.tube q.val w.val).toConvexSpaceBody := by
    rw [show (current.shading i).toConvexSpaceBody = (V i).toConvexSpaceBody from
      congrArg Tube.toConvexSpaceBody (current.same_tube i (hG hi))]
    exact hiw ▸ U0.cover.le_tube_assign q.val (Nat.le_of_lt_succ q.isLt) i
      (current.active_subset (hG hi))
  have hwide := Tube.le_rescale_of_subset (current.shading i).toTube
    (U0.cover.tube q.val w.val) hfine
  have hthicken := Tube.rescale_le_rescale_of_body_le (current.shading i).toTube
    (parentTube P)
    (show delta <= 4 * Tube.gridScale delta M q.val from hdeltaTau.trans (by nlinarith))
    (show sigma + 4 * Tube.gridScale delta M q.val <= 5 * sigma by nlinarith)
    (by simpa only [hiP] using hparent i hi)
  rw [show (Wplus w).toConvexSpaceBody = (U0.cover.tube q.val w.val).toConvexSpaceBody from
    congrArg Tube.toConvexSpaceBody (hWplus P hP w hw)]
  exact hwide.trans hthicken

end

end Kakeya.ml1Boot.TrialRestartW94
