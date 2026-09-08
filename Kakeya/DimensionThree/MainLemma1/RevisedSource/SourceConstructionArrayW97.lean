module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionDefinitionsW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualWorkingTowerW96
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.CoarseNodePrefixW112
public import Kakeya.MultiScaleSubmult

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

def actualRelativeCFArrayW97
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan : NNReal}
    (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan) (k l : Nat) : ENNReal :=
  (U.cover.indexSet k).sup (actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l)

/-- A1: exact active-node ancestor fibres, never geometric nodesUnder. -/
theorem actual_descendants_partition_three_levels_w97
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan Ctw Ccell : NNReal}
    (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
    (reg : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
    (k l m : Nat) (hkl : k < l) (hlm : l < m) (hm : m <= M)
    (R : iota) (hR : R ∈ U.cover.indexSet k) :
    let p := Kakeya.ML2Reduction.coarseNode U.cover.toChain l m
    let Qkl := actualDescendantsW95 A U.cover.assign k l R
    let Qkm := actualDescendantsW95 A U.cover.assign k m R
    Qkm.image p = Qkl ∧
      (∀ S ∈ Qkl, completeFibreW94 Qkm p S = actualDescendantsW95 A U.cover.assign l m S) ∧
      (Qkl : Set iota).Pairwise (fun S T =>
        Disjoint (actualDescendantsW95 A U.cover.assign l m S)
          (actualDescendantsW95 A U.cover.assign l m T)) ∧
      Qkm = Qkl.biUnion (actualDescendantsW95 A U.cover.assign l m) ∧
      (Qkl.card : NNReal) * reg.countBand l m <= (Qkm.card : NNReal) ∧
      (Qkm.card : NNReal) < 2 * (Qkl.card : NNReal) * reg.countBand l m := by
  have hdescendant_partition {delta : NNReal}
      {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E)
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (k l m : Nat) (hkl : k < l) (hlm : l < m) (hm : m <= M) :
      ∃ parent : iota -> iota,
        (∀ i ∈ A, parent (U.cover.assign m i) = U.cover.assign l i) ∧
        ∀ R ∈ U.cover.indexSet k,
          (actualDescendantsW95 A U.cover.assign k m R).image parent =
            actualDescendantsW95 A U.cover.assign k l R ∧
          (∀ Q ∈ actualDescendantsW95 A U.cover.assign k l R,
            (actualDescendantsW95 A U.cover.assign k m R).filter (fun W => parent W = Q) =
              actualDescendantsW95 A U.cover.assign l m Q) ∧
          ((actualDescendantsW95 A U.cover.assign k l R).card : NNReal) * hregular.countBand l m <=
            ((actualDescendantsW95 A U.cover.assign k m R).card : NNReal) ∧
          ((actualDescendantsW95 A U.cover.assign k m R).card : NNReal) <
            2 * ((actualDescendantsW95 A U.cover.assign k l R).card : NNReal) * hregular.countBand l m := by
    let parent : iota -> iota := fun Q => if hQ : Q ∈ A.image (U.cover.assign m) then
      U.cover.assign l (Finset.mem_image.mp hQ).choose else Q
    have hparent : ∀ i ∈ A, parent (U.cover.assign m i) = U.cover.assign l i := by
      intro i hi
      have hj : U.cover.assign m i ∈ A.image (U.cover.assign m) := Finset.mem_image.mpr ⟨i, hi, rfl⟩
      dsimp only [parent]
      rw [dif_pos hj]
      exact U.cover.assign_eq_of_le hlm.le hm
        (Finset.mem_image.mp hj).choose_spec.1 hi (Finset.mem_image.mp hj).choose_spec.2
    refine ⟨parent, hparent, ?_⟩
    intro R hR
    let Dkm := actualDescendantsW95 A U.cover.assign k m R
    let Dkl := actualDescendantsW95 A U.cover.assign k l R
    let Dlm := actualDescendantsW95 A U.cover.assign l m
    have himage : Dkm.image parent = Dkl := by
      ext Q
      constructor
      · intro hQ
        obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        rw [hparent i hiA]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩
      · intro hQ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_image.mpr ⟨U.cover.assign m i,
          Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩, hparent i hiA⟩
    have hfibre : ∀ Q ∈ Dkl, Dkm.filter (fun W => parent W = Q) = Dlm Q := by
      intro Q hQ
      obtain ⟨i0, hi0, hi0Q⟩ := Finset.mem_image.mp hQ
      obtain ⟨hi0A, hi0R⟩ := Finset.mem_filter.mp hi0
      ext W
      constructor
      · intro hW
        obtain ⟨hW, hWQ⟩ := Finset.mem_filter.mp hW
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        have hiQ : U.cover.assign l i = Q := (hparent i hiA).symm.trans hWQ
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiQ⟩, rfl⟩
      · intro hW
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
        obtain ⟨hiA, hiQ⟩ := Finset.mem_filter.mp hi
        have hiR : U.cover.assign k i = R :=
          (U.cover.assign_eq_of_le hkl.le (by omega) hiA hi0A (hiQ.trans hi0Q.symm)).trans hi0R
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩,
            (hparent i hiA).trans hiQ⟩
    have hQmem : ∀ Q ∈ Dkl, Q ∈ U.cover.indexSet l := by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      exact U.cover.assign_mem l (by omega) i (Finset.mem_filter.mp hi).1
    have hsum : (Dkm.card : NNReal) = ∑ Q ∈ Dkl, ((Dlm Q).card : NNReal) := by
      have hmaps : ∀ W ∈ Dkm, parent W ∈ Dkl := by
        intro W hW
        rw [← himage]
        exact Finset.mem_image.mpr ⟨W, hW, rfl⟩
      calc
        (Dkm.card : NNReal) = ∑ Q ∈ Dkl, ((Dkm.filter (fun W => parent W = Q)).card : NNReal) := by
          simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
            (Finset.sum_fiberwise_of_maps_to hmaps (fun _ => (1 : NNReal))).symm
        _ = ∑ Q ∈ Dkl, ((Dlm Q).card : NNReal) := Finset.sum_congr rfl (fun Q hQ => by rw [hfibre Q hQ])
    have hDkl : Dkl.Nonempty := by
      have hRimage : R ∈ A.image (U.cover.assign k) := (hregular.surjective k (by omega)) ▸ hR
      obtain ⟨i, hi, hiR⟩ := Finset.mem_image.mp hRimage
      exact ⟨U.cover.assign l i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hiR⟩, rfl⟩⟩
    refine ⟨himage, hfibre, ?_, ?_⟩
    · calc
        (Dkl.card : NNReal) * hregular.countBand l m = ∑ Q ∈ Dkl, hregular.countBand l m := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ <= ∑ Q ∈ Dkl, ((Dlm Q).card : NNReal) := Finset.sum_le_sum
          (fun Q hQ => hregular.count_lower l m hlm hm Q (hQmem Q hQ))
        _ = (Dkm.card : NNReal) := hsum.symm
    · calc
        (Dkm.card : NNReal) = ∑ Q ∈ Dkl, ((Dlm Q).card : NNReal) := hsum
        _ < ∑ Q ∈ Dkl, 2 * hregular.countBand l m := by
          apply Finset.sum_lt_sum
          · exact fun Q hQ => (hregular.count_upper l m hlm hm Q (hQmem Q hQ)).le
          · obtain ⟨Q, hQ⟩ := hDkl
            exact ⟨Q, hQ, hregular.count_upper l m hlm hm Q (hQmem Q hQ)⟩
        _ = 2 * (Dkl.card : NNReal) * hregular.countBand l m := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  obtain ⟨parent, hparent, hpartition⟩ := hdescendant_partition A Y U reg k l m hkl hlm hm
  obtain ⟨himage, hfibre, hlower, hupper⟩ := hpartition R hR
  let p := Kakeya.ML2Reduction.coarseNode U.cover.toChain l m
  let Qkl := actualDescendantsW95 A U.cover.assign k l R
  let Qkm := actualDescendantsW95 A U.cover.assign k m R
  have hp_assign : ∀ i ∈ A, p (U.cover.assign m i) = U.cover.assign l i := by
    intro i hi
    have hclass : (Tube.coverClass A (U.cover.toChain.assign m) (U.cover.assign m i)).Nonempty := by
      exact ⟨i, by
        simpa only [Tube.coverClass, Finset.mem_filter] using
          (show i ∈ A ∧ U.cover.toChain.assign m i = U.cover.assign m i from ⟨hi, rfl⟩)⟩
    change Kakeya.ML2Reduction.coarseNode U.cover.toChain l m (U.cover.assign m i) = _
    rw [Kakeya.ML2Reduction.coarseNode, dif_pos hclass]
    have hmem := hclass.choose_spec
    simp only [Tube.coverClass, Finset.mem_filter] at hmem
    exact U.cover.assign_eq_of_le hlm.le hm hmem.1 hi hmem.2
  have hparent_eq : ∀ W ∈ Qkm, parent W = p W := by
    intro W hW
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
    have hiA := (Finset.mem_filter.mp hi).1
    exact (hparent i hiA).trans (hp_assign i hiA).symm
  have himage' : Qkm.image p = Qkl := by
    exact (Finset.image_congr (fun W hW => (hparent_eq W hW).symm)).trans himage
  have hfibre' : ∀ S ∈ Qkl, completeFibreW94 Qkm p S =
      actualDescendantsW95 A U.cover.assign l m S := by
    intro S hS
    calc
      completeFibreW94 Qkm p S = Qkm.filter (fun W => parent W = S) := by
        ext W
        simp only [completeFibreW94, Finset.mem_filter]
        constructor
        · rintro ⟨hW, hWS⟩
          exact ⟨hW, (hparent_eq W hW).trans hWS⟩
        · rintro ⟨hW, hWS⟩
          exact ⟨hW, (hparent_eq W hW).symm.trans hWS⟩
      _ = _ := hfibre S hS
  refine ⟨himage', hfibre', ?_, ?_, hlower, hupper⟩
  · intro S hS T hT hST
    apply Finset.disjoint_left.mpr
    intro W hWS hWT
    rw [← hfibre' S hS] at hWS
    rw [← hfibre' T hT] at hWT
    exact hST ((Finset.mem_filter.mp hWS).2.symm.trans (Finset.mem_filter.mp hWT).2)
  · ext W
    constructor
    · intro hW
      have hpW : p W ∈ Qkl := himage' ▸ Finset.mem_image_of_mem p hW
      apply Finset.mem_biUnion.mpr
      refine ⟨p W, hpW, ?_⟩
      rw [← hfibre' (p W) hpW]
      exact Finset.mem_filter.mpr ⟨hW, rfl⟩
    · intro hW
      obtain ⟨S, hS, hWS⟩ := Finset.mem_biUnion.mp hW
      rw [← hfibre' S hS] at hWS
      exact (Finset.mem_filter.mp hWS).1

/-- A2 uses the lower actual-family two-scale donor, not nodesUnder. -/
theorem actual_relative_cf_composition_w97 :
    ∃ C : NNReal, 1 <= C ∧
      ∀ {iota : Type uI} [DecidableEq iota] {delta : NNReal}, 0 < delta -> delta <= 1 ->
      ∀ {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan Ctw Ccell : NNReal}
        (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan),
        A.Nonempty -> SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        (∀ i ∈ A, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        ∀ k l m : Nat, k < l -> l < m -> m <= M ->
          4 * Tube.gridScale delta M m <= Tube.gridScale delta M l ->
          (∀ R ∈ U.cover.indexSet k,
            actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k m R <=
              2 * (C : ENNReal) ^ (2 : Nat) * actualRelativeCFArrayW97 U k l *
                actualRelativeCFArrayW97 U l m) ∧
          actualRelativeCFArrayW97 U k m <=
            2 * (C : ENNReal) ^ (2 : Nat) * actualRelativeCFArrayW97 U k l *
              actualRelativeCFArrayW97 U l m := by
  obtain ⟨Ctwo, hCtwo, htwo⟩ := Kakeya.MultiScaleSubmult.maxDensity_le_two_fibreDeltaMax
    (E := E) 5 (by norm_num) 1 one_pos
  let C : NNReal := max 1 (Real.toNNReal Ctwo)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro iota inst delta hd hd1 A Y M Ccan Ctw Ccell U hA hregular hball k l m hkl hlm hm hgap
  have hdescendant_partition {delta : NNReal}
      {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E)
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (k l m : Nat) (hkl : k < l) (hlm : l < m) (hm : m <= M) :
      ∃ parent : iota -> iota,
        (∀ i ∈ A, parent (U.cover.assign m i) = U.cover.assign l i) ∧
        ∀ R ∈ U.cover.indexSet k,
          (actualDescendantsW95 A U.cover.assign k m R).image parent =
            actualDescendantsW95 A U.cover.assign k l R ∧
          (∀ Q ∈ actualDescendantsW95 A U.cover.assign k l R,
            (actualDescendantsW95 A U.cover.assign k m R).filter (fun W => parent W = Q) =
              actualDescendantsW95 A U.cover.assign l m Q) ∧
          ((actualDescendantsW95 A U.cover.assign k l R).card : NNReal) * hregular.countBand l m <=
            ((actualDescendantsW95 A U.cover.assign k m R).card : NNReal) ∧
          ((actualDescendantsW95 A U.cover.assign k m R).card : NNReal) <
            2 * ((actualDescendantsW95 A U.cover.assign k l R).card : NNReal) * hregular.countBand l m := by
    let parent : iota -> iota := fun Q => if hQ : Q ∈ A.image (U.cover.assign m) then
      U.cover.assign l (Finset.mem_image.mp hQ).choose else Q
    have hparent : ∀ i ∈ A, parent (U.cover.assign m i) = U.cover.assign l i := by
      intro i hi
      have hj : U.cover.assign m i ∈ A.image (U.cover.assign m) := Finset.mem_image.mpr ⟨i, hi, rfl⟩
      dsimp only [parent]
      rw [dif_pos hj]
      exact U.cover.assign_eq_of_le hlm.le hm
        (Finset.mem_image.mp hj).choose_spec.1 hi (Finset.mem_image.mp hj).choose_spec.2
    refine ⟨parent, hparent, ?_⟩
    intro R hR
    let Dkm := actualDescendantsW95 A U.cover.assign k m R
    let Dkl := actualDescendantsW95 A U.cover.assign k l R
    let Dlm := actualDescendantsW95 A U.cover.assign l m
    have himage : Dkm.image parent = Dkl := by
      ext Q
      constructor
      · intro hQ
        obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        rw [hparent i hiA]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩
      · intro hQ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_image.mpr ⟨U.cover.assign m i,
          Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩, hparent i hiA⟩
    have hfibre : ∀ Q ∈ Dkl, Dkm.filter (fun W => parent W = Q) = Dlm Q := by
      intro Q hQ
      obtain ⟨i0, hi0, hi0Q⟩ := Finset.mem_image.mp hQ
      obtain ⟨hi0A, hi0R⟩ := Finset.mem_filter.mp hi0
      ext W
      constructor
      · intro hW
        obtain ⟨hW, hWQ⟩ := Finset.mem_filter.mp hW
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        have hiQ : U.cover.assign l i = Q := (hparent i hiA).symm.trans hWQ
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiQ⟩, rfl⟩
      · intro hW
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
        obtain ⟨hiA, hiQ⟩ := Finset.mem_filter.mp hi
        have hiR : U.cover.assign k i = R :=
          (U.cover.assign_eq_of_le hkl.le (by omega) hiA hi0A (hiQ.trans hi0Q.symm)).trans hi0R
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩,
            (hparent i hiA).trans hiQ⟩
    have hQmem : ∀ Q ∈ Dkl, Q ∈ U.cover.indexSet l := by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      exact U.cover.assign_mem l (by omega) i (Finset.mem_filter.mp hi).1
    have hsum : (Dkm.card : NNReal) = ∑ Q ∈ Dkl, ((Dlm Q).card : NNReal) := by
      have hmaps : ∀ W ∈ Dkm, parent W ∈ Dkl := by
        intro W hW
        rw [← himage]
        exact Finset.mem_image.mpr ⟨W, hW, rfl⟩
      calc
        (Dkm.card : NNReal) = ∑ Q ∈ Dkl, ((Dkm.filter (fun W => parent W = Q)).card : NNReal) := by
          simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
            (Finset.sum_fiberwise_of_maps_to hmaps (fun _ => (1 : NNReal))).symm
        _ = ∑ Q ∈ Dkl, ((Dlm Q).card : NNReal) := Finset.sum_congr rfl (fun Q hQ => by rw [hfibre Q hQ])
    have hDkl : Dkl.Nonempty := by
      have hRimage : R ∈ A.image (U.cover.assign k) := (hregular.surjective k (by omega)) ▸ hR
      obtain ⟨i, hi, hiR⟩ := Finset.mem_image.mp hRimage
      exact ⟨U.cover.assign l i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hiR⟩, rfl⟩⟩
    refine ⟨himage, hfibre, ?_, ?_⟩
    · calc
        (Dkl.card : NNReal) * hregular.countBand l m = ∑ Q ∈ Dkl, hregular.countBand l m := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ <= ∑ Q ∈ Dkl, ((Dlm Q).card : NNReal) := Finset.sum_le_sum
          (fun Q hQ => hregular.count_lower l m hlm hm Q (hQmem Q hQ))
        _ = (Dkm.card : NNReal) := hsum.symm
    · calc
        (Dkm.card : NNReal) = ∑ Q ∈ Dkl, ((Dlm Q).card : NNReal) := hsum
        _ < ∑ Q ∈ Dkl, 2 * hregular.countBand l m := by
          apply Finset.sum_lt_sum
          · exact fun Q hQ => (hregular.count_upper l m hlm hm Q (hQmem Q hQ)).le
          · obtain ⟨Q, hQ⟩ := hDkl
            exact ⟨Q, hQ, hregular.count_upper l m hlm hm Q (hQmem Q hQ)⟩
        _ = 2 * (Dkl.card : NNReal) * hregular.countBand l m := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hactual_two_scale {delta : NNReal} (hd : 0 < delta) (hd1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E)
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (k l m : Nat) (hkl : k < l) (hlm : l < m) (hm : m <= M)
      (hgap : 4 * Tube.gridScale delta M m <= Tube.gridScale delta M l)
      (R : iota) (hR : R ∈ U.cover.indexSet k) :
      Kakeya.maxDensity (actualDescendantsW95 A U.cover.assign k m R)
        (fun W => (U.cover.tube m W).toConvexSpaceBody) <=
      ENNReal.ofReal Ctwo ^ (2 : Nat) *
        Kakeya.maxDensity (actualDescendantsW95 A U.cover.assign k l R)
          (fun Q => (U.cover.tube l Q).toConvexSpaceBody) *
        (actualDescendantsW95 A U.cover.assign k l R).sup
          (fun Q => Kakeya.maxDensity (actualDescendantsW95 A U.cover.assign l m Q)
            (fun W => (U.cover.tube m W).toConvexSpaceBody)) := by
    obtain ⟨parent, hparent, hpartition⟩ := hdescendant_partition A Y U hregular k l m hkl hlm hm
    obtain ⟨himage, hfibre, _, _⟩ := hpartition R hR
    let Q1 := actualDescendantsW95 A U.cover.assign k l R
    let Q2 := actualDescendantsW95 A U.cover.assign k m R
    let W1 := fun Q => (U.cover.tube l Q).toConvexSpaceBody
    let W2 := fun Q => (U.cover.tube m Q).toConvexSpaceBody
    change Q2.image parent = Q1 at himage
    have hQmem (a b : Nat) (hb : b <= M) (S : iota)
        (Q : iota) (hQ : Q ∈ actualDescendantsW95 A U.cover.assign a b S) :
        Q ∈ U.cover.indexSet b := by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      exact U.cover.assign_mem b hb i (Finset.mem_filter.mp hi).1
    have hQ2ne : Q2.Nonempty := by
      have hRi : R ∈ A.image (U.cover.assign k) := (hregular.surjective k (by omega)) ▸ hR
      obtain ⟨i, hi, hiR⟩ := Finset.mem_image.mp hRi
      exact ⟨U.cover.assign m i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hiR⟩, rfl⟩⟩
    have hQ1ne : Q1.Nonempty := himage ▸ hQ2ne.image parent
    have hcontain : ∀ W ∈ Q2, W2 W <= W1 (parent W) := by
      intro W hW
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
      have hiA := (Finset.mem_filter.mp hi).1
      change (U.cover.tube m (U.cover.assign m i)).toConvexSpaceBody <=
        (U.cover.tube l (parent (U.cover.assign m i))).toConvexSpaceBody
      rw [hparent i hiA]
      have hnested (n : Nat) (hln : l <= n) (hn : n <= M) :
          (U.cover.tube n (U.cover.assign n i)).toConvexSpaceBody <=
            (U.cover.tube l (U.cover.assign l i)).toConvexSpaceBody := by
        induction n, hln using Nat.le_induction with
        | base => exact le_rfl
        | succ n hln ih => exact (U.cover.tube_nested n hn i hiA).trans (ih (by omega))
      exact hnested m hlm.le hm
    obtain ⟨u, hu⟩ : ∃ u : E, ‖u‖ = 1 := exists_norm_eq E zero_le_one
    let amb : Tube 4 E := Tube.ofMidpointDirection 4 0 u hu
    have hambmid : _root_.midpoint Real amb.x amb.y = 0 := by
      rw [midpoint_eq_smul_add]
      change (⅟(2 : Real)) • ((0 - (1 / 2 : Real) • u) + (0 + (1 / 2 : Real) • u)) = 0
      simp
    have hamb_ball : amb.carrier ⊆ Metric.closedBall (0 : E) 5 := by
      intro z hz
      have h := Tube.carrier_subset_closedBall_midpoint (E := E) amb hz
      rw [hambmid, Metric.mem_closedBall] at h
      rw [Metric.mem_closedBall]
      have h4 : ((4 : NNReal) : Real) = 4 := by norm_num
      rw [h4] at h
      linarith
    have hball_amb : Metric.closedBall (0 : E) 4 ⊆ amb.carrier := by
      intro z hz
      rw [amb.carrier_eq]
      refine Set.mem_biUnion (midpoint_mem_segment amb.x amb.y) ?_
      rw [hambmid]
      simpa using hz
    let rho : Fin 3 -> NNReal := fun j => match j with
      | ⟨0, _⟩ => 4
      | ⟨1, _⟩ => Tube.gridScale delta M l
      | ⟨_ + 2, _⟩ => Tube.gridScale delta M m
    let tb : ∀ j : Fin 3, iota -> Tube (rho j) E := fun j => match j with
      | ⟨0, _⟩ => fun _ => amb
      | ⟨1, _⟩ => U.cover.tube l
      | ⟨_ + 2, _⟩ => U.cover.tube m
    let Q : Fin 3 -> Finset iota := fun j => match j with
      | ⟨0, _⟩ => {R}
      | ⟨1, _⟩ => Q1
      | ⟨_ + 2, _⟩ => Q2
    let proj : Fin 2 -> iota -> iota := fun j => match j with
      | ⟨0, _⟩ => fun _ => R
      | ⟨_ + 1, _⟩ => parent
    have hgap1 : 4 * rho 1 <= rho 0 := by
      change 4 * Tube.gridScale delta M l <= 4
      calc
        4 * Tube.gridScale delta M l <= 4 * 1 := mul_le_mul' le_rfl (Tube.gridScale_le_one hd1 M l)
        _ = 4 := by norm_num
    have hmaps : ∀ j : Fin 2, ∀ W ∈ Q j.succ, proj j W ∈ Q j.castSucc := by
      intro j
      fin_cases j
      · exact fun W hW => Finset.mem_singleton_self R
      · intro W hW
        change parent W ∈ Q1
        rw [← himage]
        exact Finset.mem_image_of_mem parent hW
    have hnest : ∀ j : Fin 2, ∀ W ∈ Q j.succ,
        (tb j.succ W).toConvexSpaceBody <= (tb j.castSucc (proj j W)).toConvexSpaceBody := by
      intro j
      fin_cases j
      · intro W hW
        change (U.cover.tube l W).toConvexSpaceBody <= amb.toConvexSpaceBody
        apply SetLike.coe_subset_coe.mpr
        exact (hregular.parent_ball l (by omega) W (hQmem k l (by omega) R W hW)).trans
          ((Metric.closedBall_subset_closedBall (by norm_num : (2 : Real) <= 4)).trans hball_amb)
      · exact hcontain
    have hball : ∀ j : Fin 3, ∀ W ∈ Q j, (tb j W).carrier ⊆ Metric.closedBall (0 : E) 5 := by
      intro j
      fin_cases j
      · exact fun W hW => hamb_ball
      · intro W hW
        exact (hregular.parent_ball l (by omega) W (hQmem k l (by omega) R W hW)).trans
          (Metric.closedBall_subset_closedBall (by norm_num))
      · intro W hW
        exact (hregular.parent_ball m hm W (hQmem k m hm R W hW)).trans
          (Metric.closedBall_subset_closedBall (by norm_num))
    have hne : ∀ j : Fin 2, (Q j.castSucc).Nonempty := by
      intro j
      fin_cases j
      · exact Finset.singleton_nonempty R
      · exact hQ1ne
    have hcard : ((Q 0).card : Real) <= 1 * (5 + 3) ^ (2 * Module.finrank Real E) := by
      change (({R} : Finset iota).card : Real) <= _
      rw [Finset.card_singleton, one_mul]
      exact_mod_cast one_le_pow₀ (by norm_num : (1 : Real) <= 5 + 3)
    have h := htwo rho (by norm_num [rho]) (by norm_num [rho])
      (Tube.gridScale_pos hd M m) hgap1 hgap tb Q proj hmaps hnest hcard hball hne
    rw [Fin.prod_univ_two] at h
    change Kakeya.maxDensity Q2 W2 <= ENNReal.ofReal Ctwo ^ (2 : Nat) *
      (Kakeya.MultiScaleSubmult.fibreDeltaMax Q1 W1 ({R} : Finset iota) (fun _ => R) *
        Kakeya.MultiScaleSubmult.fibreDeltaMax Q2 W2 Q1 parent) at h
    have hfirst : Kakeya.MultiScaleSubmult.fibreDeltaMax Q1 W1 ({R} : Finset iota) (fun _ => R) =
        Kakeya.maxDensity Q1 W1 := by
      unfold Kakeya.MultiScaleSubmult.fibreDeltaMax
      rw [Finset.sup_singleton]
      congr 1
      ext W
      simp
    have hlast : Kakeya.MultiScaleSubmult.fibreDeltaMax Q2 W2 Q1 parent =
        Q1.sup (fun S => Kakeya.maxDensity (actualDescendantsW95 A U.cover.assign l m S) W2) := by
      unfold Kakeya.MultiScaleSubmult.fibreDeltaMax
      apply Finset.sup_congr rfl
      intro S hS
      congr 1
      ext W
      simpa only [Finset.mem_filter] using Finset.ext_iff.mp (hfibre S hS) W
    rw [hfirst, hlast] at h
    simpa only [mul_assoc] using h
  have hactual_cf_composition {delta : NNReal} (hd : 0 < delta) (hd1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E)
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (k l m : Nat) (hkl : k < l) (hlm : l < m) (hm : m <= M)
      (hgap : 4 * Tube.gridScale delta M m <= Tube.gridScale delta M l)
      (R : iota) (hR : R ∈ U.cover.indexSet k) :
      actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k m R <=
        2 * ENNReal.ofReal Ctwo ^ (2 : Nat) *
          (U.cover.indexSet k).sup (actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l) *
          (U.cover.indexSet l).sup (actualRelativeFrostmanW95 A U.cover.assign U.cover.tube l m) := by
    let D := actualDescendantsW95 A U.cover.assign
    let V := fun n Q => (U.cover.tube n Q).toConvexSpaceBody
    let v := fun n => volume (U.cover.tube n R).carrier
    let X := fun a b => (U.cover.indexSet a).sup (actualRelativeFrostmanW95 A U.cover.assign U.cover.tube a b)
    have hvpos (n : Nat) : 0 < v n := (Tube.volume_pos_and_lt_top
      (Tube.gridScale_pos hd M n) (Tube.gridScale_le_one hd1 M n) (U.cover.tube n R)).1
    have hvfinite (n : Nat) : v n < ⊤ := (Tube.volume_pos_and_lt_top
      (Tube.gridScale_pos hd M n) (Tube.gridScale_le_one hd1 M n) (U.cover.tube n R)).2
    have hcontained (a b : Nat) (hab : a <= b) (hb : b <= M) (S : iota) :
        ∀ W ∈ D a b S, V b W <= V a S := by
      intro W hW
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
      obtain ⟨hiA, hiS⟩ := Finset.mem_filter.mp hi
      have hnest (n : Nat) (han : a <= n) (hn : n <= M) :
          (U.cover.tube n (U.cover.assign n i)).toConvexSpaceBody <=
            (U.cover.tube a (U.cover.assign a i)).toConvexSpaceBody := by
        induction n, han using Nat.le_induction with
        | base => exact le_rfl
        | succ n han ih => exact (U.cover.tube_nested n hn i hiA).trans (ih (by omega))
      simpa only [hiS] using hnest b hab hb
    have hsum (a b : Nat) (S : iota) :
        (∑ W ∈ D a b S, volume (V b W).carrier) = ((D a b S).card : ENNReal) * v b := by
      calc
        (∑ W ∈ D a b S, volume (V b W).carrier) = ∑ W ∈ D a b S, v b :=
          Finset.sum_congr rfl (fun W hW => Tube.volume_carrier_eq_volume_carrier (U.cover.tube b W) (U.cover.tube b R))
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hmax (a b : Nat) (hab : a < b) (hb : b <= M) (S : iota) (hS : S ∈ U.cover.indexSet a) :
        Kakeya.maxDensity (D a b S) (V b) <= X a b * (((D a b S).card : ENNReal) * v b / v a) := by
      have h := (isFrostmanIn_frostmanConstIn (D a b S) (V b) (V a S)).maxDensity_le_of_carrier_subset
        (hcontained a b hab.le hb S)
      have hden : Kakeya.densityIn (D a b S) (V b) (V a S) = ((D a b S).card : ENNReal) * v b / v a := by
        rw [Kakeya.densityIn_of_all_le (hcontained a b hab.le hb S), hsum a b S]
        rw [show volume (V a S).carrier = v a from Tube.volume_carrier_eq_volume_carrier (U.cover.tube a S) (U.cover.tube a R)]
      rw [hden] at h
      exact h.trans (mul_le_mul' (Finset.le_sup
        (f := actualRelativeFrostmanW95 A U.cover.assign U.cover.tube a b) hS) le_rfl)
    have hQmem : ∀ Q ∈ D k l R, Q ∈ U.cover.indexSet l := by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      exact U.cover.assign_mem l (by omega) i (Finset.mem_filter.mp hi).1
    have hsup : (D k l R).sup (fun Q => Kakeya.maxDensity (D l m Q) (V m)) <=
        X l m * (2 * (hregular.countBand l m : ENNReal) * v m / v l) := by
      apply Finset.sup_le
      intro Q hQ
      have hn : ((D l m Q).card : ENNReal) <= 2 * (hregular.countBand l m : ENNReal) := by
        exact_mod_cast (hregular.count_upper l m hlm hm Q (hQmem Q hQ)).le
      calc
        Kakeya.maxDensity (D l m Q) (V m) <= X l m * (((D l m Q).card : ENNReal) * v m / v l) :=
          hmax l m hlm hm Q (hQmem Q hQ)
        _ <= _ := by gcongr
    have hn : ((D k l R).card : ENNReal) * (hregular.countBand l m : ENNReal) <=
        ((D k m R).card : ENNReal) := by
      obtain ⟨parent, hparent, hpartition⟩ := hdescendant_partition A Y U hregular k l m hkl hlm hm
      exact_mod_cast (hpartition R hR).2.2.1
    have hmaxTwo := hactual_two_scale hd hd1 A Y U hregular k l m hkl hlm hm hgap R hR
    have hmaxNormalized : Kakeya.maxDensity (D k m R) (V m) <=
        ENNReal.ofReal Ctwo ^ (2 : Nat) *
          (X k l * (((D k l R).card : ENNReal) * v l / v k)) *
          (X l m * (2 * (hregular.countBand l m : ENNReal) * v m / v l)) := by
      exact hmaxTwo.trans (mul_le_mul' (mul_le_mul' le_rfl (hmax k l hkl (by omega) R hR)) hsup)
    apply frostmanConstIn_le
    apply IsFrostmanIn.of_maxDensity_mul_volume_le (hcontained k m (by omega) hm R) (hvpos k).ne'
    change Kakeya.maxDensity (D k m R) (V m) * v k <=
      (2 * ENNReal.ofReal Ctwo ^ (2 : Nat) * X k l * X l m) *
        (∑ W ∈ D k m R, volume (V m W).carrier)
    rw [hsum k m R]
    calc
      Kakeya.maxDensity (D k m R) (V m) * v k <=
          (ENNReal.ofReal Ctwo ^ (2 : Nat) *
            (X k l * (((D k l R).card : ENNReal) * v l / v k)) *
            (X l m * (2 * (hregular.countBand l m : ENNReal) * v m / v l))) * v k :=
        mul_le_mul' hmaxNormalized le_rfl
      _ = (2 * ENNReal.ofReal Ctwo ^ (2 : Nat) * X k l * X l m) *
          (((D k l R).card : ENNReal) * (hregular.countBand l m : ENNReal) * v m) *
          (v l * (v l)⁻¹) * ((v k)⁻¹ * v k) := by simp only [div_eq_mul_inv]; ring
      _ = (2 * ENNReal.ofReal Ctwo ^ (2 : Nat) * X k l * X l m) *
          (((D k l R).card : ENNReal) * (hregular.countBand l m : ENNReal) * v m) := by
        rw [ENNReal.mul_inv_cancel (hvpos l).ne' (hvfinite l).ne,
          ENNReal.inv_mul_cancel (hvpos k).ne' (hvfinite k).ne]
        simp
      _ <= _ := mul_le_mul' le_rfl (mul_le_mul' hn le_rfl)
  have hCbound : ENNReal.ofReal Ctwo <= (C : ENNReal) := by
    exact ENNReal.coe_le_coe.mpr (le_max_right (1 : NNReal) (Real.toNNReal Ctwo))
  have hparent : ∀ R ∈ U.cover.indexSet k,
      actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k m R <=
        2 * (C : ENNReal) ^ (2 : Nat) * actualRelativeCFArrayW97 U k l *
          actualRelativeCFArrayW97 U l m := by
    intro R hR
    refine (hactual_cf_composition hd hd1 A Y U hregular k l m hkl hlm hm hgap R hR).trans ?_
    change 2 * ENNReal.ofReal Ctwo ^ (2 : Nat) * actualRelativeCFArrayW97 U k l *
      actualRelativeCFArrayW97 U l m <= _
    gcongr
  exact ⟨hparent, Finset.sup_le hparent⟩

/-- A3: the crude exponent is relative-scale two; prefix CF uses the same
final count bands and exact nested assigned families. -/
theorem actual_relative_cf_crude_and_prefix_w97 (hdim : Module.finrank Real E = 3) :
    ∃ Cvol : NNReal, 1 <= Cvol ∧
      ∀ {iota : Type uI} [DecidableEq iota] {delta : NNReal}, 0 < delta -> delta <= 1 ->
      ∀ {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan Ctw Ccell : NNReal}
        (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan),
        A.Nonempty -> SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        (∀ k l : Nat, k < l -> l <= M -> ∀ R ∈ U.cover.indexSet k,
          actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l R <=
            (Cvol : ENNReal) * ((Tube.gridScale delta M k : ENNReal) /
              (Tube.gridScale delta M l : ENNReal)) ^ (2 : Nat)) ∧
        (∀ k m b : Nat, k < m -> m < b -> b <= M ->
          (∀ R ∈ U.cover.indexSet k,
            actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k m R <=
              2 * actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k b R) ∧
          actualRelativeCFArrayW97 U k m <= 4 * actualRelativeCFArrayW97 U k b) := by
  let Cvol : NNReal := max 1 (Tube.volume_le.C 3 / Tube.le_volume.c 3)
  refine ⟨Cvol, le_max_left _ _, ?_⟩
  intro iota inst delta hd hd1 A Y M Ccan Ctw Ccell U hA hregular
  have hrelative_crude {delta : NNReal} (hd : 0 < delta) (hd1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E)
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (k l : Nat) (hkl : k < l) (hl : l <= M) (R : iota) (hR : R ∈ U.cover.indexSet k) :
      1 <= actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l R ∧
        actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l R <=
          ((Tube.volume_le.C 3 : ENNReal) / (Tube.le_volume.c 3 : ENNReal)) *
            (((Tube.gridScale delta M k : ENNReal) / (Tube.gridScale delta M l : ENNReal)) ^ (2 : Nat)) := by
    let D := actualDescendantsW95 A U.cover.assign k l R
    have hRimage : R ∈ A.image (U.cover.assign k) := (hregular.surjective k (by omega)) ▸ hR
    obtain ⟨i0, hi0, hi0R⟩ := Finset.mem_image.mp hRimage
    have hD : D.Nonempty := ⟨U.cover.assign l i0, Finset.mem_image.mpr
      ⟨i0, Finset.mem_filter.mpr ⟨hi0, hi0R⟩, rfl⟩⟩
    have hcontained : ∀ Q ∈ D,
        (U.cover.tube l Q).toConvexSpaceBody <= (U.cover.tube k R).toConvexSpaceBody := by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
      have hnest : ∀ n, k <= n -> n <= M ->
          (U.cover.tube n (U.cover.assign n i)).toConvexSpaceBody <=
            (U.cover.tube k (U.cover.assign k i)).toConvexSpaceBody := by
        intro n hkn
        induction n, hkn using Nat.le_induction with
        | base => exact fun _ => le_rfl
        | succ n hkn ih =>
          intro hn
          exact (U.cover.tube_nested n hn i hiA).trans (ih (by omega))
      simpa only [hiR] using hnest l hkl.le hl
    obtain ⟨Q0, hQ0⟩ := hD
    let v := volume (U.cover.tube l Q0).carrier
    let P := (U.cover.tube k R).toConvexSpaceBody
    let V := fun Q => (U.cover.tube l Q).toConvexSpaceBody
    have hvol : ∀ Q ∈ D, volume (V Q).carrier = v := fun Q hQ =>
      Tube.volume_carrier_eq_volume_carrier (U.cover.tube l Q) (U.cover.tube l Q0)
    have hvl := Tube.volume_pos_and_lt_top (Tube.gridScale_pos hd M l)
      (Tube.gridScale_le_one hd1 M l) (U.cover.tube l Q0)
    have hvk := Tube.volume_pos_and_lt_top (Tube.gridScale_pos hd M k)
      (Tube.gridScale_le_one hd1 M k) (U.cover.tube k R)
    have hdensity : Kakeya.densityIn D V P = (D.card : ENNReal) * v / volume P.carrier := by
      rw [Kakeya.densityIn_of_all_le hcontained]
      congr 1
      calc
        (∑ i ∈ D, volume (V i).carrier) = ∑ i ∈ D, v := Finset.sum_congr rfl hvol
        _ = (D.card : ENNReal) * v := by rw [Finset.sum_const, nsmul_eq_mul]
    have hdensity_pos : 0 < Kakeya.densityIn D V P := by
      rw [hdensity]
      exact ENNReal.div_pos (mul_ne_zero
        (by exact_mod_cast (Finset.card_pos.mpr (show D.Nonempty from ⟨Q0, hQ0⟩)).ne') hvl.1.ne') hvk.2.ne
    have hCFvol : frostmanConstIn D V P <= volume P.carrier / v := by
      apply frostmanConstIn_le
      intro Q hQP
      have hcancel : volume P.carrier / v * Kakeya.densityIn D V P = (D.card : ENNReal) := by
        rw [hdensity, div_eq_mul_inv, div_eq_mul_inv]
        calc
          volume P.carrier * v⁻¹ * ((D.card : ENNReal) * v * (volume P.carrier)⁻¹) =
              (D.card : ENNReal) * (v * v⁻¹) * (volume P.carrier * (volume P.carrier)⁻¹) := by ring
          _ = (D.card : ENNReal) := by
            rw [ENNReal.mul_inv_cancel hvl.1.ne' hvl.2.ne,
              ENNReal.mul_inv_cancel hvk.1.ne' hvk.2.ne]
            simp
      rw [hcancel]
      exact Kakeya.densityIn_le_card D V Q
    refine ⟨(isFrostmanIn_frostmanConstIn D V P).one_le hdensity_pos, ?_⟩
    have hparentVolume : volume P.carrier <= (Tube.volume_le.C 3 : ENNReal) *
        ((Tube.gridScale delta M k : ENNReal) ^ (2 : Nat)) := by
      simpa only [hdim, Nat.reduceSub] using
        Tube.volume_le (Tube.gridScale_le_one hd1 M k) (U.cover.tube k R)
    have hchildVolume : (Tube.le_volume.c 3 : ENNReal) *
        ((Tube.gridScale delta M l : ENNReal) ^ (2 : Nat)) <= v := by
      simpa only [hdim, Nat.reduceSub] using Tube.le_volume (U.cover.tube l Q0)
    have hc0 : (Tube.le_volume.c 3 : ENNReal) ≠ 0 :=
      (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos 3)).ne'
    calc
      actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l R <= volume P.carrier / v := hCFvol
      _ <= ((Tube.volume_le.C 3 : ENNReal) * (Tube.gridScale delta M k : ENNReal) ^ (2 : Nat)) /
          ((Tube.le_volume.c 3 : ENNReal) * (Tube.gridScale delta M l : ENNReal) ^ (2 : Nat)) :=
        ENNReal.div_le_div hparentVolume hchildVolume
      _ = _ := by
        simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc0) (Or.inl ENNReal.coe_ne_top),
          ENNReal.inv_pow, mul_pow]
        ring
  have hdescendant_partition {delta : NNReal}
      {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E)
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (k l m : Nat) (hkl : k < l) (hlm : l < m) (hm : m <= M) :
      ∃ parent : iota -> iota,
        (∀ i ∈ A, parent (U.cover.assign m i) = U.cover.assign l i) ∧
        ∀ R ∈ U.cover.indexSet k,
          (actualDescendantsW95 A U.cover.assign k m R).image parent =
            actualDescendantsW95 A U.cover.assign k l R ∧
          (∀ Q ∈ actualDescendantsW95 A U.cover.assign k l R,
            (actualDescendantsW95 A U.cover.assign k m R).filter (fun W => parent W = Q) =
              actualDescendantsW95 A U.cover.assign l m Q) ∧
          ((actualDescendantsW95 A U.cover.assign k l R).card : NNReal) * hregular.countBand l m <=
            ((actualDescendantsW95 A U.cover.assign k m R).card : NNReal) ∧
          ((actualDescendantsW95 A U.cover.assign k m R).card : NNReal) <
            2 * ((actualDescendantsW95 A U.cover.assign k l R).card : NNReal) * hregular.countBand l m := by
    let parent : iota -> iota := fun Q => if hQ : Q ∈ A.image (U.cover.assign m) then
      U.cover.assign l (Finset.mem_image.mp hQ).choose else Q
    have hparent : ∀ i ∈ A, parent (U.cover.assign m i) = U.cover.assign l i := by
      intro i hi
      have hj : U.cover.assign m i ∈ A.image (U.cover.assign m) := Finset.mem_image.mpr ⟨i, hi, rfl⟩
      dsimp only [parent]
      rw [dif_pos hj]
      exact U.cover.assign_eq_of_le hlm.le hm
        (Finset.mem_image.mp hj).choose_spec.1 hi (Finset.mem_image.mp hj).choose_spec.2
    refine ⟨parent, hparent, ?_⟩
    intro R hR
    let Dkm := actualDescendantsW95 A U.cover.assign k m R
    let Dkl := actualDescendantsW95 A U.cover.assign k l R
    let Dlm := actualDescendantsW95 A U.cover.assign l m
    have himage : Dkm.image parent = Dkl := by
      ext Q
      constructor
      · intro hQ
        obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        rw [hparent i hiA]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩
      · intro hQ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_image.mpr ⟨U.cover.assign m i,
          Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩, hparent i hiA⟩
    have hfibre : ∀ Q ∈ Dkl, Dkm.filter (fun W => parent W = Q) = Dlm Q := by
      intro Q hQ
      obtain ⟨i0, hi0, hi0Q⟩ := Finset.mem_image.mp hQ
      obtain ⟨hi0A, hi0R⟩ := Finset.mem_filter.mp hi0
      ext W
      constructor
      · intro hW
        obtain ⟨hW, hWQ⟩ := Finset.mem_filter.mp hW
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        have hiQ : U.cover.assign l i = Q := (hparent i hiA).symm.trans hWQ
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiQ⟩, rfl⟩
      · intro hW
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
        obtain ⟨hiA, hiQ⟩ := Finset.mem_filter.mp hi
        have hiR : U.cover.assign k i = R :=
          (U.cover.assign_eq_of_le hkl.le (by omega) hiA hi0A (hiQ.trans hi0Q.symm)).trans hi0R
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩,
            (hparent i hiA).trans hiQ⟩
    have hQmem : ∀ Q ∈ Dkl, Q ∈ U.cover.indexSet l := by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      exact U.cover.assign_mem l (by omega) i (Finset.mem_filter.mp hi).1
    have hsum : (Dkm.card : NNReal) = ∑ Q ∈ Dkl, ((Dlm Q).card : NNReal) := by
      have hmaps : ∀ W ∈ Dkm, parent W ∈ Dkl := by
        intro W hW
        rw [← himage]
        exact Finset.mem_image.mpr ⟨W, hW, rfl⟩
      calc
        (Dkm.card : NNReal) = ∑ Q ∈ Dkl, ((Dkm.filter (fun W => parent W = Q)).card : NNReal) := by
          simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
            (Finset.sum_fiberwise_of_maps_to hmaps (fun _ => (1 : NNReal))).symm
        _ = ∑ Q ∈ Dkl, ((Dlm Q).card : NNReal) := Finset.sum_congr rfl (fun Q hQ => by rw [hfibre Q hQ])
    have hDkl : Dkl.Nonempty := by
      have hRimage : R ∈ A.image (U.cover.assign k) := (hregular.surjective k (by omega)) ▸ hR
      obtain ⟨i, hi, hiR⟩ := Finset.mem_image.mp hRimage
      exact ⟨U.cover.assign l i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hiR⟩, rfl⟩⟩
    refine ⟨himage, hfibre, ?_, ?_⟩
    · calc
        (Dkl.card : NNReal) * hregular.countBand l m = ∑ Q ∈ Dkl, hregular.countBand l m := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ <= ∑ Q ∈ Dkl, ((Dlm Q).card : NNReal) := Finset.sum_le_sum
          (fun Q hQ => hregular.count_lower l m hlm hm Q (hQmem Q hQ))
        _ = (Dkm.card : NNReal) := hsum.symm
    · calc
        (Dkm.card : NNReal) = ∑ Q ∈ Dkl, ((Dlm Q).card : NNReal) := hsum
        _ < ∑ Q ∈ Dkl, 2 * hregular.countBand l m := by
          apply Finset.sum_lt_sum
          · exact fun Q hQ => (hregular.count_upper l m hlm hm Q (hQmem Q hQ)).le
          · obtain ⟨Q, hQ⟩ := hDkl
            exact ⟨Q, hQ, hregular.count_upper l m hlm hm Q (hQmem Q hQ)⟩
        _ = 2 * (Dkl.card : NNReal) * hregular.countBand l m := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hrelative_prefix {delta : NNReal} (hd : 0 < delta) (hd1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E)
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (k m b : Nat) (hkm : k < m) (hmb : m < b) (hb : b <= M)
      (R : iota) (hR : R ∈ U.cover.indexSet k) :
      actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k m R <=
        2 * actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k b R := by
    obtain ⟨parent, hparent, hpartition⟩ := hdescendant_partition A Y U hregular k m b hkm hmb hb
    obtain ⟨himage, hfibre, _, _⟩ := hpartition R hR
    let fine := actualDescendantsW95 A U.cover.assign k b R
    let out := actualDescendantsW95 A U.cover.assign k m R
    let V := fun Q => (U.cover.tube b Q).toConvexSpaceBody
    let W := fun Q => (U.cover.tube m Q).toConvexSpaceBody
    let K := (U.cover.tube k R).toConvexSpaceBody
    change fine.image parent = out at himage
    have hnested (a c : Nat) (hac : a <= c) (hc : c <= M) (i : iota) (hi : i ∈ A) :
        (U.cover.tube c (U.cover.assign c i)).toConvexSpaceBody <=
          (U.cover.tube a (U.cover.assign a i)).toConvexSpaceBody := by
      revert hc
      induction c, hac using Nat.le_induction with
      | base => exact fun _ => le_rfl
      | succ c hac ih =>
        intro hc
        exact (U.cover.tube_nested c hc i hi).trans (ih (by omega))
    have hmaps : ∀ Q ∈ fine, parent Q ∈ out := by
      intro Q hQ
      rw [← himage]
      exact Finset.mem_image.mpr ⟨Q, hQ, rfl⟩
    have hVW : ∀ Q ∈ fine, V Q <= W (parent Q) := by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      have hiA := (Finset.mem_filter.mp hi).1
      change (U.cover.tube b (U.cover.assign b i)).toConvexSpaceBody <=
        (U.cover.tube m (parent (U.cover.assign b i))).toConvexSpaceBody
      rw [hparent i hiA]
      exact hnested m b hmb.le hb i hiA
    have hWK : ∀ Q ∈ out, W Q <= K := by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
      simpa only [hiR] using hnested k m hkm.le (by omega) i hiA
    have hne : ∀ Q ∈ out, (fine.filter (fun P => parent P = Q)).Nonempty := by
      intro Q hQ
      rw [← himage] at hQ
      obtain ⟨P, hP, hPQ⟩ := Finset.mem_image.mp hQ
      exact ⟨P, Finset.mem_filter.mpr ⟨hP, hPQ⟩⟩
    have hQmem : ∀ Q ∈ out, Q ∈ U.cover.indexSet m := by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      exact U.cover.assign_mem m (by omega) i (Finset.mem_filter.mp hi).1
    let vb := volume (U.cover.tube b R).carrier
    let vm := volume (U.cover.tube m R).carrier
    have hdensity (Q : iota) (hQ : Q ∈ out) :
        Kakeya.densityIn (fine.filter (fun P => parent P = Q)) V (W Q) =
          ((actualDescendantsW95 A U.cover.assign m b Q).card : ENNReal) * vb / vm := by
      have hcontained : ∀ P ∈ fine.filter (fun P => parent P = Q), V P <= W Q := by
        intro P hP
        obtain ⟨hPf, hPQ⟩ := Finset.mem_filter.mp hP
        simpa only [hPQ] using hVW P hPf
      rw [Kakeya.densityIn_of_all_le hcontained]
      have hsum : (∑ P ∈ fine.filter (fun P => parent P = Q), volume (V P).carrier) =
          ((fine.filter (fun P => parent P = Q)).card : ENNReal) * vb := by
        calc
          (∑ P ∈ fine.filter (fun P => parent P = Q), volume (V P).carrier) =
              ∑ P ∈ fine.filter (fun P => parent P = Q), vb :=
            Finset.sum_congr rfl (fun P hP => Tube.volume_carrier_eq_volume_carrier
              (U.cover.tube b P) (U.cover.tube b R))
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      rw [hsum, hfibre Q hQ]
      congr 1
      exact Tube.volume_carrier_eq_volume_carrier (U.cover.tube m Q) (U.cover.tube m R)
    have hunif : ∀ Q ∈ out, ∀ Q' ∈ out,
        Kakeya.densityIn (fine.filter (fun P => parent P = Q)) V (W Q) <=
          2 * Kakeya.densityIn (fine.filter (fun P => parent P = Q')) V (W Q') := by
      intro Q hQ Q' hQ'
      have hcountNN : ((actualDescendantsW95 A U.cover.assign m b Q).card : NNReal) <=
          2 * ((actualDescendantsW95 A U.cover.assign m b Q').card : NNReal) :=
        (hregular.count_upper m b hmb hb Q (hQmem Q hQ)).le.trans
          (mul_le_mul' le_rfl (hregular.count_lower m b hmb hb Q' (hQmem Q' hQ')))
      have hcount : ((actualDescendantsW95 A U.cover.assign m b Q).card : ENNReal) <=
          2 * ((actualDescendantsW95 A U.cover.assign m b Q').card : ENNReal) := by exact_mod_cast hcountNN
      rw [hdensity Q hQ, hdensity Q' hQ']
      calc
        ((actualDescendantsW95 A U.cover.assign m b Q).card : ENNReal) * vb / vm <=
            (2 * ((actualDescendantsW95 A U.cover.assign m b Q').card : ENNReal)) * vb / vm :=
          ENNReal.div_le_div_right (mul_le_mul' hcount le_rfl) vm
        _ = _ := by simp only [div_eq_mul_inv]; ring
    exact frostmanConstIn_le (isFrostmanIn_parents_of_uniform_fibres
      (q := fine) (out := out) (V := V) (W := W) (par := parent)
      (fib := fun Q => fine.filter (fun P => parent P = Q))
      (isFrostmanIn_frostmanConstIn fine V K)
      (fun Q hQ => (Tube.volume_pos_and_lt_top (Tube.gridScale_pos hd M b)
        (Tube.gridScale_le_one hd1 M b) (U.cover.tube b Q)).1)
      hmaps hVW hWK (fun _ => rfl) hne hunif)
  have hCvol : (Tube.volume_le.C 3 : ENNReal) / (Tube.le_volume.c 3 : ENNReal) <=
      (Cvol : ENNReal) := by
    rw [← ENNReal.coe_div (Tube.le_volume.c_pos 3).ne']
    exact ENNReal.coe_le_coe.mpr (le_max_right _ _)
  constructor
  · intro k l hkl hl R hR
    refine (hrelative_crude hd hd1 A Y U hregular k l hkl hl R hR).2.trans ?_
    exact mul_le_mul' hCvol le_rfl
  · intro k m b hkm hmb hb
    have hparent := hrelative_prefix hd hd1 A Y U hregular k m b hkm hmb hb
    refine ⟨hparent, Finset.sup_le (fun R hR => ?_)⟩
    calc
      actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k m R <=
          2 * actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k b R := hparent R hR
      _ <= 2 * actualRelativeCFArrayW97 U k b := mul_le_mul' le_rfl
        (Finset.le_sup (f := actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k b) hR)
      _ <= 4 * actualRelativeCFArrayW97 U k b := mul_le_mul' (by norm_num) le_rfl

/-- A4: the root set need not be a singleton; its actual line cap pays the top entry. -/
theorem actual_top_relative_cf_w97 (hdim : Module.finrank Real E = 3) :
    ∃ Croot : NNReal, 1 <= Croot ∧
      ∀ {iota : Type uI} [DecidableEq iota] {delta : NNReal}, 0 < delta -> delta <= 1 ->
      ∀ {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan Ctw Ccell : NNReal}
        (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan),
        1 <= M -> A.Nonempty -> SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        (∀ i ∈ A, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        ∀ F0 : ENNReal,
          frostmanConstIn A (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <= F0 ->
          ((U.cover.indexSet 0).card : NNReal) <= Ctw ∧
          actualRelativeCFArrayW97 U 0 M <= (Croot : ENNReal) * (Ctw : ENNReal) * F0 := by
  let CrootENN : ENNReal := 2 * (Tube.volume_le.C 3 : ENNReal) /
    volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
  have hCrootFinite : CrootENN ≠ ⊤ := ENNReal.div_ne_top (by finiteness)
    (ConvexSpaceBody.closedUnitBall_volume_pos (E := E)).ne'
  let Croot : NNReal := max 1 CrootENN.toNNReal
  refine ⟨Croot, le_max_left _ _, ?_⟩
  intro iota inst delta hd hd1 A Y M Ccan Ctw Ccell U hM hA hregular hball F0 hCF
  have hrelative_top {delta : NNReal} (hd : 0 < delta) (hd1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E)
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (hball : ∀ i ∈ A, (Y i).carrier ⊆ Metric.closedBall 0 1)
      (F0 : ENNReal) (hCF : frostmanConstIn A (fun i => (Y i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall <= F0)
      (R : iota) (hR : R ∈ U.cover.indexSet 0) :
      ((U.cover.indexSet 0).card : NNReal) <= Ctw ∧
      actualRelativeFrostmanW95 A U.cover.assign U.cover.tube 0 M R <=
        (2 * (Tube.volume_le.C 3 : ENNReal) / volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier) *
          (Ctw : ENNReal) * F0 := by
    let roots := U.cover.indexSet 0
    let fibres := completeFibreW94 A (U.cover.assign 0)
    let V := fun i => (Y i).toConvexSpaceBody
    let P := (U.cover.tube 0 R).toConvexSpaceBody
    let v := volume (Y R).carrier
    let vB := volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
    have hM : 0 < M := lt_of_lt_of_le Nat.zero_lt_one hM
    have hbottom : ∀ Q, actualDescendantsW95 A U.cover.assign 0 M Q = fibres Q := by
      intro Q
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
        have hjA := (Finset.mem_filter.mp hj).1
        have hji' : j = i := (hregular.bottom_assign j hjA).symm.trans hji
        exact hji' ▸ hj
      · intro hi
        exact Finset.mem_image.mpr ⟨i, hi, hregular.bottom_assign i (Finset.mem_filter.mp hi).1⟩
    have hroots : (roots.card : NNReal) <= Ctw := by
      obtain ⟨u, hu⟩ : ∃ u : E, ‖u‖ = 1 := exists_norm_eq E zero_le_one
      have hfilter : roots.filter (fun Q => liesInFiveDeltaLineTubeW94 (U.cover.tube 0 Q) 0 u) = roots := by
        apply Finset.filter_true_of_mem
        intro Q hQ x hx
        refine ⟨0, ?_⟩
        have hxball := hregular.parent_ball 0 (Nat.zero_le _) Q hQ hx
        have hx2 : dist x 0 <= 2 := Metric.mem_closedBall.mp hxball
        simpa only [zero_smul, zero_add, Tube.gridScale_zero, NNReal.coe_one, mul_one] using
          (show dist x 0 <= 5 by linarith)
      have hline := hregular.parent_line_ed 0 (Nat.zero_le _) 0 u hu
      change ((roots.filter (fun Q => liesInFiveDeltaLineTubeW94 (U.cover.tube 0 Q) 0 u)).card : NNReal) <= Ctw at hline
      rwa [hfilter] at hline
    have hcount : ∀ Q ∈ roots, ((fibres Q).card : NNReal) <= 2 * ((fibres R).card : NNReal) := by
      intro Q hQ
      have hupper := (hregular.count_upper 0 M (by omega) le_rfl Q hQ).le
      have hlower := hregular.count_lower 0 M (by omega) le_rfl R hR
      rw [hbottom Q] at hupper
      rw [hbottom R] at hlower
      exact hupper.trans (mul_le_mul' le_rfl hlower)
    have hcountA : (A.card : ENNReal) <= 2 * (Ctw : ENNReal) * ((fibres R).card : ENNReal) := by
      have hNN : (A.card : NNReal) <= 2 * Ctw * ((fibres R).card : NNReal) := by
        calc
          (A.card : NNReal) = ∑ Q ∈ roots, ((fibres Q).card : NNReal) := by
            have hsum := (Finset.sum_fiberwise_of_maps_to (U.cover.assign_mem 0 (Nat.zero_le _))
              (fun _ => (1 : NNReal))).symm
            simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
            refine hsum.trans (Finset.sum_congr rfl (fun Q hQ => ?_))
            congr 2
          _ <= ∑ Q ∈ roots, 2 * ((fibres R).card : NNReal) := Finset.sum_le_sum hcount
          _ = (roots.card : NNReal) * (2 * ((fibres R).card : NNReal)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
          _ <= Ctw * (2 * ((fibres R).card : NNReal)) := mul_le_mul' hroots le_rfl
          _ = 2 * Ctw * ((fibres R).card : NNReal) := by ring
      exact_mod_cast hNN
    have hsum (D : Finset iota) : (∑ i ∈ D, volume (V i).carrier) = (D.card : ENNReal) * v := by
      calc
        (∑ i ∈ D, volume (V i).carrier) = ∑ i ∈ D, v := Finset.sum_congr rfl
          (fun i hi => Tube.volume_carrier_eq_volume_carrier (Y i).toTube (Y R).toTube)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hdensityA : Kakeya.densityIn A V ConvexSpaceBody.closedUnitBall = (A.card : ENNReal) * v / vB := by
      rw [Kakeya.densityIn_of_all_le (fun i hi => hball i hi), hsum A]
    have hmaxA : Kakeya.maxDensity A V <= F0 * ((A.card : ENNReal) * v / vB) := by
      have h := ((isFrostmanIn_frostmanConstIn A V ConvexSpaceBody.closedUnitBall).mono hCF).maxDensity_le_of_carrier_subset
        (fun i hi => hball i hi)
      rwa [hdensityA] at h
    have hPvolume : volume P.carrier <= (Tube.volume_le.C 3 : ENNReal) := by
      have h := Tube.volume_le (Tube.gridScale_le_one hd1 M 0) (U.cover.tube 0 R)
      simpa only [hdim, Nat.reduceSub, Tube.gridScale_zero, ENNReal.coe_one, one_pow, mul_one] using h
    have hsub : fibres R ⊆ A := Finset.filter_subset _ _
    have hcontained : ∀ i ∈ fibres R, V i <= P := by
      intro i hi
      obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
      simpa only [hiR] using U.cover.le_tube_assign 0 (Nat.zero_le _) i hiA
    have hPpos : 0 < volume P.carrier := (Tube.volume_pos_and_lt_top
      (Tube.gridScale_pos hd M 0) (Tube.gridScale_le_one hd1 M 0) (U.cover.tube 0 R)).1
    have hFr : IsFrostmanIn (fibres R) V P
        ((2 * (Tube.volume_le.C 3 : ENNReal) / vB) * (Ctw : ENNReal) * F0) := by
      apply IsFrostmanIn.of_maxDensity_mul_volume_le hcontained hPpos.ne'
      rw [hsum (fibres R)]
      calc
        Kakeya.maxDensity (fibres R) V * volume P.carrier <=
            (F0 * ((A.card : ENNReal) * v / vB)) * (Tube.volume_le.C 3 : ENNReal) :=
          mul_le_mul' ((Kakeya.maxDensity_mono V hsub).trans hmaxA) hPvolume
        _ <= (F0 * ((2 * (Ctw : ENNReal) * ((fibres R).card : ENNReal)) * v / vB)) *
            (Tube.volume_le.C 3 : ENNReal) := by gcongr
        _ = _ := by simp only [div_eq_mul_inv]; ring
    refine ⟨hroots, ?_⟩
    unfold actualRelativeFrostmanW95
    rw [hbottom R, frostmanConstIn_congr (fibres R)
      (fun i hi => hregular.bottom_tube i (hsub hi)) (U.cover.tube 0 R).toConvexSpaceBody]
    exact frostmanConstIn_le hFr
  have hCbound : CrootENN <= (Croot : ENNReal) := by
    rw [← ENNReal.coe_toNNReal hCrootFinite]
    exact ENNReal.coe_le_coe.mpr (le_max_right _ _)
  obtain ⟨i, hi⟩ := hA
  have hroot := (hrelative_top hd hd1 A Y U hregular hball F0 hCF
    (U.cover.assign 0 i) (U.cover.assign_mem 0 (Nat.zero_le _) i hi)).1
  refine ⟨hroot, Finset.sup_le (fun R hR => ?_)⟩
  refine (hrelative_top hd hd1 A Y U hregular hball F0 hCF R hR).2.trans ?_
  exact mul_le_mul' (mul_le_mul' hCbound le_rfl) le_rfl

/-- A5: literal finite stopping on ONE array; eta(0) is source eta_1. -/
theorem exists_same_array_stopping_w97
    (M N : Nat) (hM : 1 <= M) (hN : 1 <= N)
    (B Ecoef : NNReal) (hB : 1 <= B) (hE : 1 <= Ecoef)
    (dCrude epsilon : Real) (hdCrude : 1 <= dCrude)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (hNlarge : epsilon ^ (-2 : Real) <= (N : Real))
    (delta : NNReal) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (rho : Nat -> NNReal) (hrho : ∀ k, k <= M -> 0 < rho k)
    (hrhoStrict : ∀ k l, k < l -> l <= M -> rho l < rho k)
    (eta : Nat -> Real) (heta : ∀ j, j <= N -> 0 < eta j)
    (hetaMono : ∀ j k, j <= k -> k <= N -> eta j <= eta k)
    (hetaTop : eta N <= epsilon)
    (hetaStep : ∀ j, j < N -> eta j <= epsilon / 2 * eta (j + 1))
    (hspanLower : delta <= rho M / rho 0)
    (hspanUpper : rho M / rho 0 <= delta ^ (epsilon ^ (2 : Nat)))
    (X : Nat -> Nat -> ENNReal)
    (hXone : ∀ k l, k < l -> l <= M -> 1 <= X k l)
    (hXfinite : ∀ k l, k < l -> l <= M -> X k l < ⊤)
    (hH1 : ∀ k l m, k < l -> l < m -> m <= M -> X k m <= (B : ENNReal) * X k l * X l m)
    (hH2 : ∀ k l, k < l -> l <= M -> X k l <= (B : ENNReal) *
      ((rho l : ENNReal) / (rho k : ENNReal)) ^ (-dCrude))
    (hH3 : X 0 M <= ((rho M : ENNReal) / (rho 0 : ENNReal)) ^ (-eta 0))
    (hH4 : ∀ a m b, a < m -> m < b -> b <= M -> X a m <= (Ecoef : ENNReal) * X a b)
    (hcalibration : (Ecoef : ENNReal) <= (delta : ENNReal) ^ (-epsilon ^ (2 : Nat) * eta 0 / 2)) :
    (∀ k, k < M -> X k M <= (B : ENNReal) ^ (N + 1) *
      (delta : ENNReal) ^ (-(dCrude + 1) * epsilon)) ∨
    ∃ a b J : Nat, a < b ∧ b <= M ∧ 1 <= J ∧ J <= N ∧
      rho b / rho a <= delta ^ epsilon ∧
      X a b <= ((rho b : ENNReal) / (rho a : ENNReal)) ^ (-eta (J - 1)) ∧
      (b < M -> X b M <= (B : ENNReal) ^ N *
        ((rho M : ENNReal) / (rho b : ENNReal)) ^ (-eta (J - 1))) ∧
      (∀ m, a < m -> m < b ->
        ((rho b : ENNReal) / (rho a : ENNReal)) ^ (1 - epsilon) <=
          (rho m : ENNReal) / (rho a : ENNReal) ->
        (rho m : ENNReal) / (rho a : ENNReal) <=
          ((rho b : ENNReal) / (rho a : ENNReal)) ^ epsilon ->
        ((rho b : ENNReal) / (rho m : ENNReal)) ^ (-eta J) < X m b) := by
  let t (k : Nat) : Real := Real.log (rho k : Real)
  let x (k l : Nat) : Real := Real.log (X k l).toReal
  let D : Real := -Real.log (delta : Real)
  let bcost : Real := Real.log (B : Real)
  let ecost : Real := Real.log (Ecoef : Real)
  have hdR : (0 : Real) < delta := hdelta
  have hdR1 : (delta : Real) < 1 := hdeltaOne
  have hD : 0 < D := neg_pos.mpr (Real.log_neg hdR hdR1)
  have hbR : (0 : Real) < B := lt_of_lt_of_le zero_lt_one hB
  have heR : (0 : Real) < Ecoef := lt_of_lt_of_le zero_lt_one hE
  have hb0 : 0 <= bcost := Real.log_nonneg hB
  have hrR (k : Nat) (hk : k <= M) : (0 : Real) < rho k := hrho k hk
  have ht (k l : Nat) (hkl : k < l) (hl : l <= M) : t l < t k :=
    Real.log_lt_log (hrR l hl) (hrhoStrict k l hkl hl)
  have hxpos (k l : Nat) (hkl : k < l) (hl : l <= M) : 0 < X k l :=
    lt_of_lt_of_le zero_lt_one (hXone k l hkl hl)
  have hlog_le {v w : ENNReal} (hv : 0 < v) (hvf : v < ⊤)
      (hw : 0 < w) (hwf : w < ⊤) :
      Real.log v.toReal <= Real.log w.toReal ↔ v <= w := by
    rw [Real.log_le_log_iff (ENNReal.toReal_pos hv.ne' hvf.ne)
      (ENNReal.toReal_pos hw.ne' hwf.ne), ENNReal.toReal_le_toReal hvf.ne hwf.ne]
  have hlog_mul {v w : ENNReal} (hv : 0 < v) (hvf : v < ⊤)
      (hw : 0 < w) (hwf : w < ⊤) :
      Real.log (v * w).toReal = Real.log v.toReal + Real.log w.toReal := by
    rw [ENNReal.toReal_mul, Real.log_mul (ENNReal.toReal_pos hv.ne' hvf.ne).ne'
      (ENNReal.toReal_pos hw.ne' hwf.ne).ne']
  have hlog_rpow {v : ENNReal} (hv : 0 < v) (hvf : v < ⊤) (q : Real) :
      Real.log (v ^ q).toReal = q * Real.log v.toReal := by
    rw [← ENNReal.toReal_rpow, Real.log_rpow (ENNReal.toReal_pos hv.ne' hvf.ne)]
  have hratioPos (k l : Nat) (hk : k <= M) (hl : l <= M) :
      0 < (rho l : ENNReal) / (rho k : ENNReal) := by
    exact ENNReal.div_pos (by exact_mod_cast (hrho l hl).ne') (by simp)
  have hratioFinite (k l : Nat) (hk : k <= M) (hl : l <= M) :
      (rho l : ENNReal) / (rho k : ENNReal) < ⊤ := by
    exact ENNReal.div_lt_top (by simp) (by exact_mod_cast (hrho k hk).ne')
  have hlog_ratio (k l : Nat) (hk : k <= M) (hl : l <= M) :
      Real.log (((rho l : ENNReal) / (rho k : ENNReal)).toReal) = t l - t k := by
    simp only [ENNReal.toReal_div, ENNReal.coe_toReal, Real.log_div
      (hrR l hl).ne' (hrR k hk).ne', t]
  have hlog_ratio_pow (k l : Nat) (hk : k <= M) (hl : l <= M) (q : Real) :
      Real.log ((((rho l : ENNReal) / (rho k : ENNReal)) ^ (-q)).toReal) =
        q * (t k - t l) := by
    rw [hlog_rpow (hratioPos k l hk hl) (hratioFinite k l hk hl), hlog_ratio k l hk hl]
    ring
  have hlog_delta_pow (q : Real) : Real.log (((delta : ENNReal) ^ q).toReal) = -q * D := by
    rw [hlog_rpow (by exact_mod_cast hdelta) (by simp)]
    simp only [ENNReal.coe_toReal, D]
    ring
  have hspan : epsilon ^ 2 * D <= t 0 - t M ∧ t 0 - t M <= D := by
    have hlo : (delta : Real) <= (rho M : Real) / rho 0 := by exact_mod_cast hspanLower
    have hhi : (rho M : Real) / rho 0 <= (delta : Real) ^ (epsilon ^ (2 : Nat)) := by
      exact_mod_cast hspanUpper
    have hlo' := Real.log_le_log hdR hlo
    have hhi' := Real.log_le_log (div_pos (hrR M le_rfl) (hrR 0 (Nat.zero_le _))) hhi
    rw [Real.log_div (hrR M le_rfl).ne' (hrR 0 (Nat.zero_le _)).ne'] at hlo' hhi'
    rw [Real.log_rpow hdR] at hhi'
    dsimp [t, D]
    constructor <;> nlinarith
  have h1 (k l m : Nat) (hkl : k < l) (hlm : l < m) (hm : m <= M) :
      x k m <= bcost + x k l + x l m := by
    have hpB : (0 : ENNReal) < B := by exact_mod_cast hbR
    have hfkl := hXfinite k l hkl (hlm.le.trans hm)
    have hflm := hXfinite l m hlm hm
    have h := (hlog_le (hxpos k m (hkl.trans hlm) hm) (hXfinite k m (hkl.trans hlm) hm)
      (ENNReal.mul_pos (ENNReal.mul_pos hpB.ne' (hxpos k l hkl (hlm.le.trans hm)).ne').ne'
        (hxpos l m hlm hm).ne') (by finiteness)).mpr (hH1 k l m hkl hlm hm)
    rw [hlog_mul (ENNReal.mul_pos hpB.ne' (hxpos k l hkl (hlm.le.trans hm)).ne')
      (by finiteness) (hxpos l m hlm hm) (hXfinite l m hlm hm),
      hlog_mul hpB (by simp) (hxpos k l hkl (hlm.le.trans hm))
        (hXfinite k l hkl (hlm.le.trans hm))] at h
    exact h
  have h2 (k l : Nat) (hkl : k < l) (hl : l <= M) :
      x k l <= bcost + dCrude * (t k - t l) := by
    have hpB : (0 : ENNReal) < B := by exact_mod_cast hbR
    have hrp : 0 < ((rho l : ENNReal) / (rho k : ENNReal)) ^ (-dCrude) :=
      ENNReal.rpow_pos (hratioPos k l (hkl.le.trans hl) hl)
        (hratioFinite k l (hkl.le.trans hl) hl).ne
    have hfinite : ((rho l : ENNReal) / (rho k : ENNReal)) ^ (-dCrude) < ⊤ := by
      exact lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
        (hratioPos k l (hkl.le.trans hl) hl).ne' (hratioFinite k l (hkl.le.trans hl) hl).ne)
    have h := (hlog_le (hxpos k l hkl hl) (hXfinite k l hkl hl)
      (ENNReal.mul_pos hpB.ne' hrp.ne') (by finiteness)).mpr (hH2 k l hkl hl)
    rw [hlog_mul hpB (by simp) hrp hfinite, hlog_ratio_pow k l (hkl.le.trans hl) hl] at h
    exact h
  have h3 : x 0 M <= eta 0 * (t 0 - t M) := by
    have hp : 0 < ((rho M : ENNReal) / (rho 0 : ENNReal)) ^ (-eta 0) :=
      ENNReal.rpow_pos (hratioPos 0 M (Nat.zero_le _) le_rfl)
        (hratioFinite 0 M (Nat.zero_le _) le_rfl).ne
    have hf : ((rho M : ENNReal) / (rho 0 : ENNReal)) ^ (-eta 0) < ⊤ :=
      lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
        (hratioPos 0 M (Nat.zero_le _) le_rfl).ne' (hratioFinite 0 M (Nat.zero_le _) le_rfl).ne)
    have h := (hlog_le (hxpos 0 M hM le_rfl) (hXfinite 0 M hM le_rfl) hp hf).mpr hH3
    rwa [hlog_ratio_pow 0 M (Nat.zero_le _) le_rfl] at h
  have h4 (a m b : Nat) (ham : a < m) (hmb : m < b) (hb : b <= M) :
      x a m <= ecost + x a b := by
    have hpE : (0 : ENNReal) < Ecoef := by exact_mod_cast heR
    have hp := hxpos a b (ham.trans hmb) hb
    have hf := hXfinite a b (ham.trans hmb) hb
    have h := (hlog_le (hxpos a m ham (hmb.le.trans hb))
      (hXfinite a m ham (hmb.le.trans hb))
      (ENNReal.mul_pos hpE.ne' hp.ne') (by finiteness)).mpr (hH4 a m b ham hmb hb)
    rw [hlog_mul hpE (by simp) hp hf] at h
    exact h
  have hcal : ecost <= epsilon ^ 2 * eta 0 / 2 * D := by
    have hpD : (0 : ENNReal) < delta := by exact_mod_cast hdelta
    have hf : (delta : ENNReal) ^ (-epsilon ^ (2 : Nat) * eta 0 / 2) < ⊤ :=
      lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero hpD.ne' (by simp))
    have h := (hlog_le (by exact_mod_cast heR) (by simp)
      (ENNReal.rpow_pos hpD (by simp)) hf).mpr hcalibration
    rw [hlog_delta_pow] at h
    simp only [ENNReal.coe_toReal] at h
    dsimp [ecost]
    nlinarith only [h]
  have hengine :
      (∀ k, k < M -> x k M <= ((N : Real) + 1) * bcost + (dCrude + 1) * epsilon * D) ∨
      ∃ a b J : Nat, a < b ∧ b <= M ∧ 1 <= J ∧ J <= N ∧
        epsilon * D <= t a - t b ∧
        x a b <= eta (J - 1) * (t a - t b) ∧
        (b < M -> x b M <= (N : Real) * bcost + eta (J - 1) * (t b - t M)) ∧
        (∀ m, a < m -> m < b ->
          epsilon * (t a - t b) <= t a - t m ->
          t a - t m <= (1 - epsilon) * (t a - t b) ->
          eta J * (t m - t b) < x m b) := by
    let Part (J : Nat) (c : Nat -> Nat) : Prop :=
      1 <= J ∧ J <= N ∧ c 0 = 0 ∧ c J = M ∧
      (∀ i, i <= J -> c i <= M) ∧
      (∀ i, i < J -> c i < c (i + 1) ∧
        epsilon ^ 2 * D <= t (c i) - t (c (i + 1)) ∧
        x (c i) (c (i + 1)) <= eta (J - 1) * (t (c i) - t (c (i + 1))))
    have hstart : ∃ c, Part 1 c := by
      refine ⟨fun i => if i = 0 then 0 else M, le_rfl, hN, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro i hi
        dsimp only
        split_ifs <;> omega
      · intro i hi
        have hi0 : i = 0 := by omega
        subst i
        simpa using And.intro (show 0 < M by omega) (And.intro hspan.1 h3)
    let J := Nat.findGreatest (fun j => ∃ c, Part j c) N
    obtain ⟨c, hc⟩ := Nat.findGreatest_spec (P := fun j => ∃ c, Part j c) hN hstart
    change Part J c at hc
    obtain ⟨hJ, hJN, hc0, hcJ, hcM, hcp⟩ := hc
    have hmax (K : Nat) (hKN : K <= N) (c' : Nat -> Nat) (hc' : Part K c') : K <= J :=
      Nat.le_findGreatest hKN ⟨c', hc'⟩
    have hcmono (i j : Nat) (hij : i <= j) (hj : j <= J) : c i <= c j := by
      induction j, hij using Nat.le_induction with
      | base => exact le_rfl
      | succ j hij ih =>
        exact (ih (by omega)).trans (hcp j (by omega)).1.le
    have hct (i : Nat) (hi : i <= J) : t (c i) - t M <= D := by
      have hzero : 0 <= c i := Nat.zero_le _
      have hle : t (c i) <= t 0 := by
        rcases eq_or_lt_of_le hzero with hz | hz
        · simp only [← hz, le_refl]
        · exact (ht 0 (c i) hz (hcM i hi)).le
      linarith [hspan.2]
    have hetaJ : 0 < eta (J - 1) := heta (J - 1) (by omega)
    have hetaJE : eta (J - 1) <= epsilon :=
      (hetaMono (J - 1) N (by omega) le_rfl).trans hetaTop
    have htail : ∀ n i : Nat, i + n = J -> 0 < n ->
        x (c i) M <= (n : Real) * bcost + eta (J - 1) * (t (c i) - t M) := by
      intro n
      induction n with
      | zero => intro i hi hn; omega
      | succ n ih =>
        intro i hi hn
        have hiJ : i < J := by omega
        by_cases hn0 : n = 0
        · subst n
          have hei : c (i + 1) = M := by rw [show i + 1 = J by omega, hcJ]
          have hentry := (hcp i hiJ).2.2
          rw [hei] at hentry
          norm_num only [Nat.cast_one, one_mul]
          linarith only [hentry, hb0]
        · have hin : i + 1 + n = J := by omega
          have hrec := ih (i + 1) hin (by omega)
          have hnext : c (i + 1) < M := by
            calc c (i + 1) < c (i + 1 + 1) := (hcp (i + 1) (by omega)).1
                 _ <= c J := hcmono _ _ (by omega) le_rfl
                 _ = M := hcJ
          have hcomp := h1 (c i) (c (i + 1)) M (hcp i hiJ).1 hnext le_rfl
          have hentry := (hcp i hiJ).2.2
          simp only [Nat.cast_succ]
          nlinarith only [hcomp, hentry, hrec]
    by_cases hlong : ∃ j, j < J ∧ epsilon * D <= t (c j) - t (c (j + 1))
    · obtain ⟨j, hj, hjlong⟩ := hlong
      have hcount : (J : Real) * epsilon ^ 2 * D + (epsilon - epsilon ^ 2) * D <= D := by
        have hsum := Finset.sum_le_sum (s := Finset.range J)
          (f := fun i => epsilon ^ 2 * D + if i = j then (epsilon - epsilon ^ 2) * D else 0)
          (g := fun i => t (c i) - t (c (i + 1))) (by
            intro i hi
            have hiJ := Finset.mem_range.mp hi
            by_cases hij : i = j
            · subst i
              simp only [ite_true]
              nlinarith only [hjlong]
            · simp only [if_neg hij, add_zero]
              exact (hcp i hiJ).2.1)
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hj),
          Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_range_sub', hc0, hcJ] at hsum
        nlinarith only [hsum, hspan.2]
      have hJltN : J < N := by
        have hep2 : 0 < epsilon ^ (2 : Nat) := pow_pos hepsilon _
        have hlarge : 1 <= (N : Real) * epsilon ^ (2 : Nat) := by
          have hn := hNlarge
          rw [Real.rpow_neg hepsilon.le, Real.rpow_two] at hn
          have hmul := mul_le_mul_of_nonneg_right hn hep2.le
          rwa [inv_mul_cancel₀ hep2.ne'] at hmul
        have hepSub : 0 < epsilon - epsilon ^ (2 : Nat) := by
          nlinarith only [hepsilon, hepsilonHalf]
        have hstrict : (J : Real) * epsilon ^ (2 : Nat) < 1 := by
          have hpos := mul_pos hepSub hD
          nlinarith only [hcount, hpos, hD]
        exact_mod_cast (show (J : Real) < N by nlinarith only [hstrict, hlarge, hep2])
      have hfail : ∀ m, c j < m -> m < c (j + 1) ->
          epsilon * (t (c j) - t (c (j + 1))) <= t (c j) - t m ->
          t (c j) - t m <= (1 - epsilon) * (t (c j) - t (c (j + 1))) ->
          eta J * (t m - t (c (j + 1))) < x m (c (j + 1)) := by
        intro m hjm hmj hwinL hwinU
        by_contra hnot
        have hsecond : x m (c (j + 1)) <= eta J * (t m - t (c (j + 1))) :=
          le_of_not_gt hnot
        have hlen : 0 < t (c j) - t (c (j + 1)) :=
          sub_pos.mpr (ht (c j) (c (j + 1)) (hcp j hj).1 (hcM (j + 1) (by omega)))
        have hetaNext : 0 < eta J := heta J hJN
        have hgap := hetaStep (J - 1) (by omega)
        rw [Nat.sub_add_cancel hJ] at hgap
        have he0 := hetaMono 0 J (Nat.zero_le _) hJN
        have heold := hetaMono (J - 1) J (by omega) hJN
        have hcal' : ecost <= epsilon / 2 * eta J * (t (c j) - t (c (j + 1))) := by
          calc ecost <= epsilon ^ 2 * eta 0 / 2 * D := hcal
               _ <= epsilon ^ 2 * eta J / 2 * D := by gcongr
               _ = epsilon / 2 * eta J * (epsilon * D) := by ring
               _ <= epsilon / 2 * eta J * (t (c j) - t (c (j + 1))) := by gcongr
        have hfirst : x (c j) m <= eta J * (t (c j) - t m) := by
          have hpref := h4 (c j) m (c (j + 1)) hjm hmj (hcM (j + 1) (by omega))
          have hentry := (hcp j hj).2.2
          have hgap' := mul_le_mul_of_nonneg_right hgap hlen.le
          have hwin' := mul_le_mul_of_nonneg_left hwinL hetaNext.le
          nlinarith only [hpref, hentry, hgap', hwin', hcal']
        have hnewL : epsilon ^ 2 * D <= t (c j) - t m := by
          have h := mul_le_mul_of_nonneg_left hjlong hepsilon.le
          nlinarith only [h, hwinL]
        have hnewR : epsilon ^ 2 * D <= t m - t (c (j + 1)) := by
          have h := mul_le_mul_of_nonneg_left hjlong hepsilon.le
          nlinarith only [h, hwinU]
        let c' (i : Nat) := if i <= j then c i else if i = j + 1 then m else c (i - 1)
        have hleft (i : Nat) (hi : i <= j) : c' i = c i := by simp [c', hi]
        have hmid : c' (j + 1) = m := by simp [c']
        have hright (i : Nat) (hi : j + 1 < i) : c' i = c (i - 1) := by
          simp [c', show ¬ i <= j by omega, show i ≠ j + 1 by omega]
        have hnew : Part (J + 1) c' := by
          refine ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩
          · rw [hleft 0 (Nat.zero_le _), hc0]
          · rw [hright (J + 1) (by omega), Nat.add_sub_cancel, hcJ]
          · intro i hi
            by_cases hij : i <= j
            · rw [hleft i hij]
              exact hcM i (by omega)
            · by_cases hi1 : i = j + 1
              · subst i
                rw [hmid]
                exact hmj.le.trans (hcM (j + 1) (by omega))
              · rw [hright i (by omega)]
                exact hcM (i - 1) (by omega)
          · intro i hi
            simp only [Nat.add_sub_cancel]
            by_cases hij : i < j
            · rw [hleft i hij.le, hleft (i + 1) (by omega)]
              obtain ⟨hp, hl, hx⟩ := hcp i (by omega)
              refine ⟨hp, hl, hx.trans ?_⟩
              exact mul_le_mul_of_nonneg_right heold
                (sub_nonneg.mpr (ht (c i) (c (i + 1)) hp (hcM (i + 1) (by omega))).le)
            · by_cases hijEq : i = j
              · subst i
                rw [hleft j le_rfl, hmid]
                exact ⟨hjm, hnewL, hfirst⟩
              · by_cases hi1 : i = j + 1
                · subst i
                  rw [hmid, hright (j + 1 + 1) (by omega)]
                  simp only [Nat.add_sub_cancel]
                  exact ⟨hmj, hnewR, hsecond⟩
                · rw [hright i (by omega), hright (i + 1) (by omega), Nat.add_sub_cancel]
                  have hei : i - 1 + 1 = i := by omega
                  obtain ⟨hp, hl, hx⟩ := hcp (i - 1) (by omega)
                  rw [hei] at hp hl hx
                  refine ⟨hp, hl, hx.trans ?_⟩
                  exact mul_le_mul_of_nonneg_right heold
                    (sub_nonneg.mpr (ht (c (i - 1)) (c i) hp (hcM i (by omega))).le)
        have hbad := hmax (J + 1) (by omega) c' hnew
        omega
      right
      refine ⟨c j, c (j + 1), J, (hcp j hj).1, hcM (j + 1) (by omega),
        hJ, hJN, hjlong, (hcp j hj).2.2, ?_, hfail⟩
      intro hb
      have hj1 : j + 1 < J := by
        by_contra h
        have he : j + 1 = J := by omega
        rw [he, hcJ] at hb
        omega
      have h := htail (J - (j + 1)) (j + 1) (by omega) (by omega)
      have hn : ((J - (j + 1) : Nat) : Real) <= N := by exact_mod_cast (show J - (j + 1) <= N by omega)
      nlinarith only [h, mul_le_mul_of_nonneg_right hn hb0]
    · left
      intro k hk
      let j := Nat.findGreatest (fun i => c i <= k) J
      have hjc : c j <= k := Nat.findGreatest_spec (P := fun i => c i <= k)
        (Nat.zero_le J) (by simpa only [hc0] using Nat.zero_le k)
      have hjle : j <= J := Nat.findGreatest_le _
      have hj : j < J := by
        by_contra h
        have he : j = J := by omega
        rw [he, hcJ] at hjc
        omega
      have hkc : k < c (j + 1) := by
        by_contra h
        have hnext := Nat.le_findGreatest (P := fun i => c i <= k)
          (show j + 1 <= J by omega) (le_of_not_gt h)
        change j + 1 <= j at hnext
        omega
      have hshort : t (c j) - t (c (j + 1)) < epsilon * D := by
        by_contra h
        exact hlong ⟨j, hj, le_of_not_gt h⟩
      have hpartial : t k - t (c (j + 1)) <= epsilon * D := by
        have htk : t k <= t (c j) := by
          rcases eq_or_lt_of_le hjc with he | he
          · rw [he]
          · exact (ht (c j) k he hk.le).le
        linarith
      have hcrude := h2 k (c (j + 1)) hkc (hcM (j + 1) (by omega))
      have hcrude' : x k (c (j + 1)) <= bcost + dCrude * epsilon * D := by
        have h := mul_le_mul_of_nonneg_left hpartial (by linarith : 0 <= dCrude)
        nlinarith only [hcrude, h]
      by_cases hend : j + 1 = J
      · rw [hend, hcJ] at hcrude'
        have hnb : 0 <= (N : Real) * bcost := mul_nonneg (Nat.cast_nonneg _) hb0
        have hed : 0 <= epsilon * D := (mul_pos hepsilon hD).le
        nlinarith only [hcrude', hnb, hed]
      · have hj1 : j + 1 < J := by omega
        have hnext : c (j + 1) < M := by
          calc c (j + 1) < c (j + 1 + 1) := (hcp (j + 1) hj1).1
               _ <= c J := hcmono _ _ (by omega) le_rfl
               _ = M := hcJ
        have hsub := htail (J - (j + 1)) (j + 1) (by omega) (by omega)
        have hcomp := h1 k (c (j + 1)) M hkc hnext le_rfl
        have hcost : ((J - (j + 1) : Nat) : Real) + 2 <= (N : Real) + 1 := by
          exact_mod_cast (show J - (j + 1) + 2 <= N + 1 by omega)
        have hcost' := mul_le_mul_of_nonneg_right hcost hb0
        have hspan' := hct (j + 1) (by omega)
        have hetaCost : eta (J - 1) * (t (c (j + 1)) - t M) <= epsilon * D := by
          calc eta (J - 1) * (t (c (j + 1)) - t M) <= eta (J - 1) * D := by gcongr
               _ <= epsilon * D := by gcongr
        nlinarith only [hcomp, hcrude', hsub, hcost', hetaCost]
  have hrpowPos (k l : Nat) (hk : k <= M) (hl : l <= M) (q : Real) :
      0 < ((rho l : ENNReal) / (rho k : ENNReal)) ^ q :=
    ENNReal.rpow_pos (hratioPos k l hk hl) (hratioFinite k l hk hl).ne
  have hrpowFinite (k l : Nat) (hk : k <= M) (hl : l <= M) (q : Real) :
      ((rho l : ENNReal) / (rho k : ENNReal)) ^ q < ⊤ :=
    lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
      (hratioPos k l hk hl).ne' (hratioFinite k l hk hl).ne)
  have hBpos (n : Nat) : (0 : ENNReal) < (B : ENNReal) ^ n := by
    have hb : (0 : ENNReal) < B := by exact_mod_cast hbR
    exact pos_iff_ne_zero.mpr (pow_ne_zero n hb.ne')
  have hBlog (n : Nat) : Real.log (((B : ENNReal) ^ n).toReal) = (n : Real) * bcost := by
    rw [ENNReal.toReal_pow, Real.log_pow]
    rfl
  rcases hengine with hall | ⟨a, b, J, hab, hb, hJ, hJN, hlong, hmid, htail, hlow⟩
  · left
    intro k hk
    have hdpos : (0 : ENNReal) < delta := by exact_mod_cast hdelta
    have hp : 0 < (delta : ENNReal) ^ (-(dCrude + 1) * epsilon) :=
      ENNReal.rpow_pos hdpos (by simp)
    have hf : (delta : ENNReal) ^ (-(dCrude + 1) * epsilon) < ⊤ :=
      lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero hdpos.ne' (by simp))
    apply (hlog_le (hxpos k M hk le_rfl) (hXfinite k M hk le_rfl)
      (ENNReal.mul_pos (hBpos (N + 1)).ne' hp.ne') (by finiteness)).mp
    rw [hlog_mul (hBpos (N + 1)) (by finiteness) hp hf, hBlog, hlog_delta_pow]
    have h := hall k hk
    simp only [Nat.cast_add, Nat.cast_one]
    dsimp [x] at h
    nlinarith only [h]
  · right
    have ha : a <= M := hab.le.trans hb
    refine ⟨a, b, J, hab, hb, hJ, hJN, ?_, ?_, ?_, ?_⟩
    · apply NNReal.coe_le_coe.mp
      change (rho b : Real) / (rho a : Real) <= (delta : Real) ^ epsilon
      apply (Real.log_le_log_iff (div_pos (hrR b hb) (hrR a ha))
        (Real.rpow_pos_of_pos hdR epsilon)).mp
      rw [Real.log_div (hrR b hb).ne' (hrR a ha).ne', Real.log_rpow hdR]
      dsimp [t, D] at hlong
      nlinarith only [hlong]
    · apply (hlog_le (hxpos a b hab hb) (hXfinite a b hab hb)
        (hrpowPos a b ha hb _) (hrpowFinite a b ha hb _)).mp
      rwa [hlog_ratio_pow a b ha hb]
    · intro hbM
      apply (hlog_le (hxpos b M hbM le_rfl) (hXfinite b M hbM le_rfl)
        (ENNReal.mul_pos (hBpos N).ne' (hrpowPos b M hb le_rfl _).ne') (by
          exact ENNReal.mul_lt_top (by finiteness) (hrpowFinite b M hb le_rfl _))).mp
      rw [hlog_mul (hBpos N) (by finiteness) (hrpowPos b M hb le_rfl _)
        (hrpowFinite b M hb le_rfl _), hBlog, hlog_ratio_pow b M hb le_rfl]
      exact htail hbM
    · intro m ham hmb hwinL hwinU
      have hm : m <= M := hmb.le.trans hb
      have hwL := (hlog_le (hrpowPos a b ha hb (1 - epsilon))
        (hrpowFinite a b ha hb (1 - epsilon)) (hratioPos a m ha hm)
        (hratioFinite a m ha hm)).mpr hwinL
      have hwU := (hlog_le (hratioPos a m ha hm) (hratioFinite a m ha hm)
        (hrpowPos a b ha hb epsilon) (hrpowFinite a b ha hb epsilon)).mpr hwinU
      rw [hlog_rpow (hratioPos a b ha hb) (hratioFinite a b ha hb),
        hlog_ratio a b ha hb, hlog_ratio a m ha hm] at hwL hwU
      have hstrict := hlow m ham hmb (by nlinarith only [hwU]) (by nlinarith only [hwL])
      apply lt_of_not_ge
      intro hbad
      have h := (hlog_le (hxpos m b hmb hb) (hXfinite m b hmb hb)
        (hrpowPos m b hm hb _) (hrpowFinite m b hm hb _)).mpr hbad
      rw [hlog_ratio_pow m b hm hb] at h
      exact (not_lt_of_ge h) hstrict

/-- A6 constructs P2 once at M*M before stopping; the visible tower is its
M-spaced restriction on the SAME final A, with exact body/radius identities. -/
theorem exists_extended_regularized_stopping_w97
    (hdim : Module.finrank Real E = 3)
    {p : Params} {beta gammaZero xiMin : Real} {xi : Fin (p.N + 1) -> Real}
    {M : Nat} (hp : SourcePassNumericsW95 p beta gammaZero xi xiMin M)
    (Cbase : NNReal) (hCbase : 1 <= Cbase) :
    ∃ (Ccan Ctw Ccell BF Cprep : NNReal) (Kprep : Nat) (ePrep : Real) (delta0 : NNReal),
      1 <= Ccan ∧ 1 <= Ctw ∧ 1 <= Ccell ∧ 1 <= BF ∧ 1 <= Cprep ∧ 1 <= Kprep ∧
      0 < ePrep ∧ ePrep < p.η 0 / 100 ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ {delta : NNReal}, 0 < delta -> delta < delta0 ->
      ∀ {iota : Type uI} [DecidableEq iota] (F : Finset iota) (Y : iota -> ShadedTube delta E),
        F.Nonempty -> (∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        (∀ i ∈ F, centredTubeW94 (Y i).toTube) ->
        lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) Cbase ->
        (delta : ENNReal) ^ ePrep <= fullness' F (fun i => (Y i).toShadedBody) ->
        frostmanConstIn F (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
          (delta : ENNReal) ^ (-ePrep) ->
        ∃ (A : Finset iota)
          (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
          (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan),
          A.Nonempty ∧ A ⊆ F ∧
          towerPreparationRetainedW95 delta Cprep Kprep * (∑ i ∈ F, volume (Y i).shade) <=
            ∑ i ∈ A, volume (Y i).shade ∧
          Nonempty (SourceRegularizedWorkingTowerW95 U Ctw Ccell) ∧
          Nonempty (SourceRegularizedWorkingTowerW95 Uext Ctw Ccell) ∧
          (∀ k, k <= M -> U.cover.indexSet k = Uext.cover.indexSet (k * M)) ∧
          (∀ k, k <= M -> U.cover.assign k = Uext.cover.assign (k * M)) ∧
          (∀ k, k <= M -> Tube.gridScale delta M k = Tube.gridScale delta (M * M) (k * M)) ∧
          (∀ k, k <= M -> ∀ R,
            HEq (U.cover.tube k R) (Uext.cover.tube (k * M) R)) ∧
          (actualEveryScaleW95 U p.ε p.N BF ∨ Nonempty (ActualSourceDividingBlockW95 U p BF)) := by
  have hgrid (delta : NNReal) (k : Nat) :
      Tube.gridScale delta (M * M) (k * M) = Tube.gridScale delta M k := by
    unfold Tube.gridScale
    congr 1
    push_cast
    have hM0 : (M : Real) ≠ 0 := by exact_mod_cast (show M ≠ 0 by have := hp.M_pos; omega)
    field_simp
  have hcastBody {r s : NNReal} (h : r = s) (T : Tube r E) :
      (h ▸ T : Tube s E).toConvexSpaceBody = T.toConvexSpaceBody := by
    cases h
    rfl
  have hcastHEq {r s : NNReal} (h : r = s) (T : Tube r E) :
      HEq (h ▸ T : Tube s E) T := by
    cases h
    rfl
  have hcastInj {r s : NNReal} (h : r = s) (T V : Tube r E) :
      (h ▸ T : Tube s E) = (h ▸ V : Tube s E) -> T = V := by
    cases h
    exact id
  have hrestrict {delta : NNReal} {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E) (Ccan Ctw Ccell : NNReal)
      (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan)
      (hext : SourceRegularizedWorkingTowerW95 Uext Ctw Ccell) :
      ∃ U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan,
        Nonempty (SourceRegularizedWorkingTowerW95 U Ctw Ccell) ∧
        (∀ k, k <= M -> U.cover.indexSet k = Uext.cover.indexSet (k * M)) ∧
        (∀ k, k <= M -> U.cover.assign k = Uext.cover.assign (k * M)) ∧
        (∀ k, k <= M -> Tube.gridScale delta M k = Tube.gridScale delta (M * M) (k * M)) ∧
        (∀ k, k <= M -> ∀ R, HEq (U.cover.tube k R) (Uext.cover.tube (k * M) R)) := by
    have hm (k : Nat) (hk : k <= M) : k * M <= M * M := Nat.mul_le_mul_right M hk
    have hlt (k l : Nat) (hkl : k < l) : k * M < l * M :=
      Nat.mul_lt_mul_of_pos_right hkl (by have := hp.M_pos; omega)
    let tubes (k : Nat) (R : iota) : Tube (Tube.gridScale delta M k) E :=
      hgrid delta k ▸ Uext.cover.tube (k * M) R
    have htube (k : Nat) (R : iota) :
        (tubes k R).toConvexSpaceBody = (Uext.cover.tube (k * M) R).toConvexSpaceBody :=
      hcastBody (hgrid delta k) _
    have hcarrier (k : Nat) (R : iota) :
        (tubes k R).carrier = (Uext.cover.tube (k * M) R).carrier :=
      congrArg (fun V : ConvexSpaceBody E => V.carrier) (htube k R)
    let G : Tube.GridCoverSystem A (fun i => (Y i).toTube) M := {
      indexSet := fun k => Uext.cover.indexSet (k * M)
      assign := fun k => Uext.cover.assign (k * M)
      tube := tubes
      assign_mem := fun k hk i hi => Uext.cover.assign_mem (k * M) (hm k hk) i hi
      le_tube_assign := by
        intro k hk i hi
        rw [htube]
        exact Uext.cover.le_tube_assign (k * M) (hm k hk) i hi
      nested := by
        intro k hk i hi j hj hij
        exact Uext.cover.assign_eq_of_le (Nat.mul_le_mul_right M (Nat.le_succ k))
          (hm (k + 1) hk) hi hj hij
      tube_nested := by
        intro k hk i hi
        rw [htube, htube]
        exact Uext.cover.toChain.tube_assign_le (Nat.mul_le_mul_right M (Nat.le_succ k))
          (hm (k + 1) hk) hi }
    let U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan := {
      cover := G
      branchingN := fun k => Uext.branchingN (k * M)
      tube_injOn := by
        intro k hk R hR S hS hRS
        apply Uext.tube_injOn (k * M) (hm k hk) hR hS
        exact hcastInj (hgrid delta k) _ _ hRS
      boundedOverlap := by
        intro k hk V
        let Vext : Tube (Tube.gridScale delta (M * M) (k * M)) E := (hgrid delta k).symm ▸ V
        have hV : Vext.toConvexSpaceBody = V.toConvexSpaceBody := hcastBody (hgrid delta k).symm V
        have h := Uext.boundedOverlap (k * M) (hm k hk) Vext
        change (((Uext.cover.indexSet (k * M)).filter (fun R => ∃ i ∈ A,
          (Y i).toConvexSpaceBody <= (tubes k R).toConvexSpaceBody ∧
          (Y i).toConvexSpaceBody <= V.toConvexSpaceBody)).card : NNReal) <= Ccan
        simpa only [htube, hV] using h
      card_class_le := fun k hk R hR => Uext.card_class_le (k * M) (hm k hk) R hR
      le_card_class := fun k hk R hR => Uext.le_card_class (k * M) (hm k hk) R hR }
    have hrel (k l : Nat) (R : iota) :
        actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l R =
          actualRelativeFrostmanW95 A Uext.cover.assign Uext.cover.tube (k * M) (l * M) R := by
      simp only [actualRelativeFrostmanW95, actualDescendantsW95, U, G, htube]
    have hreg : SourceRegularizedWorkingTowerW95 U Ctw Ccell := {
      surjective := fun k hk => hext.surjective (k * M) (hm k hk)
      bottom_index := hext.bottom_index
      bottom_assign := hext.bottom_assign
      bottom_tube := by
        intro i hi
        change (tubes M i).toConvexSpaceBody = (Y i).toConvexSpaceBody
        rw [htube]
        exact hext.bottom_tube i hi
      nice := by
        intro k hk V
        let Vext : Tube (Tube.gridScale delta (M * M) (k * M)) E := (hgrid delta k).symm ▸ V
        have hV : Vext.toConvexSpaceBody = V.toConvexSpaceBody := hcastBody (hgrid delta k).symm V
        have h := hext.nice (k * M) (hm k hk) Vext
        change ((Uext.cover.indexSet (k * M)).filter (fun R => ∃ i ∈ A,
          (Y i).toConvexSpaceBody <= (tubes k R).toConvexSpaceBody ∧
          (Y i).toConvexSpaceBody <= V.toConvexSpaceBody)).card <= _
        simpa only [htube, hV] using h
      parent_ball := by
        intro k hk R hR
        change (tubes k R).carrier ⊆ Metric.closedBall 0 2
        rw [hcarrier]
        exact hext.parent_ball (k * M) (hm k hk) R hR
      parent_line_ed := by
        intro k hk
        have h := hext.parent_line_ed (k * M) (hm k hk)
        simpa only [lineEssentiallyDistinctW94, liesInFiveDeltaLineTubeW94, U, G, hcarrier, hgrid] using h
      geometric_count := by
        intro k hk R hR
        have h := hext.geometric_count (k * M) (hm k hk) R hR
        simpa only [exactTubeCellW87, U, G, htube] using h
      countBand := fun k l => hext.countBand (k * M) (l * M)
      countBand_pos := fun k l hkl hl => hext.countBand_pos _ _ (hlt k l hkl) (hm l hl)
      count_lower := fun k l hkl hl R hR => hext.count_lower _ _ (hlt k l hkl) (hm l hl) R hR
      count_upper := fun k l hkl hl R hR => hext.count_upper _ _ (hlt k l hkl) (hm l hl) R hR
      frostmanBand := fun k l => hext.frostmanBand (k * M) (l * M)
      frostmanBand_pos := fun k l hkl hl => hext.frostmanBand_pos _ _ (hlt k l hkl) (hm l hl)
      frostmanBand_finite := fun k l hkl hl => hext.frostmanBand_finite _ _ (hlt k l hkl) (hm l hl)
      frostman_lower := by
        intro k l hkl hl R hR
        rw [hrel]
        exact hext.frostman_lower _ _ (hlt k l hkl) (hm l hl) R hR
      frostman_upper := by
        intro k l hkl hl R hR
        rw [hrel]
        exact hext.frostman_upper _ _ (hlt k l hkl) (hm l hl) R hR }
    exact ⟨U, ⟨hreg⟩, fun _ _ => rfl, fun _ _ => rfl, fun k _ => (hgrid delta k).symm,
      fun k _ R => hcastHEq (hgrid delta k) _⟩
  obtain ⟨Ccan, Ctw, Ccell, Cprep, Kprep, deltaPrep,
    hCcan, hCtw, hCcell, hCprep, hKprep, hdeltaPrep, hdeltaPrep1, htower⟩ :=
    exists_actual_source_regularized_working_tower_w95.{uE,uI} hdim (M * M)
      (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by have := hp.M_pos; omega)
        (by have := hp.M_pos; omega))) Cbase hCbase
  obtain ⟨Ctwo, hCtwo, htwo⟩ := actual_relative_cf_composition_w97.{uE,uI} (E := E)
  obtain ⟨Cvol, hCvol, hcrude⟩ := actual_relative_cf_crude_and_prefix_w97.{uE,uI} hdim
  obtain ⟨Croot, hCroot, hroot⟩ := actual_top_relative_cf_w97.{uE,uI} hdim
  let BF : NNReal := max Cvol (2 * Ctwo ^ 2)
  have hBF : 1 <= BF := hCvol.trans (le_max_left _ _)
  let ePrep : Real := p.η 0 / 200
  have hePrep : 0 < ePrep := div_pos (hp.zeta_pos 0 (Nat.zero_le _)) (by norm_num)
  have hePrepSmall : ePrep < p.η 0 / 100 := by
    dsimp [ePrep]
    linarith [hp.zeta_pos 0 (Nat.zero_le _)]
  have hprepCost : Filter.Eventually (fun delta : NNReal => (delta : ENNReal) ^ ePrep <=
      towerPreparationRetainedW95 delta Cprep Kprep) (nhdsWithin 0 (Set.Ioi 0)) := by
    filter_upwards [ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg (half_pos hePrep) Kprep,
      eventually_finite_const_le_rpow_neg (c := (Cprep : ENNReal) * 2 ^ Kprep)
        (by finiteness) (half_pos hePrep),
      eventually_le_nhdsGT (c := (1 : NNReal)) one_pos,
      self_mem_nhdsWithin] with delta hpoly hconst hd1 hd0
    have hdpos : 0 < delta := hd0
    have hdR : (0 : Real) < delta := hdpos
    let t : Real := Real.logb 2 (1 / (delta : Real))
    have ht0 : 0 <= t := by
      apply div_nonneg (Real.log_nonneg ?_) (Real.log_nonneg (by norm_num))
      exact (le_div_iff₀ hdR).mpr (by simpa only [one_mul] using (show (delta : Real) <= 1 from hd1))
    have hbase : ENNReal.ofReal (2 + t) <= 2 * ENNReal.ofReal (1 + t) := by
      have h : 2 + t <= 2 * (1 + t) := by linarith
      simpa only [ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 2), ENNReal.ofReal_ofNat] using
        ENNReal.ofReal_le_ofReal h
    have hden : (Cprep : ENNReal) * ENNReal.ofReal ((2 + t) ^ Kprep) <=
        (delta : ENNReal) ^ (-ePrep) := by
      rw [ENNReal.ofReal_pow (by linarith : 0 <= 2 + t)]
      calc
        (Cprep : ENNReal) * ENNReal.ofReal (2 + t) ^ Kprep <=
            (Cprep : ENNReal) * (2 * ENNReal.ofReal (1 + t)) ^ Kprep := by gcongr
        _ = ((Cprep : ENNReal) * 2 ^ Kprep) * ENNReal.ofReal (1 + t) ^ Kprep := by
          rw [mul_pow]; ring
        _ <= (delta : ENNReal) ^ (-(ePrep / 2)) * (delta : ENNReal) ^ (-(ePrep / 2)) :=
          mul_le_mul' hconst hpoly
        _ = (delta : ENNReal) ^ (-ePrep) := by
          rw [← ENNReal.rpow_add _ _ (ENNReal.coe_pos.mpr hdpos).ne' ENNReal.coe_ne_top]
          congr 1
          ring
    change (delta : ENNReal) ^ ePrep <= ((Cprep : ENNReal) * ENNReal.ofReal ((2 + t) ^ Kprep))⁻¹
    calc
      (delta : ENNReal) ^ ePrep = ((delta : ENNReal) ^ (-ePrep))⁻¹ := by rw [ENNReal.rpow_neg, inv_inv]
      _ <= _ := ENNReal.inv_le_inv.mpr hden
  have hstop {delta : NNReal} (hd : 0 < delta) (hd1 : delta < 1)
      (hgridGap : delta <= (16 : NNReal) ^ (-(M : Real)))
      (hcal : (4 : ENNReal) <= (delta : ENNReal) ^ (-p.ε ^ (2 : Nat) * p.η 0 / 2))
      {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E)
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (hA : A.Nonempty) (hreg : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (hball : ∀ i ∈ A, (Y i).carrier ⊆ Metric.closedBall 0 1)
      (hCFtop : actualRelativeCFArrayW97 U 0 M <= (delta : ENNReal) ^ (-p.η 0)) :
      actualEveryScaleW95 U p.ε p.N BF ∨ Nonempty (ActualSourceDividingBlockW95 U p BF) := by
    have hMpos : 0 < M := by have := hp.M_pos; omega
    let rho := Tube.gridScale delta M
    let X := actualRelativeCFArrayW97 U
    have hrho (k : Nat) : 0 < rho k := Tube.gridScale_pos hd M k
    have hrhoE (k : Nat) : (0 : ENNReal) < rho k := ENNReal.coe_pos.mpr (hrho k)
    have hratioPos (k l : Nat) : 0 < (rho l : ENNReal) / (rho k : ENNReal) :=
      ENNReal.div_pos (hrhoE l).ne' ENNReal.coe_ne_top
    have hratioFinite (k l : Nat) : (rho l : ENNReal) / (rho k : ENNReal) < ⊤ :=
      ENNReal.div_lt_top ENNReal.coe_ne_top (hrhoE k).ne'
    have hinverse (k l : Nat) (q : Real) :
        ((rho l : ENNReal) / (rho k : ENNReal)) ^ (-q) =
          ((rho k : ENNReal) / (rho l : ENNReal)) ^ q := by
      rw [ENNReal.rpow_neg, ← ENNReal.inv_rpow,
        ENNReal.inv_div (Or.inl ENNReal.coe_ne_top) (Or.inl (hrhoE k).ne')]
    obtain ⟨hcrudeU, hprefixU⟩ := hcrude hd hd1.le U hA hreg
    have hXcrude (k l : Nat) (hkl : k < l) (hl : l <= M) :
        X k l <= (Cvol : ENNReal) * ((rho k : ENNReal) / (rho l : ENNReal)) ^ (2 : Nat) :=
      Finset.sup_le (fun R hR => hcrudeU k l hkl hl R hR)
    have hXfinite (k l : Nat) (hkl : k < l) (hl : l <= M) : X k l < ⊤ := by
      apply (hXcrude k l hkl hl).trans_lt
      exact ENNReal.mul_lt_top (by simp) (by
        exact lt_top_iff_ne_top.mpr (ENNReal.pow_ne_top (hratioFinite l k).ne))
    have hXone (k l : Nat) (hkl : k < l) (hl : l <= M) : 1 <= X k l := by
      obtain ⟨i, hi⟩ := hA
      let R := U.cover.assign k i
      let Q := U.cover.assign l i
      have hR : R ∈ U.cover.indexSet k := U.cover.assign_mem k (hkl.le.trans hl) i hi
      have hQ : Q ∈ actualDescendantsW95 A U.cover.assign k l R :=
        Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, rfl⟩
      have hcontained : (U.cover.tube l Q).toConvexSpaceBody <=
          (U.cover.tube k R).toConvexSpaceBody :=
        U.cover.toChain.tube_assign_le hkl.le hl hi
      have hdensity : 0 < Kakeya.densityIn (actualDescendantsW95 A U.cover.assign k l R)
          (fun Q => (U.cover.tube l Q).toConvexSpaceBody) (U.cover.tube k R).toConvexSpaceBody :=
        (Kakeya.densityIn_pos_iff _ _ _).mpr ⟨Q, hQ,
          (Tube.volume_pos_and_lt_top (hrho l) (Tube.gridScale_le_one hd1.le M l)
            (U.cover.tube l Q)).1, hcontained⟩
      exact ((isFrostmanIn_frostmanConstIn _ _ _).one_le hdensity).trans
        (Finset.le_sup (f := actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l) hR)
    have hH1 (k l m : Nat) (hkl : k < l) (hlm : l < m) (hm : m <= M) :
        X k m <= (BF : ENNReal) * X k l * X l m := by
      have hgap : 4 * Tube.gridScale delta M m <= Tube.gridScale delta M l := by
        calc 4 * Tube.gridScale delta M m <= 16 * Tube.gridScale delta M m := by gcongr <;> norm_num
             _ <= _ := Tube.sixteen_mul_gridScale_le hd hd1.le hgridGap hlm hm
      have h := (htwo hd hd1.le U hA hreg hball k l m hkl hlm hm hgap).2
      refine h.trans (mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl)
      exact_mod_cast (show 2 * Ctwo ^ (2 : Nat) <= BF from le_max_right _ _)
    have hH2 (k l : Nat) (hkl : k < l) (hl : l <= M) :
        X k l <= (BF : ENNReal) * ((rho l : ENNReal) / (rho k : ENNReal)) ^ (-2 : Real) := by
      rw [hinverse, ENNReal.rpow_two]
      exact (hXcrude k l hkl hl).trans (mul_le_mul'
        (by exact_mod_cast (show Cvol <= BF from le_max_left _ _)) le_rfl)
    have hNlarge : p.ε ^ (-2 : Real) <= (p.N : Real) := by
      rw [hp.epsilon_eq, ← Real.rpow_mul (Nat.cast_nonneg _)]
      norm_num
    have hspanUpper : rho M / rho 0 <= delta ^ (p.ε ^ (2 : Nat)) := by
      rw [show rho M = delta from Tube.gridScale_self delta (by have := hp.M_pos; omega),
        show rho 0 = 1 from Tube.gridScale_zero delta M, div_one]
      calc delta = delta ^ (1 : Real) := (NNReal.rpow_one _).symm
           _ <= _ := NNReal.rpow_le_rpow_of_exponent_ge hd hd1.le
              (by nlinarith [hp.epsilon_pos, hp.epsilon_small])
    have hH3 : X 0 M <= ((rho M : ENNReal) / (rho 0 : ENNReal)) ^ (-p.η 0) := by
      simpa only [rho, Tube.gridScale_self delta (N := M) hMpos,
        Tube.gridScale_zero, ENNReal.coe_one, div_one] using hCFtop
    have hbottom (k : Nat) (R : iota) :
        actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k M R =
          frostmanConstIn (completeFibreW94 A (U.cover.assign k) R)
            (fun i => (Y i).toConvexSpaceBody) (U.cover.tube k R).toConvexSpaceBody := by
      have hD : actualDescendantsW95 A U.cover.assign k M R =
          completeFibreW94 A (U.cover.assign k) R := by
        calc actualDescendantsW95 A U.cover.assign k M R =
            (completeFibreW94 A (U.cover.assign k) R).image id :=
              Finset.image_congr (fun i hi => hreg.bottom_assign i (Finset.mem_filter.mp hi).1)
             _ = _ := Finset.image_id
      unfold actualRelativeFrostmanW95
      rw [hD]
      exact frostmanConstIn_congr _ (fun i hi => hreg.bottom_tube i (Finset.mem_filter.mp hi).1) _
    obtain hall | ⟨a, b, J, hab, hb, hJ, hJN, hlong, hmiddle, htail, hlow⟩ :=
      exists_same_array_stopping_w97 M p.N hp.M_pos (by have := hp.N_large; omega)
        BF 4 hBF (by norm_num) 2 p.ε (by norm_num) hp.epsilon_pos
        (by linarith [hp.epsilon_small]) hNlarge delta hd hd1 rho (fun k hk => hrho k)
        (fun k l hkl hl => Tube.gridScale_lt_gridScale hd hd1 (by have := hp.M_pos; omega) hkl)
        p.η hp.zeta_pos hp.zeta_mono (by linarith [hp.zeta_top, hp.epsilon_pos])
        (fun j hj => by
          have h := hp.rung_next j hj
          have hpos := mul_pos hp.epsilon_pos (hp.zeta_pos (j + 1) (by omega))
          nlinarith only [h, hpos])
        (by simp only [rho, Tube.gridScale_self delta (N := M) hMpos,
          Tube.gridScale_zero, div_one, le_refl]) hspanUpper X hXone hXfinite hH1 hH2 hH3
        (fun a m b ham hmb hb => (hprefixU a m b ham hmb hb).2) hcal
    · left
      intro k hk R hR
      by_cases hkM : k < M
      · rw [← hbottom k R]
        have h := (Finset.le_sup (f := actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k M) hR).trans
          (hall k hkM)
        norm_num only at h
        exact h
      · have he : k = M := by omega
        subst k
        have hRA : R ∈ A := hreg.bottom_index ▸ hR
        have hfibre : completeFibreW94 A (U.cover.assign M) R = {R} := by
          ext i
          simp only [completeFibreW94, Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hi, hieq⟩
            rwa [hreg.bottom_assign i hi] at hieq
          · intro hei
            subst i
            exact ⟨hRA, hreg.bottom_assign R hRA⟩
        rw [hfibre, hreg.bottom_tube R hRA]
        have hsingleton : IsFrostmanIn {R} (fun i => (Y i).toConvexSpaceBody)
            (Y R).toConvexSpaceBody 1 := by
          apply IsFrostmanIn.of_maxDensity_mul_volume_le
            (fun i hi => by rw [Finset.mem_singleton.mp hi])
            (Tube.volume_pos_and_lt_top hd hd1.le (Y R).toTube).1.ne'
          have hmax : Kakeya.maxDensity {R} (fun i => (Y i).toConvexSpaceBody) <= 1 := by
            simpa only [Finset.card_singleton, Nat.cast_one] using
              Kakeya.maxDensity_le_card {R} (fun i => (Y i).toConvexSpaceBody)
          simpa only [Finset.sum_singleton, one_mul] using
            mul_le_mul_right' hmax (volume (Y R).carrier)
        refine (frostmanConstIn_le hsingleton).trans ?_
        have hpow : (1 : ENNReal) <= (delta : ENNReal) ^ (-3 * p.ε) := by
          simpa only [ENNReal.rpow_zero] using ENNReal.rpow_le_rpow_of_exponent_ge
            (x := (delta : ENNReal)) (by exact_mod_cast hd1.le)
            (show -3 * p.ε <= 0 by linarith [hp.epsilon_pos])
        exact one_le_mul (one_le_pow₀ (by exact_mod_cast hBF)) hpow
    · right
      refine ⟨{
        a := ⟨a, by omega⟩
        b := ⟨b, by omega⟩
        a_lt_b := hab
        label := ⟨J - 1, by omega⟩
        label_active := by change J - 1 < p.N; omega
        block_long := hlong
        middle_upper := by
          intro R hR
          have h := (Finset.le_sup (f := actualRelativeFrostmanW95 A U.cover.assign U.cover.tube a b) hR).trans hmiddle
          simpa only [hinverse] using h
        tail_upper := by
          intro hbM R hR
          rw [← hbottom b R]
          have h := (Finset.le_sup (f := actualRelativeFrostmanW95 A U.cover.assign U.cover.tube b M) hR).trans
            (htail hbM)
          rw [hinverse b M (p.η (J - 1))] at h
          simpa only [rho, Tube.gridScale_self delta (N := M) hMpos] using h
        intermediate_lower := by
          intro l hal hlb hwinL hwinU R hR
          have hl : l <= M := hlb.le.trans hb
          let rab : ENNReal := (rho b : ENNReal) / (rho a : ENNReal)
          let ral : ENNReal := (rho l : ENNReal) / (rho a : ENNReal)
          let rlb : ENNReal := (rho b : ENNReal) / (rho l : ENNReal)
          have hrab : 0 < rab := hratioPos a b
          have hral : 0 < ral := hratioPos a l
          have hrlb : 0 < rlb := hratioPos l b
          have hrabfin : rab < ⊤ := hratioFinite a b
          have hralfin : ral < ⊤ := hratioFinite a l
          have hrlbfin : rlb < ⊤ := hratioFinite l b
          have hprod : ral * rlb = rab := by
            dsimp [ral, rlb, rab]
            simp only [div_eq_mul_inv]
            calc (rho l : ENNReal) * (rho a : ENNReal)⁻¹ *
                ((rho b : ENNReal) * (rho l : ENNReal)⁻¹) =
                  ((rho l : ENNReal) * (rho l : ENNReal)⁻¹) *
                    ((rho b : ENNReal) * (rho a : ENNReal)⁻¹) := by ring
                 _ = _ := by rw [ENNReal.mul_inv_cancel (hrhoE l).ne' ENNReal.coe_ne_top, one_mul]
          have hpowprod : rab ^ (1 - p.ε) * rab ^ p.ε = rab := by
            rw [← ENNReal.rpow_add _ _ hrab.ne' hrabfin.ne]
            simp only [sub_add_cancel, ENNReal.rpow_one]
          have hwindowL : rab ^ (1 - p.ε) <= ral := by
            apply (ENNReal.mul_le_mul_iff_left hrlb.ne' hrlbfin.ne).mp
            calc rab ^ (1 - p.ε) * rlb <= rab ^ (1 - p.ε) * rab ^ p.ε :=
                   mul_le_mul_left' hwinU _
                 _ = ral * rlb := hpowprod.trans hprod.symm
          have hwindowU : ral <= rab ^ p.ε := by
            apply (ENNReal.mul_le_mul_iff_left
              (ENNReal.rpow_pos hrab hrabfin.ne).ne'
              (ENNReal.rpow_ne_top_of_ne_zero hrab.ne' hrabfin.ne)).mp
            calc ral * rab ^ (1 - p.ε) <= ral * rlb := mul_le_mul_left' hwinL _
                 _ = rab ^ p.ε * rab ^ (1 - p.ε) := by rw [hprod, mul_comm, hpowprod]
          have hstrict : rlb ^ (-p.η J) < X l b := hlow l hal hlb hwindowL hwindowU
          have hband : X l b <= 2 * hreg.frostmanBand l b :=
            Finset.sup_le (fun Q hQ => (hreg.frostman_upper l b hlb hb Q hQ).le)
          have hparent := hreg.frostman_lower l b hlb hb R hR
          have hbound : rlb ^ (-p.η J) <
              2 * actualRelativeFrostmanW95 A U.cover.assign U.cover.tube l b R :=
            hstrict.trans_le (hband.trans (mul_le_mul_left' hparent 2))
          have hhalf := ENNReal.mul_lt_mul_right (a := (2 : ENNReal)⁻¹)
            (by norm_num) (by finiteness) hbound
          rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num : (2 : ENNReal) ≠ 0)
            (by simp), one_mul] at hhalf
          simpa only [Nat.sub_add_cancel hJ, one_div, rlb, hinverse] using hhalf }⟩
  have hsmall : Filter.Eventually (fun delta : NNReal =>
      (delta : ENNReal) ^ ePrep <= towerPreparationRetainedW95 delta Cprep Kprep ∧
      (Croot : ENNReal) * Ctw <= (delta : ENNReal) ^ (-ePrep) ∧
      (4 : ENNReal) <= (delta : ENNReal) ^ (-p.ε ^ (2 : Nat) * p.η 0 / 2) ∧
      delta <= (16 : NNReal) ^ (-(M : Real))) (nhdsWithin 0 (Set.Ioi 0)) := by
    filter_upwards [hprepCost,
      eventually_finite_const_le_rpow_neg (c := (Croot : ENNReal) * Ctw) (by finiteness) hePrep,
      eventually_finite_const_le_rpow_neg (c := (4 : ENNReal)) (by finiteness)
        (show 0 < p.ε ^ (2 : Nat) * p.η 0 / 2 by
          exact div_pos (mul_pos (pow_pos hp.epsilon_pos _) (hp.zeta_pos 0 (Nat.zero_le _))) (by norm_num)),
      eventually_le_nhdsGT (c := (16 : NNReal) ^ (-(M : Real))) (NNReal.rpow_pos (by norm_num))]
      with delta hprep hroot hfour hgap
    exact ⟨hprep, hroot, by simpa only [neg_div, neg_mul] using hfour, hgap⟩
  obtain ⟨deltaCut, hdeltaCut, hcut⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  let delta0 := min deltaPrep deltaCut
  have hdelta0 : 0 < delta0 := lt_min hdeltaPrep hdeltaCut
  have hdelta01 : delta0 < 1 := (min_le_left _ _).trans_lt hdeltaPrep1
  refine ⟨Ccan, Ctw, Ccell, BF, Cprep, Kprep, ePrep, delta0,
    hCcan, hCtw, hCcell, hBF, hCprep, hKprep, hePrep, hePrepSmall, hdelta0, hdelta01, ?_⟩
  intro delta hd hd0 iota inst F Y hF hball hcen hline hfull hCF
  have hd1 : delta < 1 := hd0.trans hdelta01
  have hdPrep : delta < deltaPrep := hd0.trans_le (min_le_left _ _)
  obtain ⟨hprepPaid, hrootPaid, hfourPaid, hgridGap⟩ :=
    hcut ⟨hd, hd0.trans_le (min_le_right _ _)⟩
  have hdEpos : (0 : ENNReal) < delta := ENNReal.coe_pos.mpr hd
  have hfullpos : 0 < fullness' F (fun i => (Y i).toShadedBody) :=
    (ENNReal.rpow_pos hdEpos ENNReal.coe_ne_top).trans_le hfull
  have hmass : 0 < ∑ i ∈ F, volume (Y i).shade := by
    by_contra h
    have hz : (∑ i ∈ F, volume (Y i).shade) = 0 := le_antisymm (not_lt.mp h) bot_le
    simp only [fullness', hz, ENNReal.zero_div, lt_self_iff_false] at hfullpos
  obtain ⟨A, Uext, hA, hAF, hpaid, ⟨hext⟩⟩ := htower hd hdPrep F Y hball hcen hline hmass
  obtain ⟨U, hU, hindex, hassign, hscale, htubes⟩ := hrestrict A Y Ccan Ctw Ccell Uext hext
  obtain ⟨hreg⟩ := hU
  have hLpos : 0 < 2 + Real.log (1 / (delta : Real)) / Real.log 2 := by
    have hlog : 0 <= Real.log (1 / (delta : Real)) / Real.log 2 := by
      apply div_nonneg (Real.log_nonneg ?_) (Real.log_nonneg (by norm_num))
      exact (le_div_iff₀ (show (0 : Real) < delta from hd)).mpr
        (by simpa only [one_mul] using (show (delta : Real) <= 1 from hd1.le))
    linarith
  have hdenompos : 0 < (Cprep : ENNReal) * ENNReal.ofReal
      ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ Kprep) :=
    ENNReal.mul_pos (ENNReal.coe_pos.mpr (zero_lt_one.trans_le hCprep)).ne'
      (ENNReal.ofReal_pos.mpr (pow_pos hLpos _)).ne'
  have hrpos : 0 < towerPreparationRetainedW95 delta Cprep Kprep := by
    apply ENNReal.inv_pos.mpr
    finiteness
  have hrfin : towerPreparationRetainedW95 delta Cprep Kprep < ⊤ :=
    ENNReal.inv_lt_top.mpr hdenompos
  obtain ⟨i0, hi0⟩ := hF
  obtain ⟨hvpos, hvfin⟩ := Tube.volume_pos_and_lt_top hd hd1.le (Y i0).toTube
  obtain ⟨_, _, _, hCFA⟩ := retained_state_fullness_card_frostman_w94
    F A (fun i => (Y i).toShadedBody) (fun i => (Y i).toShadedBody)
    ConvexSpaceBody.closedUnitBall (volume (Y i0).carrier) ((delta : ENNReal) ^ ePrep)
    ((delta : ENNReal) ^ (-ePrep)) (towerPreparationRetainedW95 delta Cprep Kprep)
    ⟨i0, hi0⟩ hAF hvpos hvfin
    (fun i hi => Tube.volume_carrier_eq_volume_carrier (Y i).toTube (Y i0).toTube)
    (fun i hi => hball i hi) ConvexSpaceBody.closedUnitBall_volume_pos
    ConvexSpaceBody.closedUnitBall.isCompact.measure_lt_top
    (fun i hi => rfl) (fun i hi => Set.Subset.refl _)
    (ENNReal.rpow_pos hdEpos ENNReal.coe_ne_top)
    (ENNReal.rpow_lt_top_of_nonneg hePrep.le ENNReal.coe_ne_top) hfull hCF
    ((ENNReal.rpow_ne_top_of_ne_zero hdEpos.ne' ENNReal.coe_ne_top).lt_top)
    hrpos hrfin hpaid
  have htop : actualRelativeCFArrayW97 U 0 M <= (delta : ENNReal) ^ (-p.η 0) := by
    have h := (hroot hd hd1.le U hp.M_pos hA hreg (fun i hi => hball i (hAF hi)) _ hCFA).2
    calc actualRelativeCFArrayW97 U 0 M <=
        (Croot : ENNReal) * Ctw * ((towerPreparationRetainedW95 delta Cprep Kprep *
          (delta : ENNReal) ^ ePrep)⁻¹ * (delta : ENNReal) ^ (-ePrep)) := h
      _ <= (delta : ENNReal) ^ (-ePrep) *
          (((delta : ENNReal) ^ ePrep * (delta : ENNReal) ^ ePrep)⁻¹ *
            (delta : ENNReal) ^ (-ePrep)) :=
        mul_le_mul' hrootPaid (mul_le_mul' (ENNReal.inv_le_inv.mpr
          (mul_le_mul' hprepPaid le_rfl)) le_rfl)
      _ = (delta : ENNReal) ^ (-4 * ePrep) := by
        rw [← ENNReal.rpow_add _ _ hdEpos.ne' ENNReal.coe_ne_top, ← ENNReal.rpow_neg,
          ← ENNReal.rpow_add _ _ hdEpos.ne' ENNReal.coe_ne_top,
          ← ENNReal.rpow_add _ _ hdEpos.ne' ENNReal.coe_ne_top]
        congr 1
        ring
      _ <= (delta : ENNReal) ^ (-p.η 0) :=
        ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd1.le)
          (by dsimp [ePrep]; linarith [hp.zeta_pos 0 (Nat.zero_le _)])
  exact ⟨A, U, Uext, hA, hAF, hpaid, ⟨hreg⟩, ⟨hext⟩, hindex, hassign, hscale, htubes,
    hstop hd hd1 hgridGap hfourPaid A Y U hA hreg (fun i hi => hball i (hAF hi)) htop⟩

end

end Kakeya.ml1Boot.TrialRestartW94
