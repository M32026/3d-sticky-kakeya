module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.TrialGeometryEntryW96
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Pigeonhole
import all Kakeya.Factorization

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI uP

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

def trialWeightedDensityBandLossW96 (d : NNReal) (n : Nat) : ENNReal :=
  ConvexSpaceBody.nonempty_factorization.C 3 n d * ENNReal.ofReal (1 + Real.logb 2 (n : Real))

def trialDimensionBandLossW96 (d rho : NNReal) : ENNReal :=
  ENNReal.ofReal (1 + Real.logb 2 ((rho : Real) / (d : Real))) ^ (2 : Nat)

/-- Factoring precedes density banding. D0 bounds the SAME selected reference U(S). -/
theorem exists_weighted_whole_cell_density_band_w96
    (hdim : Module.finrank Real E = 3)
    {iota : Type uI} {pi : Type uP} [DecidableEq iota] [DecidableEq pi]
    {d rho : NNReal} (hd : 0 < d) (hdhalf : d <= 1 / 2)
    (hdrho : d <= rho) (hrho : rho <= 1)
    (F : Finset iota) (Y : iota -> ShadedTube d E)
    (J : Finset pi) (P : pi -> Tube rho E) (parent : iota -> pi)
    (hF : F.Nonempty) (hmass : 0 < ∑ i ∈ F, volume (Y i).shade)
    (hball : ∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamily F (fun i => (Y i).toTube) J P parent)
    (hsurj : F.image parent = J) :
    ∃ (J1 : Finset pi) (U : pi -> Finset iota)
      (Fz : (S : pi) -> ConvexSpaceBody.Factorization (U S)
        (fun i => (Y i).toConvexSpaceBody) 2) (D0 : ENNReal),
      J1.Nonempty ∧ J1 ⊆ J ∧ 0 < D0 ∧ D0 < ⊤ ∧
      (∀ S ∈ J, U S ⊆ completeFibreW94 F parent S) ∧
      (∀ S ∈ J, (U S).Nonempty ∧ (Fz S).parts.Nonempty) ∧
      (∀ S ∈ J1, D0 <= maxDensity (U S) (fun i => (Y i).toConvexSpaceBody) ∧
        maxDensity (U S) (fun i => (Y i).toConvexSpaceBody) <= 2 * D0) ∧
      (∑ i ∈ F, volume (Y i).shade) <= trialWeightedDensityBandLossW96 d F.card *
        ∑ S ∈ J1, ∑ i ∈ U S, volume (Y i).shade ∧
      (∀ S ∈ J1, ∀ q ∈ (Fz S).parts,
        Metric.ethickness Real (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier 0
            ∈ Set.Icc (1 / 2 : ENNReal) 1 ∧
        Metric.ethickness Real (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier 1
            ∈ Set.Icc (d : ENNReal) (rho : ENNReal) ∧
        Metric.ethickness Real (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier 2
            ∈ Set.Icc (d : ENNReal) (rho : ENNReal)) := by
  classical
  have hsurjSet : Set.SurjOn parent (F : Set iota) (J : Set pi) := by
    intro S hS
    rw [← hsurj] at hS
    exact Finset.mem_image.mp hS
  obtain ⟨U, hU, Fz, hparts, hpaid, hranges⟩ := exists_perParentFactorization hdim hd
    (by simpa only [one_div] using hdhalf) hdrho hrho Y P parent hball hparent hsurjSet
  have hJ : J.Nonempty := hsurj ▸ hF.image parent
  have hUne : ∀ S ∈ J, (U S).Nonempty := by
    intro S hS
    obtain ⟨q, hq⟩ := hparts S hS
    exact ((Fz S).nonempty_of_mem_parts hq).mono ((Fz S).le hq)
  have hUf : ∀ S ∈ J, U S ⊆ F := fun S hS => (hU S hS).trans (Finset.filter_subset _ _)
  let dens := fun S => maxDensity (U S) (fun i => (Y i).toConvexSpaceBody)
  have hd1 : d <= 1 := hdrho.trans hrho
  have hdens : ∀ S ∈ J, dens S ∈ Set.Icc (1 : ENNReal) (F.card : ENNReal) := by
    intro S hS
    constructor
    · obtain ⟨i, hi⟩ := hUne S hS
      exact one_le_maxDensity ⟨i, hi, (Tube.volume_pos_and_lt_top hd hd1 (Y i).toTube).1⟩
    · exact (maxDensity_le_card _ _).trans (by exact_mod_cast Finset.card_le_card (hUf S hS))
  obtain ⟨J1, hJ1sub, hJ1ne, hbandmass, hband⟩ := exists_dyadicClass_nonempty
    (s := J) (fun S => ∑ i ∈ U S, volume (Y i).shade) dens
    (a := 1) (b := (F.card : NNReal)) (by norm_num) (by simpa using hdens)
  have hJ1 : J1.Nonempty := hJ1ne hJ
  obtain ⟨S0, hS0, hmin⟩ := J1.exists_min_image dens hJ1
  let D0 := dens S0
  have hD0 : 0 < D0 := zero_lt_one.trans_le (hdens S0 (hJ1sub hS0)).1
  have hD0finite : D0 < ⊤ := (hdens S0 (hJ1sub hS0)).2.trans_lt (by simp)
  have hCmono : ∀ S ∈ J,
      ConvexSpaceBody.nonempty_factorization.C 3 (fibre F parent S).card d <=
        ConvexSpaceBody.nonempty_factorization.C 3 F.card d := by
    intro S hS
    have hfibne : (fibre F parent S).Nonempty := (hUne S hS).mono (hU S hS)
    have hlog : Real.logb 2 ((fibre F parent S).card : Real) <= Real.logb 2 (F.card : Real) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hfibne.card_pos)
        (by exact_mod_cast Finset.card_le_card (show fibre F parent S ⊆ F from Finset.filter_subset _ _))
    unfold ConvexSpaceBody.nonempty_factorization.C
    apply mul_le_mul' _ le_rfl
    exact ENNReal.ofReal_le_ofReal (by simpa only [div_one] using add_le_add (le_refl (1 : Real)) hlog)
  have htotal : (∑ i ∈ F, volume (Y i).shade) <=
      ConvexSpaceBody.nonempty_factorization.C 3 F.card d *
        ∑ S ∈ J, ∑ i ∈ U S, volume (Y i).shade := by
    calc
      _ = ∑ S ∈ J, ∑ i ∈ fibre F parent S, volume (Y i).shade :=
        (Finset.sum_fiberwise_of_maps_to hparent.mapsTo _).symm
      _ <= ∑ S ∈ J, ConvexSpaceBody.nonempty_factorization.C 3 F.card d *
          ∑ i ∈ U S, volume (Y i).shade := Finset.sum_le_sum fun S hS =>
        (hpaid S hS).trans (mul_le_mul' (hCmono S hS) le_rfl)
      _ = _ := (Finset.mul_sum _ _ _).symm
  refine ⟨J1, U, Fz, D0, hJ1, hJ1sub, hD0, hD0finite, hU,
    fun S hS => ⟨hUne S hS, hparts S hS⟩, ?_, ?_, ?_⟩
  · exact fun S hS => ⟨hmin S hS, hband S hS S0 hS0⟩
  · apply htotal.trans
    have hmul := mul_le_mul' (le_refl (ConvexSpaceBody.nonempty_factorization.C 3 F.card d)) hbandmass
    simpa only [trialWeightedDensityBandLossW96, NNReal.coe_natCast, NNReal.coe_one,
      div_one, mul_assoc] using hmul
  · intro S hS q hq
    simpa only [one_div] using hranges S (hJ1sub hS) q hq

/-- Select common dimensions, then whole full blocks; the original U and hulls stay fixed. -/
theorem exists_full_weighted_factored_blocks_w96
    (hdim : Module.finrank Real E = 3)
    {iota : Type uI} {pi : Type uP} [DecidableEq iota] [DecidableEq pi]
    {d rho : NNReal} (hd : 0 < d) (hdrho : d <= rho) (hrho : rho <= 1)
    (F : Finset iota) (Y : iota -> ShadedTube d E)
    (J : Finset pi) (parent : iota -> pi) (U : pi -> Finset iota) (hJ : J.Nonempty)
    (hU : ∀ S ∈ J, U S ⊆ completeFibreW94 F parent S)
    (hUne : ∀ S ∈ J, (U S).Nonempty)
    (Fz : (S : pi) -> ConvexSpaceBody.Factorization (U S)
      (fun i => (Y i).toConvexSpaceBody) 2)
    (hFzne : ∀ S ∈ J, (Fz S).parts.Nonempty)
    (hranges : ∀ S ∈ J, ∀ q ∈ (Fz S).parts,
      Metric.ethickness Real (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier 0
          ∈ Set.Icc (1 / 2 : ENNReal) 1 ∧
      Metric.ethickness Real (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier 1
          ∈ Set.Icc (d : ENNReal) (rho : ENNReal) ∧
      Metric.ethickness Real (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier 2
          ∈ Set.Icc (d : ENNReal) (rho : ENNReal))
    (D0 h : ENNReal) (hD0 : 0 < D0) (hD0finite : D0 < ⊤)
    (hh : 0 < h) (hhfinite : h < ⊤)
    (hdensity : ∀ S ∈ J, D0 <= maxDensity (U S) (fun i => (Y i).toConvexSpaceBody) ∧
      maxDensity (U S) (fun i => (Y i).toConvexSpaceBody) <= 2 * D0)
    (haggregate : 2 * h * trialDimensionBandLossW96 d rho *
      (∑ S ∈ J, ∑ i ∈ U S, volume (Y i).carrier) <=
        ∑ S ∈ J, ∑ i ∈ U S, volume (Y i).shade) :
    ∃ (J2 : Finset pi) (a b : NNReal) (parts : pi -> Finset (Finset iota))
      (G : Finset iota)
      (Fout : (S : pi) -> ConvexSpaceBody.Factorization (completeFibreW94 G parent S)
        (fun i => (Y i).toConvexSpaceBody) 2),
      J2.Nonempty ∧ J2 ⊆ J ∧ d <= a ∧ a <= b ∧ b <= rho ∧
      (∀ S ∈ J2, (parts S).Nonempty ∧ parts S ⊆ (Fz S).parts) ∧
      (∀ S ∉ J2, parts S = ∅) ∧
      (∀ S, (Fout S).parts = parts S) ∧
      G = J2.biUnion (fun S => (parts S).biUnion id) ∧ G.Nonempty ∧ G ⊆ F ∧
      G.image parent = J2 ∧
      (∑ S ∈ J, ∑ i ∈ U S, volume (Y i).shade) <=
        2 * trialDimensionBandLossW96 d rho * ∑ i ∈ G, volume (Y i).shade ∧
      (∀ S ∈ J2, ∀ q ∈ parts S, q.Nonempty ∧ q ⊆ U S ∧
        h <= fullness' q (fun i => (Y i).toShadedBody) ∧
        h * (∑ i ∈ q, volume (Y i).carrier) <= ∑ i ∈ q, volume (Y i).shade ∧
        IsPlankOfDimensions plankPigeonhole.C a b
          (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)) ∧
        (plankPigeonhole.C_vol : ENNReal)⁻¹ * (a : ENNReal) * (b : ENNReal) <=
          volume (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier ∧
        volume (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier <=
          (plankPigeonhole.C_vol : ENNReal) * (a : ENNReal) * (b : ENNReal) ∧
        (D0 / 2) * volume (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier <=
          ∑ i ∈ q, volume (Y i).carrier) ∧
      ((J2.biUnion parts : Finset (Finset iota)) : Set (Finset iota)).Pairwise Disjoint := by
  classical
  let V := fun i => (Y i).toConvexSpaceBody
  let Z := fun i => (Y i).toShadedBody
  have hUdisjoint : (J : Set pi).PairwiseDisjoint U := by
    intro S hS S' hS' hne
    apply Finset.disjoint_left.mpr
    intro i hi hi'
    exact hne (((Finset.mem_filter.mp (hU S hS hi)).2).symm.trans
      (Finset.mem_filter.mp (hU S' hS' hi')).2)
  let H0 := J.biUnion U
  have hfibre0 : ∀ S ∈ J, fibre H0 parent S = U S :=
    (fibre_biUnion_eq (Finset.Subset.refl J) parent U hU).1
  have hoff0 : ∀ S ∉ J, fibre H0 parent S = ∅ :=
    fun S hS => fibre_biUnion_eq_empty_of_notMem (Finset.Subset.refl J) parent U hU hS
  obtain ⟨E0, hE0⟩ := exists_emptyFactorization (V := V) 2
  let F0 : (S : pi) -> ConvexSpaceBody.Factorization (fibre H0 parent S) V 2 :=
    fun S => if hS : S ∈ J then (exists_factorizationCopy (Fz S) (hfibre0 S hS).symm).choose
      else (exists_factorizationCopy E0 (hoff0 S hS).symm).choose
  have hF0 : ∀ S ∈ J, (F0 S).parts = (Fz S).parts := by
    intro S hS
    dsimp [F0]
    rw [dif_pos hS]
    exact (exists_factorizationCopy (Fz S) (hfibre0 S hS).symm).choose_spec
  let rep := fun S => if hS : S ∈ J then (hFzne S hS).choose else ∅
  have hrep : ∀ S ∈ J, rep S ∈ (F0 S).parts := by
    intro S hS
    rw [hF0 S hS]
    simpa only [rep, dif_pos hS] using (hFzne S hS).choose_spec
  have hC : 8 <= plankPigeonhole.C := by
    have hv : (1 : NNReal) <= Metric.volume_comparison.C 3 := by
      norm_num [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
    dsimp [plankPigeonhole.C]
    exact (by norm_num : (8 : NNReal) <= 16).trans
      (le_mul_of_one_le_right (by norm_num) hv)
  obtain ⟨Jd, hJdsub, hJdne, a, b, hda, hab, hbrho, hband, hdims0⟩ :=
    exists_commonPlankDims (C := plankPigeonhole.C) hC hd hdrho V parent
      (fun S => ∑ i ∈ U S, volume (Y i).shade) F0 rep hrep
      (by intro S hS q hq; rw [hF0 S hS] at hq; simpa only [one_div] using (hranges S hS q hq).1)
      (by intro S hS q hq; rw [hF0 S hS] at hq; exact (hranges S hS q hq).2.1)
      (by intro S hS q hq; rw [hF0 S hS] at hq; exact (hranges S hS q hq).2.2)
  have hJd : Jd.Nonempty := hJdne hJ
  have hdims : ∀ S ∈ Jd, ∀ q ∈ (Fz S).parts,
      IsPlankOfDimensions plankPigeonhole.C a b (q.convexHull_biUnion V) := by
    intro S hS q hq
    apply hdims0 S hS q
    rwa [hF0 S (hJdsub hS)]
  let H := Jd.biUnion U
  have hHU : H ⊆ H0 := Finset.biUnion_subset_biUnion_of_subset_left U hJdsub
  have hHF : H ⊆ F := by
    intro i hi
    obtain ⟨S, hS, hiU⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp (hU S (hJdsub hS) hiU)).1
  have hH : H.Nonempty := by
    obtain ⟨S, hS⟩ := hJd
    obtain ⟨i, hi⟩ := hUne S (hJdsub hS)
    exact ⟨i, Finset.mem_biUnion.mpr ⟨S, hS, hi⟩⟩
  have hJddisjoint : (Jd : Set pi).PairwiseDisjoint U :=
    fun S hS S' hS' hne => hUdisjoint (hJdsub hS) (hJdsub hS') hne
  let PG : Finpartition H := (Finpartition.combine (fun S => (Fz S).toFinpartition)
    hJddisjoint.supIndep).copy (Finset.sup_eq_biUnion Jd U)
  have hPGparts : PG.parts = Jd.biUnion (fun S => (Fz S).parts) := rfl
  have hPGfibre : ∀ q ∈ PG.parts, completeFibreW94 H PG.part q = q := by
    intro q hq
    ext i
    simp only [completeFibreW94, Finset.mem_filter]
    exact ⟨fun hi => (PG.part_eq_iff_mem hq).mp hi.2,
      fun hi => ⟨PG.le hq hi, PG.part_eq_of_mem hq hi⟩⟩
  have hHimage : H.image PG.part = PG.parts := by
    ext q
    constructor
    · rintro hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      exact PG.part_mem.mpr hi
    · intro hq
      obtain ⟨i, hi, hip⟩ := PG.part_surjOn hq
      exact Finset.mem_image.mpr ⟨i, hi, hip⟩
  let L := trialDimensionBandLossW96 d rho
  have hL : (1 : ENNReal) <= L := by
    have hdr : (0 : Real) < d := by exact_mod_cast hd
    have hratio : (1 : Real) <= (rho : Real) / d := (one_le_div hdr).mpr (by exact_mod_cast hdrho)
    have hlog := Real.logb_nonneg (by norm_num : (1 : Real) < 2) hratio
    apply one_le_pow₀
    exact ENNReal.one_le_ofReal.mpr (by linarith)
  have hLfin : L < ⊤ := by dsimp [L, trialDimensionBandLossW96]; finiteness
  have hshadepart : (∑ S ∈ Jd, ∑ i ∈ U S, volume (Y i).shade) =
      ∑ i ∈ H, volume (Y i).shade := (Finset.sum_biUnion hJddisjoint).symm
  have hcarrierpart : (∑ i ∈ H, volume (Y i).carrier) <=
      ∑ S ∈ J, ∑ i ∈ U S, volume (Y i).carrier := by
    rw [show H = Jd.biUnion U from rfl, Finset.sum_biUnion hJddisjoint]
    exact Finset.sum_le_sum_of_subset hJdsub
  have hfunded : 2 * h * (∑ i ∈ H, volume (Y i).carrier) <=
      ∑ i ∈ H, volume (Y i).shade := by
    apply (ENNReal.mul_le_mul_iff_right (zero_lt_one.trans_le hL).ne' hLfin.ne).mp
    calc
      L * (2 * h * ∑ i ∈ H, volume (Y i).carrier) <=
          L * (2 * h * ∑ S ∈ J, ∑ i ∈ U S, volume (Y i).carrier) := by gcongr
      _ = 2 * h * L * ∑ S ∈ J, ∑ i ∈ U S, volume (Y i).carrier := by ring
      _ <= ∑ S ∈ J, ∑ i ∈ U S, volume (Y i).shade := haggregate
      _ <= L * ∑ i ∈ H, volume (Y i).shade := by
        simpa only [L, trialDimensionBandLossW96, hshadepart] using hband
  have hvolpos : ∀ i ∈ H, 0 < volume (Y i).carrier :=
    fun i _ => (Tube.volume_pos_and_lt_top hd (hdrho.trans hrho) (Y i).toTube).1
  have hvolfin : ∀ i ∈ H, volume (Y i).carrier < ⊤ :=
    fun i _ => (Y i).toConvexSpaceBody.isCompact.measure_lt_top
  have heligible := exists_eligible_saturated_family_w94 H PG.part Z h hH hh hhfinite
    hvolpos hvolfin hfunded
  let t := eligibleParentsW94 H PG.part Z h
  let G := eligibleSaturatedFamilyW94 H PG.part Z h
  change t.Nonempty ∧ G.Nonempty ∧ G ⊆ H ∧ G.image PG.part = t ∧ _ at heligible
  obtain ⟨ht, hG, hGH, hGimage, hfibres, hqpos, hqfin, hqfull, hhalf⟩ := heligible
  have htPG : t ⊆ PG.parts := by
    intro q hq
    rw [← hHimage]
    have hq' : q ∈ H.image PG.part ∧ h <= fullness' (completeFibreW94 H PG.part q) Z := by
      simpa only [t, eligibleParentsW94, Finset.mem_filter] using hq
    exact hq'.1
  have hGfibre : ∀ q ∈ t, completeFibreW94 G PG.part q = q := by
    intro q hq
    exact (hfibres q hq).trans (hPGfibre q (htPG hq))
  have hGunion : G = t.biUnion id := by
    ext i
    constructor
    · intro hi
      exact Finset.mem_biUnion.mpr ⟨PG.part i, hGimage ▸ Finset.mem_image_of_mem PG.part hi,
        PG.mem_part (hGH hi)⟩
    · intro hi
      obtain ⟨q, hq, hiq⟩ := Finset.mem_biUnion.mp hi
      rw [← hGfibre q hq] at hiq
      exact (Finset.mem_filter.mp hiq).1
  let parts := fun S => if S ∈ Jd then (Fz S).parts.filter (fun q => q ∈ t) else ∅
  let J2 := Jd.filter (fun S => (parts S).Nonempty)
  have hpartsmem : ∀ S q, q ∈ parts S ↔ S ∈ Jd ∧ q ∈ (Fz S).parts ∧ q ∈ t := by
    intro S q
    by_cases hS : S ∈ Jd <;> simp [parts, hS]
  have hpartsub : ∀ S, parts S ⊆ (Fz S).parts := fun S q hq => ((hpartsmem S q).mp hq).2.1
  have hJ2sub : J2 ⊆ Jd := Finset.filter_subset _ _
  have hpartsJ2 : ∀ S ∉ J2, parts S = ∅ := by
    intro S hS
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hne
    obtain ⟨q, hq⟩ := hne
    exact hS (Finset.mem_filter.mpr ⟨((hpartsmem S q).mp hq).1, ⟨q, hq⟩⟩)
  have htparts : J2.biUnion parts = t := by
    ext q
    constructor
    · rintro hq
      obtain ⟨S, hS, hq⟩ := Finset.mem_biUnion.mp hq
      exact ((hpartsmem S q).mp hq).2.2
    · intro hq
      have hqPG := htPG hq
      rw [hPGparts] at hqPG
      obtain ⟨S, hS, hqS⟩ := Finset.mem_biUnion.mp hqPG
      have hqp : q ∈ parts S := (hpartsmem S q).mpr ⟨hS, hqS, hq⟩
      exact Finset.mem_biUnion.mpr ⟨S, Finset.mem_filter.mpr ⟨hS, ⟨q, hqp⟩⟩, hqp⟩
  have hJ2 : J2.Nonempty := by
    obtain ⟨q, hq⟩ := ht
    rw [← htparts] at hq
    obtain ⟨S, hS, _⟩ := Finset.mem_biUnion.mp hq
    exact ⟨S, hS⟩
  have hGparts : G = J2.biUnion (fun S => (parts S).biUnion id) := by
    rw [hGunion, ← htparts, Finset.biUnion_biUnion]
  have hpartfibre : ∀ S, (parts S).biUnion id = completeFibreW94 G parent S := by
    intro S
    ext i
    constructor
    · intro hi
      obtain ⟨q, hq, hiq⟩ := Finset.mem_biUnion.mp hi
      obtain ⟨hS, hqFz, hqt⟩ := (hpartsmem S q).mp hq
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [hGunion]
        exact Finset.mem_biUnion.mpr ⟨q, hqt, hiq⟩
      · exact (Finset.mem_filter.mp (hU S (hJdsub hS) ((Fz S).le hqFz hiq))).2
    · intro hi
      obtain ⟨hiG, hiS⟩ := Finset.mem_filter.mp hi
      rw [hGunion] at hiG
      obtain ⟨q, hqt, hiq⟩ := Finset.mem_biUnion.mp hiG
      have hqPG := htPG hqt
      rw [hPGparts] at hqPG
      obtain ⟨S', hS', hqS'⟩ := Finset.mem_biUnion.mp hqPG
      have hSS : S' = S := ((Finset.mem_filter.mp
        (hU S' (hJdsub hS') ((Fz S').le hqS' hiq))).2).symm.trans hiS
      subst S'
      exact Finset.mem_biUnion.mpr ⟨q, (hpartsmem S q).mpr ⟨hS', hqS', hqt⟩, hiq⟩
  let Fout := fun S => (Fz S).ofSubsetParts (hpartsub S)
    ((Finset.sup_eq_biUnion (parts S) id).trans (hpartfibre S))
  have hparentimage : G.image parent = J2 := by
    ext S
    constructor
    · rintro hS
      obtain ⟨i, hi, hiS⟩ := Finset.mem_image.mp hS
      have hif : i ∈ completeFibreW94 G parent S := Finset.mem_filter.mpr ⟨hi, hiS⟩
      rw [← hpartfibre S] at hif
      obtain ⟨q, hq, _⟩ := Finset.mem_biUnion.mp hif
      exact Finset.mem_filter.mpr ⟨((hpartsmem S q).mp hq).1, ⟨q, hq⟩⟩
    · intro hS
      obtain ⟨q, hq⟩ := (Finset.mem_filter.mp hS).2
      obtain ⟨i, hi⟩ := (Fz S).nonempty_of_mem_parts (hpartsub S hq)
      have hif : i ∈ completeFibreW94 G parent S := by
        rw [← hpartfibre S]
        exact Finset.mem_biUnion.mpr ⟨q, hq, hi⟩
      exact Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hif).1, (Finset.mem_filter.mp hif).2⟩
  refine ⟨J2, a, b, parts, G, Fout, hJ2, hJ2sub.trans hJdsub, hda, hab, hbrho,
    fun S hS => ⟨(Finset.mem_filter.mp hS).2, hpartsub S⟩,
    hpartsJ2, fun _ => rfl, hGparts, hG, hGH.trans hHF, hparentimage, ?_, ?_, ?_⟩
  · have htwo : (∑ i ∈ H, volume (Y i).shade) <= 2 * ∑ i ∈ G, volume (Y i).shade := by
      have hmul := mul_le_mul' (le_refl (2 : ENNReal)) hhalf
      change 2 * ((1 / 2 : ENNReal) * ∑ i ∈ H, volume (Y i).shade) <=
        2 * ∑ i ∈ G, volume (Y i).shade at hmul
      rw [← mul_assoc, one_div, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul] at hmul
      exact hmul
    apply hband.trans
    rw [hshadepart]
    simpa only [L, trialDimensionBandLossW96, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul' (le_refl L) htwo
  · intro S hS q hq
    obtain ⟨hSJd, hqFz, hqt⟩ := (hpartsmem S q).mp hq
    have hqne := (Fz S).nonempty_of_mem_parts hqFz
    have hqsub := (Fz S).le hqFz
    have hqfull' : h <= fullness' q Z := by
      simpa only [hPGfibre q (htPG hqt)] using hqfull q hqt
    have hqpos' : 0 < ∑ i ∈ q, volume (Y i).carrier := by
      simpa only [hPGfibre q (htPG hqt), Z] using hqpos q hqt
    have hqfin' : (∑ i ∈ q, volume (Y i).carrier) < ⊤ := by
      simpa only [hPGfibre q (htPG hqt), Z] using hqfin q hqt
    have hqmass := (ENNReal.le_div_iff_mul_le (Or.inl hqpos'.ne') (Or.inl hqfin'.ne)).mp hqfull'
    have hqDims := hdims S hSJd q hqFz
    have hqVol := volume_bounds_of_isPlankOfDimensions_vol hdim hqDims
    refine ⟨hqne, hqsub, hqfull', hqmass, hqDims, hqVol.1, hqVol.2, ?_⟩
    have hden := (hdensity S (hJdsub hSJd)).1.trans ((Fz S).maxDensity_le_mul q hqFz)
    have hhalfD : D0 / 2 <= densityIn q V (q.convexHull_biUnion V) :=
      (ENNReal.div_le_iff (by norm_num) (by simp)).mpr (by simpa only [ENNReal.coe_ofNat, mul_comm] using hden)
    rw [densityIn_of_all_le (fun i hi => Finset.le_convexHull_biUnion V hi)] at hhalfD
    obtain ⟨i, hi⟩ := hqne
    have hWpos : 0 < volume (q.convexHull_biUnion V).carrier :=
      (Tube.volume_pos_and_lt_top hd (hdrho.trans hrho) (Y i).toTube).1.trans_le
        (measure_mono (Finset.le_convexHull_biUnion V hi))
    exact (ENNReal.le_div_iff_mul_le (Or.inl hWpos.ne')
      (Or.inl (q.convexHull_biUnion V).isCompact.measure_ne_top)).mp hhalfD
  · rw [htparts]
    exact fun q hq q' hq' hne => PG.disjoint (htPG hq) (htPG hq') hne

/-- Explicit factoring, density-band and dimension-band losses have total log degree seven. -/
theorem trial_factoring_loss_le_fixed_polylog_w96
    (Ccard : Real) (hCcard : 1 <= Ccard) :
    ∃ C : Real, 1 <= C ∧ ∀ (d rho : NNReal) (n : Nat),
      0 < d -> d <= 1 / 2 -> d <= rho -> rho <= 1 -> 1 <= n ->
      (n : Real) <= Ccard * (d : Real) ^ (-4 : Real) ->
      trialWeightedDensityBandLossW96 d n * trialDimensionBandLossW96 d rho <=
        ENNReal.ofReal (C * (1 + Real.log (1 / (d : Real))) ^ (7 : Nat)) := by
  let c := Real.logb 2 Ccard
  let A := 4 * (1 + c)
  let B := max 1 (Real.log 2)⁻¹
  have hc : 0 <= c := Real.logb_nonneg (by norm_num) hCcard
  have hA : 1 <= A := by dsimp [A]; linarith
  have hB : 1 <= B := le_max_left _ _
  refine ⟨A ^ (2 : Nat) * B ^ (7 : Nat), ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hA) (one_le_pow₀ hB)
  · intro d rho n hd hdhalf hdrho hrho hn hcard
    have hd1 : d <= 1 := hdrho.trans hrho
    have hdR : (0 : Real) < d := by exact_mod_cast hd
    have hinv : (1 : Real) <= 1 / (d : Real) := (one_le_div hdR).mpr (by exact_mod_cast hd1)
    let x := Real.logb 2 (1 / (d : Real))
    let y := Real.log (1 / (d : Real))
    have hx : 0 <= x := Real.logb_nonneg (by norm_num) hinv
    have hy : 0 <= y := Real.log_nonneg hinv
    have hlogpower : Real.logb 2 ((d : Real) ^ (-4 : Real)) = 4 * x := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos hdR]
      dsimp [x]
      rw [one_div, Real.logb_inv]
      ring
    have hlogn : Real.logb 2 (n : Real) <= c + 4 * x := by
      calc
        _ <= Real.logb 2 (Ccard * (d : Real) ^ (-4 : Real)) :=
          Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast zero_lt_one.trans_le hn) hcard
        _ = _ := by
          rw [Real.logb_mul (zero_lt_one.trans_le hCcard).ne'
            (Real.rpow_pos_of_pos hdR _).ne', hlogpower]
    have hcardlog : 1 + Real.logb 2 (n : Real) <= A * (1 + x) := by
      dsimp [A]
      nlinarith [mul_nonneg hc hx]
    have hlogbase : 1 + x <= B * (1 + y) := by
      have hB1 := le_max_left (1 : Real) (Real.log 2)⁻¹
      have hBlog := le_max_right (1 : Real) (Real.log 2)⁻¹
      have hmul := mul_le_mul_of_nonneg_right hBlog hy
      dsimp [x, y, B] at *
      rw [Real.logb, div_eq_mul_inv]
      nlinarith
    have hpoly6 := plankPigeonhole_loss_le_polylog
      (Ccard := ⟨Ccard, (zero_lt_one.trans_le hCcard).le⟩) (by exact_mod_cast hCcard)
      hd hd1 hdrho hrho hn hcard
    have hcardE : ENNReal.ofReal (1 + Real.logb 2 (n : Real)) <=
        ENNReal.ofReal A * ENNReal.ofReal (1 + x) := by
      rw [← ENNReal.ofReal_mul (zero_le_one.trans hA)]
      exact ENNReal.ofReal_le_ofReal hcardlog
    calc
      _ = (ConvexSpaceBody.nonempty_factorization.C 3 n d *
          trialDimensionBandLossW96 d rho) * ENNReal.ofReal (1 + Real.logb 2 (n : Real)) := by
        unfold trialWeightedDensityBandLossW96
        ring
      _ <= (ENNReal.ofReal A * ENNReal.ofReal (1 + x) ^ (6 : Nat)) *
          (ENNReal.ofReal A * ENNReal.ofReal (1 + x)) :=
        mul_le_mul' hpoly6 hcardE
      _ = ENNReal.ofReal (A ^ (2 : Nat) * (1 + x) ^ (7 : Nat)) := by
        rw [ENNReal.ofReal_mul (p := A ^ (2 : Nat)) (by positivity), ENNReal.ofReal_pow (zero_le_one.trans hA),
          ENNReal.ofReal_pow (by linarith)]
        ring
      _ <= ENNReal.ofReal (A ^ (2 : Nat) * (B * (1 + y)) ^ (7 : Nat)) := by
        apply ENNReal.ofReal_le_ofReal
        gcongr
      _ = _ := by congr 1; rw [mul_pow]; ring

end

end Kakeya.ml1Boot.TrialRestartW94
