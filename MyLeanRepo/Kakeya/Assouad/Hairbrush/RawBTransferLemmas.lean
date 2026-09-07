import MyLeanRepo.Kakeya.Assouad.Subunit.OrientationInfrastructure
import MyLeanRepo.Kakeya.Hairbrush.PerBinCordoba
import MyLeanRepo.Kakeya.Hairbrush.IntersectionSumBound

/-!
# Transfer lemmas for Raw-B main proof

Transfers KT, ED, volume, and far-mass properties from the original acute
hairbrush to the oriented ordinary-angle family.
-/

noncomputable section

open MeasureTheory Metric Set Finset Real
open scoped Classical

namespace Kakeya.Assouad

variable {δ : ℝ}

/-- All δ-tubes have the same nominal volume. -/
lemma rawB_volume_eq (T : DeltaTube δ) :
    T.volume = Kakeya.deltaTubeVolume δ :=
  tube_volume_scaling.1 δ T

/-- KT bound transfers from F to any subfamily G ⊆ F. -/
lemma rawB_KT_subset
    {F G : TubeFamily δ} {C : ℝ}
    (hKT : Kakeya.KatzTaoConvexWolffBound F C) (hG : G ⊆ F) :
    Kakeya.KatzTaoConvexWolffBound G C := by
  intro W hW
  have h_filter_sub : (G.filter fun T => T.carrier ⊆ W) ⊆ (F.filter fun T => T.carrier ⊆ W) := by
    intro T hT
    have h1 : T ∈ G := (Finset.mem_filter.mp hT).1
    have h2 : T.carrier ⊆ W := (Finset.mem_filter.mp hT).2
    exact Finset.mem_filter.mpr ⟨hG h1, h2⟩
  have h1 : G.containedCount W ≤ F.containedCount W := by
    dsimp only [TubeFamily.containedCount]
    exact_mod_cast Finset.card_le_card h_filter_sub
  exact le_trans h1 (hKT W hW)

/-- ED transfers from F to any subfamily G ⊆ F. -/
lemma rawB_ED_subset
    {F G : TubeFamily δ}
    (hED : F.IsEssentiallyDistinct) (hG : G ⊆ F) :
    G.IsEssentiallyDistinct := by
  intro T hT U hU hne
  exact hED (hG hT) (hG hU) hne

/--
KT bound transfers to the oriented band family.

Each oriented tube has the same carrier as its preimage, so the number of
tubes contained in any convex set is unchanged (up to the injectivity of
orientation on the band family).
-/
lemma rawB_KT_orientation
    {F : TubeFamily δ} {Y : Shading F}
    {eta theta aCore zetaEnds bTube : ℝ}
    (core : HairbrushMultiplicityDenseTwoEndsCoreData Y eta theta aCore zetaEnds bTube)
    (transverse : HairbrushAcuteRobustTransverseData core)
    (hδ : 0 < δ)
    (h_ed : F.IsEssentiallyDistinct)
    {C : ℝ}
    (hKT : Kakeya.KatzTaoConvexWolffBound F C) :
    Kakeya.KatzTaoConvexWolffBound (orientedBandFamily core transverse) C := by
  let F_σ := orientedBandFamily core transverse
  let F_band := acuteBandFamily core transverse
  have h_inj := orientedBandFamily_injOn core transverse hδ h_ed
  intro W hW
  let S_σ := F_σ.filter fun U' => U'.carrier ⊆ W
  let S_band := F_band.filter fun U => U.carrier ⊆ W
  let S_F := F.filter fun U => U.carrier ⊆ W
  have h_Sσ_eq : S_σ = S_band.image (orientTube transverse.stem) := by
    ext U'
    simp only [S_σ, S_band, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Finset.mem_image.mp h1 with ⟨U, hU_band, rfl⟩
      have h3 : U.carrier ⊆ W := by
        have h4 : (orientTube transverse.stem U).carrier = U.carrier :=
          orientTube_carrier transverse.stem U
        rw [←h4]
        exact h2
      exact ⟨U, ⟨hU_band, h3⟩, rfl⟩
    · rintro ⟨U, ⟨hU_band, h2⟩, rfl⟩
      have h1 : orientTube transverse.stem U ∈ F_σ :=
        Finset.mem_image.mpr ⟨U, hU_band, rfl⟩
      have h3 : (orientTube transverse.stem U).carrier ⊆ W := by
        have h4 : (orientTube transverse.stem U).carrier = U.carrier :=
          orientTube_carrier transverse.stem U
        rw [h4]
        exact h2
      exact ⟨h1, h3⟩
  have h_Sband_sub_band : S_band ⊆ F_band := by
    intro U hU
    exact (Finset.mem_filter.mp hU).1
  have h_card_eq : S_σ.card = S_band.card := by
    rw [h_Sσ_eq]
    exact Finset.card_image_of_injOn (h_inj.mono h_Sband_sub_band)
  have h_Sband_sub_SF : S_band ⊆ S_F := by
    intro U hU
    have h1 : U ∈ F_band := (Finset.mem_filter.mp hU).1
    have h2 : U.carrier ⊆ W := (Finset.mem_filter.mp hU).2
    have h3 : U ∈ core.F3 := (Finset.mem_filter.mp h1).1
    have h4 : U ∈ F := core.F3_subset h3
    exact Finset.mem_filter.mpr ⟨h4, h2⟩
  have h_card_le : S_band.card ≤ S_F.card := Finset.card_le_card h_Sband_sub_SF
  have h9 : F_σ.containedCount W ≤ F.containedCount W := by
    dsimp only [TubeFamily.containedCount]
    have h10 : S_σ.card ≤ S_F.card := by
      rw [h_card_eq]
      exact h_card_le
    exact_mod_cast h10
  exact le_trans h9 (hKT W hW)

/--
ED transfers to the oriented band family.

Intersection volumes and tube volumes depend only on carriers, which are
preserved by orientation.
-/
lemma rawB_ED_orientation
    {F : TubeFamily δ} {Y : Shading F}
    {eta theta aCore zetaEnds bTube : ℝ}
    (core : HairbrushMultiplicityDenseTwoEndsCoreData Y eta theta aCore zetaEnds bTube)
    (transverse : HairbrushAcuteRobustTransverseData core)
    (hδ : 0 < δ)
    (h_ed : F.IsEssentiallyDistinct) :
    (orientedBandFamily core transverse).IsEssentiallyDistinct := by
  let F_σ := orientedBandFamily core transverse
  let F_band := acuteBandFamily core transverse
  have h_inj := orientedBandFamily_injOn core transverse hδ h_ed
  intro U' hU' V' hV' hne
  rcases Finset.mem_image.mp hU' with ⟨U, hU_band, rfl⟩
  rcases Finset.mem_image.mp hV' with ⟨V, hV_band, rfl⟩
  have h_U_ne_V : U ≠ V := by
    intro h
    have h_contra : orientTube transverse.stem U = orientTube transverse.stem V := by
      rw [h]
    exact hne h_contra
  have hU_F3 : U ∈ core.F3 := (Finset.mem_filter.mp hU_band).1
  have hV_F3 : V ∈ core.F3 := (Finset.mem_filter.mp hV_band).1
  have h_ed' : U.EssentiallyDistinct V :=
    h_ed (core.F3_subset hU_F3) (core.F3_subset hV_F3) h_U_ne_V
  have hcarU : (orientTube transverse.stem U).carrier = U.carrier :=
    orientTube_carrier transverse.stem U
  have hcarV : (orientTube transverse.stem V).carrier = V.carrier :=
    orientTube_carrier transverse.stem V
  have hvolU : (orientTube transverse.stem U).volume = U.volume :=
    orientTube_volume transverse.stem U
  have hvolV : (orientTube transverse.stem V).volume = V.volume :=
    orientTube_volume transverse.stem V
  have h_inter : volume ((orientTube transverse.stem U).carrier ∩ (orientTube transverse.stem V).carrier) =
      volume (U.carrier ∩ V.carrier) := by
    rw [hcarU, hcarV]
  have h_max : max (orientTube transverse.stem U).volume (orientTube transverse.stem V).volume =
      max U.volume V.volume := by
    rw [hvolU, hvolV]
  have h_goal : (orientTube transverse.stem U).EssentiallyDistinct (orientTube transverse.stem V) := by
    dsimp only [DeltaTube.EssentiallyDistinct]
    rw [h_inter, h_max]
    exact h_ed'
  exact h_goal

/--
Multiplicity sum bound: if each point is in at most M of the sets A k,
then the sum of volumes is at most M times the volume of the union.
-/
lemma rawB_multiplicity_sum
    {K : ℕ} {A : Fin K → Set Point3} {M : ENNReal}
    (hA_meas : ∀ k : Fin K, MeasurableSet (A k))
    (hM : ∀ x, (Finset.filter (fun k => x ∈ A k) Finset.univ).card ≤ M) :
    ∑ k : Fin K, volume (A k) ≤ M * volume (⋃ k : Fin K, A k) := by
  let mult : Point3 → ENNReal := fun x =>
    (Finset.filter (fun k : Fin K => x ∈ A k) Finset.univ).card
  let union_all : Set Point3 := ⋃ k : Fin K, A k
  have h_union_meas : MeasurableSet union_all :=
    MeasurableSet.iUnion fun k => hA_meas k
  have h_eq1 : ∀ x, mult x = ∑ k : Fin K, Set.indicator (A k) (fun _ => (1 : ENNReal)) x := by
    intro x
    simp [mult, Finset.sum_boole, Set.indicator_apply]
    <;> rfl
  have h_sum : ∑ k : Fin K, volume (A k) = ∫⁻ x, mult x := by
    let f : Fin K → Point3 → ENNReal := fun k x => Set.indicator (A k) (fun _ => (1 : ENNReal)) x
    have h_eq2 : ∀ k, ∫⁻ x, f k x = volume (A k) := by
      intro k
      have h : ∫⁻ x, Set.indicator (A k) (fun _ => (1 : ENNReal)) x = (1 : ENNReal) * volume (A k) :=
        MeasureTheory.lintegral_indicator_const₀ (hA_meas k).nullMeasurableSet (1 : ENNReal)
      simpa [f] using h
    calc
      ∑ k : Fin K, volume (A k)
        = ∑ k : Fin K, ∫⁻ x, f k x := by
          apply Finset.sum_congr rfl
          intro k _
          exact (h_eq2 k).symm
      _ = ∫⁻ x, ∑ k : Fin K, f k x := by
          have hf : ∀ k ∈ (Finset.univ : Finset (Fin K)), Measurable (f k) := by
            intro k _
            exact Measurable.indicator measurable_const (hA_meas k)
          exact (MeasureTheory.lintegral_finsetSum (Finset.univ : Finset (Fin K)) hf).symm
      _ = ∫⁻ x, mult x := by
          apply MeasureTheory.lintegral_congr
          intro x
          have h7 : ∑ k : Fin K, f k x = mult x := by
            simpa [f, h_eq1] using (h_eq1 x).symm
          rw [h7]
  rw [h_sum]
  have h_pointwise : ∀ x, mult x ≤ M * Set.indicator union_all (fun _ => (1 : ENNReal)) x := by
    intro x
    by_cases hx : x ∈ union_all
    · have h_ind : Set.indicator union_all (fun _ => (1 : ENNReal)) x = 1 := by
        rw [Set.indicator_apply, if_pos hx]
      rw [h_ind]
      <;> simpa using hM x
    · have h1 : ∀ k : Fin K, x ∉ A k := by
        intro k h2
        have h3 : x ∈ union_all := by
          exact Set.mem_iUnion.mpr ⟨k, h2⟩
        exact hx h3
      have h_mult0 : mult x = 0 := by
        simp [mult, h1]
        <;> decide
      rw [h_mult0]
      have h_ind0 : Set.indicator union_all (fun _ => (1 : ENNReal)) x = 0 := by
        rw [Set.indicator_apply, if_neg hx]
      rw [h_ind0]
      <;> positivity
  have h4 : ∫⁻ x, mult x ≤ ∫⁻ x, M * Set.indicator union_all (fun _ => (1 : ENNReal)) x :=
    MeasureTheory.lintegral_mono h_pointwise
  have h_meas_ind : Measurable (Set.indicator union_all (fun _ : Point3 => (1 : ENNReal))) := by
    apply Measurable.indicator measurable_const h_union_meas
  have h5 : ∫⁻ x, M * Set.indicator union_all (fun _ => (1 : ENNReal)) x =
      M * ∫⁻ x, Set.indicator union_all (fun _ => (1 : ENNReal)) x :=
    MeasureTheory.lintegral_const_mul M h_meas_ind
  have h6 : ∫⁻ x, Set.indicator union_all (fun _ => (1 : ENNReal)) x =
      (1 : ENNReal) * volume union_all :=
    MeasureTheory.lintegral_indicator_const₀ h_union_meas.nullMeasurableSet (1 : ENNReal)
  have h7 : (1 : ENNReal) * volume union_all = volume union_all := by simp
  rw [h5, h6, h7] at h4
  exact h4

/--
Package orientation properties: angle range, stem intersection, cardinality.
-/
lemma rawB_orientation_properties
    {F : TubeFamily δ} {Y : Shading F}
    {eta theta aCore zetaEnds bTube : ℝ}
    (core : HairbrushMultiplicityDenseTwoEndsCoreData Y eta theta aCore zetaEnds bTube)
    (transverse : HairbrushAcuteRobustTransverseData core)
    (hδ : 0 < δ)
    (h_ed : F.IsEssentiallyDistinct) :
    (∀ U ∈ orientedBandFamily core transverse,
      transverse.sigma ≤ angleBetween transverse.stem U ∧
      angleBetween transverse.stem U ≤ 2 * transverse.sigma) ∧
    (∀ U ∈ orientedBandFamily core transverse,
      (transverse.stem.carrier ∩ U.carrier).Nonempty) ∧
    ((orientedBandFamily core transverse).enncard =
      (acuteBandFamily core transverse).enncard) := by
  have h1 : ∀ U ∈ orientedBandFamily core transverse,
      transverse.sigma ≤ angleBetween transverse.stem U ∧
        angleBetween transverse.stem U ≤ 2 * transverse.sigma := by
    intro U hU
    exact orientedBandFamily_angle core transverse (hU' := hU)
  have h2 : ∀ U ∈ orientedBandFamily core transverse,
      (transverse.stem.carrier ∩ U.carrier).Nonempty := by
    intro U hU
    exact orientedBandFamily_intersects_stem core transverse (hU' := hU)
  have h3 : (orientedBandFamily core transverse).card =
      (acuteBandFamily core transverse).card :=
    orientedBandFamily_card core transverse hδ h_ed
  have h4 : (orientedBandFamily core transverse).enncard =
      (acuteBandFamily core transverse).enncard := by
    simp [TubeFamily.enncard, h3]
  exact ⟨h1, h2, h4⟩

/--
The far cylinder complement: points at distance ≥ r from the stem axis.
-/
def farSet (stem : DeltaTube δ) (r : ℝ) : Set Point3 :=
  {x | r ≤ ‖perpProj stem.direction (x - stem.base)‖}

/--
Far shading on the oriented family: restrict each band hair's shading to the
far cylinder complement. Retains at least 1/4 of the shading mass by the
far-mass hypothesis, and at least λ₃/4 of the tube volume by per-tube density.
-/
lemma rawB_far_shading_bound
    {F : TubeFamily δ} {Y : Shading F}
    {eta theta aCore zetaEnds bTube kappa : ℝ}
    (core : HairbrushMultiplicityDenseTwoEndsCoreData Y eta theta aCore zetaEnds bTube)
    (transverse : HairbrushAcuteRobustTransverseData core)
    (hδ : 0 < δ)
    (h_ed : F.IsEssentiallyDistinct)
    (hFar : HairbrushFarMassAtEffectiveRadius core transverse kappa) :
    ∃ (Z_far : Shading (orientedBandFamily core transverse)),
      (∀ U' ∈ orientedBandFamily core transverse,
        (core.lambda3 / 4) * U'.volume ≤ volume (Z_far.carrier U')) ∧
      (∀ U' ∈ orientedBandFamily core transverse,
        Z_far.carrier U' ⊆ core.Z.union) ∧
      (∀ U' ∈ orientedBandFamily core transverse,
        Z_far.carrier U' ⊆ farSet transverse.stem (hairbrushRawBEffectiveRadius core transverse kappa)) := by
  let F_σ := orientedBandFamily core transverse
  let F_band := acuteBandFamily core transverse
  let stem := transverse.stem
  let rEff := hairbrushRawBEffectiveRadius core transverse kappa
  let far := farSet stem rEff
  have h_far_meas : MeasurableSet far := by
    have h_cont : Continuous fun x : Point3 => ‖perpProj stem.direction (x - stem.base)‖ := by
      have h1 : Continuous fun x : Point3 => x - stem.base := continuous_id.sub continuous_const
      have h2 : Continuous fun x : Point3 => perpProj stem.direction x := by
        have h_inner : Continuous fun x : Point3 => inner ℝ x stem.direction :=
          Continuous.inner continuous_id continuous_const
        simpa [perpProj] using continuous_id.sub (h_inner.smul continuous_const)
      exact (h2.comp h1).norm
    exact h_cont.measurable measurableSet_Ici
  let Z_far : Shading F_σ :=
    { carrier := fun U' =>
        ⋃ U ∈ F_band,
          if orientTube stem U = U'
          then core.Z.carrier U ∩ far
          else (∅ : Set Point3)
      measurable_carrier := by
        intro U' hU'
        apply MeasurableSet.biUnion (F_band.finite_toSet.countable)
        intro U _
        by_cases h : orientTube stem U = U'
        · rw [if_pos h]
          have hU_F3 : U ∈ core.F3 := (Finset.mem_filter.mp (show U ∈ F_band from by tauto)).1
          exact (core.Z.measurable_carrier hU_F3).inter h_far_meas
        · rw [if_neg h]
          exact MeasurableSet.empty
      subset_tube := by
        intro U' hU'
        apply iUnion₂_subset
        intro U hU
        by_cases h : orientTube stem U = U'
        · rw [if_pos h]
          have hcar : U'.carrier = U.carrier := by
            rw [←h]
            exact orientTube_carrier stem U
          rw [hcar]
          have hU_F3' : U ∈ core.F3 := (Finset.mem_filter.mp hU).1
          have hZ_sub : core.Z.carrier U ⊆ U.carrier := core.Z.subset_tube hU_F3'
          have h_int_sub : (core.Z.carrier U ∩ far) ⊆ core.Z.carrier U :=
            Set.inter_subset_left
          exact Set.Subset.trans h_int_sub hZ_sub
        · rw [if_neg h]
          exact empty_subset _ }
  have h_carrier_eq_main : ∀ (U : DeltaTube δ), U ∈ F_band →
      Z_far.carrier (orientTube stem U) = core.Z.carrier U ∩ far := by
    intro U hU_band
    let U'_val := orientTube stem U
    have h_inj := orientedBandFamily_injOn core transverse hδ h_ed
    apply Set.Subset.antisymm
    · apply iUnion₂_subset
      intro V hV
      by_cases h : orientTube stem V = U'_val
      · rw [if_pos h]
        have h_eq : V = U := h_inj hV hU_band h
        rw [h_eq] <;> exact Subset.refl _
      · rw [if_neg h]
        exact empty_subset _
    · intro x hx
      exact Set.mem_biUnion hU_band (by rwa [if_pos rfl])
  have h_mass : ∀ U' ∈ F_σ, (core.lambda3 / 4) * U'.volume ≤ volume (Z_far.carrier U') := by
    intro U' hU'
    rcases Finset.mem_image.mp hU' with ⟨U, hU_band, rfl⟩
    let U'_val := orientTube stem U
    have h_carrier_eq := h_carrier_eq_main U hU_band
    rw [h_carrier_eq]
    have hU_F3 : U ∈ core.F3 := (Finset.mem_filter.mp hU_band).1
    have h_band_props := (Finset.mem_filter.mp hU_band).2
    have h_far_mass : (1 / 4 : ENNReal) * volume (core.Z.carrier U) ≤
        volume (core.Z.carrier U ∩ far) :=
      hFar U hU_F3 h_band_props.1 h_band_props.2.1 h_band_props.2.2.1 h_band_props.2.2.2
    have h_density : core.lambda3 * U.volume ≤ volume (core.Z.carrier U) :=
      core.per_tube_density U hU_F3
    have h_vol_eq : U'_val.volume = U.volume := orientTube_volume stem U
    calc
      (core.lambda3 / 4) * U'_val.volume
        = (core.lambda3 / 4) * U.volume := by rw [h_vol_eq]
      _ = (1 / 4 : ENNReal) * (core.lambda3 * U.volume) := by
        have h : (core.lambda3 / 4) * U.volume =
            (1 / 4 : ENNReal) * (core.lambda3 * U.volume) := by
          simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] <;> rfl
        exact h
      _ ≤ (1 / 4 : ENNReal) * volume (core.Z.carrier U) := by gcongr
      _ ≤ volume (core.Z.carrier U ∩ far) := h_far_mass
  have h_sub_Z : ∀ U' ∈ F_σ, Z_far.carrier U' ⊆ core.Z.union := by
    intro U' hU'
    rcases Finset.mem_image.mp hU' with ⟨U, hU_band, rfl⟩
    have h_carrier_eq := h_carrier_eq_main U hU_band
    rw [h_carrier_eq]
    have hU_F3 : U ∈ core.F3 := (Finset.mem_filter.mp hU_band).1
    have h_int_sub : (core.Z.carrier U ∩ far) ⊆ core.Z.carrier U :=
      Set.inter_subset_left
    intro x hx
    have h6 : x ∈ core.Z.carrier U := h_int_sub hx
    exact ⟨U, hU_F3, h6⟩
  have h_sub_far : ∀ U' ∈ F_σ, Z_far.carrier U' ⊆ far := by
    intro U' hU'
    rcases Finset.mem_image.mp hU' with ⟨U, hU_band, rfl⟩
    have h_carrier_eq := h_carrier_eq_main U hU_band
    rw [h_carrier_eq]
    have h_int_sub : (core.Z.carrier U ∩ far) ⊆ far :=
      Set.inter_subset_right
    exact h_int_sub
  exact ⟨Z_far, h_mass, h_sub_Z, h_sub_far⟩

/-- Sum of bin cardinalities ≥ family cardinality when bins cover the family. -/
lemma rawB_bins_sum_card
    {K : ℕ} {F_σ : TubeFamily δ} {bins : Fin K → TubeFamily δ}
    (h_bins_sub : ∀ k, bins k ⊆ F_σ)
    (h_bins_cover : ∀ U ∈ F_σ, ∃ k, U ∈ bins k) :
    F_σ.enncard ≤ ∑ k : Fin K, (bins k).enncard := by
  have h1 : F_σ ⊆ Finset.biUnion (Finset.univ : Finset (Fin K)) bins := by
    intro U hU
    rcases h_bins_cover U hU with ⟨k, hk⟩
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hk⟩
  have h2 : F_σ.card ≤ (Finset.biUnion (Finset.univ : Finset (Fin K)) bins).card :=
    Finset.card_le_card h1
  have h3 : (Finset.biUnion (Finset.univ : Finset (Fin K)) bins).card ≤
      ∑ k : Fin K, (bins k).card :=
    Finset.card_biUnion_le
  have h4 : F_σ.card ≤ ∑ k : Fin K, (bins k).card := le_trans h2 h3
  have h5 : (F_σ.enncard) ≤ ∑ k : Fin K, (bins k).enncard := by
    have h6 : (F_σ.enncard) = ↑(F_σ.card) := by simp [TubeFamily.enncard]
    have h7 : (∑ k : Fin K, (bins k).enncard) = ↑(∑ k : Fin K, (bins k).card) := by
      have h8 : ∀ k : Fin K, (bins k).enncard = ↑((bins k).card) := by
        intro k; simp [TubeFamily.enncard]
      calc
        (∑ k : Fin K, (bins k).enncard)
          = ∑ k : Fin K, ↑((bins k).card) := by
            apply Finset.sum_congr rfl
            intro k _
            exact h8 k
        _ = ↑(∑ k : Fin K, (bins k).card) := by
          have h9 : (∑ k : Fin K, (↑((bins k).card) : ENNReal)) =
              ↑(∑ k : Fin K, (bins k).card) := by
            simp
          exact h9
    rw [h6, h7]
    exact_mod_cast h4
  exact h5

/-- The union of far shadings over bins is contained in core.Z.union. -/
lemma rawB_union_subset_Z
    {K : ℕ} {F : TubeFamily δ} {Y : Shading F}
    {eta theta aCore zetaEnds bTube : ℝ}
    (core : HairbrushMultiplicityDenseTwoEndsCoreData Y eta theta aCore zetaEnds bTube)
    (transverse : HairbrushAcuteRobustTransverseData core)
    (Z_far : Shading (orientedBandFamily core transverse))
    (hZ_far_sub : ∀ U' ∈ orientedBandFamily core transverse,
      Z_far.carrier U' ⊆ core.Z.union)
    {bins : Fin K → TubeFamily δ}
    (h_bins_sub : ∀ k, bins k ⊆ orientedBandFamily core transverse) :
    (⋃ k : Fin K, ⋃ U ∈ bins k, Z_far.carrier U) ⊆ core.Z.union := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
  have h9 : ∃ (U : DeltaTube δ), U ∈ bins k ∧ x ∈ Z_far.carrier U := by
    simpa [Finset.mem_biUnion] using hk
  rcases h9 with ⟨U, hU, hxU⟩
  have hU' : U ∈ orientedBandFamily core transverse := h_bins_sub k hU
  exact hZ_far_sub U hU' hxU

end Kakeya.Assouad
