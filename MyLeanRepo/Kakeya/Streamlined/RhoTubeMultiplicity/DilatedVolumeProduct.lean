import MyLeanRepo.Kakeya.Streamlined.RhoTubeMultiplicity.DilatedPerTubeDensity
import MyLeanRepo.Kakeya.Streamlined.ProfileUniformRefinement.DilatedTubeBodyGeometry
import MyLeanRepo.Kakeya.Streamlined.DilatedCoverUniformization
import MyLeanRepo.Kakeya.Streamlined.RhoTubeMultiplicity.InducedShading

/-!
# Volume product for actual dilated parent bodies

This is the fixed-dilation replacement for the strict-parent volume product
used in Lemma 5.11.  The coarse family is represented by its actual
`dilatedTubeBodyFamily`; no dilated carrier is reinterpreted as a strict
unit-length `rho`-tube.
-/

noncomputable section

open MeasureTheory Metric Finset

namespace Kakeya.Streamlined

/-- Body mass of one assigned fibre in an equal-radius fine tube family. -/
lemma dilated_cover_fiberMass_eq
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse) (parent : Fin coarse.card) :
    P.toFactoring.fiberMass parent =
      P.toFactoring.fiberCount parent * Kakeya.deltaTubeVolume delta := by
  dsimp only [Factoring.fiberMass]
  calc
    (∑ index ∈ P.toFactoring.fiberIndices parent,
        (fine.toBodyFamily.body index).volume) =
        ∑ _index ∈ P.toFactoring.fiberIndices parent,
          Kakeya.deltaTubeVolume delta := by
      apply Finset.sum_congr rfl
      intro index _
      exact tube_volume_eq (fine.tube index)
        ⟨0, EuclideanSpace.single 0 1, by simp [EuclideanSpace.norm_eq]⟩
    _ = P.toFactoring.fiberCount parent * Kakeya.deltaTubeVolume delta := by
      rw [Finset.sum_const]
      simp [Factoring.fiberCount, nsmul_eq_mul]

lemma dilated_cover_fiberMass_ne_zero
    {delta rho A : ℝ} (hdelta : 0 < delta)
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse) (parent : Fin coarse.card) :
    P.toFactoring.fiberMass parent ≠ 0 := by
  rw [dilated_cover_fiberMass_eq P parent]
  have hcountPositive : 0 < P.toFactoring.fiberCount parent :=
    zero_lt_one.trans_le (P.toFactoring.one_le_fiberCount parent)
  exact mul_ne_zero hcountPositive.ne' <|
    (by
      have h := tube_volume_ge_two_delta_sq delta hdelta
      have hpositive : 0 < ENNReal.ofReal (2 * delta ^ 2) := by positivity
      exact (hpositive.trans_le h).ne')

lemma dilated_cover_fiberMass_ne_top
    {delta rho A : ℝ} (hdelta : 0 < delta)
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse) (parent : Fin coarse.card) :
    P.toFactoring.fiberMass parent ≠ ⊤ := by
  rw [dilated_cover_fiberMass_eq P parent]
  exact ENNReal.mul_ne_top (by simp [Factoring.fiberCount]) <| by
    have h : Kakeya.deltaTubeVolume delta ≤ ENNReal.ofReal
        (Real.pi * delta ^ 2 + (8 / 3 : ℝ) * Real.pi * delta ^ 3) :=
      GeometricLemmas.capsule_volume_upper delta
        hdelta
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

/-- Uniform assigned-fibre counts give the corresponding body-mass estimate
for equal-radius tubes.  This is the denominator comparison used in the
ownerwise density calculation. -/
lemma dilated_cover_parent_card_mul_fiberMass_le
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (C : ENNReal) (hC : P.toFactoring.FibersAreCUniform C)
    (parent : Fin coarse.card) :
    (coarse.card : ENNReal) * P.toFactoring.fiberMass parent ≤
      C * fine.toBodyFamily.mass := by
  let vdelta := Kakeya.deltaTubeVolume delta
  have hcount :
      (coarse.card : ENNReal) * P.toFactoring.fiberCount parent ≤
        C * fine.enncard := by
    calc
      (coarse.card : ENNReal) * P.toFactoring.fiberCount parent =
          ∑ _other : Fin coarse.card,
            P.toFactoring.fiberCount parent := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ other : Fin coarse.card,
          C * P.toFactoring.fiberCount other := by
        exact Finset.sum_le_sum fun other _ => hC.2 parent other
      _ = C * ∑ other : Fin coarse.card,
          P.toFactoring.fiberCount other := by
        rw [Finset.mul_sum]
      _ = C * fine.enncard := by
        rw [P.sum_factoringFiberCount]
  have hfiberMass : P.toFactoring.fiberMass parent =
      P.toFactoring.fiberCount parent * vdelta := by
    dsimp only [Factoring.fiberMass]
    calc
      (∑ index ∈ P.toFactoring.fiberIndices parent,
          (fine.toBodyFamily.body index).volume) =
          ∑ _index ∈ P.toFactoring.fiberIndices parent, vdelta := by
        apply Finset.sum_congr rfl
        intro index _
        exact tube_volume_eq (fine.tube index)
          ⟨0, EuclideanSpace.single 0 1, by simp [EuclideanSpace.norm_eq]⟩
      _ = P.toFactoring.fiberCount parent * vdelta := by
        rw [Finset.sum_const]
        simp [Factoring.fiberCount, nsmul_eq_mul]
  have hfineMass : fine.toBodyFamily.mass = fine.enncard * vdelta := by
    change (∑ index : Fin fine.card, (fine.tube index).volume) = _
    calc
      (∑ index : Fin fine.card, (fine.tube index).volume) =
          ∑ _index : Fin fine.card, vdelta := by
        apply Finset.sum_congr rfl
        intro index _
        exact tube_volume_eq (fine.tube index)
          ⟨0, EuclideanSpace.single 0 1, by simp [EuclideanSpace.norm_eq]⟩
      _ = fine.enncard * vdelta := by
        simp [TubeFamily.enncard, Finset.sum_const, nsmul_eq_mul]
  rw [hfiberMass, hfineMass]
  calc
    (coarse.card : ENNReal) *
          (P.toFactoring.fiberCount parent * vdelta) =
        ((coarse.card : ENNReal) * P.toFactoring.fiberCount parent) *
          vdelta := by ring
    _ ≤ (C * fine.enncard) * vdelta := by gcongr
    _ = C * (fine.enncard * vdelta) := by ring

/--
The ownerwise density form of the dilated tube estimate.  For one complete
assigned fibre, its average shaded density controls the density of the exact
induced carrier in the actual dilated parent.  This is the parent-indexed
quantity which must be frozen before the final spatial averaging in the
protected Lemma 5.11 construction.
-/
lemma dilated_exact_induced_fiber_density
    {delta rho A : ℝ}
    (hdelta : 0 < delta) (hdelta_rho : delta ≤ rho) (hrho_one : rho ≤ 1)
    (hA : 1 ≤ A)
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (Y : TubeShading fine)
    (Z : Shading (dilatedTubeBodyFamily A coarse))
    (hZ : P.toFactoring.IsExactInducedShading Y Z rho)
    (parent : Fin coarse.card) :
    (P.toFactoring.fiberShadedMass Y parent /
          P.toFactoring.fiberMass parent) *
        ((dilatedTubeBodyFamily A coarse).body parent).volume ≤
      (172800 * ENNReal.ofReal (A ^ 3)) *
        volume (Z.carrier parent) := by
  classical
  let vdelta := Kakeya.deltaTubeVolume delta
  let vrho := Kakeya.deltaTubeVolume rho
  let count := P.toFactoring.fiberCount parent
  let shaded := P.toFactoring.fiberShadedMass Y parent
  let induced := volume (Z.carrier parent)
  let a3 := ENNReal.ofReal (A ^ 3)
  have hrho : 0 < rho := hdelta.trans_le hdelta_rho
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hvdeltaZero : vdelta ≠ 0 := by
    have h := tube_volume_ge_two_delta_sq delta hdelta
    have hpositive : 0 < ENNReal.ofReal (2 * delta ^ 2) := by
      positivity
    exact (hpositive.trans_le h).ne'
  have hvdeltaTop : vdelta ≠ ⊤ := by
    have h : vdelta ≤ ENNReal.ofReal
        (Real.pi * delta ^ 2 + (8 / 3 : ℝ) * Real.pi * delta ^ 3) :=
      GeometricLemmas.capsule_volume_upper delta hdelta
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hcountZero : count ≠ 0 := by
    exact (P.toFactoring.one_le_fiberCount parent |> zero_lt_one.trans_le).ne'
  have hcountTop : count ≠ ⊤ := by
    simp [count, Factoring.fiberCount]
  have hfineVolume : ∀ index : Fin fine.card,
      (fine.tube index).volume = vdelta := by
    intro index
    exact tube_volume_eq (fine.tube index)
      ⟨0, EuclideanSpace.single 0 1, by simp [EuclideanSpace.norm_eq]⟩
  have hparentVolume : (coarse.tube parent).volume = vrho :=
    tube_volume_eq (coarse.tube parent)
      ⟨0, EuclideanSpace.single 0 1, by simp [EuclideanSpace.norm_eq]⟩
  have hdilatedVolume :
      ((dilatedTubeBodyFamily A coarse).body parent).volume = a3 * vrho := by
    change (dilatedTubeBody A (coarse.tube parent)).volume = a3 * vrho
    rw [dilatedTubeBody_volume hrho hApos, hparentVolume]
  have hfiberMass : P.toFactoring.fiberMass parent = count * vdelta := by
    dsimp only [Factoring.fiberMass, count, Factoring.fiberCount]
    calc
      (∑ index ∈ P.toFactoring.fiberIndices parent,
          (fine.toBodyFamily.body index).volume) =
          ∑ _index ∈ P.toFactoring.fiberIndices parent, vdelta := by
        apply Finset.sum_congr rfl
        intro index _
        exact hfineVolume index
      _ = ((P.toFactoring.fiberIndices parent).card : ENNReal) * vdelta := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]
  have hperTube : ∀ index ∈ P.toFactoring.fiberIndices parent,
      vrho / vdelta * volume (Y.carrier index) ≤
        172800 * induced := by
    intro index hindex
    have hparent : P.toFactoring.parent index = parent := by
      simpa [Factoring.fiberIndices] using hindex
    have hlocal := dilated_per_tube_density_scaled
      hdelta hdelta_rho hrho_one hA
      (fine.tube index) (coarse.tube parent)
      (by
        change (fine.tube index).carrier ⊆
          dilatedTubeCarrier A (coarse.tube parent)
        have hnested := P.nested index
        change (fine.tube index).carrier ⊆
          dilatedTubeCarrier A (coarse.tube (P.toFactoring.parent index)) at hnested
        rw [hparent] at hnested
        exact hnested)
      (Y.carrier index) (Y.measurable_carrier index) (Y.subset_body index)
    rw [hparentVolume] at hlocal
    have hsubset :
        dilatedTubeCarrier A (coarse.tube parent) ∩
            Metric.cthickening rho (Y.carrier index) ⊆
          Z.carrier parent := by
      intro point hpoint
      rw [hZ parent]
      refine ⟨hpoint.1, ?_⟩
      apply Metric.cthickening_subset_of_subset rho
        (show Y.carrier index ⊆
          P.toFactoring.fiberShadedUnion Y parent by
            intro x hx
            exact ⟨index, hparent, hx⟩)
      exact hpoint.2
    exact hlocal.trans <| mul_le_mul_left' (measure_mono hsubset) 172800
  have hsum : (vrho / vdelta) * shaded ≤
      count * (172800 * induced) := by
    calc
      (vrho / vdelta) * shaded =
          ∑ index ∈ P.toFactoring.fiberIndices parent,
            (vrho / vdelta) * volume (Y.carrier index) := by
        dsimp only [shaded, Factoring.fiberShadedMass]
        rw [Finset.mul_sum]
      _ ≤ ∑ _index ∈ P.toFactoring.fiberIndices parent,
          172800 * induced := Finset.sum_le_sum hperTube
      _ = count * (172800 * induced) := by
        dsimp only [count, Factoring.fiberCount]
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]
  have hscaled := mul_le_mul_left' hsum (a3 * count⁻¹)
  have hcountCancel : count⁻¹ * count = 1 :=
    ENNReal.inv_mul_cancel hcountZero hcountTop
  have hvdeltaCancel : vdelta⁻¹ * vdelta = 1 :=
    ENNReal.inv_mul_cancel hvdeltaZero hvdeltaTop
  rw [hfiberMass, hdilatedVolume]
  simpa only [div_eq_mul_inv] using (show
    (shaded * (count * vdelta)⁻¹) * (a3 * vrho) ≤
        (172800 * a3) * induced by
      calc
        (shaded * (count * vdelta)⁻¹) * (a3 * vrho) =
            (a3 * count⁻¹) * ((vrho * vdelta⁻¹) * shaded) := by
          rw [ENNReal.mul_inv (Or.inl hcountZero) (Or.inr hvdeltaZero)]
          ring
        _ ≤ (a3 * count⁻¹) *
            (count * (172800 * induced)) := hscaled
        _ = (172800 * a3) * induced := by
          rw [show (a3 * count⁻¹) *
              (count * (172800 * induced)) =
                a3 * (count⁻¹ * count) * (172800 * induced) by ring,
            hcountCancel]
          ring)

/--
The volume product for one uniform factoring of a dilated cover.

The exact sum below is over the chosen parent partition, so its uniformity
hypothesis is correctly stated on `P.toFactoring`, not on the overlapping
geometric full fibers. Paper-facing callers may supply this hypothesis through
an exact full-fiber factoring adapter.

The factor `172800` is the absolute per-tube halo loss, while `A^3` is the
exact volume ratio between the actual dilated parent body and its underlying
geometric `rho`-tube.
-/
lemma dilated_rho_tube_volume_product
    {delta rho A : ℝ}
    (hdelta : 0 < delta) (hdelta_rho : delta ≤ rho) (hrho_one : rho ≤ 1)
    (hA : 1 ≤ A)
    {fine : TubeFamily delta}
    (hfine_meas : fine.toBodyFamily.IsMeasurable)
    {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (Y : TubeShading fine) (hY_pos : 0 < Y.mass)
    (C : ENNReal) (hC : P.toFactoring.FibersAreCUniform C) :
    let Z := inducedShading P.toFactoring Y rho
      (dilatedTubeBodyFamily_measurable
        (lt_of_lt_of_le zero_lt_one hA) (hdelta.trans_le hdelta_rho).le coarse)
    (Y.mass / fine.toBodyFamily.mass) *
        (dilatedTubeBodyFamily A coarse).mass ≤
      172800 * ENNReal.ofReal (A ^ 3) * C * Z.mass := by
  classical
  let vdelta := Kakeya.deltaTubeVolume delta
  let vrho := Kakeya.deltaTubeVolume rho
  let n : ENNReal := fine.enncard
  let m : ENNReal := coarse.enncard
  let a3 : ENNReal := ENNReal.ofReal (A ^ 3)
  have hrho : 0 < rho := hdelta.trans_le hdelta_rho
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  let hcoarse_meas :=
    dilatedTubeBodyFamily_measurable hA_pos hrho.le coarse
  let Z :=
    inducedShading P.toFactoring Y rho hcoarse_meas

  have hvdelta_pos : 0 < vdelta := by
    have h := tube_volume_ge_two_delta_sq delta hdelta
    have h' : 0 < ENNReal.ofReal (2 * delta ^ 2) := by positivity
    exact h'.trans_le h
  have hvdelta_ne_zero : vdelta ≠ 0 := hvdelta_pos.ne'
  have hvdelta_ne_top : vdelta ≠ ⊤ := by
    have h :
        vdelta ≤
          ENNReal.ofReal
            (Real.pi * delta ^ 2 +
              (8 / 3 : ℝ) * Real.pi * delta ^ 3) :=
      GeometricLemmas.capsule_volume_upper delta hdelta
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

  have hvrho_pos : 0 < vrho := by
    have h := tube_volume_ge_two_delta_sq rho hrho
    have h' : 0 < ENNReal.ofReal (2 * rho ^ 2) := by positivity
    exact h'.trans_le h
  have hvrho_ne_zero : vrho ≠ 0 := hvrho_pos.ne'
  have hvrho_ne_top : vrho ≠ ⊤ := by
    have h :
        vrho ≤
          ENNReal.ofReal
            (Real.pi * rho ^ 2 +
              (8 / 3 : ℝ) * Real.pi * rho ^ 3) :=
      GeometricLemmas.capsule_volume_upper rho hrho
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

  have hn_pos : 0 < n := by
    by_contra h
    have h_card : fine.card = 0 := by
      have : (fine.card : ENNReal) = 0 := by simpa [n, TubeFamily.enncard] using h
      exact Nat.cast_eq_zero.mp this
    have hY_zero : Y.mass = 0 := by
      have h_all :
          ∀ i : Fin fine.card, volume (Y.carrier i) = 0 := by
        intro i
        have hi := i.isLt
        omega
      simp [Shading.mass, h_all]
    exact hY_pos.ne' hY_zero
  have hn_ne_zero : n ≠ 0 := hn_pos.ne'
  have hn_ne_top : n ≠ ⊤ := by
    simp [n, TubeFamily.enncard]

  have hm_pos : 0 < m := by
    by_contra h
    have h_card : coarse.card = 0 := by
      have : (coarse.card : ENNReal) = 0 := by simpa [m, TubeFamily.enncard] using h
      exact Nat.cast_eq_zero.mp this
    haveI : IsEmpty (Fin coarse.card) := by
      rw [h_card]
      infer_instance
    let i : Fin fine.card := ⟨0, by
      have : fine.card ≠ 0 := by
        intro hfine
        have : (fine.card : ENNReal) = 0 := by simp [hfine]
        exact hn_pos.ne' (by simpa [n, TubeFamily.enncard] using this)
      omega⟩
    exact IsEmpty.false (P.parent i)
  have hm_ne_zero : m ≠ 0 := hm_pos.ne'
  have hm_ne_top : m ≠ ⊤ := by
    simp [m, TubeFamily.enncard]

  let canonicalDelta : Kakeya.DeltaTube delta :=
    ⟨0, EuclideanSpace.single 0 1,
      by simp [EuclideanSpace.norm_eq] <;> norm_num⟩
  let canonicalRho : Kakeya.DeltaTube rho :=
    ⟨0, EuclideanSpace.single 0 1,
      by simp [EuclideanSpace.norm_eq] <;> norm_num⟩
  have h_fine_vol :
      ∀ i : Fin fine.card, (fine.tube i).volume = vdelta := by
    intro i
    exact tube_volume_eq (fine.tube i) canonicalDelta
  have h_coarse_vol :
      ∀ j : Fin coarse.card, (coarse.tube j).volume = vrho := by
    intro j
    exact tube_volume_eq (coarse.tube j) canonicalRho

  have h_fine_mass : fine.toBodyFamily.mass = n * vdelta := by
    change
      (∑ i : Fin fine.card, (fine.tube i).volume) = n * vdelta
    calc
      (∑ i : Fin fine.card, (fine.tube i).volume)
          = ∑ _i : Fin fine.card, vdelta := by
              apply Finset.sum_congr rfl
              intro i _
              exact h_fine_vol i
      _ = n * vdelta := by
        simp [n, TubeFamily.enncard, Finset.sum_const]

  have h_parent_body_vol :
      ∀ j : Fin coarse.card,
        ((dilatedTubeBodyFamily A coarse).body j).volume =
          a3 * vrho := by
    intro j
    change (dilatedTubeBody A (coarse.tube j)).volume = a3 * vrho
    rw [dilatedTubeBody_volume hrho hA_pos, h_coarse_vol j]
  have h_coarse_mass :
      (dilatedTubeBodyFamily A coarse).mass = m * (a3 * vrho) := by
    change
      (∑ j : Fin coarse.card,
        ((dilatedTubeBodyFamily A coarse).body j).volume) =
          m * (a3 * vrho)
    calc
      (∑ j : Fin coarse.card,
          ((dilatedTubeBodyFamily A coarse).body j).volume)
          = ∑ _j : Fin coarse.card, a3 * vrho := by
              apply Finset.sum_congr rfl
              intro j _
              exact h_parent_body_vol j
      _ = m * (a3 * vrho) := by
        simp [m, TubeFamily.enncard, Finset.sum_const]

  have hZ_exact :
      P.toFactoring.IsExactInducedShading Y Z rho :=
    inducedShading_isExact P.toFactoring Y rho hcoarse_meas

  have h_per_tube :
      ∀ i : Fin fine.card,
        vrho / vdelta * volume (Y.carrier i) ≤
          172800 * volume (Z.carrier (P.parent i)) := by
    intro i
    let j := P.parent i
    have hlocal :=
      dilated_per_tube_density_scaled
        hdelta hdelta_rho hrho_one hA
        (fine.tube i) (coarse.tube j) (P.nested i)
        (Y.carrier i) (Y.measurable_carrier i) (Y.subset_body i)
    rw [h_coarse_vol j] at hlocal
    have hinter :
        dilatedTubeCarrier A (coarse.tube j) ∩
            Metric.cthickening rho (Y.carrier i) ⊆
          Z.carrier j := by
      intro x hx
      rw [hZ_exact j]
      refine ⟨hx.1, ?_⟩
      apply Metric.cthickening_subset_of_subset rho
        (show Y.carrier i ⊆
          P.toFactoring.fiberShadedUnion Y j by
            intro y hy
            exact ⟨i, rfl, hy⟩)
      exact hx.2
    exact hlocal.trans (mul_le_mul_left' (measure_mono hinter) 172800)

  have h_sum_lower :
      vrho / vdelta * Y.mass ≤
        172800 *
          ∑ i : Fin fine.card, volume (Z.carrier (P.parent i)) := by
    calc
      vrho / vdelta * Y.mass
          = ∑ i : Fin fine.card,
              (vrho / vdelta * volume (Y.carrier i)) := by
              rw [Shading.mass]
              exact Finset.mul_sum Finset.univ
                (fun i : Fin fine.card => volume (Y.carrier i))
                (vrho / vdelta)
      _ ≤ ∑ i : Fin fine.card,
            (172800 * volume (Z.carrier (P.parent i))) :=
          Finset.sum_le_sum fun i _ => h_per_tube i
      _ = 172800 *
          ∑ i : Fin fine.card, volume (Z.carrier (P.parent i)) := by
            exact (Finset.mul_sum Finset.univ
              (fun i : Fin fine.card =>
                volume (Z.carrier (P.parent i))) 172800).symm

  let fibers := fun j : Fin coarse.card =>
    Finset.univ.filter (fun i : Fin fine.card => P.parent i = j)
  have h_fiber_decomp :
      ∑ i : Fin fine.card, volume (Z.carrier (P.parent i)) =
        ∑ j : Fin coarse.card,
          P.toFactoring.fiberCount j * volume (Z.carrier j) := by
    have h_disj : ∀ (j1 j2 : Fin coarse.card), j1 ≠ j2 →
        Disjoint (fibers j1) (fibers j2) := by
      intro j1 j2 hne
      simp only [Finset.disjoint_left, fibers,
        Finset.mem_filter, Finset.mem_univ, true_and]
      intro i h1 h2
      rw [h1] at h2
      exact hne h2
    have h_disj' :
        Set.PairwiseDisjoint
          (↑(Finset.univ : Finset (Fin coarse.card)) :
            Set (Fin coarse.card)) fibers := by
      intro j1 _ j2 _ hne
      exact h_disj j1 j2 hne
    have h_union :
        Finset.biUnion
            (Finset.univ : Finset (Fin coarse.card)) fibers =
          (Finset.univ : Finset (Fin fine.card)) := by
      apply Finset.ext
      intro i
      constructor
      · intro _
        simp
      · intro _
        exact Finset.mem_biUnion.mpr
          ⟨P.parent i, Finset.mem_univ _, by simp [fibers]⟩
    calc
      ∑ i : Fin fine.card, volume (Z.carrier (P.parent i))
          = ∑ j : Fin coarse.card,
              ∑ i ∈ fibers j,
                volume (Z.carrier (P.parent i)) := by
              rw [← Finset.sum_biUnion h_disj', h_union]
      _ = ∑ j : Fin coarse.card,
          P.toFactoring.fiberCount j * volume (Z.carrier j) := by
        apply Finset.sum_congr rfl
        intro j _
        calc
          ∑ i ∈ fibers j,
              volume (Z.carrier (P.parent i))
              = ∑ _i ∈ fibers j,
                  volume (Z.carrier j) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [(Finset.mem_filter.mp hi).2]
          _ = P.toFactoring.fiberCount j * volume (Z.carrier j) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            rfl

  have h_fiber_bound :
      ∀ j : Fin coarse.card,
        P.toFactoring.fiberCount j ≤ C * n / m := by
    intro j
    have hsum :
        ∑ k : Fin coarse.card, P.toFactoring.fiberCount j ≤
          ∑ k : Fin coarse.card, C * P.toFactoring.fiberCount k :=
      Finset.sum_le_sum fun k _ => hC.2 j k
    have hleft :
        ∑ _k : Fin coarse.card, P.toFactoring.fiberCount j =
          m * P.toFactoring.fiberCount j := by
      simp [m, TubeFamily.enncard, Finset.sum_const, nsmul_eq_mul]
    have hcount_sum :
        ∑ k : Fin coarse.card, P.toFactoring.fiberCount k = n := by
      calc
        ∑ k : Fin coarse.card, P.toFactoring.fiberCount k =
            fine.enncard := P.sum_factoringFiberCount
        _ = n := rfl
    have hright :
        ∑ k : Fin coarse.card, C * P.toFactoring.fiberCount k =
          C * n := by
      rw [← Finset.mul_sum, hcount_sum]
    rw [hleft, hright] at hsum
    have hdiv :
        (m * P.toFactoring.fiberCount j) / m ≤ (C * n) / m := by
      gcongr
    rw [show m * P.toFactoring.fiberCount j =
        P.toFactoring.fiberCount j * m by ring,
      ENNReal.mul_div_cancel_right hm_ne_zero hm_ne_top] at hdiv
    exact hdiv

  have h_sum_upper :
      ∑ j : Fin coarse.card,
          P.toFactoring.fiberCount j * volume (Z.carrier j) ≤
        (C * n / m) * Z.mass := by
    calc
      ∑ j : Fin coarse.card,
          P.toFactoring.fiberCount j * volume (Z.carrier j)
          ≤ ∑ j : Fin coarse.card,
              (C * n / m) * volume (Z.carrier j) :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_right' (h_fiber_bound j) _
      _ = (C * n / m) * Z.mass := by
        rw [Shading.mass]
        exact (Finset.mul_sum Finset.univ
          (fun j : Fin coarse.card => volume (Z.carrier j))
          (C * n / m)).symm

  have h_main :
      vrho / vdelta * Y.mass ≤
        172800 * ((C * n / m) * Z.mass) := by
    calc
      vrho / vdelta * Y.mass
          ≤ 172800 *
              ∑ i : Fin fine.card,
                volume (Z.carrier (P.parent i)) := h_sum_lower
      _ = 172800 *
            ∑ j : Fin coarse.card,
              P.toFactoring.fiberCount j * volume (Z.carrier j) := by
          rw [h_fiber_decomp]
      _ ≤ 172800 * ((C * n / m) * Z.mass) := by
          gcongr

  have h_vdelta_cancel :
      vdelta * vdelta⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hvdelta_ne_zero hvdelta_ne_top
  have h_m_cancel : m * m⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hm_ne_zero hm_ne_top
  have h_goal1 :
      a3 * m * vrho * Y.mass ≤
        172800 * a3 * C * n * vdelta * Z.mass := by
    have hmult :=
      mul_le_mul_left' h_main (a3 * vdelta * m)
    have hleft :
        a3 * vdelta * m * (vrho / vdelta * Y.mass) =
          a3 * m * vrho * Y.mass := by
      simp only [div_eq_mul_inv]
      rw [show
        a3 * vdelta * m * (vrho * vdelta⁻¹ * Y.mass) =
          a3 * m * vrho * (vdelta * vdelta⁻¹) * Y.mass by ring,
        h_vdelta_cancel, mul_one]
    have hright :
        a3 * vdelta * m *
            (172800 * ((C * n / m) * Z.mass)) =
          172800 * a3 * C * n * vdelta * Z.mass := by
      simp only [div_eq_mul_inv]
      rw [show
        a3 * vdelta * m *
            (172800 * (C * n * m⁻¹ * Z.mass)) =
          172800 * a3 * C * n * vdelta *
            (m * m⁻¹) * Z.mass by ring,
        h_m_cancel, mul_one]
    rw [hleft, hright] at hmult
    exact hmult

  have h_nvdelta_ne_zero : n * vdelta ≠ 0 :=
    mul_ne_zero hn_ne_zero hvdelta_ne_zero
  have h_nvdelta_ne_top : n * vdelta ≠ ⊤ :=
    ENNReal.mul_ne_top hn_ne_top hvdelta_ne_top
  have h_final :
      (a3 * m * vrho * Y.mass) / (n * vdelta) ≤
        172800 * a3 * C * Z.mass := by
    have hscaled :
        a3 * m * vrho * Y.mass ≤
          (172800 * a3 * C * Z.mass) * (n * vdelta) := by
      calc
        a3 * m * vrho * Y.mass
            ≤ 172800 * a3 * C * n * vdelta * Z.mass := h_goal1
        _ = (172800 * a3 * C * Z.mass) * (n * vdelta) := by ring
    calc
      (a3 * m * vrho * Y.mass) / (n * vdelta)
          ≤ ((172800 * a3 * C * Z.mass) * (n * vdelta)) /
              (n * vdelta) := by
                gcongr
      _ = 172800 * a3 * C * Z.mass := by
        rw [ENNReal.mul_div_cancel_right
          h_nvdelta_ne_zero h_nvdelta_ne_top]

  have hlhs :
      (Y.mass / fine.toBodyFamily.mass) *
          (dilatedTubeBodyFamily A coarse).mass =
        (a3 * m * vrho * Y.mass) / (n * vdelta) := by
    rw [h_fine_mass, h_coarse_mass]
    simp only [div_eq_mul_inv]
    ring
  rw [hlhs]
  exact h_final

end Kakeya.Streamlined
