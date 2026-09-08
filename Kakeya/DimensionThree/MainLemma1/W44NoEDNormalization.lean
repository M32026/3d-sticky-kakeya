/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.W44NormalizationCardPort

/-!
# Selection-free normalization for the estimate WZ middle branch

The honest replacement constructed by fine normalization is canonical on the whole ambient
index set.  Essential distinctness is needed only by the optional selection step.  Running that
step on a singleton exposes the canonical replacement, after which the one-sided comparable-body
transport applies to the original family without changing its index set.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya.ml1Boot.W44NoED

noncomputable section

universe u

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [MeasurableSpace E] [BorelSpace E]

/-- Geometric loss of the selection-free honest replacement. -/
noncomputable def C : NNReal :=
  (4 * _root_.Tube.normalization.C 3) ^ 6

theorem one_le_C : 1 <= C := by
  unfold C
  exact one_le_pow₀ (one_le_mul (by norm_num) (_root_.Tube.normalization.one_le_C 3))

/-- Normalize an arbitrary nonempty shaded tube family without an essential-distinctness
hypothesis and without selecting indices.

The card and the two-sided Q band are therefore unchanged.  Multiplicity is exactly preserved,
fullness loses one fixed geometric factor, and the Frostman constant loses two such factors. -/
theorem exists_normalization_noED [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {tau rho : NNReal} (htau0 : 0 < tau) (htaurho : tau <= rho) (hrho1 : rho <= 1)
    {iota : Type u} {s ambient : Finset iota} (Trho : Tube rho E)
    (Ttau : iota -> ShadedTube tau E)
    (hs : s.Nonempty) (hsambient : s ⊆ ambient)
    (hcontain : ∀ i ∈ ambient, (Ttau i).carrier ⊆ Trho.carrier)
    (hfull : 0 < ShadedBody.fullness s (fun i => (Ttau i).toShadedBody)) :
    exists V : iota -> ShadedTube (fineScale tau rho) E,
      (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
      ShadedBody.multiplicity s (fun i => (Ttau i).toShadedBody) =
        ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ∧
      C⁻¹ * ShadedBody.fullness s (fun i => (Ttau i).toShadedBody) <=
        ShadedBody.fullness s (fun i => (V i).toShadedBody) ∧
      frostmanConstIn s (fun i => (V i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall <=
        ((C ^ 2 : NNReal) : ENNReal) *
          frostmanConstIn s (fun i => (Ttau i).toConvexSpaceBody)
            Trho.toConvexSpaceBody := by
  classical
  have hrho0 : 0 < rho := htau0.trans_le htaurho
  have htau1 : tau <= 1 := htaurho.trans hrho1
  have hmass_ne : (∑ i ∈ s, volume (Ttau i).shade) ≠ 0 := by
    intro hmass
    have hfullENN :
        (0 : ENNReal) <
          (ShadedBody.fullness s (fun i => (Ttau i).toShadedBody) : ENNReal) :=
      ENNReal.coe_pos.mpr hfull
    rw [ShadedBody.coe_fullness] at hfullENN
    simp [hmass] at hfullENN
  have hmass : 0 < ∑ i ∈ s, volume (Ttau i).shade := pos_iff_ne_zero.mpr hmass_ne
  obtain ⟨i0, hi0, hshade0⟩ := Finset.sum_pos_iff.mp hmass
  have hcarrier0 : 0 < volume (Ttau i0).carrier :=
    (_root_.Tube.volume_pos_and_lt_top htau0 htau1 (Ttau i0).toTube).1
  have hcarrier0_top : volume (Ttau i0).carrier ≠ ⊤ :=
    (_root_.Tube.volume_pos_and_lt_top htau0 htau1 (Ttau i0).toTube).2.ne
  let mu0 : ENNReal := volume (Ttau i0).shade / volume (Ttau i0).carrier
  have hmu0 : 0 < mu0 := ENNReal.div_pos hshade0.ne' hcarrier0_top
  have hmu0_mul : mu0 * volume (Ttau i0).carrier = volume (Ttau i0).shade :=
    ENNReal.div_mul_cancel hcarrier0.ne' hcarrier0_top
  have hsingle : ({i0} : Finset iota).Nonempty := by simp
  have hsingle_sub : ({i0} : Finset iota) ⊆ ambient := by
    exact (by simpa using hi0 : ({i0} : Finset iota) ⊆ s).trans hsambient
  have hsingle_ED : (({i0} : Finset iota) : Set iota).Pairwise
      (fun i j => IsEssentiallyDistinct (Ttau i).carrier (Ttau j).carrier) := by
    simp
  have hsingle_dens : ∀ i ∈ ({i0} : Finset iota),
      ((1 : NNReal) : ENNReal)⁻¹ * mu0 * volume (Ttau i).carrier <=
          volume (Ttau i).shade ∧
        volume (Ttau i).shade <=
          ((1 : NNReal) : ENNReal) * mu0 * volume (Ttau i).carrier := by
    intro i hi
    have hi' : i = i0 := by simpa using hi
    subst i
    simpa using ⟨hmu0_mul.le, hmu0_mul.ge⟩
  obtain ⟨_s', _hs'sub, _hs'ne, V, _hVED, _hcard, _hVball_selected,
      _hmult_selected, _hfull_selected, _hfrost_selected, himage, hshade, hvol,
      hVtube, hambient⟩ :=
    W44NormalizationPort.exists_fineNormalization_constructionVisible_withCard
      hdim htau0 htaurho hrho1 (by norm_num : (1 : NNReal) <= 1) hmu0
      Trho Ttau hsingle hsingle_sub hcontain hsingle_ED hsingle_dens

  let Cn : NNReal := _root_.Tube.normalization.C 3
  have hCn1 : 1 <= Cn := _root_.Tube.normalization.one_le_C 3
  have hCn0 : 0 < (Cn : Real) := by exact_mod_cast (zero_lt_one.trans_le hCn1)
  obtain ⟨L, hL⟩ := _root_.Tube.exists_rescaleEquiv hrho0 hCn0 Trho
  have hcont : Continuous L := AffineEquiv.continuous_of_finiteDimensional L
  have hemb : MeasurableEmbedding L :=
    (AffineEquiv.toContinuousAffineEquiv L).toHomeomorph.measurableEmbedding
  let W : iota -> ShadedBody E := fun i =>
    ((Ttau i).toShadedBody).affineImage L.toAffineMap hcont hemb
  have hWcarrier : ∀ i ∈ ambient,
      (W i).carrier = Trho.rescaleMap (Cn : Real) '' (Ttau i).carrier := by
    intro i hi
    dsimp [W]
    change L.toAffineMap '' (Ttau i).carrier =
      Trho.rescaleMap (Cn : Real) '' (Ttau i).carrier
    rw [hL]
  have hWshade : ∀ i ∈ ambient,
      (W i).shade = Trho.rescaleMap (Cn : Real) '' (Ttau i).shade := by
    intro i hi
    dsimp [W]
    change L.toAffineMap '' (Ttau i).shade =
      Trho.rescaleMap (Cn : Real) '' (Ttau i).shade
    rw [hL]
  have hxy : ∀ i : iota,
      Trho.rescaleMap (Cn : Real) (Ttau i).x ≠
        Trho.rescaleMap (Cn : Real) (Ttau i).y := by
    intro i h
    rw [← hL] at h
    exact (fun hne => hne (L.injective h)) (fun hxy0 => by
      have hd := (Ttau i).toTube.dist_eq_one
      rw [hxy0] at hd
      simp at hd)
  have hscalequarter : (fineScale tau rho : Real) <= 1 / 4 := by
    exact_mod_cast (fineScale_bounds htaurho hrho0).2.1
  have hVball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro i hi
    have hv := hVtube i (hsambient hi) (hxy i)
    rw [hv]
    apply _root_.Tube.centredExtension_subset_closedBall (hxy i)
    · apply Metric.mem_closedBall.mp
      apply hambient
      exact ⟨(Ttau i).x, hcontain i (hsambient hi) ((Ttau i).toTube.x_mem_carrier), rfl⟩
    · apply Metric.mem_closedBall.mp
      apply hambient
      exact ⟨(Ttau i).y, hcontain i (hsambient hi) ((Ttau i).toTube.y_mem_carrier), rfl⟩
    · exact hscalequarter
  have hshadeVW : ∀ i ∈ s, (V i).shade = (W i).shade := by
    intro i hi
    rw [hshade i (hsambient hi), hWshade i (hsambient hi)]
  have hsubWV : ∀ i ∈ s,
      (W i).toConvexSpaceBody <= (V i).toConvexSpaceBody := by
    intro i hi
    change (W i).carrier ⊆ (V i).carrier
    rw [hWcarrier i (hsambient hi)]
    exact himage i (hsambient hi)
  have hVK : ∀ i ∈ s,
      (V i).toConvexSpaceBody <= ConvexSpaceBody.closedUnitBall := by
    intro i hi
    change (V i).carrier ⊆ ConvexSpaceBody.closedUnitBall.carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier]
    exact hVball i hi
  have hvolVW : ∀ i ∈ s,
      volume (V i).carrier <= (C : ENNReal) * volume (W i).carrier := by
    intro i hi
    simpa [C, Cn, hWcarrier i (hsambient hi)] using hvol i (hsambient hi)
  have htr := _root_.Tube.comparableTransport_oneSided one_le_C s W
    (fun i => (V i).toShadedBody) ConvexSpaceBody.closedUnitBall
    hshadeVW hsubWV hVK hvolVW
  have hmultUW : ShadedBody.multiplicity s (fun i => (Ttau i).toShadedBody) =
      ShadedBody.multiplicity s W := by
    simpa [W] using (ShadedBody.multiplicity_affineImage s
      (fun i => (Ttau i).toShadedBody) L hcont hemb).symm
  have hfullUW : ShadedBody.fullness s (fun i => (Ttau i).toShadedBody) =
      ShadedBody.fullness s W := by
    simpa [W] using (ShadedBody.fullness_affineImage s
      (fun i => (Ttau i).toShadedBody) L hcont hemb).symm

  let K' : ConvexSpaceBody E :=
    Trho.toConvexSpaceBody.affineImage L.toAffineMap hcont
  have hK'carrier : K'.carrier = Trho.rescaleMap (Cn : Real) '' Trho.carrier := by
    dsimp [K']
    change L.toAffineMap '' Trho.carrier = Trho.rescaleMap (Cn : Real) '' Trho.carrier
    rw [hL]
  have hK' : K' <= ConvexSpaceBody.closedUnitBall := by
    change K'.carrier ⊆ ConvexSpaceBody.closedUnitBall.carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier, hK'carrier]
    exact hambient.trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hK'vol : volume K'.carrier ≠ 0 := by
    dsimp [K']
    rw [ConvexSpaceBody.volume_affineImage]
    apply mul_ne_zero
    · exact (ENNReal.ofReal_eq_zero.not).mpr
        (not_le.mpr (abs_pos.mpr (LinearEquiv.isUnit_det' L.linear).ne_zero))
    · exact (_root_.Tube.volume_pos_and_lt_top hrho0 hrho1 Trho).1.ne'
  have hWK' : ∀ i ∈ s, (W i).toConvexSpaceBody <= K' := by
    intro i hi
    change (W i).carrier ⊆ K'.carrier
    rw [hWcarrier i (hsambient hi), hK'carrier]
    exact Set.image_mono (hcontain i (hsambient hi))
  have hofR : ENNReal.ofReal ((4 * (Cn : Real)) ^ 6) = (C : ENNReal) := by
    have h4Cn : 0 <= (4 : Real) * (Cn : Real) := by positivity
    rw [ENNReal.ofReal_pow h4Cn]
    change (ENNReal.ofReal ((4 : Real) * (Cn : Real))) ^ 6 = _
    rw [show ENNReal.ofReal ((4 : Real) * (Cn : Real)) =
        ((4 * Cn : NNReal) : ENNReal) by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1]
    simp [C, Cn]
  have hratio : volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier <=
      (C : ENNReal) * volume K'.carrier := by
    have h := _root_.Tube.volume_closedBall_one_le_mul_volume_rescale_image_ambient
      (E := E) hdim hrho0 (by exact_mod_cast hCn1) Trho
    calc
      volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier <=
          ENNReal.ofReal ((4 * (Cn : Real)) ^ 6) *
            volume (Trho.rescaleMap (Cn : Real) '' Trho.carrier) := by
          change volume (Metric.closedBall (0 : E) 1) <= _
          exact h
      _ = (C : ENNReal) * volume K'.carrier := by rw [hofR, hK'carrier]
  have hfrostAmbient : frostmanConstIn s (fun i => (W i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall <=
        (C : ENNReal) * frostmanConstIn s (fun i => (W i).toConvexSpaceBody) K' :=
    Kakeya.ml1Boot.W44NormalizationPort.frostmanConstIn_closedUnitBall_le_of_ambient
      (u := s) (𝕎 := W) (K' := K') (Cv := C) hK' hK'vol hWK' hratio
  have hFrel : frostmanConstIn s (fun i => (W i).toConvexSpaceBody) K' =
      frostmanConstIn s (fun i => (Ttau i).toConvexSpaceBody)
        Trho.toConvexSpaceBody := by
    have h := ConvexSpaceBody.frostmanConstIn_affineImage s
      (fun i => (Ttau i).toConvexSpaceBody) Trho.toConvexSpaceBody L hcont
    dsimp [W, K']
    exact h
  refine ⟨V, hVball, hmultUW.trans htr.1.symm, ?_, ?_⟩
  · rw [hfullUW]
    exact htr.2.1
  · calc
      frostmanConstIn s (fun i => (V i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall <=
        (C : ENNReal) * frostmanConstIn s (fun i => (W i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall := htr.2.2
      _ <= (C : ENNReal) * ((C : ENNReal) *
          frostmanConstIn s (fun i => (W i).toConvexSpaceBody) K') := by gcongr
      _ = ((C ^ 2 : NNReal) : ENNReal) *
          frostmanConstIn s (fun i => (Ttau i).toConvexSpaceBody)
            Trho.toConvexSpaceBody := by
        rw [hFrel]
        simp [pow_two, ENNReal.coe_mul, mul_assoc]

#print axioms exists_normalization_noED

end

end Kakeya.ml1Boot.W44NoED
