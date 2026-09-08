module

public import Kakeya.DimensionThree.MainLemma1.Factoring

@[expose] public section

open MeasureTheory ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- The product-only content of one-scale factoring, directly from the axiom-clean undilated GWZ
estimate.  No uniformity or density output is requested. -/
theorem exists_oneScaleProductOnly (hdim : Module.finrank ℝ E = 3)
    {σ ρ : NNReal} (hσ0 : 0 < σ) (hσρ : σ ≤ ρ) (hρ1 : ρ ≤ 1)
    {ι κ : Type u} [DecidableEq κ] {s : Finset ι} {t : Finset κ}
    (V : ι → ShadedTube σ E) (Vρ : κ → Tube ρ E) (p : ι → κ)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamily s (fun i => (V i).toTube) t Vρ p)
    (hmass : 0 < ∑ i ∈ s, volume (V i).shade) :
    ∃ t' ⊆ t, ∃ (Zρ : κ → ShadedTube ρ E) (Z' : ι → ShadedTube σ E),
      t'.Nonempty ∧
      0 < ∑ k ∈ t', volume (Zρ k).shade ∧
      (∀ k ∈ t', (Zρ k).toTube = Vρ k) ∧
      (∀ i ∈ s, p i ∈ t' → (Z' i).toTube = (V i).toTube) ∧
      ∀ k ∈ t', ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
        ≤ (factorOneScale.C s.card σ : ENNReal)
          * ShadedBody.multiplicity t' (fun k' => (Zρ k').toShadedBody)
          * ShadedBody.multiplicity (fibre (s.filter fun i => p i ∈ t') p k)
              (fun i => (Z' i).toShadedBody) := by
  classical
  have hcover : ∀ i ∈ s, (V i).toShadedBody.toConvexSpaceBody ≤
      (Vρ (p i)).toConvexSpaceBody := by
    intro i hi
    simpa using hparent.le_parent i hi
  let F : ShadedBody.FactorFamily E ι κ :=
    { innerSet := s
      innerBody := fun i => (V i).toShadedBody
      outerSet := t
      outerBody := fun k => (Vρ k).toConvexSpaceBody
      parent := p
      parent_mem := hparent.mapsTo
      inner_le_parent := hcover }
  obtain ⟨G, hGouter, hGinner, hGparent, hOuterBody, hInnerBody, hne, _hfull,
      _href, hmult, _hcontain, _hvol⟩ :=
    ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated hσ0 ⟨hσρ, hρ1⟩
      F V Vρ (by intros; rfl) (by intros; rfl) (by
        intro i hi
        simpa [F] using hball i hi)
  let t' : Finset κ := G.outerSet
  let Sout : κ → ShadedBody E := G.outerBody
  let Sin : ι → ShadedBody E := G.innerBody
  have ht't : t' ⊆ t := by simpa [t'] using hGouter
  have hGinner' : G.innerSet = s.filter (fun i => p i ∈ t') := by
    simpa [F, t'] using hGinner
  have hOutCarrier : ∀ k ∈ t', (Sout k).carrier = (Vρ k).carrier := by
    intro k hk
    have h := hOuterBody k hk
    simpa [t', Sout, F] using congrArg (fun b : ConvexSpaceBody E => b.carrier) h
  let Zρ : κ → ShadedTube ρ E := fun k =>
    if hk : k ∈ t' then
      { toTube := Vρ k
        shade := (Sout k).shade
        measurableSet_shade := (Sout k).measurableSet_shade
        shade_subset := by rw [← hOutCarrier k hk]; exact (Sout k).shade_subset }
    else
      { toTube := Vρ k
        shade := ∅
        measurableSet_shade := MeasurableSet.empty
        shade_subset := by simp }
  let Z' : ι → ShadedTube σ E := fun i =>
    if hi : i ∈ s.filter (fun i => p i ∈ t') then
      { toTube := (V i).toTube
        shade := (Sin i).shade
        measurableSet_shade := (Sin i).measurableSet_shade
        shade_subset := by
          have hbody : (Sin i).toConvexSpaceBody = (V i).toConvexSpaceBody := by
            simpa [Sin, F] using hInnerBody i (Finset.mem_filter.mp hi).1
          change (Sin i).shade ⊆ (V i).toConvexSpaceBody.carrier
          rw [← hbody]
          exact (Sin i).shade_subset }
    else
      { toTube := (V i).toTube
        shade := ∅
        measurableSet_shade := MeasurableSet.empty
        shade_subset := by simp }
  have hsumInner : 0 < ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
    have hcoef : 0 < (factorOneScale.C s.card σ : ENNReal)⁻¹ := by
      exact ENNReal.inv_pos.mpr ENNReal.coe_ne_top
    have hpos := ENNReal.mul_pos hcoef.ne' hmass.ne'
    apply hpos.trans_le
    have hhref := _href.2
    rw [hdim] at hhref
    have hhref2 := hhref
    simp only [F] at hhref2
    have hCeq : factorOneScale.C s.card σ =
        ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C 3 s.card σ 1 := by rfl
    have hC0 : factorOneScale.C s.card σ ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1)
        (one_le_factorOneScale_C s.card σ))
    have hC0orig :
        ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C 3 s.card σ 1 ≠ 0 := by
      simpa [hCeq] using hC0
    rw [ENNReal.coe_inv hC0orig] at hhref2
    rw [hCeq]
    exact hhref2
  have hsumOuter : 0 < ∑ k ∈ t', volume (Sout k).shade := by
    obtain ⟨i, hi, hvi⟩ := Finset.sum_pos_iff.mp hsumInner
    have hparent : G.parent i ∈ t' := G.parent_mem i hi
    have hmono : volume (G.innerBody i).shade ≤
        volume (G.outerBody (G.parent i)).shade := by
      exact measure_mono (G.shade_subset_parent i hi)
    have hvp : 0 < volume (G.outerBody (G.parent i)).shade := hvi.trans_le hmono
    have hvp' : 0 < volume (Sout (G.parent i)).shade := by simpa [Sout] using hvp
    have hle : volume (Sout (G.parent i)).shade ≤
        ∑ k ∈ t', volume (Sout k).shade := by
      exact Finset.single_le_sum (f := fun k => volume (Sout k).shade)
        (fun k hk => by positivity) hparent
    exact hvp'.trans_le hle
  have hZρshade : ∀ k ∈ t', (Zρ k).shade = (Sout k).shade := by
    intro k hk; simp [Zρ, hk]
  have hZρcarrier : ∀ k ∈ t', (Zρ k).carrier = (Sout k).carrier := by
    intro k hk
    have : (Zρ k).carrier = (Vρ k).carrier := by simp [Zρ, hk]
    rw [this, hOutCarrier k hk]
  have hZ'shade : ∀ i ∈ s.filter (fun i => p i ∈ t'), (Z' i).shade = (Sin i).shade := by
    intro i hi
    simp [Z', (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2]
  refine ⟨t', ht't, Zρ, Z', ?_, ?_, ?_, ?_, ?_⟩
  · exact hne (by simpa [F] using hmass)
  · calc
      0 < ∑ k ∈ t', volume (Sout k).shade := hsumOuter
      _ = ∑ k ∈ t', volume (Zρ k).shade := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (hZρshade k hk).symm ▸ rfl
  · intro k hk; simp [Zρ, hk]
  · intro i hi hip; simp [Z', hi, hip]
  · intro k hk
    have hGfiber : G.fiber k = fibre (s.filter fun i => p i ∈ t') p k := by
      simp [ShadedBody.ShadedFactorFamily.fiber, fibre, F, hGinner', hGparent]
    have hm := hmult k hk
    have hm' : ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
        (factorOneScale.C s.card σ : ENNReal) * ShadedBody.multiplicity t' Sout *
          ShadedBody.multiplicity (fibre (s.filter fun i => p i ∈ t') p k) Sin := by
      simpa [factorOneScale.C, hdim, F, t', Sout, Sin, hGfiber] using hm
    have houtEq : ShadedBody.multiplicity t' (fun j => (Zρ j).toShadedBody) =
        ShadedBody.multiplicity t' Sout := by
      unfold ShadedBody.multiplicity
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        simp [hZρshade j hj]
      · apply congrArg volume
        apply Set.iUnion₂_congr
        intro j hj
        simp [hZρshade j hj]
    have hinEq : ShadedBody.multiplicity (fibre (s.filter fun i => p i ∈ t') p k)
          (fun i => (Z' i).toShadedBody) =
        ShadedBody.multiplicity (fibre (s.filter fun i => p i ∈ t') p k) Sin := by
      unfold ShadedBody.multiplicity
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        have hi' : i ∈ s.filter (fun i => p i ∈ t') :=
          (Finset.mem_filter.mp hi).1
        simp [hZ'shade i hi']
      · apply congrArg volume
        apply Set.iUnion₂_congr
        intro i hi
        have hi' : i ∈ s.filter (fun i => p i ∈ t') :=
          (Finset.mem_filter.mp hi).1
        simp [hZ'shade i hi']
    simpa [houtEq, hinEq] using hm'

end Kakeya.ml1Boot

#print axioms Kakeya.ml1Boot.exists_oneScaleProductOnly
