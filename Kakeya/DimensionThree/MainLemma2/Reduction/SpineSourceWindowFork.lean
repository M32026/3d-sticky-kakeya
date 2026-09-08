/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFibrePerLevelFactoring

@[expose] public section

open MeasureTheory Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

open Classical in
/-- The source window: strict level endpoints and weak ratio endpoints. -/
noncomputable def sourceWindowLevels (δ : NNReal) (ε : ℝ) (a b : ℕ) : Finset ℕ :=
  (Finset.Ioo a b).filter fun k =>
    ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ε)
        ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ) ∧
    (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ)
        ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ε

theorem source_mem_windowLevels_iff (δ : NNReal) (ε : ℝ) (a b k : ℕ) :
    k ∈ sourceWindowLevels δ ε a b ↔ a < k ∧ k < b ∧
      ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ε)
          ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ) ∧
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ)
          ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ε := by
  simp only [sourceWindowLevels, Finset.mem_filter, Finset.mem_Ioo, and_assoc]

section Factoring

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open Classical in
/-- The actual capture formula restricted to one named finite domain. -/
def SourceFactoringCaptureOn (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    (Cf : ENNReal) (p : ℕ) (J : Finset ℕ) (jp : ι)
    (F : ℕ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ k ∈ J, Kakeya.maxDensity (𝒰.nodesUnder k p jp)
      (fun j => (𝒰.cover.tube k j).toConvexSpaceBody)
    ≤ Cf * Kakeya.densityIn (𝒰.nodesUnder k p jp)
      (fun j => (𝒰.cover.tube k j).toConvexSpaceBody) (F k)

/-- The volume side of the fork, on exactly the same finite domain. -/
def SourceFactoringVolumeOn (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    (v : ENNReal) (p : ℕ) (J : Finset ℕ) (jp : ι)
    (F : ℕ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ k ∈ J, v * volume (𝒰.cover.tube p jp).carrier ≤ volume (F k).carrier

/-- The eccentric discriminant retains the selected domain member and factor body. -/
def SourceSmallFactorOn (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    (v : ENNReal) (p : ℕ) (J : Finset ℕ) (jp : ι)
    (F : ℕ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ k ∈ J, volume (F k).carrier < v * volume (𝒰.cover.tube p jp).carrier

theorem source_factoringVolume_or_smallFactor
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    (v : ENNReal) (p : ℕ) (J : Finset ℕ) (jp : ι)
    (F : ℕ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    SourceFactoringVolumeOn 𝒰 v p J jp F ∨ SourceSmallFactorOn 𝒰 v p J jp F := by
  by_cases hvol : SourceFactoringVolumeOn 𝒰 v p J jp F
  · exact Or.inl hvol
  · right
    simpa only [SourceFactoringVolumeOn, SourceSmallFactorOn, not_forall,
      not_le, exists_prop] using hvol

theorem source_empty_window_fork
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    (v : ENNReal) (p : ℕ) (J : Finset ℕ) (jp : ι)
    (F : ℕ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (hJ : J = ∅) :
    SourceFactoringVolumeOn 𝒰 v p J jp F ∧ ¬ SourceSmallFactorOn 𝒰 v p J jp F := by
  simp [SourceFactoringVolumeOn, SourceSmallFactorOn, hJ]

open Classical in
theorem source_fillBinder_or_smallFactor
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    {κ : ℝ} {a p : ℕ} {J : Finset ℕ} {Cf v : ENNReal}
    (hCf0 : Cf ≠ 0) (hCftop : Cf ≠ ⊤)
    (hk0 : ∀ jp : ι, volume (𝒰.cover.tube p jp).carrier ≠ 0)
    (hktop : ∀ jp : ι, volume (𝒰.cover.tube p jp).carrier ≠ ⊤)
    {F : ι → ℕ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hcap : ∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ,
      SourceFactoringCaptureOn 𝒰 Cf p J jp (F jp))
    (hnum : ENNReal.ofReal κ * Cf ≤ v) :
    (∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ,
      ∀ k ∈ J, FillAt 𝒰 κ p k jp) ∨
    (∃ jθ ∈ 𝒰.cover.indexSet a, ∃ jp ∈ 𝒰.nodesUnder p a jθ,
      SourceSmallFactorOn 𝒰 v p J jp (F jp)) := by
  by_cases hvol : ∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ,
      SourceFactoringVolumeOn 𝒰 v p J jp (F jp)
  · left
    intro jθ hjθ jp hjp k hk
    exact fillAt_of_factoring_body 𝒰 (F jp k) hCf0 hCftop (hk0 jp) (hktop jp)
      (hcap jθ hjθ jp hjp k hk) (hvol jθ hjθ jp hjp k hk) hnum
  · right
    push Not at hvol
    obtain ⟨jθ, hjθ, jp, hjp, hnot⟩ := hvol
    exact ⟨jθ, hjθ, jp, hjp,
      (source_factoringVolume_or_smallFactor 𝒰 v p J jp (F jp)).resolve_left hnot⟩

end Factoring

section Floor

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

open Classical in
/-- A fresh restricted fork. Its F output is the existing, unchanged floor predicate. -/
theorem source_floorHypothesisAt_or_smallFactor {β ϖ ε₁ η' κ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hη' : 0 < η') (hκ : 0 < κ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (𝒰 : Tube.UniformTubeSet s (fun i => (V i).toTube) (Tube.ssfGridLen δ) Cu)
    (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (V i).toTube.carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {Cstar : ENNReal} {a b m : ℕ}
    (hwin : ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar
      (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
      (ML2Spine.spineCount ϖ ε₁) a b m)
    (hCstar : Cstar ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)))
    (hcapη : η' ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2
      * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 64)
    (hgap : ∀ p k : ℕ, a ≤ p → p < k → k ≤ b →
      4 * (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ)
        ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ))
    {p : ℕ} (hap : a ≤ p)
    (hfirst : ∀ k ∈ sourceWindowLevels δ (ML2Spine.spineDiv ϖ ε₁) a b, p < k)
    (hpar : ParentAdmissible 𝒰 η' a p)
    {Cf v : ENNReal} (hCf0 : Cf ≠ 0) (hCftop : Cf ≠ ⊤)
    (hk0 : ∀ jp : ι, volume (𝒰.cover.tube p jp).carrier ≠ 0)
    (hktop : ∀ jp : ι, volume (𝒰.cover.tube p jp).carrier ≠ ⊤)
    {F : ι → ℕ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hcap : ∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ,
      SourceFactoringCaptureOn 𝒰 Cf p
        (sourceWindowLevels δ (ML2Spine.spineDiv ϖ ε₁) a b) jp (F jp))
    (hnum : ENNReal.ofReal κ * Cf ≤ v)
    (hclose : ∀ k ∈ sourceWindowLevels δ (ML2Spine.spineDiv ϖ ε₁) a b,
      ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ))
          ^ (4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16)))
        * (Cstar ^ 2 * ENNReal.ofReal (twoScaleConst.{u, 0} (EuclideanSpace ℝ (Fin 3)) ^ 2)
          * (Cu : ENNReal) * (δ : ENNReal) ^ (-(2 * η'))
          * ((Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal) : ENNReal))
        ≤ ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ))
            ^ ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1))
          * ENNReal.ofReal κ
          * ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal) : ENNReal)) :
    FloorHypothesisAt β ϖ ε₁ gain dens η' 𝒰 a b m ∨
    (∃ jθ ∈ 𝒰.cover.indexSet a, ∃ jp ∈ 𝒰.nodesUnder p a jθ,
      ∃ k ∈ sourceWindowLevels δ (ML2Spine.spineDiv ϖ ε₁) a b,
        volume (F jp k).carrier < v * volume (𝒰.cover.tube p jp).carrier) := by
  rcases source_fillBinder_or_smallFactor 𝒰 hCf0 hCftop hk0 hktop hcap hnum with hfill | hsmall
  · left
    refine ⟨p, hap, ?_, hpar, ?_⟩
    · intro k hak hkb hlo hhi
      exact hfirst k ((source_mem_windowLevels_iff _ _ _ _ _).mpr ⟨hak, hkb, hlo, hhi⟩)
    intro jθ hjθ jp hjp m' ham' hm'b hlo hhi hpm'
    have hmem : m' ∈ sourceWindowLevels δ (ML2Spine.spineDiv ϖ ε₁) a b :=
      (source_mem_windowLevels_iff _ _ _ _ _).mpr ⟨ham', hm'b, hlo, hhi⟩
    have hδ1' : δ ≤ 1 := hδ1.le
    have hN : 0 < Tube.ssfGridLen δ :=
      (Nat.zero_lt_of_lt hwin.coarse_lt_fine).trans_le hwin.fine_le_gridLen
    have hm'N : m' ≤ Tube.ssfGridLen δ := hm'b.le.trans hwin.fine_le_gridLen
    obtain ⟨hwlo, hwhi⟩ := ceil_window_of_ratio hδ0 hδ1 hN ham' hm'b hlo hhi
    have hjp_idx : jp ∈ 𝒰.cover.indexSet p := by
      exact (Finset.mem_filter.mp hjp).1
    have hδpow_ne_top : ∀ y : ℝ, (δ : ENNReal) ^ y ≠ ⊤ := fun y => by
      rw [← ENNReal.coe_rpow_of_ne_zero hδ0.ne']
      exact ENNReal.coe_ne_top
    have hCtop : Cstar ≠ ⊤ := ne_top_of_le_ne_top (hδpow_ne_top _) hCstar
    have hgap4 : 4 * Tube.gridScale δ (Tube.ssfGridLen δ) m'
        ≤ Tube.gridScale δ (Tube.ssfGridLen δ) p := by
      exact_mod_cast hgap p m' hap hpm' hm'b.le
    have hchain := ofReal_ratio_le_maxDensity_nodesUnder_parent hδ0 hδ1' 𝒰 hs hball hwin hCtop hap
      hpar hpm'.le hm'N hgap4 hwlo hwhi hjθ hjp_idx
    have hfillp := hfill jθ hjθ jp hjp m' hmem
    unfold FillAt at hfillp
    set n := Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) with hn_def
    have hn : n = 3 := finrank_euclideanSpace_fin
    have hn1 : n - 1 = 2 := by rw [hn]
    have hall : ∀ j' ∈ 𝒰.nodesUnder m' p jp,
        (𝒰.cover.tube m' j').toConvexSpaceBody ≤ (𝒰.cover.tube p jp).toConvexSpaceBody := by
      intro j' hj'
      exact (Finset.mem_filter.mp hj').2
    have hsum := Kakeya.sum_volume_eq_densityIn_mul_volume'
      (s := 𝒰.nodesUnder m' p jp) (W := fun j' => (𝒰.cover.tube m' j').toConvexSpaceBody) hall
    have hsumle : ∑ j' ∈ 𝒰.nodesUnder m' p jp, volume ((𝒰.cover.tube m' j').toConvexSpaceBody).carrier
        ≤ ((𝒰.nodesUnder m' p jp).card : ENNReal)
          * (((Tube.volume_le.C n : NNReal) : ENNReal)
            * ((Tube.gridScale δ (Tube.ssfGridLen δ) m' : NNReal) : ENNReal) ^ (n - 1)) := by
      rw [← nsmul_eq_mul]
      exact Finset.sum_le_card_nsmul _ _ _
        (fun j' _ => Tube.volume_le (gridScale_le_one hδ1' _ _) (𝒰.cover.tube m' j'))
    have hUlo : ((Tube.le_volume.c n : NNReal) : ENNReal)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) p : NNReal) : ENNReal) ^ (n - 1)
        ≤ volume ((𝒰.cover.tube p jp).toConvexSpaceBody).carrier :=
      Tube.le_volume (𝒰.cover.tube p jp)
    have hkey : ENNReal.ofReal κ
          * Kakeya.maxDensity (𝒰.nodesUnder m' p jp)
              (fun j' => (𝒰.cover.tube m' j').toConvexSpaceBody)
          * (((Tube.le_volume.c n : NNReal) : ENNReal)
            * ((Tube.gridScale δ (Tube.ssfGridLen δ) p : NNReal) : ENNReal) ^ (n - 1))
        ≤ ((𝒰.nodesUnder m' p jp).card : ENNReal)
          * (((Tube.volume_le.C n : NNReal) : ENNReal)
            * ((Tube.gridScale δ (Tube.ssfGridLen δ) m' : NNReal) : ENNReal) ^ (n - 1)) :=
      (mul_le_mul' hfillp hUlo).trans ((le_of_eq hsum.symm).trans hsumle)
    have hcl := hclose m' hmem
    rw [ENNReal.ofReal_pow (twoScaleConst_pos.{u, 0} (EuclideanSpace ℝ (Fin 3))).le] at hcl
    set L := ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)) ^ ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1))
    set A := ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
      ^ (4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16)))
    set Δp := Kakeya.maxDensity (𝒰.nodesUnder m' p jp)
      (fun j' => (𝒰.cover.tube m' j').toConvexSpaceBody)
    set X' := Cstar ^ 2 * ENNReal.ofReal (twoScaleConst.{u, 0} (EuclideanSpace ℝ (Fin 3))) ^ 2
      * (Cu : ENNReal) * (δ : ENNReal) ^ (-(2 * η'))
    set Cv : ENNReal := ((Tube.volume_le.C n : NNReal) : ENNReal)
    set cv : ENNReal := ((Tube.le_volume.c n : NNReal) : ENNReal)
    set ρp : ENNReal := ((Tube.gridScale δ (Tube.ssfGridLen δ) p : NNReal) : ENNReal)
    set ρm : ENNReal := ((Tube.gridScale δ (Tube.ssfGridLen δ) m' : NNReal) : ENNReal)
    set K : ENNReal := ((𝒰.nodesUnder m' p jp).card : ENNReal)
    have hρmr : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) := by
      exact_mod_cast gridScale_pos hδ0 _ _
    have hρpr : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ) := by
      exact_mod_cast gridScale_pos hδ0 _ _
    have hρar : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) := by
      exact_mod_cast gridScale_pos hδ0 _ _
    have hLpos : 0 < L := ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (div_pos hρar hρmr) _)
    have hX'0 : X' ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hchain
      exact hLpos.ne' (le_antisymm hchain bot_le)
    have hX'top : X' ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top hCtop)
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) ENNReal.coe_ne_top) (hδpow_ne_top _)
    have hCv0 : Cv ≠ 0 := by
      dsimp only [Cv]
      exact_mod_cast (Tube.volume_le.C_pos n).ne'
    have hX0 : X' * Cv ≠ 0 := mul_ne_zero hX'0 hCv0
    have hXtop : X' * Cv ≠ ⊤ := ENNReal.mul_ne_top hX'top ENNReal.coe_ne_top
    have hmain : A * ρp ^ (n - 1) * (X' * Cv) ≤ K * ρm ^ (n - 1) * (X' * Cv) := by
      calc A * ρp ^ (n - 1) * (X' * Cv) = A * (X' * Cv) * ρp ^ (n - 1) := by ring
        _ ≤ L * ENNReal.ofReal κ * cv * ρp ^ (n - 1) := mul_le_mul' hcl le_rfl
        _ = L * (ENNReal.ofReal κ * (cv * ρp ^ (n - 1))) := by ring
        _ ≤ X' * Δp * (ENNReal.ofReal κ * (cv * ρp ^ (n - 1))) := mul_le_mul' hchain le_rfl
        _ = X' * (ENNReal.ofReal κ * Δp * (cv * ρp ^ (n - 1))) := by ring
        _ ≤ X' * (K * (Cv * ρm ^ (n - 1))) := mul_le_mul' le_rfl hkey
        _ = K * ρm ^ (n - 1) * (X' * Cv) := by ring
    have hfin : A * ρp ^ (n - 1) ≤ K * ρm ^ (n - 1) :=
      (ENNReal.mul_le_mul_iff_left hX0 hXtop).mp hmain
    rw [hn1] at hfin
    have hfin' := (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top))
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.pow_ne_top ENNReal.coe_ne_top))).mpr hfin
    have eA := ENNReal.toReal_ofReal (Real.rpow_nonneg (div_nonneg hρpr.le hρmr.le)
      (4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16)))
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
      ENNReal.toReal_natCast, eA] at hfin'
    have hΘp0 : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) := div_pos hρpr hρmr
    rw [Real.rpow_add hΘp0, Real.rpow_two, div_pow, div_mul_eq_mul_div,
      div_le_iff₀ (by positivity)]
    nlinarith [hfin']
  · exact Or.inr hsmall

end Floor

end Kakeya.ML2Core
