module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.Definitions
public import Kakeya.Tube.Dilate

@[expose] public section

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

lemma volume_carrier_eq_tubeVolume {δ : NNReal} {ι : Type u}
    (T : ι → ShadedTube δ Space3) (i : ι) :
    volume (T i).carrier = tubeVolume δ := by
  exact Tube.volume_carrier_eq_volume_carrier (T i).toTube (modelTube δ)

lemma iUnionShade_empty {δ : NNReal} {ι : Type u}
    (T : ι → ShadedTube δ Space3) :
    ShadedBody.iUnionShade (∅ : Finset ι) (fun i => (T i).toShadedBody) = ∅ := by
  simp [ShadedBody.iUnionShade]

lemma tubeVolume_pos_and_ne_top {δ : NNReal} (hδ : 0 < δ) :
    0 < tubeVolume δ ∧ tubeVolume δ ≠ ⊤ := by
  have hc0 : (Tube.le_volume.c 3 : ENNReal) ≠ 0 :=
    (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos 3)).ne'
  have hδ0 : (δ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hδ).ne'
  have hpow0 : (δ : ENNReal) ^ (3 - 1) ≠ 0 := pow_ne_zero _ hδ0
  constructor
  · exact lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero hc0 hpow0))
      (by simpa [tubeVolume] using Tube.le_volume (modelTube δ))
  · exact ne_of_lt (modelTube δ).isCompact.measure_lt_top

lemma katzTaoConvexWolffConstant_le {δ : NNReal} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) {C : ENNReal}
    (hC : 0 < C)
    (h : ∀ W : ConvexTestSet,
      ((@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s).card : ENNReal) ≤
        C * volume W.carrier * (tubeVolume δ)⁻¹) :
    katzTaoConvexWolffConstant s T ≤ C := by
  exact sInf_le ⟨hC, h⟩

lemma frostmanSlabWolffConstant_le {δ : NNReal} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) {C : ENNReal}
    (hC : 0 < C)
    (h : ∀ W : SlabTestSet,
      ((@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s).card : ENNReal) ≤
        C * volume W.carrier * (s.card : ENNReal)) :
    frostmanSlabWolffConstant s T ≤ C := by
  exact sInf_le ⟨hC, h⟩

lemma one_le_katzTaoConvexWolffConstant_of_nonempty {δ : NNReal} {ι : Type u}
    (hδ : 0 < δ) (s : Finset ι) (T : ι → ShadedTube δ Space3)
    (hs : s.Nonempty) :
    1 ≤ katzTaoConvexWolffConstant s T := by
  obtain ⟨i, hi⟩ := hs
  rw [katzTaoConvexWolffConstant]
  apply le_sInf
  intro C hC
  let W : ConvexTestSet :=
    { carrier := (T i).carrier
      convex_carrier := by
        rw [(T i).toTube.carrier_eq_cthickening]
        exact (convex_segment (𝕜 := ℝ) _ _).cthickening _ }
  have hiFilter : i ∈ @Finset.filter ι
      (fun j => (T j).carrier ⊆ W.carrier) (Classical.decPred _) s := by
    simp [W, hi]
  have hcount : (1 : ENNReal) ≤
      ((@Finset.filter ι (fun j => (T j).carrier ⊆ W.carrier)
        (Classical.decPred _) s).card : ENNReal) := by
    exact_mod_cast Finset.one_le_card.mpr ⟨i, hiFilter⟩
  have hbound := hC.2 W
  have hvol := tubeVolume_pos_and_ne_top hδ
  have hCbound : (1 : ENNReal) ≤ C * tubeVolume δ * (tubeVolume δ)⁻¹ := by
    exact hcount.trans (by simpa [W, volume_carrier_eq_tubeVolume T i] using hbound)
  simpa [mul_assoc, ENNReal.mul_inv_cancel hvol.1.ne' hvol.2] using hCbound

lemma e_factor_ge_d_factor {δ m ell A V : ENNReal} {η σ : ℝ}
    (hδ0 : δ ≠ 0) (hδ1 : δ ≤ 1) (hη : 0 ≤ η)
    (hσ0 : 0 ≤ σ) (hm1 : 1 ≤ m)
    (hm : m ≤ δ ^ (-η)) (hell : ell ≤ δ ^ (-η)) :
    δ ^ (η * (1 + σ)) * A * V * (A * V ^ (1 / 2 : ℝ)) ^ (-σ) ≤
      m ^ (-1 : ℝ) * A * V *
        (m ^ (-3 / 2 : ℝ) * ell * A * V ^ (1 / 2 : ℝ)) ^ (-σ) := by
  have hmInv : δ ^ η ≤ m ^ (-1 : ℝ) := by
    rw [ENNReal.rpow_neg] at hm
    rw [show (-1 : ℝ) = -(1 : ℝ) by ring, ENNReal.rpow_neg, ENNReal.rpow_one]
    simpa using ENNReal.inv_le_inv.mpr hm
  have hmPow : m ^ (-3 / 2 : ℝ) ≤ 1 := by
    exact ENNReal.rpow_le_one_of_one_le_of_neg hm1 (by norm_num)
  let X : ENNReal := A * V ^ (1 / 2 : ℝ)
  let B : ENNReal := m ^ (-3 / 2 : ℝ) * ell * A * V ^ (1 / 2 : ℝ)
  have hB : B ≤ δ ^ (-η) * X := by
    calc
      B = (m ^ (-3 / 2 : ℝ) * ell) * X := by simp [B, X, mul_assoc]
      _ ≤ δ ^ (-η) * X :=
        mul_le_mul_right' ((mul_le_of_le_one_left (by simp) hmPow).trans hell) X
  have hpow : (δ ^ (-η) * X) ^ (-σ) ≤ B ^ (-σ) := by
    have hanti {x y : ENNReal} (hxy : x ≤ y) : y ^ (-σ) ≤ x ^ (-σ) := by
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hxy hσ0)
    exact hanti hB
  have hid : δ ^ (η * σ) * X ^ (-σ) = (δ ^ (-η) * X) ^ (-σ) := by
    have hδtop : δ ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hδ1 ENNReal.one_lt_top)
    have hδpow0 : δ ^ (-η) ≠ 0 := by
      simp [ENNReal.rpow_eq_zero_iff, hδ0, hδtop]
    by_cases hX0 : X = 0
    · rcases hσ0.eq_or_lt with hσ | hσ
      · subst σ
        simp [hX0]
      · have hneg : -σ < 0 := by linarith
        have hδetaσ0 : δ ^ (η * σ) ≠ 0 := by
          simp [ENNReal.rpow_eq_zero_iff, hδ0, hδtop]
        simp [hX0, ENNReal.zero_rpow_of_neg hneg, hδetaσ0]
    · rw [ENNReal.mul_rpow_of_ne_zero hδpow0 hX0, ← ENNReal.rpow_mul]
      congr 1
      ring
  have hδtop : δ ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hδ1 ENNReal.one_lt_top)
  rw [show η * (1 + σ) = η + η * σ by ring,
    ENNReal.rpow_add _ _ hδ0 hδtop]
  have hmain : δ ^ η * δ ^ (η * σ) * A * V * X ^ (-σ) ≤
      m ^ (-1 : ℝ) * A * V * B ^ (-σ) := calc
    δ ^ η * δ ^ (η * σ) * A * V * X ^ (-σ) =
        (δ ^ η * A * V) * (δ ^ (η * σ) * X ^ (-σ)) := by ring
    _ ≤ (m ^ (-1 : ℝ) * A * V) * B ^ (-σ) :=
      mul_le_mul'
        (by simpa [mul_assoc] using mul_le_mul_right' hmInv (A * V)) (hid ▸ hpow)
    _ = m ^ (-1 : ℝ) * A * V * B ^ (-σ) := by ring
  simpa only [X, B] using hmain

theorem assertionE_implies_assertionD_sameUniverse {σ ω : ℝ} (hσ0 : 0 ≤ σ) :
    AssertionE.{u} σ ω → AssertionD.{u} σ ω := by
  intro hE ε hε
  obtain ⟨κ, ηE, hκ, hηE, hEall⟩ := hE (ε / 2) (by linarith)
  let ηD : ℝ := min ηE (ε / (2 * (1 + σ)))
  have honeσ : 0 < 1 + σ := by linarith
  have hbudgetDen : 0 < 2 * (1 + σ) := mul_pos (by norm_num) honeσ
  have hηD : 0 < ηD := lt_min hηE (div_pos hε hbudgetDen)
  have hηDηE : ηD ≤ ηE := min_le_left _ _
  have hbudget : ηD * (1 + σ) ≤ ε / 2 := by
    have hηDdiv : ηD ≤ ε / (2 * (1 + σ)) := min_le_right _ _
    calc
      ηD * (1 + σ) ≤ (ε / (2 * (1 + σ))) * (1 + σ) :=
        mul_le_mul_of_nonneg_right hηDdiv honeσ.le
      _ = ε / 2 := by field_simp
  refine ⟨κ, ηD, hκ, hηD, ?_⟩
  intro δ hδ ι s T hfamily hdense hm hell
  by_cases hs : s.Nonempty
  · have hm1 : 1 ≤ katzTaoConvexWolffConstant s T :=
      one_le_katzTaoConvexWolffConstant_of_nonempty hδ s T hs
    by_cases hδ1 : δ ≤ 1
    · have hdenseE : IsDense s T
          ⟨(δ : ℝ) ^ ηE, Real.rpow_nonneg δ.coe_nonneg ηE⟩ := by
        rw [IsDense] at hdense ⊢
        refine (mul_le_mul_right' ?_ _).trans hdense
        exact_mod_cast
          Real.rpow_le_rpow_of_exponent_ge (NNReal.coe_pos.mpr hδ) hδ1 hηDηE
      have hEbound := hEall δ hδ s T hfamily hdenseE
      let m := katzTaoConvexWolffConstant s T
      let ell := frostmanSlabWolffConstant s T
      let A : ENNReal := s.card
      let V : ENNReal := tubeVolume δ
      let Dfac : ENNReal := A * V * (A * V ^ (1 / 2 : ℝ)) ^ (-σ)
      let Efac : ENNReal := m ^ (-1 : ℝ) * A * V *
        (m ^ (-3 / 2 : ℝ) * ell * A * V ^ (1 / 2 : ℝ)) ^ (-σ)
      have hfac : (δ : ENNReal) ^ (ηD * (1 + σ)) * Dfac ≤ Efac := by
        simpa [m, ell, A, V, Dfac, Efac, mul_assoc] using
          (e_factor_ge_d_factor (δ := (δ : ENNReal)) (m := m) (ell := ell)
            (A := A) (V := V) (η := ηD) (σ := σ)
            (ENNReal.coe_ne_zero.mpr hδ.ne') (by exact_mod_cast hδ1) hηD.le hσ0
            (by simpa [m] using hm1) (by simpa [m] using hm) (by simpa [ell] using hell))
      have hδeps : (δ : ENNReal) ^ (ε / 2) ≤
          (δ : ENNReal) ^ (ηD * (1 + σ)) :=
        ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1) hbudget
      have hsmall : (δ : ENNReal) ^ (ε / 2) * Dfac ≤ Efac :=
        (mul_le_mul_right' hδeps Dfac).trans hfac
      have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
      have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
      have htargetToE :
          (κ : ENNReal) * (δ : ENNReal) ^ (ω + ε) * Dfac ≤
            (κ : ENNReal) * (δ : ENNReal) ^ (ω + ε / 2) * Efac := by
        rw [show ω + ε = (ω + ε / 2) + ε / 2 by ring,
          ENNReal.rpow_add _ _ hδ0E hδtop]
        calc
          (κ : ENNReal) * ((δ : ENNReal) ^ (ω + ε / 2) *
              (δ : ENNReal) ^ (ε / 2)) * Dfac =
              ((κ : ENNReal) * (δ : ENNReal) ^ (ω + ε / 2)) *
                ((δ : ENNReal) ^ (ε / 2) * Dfac) := by ring
          _ ≤ ((κ : ENNReal) * (δ : ENNReal) ^ (ω + ε / 2)) * Efac :=
            mul_le_mul_left' hsmall _
          _ = (κ : ENNReal) * (δ : ENNReal) ^ (ω + ε / 2) * Efac := by ring
      have hfinal : (κ : ENNReal) * (δ : ENNReal) ^ (ω + ε) * Dfac ≤
          volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) :=
        htargetToE.trans (by simpa [m, ell, A, V, Efac, mul_assoc] using hEbound)
      simpa [Dfac, A, V, mul_assoc] using hfinal
    · have hδgt : (1 : ENNReal) < δ := by exact_mod_cast lt_of_not_ge hδ1
      have hpLt : (δ : ENNReal) ^ (-ηD) < 1 :=
        ENNReal.rpow_lt_one_of_one_lt_of_neg hδgt (by linarith)
      exact ((not_lt_of_ge (hm1.trans hm)) hpLt).elim
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp [iUnionShade_empty]

end


end Kakeya.WangZahl
