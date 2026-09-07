import MyLeanRepo.Kakeya.Cinematic.Section5.RestrictedFamily
import MyLeanRepo.Kakeya.Cinematic.WZ2Input

/-!
# Separation and Katz--Tao bounds in a restricted physical metric

The intrinsic metric on a parameter subinterval is smaller than the ambient
metric but controls it by `3*K` on a cinematic family. Thus ambient
`delta`-separation and Katz--Tao non-concentration transport to the restricted
metric at scale `delta / (3*K)`, with no loss in the Katz--Tao constant.
-/

noncomputable section

namespace Kakeya.Cinematic

open C2Function

def restrictedC2Ball (I : ParameterInterval)
    (center : C2Function) (radius : ℝ) : Set C2Function :=
  {f | restrictedC2Distance I f center ≤ radius}

def FiniteFunctionFamily.IsRestrictedDeltaSeparated
    (F : FiniteFunctionFamily) (I : ParameterInterval) (delta : ℝ) : Prop :=
  ∀ ⦃f⦄, f ∈ F.carrier →
    ∀ ⦃g⦄, g ∈ F.carrier → f ≠ g →
      delta ≤ restrictedC2Distance I f g

def FiniteFunctionFamily.HasRestrictedKatzTaoBound
    (F : FiniteFunctionFamily) (I : ParameterInterval)
    (delta C : ℝ) : Prop :=
  (F.card : ℝ) ≤ C / delta ∧
    ∀ center ∈ F.carrier, ∀ r : ℝ, delta ≤ r → r ≤ 1 →
      ((F.carrier ∩ restrictedC2Ball I center r).ncard : ℝ) ≤
        C * (r / delta)

lemma FiniteFunctionFamily.IsDeltaSeparated.toRestricted
    {family : Set C2Function} {K D delta : ℝ}
    (hK : 1 ≤ K) (hfamily : IsCinematicFamily family K D)
    {F : FiniteFunctionFamily} (hF : F.carrier ⊆ family)
    (hsep : F.IsDeltaSeparated delta) (I : ParameterInterval) :
    F.IsRestrictedDeltaSeparated I (delta / (3 * K)) := by
  intro f hf g hg hne
  have hglobal : delta ≤ c2Distance f g :=
    hsep hf hg hne
  have hcompare :
      c2Distance f g ≤ 3 * K * restrictedC2Distance I f g :=
    c2Distance_le_three_mul_restrictedC2Distance
      hK hfamily (hF hf) (hF hg) I
  apply (div_le_iff₀ (by positivity : 0 < 3 * K)).2
  simpa [mul_comm] using hglobal.trans hcompare

lemma FiniteFunctionFamily.HasKatzTaoBound.toRestricted
    {family : Set C2Function} {K D delta C : ℝ}
    (hK : 1 ≤ K) (hdelta : 0 < delta) (hC : 0 ≤ C)
    (hfamily : IsCinematicFamily family K D)
    {F : FiniteFunctionFamily} (hF : F.carrier ⊆ family)
    (hKT : F.HasKatzTaoBound delta C) (I : ParameterInterval) :
    F.HasRestrictedKatzTaoBound I (delta / (3 * K)) C := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  constructor
  · calc
      (F.card : ℝ) ≤ C / delta := hKT.1
      _ ≤ C / (delta / (3 * K)) := by
        apply div_le_div_of_nonneg_left hC
        · positivity
        · apply div_le_self hdelta.le
          nlinarith
  · intro center hcenter r hscale_r hr_one
    have hcenter_family : center ∈ family := hF hcenter
    let A := F.carrier ∩ restrictedC2Ball I center r
    have hA_sub_F : A ⊆ F.carrier := Set.inter_subset_left
    have hdelta_3Kr : delta ≤ 3 * K * r := by
      have h := mul_le_mul_of_nonneg_right hscale_r
        (by positivity : 0 ≤ 3 * K)
      have heq : 3 * K * (delta / (3 * K)) = delta := by
        field_simp [hKpos.ne']
      calc
        delta = 3 * K * (delta / (3 * K)) := heq.symm
        _ = (delta / (3 * K)) * (3 * K) := by ring
        _ ≤ r * (3 * K) := h
        _ = 3 * K * r := by ring
    by_cases hradius : 3 * K * r ≤ 1
    · let B := F.carrier ∩ c2Ball center (3 * K * r)
      have hA_sub_B : A ⊆ B := by
        intro g hg
        refine ⟨hg.1, ?_⟩
        rw [mem_c2Ball]
        have hcompare :
            c2Distance g center ≤
              3 * K * restrictedC2Distance I g center :=
          c2Distance_le_three_mul_restrictedC2Distance
            hK hfamily (hF hg.1) hcenter_family I
        exact hcompare.trans
          (mul_le_mul_of_nonneg_left hg.2 (by positivity))
      have hB_fin : B.Finite := F.finite.inter_of_left _
      have hncard : A.ncard ≤ B.ncard :=
        Set.ncard_le_ncard hA_sub_B hB_fin
      have hbound :=
        hKT.2 center (3 * K * r) hdelta_3Kr hradius
      have hcast : (A.ncard : ℝ) ≤ (B.ncard : ℝ) := by
        exact_mod_cast hncard
      calc
        (A.ncard : ℝ) ≤ (B.ncard : ℝ) := hcast
        _ ≤ C * ((3 * K * r) / delta) := hbound
        _ = C * (r / (delta / (3 * K))) := by
          field_simp [hdelta.ne', hKpos.ne']
    · have hncard : A.ncard ≤ F.carrier.ncard :=
        Set.ncard_le_ncard hA_sub_F F.finite
      have hcast : (A.ncard : ℝ) ≤ (F.card : ℝ) := by
        exact_mod_cast hncard
      have hratio : 1 ≤ 3 * K * r := by linarith
      calc
        (A.ncard : ℝ) ≤ (F.card : ℝ) := hcast
        _ ≤ C / delta := hKT.1
        _ ≤ C * ((3 * K * r) / delta) := by
          have hdiv_nonneg : 0 ≤ C / delta :=
            div_nonneg hC hdelta.le
          calc
            C / delta = (C / delta) * 1 := by ring
            _ ≤ (C / delta) * (3 * K * r) := by gcongr
            _ = C * ((3 * K * r) / delta) := by ring
        _ = C * (r / (delta / (3 * K))) := by
          field_simp [hdelta.ne', hKpos.ne']

end Kakeya.Cinematic
