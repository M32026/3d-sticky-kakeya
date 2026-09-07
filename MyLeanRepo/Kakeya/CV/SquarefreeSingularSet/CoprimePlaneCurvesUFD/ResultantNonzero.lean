import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.CoprimePlaneCurvesUFD.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Resultant nonzero for irreducible coprime plane curves

If `G` is irreducible with positive degree and coprime to `F`, then `resultant G F ≠ 0`.
-/

noncomputable section

open MeasureTheory Metric Set MvPolynomial UniqueFactorizationMonoid Polynomial
open scoped Polynomial

namespace Kakeya.CV

/-- Common root of evaluated polynomials ⇒ resultant zero. -/
lemma resultant_zero_of_common_root {K : Type*} [Field K] {f g : Polynomial K} {z : K}
    (hf : f.eval z = 0) (hg : g.eval z = 0) (hf_ne : f ≠ 0) :
    Polynomial.resultant f g = 0 := by
  have hff : (Polynomial.X - Polynomial.C z) ∣ f := by
    have hdiv : (Polynomial.X - Polynomial.C z) ∣ f - Polynomial.C (f.eval z) :=
      Polynomial.X_sub_C_dvd_sub_C_eval
    rw [hf] at hdiv <;> simpa using hdiv
  have hgg : (Polynomial.X - Polynomial.C z) ∣ g := by
    have hdiv : (Polynomial.X - Polynomial.C z) ∣ g - Polynomial.C (g.eval z) :=
      Polynomial.X_sub_C_dvd_sub_C_eval
    rw [hg] at hdiv <;> simpa using hdiv
  have h_ncop : ¬ IsCoprime f g := by
    intro hcop
    have hunit : IsUnit (Polynomial.X - Polynomial.C z) := IsCoprime.isUnit_of_dvd' hcop hff hgg
    have hdeg : (Polynomial.X - Polynomial.C z).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
    have h1 : (Polynomial.X - Polynomial.C z).natDegree = 1 := by simp
    rw [h1] at hdeg <;> norm_num at hdeg
  rw [Polynomial.resultant_eq_zero_iff]
  exact ⟨Or.inl hf_ne, h_ncop⟩

/-- Resultant of irreducible G and coprime F is nonzero (when G has positive degree). -/
lemma resultant_ne_zero_of_coprime_irreducible
    {G F : Polynomial (MvPolynomial (Fin 1) ℝ)}
    (hG_irred : Irreducible G) (hG_pos : 0 < G.natDegree)
    (hcop : ∀ H, H ∣ G → H ∣ F → IsUnit H) :
    Polynomial.resultant G F ≠ 0 := by
  let eq_map := mapPolyEquiv e1
  let G' := eq_map G
  let F' := eq_map F

  have hG'_irred : Irreducible G' :=
    (MulEquiv.irreducible_iff eq_map.toMulEquiv).mpr hG_irred

  have hG'_pos : 0 < G'.natDegree := by
    have h : G'.natDegree = G.natDegree :=
      Polynomial.natDegree_map_eq_of_injective e1.injective G
    rw [h] <;> exact hG_pos

  have hG'_prim : G'.IsPrimitive := by
    rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
    intro r hcr
    rcases hcr with ⟨Q, hQ⟩
    have h_eq : G' = Polynomial.C r * Q := hQ
    have h_disj : IsUnit (Polynomial.C r) ∨ IsUnit Q := hG'_irred.2 h_eq
    cases h_disj with
    | inl hunit =>
      exact (Polynomial.isUnit_C).mp hunit
    | inr hunitQ =>
      have hdegQ : Q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hunitQ
      have h1 : (Polynomial.C r * Q).natDegree = 0 := by
        have hle : (Polynomial.C r * Q).natDegree ≤ (Polynomial.C r).natDegree + Q.natDegree :=
          Polynomial.natDegree_mul_le
        have hCr0 : (Polynomial.C r).natDegree = 0 := Polynomial.natDegree_C r
        rw [hCr0, hdegQ] at hle
        exact Nat.eq_zero_of_le_zero hle
      have h2 : G'.natDegree = (Polynomial.C r * Q).natDegree := by rw [h_eq]
      have hdeg : G'.natDegree = 0 := by rw [h2, h1]
      rw [hdeg] at hG'_pos <;> omega

  intro h_res0
  have hG'deg : G'.natDegree = G.natDegree :=
    Polynomial.natDegree_map_eq_of_injective e1.injective G
  have hF'deg : F'.natDegree = F.natDegree :=
    Polynomial.natDegree_map_eq_of_injective e1.injective F

  have h1 : Polynomial.resultant G' F' G.natDegree F.natDegree =
      e1.toRingHom (Polynomial.resultant G F G.natDegree F.natDegree) :=
    Polynomial.resultant_map_map (φ := e1.toRingHom) G F G.natDegree F.natDegree

  have h2 : Polynomial.resultant G' F' = Polynomial.resultant G' F' G.natDegree F.natDegree := by
    rw [hG'deg, hF'deg] <;> rfl

  have h_res'_zero : Polynomial.resultant G' F' = 0 := by
    have h3 : Polynomial.resultant G' F' = e1.toRingHom (Polynomial.resultant G F G.natDegree F.natDegree) := by
      rw [h2, h1]
    have h4 : e1.toRingHom (Polynomial.resultant G F G.natDegree F.natDegree) = e1 (Polynomial.resultant G F) := by rfl
    rw [h3, h4, h_res0] <;> simp

  let K := FractionRing (Polynomial ℝ)
  let i : Polynomial ℝ →+* K := algebraMap _ K

  let G'_K := Polynomial.map i G'
  let F'_K := Polynomial.map i F'

  have h_inj_i : Function.Injective i := IsFractionRing.injective (Polynomial ℝ) K
  have hGdeg : G'_K.natDegree = G'.natDegree :=
    Polynomial.natDegree_map_eq_of_injective h_inj_i G'
  have hFdeg : F'_K.natDegree = F'.natDegree :=
    Polynomial.natDegree_map_eq_of_injective h_inj_i F'

  have h_eq_res : Polynomial.resultant G'_K F'_K = i (Polynomial.resultant G' F') := by
    have h5 : Polynomial.resultant G'_K F'_K G'.natDegree F'.natDegree =
        i (Polynomial.resultant G' F' G'.natDegree F'.natDegree) :=
      Polynomial.resultant_map_map (φ := i) G' F' G'.natDegree F'.natDegree
    have h6 : Polynomial.resultant G'_K F'_K =
        Polynomial.resultant G'_K F'_K G'_K.natDegree F'_K.natDegree := by rfl
    rw [h6, hGdeg, hFdeg]
    exact h5

  have h_resK : Polynomial.resultant G'_K F'_K = 0 := by
    rw [h_eq_res, h_res'_zero] <;> simp

  have hG'_K_ne_zero : G'_K ≠ 0 := by
    intro hz
    have h3 : G' = 0 := (Polynomial.map_eq_zero_iff h_inj_i).mp hz
    rw [h3] at hG'_irred
    exact hG'_irred.ne_zero rfl

  have h_ncop : ¬ IsCoprime G'_K F'_K := by
    rw [Polynomial.resultant_eq_zero_iff] at h_resK
    exact h_resK.2

  have h_irred_K : Irreducible G'_K :=
    (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map hG'_prim).mp hG'_irred

  have h_dvd : G'_K ∣ F'_K := by
    by_cases hnd : G'_K ∣ F'_K
    · exact hnd
    · have h_prime : Prime G'_K := Irreducible.prime h_irred_K
      have h_cop : IsCoprime G'_K F'_K := by
        rw [h_prime.coprime_iff_not_dvd] <;> exact hnd
      exfalso
      exact h_ncop h_cop

  by_cases hF' : F' = 0
  · have hF : F = 0 := eq_map.injective (by simpa [F'] using hF')
    have hunit : IsUnit G := hcop G dvd_rfl (by rw [hF] <;> exact dvd_zero G)
    exact hG_irred.1 hunit
  · have hF'_prim : F'.primPart.IsPrimitive := Polynomial.isPrimitive_primPart F'
    have hcontent_ne_zero : F'.content ≠ 0 := by
      intro hz
      have h5 : F' = 0 := Polynomial.content_eq_zero_iff.mp hz
      exact hF' h5
    have h_i_content_ne_zero : i F'.content ≠ 0 := by
      intro h
      have h' : i F'.content = i 0 := by simpa using h
      exact hcontent_ne_zero (h_inj_i h')
    have h_eq2 : F'_K = Polynomial.C (i F'.content) * Polynomial.map i F'.primPart := by
      have h6 : F' = Polynomial.C F'.content * F'.primPart :=
        Polynomial.eq_C_content_mul_primPart F'
      dsimp only [F'_K]
      have h7 : Polynomial.map i F' = Polynomial.map i (Polynomial.C F'.content * F'.primPart) := by
        exact congr_arg (Polynomial.map i) h6
      have h8 : Polynomial.map i (Polynomial.C F'.content * F'.primPart) =
          Polynomial.map i (Polynomial.C F'.content) * Polynomial.map i F'.primPart := by
        rw [Polynomial.map_mul]
      have h9 : Polynomial.map i (Polynomial.C F'.content) = Polynomial.C (i F'.content) := by simp
      have h10 : Polynomial.map i F' = Polynomial.C (i F'.content) * Polynomial.map i F'.primPart := by
        rw [h7, h8, h9]
      exact h10
    have h_dvd_prim : G'_K ∣ Polynomial.map i F'.primPart := by
      rw [h_eq2] at h_dvd
      have h_unit : IsUnit (Polynomial.C (i F'.content) : K[X]) :=
        Polynomial.isUnit_C.mpr (IsUnit.mk0 _ h_i_content_ne_zero)
      exact h_unit.dvd_mul_left.mp h_dvd
    have h_dvd_R : G' ∣ F'.primPart :=
      Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map hG'_prim hF'_prim h_dvd_prim
    have h_dvd_F' : G' ∣ F' := by
      let p := F'.primPart
      let c := F'.content
      have h11 : F' = Polynomial.C c * p := Polynomial.eq_C_content_mul_primPart F'
      have h10 : p ∣ F' := by
        refine ⟨Polynomial.C c, ?_⟩
        rw [h11] <;> ring
      exact dvd_trans h_dvd_R h10

    have h_dvd_G : G ∣ F := by
      rcases h_dvd_F' with ⟨c, hc⟩
      let c' := eq_map.symm c
      have h9 : eq_map (G * c') = G' * c := by
        rw [map_mul, eq_map.apply_symm_apply]
      have h10 : eq_map F = G' * c := by simpa [F'] using hc
      have h11 : eq_map (G * c') = eq_map F := by rw [h9, h10]
      have h12 : G * c' = F := eq_map.injective h11
      exact ⟨c', h12.symm⟩

    have hunit : IsUnit G := hcop G dvd_rfl h_dvd_G
    exact hG_irred.1 hunit

end Kakeya.CV
