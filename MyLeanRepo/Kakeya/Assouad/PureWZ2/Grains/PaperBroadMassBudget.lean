import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TransversePairPaper
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement
import Mathlib.Tactic

/-!
# Broad mass budget for PureWZ2 paper tube shadings

Adapts `broad_mass_budget_main` from WZ1 to the paper shading context.

## Key difference from WZ1

WZ1's balanced cover has constant point multiplicity `m`, so the CV bound
applies directly to the multiplicity-weighted mass. Paper shadings may have
variable multiplicity, so we use an upper bound `M` to convert:

```
broadMass = ∫⁻ p in E, pointMultiplicity p ≤ M * volume E
```

Then the paper CV volume bound gives
`L * broadMass ≤ M * C * (δ² * N)^(3/2)`.

## Main result

`paper_broad_mass_budget_main`: given a paper shading `S` with multiplicity
upper bound `M`, the paper CV estimate, and a parameter absorption inequality,
prove `2 * broadMass ≤ S.mass`.

## Helper lemmas

- `paper_large_triple_count_le_multiplicity`: `Q` large triples imply
  trilinear multiplicity ≥ `Q * τ`.
- `paperCountedBroadSet_measurable`: the counted-broad set is measurable.
-/

noncomputable section

open MeasureTheory Set Finset Classical
open scoped ENNReal

namespace Kakeya.Assouad

/--
Paper version: Q large triples imply trilinear multiplicity ≥ Q * tau.

Each large triple contributes at least `tau` to the trilinear multiplicity
because `tripleVolume = |tripleProduct| ≥ tau`.
-/
lemma paper_large_triple_count_le_multiplicity
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F)
    (p : Point3) (tau : ℝ) (Q : ℕ)
    (h : Q ≤ paperLargeTripleCount Y p tau) :
    (Q : ENNReal) * ENNReal.ofReal tau ≤
      paperShadingTrilinearMultiplicity Y p := by
  classical
  let P : Finset (Fin F.card × (Fin F.card × Fin F.card)) :=
    Finset.univ.product (Finset.univ.product Finset.univ)
  let S := P.filter fun ijk =>
    p ∈ Y.carrier ijk.1 ∧
    p ∈ Y.carrier ijk.2.1 ∧
    p ∈ Y.carrier ijk.2.2 ∧
    tau ≤ |wz1TripleProduct
      (F.tube ijk.1).direction
      (F.tube ijk.2.1).direction
      (F.tube ijk.2.2).direction|
  let f (ijk : Fin F.card × (Fin F.card × Fin F.card)) : ENNReal :=
    Kakeya.CV.setIndicator (Y.carrier ijk.1) p *
    Kakeya.CV.setIndicator (Y.carrier ijk.2.1) p *
    Kakeya.CV.setIndicator (Y.carrier ijk.2.2) p *
    ENNReal.ofReal (Kakeya.CV.tripleVolume
      ![ (F.tube ijk.1).direction, (F.tube ijk.2.1).direction, (F.tube ijk.2.2).direction])

  have hS_card : S.card = paperLargeTripleCount Y p tau := by rfl
  have hQ : Q ≤ S.card := by
    rw [hS_card] at *; exact h

  have h_tv_eq : ∀ (i j k : Fin F.card),
      Kakeya.CV.tripleVolume ![ (F.tube i).direction, (F.tube j).direction, (F.tube k).direction] =
        |wz1TripleProduct (F.tube i).direction (F.tube j).direction (F.tube k).direction| := by
    intro i j k
    rfl

  have h2 : ∀ (i : Fin F.card),
      (∑ j : Fin F.card, ∑ k : Fin F.card, f (i, (j, k))) =
      ∑ jk ∈ (Finset.univ.product Finset.univ), f (i, jk) := by
    intro i
    let g_i : (Fin F.card × Fin F.card) → ENNReal := fun jk => f (i, jk)
    have h := Finset.sum_product (Finset.univ : Finset (Fin F.card)) (Finset.univ : Finset (Fin F.card)) g_i
    simpa [g_i] using h.symm
  have h3 : ∑ i : Fin F.card, (∑ j : Fin F.card, ∑ k : Fin F.card, f (i, (j, k))) =
      ∑ i : Fin F.card, ∑ jk ∈ (Finset.univ.product Finset.univ), f (i, jk) := by
    apply Finset.sum_congr rfl
    intro i _
    exact h2 i
  have h4 : ∑ i : Fin F.card, ∑ jk ∈ (Finset.univ.product Finset.univ), f (i, jk) =
      ∑ ijk ∈ P, f ijk := by
    have h := Finset.sum_product (Finset.univ : Finset (Fin F.card)) (Finset.univ.product Finset.univ) f
    simpa [P] using h.symm
  have h5 : paperShadingTrilinearMultiplicity Y p =
      ∑ i : Fin F.card, ∑ j : Fin F.card, ∑ k : Fin F.card, f (i, (j, k)) := by
    simp [paperShadingTrilinearMultiplicity, f] <;> rfl
  have h_eq : paperShadingTrilinearMultiplicity Y p = ∑ ijk ∈ P, f ijk := by
    rw [h5, h3, h4]

  by_cases htau : 0 ≤ tau
  · -- Case tau ≥ 0
    have h1 : ∀ ijk ∈ S, ENNReal.ofReal tau ≤ f ijk := by
      intro ijk hijk
      simp only [S, Finset.mem_filter] at hijk
      rcases hijk with ⟨_, hi, hj, hk, hprod⟩
      have hi' : Kakeya.CV.setIndicator (Y.carrier ijk.1) p = 1 := by
        simp [Kakeya.CV.setIndicator, hi]
      have hj' : Kakeya.CV.setIndicator (Y.carrier ijk.2.1) p = 1 := by
        simp [Kakeya.CV.setIndicator, hj]
      have hk' : Kakeya.CV.setIndicator (Y.carrier ijk.2.2) p = 1 := by
        simp [Kakeya.CV.setIndicator, hk]
      have hf : f ijk = ENNReal.ofReal (Kakeya.CV.tripleVolume
          ![ (F.tube ijk.1).direction, (F.tube ijk.2.1).direction, (F.tube ijk.2.2).direction]) := by
        simp [f, hi', hj', hk']
      rw [hf]
      have h_tv : Kakeya.CV.tripleVolume
          ![ (F.tube ijk.1).direction, (F.tube ijk.2.1).direction, (F.tube ijk.2.2).direction] =
          |wz1TripleProduct (F.tube ijk.1).direction (F.tube ijk.2.1).direction (F.tube ijk.2.2).direction| :=
        h_tv_eq ijk.1 ijk.2.1 ijk.2.2
      rw [h_tv]
      exact ENNReal.ofReal_le_ofReal hprod
    have h_sum_S : ∑ ijk ∈ S, ENNReal.ofReal tau ≤ ∑ ijk ∈ S, f ijk :=
      Finset.sum_le_sum h1
    have h_sub : S ⊆ P := by
      intro ijk hijk
      exact (Finset.mem_filter.mp hijk).1
    have h_nonneg : ∀ (x : _), x ∈ P → x ∉ S → 0 ≤ f x := by
      intro x _ _
      exact bot_le
    have h_sum_P : ∑ ijk ∈ S, f ijk ≤ ∑ ijk ∈ P, f ijk :=
      Finset.sum_le_sum_of_subset_of_nonneg h_sub h_nonneg
    have h_card_sum : ∑ ijk ∈ S, ENNReal.ofReal tau = (S.card : ENNReal) * ENNReal.ofReal tau := by
      have h : ∑ ijk ∈ S, ENNReal.ofReal tau = S.card • ENNReal.ofReal tau := by
        rw [Finset.sum_const]
      rw [h]
      simp [nsmul_eq_mul]
    rw [h_eq]
    have h3 : (Q : ENNReal) ≤ (S.card : ENNReal) := by exact_mod_cast hQ
    calc
      (Q : ENNReal) * ENNReal.ofReal tau
        ≤ (S.card : ENNReal) * ENNReal.ofReal tau := by gcongr
      _ = ∑ ijk ∈ S, ENNReal.ofReal tau := h_card_sum.symm
      _ ≤ ∑ ijk ∈ S, f ijk := h_sum_S
      _ ≤ ∑ ijk ∈ P, f ijk := h_sum_P
  · -- Case tau < 0: ENNReal.ofReal tau = 0
    have h_neg : tau < 0 := by linarith
    have h_ofReal : ENNReal.ofReal tau = 0 := by
      rw [ENNReal.ofReal_eq_zero.mpr] <;> linarith
    rw [h_ofReal]
    <;> simp

/-- The paper counted-broad set is measurable. -/
lemma paperCountedBroadSet_measurable
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F)
    (tau : ℝ) (Q : ℕ) :
    MeasurableSet (paperCountedBroadSet Y tau Q) := by
  classical
  have h_union_meas : MeasurableSet Y.union := by
    have h1 : Y.union = ⋃ i : Fin F.card, Y.carrier i := by
      ext x
      simp [Kakeya.Streamlined.Shading.union]
      <;> aesop
    rw [h1]
    exact MeasurableSet.iUnion fun i => Y.measurable_carrier i

  let P : Finset (Fin F.card × (Fin F.card × Fin F.card)) :=
    Finset.univ.product (Finset.univ.product Finset.univ)

  let condition (ijk : Fin F.card × (Fin F.card × Fin F.card)) (p : Point3) : Prop :=
    p ∈ Y.carrier ijk.1 ∧
    p ∈ Y.carrier ijk.2.1 ∧
    p ∈ Y.carrier ijk.2.2 ∧
    tau ≤ |wz1TripleProduct
      (F.tube ijk.1).direction
      (F.tube ijk.2.1).direction
      (F.tube ijk.2.2).direction|

  have h_cond_meas : ∀ ijk, MeasurableSet {p : Point3 | condition ijk p} := by
    intro ijk
    have h1 : MeasurableSet (Y.carrier ijk.1) := Y.measurable_carrier ijk.1
    have h2 : MeasurableSet (Y.carrier ijk.2.1) := Y.measurable_carrier ijk.2.1
    have h3 : MeasurableSet (Y.carrier ijk.2.2) := Y.measurable_carrier ijk.2.2
    let prod_abs := |wz1TripleProduct
      (F.tube ijk.1).direction (F.tube ijk.2.1).direction (F.tube ijk.2.2).direction|
    have h4 : MeasurableSet {p : Point3 | tau ≤ prod_abs} := by
      by_cases h : tau ≤ prod_abs
      · have h5 : {p : Point3 | tau ≤ prod_abs} = Set.univ := by
          ext p; simp [h]
        rw [h5]; exact MeasurableSet.univ
      · have h5 : {p : Point3 | tau ≤ prod_abs} = ∅ := by
          ext p; simp [h]
        rw [h5]; exact MeasurableSet.empty
    exact h1.inter (h2.inter (h3.inter h4))

  have h_count_eq : ∀ (p : Point3), paperLargeTripleCount Y p tau =
      ∑ ijk ∈ P, if condition ijk p then (1 : ℕ) else 0 := by
    intro p
    have h_filter : ∑ ijk ∈ P, (if condition ijk p then (1 : ℕ) else 0) =
        (P.filter (fun ijk => condition ijk p)).card := by
      calc
        ∑ ijk ∈ P, (if condition ijk p then (1 : ℕ) else 0)
          = ∑ ijk ∈ (P.filter (fun ijk => condition ijk p)), (1 : ℕ) +
            ∑ ijk ∈ (P.filter (fun ijk => ¬condition ijk p)), (0 : ℕ) := by
              rw [Finset.sum_ite]
        _ = (P.filter (fun ijk => condition ijk p)).card + 0 := by simp
        _ = (P.filter (fun ijk => condition ijk p)).card := by simp
    have h_def : paperLargeTripleCount Y p tau = (P.filter (fun ijk => condition ijk p)).card := by
      simp [paperLargeTripleCount, condition] <;> rfl
    rw [h_def]
    exact h_filter.symm

  have h_count_meas : Measurable (fun p : Point3 => paperLargeTripleCount Y p tau) := by
    rw [funext h_count_eq]
    apply Finset.measurable_sum
    intro ijk _
    exact measurable_one.ite (h_cond_meas ijk) measurable_zero

  have hIci : MeasurableSet (Set.Ici Q) := measurableSet_Ici
  have h5 : MeasurableSet {p : Point3 | Q ≤ paperLargeTripleCount Y p tau} :=
    h_count_meas hIci

  have h6 : paperCountedBroadSet Y tau Q =
      Y.union ∩ {p : Point3 | Q ≤ paperLargeTripleCount Y p tau} := by
    ext p
    simp [paperCountedBroadSet]
  rw [h6]
  exact h_union_meas.inter h5

/--
Main broad mass budget for paper tube shadings.

Given:
- A paper shading `S`
- The paper CV broad-set estimate `hCV` (already specialized to `S`)
- A pointwise multiplicity upper bound `M`
- Broad-set parameters `Q`, `tau`
- An absorption inequality relating the CV RHS to the shading mass

Prove: `2 * broadMass ≤ S.mass`, where `broadMass` is the point-multiplicity-weighted
mass of the counted-broad set.

This is the paper analogue of `broad_mass_budget_main`. The key difference is
that WZ1 uses constant multiplicity `m` (so the CV bound is already weighted),
while here we use an upper bound `M` to convert from volume to weighted mass.
-/
theorem paper_broad_mass_budget_main
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (C : ENNReal)
    (hCV : ∀ (E : Set Point3), MeasurableSet E → E ⊆ S.union →
      ∀ (L : ENNReal),
        (∀ p ∈ E, L ≤ (paperShadingTrilinearMultiplicity S p)^(1/2:ℝ)) →
          L * volume E ≤ C * (ENNReal.ofReal (delta^2) * F.enncard)^(3/2:ℝ))
    (M : ENNReal)
    (hmult_upper : ∀ p ∈ S.union, (S.pointMultiplicity p : ENNReal) ≤ M)
    (Q : ℕ) (tau : ℝ)
    (hQ_pos : 0 < Q)
    (htau_pos : 0 < tau)
    (h_absorb : (2 : ENNReal) * M * C * (ENNReal.ofReal (delta^2) * F.enncard)^(3/2:ℝ) ≤
        (((Q : ENNReal) * ENNReal.ofReal tau)^(1/2:ℝ)) * S.mass) :
    2 * (∫⁻ p in paperCountedBroadSet S tau Q, (S.pointMultiplicity p : ENNReal)) ≤ S.mass := by
  let E := paperCountedBroadSet S tau Q
  let L : ENNReal := ((Q : ENNReal) * ENNReal.ofReal tau)^(1/2:ℝ)
  have hE_meas : MeasurableSet E := paperCountedBroadSet_measurable S tau Q
  have hE_sub : E ⊆ S.union := by
    intro p hp
    exact hp.1
  have hQ_ne_top : (Q : ENNReal) ≠ ⊤ := by simp
  have htau_ne_top : ENNReal.ofReal tau ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_prod_ne_top : (Q : ENNReal) * ENNReal.ofReal tau ≠ ⊤ :=
    ENNReal.mul_ne_top hQ_ne_top htau_ne_top
  have h_prod_pos : (0 : ENNReal) < (Q : ENNReal) * ENNReal.ofReal tau := by positivity
  have hL_pos : L ≠ 0 := by
    have h : 0 < L := by positivity
    exact h.ne'
  have hL_top : L ≠ ⊤ := by
    have hQ_cast : (Q : ENNReal) = ENNReal.ofReal (Q : ℝ) := by norm_cast
    have h_base_eq : ((Q : ENNReal) * ENNReal.ofReal tau) = ENNReal.ofReal (((Q : ℝ) * tau)) := by
      rw [hQ_cast]
      have h : ENNReal.ofReal (Q : ℝ) * ENNReal.ofReal tau = ENNReal.ofReal ((Q : ℝ) * tau) := by
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (Q : ℝ) by positivity)]
      exact h
    have h_nonneg : 0 ≤ (Q : ℝ) * tau := by positivity
    have h_rpow : (ENNReal.ofReal ((Q : ℝ) * tau)) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (((Q : ℝ) * tau) ^ (1 / 2 : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg h_nonneg (by norm_num)
    have h_sqrt : ((Q : ℝ) * tau) ^ (1 / 2 : ℝ) = Real.sqrt ((Q : ℝ) * tau) := by
      rw [Real.sqrt_eq_rpow] <;> ring
    have hL_eq : L = ENNReal.ofReal (Real.sqrt ((Q : ℝ) * tau)) := by
      simp only [L, h_base_eq, h_rpow, h_sqrt]
    rw [hL_eq]
    exact ENNReal.ofReal_ne_top
  have hL_bound : ∀ p ∈ E, L ≤ (paperShadingTrilinearMultiplicity S p)^(1/2:ℝ) := by
    intro p hp
    have hQ_count : Q ≤ paperLargeTripleCount S p tau := hp.2
    have h_mult : (Q : ENNReal) * ENNReal.ofReal tau ≤ paperShadingTrilinearMultiplicity S p :=
      paper_large_triple_count_le_multiplicity S p tau Q hQ_count
    have h : ((Q : ENNReal) * ENNReal.ofReal tau)^(1/2:ℝ) ≤
        (paperShadingTrilinearMultiplicity S p)^(1/2:ℝ) :=
      ENNReal.rpow_le_rpow h_mult (by norm_num)
    exact h
  have hCV' := hCV E hE_meas hE_sub L hL_bound
  set broadMass := ∫⁻ p in E, (S.pointMultiplicity p : ENNReal) with hBM_def
  have h_broad_le : broadMass ≤ M * volume E := by
    have h1 : ∀ p ∈ E, (S.pointMultiplicity p : ENNReal) ≤ M := by
      intro p hp
      exact hmult_upper p (hE_sub hp)
    have h2 : broadMass ≤ ∫⁻ p in E, M := by
      exact setLIntegral_mono' hE_meas h1
    have h3 : (∫⁻ p in E, M) = M * volume E := by
      rw [setLIntegral_const] <;> rfl
    rw [h3] at h2
    exact h2
  have h1 : L * broadMass ≤ M * C * (ENNReal.ofReal (delta^2) * F.enncard)^(3/2:ℝ) := by
    calc
      L * broadMass
        ≤ L * (M * volume E) := by gcongr
      _ = M * (L * volume E) := by ring
      _ ≤ M * (C * (ENNReal.ofReal (delta^2) * F.enncard)^(3/2:ℝ)) := by gcongr
      _ = M * C * (ENNReal.ofReal (delta^2) * F.enncard)^(3/2:ℝ) := by ring
  have h2 : (2 : ENNReal) * (L * broadMass) ≤
      (2 : ENNReal) * (M * C * (ENNReal.ofReal (delta^2) * F.enncard)^(3/2:ℝ)) := by
    gcongr
  have h3 : (2 : ENNReal) * (M * C * (ENNReal.ofReal (delta^2) * F.enncard)^(3/2:ℝ)) =
      (2 : ENNReal) * M * C * (ENNReal.ofReal (delta^2) * F.enncard)^(3/2:ℝ) := by ring
  rw [h3] at h2
  have h4 : (2 : ENNReal) * (L * broadMass) ≤ L * S.mass := by
    calc
      (2 : ENNReal) * (L * broadMass)
        ≤ (2 : ENNReal) * M * C * (ENNReal.ofReal (delta^2) * F.enncard)^(3/2:ℝ) := h2
      _ ≤ L * S.mass := h_absorb
  have h5 : L * (2 * broadMass) ≤ L * S.mass := by
    have h_comm : (2 : ENNReal) * (L * broadMass) = L * (2 * broadMass) := by ring
    rw [h_comm] at h4
    exact h4
  have h6 : 2 * broadMass ≤ S.mass := by
    have h7 : L * (2 * broadMass) ≤ L * S.mass := h5
    have h8 : L * (2 * broadMass) / L ≤ S.mass := by
      exact ENNReal.div_le_of_le_mul' h7
    have h9 : L * (2 * broadMass) / L = 2 * broadMass := by
      rw [mul_comm L (2 * broadMass)]
      exact ENNReal.mul_div_cancel_right hL_pos hL_top
    rw [h9] at h8
    exact h8
  exact h6

end Kakeya.Assouad

end
