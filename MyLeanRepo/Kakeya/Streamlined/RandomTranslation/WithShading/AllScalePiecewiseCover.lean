import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeRadius
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.DownwardEDMonotonicity
import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.ConflictColoring
import MyLeanRepo.Kakeya.Streamlined.CombinatorialLemmas.TotalConflictExtraction
import MyLeanRepo.Kakeya.Streamlined.CombinatorialLemmas.StrongEDExtraction
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.ResidualAbsorption
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.EnlargementContainment
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.StrongEDConflictDegree

/-!
# All-scale piecewise cover from finite grid selections (K-strong ED)

Given a finite grid with ratio `δ^(-1/N)`, at each admissible scale ρ find the
lower bracket σ_k ≤ ρ < σ_{k+1}. Select a K-strongly essentially distinct
subfamily at scale σ_k, enlarge it to radius ρ.

K-strong ED at the upper bracket σ_{k+1} implies regular ED at any ρ ≤ σ_{k+1}
via downward monotonicity (`essentiallyDistinct_of_strong_ed_downward'`),
provided K is large enough relative to the volume ratio.

The conflict degree `D = ceil(C_K * (σ_{k+1} / σ_k)^4)` is scale-dependent and
is carried explicitly through the coloring.

## Main results

- `select_bracket_strong_ed_class`: select a K-strong ED subfamily at the
  upper bracket, with explicit conflict degree D.
- `strong_ed_upper_implies_ed_at_rho`: K-strong ED at upper bracket implies
  regular ED at any ρ between the brackets.
- `PiecewiseScaleData`: per-scale input bundle.
- `build_piecewise_uts`: assemble the `UniformTubeStructure`.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Finset Kakeya.Streamlined
open Kakeya.Streamlined.GeometricLemmas
open Kakeya.Streamlined.RandomTranslation
open Kakeya.Streamlined.RandomTranslation.WithShading

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/-- Select a K-strong ED subfamily of a UTS coarse family at the upper bracket.

Given `sigma` and `sigma_upper`, enlarge the coarse family at `sigma` to radius
`sigma_upper`, color the K-strong conflict graph, and select a conflict-free
class.

The conflict degree `D = ceil(C_K * (sigma_upper / sigma)^4)` is explicit.
The degree bound is provided by `strong_ed_enlargement_conflict_degree`.
-/
lemma select_bracket_strong_ed_class
    {δ : ℝ} (hδ : 0 < δ)
    {fine : TubeFamily δ} (hfine_ball : fine.IsInUnitBall)
    (U : UniformTubeStructure fine)
    (sigma sigma_upper : AdmissibleScale δ)
    (hsigma_le_upper : sigma.1 ≤ sigma_upper.1)
    (K : ℝ) (hK : 2 ≤ K)
    (C_K : ℝ) (hC_K_pos : 0 < C_K)
    (h_conflict_degree :
      ∀ j : Fin (U.coarse sigma).card,
        tubeConflictDegreeStrong
          (sameAxisEnlargedFamily (rho := sigma_upper.1) (U.coarse sigma))
          (Kakeya.deltaTubeVolume sigma_upper.1) (ENNReal.ofReal K) j ≤
        Nat.ceil (C_K * (sigma_upper.1 / sigma.1) ^ 4)) :
    ∃ (selected : Finset (Fin (U.coarse sigma).card)),
      (∀ j ∈ selected, ∀ k ∈ selected, j ≠ k →
        IsKStrongEssentiallyDistinct
          ((sameAxisEnlargedFamily (rho := sigma_upper.1) (U.coarse sigma)).tube j)
          ((sameAxisEnlargedFamily (rho := sigma_upper.1) (U.coarse sigma)).tube k)
          (Kakeya.deltaTubeVolume sigma_upper.1) (ENNReal.ofReal K)) ∧
      (U.coarse sigma).card ≤
        (Nat.ceil (C_K * (sigma_upper.1 / sigma.1) ^ 4) + 1) * selected.card := by
  let G_up := sameAxisEnlargedFamily (rho := sigma_upper.1) (U.coarse sigma)
  let V_up := Kakeya.deltaTubeVolume sigma_upper.1
  let K_enn := ENNReal.ofReal K
  let D := Nat.ceil (C_K * (sigma_upper.1 / sigma.1) ^ 4)
  let conflict : Fin (U.coarse sigma).card → Fin (U.coarse sigma).card → Prop :=
    fun j k =>
      volume
          (((sameAxisEnlargedFamily
              (rho := sigma_upper.1) (U.coarse sigma)).tube j).carrier ∩
            ((sameAxisEnlargedFamily
              (rho := sigma_upper.1) (U.coarse sigma)).tube k).carrier) >
        V_up / K_enn
  have hsymm : ∀ ⦃j k⦄, conflict j k → conflict k j := by
    intro j k h
    dsimp only [conflict] at h ⊢
    rwa [Set.inter_comm]
  let weight : Fin (U.coarse sigma).card → ENNReal := fun _ => 1
  have hdegree : ∀ i ∈ (Finset.univ : Finset (Fin (U.coarse sigma).card)),
      ((Finset.univ : Finset (Fin (U.coarse sigma).card)).filter
        fun j => j ≠ i ∧ conflict i j).card ≤ D := by
    intro i _
    have hbound := h_conflict_degree i
    unfold tubeConflictDegreeStrong at hbound
    rw [Finset.filter_congr_decidable] at hbound
    rw [Finset.filter_congr_decidable]
    dsimp only [conflict, D, V_up, K_enn] at hbound ⊢
    exact hbound
  rcases exists_bicriteria_bounded_conflict_free_class
      (Finset.univ : Finset (Fin (U.coarse sigma).card))
      D weight conflict hsymm hdegree with
    ⟨selected, _hsub, hfree, hcard, _hmass⟩
  have h_strong_ed : ∀ j ∈ selected, ∀ k ∈ selected, j ≠ k →
      IsKStrongEssentiallyDistinct (G_up.tube j) (G_up.tube k) V_up K_enn := by
    intro j hj k hk hne
    have h : ¬conflict j k := hfree j hj k hk hne
    have h' : ¬ (volume ((G_up.tube j).carrier ∩ (G_up.tube k).carrier) > V_up / K_enn) := h
    have h_le : volume ((G_up.tube j).carrier ∩ (G_up.tube k).carrier) ≤ V_up / K_enn :=
      le_of_not_gt h'
    exact h_le
  have huniv_card : (Finset.univ : Finset (Fin (U.coarse sigma).card)).card =
      (U.coarse sigma).card := by simp
  have hcard' : (U.coarse sigma).card ≤ (D + 1) * selected.card := by
    simpa [huniv_card] using hcard
  exact ⟨selected, h_strong_ed, hcard'⟩

/-- K-strong ED at the upper bracket implies regular ED at radius ρ.

Uses `essentiallyDistinct_of_strong_ed_downward'` with the volume ratio
bound. K must satisfy the downward monotonicity condition for the ratio
`A = σ_upper / ρ`.
-/
lemma strong_ed_upper_implies_ed_at_rho
    {σ ρ σ_upper : ℝ}
    (hσ_pos : 0 < σ) (hρ_pos : 0 < ρ) (hσ_le_ρ : σ ≤ ρ)
    (hρ_le_upper : ρ ≤ σ_upper) (hσ_upper_one : σ_upper ≤ 1)
    (K : ENNReal)
    (hK : 2 * ENNReal.ofReal (((Real.pi + 8 / 3 * Real.pi * (σ_upper / ρ)) / 2) *
        (σ_upper / ρ) ^ 2) ≤ K)
    {T : TubeFamily σ} (j k : Fin T.card)
    (h_strong : IsKStrongEssentiallyDistinct
        ((sameAxisEnlargedFamily (rho := σ_upper) T).tube j)
        ((sameAxisEnlargedFamily (rho := σ_upper) T).tube k)
        (Kakeya.deltaTubeVolume σ_upper) K) :
    ((sameAxisEnlargedFamily (rho := ρ) T).tube j).EssentiallyDistinct
      ((sameAxisEnlargedFamily (rho := ρ) T).tube k) := by
  let T_rho_j := (sameAxisEnlargedFamily (rho := ρ) T).tube j
  let T_rho_k := (sameAxisEnlargedFamily (rho := ρ) T).tube k
  let A : ℝ := σ_upper / ρ
  have hσ_upper_pos : 0 < σ_upper := by linarith
  have hA_pos : 0 < A := by
    dsimp only [A]
    positivity
  have hR_le_A : σ_upper ≤ A * ρ := by
    dsimp only [A]
    have h_eq : (σ_upper / ρ) * ρ = σ_upper := by
      field_simp [hρ_pos.ne'] <;> ring
    rw [h_eq]
    <;> exact le_refl _
  exact essentiallyDistinct_of_strong_ed_downward'
      (R := σ_upper) (r := ρ) (A := A)
      hρ_pos hσ_upper_pos hρ_le_upper
      hA_pos hR_le_A hσ_upper_one
      T_rho_j.base T_rho_k.base T_rho_j.direction T_rho_k.direction
      T_rho_j.direction_unit T_rho_k.direction_unit
      K hK h_strong

/-- Precomputed grid-scale data for one target scale ρ.

`R` is a coarse subfamily at scale σ whose upper-bracket enlargements to
`σ_upper` are pairwise K-strongly ED (witnessed by `R_upper_strong_ed`).
`P` covers the fine family `G` by `R`.
The bracket condition `σ ≤ ρ ≤ σ_upper` plus the K condition ensures ED at ρ.

`D` is the conflict degree used in the coloring, equal to
`ceil(C_K * (σ_upper / σ)^4)`. It must be threaded through downstream
constructions.
-/
structure PiecewiseScaleData
    {δ : ℝ} (G : TubeFamily δ) (uniformity : ENNReal)
    (ρ : AdmissibleScale δ) where
  σ : AdmissibleScale δ
  σ_upper : AdmissibleScale δ
  hσ_le_ρ : σ.1 ≤ ρ.1
  hρ_le_upper : ρ.1 ≤ σ_upper.1
  K : ENNReal
  hK_downward : 2 * ENNReal.ofReal (((Real.pi + 8 / 3 * Real.pi * (σ_upper.1 / ρ.1)) / 2) *
      (σ_upper.1 / ρ.1) ^ 2) ≤ K
  C_K : ℝ
  hC_K_pos : 0 < C_K
  D : ℕ
  hD_eq : D = Nat.ceil (C_K * (σ_upper.1 / σ.1) ^ 4)
  R : TubeFamily σ.1
  R_upper_strong_ed :
    ∀ j ∈ (Finset.univ : Finset (Fin R.card)),
      ∀ k ∈ (Finset.univ : Finset (Fin R.card)),
        j ≠ k →
          IsKStrongEssentiallyDistinct
            ((sameAxisEnlargedFamily (rho := σ_upper.1) R).tube j)
            ((sameAxisEnlargedFamily (rho := σ_upper.1) R).tube k)
            (Kakeya.deltaTubeVolume σ_upper.1) K
  P : TubeCover G R
  P_uniform : P.toFactoring.FibersAreCUniform uniformity

/-- Build a `UniformTubeStructure` on `G` from per-scale piecewise data.

The coarse family at ρ is the coaxial enlargement of `R` to radius ρ.
The cover parent map is inherited from `P`.
Coarse ED follows from `strong_ed_upper_implies_ed_at_rho`.
-/
def build_piecewise_uts
    {δ : ℝ} (hδ : 0 < δ)
    {G : TubeFamily δ}
    (uniformity : ENNReal)
    (h_one : 1 ≤ uniformity)
    (h_top : uniformity ≠ ⊤)
    (h_card : G.enncard ≤ uniformity)
    (data : ∀ (ρ : AdmissibleScale δ), PiecewiseScaleData G uniformity ρ) :
    UniformTubeStructure G :=
  let coarse : ∀ (ρ : AdmissibleScale δ), TubeFamily ρ.1 :=
    fun ρ => sameAxisEnlargedFamily (rho := ρ.1) (data ρ).R
  let cover : ∀ (ρ : AdmissibleScale δ), TubeCover G (coarse ρ) :=
    fun ρ =>
      let d := data ρ
      {
        parent := d.P.parent
        parent_surjective := d.P.parent_surjective
        nested := fun i =>
          have h1 : (G.tube i).carrier ⊆ (d.R.tube (d.P.parent i)).carrier :=
            d.P.nested i
          have h2 : (d.R.tube (d.P.parent i)).carrier ⊆
              ((coarse ρ).tube (d.P.parent i)).carrier := by
            simpa [coarse, sameAxisEnlargedFamily_tube] using
              carrier_subset_withRadius d.hσ_le_ρ (d.R.tube (d.P.parent i))
          h1.trans h2
      }
  {
    coarse := coarse
    cover := cover
    uniformity := uniformity
    one_le_uniformity := h_one
    uniformity_ne_top := h_top
    uniform := fun ρ =>
      (cover ρ).factoringFibersAreCUniform_of_enncard_le
        h_one h_card
    coarse_distinct := fun ρ =>
      let d := data ρ
      fun j k hne =>
        strong_ed_upper_implies_ed_at_rho (T := d.R)
          (lt_of_lt_of_le hδ d.σ.2.1)
          (lt_of_lt_of_le hδ ρ.2.1)
          d.hσ_le_ρ d.hρ_le_upper d.σ_upper.2.2
          d.K d.hK_downward j k
          (d.R_upper_strong_ed j (Finset.mem_univ j) k (Finset.mem_univ k) hne)
  }

end Kakeya.Streamlined.RandomTranslation.WithShading

end
