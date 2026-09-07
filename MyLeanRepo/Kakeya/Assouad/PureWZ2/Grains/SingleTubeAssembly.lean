import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SingleTubeGrain
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12CroppedExtremal
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import Mathlib.Tactic

/-!
# Strategy 1: Single-tube grain configuration assembly (outputLoss ≥ 2)

Given a cropped extremal configuration, select one tube and construct a
complete `PureWZ2GrainConfiguration` on the resulting single-tube family.

## Fields

- `family`, `shading`: single-tube restriction
- `line_class`, `cubical`: inherited from the ambient cropped configuration
- `extremal`:
  - `dense`: from `exists_tube_satisfying_density`
  - `volume_upper`: monotonicity from ambient volume upper bound
  - `cwa_nearby_scales`: supplied as hypothesis (direct self-cover, aurora)
- `top_level_cwa`: `single_tube_top_level_cwa` (outputLoss ≥ 2)
- `globalGrains`: `single_tube_global_grain_data`
- `localGrains`: `single_tube_local_grain_data`

## Usage

This module provides `single_tube_assembly`, which takes all the pieces and
produces the final configuration. The cwa_nearby hypothesis is the only
non-trivial remaining dependency.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set MeasureTheory Classical

attribute [local instance] Classical.propDecidable

/-- Build a single-tube `TubeFamily` from one tube of an ambient family. -/
def singleTubeFamily {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (i : Fin F.card) : Kakeya.Streamlined.TubeFamily delta where
  card := 1
  tube := fun (_ : Fin 1) => F.tube i

/-- Build a single-tube `WZ1PaperTubeShading` from one shaded carrier. -/
def singleTubeShading {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F} (i : Fin F.card)
    (hmeas : MeasurableSet (S.carrier i))
    (hsub : S.carrier i ⊆ wz1PaperTubeCarrier (F.tube i)) :
    WZ1PaperTubeShading (singleTubeFamily i) :=
  { carrier := fun (_ : Fin 1) => S.carrier i
    measurable_carrier := fun _ => hmeas
    subset_body := fun _ => hsub }

namespace singleTubeAssembly

/-- The single-tube family has card 1. -/
lemma card_eq_one {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {i : Fin F.card} :
    (singleTubeFamily i).card = 1 := by rfl

/-- Helper: any element of `Fin n` with `n = 1` has coercion `0`. -/
lemma fin_one_val {n : ℕ} (hn : n = 1) (x : Fin n) : (x : ℕ) = 0 := by
  have h : (x : ℕ) < 1 := hn ▸ x.is_lt
  omega

/-- Helper: sum over a `Fin n` with `n = 1` equals the unique value. -/
lemma sum_card_one {α : Type*} [AddCommMonoid α] {n : ℕ} (hn : n = 1)
    (f : Fin n → α) :
    ∑ i : Fin n, f i = f ⟨0, by rw [hn] <;> norm_num⟩ := by
  have h0 : 0 < n := by rw [hn] <;> norm_num
  let z : Fin n := ⟨0, h0⟩
  have h_all : ∀ (x : Fin n), x = z := by
    intro x
    apply Fin.ext
    have h : (x : ℕ) = 0 := fin_one_val hn x
    simpa [z] using h
  have h_univ : Finset.univ = {z} := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_univ, true_iff, Finset.mem_singleton]
    exact h_all x
  rw [h_univ, Finset.sum_singleton]

/-- Line class is inherited. -/
lemma line_class {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {i : Fin F.card} (h : WZ1PaperIsLineClass F) :
    WZ1PaperIsLineClass (singleTubeFamily i) := by
  intro j
  exact h i

/-- Cubical shading is inherited. -/
lemma cubical {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F} {i : Fin F.card}
    (hmeas : MeasurableSet (S.carrier i))
    (hsub : S.carrier i ⊆ wz1PaperTubeCarrier (F.tube i))
    (hcub : WZ1PaperIsCubicalShading S) :
    WZ1PaperIsCubicalShading (singleTubeShading i hmeas hsub) := by
  intro j point hpoint
  exact hcub i point hpoint

/-- Density for the single-tube shading follows from the selected tube's
density bound. -/
lemma dense {delta loss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    {i : Fin F.card}
    (hmeas : MeasurableSet (S.carrier i))
    (hsub : S.carrier i ⊆ wz1PaperTubeCarrier (F.tube i))
    (hdense :
      (Kakeya.realRpowENN delta loss) *
        volume ((wz1PaperBodyFamily F).body i).carrier ≤
      volume (S.carrier i)) :
    (singleTubeShading i hmeas hsub).IsLambdaDense
      (Kakeya.realRpowENN delta loss) := by
  have hcard1 : (singleTubeFamily i).card = 1 := singleTubeAssembly.card_eq_one
  have h₁ : (singleTubeShading i hmeas hsub).mass = volume (S.carrier i) := by
    dsimp only [singleTubeShading, Streamlined.Shading.mass]
    exact sum_card_one hcard1 _
  have h₂ : (wz1PaperBodyFamily (singleTubeFamily i)).mass =
      volume ((wz1PaperBodyFamily F).body i).carrier := by
    dsimp only [singleTubeFamily, wz1PaperBodyFamily, Streamlined.BodyFamily.mass]
    exact sum_card_one hcard1 _
  rw [Streamlined.Shading.IsLambdaDense, h₁, h₂]
  exact hdense

/-- Volume upper bound for the single-tube shading. -/
lemma volume_upper {delta sigma loss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    {i : Fin F.card}
    (hmeas : MeasurableSet (S.carrier i))
    (hsub : S.carrier i ⊆ wz1PaperTubeCarrier (F.tube i))
    (hvol : volume S.union ≤ Kakeya.realRpowENN delta (sigma - loss)) :
    volume (singleTubeShading i hmeas hsub).union ≤
      Kakeya.realRpowENN delta (sigma - loss) := by
  have h₁ : (singleTubeShading i hmeas hsub).union = S.carrier i := by
    ext x
    simp only [singleTubeShading, Streamlined.Shading.union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨j, hx⟩
      exact hx
    · intro hx
      have hcard1 : (singleTubeFamily i).card = 1 := singleTubeAssembly.card_eq_one
      have h0 : 0 < (singleTubeFamily i).card := by rw [hcard1] <;> norm_num
      let z : Fin (singleTubeFamily i).card := ⟨0, h0⟩
      exact ⟨z, hx⟩
  rw [h₁]
  have h₂ : S.carrier i ⊆ S.union := by
    intro x hx
    exact ⟨i, hx⟩
  exact (measure_mono h₂).trans hvol

/-- Essential distinctness is vacuous for a one-tube family. -/
lemma essentially_distinct {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} {i : Fin F.card} :
    WZ2PaperOrdinaryIsEssentiallyDistinct (singleTubeFamily i) := by
  intro first second hne
  exfalso
  have hcard : (singleTubeFamily i).card = 1 := singleTubeAssembly.card_eq_one
  have hfirst : (first : ℕ) = 0 := fin_one_val hcard first
  have hsecond : (second : ℕ) = 0 := fin_one_val hcard second
  have h1 : first = second := by
    apply Fin.ext
    rw [hfirst, hsecond]
  exact hne h1

end singleTubeAssembly

/-- Generalized local grain data for a single-tube shading.

Handles both the case where the tube has nonzero horizontal direction
components and the perfectly vertical case (direction = (0,0,±1)).
In the vertical case, uses `(1,0,0)` as the perpendicular direction. -/
def single_tube_local_grain_data_gen
    {delta sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (i : Fin F.card)
    (hS_sub : S.union ⊆ wz1PaperTubeCarrier (F.tube i))
    (honly : ∀ (j : Fin F.card), S.carrier j ≠ ∅ → j = i)
    (hdelta_pos : 0 < delta)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    {C : ENNReal}
    (hC_ge16 : (16 : ENNReal) ≤ C)
    (hC_top : C ≠ ⊤) :
    PureWZ2LocalGrainData S sigma C := by
  let T := F.tube i
  by_cases hdir : (T.direction 0 ≠ 0 ∨ T.direction 1 ≠ 0)
  · exact single_tube_local_grain_data i hdir hS_sub honly hdelta_pos hsigma_pos hsigma_lt_one hC_ge16 hC_top
  · -- Vertical case: T.direction 0 = 0 and T.direction 1 = 0
    have h0 : T.direction 0 = 0 := by tauto
    have h1 : T.direction 1 = 0 := by tauto
    let v : Point3 := point3 1 0 0
    have hv_norm : ‖v‖ = 1 := by
      simp [v, point3, EuclideanSpace.norm_eq, Fin.sum_univ_succ] <;> norm_num
    have hv_inner : inner ℝ T.direction v = 0 := by
      simp [v, point3, h0, h1, inner, Fin.sum_univ_succ] <;> ring
    exact
      { planeMap := fun (_ : {point : Point3 // point ∈ S.union}) => v
      , planeMap_lipschitz := by
          intro x y
          simp [edist_dist] <;> exact zero_le _
      , planeMap_unit := fun _ => hv_norm
      , planeMap_incidence := by
          intro index point hpoint
          have hne : S.carrier index ≠ ∅ := by
            intro h
            rw [h] at hpoint
            exact hpoint
          have hji : index = i := honly index hne
          have hdir_eq : (F.tube index).direction = T.direction := by
            rw [hji] <;> rfl
          have h_inner : inner ℝ (F.tube index).direction v = 0 := by
            rw [hdir_eq]; exact hv_inner
          rw [h_inner]
          have h_bound : |(0 : ℝ)| ≤ delta := by simpa using hdelta_pos.le
          exact h_bound
      , local_ad := by
          intro rho hrho_ge hrho_le point
          let E := scalarProjection v
              (S.union ∩ Metric.closedBall (point : Point3) (Real.sqrt rho))
          have hE_sub : E ⊆ scalarProjection v (wz1PaperTubeCarrier T) := by
            intro y hy
            rcases hy with ⟨x, hx, rfl⟩
            exact ⟨x, (Set.inter_subset_left.trans hS_sub) hx, rfl⟩
          have h_diam : ∀ (x y : ℝ), x ∈ E → y ∈ E → |x - y| ≤ 14 * delta := by
            intro x y hx hy
            exact tube_projection_perpendicular_diameter
              hdelta_pos T v hv_norm hv_inner x y
              (hE_sub hx) (hE_sub hy)
          have hC_ge : ENNReal.ofReal (14 + 2 : ℝ) ≤ C := by
            have h_eq : (14 + 2 : ℝ) = (16 : ℝ) := by norm_num
            rw [h_eq]; simpa using hC_ge16
          exact bounded_diameter_ad_simple
            (14 : ℝ) (by norm_num) hdelta_pos
            (by linarith) hrho_ge
            (by linarith) (by linarith)
            hC_ge hC_top h_diam
      }

/-- Assemble a complete `PureWZ2GrainConfiguration` for a single selected tube.

This is the Strategy 1 assembly for outputLoss ≥ 2. All fields except
`hcwa_nearby` are proved from the ambient extremal configuration and the
single-tube grain data lemmas.

`hcwa_nearby` is the direct self-cover nearby-scales CWA for the single-tube
family (aurora, in progress).
-/
def single_tube_assembly
    {delta sigma outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (i : Fin F.card)
    (hmeas : MeasurableSet (S.carrier i))
    (hsub : S.carrier i ⊆ wz1PaperTubeCarrier (F.tube i))
    (hline : WZ1PaperIsLineClass F)
    (hcub : WZ1PaperIsCubicalShading S)
    (hdense :
      (Kakeya.realRpowENN delta outputLoss) *
        volume ((wz1PaperBodyFamily F).body i).carrier ≤
      volume (S.carrier i))
    (hvol : volume S.union ≤ Kakeya.realRpowENN delta (sigma - outputLoss))
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (houtputLoss_ge_two : 2 ≤ outputLoss)
    (hdir_vertical : 1 / 2 ≤ |(F.tube i).direction (2 : Fin 3)|)
    (hdelta_small : delta ≤ 1 / 12)
    -- The key remaining hypothesis: nearby-scales CWA for the single tube
    (hcwa_nearby :
      WZ2PaperPureCWAAtNearbyScales
        (singleTubeFamily i)
        (Kakeya.realRpowENN delta (-outputLoss)))
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1) :
    PureWZ2GrainConfiguration sigma outputLoss delta :=
  let F' := singleTubeFamily i
  let S' := singleTubeShading i hmeas hsub
  let C : ENNReal := Kakeya.realRpowENN delta (-outputLoss)
  have hC_top : C ≠ ⊤ := by
    simp [C, Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top
  have hC_ge44 : (44 : ENNReal) ≤ C := by
    have h1 : (44 : ℝ) ≤ Real.rpow delta (-outputLoss) := by
      have h2 : Real.rpow delta (-outputLoss) ≥ Real.rpow delta (-2 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one <;> linarith
      have h3 : Real.rpow delta (-2 : ℝ) = 1 / (delta ^ 2) := by
        simp [Real.rpow_neg, Real.rpow_two]
        <;> field_simp [hdelta_pos.ne'] <;> ring
      rw [h3] at h2
      have h4 : (44 : ℝ) ≤ 1 / (delta ^ 2) := by
        have h5 : delta ^ 2 ≤ 1 / 144 := by nlinarith
        have h6 : 0 < delta ^ 2 := by positivity
        have h7 : 1 / (delta ^ 2) ≥ 144 := by
          calc 1 / (delta ^ 2) ≥ 1 / (1 / 144 : ℝ) := by gcongr
            _ = 144 := by norm_num
        linarith
      linarith
    have h4 : (44 : ENNReal) = ENNReal.ofReal (44 : ℝ) := by norm_num
    rw [h4]
    exact ENNReal.ofReal_le_ofReal h1
  have hC_ge16 : (16 : ENNReal) ≤ C := by
    exact le_trans (by norm_num) hC_ge44
  have hcard1 : F'.card = 1 := singleTubeAssembly.card_eq_one
  have h0 : 0 < F'.card := by rw [hcard1] <;> norm_num
  let z : Fin F'.card := ⟨0, h0⟩
  have honly : ∀ (j : Fin F'.card), S'.carrier j ≠ ∅ → j = z := by
    intro j _
    apply Fin.ext
    have h : (j : ℕ) = 0 := singleTubeAssembly.fin_one_val hcard1 j
    simpa [z] using h
  have hS'_sub : S'.union ⊆ wz1PaperTubeCarrier (F'.tube z) := by
    have h1 : S'.union ⊆ S.carrier i := by
      intro x hx
      rcases hx with ⟨j, hx⟩
      exact hx
    have h2 : F'.tube z = F.tube i := by rfl
    have h3 : S.carrier i ⊆ wz1PaperTubeCarrier (F.tube i) := hsub
    calc S'.union
      ⊆ S.carrier i := h1
    _ ⊆ wz1PaperTubeCarrier (F.tube i) := h3
    _ = wz1PaperTubeCarrier (F'.tube z) := by rw [h2]
  { family := F'
    shading := S'
    line_class := singleTubeAssembly.line_class hline
    cubical := singleTubeAssembly.cubical hmeas hsub hcub
    extremal :=
      { delta_pos := hdelta_pos
        delta_le_one := hdelta_le_one
        nonempty := by
          have h : F'.card = 1 := singleTubeAssembly.card_eq_one
          rw [Kakeya.Streamlined.TubeFamily.Nonempty, h]
          <;> norm_num
        cwa_nearby_scales := hcwa_nearby
        cubical := singleTubeAssembly.cubical hmeas hsub hcub
        dense := singleTubeAssembly.dense hmeas hsub hdense
        volume_upper := singleTubeAssembly.volume_upper hmeas hsub hvol }
    top_level_cwa :=
      single_tube_top_level_cwa
        (hF_card := singleTubeAssembly.card_eq_one)
        hdelta_pos hdelta_small
        (singleTubeAssembly.line_class hline)
        houtputLoss_ge_two
    globalGrains :=
      single_tube_global_grain_data
        z hdir_vertical
        hS'_sub
        hdelta_pos hsigma_pos hsigma_lt_one
        hC_ge44 hC_top
    localGrains :=
      single_tube_local_grain_data_gen
        z
        hS'_sub honly
        hdelta_pos hsigma_pos hsigma_lt_one
        hC_ge16 hC_top
  }

end Kakeya.Assouad

end
