import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.EilenbergGeneral
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.EilenbergMultidim
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.EuclideanHausdorffFinite
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.OneDIntegralBound
import Mathlib.Tactic

/-!
# Finite Perimeter from Hausdorff Bound

Non-sharp bound: if `μH[n-1](∂E) < ∞`, then `P(E) < ∞`.

## Proof route

1. **1D lemma** (`oneD_boundary_integral`): For measurable `A ⊂ ℝ` and smooth
   compactly supported `f` with `|f| ≤ 1`, `|∫_A f'| ≤ μH[0](∂A)`.

2. **Coordinate split**: For each coordinate `j`, split `E n` as `E(n-1) × ℝ`
   along `j` using `piFinSuccAbove`.

3. **Slice boundary inclusion**: `∂(slice_z E) ⊆ {t | (z,t) ∈ ∂E}`.

4. **Directional bound**: Fubini + 1D lemma + projection Eilenberg gives
   `directionalVariation E e_j ≤ μH[n-1](∂E)`.

5. **Sum**: `perimeter E ≤ ∑_j directionalVariation E e_j ≤ n · μH[n-1](∂E)`.

## Whiteprint
Supports the `structure_theorem` bootstrap.
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry

variable {n : ℕ}

-- ============================================================================
-- Section 1: 1D lemma (TODO: flint)
-- ============================================================================

section OneD

/-- **1D boundary integral bound.**
For a measurable set `A ⊂ ℝ` and smooth compactly supported `f` with `|f| ≤ 1`:
`ENNReal.ofReal |∫_A f'| ≤ μH[0](∂A)`. -/
lemma oneD_boundary_integral
    {A : Set ℝ} (hA : MeasurableSet A)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcompact : HasCompactSupport f)
    (hbound : ∀ x, |f x| ≤ 1) :
    ENNReal.ofReal |∫ x in A, deriv f x| ≤ μH[0] (frontier A) :=
  have h1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have h2 := oneD_integral_bound' hA h1 hcompact (C := 1) hbound
  have h3 : ENNReal.ofReal (1 : ℝ) * μH[0] (frontier A) = μH[0] (frontier A) := by simp
  h3 ▸ h2

end OneD

-- ============================================================================
-- Section 2: Coordinate split
-- ============================================================================

section CoordinateSplit

open EilenbergInequality

variable {m : ℕ}

/-- Measure-preserving equivalence splitting `E (m+1)` into `E m × ℝ`
along coordinate `j`. -/
noncomputable def coordSplit (j : Fin (m + 1)) : E (m + 1) ≃ᵐ E m × ℝ :=
  let e1 : E (m + 1) ≃ᵐ (Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm
  let e2 : (Fin (m + 1) → ℝ) ≃ᵐ (ℝ × (Fin m → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) j
  let e3 : (ℝ × (Fin m → ℝ)) ≃ᵐ ((Fin m → ℝ) × ℝ) :=
    MeasurableEquiv.prodComm
  let e4 : (Fin m → ℝ) ≃ᵐ E m :=
    MeasurableEquiv.toLp 2 (Fin m → ℝ)
  let e4' : ((Fin m → ℝ) × ℝ) ≃ᵐ (E m × ℝ) :=
    e4.prodCongr (MeasurableEquiv.refl ℝ)
  e1.trans e2 |>.trans e3 |>.trans e4'

/-- Projection dropping coordinate `j`. -/
noncomputable def projCoord (j : Fin (m + 1)) : E (m + 1) → E m :=
  Prod.fst ∘ coordSplit j

lemma coordSplit_apply (j : Fin (m + 1)) (x : E (m + 1)) :
    (coordSplit j x).2 = x j := by
  simp [coordSplit, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm,
    MeasurableEquiv.toLp]
  <;> rfl

lemma coordSplit_symm_tDirection (j : Fin (m + 1)) :
    (coordSplit j).symm (0, (1 : ℝ)) = EuclideanSpace.single j 1 := by
  let v : E (m + 1) := (coordSplit j).symm (0, 1)
  have h1 : ∀ (k : Fin (m + 1)), v k = if k = j then 1 else 0 := by
    intro k
    by_cases h : k = j
    · subst h
      simp [v, coordSplit, MeasurableEquiv.trans_apply,
        MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNth_apply_same]
      <;> rfl
    · have h2 : k ∈ Finset.image (Fin.succAbove j) Finset.univ := by
        rw [Fin.image_succAbove_univ j]
        simp [h]
      rcases Finset.mem_image.mp h2 with ⟨i, _, rfl⟩
      simp [v, coordSplit, MeasurableEquiv.trans_apply,
        MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNth_apply_succAbove, h]
      <;> rfl
  have h2 : v = EuclideanSpace.single j 1 := by
    ext k
    rw [h1 k, EuclideanSpace.single_apply]
    <;> rfl
  exact h2

lemma projCoord_apply (j : Fin (m + 1)) (x : E (m + 1)) (i : Fin m) :
    (projCoord j x) i = x (Fin.succAbove j i) := by
  simp [projCoord, coordSplit, MeasurableEquiv.trans_apply]
  <;> rfl

lemma projCoord_lipschitz (j : Fin (m + 1)) :
    LipschitzWith 1 (projCoord j) := by
  intro x y
  set z := x - y with hz
  set w := projCoord j z with hw
  have h1 : ‖w‖ ^ 2 = ∑ i : Fin m, |w i| ^ 2 := by
    have h11 : ‖w‖ ^ 2 = inner ℝ w w := by
      rw [inner_self_eq_norm_sq_to_K] <;> norm_cast
    rw [h11, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    have h12 : inner ℝ (w i) (w i) = |w i| ^ 2 := by
      simp [inner_self_eq_norm_sq_to_K] <;> ring
    exact h12
  have h2 : ‖z‖ ^ 2 = ∑ i : Fin (m + 1), |z i| ^ 2 := by
    have h21 : ‖z‖ ^ 2 = inner ℝ z z := by
      rw [inner_self_eq_norm_sq_to_K] <;> norm_cast
    rw [h21, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    have h22 : inner ℝ (z i) (z i) = |z i| ^ 2 := by
      simp [inner_self_eq_norm_sq_to_K] <;> ring
    exact h22
  have h_wi : ∀ i : Fin m, w i = z (Fin.succAbove j i) := by
    intro i
    rw [projCoord_apply] <;> rfl
  have h_eq_sum : ∑ i : Fin m, |w i| ^ 2 = ∑ i : Fin m, |z (Fin.succAbove j i)| ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _; rw [h_wi i]
  have h_inj : Function.Injective (Fin.succAbove j : Fin m → Fin (m + 1)) :=
    j.succAbove_right_injective
  have h_injOn : Set.InjOn (Fin.succAbove j) (↑(Finset.univ : Finset (Fin m))) :=
    fun x _ y _ h => h_inj h
  have h3 : ∑ i : Fin m, |z (Fin.succAbove j i)| ^ 2 ≤ ∑ i : Fin (m + 1), |z i| ^ 2 := by
    have h_img : ∑ i : Fin m, |z (Fin.succAbove j i)| ^ 2 =
        ∑ k ∈ Finset.image (Fin.succAbove j) (Finset.univ), |z k| ^ 2 := by
      rw [Finset.sum_image h_injOn] <;> rfl
    rw [h_img]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k _; exact Finset.mem_univ k
    · intro k _ _; positivity
  have h4 : ‖w‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    calc
      ‖w‖ ^ 2 = ∑ i : Fin m, |w i| ^ 2 := h1
      _ = ∑ i : Fin m, |z (Fin.succAbove j i)| ^ 2 := h_eq_sum
      _ ≤ ∑ i : Fin (m + 1), |z i| ^ 2 := h3
      _ = ‖z‖ ^ 2 := h2.symm
  have h5 : 0 ≤ ‖w‖ := by positivity
  have h6 : 0 ≤ ‖z‖ := by positivity
  have h_main : ‖w‖ ≤ ‖z‖ := by nlinarith
  have hlin : projCoord j (x - y) = projCoord j x - projCoord j y := by
    ext i; simp [projCoord_apply] <;> rfl
  have h_main2 : ‖projCoord j x - projCoord j y‖ ≤ ‖x - y‖ := by
    have h1 : ‖projCoord j (x - y)‖ ≤ ‖x - y‖ := by simpa [hw, hz] using h_main
    rw [hlin] at h1
    exact h1
  have h' : edist (projCoord j x) (projCoord j y) = ENNReal.ofReal ‖projCoord j x - projCoord j y‖ := by
    simp [edist_dist, dist_eq_norm]
  rw [h']
  have h'' : ENNReal.ofReal ‖projCoord j x - projCoord j y‖ ≤ ENNReal.ofReal ‖x - y‖ := by
    exact ENNReal.ofReal_le_ofReal h_main2
  have h3 : edist x y = ENNReal.ofReal ‖x - y‖ := by
    simp [edist_dist, dist_eq_norm]
  rw [h3]
  simpa using h''

lemma coordSplit_measurePreserving (j : Fin (m + 1)) :
    MeasurePreserving (coordSplit j) volume volume := by
  let e1 : E (m + 1) ≃ᵐ (Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm
  let e2 : (Fin (m + 1) → ℝ) ≃ᵐ (ℝ × (Fin m → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) j
  let e3 : (ℝ × (Fin m → ℝ)) ≃ᵐ ((Fin m → ℝ) × ℝ) :=
    MeasurableEquiv.prodComm
  let e4 : (Fin m → ℝ) ≃ᵐ E m :=
    MeasurableEquiv.toLp 2 (Fin m → ℝ)
  have h1 : MeasurePreserving e1 volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (ι := Fin (m + 1))
  have h2 : MeasurePreserving e2 volume volume :=
    volume_preserving_piFinSuccAbove (fun _ => ℝ) j
  have h3 : MeasurePreserving e3 volume volume := by
    have hv1 : (volume : Measure (ℝ × (Fin m → ℝ))) = volume.prod volume :=
      Measure.volume_eq_prod ℝ (Fin m → ℝ)
    have hv2 : (volume : Measure ((Fin m → ℝ) × ℝ)) = volume.prod volume :=
      Measure.volume_eq_prod (Fin m → ℝ) ℝ
    refine' ⟨e3.measurable_toFun, _⟩
    rw [hv1, hv2]
    exact Measure.measurePreserving_swap.map_eq
  have h41 : MeasurePreserving e4 volume volume :=
    PiLp.volume_preserving_toLp (ι := Fin m)
  have h42 : MeasurePreserving (MeasurableEquiv.refl ℝ) volume volume :=
    MeasurePreserving.id volume
  let e4' : ((Fin m → ℝ) × ℝ) ≃ᵐ (E m × ℝ) :=
    e4.prodCongr (MeasurableEquiv.refl ℝ)
  have hprod : MeasurePreserving e4' (volume.prod volume) (volume.prod volume) :=
    MeasurePreserving.prod h41 h42
  have hv : (volume : Measure ((Fin m → ℝ) × ℝ)) = volume.prod volume :=
    Measure.volume_eq_prod (Fin m → ℝ) ℝ
  have hv' : (volume : Measure (E m × ℝ)) = volume.prod volume :=
    Measure.volume_eq_prod (E m) ℝ
  have h4 : MeasurePreserving e4' volume volume := by
    simpa [hv, hv'] using hprod
  exact h4.comp (h3.comp (h2.comp h1))

/-- `coordSplit j` is additive. -/
lemma coordSplit_add (j : Fin (m + 1)) (x y : E (m + 1)) :
    coordSplit j (x + y) = coordSplit j x + coordSplit j y := by
  apply Prod.ext
  · ext i; simp [projCoord_apply, Pi.add_apply] <;> rfl
  · simp [coordSplit_apply, Pi.add_apply] <;> rfl

/-- `coordSplit j` is homogeneous. -/
lemma coordSplit_smul (j : Fin (m + 1)) (c : ℝ) (x : E (m + 1)) :
    coordSplit j (c • x) = c • coordSplit j x := by
  apply Prod.ext
  · ext i; simp [projCoord_apply, Pi.smul_apply] <;> rfl
  · simp [coordSplit_apply, Pi.smul_apply] <;> rfl

/-- `(coordSplit j).symm` is additive. -/
lemma coordSplit_symm_add (j : Fin (m + 1)) (p q : E m × ℝ) :
    (coordSplit j).symm (p + q) = (coordSplit j).symm p + (coordSplit j).symm q := by
  let e := coordSplit j
  apply e.injective
  rw [e.apply_symm_apply, coordSplit_add j, e.apply_symm_apply, e.apply_symm_apply]

/-- `(coordSplit j).symm` is homogeneous. -/
lemma coordSplit_symm_smul (j : Fin (m + 1)) (c : ℝ) (p : E m × ℝ) :
    (coordSplit j).symm (c • p) = c • (coordSplit j).symm p := by
  let e := coordSplit j
  apply e.injective
  rw [e.apply_symm_apply, coordSplit_smul j, e.apply_symm_apply]

end CoordinateSplit

-- ============================================================================
-- Section 3: Slice boundary inclusion
-- ============================================================================

section SliceBoundary

open EilenbergInequality

variable {m : ℕ} {S : Set (E (m + 1))} {j : Fin (m + 1)} {z : E m}

/-- Continuity of the slice map `t ↦ (coordSplit j).symm (z, t)`. -/
lemma slice_map_continuous (j : Fin (m + 1)) (z : E m) :
    Continuous (fun t : ℝ => (coordSplit j).symm (z, t)) := by
  let i : ℝ → E (m + 1) := fun t => (coordSplit j).symm (z, t)
  have h_coord : ∀ (k : Fin (m + 1)), Continuous (fun t : ℝ => (i t) k) := by
    intro k
    by_cases h : k = j
    · have h_kj : k = j := h
      have h_eq : ∀ (t : ℝ), (i t) k = t := by
        intro t
        rw [h_kj]
        simp [i, coordSplit, MeasurableEquiv.trans_apply,
          MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNth_apply_same] <;> rfl
      rw [funext h_eq]
      exact continuous_id
    · have h2 : k ∈ Finset.image (Fin.succAbove j) Finset.univ := by
        rw [Fin.image_succAbove_univ j] <;> simp [h]
      rcases Finset.mem_image.mp h2 with ⟨i0, _, rfl⟩
      have h_eq : ∀ (t : ℝ), (i t) (Fin.succAbove j i0) = z i0 := by
        intro t
        simp [i, coordSplit, MeasurableEquiv.trans_apply,
          MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNth_apply_succAbove] <;> rfl
      rw [funext h_eq]
      exact continuous_const
  have h_pi : Continuous (fun t : ℝ => (fun k : Fin (m + 1) => (i t) k)) :=
    continuous_pi h_coord
  have h_homeomorph : (PiLp.homeomorph (p := 2) (β := fun _ : Fin (m + 1) => ℝ)).symm ∘
      (fun t : ℝ => (fun k : Fin (m + 1) => (i t) k)) = i := by
    funext t
    apply PiLp.ext
    intro k
    rfl
  simpa [h_homeomorph] using (PiLp.homeomorph (p := 2) (β := fun _ : Fin (m + 1) => ℝ)).symm.continuous.comp h_pi

/-- Compact support of the sliced function. -/
lemma slice_map_compactSupport (j : Fin (m + 1)) (z : E m)
    {f : E (m + 1) → ℝ} (hcompact : HasCompactSupport f) :
    HasCompactSupport (fun t : ℝ => f ((coordSplit j).symm (z, t))) := by
  let i : ℝ → E (m + 1) := fun t => (coordSplit j).symm (z, t)
  let π : E (m + 1) → ℝ := fun x => x j
  have h_left_inverse : ∀ t, π (i t) = t := by
    intro t
    simp [i, π, coordSplit, MeasurableEquiv.trans_apply,
      MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNth_apply_same] <;> rfl
  have h1 : Function.support (fun t : ℝ => f (i t)) ⊆ i ⁻¹' (tsupport f) := by
    intro t ht
    have h2 : f (i t) ≠ 0 := by simpa [Function.mem_support] using ht
    have h3 : i t ∈ Function.support f := by simpa [Function.mem_support] using h2
    have h4 : i t ∈ tsupport f := subset_closure h3
    exact h4
  have h5 : IsClosed (i ⁻¹' (tsupport f)) :=
    (isClosed_tsupport f).preimage (slice_map_continuous j z)
  have h6 : i ⁻¹' (tsupport f) ⊆ π '' (tsupport f) := by
    intro t ht
    have h7 : i t ∈ tsupport f := ht
    have h8 : π (i t) = t := h_left_inverse t
    exact ⟨i t, h7, h8⟩
  have h9 : IsCompact (tsupport f) := hcompact.isCompact
  have hπ : Continuous π := by
    let proj_j : E (m + 1) →L[ℝ] ℝ :=
      { toFun := π
        map_add' := by intro x y; simp [π]
        map_smul' := by intro c x; simp [π] }
    exact proj_j.continuous
  have h10 : IsCompact (π '' (tsupport f)) := h9.image hπ
  have h11 : IsCompact (i ⁻¹' (tsupport f)) := h10.of_isClosed_subset h5 h6
  have h12 : tsupport (fun t : ℝ => f (i t)) ⊆ i ⁻¹' (tsupport f) :=
    closure_minimal h1 h5
  exact h11.of_isClosed_subset (isClosed_tsupport _) h12

/-- Smoothness of the slice map `t ↦ (coordSplit j).symm (z, t)`. -/
lemma slice_map_contDiff (j : Fin (m + 1)) (z : E m) :
    ContDiff ℝ ∞ (fun t : ℝ => (coordSplit j).symm (z, t)) := by
  let i : ℝ → E (m + 1) := fun t => (coordSplit j).symm (z, t)
  have h : ∀ (k : Fin (m + 1)), ContDiff ℝ ∞ (fun t : ℝ => (i t) k) := by
    intro k
    by_cases h : k = j
    · have h_kj : k = j := h
      have h_eq : (fun t : ℝ => (i t) k) = fun t : ℝ => t := by
        funext t
        rw [h_kj]
        simp [i, coordSplit, MeasurableEquiv.trans_apply,
          MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNth_apply_same] <;> rfl
      rw [h_eq]
      exact contDiff_id
    · have h2 : k ∈ Finset.image (Fin.succAbove j) Finset.univ := by
        rw [Fin.image_succAbove_univ j] <;> simp [h]
      rcases Finset.mem_image.mp h2 with ⟨i0, _, rfl⟩
      have h_eq : (fun t : ℝ => (i t) (Fin.succAbove j i0)) = fun _ : ℝ => z i0 := by
        funext t
        simp [i, coordSplit, MeasurableEquiv.trans_apply,
          MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNth_apply_succAbove] <;> rfl
      rw [h_eq]
      exact contDiff_const
  exact contDiff_piLp' (p := 2) h

/-- The slice map `t ↦ (coordSplit j).symm (z, t)` has derivative
`(coordSplit j).symm (0, 1) = EuclideanSpace.single j 1`. -/
lemma slice_map_hasDerivAt (j : Fin (m + 1)) (z : E m) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (coordSplit j).symm (z, t))
      ((coordSplit j).symm (0, 1)) t := by
  let c : E (m + 1) := (coordSplit j).symm (0, 1)
  let a : E (m + 1) := (coordSplit j).symm (z, 0)
  have h_affine : ∀ (s : ℝ), (coordSplit j).symm (z, s) = a + s • c := by
    intro s
    have h1 : (z, s) = (z, 0) + s • (0, 1) := by ext <;> simp <;> ring
    calc
      (coordSplit j).symm (z, s) = (coordSplit j).symm ((z, 0) + s • (0, 1)) := by rw [h1]
      _ = (coordSplit j).symm (z, 0) + (coordSplit j).symm (s • (0, 1)) :=
        coordSplit_symm_add j (z, 0) (s • (0, 1))
      _ = a + s • c := by
        rw [coordSplit_symm_smul j s (0, 1)] <;> rfl
  have h_eq : (fun t : ℝ => (coordSplit j).symm (z, t)) = fun t : ℝ => a + t • c := by
    funext t; exact h_affine t
  rw [h_eq]
  have h_smul : HasDerivAt (fun t : ℝ => t • c) c t := by
    rw [hasDerivAt_iff_isLittleO]
    have h_zero : (fun x' : ℝ => x' • c - t • c - (x' - t) • c) = 0 := by
      funext x'
      simp [sub_smul, add_smul] <;> abel
    rw [h_zero]
    exact Asymptotics.isLittleO_zero _ _
  exact h_smul.const_add a

/-- Chain rule: derivative of `t ↦ ψ ((coordSplit j).symm (z, t))` equals
the directional derivative of `ψ` in direction `single j 1`. -/
lemma sliced_deriv_eq_dirDeriv
    (j : Fin (m + 1)) (z : E m) (t : ℝ)
    {ψ : E (m + 1) → ℝ} (hψ : Differentiable ℝ ψ) :
    deriv (fun t : ℝ => ψ ((coordSplit j).symm (z, t))) t =
    fderiv ℝ ψ ((coordSplit j).symm (z, t)) (EuclideanSpace.single j 1) := by
  let i_z : ℝ → E (m + 1) := fun t => (coordSplit j).symm (z, t)
  have h_i_deriv : HasDerivAt i_z ((coordSplit j).symm (0, 1)) t :=
    slice_map_hasDerivAt j z t
  have hψ' : HasFDerivAt ψ (fderiv ℝ ψ (i_z t)) (i_z t) :=
    (hψ (i_z t)).hasFDerivAt
  have h_comp : HasDerivAt (ψ ∘ i_z)
      (fderiv ℝ ψ (i_z t) ((coordSplit j).symm (0, 1))) t :=
    hψ'.comp_hasDerivAt t h_i_deriv
  have h_dir : (coordSplit j).symm (0, 1) = EuclideanSpace.single j 1 :=
    coordSplit_symm_tDirection j
  rw [h_dir] at h_comp
  exact h_comp.deriv

/-- The frontier of a slice is contained in the slice of the frontier. -/
lemma slice_frontier_subset :
    frontier {t : ℝ | (coordSplit j).symm (z, t) ∈ S} ⊆
    {t : ℝ | (coordSplit j).symm (z, t) ∈ frontier S} := by
  let S_t := {t : ℝ | (coordSplit j).symm (z, t) ∈ S}
  let i : ℝ → E (m + 1) := fun t => (coordSplit j).symm (z, t)
  have hi_cont : Continuous i := slice_map_continuous j z
  intro t ht
  have h1 : t ∈ closure S_t := frontier_subset_closure ht
  have h2 : t ∈ closure S_tᶜ := by
    rw [frontier_eq_closure_inter_closure] at ht <;> exact ht.2
  have h_image1 : i '' closure S_t ⊆ closure (i '' S_t) := by
    exact image_closure_subset_closure_image hi_cont
  have h_image2 : i '' closure S_tᶜ ⊆ closure (i '' S_tᶜ) := by
    exact image_closure_subset_closure_image hi_cont
  have h5 : i '' S_t ⊆ S := by
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    exact ht
  have h6 : i '' S_tᶜ ⊆ Sᶜ := by
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    exact ht
  have h3 : i t ∈ closure S := by
    have h7 : i t ∈ i '' closure S_t := ⟨t, h1, rfl⟩
    exact closure_mono h5 (h_image1 h7)
  have h4 : i t ∈ closure Sᶜ := by
    have h7 : i t ∈ i '' closure S_tᶜ := ⟨t, h2, rfl⟩
    exact closure_mono h6 (h_image2 h7)
  rw [frontier_eq_closure_inter_closure]
  exact ⟨h3, h4⟩

end SliceBoundary

-- ============================================================================
-- Section 4: Directional variation bound (main hard lemma)
-- ============================================================================

section DirectionalBound

open EilenbergInequality Perimeter

variable {m : ℕ} {S : Set (E (m + 1))} (hS : MeasurableSet S) (j : Fin (m + 1))

/-- Helper: Fubini change of variables for directional derivative. -/
lemma fubini_dirDeriv
    {m : ℕ} {S : Set (E (m + 1))} (hS : MeasurableSet S)
    (j : Fin (m + 1)) (ψ : TestScalar) :
    ∫ x in S, fderiv ℝ ψ.toFun x (EuclideanSpace.single j 1) =
    ∫ z : E m, ∫ t in {t | (coordSplit j).symm (z, t) ∈ S},
      deriv (fun t => ψ.toFun ((coordSplit j).symm (z, t))) t := by
  let e := coordSplit j
  let v := EuclideanSpace.single j (1 : ℝ)
  let h_func : E (m + 1) → ℝ := fun x => fderiv ℝ ψ.toFun x v
  let g : E m × ℝ → ℝ := fun p => h_func (e.symm p)
  have h1 : Continuous (fderiv ℝ ψ.toFun) := ψ.smooth.continuous_fderiv (by simp)
  have h2 : Continuous (fun (f' : E (m + 1) →L[ℝ] ℝ) => f' v) := by fun_prop
  have h_cont : Continuous h_func := h2.comp h1
  have h_compact : HasCompactSupport h_func :=
    HasCompactSupport.fderiv_apply (𝕜 := ℝ) (hf := ψ.compact) v
  have h_h_int : Integrable h_func volume :=
    h_cont.integrable_of_hasCompactSupport h_compact
  have hmp_symm : MeasurePreserving e.symm volume volume :=
    (coordSplit_measurePreserving j).symm
  have h_g_int : Integrable g volume := hmp_symm.integrable_comp_of_integrable h_h_int
  have hme : MeasurableEmbedding e := e.measurableEmbedding
  have h_image_meas : MeasurableSet (e '' S) := hme.measurableSet_image.mpr hS
  have h_indicator_int : Integrable (Set.indicator (e '' S) g) volume :=
    Integrable.indicator h_g_int h_image_meas
  have hvol : (volume : Measure (E m × ℝ)) = volume.prod volume :=
    Measure.volume_eq_prod (E m) ℝ
  have h_indicator_int' : Integrable (Set.indicator (e '' S) g) (volume.prod volume) := by
    have h : (volume.prod volume : Measure (E m × ℝ)) = volume := hvol.symm
    rw [h]
    exact h_indicator_int
  have h_change : ∫ x in S, h_func x = ∫ p : E m × ℝ, Set.indicator (e '' S) g p := by
    have hmp : MeasurePreserving e volume volume := coordSplit_measurePreserving j
    have hme2 : MeasurableEmbedding e := e.measurableEmbedding
    have h : ∫ p in e '' S, g p = ∫ x in S, g (e x) := hmp.setIntegral_image_emb hme2 g S
    have h2 : (fun x : E (m + 1) => g (e x)) = h_func := by funext x; simp [g]
    have h3 : ∫ x in S, h_func x = ∫ p in e '' S, g p := by
      rw [←h2]
      exact h.symm
    have h4 : ∫ p : E m × ℝ, Set.indicator (e '' S) g p = ∫ p in e '' S, g p := by
      rw [integral_indicator h_image_meas] <;> rfl
    rw [h3, h4]
  have h_fubini_eq : ∫ p : E m × ℝ, Set.indicator (e '' S) g p =
      ∫ z : E m, ∫ t : ℝ, Set.indicator (e '' S) g (z, t) :=
    integral_prod (Set.indicator (e '' S) g) h_indicator_int'
  have h_main : ∫ z : E m, ∫ t : ℝ, Set.indicator (e '' S) g (z, t) =
      ∫ z : E m, ∫ t in {t | e.symm (z, t) ∈ S},
        deriv (fun t => ψ.toFun (e.symm (z, t))) t := by
    apply congr_arg (fun (f : E m → ℝ) => ∫ z : E m, f z)
    funext z
    have h_set : {t : ℝ | (z, t) ∈ e '' S} = {t : ℝ | e.symm (z, t) ∈ S} := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨x, hx, h_eq⟩
        have h3 : e x = (z, t) := h_eq
        have h4 : x = e.symm (z, t) := by rw [←h3] <;> simp
        rw [h4] at hx
        exact hx
      · intro h
        exact ⟨e.symm (z, t), h, by simp⟩
    have h_slice_meas : MeasurableSet {t : ℝ | (z, t) ∈ e '' S} := by
      have h : Measurable (fun t : ℝ => (z, t)) := by fun_prop
      exact h_image_meas.preimage h
    have h_c : ∫ t : ℝ, Set.indicator (e '' S) g (z, t) =
        ∫ t in {t | (z, t) ∈ e '' S}, g (z, t) := by
      have h_eq1 : (fun t : ℝ => Set.indicator (e '' S) g (z, t)) =
          Set.indicator {t | (z, t) ∈ e '' S} (fun t : ℝ => g (z, t)) := by
        funext t
        simp [Set.indicator_apply]
        <;> rfl
      rw [h_eq1, integral_indicator h_slice_meas] <;> rfl
    rw [h_c, h_set]
    apply congr_arg (fun (f : ℝ → ℝ) => ∫ t in {t | e.symm (z, t) ∈ S}, f t)
    funext t
    have h_diff : Differentiable ℝ ψ.toFun := ψ.smooth.differentiable (by simp)
    exact (sliced_deriv_eq_dirDeriv j z t h_diff).symm
  rw [h_change, h_fubini_eq, h_main]

/-- Slice Hausdorff bound: `μH[0](∂(S_z)) ≤ μH[0](∂S ∩ projCoord⁻¹{z})`. -/
lemma slice_hausdorff_le {m : ℕ} {S : Set (E (m + 1))} {j : Fin (m + 1)} {z : E m} :
    μH[0] (frontier {t : ℝ | (coordSplit j).symm (z, t) ∈ S}) ≤
    μH[0] (frontier S ∩ Set.preimage (projCoord j) {z}) := by
  let i : ℝ → E (m + 1) := fun t => (coordSplit j).symm (z, t)
  have h_inj : Function.Injective i := by
    intro t1 t2 h
    have h1 : (i t1) j = (i t2) j := by rw [h]
    have h2 : (i t1) j = t1 := by
      simp [i, coordSplit, MeasurableEquiv.trans_apply,
        MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNth_apply_same] <;> rfl
    have h3 : (i t2) j = t2 := by
      simp [i, coordSplit, MeasurableEquiv.trans_apply,
        MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNth_apply_same] <;> rfl
    rw [h2, h3] at h1
    exact h1
  have h_proj : ∀ t, projCoord j (i t) = z := by
    intro t
    simp [projCoord, i, coordSplit, MeasurableEquiv.trans_apply]
    <;> rfl
  have h_sub1 : frontier {t : ℝ | i t ∈ S} ⊆ {t : ℝ | i t ∈ frontier S} :=
    slice_frontier_subset (S := S) (j := j) (z := z)
  have h_img_sub : i '' frontier {t : ℝ | i t ∈ S} ⊆ frontier S ∩ Set.preimage (projCoord j) {z} := by
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    have h1 : i t ∈ frontier S := h_sub1 ht
    have h2 : projCoord j (i t) = z := h_proj t
    exact ⟨h1, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using h2⟩
  have h_iso : Isometry i := by
    have h_diff : ∀ (t1 t2 : ℝ), i t1 - i t2 = EuclideanSpace.single j (t1 - t2) := by
      intro t1 t2
      ext k
      by_cases h : k = j
      · rw [h]
        simp [i, EuclideanSpace.single_apply, coordSplit, MeasurableEquiv.trans_apply,
          MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNth_apply_same] <;> rfl
      · have h2 : ∃ (i0 : Fin m), k = Fin.succAbove j i0 := by
          have h3 : k ∈ Finset.image (Fin.succAbove j) Finset.univ := by
            rw [Fin.image_succAbove_univ j] <;> simp [h]
          rcases Finset.mem_image.mp h3 with ⟨i0, _, h4⟩
          exact ⟨i0, h4.symm⟩
        rcases h2 with ⟨i0, rfl⟩
        have h_eq1 : (i t1) (Fin.succAbove j i0) = z i0 := by
          simp [i, coordSplit, MeasurableEquiv.trans_apply,
            MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNth_apply_succAbove] <;> rfl
        have h_eq2 : (i t2) (Fin.succAbove j i0) = z i0 := by
          simp [i, coordSplit, MeasurableEquiv.trans_apply,
            MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNth_apply_succAbove] <;> rfl
        simp [EuclideanSpace.single_apply, h, h_eq1, h_eq2] <;> rfl
    intro t1 t2
    have h1 : ‖i t1 - i t2‖ = ‖EuclideanSpace.single j (t1 - t2)‖ := by
      exact congr_arg (fun x : E (m + 1) => ‖x‖) (h_diff t1 t2)
    have h2 : ‖EuclideanSpace.single j (t1 - t2)‖ = |t1 - t2| := by
      rw [EuclideanSpace.norm_single j (t1 - t2)]
      <;> simp [Real.norm_eq_abs]
    have h3 : dist (i t1) (i t2) = dist t1 t2 := by
      simp [dist_eq_norm, h1, h2, Real.norm_eq_abs]
    have h4 : edist (i t1) (i t2) = edist t1 t2 := by
      rw [edist_dist, edist_dist, h3]
    exact h4
  have h_meas0 : μH[0] (i '' frontier {t : ℝ | i t ∈ S}) =
      μH[0] (frontier {t : ℝ | i t ∈ S}) := by
    have h_preimage : μH[0] (i ⁻¹' (i '' frontier {t : ℝ | i t ∈ S})) =
        μH[0] ((i '' frontier {t : ℝ | i t ∈ S}) ∩ Set.range i) :=
      Isometry.hausdorffMeasure_preimage h_iso (by norm_num) (i '' frontier {t : ℝ | i t ∈ S})
    have h4 : i ⁻¹' (i '' frontier {t : ℝ | i t ∈ S}) = frontier {t : ℝ | i t ∈ S} := by
      exact Set.preimage_image_eq _ h_inj
    have h5 : (i '' frontier {t : ℝ | i t ∈ S}) ∩ Set.range i = i '' frontier {t : ℝ | i t ∈ S} := by
      apply Set.inter_eq_left.mpr
      intro x hx
      rcases hx with ⟨t, _, rfl⟩
      exact ⟨t, rfl⟩
    rw [h4, h5] at h_preimage
    exact h_preimage.symm
  rw [← h_meas0]
  exact measure_mono h_img_sub

/-- Integrability of the sliced directional derivative integral. -/
lemma sliced_deriv_integrable
    {m : ℕ} {S : Set (E (m + 1))} (hS : MeasurableSet S)
    (j : Fin (m + 1)) (ψ : TestScalar) :
    Integrable (fun z : E m => ∫ t in {t | (coordSplit j).symm (z, t) ∈ S},
      deriv (fun t => ψ.toFun ((coordSplit j).symm (z, t))) t) volume := by
  let e := coordSplit j
  let h_func : E (m + 1) → ℝ := fun x => fderiv ℝ ψ.toFun x (EuclideanSpace.single j 1)
  let g : E m × ℝ → ℝ := fun p => h_func (e.symm p)
  have h_h_int : Integrable h_func volume := by
    have h1 : Continuous (fderiv ℝ ψ.toFun) := ψ.smooth.continuous_fderiv (by simp)
    have h2 : Continuous (fun (f' : E (m + 1) →L[ℝ] ℝ) => f' (EuclideanSpace.single j 1)) := by fun_prop
    have h_cont : Continuous h_func := h2.comp h1
    have h_compact : HasCompactSupport h_func :=
      HasCompactSupport.fderiv_apply (𝕜 := ℝ) (hf := ψ.compact) (EuclideanSpace.single j 1)
    exact h_cont.integrable_of_hasCompactSupport h_compact
  have hmp_symm : MeasurePreserving e.symm volume volume :=
    (coordSplit_measurePreserving j).symm
  have h_g_int : Integrable g volume := hmp_symm.integrable_comp_of_integrable h_h_int
  have hme : MeasurableEmbedding e := e.measurableEmbedding
  have h_image_meas : MeasurableSet (e '' S) := hme.measurableSet_image.mpr hS
  have h_indicator_int : Integrable (Set.indicator (e '' S) g) volume :=
    Integrable.indicator h_g_int h_image_meas
  have hvol : (volume : Measure (E m × ℝ)) = volume.prod volume :=
    Measure.volume_eq_prod (E m) ℝ
  have h_indicator_int' : Integrable (Set.indicator (e '' S) g) (volume.prod volume) := by
    have h : (volume.prod volume : Measure (E m × ℝ)) = volume := hvol.symm
    rw [h]
    exact h_indicator_int
  have h_fubini_int : Integrable (fun z : E m => ∫ t : ℝ, Set.indicator (e '' S) g (z, t)) volume :=
    h_indicator_int'.integral_prod_left
  have h_eq_fun : (fun z : E m => ∫ t : ℝ, Set.indicator (e '' S) g (z, t)) =
      (fun z : E m => ∫ t in {t | (coordSplit j).symm (z, t) ∈ S},
        deriv (fun t => ψ.toFun ((coordSplit j).symm (z, t))) t) := by
    funext z
    have h_set : {t : ℝ | (z, t) ∈ e '' S} = {t : ℝ | e.symm (z, t) ∈ S} := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨x, hx, h_eq⟩
        have h3 : e x = (z, t) := h_eq
        have h4 : x = e.symm (z, t) := by rw [←h3] <;> simp
        rw [h4] at hx
        exact hx
      · intro h
        exact ⟨e.symm (z, t), h, by simp⟩
    have h_slice_meas : MeasurableSet {t : ℝ | (z, t) ∈ e '' S} := by
      have h : Measurable (fun t : ℝ => (z, t)) := by fun_prop
      exact h_image_meas.preimage h
    have h_c : ∫ t : ℝ, Set.indicator (e '' S) g (z, t) =
        ∫ t in {t | (z, t) ∈ e '' S}, g (z, t) := by
      have h_eq1 : (fun t : ℝ => Set.indicator (e '' S) g (z, t)) =
          Set.indicator {t | (z, t) ∈ e '' S} (fun t : ℝ => g (z, t)) := by
        funext t
        simp [Set.indicator_apply] <;> rfl
      rw [h_eq1, integral_indicator h_slice_meas] <;> rfl
    rw [h_c, h_set]
    apply congr_arg (fun (f : ℝ → ℝ) => ∫ t in {t | e.symm (z, t) ∈ S}, f t)
    funext t
    have h_diff : Differentiable ℝ ψ.toFun := ψ.smooth.differentiable (by simp)
    exact (sliced_deriv_eq_dirDeriv j z t h_diff).symm
  rw [h_eq_fun] at h_fubini_int
  exact h_fubini_int

/-- Directional variation in coordinate `j` is bounded by `μH[m](frontier S)`.

Proof: slice S along coordinate j, apply 1D lemma on each fiber,
use Fubini and projection Eilenberg inequality. -/
lemma directionalVariation_coord_le_hausdorff (hS : MeasurableSet S) :
    directionalVariation S (EuclideanSpace.single j 1) ≤ μH[m] (frontier S) := by
  by_cases htop : μH[m] (frontier S) = ⊤
  · rw [htop] <;> exact le_top
  · -- Case finite
    have hfin : μH[m] (frontier S) < ⊤ :=
      lt_top_iff_ne_top.mpr htop

    apply iSup_le
    intro ψ
    let split := coordSplit j
    let S_z (z : E m) : Set ℝ := {t | split.symm (z, t) ∈ S}
    let f_z (z : E m) : ℝ → ℝ := fun t => ψ.toFun (split.symm (z, t))
    -- Fubini
    have h_eq : ∫ x in S, fderiv ℝ ψ.toFun x (EuclideanSpace.single j 1) =
        ∫ z : E m, ∫ t in S_z z, deriv (f_z z) t :=
      fubini_dirDeriv hS j ψ
    -- Eilenberg
    have h_eil : ∫⁻ (z : E m), μH[0] (frontier S ∩ Set.preimage (projCoord j) {z}) ≤
        μH[m] (frontier S) :=
      general_eilenberg_d_eq_k (k := m) (f := projCoord j) (projCoord_lipschitz j)
    have h_slice : ∫⁻ (z : E m), μH[0] (frontier (S_z z)) ≤
        ∫⁻ (z : E m), μH[0] (frontier S ∩ Set.preimage (projCoord j) {z}) :=
      lintegral_mono (fun z => slice_hausdorff_le (S := S) (j := j) (z := z))
    have h_lint_top : ∫⁻ (z : E m), μH[0] (frontier (S_z z)) < ⊤ := by
      calc
        ∫⁻ (z : E m), μH[0] (frontier (S_z z))
          ≤ ∫⁻ (z : E m), μH[0] (frontier S ∩ Set.preimage (projCoord j) {z}) := h_slice
        _ ≤ μH[m] (frontier S) := h_eil
        _ < ⊤ := hfin
    -- Main integral bound: combine 1D lemma + Eilenberg
    let H : E m → ℝ := fun z => |∫ t in S_z z, deriv (f_z z) t|
    let g : E m → ENNReal := fun z =>
      μH[0] (frontier S ∩ Set.preimage (projCoord j) {z})
    have h_pointwise : ∀ᵐ (z : E m), ENNReal.ofReal (H z) ≤ g z := by
      filter_upwards with z
      have h1d : ENNReal.ofReal (H z) ≤ μH[0] (frontier (S_z z)) := by
        have hS_z : MeasurableSet (S_z z) := by
          have h_cont : Continuous (fun t : ℝ => (coordSplit j).symm (z, t)) :=
            slice_map_continuous j z
          exact hS.preimage h_cont.measurable
        have h_smooth : ContDiff ℝ ∞ (f_z z) := by
          have h1 : ContDiff ℝ ∞ (fun t : ℝ => (coordSplit j).symm (z, t)) :=
            slice_map_contDiff j z
          exact ψ.smooth.comp h1
        exact oneD_boundary_integral hS_z h_smooth
          (slice_map_compactSupport j z ψ.compact)
          (fun t => by simpa [f_z] using ψ.bound ((coordSplit j).symm (z, t)))
      have h_slice_z : μH[0] (frontier (S_z z)) ≤ g z :=
        slice_hausdorff_le (S := S) (j := j) (z := z)
      exact le_trans h1d h_slice_z
    have hH_nonneg : 0 ≤ᵐ[volume] H := by filter_upwards with z; exact abs_nonneg _
    have hH_meas : AEStronglyMeasurable H volume :=
      (sliced_deriv_integrable hS j ψ).abs.aestronglyMeasurable
    have h_main_eq : ∫ z, H z = (∫⁻ z, ENNReal.ofReal (H z)).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae hH_nonneg hH_meas
    have h_lint_mono : ∫⁻ z, ENNReal.ofReal (H z) ≤ ∫⁻ z, g z :=
      lintegral_mono_ae h_pointwise
    have h_abs_integral : |∫ z : E m, ∫ t in S_z z, deriv (f_z z) t| ≤ ∫ z, H z :=
      MeasureTheory.abs_integral_le_integral_abs
    have h_g_ne_top : (∫⁻ z, g z) ≠ ⊤ :=
      ne_top_of_le_ne_top htop h_eil
    have h_main_bound : |∫ z : E m, ∫ t in S_z z, deriv (f_z z) t| ≤
        (μH[m] (frontier S)).toReal := by
      calc
        |∫ z : E m, ∫ t in S_z z, deriv (f_z z) t|
          ≤ ∫ z, H z := h_abs_integral
        _ = (∫⁻ z, ENNReal.ofReal (H z)).toReal := h_main_eq
        _ ≤ (∫⁻ z, g z).toReal := ENNReal.toReal_mono h_g_ne_top h_lint_mono
        _ ≤ (μH[m] (frontier S)).toReal := ENNReal.toReal_mono htop h_eil
    rw [h_eq]
    exact ENNReal.ofReal_le_iff_le_toReal htop |>.mpr h_main_bound

end DirectionalBound

-- ============================================================================
-- Section 5: Perimeter bound
-- ============================================================================

section PerimeterBound

open Perimeter

variable {n : ℕ} {S : Set (E n)}

/-- Helper: `ENNReal.ofReal |∑ a_i| ≤ ∑ ENNReal.ofReal |a_i|`. -/
lemma ofReal_abs_sum_le {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ) :
    ENNReal.ofReal |∑ i ∈ s, f i| ≤ ∑ i ∈ s, ENNReal.ofReal |f i| := by
  have h1 : |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := Finset.abs_sum_le_sum_abs _ _
  have h2 : ENNReal.ofReal |∑ i ∈ s, f i| ≤ ENNReal.ofReal (∑ i ∈ s, |f i|) :=
    ENNReal.ofReal_le_ofReal h1
  have h3 : ENNReal.ofReal (∑ i ∈ s, |f i|) = ∑ i ∈ s, ENNReal.ofReal |f i| := by
    let g : α → ℝ := fun i => |f i|
    have hg : ∀ i, 0 ≤ g i := fun i => abs_nonneg _
    have h_main : ∀ (t : Finset α), ENNReal.ofReal (∑ i ∈ t, g i) = ∑ i ∈ t, ENNReal.ofReal (g i) := by
      intro t
      induction t using Finset.induction with
      | empty => simp
      | @insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ENNReal.ofReal_add (hg a) (Finset.sum_nonneg (fun i _ => hg i))]
        rw [ih]
    exact h_main s
  rw [h3] at h2
  exact h2

/-- Perimeter ≤ sum of directional variations in coordinate directions. -/
lemma perimeter_le_sum_directionalVariation :
    perimeter S ≤ ∑ j : Fin n, directionalVariation S (EuclideanSpace.single j 1) := by
  apply iSup_le
  intro φ
  have h_div : ∫ x in S, divergence φ.toFun x =
      ∑ j : Fin n, ∫ x in S, fderiv ℝ (fun y => φ.toFun y j) x (EuclideanSpace.single j 1) := by
    have h1 : divergence φ.toFun = fun x =>
        ∑ j : Fin n, fderiv ℝ (fun y => φ.toFun y j) x (EuclideanSpace.single j 1) := by
      funext x
      simp [divergence] <;> rfl
    rw [h1, integral_finsetSum] <;> simp <;> intro i
    let g_i : E n → ℝ := fun x =>
      fderiv ℝ (fun y => φ.toFun y i) x (EuclideanSpace.single i 1)
    have h2 : ContDiff ℝ ∞ (fun y : E n => φ.toFun y i) := by
      have h3 : ContDiff ℝ ∞ (fun y : E n => y i) := by
        let proj_i : E n →L[ℝ] ℝ :=
          { toFun := fun y => y i
            map_add' := by intro x y; simp
            map_smul' := by intro c x; simp }
        exact proj_i.contDiff
      exact h3.comp φ.smooth
    have hcont : Continuous g_i := by
      have h_fd_cont : Continuous (fderiv ℝ (fun y : E n => φ.toFun y i)) :=
        h2.continuous_fderiv (by norm_num)
      let eval_at : (E n →L[ℝ] ℝ) →L[ℝ] ℝ :=
        { toFun := fun l => l (EuclideanSpace.single i 1)
          map_add' := by intro l1 l2; simp
          map_smul' := by intro c l; simp }
      have h_eval : Continuous (fun (l : E n →L[ℝ] ℝ) => l (EuclideanSpace.single i 1)) :=
        eval_at.continuous
      exact h_eval.comp h_fd_cont
    have hsupp : Function.support g_i ⊆ tsupport φ.toFun := by
      intro x hx
      by_contra h
      have hUopen : IsOpen (tsupport φ.toFun)ᶜ := (isClosed_tsupport _).isOpen_compl
      have hxU : x ∈ (tsupport φ.toFun)ᶜ := h
      have h_loc : (fun y : E n => φ.toFun y i) =ᶠ[nhds x] (fun _ => 0) := by
        filter_upwards [hUopen.mem_nhds hxU] with y hy
        have h9 : φ.toFun y = 0 := by
          by_contra h10
          have h11 : y ∈ Function.support φ.toFun := by simpa [Function.mem_support] using h10
          have h12 : y ∈ closure (Function.support φ.toFun) := subset_closure h11
          exact hy h12
        rw [h9] <;> simp
      have h_const : HasFDerivAt (fun (_ : E n) => (0 : ℝ)) (0 : E n →L[ℝ] ℝ) x := by
        exact hasFDerivAt_const (c := (0 : ℝ)) x
      have h_final : HasFDerivAt (fun y : E n => φ.toFun y i) (0 : E n →L[ℝ] ℝ) x :=
        h_const.congr_of_eventuallyEq h_loc
      have h6 : fderiv ℝ (fun y : E n => φ.toFun y i) x = 0 := h_final.fderiv
      have h7 : g_i x = 0 := by
        simp only [g_i, h6, zero_apply]
      exact hx h7
    have hclosed_gi : IsClosed (tsupport g_i) := isClosed_tsupport _
    have hclosed_phi : IsClosed (tsupport φ.toFun) := isClosed_tsupport _
    have hcompact : HasCompactSupport g_i := by
      exact φ.compact.of_isClosed_subset hclosed_gi (closure_minimal hsupp hclosed_phi)
    exact hcont.integrable_of_hasCompactSupport hcompact
  have h_ennreal : ENNReal.ofReal |∫ x in S, divergence φ.toFun x| ≤
      ∑ j : Fin n, ENNReal.ofReal |∫ x in S, fderiv ℝ (fun y => φ.toFun y j) x (EuclideanSpace.single j 1)| := by
    rw [h_div]
    exact ofReal_abs_sum_le Finset.univ _
  have h_each : ∀ (j : Fin n),
      ENNReal.ofReal |∫ x in S, fderiv ℝ (fun y => φ.toFun y j) x (EuclideanSpace.single j 1)| ≤
      directionalVariation S (EuclideanSpace.single j 1) := by
    intro j
    let ψ_j : TestScalar :=
      { toFun := fun x => φ.toFun x j
        smooth := by
          have h2 : ContDiff ℝ ∞ (fun y : E n => y j) := by
            let proj_j : E n →L[ℝ] ℝ :=
              { toFun := fun y => y j
                map_add' := by intro x y; simp
                map_smul' := by intro c x; simp }
            exact proj_j.contDiff
          exact h2.comp φ.smooth
        compact := by
          have h1 : Function.support (fun x : E n => φ.toFun x j) ⊆ Function.support φ.toFun := by
            intro x hx
            have h2 : φ.toFun x j ≠ 0 := by simpa [Function.mem_support] using hx
            have h3 : φ.toFun x ≠ 0 := by
              intro h4
              rw [h4] at h2
              contradiction
            simpa [Function.mem_support] using h3
          have h_supp : tsupport (fun x : E n => φ.toFun x j) ⊆ tsupport φ.toFun :=
            closure_mono h1
          have h_closed : IsClosed (tsupport (fun x : E n => φ.toFun x j)) :=
            isClosed_tsupport _
          exact φ.compact.isCompact.of_isClosed_subset h_closed h_supp
        bound := by
          intro x
          have h6 : |φ.toFun x j| ≤ ‖φ.toFun x‖ := by
            have h7 : |φ.toFun x j| ^ 2 ≤ ∑ i : Fin n, |φ.toFun x i| ^ 2 := by
              have h_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ |φ.toFun x i| ^ 2 :=
                fun i _ => sq_nonneg _
              exact Finset.single_le_sum h_nonneg (Finset.mem_univ j)
            have h8 : ‖φ.toFun x‖ ^ 2 = ∑ i : Fin n, |φ.toFun x i| ^ 2 := by
              have h9 : ‖φ.toFun x‖ ^ 2 = inner ℝ (φ.toFun x) (φ.toFun x) := by
                rw [inner_self_eq_norm_sq_to_K] <;> norm_cast
              rw [h9, PiLp.inner_apply]
              apply Finset.sum_congr rfl
              intro i _
              simp [inner_self_eq_norm_sq_to_K] <;> ring
            have h10 : 0 ≤ |φ.toFun x j| := by positivity
            have h11 : 0 ≤ ‖φ.toFun x‖ := by positivity
            nlinarith
          exact h6.trans (φ.bound x) }
    have h9 : ENNReal.ofReal |∫ x in S, fderiv ℝ ψ_j.toFun x (EuclideanSpace.single j 1)| ≤
        directionalVariation S (EuclideanSpace.single j 1) :=
      le_iSup (fun (ψ : TestScalar) => ENNReal.ofReal |∫ x in S, fderiv ℝ ψ.toFun x (EuclideanSpace.single j 1)|) ψ_j
    simpa [ψ_j] using h9
  calc
    ENNReal.ofReal |∫ x in S, divergence φ.toFun x|
      ≤ ∑ j : Fin n, ENNReal.ofReal |∫ x in S, fderiv ℝ (fun y => φ.toFun y j) x (EuclideanSpace.single j 1)| := h_ennreal
    _ ≤ ∑ j : Fin n, directionalVariation S (EuclideanSpace.single j 1) :=
      Finset.sum_le_sum (fun i _ => h_each i)

/-- **Non-sharp perimeter bound.**
`P(S) ≤ n · μH[n-1](frontier S)`. -/
theorem perimeter_le_hausdorff (hn : 1 ≤ n) (hS : MeasurableSet S) :
    perimeter S ≤ (n : ENNReal) * μH[n - 1] (frontier S) := by
  have h1 : perimeter S ≤ ∑ j : Fin n, directionalVariation S (EuclideanSpace.single j 1) :=
    perimeter_le_sum_directionalVariation (S := S)
  have h2 : ∀ (j : Fin n), directionalVariation S (EuclideanSpace.single j 1) ≤
      μH[n - 1] (frontier S) := by
    intro j
    cases n with
    | zero => omega
    | succ n' =>
      simpa using directionalVariation_coord_le_hausdorff (hS := hS) (j := j)
  have h3 : ∑ j : Fin n, directionalVariation S (EuclideanSpace.single j 1) ≤
      (n : ENNReal) * μH[n - 1] (frontier S) := by
    calc
      ∑ j : Fin n, directionalVariation S (EuclideanSpace.single j 1)
        ≤ ∑ j : Fin n, μH[n - 1] (frontier S) := Finset.sum_le_sum (fun i _ => h2 i)
      _ = (n : ENNReal) * μH[n - 1] (frontier S) := by
        have h4 : ∑ j : Fin n, μH[n - 1] (frontier S) =
            (Finset.card (Finset.univ : Finset (Fin n))) • μH[n - 1] (frontier S) := by
          rw [Finset.sum_const] <;> rfl
        rw [h4]
        simp
        <;> ring
  exact le_trans h1 h3

/-- If `μHE[n-1](frontier S) < ∞`, then `perimeter S < ∞`. -/
theorem perimeter_finite_of_euclideanHausdorff_finite
    (hn : 1 ≤ n) (hS : MeasurableSet S)
    (hfin : μHE[n - 1] (frontier S) < ⊤) :
    perimeter S < ⊤ := by
  cases n with
  | zero =>
    exfalso
    linarith
  | succ n' =>
    have h_iff : μHE[n'] (frontier S) < ⊤ ↔ μH[n'] (frontier S) < ⊤ :=
      euclideanHausdorffMeasure_finite_iff (n := n'.succ) (d := n')
    have hfin' : μHE[n'] (frontier S) < ⊤ := by
      simpa [Nat.succ_eq_add_one] using hfin
    have h_main : μH[n'] (frontier S) < ⊤ := h_iff.mp hfin'
    have h1 : perimeter S ≤ (n'.succ : ENNReal) * μH[n'] (frontier S) := by
      simpa [Nat.succ_eq_add_one] using perimeter_le_hausdorff hn hS
    have h3 : (n'.succ : ENNReal) * μH[n'] (frontier S) < ⊤ :=
      ENNReal.mul_lt_top (by simp) h_main
    exact lt_of_le_of_lt h1 h3

end PerimeterBound

end Geometry
