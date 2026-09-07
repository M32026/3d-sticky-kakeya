import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.Eilenberg
import Mathlib.Tactic

/-!
# Multidimensional Eilenberg Inequality

Generalization of the 1D Eilenberg inequality to Lipschitz maps `f : X → E m`.

## Main results

- `eilenberg_inequality_multidim`: For `f : X → E m` Lipschitz with constant `L`
  and `d > 0`:
  `∫⁻ (y : E m), μH[d] (A ∩ f⁻¹{y}) ≤ L^m · μH[d + m] A`

- `projection_eilenberg_inequality`: For the coordinate projection
  `proj k : E(k+1) → E k` and `d_ambient > k`:
  `∫⁻ (y : E k), μH[d_ambient - k] (A ∩ (proj k)⁻¹{y}) ≤ μH[d_ambient] A`

## Proof strategy

Induction on `m`, iterating the 1D Eilenberg inequality from
`MyLeanRepo.Isoperimetric.Measure.Eilenberg`. At each step, factor
`f : X → E(k+1)` as `(proj k ∘ f, lastCoord k ∘ f)` and apply 1D Eilenberg
to the real-valued component on each fiber of the projected component.

The dependent-type induction avoids `isDefEq` timeouts by using a helper
lemma `eilenberg_helper` where `L^k` and `d+k` are moved into hypotheses
on separate variables `c : ENNReal` and `e : ℝ`.

## Whiteprint

Supports `eilenberg_multidim` and projection bounds in the coarea formula
and isoperimetric proof routes.
-/


open MeasureTheory Metric Set ENNReal Filter Classical
open scoped MeasureTheory

namespace Geometry
namespace EilenbergInequality

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
noncomputable def proj (m : ℕ) (z : E (m + 1)) : E m :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm (fun i : Fin m => z (Fin.castSucc i))

def lastCoord (m : ℕ) (z : E (m + 1)) : ℝ := z (Fin.last m)

noncomputable def eSplit (m : ℕ) : E (m + 1) ≃ᵐ E m × ℝ :=
  let e1 : E (m + 1) ≃ᵐ (Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm
  let e2 : (Fin (m + 1) → ℝ) ≃ᵐ (ℝ × (Fin m → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last m)
  let e3 : (ℝ × (Fin m → ℝ)) ≃ᵐ ((Fin m → ℝ) × ℝ) :=
    MeasurableEquiv.prodComm
  let e4 : (Fin m → ℝ) ≃ᵐ E m :=
    MeasurableEquiv.toLp 2 (Fin m → ℝ)
  let e4' : ((Fin m → ℝ) × ℝ) ≃ᵐ (E m × ℝ) :=
    e4.prodCongr (MeasurableEquiv.refl ℝ)
  e1.trans e2 |>.trans e3 |>.trans e4'

lemma eSplit_apply (m : ℕ) (z : E (m + 1)) :
    eSplit m z = (proj m z, lastCoord m z) := by
  have h1 : (eSplit m z).1 = proj m z := by
    ext j
    have h_eq1 : (eSplit m z).1 j = z (Fin.castSucc j) := by
      simp [eSplit, proj, MeasurableEquiv.toLp, MeasurableEquiv.piFinSuccAbove,
        MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr, EuclideanSpace.equiv] <;> rfl
    have h_eq2 : (proj m z) j = z (Fin.castSucc j) := by
      simp [proj, EuclideanSpace.equiv] <;> rfl
    rw [h_eq1, h_eq2]
  have h2 : (eSplit m z).2 = lastCoord m z := by
    simp [eSplit, lastCoord, MeasurableEquiv.toLp, MeasurableEquiv.piFinSuccAbove,
      MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr] <;> rfl
  exact Prod.ext h1 h2

lemma eSplit_measurePreserving (m : ℕ) :
    MeasurePreserving (eSplit m) volume volume := by
  let e1 : E (m + 1) ≃ᵐ (Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm
  let e2 : (Fin (m + 1) → ℝ) ≃ᵐ (ℝ × (Fin m → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last m)
  let e3 : (ℝ × (Fin m → ℝ)) ≃ᵐ ((Fin m → ℝ) × ℝ) :=
    MeasurableEquiv.prodComm
  let e4 : (Fin m → ℝ) ≃ᵐ E m :=
    MeasurableEquiv.toLp 2 (Fin m → ℝ)
  let e4' : ((Fin m → ℝ) × ℝ) ≃ᵐ (E m × ℝ) :=
    e4.prodCongr (MeasurableEquiv.refl ℝ)
  have h1 : MeasurePreserving e1 volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (ι := Fin (m + 1))
  have h2 : MeasurePreserving e2 volume volume :=
    volume_preserving_piFinSuccAbove (fun _ => ℝ) (Fin.last m)
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
  have hprod : MeasurePreserving e4' (volume.prod volume) (volume.prod volume) :=
    MeasurePreserving.prod h41 h42
  have hv : (volume : Measure ((Fin m → ℝ) × ℝ)) = volume.prod volume :=
    Measure.volume_eq_prod (Fin m → ℝ) ℝ
  have hv' : (volume : Measure (E m × ℝ)) = volume.prod volume :=
    Measure.volume_eq_prod (E m) ℝ
  have h4 : MeasurePreserving e4' volume volume := by
    simpa [hv, hv'] using hprod
  exact h4.comp (h3.comp (h2.comp h1))

lemma proj_lipschitz (m : ℕ) : LipschitzWith 1 (proj m) := by
  intro x y
  set z := x - y with hz
  set w := proj m z with hw
  have h1 : ‖w‖ ^ 2 = ∑ i : Fin m, |w i| ^ 2 := by
    have h11 : ‖w‖ ^ 2 = inner ℝ w w := (inner_self_eq_norm_sq_to_K w).symm
    rw [h11, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    have h12 : inner ℝ (w i) (w i) = |w i| ^ 2 := by
      simp [inner_self_eq_norm_sq_to_K] <;> ring
    exact h12
  have h2 : ‖z‖ ^ 2 = ∑ i : Fin (m + 1), |z i| ^ 2 := by
    have h21 : ‖z‖ ^ 2 = inner ℝ z z := (inner_self_eq_norm_sq_to_K z).symm
    rw [h21, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    have h22 : inner ℝ (z i) (z i) = |z i| ^ 2 := by
      simp [inner_self_eq_norm_sq_to_K] <;> ring
    exact h22
  have h_wi : ∀ i : Fin m, w i = z (Fin.castSucc i) := by
    intro i; simp [proj, EuclideanSpace.equiv] <;> rfl
  have h_eq_sum : ∑ i : Fin m, |w i| ^ 2 = ∑ i : Fin m, |z (Fin.castSucc i)| ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _; rw [h_wi i]
  have h_inj : Function.Injective (Fin.castSucc : Fin m → Fin (m + 1)) :=
    Fin.castSucc_injective m
  have h_injOn : Set.InjOn (Fin.castSucc) (↑(Finset.univ : Finset (Fin m))) :=
    fun x _ y _ h => h_inj h
  have h3 : ∑ i : Fin m, |z (Fin.castSucc i)| ^ 2 ≤ ∑ i : Fin (m + 1), |z i| ^ 2 := by
    have h_img : ∑ i : Fin m, |z (Fin.castSucc i)| ^ 2 =
        ∑ j ∈ Finset.image (Fin.castSucc) (Finset.univ), |z j| ^ 2 := by
      rw [Finset.sum_image h_injOn] <;> rfl
    rw [h_img]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j _; exact Finset.mem_univ j
    · intro j _ _; positivity
  have h4 : ‖w‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    calc
      ‖w‖ ^ 2 = ∑ i : Fin m, |w i| ^ 2 := h1
      _ = ∑ i : Fin m, |z (Fin.castSucc i)| ^ 2 := h_eq_sum
      _ ≤ ∑ i : Fin (m + 1), |z i| ^ 2 := h3
      _ = ‖z‖ ^ 2 := h2.symm
  have h5 : 0 ≤ ‖w‖ := by positivity
  have h6 : 0 ≤ ‖z‖ := by positivity
  have h_main : ‖w‖ ≤ ‖z‖ := by nlinarith
  have hlin : proj m (x - y) = proj m x - proj m y := by
    ext i; simp [proj] <;> rfl
  have h_main2 : ‖proj m x - proj m y‖ ≤ ‖x - y‖ := by
    have h1 : ‖proj m (x - y)‖ ≤ ‖x - y‖ := by simpa [hw, hz] using h_main
    rw [hlin] at h1
    exact h1
  have h' : edist (proj m x) (proj m y) = ENNReal.ofReal ‖proj m x - proj m y‖ := by
    simp [edist_dist, dist_eq_norm]
  have h'' : edist x y = ENNReal.ofReal ‖x - y‖ := by
    simp [edist_dist, dist_eq_norm]
  rw [h', h'']
  have h3 : ENNReal.ofReal ‖proj m x - proj m y‖ ≤ (1 : ENNReal) * ENNReal.ofReal ‖x - y‖ := by
    rw [one_mul]
    exact ENNReal.ofReal_le_ofReal h_main2
  exact h3

lemma lastCoord_lipschitz (m : ℕ) : LipschitzWith 1 (lastCoord m) := by
  intro x y
  have h : |(x - y) (Fin.last m)| ≤ ‖x - y‖ :=
    PiLp.norm_apply_le (x - y) (Fin.last m)
  have h' : edist (lastCoord m x) (lastCoord m y) = ENNReal.ofReal |(x - y) (Fin.last m)| := by
    simp [lastCoord, edist_dist, dist_eq_norm] <;> rfl
  have h'' : edist x y = ENNReal.ofReal ‖x - y‖ := by
    simp [edist_dist, dist_eq_norm]
  rw [h', h'']
  have h3 : ENNReal.ofReal |(x - y) (Fin.last m)| ≤ (1 : ENNReal) * ENNReal.ofReal ‖x - y‖ := by
    rw [one_mul]
    exact ENNReal.ofReal_le_ofReal h
  exact h3

/-- Base case. -/
lemma eilenberg_multidim_base {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {d : ℝ} (hd : 0 < d) {f : X → E 0} {A : Set X} {L : NNReal} (hf : LipschitzWith L f) :
    ∫⁻ (y : E 0), μH[d] (A ∩ f ⁻¹' {y}) ≤ (L : ENNReal)^0 * μH[d + 0] A := by
  have h_unique : ∀ (y z : E 0), y = z := by
    intro y z; ext i; fin_cases i
  have h1 : ∀ y, A ∩ f ⁻¹' {y} = A := by
    intro y
    have h2 : ∀ x, f x = y := fun x => h_unique (f x) y
    have h3 : f ⁻¹' {y} = Set.univ := by
      ext x; simp [h2 x]
    rw [h3]; simp
  have h5 : ∀ y, μH[d] (A ∩ f ⁻¹' {y}) = μH[d] A := fun y => by rw [h1 y]
  have h4 : ∫⁻ (y : E 0), μH[d] (A ∩ f ⁻¹' {y}) = μH[d] A := by
    rw [lintegral_congr h5]
    have h6 : ∫⁻ (_ : E 0), μH[d] A = μH[d] A * volume (Set.univ : Set (E 0)) :=
      lintegral_const (μH[d] A)
    rw [h6]
    have h7 : volume (Set.univ : Set (E 0)) = 1 := by
      let e : E 0 ≃ᵐ (Fin 0 → ℝ) := (MeasurableEquiv.toLp 2 (Fin 0 → ℝ)).symm
      have hmp : MeasurePreserving e volume volume :=
        EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (ι := Fin 0)
      have h9 : volume (Set.univ : Set (E 0)) = volume (Set.univ : Set (Fin 0 → ℝ)) := by
        have h10 : Measure.map e volume = volume := hmp.map_eq
        have h11 : volume (Set.univ : Set (Fin 0 → ℝ)) = volume (e ⁻¹' (Set.univ : Set (Fin 0 → ℝ))) := by
          rw [←h10, Measure.map_apply hmp.measurable (MeasurableSet.univ)]
        have h12 : e ⁻¹' (Set.univ : Set (Fin 0 → ℝ)) = Set.univ := by simp
        rw [h11, h12]
      rw [h9]
      have h13 : (volume : Measure (Fin 0 → ℝ)) = Measure.pi (fun (_ : Fin 0) => volume) := by
        simp [volume_pi]
      rw [h13]
      have h14 : Measure.pi (fun (_ : Fin 0) => volume) = Measure.dirac (default : Fin 0 → ℝ) := by
        ext s hs
        have h_sub : Subsingleton (Fin 0 → ℝ) := by infer_instance
        by_cases h : (default : Fin 0 → ℝ) ∈ s
        · have hs1 : s = Set.univ := by
            ext y
            have hy : y = (default : Fin 0 → ℝ) := Subsingleton.elim y (default : Fin 0 → ℝ)
            simp only [Set.mem_univ, iff_true]
            rw [hy]; exact h
          rw [hs1]
          simp [Measure.pi_empty_univ]
        · have hs2 : s = ∅ := by
            ext y
            have hy : y = (default : Fin 0 → ℝ) := Subsingleton.elim y (default : Fin 0 → ℝ)
            simp only [Set.mem_empty_iff_false, iff_false]
            rw [hy]; exact h
          rw [hs2] <;> simp
      rw [h14] <;> simp
    rw [h7] <;> ring
  rw [h4] <;> simp

/-- Step lemma (already proved to compile). -/
lemma eilenberg_multidim_step_X {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {d : ℝ} (hd : 0 < d) (k : ℕ)
    (ih : ∀ (g : X → E k) (B : Set X) (L' : NNReal), LipschitzWith L' g →
      ∫⁻ (y : E k), μH[d] (B ∩ g ⁻¹' {y}) ≤ (L' : ENNReal)^k * μH[d + k] B) :
    ∀ (g : X → E (k + 1)) (B : Set X) (L' : NNReal), LipschitzWith L' g →
      ∫⁻ (y : E (k + 1)), μH[d] (B ∩ g ⁻¹' {y}) ≤ (L' : ENNReal)^(k + 1) * μH[d + k + 1] B := by
  intro g B L' hg
  let g' : X → E k := proj k ∘ g
  let h : X → ℝ := lastCoord k ∘ g
  have hg' : LipschitzWith L' g' := by
    have hcomp : LipschitzWith (1 * L') g' := (proj_lipschitz k).comp hg
    have h1 : (1 * L') = L' := by simp
    rw [h1] at hcomp; exact hcomp
  have hh : LipschitzWith L' h := by
    have hcomp : LipschitzWith (1 * L') h := (lastCoord_lipschitz k).comp hg
    have h1 : (1 * L') = L' := by simp
    rw [h1] at hcomp; exact hcomp
  let e : E (k + 1) ≃ᵐ E k × ℝ := eSplit k
  let e' : E (k + 1) ≃ᵐ ℝ × E k := e.trans MeasurableEquiv.prodComm
  have hmp : MeasurePreserving e volume volume := eSplit_measurePreserving k
  have hmp_comm : MeasurePreserving (MeasurableEquiv.prodComm : E k × ℝ ≃ᵐ ℝ × E k) volume volume := by
    have hv1 : (volume : Measure (E k × ℝ)) = volume.prod volume := Measure.volume_eq_prod (E k) ℝ
    have hv2 : (volume : Measure (ℝ × E k)) = volume.prod volume := Measure.volume_eq_prod ℝ (E k)
    refine' ⟨MeasurableEquiv.prodComm.measurable_toFun, _⟩
    rw [hv1, hv2]
    exact Measure.measurePreserving_swap.map_eq
  have hmp' : MeasurePreserving e' volume volume := hmp_comm.comp hmp
  have hmp'_symm : MeasurePreserving e'.symm volume volume := by
    have h1 : Measure.map e'.symm (Measure.map e' volume) = Measure.map (e'.symm ∘ e') volume :=
      Measure.map_map e'.symm.measurable e'.measurable
    have h2 : e'.symm ∘ e' = id := by funext x; simp
    have h3 : Measure.map e'.symm volume = volume := by
      calc
        Measure.map e'.symm volume
          = Measure.map e'.symm (Measure.map e' volume) := by rw [hmp'.map_eq]
        _ = Measure.map (e'.symm ∘ e') volume := h1
        _ = Measure.map id volume := by rw [h2]
        _ = volume := by simp
    exact ⟨e'.symm.measurable, h3⟩
  let F : E (k + 1) → ENNReal := fun z => μH[d] (B ∩ g ⁻¹' {z})
  have h_step1 : ∫⁻ (t : ℝ), μH[d + k] (B ∩ h ⁻¹' {t}) ≤
      (L' : ENNReal) * μH[d + k + 1] B :=
    eilenberg_inequality (show 0 < d + k by linarith) hh
  have h_step2 : ∀ (t : ℝ), ∫⁻ (y : E k), μH[d] ((B ∩ h ⁻¹' {t}) ∩ g' ⁻¹' {y}) ≤
      (L' : ENNReal)^k * μH[d + k] (B ∩ h ⁻¹' {t}) := by
    intro t
    exact ih g' (B ∩ h ⁻¹' {t}) L' hg'
  have hfin : (L' : ENNReal)^k ≠ ⊤ := by
    have h2 : (L' : ENNReal)^k = ↑(L' ^ k) := by norm_cast
    rw [h2]
    exact ENNReal.coe_ne_top
  have h3 : ∫⁻ (t : ℝ), ∫⁻ (y : E k), μH[d] ((B ∩ h ⁻¹' {t}) ∩ g' ⁻¹' {y}) ≤
      (L' : ENNReal)^(k + 1) * μH[d + k + 1] B := by
    calc
      ∫⁻ (t : ℝ), ∫⁻ (y : E k), μH[d] ((B ∩ h ⁻¹' {t}) ∩ g' ⁻¹' {y})
        ≤ ∫⁻ (t : ℝ), (L' : ENNReal)^k * μH[d + k] (B ∩ h ⁻¹' {t}) :=
          lintegral_mono h_step2
      _ = (L' : ENNReal)^k * ∫⁻ (t : ℝ), μH[d + k] (B ∩ h ⁻¹' {t}) :=
          lintegral_const_mul' ((L' : ENNReal)^k) _ hfin
      _ ≤ (L' : ENNReal)^k * ((L' : ENNReal) * μH[d + k + 1] B) :=
          mul_le_mul_left' h_step1 _
      _ = (L' : ENNReal)^(k + 1) * μH[d + k + 1] B := by
          simp [pow_succ] <;> ring
  have h5 : ∀ (t : ℝ) (y : E k),
      B ∩ g ⁻¹' {e'.symm (t, y)} = (B ∩ h ⁻¹' {t}) ∩ g' ⁻¹' {y} := by
    intro t y
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    have h_eq : g x = e'.symm (t, y) ↔ g' x = y ∧ h x = t := by
      constructor
      · intro h6
        have h7 : e' (g x) = (t, y) := by
          rw [h6]; exact e'.apply_symm_apply (t, y)
        have h8 : e (g x) = (y, t) := by
          have h9 : e' (g x) = MeasurableEquiv.prodComm (e (g x)) := by rfl
          rw [h9] at h7
          have h10 : (e (g x)).2 = t ∧ (e (g x)).1 = y := by
            simpa [MeasurableEquiv.prodComm, Prod.swap] using h7
          exact Prod.ext h10.2 h10.1
        have h10 : g' x = y := by
          have h11 : (e (g x)).1 = y := by rw [h8]
          have h12 : (e (g x)).1 = g' x := by
            rw [eSplit_apply k (g x)] <;> rfl
          rw [h12] at h11; exact h11
        have h13 : h x = t := by
          have h14 : (e (g x)).2 = t := by rw [h8]
          have h15 : (e (g x)).2 = h x := by
            rw [eSplit_apply k (g x)] <;> rfl
          rw [h15] at h14; exact h14
        exact ⟨h10, h13⟩
      · rintro ⟨h10, h11⟩
        have h14 : e (g x) = (g' x, h x) := by
          rw [eSplit_apply k (g x)] <;> rfl
        have h15 : e (g x) = (y, t) := by
          rw [h14, h10, h11]
        have h16 : e' (g x) = (t, y) := by
          have h17 : e' (g x) = MeasurableEquiv.prodComm (e (g x)) := by rfl
          rw [h17, h15] <;> simp [MeasurableEquiv.prodComm, Prod.swap]
        exact e'.injective (by simpa using h16)
    constructor
    · rintro ⟨hx, h6⟩
      have ⟨h10, h11⟩ := h_eq.mp h6
      exact ⟨⟨hx, h11⟩, h10⟩
    · rintro ⟨⟨hx, h11⟩, h10⟩
      exact ⟨hx, h_eq.mpr ⟨h10, h11⟩⟩
  have h4 : ∫⁻ (z : E (k + 1)), F z = ∫⁻ (p : ℝ × E k), F (e'.symm p) :=
    hmp'_symm.lintegral_map_equiv F e'.symm
  rw [h4]
  let H : ℝ × E k → ENNReal := fun p => μH[d] ((B ∩ h ⁻¹' {p.1}) ∩ g' ⁻¹' {p.2})
  have h_eq : ∫⁻ (p : ℝ × E k), F (e'.symm p) = ∫⁻ (p : ℝ × E k), H p := by
    apply lintegral_congr
    intro p
    exact congr_arg (μH[d]) (h5 p.1 p.2)
  rw [h_eq]
  have hvol : (volume : Measure (ℝ × E k)) = volume.prod volume := Measure.volume_eq_prod ℝ (E k)
  have h6 : ∫⁻ (p : ℝ × E k), H p ≤ ∫⁻ (t : ℝ), ∫⁻ (y : E k), H (t, y) := by
    rw [hvol]
    exact lintegral_prod_le H
  have h_final : ∫⁻ (t : ℝ), ∫⁻ (y : E k), H (t, y) =
      ∫⁻ (t : ℝ), ∫⁻ (y : E k), μH[d] ((B ∩ h ⁻¹' {t}) ∩ g' ⁻¹' {y}) := by rfl
  calc
    ∫⁻ (p : ℝ × E k), H p
      ≤ ∫⁻ (t : ℝ), ∫⁻ (y : E k), H (t, y) := h6
    _ = ∫⁻ (t : ℝ), ∫⁻ (y : E k), μH[d] ((B ∩ h ⁻¹' {t}) ∩ g' ⁻¹' {y}) := h_final
    _ ≤ (L' : ENNReal)^(k + 1) * μH[d + k + 1] B := h3

/-- Helper induction with arithmetic moved to hypotheses. -/
lemma eilenberg_helper (d : ℝ) (hd : 0 < d) :
  ∀ (k : ℕ) (g : X → E k) (B : Set X) (L' : NNReal) (c : ENNReal) (e : ℝ),
    c = (L' : ENNReal)^k → e = d + k → LipschitzWith L' g →
    ∫⁻ (y : E k), μH[d] (B ∩ g ⁻¹' {y}) ≤ c * μH[e] B := by
  intro k
  induction k with
  | zero =>
    intro g B L' c e hc he hg
    have hc1 : c = 1 := by
      rw [hc] <;> simp
    have he1 : e = d := by
      rw [he] <;> ring
    rw [hc1, he1]
    have h := eilenberg_multidim_base (X := X) (d := d) hd (f := g) (A := B) (L := L') hg
    simpa using h
  | succ k ih =>
    intro g B L' c e hc he hg
    have hc2 : c = (L' : ENNReal) * (L' : ENNReal)^k := by
      rw [hc, pow_succ] <;> ring
    have he2 : e = (d + k) + 1 := by
      have h : e = d + (k + 1 : ℕ) := he
      simpa [add_assoc] using h
    let c' := (L' : ENNReal)^k
    let e' := d + k
    have h_ih' : ∀ (g0 : X → E k) (B0 : Set X) (L0 : NNReal), LipschitzWith L0 g0 →
        ∫⁻ (y : E k), μH[d] (B0 ∩ g0 ⁻¹' {y}) ≤ (L0 : ENNReal)^k * μH[e'] B0 := by
      intro g0 B0 L0 hL0
      exact ih g0 B0 L0 ((L0 : ENNReal)^k) e' rfl rfl hL0
    have h_step : ∀ (g0 : X → E (k + 1)) (B0 : Set X), LipschitzWith L' g0 →
        ∫⁻ (y : E (k + 1)), μH[d] (B0 ∩ g0 ⁻¹' {y}) ≤ (L' : ENNReal)^(k + 1) * μH[d + k + 1] B0 :=
      fun g0 B0 hL0 => eilenberg_multidim_step_X hd k h_ih' g0 B0 L' hL0
    have h_main := h_step g B hg
    rw [hc2, he2]
    have h_pow : (L' : ENNReal)^(k + 1) = (L' : ENNReal) * (L' : ENNReal)^k := by
      rw [pow_succ] <;> ring
    rw [h_pow] at h_main
    exact h_main

/-- **Multidimensional Eilenberg inequality** by induction on `m`.

For a Lipschitz map `f : X → E m` with constant `L` and `d > 0`:
`∫⁻ (y : E m), μH[d] (A ∩ f ⁻¹' {y}) ≤ L^m * μH[d + m] A`.

The induction avoids dependent-type `isDefEq` timeouts by moving
`d + k` and `L^k` into hypotheses of the helper lemma. -/
theorem eilenberg_inequality_multidim
    {m : ℕ} {f : X → E m} {A : Set X} {d : ℝ} (hd : 0 < d)
    {L : NNReal} (hf : LipschitzWith L f) :
    ∫⁻ (y : E m), μH[d] (A ∩ f ⁻¹' {y}) ≤ (L : ENNReal)^m * μH[d + m] A := by
  have h : ∀ (k : ℕ) (g : X → E k) (B : Set X) (L' : NNReal) (c : ENNReal) (e : ℝ),
      c = (L' : ENNReal)^k → e = d + k → LipschitzWith L' g →
      ∫⁻ (y : E k), μH[d] (B ∩ g ⁻¹' {y}) ≤ c * μH[e] B :=
    eilenberg_helper (X := X) d hd
  have h2 := h m
  have h3 := h2 f A L
  have h4 := h3 ((L : ENNReal)^m) (d + m)
  exact h4 rfl rfl hf

/-- **Projection Eilenberg inequality** for the coordinate projection
`proj k : E(k+1) → E k`.

For `A ⊆ E(k+1)` and ambient dimension `d_ambient > k`:
`∫⁻ (y : E k), μH[d_ambient - k] (A ∩ (proj k)⁻¹{y}) ≤ μH[d_ambient] A`.

The boundary case `d_ambient = k` (fiber dimension 0) requires the
Banach indicatrix theorem (`eilenberg_inequality_d0`). -/
lemma projection_eilenberg_inequality
    {k : ℕ} {A : Set (E (k + 1))} {d_ambient : ℝ} (h : (k : ℝ) < d_ambient) :
    ∫⁻ (y : E k), μH[d_ambient - k] (A ∩ (proj k) ⁻¹' {y}) ≤ μH[d_ambient] A := by
  set d : ℝ := d_ambient - k with hd_def
  have h_pos : 0 < d := by linarith
  have h_eq : d + (k : ℝ) = d_ambient := by
    simp [hd_def] <;> ring
  have h_main : ∫⁻ (y : E k), μH[d] (A ∩ (proj k) ⁻¹' {y}) ≤
      (1 : ENNReal)^k * μH[d + k] A :=
    eilenberg_inequality_multidim (hd := h_pos) (hf := proj_lipschitz k)
  have h_one : (1 : ENNReal)^k = 1 := by simp
  rw [h_one, one_mul, h_eq] at h_main
  exact h_main

end EilenbergInequality
end Geometry
