import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConditionalFactorStates
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConvexThickeningGrowth
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.ScaleInterpolation
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FiberBalancing

/-!
# Helper lemmas for the branch-product telescoping argument

This module provides scale-chain invariants and volume ratio facts for
the finite dividing-scales Frostman proof (paper lemma `lemmasubmultD`).

## Main results

* `IsScaleOrdered`: adjacent factors share boundary scales.
* `relativeScale_prod_eq`: product of all relative scales = `delta`.
* `prefix_scale_product`: telescoping prefix product.
* `dilatedTubeCarrier_volume_ratio`: volume ratio cancels the dilation factor.
* `cthickening_dilatedTubeCarrier_le`: thickening growth of a dilated tube carrier.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

namespace FrostmanConditionalFactorState

variable {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
  depth (A := A) (C := C) F hdelta_le_one}

/-- Helper: `get` of appended list when index is in the left part. -/
private lemma get_append_left {α : Type _} {l1 l2 : List α} {i : ℕ}
    (h : i < l1.length) (h2 : i < (l1 ++ l2).length) :
    (l1 ++ l2).get ⟨i, h2⟩ = l1.get ⟨i, h⟩ := by
  induction l1 generalizing i with
  | nil => contradiction
  | cons a t ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      have h' : i' < t.length := by
        simpa [List.length_cons] using h
      have h2' : i' < (t ++ l2).length := by
        simpa [List.length_cons] using h2
      simpa [List.get] using ih h' h2'

/-- Helper: `get` of appended list when index is in the right part. -/
private lemma get_append_right {α : Type _} {l1 l2 : List α} {i : ℕ}
    (h : l1.length ≤ i) (h2 : i < (l1 ++ l2).length) (h3 : i - l1.length < l2.length) :
    (l1 ++ l2).get ⟨i, h2⟩ = l2.get ⟨i - l1.length, h3⟩ := by
  induction l1 generalizing i with
  | nil =>
    simpa using rfl
  | cons a t ih =>
    cases i with
    | zero => contradiction
    | succ i' =>
      have h' : t.length ≤ i' := by simpa [List.length_cons] using h
      have h2' : i' < (t ++ l2).length := by simpa [List.length_cons] using h2
      have h3' : i' - t.length < l2.length := by simpa [List.length_cons] using h3
      simpa [List.get] using ih h' h2' h3'

/-- Helper: the element right after the first list in an append. -/
private lemma get_after_append {α : Type _} (l1 : List α) (a : α) (l2 : List α)
    (h : l1.length < (l1 ++ a :: l2).length) :
    (l1 ++ a :: l2).get ⟨l1.length, h⟩ = a := by
  induction l1 with
  | nil => simp [List.get]
  | cons x t ih =>
    simp [List.get] at * <;> exact ih (by simp)

/--
Adjacent factors in the list share their boundary scale:
`P_k.coarseScale = P_{k+1}.fineScale`.

This holds for every state reachable from `root` by repeated `split`.
-/
def IsScaleOrdered {level : ℕ}
    (S : FrostmanConditionalFactorState U level) : Prop :=
  ∀ (k : Fin level),
    (S.factors.get (Fin.cast S.length_eq.symm k.castSucc)).coarseScale =
    (S.factors.get (Fin.cast S.length_eq.symm k.succ)).fineScale

/-- The root state (one factor) is trivially scale ordered. -/
lemma root_isScaleOrdered (hdelta : 0 < delta) :
    (root (U := U) hdelta).IsScaleOrdered := by
  intro k
  exfalso
  exact Fin.elim0 k

/--
The product of relative scales over all factors equals `delta`.

This is a restatement of `relativeScale_prod` using `Fin`-indexed product.
-/
lemma relativeScale_prod_eq
    {level : ℕ} (S : FrostmanConditionalFactorState U level) :
    ∏ k : Fin S.factors.length, (S.factors.get k).relativeScale = delta := by
  have h_map : List.ofFn (fun k : Fin S.factors.length => (S.factors.get k).relativeScale) =
      S.factors.map FrostmanConditionalFactorScope.relativeScale :=
    List.ofFn_getElem_eq_map S.factors FrostmanConditionalFactorScope.relativeScale
  have h : (S.factors.map FrostmanConditionalFactorScope.relativeScale).prod = delta :=
    S.relativeScale_prod
  rw [← h_map, List.prod_ofFn] at h
  exact h

/--
Telescoping prefix product: for `0 < J ≤ level + 1`,
the product of the first `J` relative scales equals
`P_0.fineScale / P_{J-1}.coarseScale`.

Since `relativeScale = fineScale / coarseScale` and adjacent factors satisfy
`coarseScale_k = fineScale_{k+1}`, the product telescopes.
-/
lemma prefix_scale_product
    {level : ℕ} (S : FrostmanConditionalFactorState U level)
    (hdelta : 0 < delta)
    (J : ℕ) (hJ_pos : 0 < J) (hJ : J ≤ level + 1)
    (hchain : ∀ (k : Fin level), k.val < J - 1 →
      (S.factors.get (Fin.cast S.length_eq.symm k.castSucc)).coarseScale =
      (S.factors.get (Fin.cast S.length_eq.symm k.succ)).fineScale) :
    ((S.factors.take J).map FrostmanConditionalFactorScope.relativeScale).prod =
    (S.factors.get ⟨0, by rw [S.length_eq] <;> omega⟩).fineScale /
    (S.factors.get ⟨J - 1, by rw [S.length_eq] <;> omega⟩).coarseScale := by
  induction J with
  | zero =>
    exfalso
    linarith
  | succ J ih =>
    by_cases hJ0 : J = 0
    · -- Base case J = 0, so succ J = 1
      subst hJ0
      have h_len_pos : 0 < S.factors.length := by rw [S.length_eq] <;> omega
      have h_general : ∀ (l : List (FrostmanConditionalFactorScope U)) (hn : 0 < l.length),
          l.take 1 = [l.get ⟨0, hn⟩] := by
        intro l hn
        cases l with
        | nil => contradiction
        | cons a t =>
          simp [List.take, List.get] <;> rfl
      have h_take1 : S.factors.take 1 = [S.factors.get ⟨0, h_len_pos⟩] :=
        h_general S.factors h_len_pos
      rw [h_take1]
      simp [FrostmanConditionalFactorScope.relativeScale] <;> field_simp <;> ring
    · -- Inductive step J > 0
      have hJ_pos' : 0 < J := by omega
      have hJ_le : J ≤ level + 1 := by omega
      have hchain' : ∀ (k : Fin level), k.val < J - 1 →
          (S.factors.get (Fin.cast S.length_eq.symm k.castSucc)).coarseScale =
          (S.factors.get (Fin.cast S.length_eq.symm k.succ)).fineScale := by
        intro k hk
        exact hchain k (by omega)
      set P_J := S.factors.get ⟨J, by rw [S.length_eq] <;> omega⟩ with hPJ
      set P_0 := S.factors.get ⟨0, by rw [S.length_eq] <;> omega⟩ with hP0
      set P_prev := S.factors.get ⟨J - 1, by rw [S.length_eq] <;> omega⟩ with hPprev
      have h_len : J < S.factors.length := by rw [S.length_eq] <;> omega
      have h_general : ∀ (l : List (FrostmanConditionalFactorScope U)) (n : ℕ) (hn : n < l.length),
          l.take (n + 1) = l.take n ++ [l.get ⟨n, hn⟩] := by
        intro l
        induction l with
        | nil =>
          intro n hn
          contradiction
        | cons a l ih =>
          intro n hn
          cases n with
          | zero =>
            simp [List.take, List.get] <;> rfl
          | succ n' =>
            have h_n'_lt : n' < l.length := by
              simpa [List.length_cons] using hn
            have h_ih' : l.take (n' + 1) = l.take n' ++ [l.get ⟨n', h_n'_lt⟩] :=
              ih n' h_n'_lt
            have h_goal : (a :: l).take (n' + 2) =
                (a :: l).take (n' + 1) ++ [(a :: l).get ⟨n' + 1, hn⟩] := by
              dsimp only [List.take]
              rw [h_ih'] <;> rfl
            exact h_goal
      have h_take_succ : S.factors.take (J + 1) = S.factors.take J ++ [P_J] := by
        have h := h_general S.factors J h_len
        simpa [hPJ] using h
      rw [h_take_succ, List.map_append, List.prod_append]
      simp only [List.map_singleton, List.prod_singleton]
      rw [ih hJ_pos' hJ_le hchain']
      have hstep : P_prev.coarseScale = P_J.fineScale := by
        have h2 : J ≤ level := by linarith
        have h3 : 1 ≤ J := by linarith
        have h_idx : J - 1 < level := by omega
        let k : Fin level := ⟨J - 1, h_idx⟩
        have h_k_lt : k.val < J := by
          dsimp only [k]
          omega
        have h := hchain k h_k_lt
        have h_cast1 : (Fin.cast S.length_eq.symm k.castSucc) =
            (⟨J - 1, by rw [S.length_eq] <;> omega⟩ : Fin S.factors.length) := by
          apply Fin.ext
          simp [k, Fin.castSucc, Fin.cast]
          <;> rfl
        have h_cast2 : (Fin.cast S.length_eq.symm k.succ) =
            (⟨J, h_len⟩ : Fin S.factors.length) := by
          apply Fin.ext
          simp [k, Fin.succ, Fin.cast]
          <;> omega
        rw [h_cast1, h_cast2] at h
        exact h
      have h_fineJ_pos : 0 < P_J.fineScale := P_J.fineScale_pos hdelta
      have h_fine0_pos : 0 < P_0.fineScale := P_0.fineScale_pos hdelta
      have h_coarseJ_pos : 0 < P_J.coarseScale := P_J.coarseScale_pos hdelta
      simp only [FrostmanConditionalFactorScope.relativeScale]
      rw [hstep]
      have h_fineJ_ne_zero : P_J.fineScale ≠ 0 := h_fineJ_pos.ne'
      have h_fine0_ne_zero : P_0.fineScale ≠ 0 := h_fine0_pos.ne'
      have h_coarseJ_ne_zero : P_J.coarseScale ≠ 0 := h_coarseJ_pos.ne'
      calc
        (P_0.fineScale / P_J.fineScale) * (P_J.fineScale / P_J.coarseScale)
          = (P_0.fineScale * P_J.fineScale) / (P_J.fineScale * P_J.coarseScale) := by
            rw [div_mul_div_comm]
        _ = P_0.fineScale / P_J.coarseScale := by
          rw [mul_comm P_J.fineScale P_J.coarseScale]
          <;> field_simp [h_fineJ_ne_zero, h_fine0_ne_zero, h_coarseJ_ne_zero] <;> ring

end FrostmanConditionalFactorState

-- =====================================================================
-- Volume ratio facts
-- =====================================================================

/--
`deltaTubeVolume` is monotone: `0 ≤ r ≤ s` implies
`deltaTubeVolume r ≤ deltaTubeVolume s`.
-/
lemma deltaTubeVolume_monotone' {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    Kakeya.deltaTubeVolume r ≤ Kakeya.deltaTubeVolume s :=
  RandomTranslation.deltaTubeVolume_monotone hrs hr

/--
Upper bound for the volume ratio: if `0 < r ≤ s ≤ A * r` and `s ≤ 1`, then
`deltaTubeVolume s ≤ C(A) * deltaTubeVolume r`,
where `C(A) = ((π + 8π/3 * A) / 2) * A^2`.

Note: the exact ratio is **not** `(s/r)^3` because `deltaTubeVolume(r)`
is the volume of a radius-r thickened unit segment, which scales as
`πr² + (4/3)πr³` (quadratic leading term).
-/
lemma deltaTubeVolume_ratio_upper {r s A : ℝ}
    (hr_pos : 0 < r) (hs_pos : 0 < s)
    (hrs : r ≤ s) (hs_le_Ar : s ≤ A * r)
    (hA_pos : 0 < A) (hs_one : s ≤ 1) :
    Kakeya.deltaTubeVolume s ≤
      ENNReal.ofReal (((Real.pi + 8 / 3 * Real.pi * A) / 2) * A ^ 2) *
      Kakeya.deltaTubeVolume r :=
  RandomTranslation.deltaTubeVolume_ratio_bound
    hr_pos hs_pos hrs hs_le_Ar hA_pos hs_one

/--
Lower bound: `deltaTubeVolume r ≥ ENNReal.ofReal (2 * r^2)` for `r > 0`.
-/
lemma deltaTubeVolume_lower {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (2 * r ^ 2) ≤ Kakeya.deltaTubeVolume r :=
  RandomTranslation.deltaTubeVolume_lower_bound hr

/--
Upper bound: `deltaTubeVolume r ≤ ENNReal.ofReal ((π + 8π/3) * r^2)` for `0 < r ≤ 1`.
-/
lemma deltaTubeVolume_upper {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Kakeya.deltaTubeVolume r ≤
      ENNReal.ofReal ((Real.pi + 8 / 3 * Real.pi) * r ^ 2) :=
  RandomTranslation.deltaTubeVolume_upper_bound hr hr1

/--
The volume ratio of dilated tube carriers cancels the dilation factor:

`volume(dilatedTubeCarrier A T_r) / volume(dilatedTubeCarrier A T_s)
 = deltaTubeVolume r / deltaTubeVolume s`

for `A ≠ 0` and positive radii `r, s ≤ 1`.
-/
lemma dilatedTubeCarrier_volume_ratio
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hr1 : r ≤ 1) (hs1 : s ≤ 1)
    {A : ℝ} (hA : A ≠ 0)
    (T_r : Kakeya.DeltaTube r) (T_s : Kakeya.DeltaTube s) :
    volume (dilatedTubeCarrier A T_r) /
      volume (dilatedTubeCarrier A T_s) =
    Kakeya.deltaTubeVolume r / Kakeya.deltaTubeVolume s := by
  have hVr : volume (dilatedTubeCarrier A T_r) =
      ENNReal.ofReal (|A| ^ 3) * Kakeya.deltaTubeVolume r :=
    volume_dilatedTubeCarrier hA T_r
  have hVs : volume (dilatedTubeCarrier A T_s) =
      ENNReal.ofReal (|A| ^ 3) * Kakeya.deltaTubeVolume s :=
    volume_dilatedTubeCarrier hA T_s
  rw [hVr, hVs]
  have hA3_pos : 0 < ENNReal.ofReal (|A| ^ 3) := by
    have h : 0 < |A| ^ 3 := pow_pos (abs_pos.mpr hA) 3
    exact ENNReal.ofReal_pos.mpr h
  have hA3_ne_zero : ENNReal.ofReal (|A| ^ 3) ≠ 0 := hA3_pos.ne'
  have hA3_ne_top : ENNReal.ofReal (|A| ^ 3) ≠ ⊤ := ENNReal.ofReal_ne_top
  exact ENNReal.mul_div_mul_left
    (Kakeya.deltaTubeVolume r) (Kakeya.deltaTubeVolume s)
    hA3_ne_zero hA3_ne_top

/--
Thickening growth bound when `K` is a dilated tube carrier at scale `s`.

Since `K` contains the original radius-`s` tube (for `A ≥ 1`),
`volume(cthickening r K) ≤ (1 + 2*r/s)^3 * volume(K)`.
-/
lemma cthickening_dilatedTubeCarrier_le
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {A : ℝ} (hA : 1 ≤ A)
    (T : Kakeya.DeltaTube s) :
    volume (Metric.cthickening r (dilatedTubeCarrier A T)) ≤
      ENNReal.ofReal ((1 + 2 * r / s) ^ 3) *
        volume (dilatedTubeCarrier A T) := by
  have hTK : T.carrier ⊆ dilatedTubeCarrier A T :=
    GeometricLemmas.self_dilated_containment A hA T
  exact volume_cthickening_le_of_tube_subset
    (GeometricLemmas.dilatedTubeCarrier_convex T)
    hs hr T hTK

/--
Simplified thickening bound for `s ≤ r`:
`volume(cthickening r K) ≤ 27 * (r/s)^3 * volume(K)`.
-/
lemma cthickening_dilatedTubeCarrier_le'
    {r s : ℝ} (hs : 0 < s) (hs_le_r : s ≤ r)
    {A : ℝ} (hA : 1 ≤ A)
    (T : Kakeya.DeltaTube s) :
    volume (Metric.cthickening r (dilatedTubeCarrier A T)) ≤
      ENNReal.ofReal (27 * (r / s) ^ 3) *
        volume (dilatedTubeCarrier A T) := by
  have hTK : T.carrier ⊆ dilatedTubeCarrier A T :=
    GeometricLemmas.self_dilated_containment A hA T
  exact volume_cthickening_le_of_tube_subset'
    (GeometricLemmas.dilatedTubeCarrier_convex T)
    hs hs_le_r T hTK

end Kakeya.Streamlined
