import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.FinitePerimeterFromHausdorff
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpLemma
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

/-!
# Hausdorff Lower Density at True Reduced Boundary

Geometric slicing lemma: if a set S ⊂ ball(0,1) is L¹-close to a half-space H,
then μHE[n-1](frontier S ∩ ball(0,1)) is close to ω_{n-1}.

## Main result

`geometric_lower_bound_coord`: if S is L¹-close to `{x | x j < 0}` in the unit ball,
then `μHE[m](frontier S ∩ ball 0 1) ≥ (1-δ) * volume(ball(0:E m)1)`.
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory
open Geometry.Perimeter

namespace Geometry.StructureTheorem

variable {n : ℕ}

/-- Construct a linear isometry `φ : E n ≃ₗᵢ[ℝ] E n` mapping a unit vector `ν`
to a standard basis vector `e_j` for some `j : Fin n`. -/
lemma exists_isometry_map_to_basis {n : ℕ} (hn : 0 < n) (ν : E n) (hν_unit : ‖ν‖ = 1) :
    ∃ (j : Fin n) (φ : E n ≃ₗᵢ[ℝ] E n), φ ν = EuclideanSpace.single j 1 := by
  let s : Finset (E n) := {ν}
  have hs_orthonormal : Orthonormal ℝ ((↑) : s → E n) := by
    constructor
    · intro i
      have h_eq : (i : E n) = ν := Finset.mem_singleton.mp i.prop
      rw [h_eq]; exact hν_unit
    · intro i j hne
      have h_i_eq : (i : E n) = ν := Finset.mem_singleton.mp i.prop
      have h_j_eq : (j : E n) = ν := Finset.mem_singleton.mp j.prop
      have h_eq : i = j := by apply Subtype.ext; rw [h_i_eq, h_j_eq]
      exact False.elim (hne h_eq)
  rcases Orthonormal.exists_orthonormalBasis_extension hs_orthonormal with ⟨u, b, hsu, hb_eq⟩
  have h_card : Fintype.card {x // x ∈ u} = n := by
    have h1 : Module.finrank ℝ (E n) = Nat.card {x // x ∈ u} :=
      Module.finrank_eq_nat_card_basis b.toBasis
    have h1' : Nat.card {x // x ∈ u} = Fintype.card {x // x ∈ u} := by exact Nat.card_eq_fintype_card
    have h2 : Module.finrank ℝ (E n) = n := by simpa [E, Fintype.card_fin] using finrank_fintype_fun
    omega
  have h_ν_in_u : ν ∈ u := by
    have h3 : ({ν} : Finset (E n)) ⊆ u := hsu
    exact h3 (by simp)
  let i₀ : {x // x ∈ u} := ⟨ν, h_ν_in_u⟩
  have h_i0_val : (i₀ : E n) = ν := by rfl
  have h_b_i0 : b i₀ = ν := by
    have h : b i₀ = (i₀ : E n) := by rw [hb_eq] <;> rfl
    rw [h, h_i0_val]
  let e0 : {x // x ∈ u} ≃ Fin (Fintype.card {x // x ∈ u}) := Fintype.equivFin _
  let e : {x // x ∈ u} ≃ Fin n := e0.trans (Equiv.cast (by rw [h_card]))
  let b' : OrthonormalBasis (Fin n) ℝ (E n) := b.reindex e
  let j₀ : Fin n := e i₀
  have h_b'_j0 : b' j₀ = ν := by
    rw [OrthonormalBasis.reindex_apply] <;> simp [j₀, h_b_i0] <;> rfl
  let φ : E n ≃ₗᵢ[ℝ] E n := b'.repr
  have hφ_ν : φ ν = EuclideanSpace.single j₀ 1 := by
    have h : φ (b' j₀) = EuclideanSpace.single j₀ 1 := OrthonormalBasis.repr_self b' j₀
    rw [h_b'_j0] at h; exact h
  exact ⟨j₀, φ, hφ_ν⟩

/-- **Frontier crossing lemma**: if a connected set C intersects both S and Sᶜ,
then it intersects `frontier S`. -/
lemma frontier_crosses_connected {S : Set (E n)} {C : Set (E n)}
    (hC : IsConnected C) (hxE : (C ∩ S).Nonempty) (hyE : (C ∩ Sᶜ).Nonempty) :
    (C ∩ frontier S).Nonempty := by
  by_contra h
  have h_empty : C ∩ frontier S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have h1 : C ⊆ interior S ∪ interior (Sᶜ) := by
    intro z hz
    by_cases h2 : z ∈ S
    · have h3 : z ∈ interior S := by
        by_contra h4
        have h5 : z ∈ frontier S := (mem_frontier_iff_notMem_interior h2).mpr h4
        have h6 : z ∈ C ∩ frontier S := ⟨hz, h5⟩
        rw [h_empty] at h6
        exact h6
      exact Or.inl h3
    · have h3 : z ∈ interior (Sᶜ) := by
        by_contra h4
        have h51 : z ∈ closure S := by
          have h_eq : closure S = (interior (Sᶜ))ᶜ := closure_eq_compl_interior_compl
          rw [h_eq]; exact h4
        have h53 : z ∈ closure (Sᶜ) := subset_closure h2
        have h5 : z ∈ frontier S := by
          rw [frontier_eq_closure_inter_closure]; exact ⟨h51, h53⟩
        have h6 : z ∈ C ∩ frontier S := ⟨hz, h5⟩
        rw [h_empty] at h6
        exact h6
      exact Or.inr h3
  have h_disj : Disjoint (interior S) (interior (Sᶜ)) := by
    rw [Set.disjoint_left]; intro x hx1 hx2
    exact (interior_subset hx2) (interior_subset hx1)
  have h_preconn : IsPreconnected C := hC.2
  have h_main : C ⊆ interior S ∨ C ⊆ interior (Sᶜ) :=
    h_preconn.subset_or_subset isOpen_interior isOpen_interior h_disj h1
  rcases hxE with ⟨x, hxC, hxS⟩
  rcases hyE with ⟨y, hyC, hyScompl⟩
  cases h_main with
  | inl h_sub => exact hyScompl (interior_subset (h_sub hyC))
  | inr h_sub => exact (interior_subset (h_sub hxC)) hxS

/-- Norm identity: dropping coordinate j preserves the Pythagorean decomposition. -/
lemma norm_sq_projCoord_add_coord {m : ℕ} (j : Fin (m + 1)) (x : E (m + 1)) :
    ‖x‖ ^ 2 = ‖projCoord j x‖ ^ 2 + |x j| ^ 2 := by
  let P := projCoord j
  have h1 : ‖x‖ ^ 2 = ∑ k : Fin (m + 1), |x k| ^ 2 := by
    have h11 : ‖x‖ ^ 2 = inner ℝ x x := by
      rw [inner_self_eq_norm_sq_to_K] <;> norm_cast
    rw [h11, PiLp.inner_apply]
    <;> simp [inner_self_eq_norm_sq_to_K] <;> ring
  have h2 : ‖P x‖ ^ 2 = ∑ i : Fin m, |(P x) i| ^ 2 := by
    have h21 : ‖P x‖ ^ 2 = inner ℝ (P x) (P x) := by
      rw [inner_self_eq_norm_sq_to_K] <;> norm_cast
    rw [h21, PiLp.inner_apply]
    <;> simp [inner_self_eq_norm_sq_to_K] <;> ring
  have h3 : ∑ i : Fin m, |(P x) i| ^ 2 = ∑ i : Fin m, |x (Fin.succAbove j i)| ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [projCoord_apply j x i]
  have h4 : ∑ k : Fin (m + 1), |x k| ^ 2 =
      |x j| ^ 2 + ∑ i : Fin m, |x (Fin.succAbove j i)| ^ 2 := by
    exact Fin.sum_univ_succAbove (fun i => |x i| ^ 2) j
  rw [h1, h4, h2, h3] <;> ring

variable {m : ℕ}

/-- **Slice interval**: the set of `t` such that `(coordSplit j).symm (z, t)` lies
in the unit ball is `Ioo (-R) R` where `R = sqrt(1 - ‖z‖²)`. -/
lemma slice_interval (j : Fin (m + 1)) (z : E m) (hz : ‖z‖ < 1) :
    {t : ℝ | (coordSplit j).symm (z, t) ∈ ball (0 : E (m + 1)) 1} =
      Ioo (-(Real.sqrt (1 - ‖z‖^2))) (Real.sqrt (1 - ‖z‖^2)) := by
  let R : ℝ := Real.sqrt (1 - ‖z‖^2)
  have h_pos : 0 < 1 - ‖z‖^2 := by nlinarith [norm_nonneg z]
  have hR_pos : 0 < R := Real.sqrt_pos.mpr h_pos
  have h_main : ∀ (t : ℝ), (coordSplit j).symm (z, t) ∈ ball (0 : E (m + 1)) 1 ↔ |t| < R := by
    intro t
    let x : E (m + 1) := (coordSplit j).symm (z, t)
    have h1 : projCoord j x = z := by simp [x, projCoord] <;> rfl
    have h2 : x j = t := by
      have h21 : (coordSplit j x).2 = x j := coordSplit_apply j x
      have h22 : (coordSplit j x).2 = t := by simp [x] <;> rfl
      rw [h21] at h22; exact h22
    have h3 : ‖x‖ ^ 2 = ‖z‖ ^ 2 + |t| ^ 2 := by
      rw [norm_sq_projCoord_add_coord j x, h1, h2] <;> ring
    have h4 : ‖x‖ < 1 ↔ |t| < R := by
      have h5 : ‖x‖ ^ 2 < 1 ↔ |t| ^ 2 < 1 - ‖z‖ ^ 2 := by
        rw [h3] <;> constructor <;> intro h <;> nlinarith
      have h6 : ‖x‖ < 1 ↔ ‖x‖ ^ 2 < 1 := by
        constructor <;> intro h <;> nlinarith [norm_nonneg x]
      have h7 : |t| < R ↔ |t| ^ 2 < 1 - ‖z‖ ^ 2 := by
        constructor
        · intro h8
          have h9 : |t| ^ 2 < R ^ 2 := by nlinarith [abs_nonneg t]
          have h10 : R ^ 2 = 1 - ‖z‖ ^ 2 := by rw [Real.sq_sqrt (by linarith)]
          nlinarith
        · intro h8
          have h9 : R ^ 2 = 1 - ‖z‖ ^ 2 := by rw [Real.sq_sqrt (by linarith)]
          have h10 : |t| ^ 2 < R ^ 2 := by nlinarith
          have h11 : |t| < R := by nlinarith [abs_nonneg t, Real.sqrt_nonneg (1 - ‖z‖^2)]
          exact h11
      rw [h6, h5, h7]
    simpa [mem_ball, dist_zero_right] using h4
  ext t
  have h9 := h_main t
  simp only [Set.mem_setOf_eq, Set.mem_Ioo] at *
  have h10 : |t| < R ↔ -R < t ∧ t < R := by
    rw [abs_lt] <;> constructor <;> intro h <;> exact ⟨by linarith, by linarith⟩
  rw [h10] at h9
  exact h9

/-- **Slice volume**: for `‖z‖ < 1`, the 1D volume of the intersection of the unit
ball with the line at projection `z` is `2 * Real.sqrt (1 - ‖z‖^2)`. -/
lemma slice_volume (j : Fin (m + 1)) (z : E m) (hznorm : ‖z‖ < 1) :
    volume {t : ℝ | (coordSplit j).symm (z, t) ∈ ball (0 : E (m + 1)) 1}
      = ENNReal.ofReal (2 * Real.sqrt (1 - ‖z‖^2)) := by
  let R : ℝ := Real.sqrt (1 - ‖z‖^2)
  have h_pos : 0 < 1 - ‖z‖^2 := by nlinarith [norm_nonneg z]
  have hR_pos : 0 < R := Real.sqrt_pos.mpr h_pos
  rw [slice_interval j z hznorm]
  have h_vol : volume (Ioo (-R) R) = ENNReal.ofReal (R - (-R)) := by
    rw [Real.volume_Ioo] <;> simp [hR_pos] <;> ring_nf <;> norm_cast
  rw [h_vol]
  have h9 : R - (-R) = 2 * R := by ring
  rw [h9] <;> rfl

/-- **Half-slice volume**: for `‖z‖ < 1`, the volume of negative `t` in the
slice is `Real.sqrt (1 - ‖z‖^2)`. -/
lemma slice_negative_volume (j : Fin (m + 1)) (z : E m) (hznorm : ‖z‖ < 1) :
    volume {t : ℝ | (coordSplit j).symm (z, t) ∈ ball (0 : E (m + 1)) 1 ∧ t < 0}
      = ENNReal.ofReal (Real.sqrt (1 - ‖z‖^2)) := by
  let R : ℝ := Real.sqrt (1 - ‖z‖^2)
  have h_pos : 0 < 1 - ‖z‖^2 := by nlinarith [norm_nonneg z]
  have hR_pos : 0 < R := Real.sqrt_pos.mpr h_pos
  have h_main : ∀ (t : ℝ), (coordSplit j).symm (z, t) ∈ ball (0 : E (m + 1)) 1 ↔ |t| < R := by
    intro t
    let x : E (m + 1) := (coordSplit j).symm (z, t)
    have h1 : projCoord j x = z := by simp [x, projCoord] <;> rfl
    have h2 : x j = t := by
      have h21 : (coordSplit j x).2 = x j := coordSplit_apply j x
      have h22 : (coordSplit j x).2 = t := by simp [x] <;> rfl
      rw [h21] at h22; exact h22
    have h3 : ‖x‖ ^ 2 = ‖z‖ ^ 2 + |t| ^ 2 := by
      rw [norm_sq_projCoord_add_coord j x, h1, h2] <;> ring
    have h4 : ‖x‖ < 1 ↔ |t| < R := by
      have h5 : ‖x‖ ^ 2 < 1 ↔ |t| ^ 2 < 1 - ‖z‖ ^ 2 := by
        rw [h3] <;> constructor <;> intro h <;> nlinarith
      have h6 : ‖x‖ < 1 ↔ ‖x‖ ^ 2 < 1 := by
        constructor <;> intro h <;> nlinarith [norm_nonneg x]
      have h7 : |t| < R ↔ |t| ^ 2 < 1 - ‖z‖ ^ 2 := by
        constructor
        · intro h8
          have h9 : |t| ^ 2 < R ^ 2 := by nlinarith [abs_nonneg t]
          have h10 : R ^ 2 = 1 - ‖z‖ ^ 2 := by rw [Real.sq_sqrt (by linarith)]
          nlinarith
        · intro h8
          have h9 : R ^ 2 = 1 - ‖z‖ ^ 2 := by rw [Real.sq_sqrt (by linarith)]
          have h10 : |t| ^ 2 < R ^ 2 := by nlinarith
          have h11 : |t| < R := by nlinarith [abs_nonneg t, Real.sqrt_nonneg (1 - ‖z‖^2)]
          exact h11
      rw [h6, h5, h7]
    simpa [mem_ball, dist_zero_right] using h4
  have hI_eq : {t : ℝ | (coordSplit j).symm (z, t) ∈ ball (0 : E (m + 1)) 1 ∧ t < 0} = Ioo (-R) 0 := by
    ext t
    have h9 := h_main t
    simp only [Set.mem_setOf_eq, Set.mem_Ioo] at *
    have h10 : |t| < R ↔ -R < t ∧ t < R := by
      rw [abs_lt] <;> constructor <;> intro h <;> exact ⟨by linarith, by linarith⟩
    constructor
    · rintro ⟨hball, hneg⟩
      have h11 := (h10.mp (h9.mp hball))
      exact ⟨h11.1, by linarith⟩
    · rintro ⟨h1, h2⟩
      have h12 : |t| < R := h10.mpr ⟨h1, by linarith⟩
      exact ⟨h9.mpr h12, by linarith⟩
  rw [hI_eq]
  have h_vol : volume (Ioo (-R) 0) = ENNReal.ofReal (0 - (-R)) := by
    rw [Real.volume_Ioo] <;> simp [hR_pos] <;> ring_nf <;> norm_cast
  rw [h_vol]
  have h9 : 0 - (-R) = R := by ring
  rw [h9] <;> rfl

/-- **Lipschitz projection bound**: the Lebesgue volume of the projection
`projCoord j '' A` is at most the `m`-dimensional Euclidean Hausdorff
measure of `A`. -/
lemma projCoord_volume_le_hausdorff (j : Fin (m + 1)) (A : Set (E (m + 1))) :
    volume (projCoord j '' A) ≤ μHE[m] A := by
  have h_lip : LipschitzWith 1 (projCoord j) := projCoord_lipschitz j
  have h1 : μHE[m] (projCoord j '' A) ≤ (1 : ENNReal)^m * μHE[m] A := by
    let c : ENNReal := (volume : Measure (E m)).addHaarScalarFactor (MeasureTheory.Measure.hausdorffMeasure m)
    have hY : (μHE[m] : Measure (E m)) = c • μH[↑m] := MeasureTheory.Measure.euclideanHausdorffMeasure_def m
    have hX : (μHE[m] : Measure (E (m + 1))) = c • μH[↑m] := MeasureTheory.Measure.euclideanHausdorffMeasure_def m
    have h2 : μH[↑m] (projCoord j '' A) ≤ (1 : ENNReal)^(↑m : ℝ) * μH[↑m] A :=
      h_lip.hausdorffMeasure_image_le (by positivity) A
    have hpow : (1 : ENNReal)^(↑m : ℝ) = (1 : ENNReal)^m := by simp
    rw [hpow] at h2
    have h3 : μHE[m] (projCoord j '' A) = c * μH[↑m] (projCoord j '' A) := by rw [hY] <;> rfl
    have h4 : μHE[m] A = c * μH[↑m] A := by rw [hX] <;> rfl
    rw [h3, h4]
    have h5 : c * μH[↑m] (projCoord j '' A) ≤ c * ((1 : ENNReal)^m * μH[↑m] A) :=
      mul_le_mul_left' h2 c
    have h6 : c * ((1 : ENNReal)^m * μH[↑m] A) = (1 : ENNReal)^m * (c * μH[↑m] A) := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    exact le_trans h5 h6.le
  have h2 : (1 : ENNReal)^m = 1 := by simp
  rw [h2] at h1
  have h3 : μHE[m] (projCoord j '' A) ≤ μHE[m] A := by simpa using h1
  have h4 : (μHE[m] : Measure (E m)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume m
  have h5 : μHE[m] (projCoord j '' A) = volume (projCoord j '' A) := by
    rw [h4] <;> rfl
  rw [h5] at h3
  exact h3

/-- **Geometric lower bound (coordinate version)**: if S is L¹-close to the
half-space `{x | x j < 0}` in the unit ball, then the (n-1)-dimensional Hausdorff
measure of `frontier S ∩ ball 0 1` is close to `ω_{n-1}`. -/
lemma geometric_lower_bound_coord (m : ℕ) (j : Fin (m + 1)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (ε : ℝ), 0 < ε ∧ ∀ (S : Set (E (m + 1))), MeasurableSet S →
      (volume (symmDiff S {x | x j < 0} ∩ ball (0 : E (m + 1)) 1) < ENNReal.ofReal ε →
       μHE[m] (frontier S ∩ ball (0 : E (m + 1)) 1) ≥
         ENNReal.ofReal (1 - δ) * volume (ball (0 : E m) 1)) := by
  let ω : ENNReal := volume (ball (0 : E m) 1)
  have hω_pos : 0 < ω := by
    apply measure_ball_pos
    exact zero_lt_one
  have hω_lt_top : ω < ⊤ := measure_ball_lt_top
  let H : Set (E (m + 1)) := {x | x j < 0}
  have hH_meas : MeasurableSet H := by
    have h_cont : Continuous (fun x : E (m + 1) => x j) := by fun_prop
    exact (isOpen_lt h_cont continuous_const).measurableSet
  -- If δ ≥ 1, then (1-δ : ENNReal) = 0, so conclusion is trivial
  by_cases hδ_big : δ ≥ 1
  · exact ⟨1, by norm_num, fun _ => by
      have h1 : ENNReal.ofReal (1 - δ) = 0 := by
        simp [ENNReal.ofReal_eq_zero] <;> linarith
      have h_triv : ENNReal.ofReal (1 - δ) * ω = 0 := by rw [h1] <;> ring
      rw [h_triv] <;> simp⟩
  · -- Now 0 < δ < 1
    have hδ_lt_one : δ < 1 := by linarith
    let η : ℝ := δ / (4 * (m + 1))
    have hη_pos : 0 < η := by positivity
    have hη_lt_one : η < 1 := by
      have h1 : (m : ℝ) ≥ 0 := by positivity
      have h2 : η ≤ δ / 4 := by
        dsimp only [η]
        have h3 : 4 * ((m : ℝ) + 1) ≥ 4 := by linarith
        exact div_le_div_of_nonneg_left hδ.le (by norm_num) h3
      have h4 : δ / 4 < 1 / 4 := div_lt_div_of_pos_right hδ_lt_one (by norm_num)
      linarith
    have h_η_real : (1 - η) ^ m > 1 - δ / 2 := by
      have h_bernoulli : ∀ k : ℕ, (1 - η) ^ k ≥ 1 - (k : ℝ) * η := by
        intro k
        induction k with
        | zero => norm_num
        | succ k ih =>
          have h_nonneg : 0 ≤ 1 - η := by linarith
          have h_step : (1 - η) ^ (k + 1) ≥ 1 - ((k : ℝ) + 1) * η := by
            calc (1 - η) ^ (k + 1)
              = (1 - η) * (1 - η) ^ k := by ring
            _ ≥ (1 - η) * (1 - (k : ℝ) * η) := by
              exact mul_le_mul_of_nonneg_left ih h_nonneg
            _ = 1 - ((k : ℝ) + 1) * η + (k : ℝ) * η ^ 2 := by ring
            _ ≥ 1 - ((k : ℝ) + 1) * η := by
              have h5 : 0 ≤ (k : ℝ) * η ^ 2 := by positivity
              linarith
          simpa [Nat.cast_add, Nat.cast_one] using h_step
      have h2 : (m : ℝ) * η < δ / 2 := by
        dsimp only [η]
        have h_pos2 : 0 < (m : ℝ) + 1 := by positivity
        have h3 : (m : ℝ) / (4 * ((m : ℝ) + 1)) < 1 / 2 := by
          have h4 : (m : ℝ) < 2 * ((m : ℝ) + 1) := by linarith
          have h5 : 0 < 4 * ((m : ℝ) + 1) := by positivity
          calc (m : ℝ) / (4 * ((m : ℝ) + 1))
            < (2 * ((m : ℝ) + 1)) / (4 * ((m : ℝ) + 1)) := div_lt_div_of_pos_right h4 h5
          _ = 1 / 2 := by field_simp [h5.ne'] <;> ring
        have h6 : (m : ℝ) * (δ / (4 * ((m : ℝ) + 1))) = δ * ((m : ℝ) / (4 * ((m : ℝ) + 1))) := by ring
        rw [h6]
        have h7 : δ * ((m : ℝ) / (4 * ((m : ℝ) + 1))) < δ * (1 / 2) :=
          mul_lt_mul_of_pos_left h3 hδ
        have h8 : δ * (1 / 2) = δ / 2 := by ring
        rw [h8] at h7
        exact h7
      have h3 : (1 - η) ^ m ≥ 1 - (m : ℝ) * η := h_bernoulli m
      linarith
    have h_η_bound : (ENNReal.ofReal (1 - η)) ^ m * ω > ENNReal.ofReal (1 - δ / 2) * ω := by
      have h6 : (ENNReal.ofReal (1 - η)) ^ m = ENNReal.ofReal ((1 - η) ^ m) := by
        have h_nonneg : 0 ≤ 1 - η := by linarith
        exact (ENNReal.ofReal_pow h_nonneg m).symm
      rw [h6]
      have h7 : ENNReal.ofReal ((1 - η) ^ m) > ENNReal.ofReal (1 - δ / 2) := by
        have h71 : (1 - η) ^ m > 1 - δ / 2 := h_η_real
        have h72 : 0 ≤ 1 - δ / 2 := by linarith
        have h73 : 0 ≤ (1 - η) ^ m := by positivity
        have h_iff : ENNReal.ofReal (1 - δ / 2) < ENNReal.ofReal ((1 - η) ^ m) ↔ (1 - δ / 2) < (1 - η) ^ m :=
          ENNReal.ofReal_lt_ofReal_iff_of_nonneg h72
        exact h_iff.mpr (by linarith)
      have h_mul : ENNReal.ofReal ((1 - η) ^ m) * ω > ENNReal.ofReal (1 - δ / 2) * ω := by
        have h_ne_zero : ω ≠ 0 := hω_pos.ne'
        have h_ne_top : ω ≠ ⊤ := hω_lt_top.ne
        have h_lt : ENNReal.ofReal (1 - δ / 2) < ENNReal.ofReal ((1 - η) ^ m) := h7
        have h : ω * ENNReal.ofReal (1 - δ / 2) < ω * ENNReal.ofReal ((1 - η) ^ m) :=
          ENNReal.mul_lt_mul_right h_ne_zero h_ne_top h_lt
        simpa [mul_comm] using h
      exact h_mul
    set l_min : ℝ := Real.sqrt (2 * η - η^2) with hl_min_def
    have h2η_pos : 0 < 2 * η - η^2 := by nlinarith
    have hl_min_pos : 0 < l_min := Real.sqrt_pos.mpr h2η_pos
    -- Choose ε small enough
    let target : ENNReal := ENNReal.ofReal (δ / 2) * ω
    have htarget_pos : 0 < target := by
      have h1 : 0 < ENNReal.ofReal (δ / 2) := by positivity
      have h : 0 < ENNReal.ofReal (δ / 2) * ω := ENNReal.mul_pos h1.ne' hω_pos.ne'
      simpa [target] using h
    have htarget_lt_top : target < ⊤ := by
      apply ENNReal.mul_lt_top
      · exact ENNReal.ofReal_lt_top
      · exact hω_lt_top
    have htarget_toReal_pos : 0 < target.toReal := by
      rw [ENNReal.toReal_pos_iff]
      exact ⟨htarget_pos, htarget_lt_top⟩
    let ε : ℝ := (target.toReal / 2) * l_min
    have hε_pos : 0 < ε := by
      have h1 : 0 < target.toReal / 2 := by linarith [htarget_toReal_pos]
      exact mul_pos h1 hl_min_pos
    have hε_bound : ENNReal.ofReal (ε / l_min) < target := by
      have h9 : ε / l_min = target.toReal / 2 := by
        field_simp [hl_min_pos.ne'] <;> ring
      rw [h9]
      have h11 : ENNReal.ofReal (target.toReal / 2) < ENNReal.ofReal target.toReal := by
        have h111 : target.toReal / 2 < target.toReal := by linarith [htarget_toReal_pos]
        have h112 : 0 ≤ target.toReal / 2 := by linarith
        have h_iff : ENNReal.ofReal (target.toReal / 2) < ENNReal.ofReal target.toReal ↔ target.toReal / 2 < target.toReal :=
          ENNReal.ofReal_lt_ofReal_iff_of_nonneg h112
        exact h_iff.mpr h111
      have h12 : ENNReal.ofReal target.toReal = target :=
        ENNReal.ofReal_toReal htarget_lt_top.ne
      rw [h12] at h11
      exact h11
    refine' ⟨ε, hε_pos, _⟩
    intro S hS
    intro h_close
    let split := coordSplit j
    let S_z : E m → Set ℝ := fun z => {t | split.symm (z, t) ∈ S}
    let H_z : E m → Set ℝ := fun _ => {t | t < 0}
    let I_z : E m → Set ℝ := fun z => {t | split.symm (z, t) ∈ ball (0 : E (m + 1)) 1}
    let δ_vol : E m → ENNReal := fun z => volume (symmDiff (S_z z) (H_z z) ∩ I_z z)
    let Good : Set (E m) := {z | volume (S_z z ∩ I_z z) > 0 ∧ volume (I_z z \ S_z z) > 0}
    -- Fubini: total excess = ∫ δ_vol
    let A : Set (E m × ℝ) := (split.symm) ⁻¹' (symmDiff S H ∩ ball (0 : E (m + 1)) 1)
    have h_set_meas : MeasurableSet (symmDiff S H ∩ ball (0 : E (m + 1)) 1) := by
      have h1 : MeasurableSet S := hS
      have h2 : MeasurableSet H := hH_meas
      have h3 : MeasurableSet (ball (0 : E (m + 1)) 1) := isOpen_ball.measurableSet
      have h4 : MeasurableSet (symmDiff S H) := by
        simp [symmDiff, h1, h2] <;> fun_prop
      exact h4.inter h3
    have hA_meas : MeasurableSet A := by
      apply MeasurableSet.preimage
      · exact h_set_meas
      · exact split.symm.measurable
    have hmp_symm : MeasurePreserving split.symm volume volume :=
      (coordSplit_measurePreserving j).symm
    have h1_vol : volume (symmDiff S H ∩ ball (0 : E (m + 1)) 1) = volume A :=
      (hmp_symm.measure_preimage h_set_meas.nullMeasurableSet).symm
    have h2_fub : volume A = ∫⁻ (z : E m), volume {t : ℝ | (z, t) ∈ A} := by
      let g : E m × ℝ → ENNReal := Set.indicator A 1
      have hg_meas : Measurable g := measurable_const.indicator hA_meas
      let g' : E m → ℝ → ENNReal := fun z t => g (z, t)
      have h3 : ∫⁻ (z : E m), ∫⁻ (t : ℝ), g' z t = ∫⁻ (p : E m × ℝ), g p :=
        MeasureTheory.lintegral_lintegral hg_meas.aemeasurable
      have h_volA : ∫⁻ (p : E m × ℝ), g p = volume A := by
        have h : ∫⁻ (p : E m × ℝ), g p = 1 * volume A :=
          MeasureTheory.lintegral_indicator_const₀ hA_meas.nullMeasurableSet 1
        rw [h, one_mul]
      have h_inner : ∀ (z : E m), (∫⁻ (t : ℝ), g' z t) = volume {t : ℝ | (z, t) ∈ A} := by
        intro z
        let B : Set ℝ := {t : ℝ | (z, t) ∈ A}
        have hB_meas : MeasurableSet B := by
          exact hA_meas.preimage (show Measurable (fun t : ℝ => (z, t)) from by fun_prop)
        have h_eq1 : g' z = Set.indicator B 1 := by
          funext t
          have h_iff : (z, t) ∈ A ↔ t ∈ B := by simp [B] <;> rfl
          classical
          by_cases h : t ∈ B
          · have hA : (z, t) ∈ A := h_iff.mpr h
            simp [g', g, Set.indicator_apply, hA, h] <;> rfl
          · have hA : (z, t) ∉ A := h_iff.not.mp h
            simp [g', g, Set.indicator_apply, hA, h] <;> rfl
        rw [h_eq1]
        have h2 : ∫⁻ (t : ℝ), Set.indicator B 1 t = 1 * volume B :=
          MeasureTheory.lintegral_indicator_const₀ hB_meas.nullMeasurableSet 1
        rw [h2, one_mul]
      have h4 : ∫⁻ (z : E m), ∫⁻ (t : ℝ), g' z t = ∫⁻ (z : E m), volume {t : ℝ | (z, t) ∈ A} := by
        congr with z
        exact h_inner z
      rw [←h4, h3, h_volA]
    have h_fubini : volume (symmDiff S H ∩ ball (0 : E (m + 1)) 1) = ∫⁻ z, δ_vol z := by
      rw [h1_vol, h2_fub]
      congr with z
      have h_set_eq : {t : ℝ | (z, t) ∈ A} = symmDiff (S_z z) (H_z z) ∩ I_z z := by
        ext t
        have h_coord : (split.symm (z, t)) j = t := by
          have h1 : (coordSplit j (split.symm (z, t))).2 = t := by
            rw [MeasurableEquiv.apply_symm_apply] <;> rfl
          have h2 : (coordSplit j (split.symm (z, t))).2 = (split.symm (z, t)) j :=
            coordSplit_apply j (split.symm (z, t))
          rw [h2] at h1
          exact h1
        have h1 : (z, t) ∈ A ↔ split.symm (z, t) ∈ symmDiff S H ∩ ball (0 : E (m + 1)) 1 :=
          Iff.rfl
        rw [Set.mem_setOf_eq, h1]
        have h3 : split.symm (z, t) ∈ S ↔ t ∈ S_z z := by simp [S_z] <;> rfl
        have h4 : split.symm (z, t) ∈ H ↔ t ∈ H_z z := by
          simp [H, H_z, h_coord] <;> rfl
        have h5 : split.symm (z, t) ∈ ball (0 : E (m + 1)) 1 ↔ t ∈ I_z z := by simp [I_z] <;> rfl
        have h6 : split.symm (z, t) ∈ symmDiff S H ∩ ball (0 : E (m + 1)) 1 ↔
            t ∈ symmDiff (S_z z) (H_z z) ∩ I_z z := by
          constructor
          · rintro ⟨hSD, hball⟩
            have hI : t ∈ I_z z := h5.mp hball
            cases hSD with
            | inl hSD =>
              exact ⟨Or.inl ⟨h3.mp hSD.1, h4.not.mp hSD.2⟩, hI⟩
            | inr hSD =>
              exact ⟨Or.inr ⟨h4.mp hSD.1, h3.not.mp hSD.2⟩, hI⟩
          · rintro ⟨hSD, hI⟩
            have hball : split.symm (z, t) ∈ ball (0 : E (m + 1)) 1 := h5.mpr hI
            cases hSD with
            | inl hSD =>
              exact ⟨Or.inl ⟨h3.mpr hSD.1, h4.not.mpr hSD.2⟩, hball⟩
            | inr hSD =>
              exact ⟨Or.inr ⟨h4.mpr hSD.1, h3.not.mpr hSD.2⟩, hball⟩
        exact h6
      rw [h_set_eq]
    rw [h_fubini] at h_close
    -- δ_vol is measurable
    let f : E m × ℝ → ENNReal := Set.indicator A 1
    have hf_meas : Measurable f := measurable_const.indicator hA_meas
    have hδ_meas : Measurable (fun z : E m => ∫⁻ (t : ℝ), f (z, t)) :=
      Measurable.lintegral_prod_right' hf_meas
    have hδ_eq : (fun z : E m => ∫⁻ (t : ℝ), f (z, t)) = δ_vol := by
      funext z
      let B : Set ℝ := {t : ℝ | (z, t) ∈ A}
      have hB_meas : MeasurableSet B := hA_meas.preimage (by fun_prop)
      have h_eq1 : (fun (t : ℝ) => f (z, t)) = Set.indicator B 1 := by
        funext t
        have h_iff : (z, t) ∈ A ↔ t ∈ B := by simp [B] <;> rfl
        classical
        by_cases h : t ∈ B
        · have hA : (z, t) ∈ A := h_iff.mpr h
          simp [f, Set.indicator_apply, hA, h] <;> rfl
        · have hA : (z, t) ∉ A := h_iff.not.mp h
          simp [f, Set.indicator_apply, hA, h] <;> rfl
      have h : ∫⁻ (t : ℝ), f (z, t) = volume B := by
        rw [h_eq1]
        have h2 : ∫⁻ (t : ℝ), Set.indicator B 1 t = 1 * volume B :=
          MeasureTheory.lintegral_indicator_const₀ hB_meas.nullMeasurableSet 1
        rw [h2] <;> ring
      have h_set_eq : B = symmDiff (S_z z) (H_z z) ∩ I_z z := by
        ext t
        have h_coord : (split.symm (z, t)) j = t := by
          have h1 : (coordSplit j (split.symm (z, t))).2 = t := by
            rw [MeasurableEquiv.apply_symm_apply] <;> rfl
          have h2 : (coordSplit j (split.symm (z, t))).2 = (split.symm (z, t)) j :=
            coordSplit_apply j (split.symm (z, t))
          rw [h2] at h1
          exact h1
        have h1 : t ∈ B ↔ split.symm (z, t) ∈ symmDiff S H ∩ ball (0 : E (m + 1)) 1 :=
          Iff.rfl
        rw [h1]
        have h3 : split.symm (z, t) ∈ S ↔ t ∈ S_z z := by simp [S_z] <;> rfl
        have h4 : split.symm (z, t) ∈ H ↔ t ∈ H_z z := by
          simp [H, H_z, h_coord] <;> rfl
        have h5 : split.symm (z, t) ∈ ball (0 : E (m + 1)) 1 ↔ t ∈ I_z z := by simp [I_z] <;> rfl
        have h6 : split.symm (z, t) ∈ symmDiff S H ∩ ball (0 : E (m + 1)) 1 ↔
            t ∈ symmDiff (S_z z) (H_z z) ∩ I_z z := by
          constructor
          · rintro ⟨hSD, hball⟩
            have hI : t ∈ I_z z := h5.mp hball
            cases hSD with
            | inl hSD =>
              exact ⟨Or.inl ⟨h3.mp hSD.1, h4.not.mp hSD.2⟩, hI⟩
            | inr hSD =>
              exact ⟨Or.inr ⟨h4.mp hSD.1, h3.not.mp hSD.2⟩, hI⟩
          · rintro ⟨hSD, hI⟩
            have hball : split.symm (z, t) ∈ ball (0 : E (m + 1)) 1 := h5.mpr hI
            cases hSD with
            | inl hSD =>
              exact ⟨Or.inl ⟨h3.mpr hSD.1, h4.not.mpr hSD.2⟩, hball⟩
            | inr hSD =>
              exact ⟨Or.inr ⟨h4.mpr hSD.1, h3.not.mpr hSD.2⟩, hball⟩
        exact h6
      rw [h, h_set_eq]
    have hδ_vol_meas : Measurable δ_vol := by
      rw [← hδ_eq] <;> exact hδ_meas
    -- If z ∈ ball(0,1-η) and δ_vol z < l_min, then z ∈ Good
    have h_good_if_small : ∀ z, ‖z‖ ≤ 1 - η → δ_vol z < ENNReal.ofReal l_min → z ∈ Good := by
      intro z hz_norm h_small
      have hz_lt_one : ‖z‖ < 1 := by linarith
      let R := Real.sqrt (1 - ‖z‖ ^ 2)
      have hR_pos : 0 < R := by
        have h : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
        exact Real.sqrt_pos.mpr h
      have h_len : volume (I_z z) = ENNReal.ofReal (2 * R) := slice_volume j z hz_lt_one
      have h_set_H : H_z z ∩ I_z z = {t : ℝ | (coordSplit j).symm (z, t) ∈ ball (0 : E (m + 1)) 1 ∧ t < 0} := by
        ext t
        simp [H_z, I_z]
        <;> constructor <;> intro h <;> exact ⟨h.2, h.1⟩
      have h_half_len : volume (H_z z ∩ I_z z) = ENNReal.ofReal R := by
        rw [h_set_H]
        exact slice_negative_volume j z hz_lt_one
      have h_disj1 : Disjoint (H_z z ∩ I_z z) (I_z z \ H_z z) := by
        simp [Set.disjoint_left] <;> tauto
      have h_union1 : (H_z z ∩ I_z z) ∪ (I_z z \ H_z z) = I_z z := by
        ext t
        simp only [H_z, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
        <;> by_cases h : t < 0 <;> simp [h] <;> tauto
      have h_H_meas : MeasurableSet (H_z z) := by
        simp only [H_z]
        have h : IsOpen {t : ℝ | t < 0} := isOpen_lt continuous_id continuous_const
        exact h.measurableSet
      have h_I_meas : MeasurableSet (I_z z) := by
        simp only [I_z]
        exact isOpen_ball.measurableSet.preimage (by fun_prop)
      have h_meas1 : MeasurableSet (H_z z ∩ I_z z) := h_H_meas.inter h_I_meas
      have h_meas2 : MeasurableSet (I_z z \ H_z z) := h_I_meas.diff h_H_meas
      have h_other_half : volume (I_z z \ H_z z) = ENNReal.ofReal R := by
        have h_union_vol : volume ((H_z z ∩ I_z z) ∪ (I_z z \ H_z z)) =
            volume (H_z z ∩ I_z z) + volume (I_z z \ H_z z) :=
          measure_union h_disj1 h_meas2
        have h_eq1 : volume (I_z z) = volume ((H_z z ∩ I_z z) ∪ (I_z z \ H_z z)) := by
          rw [h_union1]
        have h_eq : volume (I_z z) = volume (H_z z ∩ I_z z) + volume (I_z z \ H_z z) := by
          rw [h_eq1, h_union_vol]
        rw [h_len, h_half_len] at h_eq
        have h6 : ENNReal.ofReal (2 * R) = ENNReal.ofReal R + ENNReal.ofReal R := by
          rw [← ENNReal.ofReal_add hR_pos.le hR_pos.le] <;> ring_nf <;> norm_num
        rw [h6] at h_eq
        have h7 : ENNReal.ofReal R + ENNReal.ofReal R = ENNReal.ofReal R + volume (I_z z \ H_z z) := h_eq
        have h8 : ENNReal.ofReal R ≠ ⊤ := ENNReal.ofReal_lt_top.ne
        have h9 : volume (I_z z \ H_z z) = ENNReal.ofReal R := by
          have h10 : ENNReal.ofReal R + volume (I_z z \ H_z z) = ENNReal.ofReal R + ENNReal.ofReal R := h7.symm
          exact (ENNReal.add_right_inj h8).mp h10
        exact h9
      have h9 : 2 * η - η^2 ≤ 1 - ‖z‖^2 := by
        have h10 : ‖z‖ ≤ 1 - η := hz_norm
        nlinarith [norm_nonneg z, hη_pos]
      have h10 : l_min ≤ R := by
        rw [hl_min_def]
        exact Real.sqrt_le_sqrt h9
      have h_lmin_le : ENNReal.ofReal l_min ≤ ENNReal.ofReal R :=
        ENNReal.ofReal_le_ofReal h10
      -- Prove volume (S_z z ∩ I_z z) > 0
      let A1 := (H_z z ∩ I_z z) \ S_z z
      have hA1_sub : A1 ⊆ symmDiff (S_z z) (H_z z) ∩ I_z z := by
        intro t ht
        rcases ht with ⟨⟨hH, hI⟩, hnS⟩
        exact ⟨Or.inr ⟨hH, hnS⟩, hI⟩
      have h43 : volume A1 ≤ δ_vol z := measure_mono hA1_sub
      have h45 : volume A1 < volume (H_z z ∩ I_z z) := by
        rw [h_half_len]
        have hδ_lt_R : δ_vol z < ENNReal.ofReal R := lt_of_lt_of_le h_small h_lmin_le
        exact lt_of_le_of_lt h43 hδ_lt_R
      have h41 : H_z z ∩ I_z z ⊆ (S_z z ∩ I_z z) ∪ A1 := by
        intro t ht
        by_cases h5 : t ∈ S_z z
        · exact Or.inl ⟨h5, ht.2⟩
        · exact Or.inr ⟨ht, h5⟩
      have h42 : volume (H_z z ∩ I_z z) ≤ volume (S_z z ∩ I_z z) + volume A1 :=
        calc volume (H_z z ∩ I_z z)
          ≤ volume ((S_z z ∩ I_z z) ∪ A1) := measure_mono h41
        _ ≤ volume (S_z z ∩ I_z z) + volume A1 := measure_union_le _ _
      have h1_pos : volume (S_z z ∩ I_z z) > 0 := by
        by_contra h
        have h0 : volume (S_z z ∩ I_z z) = 0 := by simpa using h
        rw [h0] at h42
        have h6 : volume (H_z z ∩ I_z z) ≤ volume A1 := by simpa using h42
        exact not_le.mpr h45 h6
      -- Prove volume (I_z z \ S_z z) > 0
      let A2 := (I_z z \ H_z z) ∩ S_z z
      have hA2_sub : A2 ⊆ symmDiff (S_z z) (H_z z) ∩ I_z z := by
        intro t ht
        rcases ht with ⟨⟨hI, hnH⟩, hS⟩
        exact ⟨Or.inl ⟨hS, hnH⟩, hI⟩
      have h53 : volume A2 ≤ δ_vol z := measure_mono hA2_sub
      have h55 : volume A2 < volume (I_z z \ H_z z) := by
        rw [h_other_half]
        have hδ_lt_R : δ_vol z < ENNReal.ofReal R := lt_of_lt_of_le h_small h_lmin_le
        exact lt_of_le_of_lt h53 hδ_lt_R
      have h51 : I_z z \ H_z z ⊆ (I_z z \ S_z z) ∪ A2 := by
        intro t ht
        by_cases h5 : t ∈ S_z z
        · exact Or.inr ⟨ht, h5⟩
        · exact Or.inl ⟨ht.1, h5⟩
      have h52 : volume (I_z z \ H_z z) ≤ volume (I_z z \ S_z z) + volume A2 :=
        calc volume (I_z z \ H_z z)
          ≤ volume ((I_z z \ S_z z) ∪ A2) := measure_mono h51
        _ ≤ volume (I_z z \ S_z z) + volume A2 := measure_union_le _ _
      have h2_pos : volume (I_z z \ S_z z) > 0 := by
        by_contra h
        have h0 : volume (I_z z \ S_z z) = 0 := by simpa using h
        rw [h0] at h52
        have h6 : volume (I_z z \ H_z z) ≤ volume A2 := by simpa using h52
        exact not_le.mpr h55 h6
      exact ⟨h1_pos, h2_pos⟩
    -- Measurable bad set: z in ball(0,1-η) with δ_vol z ≥ l_min
    let Bad' : Set (E m) := ball (0 : E m) (1 - η) ∩ {z | δ_vol z ≥ ENNReal.ofReal l_min}
    have hBad'_meas : MeasurableSet Bad' := by
      have hIci : MeasurableSet (Set.Ici (ENNReal.ofReal l_min)) := measurableSet_Ici
      have h1 : MeasurableSet {z : E m | δ_vol z ≥ ENNReal.ofReal l_min} :=
        hδ_vol_meas hIci
      exact isOpen_ball.measurableSet.inter h1
    have hBad'_sub : Bad' ⊆ ball (0 : E m) (1 - η) := by simp [Bad'] <;> tauto
    -- If z in ball but not Bad', then z ∈ Good
    have h_good_from_not_bad : ∀ z ∈ ball (0 : E m) (1 - η), z ∉ Bad' → z ∈ Good := by
      intro z hz_ball hz_not_bad
      have hz_lt : ‖z‖ < 1 - η := by simpa [ball] using hz_ball
      have hz_norm : ‖z‖ ≤ 1 - η := le_of_lt hz_lt
      have h_small : δ_vol z < ENNReal.ofReal l_min := by
        have h : z ∉ Bad' := hz_not_bad
        simp only [Bad', Set.mem_inter_iff, Set.mem_setOf_eq] at h
        by_contra h'
        have h'2 : δ_vol z ≥ ENNReal.ofReal l_min := le_of_not_gt h'
        exact h ⟨hz_ball, h'2⟩
      exact h_good_if_small z hz_norm h_small
    -- Good ∩ ball ⊇ ball \ Bad'
    have h_good_super : ball (0 : E m) (1 - η) \ Bad' ⊆ Good ∩ ball (0 : E m) (1 - η) := by
      intro z hz
      have hz_ball : z ∈ ball (0 : E m) (1 - η) := hz.1
      have hz_not_bad : z ∉ Bad' := hz.2
      have hz_good : z ∈ Good := h_good_from_not_bad z hz_ball hz_not_bad
      exact ⟨hz_good, hz_ball⟩
    -- Markov: volume(Bad') * l_min ≤ total excess
    have h_markov : volume Bad' * ENNReal.ofReal l_min ≤ ∫⁻ z, δ_vol z := by
      have hfg : Set.indicator Bad' δ_vol ≤ δ_vol := by
        intro z
        by_cases h : z ∈ Bad'
        · simp [h, Set.indicator_apply]
        · simp [h, Set.indicator_apply] <;> exact zero_le _
      have h1 : ∫⁻ z in Bad', δ_vol z ≤ ∫⁻ z, δ_vol z := by
        have h_eq : ∫⁻ z in Bad', δ_vol z = ∫⁻ z, Set.indicator Bad' δ_vol z := by
          rw [MeasureTheory.lintegral_indicator hBad'_meas] <;> rfl
        rw [h_eq]
        exact lintegral_mono hfg
      have h3 : ∀ z ∈ Bad', ENNReal.ofReal l_min ≤ δ_vol z := by
        intro z hz
        exact hz.2
      have h4 : ∫⁻ z in Bad', ENNReal.ofReal l_min ≤ ∫⁻ z in Bad', δ_vol z :=
        setLIntegral_mono' hBad'_meas h3
      have h5 : ∫⁻ z in Bad', ENNReal.ofReal l_min = volume Bad' * ENNReal.ofReal l_min := by
        have h6 : ∫⁻ z, Set.indicator Bad' (fun _ => ENNReal.ofReal l_min) z =
            ENNReal.ofReal l_min * volume Bad' :=
          MeasureTheory.lintegral_indicator_const₀ hBad'_meas.nullMeasurableSet (ENNReal.ofReal l_min)
        have h7 : ∫⁻ z in Bad', ENNReal.ofReal l_min = ∫⁻ z, Set.indicator Bad' (fun _ => ENNReal.ofReal l_min) z := by
          rw [MeasureTheory.lintegral_indicator hBad'_meas] <;> rfl
        rw [h7, h6] <;> ring
      rw [h5] at h4
      exact le_trans h4 h1
    have hε_nonneg : 0 ≤ ε := by linarith [hε_pos]
    have h6_mul : ENNReal.ofReal ε = ENNReal.ofReal (ε / l_min) * ENNReal.ofReal l_min := by
      have h : (ε / l_min) * l_min = ε := by
        field_simp [hl_min_pos.ne'] <;> ring
      have h2 : ENNReal.ofReal ε = ENNReal.ofReal ((ε / l_min) * l_min) := by rw [h]
      have h_nonneg_div : 0 ≤ ε / l_min := div_nonneg (by linarith [hε_pos]) (by linarith [hl_min_pos])
      have h_mul : ENNReal.ofReal ((ε / l_min) * l_min) = ENNReal.ofReal (ε / l_min) * ENNReal.ofReal l_min :=
        ENNReal.ofReal_mul h_nonneg_div
      rw [h2, h_mul]
    have h_bad_vol : volume Bad' < target := by
      have h71 : volume Bad' * ENNReal.ofReal l_min ≤ ∫⁻ z, δ_vol z := h_markov
      have h72 : ∫⁻ z, δ_vol z < ENNReal.ofReal ε := h_close
      have h73 : ENNReal.ofReal ε = ENNReal.ofReal (ε / l_min) * ENNReal.ofReal l_min := h6_mul
      rw [h73] at h72
      have h7 : volume Bad' * ENNReal.ofReal l_min < ENNReal.ofReal (ε / l_min) * ENNReal.ofReal l_min :=
        lt_of_le_of_lt h71 h72
      have h8 : ENNReal.ofReal l_min ≠ 0 := by positivity
      have h8' : ENNReal.ofReal l_min ≠ ⊤ := ENNReal.ofReal_lt_top.ne
      have h7' : ENNReal.ofReal l_min * volume Bad' < ENNReal.ofReal l_min * ENNReal.ofReal (ε / l_min) := by
        simpa [mul_comm] using h7
      have h9 : volume Bad' < ENNReal.ofReal (ε / l_min) := by
        by_contra h9'
        have h10 : ENNReal.ofReal (ε / l_min) ≤ volume Bad' := le_of_not_gt h9'
        have h11 : ENNReal.ofReal l_min * ENNReal.ofReal (ε / l_min) ≤ ENNReal.ofReal l_min * volume Bad' :=
          mul_le_mul_left' h10 (ENNReal.ofReal l_min)
        exact not_le.mpr h7' h11
      exact lt_trans h9 hε_bound
    -- volume ball = volume (ball \ Bad') + volume Bad'
    have h_ball_meas : MeasurableSet (ball (0 : E m) (1 - η)) := isOpen_ball.measurableSet
    have h_ball_scaling : volume (ball (0 : E m) (1 - η)) = ENNReal.ofReal (1 - η) ^ m * ω := by
      by_cases h_m : m = 0
      · subst h_m
        have h_pos1 : 0 < 1 - η := by linarith [hη_lt_one]
        have h_x0 : ∀ (x : E 0), x = 0 := fun x => Subsingleton.elim x 0
        have h_ball1 : ball (0 : E 0) (1 - η) = Set.univ := by
          apply Set.eq_univ_of_forall
          intro x
          have hx : x = (0 : E 0) := h_x0 x
          rw [hx, mem_ball, dist_zero_right, norm_zero]
          exact h_pos1
        have h_ball2 : ball (0 : E 0) 1 = Set.univ := by
          apply Set.eq_univ_of_forall
          intro x
          have hx : x = (0 : E 0) := h_x0 x
          rw [hx, mem_ball, dist_zero_right] <;> norm_num
        have h_eq : volume (ball (0 : E 0) (1 - η)) = volume (ball (0 : E 0) 1) := by
          rw [h_ball1, h_ball2]
        simpa [ω, pow_zero] using h_eq
      · have h_pos : 0 < m := Nat.pos_of_ne_zero h_m
        haveI : Nontrivial (E m) := by
          have h_pos : 0 < m := Nat.pos_of_ne_zero h_m
          let i : Fin m := ⟨0, h_pos⟩
          refine' ⟨(0 : E m), EuclideanSpace.single i 1, _⟩
          intro h
          have h4 : (0 : E m) i = (EuclideanSpace.single i 1 : E m) i := by rw [h]
          simpa using h4
        have h_finrank : Module.finrank ℝ (E m) = m := by simp
        let K : ENNReal := ENNReal.ofReal (Real.sqrt Real.pi ^ m / Real.Gamma (m / 2 + 1))
        have h1 : volume (ball (0 : E m) (1 - η)) = ENNReal.ofReal (1 - η) ^ m * K := by
          rw [InnerProductSpace.volume_ball (0 : E m) (1 - η)]
          <;> simp [h_finrank, K] <;> ring
        have h2 : ω = K := by
          have h3 : volume (ball (0 : E m) 1) = (ENNReal.ofReal (1 : ℝ)) ^ m * K := by
            rw [InnerProductSpace.volume_ball (0 : E m) (1 : ℝ)]
            <;> simp [h_finrank, K] <;> ring
          simpa [ω] using h3
        rw [h1, h2] <;> ring
    have h_union2 : (ball (0 : E m) (1 - η) \ Bad') ∪ Bad' = ball (0 : E m) (1 - η) := by
      ext z
      simp only [Bad', Set.mem_union, Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq]
      <;> by_cases h : z ∈ ball (0 : E m) (1 - η)
      · simp [h]
        <;> exact lt_or_ge (δ_vol z) (ENNReal.ofReal l_min)
      · simp [h]
    have h_diff_meas : MeasurableSet (ball (0 : E m) (1 - η) \ Bad') := h_ball_meas.diff hBad'_meas
    have h_eq_add : volume (ball (0 : E m) (1 - η)) =
        volume (ball (0 : E m) (1 - η) \ Bad') + volume Bad' := by
      have h_disj : Disjoint (ball (0 : E m) (1 - η) \ Bad') Bad' := by
        simp [Set.disjoint_left]
      have h_eq : volume ((ball (0 : E m) (1 - η) \ Bad') ∪ Bad') =
          volume (ball (0 : E m) (1 - η) \ Bad') + volume Bad' :=
        measure_union h_disj hBad'_meas
      rw [h_union2] at h_eq
      exact h_eq
    have h_main : volume (Good ∩ ball (0 : E m) (1 - η)) ≥ ENNReal.ofReal (1 - δ) * ω := by
      set A := volume (ball (0 : E m) (1 - η) \ Bad') with hA_def
      set B := volume Bad' with hB_def
      set C := ENNReal.ofReal (δ / 2) * ω with hC_def
      set D := ENNReal.ofReal (1 - δ / 2) * ω with hD_def
      set E_val := ENNReal.ofReal (1 - η) ^ m * ω with hE_val_def
      set F := ENNReal.ofReal (1 - δ) * ω with hF_def
      have h10 : volume (Good ∩ ball (0 : E m) (1 - η)) ≥ A := measure_mono h_good_super
      have h11 : A + B = E_val := by
        simp only [hA_def, hB_def, hE_val_def]
        rw [← h_eq_add, h_ball_scaling]
      have h12 : B < C := h_bad_vol
      have h13 : D < E_val := h_η_bound
      have h14 : δ / 2 < 1 - δ / 2 := by linarith [hδ_lt_one]
      have h151 : ENNReal.ofReal (δ / 2) < ENNReal.ofReal (1 - δ / 2) := by
        have h_nonneg1 : 0 ≤ δ / 2 := by linarith
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h_nonneg1).mpr h14
      have h15 : C < D := by
        have h : ω * ENNReal.ofReal (δ / 2) < ω * ENNReal.ofReal (1 - δ / 2) :=
          ENNReal.mul_lt_mul_right hω_pos.ne' hω_lt_top.ne h151
        simpa [hC_def, hD_def, mul_comm] using h
      have hA_lt_top : A ≠ ⊤ := by
        have h : A ≤ volume (ball (0 : E m) (1 - η)) := measure_mono (by simp)
        have h2 : volume (ball (0 : E m) (1 - η)) < ⊤ := by
          rw [h_ball_scaling]
          have h3 : ENNReal.ofReal (1 - η) ^ m < ⊤ := by
            apply ENNReal.pow_lt_top
            exact ENNReal.ofReal_lt_top
          exact ENNReal.mul_lt_top h3 hω_lt_top
        exact (lt_of_le_of_lt h h2).ne
      have h20 : A + B < A + C := (ENNReal.add_lt_add_iff_left hA_lt_top).mpr h12
      have h21 : E_val < A + C := by
        have h22 : A + B = E_val := h11
        rw [h22] at h20
        exact h20
      have h23 : D < A + C := lt_trans h13 h21
      have h24 : D = F + C := by
        have h25 : 1 - δ / 2 = (1 - δ) + δ / 2 := by ring
        have h26 : ENNReal.ofReal (1 - δ / 2) = ENNReal.ofReal ((1 - δ) + δ / 2) := by rw [h25]
        have h27 : ENNReal.ofReal ((1 - δ) + δ / 2) = ENNReal.ofReal (1 - δ) + ENNReal.ofReal (δ / 2) := by
          rw [ENNReal.ofReal_add (by linarith) (by linarith)]
        have h28 : ENNReal.ofReal (1 - δ / 2) * ω =
            (ENNReal.ofReal (1 - δ) + ENNReal.ofReal (δ / 2)) * ω := by
          rw [h26, h27]
        rw [hD_def, h28]
        rw [right_distrib]
        <;> rfl
      rw [h24] at h23
      have h29 : C ≠ ⊤ := by
        simp only [hC_def]
        have h3 : ENNReal.ofReal (δ / 2) < ⊤ := ENNReal.ofReal_lt_top
        exact (ENNReal.mul_lt_top h3 hω_lt_top).ne
      have h31 : C + F < C + A := by
        have h : F + C < A + C := h23
        have h32 : F + C = C + F := add_comm F C
        have h33 : A + C = C + A := add_comm A C
        rw [h32, h33] at h
        exact h
      have h30 : F < A := (ENNReal.add_lt_add_iff_left h29).mp h31
      have h_final : F ≤ volume (Good ∩ ball (0 : E m) (1 - η)) := by
        calc F
          ≤ A := h30.le
        _ ≤ volume (Good ∩ ball (0 : E m) (1 - η)) := h10
      exact h_final
    -- Good ⊆ projection of frontier
    have h_good_proj : Good ∩ ball (0 : E m) (1 - η) ⊆
        projCoord j '' (frontier S ∩ ball (0 : E (m + 1)) 1) := by
      intro z hz
      have hz_good : z ∈ Good := hz.1
      have hz_ball : z ∈ ball (0 : E m) (1 - η) := hz.2
      have hz_norm : ‖z‖ < 1 := by
        have h : ‖z‖ < 1 - η := by simpa [ball] using hz_ball
        linarith [hη_pos]
      rcases hz_good with ⟨h1, h2⟩
      have h1' : (S_z z ∩ I_z z).Nonempty := by
        by_contra h
        have h_empty : S_z z ∩ I_z z = ∅ := Set.not_nonempty_iff_eq_empty.mp h
        rw [h_empty] at h1
        simp at h1
      have h2' : (I_z z \ S_z z).Nonempty := by
        by_contra h
        have h_empty : I_z z \ S_z z = ∅ := Set.not_nonempty_iff_eq_empty.mp h
        rw [h_empty] at h2
        simp at h2
      rcases h1' with ⟨t1, ht1⟩
      rcases h2' with ⟨t2, ht2⟩
      let x1 := split.symm (z, t1)
      let x2 := split.symm (z, t2)
      have hx1_in_S : x1 ∈ S := ht1.1
      have hx1_in_ball : x1 ∈ ball (0 : E (m + 1)) 1 := ht1.2
      have hx2_not_S : x2 ∉ S := ht2.2
      have hx2_in_ball : x2 ∈ ball (0 : E (m + 1)) 1 := ht2.1
      let C : Set (E (m + 1)) := Set.image (fun t : ℝ => split.symm (z, t)) (I_z z)
      have hC_eq : C = Set.image (fun t : ℝ => split.symm (z, t)) (I_z z) := by rfl
      have hI_eq : I_z z = Ioo (-(Real.sqrt (1 - ‖z‖^2))) (Real.sqrt (1 - ‖z‖^2)) :=
        slice_interval j z hz_norm
      have hC_conn : IsConnected C := by
        rw [hC_eq, hI_eq]
        have h_endpoints : -(Real.sqrt (1 - ‖z‖^2)) < Real.sqrt (1 - ‖z‖^2) := by
          have h_pos : 0 < Real.sqrt (1 - ‖z‖^2) := by
            have h : 0 < 1 - ‖z‖^2 := by nlinarith [norm_nonneg z]
            exact Real.sqrt_pos.mpr h
          linarith
        have h_conn : IsConnected (Ioo (-(Real.sqrt (1 - ‖z‖^2))) (Real.sqrt (1 - ‖z‖^2))) :=
          isConnected_Ioo h_endpoints
        have h_cont : Continuous (fun t : ℝ => split.symm (z, t)) :=
          slice_map_continuous j z
        exact h_conn.image (fun t : ℝ => split.symm (z, t)) h_cont.continuousOn
      have hC_sub : C ⊆ ball (0 : E (m + 1)) 1 := by
        rw [hC_eq]
        intro y hy
        rcases hy with ⟨t, ht, rfl⟩
        exact ht
      have hxE : (C ∩ S).Nonempty := by
        refine' ⟨x1, _, hx1_in_S⟩
        rw [hC_eq]
        exact ⟨t1, ht1.2, rfl⟩
      have hyE : (C ∩ Sᶜ).Nonempty := by
        refine' ⟨x2, _, hx2_not_S⟩
        rw [hC_eq]
        exact ⟨t2, ht2.1, rfl⟩
      have h_cross : (C ∩ frontier S).Nonempty := frontier_crosses_connected hC_conn hxE hyE
      rcases h_cross with ⟨y, hyC, hy_frontier⟩
      have hy_ball : y ∈ ball (0 : E (m + 1)) 1 := hC_sub hyC
      have h_proj : projCoord j y = z := by
        have hyC' : y ∈ Set.image (fun t : ℝ => split.symm (z, t)) (I_z z) := by
          rw [← hC_eq] <;> exact hyC
        rcases hyC' with ⟨t, _, rfl⟩
        simp [projCoord, split] <;> rfl
      exact ⟨y, ⟨hy_frontier, hy_ball⟩, h_proj⟩
    -- Lipschitz projection bound
    let A_set : Set (E (m + 1)) := frontier S ∩ ball (0 : E (m + 1)) 1
    let H_meas : Measure (E (m + 1)) := μHE[m]
    have h_lip : volume (projCoord j '' A_set) ≤ H_meas A_set :=
      projCoord_volume_le_hausdorff j A_set
    have h_step1 : ENNReal.ofReal (1 - δ) * ω ≤ volume (Good ∩ ball (0 : E m) (1 - η)) := h_main
    have h_step2 : volume (Good ∩ ball (0 : E m) (1 - η)) ≤ volume (projCoord j '' A_set) :=
      measure_mono h_good_proj
    have h_step3 : volume (projCoord j '' A_set) ≤ H_meas A_set := h_lip
    exact le_trans h_step1 (le_trans h_step2 h_step3)

/-- **Dimension-polymorphic wrapper** for `geometric_lower_bound_coord`.
Takes `n : ℕ` and `j : Fin n` directly, avoiding the `m + 1 = n` transport. -/
lemma geometric_lower_bound_coord_n (n : ℕ) (hn : 2 ≤ n) (j : Fin n) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (ε : ℝ), 0 < ε ∧ ∀ (S : Set (E n)), MeasurableSet S →
      (volume (symmDiff S {x | x j < 0} ∩ ball (0 : E n) 1) < ENNReal.ofReal ε →
       μHE[n - 1] (frontier S ∩ ball (0 : E n) 1) ≥
         ENNReal.ofReal (1 - δ) * volume (ball (0 : E (n - 1)) 1)) := by
  cases n with
  | zero => omega
  | succ m =>
    have h_m_pos : 0 < m := by omega
    rcases geometric_lower_bound_coord m j δ hδ with ⟨ε, hε_pos, h_geom⟩
    refine ⟨ε, hε_pos, fun S hS h_excess => ?_⟩
    exact h_geom S hS h_excess

/-- **Hyperplane disk measure equals ball volume in dimension `n-1`.** -/
lemma hyperplane_disk_eq_ball_volume {n : ℕ} (hn : 2 ≤ n) (ν_vec : E n) (hν_unit : ‖ν_vec‖ = 1) :
    μHE[n - 1] ({z : E n | inner ℝ z ν_vec = 0} ∩ ball (0 : E n) 1) =
    volume (ball (0 : E (n - 1)) 1) := by
  let f : Module.Dual ℝ (E n) :=
    { toFun := fun z => inner ℝ z ν_vec
      map_add' := by simp [inner_add_left]
      map_smul' := by simp [inner_smul_left] }
  let H : Submodule ℝ (E n) := LinearMap.ker f
  have hH_def : (H : Set (E n)) = {z | inner ℝ z ν_vec = 0} := by
    ext z; simp [H, f] <;> rfl
  have hf_ne_zero : f ≠ 0 := by
    intro h
    have h1 : f ν_vec = 0 := by rw [h] <;> simp
    have h2 : f ν_vec = inner ℝ ν_vec ν_vec := by rfl
    rw [h2] at h1
    have h3 : inner ℝ ν_vec ν_vec = ‖ν_vec‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K] <;> norm_cast
    rw [h3, hν_unit] at h1 <;> norm_num at h1
  have h_dim : Module.finrank ℝ H + 1 = Module.finrank ℝ (E n) :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hf_ne_zero
  have h_finrank_E : Module.finrank ℝ (E n) = n := by
    simpa [E, Fintype.card_fin] using finrank_fintype_fun
  have h_dim' : Module.finrank ℝ H = n - 1 := by omega
  let i : H → E n := Subtype.val
  have hi : Isometry i := by
    intro x y
    simp [i, edist_dist]
    <;> rfl
  let s : Set H := ball (0 : H) 1
  have h_image : i '' s = (H : Set (E n)) ∩ ball (0 : E n) 1 := by
    ext y
    simp only [Set.mem_image, s, Set.mem_inter_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.prop, by simpa [mem_ball] using hx⟩
    · rintro ⟨hy, hball⟩
      refine ⟨⟨y, hy⟩, by simpa [mem_ball] using hball, rfl⟩
  have h_meas : μHE[n - 1] (i '' s) = μHE[n - 1] s :=
    Isometry.euclideanHausdorffMeasure_image hi s
  have h_eq : (μHE[n - 1] : Measure H) = volume := by
    have h_tmp : (μHE[Module.finrank ℝ H] : Measure H) = volume :=
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume
    rw [h_dim'] at h_tmp
    exact h_tmp
  have h_main : μHE[n - 1] ((H : Set (E n)) ∩ ball (0 : E n) 1) = volume (ball (0 : H) 1) := by
    calc μHE[n - 1] ((H : Set (E n)) ∩ ball (0 : E n) 1)
      = μHE[n - 1] (i '' s) := by rw [h_image]
    _ = μHE[n - 1] s := h_meas
    _ = volume s := by rw [h_eq]
    _ = volume (ball (0 : H) 1) := by rfl
  have h_set_eq : {z : E n | inner ℝ z ν_vec = 0} ∩ ball (0 : E n) 1 = (H : Set (E n)) ∩ ball (0 : E n) 1 := by
    rw [hH_def]
  rw [h_set_eq, h_main]
  have h_ball_eq : volume (ball (0 : H) 1) = volume (ball (0 : E (n - 1)) 1) := by
    have h_finrank_H : Module.finrank ℝ H = n - 1 := h_dim'
    have h_pos : 0 < Module.finrank ℝ H := by omega
    letI h_nontriv_H : Nontrivial H := Module.nontrivial_of_finrank_pos h_pos
    have h_pos2 : 0 < n - 1 := by omega
    letI h_nontriv_E : Nontrivial (E (n - 1)) := by
      let i0 : Fin (n - 1) := ⟨0, by omega⟩
      refine' ⟨(0 : E (n - 1)), EuclideanSpace.single i0 1, _⟩
      intro h
      have h2 : (0 : E (n - 1)) i0 = (EuclideanSpace.single i0 1) i0 := by
        exact congr_arg (fun (x : E (n - 1)) => x i0) h
      simpa [EuclideanSpace.single_apply] using h2
    have h1 : volume (ball (0 : H) 1) = ENNReal.ofReal (1 : ℝ) ^ Module.finrank ℝ H *
        ENNReal.ofReal (Real.sqrt Real.pi ^ Module.finrank ℝ H / Real.Gamma (Module.finrank ℝ H / 2 + 1)) :=
      InnerProductSpace.volume_ball (0 : H) 1
    have h_finrank_E : Module.finrank ℝ (E (n - 1)) = n - 1 := by
      simp [E, Fintype.card_fin]
    have h2 : volume (ball (0 : E (n - 1)) 1) = ENNReal.ofReal (1 : ℝ) ^ Module.finrank ℝ (E (n - 1)) *
        ENNReal.ofReal (Real.sqrt Real.pi ^ Module.finrank ℝ (E (n - 1)) / Real.Gamma (Module.finrank ℝ (E (n - 1)) / 2 + 1)) :=
      InnerProductSpace.volume_ball (0 : E (n - 1)) 1
    rw [h1, h2, h_finrank_H, h_finrank_E] <;> rfl
  exact h_ball_eq

/-- **Lower Hausdorff density at TRB points**.

For any `ε > 0`, for all sufficiently small `r > 0`,
`H(frontier U ∩ ball x r) / r^(n-1) ≥ H(hyperplane disk) - ε`. -/
lemma hausdorff_lower_density_at_trb
    {U : Set (E n)} (hU : IsOpen U) (hBdd : Bornology.IsBounded U)
    (h_perim_finite : perimeter U < ⊤) (hn : 2 ≤ n)
    (h_haus_frontier_lt_top : μHE[n - 1] (frontier U) < ⊤)
    (x : E n) (ν_vec : E n) (hν_unit : ‖ν_vec‖ = 1)
    (hdata : ReducedBoundaryData U x ν_vec) :
    ∀ (ε : ℝ), 0 < ε →
      ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0),
        (μHE[n - 1] (frontier U ∩ ball x r)).toReal / r ^ (n - 1) ≥
        (μHE[n - 1] ({z : E n | inner ℝ z ν_vec = 0} ∩ ball (0 : E n) 1)).toReal - ε := by
  set m : ℕ := n - 1 with hm_def
  have hm_pos : 0 < m := by omega
  letI : Nonempty (Fin m) := ⟨⟨0, hm_pos⟩⟩
  have hmn : m + 1 = n := by omega
  let ω : ENNReal := μHE[n - 1] ({z : E n | inner ℝ z ν_vec = 0} ∩ ball (0 : E n) 1)
  have hω_eq : ω = volume (ball (0 : E m) 1) :=
    hyperplane_disk_eq_ball_volume hn ν_vec hν_unit
  have hω_pos : 0 < ω := by
    rw [hω_eq]
    have h : 0 < volume (ball (0 : E m) 1) := by
      apply MeasureTheory.Measure.measure_pos_of_nonempty_interior
      have h_open : IsOpen (ball (0 : E m) 1) := isOpen_ball
      have h_int : interior (ball (0 : E m) 1) = ball (0 : E m) 1 := h_open.interior_eq
      rw [h_int]
      exact ⟨0, by simp [mem_ball, dist_zero_right]⟩
    exact h
  have hω_lt_top : ω < ⊤ := by
    rw [hω_eq]
    exact measure_ball_lt_top
  have hω_toReal_pos : 0 < ω.toReal := ENNReal.toReal_pos hω_pos.ne' hω_lt_top.ne
  let Hν : Set (E n) := halfSpace ν_vec
  have h_n_pos : 0 < n := by linarith
  rcases exists_isometry_map_to_basis h_n_pos ν_vec hν_unit with ⟨j, e, heν⟩
  let e_j : E n := EuclideanSpace.single j 1
  have he_inner : ∀ (z : E n), inner ℝ (e z) e_j = inner ℝ z ν_vec := by
    intro z
    have h : inner ℝ (e z) (e ν_vec) = inner ℝ z ν_vec :=
      LinearIsometryEquiv.inner_map_map e z ν_vec
    rw [heν] at h
    exact h
  have he_halfspace : e '' Hν = {y : E n | y j < 0} := by
    ext y
    simp only [Set.mem_image, Hν, halfSpace, Set.mem_setOf_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h : inner ℝ (e z) e_j < 0 := by rw [he_inner z] <;> exact hz
      have h' : inner ℝ (e z) e_j = (e z) j := by
        simp [e_j, EuclideanSpace.inner_single_right]
        <;> rfl
      rw [h'] at h
      exact h
    · intro hy
      have h5 : inner ℝ y e_j < 0 := by
        have h' : inner ℝ y e_j = y j := by
          simp [e_j, EuclideanSpace.inner_single_right] <;> rfl
        have h_yj : y j < 0 := hy
        rw [h']
        exact h_yj
      have h6 : inner ℝ (e.symm y) ν_vec < 0 := by
        have h7 : inner ℝ (e (e.symm y)) e_j = inner ℝ (e.symm y) ν_vec := he_inner (e.symm y)
        have h8 : inner ℝ (e (e.symm y)) e_j < 0 := by
          have h9 : e (e.symm y) = y := e.apply_symm_apply y
          rw [h9] <;> exact h5
        exact h7 ▸ h8
      exact ⟨e.symm y, h6, e.apply_symm_apply y⟩
  have he_ball : e '' (ball (0 : E n) 1) = ball (0 : E n) 1 := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h : ‖e z‖ = ‖z‖ := e.norm_map z
      simpa [mem_ball, h] using hz
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      have h : ‖e.symm y‖ = ‖y‖ := by
        have h2 : ‖e (e.symm y)‖ = ‖e.symm y‖ := e.norm_map (e.symm y)
        have h3 : e (e.symm y) = y := e.apply_symm_apply y
        rw [h3] at h2
        exact h2.symm
      simpa [mem_ball, h] using hy
  have hU_meas : MeasurableSet U := IsOpen.measurableSet hU
  have hS_meas : ∀ (r : ℝ), 0 < r → MeasurableSet (blowUp U x r) := by
    intro r hr
    have hr' : r ≠ 0 := hr.ne'
    have h_open : IsOpen (blowUp U x r) :=
      (blowUpMapHomeomorph x hr').isOpen_image.mpr hU
    exact IsOpen.measurableSet h_open
  have h_frontier_blowUp : ∀ (r : ℝ), r ≠ 0 →
      frontier (blowUp U x r) = blowUp (frontier U) x r := by
    intro r hr
    let h := blowUpMapHomeomorph x hr
    exact (h.image_frontier U).symm
  have h_blowUp_inter : ∀ (r : ℝ), 0 < r →
      blowUp (frontier U) x r ∩ ball (0 : E n) 1 = blowUp (frontier U ∩ ball x r) x r := by
    intro r hr
    have h := blowUp_inter_ball (S := frontier U) (x := x) (r := r) (R := 1) hr (by norm_num)
    simpa [mul_one] using h
  intro ε hε
  set δ0 : ℝ := ε / (2 * ω.toReal) with hδ0_def
  set δ : ℝ := min δ0 (1 / 2 : ℝ) with hδ_def
  have hδ_pos : 0 < δ := by
    rw [hδ_def]
    have h1 : 0 < δ0 := by
      rw [hδ0_def] <;> positivity
    exact lt_min h1 (by norm_num)
  have hδ_le_half : δ ≤ 1 / 2 := min_le_right _ _
  have hδ_lt_one : δ < 1 := by linarith
  have h1mδ_pos : 0 < 1 - δ := by linarith
  have hδω : δ * ω.toReal < ε := by
    have h1 : δ ≤ δ0 := min_le_left _ _
    have h2 : 0 ≤ ω.toReal := by positivity
    have h3 : δ * ω.toReal ≤ δ0 * ω.toReal := mul_le_mul_of_nonneg_right h1 h2
    have h4 : δ0 * ω.toReal = ε / 2 := by
      rw [hδ0_def]
      have h : 0 < ω.toReal := hω_toReal_pos
      field_simp [h.ne'] <;> ring
    rw [h4] at h3
    linarith
  rcases geometric_lower_bound_coord_n n hn j δ hδ_pos
    with ⟨ε_geom, hε_geom_pos, h_geom⟩
  have h_blowup : Tendsto (fun r : ℝ => blowUpExcess U x ν_vec r 1)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    blow_up_lemma hU.measurableSet x ν_vec hν_unit hdata hn 1 (by norm_num)
  have h_eventually : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0),
      blowUpExcess U x ν_vec r 1 < ENNReal.ofReal ε_geom :=
    h_blowup (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε_geom_pos))
  filter_upwards [h_eventually, self_mem_nhdsWithin] with r hr_excess hr_pos
  set S_r : Set (E n) := blowUp U x r with hS_r_def
  set S'_r : Set (E n) := e '' S_r with hS'_r_def
  have hS_r_open : IsOpen S_r :=
    (blowUpMapHomeomorph x hr_pos.ne').isOpen_image.mpr hU
  have hS'_open : IsOpen S'_r :=
    e.toHomeomorph.isOpen_image.mpr hS_r_open
  have h_meas_S' : MeasurableSet S'_r := IsOpen.measurableSet hS'_open
  have h_excess_rot : volume (symmDiff S'_r {y : E n | y j < 0} ∩ ball (0 : E n) 1) =
      volume (symmDiff S_r Hν ∩ ball (0 : E n) 1) := by
    have h_image_symm : e '' (symmDiff S_r Hν) = symmDiff S'_r (e '' Hν) :=
      Set.image_symmDiff e.injective S_r Hν
    have h1 : e '' (symmDiff S_r Hν ∩ ball (0 : E n) 1) =
        symmDiff S'_r {y : E n | y j < 0} ∩ ball (0 : E n) 1 := by
      rw [Set.image_inter e.injective, h_image_symm, he_halfspace, he_ball]
      <;> rfl
    have h_mp : MeasurePreserving e volume volume := e.measurePreserving
    have h_set_meas : MeasurableSet (symmDiff S_r Hν ∩ ball (0 : E n) 1) := by
      have hHν_meas : MeasurableSet Hν := by
        apply IsOpen.measurableSet
        exact isOpen_lt (continuous_id.inner continuous_const) continuous_const
      have h_ball_meas : MeasurableSet (ball (0 : E n) 1) := isOpen_ball.measurableSet
      have hS_r_meas2 : MeasurableSet S_r := IsOpen.measurableSet hS_r_open
      have h_symm_meas : MeasurableSet (symmDiff S_r Hν) := by
        simp [symmDiff, hS_r_meas2, hHν_meas] <;> fun_prop
      exact h_symm_meas.inter h_ball_meas
    have h2 : volume (e '' (symmDiff S_r Hν ∩ ball (0 : E n) 1)) =
        volume (symmDiff S_r Hν ∩ ball (0 : E n) 1) := by
      have h3 : e '' (symmDiff S_r Hν ∩ ball (0 : E n) 1) =
          e.symm ⁻¹' (symmDiff S_r Hν ∩ ball (0 : E n) 1) := by
        ext y
        simp only [Set.mem_image, Set.mem_preimage]
        constructor
        · rintro ⟨x, hx, rfl⟩
          simpa using hx
        · intro hy
          exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
      rw [h3]
      have hns : NullMeasurableSet (symmDiff S_r Hν ∩ ball (0 : E n) 1) volume := by
        exact MeasurableSet.nullMeasurableSet h_set_meas
      exact e.symm.measurePreserving.measure_preimage hns
    rw [← h2, h1]
  have h_excess_lt : volume (symmDiff S'_r {y : E n | y j < 0} ∩ ball (0 : E n) 1) <
      ENNReal.ofReal ε_geom := by
    rw [h_excess_rot]
    simpa [blowUpExcess] using hr_excess
  have h_main_geom : μHE[m] (frontier S'_r ∩ ball (0 : E n) 1) ≥
      ENNReal.ofReal (1 - δ) * volume (ball (0 : E m) 1) :=
    h_geom S'_r h_meas_S' h_excess_lt
  have h_frontier_image : e '' (frontier S_r ∩ ball (0 : E n) 1) =
      frontier S'_r ∩ ball (0 : E n) 1 := by
    have h1 : e '' frontier S_r = frontier S'_r :=
      e.toHomeomorph.image_frontier S_r
    rw [Set.image_inter e.injective, h1, he_ball]
  have h_iso_haus : μHE[m] (frontier S'_r ∩ ball (0 : E n) 1) =
      μHE[m] (frontier S_r ∩ ball (0 : E n) 1) := by
    rw [← h_frontier_image]
    exact Isometry.euclideanHausdorffMeasure_image e.isometry (frontier S_r ∩ ball (0 : E n) 1)
  have h_geom2 : μHE[m] (frontier S_r ∩ ball (0 : E n) 1) ≥
      ENNReal.ofReal (1 - δ) * volume (ball (0 : E m) 1) := by
    rw [← h_iso_haus]
    exact h_main_geom
  have hr_ne : r ≠ 0 := hr_pos.ne'
  have h_frontier_eq : frontier S_r = blowUp (frontier U) x r :=
    h_frontier_blowUp r hr_ne
  have h_inter_eq : frontier S_r ∩ ball (0 : E n) 1 =
      blowUp (frontier U ∩ ball x r) x r := by
    rw [h_frontier_eq]
    exact h_blowUp_inter r hr_pos
  rw [h_inter_eq] at h_geom2
  let A : Set (E n) := frontier U ∩ ball x r
  have hA_meas : MeasurableSet A :=
    isClosed_frontier.measurableSet.inter isOpen_ball.measurableSet
  let translate : Set (E n) := (fun y : E n => y - x) '' A
  have h_translate_haus : μHE[m] translate = μHE[m] A := by
    let e2 : E n ≃ᵢ E n :=
      { toFun := fun y => y - x
        invFun := fun y => y + x
        left_inv := by intro y; simp
        right_inv := by intro y; simp
        isometry_toFun := by
          intro y z
          simp [edist_dist] }
    exact Isometry.euclideanHausdorffMeasure_image e2.isometry A
  let scaled : Set (E n) := (fun y : E n => (1 / r) • y) '' translate
  have h_scale : blowUp A x r = scaled := by
    ext z
    simp only [blowUp, blowUpMap, Set.mem_image, scaled]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y - x, ⟨y, hy, rfl⟩, by simp⟩
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by simp⟩
  rw [h_scale] at h_geom2
  have h_haus_scale : μHE[m] scaled = ↑(‖(1 / r : ℝ)‖₊ ^ m) * μHE[m] translate :=
    MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀ m (show (1 / r : ℝ) ≠ 0 from by positivity) translate
  have h_pos1r : 0 < 1 / r := div_pos zero_lt_one hr_pos
  have h_norm_eq : (↑(‖(1 / r : ℝ)‖₊ ^ m) : ENNReal) = (ENNReal.ofReal (1 / r)) ^ m := by
    have h_pos : 0 ≤ 1 / r := by linarith
    let a : NNReal := ⟨1 / r, h_pos⟩
    have h_coe_real : (↑(‖(1 / r : ℝ)‖₊) : ℝ) = (↑a : ℝ) := by
      have h7 : (↑(‖(1 / r : ℝ)‖₊) : ℝ) = |1 / r| := by exact Real.ext_cauchy rfl
      have h8 : (↑a : ℝ) = 1 / r := by
        dsimp only [a]
        <;> rfl
      rw [h7, h8, abs_of_pos h_pos1r]
    have ha : ‖(1 / r : ℝ)‖₊ = a := by
      apply NNReal.coe_injective
      exact h_coe_real
    rw [ha]
    have h_coe_pow : (↑(a ^ m) : ENNReal) = (↑a : ENNReal) ^ m := by exact coe_pow a m
    have h_coe_a : (↑a : ENNReal) = ENNReal.ofReal (1 / r) := by
      have h9 : (↑a : ENNReal) = ENNReal.ofReal (↑a : ℝ) := ENNReal.coe_nnreal_eq a
      rw [h9]
      have h10 : (↑a : ℝ) = 1 / r := by
        dsimp only [a] <;> rfl
      rw [h10]
    rw [h_coe_pow, h_coe_a]
  rw [h_haus_scale, h_norm_eq, h_translate_haus] at h_geom2
  set target : ENNReal := ENNReal.ofReal (1 - δ) * volume (ball (0 : E m) 1) with htarget_def
  have h_inv : (ENNReal.ofReal r) ^ m * (ENNReal.ofReal (1 / r)) ^ m = 1 := by
    have hr_pos' : 0 < r := hr_pos
    have h4 : ENNReal.ofReal r * ENNReal.ofReal (1 / r) = 1 := by
      have h_nonneg1 : 0 ≤ r := by linarith
      have h_nonneg2 : 0 ≤ 1 / r := by linarith
      have h_eq : ENNReal.ofReal r * ENNReal.ofReal (1 / r) = ENNReal.ofReal (r * (1 / r)) := by
        exact (ENNReal.ofReal_mul h_nonneg1).symm
      rw [h_eq]
      have h5 : r * (1 / r) = 1 := by field_simp [hr_ne] <;> ring
      rw [h5] <;> norm_num
    have h5 : (ENNReal.ofReal r) ^ m * (ENNReal.ofReal (1 / r)) ^ m =
        (ENNReal.ofReal r * ENNReal.ofReal (1 / r)) ^ m := by
      rw [← mul_pow]
    rw [h5, h4, one_pow]
  have h_r_ne_top : (ENNReal.ofReal r) ^ m ≠ ⊤ := by
    apply ENNReal.pow_ne_top
    exact ENNReal.ofReal_ne_top
  have h_r_pos : (ENNReal.ofReal r) ^ m ≠ 0 := by
    have hr_pos' : 0 < r := hr_pos
    have h : 0 < ENNReal.ofReal r := ENNReal.ofReal_pos.mpr hr_pos'
    exact pow_ne_zero m h.ne'
  have h_geom3 : (ENNReal.ofReal r) ^ m * ((ENNReal.ofReal (1 / r)) ^ m * μHE[m] A) ≥
      (ENNReal.ofReal r) ^ m * target :=
    mul_le_mul_left' h_geom2 ((ENNReal.ofReal r) ^ m)
  have h_geom4 : μHE[m] A ≥ (ENNReal.ofReal r) ^ m * target := by
    have h9 : (ENNReal.ofReal r) ^ m * ((ENNReal.ofReal (1 / r)) ^ m * μHE[m] A) = μHE[m] A := by
      rw [←mul_assoc, h_inv, one_mul]
    rw [h9] at h_geom3
    exact h_geom3
  have h_final1 : μHE[m] A ≥ (ENNReal.ofReal r) ^ m * target := h_geom4
  have h_lt_top1 : μHE[m] A < ⊤ := by
    have h_sub : A ⊆ frontier U := by simp [A]
    have h : μHE[m] A ≤ μHE[m] (frontier U) := measure_mono h_sub
    exact h.trans_lt h_haus_frontier_lt_top
  have h_toReal : (μHE[m] A).toReal ≥ ((ENNReal.ofReal r) ^ m * target).toReal :=
    ENNReal.toReal_mono h_lt_top1.ne h_final1
  have h1 : 0 ≤ r := hr_pos.le
  have h1mδ_nonneg : 0 ≤ 1 - δ := h1mδ_pos.le
  have h_toReal_r : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal h1
  have h_toReal_1mδ : (ENNReal.ofReal (1 - δ)).toReal = 1 - δ := ENNReal.toReal_ofReal h1mδ_nonneg
  have h_target_lt_top : target < ⊤ := by
    rw [htarget_def]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
  have h_toReal2 : ((ENNReal.ofReal r) ^ m * target).toReal =
      r ^ m * ((1 - δ) * (volume (ball (0 : E m) 1)).toReal) := by
    have h4 : ((ENNReal.ofReal r) ^ m * target).toReal =
        ((ENNReal.ofReal r) ^ m).toReal * target.toReal := by
      rw [ENNReal.toReal_mul]
    rw [h4]
    have h5 : ((ENNReal.ofReal r) ^ m).toReal = r ^ m := by
      rw [ENNReal.toReal_pow, h_toReal_r] <;> norm_cast
    have h6 : target.toReal = (1 - δ) * (volume (ball (0 : E m) 1)).toReal := by
      rw [htarget_def]
      rw [ENNReal.toReal_mul]
      rw [h_toReal_1mδ] <;> ring
    rw [h5, h6] <;> ring
  rw [h_toReal2] at h_toReal
  have h_ω_toReal : (volume (ball (0 : E m) 1)).toReal = ω.toReal := by rw [hω_eq]
  rw [h_ω_toReal] at h_toReal
  have h_pos_pow : 0 < r ^ m := pow_pos hr_pos m
  have h_goal : (μHE[m] A).toReal / r ^ m ≥ (1 - δ) * ω.toReal := by
    have h_nonneg_pow : 0 ≤ r ^ m := by positivity
    have h_step1 : (r ^ m * ((1 - δ) * ω.toReal)) / r ^ m ≤ (μHE[m] A).toReal / r ^ m :=
      div_le_div_of_nonneg_right h_toReal h_nonneg_pow
    have h_step2 : (r ^ m * ((1 - δ) * ω.toReal)) / r ^ m = (1 - δ) * ω.toReal := by
      field_simp [h_pos_pow.ne'] <;> ring
    rw [h_step2] at h_step1
    exact h_step1
  have h_final : (1 - δ) * ω.toReal ≥ ω.toReal - ε := by
    have h : (1 - δ) * ω.toReal = ω.toReal - δ * ω.toReal := by ring
    rw [h]; linarith [hδω]
  exact h_final.trans h_goal

end Geometry.StructureTheorem
