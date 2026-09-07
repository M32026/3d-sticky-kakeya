import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSliceDoubleCounting
import Mathlib.Tactic

/-!
# Common-slice energy lower bound

This is the finite Cauchy--Schwarz step in `wz2_63.tex`, lines 119--128.
If the shaded mass in interval `I` satisfies `m_I ≤ A n_I`, then

`(sum_I m_I)^2 ≤ (# intervals) A sum_I n_I m_I`.

Together with `CommonSliceDoubleCounting`, this is the paper's lower bound
for the average mass retained by an anchor tube.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open ENNReal

/-- Finite Cauchy--Schwarz for finite-valued `ENNReal` weights. -/
lemma cauchy_schwarz_ennreal
    {Index : Type*} [Fintype Index]
    (mass : Index → ENNReal)
    (hmassFinite : ∀ index, mass index ≠ ⊤) :
    (∑ index, mass index) ^ 2 ≤
      (Fintype.card Index : ENNReal) *
        ∑ index, mass index ^ 2 := by
  have hsumFinite : (∑ index, mass index) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr fun index _ => hmassFinite index
  have hsquaresFinite : (∑ index, mass index ^ 2) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr fun index _ =>
      ENNReal.pow_ne_top (hmassFinite index)
  have hleftFinite : (∑ index, mass index) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top hsumFinite
  have hrightFinite :
      (Fintype.card Index : ENNReal) *
          (∑ index, mass index ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hsquaresFinite
  apply (ENNReal.toReal_le_toReal hleftFinite hrightFinite).mp
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_sum]
  · rw [ENNReal.toReal_sum]
    · simp_rw [ENNReal.toReal_pow]
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ : Finset Index)
        (fun index => (mass index).toReal)
        (fun _ => (1 : ℝ))
      simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hcs
    · intro index _
      exact ENNReal.pow_ne_top (hmassFinite index)
  · intro index _
    exact hmassFinite index

/-- The interval mass bound converts the sum of squares into the incidence
energy used by common-slice double counting. -/
theorem common_slice_energy_lower_bound
    {Tube Interval : Type*}
    [Fintype Tube] [Fintype Interval]
    (meets : Tube → Interval → Prop)
    (mass : Interval → ENNReal)
    (hmassFinite : ∀ interval, mass interval ≠ ⊤)
    (A : ENNReal)
    (hmassCount : ∀ interval,
      mass interval ≤
        A * (commonSliceMeetingCount meets interval : ENNReal)) :
    (∑ interval, mass interval) ^ 2 ≤
      (Fintype.card Interval : ENNReal) * A *
        ∑ interval,
          (commonSliceMeetingCount meets interval : ENNReal) *
            mass interval := by
  have hcs := cauchy_schwarz_ennreal mass hmassFinite
  have hsquares :
      (∑ interval, mass interval ^ 2) ≤
        A * ∑ interval,
          (commonSliceMeetingCount meets interval : ENNReal) *
            mass interval := by
    calc
      (∑ interval, mass interval ^ 2) ≤
          ∑ interval,
            A * (commonSliceMeetingCount meets interval : ENNReal) *
              mass interval := by
        apply Finset.sum_le_sum
        intro interval _
        calc
          mass interval ^ 2 = mass interval * mass interval := by ring
          _ ≤ (A * (commonSliceMeetingCount meets interval : ENNReal)) *
              mass interval := by
            exact mul_le_mul_right' (hmassCount interval) _
      _ = A * ∑ interval,
          (commonSliceMeetingCount meets interval : ENNReal) *
            mass interval := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro interval _
        ring
  calc
    (∑ interval, mass interval) ^ 2 ≤
        (Fintype.card Interval : ENNReal) *
          ∑ interval, mass interval ^ 2 := hcs
    _ ≤ (Fintype.card Interval : ENNReal) *
          (A * ∑ interval,
            (commonSliceMeetingCount meets interval : ENNReal) *
              mass interval) := by
      exact mul_le_mul_left' hsquares _
    _ = (Fintype.card Interval : ENNReal) * A *
          ∑ interval,
            (commonSliceMeetingCount meets interval : ENNReal) *
              mass interval := by ring

/-- Paper-ready common-slice anchor selection from the interval mass bound
and the aggregate energy inequality. -/
theorem exists_common_slice_anchor_of_mass_square
    {Tube Interval : Type*}
    [Fintype Tube] [Nonempty Tube] [Fintype Interval] [Nonempty Interval]
    (meets : Tube → Interval → Prop)
    (mass : Interval → ENNReal)
    (hmassFinite : ∀ interval, mass interval ≠ ⊤)
    (A target : ENNReal)
    (hAZero : A ≠ 0)
    (hAFinite : A ≠ ⊤)
    (hmassCount : ∀ interval,
      mass interval ≤
        A * (commonSliceMeetingCount meets interval : ENNReal))
    (haggregate :
      (Fintype.card Tube : ENNReal) * target *
          ((Fintype.card Interval : ENNReal) * A) ≤
        (∑ interval, mass interval) ^ 2) :
    ∃ anchor : Tube,
      target ≤ commonSliceRetainedMass meets mass anchor := by
  let energy : ENNReal :=
    ∑ interval,
      (commonSliceMeetingCount meets interval : ENNReal) * mass interval
  have hcs := common_slice_energy_lower_bound
    meets mass hmassFinite A hmassCount
  have hfactorZero :
      (Fintype.card Interval : ENNReal) * A ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast Fintype.card_pos.ne'
    · exact hAZero
  have hfactorFinite :
      (Fintype.card Interval : ENNReal) * A ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hAFinite
  have henergy :
      (Fintype.card Tube : ENNReal) * target ≤ energy := by
    have hscaled :
        ((Fintype.card Interval : ENNReal) * A) *
            ((Fintype.card Tube : ENNReal) * target) ≤
          ((Fintype.card Interval : ENNReal) * A) * energy := by
      calc
      ((Fintype.card Interval : ENNReal) * A) *
          ((Fintype.card Tube : ENNReal) * target) =
        ((Fintype.card Tube : ENNReal) * target) *
          ((Fintype.card Interval : ENNReal) * A) := by ring
      _ ≤
        (∑ interval, mass interval) ^ 2 := by
          simpa [mul_assoc] using haggregate
      _ ≤ ((Fintype.card Interval : ENNReal) * A) * energy := by
        simpa [energy, mul_assoc] using hcs
    exact (ENNReal.mul_le_mul_iff_right hfactorZero hfactorFinite).mp hscaled
  exact exists_common_slice_anchor_of_card_mul_le
    meets mass target henergy

end Kakeya.Assouad.PureWZ2

end
