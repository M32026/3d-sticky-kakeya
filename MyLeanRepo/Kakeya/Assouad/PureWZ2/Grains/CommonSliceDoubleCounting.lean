import MyLeanRepo.Kakeya.Assouad.WZ1.GridCovering

/-!
# Common-slice double counting

This is the finite combinatorial step in the common-slice refinement of
Proposition 6.3.  For every longitudinal interval `I`, let `mass I = m_I`
and let `meets tube I` record that the shading of `tube` meets `I`.  The
mass retained after choosing an anchor tube is the sum of `m_I` over the
intervals met by that anchor.  Double counting gives

`sum_anchor retained(anchor) = sum_I n_I * m_I`.

Consequently, if the right-hand side is at least `#tubes * target`, one
anchor retains at least `target`.  This is exactly the step called
"Dividing the preceding estimate by N" in the paper proof.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The shaded mass retained by keeping precisely the longitudinal intervals
met by one anchor tube. -/
def commonSliceRetainedMass
    {Tube Interval : Type*}
    [Fintype Interval]
    (meets : Tube → Interval → Prop)
    (mass : Interval → ENNReal)
    (anchor : Tube) : ENNReal := by
  classical
  exact ∑ interval, if meets anchor interval then mass interval else 0

/-- Number of tubes meeting one longitudinal interval. -/
def commonSliceMeetingCount
    {Tube Interval : Type*}
    [Fintype Tube]
    (meets : Tube → Interval → Prop)
    (interval : Interval) : ℕ := by
  classical
  exact (Finset.univ.filter fun tube => meets tube interval).card

/-- Exact tube--interval double counting for the common-slice refinement. -/
lemma common_slice_retained_mass_sum_eq
    {Tube Interval : Type*}
    [Fintype Tube] [Fintype Interval]
    (meets : Tube → Interval → Prop)
    (mass : Interval → ENNReal) :
    (∑ tube, commonSliceRetainedMass meets mass tube) =
      ∑ interval,
        (commonSliceMeetingCount meets interval : ENNReal) *
          mass interval := by
  classical
  unfold commonSliceRetainedMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro interval _
  calc
    (∑ tube, if meets tube interval then mass interval else 0) =
        ∑ tube ∈ Finset.univ.filter (fun tube => meets tube interval),
          mass interval := by
      rw [Finset.sum_filter]
    _ = (commonSliceMeetingCount meets interval : ENNReal) *
          mass interval := by
      unfold commonSliceMeetingCount
      simp [Finset.sum_const, nsmul_eq_mul]

/-- Some anchor tube retains at least the average double-counted mass. -/
theorem exists_common_slice_anchor_average
    {Tube Interval : Type*}
    [Fintype Tube] [Nonempty Tube] [Fintype Interval]
    (meets : Tube → Interval → Prop)
    (mass : Interval → ENNReal) :
    ∃ anchor : Tube,
      (∑ interval,
          (commonSliceMeetingCount meets interval : ENNReal) *
            mass interval) ≤
        (Fintype.card Tube : ENNReal) *
          commonSliceRetainedMass meets mass anchor := by
  classical
  rcases Kakeya.Assouad.exists_ge_average
      (fun tube : Tube => commonSliceRetainedMass meets mass tube) with
    ⟨anchor, hanchor⟩
  refine ⟨anchor, ?_⟩
  rw [← common_slice_retained_mass_sum_eq meets mass]
  exact hanchor

/-- Paper form of the common-slice selection: after the double-counted mass
dominates `#tubes * target`, one tube retains at least `target`. -/
theorem exists_common_slice_anchor_of_card_mul_le
    {Tube Interval : Type*}
    [Fintype Tube] [Nonempty Tube] [Fintype Interval]
    (meets : Tube → Interval → Prop)
    (mass : Interval → ENNReal)
    (target : ENNReal)
    (henergy :
      (Fintype.card Tube : ENNReal) * target ≤
        ∑ interval,
          (commonSliceMeetingCount meets interval : ENNReal) *
            mass interval) :
    ∃ anchor : Tube,
      target ≤ commonSliceRetainedMass meets mass anchor := by
  classical
  rcases exists_common_slice_anchor_average meets mass with
    ⟨anchor, hanchor⟩
  refine ⟨anchor, ?_⟩
  have hscaled :
      (Fintype.card Tube : ENNReal) * target ≤
        (Fintype.card Tube : ENNReal) *
          commonSliceRetainedMass meets mass anchor :=
    henergy.trans hanchor
  apply (ENNReal.mul_le_mul_iff_right ?_ ?_).mp hscaled
  · exact_mod_cast Fintype.card_pos.ne'
  · simp

end Kakeya.Assouad.PureWZ2

end
