import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDotSpreadFromConcentration

/-!
# Arithmetic helpers for the narrow concentration reduction

Expensive ENNReal-to-real cardinality transports are isolated here so the
large geometric reduction remains within the default heartbeat budget.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- A uniformly dense fiber over an ambient Frostman class has the expected
real-cardinality lower bound. -/
lemma narrow_dense_fiber_real_card_lower
    {index : Type*} [DecidableEq index]
    {points : Finset index}
    {delta eta workingLambda : ℝ}
    {ambientCard : ENNReal}
    (hdelta : 0 < delta)
    (hambient :
      Kakeya.realRpowENN delta (workingLambda - 1) ≤
        ambientCard)
    (hfiber :
      ((1 / 256 : ENNReal) *
          Kakeya.realRpowENN delta eta) *
          ambientCard ≤
        (points.card : ENNReal)) :
    (1 / 256 : ℝ) *
          Real.rpow delta (eta + workingLambda - 1) ≤
        (points.card : ℝ) := by
  have hproduct :
      (1 / 256 : ENNReal) *
            Kakeya.realRpowENN delta eta *
            Kakeya.realRpowENN delta (workingLambda - 1) ≤
          (points.card : ENNReal) := by
    calc
      (1 / 256 : ENNReal) *
            Kakeya.realRpowENN delta eta *
            Kakeya.realRpowENN delta (workingLambda - 1)
          ≤ ((1 / 256 : ENNReal) *
              Kakeya.realRpowENN delta eta) *
              ambientCard := by
            gcongr
      _ ≤ (points.card : ENNReal) := hfiber
  have hrpowProduct :
      Kakeya.realRpowENN delta eta *
          Kakeya.realRpowENN delta (workingLambda - 1) =
        Kakeya.realRpowENN delta
          (eta + workingLambda - 1) := by
    have h_pos1 :
        0 ≤ Real.rpow delta eta :=
      Real.rpow_nonneg hdelta.le _
    have h_add :
        Real.rpow delta eta *
            Real.rpow delta (workingLambda - 1) =
          Real.rpow delta
            (eta + workingLambda - 1) := by
      have h :=
        Real.rpow_add hdelta eta (workingLambda - 1)
      have h_exp :
          eta + (workingLambda - 1) =
            eta + workingLambda - 1 := by
        ring
      rw [h_exp] at h
      exact h.symm
    simp only [Kakeya.realRpowENN]
    rw [← ENNReal.ofReal_mul h_pos1, h_add]
  rw [mul_assoc, hrpowProduct] at hproduct
  have htoReal :=
    ENNReal.toReal_mono
      (by simp : (points.card : ENNReal) ≠ ⊤)
      hproduct
  have hrpowToReal :
      (Kakeya.realRpowENN delta
          (eta + workingLambda - 1)).toReal =
        Real.rpow delta (eta + workingLambda - 1) := by
    simp [Kakeya.realRpowENN,
      Real.rpow_nonneg hdelta.le]
  simpa [ENNReal.toReal_mul, hrpowToReal] using htoReal

end Kakeya.Assouad
