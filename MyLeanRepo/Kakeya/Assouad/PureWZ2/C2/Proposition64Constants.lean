import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothSegmentExtension

/-!
# Fixed analytic constants for Proposition 6.4

The proof of `wz2_64.tex` fixes the absolute constant in the smooth segment
extension before choosing the runtime scale.  Naming that witness prevents
the later Lemma-3.5 threshold from depending on an arbitrary output record.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The once-and-for-all smooth-extension constant used in Proposition 6.4. -/
noncomputable def pureWZ2Proposition64ExtensionConstant : ℝ :=
  Classical.choose wz1_smooth_segment_extension

theorem pureWZ2Proposition64ExtensionConstant_spec :
    WZ1SmoothSegmentExtensionAtConstantStatement
      pureWZ2Proposition64ExtensionConstant :=
  Classical.choose_spec wz1_smooth_segment_extension

theorem pureWZ2Proposition64ExtensionConstant_one :
    1 ≤ pureWZ2Proposition64ExtensionConstant :=
  pureWZ2Proposition64ExtensionConstant_spec.1

/-- The fixed normalization constant `C_*` from `wz2_64.tex`. -/
noncomputable def pureWZ2Proposition64NormalizationConstant : ℝ :=
  max 9 (3 * pureWZ2Proposition64ExtensionConstant)

theorem pureWZ2Proposition64NormalizationConstant_nine :
    9 ≤ pureWZ2Proposition64NormalizationConstant := by
  exact le_max_left _ _

theorem pureWZ2Proposition64NormalizationConstant_one :
    1 ≤ pureWZ2Proposition64NormalizationConstant :=
  (by norm_num : (1 : ℝ) ≤ 9).trans
    pureWZ2Proposition64NormalizationConstant_nine

theorem pureWZ2Proposition64NormalizationConstant_pos :
    0 < pureWZ2Proposition64NormalizationConstant :=
  lt_of_lt_of_le zero_lt_one
    pureWZ2Proposition64NormalizationConstant_one

end Kakeya.Assouad

end
