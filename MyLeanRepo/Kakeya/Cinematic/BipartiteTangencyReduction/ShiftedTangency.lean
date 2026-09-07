import MyLeanRepo.Kakeya.Cinematic.Geometry

/-!
# Tangency transfer through vertical translations

These lemmas put tangent relations for vertically translated functions under
one common tangency constant, as required by graph-lens non-overlap.
-/

namespace Kakeya.Cinematic

lemma CurvilinearRectangle.IsLambdaTangent.mono
    {delta t lambda₁ lambda₂ : ℝ}
    {R : CurvilinearRectangle delta t} {f : C2Function}
    (hdelta : 0 ≤ delta) (hlambda : lambda₁ ≤ lambda₂)
    (h : R.IsLambdaTangent f lambda₁) :
    R.IsLambdaTangent f lambda₂ := by
  intro p hp
  exact (h p hp).trans
    (mul_le_mul_of_nonneg_right hlambda hdelta)

lemma isLambdaTangent_of_verticalTranslate_eq
    {delta t lambda c_f c_g : ℝ}
    (hdelta : 0 < delta)
    {R : CurvilinearRectangle delta t} {f g : C2Function}
    (h : R.IsLambdaTangent g lambda)
    (heq : f.verticalTranslate c_f = g.verticalTranslate c_g) :
    R.IsLambdaTangent f
      (lambda + |c_f - c_g| / delta) := by
  intro p hp
  have heval :=
    congrArg (fun q : C2Function => q p.1) heq
  change f p.1 + c_f = g p.1 + c_g at heval
  have hrewrite :
      p.2 - f p.1 =
        (p.2 - g p.1) + (c_f - c_g) := by
    linarith
  rw [hrewrite]
  calc
    |(p.2 - g p.1) + (c_f - c_g)|
        ≤ |p.2 - g p.1| + |c_f - c_g| :=
      abs_add_le _ _
    _ ≤ lambda * delta + |c_f - c_g| := by
      gcongr
      exact h p hp
    _ = (lambda + |c_f - c_g| / delta) *
        delta := by
      field_simp [hdelta.ne']

end Kakeya.Cinematic
