import MyLeanRepo.Kakeya.Streamlined.Statements

/-!
# Elementary facts for the streamlined API

This module is deliberately small and contains no placeholders.  It is safe
for every standalone SeedProver target to import.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- The empty indexed body family. -/
def emptyBodyFamily : BodyFamily where
  card := 0
  body := Fin.elim0

@[simp]
theorem emptyBodyFamily_enncard : emptyBodyFamily.enncard = 0 := by
  simp [emptyBodyFamily, BodyFamily.enncard]

@[simp]
theorem emptyBodyFamily_mass : emptyBodyFamily.mass = 0 := by
  simp [emptyBodyFamily, BodyFamily.mass]

theorem comparableBy_refl (x : ENNReal) : ComparableBy 1 x x := by
  simp [ComparableBy]

theorem comparableBy_symm {C x y : ENNReal}
    (h : ComparableBy C x y) : ComparableBy C y x := by
  exact ⟨h.1, h.2.2, h.2.1⟩

end Kakeya.Streamlined
