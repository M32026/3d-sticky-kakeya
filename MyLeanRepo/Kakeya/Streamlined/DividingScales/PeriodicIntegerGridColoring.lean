import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.ConflictColoring

/-!
# Periodic coloring of integer grid labels

Nested phase-space grids assign every object an integer tuple at every
distinguished level.  If two conflicting labels differ by less than one
fixed modulus in every coordinate, reducing all coordinates modulo that
modulus is a proper coloring.

This module is purely combinatorial.  It does not choose tube parents or
assert a geometric conflict bound.  A producer only has to supply an
injective integer label and the coordinatewise conflict-distance estimate.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- The canonical nonnegative residue of an integer as an element of `Fin`. -/
def periodicIntResidue
    (modulus : ℕ) (hmodulus : 0 < modulus) (value : ℤ) :
    Fin modulus :=
  ⟨Int.toNat (value % (modulus : ℤ)), by
    rw [Int.toNat_lt
      (Int.emod_nonneg _ (by exact_mod_cast hmodulus.ne'))]
    exact Int.emod_lt_of_pos _ (by exact_mod_cast hmodulus)⟩

/--
Two integers with the same residue and distance below the modulus are equal.
-/
lemma eq_of_periodicIntResidue_eq_of_abs_sub_lt
    {modulus : ℕ} (hmodulus : 0 < modulus)
    {first second : ℤ}
    (hresidue :
      periodicIntResidue modulus hmodulus first =
        periodicIntResidue modulus hmodulus second)
    (hclose : |first - second| < (modulus : ℤ)) :
    first = second := by
  have hvalue := congrArg Fin.val hresidue
  dsimp only [periodicIntResidue] at hvalue
  have hfirstNonneg :
      0 ≤ first % (modulus : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast hmodulus.ne')
  have hsecondNonneg :
      0 ≤ second % (modulus : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast hmodulus.ne')
  have hmod :
      first % (modulus : ℤ) =
        second % (modulus : ℤ) := by
    rw [← Int.natCast_toNat_eq_self.mpr hfirstNonneg,
      ← Int.natCast_toNat_eq_self.mpr hsecondNonneg]
    exact_mod_cast hvalue
  have hdvd : (modulus : ℤ) ∣ second - first :=
    Int.modEq_iff_dvd.mp hmod
  have hzero : second - first = 0 :=
    Int.eq_zero_of_abs_lt_dvd hdvd (by
      simpa [abs_sub_comm] using hclose)
  omega

/-- Coordinatewise periodic color of one multilevel integer label. -/
def periodicIntegerGridColor
    {levels dimension : ℕ}
    (modulus : ℕ) (hmodulus : 0 < modulus)
    (label : Fin levels → Fin dimension → ℤ) :
    Fin levels → Fin dimension → Fin modulus :=
  fun level coordinate =>
    periodicIntResidue modulus hmodulus (label level coordinate)

/--
Coordinatewise periodic colors are proper whenever conflict forces every
integer coordinate difference below the modulus.
-/
theorem periodicIntegerGridColor_proper
    {α : Type*}
    {levels dimension modulus : ℕ}
    (hmodulus : 0 < modulus)
    (label : α → Fin levels → Fin dimension → ℤ)
    (hlabel : Function.Injective label)
    (conflict : α → α → Prop)
    (hconflict :
      ∀ first second,
        conflict first second →
        ∀ level coordinate,
          |label first level coordinate -
              label second level coordinate| <
            (modulus : ℤ)) :
    ∀ first second,
      conflict first second →
      periodicIntegerGridColor modulus hmodulus (label first) =
          periodicIntegerGridColor modulus hmodulus (label second) →
        first = second := by
  intro first second hfirstSecond hcolor
  apply hlabel
  funext level coordinate
  apply eq_of_periodicIntResidue_eq_of_abs_sub_lt hmodulus
  · exact congrFun (congrFun hcolor level) coordinate
  · exact hconflict first second hfirstSecond level coordinate

/-- Exact number of coordinatewise periodic colors. -/
lemma periodicIntegerGridColor_card
    (levels dimension modulus : ℕ) :
    Fintype.card
        (Fin levels → Fin dimension → Fin modulus) =
      modulus ^ (levels * dimension) := by
  calc
    Fintype.card
        (Fin levels → Fin dimension → Fin modulus) =
        (modulus ^ dimension) ^ levels := by simp
    _ = modulus ^ (dimension * levels) :=
      (pow_mul modulus dimension levels).symm
    _ = modulus ^ (levels * dimension) := by
      rw [Nat.mul_comm dimension levels]

/--
One periodic color class is conflict-free and retains the reciprocal
`modulus^(levels * dimension)` share of any nonnegative `ENNReal` weight.
-/
theorem exists_heavy_periodicIntegerGridColor_class
    {α : Type*} [DecidableEq α]
    {levels dimension modulus : ℕ}
    (hmodulus : 0 < modulus)
    (indices : Finset α)
    (label : α → Fin levels → Fin dimension → ℤ)
    (hlabel : Function.Injective label)
    (weight : α → ENNReal)
    (conflict : α → α → Prop)
    (hconflict :
      ∀ first second,
        conflict first second →
        ∀ level coordinate,
          |label first level coordinate -
              label second level coordinate| <
            (modulus : ℤ)) :
    ∃ selected : Finset α,
      selected ⊆ indices ∧
      (∀ first ∈ selected, ∀ second ∈ selected,
        first ≠ second → ¬ conflict first second) ∧
      (∑ index ∈ indices, weight index) ≤
        (modulus ^ (levels * dimension) : ℕ) *
          ∑ index ∈ selected, weight index := by
  let Color := Fin levels → Fin dimension → Fin modulus
  have hColorCard :
      Fintype.card Color =
        modulus ^ (levels * dimension) :=
    periodicIntegerGridColor_card levels dimension modulus
  let colorEquiv :
      Color ≃ Fin (modulus ^ (levels * dimension)) :=
    (Fintype.equivFin Color).trans (Equiv.cast (by
      rw [hColorCard]))
  let color : α → Fin (modulus ^ (levels * dimension)) :=
    fun index =>
      colorEquiv
        (periodicIntegerGridColor modulus hmodulus (label index))
  have hcolorCount :
      0 < modulus ^ (levels * dimension) :=
    pow_pos hmodulus _
  have hproper :
      ∀ first ∈ indices, ∀ second ∈ indices,
        first ≠ second →
        conflict first second →
          color first ≠ color second := by
    intro first _ second _ hne hfirstSecond hcolor
    apply hne
    apply
      periodicIntegerGridColor_proper
        hmodulus label hlabel conflict hconflict
        first second hfirstSecond
    exact colorEquiv.injective hcolor
  rcases
      exists_heavy_conflict_free_color_class
        indices
        (modulus ^ (levels * dimension))
        hcolorCount color weight conflict hproper with
    ⟨chosen, hsubset, hfree, hmass⟩
  exact
    ⟨indices.filter fun index => color index = chosen,
      hsubset, hfree, hmass⟩

end Kakeya.Streamlined
