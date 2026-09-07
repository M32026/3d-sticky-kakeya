import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions

/-!
# Aggregate mass retention for carrierwise pruning

These lemmas separate two generic measure-theoretic steps from the numerical
bookkeeping of a concrete pruning:

1. sum a uniform carrierwise deletion bound over a finite shading;
2. convert `Y.mass ≤ Z.mass + loss * Y.mass` into
   `keep * Y.mass ≤ Z.mass` when `keep + loss = 1`.
-/

namespace Kakeya.Assouad

noncomputable section

open MeasureTheory Set

/--
A subshading whose deleted part in every carrier has volume at most `error`
loses at most `F.card * error` aggregate shaded mass.
-/
lemma shading_mass_le_subshading_mass_add_error
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y Z : Kakeya.Streamlined.TubeShading F}
    (hsub : IsSubshading Z Y)
    (error : ENNReal)
    (herror :
      ∀ index : Fin F.card,
        volume (Y.carrier index \ Z.carrier index) ≤ error) :
    Y.mass ≤ Z.mass + (F.card : ENNReal) * error := by
  have hcarrier :
      ∀ index : Fin F.card,
        volume (Y.carrier index) ≤
          volume (Z.carrier index) +
            volume (Y.carrier index \ Z.carrier index) := by
    intro index
    have hunion :
        Z.carrier index ∪
            (Y.carrier index \ Z.carrier index) =
          Y.carrier index := by
      ext point
      constructor
      · intro hpoint
        rcases hpoint with hpointZ | hpointDiff
        · exact hsub index hpointZ
        · exact hpointDiff.1
      · intro hpoint
        by_cases hpointZ : point ∈ Z.carrier index
        · exact Or.inl hpointZ
        · exact Or.inr ⟨hpoint, hpointZ⟩
    calc
      volume (Y.carrier index) =
          volume
            (Z.carrier index ∪
              (Y.carrier index \ Z.carrier index)) :=
        congrArg volume hunion.symm
      _ ≤
          volume (Z.carrier index) +
            volume (Y.carrier index \ Z.carrier index) :=
        MeasureTheory.measure_union_le
          (μ := volume)
          (Z.carrier index)
          (Y.carrier index \ Z.carrier index)
  calc
    Y.mass =
        ∑ index : Fin F.card,
          volume (Y.carrier index) := rfl
    _ ≤
        ∑ index : Fin F.card,
          (volume (Z.carrier index) +
            volume (Y.carrier index \ Z.carrier index)) :=
      Finset.sum_le_sum fun index _ => hcarrier index
    _ =
        Z.mass +
          ∑ index : Fin F.card,
            volume (Y.carrier index \ Z.carrier index) := by
      rw [Finset.sum_add_distrib]
      rfl
    _ ≤
        Z.mass + ∑ _index : Fin F.card, error := by
      have hsum :
          (∑ index : Fin F.card,
              volume (Y.carrier index \ Z.carrier index)) ≤
            ∑ _index : Fin F.card, error :=
        Finset.sum_le_sum fun index _ => herror index
      exact add_le_add_right hsum Z.mass
    _ =
        Z.mass + (F.card : ENNReal) * error := by
      simp [Finset.sum_const]

/--
Cancel a finite removed-mass allowance from both sides of a retention
inequality.
-/
lemma retained_mass_of_mass_le_add_loss
    {sourceMass retainedMass : ENNReal}
    {keep loss : ENNReal}
    (hsourceFinite : sourceMass ≠ ⊤)
    (hlossFinite : loss ≠ ⊤)
    (hpartition : keep + loss = 1)
    (hmass :
      sourceMass ≤ retainedMass + loss * sourceMass) :
    keep * sourceMass ≤ retainedMass := by
  have hlossMassFinite : loss * sourceMass ≠ ⊤ :=
    ENNReal.mul_ne_top hlossFinite hsourceFinite
  apply
    (ENNReal.add_le_add_iff_right hlossMassFinite).mp
  calc
    keep * sourceMass + loss * sourceMass =
        (keep + loss) * sourceMass := by
      rw [add_mul]
    _ = sourceMass := by rw [hpartition, one_mul]
    _ ≤ retainedMass + loss * sourceMass := hmass

/--
Combine a raw aggregate deletion bound with a fractional error budget.
-/
lemma retained_mass_of_error_le_fraction
    {sourceMass retainedMass error : ENNReal}
    {keep loss : ENNReal}
    (hsourceFinite : sourceMass ≠ ⊤)
    (hlossFinite : loss ≠ ⊤)
    (hpartition : keep + loss = 1)
    (hmass : sourceMass ≤ retainedMass + error)
    (herror : error ≤ loss * sourceMass) :
    keep * sourceMass ≤ retainedMass := by
  apply retained_mass_of_mass_le_add_loss
    hsourceFinite hlossFinite hpartition
  exact hmass.trans <| by
    gcongr

/--
Convert a one-sided aggregate error decomposition into a truncated-subtraction
bound.
-/
lemma dropped_mass_of_mass_le_add_error
    {sourceMass retainedMass error : ENNReal}
    (hmass : sourceMass ≤ retainedMass + error) :
    sourceMass - retainedMass ≤ error := by
  rw [tsub_le_iff_right]
  simpa [add_comm] using hmass

end

end Kakeya.Assouad
