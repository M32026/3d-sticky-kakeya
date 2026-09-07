import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PreliminarySelection

/-!
# Proposition 6.2 metric parents: inserted CWA after the final core

The auxiliary mesh/ancestry classes are nodes of the augmented tree.  Its
node-density estimate transfers the pre-core inserted-level CWA to the final
core without another pruning step.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem pureWZ2_prop62_inserted_cwa_after_core
    {Leaf Aux : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Aux] [DecidableEq Aux]
    (label : Leaf → Aux)
    (selected core : Finset Leaf)
    (core_subset : core ⊆ selected)
    (depth : ℕ)
    (auxiliaryFiber : Aux → Finset Leaf)
    (fiber_eq :
      ∀ auxiliary,
        auxiliaryFiber auxiliary =
          Finset.univ.filter fun leaf =>
            label leaf = auxiliary)
    (node_density :
      ∀ auxiliary,
        (core ∩ auxiliaryFiber auxiliary).Nonempty →
          selected.card * (auxiliaryFiber auxiliary).card ≤
            2 ^ depth *
              (core ∩ auxiliaryFiber auxiliary).card *
              Fintype.card Leaf)
    (auxiliary : Aux)
    (core_nonempty :
      (core ∩ auxiliaryFiber auxiliary).Nonempty)
    (C volumeFactor : ENNReal)
    (predicate : Leaf → Prop)
    (ambient_cwa :
      (((auxiliaryFiber auxiliary).filter predicate).card :
        ENNReal) ≤
        C * volumeFactor *
          ((auxiliaryFiber auxiliary).card : ENNReal)) :
    (((core ∩ auxiliaryFiber auxiliary).filter predicate).card :
      ENNReal) ≤
      (C * (2 ^ depth : ENNReal) *
          (Fintype.card Leaf : ENNReal) *
          (selected.card : ENNReal)⁻¹) *
        volumeFactor *
        (((core ∩ auxiliaryFiber auxiliary).card : ENNReal)) := by
  have hcount :
      ((core ∩ auxiliaryFiber auxiliary).filter predicate).card ≤
        ((auxiliaryFiber auxiliary).filter predicate).card := by
    exact Finset.card_le_card <| by
      intro leaf hleaf
      have hfiltered := Finset.mem_filter.mp hleaf
      have hinter := Finset.mem_inter.mp hfiltered.1
      exact Finset.mem_filter.mpr
        ⟨hinter.2, hfiltered.2⟩
  have hcountENN :
      (((core ∩ auxiliaryFiber auxiliary).filter predicate).card :
        ENNReal) ≤
        (((auxiliaryFiber auxiliary).filter predicate).card :
          ENNReal) := by
    exact_mod_cast hcount
  have hdensityNat :=
    node_density auxiliary core_nonempty
  have hdensity :
      (selected.card : ENNReal) *
          ((auxiliaryFiber auxiliary).card : ENNReal) ≤
        (2 ^ depth : ENNReal) *
          ((core ∩ auxiliaryFiber auxiliary).card : ENNReal) *
          (Fintype.card Leaf : ENNReal) := by
    exact_mod_cast hdensityNat
  have selectedPos : 0 < selected.card := by
    rcases Finset.nonempty_def.mp core_nonempty with
      ⟨leaf, hleaf⟩
    have hleafSelected : leaf ∈ selected :=
      core_subset (Finset.mem_inter.mp hleaf).1
    exact Finset.card_pos.mpr ⟨leaf, hleafSelected⟩
  have selectedENNPos : 0 < (selected.card : ENNReal) := by
    exact_mod_cast selectedPos
  have selectedENNTop : (selected.card : ENNReal) ≠ ⊤ := by
    simp
  have fiberBound :
      ((auxiliaryFiber auxiliary).card : ENNReal) ≤
        (2 ^ depth : ENNReal) *
          ((core ∩ auxiliaryFiber auxiliary).card : ENNReal) *
          (Fintype.card Leaf : ENNReal) *
          (selected.card : ENNReal)⁻¹ := by
    calc
      ((auxiliaryFiber auxiliary).card : ENNReal) =
          ((selected.card : ENNReal) *
            (selected.card : ENNReal)⁻¹) *
              ((auxiliaryFiber auxiliary).card : ENNReal) := by
        rw [ENNReal.mul_inv_cancel
          selectedENNPos.ne' selectedENNTop]
        simp
      _ =
          ((selected.card : ENNReal) *
            ((auxiliaryFiber auxiliary).card : ENNReal)) *
              (selected.card : ENNReal)⁻¹ := by
        ring
      _ ≤
          ((2 ^ depth : ENNReal) *
            ((core ∩ auxiliaryFiber auxiliary).card : ENNReal) *
            (Fintype.card Leaf : ENNReal)) *
              (selected.card : ENNReal)⁻¹ := by
        gcongr
      _ = _ := rfl
  calc
    (((core ∩ auxiliaryFiber auxiliary).filter predicate).card :
        ENNReal) ≤
      (((auxiliaryFiber auxiliary).filter predicate).card :
        ENNReal) := hcountENN
    _ ≤
      C * volumeFactor *
        ((auxiliaryFiber auxiliary).card : ENNReal) :=
      ambient_cwa
    _ ≤
      C * volumeFactor *
        ((2 ^ depth : ENNReal) *
          ((core ∩ auxiliaryFiber auxiliary).card : ENNReal) *
          (Fintype.card Leaf : ENNReal) *
          (selected.card : ENNReal)⁻¹) := by
      gcongr
    _ =
      (C * (2 ^ depth : ENNReal) *
          (Fintype.card Leaf : ENNReal) *
          (selected.card : ENNReal)⁻¹) *
        volumeFactor *
        ((core ∩ auxiliaryFiber auxiliary).card : ENNReal) := by
      ring

end Kakeya.Assouad

end
