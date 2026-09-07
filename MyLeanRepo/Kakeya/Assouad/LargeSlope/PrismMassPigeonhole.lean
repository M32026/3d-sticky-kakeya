import MyLeanRepo.Kakeya.Assouad.Statements

/-! WZ2 Section 6, Step 4: finite prism-mass pigeonholing. -/

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem prism_mass_pigeonhole :
    PrismMassPigeonholeStatement := by
  intro ι κ _ _ tubes prisms hprisms pieceMass total cap htotal hcap
  let active : κ → Finset ι :=
    fun j => tubes.filter (fun i => pieceMass i j ≠ 0)
  have hpiece :
      ∀ j ∈ prisms,
        (∑ i ∈ tubes, pieceMass i j) ≤
          ((active j).card : ENNReal) * cap := by
    intro j hj
    have hsum :
        (∑ i ∈ tubes, pieceMass i j) =
          ∑ i ∈ active j, pieceMass i j := by
      have hrewrite :
          (∑ i ∈ tubes, pieceMass i j) =
            ∑ i ∈ tubes,
              (if pieceMass i j ≠ 0 then pieceMass i j else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : pieceMass i j ≠ 0
        · rw [if_pos h]
        · have h' : pieceMass i j = 0 := by tauto
          rw [if_neg h, h']
      rw [hrewrite, ← Finset.sum_filter]
    rw [hsum]
    have hbound :
        ∑ i ∈ active j, pieceMass i j ≤
          ∑ _i ∈ active j, cap := by
      apply Finset.sum_le_sum
      intro i hi
      exact hcap i (Finset.mem_filter.mp hi).1 j hj
    calc
      ∑ i ∈ active j, pieceMass i j
          ≤ ∑ _i ∈ active j, cap := hbound
      _ = ((active j).card : ENNReal) * cap := by
        rw [Finset.sum_const]
        ring
  have htotal' :
      total ≤ ∑ j ∈ prisms, ∑ i ∈ tubes, pieceMass i j := by
    rw [← Finset.sum_comm]
    exact htotal
  have hsum :
      total ≤ ∑ j ∈ prisms, (((active j).card : ENNReal) * cap) := by
    exact htotal'.trans (Finset.sum_le_sum fun j hj => hpiece j hj)
  obtain ⟨j₀, hj₀, hmax⟩ :=
    Finset.exists_max_image prisms (fun j : κ => (active j).card) hprisms
  have hactive :
      ∑ j ∈ prisms, ((active j).card : ENNReal) ≤
        (prisms.card : ENNReal) * ((active j₀).card : ENNReal) := by
    calc
      ∑ j ∈ prisms, ((active j).card : ENNReal)
          ≤ ∑ _j ∈ prisms, ((active j₀).card : ENNReal) := by
            apply Finset.sum_le_sum
            intro j hj
            exact_mod_cast hmax j hj
      _ = (prisms.card : ENNReal) *
          ((active j₀).card : ENNReal) := by
            rw [Finset.sum_const]
            ring
  have hsum' :
      total ≤ cap * ∑ j ∈ prisms, ((active j).card : ENNReal) := by
    calc
      total ≤ ∑ j ∈ prisms,
          (((active j).card : ENNReal) * cap) := hsum
      _ = cap * ∑ j ∈ prisms,
          ((active j).card : ENNReal) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
  refine ⟨j₀, hj₀, ?_⟩
  calc
    total ≤ cap * ∑ j ∈ prisms,
        ((active j).card : ENNReal) := hsum'
    _ ≤ cap * ((prisms.card : ENNReal) *
        ((active j₀).card : ENNReal)) := by gcongr
    _ = (prisms.card : ENNReal) * cap *
        ((tubes.filter fun i => pieceMass i j₀ ≠ 0).card : ENNReal) := by
          change cap * ((prisms.card : ENNReal) *
              ((active j₀).card : ENNReal)) =
            (prisms.card : ENNReal) * cap *
              ((active j₀).card : ENNReal)
          ring

end Kakeya.Assouad
