import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# Fine rectangle and good-pair incidence bound
-/

namespace Kakeya.Cinematic

theorem fine_pair_incidence_bound :
    FinePairIncidenceBoundStatement := by
  intro hPair ρ σ _ _ fine pairs incidence goodCount perPair hLower hUpper
  have hCount :=
    hPair ρ (Fin 3 × σ) fine ((Finset.univ : Finset (Fin 3)).product pairs)
      (fun R => (Finset.univ : Finset (Fin 3)).product (incidence R))
      (goodCount ^ 2) perPair
      (by
        intro R hR
        have hinter :
            (Finset.univ : Finset (Fin 3)).product pairs ∩
                (Finset.univ : Finset (Fin 3)).product (incidence R) =
              (Finset.univ : Finset (Fin 3)).product
                (pairs ∩ incidence R) := by
          ext pair
          simp
        rw [hinter]
        simpa [Finset.card_product] using hLower R hR)
      (by
        rintro ⟨i, p⟩ hp
        have hp' : p ∈ pairs := (Finset.mem_product.mp hp).2
        have hfilter :
            fine.filter (fun R =>
                (i, p) ∈
                  (Finset.univ : Finset (Fin 3)).product
                    (incidence R)) =
              fine.filter (fun R => p ∈ incidence R) := by
          ext R
          simp
        rw [hfilter]
        exact hUpper p hp')
  simpa [Finset.card_product, Nat.mul_assoc] using hCount

end Kakeya.Cinematic
