import Kakeya.DimensionThree.Final

/-! Final checks for the proved Sticky boundary and unconditional 3D theorem. -/

#check (Kakeya.Integration.stickyFrostmanEstimate_of_finrank_three :
  Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 →
    StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)))

#check (KakeyaDimensionThree_of_stickyFrostmanEstimate :
  StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)) →
    KakeyaSetConjecture 3)

#check (KakeyaDimensionThree : KakeyaSetConjecture 3)

#print axioms Kakeya.Integration.stickyFrostmanEstimate_of_finrank_three
#print axioms KakeyaDimensionThree_of_stickyFrostmanEstimate
#print axioms KakeyaDimensionThree
