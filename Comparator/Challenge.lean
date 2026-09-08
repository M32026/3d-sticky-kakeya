import Comparator.Statements

local instance : Fintype (Fin 3) := Fin.fintype 3

/-- **Wang--Zahl's three-dimensional Kakeya theorem.** Every Kakeya set in
three-dimensional Euclidean space has full Hausdorff dimension. -/
theorem wang_zahl_kakeya_dimH {K : Set Space} (hK : IsKakeya K) :
    dimH K = 3 := by
  sorry
