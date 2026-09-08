import Comparator.SolutionStatements
import Kakeya.DimensionThree.Final

open MeasureTheory

local instance : Fintype (Fin 3) := Fin.fintype 3

/-- **Wang--Zahl's three-dimensional Kakeya theorem.** Every Kakeya set in
three-dimensional Euclidean space has full Hausdorff dimension. -/
theorem wang_zahl_kakeya_dimH {K : Set Space} (hK : IsKakeya K) :
    dimH K = 3 := by
  apply KakeyaDimensionThree K
  refine ⟨hK.1, ?_⟩
  intro v hv
  obtain ⟨x, hx⟩ := hK.2 v hv
  refine ⟨x, ?_⟩
  rintro y ⟨t, ht, rfl⟩
  simpa [AffineMap.lineMap_apply_module', add_comm] using hx t ht
