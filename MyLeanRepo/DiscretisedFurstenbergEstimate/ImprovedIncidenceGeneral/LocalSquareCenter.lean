module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes

@[expose] public section

noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DiscretisedFurstenbergEstimate

/-- Center of a dyadic square in the Euclidean plane. -/
noncomputable def localSquareCenter {n : ℕ} (q : DyadicSquare n) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun i : Fin 2 =>
    if i = 0 then ((q.i : ℝ) + 1 / 2) * dyadicDelta n
    else ((q.j : ℝ) + 1 / 2) * dyadicDelta n

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

end
