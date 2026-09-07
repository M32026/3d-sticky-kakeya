import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceParentMass

/-!
# Regularize selected incidence fibers below one coarse parent

After parent--function incidence degrees have been regularized, the selected
edge set need not retain every function in each original pointwise fiber.
This statement selects the fine rectangles whose selected rectangle-fiber
cardinality is at least half the parent average.  It preserves a quantitative
fraction of the parent edge mass and exposes one positive natural lower scale
for the later good-pair count.
-/

namespace Kakeya.Cinematic

def IncidenceRectangleFiberRegularizationStatement : Prop :=
  ∀ {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ],
    ∀ (edges : Finset (α × β)) (parent : β → γ) (coarse : γ)
      (fiberLower : ℕ) (logLoss fiberBound : ℝ),
      0 < fiberLower →
      1 ≤ logLoss →
      0 < fiberBound →
      (incidenceParentEdges edges parent coarse).Nonempty →
      ((incidenceRectangleSupport
          edges parent coarse).card : ℝ) * (fiberLower : ℝ) ≤
        logLoss *
          ((incidenceParentEdges edges parent coarse).card : ℝ) →
      (∀ rectangle ∈
          incidenceRectangleSupport edges parent coarse,
        ((incidenceRectangleFiber edges rectangle).card : ℝ) ≤
          fiberBound) →
      ∃ (pairLower : ℕ) (selectedRectangles : Finset β),
        pairLower =
          Nat.ceil ((fiberLower : ℝ) / (2 * logLoss)) ∧
        0 < pairLower ∧
        selectedRectangles =
          (incidenceRectangleSupport edges parent coarse).filter
            (fun rectangle =>
              (fiberLower : ℝ) / (2 * logLoss) ≤
                ((incidenceRectangleFiber
                  edges rectangle).card : ℝ)) ∧
        selectedRectangles.Nonempty ∧
        (((incidenceParentEdges
              edges parent coarse).card : ℝ) / 2) /
            fiberBound ≤
          (selectedRectangles.card : ℝ) ∧
        (fiberLower : ℝ) ≤
          2 * logLoss * (pairLower : ℝ) ∧
        ∀ rectangle ∈ selectedRectangles,
          pairLower ≤
            (incidenceRectangleFiber edges rectangle).card

end Kakeya.Cinematic
