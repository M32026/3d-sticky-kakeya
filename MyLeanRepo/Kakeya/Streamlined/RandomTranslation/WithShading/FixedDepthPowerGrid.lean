import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.ScaleInterpolation
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.MultiscaleShifts

/-!
# Dependency-light fixed-depth power grid

This module contains only the numerical grid and tail-radius data shared by
the strict compatibility construction and the native dilated hard branch.
It deliberately does not import label maps, uniform-structure translation, or
the historical multiscale cover implementation.
-/

noncomputable section

open BigOperators
open Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/-- A fixed-depth descending power grid with a compatible positive tail
schedule. -/
structure FixedDepthPowerGrid (delta : ℝ) (N : ℕ) where
  scale : Fin (N + 1) → AdmissibleScale delta
  radius : Fin N → ℝ
  hpower :
    ∀ k : Fin (N + 1),
      ENNReal.ofReal (scale k).1 =
        RandomTranslation.scaleGrid delta N k.val
  hfirst : (scale 0).1 = 1
  hlast : (scale (Fin.last N)).1 = delta
  hstrict :
    ∀ k : Fin N,
      (scale (Fin.succ k)).1 <
        (scale (Fin.castSucc k)).1
  hratio :
    ∀ k : Fin N,
      ENNReal.ofReal (scale (Fin.castSucc k)).1 =
        Kakeya.realRpowENN delta (-(1 / (N : ℝ))) *
          ENNReal.ofReal (scale (Fin.succ k)).1
  hradius_pos : ∀ k, 0 < radius k
  htail :
    ∀ k : Fin N,
      (∑ j ∈ Finset.univ.filter
          (fun j : Fin N => k.val ≤ j.val),
          radius j) ≤
        (scale (Fin.castSucc k)).1 -
          (scale (Fin.succ k)).1
  htotal : multiscaleTotalRadius radius ≤ 1
  hbracket :
    ∀ rho : AdmissibleScale delta,
      ∃ k : Fin N,
        (scale (Fin.succ k)).1 ≤ rho.1 ∧
          rho.1 ≤ (scale (Fin.castSucc k)).1

namespace FixedDepthPowerGrid

variable {delta : ℝ} {N : ℕ}

/-- Lower endpoint at one descending grid cut. -/
def fineScale (grid : FixedDepthPowerGrid delta N)
    (k : Fin N) : AdmissibleScale delta :=
  grid.scale (Fin.succ k)

/-- Upper endpoint at one descending grid cut. -/
def coarseScale (grid : FixedDepthPowerGrid delta N)
    (k : Fin N) : ℝ :=
  (grid.scale (Fin.castSucc k)).1

/-- The squared coarse-to-fine scale ratio at one descending cut. -/
def adjacentScaleSquare (grid : FixedDepthPowerGrid delta N)
    (k : Fin N) : ENNReal :=
  (ENNReal.ofReal (grid.coarseScale k) /
      ENNReal.ofReal (grid.fineScale k).1) ^ 2

end FixedDepthPowerGrid

/-- Compatibility name for the squared scale ratio used by the fixed-depth
copy-count construction. -/
abbrev fixedDepthAdjacentScaleSquare
    {delta : ℝ} {N : ℕ}
    (grid : FixedDepthPowerGrid delta N)
    (k : Fin N) : ENNReal :=
  grid.adjacentScaleSquare k

end Kakeya.Streamlined.RandomTranslation.WithShading

end
