/-
# Quotient Chain Map for RP^n

Provides the chain map `C_*(S^n; Z/2) → C_*(RP^n; Z/2)` induced by the
quotient map, and the lifting lemma for singular simplices.

The kernel equality and SES are in `QuotientKernel.lean`.

## Whiteprint Node
- `degree_route/quotient_ses`
-/

import MyLeanRepo.Kakeya.BorsukUlam.TransferFull
import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.RealProjectiveSpace
import Mathlib.Topology.Homotopy.Lifting

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial Preadditive
open SeedMathlib.AlgebraicTopology.Degree
open BorsukUlamBackup
open BorsukUlam.BackupRoute

variable {n : ℕ}

namespace BorsukUlam.QuotientSES

/-! ### Chain map induced by the quotient map -/

/-- Continuity of the quotient map. -/
lemma continuous_quotientMap : Continuous (quotientMap n) := by
  exact { isOpen_preimage := fun _ hs => hs }

/-- The quotient map as a continuous map. -/
def quotientCmap : C(Sphere n, RPType n) :=
  ⟨quotientMap n, continuous_quotientMap⟩

/-- The singular simplicial set of RP^n. -/
abbrev rpSSet (n : ℕ) := TopCat.toSSet.obj (TopCat.of (RPType n))

/-- The type of singular k-simplices of RP^n. -/
abbrev RPSimplices (n k : ℕ) := rpSSet n _⦋k⦌

/-- The singular chain complex of RP^n with Z/2 coefficients. -/
abbrev ChainRP2 (n : ℕ) : ChainComplex (ModuleCat (ZMod 2)) ℕ :=
  chainFunctor2.obj (TopCat.of (RPType n))

/-- The chain map C_*(S^n) → C_*(RP^n) induced by the quotient map. -/
def quotientChainMap (n : ℕ) : ChainSphere2 n ⟶ ChainRP2 n :=
  chainFunctor2.map (TopCat.ofHom quotientCmap)

/-! ### Lifting singular simplices -/

/-- The standard topological k-simplex is contractible. -/
instance stdSimplex_contractible (k : ℕ) :
    ContractibleSpace (stdSimplex ℝ (Fin (k + 1))) := by
  have h_conv : Convex ℝ (stdSimplex ℝ (Fin (k + 1))) := convex_stdSimplex ℝ (Fin (k + 1))
  have h_ne : (stdSimplex ℝ (Fin (k + 1))).Nonempty := Set.Nonempty.of_subtype
  exact Convex.contractibleSpace h_conv h_ne

/-- The standard simplex is locally path connected (as a convex set). -/
instance stdSimplex_locPathConnected (k : ℕ) :
    LocPathConnectedSpace (stdSimplex ℝ (Fin (k + 1))) := by
  letI : NormedSpace ℝ (Fin (k + 1) → ℝ) := by infer_instance
  let _i : Convex ℝ (stdSimplex ℝ (Fin (k + 1))) := convex_stdSimplex ℝ (Fin (k + 1))
  exact Convex.locPathConnectedSpace (Fin (k + 1) → ℝ) _i

/-- The standard simplex is simply connected (contractible). -/
instance stdSimplex_simplyConnected (k : ℕ) :
    SimplyConnectedSpace (stdSimplex ℝ (Fin (k + 1))) :=
  SimplyConnectedSpace.ofContractible (stdSimplex ℝ (Fin (k + 1)))

/-- Every singular k-simplex of RP^n lifts to S^n.

Since the standard simplex is contractible and the quotient map is a covering,
any map from the simplex to RP^n lifts to S^n. -/
lemma lift_simplex (k : ℕ) (σ : C(stdSimplex ℝ (Fin (k + 1)), RPType n)) :
    ∃ (sigma_lift : C(stdSimplex ℝ (Fin (k + 1)), Sphere n)),
      quotientCmap.comp sigma_lift = σ := by
  let Δk := stdSimplex ℝ (Fin (k + 1))
  classical
  let t0 : Δk := Classical.arbitrary Δk
  let y0 : RPType n := σ t0
  have h_exists_rep : ∃ (x0 : Sphere n), quotientMap n x0 = y0 :=
    Quotient.exists_rep y0
  rcases h_exists_rep with ⟨x0, hx0⟩
  have hcov : IsCoveringMap (quotientMap n) := by
    exact quotientIsCovering (n := n)
  have h_main : ∃! (F : C(Δk, Sphere n)), F t0 = x0 ∧
      (quotientMap n) ∘ F = σ :=
    hcov.existsUnique_continuousMap_lifts σ t0 x0 hx0
  rcases h_main with ⟨F, ⟨hF0, hF_lifts⟩, _⟩
  refine ⟨F, ?_⟩
  apply ContinuousMap.ext
  intro a
  have h_eq : (quotientCmap.comp F) a = σ a := by
    simpa [quotientCmap, ContinuousMap.comp_apply] using congr_fun hF_lifts a
  exact h_eq

end BorsukUlam.QuotientSES

end
