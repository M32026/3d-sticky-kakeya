/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ConvexBody.ContainerChange
public import Kakeya.AffineMap

/-!
# The transport chain of item (iv), read in source coordinates

`ConvexSpaceBody.le_frostmanConstIn_of_transport_of_source_doubling`
(`Kakeya/ConvexBody/ContainerChange.lean`) states the surviving content of item (iv) of
`Kakeya.ml1Boot.exists_fineNormalization_lower` entirely inside the *normalized* space: its
source family is `𝕎 = Ψ ∘ 𝕌` and its inner container is `Q = Ψ(T_σ)`.

What the hypothesis `hFb` of that lemma supplies is the same data one affine map earlier: the
Frostman lower bound and the doubling clause are read on `𝕌` and `T_σ` in the *source* space.
Since `Ψ` is an affine equivalence, both readings are literally equal
(`Kakeya.densityIn_affineImage`, `ConvexSpaceBody.frostmanConstIn_affineImage`), and this file
composes the two steps so that item (iv) can quote its hypotheses in the coordinates it has
them in.

The pullback `Ks` of the outer container is the source body the doubling clause of `hFb` is
instantiated at: `hFb` quantifies its clause over *all* enlargements `D ⊇ T_σ` of bounded
volume, and `Ks = Ψ⁻¹(2 · T_ρ)` is one such `D`.
-/

@[expose] public section

open MeasureTheory Kakeya

namespace ConvexSpaceBody

section AffineTransport

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}
  {s : Finset ι} {V : ι → ConvexSpaceBody E} {A C : ENNReal}

/-- **Item (iv)'s inequality with its hypotheses quoted in source coordinates.**

`ConvexSpaceBody.le_frostmanConstIn_of_transport_of_source_doubling` precomposed with the affine
equivalence `L = Ψ`.  The Frostman lower bound `hsrc` and the doubling clause `hdoub` are the two
conjuncts of `hFb` of `Kakeya.ml1Boot.exists_fineNormalization_lower`, read at the source family
`Ws = 𝕌` and the source containers `Qs = T_σ` and `Ks = Ψ⁻¹(2 · T_ρ)`; every other hypothesis is
about the normalized family and the two normalized containers.

Neither step of the affine passage costs anything: `Kakeya.familyIn_affineImage`,
`Kakeya.densityIn_affineImage` and `ConvexSpaceBody.frostmanConstIn_affineImage` are exact
equalities. -/
theorem le_frostmanConstIn_of_affine_transport {Cd Cv : ENNReal} (hC : 1 ≤ C)
    (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L)
    (Ws : ι → ConvexSpaceBody E) (Qs Ks : ConvexSpaceBody E) (Q' : ConvexSpaceBody E)
    (hK0 : volume (Ks.affineImage L.toAffineMap hcont).carrier ≠ 0)
    (hKtop : volume (Ks.affineImage L.toAffineMap hcont).carrier ≠ ⊤)
    (hQ0 : volume (Qs.affineImage L.toAffineMap hcont).carrier ≠ 0)
    (hQtop : volume (Qs.affineImage L.toAffineMap hcont).carrier ≠ ⊤)
    (hQQ' : Qs.affineImage L.toAffineMap hcont ≤ Q')
    (hQ'K : Q' ≤ Ks.affineImage L.toAffineMap hcont)
    (hVQ' : ∀ i ∈ familyIn s (fun i => (Ws i).affineImage L.toAffineMap hcont)
        (Qs.affineImage L.toAffineMap hcont), V i ≤ Q')
    (hWV : ∀ i ∈ s, (Ws i).affineImage L.toAffineMap hcont ≤ V i)
    (hvol : ∀ i ∈ s, volume (V i).carrier
      ≤ C * volume ((Ws i).affineImage L.toAffineMap hcont).carrier)
    (hdilate : ∀ K'' ≤ Q', ∃ M ≤ Q', K'' ≤ M ∧ volume M.carrier ≤ C * volume K''.carrier ∧
      ∀ i ∈ familyIn s (fun i => (Ws i).affineImage L.toAffineMap hcont)
          (Qs.affineImage L.toAffineMap hcont),
        (Ws i).affineImage L.toAffineMap hcont ≤ K'' → V i ≤ M)
    (hVK : ∀ i ∈ s, (Ws i).affineImage L.toAffineMap hcont
      ≤ Qs.affineImage L.toAffineMap hcont → V i ≤ Ks.affineImage L.toAffineMap hcont)
    (hvolQK : volume (Ks.affineImage L.toAffineMap hcont).carrier
      ≤ Cv * volume (Qs.affineImage L.toAffineMap hcont).carrier)
    (hdoub : densityIn s Ws Ks ≤ Cd * densityIn s Ws Qs)
    (hsrc : A ≤ frostmanConstIn (familyIn s Ws Qs) Ws Qs) :
    A ≤ C ^ 2 * (C * Cd * Cv)
      * frostmanConstIn (familyIn s V (Ks.affineImage L.toAffineMap hcont)) V
          (Ks.affineImage L.toAffineMap hcont) := by
  have hdoub' : densityIn s (fun i => (Ws i).affineImage L.toAffineMap hcont)
        (Ks.affineImage L.toAffineMap hcont)
      ≤ Cd * densityIn s (fun i => (Ws i).affineImage L.toAffineMap hcont)
          (Qs.affineImage L.toAffineMap hcont) := by
    rw [Kakeya.densityIn_affineImage s Ws Ks L hcont,
      Kakeya.densityIn_affineImage s Ws Qs L hcont]
    exact hdoub
  have hsrc' : A ≤ frostmanConstIn
      (familyIn s (fun i => (Ws i).affineImage L.toAffineMap hcont)
        (Qs.affineImage L.toAffineMap hcont))
      (fun i => (Ws i).affineImage L.toAffineMap hcont)
      (Qs.affineImage L.toAffineMap hcont) := by
    rw [Kakeya.familyIn_affineImage s Ws Qs L hcont,
      ConvexSpaceBody.frostmanConstIn_affineImage (familyIn s Ws Qs) Ws Qs L hcont]
    exact hsrc
  exact le_frostmanConstIn_of_transport_of_source_doubling (W := fun i =>
      (Ws i).affineImage L.toAffineMap hcont) (Q' := Q')
    hC hK0 hKtop hQ0 hQtop hQQ' hQ'K hVQ' hWV hvol hdilate hVK hvolQK hdoub' hsrc'

end AffineTransport

end ConvexSpaceBody
