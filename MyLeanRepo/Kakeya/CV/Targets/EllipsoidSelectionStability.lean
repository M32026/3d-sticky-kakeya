import MyLeanRepo.Kakeya.CV.Statements

/-!
# Stability of same-colour ellipsoid selection

Carbery--Valdimarsson Lemma 10, isolating the continuity argument used in the
antipodal separation step.

## Proof outline

The proof chains homothetic closeness relations:

1. `AreHomotheticallyCloseAt.symm`: if `A` is α-close to `B`, then `B` is α-close to `A`
   (for `α ≠ 0`). Proved by applying the inverse dilation to both inclusions.

2. `AreHomotheticallyCloseAt.trans`: if `A` is α-close to `B` and `B` is β-close to `C`,
   then `A` is (αβ)-close to `C`. Proved using `dilateAbout_comp`.

3. Main chain: for eventually all `m`,
   `Eseq m` ↔ `Kseq m` ↔ `K` ↔ `E` with factors α, α, α,
   yielding α³-closeness of `Eseq m` to `E`.

4. The net's α³-separation hypothesis for same-colour ellipsoids gives equality.
-/

namespace Kakeya.CV

theorem ellipsoid_selection_stability :
    EllipsoidSelectionStabilityStatement := by
  intro α N net colour z K Kseq E Eseq hα hconv hE_net hEseq_net hcolour hE hEseq hsep
  have hne : α ≠ 0 := by linarith
  have hconv_eventually : ∀ᶠ m in Filter.atTop,
      AreHomotheticallyCloseAt z α (Kseq m) K := hconv α hα
  filter_upwards [hconv_eventually] with m hconv_m
  let Em := ellipsoidCarrier (Eseq m)
  let Ecar := ellipsoidCarrier E
  have h1 : AreHomotheticallyCloseAt z α Em (Kseq m) :=
    (hEseq m).symm hne
  have h2 : AreHomotheticallyCloseAt z α (Kseq m) K := hconv_m
  have h3 : AreHomotheticallyCloseAt z α K Ecar := hE
  have h4 : AreHomotheticallyCloseAt z (α * α) Em K := h1.trans h2
  have h5 : AreHomotheticallyCloseAt z (α * α * α) Em Ecar := h4.trans h3
  have h6 : α * α * α = α ^ 3 := by ring
  rw [h6] at h5
  exact hsep (Eseq m) (hEseq_net m) E hE_net (hcolour m) h5

end Kakeya.CV
