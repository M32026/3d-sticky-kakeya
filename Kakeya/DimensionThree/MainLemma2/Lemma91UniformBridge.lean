/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2Ptw
public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyUniform
public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyClosed

/-!
# The `Lemma91Uniform` crossing, pinned

**The finding this file records.**  Four declarations of the GWZ reduction exist **twice**, in two
namespaces, with character-identical bodies:

| declaration | `Kakeya.VNSUniform` | `Kakeya.ML2Assembly` |
|---|---|---|
| `VNSBody`                  | `VeryNotStickyUniform.lean:84`  | `Reduction/Assembly.lean:78`  |
| `Lemma91`                  | `VeryNotStickyUniform.lean:104` | `Reduction/Assembly.lean:98`  |
| `Lemma91Uniform`           | `VeryNotStickyUniform.lean:118` | `Reduction/Assembly.lean:125` |
| `lemma91_of_lemma91Uniform`| `VeryNotStickyUniform.lean:124` | `Reduction/Assembly.lean:134` |

The two declaring files sit on **separate branches of the import graph** —
`Reduction/Assembly.lean` imports `Kakeya.DimensionThree.MainLemma2.VeryNotStickyCase`, not
`VeryNotStickyUniform` — so neither sees the other's copy, and **nothing in the development
composes the producer with the consumer.**  The producer of the uniform companion,
`Kakeya.VNSUniform.lemma91Uniform_of_uniformPlankExponent`, delivers the `VNSUniform` copy; its
only consumer, `Kakeya.ML2Assembly.pointwiseCore_of_lemma91Uniform_of_geometricCore`, asks for
the `ML2Assembly` copy.  Read as names, the only proved supplier does not feed the only consumer.

**Read as terms, it does, and the compiler says so here.**  Both are plain `def`s — neither
`irreducible` nor `opaque` — and their bodies elaborate to the same term, so the two `Prop`s are
definitionally equal and a term of either *is* a term of the other, with no transport:
`Kakeya.ML2Bridge.lemma91Uniform_eq` is `rfl` and
`Kakeya.ML2Bridge.assemblyLemma91Uniform_of_vnsUniform` is `id`.  **So there is no gap in the
route.**

**But the bridge is definitional, not named, and that is a nameable fragility.**  Marking either
`Lemma91Uniform` — or either `VNSBody`, on which they depend — `@[irreducible]`, or letting one
body drift from the other by a single byte, severs the route *silently*: nothing would fail to
compile, because nothing composes them.  This file removes that silence.  The three `rfl`
tripwires below break immediately on any divergence, and
`Kakeya.ML2Bridge.mainLemma2Statement_of_uniformPlankExponent` makes the crossing **load-bearing
in the build** by actually performing it, end to end, onto the protected statement.

**Nothing is deduplicated here, deliberately.**  Merging the two clusters would edit two files
that other work holds; the disconnect-that-wasn't is the finding, and a pin is the right size of
response to it.

## What the end-to-end composition says

`Kakeya.ML2Bridge.mainLemma2Statement_of_uniformPlankExponent` is the whole GWZ route in one
type: from the `β`-uniform plank-Frostman residual, the windowed geometric core, and the
small-cardinality hypothesis, the protected Main Lemma 2 follows.  It assumes nothing new — all
three are obligations the development already carries — and it lands on
`Kakeya.VNSUniform.MainLemma2Statement`, which `Kakeya.DimensionThree.MainLemma2Ptw`'s Tripwires
1 and 2 pin to `Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate` in **both**
directions.  So it is a statement about the protected declaration, not about a paraphrase of it.
-/

@[expose] public section

namespace Kakeya.ML2Bridge

universe u

/-! ## The three `rfl` tripwires -/

/-- **Tripwire.**  The two `VNSBody`s are the same `Prop`-valued function.  This is the base of
the crossing: `Lemma91Uniform` is stated in terms of `VNSBody`, so if these diverge the rest
does too. -/
theorem vnsBody_eq : VNSUniform.VNSBody.{u} = ML2Assembly.VNSBody.{u} := rfl

/-- **Tripwire.**  The two `Lemma91`s are the same `Prop`. -/
theorem lemma91_eq : VNSUniform.Lemma91.{u} = ML2Assembly.Lemma91.{u} := rfl

/-- **Tripwire.**  The two `Lemma91Uniform`s are the same `Prop`.  This is the one the route
depends on: `Kakeya.VNSUniform.lemma91Uniform_of_uniformPlankExponent` produces the left-hand
side and `Kakeya.ML2Assembly.pointwiseCore_of_lemma91Uniform_of_geometricCore` consumes the
right-hand side. -/
theorem lemma91Uniform_eq : VNSUniform.Lemma91Uniform.{u} = ML2Assembly.Lemma91Uniform.{u} := rfl

/-! ## The named bridges -/

/-- The `VNSUniform` uniform companion **is** the `ML2Assembly` one — no transport, no coercion,
no rewriting.  Named so that a reader crossing the two namespaces has something to cite other
than definitional unfolding. -/
theorem assemblyLemma91Uniform_of_vnsUniform (h : VNSUniform.Lemma91Uniform.{u}) :
    ML2Assembly.Lemma91Uniform.{u} := h

/-- The converse crossing, equally free. -/
theorem vnsUniformLemma91Uniform_of_assembly (h : ML2Assembly.Lemma91Uniform.{u}) :
    VNSUniform.Lemma91Uniform.{u} := h

/-! ## The crossing, performed -/

/-- **The GWZ route end to end, and the reason the crossing is load-bearing in the build.**

From the three obligations the development currently carries —
`Kakeya.VNSUniform.UniformPlankExponent` on every window, `Kakeya.ML2Assembly.GeometricCore`
and `Kakeya.ML2Assembly.SmallCardHyp` — the protected Main Lemma 2 follows, by composing

* `Kakeya.VNSUniform.lemma91Uniform_of_uniformPlankExponent` (produces the `VNSUniform` copy),
* `Kakeya.ML2Assembly.pointwiseCore_of_lemma91Uniform_of_geometricCore` (consumes the
  `ML2Assembly` copy — this application is the crossing),
* `Kakeya.ML2Ptw.protected_statement_of_pointwiseCore` (the live two-hypothesis assembly).

Nothing new is assumed; the content is that these three lemmas *compose*, which no other
declaration in the development checks.

In other words the *assembly* half of the GWZ route is
axiom-clean and every open obligation on the route is upstream, inside the Section-9 case split:
`Kakeya.VeryNotSticky.exists_setup_caseSideData`,
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid`,
`Kakeya.VeryNotSticky.coarseKatzTaoBound` (refuted, kept on the record deliberately),
`ShadedPlank.reduction_to_slab_atTypicalAngle`,
`Kakeya.ThinCase.factoringApply`, and
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`.

So this theorem does **not** say Main Lemma 2 holds modulo three hypotheses.  It says the three
lemmas type-compose across the namespace boundary, and it fails to compile the moment they stop
doing so — which is its whole purpose. -/
theorem mainLemma2Statement_of_uniformPlankExponent
    (hplank : ∀ β₀ : ℝ, 0 < β₀ → β₀ ≤ 1 → VNSUniform.UniformPlankExponent.{u} β₀)
    (hcore : ML2Assembly.GeometricCore.{u}) (hsmall : ML2Assembly.SmallCardHyp.{u}) :
    VNSUniform.MainLemma2Statement.{u} :=
  ML2Ptw.protected_statement_of_pointwiseCore
    (ML2Assembly.pointwiseCore_of_lemma91Uniform_of_geometricCore
      (assemblyLemma91Uniform_of_vnsUniform
        (VNSUniform.lemma91Uniform_of_uniformPlankExponent hplank)) hcore)
    hsmall

end Kakeya.ML2Bridge
