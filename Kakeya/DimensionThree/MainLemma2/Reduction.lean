/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.Envelope
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineParams
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTwoScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineRescale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineInheritance
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineNonEccentric
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEccentric
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCardLower
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEveryScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.Assembly
public import Kakeya.DimensionThree.MainLemma2.Reduction.AssemblyPointwise
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCardBand
public import Kakeya.DimensionThree.MainLemma2.Reduction.BandMultilinear
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDichotomyInputs
public import Kakeya.DimensionThree.MainLemma2.Reduction.BandSqueeze
public import Kakeya.DimensionThree.MainLemma2.Reduction.BandSqueezeAlt
public import Kakeya.DimensionThree.MainLemma2.Reduction.CarriedBand
public import Kakeya.DimensionThree.MainLemma2.Reduction.GainFloor

/-!
# The GWZ reduction of Main Lemma 2 to Lemma 9.1

Aggregator for the pieces of the reduction of GWZ Main Lemma 2
(`Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate`) to GWZ Lemma 9.1
(`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`), following
`blueprint/src/GWZAdapted/section9.tex`.

* `Reduction.Envelope` — the monotone envelope of the admissible drops `ν`.
* `Reduction.SpineParams` — the parameter chain `ε₁ → ε₂ → (N, e, η_j) → ν`, and the proof that
  reading Theorem 7.3(B) at the outer `ε` makes an `ε`-free `ν` impossible.
* `Reduction.SpineTwoScale` — the two-scale multiplicity split at `τ` and `θ`.
* `Reduction.SpineRescale` — the transport laws of the two rescalings.
* `Reduction.SpineInheritance` — the adapters for GWZ Remark 3.3, downwards and upwards.
* `Reduction.SpineNonEccentric` — the non-eccentric case of the induction (steps 3-8 and 11).
* `Reduction.SpineEccentric` — the eccentric case, against the `Cw`-parameterised
  `Kakeya.GlobalPlankFactorization`.
* `Reduction.SpineDichotomyInputs` — component G2a: the essential-distinctness hypothesis, the
  uniform hierarchy and the `4096 ≤ N` side condition of GWZ Lemma 7.7(B), all produced from
  `Kakeya.ML2Assembly.Dichotomy`'s own hypotheses, and 7.7(B) run on them.
* `Reduction.SpineCardLower` — the `|𝕋| > δ⁻¹` dichotomy.
* `Reduction.SpineEveryScale` — the dividing-scales dichotomy of GWZ Lemma 7.7(B) and its
  every-scale branch through GWZ Theorem 7.3(B).
* `Reduction.Assembly` — the chaining of the above into `GWZ Lemma 9.1 ⟹ GWZ Main Lemma 2`.
* `Reduction.AssemblyPointwise` — the same chaining from **two** hypotheses instead of three:
  GWZ Lemma 9.1 is consumed as a term and the geometric core is stated at one exponent, so the
  `β`-uniform companion `Kakeya.ML2Assembly.Lemma91Uniform` is no longer needed.  Additive: it
  edits and removes nothing in `Reduction.Assembly`.
* `Reduction.SpineCardBand` — the small-cardinality band left open by the assembly.
* `Reduction.BandMultilinear` — the multilinear-Kakeya input that band would need, stated and
  scoped; `Kakeya.ML2BandML.TrilinearKakeya` is not proved here.
* `Reduction.BandSqueeze` (`Kakeya.ML2Squeeze`) and `Reduction.BandSqueezeAlt`
  (`Kakeya.ML2BandSqz`) — two INDEPENDENT kernel proofs that the reduction above is **circular**:
  `SmallCard γ ↔ KatzTaoEstimate Space3 γ` under the `diag(1,h,h)` squeeze, so
  `Reduction.Assembly`'s dichotomy hypothesis, GWZ Lemma 9.1 and the geometric core are all
  redundant there.  They are the record of why Main Lemma 2 must be rebuilt rather than shipped,
  and `Kakeya.ML2Squeeze.producer_of_smallCard_is_producer_of_goal` is the mechanical acceptance
  test any replacement obligation must fail.
* `Reduction.GainFloor` (`Kakeya.ML2GainFloor`) — the answer to the rebuild proposed there:
  a **gain** `μ ≤ δ^g|𝕋|^β` carries its own cardinality floor `|𝕋| ≥ δ^{-g/β}`, because
  `μ ≥ 1`.  So `Kakeya.ML2Squeeze.GainOnly` and `Kakeya.ML2Squeeze.GainDichotomy` — the gain with
  the cardinality clause deleted — are **false**, and every band that *is* true leaves the goal as
  its residue.

Namespaces are split across these files: `SpineParams`, `SpineInheritance` and
`SpineNonEccentric` live in `Kakeya.ML2Spine`; `SpineTwoScale`, `SpineRescale`, `Envelope`,
`SpineEccentric` and `SpineEveryScale` live in `Kakeya.ML2Reduction`; `SpineCardLower` lives in
`Kakeya.MainLemma2.Reduction`; `Assembly` lives in `Kakeya.ML2Assembly` and consumes them;
`SpineCardBand` lives in `Kakeya.ML2Band` and `BandMultilinear` in `Kakeya.ML2BandML`.
-/
