/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2
public import Kakeya.DimensionThree.MainLemma2.Reduction.AssemblyPointwise

/-!
# The pointwise geometric formulation of Main Lemma 2

`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_frostmanEstimate_of_pointwiseCore`
derives the Main Lemma 2 statement from GWZ Lemma 9.1 and the geometric
hypotheses `PointwiseCore` and `SmallCardHyp`. The declarations below compare
this formulation with the public Main Lemma 2 statement.
-/

@[expose] public section

namespace Kakeya.ML2Ptw

universe u

/-- **compatibility 1.**  `Kakeya.VNSUniform.MainLemma2Statement` — the statement the pointwise
reduction is proved against — is the protected Main Lemma 2, verbatim.  If either drifts, this
stops compiling. -/
example : Kakeya.VNSUniform.MainLemma2Statement.{u} :=
  Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate.{u}

/-- **compatibility 2, the other direction.**  A term of `Kakeya.VNSUniform.MainLemma2Statement` is a
term of the protected declaration's type, by `id`.  Together with compatibility 1 this pins the two
types to each other rather than merely exhibiting one from the other. -/
example (h : Kakeya.VNSUniform.MainLemma2Statement.{u}) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - ν β) := h

/-- **compatibility 3.**  The two-hypothesis GWZ route delivers exactly the protected statement.
Consequently the rewire is a substitution of proof terms and cannot alter the statement. -/
theorem protected_statement_of_pointwiseCore
    (hcore : ML2Assembly.PointwiseCore.{u}) (hsmall : ML2Assembly.SmallCardHyp.{u}) :
    Kakeya.VNSUniform.MainLemma2Statement.{u} :=
  ML2Assembly.katzTaoEstimate_sub_of_frostmanEstimate_of_pointwiseCore hcore hsmall

/-- **compatibility 4.**  The same, from the `β`-parameterised form of the geometric obligation. -/
theorem protected_statement_of_geometricCoreAt
    (hcore : ML2Assembly.GeometricCoreAt.{u}) (hsmall : ML2Assembly.SmallCardHyp.{u}) :
    Kakeya.VNSUniform.MainLemma2Statement.{u} :=
  ML2Assembly.katzTaoEstimate_sub_of_frostmanEstimate_of_geometricCoreAt hcore hsmall

/-- **compatibility 6.**  The *other* route to the protected statement — through
`Reduction/Envelope.lean`'s monotone envelope rather than through
`Kakeya.VNSUniform.mainLemma2Statement_of_pointwise_drop` — lands on it too, from the same two
hypotheses.  So the `MonotoneOn ν` clause has two independent discharges and neither needs a
`β`-uniform Lemma 9.1. -/
theorem protected_statement_via_envelope
    (hcore : ML2Assembly.PointwiseCore.{u}) (hsmall : ML2Assembly.SmallCardHyp.{u}) :
    Kakeya.VNSUniform.MainLemma2Statement.{u} :=
  ML2Assembly.katzTaoEstimate_sub_of_pointwiseCore_via_envelope hcore hsmall

/-- **compatibility 5.**  The three-hypothesis assembly of `Reduction/Assembly.lean` also lands on the
protected statement, so the two routes are comparable as terms of one type and the move from three
obligations to two is visibly a change of hypotheses only. -/
theorem protected_statement_of_lemma91Uniform
    (h91 : ML2Assembly.Lemma91Uniform.{u}) (hcore : ML2Assembly.GeometricCore.{u})
    (hsmall : ML2Assembly.SmallCardHyp.{u}) :
    Kakeya.VNSUniform.MainLemma2Statement.{u} :=
  ML2Assembly.katzTaoEstimate_sub_of_frostmanEstimate_of_lemma91 h91 hcore hsmall

end Kakeya.ML2Ptw
