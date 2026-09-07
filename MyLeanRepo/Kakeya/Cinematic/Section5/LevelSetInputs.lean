import MyLeanRepo.Kakeya.Cinematic.Statements
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ClusterDefinitions

/-!
# Explicit Section 5 level-set leaves

These propositions isolate the remaining geometric and finite-combinatorial
steps between fine rectangles and the bipartite tangency theorem.
-/

namespace Kakeya.Cinematic

/-- PYZ Lemma 44: place a fine rectangle in its centered coarse dilation. -/
def FineToCoarseContainmentStatement : Prop :=
  ∀ {K delta t Delta C_R : ℝ},
    1 ≤ K →
    0 < delta →
    delta ≤ Delta →
    Delta ≤ t →
    0 < t →
    0 < C_R →
    256 * K^2 ≤ C_R →
    ∀ {I : ParameterInterval},
      I.IsControlled K →
      ∀ {R : CurvilinearRectangle delta (C_R * t * Delta / delta)},
        R.IsOverCentralQuarterOf I →
        ∃ S : CurvilinearRectangle Delta (C_R * t),
          S.function = R.function ∧
          S.interval.midpoint = R.interval.midpoint ∧
          R.carrier ⊆ S.carrier

/--
Paper-facing form of PYZ Lemma 44. The fine rectangle is centered at a point
of the centered eighth of `I`; the containing coarse rectangle therefore
remains over the centered quarter required by Proposition 26.
-/
def FineToCoarseCentralStatement : Prop :=
  ∀ {K delta t Delta C_R : ℝ},
    1 ≤ K →
    0 < delta →
    delta ≤ Delta →
    Delta ≤ t →
    0 < t →
    0 < C_R →
    9216 * K^2 ≤ C_R →
    ∀ {I : ParameterInterval},
      I.IsControlled K →
      ∀ {R : CurvilinearRectangle delta (C_R * t * Delta / delta)},
        R.IsOverCentralQuarterOf I →
        |R.interval.midpoint - I.midpoint| ≤ I.length / 16 →
        ∃ S : CurvilinearRectangle Delta (C_R * t),
          S.function = R.function ∧
          S.interval.midpoint = R.interval.midpoint ∧
          R.carrier ⊆ S.carrier ∧
          S.IsOverCentralQuarterOf I

/-- PYZ Lemma 44: fine tangency persists on the containing coarse rectangle. -/
def FineTangencyLiftToCoarseStatement : Prop :=
  ∀ {K D delta t Delta C_R : ℝ},
    1 ≤ K →
    1 ≤ D →
    0 < delta →
    delta ≤ Delta →
    Delta ≤ t →
    0 < t →
    0 < C_R →
    9216 * K^2 ≤ C_R →
    ∀ {family : Set C2Function},
      IsCinematicFamily family K D →
      ∀ {I : ParameterInterval},
        I.IsControlled K →
        ∀ {R : CurvilinearRectangle delta (C_R * t * Delta / delta)},
          ∀ {S : CurvilinearRectangle Delta (C_R * t)},
            R.IsOverCentralQuarterOf I →
            S.function = R.function →
            S.interval.midpoint = R.interval.midpoint →
            R.carrier ⊆ S.carrier →
            ∀ {f k : C2Function},
              R.function = k →
              k ∈ family →
              f ∈ family →
              c2Distance f k ≤ 6 * t →
              tangencyParameterOn I f k ≤ Delta →
              R.IsLambdaTangent f 5 →
              S.IsLambdaTangent f 5

/--
From a bounded cover and per-ball non-concentration, every rectangle has two
well-separated tangent clusters. This is the per-rectangle step preceding the
ball-pair pigeonhole in PYZ Section 5.
-/
def SeparatedTangentBallPairStatement : Prop :=
  ∀ {delta t r : ℝ},
    0 < r →
    ∀ (H : FiniteFunctionFamily),
      ∀ (R : RectangleFamily delta t),
        R.Nonempty →
        ∀ (centers : Finset C2Function),
          centers.Nonempty →
          H.carrier ⊆
            ⋃ c ∈ centers, c2Ball c r →
          ∀ q : ℕ, 0 < q →
            (∀ i,
              2 * centers.card * q ≤
                RectangleFamily.tangentCount (R.rectangle i) H 5) →
            (∀ i, ∀ c ∈ centers,
              2 * RectangleFamily.tangentCount
                    (R.rectangle i) (H.cluster c (11 * r)) 5 ≤
                RectangleFamily.tangentCount (R.rectangle i) H 5) →
            ∀ i,
              ∃ c ∈ centers, ∃ d ∈ centers,
                10 * r ≤ c2Distance c d ∧
                q ≤ RectangleFamily.tangentCount
                    (R.rectangle i) (H.cluster c r) 5 ∧
                q ≤ RectangleFamily.tangentCount
                    (R.rectangle i) (H.cluster d r) 5 ∧
                (H.cluster c r).AreSeparated (H.cluster d r) (8 * r)

/--
Paper-facing form of the separated-cluster selection. The tangent fiber
`T i = F(Ṙ_i)` may depend on the coarse rectangle, while all selected
functions lie in one ambient family `H`. The output is promoted to clusters
of `H`, ready for the shared-pair pigeonhole.
-/
def FiberwiseSeparatedTangentBallPairStatement : Prop :=
  ∀ {delta t r : ℝ},
    0 < r →
    ∀ (H : FiniteFunctionFamily),
      ∀ (R : RectangleFamily delta t),
        R.Nonempty →
        ∀ (T : Fin R.card → FiniteFunctionFamily),
          (∀ i, (T i).carrier ⊆ H.carrier) →
          ∀ (centers : Finset C2Function),
            centers.Nonempty →
            (∀ i,
              (T i).carrier ⊆
                ⋃ c ∈ centers, c2Ball c r) →
            ∀ q : ℕ, 0 < q →
              (∀ i,
                2 * centers.card * q ≤
                  RectangleFamily.tangentCount
                    (R.rectangle i) (T i) 5) →
              (∀ i, ∀ c ∈ centers,
                2 * RectangleFamily.tangentCount
                      (R.rectangle i) ((T i).cluster c (11 * r)) 5 ≤
                  RectangleFamily.tangentCount
                    (R.rectangle i) (T i) 5) →
              ∀ i,
                ∃ c ∈ centers, ∃ d ∈ centers,
                  10 * r ≤ c2Distance c d ∧
                  q ≤ RectangleFamily.tangentCount
                      (R.rectangle i) (H.cluster c r) 5 ∧
                  q ≤ RectangleFamily.tangentCount
                      (R.rectangle i) (H.cluster d r) 5 ∧
                  (H.cluster c r).AreSeparated
                    (H.cluster d r) (8 * r)

/-- Arbitrary-tangency version used after coarse-parent tangency transfer. -/
def FiberwiseSeparatedTangentBallPairAtStatement : Prop :=
  ∀ {delta t r tangency : ℝ},
    0 < r →
    ∀ (H : FiniteFunctionFamily),
      ∀ (R : RectangleFamily delta t),
        R.Nonempty →
        ∀ (T : Fin R.card → FiniteFunctionFamily),
          (∀ i, (T i).carrier ⊆ H.carrier) →
          ∀ (centers : Finset C2Function),
            centers.Nonempty →
            (∀ i,
              (T i).carrier ⊆
                ⋃ c ∈ centers, c2Ball c r) →
            ∀ q : ℕ, 0 < q →
              (∀ i,
                2 * centers.card * q ≤
                  RectangleFamily.tangentCount
                    (R.rectangle i) (T i) tangency) →
              (∀ i, ∀ c ∈ centers,
                2 * RectangleFamily.tangentCount
                      (R.rectangle i) ((T i).cluster c (11 * r))
                        tangency ≤
                  RectangleFamily.tangentCount
                    (R.rectangle i) (T i) tangency) →
              ∀ i,
                ∃ c ∈ centers, ∃ d ∈ centers,
                  10 * r ≤ c2Distance c d ∧
                  q ≤ RectangleFamily.tangentCount
                      (R.rectangle i) (H.cluster c r) tangency ∧
                  q ≤ RectangleFamily.tangentCount
                      (R.rectangle i) (H.cluster d r) tangency ∧
                  (H.cluster c r).AreSeparated
                    (H.cluster d r) (8 * r)

/--
Pigeonhole the rectangle-dependent ball pairs to one shared pair and a large
rectangle subfamily. This is the finite step actually used before applying
Proposition 26.
-/
def SharedTangentBallPairPigeonholeStatement : Prop :=
  ∀ {delta t r : ℝ},
    ∀ (H : FiniteFunctionFamily),
      ∀ (R : RectangleFamily delta t),
        R.Nonempty →
        ∀ (centers : Finset C2Function),
          ∀ q : ℕ,
            (∀ i,
              ∃ c ∈ centers, ∃ d ∈ centers,
                10 * r ≤ c2Distance c d ∧
                q ≤ RectangleFamily.tangentCount
                    (R.rectangle i) (H.cluster c r) 5 ∧
                q ≤ RectangleFamily.tangentCount
                    (R.rectangle i) (H.cluster d r) 5 ∧
                (H.cluster c r).AreSeparated (H.cluster d r) (8 * r)) →
            ∃ c ∈ centers, ∃ d ∈ centers,
              10 * r ≤ c2Distance c d ∧
              (H.cluster c r).AreSeparated (H.cluster d r) (8 * r) ∧
              ∃ S : RectangleSubfamily R,
                R.card ≤ centers.card ^ 2 * S.card ∧
                ∀ j,
                  q ≤ RectangleFamily.tangentCount
                      (S.family.rectangle j) (H.cluster c r) 5 ∧
                  q ≤ RectangleFamily.tangentCount
                      (S.family.rectangle j) (H.cluster d r) 5

/-- Arbitrary-tangency shared-pair pigeonhole. -/
def SharedTangentBallPairPigeonholeAtStatement : Prop :=
  ∀ {delta t r tangency : ℝ},
    ∀ (H : FiniteFunctionFamily),
      ∀ (R : RectangleFamily delta t),
        R.Nonempty →
        ∀ (centers : Finset C2Function),
          ∀ q : ℕ,
            (∀ i,
              ∃ c ∈ centers, ∃ d ∈ centers,
                10 * r ≤ c2Distance c d ∧
                q ≤ RectangleFamily.tangentCount
                    (R.rectangle i) (H.cluster c r) tangency ∧
                q ≤ RectangleFamily.tangentCount
                    (R.rectangle i) (H.cluster d r) tangency ∧
                (H.cluster c r).AreSeparated
                  (H.cluster d r) (8 * r)) →
            ∃ c ∈ centers, ∃ d ∈ centers,
              10 * r ≤ c2Distance c d ∧
              (H.cluster c r).AreSeparated (H.cluster d r) (8 * r) ∧
              ∃ S : RectangleSubfamily R,
                R.card ≤ centers.card ^ 2 * S.card ∧
                ∀ j,
                  q ≤ RectangleFamily.tangentCount
                      (S.family.rectangle j) (H.cluster c r) tangency ∧
                  q ≤ RectangleFamily.tangentCount
                      (S.family.rectangle j) (H.cluster d r) tangency

/--
PYZ Lemma 46 in the quantitative form needed by the WZ2 specialization.
The hypotheses make the application of the closed fixed-pair packing theorem
explicit; the conclusion is weakened to the paper's `delta^(-4*eta)` loss.
-/
def Lemma46FixedPairIncidenceStatement : Prop :=
  TangencyGeometryCompletionStatement →
    ∀ {K D delta t eta A Cc : ℝ},
      1 ≤ K →
      1 ≤ D →
      0 < delta →
      0 < t →
      0 < eta →
      delta ≤ 1 →
      A = Real.rpow delta (-2 * eta) →
      1 ≤ A →
      delta / t ≤ 1 / (60 * K * A) →
      100 ≤ Cc →
      Cc * delta ≤ t →
      ∀ {family : Set C2Function},
        IsCinematicFamily family K D →
        ∀ {I : ParameterInterval},
          I.IsControlled K →
          ∀ {w b : C2Function},
            w ∈ family →
            b ∈ family →
            w ≠ b →
            t / A ≤ c2Distance w b →
            ∀ {R : RectangleFamily delta t},
              R.IsOverCentralQuarterOf I →
              R.IsPairwiseIncomparable family Cc →
              (∀ i,
                (R.rectangle i).IsLambdaTangent w 5 ∧
                  (R.rectangle i).IsLambdaTangent b 5) →
              ∃ C_pair : ℝ, 0 < C_pair ∧
                (R.card : ℝ) ≤
                  C_pair * Real.rpow delta (-4 * eta)

/--
Finite doubling cover of one localized tangent family. This is the common
center set used for all rectangle-dependent fibers before the ball-pair
pigeonhole in PYZ Section 5.
-/
def FiniteTangentBallCoverStatement : Prop :=
  ∀ {K D diameter radius : ℝ},
    1 ≤ D →
    0 < diameter →
    0 < radius →
    ∀ {family : Set C2Function},
      IsCinematicFamily family K D →
      ∀ (H : FiniteFunctionFamily),
        H.carrier ⊆ family →
        (∀ f ∈ H.carrier, ∀ g ∈ H.carrier,
          c2Distance f g ≤ diameter) →
        ∃ centers : Finset C2Function,
          (centers : Set C2Function) ⊆ family ∧
          H.carrier ⊆ ⋃ c ∈ centers, c2Ball c radius ∧
          ∃ depth : ℕ,
            diameter / 2 ^ depth ≤ radius ∧
            (centers.card : ℝ) ≤ D ^ depth

/--
PYZ Lemma 45: specialize the two two-ends non-concentration inequalities
to one metric cutoff and one tangency cutoff. The retained good fiber `G`
may be smaller than the base pointwise fiber `F`.
-/
def Lemma45BadSetBoundsStatement : Prop :=
  ∀ {delta t Delta metricExponent tangencyExponent
      metricCut tangencyCut : ℝ},
    0 < delta →
    0 < t →
    0 < Delta →
    0 < metricExponent →
    0 < tangencyExponent →
    0 < metricCut →
    metricCut < 1 →
    delta / t < metricCut →
    0 < tangencyCut →
    tangencyCut < 1 →
    delta / Delta < tangencyCut →
    ∀ {I : ParameterInterval},
      ∀ (F G : FiniteFunctionFamily),
        G.carrier ⊆ F.carrier →
        (∀ g ∈ G.carrier,
          ((F.carrier ∩ c2Ball g (metricCut * t)).ncard : ℝ) ≤
            4 * Real.rpow (2 * metricCut) metricExponent *
              (F.card : ℝ)) →
        (∀ g ∈ G.carrier,
          ((F.carrier ∩
              {f | tangencyParameterOn I f g ≤
                tangencyCut * Delta}).ncard : ℝ) ≤
            2 * Real.rpow tangencyCut tangencyExponent *
              (G.card : ℝ)) →
        12 * Real.rpow (2 * metricCut) metricExponent *
            (F.card : ℝ) ≤
          (G.card : ℝ) →
        6 * Real.rpow tangencyCut tangencyExponent ≤ 1 →
        ∀ g ∈ G.carrier,
          3 * ((G.carrier ∩
              c2Ball g (metricCut * t)).ncard : ℝ) ≤
            (G.card : ℝ) ∧
          3 * ((G.carrier ∩
              {f | tangencyParameterOn I f g + delta <
                tangencyCut * Delta}).ncard : ℝ) ≤
            (G.card : ℝ)

/--
The counting core of PYZ Lemma 47. The two incidence inequalities are the
defining double-count for the rectangle-dependent coarse fiber `H`; the
remaining hypotheses are exactly the two-ends retention bounds.
-/
def CoarseFiberNonconcentrationStatement : Prop :=
  ∀ {M q : ℕ} {mu₁ mu₂ coefficient logLoss : ℝ},
    0 < q →
    0 < mu₂ →
    0 ≤ coefficient →
    1 ≤ logLoss →
    mu₁ ≤ coefficient * mu₂ →
    ∀ (H : FiniteFunctionFamily),
      ∀ (G : Fin M → FiniteFunctionFamily),
        (∀ i, (G i).carrier ⊆ H.carrier) →
        M * mu₂ ≤ logLoss * q * (H.card : ℝ) →
        (∀ center radius,
          (q : ℝ) *
              ((H.carrier ∩ c2Ball center radius).ncard : ℝ) ≤
            ∑ i, (((G i).carrier ∩
              c2Ball center radius).ncard : ℝ)) →
        (∀ center radius,
          (∑ i, (((G i).carrier ∩
              c2Ball center radius).ncard : ℝ)) ≤
            M * mu₁) →
        ∀ center radius,
          ((H.carrier ∩ c2Ball center radius).ncard : ℝ) ≤
            logLoss * coefficient * (H.card : ℝ)

/--
The finite incidence core behind the second bound for the coarse grouping
multiplicity `M`. Every fine rectangle supplies many good function pairs,
and each function pair occurs in only boundedly many fine rectangles.
-/
def FinePairIncidenceBoundStatement : Prop :=
  PairIncidenceCountingStatement →
    ∀ (ρ σ : Type) [DecidableEq ρ] [DecidableEq σ],
      ∀ fine : Finset ρ,
        ∀ pairs : Finset σ,
          ∀ incidence : ρ → Finset σ,
            ∀ goodCount perPair : ℕ,
              (∀ R ∈ fine, goodCount^2 ≤
                3 * (pairs ∩ incidence R).card) →
              (∀ p ∈ pairs,
                (fine.filter fun R => p ∈ incidence R).card ≤ perPair) →
              fine.card * goodCount^2 ≤
                3 * pairs.card * perPair

/--
The geometric interpolation step combining the measure and tangency bounds
for the coarse grouping multiplicity `M`.
-/
def CoarseMultiplicityInterpolationStatement : Prop :=
  ∀ M measureBound tangencyBound : ℝ,
    0 ≤ M →
    0 ≤ measureBound →
    0 ≤ tangencyBound →
    M ≤ measureBound →
    M ≤ tangencyBound →
    M ≤ Real.rpow measureBound (1 / 4 : ℝ) *
      Real.rpow tangencyBound (3 / 4 : ℝ)

/--
Finite measurable pigeonholing with an explicit retained-mass certificate.

If a finite measurable family of bins covers a finite-measure set `E`, then
one measurable bin intersection retains at least a `1 / loss` fraction of
the measure whenever `loss` dominates the number of bins.
-/
def FiniteMeasurableCoverRetainedMassStatement : Prop :=
  ∀ {α : Type*} [MeasurableSpace α]
      {μ : MeasureTheory.Measure α}
      {ι : Type*} [Fintype ι] [Nonempty ι]
      (E : Set α) (bins : ι → Set α) (loss : ℝ),
    MeasurableSet E →
    μ E < ⊤ →
    (∀ i, MeasurableSet (bins i)) →
    E ⊆ ⋃ i, bins i →
    0 ≤ loss →
    (Fintype.card ι : ℝ) ≤ loss →
    ∃ i : ι,
      MeasurableSet (E ∩ bins i) ∧
      E ∩ bins i ⊆ E ∧
      μ E ≤ ENNReal.ofReal loss * μ (E ∩ bins i)

/--
Measurable argmax bins for a finite family of measurable real scores.

Ties are deliberately allowed: the bins may overlap, but every point belongs
to at least one bin. This is the measurable finite-choice interface needed
before applying `FiniteMeasurableCoverRetainedMassStatement`.
-/
def FiniteMeasurableArgmaxCoverStatement : Prop :=
  ∀ {α : Type*} [MeasurableSpace α]
      {ι : Type*} [Fintype ι] [Nonempty ι]
      (score : ι → α → ℝ),
    (∀ i, Measurable (score i)) →
    (∀ i, MeasurableSet {x | ∀ j, score j x ≤ score i x}) ∧
    Set.univ ⊆ ⋃ i, {x | ∀ j, score j x ≤ score i x}

/--
Area bound for one graph neighborhood over an arbitrary horizontal interval.

For an endpoint stub with `b - a = delta`, this gives the `O(delta^2)`
single-curve estimate used in the globalization following PYZ Lemma 39.
-/
def HorizontalGraphNeighborhoodVolumeStatement : Prop :=
  ∀ {f : C2Function} {delta L a b : ℝ},
    0 < delta →
    a ≤ b →
    Set.Icc a b ⊆ unitInterval →
    (∀ x : UnitPoint, |f.firstDeriv x| ≤ L) →
    MeasureTheory.volume
        (graphNeighborhood f delta ∩
          (Set.Icc a b ×ˢ (Set.univ : Set ℝ))) ≤
      ENNReal.ofReal (2 * (1 + L) * delta * (b - a))

/--
Multiplicity-weighted endpoint-stub estimate.

If every point of a measurable horizontal stub belongs to at least `mu`
graph neighborhoods, integrating the multiplicity and applying the
single-graph area estimate bounds `mu * volume E` by `F.card` copies of the
single-graph bound. This is the exact counting input used for the two endpoint
intervals in the globalization following PYZ Lemma 39.
-/
def HorizontalStubMultiplicityVolumeStatement : Prop :=
  HorizontalGraphNeighborhoodVolumeStatement →
    ∀ {F : FiniteFunctionFamily} {delta L a b : ℝ} {mu : ℕ}
        {E : Set (ℝ × ℝ)},
      0 < delta →
      a ≤ b →
      Set.Icc a b ⊆ unitInterval →
      (∀ f ∈ F.carrier, ∀ x : UnitPoint, |f.firstDeriv x| ≤ L) →
      0 < mu →
      MeasurableSet E →
      E ⊆ Set.Icc a b ×ˢ (Set.univ : Set ℝ) →
      (∀ p ∈ E, (mu : ℝ) ≤ multiplicity F delta p) →
      ENNReal.ofReal (mu : ℝ) * MeasureTheory.volume E ≤
        ENNReal.ofReal
          (2 * (1 + L) * delta * (b - a) * (F.card : ℝ))

end Kakeya.Cinematic
