import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.HolderAssembly
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CinematicShear
import MyLeanRepo.Kakeya.Cinematic.Definitions
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Multiplicity transfer with an explicit curve-fiber cap

The rejected Section 7 route bounded every active tube by the same cinematic
multiplicity and then summed over all tubes, losing a factor `F.card`.  The
correct combinatorial transition groups active tubes by their assigned
selected cinematic curve and loses only the maximum assignment-fiber size.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- ENNReal-valued multiplicity of cinematic graph neighborhoods. -/
def cinematicMultiplicityENN
    (G : Kakeya.Cinematic.FiniteFunctionFamily)
    (r : ℝ) (p : ℝ × ℝ) : ENNReal :=
  ∑ g ∈ G.toFinset,
    (Kakeya.Cinematic.graphNeighborhood g r).indicator
      (fun _ => (1 : ENNReal)) p

lemma measurable_cinematicMultiplicityENN
    (G : Kakeya.Cinematic.FiniteFunctionFamily) (r : ℝ) :
    Measurable (cinematicMultiplicityENN G r) := by
  classical
  apply Finset.measurable_sum
  intro g _
  exact measurable_const.indicator
    (Kakeya.Cinematic.measurableSet_graphNeighborhood g r)

/--
The ENNReal-valued multiplicity is the nonnegative lift of the real-valued
multiplicity used by the PYZ input.
-/
lemma cinematicMultiplicityENN_eq_ofReal
    (G : Kakeya.Cinematic.FiniteFunctionFamily)
    (r : ℝ) (p : ℝ × ℝ) :
    cinematicMultiplicityENN G r p =
      ENNReal.ofReal (Kakeya.Cinematic.multiplicity G r p) := by
  classical
  simp only [cinematicMultiplicityENN, Kakeya.Cinematic.multiplicity]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro g _
    by_cases hp : p ∈ Kakeya.Cinematic.graphNeighborhood g r
    · simp [Set.indicator_of_mem hp]
    · simp [Set.indicator_of_notMem hp]
  · intro g _
    exact Set.indicator_nonneg (fun _ _ => by norm_num) p

/-- PYZ's real multiplicity bound applies unchanged to the ENNReal lift. -/
lemma eLpNorm_cinematicMultiplicityENN
    (G : Kakeya.Cinematic.FiniteFunctionFamily)
    (r : ℝ) (p : ENNReal) :
    eLpNorm (cinematicMultiplicityENN G r) p volume =
      eLpNorm (Kakeya.Cinematic.multiplicity G r) p volume := by
  have hfun :
      cinematicMultiplicityENN G r =
        ENNReal.ofReal ∘ Kakeya.Cinematic.multiplicity G r := by
    funext x
    exact cinematicMultiplicityENN_eq_ofReal G r x
  rw [hfun]
  apply MeasureTheory.eLpNorm_ofReal
  exact Filter.Eventually.of_forall fun x => by
    simp only [Kakeya.Cinematic.multiplicity]
    apply Finset.sum_nonneg
    intro g _
    exact Set.indicator_nonneg (fun _ _ => by norm_num) x

/-- Cinematic multiplicity is monotone in the graph-neighborhood radius. -/
lemma cinematicMultiplicityENN_mono_radius
    (G : Kakeya.Cinematic.FiniteFunctionFamily)
    {r R : ℝ} (hrR : r ≤ R) (p : ℝ × ℝ) :
    cinematicMultiplicityENN G r p ≤
      cinematicMultiplicityENN G R p := by
  classical
  simp only [cinematicMultiplicityENN]
  apply Finset.sum_le_sum
  intro g hg
  by_cases hp :
      p ∈ Kakeya.Cinematic.graphNeighborhood g r
  · have hpR :
        p ∈ Kakeya.Cinematic.graphNeighborhood g R :=
      Metric.thickening_mono hrR
        (Kakeya.Cinematic.functionGraph g) hp
    simp [Set.indicator_of_mem hp, Set.indicator_of_mem hpR]
  · simp [Set.indicator_of_notMem hp]

/-- The cinematic `L^p` norm is monotone in the neighborhood radius. -/
lemma eLpNorm_cinematicMultiplicityENN_mono_radius
    (G : Kakeya.Cinematic.FiniteFunctionFamily)
    {r R : ℝ} (hrR : r ≤ R) (p : ENNReal) :
    eLpNorm (cinematicMultiplicityENN G r) p volume ≤
      eLpNorm (cinematicMultiplicityENN G R) p volume := by
  apply MeasureTheory.eLpNorm_mono_enorm
  intro x
  simpa only [enorm_eq_self] using
    cinematicMultiplicityENN_mono_radius G hrR x

/--
Pointwise multiplicity transfer through a selected-curve assignment.

Only active tubes are assigned.  If every assigned tube projection is carried
into the corresponding graph neighborhood and every selected curve has at
most `M` active preimages, then the tube multiplicity is at most `M` times the
cinematic multiplicity.  No global tube-cardinality factor appears.
-/
lemma twistedProjectionMultiplicity_le_of_curve_fiber_cap
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Z : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    (G : Kakeya.Cinematic.FiniteFunctionFamily)
    (assign : Fin F.card → Kakeya.Cinematic.C2Function)
    (shear : Point2 → ℝ × ℝ)
    (r : ℝ) (M : ENNReal)
    (hassign :
      ∀ i, Z.carrier i ≠ ∅ → assign i ∈ G.carrier)
    (himage :
      ∀ i, Z.carrier i ≠ ∅ →
        shear '' (twistedProjection f '' Z.carrier i) ⊆
          Kakeya.Cinematic.graphNeighborhood (assign i) r)
    (hfiber :
      ∀ g ∈ G.toFinset,
        ((Finset.univ.filter fun i : Fin F.card =>
          Z.carrier i ≠ ∅ ∧ assign i = g).card : ENNReal) ≤ M)
    (q : Point2) :
    twistedProjectionMultiplicity Z f q ≤
      M * cinematicMultiplicityENN G r (shear q) := by
  classical
  let active : Finset (Fin F.card) :=
    Finset.univ.filter fun i => Z.carrier i ≠ ∅
  let tubeTerm (i : Fin F.card) : ENNReal :=
    (twistedProjection f '' Z.carrier i).indicator
      (fun _ => (1 : ENNReal)) q
  let graphTerm (g : Kakeya.Cinematic.C2Function) : ENNReal :=
    (Kakeya.Cinematic.graphNeighborhood g r).indicator
      (fun _ => (1 : ENNReal)) (shear q)
  have hinactive : ∀ i ∉ active, tubeTerm i = 0 := by
    intro i hi
    have hempty : Z.carrier i = ∅ := by
      simpa [active] using hi
    simp [tubeTerm, hempty]
  have hterm : ∀ i ∈ active, tubeTerm i ≤ graphTerm (assign i) := by
    intro i hi
    have hne : Z.carrier i ≠ ∅ := by
      simpa [active] using hi
    by_cases hq : q ∈ twistedProjection f '' Z.carrier i
    · have hshear :
          shear q ∈
            Kakeya.Cinematic.graphNeighborhood (assign i) r :=
        himage i hne ⟨q, hq, rfl⟩
      simp [tubeTerm, graphTerm, hq, hshear]
    · simp [tubeTerm, hq]
  have hmaps : ∀ i ∈ active, assign i ∈ G.toFinset := by
    intro i hi
    have hne : Z.carrier i ≠ ∅ := by
      simpa [active] using hi
    simpa [Kakeya.Cinematic.FiniteFunctionFamily.toFinset] using
      hassign i hne
  have hgroup :=
    Finset.sum_fiberwise_of_maps_to hmaps
      (fun i => graphTerm (assign i))
  calc
    twistedProjectionMultiplicity Z f q
        = ∑ i : Fin F.card, tubeTerm i := by
          rfl
    _ = ∑ i ∈ active, tubeTerm i := by
          rw [Finset.sum_subset (show active ⊆ Finset.univ from by simp)]
          intro i _ hi
          exact hinactive i hi
    _ ≤ ∑ i ∈ active, graphTerm (assign i) := by
          exact Finset.sum_le_sum hterm
    _ = ∑ g ∈ G.toFinset,
          ∑ i ∈ active with assign i = g, graphTerm (assign i) := by
          exact hgroup.symm
    _ ≤ ∑ g ∈ G.toFinset, M * graphTerm g := by
          apply Finset.sum_le_sum
          intro g hg
          have hinner :
              (∑ i ∈ active with assign i = g,
                  graphTerm (assign i)) =
                ((active.filter fun i => assign i = g).card : ENNReal) *
                  graphTerm g := by
            calc
              (∑ i ∈ active with assign i = g,
                  graphTerm (assign i))
                  = ∑ _i ∈ active.filter (fun i => assign i = g),
                      graphTerm g := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [(Finset.mem_filter.mp hi).2]
              _ = ((active.filter fun i => assign i = g).card : ENNReal) *
                    graphTerm g := by
                    simp
          have hfilter :
              active.filter (fun i => assign i = g) =
                Finset.univ.filter (fun i : Fin F.card =>
                  Z.carrier i ≠ ∅ ∧ assign i = g) := by
            ext i
            simp [active, and_assoc]
          rw [hinner, hfilter]
          exact mul_le_mul_right' (hfiber g hg) _
    _ = M * cinematicMultiplicityENN G r (shear q) := by
          simp only [cinematicMultiplicityENN, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro g _
          rfl

/--
Pointwise multiplicity transfer using only the assignment fibers that
actually contribute at the current projected point.

This is weaker than a global active-fiber cap and is the form compatible with
the geometric Tube-Wolff count: tubes that share a selected curve but occur in
different axial windows need not be counted together unless their projected
shadings cover the same point.
-/
lemma twistedProjectionMultiplicity_le_of_pointwise_curve_fiber_cap
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Z : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    (G : Kakeya.Cinematic.FiniteFunctionFamily)
    (assign : Fin F.card → Kakeya.Cinematic.C2Function)
    (shear : Point2 → ℝ × ℝ)
    (r : ℝ) (M : ENNReal)
    (hassign :
      ∀ i, Z.carrier i ≠ ∅ → assign i ∈ G.carrier)
    (himage :
      ∀ i, Z.carrier i ≠ ∅ →
        shear '' (twistedProjection f '' Z.carrier i) ⊆
          Kakeya.Cinematic.graphNeighborhood (assign i) r)
    (hfiber :
      ∀ q g, g ∈ G.toFinset →
        ((Finset.univ.filter fun i : Fin F.card =>
          q ∈ twistedProjection f '' Z.carrier i ∧ assign i = g).card :
            ENNReal) ≤ M)
    (q : Point2) :
    twistedProjectionMultiplicity Z f q ≤
      M * cinematicMultiplicityENN G r (shear q) := by
  classical
  let contributing : Finset (Fin F.card) :=
    Finset.univ.filter fun i =>
      q ∈ twistedProjection f '' Z.carrier i
  let tubeTerm (i : Fin F.card) : ENNReal :=
    (twistedProjection f '' Z.carrier i).indicator
      (fun _ => (1 : ENNReal)) q
  let graphTerm (g : Kakeya.Cinematic.C2Function) : ENNReal :=
    (Kakeya.Cinematic.graphNeighborhood g r).indicator
      (fun _ => (1 : ENNReal)) (shear q)
  have houtside : ∀ i ∉ contributing, tubeTerm i = 0 := by
    intro i hi
    have hq : q ∉ twistedProjection f '' Z.carrier i := by
      simpa [contributing] using hi
    simp [tubeTerm, hq]
  have hterm : ∀ i ∈ contributing, tubeTerm i ≤ graphTerm (assign i) := by
    intro i hi
    have hq : q ∈ twistedProjection f '' Z.carrier i := by
      simpa [contributing] using hi
    have hne : Z.carrier i ≠ ∅ := by
      intro hempty
      simp [hempty] at hq
    have hshear :
        shear q ∈ Kakeya.Cinematic.graphNeighborhood (assign i) r :=
      himage i hne ⟨q, hq, rfl⟩
    simp [tubeTerm, graphTerm, hq, hshear]
  have hmaps : ∀ i ∈ contributing, assign i ∈ G.toFinset := by
    intro i hi
    have hq : q ∈ twistedProjection f '' Z.carrier i := by
      simpa [contributing] using hi
    have hne : Z.carrier i ≠ ∅ := by
      intro hempty
      simp [hempty] at hq
    simpa [Kakeya.Cinematic.FiniteFunctionFamily.toFinset] using
      hassign i hne
  have hgroup :=
    Finset.sum_fiberwise_of_maps_to hmaps
      (fun i => graphTerm (assign i))
  calc
    twistedProjectionMultiplicity Z f q
        = ∑ i : Fin F.card, tubeTerm i := by
          rfl
    _ = ∑ i ∈ contributing, tubeTerm i := by
          rw [Finset.sum_subset
            (show contributing ⊆ Finset.univ from by simp)]
          intro i _ hi
          exact houtside i hi
    _ ≤ ∑ i ∈ contributing, graphTerm (assign i) := by
          exact Finset.sum_le_sum hterm
    _ = ∑ g ∈ G.toFinset,
          ∑ i ∈ contributing with assign i = g, graphTerm (assign i) := by
          exact hgroup.symm
    _ ≤ ∑ g ∈ G.toFinset, M * graphTerm g := by
          apply Finset.sum_le_sum
          intro g hg
          have hinner :
              (∑ i ∈ contributing with assign i = g,
                  graphTerm (assign i)) =
                ((contributing.filter fun i => assign i = g).card : ENNReal) *
                  graphTerm g := by
            calc
              (∑ i ∈ contributing with assign i = g,
                  graphTerm (assign i))
                  = ∑ _i ∈ contributing.filter (fun i => assign i = g),
                      graphTerm g := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [(Finset.mem_filter.mp hi).2]
              _ = ((contributing.filter fun i => assign i = g).card :
                    ENNReal) * graphTerm g := by
                    simp
          have hfilter :
              contributing.filter (fun i => assign i = g) =
                Finset.univ.filter (fun i : Fin F.card =>
                  q ∈ twistedProjection f '' Z.carrier i ∧ assign i = g) := by
            ext i
            simp [contributing, and_assoc]
          rw [hinner, hfilter]
          exact mul_le_mul_right' (hfiber q g hg) _
    _ = M * cinematicMultiplicityENN G r (shear q) := by
          simp only [cinematicMultiplicityENN, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro g _
          rfl

/--
Lift the pointwise selected-curve multiplicity transfer to `L^{3/2}`.

The cinematic shear disappears from the final norm because it preserves
planar Lebesgue measure.  The assignment-fiber loss remains the explicit
factor `M`.
-/
lemma eLpNorm_twistedProjectionMultiplicity_le_of_curve_fiber_cap
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Z : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    (G : Kakeya.Cinematic.FiniteFunctionFamily)
    (assign : Fin F.card → Kakeya.Cinematic.C2Function)
    (c0 r : ℝ) (M : ENNReal)
    (hassign :
      ∀ i, Z.carrier i ≠ ∅ → assign i ∈ G.carrier)
    (himage :
      ∀ i, Z.carrier i ≠ ∅ →
        cinematicShear c0 '' (twistedProjection f '' Z.carrier i) ⊆
          Kakeya.Cinematic.graphNeighborhood (assign i) r)
    (hfiber :
      ∀ g ∈ G.toFinset,
        ((Finset.univ.filter fun i : Fin F.card =>
          Z.carrier i ≠ ∅ ∧ assign i = g).card : ENNReal) ≤ M) :
    eLpNorm (twistedProjectionMultiplicity Z f)
        (3 / 2 : ENNReal) volume ≤
      M * eLpNorm (cinematicMultiplicityENN G r)
        (3 / 2 : ENNReal) volume := by
  let graphMultiplicity : Point2 → ENNReal :=
    cinematicMultiplicityENN G r ∘ cinematicShear c0
  have hgraph_meas : Measurable graphMultiplicity :=
    (measurable_cinematicMultiplicityENN G r).comp
      (cinematicShear_measurePreserving c0).measurable
  have hpoint :
      ∀ q, twistedProjectionMultiplicity Z f q ≤
        M * graphMultiplicity q := by
    intro q
    exact twistedProjectionMultiplicity_le_of_curve_fiber_cap
      Z f G assign (cinematicShear c0) r M
        hassign himage hfiber q
  have hnorm :
      eLpNorm (twistedProjectionMultiplicity Z f)
          (3 / 2 : ENNReal) volume ≤
        M * eLpNorm graphMultiplicity (3 / 2 : ENNReal) volume := by
    apply MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul''
      (p := (3 / 2 : ENNReal)) hgraph_meas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun q => hpoint q
  have hshear :
      eLpNorm graphMultiplicity (3 / 2 : ENNReal) volume =
        eLpNorm (cinematicMultiplicityENN G r)
          (3 / 2 : ENNReal) volume := by
    exact eLpNorm_comp_cinematicShear c0
      (cinematicMultiplicityENN G r) (3 / 2 : ENNReal)
      (measurable_cinematicMultiplicityENN G r)
  rw [hshear] at hnorm
  exact hnorm

/--
Lift the pointwise contributing-fiber transfer to `L^{3/2}`.

The fiber hypothesis is allowed to depend on the projected point, while the
uniform bound `M` remains outside the norm.
-/
lemma eLpNorm_twistedProjectionMultiplicity_le_of_pointwise_curve_fiber_cap
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Z : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    (G : Kakeya.Cinematic.FiniteFunctionFamily)
    (assign : Fin F.card → Kakeya.Cinematic.C2Function)
    (c0 r : ℝ) (M : ENNReal)
    (hassign :
      ∀ i, Z.carrier i ≠ ∅ → assign i ∈ G.carrier)
    (himage :
      ∀ i, Z.carrier i ≠ ∅ →
        cinematicShear c0 '' (twistedProjection f '' Z.carrier i) ⊆
          Kakeya.Cinematic.graphNeighborhood (assign i) r)
    (hfiber :
      ∀ q g, g ∈ G.toFinset →
        ((Finset.univ.filter fun i : Fin F.card =>
          q ∈ twistedProjection f '' Z.carrier i ∧ assign i = g).card :
            ENNReal) ≤ M) :
    eLpNorm (twistedProjectionMultiplicity Z f)
        (3 / 2 : ENNReal) volume ≤
      M * eLpNorm (cinematicMultiplicityENN G r)
        (3 / 2 : ENNReal) volume := by
  let graphMultiplicity : Point2 → ENNReal :=
    cinematicMultiplicityENN G r ∘ cinematicShear c0
  have hgraph_meas : Measurable graphMultiplicity :=
    (measurable_cinematicMultiplicityENN G r).comp
      (cinematicShear_measurePreserving c0).measurable
  have hpoint :
      ∀ q, twistedProjectionMultiplicity Z f q ≤
        M * graphMultiplicity q := by
    intro q
    exact twistedProjectionMultiplicity_le_of_pointwise_curve_fiber_cap
      Z f G assign (cinematicShear c0) r M
        hassign himage hfiber q
  have hnorm :
      eLpNorm (twistedProjectionMultiplicity Z f)
          (3 / 2 : ENNReal) volume ≤
        M * eLpNorm graphMultiplicity (3 / 2 : ENNReal) volume := by
    apply MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul''
      (p := (3 / 2 : ENNReal)) hgraph_meas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun q => hpoint q
  have hshear :
      eLpNorm graphMultiplicity (3 / 2 : ENNReal) volume =
        eLpNorm (cinematicMultiplicityENN G r)
          (3 / 2 : ENNReal) volume := by
    exact eLpNorm_comp_cinematicShear c0
      (cinematicMultiplicityENN G r) (3 / 2 : ENNReal)
      (measurable_cinematicMultiplicityENN G r)
  rw [hshear] at hnorm
  exact hnorm

/--
Complete the analytic assembly from selected curves to a twisted-union volume
lower bound.  Geometry supplies the measurable projected carriers and their
one-tube area lower bounds; the curve assignment supplies the fiber cap; PYZ
supplies the cinematic `L^{3/2}` bound.
-/
lemma holder_twistedUnion_volume_of_curve_fiber_cap
    {delta : ℝ} (hdelta : 0 < delta)
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Z : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    (G : Kakeya.Cinematic.FiniteFunctionFamily)
    (assign : Fin F.card → Kakeya.Cinematic.C2Function)
    (c0 r : ℝ) (M P : ENNReal)
    (himages :
      ∀ i, MeasurableSet (twistedProjection f '' Z.carrier i))
    (harea :
      ∀ i,
        volume (Z.carrier i) ≤
          ENNReal.ofReal (20 * delta) *
            volume (twistedProjection f '' Z.carrier i))
    (hassign :
      ∀ i, Z.carrier i ≠ ∅ → assign i ∈ G.carrier)
    (himage :
      ∀ i, Z.carrier i ≠ ∅ →
        cinematicShear c0 '' (twistedProjection f '' Z.carrier i) ⊆
          Kakeya.Cinematic.graphNeighborhood (assign i) r)
    (hfiber :
      ∀ g ∈ G.toFinset,
        ((Finset.univ.filter fun i : Fin F.card =>
          Z.carrier i ≠ ∅ ∧ assign i = g).card : ENNReal) ≤ M)
    (hcinematic :
      eLpNorm (cinematicMultiplicityENN G r)
        (3 / 2 : ENNReal) volume ≤ P) :
    volume (twistedUnion Z f) ≥
      ((Z.mass / ENNReal.ofReal (20 * delta)) / (M * P)) ^ 3 := by
  have htube :
      eLpNorm (twistedProjectionMultiplicity Z f)
          (3 / 2 : ENNReal) volume ≤
        M * P := by
    exact
      (eLpNorm_twistedProjectionMultiplicity_le_of_curve_fiber_cap
        Z f G assign c0 r M hassign himage hfiber).trans
        (mul_le_mul_left' hcinematic M)
  exact holder_twistedUnion_volume_of_projected_areas
    hdelta Z f himages harea (M * P) htube

/--
Complete the Hölder volume assembly from a pointwise contributing-fiber cap.

Unlike `holder_twistedUnion_volume_of_curve_fiber_cap`, this version does not
require all active tubes assigned to one curve to lie in a single global
fiber.  It only bounds the tubes from that assignment fiber whose projected
shadings cover the current point.
-/
lemma holder_twistedUnion_volume_of_pointwise_curve_fiber_cap
    {delta : ℝ} (hdelta : 0 < delta)
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Z : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    (G : Kakeya.Cinematic.FiniteFunctionFamily)
    (assign : Fin F.card → Kakeya.Cinematic.C2Function)
    (c0 r : ℝ) (M P : ENNReal)
    (himages :
      ∀ i, MeasurableSet (twistedProjection f '' Z.carrier i))
    (harea :
      ∀ i,
        volume (Z.carrier i) ≤
          ENNReal.ofReal (20 * delta) *
            volume (twistedProjection f '' Z.carrier i))
    (hassign :
      ∀ i, Z.carrier i ≠ ∅ → assign i ∈ G.carrier)
    (himage :
      ∀ i, Z.carrier i ≠ ∅ →
        cinematicShear c0 '' (twistedProjection f '' Z.carrier i) ⊆
          Kakeya.Cinematic.graphNeighborhood (assign i) r)
    (hfiber :
      ∀ q g, g ∈ G.toFinset →
        ((Finset.univ.filter fun i : Fin F.card =>
          q ∈ twistedProjection f '' Z.carrier i ∧ assign i = g).card :
            ENNReal) ≤ M)
    (hcinematic :
      eLpNorm (cinematicMultiplicityENN G r)
        (3 / 2 : ENNReal) volume ≤ P) :
    volume (twistedUnion Z f) ≥
      ((Z.mass / ENNReal.ofReal (20 * delta)) / (M * P)) ^ 3 := by
  have htube :
      eLpNorm (twistedProjectionMultiplicity Z f)
          (3 / 2 : ENNReal) volume ≤
        M * P := by
    exact
      (eLpNorm_twistedProjectionMultiplicity_le_of_pointwise_curve_fiber_cap
        Z f G assign c0 r M hassign himage hfiber).trans
        (mul_le_mul_left' hcinematic M)
  exact holder_twistedUnion_volume_of_projected_areas
    hdelta Z f himages harea (M * P) htube

end Kakeya.Assouad
