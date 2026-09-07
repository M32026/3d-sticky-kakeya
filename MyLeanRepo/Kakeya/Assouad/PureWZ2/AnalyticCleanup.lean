import MyLeanRepo.Kakeya.Assouad.PureWZ2.BoundedConflictDegree
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.WeightedSelection
import MyLeanRepo.Kakeya.Assouad.Targets.WeightedEssentiallyDistinctSelection
import MyLeanRepo.Kakeya.Streamlined.GeneralizedKatzTao.ProbabilisticThinning
import MyLeanRepo.Kakeya.Streamlined.MaximalDensityFactoring.SubfamilyHelpers

/-!
# Fixed-scale analytic cleanup for pure WZ2 Node 7b

First run bounded Bernoulli thinning to control arbitrary convex density, then
apply weighted finite-graph selection to obtain volume-overlap essential
distinctness.  The output retains exact source indices and an explicit product
mass inequality; exponent absorption is intentionally left to the caller.
-/

noncomputable section

open MeasureTheory Set Finset
open Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2AnalyticCleanupData
    {delta : ℝ}
    (ambient : Kakeya.Streamlined.TubeFamily delta)
    (ambientShading : Kakeya.Streamlined.TubeShading ambient)
    (target : ENNReal)
    (D : ENNReal)
    (net : TubeDensityTestNet delta) where
  samplingRate : ENNReal
  samplingRate_eq : samplingRate = target / D
  samplingRate_zero : samplingRate ≠ 0
  samplingRate_top : samplingRate ≠ ⊤
  thinned : Kakeya.Streamlined.TubeSubfamily ambient
  selected : Finset (Fin thinned.family.card)
  thinned_deltaMax :
    thinned.family.toBodyFamily.deltaMax ≤
      net.lossFactor * 10 * target
  thinned_card_upper :
    thinned.family.enncard ≤
      2 * samplingRate * ambient.enncard
  mass_retention :
    (1 / 2 : ENNReal) *
          samplingRate *
          ambientShading.mass ≤
      (27000000000 * (net.lossFactor * 10 * target) + 1) *
        (selectedTubeShading
          (thinned.restrictShading ambientShading) selected).mass
  analytic_distinct :
    (selectedTubeFamily thinned.family selected).IsEssentiallyDistinct

namespace PureWZ2AnalyticCleanupData

abbrev loss
    {delta : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : Kakeya.Streamlined.TubeShading ambient}
    {target D : ENNReal} {net : TubeDensityTestNet delta}
    (_data : PureWZ2AnalyticCleanupData ambient ambientShading target D net) :
    ENNReal :=
  27000000000 * (net.lossFactor * 10 * target) + 1

abbrev family
    {delta : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : Kakeya.Streamlined.TubeShading ambient}
    {target D : ENNReal} {net : TubeDensityTestNet delta}
    (data : PureWZ2AnalyticCleanupData ambient ambientShading target D net) :
    Kakeya.Streamlined.TubeFamily delta :=
  selectedTubeFamily data.thinned.family data.selected

abbrev shading
    {delta : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : Kakeya.Streamlined.TubeShading ambient}
    {target D : ENNReal} {net : TubeDensityTestNet delta}
    (data : PureWZ2AnalyticCleanupData ambient ambientShading target D net) :
    Kakeya.Streamlined.TubeShading data.family :=
  selectedTubeShading
    (data.thinned.restrictShading ambientShading) data.selected

def sourceIndex
    {delta : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : Kakeya.Streamlined.TubeShading ambient}
    {target D : ENNReal} {net : TubeDensityTestNet delta}
    (data : PureWZ2AnalyticCleanupData ambient ambientShading target D net) :
    Fin data.family.card → Fin ambient.card :=
  fun index =>
    data.thinned.embedding (data.selected.equivFin.symm index).1

lemma sourceIndex_injective
    {delta : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : Kakeya.Streamlined.TubeShading ambient}
    {target D : ENNReal} {net : TubeDensityTestNet delta}
    (data : PureWZ2AnalyticCleanupData ambient ambientShading target D net) :
    Function.Injective data.sourceIndex := by
  intro first second heq
  have hinner :
      (data.selected.equivFin.symm first).1 =
        (data.selected.equivFin.symm second).1 :=
    data.thinned.embedding.injective heq
  have hsubtype : data.selected.equivFin.symm first =
      data.selected.equivFin.symm second := Subtype.ext hinner
  exact data.selected.equivFin.symm.injective hsubtype

lemma tube_eq_source
    {delta : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : Kakeya.Streamlined.TubeShading ambient}
    {target D : ENNReal} {net : TubeDensityTestNet delta}
    (data : PureWZ2AnalyticCleanupData ambient ambientShading target D net)
    (index : Fin data.family.card) :
    data.family.tube index = ambient.tube (data.sourceIndex index) := by
  change data.thinned.family.tube (data.selected.equivFin.symm index).1 =
    ambient.tube
      (data.thinned.embedding (data.selected.equivFin.symm index).1)
  exact data.thinned.tube_eq _

lemma shading_subset_source
    {delta : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : Kakeya.Streamlined.TubeShading ambient}
    {target D : ENNReal} {net : TubeDensityTestNet delta}
    (data : PureWZ2AnalyticCleanupData ambient ambientShading target D net)
    (index : Fin data.family.card) :
    data.shading.carrier index ⊆
      ambientShading.carrier (data.sourceIndex index) := by
  exact Set.Subset.rfl

lemma deltaMax_le
    {delta : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : Kakeya.Streamlined.TubeShading ambient}
    {target D : ENNReal} {net : TubeDensityTestNet delta}
    (data : PureWZ2AnalyticCleanupData ambient ambientShading target D net) :
    data.family.toBodyFamily.deltaMax ≤ net.lossFactor * 10 * target := by
  have hsub : data.family.toBodyFamily.deltaMax ≤
      data.thinned.family.toBodyFamily.deltaMax := by
    let selectedSubfamily : Kakeya.Streamlined.TubeSubfamily
        data.thinned.family :=
      { family := selectedTubeFamily data.thinned.family data.selected
        embedding :=
          { toFun := fun index => (data.selected.equivFin.symm index).1
            inj' := fun first second heq =>
              data.selected.equivFin.symm.injective (Subtype.ext heq) }
        tube_eq := fun _ => rfl }
    have h := Kakeya.Streamlined.subfamily_deltaMax_le
      selectedSubfamily.toBodySubfamily
    exact h
  exact hsub.trans data.thinned_deltaMax

lemma family_mass_le
    {delta : ℝ} (hdelta : 0 < delta)
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : Kakeya.Streamlined.TubeShading ambient}
    {target D : ENNReal} {net : TubeDensityTestNet delta}
    (data : PureWZ2AnalyticCleanupData ambient ambientShading target D net) :
    data.family.toBodyFamily.mass ≤
      2 * data.samplingRate * ambient.toBodyFamily.mass := by
  rw [tubeFamily_mass_eq_nominal data.family,
    tubeFamily_mass_eq_nominal ambient]
  have hcard : data.family.enncard ≤ data.thinned.family.enncard := by
    change (data.selected.card : ENNReal) ≤
      (data.thinned.family.card : ENNReal)
    have hcardNat : data.selected.card ≤ data.thinned.family.card := by
      have h := Finset.card_le_card
        (Finset.subset_univ data.selected :
          data.selected ⊆
            (Finset.univ : Finset (Fin data.thinned.family.card)))
      simpa using h
    exact_mod_cast hcardNat
  calc
    data.family.enncard * Kakeya.deltaTubeVolume delta
        ≤ data.thinned.family.enncard * Kakeya.deltaTubeVolume delta := by
          gcongr
    _ ≤ (2 * data.samplingRate * ambient.enncard) *
          Kakeya.deltaTubeVolume delta := by
          exact mul_le_mul_of_nonneg_right data.thinned_card_upper (by simp)
    _ = 2 * data.samplingRate *
          (ambient.enncard * Kakeya.deltaTubeVolume delta) := by ring

lemma family_card_le
    {delta : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : Kakeya.Streamlined.TubeShading ambient}
    {target D : ENNReal} {net : TubeDensityTestNet delta}
    (data : PureWZ2AnalyticCleanupData ambient ambientShading target D net) :
    data.family.enncard ≤
      2 * data.samplingRate * ambient.enncard := by
  change (data.selected.card : ENNReal) ≤
    2 * data.samplingRate * ambient.enncard
  have hcardNat : data.selected.card ≤ data.thinned.family.card := by
    have h := Finset.card_le_card
      (Finset.subset_univ data.selected :
        data.selected ⊆
          (Finset.univ : Finset (Fin data.thinned.family.card)))
    simpa using h
  have hselected : (data.selected.card : ENNReal) ≤
      data.thinned.family.enncard := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using
      (show (data.selected.card : ENNReal) ≤
        (data.thinned.family.card : ENNReal) by exact_mod_cast hcardNat)
  exact hselected.trans data.thinned_card_upper

lemma isLambdaDense_of_absorption
    {delta : ℝ} (hdelta : 0 < delta)
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : Kakeya.Streamlined.TubeShading ambient}
    {target D desired ambientDensity : ENNReal}
    {net : TubeDensityTestNet delta}
    (data : PureWZ2AnalyticCleanupData ambient ambientShading target D net)
    (htarget_zero : target ≠ 0) (htarget_top : target ≠ ⊤)
    (hD_zero : D ≠ 0) (hD_top : D ≠ ⊤)
    (hdense : ambientShading.IsLambdaDense ambientDensity)
    (habsorb : desired * 2 * data.loss ≤
      (1 / 2 : ENNReal) * ambientDensity) :
    data.shading.IsLambdaDense desired := by
  let p : ENNReal := data.samplingRate
  let L : ENNReal := data.loss
  have hmassFamily := data.family_mass_le hdelta
  have hstep : (1 / 2 : ENNReal) * p * ambientDensity *
      ambient.toBodyFamily.mass ≤ L * data.shading.mass := by
    calc
      (1 / 2 : ENNReal) * p * ambientDensity *
          ambient.toBodyFamily.mass =
          (1 / 2 : ENNReal) * p *
            (ambientDensity * ambient.toBodyFamily.mass) := by ring
      _ ≤ (1 / 2 : ENNReal) * p * ambientShading.mass := by
            exact mul_le_mul_of_nonneg_left hdense (by simp)
      _ ≤ L * data.shading.mass := data.mass_retention
  have hpZero : p ≠ 0 := data.samplingRate_zero
  have hpTop : p ≠ ⊤ := data.samplingRate_top
  have hLzero : L ≠ 0 := by simp [L, loss]
  have hLtop : L ≠ ⊤ := by
    simp only [L, loss]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top net.lossFactor_ne_top (by norm_num))
          htarget_top), ENNReal.one_ne_top⟩
  have hgoalL : L * (desired * data.family.toBodyFamily.mass) ≤
      L * data.shading.mass := by
    calc
      L * (desired * data.family.toBodyFamily.mass)
          ≤ L * (desired * (2 * p * ambient.toBodyFamily.mass)) := by
            gcongr
      _ = (desired * 2 * L) * p * ambient.toBodyFamily.mass := by ring
      _ ≤ ((1 / 2 : ENNReal) * ambientDensity) * p *
            ambient.toBodyFamily.mass := by gcongr
      _ = (1 / 2 : ENNReal) * p * ambientDensity *
            ambient.toBodyFamily.mass := by ring
      _ ≤ L * data.shading.mass := hstep
  have hgoalR : (desired * data.family.toBodyFamily.mass) * L ≤
      data.shading.mass * L := by simpa [mul_comm] using hgoalL
  exact (ENNReal.mul_le_mul_iff_left hLzero hLtop).mp hgoalR

lemma cardinality_retention
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : Kakeya.Streamlined.TubeShading ambient}
    {target D ambientDensity : ENNReal}
    {net : TubeDensityTestNet delta}
    (data : PureWZ2AnalyticCleanupData ambient ambientShading target D net)
    (htarget_top : target ≠ ⊤)
    (hdense : ambientShading.IsLambdaDense ambientDensity) :
    (data.loss⁻¹ * ((1 / 2 : ENNReal) * data.samplingRate * ambientDensity)) *
        ambient.enncard ≤ data.family.enncard := by
  let V := Kakeya.deltaTubeVolume delta
  have hVpos : 0 < V := (tube_volume_scaling.2.1 delta hdelta hdelta_one).1
  have hVtop : V ≠ ⊤ := (tube_volume_scaling.2.1 delta hdelta hdelta_one).2
  have hZmass : data.shading.mass ≤ data.family.toBodyFamily.mass := by
    apply Finset.sum_le_sum
    intro i _
    exact measure_mono (data.shading.subset_body i)
  have hmain : ((1 / 2 : ENNReal) * data.samplingRate * ambientDensity) *
      ambient.toBodyFamily.mass ≤ data.loss * data.family.toBodyFamily.mass := by
    calc
      _ = (1 / 2 : ENNReal) * data.samplingRate *
          (ambientDensity * ambient.toBodyFamily.mass) := by ring
      _ ≤ (1 / 2 : ENNReal) * data.samplingRate * ambientShading.mass := by
            exact mul_le_mul_of_nonneg_left hdense (by simp)
      _ ≤ data.loss * data.shading.mass := data.mass_retention
      _ ≤ data.loss * data.family.toBodyFamily.mass := by
            exact mul_le_mul_of_nonneg_left hZmass (by simp)
  have hAmbientMass : ambient.toBodyFamily.mass = ambient.enncard * V := by
    exact tubeFamily_mass_eq_nominal ambient
  have hFamilyMass : data.family.toBodyFamily.mass = data.family.enncard * V := by
    exact tubeFamily_mass_eq_nominal data.family
  rw [hAmbientMass, hFamilyMass] at hmain
  have hcancel : ((1 / 2 : ENNReal) * data.samplingRate * ambientDensity) *
      ambient.enncard ≤ data.loss * data.family.enncard := by
    apply (ENNReal.mul_le_mul_iff_right hVpos.ne' hVtop).mp
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmain
  have hLzero : data.loss ≠ 0 := by simp [loss]
  have hLtop : data.loss ≠ ⊤ := by
    simp only [loss]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top net.lossFactor_ne_top (by norm_num))
          htarget_top), ENNReal.one_ne_top⟩
  calc
    (data.loss⁻¹ * ((1 / 2 : ENNReal) * data.samplingRate * ambientDensity)) *
        ambient.enncard =
      data.loss⁻¹ *
        (((1 / 2 : ENNReal) * data.samplingRate * ambientDensity) *
          ambient.enncard) := by ring
    _ ≤ data.loss⁻¹ * (data.loss * data.family.enncard) := by gcongr
    _ = data.family.enncard := ENNReal.inv_mul_cancel_left hLzero hLtop

end PureWZ2AnalyticCleanupData

lemma pure_wz2_analytic_cleanup
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hdelta_small : delta ≤ 1 / 1000)
    (ambient : Kakeya.Streamlined.TubeFamily delta)
    (ambient_nonempty : ambient.Nonempty)
    (ambient_support :
      ∀ i, (ambient.tube i).carrier ⊆ Metric.closedBall (0 : Point3) 10)
    (ambientShading : Kakeya.Streamlined.TubeShading ambient)
    (eta : ℝ)
    (heta_pos : 0 < eta)
    (D : ENNReal)
    (hdeltaMax_D : ambient.toBodyFamily.deltaMax ≤ D)
    (hD_top : D ≠ ⊤)
    (htarget_D : Kakeya.realRpowENN delta (-eta) ≤ D)
    (net : TubeDensityTestNet delta)
    (h_mu_ge_V : Kakeya.deltaTubeVolume delta ≤
      (Kakeya.realRpowENN delta (-eta) /
        D) * ambientShading.mass)
    (h_union_bound :
      let target := Kakeya.realRpowENN delta (-eta)
      let p := target.toReal / D.toReal
      (net.testSets.card : ℝ) *
            Real.exp (-(11 - Real.exp 1) * target.toReal) +
          Real.exp (-(3 - Real.exp 1) * p * (ambient.card : ℝ)) <
        1 / 8) :
    Nonempty
      (PureWZ2AnalyticCleanupData ambient ambientShading
        (Kakeya.realRpowENN delta (-eta)) D net) := by
  let target := Kakeya.realRpowENN delta (-eta)
  rcases Kakeya.Streamlined.ProbabilisticThinning.probabilistic_thinning_bounded
      (hδ := hdelta) (hδ1 := hdelta_one)
      (hT_nonempty := ambient_nonempty) (hT_support := ambient_support)
      (Z := ambientShading) (D := D)
      (hD := hdeltaMax_D) (hD_ne_top := hD_top)
      (η' := eta) (hη'_pos := heta_pos)
      (h_thin := htarget_D) (net := net)
      (h_mu_ge_V := h_mu_ge_V)
      (h_union_bound := by simpa [target] using h_union_bound) with
    ⟨thinned, hthinnedDelta, hthinnedCard, hthinnedMass⟩
  let conflict : ENNReal :=
    27000000000 * (net.lossFactor * 10 * target)
  have hdegree : ∀ i,
      ((Finset.univ.filter fun j =>
        ¬(thinned.family.tube i).EssentiallyDistinct
          (thinned.family.tube j)).card : ENNReal) ≤ conflict :=
    tubeFamily_nonessential_degree_le_deltaMax
      hdelta hdelta_small thinned.family
      (net.lossFactor * 10 * target) hthinnedDelta
  rcases weighted_essentially_distinct_shading_refinement_of_broad_ennreal_degree
      weighted_essentially_distinct_selection
      thinned.family (thinned.restrictShading ambientShading)
      conflict hdegree with
    ⟨selected, hdistinct, _hunion, hmass⟩
  refine ⟨{
    samplingRate := target / D
    samplingRate_eq := rfl
    samplingRate_zero := by
      have htarget : target ≠ 0 := by
        dsimp only [target, Kakeya.realRpowENN]
        exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)).ne'
      exact ENNReal.div_ne_zero.mpr ⟨htarget, hD_top⟩
    samplingRate_top := by
      have htargetTop : target ≠ ⊤ := by
        simp [target, Kakeya.realRpowENN]
      have hDzero : D ≠ 0 := by
        intro hzero
        rw [hzero] at htarget_D
        have htargetPos : 0 < target := by
          dsimp only [target, Kakeya.realRpowENN]
          exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)
        exact (not_le_of_gt htargetPos) htarget_D
      exact ENNReal.div_ne_top htargetTop hDzero
    thinned := thinned
    selected := selected
    thinned_deltaMax := hthinnedDelta
    thinned_card_upper := hthinnedCard
    mass_retention := ?_
    analytic_distinct := hdistinct }⟩
  calc
    (1 / 2 : ENNReal) *
          (target / D) * ambientShading.mass
        ≤ (thinned.restrictShading ambientShading).mass := hthinnedMass
    _ ≤ (conflict + 1) *
        (selectedTubeShading
          (thinned.restrictShading ambientShading) selected).mass := hmass
    _ = (27000000000 * (net.lossFactor * 10 * target) + 1) *
        (selectedTubeShading
          (thinned.restrictShading ambientShading) selected).mass := rfl

lemma pure_wz2_analytic_cleanup_low
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hdelta_small : delta ≤ 1 / 1000)
    (ambient : Kakeya.Streamlined.TubeFamily delta)
    (ambientShading : Kakeya.Streamlined.TubeShading ambient)
    (eta : ℝ) (heta_pos : 0 < eta)
    (net : TubeDensityTestNet delta)
    (hlow : ambient.toBodyFamily.deltaMax ≤
      Kakeya.realRpowENN delta (-eta)) :
    Nonempty
      (PureWZ2AnalyticCleanupData ambient ambientShading
        (Kakeya.realRpowENN delta (-eta))
        (Kakeya.realRpowENN delta (-eta)) net) := by
  let target := Kakeya.realRpowENN delta (-eta)
  let thinned : Kakeya.Streamlined.TubeSubfamily ambient :=
    { family := ambient
      embedding := Function.Embedding.refl _
      tube_eq := fun _ => rfl }
  let conflict : ENNReal :=
    27000000000 * (net.lossFactor * 10 * target)
  have htarget_le : target ≤ net.lossFactor * 10 * target := by
    have hone : (1 : ENNReal) ≤ net.lossFactor * 10 := by
      calc
        (1 : ENNReal) ≤ net.lossFactor := net.one_le_lossFactor
        _ ≤ net.lossFactor * 10 := by
          simpa using mul_le_mul_left' (show (1 : ENNReal) ≤ 10 by norm_num)
            net.lossFactor
    simpa [one_mul] using mul_le_mul_right' hone target
  have hthinnedDelta : thinned.family.toBodyFamily.deltaMax ≤
      net.lossFactor * 10 * target := hlow.trans htarget_le
  have hdegree : ∀ i,
      ((Finset.univ.filter fun j =>
        ¬(thinned.family.tube i).EssentiallyDistinct
          (thinned.family.tube j)).card : ENNReal) ≤ conflict :=
    tubeFamily_nonessential_degree_le_deltaMax
      hdelta hdelta_small thinned.family
      (net.lossFactor * 10 * target) hthinnedDelta
  rcases weighted_essentially_distinct_shading_refinement_of_broad_ennreal_degree
      weighted_essentially_distinct_selection
      thinned.family (thinned.restrictShading ambientShading)
      conflict hdegree with
    ⟨selected, hdistinct, _hunion, hmass⟩
  refine ⟨{
    samplingRate := 1
    samplingRate_eq := by
      change (1 : ENNReal) =
        Kakeya.realRpowENN delta (-eta) /
          Kakeya.realRpowENN delta (-eta)
      exact (ENNReal.div_self
        (by
          exact (ENNReal.ofReal_pos.mpr
            (Real.rpow_pos_of_pos hdelta _)).ne')
        ENNReal.ofReal_ne_top).symm
    samplingRate_zero := one_ne_zero
    samplingRate_top := ENNReal.one_ne_top
    thinned := thinned
    selected := selected
    thinned_deltaMax := hthinnedDelta
    thinned_card_upper := ?_
    mass_retention := ?_
    analytic_distinct := hdistinct }⟩
  · simp [thinned]
    have htwo : (ambient.enncard : ENNReal) ≤ 2 * ambient.enncard := by
      calc
        ambient.enncard = 1 * ambient.enncard := by simp
        _ ≤ 2 * ambient.enncard :=
          mul_le_mul_right' (show (1 : ENNReal) ≤ 2 by norm_num) _
    exact htwo
  · calc
      (1 / 2 : ENNReal) * 1 * ambientShading.mass
          ≤ ambientShading.mass := by
            calc
              (1 / 2 : ENNReal) * 1 * ambientShading.mass
                  ≤ 1 * 1 * ambientShading.mass := by gcongr <;> norm_num
              _ = ambientShading.mass := by ring
      _ = (thinned.restrictShading ambientShading).mass := by rfl
      _ ≤ (conflict + 1) *
          (selectedTubeShading
            (thinned.restrictShading ambientShading) selected).mass := hmass
      _ = (27000000000 * (net.lossFactor * 10 * target) + 1) *
          (selectedTubeShading
            (thinned.restrictShading ambientShading) selected).mass := rfl

end Kakeya.Assouad

end
