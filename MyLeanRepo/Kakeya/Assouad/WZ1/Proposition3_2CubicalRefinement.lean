import MyLeanRepo.Kakeya.Assouad.MultiplicityPigeonholing
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2LeafStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition5FiberRefinement

/-!
# Cubical refinement infrastructure for WZ1 Proposition 3.2

Membership in a cubical shading is constant on each normalized standard cell.
Consequently its point multiplicity and every dyadic multiplicity band are
also constant on each cell. This proves that the historical multiplicity
pigeonholing and the union of independently selected parent shadings preserve
the cubical certificate required by the paper-aligned Lemma 3.3.
-/

noncomputable section

namespace Kakeya.Assouad

theorem WZ1IsCubicalShading.carrier_mem_iff_of_same_cell
    {rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily rho}
    {shading : Kakeya.Streamlined.TubeShading family}
    (hcubical : WZ1IsCubicalShading shading)
    (index : Fin family.card)
    {first second : Point3}
    (hsame :
      wz1StandardGridIndex rho first =
        wz1StandardGridIndex rho second) :
    first ∈ shading.carrier index ↔
      second ∈ shading.carrier index := by
  constructor
  · intro hfirst
    apply
      hcubical index first hfirst
    exact
      (mem_wz1StandardGridCube _ _ _).mpr hsame.symm
  · intro hsecond
    apply
      hcubical index second hsecond
    exact
      (mem_wz1StandardGridCube _ _ _).mpr hsame

theorem WZ1IsCubicalShading.pointMultiplicity_eq_of_same_cell
    {rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily rho}
    {shading : Kakeya.Streamlined.TubeShading family}
    (hcubical : WZ1IsCubicalShading shading)
    {first second : Point3}
    (hsame :
      wz1StandardGridIndex rho first =
        wz1StandardGridIndex rho second) :
    shading.pointMultiplicity first =
      shading.pointMultiplicity second := by
  classical
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  apply Finset.filter_congr
  intro index _
  exact
    hcubical.carrier_mem_iff_of_same_cell index hsame

theorem WZ1IsCubicalShading.dyadicMultiplicityBand_mem_iff_of_same_cell
    {rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily rho}
    {shading : Kakeya.Streamlined.TubeShading family}
    (hcubical : WZ1IsCubicalShading shading)
    (level : ℕ)
    {first second : Point3}
    (hsame :
      wz1StandardGridIndex rho first =
        wz1StandardGridIndex rho second) :
    first ∈ dyadicMultiplicityBand shading level ↔
      second ∈ dyadicMultiplicityBand shading level := by
  have hmultiplicity :=
    hcubical.pointMultiplicity_eq_of_same_cell hsame
  simp only [dyadicMultiplicityBand, Set.mem_setOf_eq]
  rw [hmultiplicity]

theorem WZ1IsCubicalShading.dyadicBandSubshading
    {rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily rho}
    {shading : Kakeya.Streamlined.TubeShading family}
    (hcubical : WZ1IsCubicalShading shading)
    (level : ℕ) :
    WZ1IsCubicalShading
      (dyadicBandSubshading shading level) := by
  intro index first hfirst second hsecond
  rcases hfirst with ⟨hfirstCarrier, hfirstBand⟩
  have hsame :
      wz1StandardGridIndex rho second =
        wz1StandardGridIndex rho first :=
    (mem_wz1StandardGridCube _ _ _).mp hsecond
  have hsecondCarrier :
      second ∈ shading.carrier index :=
    (hcubical.carrier_mem_iff_of_same_cell index hsame.symm).mp
      hfirstCarrier
  have hsecondBand :
      second ∈ dyadicMultiplicityBand shading level :=
    (hcubical.dyadicMultiplicityBand_mem_iff_of_same_cell
      level hsame.symm).mp hfirstBand
  exact ⟨hsecondCarrier, hsecondBand⟩

/--
The quantitative fine-multiplicity refinement preserves whole standard cells
when its input shading is cubical.
-/
theorem fine_multiplicity_refinement_explicit_cubical
    {delta sigma epsilon eta : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hepsilon : 0 < epsilon)
    (heta : 0 < eta) (heta_3le : 3 * eta < epsilon)
    {family : Kakeya.Streamlined.TubeFamily delta}
    {uniform : Kakeya.Streamlined.UniformTubeStructure family}
    {shading : Kakeya.Streamlined.TubeShading family}
    (hfamily_nonempty : family.Nonempty)
    (hfamily_distinct : family.IsEssentiallyDistinct)
    (huniform :
      uniform.uniformity ≤ Kakeya.realRpowENN delta (-eta))
    (hfrostman :
      uniform.IsFrostmanAtEveryScale
        (Kakeya.realRpowENN delta (-eta)))
    (hdense :
      shading.IsLambdaDense (Kakeya.realRpowENN delta eta))
    (hvolume :
      MeasureTheory.volume shading.union ≤
        Kakeya.realRpowENN delta (sigma - eta))
    (hcardinality :
      2 * (Nat.log 2 family.card + 1 : ENNReal) ≤
        Kakeya.realRpowENN delta (eta - epsilon))
    (hmass :
      Kakeya.realRpowENN delta (2 * eta) ≥
        4 * Kakeya.realRpowENN delta (epsilon - eta))
    (hcubical : WZ1IsCubicalShading shading) :
    ∃ (refined : Kakeya.Streamlined.TubeShading family)
        (multiplicity : ℕ),
      IsSubshading refined shading ∧
      WZ1IsCubicalShading refined ∧
      0 < multiplicity ∧
      refined.HasConstantMultiplicity
        multiplicity (2 * multiplicity) ∧
      Kakeya.realRpowENN delta (-sigma + epsilon) ≤
        (multiplicity : ENNReal) ∧
      refined.mass ≥
        Kakeya.realRpowENN delta epsilon *
          family.toBodyFamily.mass := by
  rcases
      fine_multiplicity_refinement_explicit_with_band
        hdelta hdelta_one hsigma hsigma_one
        hepsilon heta heta_3le
        hfamily_nonempty hfamily_distinct huniform hfrostman
        hdense hvolume hcardinality hmass with
    ⟨refined, multiplicity, hsubshading,
      hmultiplicity, hconstant, hlower, hrefinedMass,
      level, hlevel⟩
  refine
    ⟨refined, multiplicity, hsubshading, ?_,
      hmultiplicity, hconstant, hlower, hrefinedMass⟩
  rw [hlevel]
  exact hcubical.dyadicBandSubshading level

/-- Restrict a shading by retaining complete tube indices. -/
def wz1IndexSubshading
    {rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily rho}
    (shading : Kakeya.Streamlined.TubeShading family)
    (selected : Finset (Fin family.card)) :
    Kakeya.Streamlined.TubeShading family where
  carrier index :=
    if index ∈ selected then shading.carrier index else ∅
  measurable_carrier index := by
    by_cases hindex : index ∈ selected
    · rw [if_pos hindex]
      exact shading.measurable_carrier index
    · rw [if_neg hindex]
      exact MeasurableSet.empty
  subset_body index := by
    by_cases hindex : index ∈ selected
    · rw [if_pos hindex]
      exact shading.subset_body index
    · rw [if_neg hindex]
      exact Set.empty_subset _

theorem wz1IndexSubshading_isSubshading
    {rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily rho}
    (shading : Kakeya.Streamlined.TubeShading family)
    (selected : Finset (Fin family.card)) :
    IsSubshading
      (wz1IndexSubshading shading selected) shading := by
  intro index
  by_cases hindex : index ∈ selected
  · simp [wz1IndexSubshading, hindex]
  · simp [wz1IndexSubshading, hindex]

theorem WZ1IsCubicalShading.indexSubshading
    {rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily rho}
    {shading : Kakeya.Streamlined.TubeShading family}
    (hcubical : WZ1IsCubicalShading shading)
    (selected : Finset (Fin family.card)) :
    WZ1IsCubicalShading
      (wz1IndexSubshading shading selected) := by
  intro index first hfirst second hsecond
  by_cases hindex : index ∈ selected
  · rw [show
        (wz1IndexSubshading shading selected).carrier index =
          shading.carrier index by
        simp [wz1IndexSubshading, hindex]] at hfirst ⊢
    exact hcubical index first hfirst hsecond
  · rw [show
        (wz1IndexSubshading shading selected).carrier index = ∅ by
        simp [wz1IndexSubshading, hindex]] at hfirst
    exact hfirst.elim

theorem unionParentShadings_cubical
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {uniform : Kakeya.Streamlined.UniformTubeStructure family}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {retained : Finset (Fin (uniform.coarse rho).card)}
    {source :
      Fin (uniform.coarse rho).card →
        Kakeya.Streamlined.TubeShading family}
    (hcubical :
      ∀ parent ∈ retained,
        WZ1IsCubicalShading (source parent)) :
    WZ1IsCubicalShading
      (unionParentShadings retained source) := by
  intro index first hfirst second hsecond
  let parent := (uniform.cover rho).parent index
  by_cases hparent : parent ∈ retained
  · have hcarrier :
        (unionParentShadings retained source).carrier index =
          (source parent).carrier index := by
      exact unionParentShadings_carrier_of_mem hparent
    rw [hcarrier] at hfirst ⊢
    exact
      hcubical parent hparent index first hfirst hsecond
  · have hcarrier :
        (unionParentShadings retained source).carrier index = ∅ := by
      exact unionParentShadings_carrier_of_not_mem hparent
    rw [hcarrier] at hfirst
    exact hfirst.elim

end Kakeya.Assouad
