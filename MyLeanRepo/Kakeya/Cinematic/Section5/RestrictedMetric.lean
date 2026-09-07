import MyLeanRepo.Kakeya.Cinematic.Geometry
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Intrinsic C2 metric on a parameter subinterval

The globalization following PYZ Lemma 39 restricts a cinematic family to
geometrically shrinking subintervals. This module equips each physical
subinterval with its intrinsic, unscaled `C²` metric and compares that metric
with the ambient unit-interval metric.
-/

noncomputable section

namespace Kakeya.Cinematic

namespace ParameterInterval

abbrev LocalPoint (I : ParameterInterval) :=
  {x : UnitPoint // x ∈ I.carrier}

lemma isClosed_carrier (I : ParameterInterval) : IsClosed I.carrier := by
  exact (isClosed_le continuous_const continuous_subtype_val).inter
    (isClosed_le continuous_subtype_val continuous_const)

noncomputable instance (I : ParameterInterval) : CompactSpace I.LocalPoint :=
  isCompact_iff_compactSpace.mp I.isClosed_carrier.isCompact

end ParameterInterval

namespace C2Function

private def restrictedValue (f : C2Function) (I : ParameterInterval) :
    C(I.LocalPoint, ℝ) :=
  ⟨fun x => f x.1, f.value.continuous.comp continuous_subtype_val⟩

private def restrictedFirstDeriv (f : C2Function) (I : ParameterInterval) :
    C(I.LocalPoint, ℝ) :=
  ⟨fun x => f.firstDeriv x.1,
    f.firstDeriv.continuous.comp continuous_subtype_val⟩

private def restrictedSecondDeriv (f : C2Function) (I : ParameterInterval) :
    C(I.LocalPoint, ℝ) :=
  ⟨fun x => f.secondDeriv x.1,
    f.secondDeriv.continuous.comp continuous_subtype_val⟩

def restrictedJet (f : C2Function) (I : ParameterInterval) :
    C(I.LocalPoint, ℝ) × C(I.LocalPoint, ℝ) × C(I.LocalPoint, ℝ) :=
  (restrictedValue f I, restrictedFirstDeriv f I,
    restrictedSecondDeriv f I)

def restrictedC2Distance (I : ParameterInterval)
    (f g : C2Function) : ℝ :=
  dist (restrictedJet f I) (restrictedJet g I)

lemma abs_value_sub_le_restrictedC2Distance
    (I : ParameterInterval) (f g : C2Function) (x : I.LocalPoint) :
    |f x.1 - g x.1| ≤ restrictedC2Distance I f g := by
  calc
    |f x.1 - g x.1| =
        dist ((restrictedValue f I) x) ((restrictedValue g I) x) := by
      simp [restrictedValue, Real.dist_eq]
    _ ≤ dist (restrictedValue f I) (restrictedValue g I) :=
      ContinuousMap.dist_apply_le_dist x
    _ ≤ restrictedC2Distance I f g := by
      simp [restrictedC2Distance, restrictedJet, Prod.dist_eq]

lemma abs_firstDeriv_sub_le_restrictedC2Distance
    (I : ParameterInterval) (f g : C2Function) (x : I.LocalPoint) :
    |f.firstDeriv x.1 - g.firstDeriv x.1| ≤
      restrictedC2Distance I f g := by
  calc
    |f.firstDeriv x.1 - g.firstDeriv x.1| =
        dist ((restrictedFirstDeriv f I) x)
          ((restrictedFirstDeriv g I) x) := by
      simp [restrictedFirstDeriv, Real.dist_eq]
    _ ≤ dist (restrictedFirstDeriv f I)
        (restrictedFirstDeriv g I) :=
      ContinuousMap.dist_apply_le_dist x
    _ ≤ restrictedC2Distance I f g := by
      simp [restrictedC2Distance, restrictedJet, Prod.dist_eq]

lemma abs_secondDeriv_sub_le_restrictedC2Distance
    (I : ParameterInterval) (f g : C2Function) (x : I.LocalPoint) :
    |f.secondDeriv x.1 - g.secondDeriv x.1| ≤
      restrictedC2Distance I f g := by
  calc
    |f.secondDeriv x.1 - g.secondDeriv x.1| =
        dist ((restrictedSecondDeriv f I) x)
          ((restrictedSecondDeriv g I) x) := by
      simp [restrictedSecondDeriv, Real.dist_eq]
    _ ≤ dist (restrictedSecondDeriv f I)
        (restrictedSecondDeriv g I) :=
      ContinuousMap.dist_apply_le_dist x
    _ ≤ restrictedC2Distance I f g := by
      simp [restrictedC2Distance, restrictedJet, Prod.dist_eq]

lemma restrictedC2Distance_le
    (I : ParameterInterval) (f g : C2Function) :
    restrictedC2Distance I f g ≤ c2Distance f g := by
  have hv : dist (restrictedValue f I) (restrictedValue g I) ≤
      dist f.value g.value := by
    rw [ContinuousMap.dist_le dist_nonneg]
    intro x
    exact ContinuousMap.dist_apply_le_dist x.1
  have hd1 :
      dist (restrictedFirstDeriv f I) (restrictedFirstDeriv g I) ≤
        dist f.firstDeriv g.firstDeriv := by
    rw [ContinuousMap.dist_le dist_nonneg]
    intro x
    exact ContinuousMap.dist_apply_le_dist x.1
  have hd2 :
      dist (restrictedSecondDeriv f I) (restrictedSecondDeriv g I) ≤
        dist f.secondDeriv g.secondDeriv := by
    rw [ContinuousMap.dist_le dist_nonneg]
    intro x
    exact ContinuousMap.dist_apply_le_dist x.1
  rw [restrictedC2Distance, restrictedJet]
  simp only [Prod.dist_eq]
  exact
    max_le (hv.trans (value_dist_le_c2Distance f g))
      (max_le
        (hd1.trans (firstDeriv_dist_le_c2Distance f g))
        (hd2.trans (secondDeriv_dist_le_c2Distance f g)))

lemma c2Distance_le_three_mul_restrictedC2Distance
    {family : Set C2Function} {K D : ℝ}
    (hK : 1 ≤ K) (hfamily : IsCinematicFamily family K D)
    {f g : C2Function} (hf : f ∈ family) (hg : g ∈ family)
    (I : ParameterInterval) :
    c2Distance f g ≤ 3 * K * restrictedC2Distance I f g := by
  let left : UnitPoint := ⟨I.left, I.left_mem⟩
  let x : I.LocalPoint :=
    ⟨left, ⟨le_rfl, I.left_le_right⟩⟩
  have hgap : K⁻¹ * c2Distance f g ≤ jetGap f g x.1 :=
    hfamily.2.2 hf hg x.1
  have hlocal :
      jetGap f g x.1 ≤ 3 * restrictedC2Distance I f g := by
    have h0 := abs_value_sub_le_restrictedC2Distance I f g x
    have h1 := abs_firstDeriv_sub_le_restrictedC2Distance I f g x
    have h2 := abs_secondDeriv_sub_le_restrictedC2Distance I f g x
    simp only [jetGap]
    linarith
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hglobal_gap :
      c2Distance f g ≤ K * jetGap f g x.1 := by
    calc
      c2Distance f g = K * (K⁻¹ * c2Distance f g) := by
        field_simp [hKpos.ne']
      _ ≤ K * jetGap f g x.1 :=
        mul_le_mul_of_nonneg_left hgap hKpos.le
  calc
    c2Distance f g ≤ K * jetGap f g x.1 := hglobal_gap
    _ ≤ K * (3 * restrictedC2Distance I f g) := by gcongr
    _ = 3 * K * restrictedC2Distance I f g := by ring

end C2Function

end Kakeya.Cinematic
