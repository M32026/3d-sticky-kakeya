import MyLeanRepo.Kakeya.CV.MultilinearKakeya
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.MainAssembly

/-!
# Geometry for lattice-cube directional-area columns

Fixed-scale geometric helpers used in the CV Section 4 column budgets.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Kakeya.CV

/-- Coordinatewise parity colour of an integer lattice cube. -/
def latticeCubeColor (q : UnitLatticeCube) : Fin 3 → ZMod 2 :=
  fun i => q i

/-- Distinct closed unit lattice cubes of the same parity colour are disjoint. -/
lemma unitCube_disjoint_of_sameColor_of_ne
    (q r : UnitLatticeCube) (hcolor : latticeCubeColor q = latticeCubeColor r)
    (hne : q ≠ r) :
    Disjoint (unitCube (latticeCubeCenter q))
      (unitCube (latticeCubeCenter r)) := by
  rw [Set.disjoint_left]
  intro x hxq hxr
  exfalso
  apply hne
  funext i
  have hmod : ((q i : ℤ) : ZMod 2) = (r i : ℤ) := by
    exact congrFun hcolor i
  have hdvd : (2 : ℤ) ∣ r i - q i :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (q i) (r i) 2).mp hmod
  have hreal : |((r i : ℝ) - (q i : ℝ))| ≤ 1 := by
    calc
      |((r i : ℝ) - (q i : ℝ))| =
          |((r i : ℝ) - x i) + (x i - (q i : ℝ))| := by ring_nf
      _ ≤ |(r i : ℝ) - x i| + |x i - (q i : ℝ)| :=
        abs_add_le _ _
      _ = |x i - (r i : ℝ)| + |x i - (q i : ℝ)| := by
        rw [abs_sub_comm (r i : ℝ) (x i)]
      _ ≤ 1 / 2 + 1 / 2 := by
        gcongr
        · simpa [latticeCubeCenter] using hxr i
        · simpa [latticeCubeCenter] using hxq i
      _ = 1 := by norm_num
  have hint : |r i - q i| < (2 : ℤ) := by
    have hreal' : |((r i : ℝ) - (q i : ℝ))| < 2 :=
      hreal.trans_lt (by norm_num)
    exact_mod_cast hreal'
  have hzero : r i - q i = 0 :=
    Int.eq_zero_of_abs_lt_dvd hdvd hint
  omega

/--
The production polynomial-cylinder proof gives the unit-tube estimate for
every nonzero polynomial; no singular-set hypothesis is needed for this
stronger internal form.
-/
lemma directionalSurfaceArea_unitTube_le
    (p : MvPolynomial (Fin 3) ℝ) (a e : Point 3) (k : ℕ)
    (hp : p ≠ 0) (hdeg : p.totalDegree ≤ k) (he : ‖e‖ = 1) :
    directionalSurfaceArea e p (polynomialZeroSet p ∩ unitTube a e) ≤
      12 * planeConstant * ENNReal.ofReal Real.pi * (k : ENNReal) := by
  rcases exists_rotation_to_e3 e he with ⟨R, hR⟩
  let p' : MvPolynomial (Fin 3) ℝ := rotatedPoly p R
  have hp'_ne : p' ≠ 0 := rotatedPoly_ne_zero p R hp
  have hp'_deg : p'.totalDegree ≤ k :=
    (rotatedPoly_totalDegree_le p R).trans hdeg
  let S := polynomialZeroSet p ∩ unitTube a e
  let S' := polynomialZeroSet p' ∩ unitTube (R a) e3
  have hS' : R '' S = S' := by
    have hzero : R '' polynomialZeroSet p = polynomialZeroSet p' :=
      rotated_zeroSet p R
    have htube : R '' unitTube a e = unitTube (R a) e3 :=
      rotated_unitTube R a e hR
    have h : R '' S =
        (R '' polynomialZeroSet p) ∩ (R '' unitTube a e) := by
      ext y
      simp only [S, Set.mem_image, Set.mem_inter_iff]
      constructor
      · rintro ⟨x, ⟨hxzero, hxtube⟩, rfl⟩
        exact ⟨⟨x, hxzero, rfl⟩, ⟨x, hxtube, rfl⟩⟩
      · rintro ⟨⟨x, hxzero, rfl⟩, ⟨z, hztube, hz⟩⟩
        have hzx : z = x := R.injective hz
        subst z
        exact ⟨x, ⟨hxzero, hztube⟩, rfl⟩
    rw [h, hzero, htube]
  have htransfer :
      directionalSurfaceArea e p S =
        directionalSurfaceArea e3 p' S' := by
    have h := directionalSurfaceArea_transfer p R e hR S
    rwa [hS'] at h
  rw [htransfer]
  exact directional_estimate_e3 p' (R a) k hp'_ne hp'_deg

private lemma unitCube_diameter_le_two
    (c x y : Point 3) (hx : x ∈ unitCube c) (hy : y ∈ unitCube c) :
    dist x y ≤ 2 := by
  have hxc : dist x c ≤ 1 := by
    simpa [Metric.mem_closedBall] using unitCube_subset_closedBall c hx
  have hyc : dist y c ≤ 1 := by
    simpa [Metric.mem_closedBall] using unitCube_subset_closedBall c hy
  calc
    dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
    _ = dist x c + dist y c := by rw [dist_comm c y]
    _ ≤ 2 := by linarith

/--
If a unit tube meets a lattice cube, the whole cube lies in the closed
radius-three neighborhood of the same affine line.
-/
lemma latticeCube_subset_threeTube_of_meets
    (F : UnitLineFamily) (i : Fin F.card) (q : UnitLatticeCube)
    (hmeet : unitLineMeetsLatticeCube F i q) :
    unitCube (latticeCubeCenter q) ⊆
      {x | Metric.infDist x
        (affineLine (F.base i) (F.direction i)) ≤ 3} := by
  rcases hmeet with ⟨y, hytube, hycube⟩
  intro x hxcube
  have hyline :
      Metric.infDist y (affineLine (F.base i) (F.direction i)) ≤ 1 := by
    simpa [UnitLineFamily.tube, unitTube] using hytube
  have hxy : dist x y ≤ 2 :=
    unitCube_diameter_le_two (latticeCubeCenter q) x y hxcube hycube
  calc
    Metric.infDist x (affineLine (F.base i) (F.direction i)) ≤
        Metric.infDist y (affineLine (F.base i) (F.direction i)) +
          dist x y :=
      Metric.infDist_le_infDist_add_dist
    _ ≤ 3 := by linarith

/--
One fixed finite family of offsets covers every closed radius-three
neighborhood of an affine line by unit tubes with the same direction.
-/
lemma exists_finite_unitTube_cover_threeTube :
    ∃ offsets : Finset (Point 3),
      ∀ (a e : Point 3),
        {x | Metric.infDist x (affineLine a e) ≤ 3} ⊆
          ⋃ c ∈ offsets, unitTube (a + c) e := by
  rcases (isCompact_closedBall (0 : Point 3) 3).finite_cover_balls
      (show (0 : ℝ) < 1 by norm_num) with
    ⟨offsetSet, _, hoffsets_finite, hcover⟩
  classical
  let offsets : Finset (Point 3) := hoffsets_finite.toFinset
  refine ⟨offsets, ?_⟩
  intro a e x hx
  have hline_nonempty : (affineLine a e).Nonempty := by
    refine ⟨a, 0, ?_⟩
    simp
  obtain ⟨z, hzline, hdist⟩ :=
    (isClosed_affineLine a e).exists_infDist_eq_dist hline_nonempty x
  have hxz : dist x z ≤ 3 := by
    rw [← hdist]
    exact hx
  let w : Point 3 := x - z
  have hwball : w ∈ Metric.closedBall (0 : Point 3) 3 := by
    simpa [w, Metric.mem_closedBall, dist_zero_right, dist_eq_norm] using hxz
  have hwcover := hcover hwball
  rcases Set.mem_iUnion.mp hwcover with ⟨c, hwcover⟩
  rcases Set.mem_iUnion.mp hwcover with ⟨hcset, hwc⟩
  have hcoffset : c ∈ offsets := by
    simpa [offsets] using hcset
  apply Set.mem_iUnion₂.mpr
  refine ⟨c, hcoffset, ?_⟩
  rcases hzline with ⟨t, rfl⟩
  have hyline :
      (a + c) + t • e ∈ affineLine (a + c) e := ⟨t, rfl⟩
  have hdist' : dist x ((a + c) + t • e) ≤ 1 := by
    have hwc' : dist (x - (a + t • e)) c < 1 := by
      simpa [w] using hwc
    have heq :
        dist x ((a + c) + t • e) =
          dist (x - (a + t • e)) c := by
      simp only [dist_eq_norm]
      congr 1
      abel
    rw [heq]
    exact hwc'.le
  exact (Metric.infDist_le_dist_of_mem hyline).trans hdist'

lemma directionalSurfaceArea_color_column_le
    (offsets : Finset (Point 3))
    (hoffsets : ∀ (a e : Point 3),
      {x | Metric.infDist x (affineLine a e) ≤ 3} ⊆
        ⋃ c ∈ offsets, unitTube (a + c) e)
    (p : MvPolynomial (Fin 3) ℝ) (k : ℕ)
    (hp : p ≠ 0) (hdeg : p.totalDegree ≤ k)
    (F : UnitLineFamily) (i : Fin F.card)
    (c : Fin 3 → ZMod 2) (active : Finset UnitLatticeCube)
    (hcolor : ∀ q ∈ active, latticeCubeColor q = c)
    (hmeet : ∀ q ∈ active, unitLineMeetsLatticeCube F i q) :
    ∑ q ∈ active,
        directionalSurfaceArea (F.direction i) p
          (polynomialZeroSet p ∩ unitCube (latticeCubeCenter q)) ≤
      (offsets.card : ENNReal) *
        (12 * planeConstant * ENNReal.ofReal Real.pi * (k : ENNReal)) := by
  classical
  let S : active → Set (Point 3) := fun q =>
    polynomialZeroSet p ∩ unitCube (latticeCubeCenter q.1)
  have hS_meas : ∀ q, MeasurableSet (S q) := by
    intro q
    exact (measurableSet_polynomialZeroSet p).inter
      (unitCube_measurableSet (latticeCubeCenter q.1))
  have hS_disj : Pairwise fun q r : active => Disjoint (S q) (S r) := by
    intro q r hqr
    apply Set.disjoint_of_subset_right Set.inter_subset_right
    apply Set.disjoint_of_subset_left Set.inter_subset_right
    have hqcolor : latticeCubeColor q.1 = c := hcolor q.1 q.2
    have hrcolor : latticeCubeColor r.1 = c := hcolor r.1 r.2
    apply unitCube_disjoint_of_sameColor_of_ne q.1 r.1 (hqcolor.trans hrcolor.symm)
    intro h
    apply hqr
    exact Subtype.ext h
  have hunion_three : (⋃ q : active, S q) ⊆
      {x | Metric.infDist x (affineLine (F.base i) (F.direction i)) ≤ 3} := by
    apply Set.iUnion_subset
    intro q
    exact (Set.inter_subset_right.trans
      (latticeCube_subset_threeTube_of_meets F i q.1
        (hmeet q.1 q.2)))
  let Cover : offsets → Set (Point 3) := fun d =>
    polynomialZeroSet p ∩ unitTube (F.base i + d.1) (F.direction i)
  have hunion_cover : (⋃ q : active, S q) ⊆ ⋃ d : offsets, Cover d := by
    intro x hx
    have hxthree := hunion_three hx
    have hxcover := hoffsets (F.base i) (F.direction i) hxthree
    rcases Set.mem_iUnion₂.mp hxcover with ⟨d, hd, hxd⟩
    apply Set.mem_iUnion.mpr
    refine ⟨⟨d, hd⟩, ?_⟩
    exact ⟨by
      rcases Set.mem_iUnion.mp hx with ⟨q, hxq⟩
      exact hxq.1, hxd⟩
  have hcover_bound :
      directionalSurfaceArea (F.direction i) p (⋃ d : offsets, Cover d) ≤
        ∑ d : offsets,
          directionalSurfaceArea (F.direction i) p (Cover d) := by
    dsimp only [directionalSurfaceArea]
    simpa [tsum_fintype] using
      (MeasureTheory.lintegral_iUnion_le (fun d : offsets => Cover d)
        (fun x => ENNReal.ofReal
          ‖inner ℝ (F.direction i) (polynomialUnitNormal p x)‖))
  have h_each : ∀ d : offsets,
      directionalSurfaceArea (F.direction i) p (Cover d) ≤
        12 * planeConstant * ENNReal.ofReal Real.pi * (k : ENNReal) := by
    intro d
    exact directionalSurfaceArea_unitTube_le p (F.base i + d.1)
      (F.direction i) k hp hdeg (F.direction_unit i)
  have hactive :
      ∑ q ∈ active,
          directionalSurfaceArea (F.direction i) p
            (polynomialZeroSet p ∩ unitCube (latticeCubeCenter q)) =
        directionalSurfaceArea (F.direction i) p (⋃ q : active, S q) := by
    rw [← Finset.sum_coe_sort]
    exact (directionalSurfaceArea_finite_iUnion (F.direction i) p S
      hS_disj hS_meas).symm
  calc
    (∑ q ∈ active,
        directionalSurfaceArea (F.direction i) p
          (polynomialZeroSet p ∩ unitCube (latticeCubeCenter q))) =
      directionalSurfaceArea (F.direction i) p (⋃ q : active, S q) := hactive
    _ ≤ directionalSurfaceArea (F.direction i) p (⋃ d : offsets, Cover d) :=
      directionalSurfaceArea_mono _ _ hunion_cover
    _ ≤ ∑ d : offsets, directionalSurfaceArea (F.direction i) p (Cover d) := hcover_bound
    _ ≤ ∑ _d : offsets,
        (12 * planeConstant * ENNReal.ofReal Real.pi * (k : ENNReal)) := by
      exact Finset.sum_le_sum fun d _ => h_each d
    _ = (offsets.card : ENNReal) *
        (12 * planeConstant * ENNReal.ofReal Real.pi * (k : ENNReal)) := by
      simp [Finset.sum_const, nsmul_eq_mul]

lemma directionalSurfaceArea_column_le
    (offsets : Finset (Point 3))
    (hoffsets : ∀ (a e : Point 3),
      {x | Metric.infDist x (affineLine a e) ≤ 3} ⊆
        ⋃ c ∈ offsets, unitTube (a + c) e)
    (p : MvPolynomial (Fin 3) ℝ) (k : ℕ)
    (hp : p ≠ 0) (hdeg : p.totalDegree ≤ k)
    (F : UnitLineFamily) (i : Fin F.card)
    (active : Finset UnitLatticeCube)
    (hmeet : ∀ q ∈ active, unitLineMeetsLatticeCube F i q) :
    ∑ q ∈ active,
        directionalSurfaceArea (F.direction i) p
          (polynomialZeroSet p ∩ unitCube (latticeCubeCenter q)) ≤
      8 * (offsets.card : ENNReal) *
        (12 * planeConstant * ENNReal.ofReal Real.pi * (k : ENNReal)) := by
  classical
  have hsplit :
      ∑ q ∈ active,
          directionalSurfaceArea (F.direction i) p
            (polynomialZeroSet p ∩ unitCube (latticeCubeCenter q)) =
        ∑ c : (Fin 3 → ZMod 2),
          ∑ q ∈ active with latticeCubeColor q = c,
            directionalSurfaceArea (F.direction i) p
              (polynomialZeroSet p ∩ unitCube (latticeCubeCenter q)) := by
    exact (Finset.sum_fiberwise active latticeCubeColor _).symm
  rw [hsplit]
  calc
    _ ≤ ∑ _c : (Fin 3 → ZMod 2),
        ((offsets.card : ENNReal) *
          (12 * planeConstant * ENNReal.ofReal Real.pi * (k : ENNReal))) := by
      apply Finset.sum_le_sum
      intro c _
      apply directionalSurfaceArea_color_column_le offsets hoffsets p k hp hdeg F i c
        (active.filter fun q => latticeCubeColor q = c)
      · intro q hq
        exact (Finset.mem_filter.mp hq).2
      · intro q hq
        exact hmeet q (Finset.mem_filter.mp hq).1
    _ = 8 * (offsets.card : ENNReal) *
        (12 * planeConstant * ENNReal.ofReal Real.pi * (k : ENNReal)) := by
      rw [Finset.sum_const]
      simp [ZMod.card, nsmul_eq_mul]
      ring

/--
The column budget for every polynomial in a bounded-degree parameterization,
including the zero polynomial.
-/
lemma parameterDirectionalSurfaceArea_column_le
    {k : ℕ} (P : PolynomialParameterization k)
    (offsets : Finset (Point 3))
    (hoffsets : ∀ (a e : Point 3),
      {x | Metric.infDist x (affineLine a e) ≤ 3} ⊆
        ⋃ c ∈ offsets, unitTube (a + c) e)
    (y : CoefficientSpace P.dim)
    (F : UnitLineFamily) (i : Fin F.card)
    (active : Finset UnitLatticeCube)
    (hmeet : ∀ q ∈ active, unitLineMeetsLatticeCube F i q) :
    ∑ q ∈ active,
        directionalSurfaceArea (F.direction i) (parameterPolynomial P y)
          (polynomialZeroSet (parameterPolynomial P y) ∩
            unitCube (latticeCubeCenter q)) ≤
      8 * (offsets.card : ENNReal) *
        (12 * planeConstant * ENNReal.ofReal Real.pi * (k : ENNReal)) := by
  by_cases hp : parameterPolynomial P y = 0
  · simp_rw [hp, directionalSurfaceArea_zero]
    simp
  · exact directionalSurfaceArea_column_le offsets hoffsets
      (parameterPolynomial P y) k hp (P.equiv y).property F i active hmeet


end Kakeya.CV
