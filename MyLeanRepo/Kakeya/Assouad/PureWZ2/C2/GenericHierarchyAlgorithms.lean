import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredHierarchyIteration
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# BodyFamily-generic popularity refinement and volume retention

Generalized versions of the UTS-free Cor 26 hierarchy algorithms that work
with ANY `BodyFamily`, including `WZ1PaperTubeShading` (= `Shading (wz1PaperBodyFamily F)`).

The originals are typed on `TubeShading F` but only use the generic `Shading`
API (`carrier`, `union`, `pointMultiplicity`, `measurable_carrier`).
-/

noncomputable section

open MeasureTheory Set Metric Finset ENNReal

namespace Kakeya.Assouad

/-- Generic subshading: one shading is pointwise contained in another. -/
def IsSubshadingGeneric {BF : Kakeya.Streamlined.BodyFamily}
    (Z Y : Kakeya.Streamlined.Shading BF) : Prop :=
  ∀ i, Z.carrier i ⊆ Y.carrier i

/-- Generic subshading implies union subset. -/
lemma IsSubshadingGeneric.union_subset {BF : Kakeya.Streamlined.BodyFamily}
    {Z Y : Kakeya.Streamlined.Shading BF}
    (h : IsSubshadingGeneric Z Y) : Z.union ⊆ Y.union := by
  intro p hp
  rcases hp with ⟨i, hpi⟩
  exact ⟨i, h i hpi⟩

/-! ## Common spatial restriction

The Corollary-5.6 proof repeatedly keeps a previously chosen
constant-multiplicity shading but restricts every carrier to the same spatial
set.  Taking that set to be the union of a later refinement preserves the
later union while retaining the earlier point multiplicity on that union.
-/

/-- Restrict every carrier of `source` to the shaded union of `mask`. -/
def spatialRestrictionToUnionGeneric
    {BF : Kakeya.Streamlined.BodyFamily}
    (source mask : Kakeya.Streamlined.Shading BF) :
    Kakeya.Streamlined.Shading BF where
  carrier index := source.carrier index ∩ mask.union
  measurable_carrier index :=
    (source.measurable_carrier index).inter (by
      have hunion : mask.union = ⋃ index : Fin BF.card, mask.carrier index := by
        ext point
        simp [Kakeya.Streamlined.Shading.union]
      rw [hunion]
      exact MeasurableSet.iUnion fun index => mask.measurable_carrier index)
  subset_body index := Set.inter_subset_left.trans (source.subset_body index)

@[simp] lemma spatialRestrictionToUnionGeneric_carrier
    {BF : Kakeya.Streamlined.BodyFamily}
    (source mask : Kakeya.Streamlined.Shading BF) (index : Fin BF.card) :
    (spatialRestrictionToUnionGeneric source mask).carrier index =
      source.carrier index ∩ mask.union := rfl

/-- A common spatial restriction is a pointwise subshading of its source. -/
lemma spatialRestrictionToUnionGeneric_subshading
    {BF : Kakeya.Streamlined.BodyFamily}
    (source mask : Kakeya.Streamlined.Shading BF) :
    IsSubshadingGeneric
      (spatialRestrictionToUnionGeneric source mask) source := by
  intro index point hpoint
  exact hpoint.1

/-- If the mask is already a subshading of the source, the common spatial
restriction has exactly the mask's shaded union. -/
lemma spatialRestrictionToUnionGeneric_union_eq
    {BF : Kakeya.Streamlined.BodyFamily}
    {source mask : Kakeya.Streamlined.Shading BF}
    (hmask : IsSubshadingGeneric mask source) :
    (spatialRestrictionToUnionGeneric source mask).union = mask.union := by
  ext point
  constructor
  · rintro ⟨index, _hsource, hmaskUnion⟩
    exact hmaskUnion
  · intro hpoint
    rcases hpoint with ⟨index, hindex⟩
    exact ⟨index, hmask index hindex, ⟨index, hindex⟩⟩

/-- On its retained union, a common spatial restriction has exactly the point
multiplicity of the source shading. -/
lemma spatialRestrictionToUnionGeneric_pointMultiplicity_eq
    {BF : Kakeya.Streamlined.BodyFamily}
    {source mask : Kakeya.Streamlined.Shading BF}
    {point : Point3}
    (hpoint : point ∈
      (spatialRestrictionToUnionGeneric source mask).union) :
    (spatialRestrictionToUnionGeneric source mask).pointMultiplicity point =
      source.pointMultiplicity point := by
  classical
  have hmaskUnion : point ∈ mask.union := by
    rcases hpoint with ⟨_index, _hsource, hmaskUnion⟩
    exact hmaskUnion
  unfold Kakeya.Streamlined.Shading.pointMultiplicity
  congr 1
  apply Finset.filter_congr
  intro index _
  simp only [spatialRestrictionToUnionGeneric_carrier, Set.mem_inter_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, hmaskUnion⟩⟩

/-- A common spatial restriction inherits a constant-multiplicity band from
its source. -/
lemma spatialRestrictionToUnionGeneric_constantMultiplicity
    {BF : Kakeya.Streamlined.BodyFamily}
    {source mask : Kakeya.Streamlined.Shading BF}
    {lower upper : ℕ}
    (hconstant : source.HasConstantMultiplicity lower upper) :
    (spatialRestrictionToUnionGeneric source mask).HasConstantMultiplicity
      lower upper := by
  intro point hpoint
  rw [spatialRestrictionToUnionGeneric_pointMultiplicity_eq hpoint]
  exact hconstant point
    ((spatialRestrictionToUnionGeneric_subshading source mask).union_subset
      hpoint)

/-- For paper shadings, intersecting two unions of whole delta-cells still
gives a whole-cell shading. -/
lemma spatialRestrictionToUnionGeneric_cubical
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source mask : WZ1PaperTubeShading family}
    (hsource : WZ1PaperIsCubicalShading source)
    (hmask : WZ1PaperIsCubicalShading mask) :
    WZ1PaperIsCubicalShading
      (spatialRestrictionToUnionGeneric source mask) := by
  intro index point hpoint other hother
  have hsourceOther : other ∈ source.carrier index :=
    hsource index point hpoint.1 hother
  have hmaskOther : other ∈ mask.union := by
    rcases hpoint.2 with ⟨maskIndex, hmaskPoint⟩
    exact ⟨maskIndex, hmask maskIndex point hmaskPoint hother⟩
  exact ⟨hsourceOther, hmaskOther⟩

/-! ## Generic thinShading -/

/-- Thin a generic shading by removing all points whose height belongs to H. -/
def thinShadingGeneric {BF : Kakeya.Streamlined.BodyFamily}
    (Z : Kakeya.Streamlined.Shading BF) (H : Set ℝ)
    (hH_meas : MeasurableSet H) :
    Kakeya.Streamlined.Shading BF :=
  let heightMap : Point3 → ℝ := fun p => p 2
  have h_height_meas : Measurable heightMap := by
    have h_cont : Continuous heightMap :=
      PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2
    exact h_cont.measurable
  { carrier := fun i => Z.carrier i \ heightMap ⁻¹' H
    measurable_carrier := fun i =>
      (Z.measurable_carrier i).diff (h_height_meas hH_meas)
    subset_body := fun i =>
      Set.Subset.trans (fun x hx => hx.1) (Z.subset_body i) }

/-- The thinned shading is a subshading of the original. -/
lemma thinShadingGeneric_subshading {BF : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading BF} {H : Set ℝ} {hH_meas : MeasurableSet H} :
    IsSubshadingGeneric (thinShadingGeneric Z H hH_meas) Z := by
  intro i x hx
  exact hx.1

/-- Union of thinned shading. -/
lemma thinShadingGeneric_union {BF : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading BF} {H : Set ℝ} {hH_meas : MeasurableSet H} :
    (thinShadingGeneric Z H hH_meas).union = Z.union \ {p : Point3 | p 2 ∈ H} := by
  ext p
  simp only [thinShadingGeneric, Kakeya.Streamlined.Shading.union, Set.mem_sdiff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩⟩
    exact ⟨⟨i, h1⟩, h2⟩
  · rintro ⟨⟨i, h1⟩, h2⟩
    exact ⟨i, ⟨h1, h2⟩⟩

/-- Point multiplicity is preserved by horizontal thinning. -/
lemma thinShadingGeneric_same_multiplicity {BF : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading BF} {H : Set ℝ} {hH_meas : MeasurableSet H}
    {p : Point3} (hp : p ∈ (thinShadingGeneric Z H hH_meas).union) :
    (thinShadingGeneric Z H hH_meas).pointMultiplicity p = Z.pointMultiplicity p := by
  classical
  have hpH : p 2 ∉ H := by
    have h : p ∈ (thinShadingGeneric Z H hH_meas).union := hp
    rw [thinShadingGeneric_union] at h
    exact h.2
  have h1 : ∀ (i : Fin BF.card), p ∈ (thinShadingGeneric Z H hH_meas).carrier i ↔ p ∈ Z.carrier i := by
    intro i
    simp only [thinShadingGeneric, Set.mem_sdiff]
    exact ⟨fun h => h.1, fun h => ⟨h, hpH⟩⟩
  have h_eq : (Finset.univ.filter fun i : Fin BF.card => p ∈ (thinShadingGeneric Z H hH_meas).carrier i) =
      (Finset.univ.filter fun i : Fin BF.card => p ∈ Z.carrier i) := by
    apply Finset.ext
    intro i
    simpa using h1 i
  have h_main : (thinShadingGeneric Z H hH_meas).pointMultiplicity p = Z.pointMultiplicity p := by
    unfold Kakeya.Streamlined.Shading.pointMultiplicity
    exact congr_arg Finset.card h_eq
  exact h_main

/-! ## Generic volume in slab/core -/

/-- Volume of the shaded union inside a horizontal slab [a, b]. -/
def volumeInSlabGeneric {BF : Kakeya.Streamlined.BodyFamily}
    (Z : Kakeya.Streamlined.Shading BF) (a b : ℝ) : ENNReal :=
  MeasureTheory.volume (Z.union ∩ {p : Point3 | p 2 ∈ Set.Icc a b})

/-- Volume of the shaded union inside a trapezoid core. -/
def volumeInCoreGeneric {BF : Kakeya.Streamlined.BodyFamily}
    (Z : Kakeya.Streamlined.Shading BF)
    (t : WZ1VerticalTrapezoid) : ENNReal :=
  volumeInSlabGeneric Z t.left t.right

/-! ## Generic single-level thinning with raw cores -/

/--
Select popular trapezoids by volume threshold and thin the shading by keeping
only heights in the RAW popular cores (no shrinking).
-/
lemma single_level_thin_only_generic
    {BF : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading BF}
    {T : Finset WZ1VerticalTrapezoid}
    {A_max : ENNReal} {threshold : ℝ}
    (h_thresh_pos : 0 ≤ threshold)
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a)) :
    ∃ (Z' : Kakeya.Streamlined.Shading BF)
      (popular : Finset WZ1VerticalTrapezoid),
      IsSubshadingGeneric Z' Z ∧
      (∀ t, t ∈ popular ↔ t ∈ T ∧ volumeInCoreGeneric Z t > A_max * ENNReal.ofReal threshold) ∧
      (∀ (z : ℝ), horizontalSlice Z'.union z ≠ ∅ → ∃ t ∈ popular, z ∈ t.core) ∧
      (Z'.union = Z.union \ {p : Point3 | p 2 ∉ (⋃ s ∈ popular, s.core)}) ∧
      (∀ p ∈ Z'.union, Z'.pointMultiplicity p = Z.pointMultiplicity p) := by
  classical
  let popular : Finset WZ1VerticalTrapezoid :=
    T.filter (fun t => volumeInCoreGeneric Z t > A_max * ENNReal.ofReal threshold)
  have h_popular_iff : ∀ t, t ∈ popular ↔
      t ∈ T ∧ volumeInCoreGeneric Z t > A_max * ENNReal.ofReal threshold := by
    intro t; simp [popular] <;> tauto
  let popularCores : Set ℝ := ⋃ t ∈ popular, t.core
  have h_meas : MeasurableSet popularCores := by
    have h : (popular : Set WZ1VerticalTrapezoid).Countable := Set.to_countable _
    exact MeasurableSet.biUnion h (fun t _ => measurableSet_Icc)
  let H : Set ℝ := popularCoresᶜ
  have hH_meas : MeasurableSet H := h_meas.compl
  let Z' : Kakeya.Streamlined.Shading BF := thinShadingGeneric Z H hH_meas
  have hZ'_sub : IsSubshadingGeneric Z' Z := thinShadingGeneric_subshading
  have hZ'_union : Z'.union = Z.union \ {p : Point3 | p 2 ∈ H} := thinShadingGeneric_union
  have h_coverage : ∀ (z : ℝ), horizontalSlice Z'.union z ≠ ∅ → ∃ t ∈ popular, z ∈ t.core := by
    intro z hz
    have h_z_in : z ∈ popularCores := by
      by_contra h
      have hz' : z ∈ H := h
      have h_empty : horizontalSlice Z'.union z = ∅ := by
        ext p
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hp
        have hpe : p ∈ Z'.union ∧ p 2 = z := by
          simp only [horizontalSlice, Set.mem_setOf_eq] at hp <;> exact hp
        rw [hZ'_union] at hpe
        have h2 : p 2 ∉ H := hpe.1.2
        rw [hpe.2] at h2
        exact h2 hz'
      rw [h_empty] at hz <;> simp at hz
    simp only [popularCores, Set.mem_iUnion] at h_z_in
    rcases h_z_in with ⟨t, ht, hzcore⟩
    exact ⟨t, ht, hzcore⟩
  have h_union_eq : Z'.union = Z.union \ {p : Point3 | p 2 ∉ (⋃ s ∈ popular, s.core)} := by
    have hH_eq : {p : Point3 | p 2 ∈ H} = {p : Point3 | p 2 ∉ (⋃ s ∈ popular, s.core)} := by
      ext p; simp [H, popularCores] <;> tauto
    rw [hZ'_union, hH_eq]
  have h_same_mult : ∀ p ∈ Z'.union, Z'.pointMultiplicity p = Z.pointMultiplicity p :=
    fun p hp => thinShadingGeneric_same_multiplicity (hp := hp)
  exact ⟨Z', popular, hZ'_sub, h_popular_iff, h_coverage, h_union_eq, h_same_mult⟩

/-! ## Generic shrink trapezoid to active points -/

/-- Construct a shrunk trapezoid whose left and right endpoints are given active points. -/
def shrinkTrapezoidToPointsGeneric
    (t : WZ1VerticalTrapezoid)
    (a b : ℝ) (hab : a < b)
    (ha_in : a ∈ t.core) (hb_in : b ∈ t.core) :
    WZ1VerticalTrapezoid :=
  { left := a
    right := b
    left_lt_right := hab
    slope := t.slope
    intercept := t.intercept
    height := t.height
    height_pos := t.height_pos }

lemma shrinkTrapezoidToPointsGeneric_spec
    (t : WZ1VerticalTrapezoid)
    (a b : ℝ) (hab : a < b)
    (ha_in : a ∈ t.core) (hb_in : b ∈ t.core) :
    let t' := shrinkTrapezoidToPointsGeneric t a b hab ha_in hb_in
    t'.core ⊆ t.core ∧
    t'.left = a ∧ t'.right = b ∧
    t'.slope = t.slope ∧
    t'.intercept = t.intercept ∧
    t'.height = t.height := by
  dsimp only [shrinkTrapezoidToPointsGeneric]
  constructor
  · intro z hz
    have h1 : a ≤ z := (Set.mem_Icc.mp hz).1
    have h2 : z ≤ b := (Set.mem_Icc.mp hz).2
    have h3 : t.left ≤ a := (Set.mem_Icc.mp ha_in).1
    have h4 : b ≤ t.right := (Set.mem_Icc.mp hb_in).2
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Generic active points from volume -/

/--
If z is active in Z and z is not in the removed height set H,
then z remains active in the thinned shading Z'.
-/
lemma active_height_preserved_generic
    {BF : Kakeya.Streamlined.BodyFamily}
    {Z Z' : Kakeya.Streamlined.Shading BF} {H : Set ℝ}
    (hZ'_union : Z'.union = Z.union \ {p : Point3 | p 2 ∈ H})
    {z : ℝ} (hz_active : z ∈ activeSetOf Z.union) (hz_notin_H : z ∉ H) :
    z ∈ activeSetOf Z'.union := by
  have h_ne : (horizontalSlice Z.union z).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hz_active
  rcases h_ne with ⟨p, hp⟩
  have hpZ : p ∈ Z.union := by
    simp only [horizontalSlice, Set.mem_setOf_eq] at hp <;> exact hp.1
  have hpz : p 2 = z := by
    simp only [horizontalSlice, Set.mem_setOf_eq] at hp <;> exact hp.2
  have hpinZ' : p ∈ Z'.union := by
    rw [hZ'_union]
    have h2 : p 2 ∉ H := by rw [hpz]; exact hz_notin_H
    exact ⟨hpZ, h2⟩
  have hslice : p ∈ horizontalSlice Z'.union z := by
    simp only [horizontalSlice, Set.mem_setOf_eq] <;> exact ⟨hpinZ', hpz⟩
  exact Set.nonempty_iff_ne_empty.mp ⟨p, hslice⟩

/--
Given a volume lower bound on the shaded union inside a trapezoid core,
and an upper bound A_max on the area of each horizontal slice, prove
there exist active heights a,b in the core with b-a > L.
-/
lemma active_points_from_volume_generic
    {BF : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading BF}
    {t : WZ1VerticalTrapezoid}
    {A_max : ENNReal} {L : ℝ} (hL_pos : 0 ≤ L)
    (h_vol : volume (Z.union ∩ horizontalSlab t.left t.right) >
      A_max * ENNReal.ofReal L)
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a)) :
    ∃ (a b : ℝ), a ∈ activeSetOf Z.union ∩ t.core ∧
      b ∈ activeSetOf Z.union ∩ t.core ∧ b - a > L := by
  let A : Set ℝ := activeSetOf Z.union ∩ t.core
  have hA_nonempty : A.Nonempty := by
    by_contra h
    have h' : A = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have h_empty : Z.union ∩ horizontalSlab t.left t.right = ∅ := by
      ext p
      simp only [Set.mem_empty_iff_false, Set.mem_setOf_eq, iff_false]
      intro hp
      have hz : p 2 ∈ t.core := by
        simp only [horizontalSlab, Set.mem_setOf_eq] at hp <;> exact hp.2
      have h_active : p 2 ∈ activeSetOf Z.union := by
        have hslice : p ∈ horizontalSlice Z.union (p 2) := by
          simp [horizontalSlice, hp.1]
        exact Set.nonempty_iff_ne_empty.mp ⟨p, hslice⟩
      have h_in_A : p 2 ∈ A := ⟨h_active, hz⟩
      rw [h'] at h_in_A <;> simp at h_in_A
    rw [h_empty] at h_vol
    simp at h_vol <;> exact h_vol
  let i : ℝ := sInf A
  let s : ℝ := sSup A
  have h_bdd_below : BddBelow A := ⟨t.left, fun x hx => (Set.mem_Icc.mp hx.2).1⟩
  have h_bdd_above : BddAbove A := ⟨t.right, fun x hx => (Set.mem_Icc.mp hx.2).2⟩
  have h1 : ∀ x ∈ A, i ≤ x := fun x hx => csInf_le h_bdd_below hx
  have h2 : ∀ x ∈ A, x ≤ s := fun x hx => le_csSup h_bdd_above hx
  by_cases h_span : s - i ≤ L
  · have h3 : A ⊆ Set.Icc i (i + L) := by
      intro x hx
      have h4 : i ≤ x := h1 x hx
      have h5 : x ≤ s := h2 x hx
      have h6 : x ≤ i + L := by linarith
      exact ⟨h4, h6⟩
    have h4 : Z.union ∩ horizontalSlab t.left t.right ⊆
        Z.union ∩ horizontalSlab i (i + L) := by
      intro p hp
      have hz : p 2 ∈ t.core := by
        simp only [horizontalSlab, Set.mem_setOf_eq] at hp <;> exact hp.2
      have h_active : p 2 ∈ activeSetOf Z.union := by
        have hslice : p ∈ horizontalSlice Z.union (p 2) := by
          simp [horizontalSlice, hp.1]
        exact Set.nonempty_iff_ne_empty.mp ⟨p, hslice⟩
      have h_in_A : p 2 ∈ A := ⟨h_active, hz⟩
      have h5 : p 2 ∈ Set.Icc i (i + L) := h3 h_in_A
      exact ⟨hp.1, by simpa [horizontalSlab] using h5⟩
    have h5 : volume (Z.union ∩ horizontalSlab t.left t.right) ≤
        volume (Z.union ∩ horizontalSlab i (i + L)) := measure_mono h4
    have h6 : i ≤ i + L := by linarith
    have h7 : volume (Z.union ∩ horizontalSlab i (i + L)) ≤
        A_max * ENNReal.ofReal L := by
      have h8 := h_slab_bound i (i + L) h6
      have h9 : (i + L) - i = L := by ring
      rw [h9] at h8
      exact h8
    have h10 : volume (Z.union ∩ horizontalSlab t.left t.right) ≤
        A_max * ENNReal.ofReal L := le_trans h5 h7
    exfalso
    exact not_le.mpr h_vol h10
  · have h_span' : s - i > L := by linarith
    have h_exists_a : ∃ (a : ℝ), a ∈ A ∧ a < i + (s - i - L) / 2 := by
      by_contra h
      have h_all : ∀ x ∈ A, i + (s - i - L) / 2 ≤ x := by
        simpa [not_exists, not_and, not_lt] using h
      have h_i_ge : i + (s - i - L) / 2 ≤ i :=
        le_csInf hA_nonempty h_all
      linarith
    have h_exists_b : ∃ (b : ℝ), b ∈ A ∧ b > s - (s - i - L) / 2 := by
      by_contra h
      have h_all : ∀ x ∈ A, x ≤ s - (s - i - L) / 2 := by
        simpa [not_exists, not_and, not_lt] using h
      have h_s_le : s ≤ s - (s - i - L) / 2 :=
        csSup_le hA_nonempty h_all
      linarith
    rcases h_exists_a with ⟨a, haA, ha_lt⟩
    rcases h_exists_b with ⟨b, hbA, hb_gt⟩
    have h_diff : b - a > L := by linarith
    exact ⟨a, b, haA, hbA, h_diff⟩

/-! ## Generic single-level popularity refinement with endpoint anchoring -/

/--
Single-level popularity selection and endpoint anchoring (generic BodyFamily version).

Select trapezoids with sufficient volume in their core, shrink them to active
endpoints, and thin Z to retain only heights covered by shrunk popular cores.
-/
lemma single_level_popularity_refine_generic
    {BF : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading BF}
    {T : Finset WZ1VerticalTrapezoid}
    {A_max : ENNReal} {L : ℝ}
    (hL_pos : 0 ≤ L)
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a)) :
    ∃ (Z' : Kakeya.Streamlined.Shading BF)
      (T' : Finset WZ1VerticalTrapezoid),
      IsSubshadingGeneric Z' Z ∧
      (∀ t' ∈ T', horizontalSlice Z'.union t'.left ≠ ∅ ∧
                        horizontalSlice Z'.union t'.right ≠ ∅) ∧
      (∀ t' ∈ T', L ≤ t'.length) ∧
      (∀ t' ∈ T', ∃ t ∈ T,
        t'.core ⊆ t.core ∧ t'.slope = t.slope ∧ t'.intercept = t.intercept ∧ t'.height = t.height) ∧
      (∀ (z : ℝ), horizontalSlice Z'.union z ≠ ∅ →
        ∃ t' ∈ T', z ∈ t'.core) ∧
      (∀ p ∈ Z'.union, Z'.pointMultiplicity p = Z.pointMultiplicity p) := by
  classical
  let popular : Finset WZ1VerticalTrapezoid :=
    T.filter (fun t => volumeInCoreGeneric Z t > A_max * ENNReal.ofReal L)
  have h_popular_iff : ∀ t, t ∈ popular ↔
      t ∈ T ∧ volumeInCoreGeneric Z t > A_max * ENNReal.ofReal L := by
    intro t; simp [popular]
  let P (t : WZ1VerticalTrapezoid) : Prop :=
    ∃ (a b : ℝ), a ∈ activeSetOf Z.union ∩ t.core ∧
      b ∈ activeSetOf Z.union ∩ t.core ∧ b - a > L
  have h_main : ∀ t ∈ popular, P t := by
    intro t ht
    have h_vol : volumeInCoreGeneric Z t > A_max * ENNReal.ofReal L :=
      (h_popular_iff t).mp ht |>.2
    exact active_points_from_volume_generic hL_pos h_vol h_slab_bound
  choose a b ha hb hdiff using h_main
  let shrunk (t : WZ1VerticalTrapezoid) : WZ1VerticalTrapezoid :=
    if ht : t ∈ popular then
      shrinkTrapezoidToPointsGeneric t (a t ht) (b t ht)
        (by linarith [hdiff t ht]) (ha t ht).2 (hb t ht).2
    else t
  let T' : Finset WZ1VerticalTrapezoid := popular.image shrunk
  let popularCores : Set ℝ := ⋃ t' ∈ T', t'.core
  have h_popularCores_meas : MeasurableSet popularCores := by
    have h : (T' : Set WZ1VerticalTrapezoid).Countable := Set.to_countable _
    exact MeasurableSet.biUnion h (fun t' _ => measurableSet_Icc)
  let H : Set ℝ := popularCoresᶜ
  have hH_meas : MeasurableSet H := h_popularCores_meas.compl
  let Z' : Kakeya.Streamlined.Shading BF := thinShadingGeneric Z H hH_meas
  have hZ'_sub : IsSubshadingGeneric Z' Z := thinShadingGeneric_subshading
  have hZ'_union : Z'.union = Z.union \ {p : Point3 | p 2 ∈ H} := thinShadingGeneric_union
  have h_shrunk_spec : ∀ (t : WZ1VerticalTrapezoid) (ht : t ∈ popular),
      (shrunk t).left = a t ht ∧ (shrunk t).right = b t ht ∧
      (shrunk t).core ⊆ t.core ∧ (shrunk t).slope = t.slope ∧
      (shrunk t).intercept = t.intercept ∧
      (shrunk t).height = t.height ∧ L ≤ (shrunk t).length := by
    intro t ht
    dsimp only [shrunk]
    rw [dif_pos ht]
    have h_spec := shrinkTrapezoidToPointsGeneric_spec t (a t ht) (b t ht)
      (by linarith [hdiff t ht]) (ha t ht).2 (hb t ht).2
    have h_len : L ≤ (b t ht) - (a t ht) := le_of_lt (hdiff t ht)
    exact ⟨h_spec.2.1, h_spec.2.2.1, h_spec.1, h_spec.2.2.2.1, h_spec.2.2.2.2.1, h_spec.2.2.2.2.2, h_len⟩
  have h_coverage : ∀ (z : ℝ), horizontalSlice Z'.union z ≠ ∅ →
      ∃ t' ∈ T', z ∈ t'.core := by
    intro z hz
    have h_z_in_popularCores : z ∈ popularCores := by
      by_contra h
      have hz' : z ∈ H := h
      have h_empty : horizontalSlice Z'.union z = ∅ := by
        ext p
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hp
        have hpe : p ∈ Z'.union ∧ p 2 = z := by
          simp only [horizontalSlice, Set.mem_setOf_eq] at hp <;> exact hp
        rw [hZ'_union] at hpe
        have h2 : p 2 ∉ H := hpe.1.2
        rw [hpe.2] at h2
        exact h2 hz'
      rw [h_empty] at hz <;> simp at hz
    simp only [popularCores, Set.mem_iUnion] at h_z_in_popularCores
    rcases h_z_in_popularCores with ⟨t', ht', hzcore⟩
    exact ⟨t', ht', hzcore⟩
  have h_active_endpoints : ∀ t' ∈ T',
      horizontalSlice Z'.union t'.left ≠ ∅ ∧
      horizontalSlice Z'.union t'.right ≠ ∅ := by
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    have h_spec := h_shrunk_spec t ht
    have h_at_active : a t ht ∈ activeSetOf Z.union := (ha t ht).1
    have h_bt_active : b t ht ∈ activeSetOf Z.union := (hb t ht).1
    have h_at_in_core : a t ht ∈ (shrunk t).core := by
      have h : (shrunk t).left = a t ht := h_spec.1
      rw [←h]
      exact ⟨le_refl _, (shrunk t).left_lt_right.le⟩
    have h_bt_in_core : b t ht ∈ (shrunk t).core := by
      have h : (shrunk t).right = b t ht := h_spec.2.1
      rw [←h]
      exact ⟨(shrunk t).left_lt_right.le, le_refl _⟩
    have h_st_in_T' : shrunk t ∈ T' := Finset.mem_image_of_mem shrunk ht
    have h_at_in_pc : a t ht ∈ popularCores := by
      simpa [popularCores, Set.mem_iUnion] using ⟨shrunk t, h_st_in_T', h_at_in_core⟩
    have h_bt_in_pc : b t ht ∈ popularCores := by
      simpa [popularCores, Set.mem_iUnion] using ⟨shrunk t, h_st_in_T', h_bt_in_core⟩
    have h_at_notin_H : a t ht ∉ H := by simpa [H] using h_at_in_pc
    have h_bt_notin_H : b t ht ∉ H := by simpa [H] using h_bt_in_pc
    have h_at_active' : a t ht ∈ activeSetOf Z'.union :=
      active_height_preserved_generic hZ'_union h_at_active h_at_notin_H
    have h_bt_active' : b t ht ∈ activeSetOf Z'.union :=
      active_height_preserved_generic hZ'_union h_bt_active h_bt_notin_H
    have h_left_eq : (shrunk t).left = a t ht := h_spec.1
    have h_right_eq : (shrunk t).right = b t ht := h_spec.2.1
    constructor
    · rw [h_left_eq]; exact h_at_active'
    · rw [h_right_eq]; exact h_bt_active'
  have h_length : ∀ t' ∈ T', L ≤ t'.length := by
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    rcases h_shrunk_spec t ht with ⟨_, _, _, _, _, _, h_len⟩
    exact h_len
  have h_provenance : ∀ t' ∈ T', ∃ t ∈ T,
      t'.core ⊆ t.core ∧ t'.slope = t.slope ∧ t'.intercept = t.intercept ∧ t'.height = t.height := by
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    have h_t_in_T : t ∈ T := (h_popular_iff t).mp ht |>.1
    rcases h_shrunk_spec t ht with ⟨_, _, h_core, h_slope, h_int, h_hgt, _⟩
    exact ⟨t, h_t_in_T, h_core, h_slope, h_int, h_hgt⟩
  exact ⟨Z', T', hZ'_sub, h_active_endpoints, h_length, h_provenance, h_coverage,
    fun p hp => thinShadingGeneric_same_multiplicity (hp := hp)⟩

/-! ## Generic multi-level thinning -/

/--
Process levels 0..j coarsest to finest using `single_level_thin_only_generic`.
-/
lemma multi_level_thin_only_up_to_generic
    {N : ℕ} {BF : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading BF}
    {rawTrapezoids : Fin N → Finset WZ1VerticalTrapezoid}
    {A_max : ENNReal}
    {L : Fin N → ℝ}
    (C : ℝ)
    (hC_nonneg : 0 ≤ C)
    (hL_pos : ∀ j, 0 ≤ L j)
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a)) :
    ∀ (j : ℕ), j < N →
      ∀ (Z_j : Kakeya.Streamlined.Shading BF),
        IsSubshadingGeneric Z_j Z →
    ∃ (Z_out : Kakeya.Streamlined.Shading BF)
      (P : Fin N → Finset WZ1VerticalTrapezoid),
      IsSubshadingGeneric Z_out Z_j ∧
      (∀ (i : Fin N), (i : ℕ) ≤ j → P i ⊆ rawTrapezoids i) ∧
      (∀ (i : Fin N), (i : ℕ) ≤ j →
        ∀ (z : ℝ), horizontalSlice Z_out.union z ≠ ∅ → ∃ t ∈ P i, z ∈ t.core) := by
  intro j
  induction j with
  | zero =>
    intro hj Z_j hZ_j_sub
    let j_fin : Fin N := ⟨0, hj⟩
    have h_slab_bound_j : ∀ (a b : ℝ), a ≤ b →
        volume (Z_j.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a) := by
      intro a b hab
      have h1 : Z_j.union ∩ horizontalSlab a b ⊆ Z.union ∩ horizontalSlab a b :=
        Set.inter_subset_inter_left _ hZ_j_sub.union_subset
      exact (measure_mono h1).trans (h_slab_bound a b hab)
    have h_thresh_pos : 0 ≤ C * L j_fin := mul_nonneg hC_nonneg (hL_pos j_fin)
    rcases single_level_thin_only_generic h_thresh_pos h_slab_bound_j with
      ⟨Z_out, P_0, hZ_out_sub, h_spec_0, h_cov_0, _⟩
    let P : Fin N → Finset WZ1VerticalTrapezoid :=
      fun i => if (i : ℕ) = 0 then P_0 else ∅
    refine ⟨Z_out, P, hZ_out_sub, ?_⟩
    constructor
    · intro i hi
      have h_i_zero : (i : ℕ) = 0 := by omega
      have hP : P i = P_0 := by dsimp only [P]; rw [if_pos h_i_zero]
      have h_i_eq : i = j_fin := by apply Fin.ext; exact h_i_zero
      rw [hP, h_i_eq]
      intro t ht
      exact ((h_spec_0 t).mp ht).1
    · intro i hi z hz
      have h_i_zero : (i : ℕ) = 0 := by omega
      have hP : P i = P_0 := by dsimp only [P]; rw [if_pos h_i_zero]
      rw [hP]; exact h_cov_0 z hz
  | succ j' ih =>
    intro hj Z_j hZ_j_sub
    have h_j'_lt_N : j' < N := by omega
    rcases ih h_j'_lt_N Z_j hZ_j_sub with
      ⟨Z_prev, P_prev, hZ_prev_sub, h_sub_prev, h_cov_prev⟩
    let j_fin : Fin N := ⟨j'.succ, hj⟩
    have h_slab_bound_prev : ∀ (a b : ℝ), a ≤ b →
        volume (Z_prev.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a) := by
      intro a b hab
      let h_trans : IsSubshadingGeneric Z_prev Z := fun i => Set.Subset.trans (hZ_prev_sub i) (hZ_j_sub i)
      have h1 : Z_prev.union ∩ horizontalSlab a b ⊆ Z.union ∩ horizontalSlab a b :=
        Set.inter_subset_inter_left _ h_trans.union_subset
      exact (measure_mono h1).trans (h_slab_bound a b hab)
    have h_thresh_pos : 0 ≤ C * L j_fin := mul_nonneg hC_nonneg (hL_pos j_fin)
    rcases single_level_thin_only_generic h_thresh_pos h_slab_bound_prev with
      ⟨Z_out, P_j, hZ_out_sub, h_spec_j, h_cov_j, _⟩
    let P : Fin N → Finset WZ1VerticalTrapezoid :=
      fun i => if (i : ℕ) = j'.succ then P_j else P_prev i
    refine ⟨Z_out, P, fun i => Set.Subset.trans (hZ_out_sub i) (hZ_prev_sub i), ?_⟩
    constructor
    · intro i hi
      by_cases h_i_j : (i : ℕ) = j'.succ
      · have hP : P i = P_j := by dsimp only [P]; rw [if_pos h_i_j]
        have h_i_eq : i = j_fin := by apply Fin.ext; exact h_i_j
        rw [hP, h_i_eq]
        intro t ht; exact ((h_spec_j t).mp ht).1
      · have h_i_le : (i : ℕ) ≤ j' := by omega
        have h_ne : (i : ℕ) ≠ j'.succ := h_i_j
        have hP : P i = P_prev i := by dsimp only [P]; rw [if_neg h_ne]
        rw [hP]; exact h_sub_prev i h_i_le
    · intro i hi z hz
      by_cases h_i_j : (i : ℕ) = j'.succ
      · have hP : P i = P_j := by dsimp only [P]; rw [if_pos h_i_j]
        rw [hP]; exact h_cov_j z hz
      · have h_i_le : (i : ℕ) ≤ j' := by omega
        have h_ne : (i : ℕ) ≠ j'.succ := h_i_j
        have hP : P i = P_prev i := by dsimp only [P]; rw [if_neg h_ne]
        rw [hP]
        have h_z_prev : horizontalSlice Z_prev.union z ≠ ∅ := by
          have h2 : Z_out.union ⊆ Z_prev.union := hZ_out_sub.union_subset
          have h3 : horizontalSlice Z_out.union z ⊆ horizontalSlice Z_prev.union z :=
            fun p hp => ⟨h2 hp.1, hp.2⟩
          exact Set.Nonempty.mono h3 (Set.nonempty_iff_ne_empty.mpr hz) |>.ne_empty
        exact h_cov_prev i h_i_le z h_z_prev

/--
Top-level multi-level thinning with raw popular cores.
Processes all N levels coarsest to finest.
-/
lemma multi_level_thin_only_generic
    {N : ℕ} {BF : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading BF}
    {rawTrapezoids : Fin N → Finset WZ1VerticalTrapezoid}
    {A_max : ENNReal}
    {L : Fin N → ℝ}
    (C : ℝ)
    (hC_nonneg : 0 ≤ C)
    (hN_pos : 0 < N)
    (hL_pos : ∀ j, 0 ≤ L j)
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a)) :
    ∃ (Z1 : Kakeya.Streamlined.Shading BF)
      (P : Fin N → Finset WZ1VerticalTrapezoid),
      IsSubshadingGeneric Z1 Z ∧
      (∀ j, P j ⊆ rawTrapezoids j) ∧
      (∀ j, ∀ z, horizontalSlice Z1.union z ≠ ∅ → ∃ t ∈ P j, z ∈ t.core) := by
  have h_last_lt : N - 1 < N := by omega
  have h_id : IsSubshadingGeneric Z Z := fun i => Set.Subset.refl (Z.carrier i)
  rcases multi_level_thin_only_up_to_generic C hC_nonneg hL_pos h_slab_bound (N - 1) h_last_lt Z h_id with
    ⟨Z1, P, hZ1_sub, h_sub, h_cov⟩
  refine ⟨Z1, P, hZ1_sub, ?_⟩
  constructor
  · intro j
    have hj_le : (j : ℕ) ≤ N - 1 := by omega
    exact h_sub j hj_le
  · intro j z hz
    have hj_le : (j : ℕ) ≤ N - 1 := by omega
    exact h_cov j hj_le z hz

/-!
## Slab volume bounds for paper shadings

Paper shadings are contained in `axisBox 2 2 2 = [-1,1]^3`, so the x and y
coordinate diameters are at most 2. This gives the slab volume bound
`4 * (b-a)`, without requiring UTS or AD.
-/

/--
Volume of a set contained in `axisBox 2 2 2` inside a horizontal slab
is at most `4 * (b - a)`.
Generic version works for any `BodyFamily` shading.
-/
lemma axisBox_slab_volume_bound_generic
    {BF : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading BF}
    (hZ_box : Z.union ⊆ Kakeya.Streamlined.axisBox 2 2 2)
    {a b : ℝ} (_ha : a ≤ b) :
    MeasureTheory.volume (Z.union ∩ horizontalSlab a b) ≤
      (4 : ENNReal) * ENNReal.ofReal (b - a) := by
  let S : Set Point3 := Z.union ∩ horizontalSlab a b
  have h_union_eq : Z.union = ⋃ i : Fin BF.card, Z.carrier i := by
    ext x
    simp [Kakeya.Streamlined.Shading.union, Set.mem_iUnion]
  have h_union_meas : MeasurableSet Z.union := by
    rw [h_union_eq]
    exact MeasurableSet.iUnion (fun i => Z.measurable_carrier i)
  have hS_meas : MeasurableSet S := by
    have h_cont : Continuous (fun p : Point3 => p 2) :=
      PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2
    have h_slab_meas : MeasurableSet (horizontalSlab a b) :=
      h_cont.measurable measurableSet_Icc
    exact h_union_meas.inter h_slab_meas
  have h_coord_bound : ∀ (i : Fin 3), ∀ p ∈ S, |p i| ≤ 1 := by
    intro i p hp
    have h5 : p ∈ Z.union := hp.1
    have h6 : p ∈ Kakeya.Streamlined.axisBox 2 2 2 := hZ_box h5
    have h7 : |p 0| ≤ 1 ∧ |p 1| ≤ 1 ∧ |p 2| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using h6
    fin_cases i <;> tauto
  have h_ediam_bound : ∀ (i : Fin 3),
      Metric.ediam ((fun p : Point3 => p i) '' S) ≤ 2 := by
    intro i
    have h9 : ((fun p : Point3 => p i) '' S) ⊆ Set.Icc (-1 : ℝ) 1 := by
      intro x hx
      rcases hx with ⟨p, hp, rfl⟩
      have h10 : |p i| ≤ 1 := h_coord_bound i p hp
      have h11 : -1 ≤ p i ∧ p i ≤ 1 := by
        rw [abs_le] at h10; exact h10
      exact ⟨h11.1, h11.2⟩
    have h12 : ∀ (x : ℝ), x ∈ ((fun p : Point3 => p i) '' S) →
        ∀ (y : ℝ), y ∈ ((fun p : Point3 => p i) '' S) → dist x y ≤ 2 := by
      intro x hx y hy
      have h13 : x ∈ Set.Icc (-1 : ℝ) 1 := h9 hx
      have h14 : y ∈ Set.Icc (-1 : ℝ) 1 := h9 hy
      have h15 : -2 ≤ x - y := by linarith [h13.1, h13.2, h14.1, h14.2]
      have h16 : x - y ≤ 2 := by linarith [h13.1, h13.2, h14.1, h14.2]
      have h17 : |x - y| ≤ 2 := by rw [abs_le]; exact ⟨h15, h16⟩
      simpa [Real.dist_eq] using h17
    have h15 : Metric.ediam ((fun p : Point3 => p i) '' S) ≤ ENNReal.ofReal 2 :=
      Metric.ediam_le_of_forall_dist_le h12
    simpa using h15
  let F_equiv : Point3 ≃ᵐ (Fin 3 → ℝ) :=
    { toFun := WithLp.ofLp (p := 2)
      invFun := WithLp.toLp (p := 2)
      left_inv := WithLp.toLp_ofLp (p := 2)
      right_inv := WithLp.ofLp_toLp (p := 2)
      measurable_toFun := (PiLp.volume_preserving_ofLp (ι := Fin 3)).measurable
      measurable_invFun := (PiLp.continuous_toLp 2 (β := fun (_ : Fin 3) => ℝ)).measurable }
  let S' : Set (Fin 3 → ℝ) := F_equiv '' S
  have hpres : MeasurePreserving F_equiv volume volume :=
    PiLp.volume_preserving_ofLp (ι := Fin 3)
  have hvol : volume S = volume S' := by
    have hmap : Measure.map F_equiv volume = volume := hpres.map_eq
    have hpre : F_equiv ⁻¹' S' = S := Set.preimage_image_eq _ F_equiv.injective
    have hS'_meas : MeasurableSet S' := F_equiv.measurableSet_image.mpr hS_meas
    have h2 : volume (F_equiv ⁻¹' S') = Measure.map F_equiv volume S' :=
      (Measure.map_apply hpres.measurable hS'_meas).symm
    rw [hpre] at h2; exact h2.trans (by rw [hmap])
  rw [hvol]
  have h2 : volume S' ≤ ∏ i : Fin 3, Metric.ediam (Function.eval i '' S') :=
    Real.volume_pi_le_prod_diam S'
  have hproj : ∀ (i : Fin 3), (Function.eval i '' S') = (fun p : Point3 => p i) '' S := by
    intro i; ext x; simp [S']; constructor <;> rintro ⟨p, hp, rfl⟩ <;> exact ⟨p, hp, rfl⟩
  have h3 : Metric.ediam (Function.eval 0 '' S') ≤ 2 := by rw [hproj 0]; exact h_ediam_bound 0
  have h4 : Metric.ediam (Function.eval 1 '' S') ≤ 2 := by rw [hproj 1]; exact h_ediam_bound 1
  have h_z_diam : Metric.ediam (Function.eval 2 '' S') ≤ ENNReal.ofReal (b - a) := by
    rw [hproj 2]
    have h10 : ∀ (x : ℝ), x ∈ (fun p : Point3 => p 2) '' S →
        ∀ (y : ℝ), y ∈ (fun p : Point3 => p 2) '' S → dist x y ≤ b - a := by
      intro x hx y hy
      rcases hx with ⟨p, hp, rfl⟩
      rcases hy with ⟨q, hq, rfl⟩
      have hx1 : a ≤ p 2 := hp.2.1
      have hx2 : p 2 ≤ b := hp.2.2
      have hy1 : a ≤ q 2 := hq.2.1
      have hy2 : q 2 ≤ b := hq.2.2
      have h : |p 2 - q 2| ≤ b - a := by rw [abs_le]; constructor <;> linarith
      simpa [Real.dist_eq] using h
    exact Metric.ediam_le_of_forall_dist_le h10
  have h_prod : (∏ i : Fin 3, Metric.ediam (Function.eval i '' S')) =
      Metric.ediam (Function.eval 0 '' S') *
      Metric.ediam (Function.eval 1 '' S') *
      Metric.ediam (Function.eval 2 '' S') := by
    simp [Fin.prod_univ_succ] <;> ring
  rw [h_prod] at h2
  have h_mul : Metric.ediam (Function.eval 0 '' S') * Metric.ediam (Function.eval 1 '' S') ≤ (4 : ENNReal) := by
    calc
      Metric.ediam (Function.eval 0 '' S') * Metric.ediam (Function.eval 1 '' S')
        ≤ (2 : ENNReal) * Metric.ediam (Function.eval 1 '' S') := by gcongr
      _ ≤ (2 : ENNReal) * (2 : ENNReal) := by gcongr
      _ = (4 : ENNReal) := by norm_num
  have h6 : (Metric.ediam (Function.eval 0 '' S') *
      Metric.ediam (Function.eval 1 '' S') *
      Metric.ediam (Function.eval 2 '' S')) ≤
      (4 : ENNReal) * Metric.ediam (Function.eval 2 '' S') := by
    have h8 : (Metric.ediam (Function.eval 0 '' S') * Metric.ediam (Function.eval 1 '' S')) *
        Metric.ediam (Function.eval 2 '' S') ≤
        (4 : ENNReal) * Metric.ediam (Function.eval 2 '' S') := by
      gcongr
    simpa [mul_assoc] using h8
  exact h2.trans (h6.trans (by gcongr))
/--
Paper shadings are contained in `axisBox 2 2 2` because each carrier is
contained in `wz1PaperTubeCarrier`, which intersects `axisBox 2 2 2`.
-/
lemma paperShading_subset_axisBox
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Z : WZ1PaperTubeShading F} :
    Z.union ⊆ Kakeya.Streamlined.axisBox 2 2 2 := by
  intro p hp
  rcases hp with ⟨i, hpi⟩
  have h1 : p ∈ wz1PaperTubeCarrier (F.tube i) := Z.subset_body i hpi
  simp only [wz1PaperTubeCarrier, Set.mem_inter_iff] at h1
  exact h1.2
/--
Slab volume bound for paper shadings: volume in `[a,b]` ≤ `4 * (b-a)`.
This is the pure WZ2 replacement for UTS-dependent AD slab bounds.
Uses the geometric fact that paper tubes are cropped to `[-1,1]^3`.
-/
lemma paper_slab_volume_bound
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Z : WZ1PaperTubeShading F}
    {a b : ℝ} (_ha : a ≤ b) :
    MeasureTheory.volume (Z.union ∩ horizontalSlab a b) ≤
      (4 : ENNReal) * ENNReal.ofReal (b - a) :=
  axisBox_slab_volume_bound_generic paperShading_subset_axisBox _ha
end Kakeya.Assouad
