import MyLeanRepo.Kakeya.Streamlined.Estimates

/-!
# Composition of factorings and Frostman constants

Given factorings `P1 : Factoring fine middle` and
`P2 : Factoring middle coarse`, construct their composition and transfer a
fiberwise Frostman bound under explicit density, overlap, and volume-ratio
hypotheses.
-/

noncomputable section

open MeasureTheory Set Finset
open scoped Classical

namespace Kakeya.Streamlined

namespace Factoring

/-- Compose two factorings `fine → middle → coarse`. -/
def compose {fine middle coarse : BodyFamily}
    (P1 : Factoring fine middle)
    (P2 : Factoring middle coarse) :
    Factoring fine coarse where
  parent i := P2.parent (P1.parent i)
  parent_surjective := by
    intro k
    rcases P2.parent_surjective k with ⟨j, hj⟩
    rcases P1.parent_surjective j with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change P2.parent (P1.parent i) = k
    rw [hi, hj]
  contained i :=
    (P1.contained i).trans (P2.contained (P1.parent i))

@[simp]
lemma compose_parent
    {fine middle coarse : BodyFamily}
    (P1 : Factoring fine middle)
    (P2 : Factoring middle coarse)
    (i : Fin fine.card) :
    (P1.compose P2).parent i = P2.parent (P1.parent i) :=
  rfl

/-- A composed fiber is the union of the corresponding first-level fibers. -/
lemma compose_fiberIndices
    {fine middle coarse : BodyFamily}
    {P1 : Factoring fine middle} {P2 : Factoring middle coarse}
    {k : Fin coarse.card} :
    (P1.compose P2).fiberIndices k =
      Finset.biUnion (P2.fiberIndices k)
        fun j => P1.fiberIndices j := by
  ext i
  simp only [fiberIndices, compose, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_biUnion]
  constructor
  · intro h
    exact ⟨P1.parent i, by simpa using h, rfl⟩
  · rintro ⟨j, hj, hji⟩
    have : P1.parent i = j := by simpa using hji
    rwa [this]

/-- Distinct first-level fibers are disjoint. -/
lemma compose_fibers_disjoint
    {fine middle coarse : BodyFamily}
    {P1 : Factoring fine middle} {P2 : Factoring middle coarse}
    {k : Fin coarse.card} :
    ∀ j1 ∈ P2.fiberIndices k, ∀ j2 ∈ P2.fiberIndices k,
      j1 ≠ j2 →
        Disjoint (P1.fiberIndices j1) (P1.fiberIndices j2) := by
  intro j1 _ j2 _ hne
  simp only [fiberIndices, Finset.disjoint_left, Finset.mem_filter,
    Finset.mem_univ, true_and]
  intro i hi1 hi2
  exact hne (hi1.symm.trans hi2)

/-- Fiber mass of the composition is the sum of first-level fiber masses. -/
lemma compose_fiberMass
    {fine middle coarse : BodyFamily}
    {P1 : Factoring fine middle} {P2 : Factoring middle coarse}
    {k : Fin coarse.card} :
    (P1.compose P2).fiberMass k =
      ∑ j ∈ P2.fiberIndices k, P1.fiberMass j := by
  rw [fiberMass, compose_fiberIndices]
  rw [Finset.sum_biUnion compose_fibers_disjoint]
  <;> rfl

/--
Contained fiber mass of the composition is the sum of first-level contained
fiber masses.
-/
lemma compose_fiberContainedMass
    {fine middle coarse : BodyFamily}
    {P1 : Factoring fine middle} {P2 : Factoring middle coarse}
    {k : Fin coarse.card} {K : Set Point3} :
    (P1.compose P2).fiberContainedMass k K =
      ∑ j ∈ P2.fiberIndices k, P1.fiberContainedMass j K := by
  have h_filter_biUnion :
      ((P2.fiberIndices k).biUnion fun j => P1.fiberIndices j).filter
          (fun i : Fin fine.card => (fine.body i).carrier ⊆ K) =
        (P2.fiberIndices k).biUnion
          fun j =>
            (P1.fiberIndices j).filter
              fun i : Fin fine.card => (fine.body i).carrier ⊆ K := by
    ext i
    simp [Finset.mem_biUnion]
    <;> tauto
  calc
    (P1.compose P2).fiberContainedMass k K
        =
      ∑ i ∈ ((P1.compose P2).fiberIndices k).filter
          (fun i => (fine.body i).carrier ⊆ K),
        (fine.body i).volume := by
          rfl
    _ =
      ∑ i ∈ ((P2.fiberIndices k).biUnion
          fun j => P1.fiberIndices j).filter
          (fun i => (fine.body i).carrier ⊆ K),
        (fine.body i).volume := by
          rw [compose_fiberIndices]
    _ =
      ∑ i ∈ (P2.fiberIndices k).biUnion
          (fun j =>
            (P1.fiberIndices j).filter
              fun i => (fine.body i).carrier ⊆ K),
        (fine.body i).volume := by
          rw [h_filter_biUnion]
    _ =
      ∑ j ∈ P2.fiberIndices k,
        ∑ i ∈ (P1.fiberIndices j).filter
            (fun i => (fine.body i).carrier ⊆ K),
          (fine.body i).volume := by
          let Q : Fin fine.card → Prop :=
            fun i => (fine.body i).carrier ⊆ K
          have hdisj :
              ∀ j1 ∈ P2.fiberIndices k,
                ∀ j2 ∈ P2.fiberIndices k,
                  j1 ≠ j2 →
                    Disjoint
                      ((P1.fiberIndices j1).filter Q)
                      ((P1.fiberIndices j2).filter Q) := by
            intro j1 hj1 j2 hj2 hne
            exact
              (compose_fibers_disjoint j1 hj1 j2 hj2 hne).mono
                (Finset.filter_subset Q (P1.fiberIndices j1))
                (Finset.filter_subset Q (P1.fiberIndices j2))
          exact Finset.sum_biUnion hdisj
    _ = ∑ j ∈ P2.fiberIndices k, P1.fiberContainedMass j K := by
          apply Finset.sum_congr rfl
          intro j _
          rfl

/--
Regroup Frostman fibers along a second parent map when every final parent
volume is bounded by a fixed multiple of each middle-parent volume occurring
in its fiber.  The final factoring need not factor through a geometric
middle-to-coarse containment: only the displayed equality of parent maps is
used.  In particular, no number-of-pieces factor occurs.
-/
lemma regroup_frostman_of_parent_volume_ratio
    {fine middle coarse : BodyFamily}
    (P1 : Factoring fine middle) (Q : Factoring fine coarse)
    (group : Fin middle.card → Fin coarse.card)
    (hparent : ∀ index, Q.parent index = group (P1.parent index))
    {C Cvol : ENNReal}
    (hFrostman : P1.FibersAreCFrostman C)
    (hmiddleConvex : middle.IsConvex)
    (hvolume : ∀ finalParent middleParent,
      group middleParent = finalParent →
        (coarse.body finalParent).volume ≤
          Cvol * (middle.body middleParent).volume) :
    Q.FibersAreCFrostman (Cvol * C) := by
  classical
  intro finalParent test htestConvex htestSubset
  let selectedMiddle : Finset (Fin middle.card) :=
    Finset.univ.filter fun middleParent =>
      group middleParent = finalParent
  let localTest : Fin middle.card → Set Point3 := fun middleParent =>
    test ∩ (middle.body middleParent).carrier
  have hfiberIndices :
      Q.fiberIndices finalParent =
        selectedMiddle.biUnion fun middleParent =>
          P1.fiberIndices middleParent := by
    ext index
    simp only [Factoring.fiberIndices, selectedMiddle,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro hindex
      refine ⟨P1.parent index, ?_, rfl⟩
      rwa [hparent index] at hindex
    · rintro ⟨middleParent, hmiddleParent, hindex⟩
      rw [hparent index, hindex]
      exact hmiddleParent
  have hdisjoint :
      ∀ first ∈ selectedMiddle, ∀ second ∈ selectedMiddle,
        first ≠ second →
          Disjoint (P1.fiberIndices first) (P1.fiberIndices second) := by
    intro first _ second _ hne
    simp only [Factoring.fiberIndices, Finset.disjoint_left,
      Finset.mem_filter, Finset.mem_univ, true_and]
    intro index hfirst hsecond
    exact hne (hfirst.symm.trans hsecond)
  have hrestrict : ∀ middleParent ∈ selectedMiddle,
      P1.fiberContainedMass middleParent test =
        P1.fiberContainedMass middleParent (localTest middleParent) := by
    intro middleParent _
    dsimp only [Factoring.fiberContainedMass]
    congr 1
    apply Finset.filter_congr
    intro index hindex
    have hparentEq : P1.parent index = middleParent :=
      (Finset.mem_filter.mp hindex).2
    have hmiddle :
        (fine.body index).carrier ⊆
          (middle.body middleParent).carrier := by
      simpa [hparentEq] using P1.contained index
    exact ⟨fun h => Set.subset_inter h hmiddle,
      fun h => h.trans Set.inter_subset_left⟩
  have hpiece : ∀ middleParent ∈ selectedMiddle,
      P1.fiberContainedMass middleParent test *
          (coarse.body finalParent).volume ≤
        (Cvol * C) * P1.fiberMass middleParent * volume test := by
    intro middleParent hmiddleParent
    have hgroup : group middleParent = finalParent :=
      (Finset.mem_filter.mp hmiddleParent).2
    calc
      P1.fiberContainedMass middleParent test *
            (coarse.body finalParent).volume
          ≤ P1.fiberContainedMass middleParent test *
              (Cvol * (middle.body middleParent).volume) := by
        gcongr
        exact hvolume finalParent middleParent hgroup
      _ = Cvol *
          (P1.fiberContainedMass middleParent test *
            (middle.body middleParent).volume) := by ring
      _ = Cvol *
          (P1.fiberContainedMass middleParent (localTest middleParent) *
            (middle.body middleParent).volume) := by
        rw [hrestrict middleParent hmiddleParent]
      _ ≤ Cvol *
          (C * P1.fiberMass middleParent *
            volume (localTest middleParent)) := by
        exact mul_le_mul_left'
          (hFrostman middleParent (localTest middleParent)
            (htestConvex.inter (hmiddleConvex middleParent))
            Set.inter_subset_right) Cvol
      _ ≤ Cvol *
          (C * P1.fiberMass middleParent * volume test) := by
        have htestVolume :
            volume (localTest middleParent) ≤ volume test :=
          measure_mono Set.inter_subset_left
        gcongr
      _ = (Cvol * C) * P1.fiberMass middleParent * volume test := by
        ring
  have hfiberContainedMass :
      Q.fiberContainedMass finalParent test =
        ∑ middleParent ∈ selectedMiddle,
          P1.fiberContainedMass middleParent test := by
    have hfilterBiUnion :
        (selectedMiddle.biUnion fun middleParent =>
            P1.fiberIndices middleParent).filter
              (fun index => (fine.body index).carrier ⊆ test) =
          selectedMiddle.biUnion fun middleParent =>
            (P1.fiberIndices middleParent).filter
              (fun index => (fine.body index).carrier ⊆ test) := by
      ext index
      simp only [Finset.mem_filter, Finset.mem_biUnion]
      tauto
    dsimp only [Factoring.fiberContainedMass]
    rw [hfiberIndices, hfilterBiUnion]
    rw [Finset.sum_biUnion]
    intro first hfirst second hsecond hne
    exact (hdisjoint first hfirst second hsecond hne).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hfiberMass :
      Q.fiberMass finalParent =
        ∑ middleParent ∈ selectedMiddle, P1.fiberMass middleParent := by
    dsimp only [Factoring.fiberMass]
    rw [hfiberIndices, Finset.sum_biUnion hdisjoint]
  rw [hfiberContainedMass, hfiberMass, Finset.sum_mul]
  calc
    ∑ middleParent ∈ selectedMiddle,
          P1.fiberContainedMass middleParent test *
            (coarse.body finalParent).volume
        ≤ ∑ middleParent ∈ selectedMiddle,
          (Cvol * C) * P1.fiberMass middleParent * volume test := by
      exact Finset.sum_le_sum hpiece
    _ = (Cvol * C) *
          (∑ middleParent ∈ selectedMiddle, P1.fiberMass middleParent) *
            volume test := by
      rw [Finset.mul_sum, Finset.sum_mul]

/--
Compose fiberwise Frostman bounds.

The middle bodies have common volume `Vmid`. Their first-level fiber
densities lie in `[d, Cdens * d]`; their intersections inside each coarse
fiber have overlap at most `Coverlap`; and each coarse body has volume at
most `Cvol * Vmid` times its middle-fiber cardinality.
-/
lemma compose_frostman
    {fine middle coarse : BodyFamily}
    {P1 : Factoring fine middle} {P2 : Factoring middle coarse}
    {C1 Cdens Cvol Coverlap Vmid d : ENNReal}
    (_hd_pos : 0 < d)
    (hFrost1 : P1.FibersAreCFrostman C1)
    (h_middle_conv : middle.IsConvex)
    (hVmid : ∀ j, (middle.body j).volume = Vmid)
    (hVmid_pos : 0 < Vmid) (hVmid_top : Vmid ≠ ⊤)
    (h_density_lower : ∀ j, d ≤ P1.fiberMass j / Vmid)
    (h_density_upper :
      ∀ j, P1.fiberMass j / Vmid ≤ Cdens * d)
    (hOverlap :
      ∀ (k : Fin coarse.card) (K : Set Point3),
        Convex ℝ K →
        K ⊆ (coarse.body k).carrier →
          ∑ j ∈ P2.fiberIndices k,
              volume (K ∩ (middle.body j).carrier) ≤
            Coverlap * volume K)
    (h_vol_ratio :
      ∀ k, (coarse.body k).volume ≤
        Cvol * Vmid * (P2.fiberIndices k).card) :
    (P1.compose P2).FibersAreCFrostman
      (Cdens * C1 * Cvol * Coverlap) := by
  intro k K hK_conv hK_sub
  have h_step1 :
      (P1.compose P2).fiberContainedMass k K ≤
        C1 * Cdens * d * Coverlap * volume K := by
    have h_piece :
        ∀ j ∈ P2.fiberIndices k,
          P1.fiberContainedMass j
              (K ∩ (middle.body j).carrier) ≤
            C1 * (Cdens * d) *
              volume (K ∩ (middle.body j).carrier) := by
      intro j _
      have hKj_conv :
          Convex ℝ (K ∩ (middle.body j).carrier) :=
        hK_conv.inter (h_middle_conv j)
      have hKj_sub :
          K ∩ (middle.body j).carrier ⊆
            (middle.body j).carrier := inter_subset_right
      have hbase :=
        hFrost1 j (K ∩ (middle.body j).carrier)
          hKj_conv hKj_sub
      rw [hVmid j] at hbase
      have hscaled :=
        mul_le_mul_right' hbase Vmid⁻¹
      have hcancel :
          P1.fiberContainedMass j
                (K ∩ (middle.body j).carrier) *
              Vmid * Vmid⁻¹ =
            P1.fiberContainedMass j
              (K ∩ (middle.body j).carrier) := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hVmid_pos.ne' hVmid_top,
          mul_one]
      have hrearrange :
          C1 * P1.fiberMass j *
                volume (K ∩ (middle.body j).carrier) *
              Vmid⁻¹ =
            C1 * (P1.fiberMass j / Vmid) *
              volume (K ∩ (middle.body j).carrier) := by
        simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
      rw [hcancel, hrearrange] at hscaled
      exact hscaled.trans <| by
        gcongr
        exact h_density_upper j
    have hrestrict :
        ∀ j ∈ P2.fiberIndices k,
          P1.fiberContainedMass j K =
            P1.fiberContainedMass j
              (K ∩ (middle.body j).carrier) := by
      intro j _
      have h_iff : ∀ i ∈ P1.fiberIndices j,
          ((fine.body i).carrier ⊆ K ∩ (middle.body j).carrier) ↔
          ((fine.body i).carrier ⊆ K) := by
        intro i hi
        have h_parent : P1.parent i = j :=
          (Finset.mem_filter.mp hi).2
        have h_sub :
            (fine.body i).carrier ⊆ (middle.body j).carrier := by
          rw [← h_parent]
          exact P1.contained i
        exact
          ⟨fun h => h.trans Set.inter_subset_left,
            fun h => Set.subset_inter h h_sub⟩
      have h_filter_eq :
          (P1.fiberIndices j).filter
              (fun i =>
                (fine.body i).carrier ⊆
                  K ∩ (middle.body j).carrier) =
            (P1.fiberIndices j).filter
              (fun i => (fine.body i).carrier ⊆ K) := by
        apply Finset.filter_congr
        intro i hi
        exact h_iff i hi
      simp only [fiberContainedMass, h_filter_eq]
    calc
      (P1.compose P2).fiberContainedMass k K
          =
        ∑ j ∈ P2.fiberIndices k,
          P1.fiberContainedMass j K :=
        compose_fiberContainedMass
      _ =
        ∑ j ∈ P2.fiberIndices k,
          P1.fiberContainedMass j
            (K ∩ (middle.body j).carrier) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact hrestrict j hj
      _ ≤
        ∑ j ∈ P2.fiberIndices k,
          C1 * (Cdens * d) *
            volume (K ∩ (middle.body j).carrier) := by
              gcongr with j hj
              exact h_piece j hj
      _ =
        C1 * Cdens * d *
          ∑ j ∈ P2.fiberIndices k,
            volume (K ∩ (middle.body j).carrier) := by
              rw [Finset.mul_sum]
              simp [mul_assoc, mul_comm, mul_left_comm]
      _ ≤ C1 * Cdens * d * (Coverlap * volume K) := by
              gcongr
              exact hOverlap k K hK_conv hK_sub
      _ = C1 * Cdens * d * Coverlap * volume K := by
              ring
  have h_step2 :
      d * Vmid * (P2.fiberIndices k).card ≤
        (P1.compose P2).fiberMass k := by
    calc
      d * Vmid * (P2.fiberIndices k).card
          =
        Vmid * ∑ j ∈ P2.fiberIndices k, d := by
            rw [Finset.mul_sum]
            simp [mul_assoc, mul_comm, mul_left_comm]
      _ ≤
        Vmid *
          ∑ j ∈ P2.fiberIndices k,
            P1.fiberMass j / Vmid := by
              gcongr with j _
              exact h_density_lower j
      _ =
        ∑ j ∈ P2.fiberIndices k,
          Vmid * (P1.fiberMass j / Vmid) := by
            rw [Finset.mul_sum]
      _ ≤
        ∑ j ∈ P2.fiberIndices k, P1.fiberMass j := by
          gcongr with j _
          exact ENNReal.mul_div_le
      _ = (P1.compose P2).fiberMass k :=
        compose_fiberMass.symm
  have h_step3 :
      d * (coarse.body k).volume ≤
        Cvol * (P1.compose P2).fiberMass k := by
    calc
      d * (coarse.body k).volume
          ≤
        d * (Cvol * Vmid * (P2.fiberIndices k).card) := by
          gcongr
          exact h_vol_ratio k
      _ = Cvol * (d * Vmid * (P2.fiberIndices k).card) := by
          ring
      _ ≤ Cvol * (P1.compose P2).fiberMass k := by
          gcongr
  calc
    (P1.compose P2).fiberContainedMass k K *
          (coarse.body k).volume
        ≤
      (C1 * Cdens * d * Coverlap * volume K) *
        (coarse.body k).volume := by
          gcongr
    _ =
      C1 * Cdens * Coverlap * volume K *
        (d * (coarse.body k).volume) := by
          ring
    _ ≤
      C1 * Cdens * Coverlap * volume K *
        (Cvol * (P1.compose P2).fiberMass k) := by
          gcongr
    _ =
      Cdens * C1 * Cvol * Coverlap *
        (P1.compose P2).fiberMass k * volume K := by
          ring

end Factoring

end Kakeya.Streamlined
