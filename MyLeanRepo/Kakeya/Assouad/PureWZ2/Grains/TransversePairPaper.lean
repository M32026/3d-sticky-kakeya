import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.BroadSetHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.CombinatorialPigeonhole
import MyLeanRepo.Kakeya.Assouad.WZ1.MeasurableFiniteChoice
import MyLeanRepo.Kakeya.Assouad.WZ1.InnerCrossTriple
import MyLeanRepo.Kakeya.Assouad.WZ1.SelectedCarrierMeasurable
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperCV
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement
import Mathlib.Tactic

/-!
# Transverse-pair parameter sub-lemma for WZ1PaperTubeShading

Adapts the narrow-pruning + weak-planiness pipeline to paper tube shadings
(6δ-thick full lines cropped to a box).

## Paper-shading compatibility

The standard WZ1 narrow-pruning infrastructure works on `TubeShading F`
(δ-thick unit segments). Paper shadings use 6δ-thick full lines cropped to
`[-2,2]^3`. We define paper-compatible versions of all key structures and
theorems. The mathematical content is identical since all proofs only use
shading carriers, point multiplicity, mass, and tube directions — all
available for paper shadings.
-/

noncomputable section

open MeasureTheory Set Finset Classical

namespace Kakeya.Assouad

/-!
## Paper-shading compatibility definitions
-/

/-!
## Paper-shading versions of narrow-pruning definitions
-/

/-- Large triple count for paper tube shadings. -/
def paperLargeTripleCount
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F)
    (p : Point3) (tau : ℝ) : ℕ := by
  classical
  exact
    ((Finset.univ.product (Finset.univ.product Finset.univ)).filter fun ijk =>
      p ∈ Y.carrier ijk.1 ∧
      p ∈ Y.carrier ijk.2.1 ∧
      p ∈ Y.carrier ijk.2.2 ∧
      tau ≤
        |wz1TripleProduct
          (F.tube ijk.1).direction
          (F.tube ijk.2.1).direction
          (F.tube ijk.2.2).direction|).card

/-- Counted broad set for paper tube shadings. -/
def paperCountedBroadSet
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F)
    (tau : ℝ) (Q : ℕ) : Set Point3 :=
  {p | p ∈ Y.union ∧ Q ≤ paperLargeTripleCount Y p tau}

/-- Narrow refinement data for paper tube shadings. -/
structure PaperWZ1NarrowRefinementData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F)
    (tau : ℝ) (Q : ℕ) where
  shading : WZ1PaperTubeShading F
  subshading : PaperIsSubshading shading Y
  carrier_eq :
    ∀ i, shading.carrier i =
      Y.carrier i \ paperCountedBroadSet Y tau Q
  mass_lower : (1 / 2 : ENNReal) * Y.mass ≤ shading.mass
  large_triple_count_lt :
    ∀ p ∈ shading.union,
      paperLargeTripleCount shading p tau < Q

/-- Weak plane map data for paper tube shadings. -/
structure PaperWZ1WeakPlaneMapData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F)
    (incidenceScale : ℝ) where
  planeMap : Point3 → Point3
  measurable : Measurable planeMap
  unit : ∀ p ∈ Y.union, ‖planeMap p‖ = 1
  incidence :
    ∀ i p, p ∈ Y.carrier i →
      |inner ℝ (F.tube i).direction (planeMap p)| ≤
        incidenceScale

/-- Good third direction count for paper tube shadings. -/
def paperGoodThirdCount
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F)
    (p : Point3) (i j : Fin F.card) (tau : ℝ) : ℕ := by
  classical
  exact
    (Finset.univ.filter fun k =>
      p ∈ Y.carrier k ∧
      |wz1TripleProduct
        (F.tube i).direction
        (F.tube j).direction
        (F.tube k).direction| < tau).card

/-- Narrow direction selection for paper tube shadings. -/
structure PaperWZ1NarrowDirectionSelection
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F)
    (kappa : ℝ) where
  first : Point3 → Fin F.card
  second : Point3 → Fin F.card
  first_measurable : Measurable first
  second_measurable : Measurable second
  first_mem : ∀ p ∈ Y.union, p ∈ Y.carrier (first p)
  second_mem : ∀ p ∈ Y.union, p ∈ Y.carrier (second p)
  transverse : ∀ p ∈ Y.union,
    kappa ≤ ‖wz1Cross (F.tube (first p)).direction (F.tube (second p)).direction‖

/-- Normalized cross-product normal for paper direction selection. -/
def PaperWZ1NarrowDirectionSelection.normal
    {delta kappa : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (selection : PaperWZ1NarrowDirectionSelection Y kappa)
    (p : Point3) : Point3 :=
  let cross :=
    wz1Cross
      (F.tube (selection.first p)).direction
      (F.tube (selection.second p)).direction
  (‖cross‖)⁻¹ • cross

/-!
## Parameter budget verification
-/

lemma transverse_pair_parameter_budget
    (delta kappa : ℝ) (m Q R : ℕ)
    (hkappa_pos : 0 < kappa)
    (hQ : 4 * Q ≤ m ^ 3)
    (hR : 12 * R ≤ m)
    (tau : ℝ) (htau : tau = 6 * delta * kappa) :
    (4 * Q ≤ m ^ 3) ∧
    (12 * R ≤ m) ∧
    (tau / kappa ≤ 6 * delta) := by
  constructor
  · exact hQ
  constructor
  · exact hR
  · rw [htau]
    have h : (6 * delta * kappa) / kappa = 6 * delta := by
      field_simp [hkappa_pos.ne']
    rw [h]

/-!
## Paper narrow pruning

Adaptation of `wz1_narrow_pruning` to paper shadings. The proof is identical
since paper carriers are subsets of the bounded box `[-2,2]^3`, ensuring
finite mass.
-/

theorem paper_narrow_pruning
    {delta tau : ℝ} {Q : ℕ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (hB : MeasurableSet (paperCountedBroadSet Y tau Q))
    (h_mass : 2 * (∫⁻ p in paperCountedBroadSet Y tau Q,
        (Y.pointMultiplicity p : ENNReal)) ≤ Y.mass) :
    Nonempty (PaperWZ1NarrowRefinementData Y tau Q) := by
  let B := paperCountedBroadSet Y tau Q
  let shading : WZ1PaperTubeShading F :=
    { carrier := fun i => Y.carrier i \ B
      measurable_carrier := fun i =>
        (Y.measurable_carrier i).diff hB
      subset_body := fun i =>
        Set.Subset.trans (fun p hp => hp.1) (Y.subset_body i) }
  have h_sub : PaperIsSubshading shading Y := by
    intro i
    exact fun p hp => hp.1
  have h_carrier_eq : ∀ i, shading.carrier i = Y.carrier i \ B := by
    intro i
    rfl
  let broadMass : ENNReal := ∫⁻ p in B, (Y.pointMultiplicity p : ENNReal)
  have h_fubini :
      (∑ i : Fin F.card, MeasureTheory.volume (Y.carrier i ∩ B)) = broadMass :=
    sum_volume_inter_eq_setLIntegral_pointMultiplicity Y hB
  have h_mass_decomp : Y.mass = shading.mass + broadMass := by
    have h1 : ∀ i : Fin F.card,
        MeasureTheory.volume (Y.carrier i) =
          MeasureTheory.volume (shading.carrier i) +
          MeasureTheory.volume (Y.carrier i ∩ B) := by
      intro i
      have h2 : MeasureTheory.volume (Y.carrier i ∩ B) +
              MeasureTheory.volume (Y.carrier i \ B) =
            MeasureTheory.volume (Y.carrier i) :=
          MeasureTheory.measure_inter_add_sdiff₀ (Y.carrier i) hB.nullMeasurableSet
      simpa [shading, add_comm] using h2.symm
    calc
      Y.mass
        = ∑ i : Fin F.card, MeasureTheory.volume (Y.carrier i) := rfl
      _ = ∑ i : Fin F.card, (MeasureTheory.volume (shading.carrier i) +
            MeasureTheory.volume (Y.carrier i ∩ B)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact h1 i
      _ = shading.mass + ∑ i : Fin F.card, MeasureTheory.volume (Y.carrier i ∩ B) := by
          rw [Finset.sum_add_distrib] <;> rfl
      _ = shading.mass + broadMass := by rw [h_fubini]
  have hY_finite : Y.mass ≠ ⊤ := by
    simp only [Kakeya.Streamlined.Shading.mass, ENNReal.sum_ne_top]
    intro i _
    have hle : MeasureTheory.volume (Y.carrier i) ≤
        MeasureTheory.volume (Kakeya.Streamlined.axisBox 2 2 2) :=
      MeasureTheory.measure_mono
        (Set.Subset.trans (Y.subset_body i) Set.inter_subset_right)
    have hbox : MeasureTheory.volume (Kakeya.Streamlined.axisBox 2 2 2) ≠ ⊤ := by
      have hclosed : IsClosed (Kakeya.Streamlined.axisBox 2 2 2) := by
        have h : ∀ (i : Fin 3), IsClosed {x : Point3 | |x i| ≤ 1} := by
          intro i
          have hcont : Continuous fun (x : Point3) => x i :=
            PiLp.continuous_apply 2 (fun x => ℝ) i
          exact isClosed_le (continuous_abs.comp hcont) continuous_const
        have h' : Kakeya.Streamlined.axisBox 2 2 2 =
            {x | |x 0| ≤ 1} ∩ ({x | |x 1| ≤ 1} ∩ {x | |x 2| ≤ 1}) := by
          ext x <;> simp [Kakeya.Streamlined.axisBox] <;> ring_nf <;> tauto
        rw [h']
        exact (h 0).inter ((h 1).inter (h 2))
      have hsub : Kakeya.Streamlined.axisBox 2 2 2 ⊆ Metric.closedBall (0 : Point3) (Real.sqrt 3) := by
        intro x hx
        have hbox : |x 0| ≤ 1 ∧ |x 1| ≤ 1 ∧ |x 2| ≤ 1 := by
          simpa [Kakeya.Streamlined.axisBox] using hx
        have h4 : ∀ i : Fin 3, (x i)^2 ≤ 1 := by
          intro i
          have h5 : |x i| ≤ 1 := by
            fin_cases i <;> simp [hbox] <;> linarith
          nlinarith [abs_le.mp h5]
        have h3 : ∑ i : Fin 3, (x i)^2 ≤ 3 := by
          calc
            ∑ i : Fin 3, (x i)^2 ≤ ∑ i : Fin 3, (1 : ℝ) := by
              apply Finset.sum_le_sum
              intro i _
              exact h4 i
            _ = 3 := by simp
        have hgoal : ‖x‖ ≤ Real.sqrt 3 := by
          rw [EuclideanSpace.norm_eq]
          have h3' : ∑ i : Fin 3, ‖x i‖ ^ 2 ≤ 3 := by
            have h_eq : ∑ i : Fin 3, ‖x i‖ ^ 2 = ∑ i : Fin 3, (x i)^2 := by
              apply Finset.sum_congr rfl
              intro i _
              simp [sq_abs]
            rw [h_eq]
            exact h3
          exact Real.sqrt_le_sqrt h3'
        simpa [Metric.mem_closedBall, dist_zero_right] using hgoal
      have hball_bounded : Bornology.IsBounded (Metric.closedBall (0 : Point3) (Real.sqrt 3)) :=
        Metric.isBounded_closedBall
      have hbounded : Bornology.IsBounded (Kakeya.Streamlined.axisBox 2 2 2) :=
        hball_bounded.subset hsub
      have hcompact : IsCompact (Kakeya.Streamlined.axisBox 2 2 2) :=
        Metric.isCompact_of_isClosed_isBounded hclosed hbounded
      exact hcompact.measure_lt_top.ne
    exact (hle.trans_lt hbox.lt_top).ne
  have h_broad_finite : broadMass ≠ ⊤ := by
    by_contra h
    have h' : 2 * broadMass = ⊤ := by
      rw [h] <;> simp
    rw [h'] at h_mass
    exact hY_finite (top_le_iff.mp h_mass)
  have h_broad_le_shading : broadMass ≤ shading.mass := by
    have h3 : 2 * broadMass ≤ shading.mass + broadMass := by
      rw [← h_mass_decomp]
      exact h_mass
    have h4 : broadMass + broadMass ≤ shading.mass + broadMass := by
      simpa [two_mul] using h3
    exact (WithTop.add_le_add_iff_right h_broad_finite).mp h4
  have h5 : Y.mass ≤ 2 * shading.mass := by
    calc
      Y.mass = shading.mass + broadMass := h_mass_decomp
      _ ≤ shading.mass + shading.mass := by gcongr
      _ = 2 * shading.mass := by simp [two_mul]
  have h_half : (1 / 2 : ENNReal) * Y.mass ≤ shading.mass := by
    have h6 : (1 / 2 : ENNReal) * Y.mass ≤ (1 / 2 : ENNReal) * (2 * shading.mass) :=
      mul_le_mul_right h5 (1 / 2 : ENNReal)
    have h7 : (1 / 2 : ENNReal) * (2 * shading.mass) = shading.mass := by
      simpa [div_eq_mul_inv] using
        ENNReal.inv_mul_cancel_left (show (2 : ENNReal) ≠ 0 by norm_num)
          (show (2 : ENNReal) ≠ ⊤ by norm_num)
    rw [h7] at h6
    exact h6
  have h_count_mono : ∀ p, paperLargeTripleCount shading p tau ≤
      paperLargeTripleCount Y p tau := by
    intro p
    classical
    apply Finset.card_le_card
    intro ijk h
    simp only [Finset.mem_filter] at h ⊢
    exact ⟨h.1, h_sub ijk.1 h.2.1, h_sub ijk.2.1 h.2.2.1,
      h_sub ijk.2.2 h.2.2.2.1, h.2.2.2.2⟩
  have h_union_sub : ∀ {p : Point3}, p ∈ shading.union → p ∈ Y.union := by
    intro p hp
    rcases hp with ⟨i, hi⟩
    exact ⟨i, h_sub i hi⟩
  have h_lt : ∀ p ∈ shading.union, paperLargeTripleCount shading p tau < Q := by
    intro p hp
    have h_in_Y : p ∈ Y.union := h_union_sub hp
    have h_not_B : p ∉ B := by
      rcases hp with ⟨i, hi⟩
      exact hi.2
    have h_count_lt_Q : paperLargeTripleCount Y p tau < Q := by
      by_contra h
      have h' : Q ≤ paperLargeTripleCount Y p tau := by linarith
      exact h_not_B ⟨h_in_Y, h'⟩
    exact (h_count_mono p).trans_lt h_count_lt_Q
  exact ⟨⟨shading, h_sub, h_carrier_eq, h_half, h_lt⟩⟩

/-!
## Paper mass lower from multiplicity

Adaptation of `mass_lower_from_pointMultiplicity` to paper shadings.
-/

lemma paper_mass_lower_from_pointMultiplicity
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Z Y : WZ1PaperTubeShading F}
    (h_mult : ∀ p ∈ Y.union, Y.pointMultiplicity p ≤ 4 * Z.pointMultiplicity p) :
    (1 / 4 : ENNReal) * Y.mass ≤ Z.mass := by
  have h1 : ∀ p : Point3,
      (Y.pointMultiplicity p : ENNReal) ≤ 4 * (Z.pointMultiplicity p : ENNReal) := by
    intro p
    by_cases hp : p ∈ Y.union
    · exact_mod_cast h_mult p hp
    · have hY0 : Y.pointMultiplicity p = 0 := by
        simpa [Kakeya.Streamlined.Shading.pointMultiplicity,
          Kakeya.Streamlined.Shading.union] using hp
      rw [hY0] <;> simp
  have h2 : (∫⁻ p, (Y.pointMultiplicity p : ENNReal)) ≤
      ∫⁻ p, 4 * (Z.pointMultiplicity p : ENNReal) :=
    MeasureTheory.lintegral_mono h1
  have hZmeas : Measurable fun p : Point3 => (Z.pointMultiplicity p : ENNReal) := by
    have h_eq : (fun p : Point3 => (Z.pointMultiplicity p : ENNReal)) =
        fun p => ∑ i : Fin F.card,
          (Z.carrier i).indicator (fun _ => (1 : ENNReal)) p := by
      funext p
      exact coe_pointMultiplicity_eq_sum_indicator Z p
    rw [h_eq]
    exact Finset.measurable_sum _ (fun i _ =>
      measurable_const.indicator (Z.measurable_carrier i))
  have h3 : (∫⁻ p, 4 * (Z.pointMultiplicity p : ENNReal)) =
      4 * (∫⁻ p, (Z.pointMultiplicity p : ENNReal)) := by
    rw [MeasureTheory.lintegral_const_mul] <;> exact hZmeas
  rw [lintegral_pointMultiplicity Y, h3,
    lintegral_pointMultiplicity Z] at h2
  have h7 : (1 / 4 : ENNReal) * Y.mass ≤
      (1 / 4 : ENNReal) * (4 * Z.mass) :=
    mul_le_mul_right h2 (1 / 4 : ENNReal)
  have h8 : (1 / 4 : ENNReal) * (4 * Z.mass) = Z.mass := by
    simpa [div_eq_mul_inv] using
      ENNReal.inv_mul_cancel_left
        (show (4 : ENNReal) ≠ 0 by norm_num)
        (show (4 : ENNReal) ≠ ⊤ by norm_num)
  rw [h8] at h7
  exact h7

/-!
## Paper good-pair measurability
-/

lemma paper_measurable_goodThirdCount
    {delta tau : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (i j : Fin F.card) :
    Measurable fun p : Point3 => paperGoodThirdCount Y p i j tau := by
  classical
  let Q : Point3 → Fin F.card → Prop := fun p k =>
    p ∈ Y.carrier k ∧
      |wz1TripleProduct (F.tube i).direction (F.tube j).direction
        (F.tube k).direction| < tau
  have hQ : ∀ k : Fin F.card, MeasurableSet {p : Point3 | Q p k} := by
    intro k
    by_cases hthresh : |wz1TripleProduct (F.tube i).direction
        (F.tube j).direction (F.tube k).direction| < tau
    · have h_set : {p : Point3 | Q p k} = Y.carrier k := by
        ext p <;> simp [Q, hthresh]
      rw [h_set] <;> exact Y.measurable_carrier k
    · have h_set : {p : Point3 | Q p k} = (∅ : Set Point3) := by
        ext p <;> simp [Q, hthresh]
      rw [h_set] <;> exact MeasurableSet.empty
  have h_sum : Measurable fun p : Point3 =>
      ∑ k : Fin F.card, if Q p k then (1 : ℕ) else 0 := by
    apply Finset.measurable_sum Finset.univ
    intro k _
    exact Measurable.ite (hQ k) measurable_const measurable_const
  have h_eq : (fun p : Point3 => paperGoodThirdCount Y p i j tau) =
      fun p : Point3 => ∑ k : Fin F.card, if Q p k then (1 : ℕ) else 0 := by
    funext p
    have h : paperGoodThirdCount Y p i j tau =
        (Finset.univ.filter (Q p)).card := by rfl
    rw [h, Finset.card_filter]
  exact h_eq ▸ h_sum

lemma paper_good_pair_predicate_measurable
    {delta kappa tau : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (ij : Fin F.card × Fin F.card) :
    MeasurableSet {p : Point3 |
      p ∈ Y.carrier ij.1 ∧
      p ∈ Y.carrier ij.2 ∧
      kappa ≤ ‖wz1Cross (F.tube ij.1).direction (F.tube ij.2).direction‖ ∧
      4 * paperGoodThirdCount Y p ij.1 ij.2 tau ≥ Y.pointMultiplicity p} := by
  let i := ij.1
  let j := ij.2
  let crossNorm : ℝ := ‖wz1Cross (F.tube i).direction (F.tube j).direction‖
  have h1 : MeasurableSet (Y.carrier i) := Y.measurable_carrier i
  have h2 : MeasurableSet (Y.carrier j) := Y.measurable_carrier j
  have h3 : MeasurableSet {p : Point3 | kappa ≤ crossNorm} := by
    by_cases h : kappa ≤ crossNorm
    · have h_set : {p : Point3 | kappa ≤ crossNorm} = Set.univ := by
        ext p <;> simp [h]
      rw [h_set] <;> exact MeasurableSet.univ
    · have h_set : {p : Point3 | kappa ≤ crossNorm} = (∅ : Set Point3) := by
        ext p <;> simp [h]
      rw [h_set] <;> exact MeasurableSet.empty
  have h4Count : Measurable fun p : Point3 =>
      paperGoodThirdCount Y p i j tau :=
    paper_measurable_goodThirdCount i j
  have h4Mult : Measurable fun p : Point3 => Y.pointMultiplicity p :=
    measurable_pointMultiplicity Y
  have h4 : MeasurableSet {p : Point3 |
      4 * paperGoodThirdCount Y p i j tau ≥ Y.pointMultiplicity p} := by
    let f : Point3 → ℕ × ℕ := fun p =>
      (paperGoodThirdCount Y p i j tau, Y.pointMultiplicity p)
    have hf : Measurable f := h4Count.prod h4Mult
    let S : Set (ℕ × ℕ) := {nm | 4 * nm.1 ≥ nm.2}
    have hS : MeasurableSet S := DiscreteMeasurableSpace.forall_measurableSet S
    have h_eq : {p : Point3 | 4 * paperGoodThirdCount Y p i j tau ≥ Y.pointMultiplicity p} =
        f ⁻¹' S := by
      ext p <;> simp [f, S]
    rw [h_eq] <;> exact hf hS
  exact h1.inter (h2.inter (h3.inter h4))

lemma PaperWZ1NarrowDirectionSelection.normal_measurable
    {delta kappa : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (selection : PaperWZ1NarrowDirectionSelection Y kappa) :
    Measurable selection.normal := by
  classical
  let pair : Point3 → Fin F.card × Fin F.card :=
    fun p => (selection.first p, selection.second p)
  have hpair : Measurable pair :=
    selection.first_measurable.prod selection.second_measurable
  let crossOfPair : Fin F.card × Fin F.card → Point3 :=
    fun ij => wz1Cross (F.tube ij.1).direction (F.tube ij.2).direction
  have hCrossOfPair : Measurable crossOfPair := measurable_of_finite crossOfPair
  have hcross : Measurable fun p : Point3 =>
      wz1Cross (F.tube (selection.first p)).direction
        (F.tube (selection.second p)).direction :=
    hCrossOfPair.comp hpair
  have hnorm : Measurable fun p : Point3 =>
      ‖wz1Cross (F.tube (selection.first p)).direction
        (F.tube (selection.second p)).direction‖ := hcross.norm
  have hinv : Measurable fun p : Point3 =>
      (‖wz1Cross (F.tube (selection.first p)).direction
        (F.tube (selection.second p)).direction‖)⁻¹ := hnorm.inv
  unfold PaperWZ1NarrowDirectionSelection.normal
  exact hinv.smul hcross

/-!
## Paper weak planiness from narrow

Adaptation of `wz1_weak_planiness_from_narrow` to paper shadings.
-/

theorem paper_weak_planiness_from_narrow
    {delta kappa tau : ℝ} {Q R : ℕ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (hkappa : 0 < kappa)
    (hF : F.Nonempty)
    (narrow : PaperWZ1NarrowRefinementData Y tau Q)
    (hclose : ∀ p ∈ narrow.shading.union, ∀ i,
      p ∈ narrow.shading.carrier i →
        paperCloseDirectionCount narrow.shading p i kappa < R)
    (hmult : ∀ p ∈ narrow.shading.union,
      let mu := narrow.shading.pointMultiplicity p
      4 * (Q + 3 * R * mu ^ 2) ≤ 3 * mu ^ 3) :
    ∃ (selection : PaperWZ1NarrowDirectionSelection narrow.shading kappa)
      (selected : WZ1PaperTubeShading F)
      (planeMap : PaperWZ1WeakPlaneMapData selected (tau / kappa)),
      PaperIsSubshading selected narrow.shading ∧
      (1 / 4 : ENNReal) * narrow.shading.mass ≤ selected.mass := by
  classical
  let Z := narrow.shading
  have hGoodPair : ∀ p : Point3, p ∈ Z.union →
      ∃ i j : Fin F.card,
        p ∈ Z.carrier i ∧
        p ∈ Z.carrier j ∧
        kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ ∧
        Z.pointMultiplicity p ≤ 4 * paperGoodThirdCount Z p i j tau := by
    intro p hp
    let A : Finset (Fin F.card) :=
      Finset.univ.filter fun i => p ∈ Z.carrier i
    have hAcard : A.card = Z.pointMultiplicity p := by
      simp [A, Kakeya.Streamlined.Shading.pointMultiplicity] <;> rfl
    let Broad : Fin F.card → Fin F.card → Fin F.card → Prop :=
      fun i j k => tau ≤ |wz1TripleProduct
        (F.tube i).direction (F.tube j).direction (F.tube k).direction|
    let Close : Fin F.card → Fin F.card → Prop :=
      fun i j => ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < kappa
    have hBroad :
        ((A.product (A.product A)).filter
          (fun x : Fin F.card × (Fin F.card × Fin F.card) =>
            Broad x.1 x.2.1 x.2.2)).card < Q := by
      let S := (A.product (A.product A)).filter
          (fun x : Fin F.card × (Fin F.card × Fin F.card) =>
            Broad x.1 x.2.1 x.2.2)
      have h1 : S.card = paperLargeTripleCount Z p tau := by
        have h_eq : S = (Finset.univ.product (Finset.univ.product Finset.univ)).filter
            (fun x : Fin F.card × (Fin F.card × Fin F.card) =>
              p ∈ Z.carrier x.1 ∧ p ∈ Z.carrier x.2.1 ∧
              p ∈ Z.carrier x.2.2 ∧ Broad x.1 x.2.1 x.2.2) := by
          apply Finset.ext
          intro x
          have hAmem : ∀ i : Fin F.card, i ∈ A ↔ p ∈ Z.carrier i := by
            intro i <;> simp [A, Finset.mem_filter]
          simp [S, A, Broad, Finset.mem_filter, Finset.mem_product,
            Finset.mem_univ, hAmem] <;> tauto
        rw [h_eq]
        <;> rfl
      rw [h1]
      exact narrow.large_triple_count_lt p hp
    have hClose : ∀ i ∈ A, (A.filter fun j => Close i j).card < R := by
      intro i hi
      have hi' : p ∈ Z.carrier i := by
        simpa [A, Finset.mem_filter] using hi
      have hEq : (A.filter fun j => Close i j).card =
          paperCloseDirectionCount Z p i kappa := by
        simp [Close, A, paperCloseDirectionCount, Finset.filter_filter] <;> congr
      rw [hEq]
      exact hclose p hp i hi'
    have hMain : 4 * (Q + 3 * R * A.card ^ 2) ≤ 3 * A.card ^ 3 := by
      rw [hAcard]
      exact hmult p hp
    rcases combinatorial_pigeonhole A Broad Close Q R hBroad hClose hMain
      with ⟨i, hi, j, hj, hNotClose, hCount⟩
    have hi' : p ∈ Z.carrier i := by simpa [A, Finset.mem_filter] using hi
    have hj' : p ∈ Z.carrier j := by simpa [A, Finset.mem_filter] using hj
    have hTransverse : kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ :=
      Std.not_lt.mp hNotClose
    let good := A.filter fun k =>
      ¬Broad i j k ∧ ¬Close i j ∧ ¬Close i k ∧ ¬Close j k
    have hSubset : good ⊆ A.filter fun k =>
        |wz1TripleProduct (F.tube i).direction (F.tube j).direction
          (F.tube k).direction| < tau := by
      intro k hk
      have hFilter : ¬Broad i j k ∧ ¬Close i j ∧ ¬Close i k ∧ ¬Close j k :=
        (Finset.mem_filter.mp hk).2
      have hkA : k ∈ A := (Finset.mem_filter.mp hk).1
      have hNarrow : ¬Broad i j k := hFilter.1
      simp only [Broad, not_le] at hNarrow
      exact Finset.mem_filter.mpr ⟨hkA, hNarrow⟩
    have hCount2 : good.card ≤ (A.filter fun k =>
        |wz1TripleProduct (F.tube i).direction (F.tube j).direction
          (F.tube k).direction| < tau).card :=
      Finset.card_le_card hSubset
    have hGoodThird : (A.filter fun k =>
        |wz1TripleProduct (F.tube i).direction (F.tube j).direction
          (F.tube k).direction| < tau).card =
        paperGoodThirdCount Z p i j tau := by
      simp [paperGoodThirdCount, A, Finset.filter_filter] <;> congr
    have hFinal : Z.pointMultiplicity p ≤ 4 * paperGoodThirdCount Z p i j tau := by
      rw [hAcard] at *
      rw [← hGoodThird]
      exact hCount.trans (mul_le_mul_of_nonneg_left hCount2 (by norm_num))
    exact ⟨i, j, hi', hj', hTransverse, hFinal⟩
  let N : ℕ := Fintype.card (Fin F.card × Fin F.card)
  have hN : 0 < N := by
    have h1 : N = F.card * F.card := by simp [N, Fintype.card_prod]
    rw [h1] <;> exact mul_pos hF hF
  let defaultIndex : Fin N := ⟨0, hN⟩
  let equivPair : Fin F.card × Fin F.card ≃ Fin N :=
    Fintype.equivFin (Fin F.card × Fin F.card)
  let Qualifies (p : Point3) (ij : Fin F.card × Fin F.card) : Prop :=
    p ∈ Z.carrier ij.1 ∧ p ∈ Z.carrier ij.2 ∧
    kappa ≤ ‖wz1Cross (F.tube ij.1).direction (F.tube ij.2).direction‖ ∧
    Z.pointMultiplicity p ≤ 4 * paperGoodThirdCount Z p ij.1 ij.2 tau
  let P : Point3 → Fin N → Prop := fun p n =>
    (p ∈ Z.union ∧ Qualifies p (equivPair.symm n)) ∨
      (p ∉ Z.union ∧ n = defaultIndex)
  have hPmeas : ∀ n : Fin N, MeasurableSet {p : Point3 | P p n} := by
    intro n
    have h1 : MeasurableSet {p : Point3 | p ∈ Z.union ∧ Qualifies p (equivPair.symm n)} :=
      (measurableSet_shading_union Z).inter
        (paper_good_pair_predicate_measurable (equivPair.symm n))
    by_cases hn : n = defaultIndex
    · subst hn
      have hSet : {p : Point3 | P p defaultIndex} =
          {p : Point3 | p ∈ Z.union ∧ Qualifies p (equivPair.symm defaultIndex)} ∪ Z.unionᶜ := by
        ext p <;> simp [P, Qualifies] <;> tauto
      rw [hSet]
      exact h1.union (measurableSet_shading_union Z).compl
    · have hSet : {p : Point3 | P p n} =
          {p : Point3 | p ∈ Z.union ∧ Qualifies p (equivPair.symm n)} := by
        ext p <;> simp [P, hn]
      rw [hSet] <;> exact h1
  have hPnonempty : ∀ p : Point3, ∃ n : Fin N, P p n := by
    intro p
    by_cases hp : p ∈ Z.union
    · rcases hGoodPair p hp with ⟨i, j, hi, hj, hTransverse, hCount⟩
      let ij : Fin F.card × Fin F.card := (i, j)
      have hQualifies : Qualifies p ij := ⟨hi, hj, hTransverse, hCount⟩
      let n : Fin N := equivPair ij
      refine ⟨n, ?_⟩
      have hEq : equivPair.symm n = ij := equivPair.left_inv ij
      simp [P, hp, hEq, hQualifies]
    · exact ⟨defaultIndex, by simp [P, hp]⟩
  rcases measurableFiniteChoice hPmeas hPnonempty with
    ⟨choice, hChoiceMeasurable, hChoice, _hChoiceMinimal⟩
  let chosen : Point3 → Fin F.card × Fin F.card :=
    fun p => equivPair.symm (choice p)
  have hChosenMeasurable : Measurable chosen := by
    have hEquivMeasurable : Measurable (equivPair.symm : Fin N → Fin F.card × Fin F.card) :=
      Measurable.of_discrete
    exact hEquivMeasurable.comp hChoiceMeasurable
  let first : Point3 → Fin F.card := fun p => (chosen p).1
  let second : Point3 → Fin F.card := fun p => (chosen p).2
  have hFirstMeasurable : Measurable first := hChosenMeasurable.fst
  have hSecondMeasurable : Measurable second := hChosenMeasurable.snd
  have hFirstMem : ∀ p ∈ Z.union, p ∈ Z.carrier (first p) := by
    intro p hp
    have h := hChoice p
    rcases h with h | h
    · exact h.2.1
    · exact False.elim (h.1 hp)
  have hSecondMem : ∀ p ∈ Z.union, p ∈ Z.carrier (second p) := by
    intro p hp
    have h := hChoice p
    rcases h with h | h
    · exact h.2.2.1
    · exact False.elim (h.1 hp)
  have hTransverse : ∀ p ∈ Z.union,
      kappa ≤ ‖wz1Cross (F.tube (first p)).direction (F.tube (second p)).direction‖ := by
    intro p hp
    have h := hChoice p
    rcases h with h | h
    · exact h.2.2.2.1
    · exact False.elim (h.1 hp)
  have hGoodCount : ∀ p ∈ Z.union,
      Z.pointMultiplicity p ≤ 4 * paperGoodThirdCount Z p (first p) (second p) tau := by
    intro p hp
    have h := hChoice p
    rcases h with h | h
    · exact h.2.2.2.2
    · exact False.elim (h.1 hp)
  let selection : PaperWZ1NarrowDirectionSelection Z kappa :=
    { first := first
      second := second
      first_measurable := hFirstMeasurable
      second_measurable := hSecondMeasurable
      first_mem := hFirstMem
      second_mem := hSecondMem
      transverse := hTransverse }
  let selected : WZ1PaperTubeShading F :=
    { carrier := fun k =>
        {p | p ∈ Z.carrier k ∧
          |wz1TripleProduct (F.tube (first p)).direction
            (F.tube (second p)).direction (F.tube k).direction| < tau}
      measurable_carrier := fun k =>
        (Z.measurable_carrier k).inter
          (measurable_selected_carrier hFirstMeasurable hSecondMeasurable k)
      subset_body := fun k p hp => Z.subset_body k hp.1 }
  have hSelectedSub : PaperIsSubshading selected Z := by
    intro k p hp
    exact hp.1
  have hMultiplicity : ∀ p ∈ Z.union,
      Z.pointMultiplicity p ≤ 4 * selected.pointMultiplicity p := by
    intro p hp
    have h1 : Z.pointMultiplicity p ≤
        4 * paperGoodThirdCount Z p (first p) (second p) tau := hGoodCount p hp
    have h2 : paperGoodThirdCount Z p (first p) (second p) tau ≤
        selected.pointMultiplicity p := by
      simp [selected, Kakeya.Streamlined.Shading.pointMultiplicity,
        paperGoodThirdCount]
      <;> exact Finset.card_le_card (fun k hk =>
        (Finset.mem_filter.mp hk).2)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))
  have hMass : (1 / 4 : ENNReal) * Z.mass ≤ selected.mass :=
    paper_mass_lower_from_pointMultiplicity hMultiplicity
  let planeMap : PaperWZ1WeakPlaneMapData selected (tau / kappa) :=
    { planeMap := selection.normal
      measurable := selection.normal_measurable
      unit := by
        intro p hp
        rcases hp with ⟨k, hk⟩
        have hpSelected : p ∈ selected.union := ⟨k, hk⟩
        have hpZ : p ∈ Z.union := by
          rcases hpSelected with ⟨k, hk⟩
          exact ⟨k, hSelectedSub k hk⟩
        let cross := wz1Cross (F.tube (first p)).direction (F.tube (second p)).direction
        have hCrossPos : 0 < ‖cross‖ := hkappa.trans_le (hTransverse p hpZ)
        have hCrossNe : ‖cross‖ ≠ 0 := hCrossPos.ne'
        have h1 : selection.normal p = (‖cross‖)⁻¹ • cross := by rfl
        rw [h1, norm_smul]
        have hAbs : ‖(‖cross‖)⁻¹‖ = (‖cross‖)⁻¹ := by
          simp [Real.norm_eq_abs, abs_of_pos]
        rw [hAbs]
        field_simp [hCrossNe]
      incidence := by
        intro i p hp
        have hpSelected : p ∈ selected.union := ⟨i, hp⟩
        have hpZ : p ∈ Z.union := by
          rcases hpSelected with ⟨i, hi⟩
          exact ⟨i, hSelectedSub i hi⟩
        let u := (F.tube (first p)).direction
        let v := (F.tube (second p)).direction
        let w := (F.tube i).direction
        let cross := wz1Cross u v
        have hCross : kappa ≤ ‖cross‖ := hTransverse p hpZ
        have hCrossPos : 0 < ‖cross‖ := hkappa.trans_le hCross
        have hTriple : |wz1TripleProduct u v w| ≤ tau := le_of_lt hp.2
        have hInner : inner ℝ w cross = wz1TripleProduct u v w := inner_cross_triple u v w
        have hEq : inner ℝ w (selection.normal p) =
            (‖cross‖)⁻¹ * wz1TripleProduct u v w := by
          have hDef : selection.normal p = (‖cross‖)⁻¹ • cross := by rfl
          rw [hDef, inner_smul_right, hInner]
        rw [hEq]
        have hAbs : |(‖cross‖)⁻¹ * wz1TripleProduct u v w| =
            |wz1TripleProduct u v w| / ‖cross‖ := by
          rw [abs_mul, abs_inv, abs_of_pos hCrossPos]
          <;> field_simp [hCrossPos.ne']
        rw [hAbs]
        exact (div_le_div_of_nonneg_left (abs_nonneg _) hkappa hCross).trans
          (div_le_div_of_nonneg_right hTriple hkappa.le) }
  exact ⟨selection, selected, planeMap, hSelectedSub, hMass⟩

/-!
## Main transverse-pair theorem (paper shading version)
-/

theorem transverse_pair_plane_map_paper
    {delta kappa tau : ℝ} {Q R m : ℕ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (hkappa_pos : 0 < kappa)
    (hF : F.Nonempty)
    (hincidence : tau / kappa ≤ 6 * delta)
    (hmult_lower : ∀ p ∈ Y.union, m ≤ Y.pointMultiplicity p)
    (hQ : 4 * Q ≤ m ^ 3)
    (hR : 12 * R ≤ m)
    (hbroad_meas : MeasurableSet (paperCountedBroadSet Y tau Q))
    (hbroad_small :
      2 * (∫⁻ p in paperCountedBroadSet Y tau Q,
        (Y.pointMultiplicity p : ENNReal)) ≤ Y.mass)
    (hclose : ∀ p ∈ Y.union, ∀ i,
      p ∈ Y.carrier i →
        paperCloseDirectionCount Y p i kappa < R) :
    ∃ (narrow : PaperWZ1NarrowRefinementData Y tau Q)
      (selected : WZ1PaperTubeShading F)
      (planeMap : PaperWZ1WeakPlaneMapData selected (6 * delta)),
      PaperIsSubshading selected narrow.shading ∧
      (1 / 4 : ENNReal) * narrow.shading.mass ≤ selected.mass := by
  -- Step 1: Paper narrow pruning
  have h_narrow : Nonempty (PaperWZ1NarrowRefinementData Y tau Q) :=
    paper_narrow_pruning hbroad_meas hbroad_small
  rcases h_narrow with ⟨narrow⟩
  -- Step 2: Multiplicity preservation
  have h_mult_eq : ∀ p ∈ narrow.shading.union,
      narrow.shading.pointMultiplicity p = Y.pointMultiplicity p := by
    intro p hp
    have h_not_broad : p ∉ paperCountedBroadSet Y tau Q := by
      rcases hp with ⟨i, hi⟩
      have h : p ∈ Y.carrier i \ paperCountedBroadSet Y tau Q := by
        rw [narrow.carrier_eq i] at hi <;> exact hi
      exact h.2
    have h1 : ∀ j : Fin F.card, p ∈ narrow.shading.carrier j ↔ p ∈ Y.carrier j := by
      intro j
      rw [narrow.carrier_eq j]
      simp [h_not_broad]
    have h_le1 : narrow.shading.pointMultiplicity p ≤ Y.pointMultiplicity p := by
      classical
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact (h1 j).mp hj
    have h_le2 : Y.pointMultiplicity p ≤ narrow.shading.pointMultiplicity p := by
      classical
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact (h1 j).mpr hj
    exact le_antisymm h_le1 h_le2
  have hmult : ∀ p ∈ narrow.shading.union,
      let mu := narrow.shading.pointMultiplicity p
      4 * (Q + 3 * R * mu ^ 2) ≤ 3 * mu ^ 3 := by
    intro p hp
    let mu := narrow.shading.pointMultiplicity p
    have h_mu_eq : mu = Y.pointMultiplicity p := h_mult_eq p hp
    have h_mu_lower : m ≤ mu := by
      rw [h_mu_eq]
      exact hmult_lower p (by
        rcases hp with ⟨i, hi⟩
        exact ⟨i, narrow.subshading i hi⟩)
    exact wz1_good_triple_budget m Q R mu h_mu_lower hQ hR
  -- Step 3: Close-direction count on narrow shading
  have hclose_narrow : ∀ p ∈ narrow.shading.union, ∀ i,
      p ∈ narrow.shading.carrier i →
        paperCloseDirectionCount narrow.shading p i kappa < R := by
    intro p hp i hpi
    have h1 : p ∈ Y.carrier i := narrow.subshading i hpi
    have h2 : p ∈ Y.union := ⟨i, h1⟩
    have h3 : paperCloseDirectionCount narrow.shading p i kappa ≤
        paperCloseDirectionCount Y p i kappa := by
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter] at hj ⊢
      exact ⟨hj.1, narrow.subshading j hj.2.1, hj.2.2⟩
    exact h3.trans_lt (hclose p h2 i h1)
  -- Step 4: Apply paper weak planiness from narrow
  have h_main := paper_weak_planiness_from_narrow
    hkappa_pos hF narrow hclose_narrow hmult
  rcases h_main with ⟨selection, selected, planeMap, hsub, hmass⟩
  -- Step 5: Weaken incidence to 6 * delta
  let planeMap' : PaperWZ1WeakPlaneMapData selected (6 * delta) :=
    { planeMap := planeMap.planeMap
      measurable := planeMap.measurable
      unit := planeMap.unit
      incidence := by
        intro i p hp
        have h := planeMap.incidence i p hp
        have h' : tau / kappa ≤ 6 * delta := hincidence
        exact h.trans h' }
  exact ⟨narrow, selected, planeMap', hsub, hmass⟩

/-!
## Cubicality preservation under narrow pruning

The narrow-pruning broad set is a union of grid cubes when the base shading
is cubical, because the large-triple count depends only on which carriers
contain a point (constant within a cube) and on tube directions (independent
of position). Therefore removing the broad set preserves cubicality.
-/

/-- Difference of a cubical set by a cubical set is cubical.

If `B` is a union of grid cubes and `p ∉ B`, then the entire cube of `p`
is disjoint from `B`. -/
lemma cubical_set_diff
    {delta : ℝ} {S B : Set Point3}
    (hS_cubical : ∀ p ∈ S, wz1PaperGridCube delta (wz1PaperGridIndex delta p) ⊆ S)
    (hB_cubical : ∀ p ∈ B, wz1PaperGridCube delta (wz1PaperGridIndex delta p) ⊆ B) :
    ∀ p ∈ S \ B, wz1PaperGridCube delta (wz1PaperGridIndex delta p) ⊆ S \ B := by
  intro p hp
  have h1 : wz1PaperGridCube delta (wz1PaperGridIndex delta p) ⊆ S :=
    hS_cubical p hp.1
  have h2 : Disjoint (wz1PaperGridCube delta (wz1PaperGridIndex delta p)) B := by
    rw [Set.disjoint_left]
    intro q hq hqB
    have h3 : wz1PaperGridCube delta (wz1PaperGridIndex delta q) ⊆ B :=
      hB_cubical q hqB
    have h4 : wz1PaperGridIndex delta q = wz1PaperGridIndex delta p :=
      (mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta p) q).mp hq
    have h5 : p ∈ wz1PaperGridCube delta (wz1PaperGridIndex delta p) := by
      simp [mem_wz1PaperGridCube]
    rw [h4] at h3
    exact hp.2 (h3 h5)
  have hgoal : wz1PaperGridCube delta (wz1PaperGridIndex delta p) ⊆ S \ B := by
    intro x hx
    exact ⟨h1 hx, Set.disjoint_left.mp h2 hx⟩
  exact hgoal

/-- The counted broad set is cubical when the base shading is cubical.

Within a single grid cube, the set of carriers containing a point is constant
(by cubicality), and the large-triple count depends only on carriers and
directions. Hence the broad set is a union of entire grid cubes. -/
lemma broad_set_cubical
    {delta tau : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hS_cubical : WZ1PaperIsCubicalShading S)
    (Q : ℕ) :
    ∀ p ∈ paperCountedBroadSet S tau Q,
      wz1PaperGridCube delta (wz1PaperGridIndex delta p) ⊆
        paperCountedBroadSet S tau Q := by
  intro p hp
  intro q hq
  have hcell : wz1PaperGridIndex delta q = wz1PaperGridIndex delta p :=
    (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta p) q).mp hq
  have hsame : ∀ (i : Fin F.card), p ∈ S.carrier i ↔ q ∈ S.carrier i := by
    intro i
    constructor
    · intro hpi
      have hcube : wz1PaperGridCube delta (wz1PaperGridIndex delta p) ⊆ S.carrier i :=
        hS_cubical i p hpi
      exact hcube hq
    · intro hqi
      have hcube : wz1PaperGridCube delta (wz1PaperGridIndex delta q) ⊆ S.carrier i :=
        hS_cubical i q hqi
      have hp_in : p ∈ wz1PaperGridCube delta (wz1PaperGridIndex delta q) := by
        rw [hcell]
        <;> simp [mem_wz1PaperGridCube]
      exact hcube hp_in
  have h_union : p ∈ S.union ↔ q ∈ S.union := by
    constructor
    · rintro ⟨i, hi⟩; exact ⟨i, (hsame i).mp hi⟩
    · rintro ⟨i, hi⟩; exact ⟨i, (hsame i).mpr hi⟩
  have h_count : paperLargeTripleCount S p tau = paperLargeTripleCount S q tau := by
    dsimp only [paperLargeTripleCount]
    classical
    apply congr_arg Finset.card
    apply Finset.ext
    intro ijk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h2 : (p ∈ S.carrier ijk.1 ∧ p ∈ S.carrier ijk.2.1 ∧ p ∈ S.carrier ijk.2.2) ↔
        (q ∈ S.carrier ijk.1 ∧ q ∈ S.carrier ijk.2.1 ∧ q ∈ S.carrier ijk.2.2) := by
      simp [hsame]
    tauto
  have hQ : Q ≤ paperLargeTripleCount S p tau := hp.2
  have hQ' : Q ≤ paperLargeTripleCount S q tau := by
    rw [←h_count]; exact hQ
  exact ⟨h_union.mp hp.1, hQ'⟩

/-- Narrow pruning preserves cubicality of the shading. -/
lemma narrow_pruning_preserves_cubical
    {delta tau : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (Q : ℕ)
    (hS_cubical : WZ1PaperIsCubicalShading S)
    (narrow : PaperWZ1NarrowRefinementData S tau Q) :
    WZ1PaperIsCubicalShading narrow.shading := by
  intro i p hp
  have hcarrier_cubical : ∀ p ∈ S.carrier i,
      wz1PaperGridCube delta (wz1PaperGridIndex delta p) ⊆ S.carrier i :=
    hS_cubical i
  have hbroad_cubical : ∀ p ∈ paperCountedBroadSet S tau Q,
      wz1PaperGridCube delta (wz1PaperGridIndex delta p) ⊆ paperCountedBroadSet S tau Q :=
    broad_set_cubical hS_cubical Q
  have h_eq : narrow.shading.carrier i = S.carrier i \ paperCountedBroadSet S tau Q :=
    narrow.carrier_eq i
  rw [h_eq] at hp
  rw [h_eq]
  exact cubical_set_diff hcarrier_cubical hbroad_cubical p hp

end Kakeya.Assouad

end
