import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.Estimates
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Translation infrastructure for tube families

Translation by a fixed vector preserves all metric and measure-theoretic
properties of tubes, shadings, and families.  We also prove that a tube
centered at the origin with small radius has its full carrier in the unit ball.
-/

noncomputable section

open Kakeya Metric Set MeasureTheory

namespace TranslationInfrastructure

/-- Translation commutes with thickening. -/
lemma translate_cthickening {δ : ℝ} (v : Point3) (S : Set Point3) :
    cthickening δ (image (fun x : Point3 => x + v) S) =
    image (fun x : Point3 => x + v) (cthickening δ S) := by
  let e : Point3 ≃ᵢ Point3 := IsometryEquiv.vaddConst v
  let f : Point3 → Point3 := fun x => x + v
  let g : Point3 → Point3 := fun x => x - v
  have hf : Isometry f := e.isometry
  ext z
  have h1 : infEDist z (f '' S) = infEDist (g z) S := by
    have h2 : infEDist (f (g z)) (f '' S) = infEDist (g z) S :=
      Metric.infEDist_image hf (x := g z) (t := S)
    have h3 : f (g z) = z := by
      simp [f, g]
    rw [h3] at h2
    exact h2
  simp only [Metric.cthickening_eq_preimage_infEDist, mem_preimage, mem_image, Set.mem_Iic]
  constructor
  · intro h
    have h4 : infEDist (g z) S ≤ ENNReal.ofReal δ := by
      rw [←h1]; exact h
    exact ⟨g z, h4, by simp [f, g]⟩
  · rintro ⟨w, hw, rfl⟩
    have h4 : infEDist (f w) (f '' S) ≤ ENNReal.ofReal δ := by
      rw [Metric.infEDist_image hf (x := w) (t := S)]
      exact hw
    exact h4

/-- Translate a tube by a fixed vector. -/
def translateTube {δ : ℝ} (v : Point3) (T : DeltaTube δ) : DeltaTube δ :=
  { base := T.base + v
    direction := T.direction
    direction_unit := T.direction_unit }

/-- The unit segment of a translated tube is the translated segment. -/
lemma translateTube_unitSegment {δ : ℝ} (v : Point3) (T : DeltaTube δ) :
    unitSegment (translateTube v T).base (translateTube v T).direction =
    image (fun x : Point3 => x + v) (unitSegment T.base T.direction) := by
  ext x
  simp only [translateTube, unitSegment, mem_image]
  constructor
  · rintro ⟨t, ht, hx⟩
    refine ⟨T.base + t • T.direction, ⟨t, ht, rfl⟩, ?_⟩
    have h : (T.base + v) + t • T.direction = T.base + t • T.direction + v := by abel
    rw [h] at hx
    exact hx
  · rintro ⟨y, hy, hxy⟩
    rcases hy with ⟨t, ht, hyt⟩
    have h_goal : (T.base + v) + t • T.direction = x := by
      calc
        (T.base + v) + t • T.direction = T.base + t • T.direction + v := by abel
        _ = y + v := by exact congr_arg (fun z => z + v) hyt
        _ = x := hxy
    exact ⟨t, ht, h_goal⟩

/-- The carrier of a translated tube is the translated carrier. -/
lemma translateTube_carrier {δ : ℝ} (v : Point3) (T : DeltaTube δ) :
    (translateTube v T).carrier = image (fun x : Point3 => x + v) T.carrier := by
  let f : Point3 → Point3 := fun x => x + v
  calc
    (translateTube v T).carrier
      = cthickening δ (unitSegment (translateTube v T).base (translateTube v T).direction) := by rfl
    _ = cthickening δ (f '' (unitSegment T.base T.direction)) := by rw [translateTube_unitSegment]
    _ = f '' (cthickening δ (unitSegment T.base T.direction)) := by rw [translate_cthickening]
    _ = f '' T.carrier := by rfl

/-- Volume is preserved under translation for measurable sets. -/
lemma volume_translate {v : Point3} {S : Set Point3} (hS : MeasurableSet S) :
    volume (image (fun x : Point3 => x + v) S) = volume S := by
  have h_eq : (fun x : Point3 => x + v) '' S = (fun x : Point3 => x + (-v)) ⁻¹' S := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨y + (-v), hy, by simp⟩
  rw [h_eq]
  exact MeasureTheory.measure_preimage_add_right volume (-v) S

/-- Translation preserves essential distinctness. -/
lemma translateTube_preserves_essentiallyDistinct {δ : ℝ} (v : Point3)
    {T U : DeltaTube δ} (h : T.EssentiallyDistinct U) :
    (translateTube v T).EssentiallyDistinct (translateTube v U) := by
  let T' := translateTube v T
  let U' := translateTube v U
  let f : Point3 → Point3 := fun x => x + v
  have hinj : Function.Injective f := by
    intro a b h; simpa [f] using h
  have hcarT : T'.carrier = f '' T.carrier := translateTube_carrier v T
  have hcarU : U'.carrier = f '' U.carrier := translateTube_carrier v U
  have h1 : f '' T.carrier ∩ f '' U.carrier = f '' (T.carrier ∩ U.carrier) := by
    exact (Set.image_inter hinj).symm
  have hS : MeasurableSet (T.carrier ∩ U.carrier) :=
    Metric.isClosed_cthickening.measurableSet.inter
      Metric.isClosed_cthickening.measurableSet
  have hvol1 : volume (T'.carrier ∩ U'.carrier) = volume (T.carrier ∩ U.carrier) := by
    rw [hcarT, hcarU, h1, volume_translate hS]
  have hvolT : T'.volume = T.volume := by
    rw [DeltaTube.volume, hcarT]
    exact volume_translate Metric.isClosed_cthickening.measurableSet
  have hvolU : U'.volume = U.volume := by
    rw [DeltaTube.volume, hcarU]
    exact volume_translate Metric.isClosed_cthickening.measurableSet
  have hgoal : volume (T'.carrier ∩ U'.carrier) ≤ (2 : ENNReal)⁻¹ * max T'.volume U'.volume := by
    rw [hvol1, hvolT, hvolU]
    exact h
  exact hgoal

/-- Translate an entire tube family by a fixed vector. -/
def translateFamily {δ : ℝ} (v : Point3) (F : Streamlined.TubeFamily δ) :
    Streamlined.TubeFamily δ :=
  { card := F.card
    tube := fun i => translateTube v (F.tube i) }

/-- Translate a shading by a fixed vector. -/
def translateShading {δ : ℝ} {F : Streamlined.TubeFamily δ}
    (v : Point3) (Y : Streamlined.TubeShading F) :
    Streamlined.TubeShading (translateFamily v F) :=
  { carrier := fun i => image (fun x : Point3 => x + v) (Y.carrier i)
    measurable_carrier := by
      intro i
      have h_eq : image (fun x : Point3 => x + v) (Y.carrier i) =
            (fun x : Point3 => x + (-v)) ⁻¹' (Y.carrier i) := by
        ext z
        simp only [Set.mem_image, Set.mem_preimage]
        constructor
        · rintro ⟨x, hx, rfl⟩
          simpa using hx
        · intro hz
          exact ⟨z + (-v), hz, by simp⟩
      rw [h_eq]
      exact (Y.measurable_carrier i).preimage (by fun_prop)
    subset_body := by
      intro i x hx
      rcases hx with ⟨y, hy, rfl⟩
      have hsub : y ∈ (F.toBodyFamily.body i).carrier := Y.subset_body i hy
      have h_eq : (F.toBodyFamily.body i).carrier = (F.tube i).carrier := by rfl
      rw [h_eq] at hsub
      have h : y + v ∈ (translateTube v (F.tube i)).carrier := by
        rw [translateTube_carrier]
        exact ⟨y, hsub, rfl⟩
      exact h }

/-- Translation preserves Nonempty. -/
lemma translateFamily_nonempty {δ : ℝ} (v : Point3) {F : Streamlined.TubeFamily δ}
    (h : F.Nonempty) : (translateFamily v F).Nonempty :=
  h

/-- Translation preserves IsEssentiallyDistinct. -/
lemma translateFamily_distinct {δ : ℝ} (v : Point3) {F : Streamlined.TubeFamily δ}
    (h : F.IsEssentiallyDistinct) :
    (translateFamily v F).IsEssentiallyDistinct := by
  intro i j hne
  exact translateTube_preserves_essentiallyDistinct v (h i j hne)

/-- The union of a translated shading is the translated union. -/
lemma translateShading_union {δ : ℝ} {F : Streamlined.TubeFamily δ}
    (v : Point3) (Y : Streamlined.TubeShading F) :
    (translateShading v Y).union = image (fun x : Point3 => x + v) Y.union := by
  ext x
  simp [translateShading, Shading.union, Streamlined.TubeShading, Fin.cast]
  <;> tauto

/-- Translation preserves shading mass. -/
lemma translateShading_mass {δ : ℝ} {F : Streamlined.TubeFamily δ}
    (v : Point3) (Y : Streamlined.TubeShading F) :
    (translateShading v Y).mass = Y.mass := by
  let f : Point3 → Point3 := fun x => x + v
  have h : ∀ i : Fin F.card, volume (image f (Y.carrier i)) = volume (Y.carrier i) := by
    intro i
    exact volume_translate (Y.measurable_carrier i)
  have hsum : ∑ i : Fin F.card, volume (image f (Y.carrier i)) =
        ∑ i : Fin F.card, volume (Y.carrier i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact h i
  have hcard : (translateFamily v F).card = F.card := by simp [translateFamily]
  let e : Fin (translateFamily v F).card ≃ Fin F.card :=
    { toFun := Fin.cast hcard,
      invFun := Fin.cast hcard.symm,
      left_inv := by intro x; apply Fin.ext; simp [Fin.cast],
      right_inv := by intro x; apply Fin.ext; simp [Fin.cast] }
  have h_main : (translateShading v Y).mass =
        ∑ i : Fin F.card, volume (image f (Y.carrier i)) := by
    have h2 : (translateShading v Y).mass =
          ∑ i : Fin (translateFamily v F).card, volume ((translateShading v Y).carrier i) := by rfl
    rw [h2]
    have h3 : ∑ i : Fin (translateFamily v F).card, volume ((translateShading v Y).carrier i) =
          ∑ i : Fin (translateFamily v F).card, volume (image f (Y.carrier (e i))) := by
      apply Finset.sum_congr rfl
      intro i _
      rfl
    rw [h3]
    exact e.sum_comp (fun j : Fin F.card => volume (image f (Y.carrier j)))
  rw [h_main, hsum]
  <;> rfl

/-- Translation preserves family mass. -/
lemma translateFamily_mass {δ : ℝ} (v : Point3) (F : Streamlined.TubeFamily δ) :
    (translateFamily v F).toBodyFamily.mass = F.toBodyFamily.mass := by
  have h : ∀ i : Fin F.card, (translateTube v (F.tube i)).volume = (F.tube i).volume := by
    intro i
    rw [DeltaTube.volume, translateTube_carrier]
    exact volume_translate Metric.isClosed_cthickening.measurableSet
  have hsum : ∑ i : Fin F.card, (translateTube v (F.tube i)).volume =
        ∑ i : Fin F.card, (F.tube i).volume := by
    apply Finset.sum_congr rfl
    intro i _
    exact h i
  have hdef : (translateFamily v F).toBodyFamily.mass =
        ∑ i : Fin F.card, (translateTube v (F.tube i)).volume := by
    simp [translateFamily, Streamlined.TubeFamily.toBodyFamily]
    <;> rfl
  have hdef2 : F.toBodyFamily.mass = ∑ i : Fin F.card, (F.tube i).volume := by rfl
  rw [hdef, hdef2, hsum]

/-- Translation preserves IsLambdaDense. -/
lemma translateShading_dense {δ : ℝ} {F : Streamlined.TubeFamily δ}
    (v : Point3) {Y : Streamlined.TubeShading F} {lambda : ENNReal}
    (h : Y.IsLambdaDense lambda) :
    (translateShading v Y).IsLambdaDense lambda := by
  have h1 : (translateFamily v F).toBodyFamily.mass = F.toBodyFamily.mass :=
    translateFamily_mass v F
  have h2 : (translateShading v Y).mass = Y.mass := translateShading_mass v Y
  have hgoal : lambda * (translateFamily v F).toBodyFamily.mass ≤
        (translateShading v Y).mass := by
    rw [h1, h2]
    exact h
  exact hgoal

/--
A tube centered at the origin (midpoint = 0) with radius `δ ≤ 1/2` has its
full carrier contained in the closed unit ball.
-/
lemma centered_tube_in_unitBall {δ : ℝ} (T : DeltaTube δ)
    (hmid : (T.base + (1 / 2 : ℝ) • T.direction) = 0)
    (hδ : 0 ≤ δ) (hδ_le : δ ≤ 1 / 2) :
    T.carrier ⊆ closedBall (0 : Point3) 1 := by
  intro x hx
  have h_compact : IsCompact (unitSegment T.base T.direction) := by
    apply IsCompact.image
    · exact isCompact_Icc
    · continuity
  have h_iff : x ∈ T.carrier ↔ ∃ (y : Point3),
        y ∈ unitSegment T.base T.direction ∧ dist x y ≤ δ := by
    have h : T.carrier = ⋃ y ∈ unitSegment T.base T.direction, closedBall y δ :=
      h_compact.cthickening_eq_biUnion_closedBall hδ
    rw [h]
    simp [mem_iUnion, mem_closedBall]
  rcases h_iff.mp hx with ⟨y, hy_seg, hdist⟩
  rcases hy_seg with ⟨t, ht, rfl⟩
  have hseg_norm : ‖T.base + t • T.direction‖ ≤ 1 / 2 := by
    have h1 : T.base + t • T.direction =
          ((t - 1 / 2 : ℝ) • T.direction) := by
      have h2 : T.base = -(1 / 2 : ℝ) • T.direction := by
        have h3 : T.base + (1 / 2 : ℝ) • T.direction = 0 := hmid
        simpa [sub_eq_zero] using eq_neg_of_add_eq_zero_left h3
      rw [h2]
      ext i <;> simp [smul_add, smul_smul] <;> ring
    rw [h1]
    have h4 : ‖(t - 1 / 2 : ℝ) • T.direction‖ =
          |(t - 1 / 2 : ℝ)| * ‖T.direction‖ := norm_smul _ _
    rw [h4]
    have h5 : ‖T.direction‖ = 1 := T.direction_unit
    rw [h5]
    have h6 : |(t - 1 / 2 : ℝ)| ≤ 1 / 2 := by
      rw [abs_le] <;> constructor <;> linarith [ht.1, ht.2]
    linarith
  have hx_norm : ‖x‖ ≤ 1 := by
    have h : ‖x‖ ≤ ‖T.base + t • T.direction‖ + dist x (T.base + t • T.direction) := by
      have h2 : ‖x‖ ≤ ‖T.base + t • T.direction‖ + ‖x - (T.base + t • T.direction)‖ := by
        have h3 : x = (T.base + t • T.direction) + (x - (T.base + t • T.direction)) := by abel
        rw [h3]
        simpa using norm_add_le (T.base + t • T.direction) (x - (T.base + t • T.direction))
      rw [←dist_eq_norm] at h2
      exact h2
    linarith
  simpa [mem_closedBall] using hx_norm

/--
Translating a tube by `-midpoint` centers it at the origin.
If `δ ≤ 1/2`, the translated tube's carrier lies in the unit ball.
-/
lemma translate_to_center_in_unitBall {δ : ℝ} (T : DeltaTube δ)
    (hδ : 0 ≤ δ) (hδ_le : δ ≤ 1 / 2) :
    let m := T.base + (1 / 2 : ℝ) • T.direction
    (translateTube (-m) T).carrier ⊆ closedBall (0 : Point3) 1 := by
  let m := T.base + (1 / 2 : ℝ) • T.direction
  let T' := translateTube (-m) T
  have hmid' : T'.base + (1 / 2 : ℝ) • T'.direction = 0 := by
    simp [T', translateTube, m] <;> abel
  exact centered_tube_in_unitBall T' hmid' hδ hδ_le

end TranslationInfrastructure
