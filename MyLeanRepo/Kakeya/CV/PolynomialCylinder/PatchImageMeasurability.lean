import MyLeanRepo.Kakeya.CV.PolynomialCylinder.RegularCover
import MyLeanRepo.Kakeya.CV.GeometricMeasure.GraphPullbackMeasure

/-!
# Measurability of graph patch images in the product space
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real Classical

namespace Kakeya.CV

variable {k : ℕ} {P : PolynomialParameterization k}

/-- Projection from R3 to R2 according to the graph direction.
For dir=0 (x-graph): projects to (z2, z1) so that projection of xGraphMap is identity.
For dir=1 (y-graph): projects to (z0, z2).
For dir=2 (z-graph): projects to (z0, z1) = graphProjection. -/
def dirProjection (dir : Fin 3) : Point 3 → Point 2 :=
  match dir with
  | 0 => fun z => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![z 2, z 1]
  | 1 => fun z => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![z 0, z 2]
  | 2 => graphProjection

/-- The graph-value coordinate according to direction. -/
def dirCoord (dir : Fin 3) (z : Point 3) : ℝ := z dir

lemma dirProjection_continuous (dir : Fin 3) : Continuous (dirProjection dir) := by
  fin_cases dir
  · exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
      (continuous_pi fun i : Fin 2 => by
        fin_cases i <;> exact PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) _)
  · exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
      (continuous_pi fun i : Fin 2 => by
        fin_cases i <;> exact PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) _)
  · exact graphProjection_continuous

lemma dirCoord_continuous (dir : Fin 3) : Continuous (dirCoord dir) :=
  PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) dir

/-- `swapCoords` component formula. -/
lemma swapCoords_apply (i j : Fin 3) (z : Point 3) (k : Fin 3) :
    (swapCoords i j z) k =
      if k = i then z j else if k = j then z i else z k := by
  simp [swapCoords, permuteCoords_apply, Equiv.swap_apply_def]
  <;> split_ifs <;> tauto

/-- A point is on a directional graph exactly when its directional projection
is the base point and its selected coordinate is the graph value. -/
lemma dirGraphMap_iff
    (dir : Fin 3) (g : Point 2 → ℝ) (z : Point 3) (y : Point 2) :
    z = dirGraphMap dir g y ↔
      dirProjection dir z = y ∧ dirCoord dir z = g y := by
  fin_cases dir
  · have h_xgraph_comp : ∀ (i : Fin 3),
        (xGraphMap g y) i =
          match i with
          | 0 => g y
          | 1 => y 1
          | 2 => y 0 := by
      intro i
      fin_cases i <;> simp [xGraphMap, graphMap, swapCoords_apply] <;> rfl
    constructor
    · intro h
      have h0 : z 0 = g y := by rw [h] <;> exact h_xgraph_comp 0
      have h1 : z 1 = y 1 := by rw [h] <;> exact h_xgraph_comp 1
      have h2 : z 2 = y 0 := by rw [h] <;> exact h_xgraph_comp 2
      constructor
      · ext j
        fin_cases j <;> simp [dirProjection, h2, h1] <;> rfl
      · exact h0
    · rintro ⟨hproj, hcoord⟩
      have h1 : z 1 = y 1 := by
        have h : (dirProjection 0 z) 1 = y 1 :=
          congr_arg (fun p : Point 2 => p 1) hproj
        simpa [dirProjection] using h
      have h2 : z 2 = y 0 := by
        have h : (dirProjection 0 z) 0 = y 0 :=
          congr_arg (fun p : Point 2 => p 0) hproj
        simpa [dirProjection] using h
      have h0 : z 0 = g y := by
        simpa [dirCoord] using hcoord
      ext i
      fin_cases i <;>
        simp [dirGraphMap, h_xgraph_comp, h0, h1, h2] <;> tauto
  · have h_ygraph_comp : ∀ (i : Fin 3),
        (yGraphMap g y) i =
          match i with
          | 0 => y 0
          | 1 => g y
          | 2 => y 1 := by
      intro i
      fin_cases i <;> simp [yGraphMap, graphMap, swapCoords_apply] <;> rfl
    constructor
    · intro h
      have h0 : z 0 = y 0 := by rw [h] <;> exact h_ygraph_comp 0
      have h1 : z 1 = g y := by rw [h] <;> exact h_ygraph_comp 1
      have h2 : z 2 = y 1 := by rw [h] <;> exact h_ygraph_comp 2
      constructor
      · ext j
        fin_cases j <;> simp [dirProjection, h0, h2] <;> rfl
      · exact h1
    · rintro ⟨hproj, hcoord⟩
      have h0 : z 0 = y 0 := by
        have h : (dirProjection 1 z) 0 = y 0 :=
          congr_arg (fun p : Point 2 => p 0) hproj
        simpa [dirProjection] using h
      have h2 : z 2 = y 1 := by
        have h : (dirProjection 1 z) 1 = y 1 :=
          congr_arg (fun p : Point 2 => p 1) hproj
        simpa [dirProjection] using h
      have h1 : z 1 = g y := by
        simpa [dirCoord] using hcoord
      ext i
      fin_cases i <;>
        simp [dirGraphMap, h_ygraph_comp, h0, h1, h2] <;> tauto
  · have h_graph_comp : ∀ (i : Fin 3),
        (graphMap g y) i =
          match i with
          | 0 => y 0
          | 1 => y 1
          | 2 => g y := by
      intro i
      fin_cases i <;> simp [graphMap] <;> rfl
    constructor
    · intro h
      have h0 : z 0 = y 0 := by rw [h] <;> exact h_graph_comp 0
      have h1 : z 1 = y 1 := by rw [h] <;> exact h_graph_comp 1
      have h2 : z 2 = g y := by rw [h] <;> exact h_graph_comp 2
      constructor
      · ext j
        fin_cases j <;>
          simp [dirProjection, graphProjection, h0, h1] <;> rfl
      · exact h2
    · rintro ⟨hproj, hcoord⟩
      have h0 : z 0 = y 0 := by
        have h : (dirProjection 2 z) 0 = y 0 :=
          congr_arg (fun p : Point 2 => p 0) hproj
        simpa [dirProjection, graphProjection] using h
      have h1 : z 1 = y 1 := by
        have h : (dirProjection 2 z) 1 = y 1 :=
          congr_arg (fun p : Point 2 => p 1) hproj
        simpa [dirProjection, graphProjection] using h
      have h2 : z 2 = g y := by
        simpa [dirCoord] using hcoord
      ext i
      fin_cases i <;>
        simp [dirGraphMap, h_graph_comp, h0, h1, h2] <;> tauto

/-- The joint set of a unified direction-tagged patch. -/
def coverPatchImage (patch : CoverPatch k P) :
    Set (CoefficientSpace P.dim × Point 3) :=
  {p | p.1 ∈ patch.V ∧
    p.2 ∈ dirGraphMap patch.dir (patch.g p.1) '' patch.A}

/-- Unified patch images are measurable sets. -/
lemma coverPatchImage_measurable (patch : CoverPatch k P) :
    MeasurableSet (coverPatchImage patch) := by
  let Coeff := CoefficientSpace P.dim
  let dir : Fin 3 := patch.dir
  let V := patch.V
  let A := patch.A
  let g := patch.g
  have hdirProj_cont : Continuous (dirProjection dir) :=
    dirProjection_continuous dir
  have hdirCoord_cont : Continuous (dirCoord dir) :=
    dirCoord_continuous dir
  let Doms : Set (Coeff × Point 3) :=
    V ×ˢ {z | dirProjection dir z ∈ A}
  have hDoms_open : IsOpen Doms :=
    patch.hV_open.prod (hdirProj_cont.isOpen_preimage _ patch.hA_open)
  have hDoms_meas : MeasurableSet Doms := hDoms_open.measurableSet
  let h2 : Coeff × Point 3 → ℝ :=
    Set.piecewise Doms
      (fun p : Coeff × Point 3 => g p.1 (dirProjection dir p.2))
      (fun _ => 0)
  have h_cont_on :
      ContinuousOn
        (fun p : Coeff × Point 3 => g p.1 (dirProjection dir p.2)) Doms := by
    have h1 :
        ContinuousOn (fun q : Coeff × Point 2 => g q.1 q.2) (V ×ˢ A) :=
      patch.hg_smooth.continuousOn
    have h_fst : ContinuousOn (fun p : Coeff × Point 3 => p.1) Doms :=
      continuous_fst.continuousOn
    have h_snd_proj :
        ContinuousOn (fun p : Coeff × Point 3 => dirProjection dir p.2) Doms :=
      (hdirProj_cont.comp continuous_snd).continuousOn
    have h_map :
        ContinuousOn
          (fun p : Coeff × Point 3 => (p.1, dirProjection dir p.2)) Doms :=
      h_fst.prodMk h_snd_proj
    exact h1.comp h_map fun _ h => h
  have h2_meas : Measurable h2 :=
    h_cont_on.measurable_piecewise continuousOn_const hDoms_meas
  let h1 : Coeff × Point 3 → ℝ := fun p => dirCoord dir p.2
  have h1_meas : Measurable h1 :=
    (hdirCoord_cont.comp continuous_snd).measurable
  let S1 : Set (Coeff × Point 3) := {p | p.1 ∈ V}
  let S2 : Set (Coeff × Point 3) := {p | dirProjection dir p.2 ∈ A}
  let S3 : Set (Coeff × Point 3) := {p | h1 p = h2 p}
  have hS1_meas : MeasurableSet S1 :=
    patch.hV_open.measurableSet.preimage measurable_fst
  have hS2_meas : MeasurableSet S2 :=
    patch.hA_open.measurableSet.preimage
      (hdirProj_cont.comp continuous_snd).measurable
  have hS3_meas : MeasurableSet S3 := by
    have h_diff : Measurable (fun p => h1 p - h2 p) := h1_meas.sub h2_meas
    have h_eq : S3 = {p | h1 p - h2 p = 0} := by
      ext p
      simp [S3, sub_eq_zero] <;> ring
    rw [h_eq]
    exact h_diff (MeasurableSet.singleton 0)
  have h_main : coverPatchImage patch = (S1 ∩ S2) ∩ S3 := by
    ext p
    rcases p with ⟨x, z⟩
    change
      (x ∈ V ∧
          z ∈ dirGraphMap dir (g x) '' A) ↔
        ((x ∈ V ∧ dirProjection dir z ∈ A) ∧
          h1 (x, z) = h2 (x, z))
    constructor
    · rintro ⟨hxV, y, hyA, rfl⟩
      have h_iff :=
        (dirGraphMap_iff dir (g x) (dirGraphMap dir (g x) y) y).mp rfl
      have h_in_Doms : (x, dirGraphMap dir (g x) y) ∈ Doms := by
        refine ⟨hxV, ?_⟩
        change dirProjection dir (dirGraphMap dir (g x) y) ∈ A
        rw [h_iff.1]
        exact hyA
      have h_h2 :
          h2 (x, dirGraphMap dir (g x) y) = g x y := by
        dsimp only [h2]
        rw [Set.piecewise_eq_of_mem Doms _ _ h_in_Doms, h_iff.1]
      have h_h1 :
          h1 (x, dirGraphMap dir (g x) y) = g x y := by
        simpa [h1] using h_iff.2
      have hproj : dirProjection dir (dirGraphMap dir (g x) y) ∈ A := by
        rw [h_iff.1]
        exact hyA
      exact ⟨⟨hxV, hproj⟩, h_h1.trans h_h2.symm⟩
    · rintro ⟨⟨hxV, hprojA⟩, heq⟩
      let y := dirProjection dir z
      have hyA : y ∈ A := hprojA
      have h_in_Doms : (x, z) ∈ Doms := ⟨hxV, hyA⟩
      have h_h2 : h2 (x, z) = g x y := by
        dsimp only [h2]
        rw [Set.piecewise_eq_of_mem Doms _ _ h_in_Doms]
      have h_coord : dirCoord dir z = g x y := by
        have h : h1 (x, z) = h2 (x, z) := heq
        change dirCoord dir z = h2 (x, z) at h
        rw [h_h2] at h
        exact h
      have h_z_eq : z = dirGraphMap dir (g x) y :=
        (dirGraphMap_iff dir (g x) z y).mpr ⟨rfl, h_coord⟩
      exact ⟨hxV, y, hyA, h_z_eq.symm⟩
  rw [h_main]
  exact (hS1_meas.inter hS2_meas).inter hS3_meas

end Kakeya.CV
