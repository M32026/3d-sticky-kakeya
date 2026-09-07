import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseSupportCardinalityRegularization
import MyLeanRepo.Kakeya.Cinematic.Section5.FineFiberIncidenceGraph
import MyLeanRepo.Kakeya.Cinematic.Section5.FinsetRectangleSubfamily
import MyLeanRepo.Kakeya.Cinematic.Section5.ClusterNonconcentrationArithmetic
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.TangentCountExact

/-!
# Selected coarse rectangles with incidence supports

This module packages a selected set of coarse parents as a rectangle
subfamily and reindexes the corresponding regularized incidence supports.
-/

noncomputable section

namespace Kakeya.Cinematic

local instance selectedCoarseIncidenceSubfamilyDecidableEq :
    DecidableEq C2Function := Classical.decEq _

def selectedCoarseSubfamily
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (selectedParents : Finset (Fin data.coarse.card)) :
    RectangleSubfamily data.coarse :=
  RectangleSubfamily.ofFinset data.coarse selectedParents

def selectedCoarseIncidenceSupport
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (selectedEdges : Finset (C2Function × Fin fine.card))
    (selectedParents : Finset (Fin data.coarse.card))
    (index : Fin (selectedCoarseSubfamily data selectedParents).card) :
    FiniteFunctionFamily :=
  incidenceSupportFamily selectedEdges data.parent
    ((selectedCoarseSubfamily data selectedParents).embedding index)

lemma selectedCoarseSubfamily_parent_mem
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (selectedParents : Finset (Fin data.coarse.card))
    (index : Fin (selectedCoarseSubfamily data selectedParents).card) :
    (selectedCoarseSubfamily data selectedParents).embedding index ∈
      selectedParents :=
  RectangleSubfamily.ofFinset_embedding_mem
    data.coarse selectedParents index

@[simp]
lemma selectedCoarseSubfamily_card
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (selectedParents : Finset (Fin data.coarse.card)) :
    (selectedCoarseSubfamily data selectedParents).card =
      selectedParents.card :=
  rfl

lemma selectedCoarseIncidenceSupport_card_range
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (selectedEdges : Finset (C2Function × Fin fine.card))
    (selectedParents : Finset (Fin data.coarse.card))
    {lower upper : ℕ}
    (hrange : ∀ coarse ∈ selectedParents,
      lower ≤
          (incidenceFunctionSupport
            selectedEdges data.parent coarse).card ∧
        (incidenceFunctionSupport
          selectedEdges data.parent coarse).card < upper)
    (index : Fin (selectedCoarseSubfamily data selectedParents).card) :
    lower ≤
        (selectedCoarseIncidenceSupport
          data selectedEdges selectedParents index).card ∧
      (selectedCoarseIncidenceSupport
        data selectedEdges selectedParents index).card < upper := by
  let coarse :=
    (selectedCoarseSubfamily data selectedParents).embedding index
  have hcoarse : coarse ∈ selectedParents :=
    selectedCoarseSubfamily_parent_mem data selectedParents index
  have h := hrange coarse hcoarse
  simpa [selectedCoarseIncidenceSupport, coarse,
    incidenceSupportFamily, FiniteFunctionFamily.card] using h

lemma selectedCoarseIncidenceSupport_tangent
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R tangency : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (rectangles : Finset (Fin fine.card))
    (fiber : Fin fine.card → FiniteFunctionFamily)
    (selectedEdges : Finset (C2Function × Fin fine.card))
    (hselected :
      selectedEdges ⊆ fineFiberIncidenceEdgesOn rectangles fiber)
    (selectedParents : Finset (Fin data.coarse.card))
    (hall : ∀ coarse, ∀ function ∈
        (coarseTangentFamily data fiber coarse).carrier,
      (data.coarse.rectangle coarse).IsLambdaTangent
        function tangency)
    (index : Fin (selectedCoarseSubfamily data selectedParents).card) :
    ∀ function ∈
        (selectedCoarseIncidenceSupport
          data selectedEdges selectedParents index).carrier,
      ((selectedCoarseSubfamily data selectedParents).family.rectangle index
        ).IsLambdaTangent function tangency := by
  intro function hfunction
  let coarse :=
    (selectedCoarseSubfamily data selectedParents).embedding index
  have hon_subset :
      fineFiberIncidenceEdgesOn rectangles fiber ⊆
        fineFiberIncidenceEdges fiber := by
    intro edge hedge
    rcases edge with ⟨candidate, rectangle⟩
    have hedge' :=
      (mem_fineFiberIncidenceEdgesOn
        rectangles fiber candidate rectangle).mp hedge
    exact
      (mem_fineFiberIncidenceEdges
        fiber candidate rectangle).mpr hedge'.2
  have hselected_full :
      selectedEdges ⊆ fineFiberIncidenceEdges fiber :=
    hselected.trans hon_subset
  have htangent :=
    incidenceSupportFamily_tangent data fiber selectedEdges
      hselected_full
      hall coarse function
  have h := htangent hfunction
  exact h

lemma selectedCoarseIncidenceSupport_subset
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (selectedEdges : Finset (C2Function × Fin fine.card))
    (selectedParents : Finset (Fin data.coarse.card))
    (ambient : FiniteFunctionFamily)
    (hsupport : ∀ coarse ∈ selectedParents,
      (incidenceFunctionSupport
        selectedEdges data.parent coarse : Set C2Function) ⊆
        ambient.carrier)
    (index : Fin (selectedCoarseSubfamily data selectedParents).card) :
    (selectedCoarseIncidenceSupport
      data selectedEdges selectedParents index).carrier ⊆
      ambient.carrier := by
  let coarse :=
    (selectedCoarseSubfamily data selectedParents).embedding index
  have hcoarse : coarse ∈ selectedParents :=
    selectedCoarseSubfamily_parent_mem data selectedParents index
  simpa [selectedCoarseIncidenceSupport, incidenceSupportFamily,
    coarse] using hsupport coarse hcoarse

lemma selectedCoarseIncidenceSupport_cover
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (selectedEdges : Finset (C2Function × Fin fine.card))
    (selectedParents : Finset (Fin data.coarse.card))
    (centers : Finset C2Function) (radius : ℝ)
    (hcover : ∀ coarse ∈ selectedParents,
      (incidenceFunctionSupport
        selectedEdges data.parent coarse : Set C2Function) ⊆
        ⋃ center ∈ (centers : Set C2Function),
          c2Ball center radius)
    (index : Fin (selectedCoarseSubfamily data selectedParents).card) :
    (selectedCoarseIncidenceSupport
      data selectedEdges selectedParents index).carrier ⊆
      ⋃ center ∈ (centers : Set C2Function),
        c2Ball center radius := by
  let coarse :=
    (selectedCoarseSubfamily data selectedParents).embedding index
  have hcoarse : coarse ∈ selectedParents :=
    selectedCoarseSubfamily_parent_mem data selectedParents index
  simpa [selectedCoarseIncidenceSupport, incidenceSupportFamily,
    coarse] using hcover coarse hcoarse

lemma selectedCoarseIncidenceSupport_tangentCount
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R tangency : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (rectangles : Finset (Fin fine.card))
    (fiber : Fin fine.card → FiniteFunctionFamily)
    (selectedEdges : Finset (C2Function × Fin fine.card))
    (hselected :
      selectedEdges ⊆ fineFiberIncidenceEdgesOn rectangles fiber)
    (selectedParents : Finset (Fin data.coarse.card))
    (hall : ∀ coarse, ∀ function ∈
        (coarseTangentFamily data fiber coarse).carrier,
      (data.coarse.rectangle coarse).IsLambdaTangent
        function tangency)
    (index : Fin (selectedCoarseSubfamily data selectedParents).card) :
    RectangleFamily.tangentCount
        ((selectedCoarseSubfamily data selectedParents).family.rectangle index)
        (selectedCoarseIncidenceSupport
          data selectedEdges selectedParents index) tangency =
      (selectedCoarseIncidenceSupport
        data selectedEdges selectedParents index).card := by
  apply RectangleFamily.tangentCount_eq_card_of_all_tangent
  exact selectedCoarseIncidenceSupport_tangent
    data rectangles fiber selectedEdges hselected
      selectedParents hall index

lemma selectedCoarseIncidenceSupport_cluster_tangentCount
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R tangency radius : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (rectangles : Finset (Fin fine.card))
    (fiber : Fin fine.card → FiniteFunctionFamily)
    (selectedEdges : Finset (C2Function × Fin fine.card))
    (hselected :
      selectedEdges ⊆ fineFiberIncidenceEdgesOn rectangles fiber)
    (selectedParents : Finset (Fin data.coarse.card))
    (hall : ∀ coarse, ∀ function ∈
        (coarseTangentFamily data fiber coarse).carrier,
      (data.coarse.rectangle coarse).IsLambdaTangent
        function tangency)
    (index : Fin (selectedCoarseSubfamily data selectedParents).card)
    (center : C2Function) :
    RectangleFamily.tangentCount
        ((selectedCoarseSubfamily data selectedParents).family.rectangle index)
        ((selectedCoarseIncidenceSupport
          data selectedEdges selectedParents index).cluster center radius)
        tangency =
      ((selectedCoarseIncidenceSupport
        data selectedEdges selectedParents index).cluster center radius).card := by
  apply RectangleFamily.tangentCount_cluster_eq_card_of_all_tangent
  exact selectedCoarseIncidenceSupport_tangent
    data rectangles fiber selectedEdges hselected
      selectedParents hall index

lemma selectedCoarseIncidenceSupport_cluster_tangentCount_half
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R tangency radius : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (rectangles : Finset (Fin fine.card))
    (fiber : Fin fine.card → FiniteFunctionFamily)
    (selectedEdges : Finset (C2Function × Fin fine.card))
    (hselected :
      selectedEdges ⊆ fineFiberIncidenceEdgesOn rectangles fiber)
    (selectedParents : Finset (Fin data.coarse.card))
    (hall : ∀ coarse, ∀ function ∈
        (coarseTangentFamily data fiber coarse).carrier,
      (data.coarse.rectangle coarse).IsLambdaTangent
        function tangency)
    {logLoss coefficient : ℝ}
    (hsmall : 4 * logLoss * coefficient ≤ 1)
    (hNonconcentration :
      ∀ coarse ∈ selectedParents, ∀ center,
        ((((incidenceSupportFamily
              selectedEdges data.parent coarse).carrier ∩
            c2Ball center radius).ncard : ℕ) : ℝ) ≤
          (2 * logLoss) * coefficient *
            ((incidenceSupportFamily
              selectedEdges data.parent coarse).card : ℝ))
    (index : Fin (selectedCoarseSubfamily data selectedParents).card)
    (center : C2Function) :
    2 * RectangleFamily.tangentCount
          ((selectedCoarseSubfamily data selectedParents).family.rectangle index)
          ((selectedCoarseIncidenceSupport
            data selectedEdges selectedParents index).cluster center radius)
          tangency ≤
      RectangleFamily.tangentCount
        ((selectedCoarseSubfamily data selectedParents).family.rectangle index)
        (selectedCoarseIncidenceSupport
          data selectedEdges selectedParents index) tangency := by
  let coarse :=
    (selectedCoarseSubfamily data selectedParents).embedding index
  have hcoarse : coarse ∈ selectedParents :=
    selectedCoarseSubfamily_parent_mem data selectedParents index
  have hcluster :
      (((incidenceSupportFamily
            selectedEdges data.parent coarse).carrier ∩
          c2Ball center radius).ncard : ℕ) =
        ((selectedCoarseIncidenceSupport
          data selectedEdges selectedParents index).cluster
            center radius).card := by
    rfl
  have htotal :
      (incidenceSupportFamily
        selectedEdges data.parent coarse).card =
        (selectedCoarseIncidenceSupport
          data selectedEdges selectedParents index).card := by
    rfl
  have hhalf :
      2 * ((selectedCoarseIncidenceSupport
          data selectedEdges selectedParents index).cluster
            center radius).card ≤
        (selectedCoarseIncidenceSupport
          data selectedEdges selectedParents index).card := by
    apply cluster_half_of_incidence_nonconcentration hsmall
    rw [← hcluster, ← htotal]
    exact hNonconcentration coarse hcoarse center
  rw [
    selectedCoarseIncidenceSupport_cluster_tangentCount
      data rectangles fiber selectedEdges hselected
        selectedParents hall index center,
    selectedCoarseIncidenceSupport_tangentCount
      data rectangles fiber selectedEdges hselected
        selectedParents hall index]
  exact hhalf

lemma selectedCoarseSubfamily_centers
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (selectedParents : Finset (Fin data.coarse.card)) :
    (selectedCoarseSubfamily data selectedParents).family.CentersIn family :=
  (selectedCoarseSubfamily data selectedParents).centersIn_transfer
    data.coarse_centers

lemma selectedCoarseSubfamily_central
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (selectedParents : Finset (Fin data.coarse.card)) :
    ((selectedCoarseSubfamily data selectedParents).family
      ).IsOverCentralQuarterOf I :=
  RectangleSubfamily.overCentralQuarter_transfer
    (selectedCoarseSubfamily data selectedParents)
    data.coarse_central

lemma selectedCoarseSubfamily_incomparable
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (selectedParents : Finset (Fin data.coarse.card)) :
    ((selectedCoarseSubfamily data selectedParents).family
      ).IsPairwiseIncomparable family 100 :=
  RectangleSubfamily.ofFinset_incomparable
    data.coarse_incomparable selectedParents

lemma selectedCoarseSubfamily_nonempty
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    {selectedParents : Finset (Fin data.coarse.card)}
    (hselected : selectedParents.Nonempty) :
    (selectedCoarseSubfamily data selectedParents).family.Nonempty :=
  RectangleSubfamily.ofFinset_nonempty hselected

end Kakeya.Cinematic
