import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseGroupingSetup
import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceCoarseFiberNonconcentrationInputs

/-!
# Incidence graph of selected fine fibers

This module connects the pure finite incidence graph used in PYZ Lemma 47
to the pointwise retained fibers and their coarse parents.
-/

noncomputable section

namespace Kakeya.Cinematic

local instance : DecidableEq C2Function := Classical.decEq _

/-- All function--rectangle incidences in a finite family of pointwise
function fibers. -/
def fineFiberIncidenceEdgesOn
    {β : Type*} [DecidableEq β]
    (rectangles : Finset β)
    (fiber : β → FiniteFunctionFamily) :
    Finset (C2Function × β) :=
  rectangles.biUnion fun rectangle =>
    (fiber rectangle).toFinset.image fun function =>
      (function, rectangle)

def fineFiberIncidenceEdges
    {β : Type*} [Fintype β] [DecidableEq β]
    (fiber : β → FiniteFunctionFamily) :
    Finset (C2Function × β) :=
  fineFiberIncidenceEdgesOn Finset.univ fiber

@[simp]
lemma mem_fineFiberIncidenceEdgesOn
    {β : Type*} [DecidableEq β]
    (rectangles : Finset β)
    (fiber : β → FiniteFunctionFamily)
    (function : C2Function) (rectangle : β) :
    (function, rectangle) ∈
        fineFiberIncidenceEdgesOn rectangles fiber ↔
      rectangle ∈ rectangles ∧
        function ∈ (fiber rectangle).carrier := by
  simp [fineFiberIncidenceEdgesOn, FiniteFunctionFamily.toFinset]

@[simp]
lemma mem_fineFiberIncidenceEdges
    {β : Type*} [Fintype β] [DecidableEq β]
    (fiber : β → FiniteFunctionFamily)
    (function : C2Function) (rectangle : β) :
    (function, rectangle) ∈ fineFiberIncidenceEdges fiber ↔
      function ∈ (fiber rectangle).carrier := by
  simp [fineFiberIncidenceEdges]

lemma fineFiberIncidenceEdgesOn_card
    {β : Type*} [DecidableEq β]
    (rectangles : Finset β)
    (fiber : β → FiniteFunctionFamily) :
    (fineFiberIncidenceEdgesOn rectangles fiber).card =
      ∑ rectangle ∈ rectangles, (fiber rectangle).card := by
  let edgesAt : β → Finset (C2Function × β) := fun rectangle =>
    (fiber rectangle).toFinset.image fun function =>
      (function, rectangle)
  have hdisjoint :
      (rectangles : Set β).PairwiseDisjoint edgesAt := by
    intro left _ right _ hne
    change Disjoint (edgesAt left) (edgesAt right)
    rw [Finset.disjoint_left]
    intro edge hedge_left hedge_right
    rcases Finset.mem_image.mp hedge_left with
      ⟨leftFunction, _, hleft⟩
    rcases Finset.mem_image.mp hedge_right with
      ⟨rightFunction, _, hright⟩
    have hsnd :
        (leftFunction, left).2 = (rightFunction, right).2 :=
      congrArg Prod.snd (hleft.trans hright.symm)
    exact hne hsnd
  have hcard :
      (fineFiberIncidenceEdgesOn rectangles fiber).card =
        ∑ rectangle ∈ rectangles, (edgesAt rectangle).card := by
    exact Finset.card_biUnion (h := hdisjoint)
  rw [hcard]
  apply Finset.sum_congr rfl
  intro rectangle _
  have himage :
      (edgesAt rectangle).card =
        (fiber rectangle).toFinset.card := by
    apply Finset.card_image_of_injOn
    intro left _ right _ heq
    exact congrArg Prod.fst heq
  rw [himage]
  exact
    (Set.ncard_eq_toFinset_card
      (fiber rectangle).carrier (fiber rectangle).finite).symm

lemma card_mul_le_fineFiberIncidenceEdgesOn
    {β : Type*} [DecidableEq β]
    (rectangles : Finset β)
    (fiber : β → FiniteFunctionFamily)
    (q : ℕ)
    (hlower : ∀ rectangle ∈ rectangles,
      q ≤ (fiber rectangle).card) :
    rectangles.card * q ≤
      (fineFiberIncidenceEdgesOn rectangles fiber).card := by
  rw [fineFiberIncidenceEdgesOn_card]
  calc
    rectangles.card * q =
        ∑ _rectangle ∈ rectangles, q := by
      simp [Finset.sum_const]
    _ ≤ ∑ rectangle ∈ rectangles, (fiber rectangle).card :=
      Finset.sum_le_sum fun rectangle hrectangle =>
        hlower rectangle hrectangle

lemma fineFiberIncidenceEdgesOn_card_le_mul
    {β : Type*} [DecidableEq β]
    (rectangles : Finset β)
    (fiber : β → FiniteFunctionFamily)
    (upper : ℕ)
    (hupper : ∀ rectangle ∈ rectangles,
      (fiber rectangle).card ≤ upper) :
    (fineFiberIncidenceEdgesOn rectangles fiber).card ≤
      rectangles.card * upper := by
  rw [fineFiberIncidenceEdgesOn_card]
  calc
    (∑ rectangle ∈ rectangles, (fiber rectangle).card) ≤
        ∑ _rectangle ∈ rectangles, upper :=
      Finset.sum_le_sum fun rectangle hrectangle =>
        hupper rectangle hrectangle
    _ = rectangles.card * upper := by
      simp [Finset.sum_const]

lemma incidenceRectangleFiber_subset_fiber_on
    {β : Type*} [DecidableEq β]
    (rectangles : Finset β)
    (fiber : β → FiniteFunctionFamily)
    (selected : Finset (C2Function × β))
    (hselected :
      selected ⊆ fineFiberIncidenceEdgesOn rectangles fiber)
    (rectangle : β) :
    incidenceRectangleFiber selected rectangle ⊆
      (fiber rectangle).toFinset := by
  intro function hfunction
  rcases Finset.mem_image.mp hfunction with
    ⟨edge, hedge, hedge_function⟩
  rcases edge with ⟨candidate, source⟩
  have hedge_selected : (candidate, source) ∈ selected :=
    (Finset.mem_filter.mp hedge).1
  have hsource : source = rectangle :=
    (Finset.mem_filter.mp hedge).2
  have hedge_full :=
    hselected hedge_selected
  have hcandidate :
      candidate ∈ (fiber source).carrier :=
    (mem_fineFiberIncidenceEdgesOn
      rectangles fiber candidate source).mp hedge_full |>.2
  subst source
  have hcandidate_eq : candidate = function := hedge_function
  subst candidate
  simpa [FiniteFunctionFamily.toFinset] using hcandidate

lemma incidenceRectangleFiber_subset_fiber
    {β : Type*} [Fintype β] [DecidableEq β]
    (fiber : β → FiniteFunctionFamily)
    (selected : Finset (C2Function × β))
    (hselected : selected ⊆ fineFiberIncidenceEdges fiber)
    (rectangle : β) :
    incidenceRectangleFiber selected rectangle ⊆
      (fiber rectangle).toFinset := by
  apply incidenceRectangleFiber_subset_fiber_on
    Finset.univ fiber selected
  simpa [fineFiberIncidenceEdges] using hselected

lemma incidenceFunctionSupport_subset_ambient_on
    {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (rectangles : Finset β)
    (fiber : β → FiniteFunctionFamily)
    (selected : Finset (C2Function × β))
    (hselected :
      selected ⊆ fineFiberIncidenceEdgesOn rectangles fiber)
    (ambient : FiniteFunctionFamily)
    (hfiber : ∀ rectangle ∈ rectangles,
      (fiber rectangle).carrier ⊆ ambient.carrier)
    (parent : β → γ) (coarse : γ) :
    (incidenceFunctionSupport selected parent coarse :
        Set C2Function) ⊆ ambient.carrier := by
  intro function hfunction
  rcases Finset.mem_image.mp hfunction with
    ⟨edge, hedge, hedgeFunction⟩
  have hedgeSelected : edge ∈ selected :=
    (Finset.mem_filter.mp hedge).1
  have hedgeFull := hselected hedgeSelected
  have hedgeData :=
    (mem_fineFiberIncidenceEdgesOn
      rectangles fiber edge.1 edge.2).mp hedgeFull
  have hfunctionFiber :
      function ∈ (fiber edge.2).carrier := by
    rw [← hedgeFunction]
    exact hedgeData.2
  exact hfiber edge.2 hedgeData.1 hfunctionFiber

lemma incidenceRectangleSupport_subset_selected
    {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (rectangles : Finset β)
    (fiber : β → FiniteFunctionFamily)
    (selected : Finset (C2Function × β))
    (hselected :
      selected ⊆ fineFiberIncidenceEdgesOn rectangles fiber)
    (parent : β → γ) (coarse : γ) :
    incidenceRectangleSupport selected parent coarse ⊆
      rectangles := by
  intro rectangle hrectangle
  rcases Finset.mem_image.mp hrectangle with
    ⟨edge, hedge, hedge_rectangle⟩
  rcases edge with ⟨function, source⟩
  have hedge_selected : (function, source) ∈ selected :=
    (Finset.mem_filter.mp hedge).1
  have hedge_full := hselected hedge_selected
  have hsource_mem :
      source ∈ rectangles :=
    (mem_fineFiberIncidenceEdgesOn
      rectangles fiber function source).mp hedge_full |>.1
  have hsource_eq : source = rectangle := hedge_rectangle
  simpa [hsource_eq] using hsource_mem

lemma incidenceRectangleSupport_subset_coarseFiber
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (fiber : Fin fine.card → FiniteFunctionFamily)
    (selected : Finset (C2Function × Fin fine.card))
    (hselected : selected ⊆ fineFiberIncidenceEdges fiber)
    (coarse : Fin data.coarse.card) :
    incidenceRectangleSupport selected data.parent coarse ⊆
      data.fiber coarse := by
  intro rectangle hrectangle
  rcases Finset.mem_image.mp hrectangle with
    ⟨edge, hedge, hedge_rectangle⟩
  rcases edge with ⟨function, source⟩
  have hedge_selected : (function, source) ∈ selected :=
    (Finset.mem_filter.mp hedge).1
  have hparent : data.parent source = coarse :=
    (Finset.mem_filter.mp hedge).2
  have hsource_eq : source = rectangle := hedge_rectangle
  subst source
  simpa [CoarseRectangleGroupingData.fiber] using hparent

lemma incidenceFunctionSupport_subset_coarseTangentFamily
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (fiber : Fin fine.card → FiniteFunctionFamily)
    (selected : Finset (C2Function × Fin fine.card))
    (hselected : selected ⊆ fineFiberIncidenceEdges fiber)
    (coarse : Fin data.coarse.card) :
    (incidenceFunctionSupport selected data.parent coarse :
        Set C2Function) ⊆
      (coarseTangentFamily data fiber coarse).carrier := by
  intro function hfunction
  rcases Finset.mem_image.mp hfunction with
    ⟨edge, hedge, hedge_function⟩
  rcases edge with ⟨candidate, rectangle⟩
  have hedge_selected : (candidate, rectangle) ∈ selected :=
    (Finset.mem_filter.mp hedge).1
  have hparent : data.parent rectangle = coarse :=
    (Finset.mem_filter.mp hedge).2
  have hedge_full :=
    hselected hedge_selected
  have hcandidate :
      candidate ∈ (fiber rectangle).carrier :=
    (mem_fineFiberIncidenceEdges fiber candidate rectangle).mp
      hedge_full
  have hrectangle : rectangle ∈ data.fiber coarse := by
    simpa [CoarseRectangleGroupingData.fiber] using hparent
  have hcandidate_union :
      candidate ∈
        Finset.biUnion (data.fiber coarse)
          (fun index => (fiber index).toFinset) :=
    Finset.mem_biUnion.mpr
      ⟨rectangle, hrectangle, by
        simpa [FiniteFunctionFamily.toFinset] using hcandidate⟩
  have hcandidate_eq : candidate = function := hedge_function
  subst candidate
  simpa [coarseTangentFamily] using hcandidate_union

lemma incidenceSupportFamily_tangent
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R tangency : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (fiber : Fin fine.card → FiniteFunctionFamily)
    (selected : Finset (C2Function × Fin fine.card))
    (hselected : selected ⊆ fineFiberIncidenceEdges fiber)
    (hall : ∀ coarse, ∀ function ∈
        (coarseTangentFamily data fiber coarse).carrier,
      (data.coarse.rectangle coarse).IsLambdaTangent
        function tangency)
    (coarse : Fin data.coarse.card) :
    ∀ function ∈
        (incidenceSupportFamily selected data.parent coarse).carrier,
      (data.coarse.rectangle coarse).IsLambdaTangent
        function tangency := by
  intro function hfunction
  apply hall coarse function
  exact incidenceFunctionSupport_subset_coarseTangentFamily
    data fiber selected hselected coarse hfunction

end Kakeya.Cinematic
