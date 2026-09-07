import MyLeanRepo.Kakeya.Cinematic.Section5.FiniteHeavySelection
import MyLeanRepo.Kakeya.Cinematic.Section5.FineFiberIncidenceGraph
import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceSupportDoubleCount
import MyLeanRepo.Kakeya.Cinematic.Section5.ParentFiberCardinalityRegularizationInputs

/-!
# Decompose selected incidence mass by coarse parent

These exact cardinality identities support the two heavy refinements after
incidence-degree regularization.
-/

noncomputable section

namespace Kakeya.Cinematic

attribute [local instance] Classical.decEq

def incidenceParentSupport
    {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (edges : Finset (α × β)) (parent : β → γ) : Finset γ :=
  edges.image fun edge => parent edge.2

def incidenceParentEdges
    {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (edges : Finset (α × β)) (parent : β → γ)
    (coarse : γ) : Finset (α × β) :=
  edges.filter fun edge => parent edge.2 = coarse

lemma incidenceParentEdges_nonempty_iff
    {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (edges : Finset (α × β)) (parent : β → γ)
    (coarse : γ) :
    (incidenceParentEdges edges parent coarse).Nonempty ↔
      coarse ∈ incidenceParentSupport edges parent := by
  constructor
  · rintro ⟨edge, hedge⟩
    have hedge' := Finset.mem_filter.mp hedge
    exact Finset.mem_image.mpr
      ⟨edge, hedge'.1, hedge'.2⟩
  · intro hcoarse
    rcases Finset.mem_image.mp hcoarse with
      ⟨edge, hedge, hedge_parent⟩
    exact ⟨edge, Finset.mem_filter.mpr
      ⟨hedge, hedge_parent⟩⟩

lemma sum_incidenceParentEdges_card
    {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (edges : Finset (α × β)) (parent : β → γ) :
    ∑ coarse ∈ incidenceParentSupport edges parent,
        (incidenceParentEdges edges parent coarse).card =
      edges.card := by
  have hmaps :
      (edges : Set (α × β)).MapsTo
        (fun edge => parent edge.2)
        (incidenceParentSupport edges parent : Set γ) := by
    intro edge hedge
    exact Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
  simpa [incidenceParentEdges] using
    (Finset.card_eq_sum_card_fiberwise hmaps).symm

lemma incidenceParentEdges_card_eq_rectangle_sum
    {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (edges : Finset (α × β)) (parent : β → γ)
    (coarse : γ) :
    (incidenceParentEdges edges parent coarse).card =
      ∑ rectangle ∈ incidenceRectangleSupport edges parent coarse,
        (incidenceRectangleFiber edges rectangle).card := by
  let parentEdges := incidenceParentEdges edges parent coarse
  let rectangles := incidenceRectangleSupport edges parent coarse
  have hrectangles :
      rectangles = parentEdges.image Prod.snd := by
    rfl
  have hmaps :
      (parentEdges : Set (α × β)).MapsTo
        Prod.snd (rectangles : Set β) := by
    intro edge hedge
    rw [hrectangles]
    exact Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
  have hfiber :
      ∀ rectangle ∈ rectangles,
        (parentEdges.filter fun edge => edge.2 = rectangle).card =
          (incidenceRectangleFiber edges rectangle).card := by
    intro rectangle hrectangle
    have hparent : parent rectangle = coarse := by
      rw [hrectangles] at hrectangle
      rcases Finset.mem_image.mp hrectangle with
        ⟨edge, hedge, hedge_rectangle⟩
      have hedge_parent :
          parent edge.2 = coarse :=
        (Finset.mem_filter.mp hedge).2
      rwa [← hedge_rectangle]
    have heq :
        parentEdges.filter (fun edge => edge.2 = rectangle) =
          edges.filter (fun edge => edge.2 = rectangle) := by
      ext edge
      simp only [Finset.mem_filter, parentEdges,
        incidenceParentEdges]
      constructor
      · rintro ⟨⟨hedge, _⟩, hedge_rectangle⟩
        exact ⟨hedge, hedge_rectangle⟩
      · rintro ⟨hedge, hedge_rectangle⟩
        exact ⟨⟨hedge, by
          rw [hedge_rectangle]
          exact hparent⟩, hedge_rectangle⟩
    rw [heq, incidenceRectangleFiber]
    apply Eq.symm
    apply Finset.card_image_of_injOn
    intro left hleft right hright hfst
    have hleft_snd : left.2 = rectangle :=
      (Finset.mem_filter.mp hleft).2
    have hright_snd : right.2 = rectangle :=
      (Finset.mem_filter.mp hright).2
    exact Prod.ext hfst
      (hleft_snd.trans hright_snd.symm)
  calc
    (incidenceParentEdges edges parent coarse).card =
        ∑ rectangle ∈ rectangles,
          (parentEdges.filter fun edge =>
            edge.2 = rectangle).card := by
      exact Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ rectangle ∈ rectangles,
          (incidenceRectangleFiber edges rectangle).card := by
      apply Finset.sum_congr rfl
      intro rectangle hrectangle
      exact hfiber rectangle hrectangle

lemma incidenceCountOverParent_support_eq_parentEdges_card
    {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [Fintype β]
    (edges : Finset (α × β)) (parent : β → γ)
    (coarse : γ) :
    incidenceCountOverParent edges parent coarse
        (incidenceFunctionSupport edges parent coarse) =
      (incidenceParentEdges edges parent coarse).card := by
  have hinter :
      ∀ rectangle ∈
          incidenceRectangleSupport edges parent coarse,
        incidenceRectangleFiber edges rectangle ∩
            incidenceFunctionSupport edges parent coarse =
          incidenceRectangleFiber edges rectangle := by
    intro rectangle hrectangle
    apply Finset.inter_eq_left.mpr
    intro function hfunction
    rcases Finset.mem_image.mp hfunction with
      ⟨edge, hedge, rfl⟩
    have hedge_mem : edge ∈ edges :=
      (Finset.mem_filter.mp hedge).1
    have hedge_rect : edge.2 = rectangle :=
      (Finset.mem_filter.mp hedge).2
    have hparent : parent rectangle = coarse := by
      rcases Finset.mem_image.mp hrectangle with
        ⟨edge', hedge', heq⟩
      have hp : parent edge'.2 = coarse :=
        (Finset.mem_filter.mp hedge').2
      rwa [← heq]
    apply Finset.mem_image.mpr
    refine
      ⟨edge, Finset.mem_filter.mpr ⟨hedge_mem, ?_⟩, rfl⟩
    rw [hedge_rect]
    exact hparent
  rw [incidenceCountOverParent]
  have hsum :
      (∑ rectangle ∈
          incidenceRectangleSupport edges parent coarse,
        (incidenceRectangleFiber edges rectangle ∩
          incidenceFunctionSupport edges parent coarse).card) =
        ∑ rectangle ∈
          incidenceRectangleSupport edges parent coarse,
          (incidenceRectangleFiber edges rectangle).card := by
    apply Finset.sum_congr rfl
    intro rectangle hrectangle
    rw [hinter rectangle hrectangle]
  rw [hsum]
  exact
    (incidenceParentEdges_card_eq_rectangle_sum
      edges parent coarse).symm

lemma incidenceParentEdges_card_le_support_mul_fiberBound
    {β γ : Type*}
    [DecidableEq β] [DecidableEq γ]
    (rectangles : Finset β)
    (fiber : β → FiniteFunctionFamily)
    (edges : Finset (C2Function × β))
    (hselected :
      edges ⊆ fineFiberIncidenceEdgesOn rectangles fiber)
    (parent : β → γ) (coarse : γ)
    (fiberBound : ℝ)
    (hfiberBound : ∀ rectangle ∈ rectangles,
      ((fiber rectangle).card : ℝ) ≤ fiberBound) :
    ((incidenceParentEdges edges parent coarse).card : ℝ) ≤
      ((incidenceRectangleSupport
        edges parent coarse).card : ℝ) * fiberBound := by
  rw [incidenceParentEdges_card_eq_rectangle_sum]
  have hrectangleSubset :
      incidenceRectangleSupport edges parent coarse ⊆
        rectangles :=
    incidenceRectangleSupport_subset_selected
      rectangles fiber edges hselected parent coarse
  calc
    ((∑ rectangle ∈
        incidenceRectangleSupport edges parent coarse,
          (incidenceRectangleFiber edges rectangle).card : ℕ) : ℝ) =
        ∑ rectangle ∈
          incidenceRectangleSupport edges parent coarse,
            ((incidenceRectangleFiber edges rectangle).card : ℝ) := by
      norm_cast
    _ ≤ ∑ _rectangle ∈
          incidenceRectangleSupport edges parent coarse,
            fiberBound := by
      apply Finset.sum_le_sum
      intro rectangle hrectangle
      have hsubset :
          (incidenceRectangleFiber edges rectangle :
              Set C2Function) ⊆
            (fiber rectangle).carrier := by
        intro function hfunction
        have hfunction' :=
          incidenceRectangleFiber_subset_fiber_on
            rectangles fiber edges hselected rectangle hfunction
        simpa [FiniteFunctionFamily.toFinset] using hfunction'
      have hcard :
          (incidenceRectangleFiber edges rectangle).card ≤
            (fiber rectangle).card := by
        rw [FiniteFunctionFamily.card]
        simpa using
          Set.ncard_le_ncard hsubset (fiber rectangle).finite
      have hcard' :
          ((incidenceRectangleFiber edges rectangle).card : ℝ) ≤
            ((fiber rectangle).card : ℝ) := by
        exact_mod_cast hcard
      exact hcard'.trans
        (hfiberBound rectangle (hrectangleSubset hrectangle))
    _ =
        ((incidenceRectangleSupport
          edges parent coarse).card : ℝ) * fiberBound := by
      simp [Finset.sum_const]

lemma incidenceParentEdges_card_le_rectangleBound_mul_fiberBound
    {β γ : Type*}
    [DecidableEq β] [DecidableEq γ]
    (rectangles : Finset β)
    (fiber : β → FiniteFunctionFamily)
    (edges : Finset (C2Function × β))
    (hselected :
      edges ⊆ fineFiberIncidenceEdgesOn rectangles fiber)
    (parent : β → γ) (coarse : γ)
    (rectangleBound fiberBound : ℝ)
    (hfiberBoundNonneg : 0 ≤ fiberBound)
    (hrectangleBound :
      ((incidenceRectangleSupport
        edges parent coarse).card : ℝ) ≤ rectangleBound)
    (hfiberBound : ∀ rectangle ∈ rectangles,
      ((fiber rectangle).card : ℝ) ≤ fiberBound) :
    ((incidenceParentEdges edges parent coarse).card : ℝ) ≤
      rectangleBound * fiberBound := by
  exact
    (incidenceParentEdges_card_le_support_mul_fiberBound
      rectangles fiber edges hselected parent coarse
      fiberBound hfiberBound).trans
        (mul_le_mul_of_nonneg_right
          hrectangleBound hfiberBoundNonneg)

lemma incidenceParentSupport_subset_parentSupport
    {β γ : Type*}
    [DecidableEq β] [DecidableEq γ]
    (rectangles : Finset β)
    (fiber : β → FiniteFunctionFamily)
    (edges : Finset (C2Function × β))
    (hselected :
      edges ⊆ fineFiberIncidenceEdgesOn rectangles fiber)
    (parent : β → γ) :
    incidenceParentSupport edges parent ⊆
      parentSupport rectangles parent := by
  intro coarse hcoarse
  rcases Finset.mem_image.mp hcoarse with
    ⟨edge, hedge, hedge_parent⟩
  have hedgeFull := hselected hedge
  have hrectangle :
      edge.2 ∈ rectangles :=
    (mem_fineFiberIncidenceEdgesOn
      rectangles fiber edge.1 edge.2).mp hedgeFull |>.1
  exact Finset.mem_image.mpr
    ⟨edge.2, hrectangle, hedge_parent⟩

lemma incidenceRectangleSupport_subset_parentFiber_on
    {β γ : Type*}
    [DecidableEq β] [DecidableEq γ]
    (rectangles : Finset β)
    (fiber : β → FiniteFunctionFamily)
    (edges : Finset (C2Function × β))
    (hselected :
      edges ⊆ fineFiberIncidenceEdgesOn rectangles fiber)
    (parent : β → γ) (coarse : γ) :
    incidenceRectangleSupport edges parent coarse ⊆
      parentFiber rectangles parent coarse := by
  intro rectangle hrectangle
  have hrectangleSelected :
      rectangle ∈ rectangles :=
    incidenceRectangleSupport_subset_selected
      rectangles fiber edges hselected parent coarse
        hrectangle
  rcases Finset.mem_image.mp hrectangle with
    ⟨edge, hedge, hedgeRectangle⟩
  have hparent :
      parent edge.2 = coarse :=
    (Finset.mem_filter.mp hedge).2
  refine Finset.mem_filter.mpr
    ⟨hrectangleSelected, ?_⟩
  rwa [← hedgeRectangle]

lemma incidenceParentSupport_card_mul_lower_le_rectangles_card
    {β γ : Type*}
    [DecidableEq β] [DecidableEq γ]
    (rectangles : Finset β)
    (fiber : β → FiniteFunctionFamily)
    (edges : Finset (C2Function × β))
    (hselected :
      edges ⊆ fineFiberIncidenceEdgesOn rectangles fiber)
    (parent : β → γ) (lower : ℕ)
    (hlower :
      ∀ coarse ∈ incidenceParentSupport edges parent,
        lower ≤ (parentFiber rectangles parent coarse).card) :
    (incidenceParentSupport edges parent).card * lower ≤
      rectangles.card := by
  let active := incidenceParentSupport edges parent
  have hactive :
      active ⊆ parentSupport rectangles parent :=
    incidenceParentSupport_subset_parentSupport
      rectangles fiber edges hselected parent
  have hmaps :
      (rectangles.filter fun rectangle =>
        parent rectangle ∈ active : Set β).MapsTo parent active := by
    intro rectangle hrectangle
    exact (Finset.mem_filter.mp hrectangle).2
  have hpartition :
      (rectangles.filter fun rectangle =>
        parent rectangle ∈ active).card =
        ∑ coarse ∈ active,
          (parentFiber rectangles parent coarse).card := by
    have h :=
      Finset.card_eq_sum_card_fiberwise hmaps
    have hfiber :
        ∀ coarse ∈ active,
          ((rectangles.filter fun rectangle =>
              parent rectangle ∈ active).filter fun rectangle =>
                parent rectangle = coarse) =
            parentFiber rectangles parent coarse := by
      intro coarse hcoarse
      ext rectangle
      simp only [Finset.mem_filter, parentFiber]
      constructor
      · rintro ⟨⟨hrectangle, _⟩, hparent⟩
        exact ⟨hrectangle, hparent⟩
      · rintro ⟨hrectangle, hparent⟩
        refine ⟨⟨hrectangle, ?_⟩, hparent⟩
        rw [hparent]
        exact hcoarse
    rw [h]
    apply Finset.sum_congr rfl
    intro coarse hcoarse
    exact congrArg Finset.card (hfiber coarse hcoarse)
  calc
    active.card * lower =
        ∑ _coarse ∈ active, lower := by
      simp [Finset.sum_const]
    _ ≤ ∑ coarse ∈ active,
          (parentFiber rectangles parent coarse).card :=
      Finset.sum_le_sum fun coarse hcoarse =>
        hlower coarse hcoarse
    _ =
        (rectangles.filter fun rectangle =>
          parent rectangle ∈ active).card :=
      hpartition.symm
    _ ≤ rectangles.card :=
      Finset.card_le_card (Finset.filter_subset _ _)

lemma heavy_parent_numerator_half
    {rectangles rawEdges selectedEdges active rectangleBound
      fiberLower degreeLoss : ℕ}
    (hdegreeLoss : 0 < degreeLoss)
    (hactive :
      active * rectangleBound ≤ 2 * rectangles)
    (hrawLower :
      rectangles * fiberLower ≤ rawEdges)
    (hretention :
      rawEdges ≤ degreeLoss * selectedEdges) :
    (selectedEdges : ℝ) / 2 ≤
      (selectedEdges : ℝ) -
        (active : ℝ) *
          (((rectangleBound : ℝ) * (fiberLower : ℝ)) /
            (4 * (degreeLoss : ℝ))) := by
  have hdegreeLossReal : 0 < (degreeLoss : ℝ) := by
    exact_mod_cast hdegreeLoss
  have hactiveReal :
      (active : ℝ) * (rectangleBound : ℝ) ≤
        2 * (rectangles : ℝ) := by
    exact_mod_cast hactive
  have hrawLowerReal :
      (rectangles : ℝ) * (fiberLower : ℝ) ≤
        (rawEdges : ℝ) := by
    exact_mod_cast hrawLower
  have hretentionReal :
      (rawEdges : ℝ) ≤
        (degreeLoss : ℝ) * (selectedEdges : ℝ) := by
    exact_mod_cast hretention
  have hlight :
      (active : ℝ) *
          (((rectangleBound : ℝ) * (fiberLower : ℝ)) /
            (4 * (degreeLoss : ℝ))) ≤
        (selectedEdges : ℝ) / 2 := by
    have hdenominator : 0 < 4 * (degreeLoss : ℝ) := by
      positivity
    rw [show
      (active : ℝ) *
          (((rectangleBound : ℝ) * (fiberLower : ℝ)) /
            (4 * (degreeLoss : ℝ))) =
        ((active : ℝ) * (rectangleBound : ℝ) *
          (fiberLower : ℝ)) /
            (4 * (degreeLoss : ℝ)) by ring]
    apply (div_le_iff₀ hdenominator).2
    calc
      (active : ℝ) * (rectangleBound : ℝ) *
          (fiberLower : ℝ) =
        ((active : ℝ) * (rectangleBound : ℝ)) *
          (fiberLower : ℝ) := by ring
      _ ≤
          (2 * (rectangles : ℝ)) *
            (fiberLower : ℝ) := by
        gcongr
      _ ≤ 2 * (rawEdges : ℝ) := by
        nlinarith
      _ ≤
          2 * ((degreeLoss : ℝ) *
            (selectedEdges : ℝ)) := by
        gcongr
      _ =
          (selectedEdges : ℝ) / 2 *
            (4 * (degreeLoss : ℝ)) := by
        ring
  linarith

lemma incidence_heavy_parent_selection
    {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [Fintype β]
    (edges : Finset (α × β)) (parent : β → γ)
    (rectangleBound mu₂ logLoss upper : ℝ)
    (hrectangleBound : 0 ≤ rectangleBound)
    (hmu₂ : 0 ≤ mu₂)
    (hlogLoss : 0 < logLoss)
    (hupper : 0 < upper)
    (hrectangle :
      ∀ coarse ∈ incidenceParentSupport edges parent,
        ((incidenceRectangleSupport
          edges parent coarse).card : ℝ) ≤ rectangleBound)
    (hedgeUpper :
      ∀ coarse ∈ incidenceParentSupport edges parent,
        ((incidenceParentEdges
          edges parent coarse).card : ℝ) ≤ upper) :
    let active := incidenceParentSupport edges parent
    let threshold := rectangleBound * mu₂ / logLoss
    let heavy := active.filter fun coarse =>
      threshold ≤
        ((incidenceParentEdges
          edges parent coarse).card : ℝ)
    ((edges.card : ℝ) -
        (active.card : ℝ) * threshold) / upper ≤
          (heavy.card : ℝ) ∧
      ∀ coarse ∈ heavy,
        ((incidenceRectangleSupport
            edges parent coarse).card : ℝ) * mu₂ ≤
          logLoss *
            (incidenceCountOverParent
              edges parent coarse
              (incidenceFunctionSupport
                edges parent coarse) : ℝ) := by
  dsimp only
  let active := incidenceParentSupport edges parent
  let threshold := rectangleBound * mu₂ / logLoss
  let heavy := active.filter fun coarse =>
    threshold ≤
      ((incidenceParentEdges
        edges parent coarse).card : ℝ)
  have hthreshold : 0 ≤ threshold := by
    dsimp only [threshold]
    positivity
  have hsumReal :
      (edges.card : ℝ) =
        ∑ coarse ∈ active,
          ((incidenceParentEdges
            edges parent coarse).card : ℝ) := by
    exact_mod_cast
      (sum_incidenceParentEdges_card edges parent).symm
  have hcardLower :
      ((edges.card : ℝ) -
          (active.card : ℝ) * threshold) / upper ≤
        (heavy.card : ℝ) := by
    apply heavy_card_lower active
      (fun coarse =>
        ((incidenceParentEdges
          edges parent coarse).card : ℝ))
      threshold upper (edges.card : ℝ)
      hthreshold hupper
    · intro coarse hcoarse
      exact hedgeUpper coarse hcoarse
    · rw [hsumReal]
  refine ⟨hcardLower, ?_⟩
  intro coarse hcoarse
  have hcoarseActive : coarse ∈ active :=
    (Finset.mem_filter.mp hcoarse).1
  have hcoarseHeavy :
      threshold ≤
        ((incidenceParentEdges
          edges parent coarse).card : ℝ) :=
    (Finset.mem_filter.mp hcoarse).2
  have hrect := hrectangle coarse hcoarseActive
  have hscaled :
      ((incidenceRectangleSupport
          edges parent coarse).card : ℝ) * mu₂ ≤
        rectangleBound * mu₂ :=
    mul_le_mul_of_nonneg_right hrect hmu₂
  have hthresholdScaled :
      rectangleBound * mu₂ ≤
        logLoss *
          ((incidenceParentEdges
            edges parent coarse).card : ℝ) := by
    have h :=
      mul_le_mul_of_nonneg_left
        hcoarseHeavy hlogLoss.le
    dsimp only [threshold] at h
    have hcancel :
        logLoss * (rectangleBound * mu₂ / logLoss) =
          rectangleBound * mu₂ := by
      field_simp [hlogLoss.ne']
    rw [hcancel] at h
    exact h
  rw [incidenceCountOverParent_support_eq_parentEdges_card]
  exact hscaled.trans hthresholdScaled

lemma incidence_heavy_parent_selection_of_fiber_bound
    {β γ : Type*}
    [Fintype β] [DecidableEq β] [DecidableEq γ]
    (rectangles : Finset β)
    (fiber : β → FiniteFunctionFamily)
    (edges : Finset (C2Function × β))
    (hselected :
      edges ⊆ fineFiberIncidenceEdgesOn rectangles fiber)
    (parent : β → γ)
    (rectangleBound mu₂ logLoss fiberBound : ℝ)
    (hrectangleBound : 0 < rectangleBound)
    (hmu₂ : 0 ≤ mu₂)
    (hlogLoss : 0 < logLoss)
    (hfiberBoundPos : 0 < fiberBound)
    (hrectangle :
      ∀ coarse ∈ incidenceParentSupport edges parent,
        ((incidenceRectangleSupport
          edges parent coarse).card : ℝ) ≤ rectangleBound)
    (hfiberBound : ∀ rectangle ∈ rectangles,
      ((fiber rectangle).card : ℝ) ≤ fiberBound) :
    let active := incidenceParentSupport edges parent
    let threshold := rectangleBound * mu₂ / logLoss
    let upper := rectangleBound * fiberBound
    let heavy := active.filter fun coarse =>
      threshold ≤
        ((incidenceParentEdges
          edges parent coarse).card : ℝ)
    ((edges.card : ℝ) -
        (active.card : ℝ) * threshold) / upper ≤
          (heavy.card : ℝ) ∧
      ∀ coarse ∈ heavy,
        ((incidenceRectangleSupport
            edges parent coarse).card : ℝ) * mu₂ ≤
          logLoss *
            (incidenceCountOverParent
              edges parent coarse
              (incidenceFunctionSupport
                edges parent coarse) : ℝ) := by
  dsimp only
  apply incidence_heavy_parent_selection
    edges parent rectangleBound mu₂ logLoss
      (rectangleBound * fiberBound)
      hrectangleBound.le hmu₂ hlogLoss
      (mul_pos hrectangleBound hfiberBoundPos)
      hrectangle
  intro coarse hcoarse
  exact
    incidenceParentEdges_card_le_rectangleBound_mul_fiberBound
      rectangles fiber edges hselected parent coarse
      rectangleBound fiberBound hfiberBoundPos.le
      (hrectangle coarse hcoarse) hfiberBound

lemma incidence_quantitative_heavy_parent_selection
    {β γ : Type*}
    [Fintype β] [DecidableEq β] [DecidableEq γ]
    (rectangles : Finset β)
    (fiber : β → FiniteFunctionFamily)
    (selectedEdges : Finset (C2Function × β))
    (hselected :
      selectedEdges ⊆
        fineFiberIncidenceEdgesOn rectangles fiber)
    (parent : β → γ)
    (M_parent q_fiber degreeLoss : ℕ)
    (fiberBound : ℝ)
    (hM_parent : 0 < M_parent)
    (hq_fiber : 0 < q_fiber)
    (hdegreeLoss : 0 < degreeLoss)
    (hfiberBoundPos : 0 < fiberBound)
    (hparentRange :
      ∀ coarse ∈ incidenceParentSupport selectedEdges parent,
        M_parent ≤
            (parentFiber rectangles parent coarse).card ∧
          (parentFiber rectangles parent coarse).card <
            2 * M_parent)
    (hfiberLower : ∀ rectangle ∈ rectangles,
      q_fiber ≤ (fiber rectangle).card)
    (hfiberBound : ∀ rectangle ∈ rectangles,
      ((fiber rectangle).card : ℝ) ≤ fiberBound)
    (hretention :
      (fineFiberIncidenceEdgesOn rectangles fiber).card ≤
        degreeLoss * selectedEdges.card)
    (hselectedNonempty : selectedEdges.Nonempty) :
    let active := incidenceParentSupport selectedEdges parent
    let rectangleBound : ℝ := 2 * M_parent
    let mu₂ : ℝ := q_fiber
    let logLoss : ℝ := 4 * degreeLoss
    let upper := rectangleBound * fiberBound
    let threshold := rectangleBound * mu₂ / logLoss
    let heavy := active.filter fun coarse =>
      threshold ≤
        ((incidenceParentEdges
          selectedEdges parent coarse).card : ℝ)
    (((selectedEdges.card : ℝ) / 2) / upper ≤
        (heavy.card : ℝ)) ∧
      heavy.Nonempty ∧
      ∀ coarse ∈ heavy,
        ((incidenceRectangleSupport
            selectedEdges parent coarse).card : ℝ) * mu₂ ≤
          logLoss *
            (incidenceCountOverParent
              selectedEdges parent coarse
              (incidenceFunctionSupport
                selectedEdges parent coarse) : ℝ) := by
  dsimp only
  let active := incidenceParentSupport selectedEdges parent
  let rectangleBound : ℝ := 2 * M_parent
  let mu₂ : ℝ := q_fiber
  let logLoss : ℝ := 4 * degreeLoss
  let upper := rectangleBound * fiberBound
  let threshold := rectangleBound * mu₂ / logLoss
  let heavy := active.filter fun coarse =>
    threshold ≤
      ((incidenceParentEdges
        selectedEdges parent coarse).card : ℝ)
  have hrectangleBound : 0 < rectangleBound := by
    dsimp only [rectangleBound]
    exact_mod_cast (Nat.mul_pos (by omega) hM_parent)
  have hmu₂ : 0 ≤ mu₂ := by
    dsimp only [mu₂]
    positivity
  have hlogLoss : 0 < logLoss := by
    dsimp only [logLoss]
    exact_mod_cast (Nat.mul_pos (by omega) hdegreeLoss)
  have hrectangle :
      ∀ coarse ∈ active,
        ((incidenceRectangleSupport
          selectedEdges parent coarse).card : ℝ) ≤
            rectangleBound := by
    intro coarse hcoarse
    have hsupport :
        incidenceRectangleSupport
            selectedEdges parent coarse ⊆
          parentFiber rectangles parent coarse :=
      incidenceRectangleSupport_subset_parentFiber_on
        rectangles fiber selectedEdges hselected parent coarse
    have hcard :
        (incidenceRectangleSupport
          selectedEdges parent coarse).card ≤
            (parentFiber rectangles parent coarse).card :=
      Finset.card_le_card hsupport
    have hrange := hparentRange coarse hcoarse
    dsimp only [rectangleBound]
    exact_mod_cast hcard.trans (Nat.le_of_lt hrange.2)
  have hactiveLower :
      active.card * M_parent ≤ rectangles.card :=
    incidenceParentSupport_card_mul_lower_le_rectangles_card
      rectangles fiber selectedEdges hselected parent M_parent
      (fun coarse hcoarse => (hparentRange coarse hcoarse).1)
  have hactiveCapacity :
      active.card * (2 * M_parent) ≤
        2 * rectangles.card := by
    calc
      active.card * (2 * M_parent) =
          2 * (active.card * M_parent) := by ring
      _ ≤ 2 * rectangles.card :=
        Nat.mul_le_mul_left 2 hactiveLower
  have hrawLower :
      rectangles.card * q_fiber ≤
        (fineFiberIncidenceEdgesOn rectangles fiber).card :=
    card_mul_le_fineFiberIncidenceEdgesOn
      rectangles fiber q_fiber hfiberLower
  have hnumerator :
      (selectedEdges.card : ℝ) / 2 ≤
        (selectedEdges.card : ℝ) -
          (active.card : ℝ) * threshold := by
    have hmain :=
      heavy_parent_numerator_half
        hdegreeLoss hactiveCapacity hrawLower hretention
    dsimp only [threshold, rectangleBound, mu₂, logLoss]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmain
  rcases incidence_heavy_parent_selection_of_fiber_bound
      rectangles fiber selectedEdges hselected parent
      rectangleBound mu₂ logLoss fiberBound
      hrectangleBound hmu₂ hlogLoss hfiberBoundPos
      hrectangle hfiberBound with
    ⟨hheavy, haggregate⟩
  have hupper : 0 < upper := by
    dsimp only [upper]
    exact mul_pos hrectangleBound hfiberBoundPos
  have hquantitative :
      ((selectedEdges.card : ℝ) / 2) / upper ≤
        (heavy.card : ℝ) := by
    exact
      (div_le_div_of_nonneg_right
        hnumerator hupper.le).trans hheavy
  have hselectedCard :
      0 < (selectedEdges.card : ℝ) := by
    exact_mod_cast hselectedNonempty.card_pos
  have hheavyCard :
      0 < (heavy.card : ℝ) := by
    have hpositive :
        0 < ((selectedEdges.card : ℝ) / 2) / upper := by
      positivity
    exact hpositive.trans_le hquantitative
  have hheavyNonempty : heavy.Nonempty :=
    Finset.card_pos.mp (by exact_mod_cast hheavyCard)
  exact ⟨hquantitative, hheavyNonempty, haggregate⟩

end Kakeya.Cinematic
