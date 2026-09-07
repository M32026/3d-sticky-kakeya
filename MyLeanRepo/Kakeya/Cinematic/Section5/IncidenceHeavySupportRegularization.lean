import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseSupportCardinalityRegularization
import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceCoarseFiberNonconcentration
import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceParentMass

/-!
# Regularize heavy coarse incidence supports

This module applies the aggregate Lemma 47 bridge on a finite heavy-parent
family, then performs the final dyadic support-cardinality regularization.
-/

noncomputable section

namespace Kakeya.Cinematic

attribute [local instance] Classical.decEq

lemma incidenceFunctionSupport_nonempty_of_mem_parentSupport
    {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (edges : Finset (α × β)) (parent : β → γ)
    (coarse : γ)
    (hcoarse : coarse ∈ incidenceParentSupport edges parent) :
    (incidenceFunctionSupport edges parent coarse).Nonempty := by
  rcases Finset.mem_image.mp hcoarse with
    ⟨edge, hedge, hedgeParent⟩
  refine ⟨edge.1, Finset.mem_image.mpr ?_⟩
  exact
    ⟨edge, Finset.mem_filter.mpr
      ⟨hedge, hedgeParent⟩, rfl⟩

lemma incidenceRectangleSupport_nonempty_of_mem_parentSupport
    {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (edges : Finset (α × β)) (parent : β → γ)
    (coarse : γ)
    (hcoarse : coarse ∈ incidenceParentSupport edges parent) :
    (incidenceRectangleSupport edges parent coarse).Nonempty := by
  rcases Finset.mem_image.mp hcoarse with
    ⟨edge, hedge, hedgeParent⟩
  refine ⟨edge.2, Finset.mem_image.mpr ?_⟩
  exact
    ⟨edge, Finset.mem_filter.mpr
      ⟨hedge, hedgeParent⟩, rfl⟩

lemma incidence_nonconcentration_on_parents
    {β γ : Type*}
    [Fintype β] [DecidableEq β] [DecidableEq γ]
    (hNonconcentration : CoarseFiberNonconcentrationStatement)
    (edges : Finset (C2Function × β)) (parent : β → γ)
    (level : ℕ)
    (hRegular :
      ∀ function coarse,
        incidenceDegree edges parent function coarse = 0 ∨
          (2 ^ level ≤
              incidenceDegree edges parent function coarse ∧
            incidenceDegree edges parent function coarse <
              2 ^ (level + 1)))
    (parents : Finset γ)
    (hparents :
      parents ⊆ incidenceParentSupport edges parent)
    {mu₁ mu₂ coefficient logLoss : ℝ}
    (hmu₂ : 0 < mu₂)
    (hcoefficient : 0 ≤ coefficient)
    (hlogLoss : 1 ≤ logLoss)
    (hmu₁ : mu₁ ≤ coefficient * mu₂)
    (hAggregate :
      ∀ coarse ∈ parents,
        ((incidenceRectangleSupport
            edges parent coarse).card : ℝ) * mu₂ ≤
          logLoss *
            (incidenceCountOverParent
              edges parent coarse
              (incidenceFunctionSupport
                edges parent coarse) : ℝ))
    (hBallUpper :
      ∀ coarse ∈ parents,
        ∀ rectangle ∈
            incidenceRectangleSupport edges parent coarse,
          ∀ center radius,
            (((incidenceRectangleFiber edges rectangle :
                  Set C2Function) ∩
                c2Ball center radius).ncard : ℝ) ≤ mu₁) :
    ∀ coarse ∈ parents, ∀ center radius,
      (((incidenceSupportFamily
            edges parent coarse).carrier ∩
          c2Ball center radius).ncard : ℝ) ≤
        (2 * logLoss) * coefficient *
          ((incidenceSupportFamily
            edges parent coarse).card : ℝ) := by
  intro coarse hcoarse center radius
  apply incidence_coarse_fiber_nonconcentration
    incidence_support_double_count hNonconcentration
      edges parent level hRegular coarse
  · exact
      incidenceRectangleSupport_nonempty_of_mem_parentSupport
        edges parent coarse (hparents hcoarse)
  · exact hmu₂
  · exact hcoefficient
  · exact hlogLoss
  · exact hmu₁
  · exact hAggregate coarse hcoarse
  · exact hBallUpper coarse hcoarse

lemma regularize_heavy_incidence_supports
    {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (ambient : Finset C2Function)
    (edges : Finset (C2Function × β))
    (parent : β → γ)
    (heavy : Finset γ)
    (hheavy : heavy.Nonempty)
    (hheavyParent :
      heavy ⊆ incidenceParentSupport edges parent)
    (hsupportAmbient :
      ∀ coarse ∈ heavy,
        incidenceFunctionSupport edges parent coarse ⊆
          ambient) :
    ∃ (level : ℕ) (selected : Finset γ),
      level ≤ Nat.log2 ambient.card ∧
      selected.Nonempty ∧
      selected =
        heavy.filter (fun coarse =>
          2 ^ level ≤
              (incidenceFunctionSupport
                edges parent coarse).card ∧
            (incidenceFunctionSupport
              edges parent coarse).card <
                2 ^ (level + 1)) ∧
      heavy.card ≤
        (Nat.log2 ambient.card + 1) * selected.card ∧
      selected ⊆ heavy ∧
      ∀ coarse ∈ selected,
        2 ^ level ≤
            (incidenceFunctionSupport
              edges parent coarse).card ∧
          (incidenceFunctionSupport
            edges parent coarse).card <
              2 ^ (level + 1) := by
  rcases coarse_support_cardinality_regularization
      ambient heavy
      (fun coarse =>
        incidenceFunctionSupport edges parent coarse)
      hheavy
      (fun coarse hcoarse =>
        incidenceFunctionSupport_nonempty_of_mem_parentSupport
          edges parent coarse (hheavyParent hcoarse))
      hsupportAmbient with
    ⟨level, selected, hlevel, hselected,
      hselectedEq, hretention, hrange⟩
  have hselectedSub : selected ⊆ heavy := by
    intro coarse hcoarse
    rw [hselectedEq] at hcoarse
    exact (Finset.mem_filter.mp hcoarse).1
  exact
    ⟨level, selected, hlevel, hselected,
      hselectedEq, hretention, hselectedSub, hrange⟩

lemma regularize_heavy_incidence_supports_with_nonconcentration
    {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (ambient : Finset C2Function)
    (edges : Finset (C2Function × β))
    (parent : β → γ)
    (heavy : Finset γ)
    (hheavy : heavy.Nonempty)
    (hheavyParent :
      heavy ⊆ incidenceParentSupport edges parent)
    (hsupportAmbient :
      ∀ coarse ∈ heavy,
        incidenceFunctionSupport edges parent coarse ⊆
          ambient)
    (factor : ℝ)
    (hNonconcentration :
      ∀ coarse ∈ heavy, ∀ center radius,
        (((incidenceSupportFamily
              edges parent coarse).carrier ∩
            c2Ball center radius).ncard : ℝ) ≤
          factor *
            ((incidenceSupportFamily
              edges parent coarse).card : ℝ)) :
    ∃ (level : ℕ) (selected : Finset γ),
      level ≤ Nat.log2 ambient.card ∧
      selected.Nonempty ∧
      selected =
        heavy.filter (fun coarse =>
          2 ^ level ≤
              (incidenceFunctionSupport
                edges parent coarse).card ∧
            (incidenceFunctionSupport
              edges parent coarse).card <
                2 ^ (level + 1)) ∧
      heavy.card ≤
        (Nat.log2 ambient.card + 1) * selected.card ∧
      selected ⊆ heavy ∧
      (∀ coarse ∈ selected,
        2 ^ level ≤
            (incidenceFunctionSupport
              edges parent coarse).card ∧
          (incidenceFunctionSupport
            edges parent coarse).card <
              2 ^ (level + 1)) ∧
      ∀ coarse ∈ selected, ∀ center radius,
        (((incidenceSupportFamily
              edges parent coarse).carrier ∩
            c2Ball center radius).ncard : ℝ) ≤
          factor *
            ((incidenceSupportFamily
              edges parent coarse).card : ℝ) := by
  rcases regularize_heavy_incidence_supports
      ambient edges parent heavy hheavy
      hheavyParent hsupportAmbient with
    ⟨level, selected, hlevel, hselected,
      hselectedEq, hretention, hselectedSub, hrange⟩
  refine
    ⟨level, selected, hlevel, hselected,
      hselectedEq, hretention, hselectedSub, hrange, ?_⟩
  intro coarse hcoarse
  exact hNonconcentration coarse (hselectedSub hcoarse)

end Kakeya.Cinematic
