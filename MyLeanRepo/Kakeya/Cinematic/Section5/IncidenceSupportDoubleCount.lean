import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceSupportDoubleCountInputs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Build regularized coarse supports and double count incidences

Both sides of the incidence identity count the selected edges below one
coarse parent whose function lies in the tested set.
-/

namespace Kakeya.Cinematic

theorem incidence_support_double_count :
    IncidenceSupportDoubleCountStatement := by
  intro α β γ _ _ _ _ edges parent level h_reg coarse test
  let filtered := edges.filter (fun edge => parent edge.2 = coarse)
  let filteredTest := filtered.filter (fun edge => edge.1 ∈ test)
  let support := incidenceFunctionSupport edges parent coarse
  let rectSupport := incidenceRectangleSupport edges parent coarse

  have hsupport : support = filtered.image Prod.fst := by
    rfl
  have hrectSupport : rectSupport = filtered.image Prod.snd := by
    rfl

  have h1 :
      ∀ function,
        function ∈ support ↔
          0 < incidenceDegree edges parent function coarse := by
    intro function
    have h_mem :
        function ∈ support ↔
          ∃ edge ∈ filtered, edge.1 = function := by
      rw [hsupport, Finset.mem_image]
    have h_card :
        0 < incidenceDegree edges parent function coarse ↔
          (edges.filter fun edge =>
            edge.1 = function ∧
              parent edge.2 = coarse).Nonempty := by
      rw [incidenceDegree, Finset.card_pos]
    rw [h_mem, h_card]
    constructor
    · rintro ⟨edge, hedge, rfl⟩
      rw [Finset.mem_filter] at hedge
      refine ⟨edge, Finset.mem_filter.mpr ⟨hedge.1, ?_⟩⟩
      exact ⟨rfl, hedge.2⟩
    · rintro ⟨edge, hedge⟩
      rw [Finset.mem_filter] at hedge
      exact
        ⟨edge, Finset.mem_filter.mpr ⟨hedge.1, hedge.2.2⟩,
          hedge.2.1⟩

  have h_parent_rect :
      ∀ rectangle ∈ rectSupport, parent rectangle = coarse := by
    intro rectangle hrectangle
    rw [hrectSupport] at hrectangle
    rcases Finset.mem_image.mp hrectangle with ⟨edge, hedge, rfl⟩
    rw [Finset.mem_filter] at hedge
    exact hedge.2

  have h_rect_fiber :
      ∀ rectangle ∈ rectSupport,
        ((incidenceRectangleFiber edges rectangle) ∩ test).card =
          (filteredTest.filter fun edge =>
            edge.2 = rectangle).card := by
    intro rectangle hrectangle
    have hparent : parent rectangle = coarse :=
      h_parent_rect rectangle hrectangle
    have hfilter :
        edges.filter (fun edge => edge.2 = rectangle) =
          filtered.filter (fun edge => edge.2 = rectangle) := by
      ext edge
      simp only [Finset.mem_filter, filtered]
      constructor
      · intro h
        exact ⟨⟨h.1, by rw [h.2]; exact hparent⟩, h.2⟩
      · intro h
        exact ⟨h.1.1, h.2⟩
    have hfiber :
        incidenceRectangleFiber edges rectangle =
          (filtered.filter fun edge =>
            edge.2 = rectangle).image Prod.fst := by
      rw [incidenceRectangleFiber, hfilter]
    rw [hfiber]
    let fiber := filtered.filter fun edge => edge.2 = rectangle
    have hinter :
        fiber.image Prod.fst ∩ test =
          Finset.filter (fun function : α =>
            function ∈ test) (fiber.image Prod.fst) := by
      rfl
    rw [hinter]
    have hfilter_image :
        Finset.filter (fun function : α =>
            function ∈ test) (fiber.image Prod.fst) =
          (fiber.filter fun edge =>
            edge.1 ∈ test).image Prod.fst := by
      rw [Finset.filter_image]
    rw [hfilter_image]
    have hfilter_comm :
        fiber.filter (fun edge => edge.1 ∈ test) =
          filteredTest.filter (fun edge =>
            edge.2 = rectangle) := by
      ext edge
      simp only [Finset.mem_filter, filteredTest, fiber]
      tauto
    rw [hfilter_comm]
    apply Finset.card_image_of_injOn
    intro left hleft right hright hfst
    have hleft' :
        left ∈ filteredTest ∧ left.2 = rectangle := by
      simpa [Finset.mem_filter] using hleft
    have hright' :
        right ∈ filteredTest ∧ right.2 = rectangle := by
      simpa [Finset.mem_filter] using hright
    exact Prod.ext hfst (hleft'.2.trans hright'.2.symm)

  have h_mapsTo :
      Set.MapsTo Prod.snd
        (filteredTest : Set (α × β)) (rectSupport : Set β) := by
    intro edge hedge
    have hedge' : edge ∈ filtered ∧ edge.1 ∈ test := by
      simpa [Finset.mem_filter, filteredTest] using hedge
    rw [hrectSupport]
    exact Finset.mem_image.mpr ⟨edge, hedge'.1, rfl⟩

  have h_lhs :
      incidenceCountOverParent edges parent coarse test =
        filteredTest.card := by
    rw [incidenceCountOverParent]
    have hsum :
        ∑ rectangle ∈ rectSupport,
            ((incidenceRectangleFiber edges rectangle) ∩ test).card =
          ∑ rectangle ∈ rectSupport,
            (filteredTest.filter fun edge =>
              edge.2 = rectangle).card := by
      apply Finset.sum_congr rfl
      intro rectangle hrectangle
      exact h_rect_fiber rectangle hrectangle
    rw [hsum]
    exact (Finset.card_eq_sum_card_fiberwise
      (H := h_mapsTo)).symm

  have h_support_inter :
      support ∩ test = filteredTest.image Prod.fst := by
    have hinter :
        support ∩ test =
          Finset.filter (fun function : α =>
            function ∈ test) support := by
      rfl
    rw [hinter, hsupport]
    rw [Finset.filter_image]

  have h_degree_fiber :
      ∀ function ∈ filteredTest.image Prod.fst,
        incidenceDegree edges parent function coarse =
          (filteredTest.filter fun edge =>
            edge.1 = function).card := by
    intro function hfunction
    rcases Finset.mem_image.mp hfunction with
      ⟨edge, hedge, hfunction_eq⟩
    rw [Finset.mem_filter] at hedge
    have hfunction_test : function ∈ test := by
      rw [← hfunction_eq]
      exact hedge.2
    have hfilter :
        edges.filter (fun edge =>
            edge.1 = function ∧ parent edge.2 = coarse) =
          filtered.filter (fun edge =>
            edge.1 = function) := by
      ext edge
      simp only [Finset.mem_filter, filtered]
      constructor <;> intro h <;> tauto
    have hfilter_test :
        filtered.filter (fun edge => edge.1 = function) =
          filteredTest.filter (fun edge =>
            edge.1 = function) := by
      ext edge
      simp only [Finset.mem_filter, filteredTest]
      constructor
      · intro h
        have hedge_test : edge.1 ∈ test := by
          rw [h.2]
          exact hfunction_test
        exact ⟨⟨h.1, hedge_test⟩, h.2⟩
      · intro h
        exact ⟨h.1.1, h.2⟩
    rw [incidenceDegree, hfilter, hfilter_test]

  have h_rhs :
      (support ∩ test).sum
          (fun function =>
            incidenceDegree edges parent function coarse) =
        filteredTest.card := by
    rw [h_support_inter]
    have hsum :
        ∑ function ∈ filteredTest.image Prod.fst,
            incidenceDegree edges parent function coarse =
          ∑ function ∈ filteredTest.image Prod.fst,
            (filteredTest.filter fun edge =>
              edge.1 = function).card := by
      apply Finset.sum_congr rfl
      intro function hfunction
      exact h_degree_fiber function hfunction
    rw [hsum]
    exact
      (Finset.card_eq_sum_card_image Prod.fst filteredTest).symm

  have h2 :
      incidenceCountOverParent edges parent coarse test =
        (support ∩ test).sum
          (fun function =>
            incidenceDegree edges parent function coarse) := by
    rw [h_lhs, h_rhs]

  have h3 :
      2 ^ level * (support ∩ test).card ≤
        incidenceCountOverParent edges parent coarse test := by
    rw [h2]
    have hlower :
        ∀ function ∈ support ∩ test,
          2 ^ level ≤
            incidenceDegree edges parent function coarse := by
      intro function hfunction
      have hpositive :
          0 < incidenceDegree edges parent function coarse :=
        (h1 function).mp (Finset.mem_inter.mp hfunction).1
      rcases h_reg function coarse with hzero | hrange
      · rw [hzero] at hpositive
        contradiction
      · exact hrange.1
    have hsum :
        (support ∩ test).card • (2 ^ level) ≤
          ∑ function ∈ support ∩ test,
            incidenceDegree edges parent function coarse :=
      Finset.card_nsmul_le_sum
        (support ∩ test)
        (fun function =>
          incidenceDegree edges parent function coarse)
        (2 ^ level) hlower
    simpa [Nat.nsmul_eq_mul, mul_comm] using hsum

  have h4 :
      ∀ bound : ℕ,
        (∀ rectangle ∈ rectSupport,
          ((incidenceRectangleFiber edges rectangle) ∩ test).card ≤
            bound) →
        incidenceCountOverParent edges parent coarse test ≤
          rectSupport.card * bound := by
    intro bound hbound
    rw [incidenceCountOverParent]
    have hsum :
        ∑ rectangle ∈ rectSupport,
            ((incidenceRectangleFiber edges rectangle) ∩ test).card ≤
          rectSupport.card • bound :=
      Finset.sum_le_card_nsmul rectSupport
        (fun rectangle =>
          ((incidenceRectangleFiber edges rectangle) ∩ test).card)
        bound hbound
    simpa [Nat.nsmul_eq_mul, mul_comm] using hsum

  exact ⟨h1, h2, h3, h4⟩

end Kakeya.Cinematic
