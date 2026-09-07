import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceCoarseFiberNonconcentrationAtInputs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Selected-incidence nonconcentration at one fixed ball scale

This is the fixed-ball specialization of `incidence_coarse_fiber_nonconcentration`.
The center and radius are fixed throughout rather than universally quantified,
which avoids the false strict nonconcentration claim at arbitrarily large radii.
-/

namespace Kakeya.Cinematic

theorem incidence_coarse_fiber_nonconcentration_at :
    IncidenceCoarseFiberNonconcentrationAtStatement := by
  intro β γ _ _ _ hDoubleCount edges parent level hReg coarse hRectNonempty
  intro testCenter radius mu₁ mu₂ coefficient logLoss hMu2Pos hCoeffNonneg
    hLogLossOne hMu1Le hAggregate hBallUpper

  classical
  let rectSupport := incidenceRectangleSupport edges parent coarse
  let funcSupport := incidenceFunctionSupport edges parent coarse
  let M : ℕ := rectSupport.card
  let q : ℕ := 2 ^ level
  let H : FiniteFunctionFamily := incidenceSupportFamily edges parent coarse
  let G : Fin M → FiniteFunctionFamily :=
    incidenceActiveFiberFamily edges parent coarse

  have hq_pos : 0 < q := by positivity

  have hH_card : H.card = funcSupport.card := by
    simp [FiniteFunctionFamily.card, H, incidenceSupportFamily]
    <;> rfl

  have hCarrier : ∀ i : Fin M, (G i).carrier ⊆ H.carrier := by
    intro i
    let rect := incidenceActiveRectangle edges parent coarse i
    have hRectMem : rect ∈ rectSupport :=
      ((Finset.equivFin rectSupport).symm i).property
    intro f hf
    have h_f_in_fiber : f ∈ incidenceRectangleFiber edges rect := by
      exact_mod_cast hf
    rcases Finset.mem_image.mp h_f_in_fiber with ⟨edge, hedge, rfl⟩
    have hEdgeInEdges : edge ∈ edges := (Finset.mem_filter.mp hedge).1
    have hEdgeSnd : edge.2 = rect := (Finset.mem_filter.mp hedge).2
    have hParentRect : parent rect = coarse := by
      rcases Finset.mem_image.mp hRectMem with ⟨edge', hedge', h_eq⟩
      have h : parent edge'.2 = coarse := (Finset.mem_filter.mp hedge').2
      rw [h_eq] at h
      exact h
    have hFiltered : edge ∈ edges.filter (fun e => parent e.2 = coarse) := by
      rw [Finset.mem_filter]
      exact ⟨hEdgeInEdges, by rw [hEdgeSnd]; exact hParentRect⟩
    exact Finset.mem_image.mpr ⟨edge, hFiltered, rfl⟩

  have hDC_support := hDoubleCount edges parent level hReg coarse funcSupport
  rcases hDC_support with ⟨h1, h2, _, _⟩

  have hDegreeUpper :
      ∀ f ∈ funcSupport, incidenceDegree edges parent f coarse < 2 * q := by
    intro f hf
    have hPos : 0 < incidenceDegree edges parent f coarse := (h1 f).mp hf
    rcases hReg f coarse with hzero | hrange
    · rw [hzero] at hPos
      contradiction
    · have h :
          incidenceDegree edges parent f coarse < 2 ^ (level + 1) :=
        hrange.2
      have h' : 2 ^ (level + 1) = 2 * q := by
        simp [q, pow_succ] <;> ring
      rw [h'] at h
      exact h

  have hSumUpper :
      incidenceCountOverParent edges parent coarse funcSupport ≤
        (2 * q) * funcSupport.card := by
    rw [h2]
    have h_inter : funcSupport ∩ funcSupport = funcSupport := by simp
    rw [h_inter]
    have h :
        ∑ f ∈ funcSupport, incidenceDegree edges parent f coarse ≤
          ∑ f ∈ funcSupport, (2 * q) := by
      apply Finset.sum_le_sum
      intro f hf
      exact Nat.le_of_lt (hDegreeUpper f hf)
    simpa [Finset.sum_const, mul_comm] using h

  have hAggregateUpper :
      (M : ℝ) * mu₂ ≤ (2 * logLoss) * (q : ℝ) * (H.card : ℝ) := by
    have h' :
        (incidenceCountOverParent edges parent coarse funcSupport : ℝ) ≤
          ((2 * q) * funcSupport.card : ℝ) := by
      exact_mod_cast hSumUpper
    have hH_card' : (H.card : ℝ) = (funcSupport.card : ℝ) := by
      exact_mod_cast hH_card
    calc
      (M : ℝ) * mu₂ ≤
          logLoss *
            (incidenceCountOverParent edges parent coarse funcSupport : ℝ) :=
        hAggregate
      _ ≤ logLoss * (((2 * q) * funcSupport.card : ℝ)) := by gcongr
      _ = (2 * logLoss) * (q : ℝ) * (H.card : ℝ) := by
        rw [hH_card']
        ring

  let ballSet : Set C2Function := c2Ball testCenter radius
  let testSet : Set C2Function := H.carrier ∩ ballSet
  have hTestSetFinite : testSet.Finite := H.finite.inter_of_left _
  let test : Finset C2Function := hTestSetFinite.toFinset

  have hTestCard : test.card = testSet.ncard := by
    simp [test, Set.Finite.toFinset]

  have h_coe_test : (test : Set C2Function) = testSet := by
    simp [test, Set.Finite.toFinset]

  have hTestSubFunc :
      (test : Set C2Function) ⊆ (funcSupport : Set C2Function) := by
    intro x hx
    have h : x ∈ testSet := by
      rw [← h_coe_test]
      exact hx
    exact h.1

  have hDC_test := hDoubleCount edges parent level hReg coarse test
  rcases hDC_test with ⟨_, _, h3_test, _⟩

  have hInterTest : funcSupport ∩ test = test := by
    rw [Finset.inter_eq_right.mpr hTestSubFunc]

  have hLowerNat :
      q * test.card ≤ incidenceCountOverParent edges parent coarse test := by
    rw [hInterTest] at h3_test
    exact h3_test

  have h_eq1 : ∀ (i : Fin M),
      ((incidenceRectangleFiber edges
            (incidenceActiveRectangle edges parent coarse i)) ∩
          test).card =
        ((G i).carrier ∩ ballSet).ncard := by
    intro i
    let rect := incidenceActiveRectangle edges parent coarse i
    let s : Finset C2Function := incidenceRectangleFiber edges rect ∩ test
    have hContain : (G i).carrier ⊆ H.carrier := hCarrier i
    have h_coe : (s : Set C2Function) = (G i).carrier ∩ ballSet := by
      ext x
      simp only [s, Finset.mem_coe, Finset.mem_inter, Set.mem_inter_iff]
      constructor
      · rintro ⟨hx1, hx2⟩
        have h_x_in_carrier : x ∈ (G i).carrier := by exact_mod_cast hx1
        have h_x_in_coe : x ∈ (test : Set C2Function) := hx2
        have h_x_in_testSet : x ∈ testSet := by
          rw [h_coe_test] at h_x_in_coe
          exact h_x_in_coe
        exact ⟨h_x_in_carrier, h_x_in_testSet.2⟩
      · rintro ⟨h_x_in_carrier, h_x_in_ball⟩
        have h_x_in_H : x ∈ H.carrier := hContain h_x_in_carrier
        have h_x_in_testSet : x ∈ testSet := ⟨h_x_in_H, h_x_in_ball⟩
        have h_x_in_coe : x ∈ (test : Set C2Function) := by
          rw [h_coe_test]
          exact h_x_in_testSet
        exact ⟨by exact_mod_cast h_x_in_carrier, h_x_in_coe⟩
    have h_ncard : (s : Set C2Function).ncard = s.card := by
      have h9 : (s : Set C2Function).toFinset = s := by
        ext y
        simp
      have h10 :
          (s : Set C2Function).ncard =
            (s : Set C2Function).toFinset.card := by
        simp [Set.ncard]
      rw [h10, h9]
    rw [← h_ncard, h_coe]

  have h_sum :
      ∑ rect ∈ rectSupport,
          ((incidenceRectangleFiber edges rect) ∩ test).card =
        ∑ i : Fin M,
          ((incidenceRectangleFiber edges
              (incidenceActiveRectangle edges parent coarse i)) ∩
            test).card := by
    let g : β → ℕ :=
      fun rect => (incidenceRectangleFiber edges rect ∩ test).card
    have h_attach :
        ∑ x ∈ rectSupport.attach, g x.val =
          ∑ rect ∈ rectSupport, g rect := by
      rw [Finset.sum_attach]
    have h_univ :
        ∑ x : {x // x ∈ rectSupport}, g x.val =
          ∑ x ∈ rectSupport.attach, g x.val := by
      have h7 : rectSupport.attach = Finset.univ := by
        simp [Finset.attach]
      rw [h7]
    have h1 :
        ∑ rect ∈ rectSupport, g rect =
          ∑ x : {x // x ∈ rectSupport}, g x.val := by
      rw [← h_attach, ← h_univ]
    have h2 :
        ∑ x : {x // x ∈ rectSupport}, g x.val =
          ∑ i : Fin M,
            g (incidenceActiveRectangle edges parent coarse i) := by
      let e : {x // x ∈ rectSupport} ≃ Fin M :=
        Finset.equivFin rectSupport
      let f : {x // x ∈ rectSupport} → ℕ := fun x => g x.val
      let g' : Fin M → ℕ :=
        fun i => g (incidenceActiveRectangle edges parent coarse i)
      have h_eq : ∀ (x : {x // x ∈ rectSupport}), f x = g' (e x) := by
        intro x
        have h6 : e.symm (e x) = x := e.left_inv x
        have h7 :
            incidenceActiveRectangle edges parent coarse (e x) = x.val := by
          unfold incidenceActiveRectangle
          exact congr_arg Subtype.val h6
        simp [g', f, h7]
      exact Fintype.sum_equiv e f g' h_eq
    simpa [g] using h1.trans h2

  have h_nat :
      q * test.card ≤
        ∑ i : Fin M, ((G i).carrier ∩ ballSet).ncard := by
    have h1 :
        q * test.card ≤ incidenceCountOverParent edges parent coarse test :=
      hLowerNat
    have h2 :
        incidenceCountOverParent edges parent coarse test =
          ∑ i : Fin M, ((G i).carrier ∩ ballSet).ncard := by
      calc
        incidenceCountOverParent edges parent coarse test =
            ∑ rect ∈ rectSupport,
              ((incidenceRectangleFiber edges rect) ∩ test).card := by
          rfl
        _ = ∑ i : Fin M,
              ((incidenceRectangleFiber edges
                  (incidenceActiveRectangle edges parent coarse i)) ∩
                test).card :=
          h_sum
        _ = ∑ i : Fin M, ((G i).carrier ∩ ballSet).ncard := by
          apply Finset.sum_congr rfl
          intro i _
          exact h_eq1 i
    rw [h2] at h1
    exact h1

  have hLower :
      (q : ℝ) * ((H.carrier ∩ ballSet).ncard : ℝ) ≤
        ∑ i : Fin M, (((G i).carrier ∩ ballSet).ncard : ℝ) := by
    have h_test : test.card = (H.carrier ∩ ballSet).ncard := hTestCard
    have h_nat' :
        q * (H.carrier ∩ ballSet).ncard ≤
          ∑ i : Fin M, ((G i).carrier ∩ ballSet).ncard := by
      rw [← h_test]
      exact h_nat
    exact_mod_cast h_nat'

  have hUpper :
      (∑ i : Fin M, (((G i).carrier ∩ ballSet).ncard : ℝ)) ≤
        (M : ℝ) * mu₁ := by
    have h_each : ∀ i : Fin M,
        (((G i).carrier ∩ ballSet).ncard : ℝ) ≤ mu₁ := by
      intro i
      let rect := incidenceActiveRectangle edges parent coarse i
      have hRectMem : rect ∈ rectSupport :=
        ((Finset.equivFin rectSupport).symm i).property
      exact hBallUpper rect hRectMem
    calc
      ∑ i : Fin M, (((G i).carrier ∩ ballSet).ncard : ℝ) ≤
          ∑ i : Fin M, mu₁ :=
        Finset.sum_le_sum (fun i _ => h_each i)
      _ = (M : ℝ) * mu₁ := by
        simp [Finset.sum_const, mul_comm]

  have hq_real : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have hcount :
      (q : ℝ) * ((H.carrier ∩ ballSet).ncard : ℝ) ≤
        (q : ℝ) * ((2 * logLoss) * coefficient * (H.card : ℝ)) := by
    calc
      (q : ℝ) * ((H.carrier ∩ ballSet).ncard : ℝ) ≤
          ∑ i : Fin M, (((G i).carrier ∩ ballSet).ncard : ℝ) :=
        hLower
      _ ≤ (M : ℝ) * mu₁ := hUpper
      _ ≤ (M : ℝ) * (coefficient * mu₂) :=
        mul_le_mul_of_nonneg_left hMu1Le (by positivity)
      _ = coefficient * ((M : ℝ) * mu₂) := by ring
      _ ≤ coefficient * ((2 * logLoss) * (q : ℝ) * (H.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hAggregateUpper hCoeffNonneg
      _ = (q : ℝ) * ((2 * logLoss) * coefficient * (H.card : ℝ)) := by
        ring
  exact le_of_mul_le_mul_left hcount hq_real

end Kakeya.Cinematic
