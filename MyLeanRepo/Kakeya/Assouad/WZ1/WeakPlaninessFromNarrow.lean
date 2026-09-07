import MyLeanRepo.Kakeya.Assouad.WZ1.CrossNormal
import MyLeanRepo.Kakeya.Assouad.WZ1.CombinatorialPigeonhole
import MyLeanRepo.Kakeya.Assouad.WZ1.GoodPairMeasurable
import MyLeanRepo.Kakeya.Assouad.WZ1.InnerCrossTriple
import MyLeanRepo.Kakeya.Assouad.WZ1.MassLowerFromMultiplicity
import MyLeanRepo.Kakeya.Assouad.WZ1.SelectedCarrierMeasurable

/-!
# WZ1 weak planiness

Closed proof of WZ1 Lemma 11: select one measurable transverse active pair at
each counted-narrow point, retain the many narrow third directions, and use
the normalized cross product as the weak plane map.
-/

namespace Kakeya.Assouad

open MeasureTheory Finset

theorem wz1_weak_planiness_from_narrow :
    WZ1WeakPlaninessFromNarrowStatement := by
  intro delta kappa tau Q R hkappa F hF Y narrow hclose hmult
  classical
  let Z := narrow.shading
  have hGoodPair : ∀ p : Point3, p ∈ Z.union →
      ∃ i j : Fin F.card,
        p ∈ Z.carrier i ∧
        p ∈ Z.carrier j ∧
        kappa ≤
          ‖wz1Cross
            (F.tube i).direction
            (F.tube j).direction‖ ∧
        Z.pointMultiplicity p ≤
          4 * wz1GoodThirdCount Z p i j tau := by
    intro p hp
    let A : Finset (Fin F.card) :=
      Finset.univ.filter fun i => p ∈ Z.carrier i
    have hAcard : A.card = Z.pointMultiplicity p := by
      simp [A, Kakeya.Streamlined.Shading.pointMultiplicity]
      rfl
    let Broad : Fin F.card → Fin F.card → Fin F.card → Prop :=
      fun i j k =>
        tau ≤
          |wz1TripleProduct
            (F.tube i).direction
            (F.tube j).direction
            (F.tube k).direction|
    let Close : Fin F.card → Fin F.card → Prop :=
      fun i j =>
        ‖wz1Cross
          (F.tube i).direction
          (F.tube j).direction‖ < kappa
    have hBroad :
        ((A.product (A.product A)).filter
          (fun x : Fin F.card × (Fin F.card × Fin F.card) =>
            Broad x.1 x.2.1 x.2.2)).card < Q := by
      let S :=
        (A.product (A.product A)).filter
          (fun x : Fin F.card × (Fin F.card × Fin F.card) =>
            Broad x.1 x.2.1 x.2.2)
      let T :=
        (Finset.univ.product
          (Finset.univ.product Finset.univ)).filter
            (fun x : Fin F.card × (Fin F.card × Fin F.card) =>
              p ∈ Z.carrier x.1 ∧
              p ∈ Z.carrier x.2.1 ∧
              p ∈ Z.carrier x.2.2 ∧
              Broad x.1 x.2.1 x.2.2)
      have hST : S = T := by
        apply Finset.ext
        intro x
        have hAmem : ∀ i : Fin F.card, i ∈ A ↔ p ∈ Z.carrier i := by
          intro i
          simp [A, Finset.mem_filter]
        simp [S, T, Broad, Finset.mem_filter, Finset.mem_product,
          Finset.mem_univ, hAmem]
        tauto
      have h1 : S.card = T.card := by rw [hST]
      have h2 : T.card = wz1LargeTripleCount Z p tau := by rfl
      rw [h1, h2]
      exact narrow.large_triple_count_lt p hp
    have hClose :
        ∀ i ∈ A, (A.filter fun j => Close i j).card < R := by
      intro i hi
      have hi' : p ∈ Z.carrier i := by
        simpa [A, Finset.mem_filter] using hi
      have hEq :
          (A.filter fun j => Close i j).card =
            wz1CloseDirectionCount Z p i kappa := by
        simp [Close, A, wz1CloseDirectionCount, Finset.filter_filter]
        congr
      rw [hEq]
      exact hclose p hp i hi'
    have hMain :
        4 * (Q + 3 * R * A.card ^ 2) ≤ 3 * A.card ^ 3 := by
      rw [hAcard]
      exact hmult p hp
    rcases
        combinatorial_pigeonhole
          A Broad Close Q R hBroad hClose hMain with
      ⟨i, hi, j, hj, hNotClose, hCount⟩
    have hi' : p ∈ Z.carrier i := by
      simpa [A, Finset.mem_filter] using hi
    have hj' : p ∈ Z.carrier j := by
      simpa [A, Finset.mem_filter] using hj
    have hTransverse :
        kappa ≤
          ‖wz1Cross
            (F.tube i).direction
            (F.tube j).direction‖ :=
      Std.not_lt.mp hNotClose
    let good := A.filter fun k =>
      ¬Broad i j k ∧
      ¬Close i j ∧
      ¬Close i k ∧
      ¬Close j k
    have hSubset :
        good ⊆
          A.filter fun k =>
            |wz1TripleProduct
              (F.tube i).direction
              (F.tube j).direction
              (F.tube k).direction| < tau := by
      intro k hk
      have hFilter :
          ¬Broad i j k ∧
          ¬Close i j ∧
          ¬Close i k ∧
          ¬Close j k :=
        (Finset.mem_filter.mp hk).2
      have hkA : k ∈ A := (Finset.mem_filter.mp hk).1
      have hNarrow : ¬Broad i j k := hFilter.1
      simp only [Broad, not_le] at hNarrow
      exact Finset.mem_filter.mpr ⟨hkA, hNarrow⟩
    have hCount2 :
        good.card ≤
          (A.filter fun k =>
            |wz1TripleProduct
              (F.tube i).direction
              (F.tube j).direction
              (F.tube k).direction| < tau).card :=
      Finset.card_le_card hSubset
    have hGoodThird :
        (A.filter fun k =>
          |wz1TripleProduct
            (F.tube i).direction
            (F.tube j).direction
            (F.tube k).direction| < tau).card =
          wz1GoodThirdCount Z p i j tau := by
      simp [wz1GoodThirdCount, A, Finset.filter_filter]
      congr
    have hFinal :
        Z.pointMultiplicity p ≤
          4 * wz1GoodThirdCount Z p i j tau := by
      rw [hAcard] at *
      rw [← hGoodThird]
      exact
        hCount.trans
          (mul_le_mul_of_nonneg_left hCount2 (by norm_num))
    exact ⟨i, j, hi', hj', hTransverse, hFinal⟩

  let N : ℕ := Fintype.card (Fin F.card × Fin F.card)
  have hN : 0 < N := by
    have h1 : N = F.card * F.card := by
      simp [N, Fintype.card_prod]
    rw [h1]
    exact mul_pos hF hF
  let defaultIndex : Fin N := ⟨0, hN⟩
  let equivPair : Fin F.card × Fin F.card ≃ Fin N :=
    Fintype.equivFin (Fin F.card × Fin F.card)
  let Qualifies (p : Point3) (ij : Fin F.card × Fin F.card) : Prop :=
    p ∈ Z.carrier ij.1 ∧
    p ∈ Z.carrier ij.2 ∧
    kappa ≤
      ‖wz1Cross
        (F.tube ij.1).direction
        (F.tube ij.2).direction‖ ∧
    Z.pointMultiplicity p ≤
      4 * wz1GoodThirdCount Z p ij.1 ij.2 tau
  let P : Point3 → Fin N → Prop := fun p n =>
    (p ∈ Z.union ∧ Qualifies p (equivPair.symm n)) ∨
      (p ∉ Z.union ∧ n = defaultIndex)
  have hPmeas : ∀ n : Fin N, MeasurableSet {p : Point3 | P p n} := by
    intro n
    have h1 :
        MeasurableSet
          {p : Point3 |
            p ∈ Z.union ∧ Qualifies p (equivPair.symm n)} :=
      (measurableSet_shading_union Z).inter
        (wz1GoodPairPredicate_measurable (equivPair.symm n))
    by_cases hn : n = defaultIndex
    · subst hn
      have hSet :
          {p : Point3 | P p defaultIndex} =
            {p : Point3 |
              p ∈ Z.union ∧
                Qualifies p (equivPair.symm defaultIndex)} ∪
              Z.unionᶜ := by
        ext p
        simp [P, Qualifies]
        tauto
      rw [hSet]
      exact h1.union (measurableSet_shading_union Z).compl
    · have hSet :
          {p : Point3 | P p n} =
            {p : Point3 |
              p ∈ Z.union ∧ Qualifies p (equivPair.symm n)} := by
        ext p
        simp [P, hn]
      rw [hSet]
      exact h1
  have hPnonempty : ∀ p : Point3, ∃ n : Fin N, P p n := by
    intro p
    by_cases hp : p ∈ Z.union
    · rcases hGoodPair p hp with
        ⟨i, j, hi, hj, hTransverse, hCount⟩
      let ij : Fin F.card × Fin F.card := (i, j)
      have hQualifies : Qualifies p ij :=
        ⟨hi, hj, hTransverse, hCount⟩
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
    have hEquivMeasurable :
        Measurable
          (equivPair.symm :
            Fin N → Fin F.card × Fin F.card) :=
      Measurable.of_discrete
    exact hEquivMeasurable.comp hChoiceMeasurable
  let first : Point3 → Fin F.card := fun p => (chosen p).1
  let second : Point3 → Fin F.card := fun p => (chosen p).2
  have hFirstMeasurable : Measurable first :=
    hChosenMeasurable.fst
  have hSecondMeasurable : Measurable second :=
    hChosenMeasurable.snd
  have hFirstMem :
      ∀ p ∈ Z.union, p ∈ Z.carrier (first p) := by
    intro p hp
    have h := hChoice p
    rcases h with h | h
    · exact h.2.1
    · exact False.elim (h.1 hp)
  have hSecondMem :
      ∀ p ∈ Z.union, p ∈ Z.carrier (second p) := by
    intro p hp
    have h := hChoice p
    rcases h with h | h
    · exact h.2.2.1
    · exact False.elim (h.1 hp)
  have hTransverse :
      ∀ p ∈ Z.union,
        kappa ≤
          ‖wz1Cross
            (F.tube (first p)).direction
            (F.tube (second p)).direction‖ := by
    intro p hp
    have h := hChoice p
    rcases h with h | h
    · exact h.2.2.2.1
    · exact False.elim (h.1 hp)
  have hGoodCount :
      ∀ p ∈ Z.union,
        Z.pointMultiplicity p ≤
          4 * wz1GoodThirdCount
            Z p (first p) (second p) tau := by
    intro p hp
    have h := hChoice p
    rcases h with h | h
    · exact h.2.2.2.2
    · exact False.elim (h.1 hp)
  let selection : WZ1NarrowDirectionSelection Z kappa :=
    { first := first
      second := second
      first_measurable := hFirstMeasurable
      second_measurable := hSecondMeasurable
      first_mem := hFirstMem
      second_mem := hSecondMem
      transverse := hTransverse }
  let selected : Kakeya.Streamlined.TubeShading F :=
    { carrier := fun k =>
        {p |
          p ∈ Z.carrier k ∧
          |wz1TripleProduct
            (F.tube (first p)).direction
            (F.tube (second p)).direction
            (F.tube k).direction| < tau}
      measurable_carrier := fun k =>
        (Z.measurable_carrier k).inter
          (measurable_selected_carrier
            hFirstMeasurable hSecondMeasurable k)
      subset_body := fun k p hp => Z.subset_body k hp.1 }
  have hSelectedSub : IsSubshading selected Z := by
    intro k p hp
    exact hp.1
  have hCarrierEq :
      ∀ k, selected.carrier k =
        {p |
          p ∈ Z.carrier k ∧
          |wz1TripleProduct
            (F.tube (selection.first p)).direction
            (F.tube (selection.second p)).direction
            (F.tube k).direction| < tau} := by
    intro k
    rfl
  have hMultiplicity :
      ∀ p ∈ Z.union,
        Z.pointMultiplicity p ≤
          4 * selected.pointMultiplicity p := by
    intro p hp
    have h1 :
        Z.pointMultiplicity p ≤
          4 * wz1GoodThirdCount
            Z p (first p) (second p) tau :=
      hGoodCount p hp
    have h2 :
        wz1GoodThirdCount
            Z p (first p) (second p) tau ≤
          selected.pointMultiplicity p := by
      simp [selected, Kakeya.Streamlined.Shading.pointMultiplicity,
        wz1GoodThirdCount]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))
  have hMass :
      (1 / 4 : ENNReal) * Z.mass ≤ selected.mass :=
    mass_lower_from_pointMultiplicity hMultiplicity
  let planeMap : WZ1WeakPlaneMapData selected (tau / kappa) :=
    { planeMap := selection.normal
      measurable := selection.normal_measurable
      unit := by
        intro p hp
        rcases hp with ⟨k, hk⟩
        have hpSelected : p ∈ selected.union := ⟨k, hk⟩
        have hpZ : p ∈ Z.union :=
          hSelectedSub.union_subset hpSelected
        let cross :=
          wz1Cross
            (F.tube (first p)).direction
            (F.tube (second p)).direction
        have hCrossPos : 0 < ‖cross‖ :=
          hkappa.trans_le (hTransverse p hpZ)
        have hCrossNe : ‖cross‖ ≠ 0 := hCrossPos.ne'
        have h1 :
            selection.normal p = (‖cross‖)⁻¹ • cross := by
          rfl
        rw [h1, norm_smul]
        have hAbs : ‖(‖cross‖)⁻¹‖ = (‖cross‖)⁻¹ := by
          simp [Real.norm_eq_abs, abs_of_pos]
        rw [hAbs]
        field_simp [hCrossNe]
      incidence := by
        intro i p hp
        have hpSelected : p ∈ selected.union := ⟨i, hp⟩
        have hpZ : p ∈ Z.union :=
          hSelectedSub.union_subset hpSelected
        let u := (F.tube (first p)).direction
        let v := (F.tube (second p)).direction
        let w := (F.tube i).direction
        let cross := wz1Cross u v
        have hCross : kappa ≤ ‖cross‖ := hTransverse p hpZ
        have hCrossPos : 0 < ‖cross‖ :=
          hkappa.trans_le hCross
        have hTriple :
            |wz1TripleProduct u v w| ≤ tau :=
          le_of_lt hp.2
        have hInner :
            inner ℝ w cross = wz1TripleProduct u v w :=
          inner_cross_triple u v w
        have hEq :
            inner ℝ w (selection.normal p) =
              (‖cross‖)⁻¹ * wz1TripleProduct u v w := by
          have hDef :
              selection.normal p = (‖cross‖)⁻¹ • cross := by
            rfl
          rw [hDef, inner_smul_right, hInner]
        rw [hEq]
        have hAbs :
            |(‖cross‖)⁻¹ * wz1TripleProduct u v w| =
              |wz1TripleProduct u v w| / ‖cross‖ := by
          rw [abs_mul, abs_inv, abs_of_pos hCrossPos]
          field_simp [hCrossPos.ne']
        rw [hAbs]
        exact
          (div_le_div_of_nonneg_left
            (abs_nonneg _) hkappa hCross).trans
            (div_le_div_of_nonneg_right hTriple hkappa.le) }
  have hPlaneMapEq :
      ∀ p ∈ selected.union,
        planeMap.planeMap p = selection.normal p := by
    intro p hp
    rfl
  exact
    ⟨⟨narrow, selection, selected, hSelectedSub, hCarrierEq,
      hMultiplicity, hMass, planeMap, hPlaneMapEq⟩, rfl⟩

end Kakeya.Assouad
