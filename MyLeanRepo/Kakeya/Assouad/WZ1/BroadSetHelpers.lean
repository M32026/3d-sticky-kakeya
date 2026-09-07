import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions

/-!
# Helper lemmas for the WZ1 counted-broad set

1. `wz1_large_triple_count_le_multiplicity`: Q large triples imply
   multiplicity ≥ Q * tau.

2. `wz1CountedBroadSet_measurable`: the counted-broad set is measurable.
-/

noncomputable section

namespace Kakeya.Assouad

open Finset

lemma wz1_large_triple_count_le_multiplicity
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (p : Point3) (tau : ℝ) (Q : ℕ)
    (h : Q ≤ wz1LargeTripleCount Y p tau) :
    (Q : ENNReal) * ENNReal.ofReal tau ≤
      wz1ShadingTrilinearMultiplicity Y p := by
  classical
  let P : Finset (Fin F.card × (Fin F.card × Fin F.card)) :=
    Finset.univ.product (Finset.univ.product Finset.univ)
  let S := P.filter fun ijk =>
    p ∈ Y.carrier ijk.1 ∧
    p ∈ Y.carrier ijk.2.1 ∧
    p ∈ Y.carrier ijk.2.2 ∧
    tau ≤ |wz1TripleProduct
      (F.tube ijk.1).direction
      (F.tube ijk.2.1).direction
      (F.tube ijk.2.2).direction|
  let f (ijk : Fin F.card × (Fin F.card × Fin F.card)) : ENNReal :=
    Set.indicator (Y.carrier ijk.1) (fun _ => (1 : ENNReal)) p *
    Set.indicator (Y.carrier ijk.2.1) (fun _ => (1 : ENNReal)) p *
    Set.indicator (Y.carrier ijk.2.2) (fun _ => (1 : ENNReal)) p *
    ENNReal.ofReal
      |wz1TripleProduct
        (F.tube ijk.1).direction
        (F.tube ijk.2.1).direction
        (F.tube ijk.2.2).direction|
  let g (i j k : Fin F.card) : ENNReal :=
    Set.indicator (Y.carrier i) (fun _ => (1 : ENNReal)) p *
    Set.indicator (Y.carrier j) (fun _ => (1 : ENNReal)) p *
    Set.indicator (Y.carrier k) (fun _ => (1 : ENNReal)) p *
    ENNReal.ofReal
      |wz1TripleProduct (F.tube i).direction (F.tube j).direction (F.tube k).direction|

  have hS_card : S.card = wz1LargeTripleCount Y p tau := by rfl
  have hQ : Q ≤ S.card := by
    rw [hS_card] at *; exact h

  have h_step1 : ∀ (i : Fin F.card),
      (∑ j : Fin F.card, ∑ k : Fin F.card, g i j k) =
      ∑ jk ∈ (Finset.univ.product Finset.univ), g i jk.1 jk.2 := by
    intro i
    let h : (Fin F.card × Fin F.card) → ENNReal := fun jk => g i jk.1 jk.2
    have h_eq1 : ∑ jk ∈ (Finset.univ.product Finset.univ), h jk =
        ∑ j : Fin F.card, ∑ k : Fin F.card, h (j, k) := Finset.sum_product _ _ h
    have h_eq2 : ∑ j : Fin F.card, ∑ k : Fin F.card, h (j, k) =
        ∑ j : Fin F.card, ∑ k : Fin F.card, g i j k := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      simp [h]
    exact (h_eq1.trans h_eq2).symm
  have h_eq : wz1ShadingTrilinearMultiplicity Y p = ∑ ijk ∈ P, f ijk := by
    have h3 : ∑ i : Fin F.card, (∑ j : Fin F.card, ∑ k : Fin F.card, g i j k) =
        ∑ i : Fin F.card, ∑ jk ∈ (Finset.univ.product Finset.univ), g i jk.1 jk.2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact h_step1 i
    let h2 : (Fin F.card × (Fin F.card × Fin F.card)) → ENNReal := fun ijk =>
      g ijk.1 ijk.2.1 ijk.2.2
    have h41 : ∑ ijk ∈ P, h2 ijk =
        ∑ i : Fin F.card, ∑ jk ∈ (Finset.univ.product Finset.univ), h2 (i, jk) :=
      Finset.sum_product _ _ h2
    have h42 : ∑ i : Fin F.card, ∑ jk ∈ (Finset.univ.product Finset.univ), h2 (i, jk) =
        ∑ i : Fin F.card, ∑ jk ∈ (Finset.univ.product Finset.univ), g i jk.1 jk.2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro jk _
      simp [h2]
    have h43 : ∑ ijk ∈ P, f ijk = ∑ ijk ∈ P, h2 ijk := by
      apply Finset.sum_congr rfl
      intro ijk _
      simp [f, g, h2]
    have h4 : ∑ i : Fin F.card, ∑ jk ∈ (Finset.univ.product Finset.univ), g i jk.1 jk.2 =
        ∑ ijk ∈ P, f ijk := by
      exact (h42.symm.trans h41.symm).trans h43.symm
    have h5 : wz1ShadingTrilinearMultiplicity Y p =
        ∑ i : Fin F.card, ∑ j : Fin F.card, ∑ k : Fin F.card, g i j k := by
      simp [wz1ShadingTrilinearMultiplicity, g]
    rw [h5, h3, h4]

  by_cases htau : 0 ≤ tau
  · -- Case tau ≥ 0
    have h1 : ∀ ijk ∈ S, ENNReal.ofReal tau ≤ f ijk := by
      intro ijk hijk
      simp only [S, Finset.mem_filter] at hijk
      rcases hijk with ⟨_, hi, hj, hk, hprod⟩
      have hi' : Set.indicator (Y.carrier ijk.1) (fun _ => (1 : ENNReal)) p = 1 := by
        simp [hi]
      have hj' : Set.indicator (Y.carrier ijk.2.1) (fun _ => (1 : ENNReal)) p = 1 := by
        simp [hj]
      have hk' : Set.indicator (Y.carrier ijk.2.2) (fun _ => (1 : ENNReal)) p = 1 := by
        simp [hk]
      have hf : f ijk = ENNReal.ofReal
          |wz1TripleProduct
            (F.tube ijk.1).direction
            (F.tube ijk.2.1).direction
            (F.tube ijk.2.2).direction| := by
        simp [f, hi', hj', hk']
      rw [hf]
      exact ENNReal.ofReal_le_ofReal hprod
    have h_sum_S : ∑ ijk ∈ S, ENNReal.ofReal tau ≤ ∑ ijk ∈ S, f ijk :=
      Finset.sum_le_sum h1
    have h_sub : S ⊆ P := by
      intro ijk hijk
      exact (Finset.mem_filter.mp hijk).1
    have h_nonneg : ∀ (x : _), x ∈ P → x ∉ S → 0 ≤ f x := by
      intro x _ _
      exact bot_le
    have h_sum_P : ∑ ijk ∈ S, f ijk ≤ ∑ ijk ∈ P, f ijk :=
      Finset.sum_le_sum_of_subset_of_nonneg h_sub h_nonneg
    have h_card_sum : ∑ ijk ∈ S, ENNReal.ofReal tau = (S.card : ENNReal) * ENNReal.ofReal tau := by
      have h : ∑ ijk ∈ S, ENNReal.ofReal tau = S.card • ENNReal.ofReal tau := by
        rw [Finset.sum_const]
      rw [h]
      simp [nsmul_eq_mul]
    rw [h_eq]
    have h3 : (Q : ENNReal) ≤ (S.card : ENNReal) := by exact_mod_cast hQ
    calc
      (Q : ENNReal) * ENNReal.ofReal tau
        ≤ (S.card : ENNReal) * ENNReal.ofReal tau := by
          gcongr
      _ = ∑ ijk ∈ S, ENNReal.ofReal tau := h_card_sum.symm
      _ ≤ ∑ ijk ∈ S, f ijk := h_sum_S
      _ ≤ ∑ ijk ∈ P, f ijk := h_sum_P
  · -- Case tau < 0: ENNReal.ofReal tau = 0
    have h_neg : tau < 0 := by linarith
    have h_ofReal : ENNReal.ofReal tau = 0 := by
      rw [ENNReal.ofReal_eq_zero.mpr] <;> linarith
    rw [h_ofReal]
    <;> simp

lemma wz1CountedBroadSet_measurable
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (tau : ℝ) (Q : ℕ) :
    MeasurableSet (wz1CountedBroadSet Y tau Q) := by
  classical
  have h_union_meas : MeasurableSet Y.union := by
    have h1 : Y.union = ⋃ i : Fin F.card, Y.carrier i := by
      ext x
      simp [Kakeya.Streamlined.Shading.union]
      <;> aesop
    rw [h1]
    exact MeasurableSet.iUnion fun i => Y.measurable_carrier i

  let P : Finset (Fin F.card × (Fin F.card × Fin F.card)) :=
    Finset.univ.product (Finset.univ.product Finset.univ)

  let condition (ijk : Fin F.card × (Fin F.card × Fin F.card)) (p : Point3) : Prop :=
    p ∈ Y.carrier ijk.1 ∧
    p ∈ Y.carrier ijk.2.1 ∧
    p ∈ Y.carrier ijk.2.2 ∧
    tau ≤ |wz1TripleProduct
      (F.tube ijk.1).direction
      (F.tube ijk.2.1).direction
      (F.tube ijk.2.2).direction|

  have h_cond_meas : ∀ ijk, MeasurableSet {p : Point3 | condition ijk p} := by
    intro ijk
    have h1 : MeasurableSet (Y.carrier ijk.1) := Y.measurable_carrier ijk.1
    have h2 : MeasurableSet (Y.carrier ijk.2.1) := Y.measurable_carrier ijk.2.1
    have h3 : MeasurableSet (Y.carrier ijk.2.2) := Y.measurable_carrier ijk.2.2
    let prod_abs := |wz1TripleProduct
      (F.tube ijk.1).direction (F.tube ijk.2.1).direction (F.tube ijk.2.2).direction|
    have h4 : MeasurableSet {p : Point3 | tau ≤ prod_abs} := by
      by_cases h : tau ≤ prod_abs
      · have h5 : {p : Point3 | tau ≤ prod_abs} = Set.univ := by
          ext p; simp [h]
        rw [h5]; exact MeasurableSet.univ
      · have h5 : {p : Point3 | tau ≤ prod_abs} = ∅ := by
          ext p; simp [h]
        rw [h5]; exact MeasurableSet.empty
    exact h1.inter (h2.inter (h3.inter h4))

  have h_count_eq : ∀ (p : Point3), wz1LargeTripleCount Y p tau =
      ∑ ijk ∈ P, if condition ijk p then (1 : ℕ) else 0 := by
    intro p
    have h_filter : ∑ ijk ∈ P, (if condition ijk p then (1 : ℕ) else 0) =
        (P.filter (fun ijk => condition ijk p)).card := by
      calc
        ∑ ijk ∈ P, (if condition ijk p then (1 : ℕ) else 0)
          = ∑ ijk ∈ (P.filter (fun ijk => condition ijk p)), (1 : ℕ) +
            ∑ ijk ∈ (P.filter (fun ijk => ¬condition ijk p)), (0 : ℕ) := by
              rw [Finset.sum_ite]
        _ = (P.filter (fun ijk => condition ijk p)).card + 0 := by simp
        _ = (P.filter (fun ijk => condition ijk p)).card := by simp
    have h_def : wz1LargeTripleCount Y p tau = (P.filter (fun ijk => condition ijk p)).card := by
      simp [wz1LargeTripleCount, condition] <;> rfl
    rw [h_def]
    exact h_filter.symm

  have h_count_meas : Measurable (fun p : Point3 => wz1LargeTripleCount Y p tau) := by
    rw [funext h_count_eq]
    apply Finset.measurable_sum
    intro ijk _
    exact measurable_one.ite (h_cond_meas ijk) measurable_zero

  have hIci : MeasurableSet (Set.Ici Q) := measurableSet_Ici
  have h5 : MeasurableSet {p : Point3 | Q ≤ wz1LargeTripleCount Y p tau} :=
    h_count_meas hIci

  have h6 : wz1CountedBroadSet Y tau Q =
      Y.union ∩ {p : Point3 | Q ≤ wz1LargeTripleCount Y p tau} := by
    ext p
    simp [wz1CountedBroadSet]
  rw [h6]
  exact h_union_meas.inter h5

/--
The good-triple budget inequality from WZ1 Lemma 11.

Given constant multiplicity `mu ∈ [m, 2m]` and thresholds `Q, R` satisfying
`4 * Q ≤ m^3` and `12 * R ≤ m`, we have
`4 * (Q + 3 * R * mu^2) ≤ 3 * mu^3`.

Proof: `4*Q ≤ mu^3` and `12*R*mu^2 ≤ mu^3`, so their sum is at most
`2 * mu^3 ≤ 3 * mu^3`.
-/
lemma wz1_good_triple_budget
    (m Q R mu : ℕ)
    (hm_mu : m ≤ mu)
    (hQ : 4 * Q ≤ m ^ 3)
    (hR : 12 * R ≤ m) :
    4 * (Q + 3 * R * mu ^ 2) ≤ 3 * mu ^ 3 := by
  have h1 : 4 * Q ≤ mu ^ 3 := by
    calc
      4 * Q ≤ m ^ 3 := hQ
      _ ≤ mu ^ 3 := by gcongr
  have h2 : 12 * R ≤ mu := by
    calc
      12 * R ≤ m := hR
      _ ≤ mu := hm_mu
  have h3 : 12 * R * mu ^ 2 ≤ mu ^ 3 := by
    calc
      12 * R * mu ^ 2 ≤ mu * mu ^ 2 := by
        gcongr
        <;> nlinarith
      _ = mu ^ 3 := by ring
  have h4 : 4 * (Q + 3 * R * mu ^ 2) = 4 * Q + 12 * R * mu ^ 2 := by
    ring
  rw [h4]
  calc
    4 * Q + 12 * R * mu ^ 2 ≤ mu ^ 3 + mu ^ 3 := by
      gcongr <;> omega
    _ = 2 * mu ^ 3 := by ring
    _ ≤ 3 * mu ^ 3 := by
      nlinarith

end Kakeya.Assouad
