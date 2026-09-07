import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredHierarchyHelpers
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Tactic

/-!
# Generalized thickening lemma for IsADSet1

If `IsADSet1 E δ α C` and `B ⊆ cthickening ε E` with `ε > 0`,
then `IsADSet1 B δ α (K^2 * C)` where `K = 2 * (ceil(ε/δ) + 1)`.
Unlike the existing simple thickening theorem, this permits arbitrary
positive `ε`, not only `ε ≤ δ`.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

private lemma externalCoveringNumber_exists
    {X : Type*} [PseudoEMetricSpace X] {ε : NNReal} {A : Set X}
    (_h : externalCoveringNumber ε A ≠ ⊤) :
    ∃ C : Set X, IsCover ε A C ∧ C.encard = externalCoveringNumber ε A := by
  have h_nonempty : Nonempty {s : Set X // IsCover ε A s} :=
    ⟨⟨A, IsCover.refl ε A⟩⟩
  obtain ⟨C, hC⟩ := ENat.exists_eq_iInf
    (fun C : {s : Set X // IsCover ε A s} => (C : Set X).encard)
  have h_eq : (C : Set X).encard = externalCoveringNumber ε A := by
    simpa [externalCoveringNumber, iInf_subtype] using hC
  exact ⟨(C : Set X), C.property, h_eq⟩

lemma shift_cover_geometric
    {y rho : ℝ} (hrho : 0 < rho) {k' : ℕ}
    (h : |y| ≤ (k' + 1 : ℝ) * rho) :
    ∃ j : ℤ, (-(k' : ℤ) ≤ j ∧ j ≤ (k' : ℤ) + 1) ∧
      |y - 2 * (j : ℝ) * rho| ≤ rho := by
  let j : ℤ := Int.floor (y / (2 * rho) + 1 / 2)
  have h_pos2 : 0 < 2 * rho := by linarith
  have h1 : (j : ℝ) ≤ y / (2 * rho) + 1 / 2 := Int.floor_le _
  have h2 : y / (2 * rho) + 1 / 2 < (j : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have h5 : |y / (2 * rho) - (j : ℝ)| ≤ 1 / 2 := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h6 : |y - 2 * (j : ℝ) * rho| ≤ rho := by
    have h71 : 2 * rho * (y / (2 * rho)) = y := by
      field_simp [hrho.ne'] <;> ring
    have h7 :
        y - 2 * (j : ℝ) * rho =
          2 * rho * (y / (2 * rho) - (j : ℝ)) := by
      rw [mul_sub, h71] <;> ring
    rw [h7, abs_mul, abs_of_pos h_pos2]
    have h9 :
        2 * rho * |y / (2 * rho) - (j : ℝ)| ≤
          2 * rho * (1 / 2 : ℝ) := by
      gcongr
    linarith
  have h_ybound1 : -(k' + 1 : ℝ) / 2 ≤ y / (2 * rho) := by
    have h10 : y ≥ -((k' + 1 : ℝ) * rho) := (abs_le.mp h).1
    have h11 :
        y / (2 * rho) ≥
          -((k' + 1 : ℝ) * rho) / (2 * rho) := by
      gcongr
    have h12 :
        -((k' + 1 : ℝ) * rho) / (2 * rho) =
          -((k' + 1 : ℝ) / 2) := by
      field_simp [hrho.ne'] <;> ring
    linarith
  have h_ybound2 : y / (2 * rho) ≤ (k' + 1 : ℝ) / 2 := by
    have h10 : y ≤ (k' + 1 : ℝ) * rho := (abs_le.mp h).2
    have h11 :
        y / (2 * rho) ≤ ((k' + 1 : ℝ) * rho) / (2 * rho) := by
      gcongr
    have h12 :
        ((k' + 1 : ℝ) * rho) / (2 * rho) =
          (k' + 1 : ℝ) / 2 := by
      field_simp [hrho.ne'] <;> ring
    linarith
  have h_lower : -(k' : ℤ) ≤ j := by
    by_contra h15
    have h16 : j ≤ -(k' : ℤ) - 1 := by omega
    have h17 : (j : ℝ) ≤ -(k' : ℝ) - 1 := by exact_mod_cast h16
    linarith
  have h_upper : j ≤ (k' : ℤ) + 1 := by
    by_contra h15
    have h16 : j ≥ (k' : ℤ) + 2 := by omega
    have h17 : (j : ℝ) ≥ (k' : ℝ) + 2 := by exact_mod_cast h16
    linarith
  exact ⟨j, ⟨h_lower, h_upper⟩, h6⟩

lemma finite_cover_cthickening_general
    {rho epsilon : ℝ} (hrho : 0 ≤ rho) (hepsilon : 0 ≤ epsilon)
    {S : Set ℝ} {C : Finset ℝ}
    (hC : IsCover ⟨rho, hrho⟩ S (C : Set ℝ))
    {x : ℝ} (hx : x ∈ cthickening epsilon S) :
    ∃ c ∈ C, dist x c ≤ rho + epsilon := by
  by_contra h
  push Not at h
  have hC_nonempty : C.Nonempty := by
    by_cases hC_empty : C = ∅
    · have hS_empty : S = ∅ := by
        by_contra hS2
        obtain ⟨s, hs⟩ := Set.nonempty_iff_ne_empty.mpr hS2
        rcases hC hs with ⟨c, hc, _⟩
        rw [hC_empty] at hc <;> simp at hc
      rw [hS_empty] at hx
      simp [cthickening] at hx
    · exact Finset.nonempty_iff_ne_empty.mpr hC_empty
  let dists : Finset ℝ := C.image (fun c => dist x c - (rho + epsilon))
  rcases hC_nonempty with ⟨c0, hc0⟩
  have h_dists_nonempty : dists.Nonempty :=
    ⟨_, Finset.mem_image.mpr ⟨c0, hc0, rfl⟩⟩
  let η := dists.min' h_dists_nonempty
  have hη_in : η ∈ dists := Finset.min'_mem dists h_dists_nonempty
  have hη_pos : 0 < η := by
    rcases Finset.mem_image.mp hη_in with ⟨c, hc, h_eq⟩
    have h_gt : rho + epsilon < dist x c := h c hc
    rw [← h_eq]
    exact sub_pos.mpr h_gt
  have h_ge : ∀ c ∈ C, dist x c - (rho + epsilon) ≥ η := by
    intro c hc
    exact Finset.min'_le dists _
      (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  have h_all : ∀ s ∈ S, dist x s ≥ epsilon + η := by
    intro s hs
    rcases hC hs with ⟨c, hc, hedist⟩
    have hdist_sc : dist s c ≤ rho := by exact_mod_cast hedist
    have h1 : dist x c ≥ rho + epsilon + η := by
      have := h_ge c hc
      linarith
    have h2 : dist x c ≤ dist x s + dist s c := dist_triangle x s c
    linarith
  have h5 : ENNReal.ofReal (epsilon + η) ≤ infEDist x S := by
    rw [Metric.le_infEDist]
    intro s hs
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (h_all s hs)
  have h6 : infEDist x S ≤ ENNReal.ofReal epsilon := by
    simpa [cthickening, Set.mem_setOf_eq] using hx
  have h7 : ENNReal.ofReal epsilon < ENNReal.ofReal (epsilon + η) := by
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hepsilon]
    linarith
  exact (not_le.mpr h7) (h5.trans h6)

lemma externalCoveringNumber_cthickening_general
    {epsilon rho : ℝ} (hepsilon : 0 < epsilon) (hrho : 0 < rho)
    {S : Set ℝ} :
    externalCoveringNumber ⟨rho, by linarith⟩ (cthickening epsilon S) ≤
      (2 * Nat.ceil (epsilon / rho) + 2 : ENat) *
        externalCoveringNumber ⟨rho, by linarith⟩ S := by
  let k' : ℕ := Nat.ceil (epsilon / rho)
  have hk' : (k' : ℝ) ≥ epsilon / rho := Nat.le_ceil _
  have h_eps_bound : epsilon ≤ (k' : ℝ) * rho := by
    calc
      epsilon = (epsilon / rho) * rho := by
        field_simp [hrho.ne'] <;> ring
      _ ≤ (k' : ℝ) * rho := by gcongr
  by_cases htop :
      externalCoveringNumber ⟨rho, by linarith⟩ S = ⊤
  · rw [htop]
    simp
  · rcases externalCoveringNumber_exists htop with
      ⟨C, hCcover, hCcard⟩
    have hC_finite : Set.Finite C := by
      have h : C.encard ≠ ⊤ := by
        rw [hCcard]
        exact htop
      exact encard_ne_top_iff.mp h
    let Cfin : Finset ℝ := hC_finite.toFinset
    have hCfin_coe : (Cfin : Set ℝ) = C := by
      simp [Cfin, hC_finite.coe_toFinset]
    have hCcover' :
        IsCover ⟨rho, by linarith⟩ S (Cfin : Set ℝ) := by
      rw [hCfin_coe]
      exact hCcover
    let shifts : Finset ℤ :=
      Finset.Icc (-(k' : ℤ)) ((k' : ℤ) + 1)
    let shifts' : Finset ℝ :=
      shifts.image (fun j : ℤ => (j : ℝ))
    let C' : Finset ℝ :=
      Cfin.biUnion fun c =>
        shifts'.image (fun t => c + 2 * t * rho)
    have hcover :
        IsCover ⟨rho, by linarith⟩
          (cthickening epsilon S) (C' : Set ℝ) := by
      intro x hx
      rcases finite_cover_cthickening_general
          (by linarith) (by linarith) hCcover' hx with
        ⟨c, hc, hdist⟩
      have h_abs : |x - c| ≤ rho + epsilon := by
        simpa [Real.dist_eq] using hdist
      have h_range : |x - c| ≤ (k' + 1 : ℝ) * rho := by
        calc
          |x - c| ≤ rho + epsilon := h_abs
          _ ≤ rho + (k' : ℝ) * rho := by gcongr
          _ = (k' + 1 : ℝ) * rho := by ring
      rcases shift_cover_geometric hrho h_range with
        ⟨j, hj_range, hj_dist⟩
      have h_j' : (j : ℝ) ∈ shifts' := by
        exact Finset.mem_image.mpr
          ⟨j, by simp [shifts, Finset.mem_Icc, hj_range], rfl⟩
      let c' := c + 2 * (j : ℝ) * rho
      have h_c'_in_img :
          c' ∈ Finset.image
            (fun t : ℝ => c + 2 * t * rho) shifts' := by
        exact Finset.mem_image.mpr
          ⟨(j : ℝ), h_j', by simp [c']⟩
      have h_c'_in_C' : c' ∈ C' := by
        exact Finset.mem_biUnion.mpr
          ⟨c, hc, h_c'_in_img⟩
      have h_dist' : dist x c' ≤ rho := by
        have h_eq :
            x - c' = x - c - 2 * (j : ℝ) * rho := by
          ring
        rw [Real.dist_eq, h_eq]
        exact hj_dist
      let eps_nn : NNReal := ⟨rho, by linarith⟩
      have h_edist : edist x c' ≤ (↑eps_nn : ENNReal) := by
        rw [edist_dist, ENNReal.coe_nnreal_eq]
        exact ENNReal.ofReal_le_ofReal h_dist'
      exact ⟨c', h_c'_in_C', h_edist⟩
    have h_card : C'.card ≤ Cfin.card * shifts'.card := by
      calc
        C'.card ≤
            ∑ c ∈ Cfin,
              (shifts'.image
                (fun t : ℝ => c + 2 * t * rho)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _c ∈ Cfin, shifts'.card :=
          Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
        _ = Cfin.card * shifts'.card := by
          simp [Finset.sum_const]
    have h_inj : Set.InjOn (fun j : ℤ => (j : ℝ)) shifts := by
      intro a _ b _ h
      exact Int.cast_inj.mp h
    have h_shifts'_card : shifts'.card = shifts.card :=
      Finset.card_image_of_injOn h_inj
    have h_shifts_card : shifts.card = 2 * k' + 2 := by
      have h1 : (-(k' : ℤ)) ≤ (k' : ℤ) + 1 + 1 := by omega
      have h2 :
          (↑shifts.card : ℤ) =
            ((k' : ℤ) + 1) + 1 - (-(k' : ℤ)) :=
        Int.card_Icc_of_le
          (-(k' : ℤ)) ((k' : ℤ) + 1) h1
      have h3 :
          (↑shifts.card : ℤ) = 2 * (k' : ℤ) + 2 := by
        rw [h2]
        ring
      exact_mod_cast h3
    have h_main :
        externalCoveringNumber ⟨rho, by linarith⟩
            (cthickening epsilon S) ≤
          (C' : Set ℝ).encard :=
      IsCover.externalCoveringNumber_le_encard hcover
    have h_encard : (C' : Set ℝ).encard = ↑C'.card := by
      simp
    rw [h_encard] at h_main
    have h2 : C.encard = ↑Cfin.card := by
      have h3 : C.encard = (Cfin : Set ℝ).encard := by
        rw [hCfin_coe]
      rw [h3]
      simp
    rw [h2] at hCcard
    have h4 : C'.card ≤ Cfin.card * (2 * k' + 2) := by
      rw [h_shifts'_card, h_shifts_card] at h_card
      exact h_card
    have h_final :
        (↑C'.card : ENat) ≤
          (2 * k' + 2 : ENat) *
            externalCoveringNumber ⟨rho, by linarith⟩ S := by
      have h5 :
          (↑C'.card : ENat) ≤
            ↑(Cfin.card * (2 * k' + 2)) := by
        exact_mod_cast h4
      have h6 :
          (↑C'.card : ENat) ≤
            (2 * k' + 2 : ENat) * (↑Cfin.card : ENat) := by
        simpa [mul_comm] using h5
      rw [hCcard] at *
      exact h6
    exact h_main.trans h_final

lemma thickening_inter_containment_general
    {A B : Set ℝ} {x r epsilon : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (hA_thick : A ⊆ cthickening epsilon B) :
    A ∩ Metric.closedBall x r ⊆
      cthickening epsilon
        (B ∩ Metric.closedBall x (r + 2 * epsilon)) := by
  intro y hy
  have h_y_in : y ∈ cthickening epsilon B := hA_thick hy.1
  by_contra h_not
  have h_infEDist_core_gt :
      infEDist y (B ∩ Metric.closedBall x (r + 2 * epsilon)) >
        ENNReal.ofReal epsilon := by
    simpa [cthickening, Set.mem_setOf_eq] using h_not
  have h_exists_eps : ∃ ε' : ℝ, 0 < ε' ∧
      infEDist y (B ∩ Metric.closedBall x (r + 2 * epsilon)) ≥
        ENNReal.ofReal (epsilon + ε') := by
    let S' := B ∩ Metric.closedBall x (r + 2 * epsilon)
    by_cases h_top : infEDist y S' = ⊤
    · exact ⟨1, by norm_num, by rw [h_top]; simp⟩
    · let r' := ENNReal.toReal (infEDist y S')
      have hr : ENNReal.ofReal r' = infEDist y S' :=
        ENNReal.ofReal_toReal_eq_iff.mpr h_top
      have h_gt : r' > epsilon := by
        have h1 : ENNReal.ofReal r' > ENNReal.ofReal epsilon := by
          rw [hr]
          exact h_infEDist_core_gt
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
          (by linarith)).mp h1
      refine ⟨(r' - epsilon) / 2, by linarith, ?_⟩
      rw [← hr]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  rcases h_exists_eps with ⟨ε', hε_pos, h_core_ge⟩
  let ε'' := min ε' epsilon
  have hε''_pos : 0 < ε'' := by positivity
  have h_all : ∀ b ∈ B, dist y b ≥ epsilon + ε'' := by
    intro b hb
    by_cases hball :
        b ∈ Metric.closedBall x (r + 2 * epsilon)
    · have h2 :
          infEDist y
              (B ∩ Metric.closedBall x (r + 2 * epsilon)) ≤
            edist y b :=
        Metric.infEDist_le_edist_of_mem ⟨hb, hball⟩
      have h3 : ENNReal.ofReal (epsilon + ε') ≤ edist y b :=
        h_core_ge.trans h2
      rw [edist_dist] at h3
      have h4 : epsilon + ε' ≤ dist y b :=
        (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3
      linarith [min_le_left ε' epsilon]
    · have h_dist_bx : dist b x > r + 2 * epsilon := by
        simpa [Metric.mem_closedBall, not_le] using hball
      have h_dist_yx : dist y x ≤ r := by
        simpa [Metric.mem_closedBall] using hy.2
      have htri := dist_triangle b y x
      rw [dist_comm b y] at htri
      linarith [min_le_right ε' epsilon]
  have h_infEDist_B_ge :
      ENNReal.ofReal (epsilon + ε'') ≤ infEDist y B := by
    rw [Metric.le_infEDist]
    intro b hb
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (h_all b hb)
  have h6 :
      ENNReal.ofReal epsilon <
        ENNReal.ofReal (epsilon + ε'') := by
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)]
    linarith
  have h7 : ENNReal.ofReal (epsilon + ε'') ≤ ENNReal.ofReal epsilon :=
    h_infEDist_B_ge.trans h_y_in
  exact (not_le.mpr h6) h7

lemma closedBall_split_2k2
    {x r epsilon delta : ℝ} {k : ℕ}
    (hr : 0 < r) (hdelta_r : delta ≤ r)
    (hepsilon : 0 ≤ epsilon) (hk : epsilon ≤ (k : ℝ) * delta) :
    Metric.closedBall x (r + 2 * epsilon) ⊆
    ⋃ j ∈ Finset.range (2 * k + 2),
      Metric.closedBall (x - 2 * epsilon - r + 2 * (j : ℝ) * r) r := by
  intro z hz
  have h_abs : |z - x| ≤ r + 2 * epsilon := by
    simpa [Metric.mem_closedBall, Real.dist_eq] using hz
  let t : ℝ := z - x + 2 * epsilon + r
  have ht_nonneg : 0 ≤ t := by
    have h1 : z - x ≥ -(r + 2 * epsilon) := by
      linarith [abs_le.mp h_abs]
    linarith
  have h_kr : epsilon ≤ (k : ℝ) * r := by
    calc
      epsilon ≤ (k : ℝ) * delta := hk
      _ ≤ (k : ℝ) * r := by gcongr
  have ht_upper : t ≤ (4 * k + 2) * r := by
    have h1 : z - x ≤ r + 2 * epsilon := (abs_le.mp h_abs).2
    have h2 : t ≤ 2 * r + 4 * epsilon := by
      dsimp only [t]
      linarith
    have h3 : 4 * epsilon ≤ 4 * ((k : ℝ) * r) :=
      mul_le_mul_of_nonneg_left h_kr (by norm_num)
    have h4 : 4 * ((k : ℝ) * r) = 4 * (k : ℝ) * r := by
      ring
    rw [h4] at h3
    linarith
  let j : ℤ := Int.floor ((t + r) / (2 * r))
  have h_arg_nonneg : 0 ≤ (t + r) / (2 * r) := by positivity
  have h_j_nonneg : 0 ≤ j := Int.floor_nonneg.mpr h_arg_nonneg
  have h_j_upper : j ≤ (2 * k + 1 : ℤ) := by
    have h5 :
        (t + r) / (2 * r) ≤
          ((4 * k + 2) * r + r) / (2 * r) := by
      gcongr
    have h6 :
        ((4 * k + 2) * r + r) / (2 * r) =
          (4 * k + 3 : ℝ) / 2 := by
      field_simp [hr.ne'] <;> ring
    rw [h6] at h5
    have h7 : (j : ℝ) ≤ (4 * k + 3 : ℝ) / 2 := by
      calc
        (j : ℝ) ≤ (t + r) / (2 * r) := Int.floor_le _
        _ ≤ (4 * k + 3 : ℝ) / 2 := h5
    have h9 : (j : ℝ) < (2 * k + 2 : ℝ) := by linarith
    have h10 : j < 2 * k + 2 := by exact_mod_cast h9
    omega
  let jn : ℕ := j.toNat
  have hjn_coe : (jn : ℤ) = j := by
    simp [jn, Int.toNat_of_nonneg h_j_nonneg]
  have h_jn_in : jn ∈ Finset.range (2 * k + 2) := by
    have h11 : j < 2 * k + 2 := by omega
    have h12 : (jn : ℤ) < 2 * k + 2 := by
      rw [hjn_coe]
      exact h11
    have h13 : jn < 2 * k + 2 := by exact_mod_cast h12
    simpa [Finset.mem_range] using h13
  have hj1 : 2 * (j : ℝ) * r ≤ t + r := by
    have h : (j : ℝ) ≤ (t + r) / (2 * r) := Int.floor_le _
    calc
      2 * (j : ℝ) * r ≤
          2 * ((t + r) / (2 * r)) * r := by gcongr
      _ = t + r := by field_simp [hr.ne'] <;> ring
  have hj2 : t + r < 2 * ((j : ℝ) + 1) * r := by
    have h : (t + r) / (2 * r) < (j : ℝ) + 1 :=
      Int.lt_floor_add_one _
    calc
      t + r = 2 * r * ((t + r) / (2 * r)) := by
        field_simp [hr.ne'] <;> ring
      _ < 2 * r * ((j : ℝ) + 1) := by gcongr
      _ = 2 * ((j : ℝ) + 1) * r := by ring
  have h_dist : |t - 2 * (j : ℝ) * r| ≤ r := by
    have h_lower2 : t - 2 * (j : ℝ) * r ≥ -r := by linarith
    have h_upper2 : t - 2 * (j : ℝ) * r < r := by linarith
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h_final :
      |z - (x - 2 * epsilon - r + 2 * (jn : ℝ) * r)| ≤ r := by
    have h_eq1 : (jn : ℝ) = (j : ℝ) := by exact_mod_cast hjn_coe
    have h_eq :
        z - (x - 2 * epsilon - r + 2 * (jn : ℝ) * r) =
          t - 2 * (j : ℝ) * r := by
      rw [h_eq1] <;> ring
    rw [h_eq]
    exact h_dist
  exact Set.mem_iUnion₂.mpr
    ⟨jn, h_jn_in,
      by simpa [Metric.mem_closedBall, Real.dist_eq] using h_final⟩

private lemma cthickening_finite_iUnion
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Set ℝ) {epsilon : ℝ} :
    cthickening epsilon (⋃ i ∈ s, f i) =
      ⋃ i ∈ s, cthickening epsilon (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have h1 :
        (⋃ i ∈ insert a s, f i) = f a ∪ ⋃ i ∈ s, f i := by
      ext x
      simp [ha, Finset.mem_insert, Set.mem_iUnion] <;> aesop
    have h2 :
        (⋃ i ∈ insert a s, cthickening epsilon (f i)) =
          cthickening epsilon (f a) ∪
            ⋃ i ∈ s, cthickening epsilon (f i) := by
      ext x
      simp [ha, Finset.mem_insert, Set.mem_iUnion] <;> aesop
    rw [h1, Metric.cthickening_union epsilon (f a) (⋃ i ∈ s, f i),
      ih, h2]

lemma IsADSet1.generalized_thickening
    {E B : Set ℝ} {δ α ε : ℝ} {C : ENNReal}
    (hAD : IsADSet1 E δ α C)
    (hthick : B ⊆ Metric.cthickening ε E)
    (hB_bounded : B ⊆ Set.Icc (-4 : ℝ) 4)
    (hδ_pos : 0 < δ)
    (hε_pos : 0 < ε) :
    IsADSet1 B δ α
      ((2 * (Nat.ceil (ε / δ) + 1) : ENNReal) ^ 2 * C) := by
  rcases hAD with ⟨hδ, hα, hα_one, hC_one, hE_bounded, hcover⟩
  let k : ℕ := Nat.ceil (ε / δ)
  let K : ℕ := 2 * (k + 1)
  have hK_pos : 0 < K := by positivity
  have hC_target :
      (1 : ENNReal) ≤
        (2 * (Nat.ceil (ε / δ) + 1) : ENNReal) ^ 2 * C := by
    have h_pos : 0 < 2 * (Nat.ceil (ε / δ) + 1) := by omega
    have h3 :
        (1 : ENNReal) ≤
          (2 * (Nat.ceil (ε / δ) + 1) : ENNReal) := by
      exact_mod_cast h_pos
    have h4 :
        (1 : ENNReal) ≤
          (2 * (Nat.ceil (ε / δ) + 1) : ENNReal) ^ 2 := by
      calc
        (1 : ENNReal) = 1 * 1 := by ring
        _ ≤ _ * _ := mul_le_mul' h3 h3
        _ = _ := by ring
    exact h4.trans (le_mul_of_one_le_right' hC_one)
  refine ⟨hδ, hα, hα_one, hC_target, hB_bounded, ?_⟩
  intro ρ hρ hδ_ρ hρ_one x r hρ_r hr_one
  have hρ_pos : 0 < ρ := by linarith
  have hr_pos : 0 < r := by linarith
  set eps_nn : NNReal := ⟨ρ, by linarith⟩
  have h_kr : ε ≤ (k : ℝ) * δ := by
    have h : (k : ℝ) ≥ ε / δ := Nat.le_ceil (ε / δ)
    calc
      ε = (ε / δ) * δ := by field_simp [hδ_pos.ne'] <;> ring
      _ ≤ (k : ℝ) * δ := by gcongr
  let k' : ℕ := Nat.ceil (ε / ρ)
  have hk'_le : k' ≤ k := by
    have h1 : ε / ρ ≤ ε / δ := by gcongr
    have h2 : ε / δ ≤ (k : ℝ) := Nat.le_ceil (ε / δ)
    exact Nat.ceil_le.mpr (h1.trans h2)
  let centers : Finset ℕ := Finset.range (2 * k + 2)
  let E_j : ℕ → Set ℝ := fun j =>
    E ∩ Metric.closedBall
      (x - 2 * ε - r + 2 * (j : ℝ) * r) r
  have hδ_r : δ ≤ r := hδ_ρ.trans hρ_r
  let S1 : Set ℝ := E ∩ Metric.closedBall x (r + 2 * ε)
  let S2 : Set ℝ := ⋃ j ∈ centers, E_j j
  have h_split_ball :
      Metric.closedBall x (r + 2 * ε) ⊆
        ⋃ j ∈ centers,
          Metric.closedBall
            (x - 2 * ε - r + 2 * (j : ℝ) * r) r :=
    closedBall_split_2k2 hr_pos hδ_r (by linarith) h_kr
  have h_split1 : S1 ⊆ S2 := by
    intro z hz
    rcases Set.mem_iUnion₂.mp (h_split_ball hz.2) with ⟨j, hj, hzj⟩
    exact Set.mem_iUnion₂.mpr ⟨j, hj, ⟨hz.1, hzj⟩⟩
  have h_contain :
      B ∩ Metric.closedBall x r ⊆
        Metric.cthickening ε S1 :=
    thickening_inter_containment_general hε_pos hthick
  have h_cthick_union :
      Metric.cthickening ε S1 ⊆
        ⋃ j ∈ centers, Metric.cthickening ε (E_j j) := by
    have h1 :
        Metric.cthickening ε S1 ⊆ Metric.cthickening ε S2 := by
      intro y hy
      have h_inf : ∀ z ∈ S1, infEDist y S2 ≤ edist y z := by
        intro z hz
        exact Metric.infEDist_le_edist_of_mem (h_split1 hz)
      have h2 : infEDist y S2 ≤ infEDist y S1 := by
        simpa [Metric.infEDist, le_iInf_iff] using h_inf
      have h3 : infEDist y S1 ≤ ENNReal.ofReal ε := by
        simpa [Metric.cthickening] using hy
      exact h2.trans h3
    rwa [cthickening_finite_iUnion centers E_j] at h1
  have hB_sub :
      B ∩ Metric.closedBall x r ⊆
        ⋃ j ∈ centers, Metric.cthickening ε (E_j j) :=
    h_contain.trans h_cthick_union
  have h_finite_union :
      (↑(externalCoveringNumber eps_nn
        (⋃ j ∈ centers, Metric.cthickening ε (E_j j))) : ENNReal) ≤
        ∑ j ∈ centers,
          (↑(externalCoveringNumber eps_nn
            (Metric.cthickening ε (E_j j))) : ENNReal) :=
    externalCoveringNumber_finite_union_le centers
      (fun j => Metric.cthickening ε (E_j j))
  have h_main1 :
      externalCoveringNumber eps_nn
          (B ∩ Metric.closedBall x r) ≤
        externalCoveringNumber eps_nn
          (⋃ j ∈ centers, Metric.cthickening ε (E_j j)) :=
    externalCoveringNumber_mono_set hB_sub
  have h_each : ∀ j ∈ centers,
      (↑(externalCoveringNumber eps_nn
        (Metric.cthickening ε (E_j j))) : ENNReal) ≤
        (2 * k' + 2 : ENNReal) * C *
          Kakeya.realRpowENN (r / ρ) α := by
    intro j _
    have h_thick :
        (↑(externalCoveringNumber eps_nn
          (Metric.cthickening ε (E_j j))) : ENNReal) ≤
          (2 * k' + 2 : ENNReal) *
            ↑(externalCoveringNumber eps_nn (E_j j)) := by
      exact_mod_cast
        externalCoveringNumber_cthickening_general hε_pos hρ_pos
    have h_AD :
        (↑(externalCoveringNumber eps_nn (E_j j)) : ENNReal) ≤
          C * Kakeya.realRpowENN (r / ρ) α :=
      hcover ρ hρ hδ_ρ hρ_one
        (x - 2 * ε - r + 2 * (j : ℝ) * r) r hρ_r hr_one
    exact h_thick.trans (by
      calc
        (2 * k' + 2 : ENNReal) *
            ↑(externalCoveringNumber eps_nn (E_j j)) ≤
          (2 * k' + 2 : ENNReal) *
            (C * Kakeya.realRpowENN (r / ρ) α) := by gcongr
        _ = _ := by ring)
  have h_sum :
      ∑ j ∈ centers,
          (↑(externalCoveringNumber eps_nn
            (Metric.cthickening ε (E_j j))) : ENNReal) ≤
        (centers.card : ENNReal) * (2 * k' + 2 : ENNReal) *
          C * Kakeya.realRpowENN (r / ρ) α := by
    calc
      _ ≤ ∑ _j ∈ centers,
          ((2 * k' + 2 : ENNReal) * C *
            Kakeya.realRpowENN (r / ρ) α) :=
        Finset.sum_le_sum h_each
      _ = _ := by simp [centers, Finset.sum_const] <;> ring
  have h_centers_card : centers.card = 2 * k + 2 := by
    simp [centers] <;> omega
  have hK_eq :
      (K : ENNReal) =
        (2 * (Nat.ceil (ε / δ) + 1) : ENNReal) := by
    simp [K, k] <;> norm_cast
  have h_final :
      (centers.card : ENNReal) * (2 * k' + 2 : ENNReal) ≤
        (K : ENNReal) ^ 2 := by
    have h_card' :
        (centers.card : ENNReal) = 2 * (k : ENNReal) + 2 := by
      rw [h_centers_card] <;> norm_cast <;> ring
    rw [h_card']
    have h1 :
        (2 * (k : ENNReal) + 2) * (2 * (k' : ENNReal) + 2) ≤
          (2 * (k : ENNReal) + 2) * (2 * (k : ENNReal) + 2) := by
      gcongr <;> exact_mod_cast hk'_le
    have h2 : 2 * (k : ENNReal) + 2 = (K : ENNReal) := by
      simp [K] <;> norm_cast <;> ring
    calc
      (2 * (k : ENNReal) + 2) * (2 * (k' : ENNReal) + 2) ≤
          (2 * (k : ENNReal) + 2) * (2 * (k : ENNReal) + 2) := h1
      _ = (K : ENNReal) ^ 2 := by rw [h2, pow_two]
  calc
    (↑(externalCoveringNumber eps_nn
        (B ∩ Metric.closedBall x r)) : ENNReal) ≤
        ↑(externalCoveringNumber eps_nn
          (⋃ j ∈ centers, Metric.cthickening ε (E_j j))) := by
      exact_mod_cast h_main1
    _ ≤ ∑ j ∈ centers,
        (↑(externalCoveringNumber eps_nn
          (Metric.cthickening ε (E_j j))) : ENNReal) := h_finite_union
    _ ≤ (centers.card : ENNReal) * (2 * k' + 2 : ENNReal) *
        C * Kakeya.realRpowENN (r / ρ) α := h_sum
    _ ≤ (K : ENNReal) ^ 2 * C *
        Kakeya.realRpowENN (r / ρ) α := by
      gcongr
    _ = (2 * (Nat.ceil (ε / δ) + 1) : ENNReal) ^ 2 *
        C * Kakeya.realRpowENN (r / ρ) α := by rw [hK_eq]

end Kakeya.Assouad
