module

/-
  Conversion lemma: IsSetBetweenScales → IsFinsetDeltaSSet

  Converts the between-scales s-set property at scales (δ, 1) to the
  discrete s-set property on DSquare finsets (Euclidean metric on corners).

  Used in the Prop73 base case (n=1), where Δ₀=1 so the single block
  spans the full scale range.

  Output constant: conversionKGeo s * C, where conversionKGeo s = 2000 * 2^s.
  The actual geometric factor is ≤ 810 for C ≥ 1, and 2000*2^s ≥ 2000 > 810.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicConversion
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate

/-- Geometric constant for the IsSetBetweenScales → IsFinsetDeltaSSet conversion. -/
def conversionKGeo (s : ℝ) : ℝ := 2000 * Real.rpow 2 s

/-- Each coordinate difference is bounded by the Euclidean distance. -/
lemma coord_le_dist {x y : EuclideanPlane} (i : Fin 2) : |y i - x i| ≤ dist y x := by
  have h1 : dist y x = ‖y - x‖ := by rfl
  rw [h1]
  have h2 : ‖y - x‖ ^ 2 = ∑ j : Fin 2, |(y - x) j| ^ 2 := by
    have h3 : ‖y - x‖ = Real.sqrt (∑ j : Fin 2, |(y - x) j| ^ 2) := by
      simpa [EuclideanSpace.norm_eq, norm_natAbs] using rfl
    rw [h3]
    rw [Real.sq_sqrt] <;> positivity
  have h4 : |(y - x) i| ^ 2 ≤ ‖y - x‖ ^ 2 := by
    rw [h2]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (|(y - x) j|)) (Finset.mem_univ i)
  have h5 : 0 ≤ |(y - x) i| := abs_nonneg _
  have h6 : 0 ≤ ‖y - x‖ := norm_nonneg _
  have h7 : |(y - x) i| ≤ ‖y - x‖ := by nlinarith
  exact h7

/-- External covering number is subadditive under binary union. -/
lemma externalCoveringNumber_union_le {X : Type*} [PseudoMetricSpace X] {ε : NNReal} {A B : Set X} :
    Metric.externalCoveringNumber ε (A ∪ B) ≤
      Metric.externalCoveringNumber ε A + Metric.externalCoveringNumber ε B := by
  let nA := Metric.externalCoveringNumber ε A
  let nB := Metric.externalCoveringNumber ε B
  have h_union_cover : ∀ (CA : Set X), Metric.IsCover ε A CA →
      ∀ (CB : Set X), Metric.IsCover ε B CB →
      Metric.externalCoveringNumber ε (A ∪ B) ≤ CA.encard + CB.encard := by
    intro CA hCA CB hCB
    have hCA' : Metric.IsCover ε A (CA ∪ CB) := hCA.mono (by simp)
    have hCB' : Metric.IsCover ε B (CA ∪ CB) := hCB.mono (by simp)
    have h1 : Metric.IsCover ε (A ∪ B) (CA ∪ CB) := by
      simp only [Metric.IsCover, SetRel.IsCover] at *
      intro z hz
      cases hz with
      | inl hzA => exact hCA' hzA
      | inr hzB => exact hCB' hzB
    have h2 : Metric.externalCoveringNumber ε (A ∪ B) ≤ (CA ∪ CB).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard h1
    have h3 : (CA ∪ CB).encard ≤ CA.encard + CB.encard := Set.encard_union_le _ _
    exact le_trans h2 h3
  have h4 : ∀ (CB : Set X), Metric.IsCover ε B CB →
      Metric.externalCoveringNumber ε (A ∪ B) ≤ nA + CB.encard := by
    intro CB hCB
    have h5 : ∀ (CA : Set X), Metric.IsCover ε A CA →
        Metric.externalCoveringNumber ε (A ∪ B) ≤ CA.encard + CB.encard :=
      fun CA hCA => h_union_cover CA hCA CB hCB
    have h6 : Metric.externalCoveringNumber ε (A ∪ B) ≤
        ⨅ (CA : Set X) (_ : Metric.IsCover ε A CA), CA.encard + CB.encard :=
      le_iInf₂ h5
    have h7 : (⨅ (CA : Set X) (_ : Metric.IsCover ε A CA), CA.encard + CB.encard) =
        nA + CB.encard := by
      have h71 : (⨅ (CA : Set X) (_ : Metric.IsCover ε A CA), CA.encard + CB.encard) =
          (⨅ (CA : Set X), (⨅ (_ : Metric.IsCover ε A CA), CA.encard) + CB.encard) := by
        congr; funext CA
        have h : (⨅ (_ : Metric.IsCover ε A CA), CA.encard + CB.encard) =
            (⨅ (_ : Metric.IsCover ε A CA), CA.encard) + CB.encard := by exact Eq.symm ENat.iInf_add
        exact h
      rw [h71]
      have h72 : (⨅ (CA : Set X), (⨅ (_ : Metric.IsCover ε A CA), CA.encard) + CB.encard) =
          (⨅ (CA : Set X) (_ : Metric.IsCover ε A CA), CA.encard) + CB.encard := by
        rw [ENat.iInf_add]
      rw [h72] <;> rfl
    rw [h7] at h6
    exact h6
  have h9 : Metric.externalCoveringNumber ε (A ∪ B) ≤
      ⨅ (CB : Set X) (_ : Metric.IsCover ε B CB), nA + CB.encard :=
    le_iInf₂ h4
  have h10 : (⨅ (CB : Set X) (_ : Metric.IsCover ε B CB), nA + CB.encard) = nA + nB := by
    have h101 : (⨅ (CB : Set X) (_ : Metric.IsCover ε B CB), nA + CB.encard) =
        (⨅ (CB : Set X), nA + (⨅ (_ : Metric.IsCover ε B CB), CB.encard)) := by
      congr; funext CB
      have h : (⨅ (_ : Metric.IsCover ε B CB), nA + CB.encard) =
          nA + (⨅ (_ : Metric.IsCover ε B CB), CB.encard) := by exact Eq.symm ENat.add_iInf
      exact h
    rw [h101]
    have h102 : (⨅ (CB : Set X), nA + (⨅ (_ : Metric.IsCover ε B CB), CB.encard)) =
        nA + (⨅ (CB : Set X) (_ : Metric.IsCover ε B CB), CB.encard) := by
      have h_comm : ∀ (CB : Set X), nA + (⨅ (_ : Metric.IsCover ε B CB), CB.encard) =
          (⨅ (_ : Metric.IsCover ε B CB), CB.encard) + nA := by
        intro CB; exact add_comm _ _
      have h_eq : (⨅ (CB : Set X), nA + (⨅ (_ : Metric.IsCover ε B CB), CB.encard)) =
          (⨅ (CB : Set X), (⨅ (_ : Metric.IsCover ε B CB), CB.encard) + nA) := by
        congr; funext CB; exact h_comm CB
      rw [h_eq]
      let g : Set X → ENat := fun CB => ⨅ (_ : Metric.IsCover ε B CB), CB.encard
      have h_iinf_add : (⨅ (CB : Set X), g CB + nA) = iInf g + nA := by
        exact Eq.symm (ENat.iInf_add (f := g) (a := nA))
      rw [h_iinf_add] <;> abel
    rw [h102] <;> rfl
  rw [h10] at h9
  exact h9

/-- External covering number of finite union ≤ sum of covering numbers. -/
lemma externalCoveringNumber_biUnion_le {X : Type*} [PseudoMetricSpace X] {ε : NNReal}
    {ι : Type*} (S : Finset ι) (A : ι → Set X) :
    Metric.externalCoveringNumber ε (⋃ i ∈ S, A i) ≤
      ∑ i ∈ S, Metric.externalCoveringNumber ε (A i) := by
  have h0 : Metric.externalCoveringNumber ε (∅ : Set X) = 0 :=
    Metric.externalCoveringNumber_empty ε
  have h : Metric.externalCoveringNumber ε (⋃ i ∈ S, A i) ≤
      ∑ i ∈ S, Metric.externalCoveringNumber ε (A i) :=
    Finset.apply_union_le_sum h0 (fun {s t} => externalCoveringNumber_union_le) (s := A) (t := S)
  exact h

/-- Coercion from ENat to ENNReal preserves finite sums. -/
lemma ennreal_coe_finset_sum {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ENat} :
    (↑(∑ i ∈ s, f i) : ENNReal) = ∑ i ∈ s, (↑(f i) : ENNReal) := by
  have h_add : ∀ (x y : ENat), (↑(x + y) : ENNReal) = (↑x : ENNReal) + (↑y : ENNReal) := by
    intro x y
    cases x with
    | top =>
      cases y with
      | top => simp
      | coe yn => simp
    | coe xn =>
      cases y with
      | top => simp
      | coe yn =>
        simp [ENat.coe_add, Nat.cast_add] <;> norm_cast
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h_add, ih]

/-- A closed ball of radius r < 1 intersects at most 9 unit dyadic squares. -/
lemma ball_intersects_9_unit_squares'' (x : EuclideanPlane) {r : ℝ} (hr : r < 1) (hr0 : 0 ≤ r) :
    ∃ (S : Finset (ℤ × ℤ)), S.card ≤ 9 ∧
      ∀ (i j : ℤ), (Metric.closedBall x r ∩ dyadicSquare 1 i j).Nonempty → (i, j) ∈ S := by
  let i0 : ℤ := ⌊x 0⌋
  let j0 : ℤ := ⌊x 1⌋
  let S : Finset (ℤ × ℤ) := (Finset.Icc (i0 - 1) (i0 + 1)) ×ˢ (Finset.Icc (j0 - 1) (j0 + 1))
  have hcard : S.card ≤ 9 := by
    have h1 : (Finset.Icc (i0 - 1) (i0 + 1)).card = 3 := by simp [Finset.card_eq_zero] <;> omega
    have h2 : (Finset.Icc (j0 - 1) (j0 + 1)).card = 3 := by simp [Finset.card_eq_zero] <;> omega
    simp [S, Finset.card_product, h1, h2] <;> omega
  refine ⟨S, hcard, ?_⟩
  intro i j hne
  rcases hne with ⟨y, hyball, hysq⟩
  have hysq' : y 0 ∈ Set.Ico ((i : ℝ)) ((i : ℝ) + 1) ∧ y 1 ∈ Set.Ico ((j : ℝ)) ((j : ℝ) + 1) := by
    simpa [dyadicSquare, one_mul] using hysq
  have hdist : dist y x ≤ r := hyball
  have hx0 : |y 0 - x 0| ≤ r := by
    have h : |y 0 - x 0| ≤ dist y x := coord_le_dist 0
    exact h.trans hdist
  have hx1 : |y 1 - x 1| ≤ r := by
    have h : |y 1 - x 1| ≤ dist y x := coord_le_dist 1
    exact h.trans hdist
  have hi0_le : (i0 : ℝ) ≤ x 0 := Int.floor_le (x 0)
  have hi0_gt : x 0 < (i0 : ℝ) + 1 := Int.lt_floor_add_one (x 0)
  have hj0_le : (j0 : ℝ) ≤ x 1 := Int.floor_le (x 1)
  have hj0_gt : x 1 < (j0 : ℝ) + 1 := Int.lt_floor_add_one (x 1)
  have h_i1 : i0 - 1 ≤ i := by
    by_contra h; push Not at h
    have h_int : i ≤ i0 - 2 := by omega
    have h_y : y 0 < (i0 - 1 : ℝ) := by
      have h1 : y 0 < (i : ℝ) + 1 := hysq'.1.2
      have h2 : (i : ℝ) ≤ (i0 - 2 : ℝ) := by exact_mod_cast h_int
      linarith
    have h_x : (i0 : ℝ) ≤ x 0 := hi0_le
    have h9 : y 0 < x 0 := by linarith
    have h10 : |y 0 - x 0| = x 0 - y 0 := by
      rw [abs_of_neg (show y 0 - x 0 < 0 by linarith)] <;> linarith
    rw [h10] at hx0
    linarith [hr]
  have h_i2 : i ≤ i0 + 1 := by
    by_contra h; push Not at h
    have h_int : i ≥ i0 + 2 := by omega
    have h_y : y 0 ≥ (i0 + 2 : ℝ) := by
      have h1 : (i : ℝ) ≤ y 0 := hysq'.1.1
      have h2 : (i0 + 2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast h_int
      linarith
    have h_x : x 0 < (i0 + 1 : ℝ) := hi0_gt
    have h9 : x 0 < y 0 := by linarith
    have h10 : |y 0 - x 0| = y 0 - x 0 := by
      rw [abs_of_pos (show 0 < y 0 - x 0 by linarith)]
    rw [h10] at hx0
    linarith [hr]
  have h_j1 : j0 - 1 ≤ j := by
    by_contra h; push Not at h
    have h_int : j ≤ j0 - 2 := by omega
    have h_y : y 1 < (j0 - 1 : ℝ) := by
      have h1 : y 1 < (j : ℝ) + 1 := hysq'.2.2
      have h2 : (j : ℝ) ≤ (j0 - 2 : ℝ) := by exact_mod_cast h_int
      linarith
    have h_x : (j0 : ℝ) ≤ x 1 := hj0_le
    have h9 : y 1 < x 1 := by linarith
    have h10 : |y 1 - x 1| = x 1 - y 1 := by
      rw [abs_of_neg (show y 1 - x 1 < 0 by linarith)] <;> linarith
    rw [h10] at hx1
    linarith [hr]
  have h_j2 : j ≤ j0 + 1 := by
    by_contra h; push Not at h
    have h_int : j ≥ j0 + 2 := by omega
    have h_y : y 1 ≥ (j0 + 2 : ℝ) := by
      have h1 : (j : ℝ) ≤ y 1 := hysq'.2.1
      have h2 : (j0 + 2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h_int
      linarith
    have h_x : x 1 < (j0 + 1 : ℝ) := hj0_gt
    have h9 : x 1 < y 1 := by linarith
    have h10 : |y 1 - x 1| = y 1 - x 1 := by
      rw [abs_of_pos (show 0 < y 1 - x 1 by linarith)]
    rw [h10] at hx1
    linarith [hr]
  have h_i_in : i ∈ Finset.Icc (i0 - 1) (i0 + 1) := by
    simp only [Finset.mem_Icc] <;> omega
  have h_j_in : j ∈ Finset.Icc (j0 - 1) (j0 + 1) := by
    simp only [Finset.mem_Icc] <;> omega
  exact Finset.mem_product.mpr ⟨h_i_in, h_j_in⟩

/-- External covering number is preserved by a surjective isometry. -/
lemma externalCoveringNumber_image_of_isometry {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} (hf : Isometry f) (hsurj : Function.Surjective f)
    (A : Set X) (ε : NNReal) :
    Metric.externalCoveringNumber ε (f '' A) = Metric.externalCoveringNumber ε A := by
  have h1 : Metric.externalCoveringNumber ε (f '' A) ≤ Metric.externalCoveringNumber ε A := by
    apply le_iInf₂
    intro C hC
    have hCov : Metric.IsCover ε (f '' A) (f '' C) := (hf.isCover_image_iff C).mpr hC
    have h_inj : Set.InjOn f C := fun x _ y _ hxy => hf.injective hxy
    have h2 : (f '' C).encard = C.encard := Set.InjOn.encard_image h_inj
    have h3 : Metric.externalCoveringNumber ε (f '' A) ≤ (f '' C).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hCov
    rw [h2] at h3
    exact h3
  have h2 : Metric.externalCoveringNumber ε A ≤ Metric.externalCoveringNumber ε (f '' A) := by
    apply le_iInf₂
    intro D hD
    let C' : Set X := f ⁻¹' D
    have h_range : D ⊆ Set.range f := by simp [hsurj.range_eq]
    have hC' : f '' C' = D := by
      rw [Set.image_preimage_eq_iff] <;> exact h_range
    have hCov : Metric.IsCover ε A C' := by
      have h3 : Metric.IsCover ε (f '' A) D := hD
      rw [←hC'] at h3
      exact (hf.isCover_image_iff C').mp h3
    have h_inj' : Set.InjOn f C' := fun x _ y _ hxy => hf.injective hxy
    have h4 : (f '' C').encard = C'.encard := Set.InjOn.encard_image h_inj'
    have h5 : C'.encard = D.encard := by
      rw [←h4, hC']
    have h7 : Metric.externalCoveringNumber ε A ≤ C'.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hCov
    rw [h5] at h7
    exact h7
  exact le_antisymm h1 h2

/-- S-set property is invariant under translation. -/
lemma isDeltaSSet_of_translated'' {δ s C : ℝ} {P : Set EuclideanPlane} {v : EuclideanPlane}
    (h : IsDeltaSSet δ s C ((fun p : EuclideanPlane => p - v) '' P)) :
    IsDeltaSSet δ s C P := by
  let e : EuclideanPlane → EuclideanPlane := fun p => p - v
  have h_iso : Isometry e := by
    rw [isometry_iff_dist_eq]
    intro x y
    simp [e, dist_eq_norm] <;> abel
  have h_surj : Function.Surjective e := by
    intro y
    refine ⟨y + v, ?_⟩
    simp [e] <;> abel
  have h_main : ∀ (x : EuclideanPlane) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
    intro x r hr
    have h1 : e '' (P ∩ Metric.closedBall x r) =
        (e '' P) ∩ Metric.closedBall (e x) r := by
      ext y; simp only [Set.mem_image, Set.mem_inter_iff]
      constructor
      · rintro ⟨z, ⟨hzP, hzball⟩, rfl⟩
        exact ⟨⟨z, hzP, rfl⟩, by simpa [e] using hzball⟩
      · rintro ⟨⟨z, hzP, rfl⟩, hball⟩
        exact ⟨z, ⟨hzP, by simpa [e] using hball⟩, rfl⟩
    have h2 := h.2.2.2.2 (e x) r hr
    rw [←h1] at h2
    have h3 : (Metric.externalCoveringNumber δ.toNNReal (e '' (P ∩ Metric.closedBall x r)) : ENNReal) =
        (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) := by
      rw [externalCoveringNumber_image_of_isometry h_iso h_surj]
    have h4 : (Metric.externalCoveringNumber δ.toNNReal (e '' P) : ENNReal) =
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
      rw [externalCoveringNumber_image_of_isometry h_iso h_surj]
    rw [h3, h4] at h2; exact h2
  have hP_nonempty : P.Nonempty := by
    rcases h.1 with ⟨y, ⟨x, hx, rfl⟩⟩
    exact ⟨x, hx⟩
  exact ⟨hP_nonempty, h.2.1, h.2.2.1, h.2.2.2.1, h_main⟩

/-- Weaken the constant in an IsFinsetDeltaSSet. -/
lemma finset_deltaSSet_weaken_constant {X : Type*} [MetricSpace X] {δ s C C' : ℝ}
    {P : Finset X} (h : IsDeltaSSet δ s C (P : Set X)) (hC : C ≤ C') :
    IsDeltaSSet δ s C' (P : Set X) := by
  have hC'_pos : 0 < C' := by linarith [h.2.2.1]
  refine ⟨h.1, h.2.1, hC'_pos, h.2.2.2.1, fun x r hr => ?_⟩
  have h5 := h.2.2.2.2 x r hr
  calc (Metric.externalCoveringNumber δ.toNNReal ((P : Set X) ∩ Metric.closedBall x r) : ENNReal)
    ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal (P : Set X) : ENNReal) := h5
  _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal (P : Set X) : ENNReal) := by
    gcongr

/-- Finite-case helper: |P| ≤ 9 * |𝒞| when each ball contains ≤ 9 points. -/
lemma finset_card_le_9_times_cover_finite {X : Type*} [MetricSpace X] [DecidableEq X] {ε : NNReal} {P : Finset X} {𝒞 : Set X}
    (h9 : ∀ (A : Finset X) (c : X), (A.filter (fun q => dist q c ≤ (ε : ℝ))).card ≤ 9)
    (hcover : Metric.IsCover ε (P : Set X) 𝒞)
    (hCfin : Set.Finite 𝒞) :
    (P.card : ENat) ≤ (9 : ENat) * 𝒞.encard := by
  let Cfin : Finset X := hCfin.toFinset
  have h2 : (Cfin : Set X) = 𝒞 := Set.Finite.coe_toFinset hCfin
  have h3 : ∀ c ∈ Cfin, (P.filter (fun q => dist q c ≤ (ε : ℝ))).card ≤ 9 :=
    fun c _ => h9 P c
  let B : Finset X := Cfin.biUnion (fun c => P.filter (fun q => dist q c ≤ (ε : ℝ)))
  have h4 : P ⊆ B := by
    intro q hq
    rcases hcover hq with ⟨c, hc, hedist⟩
    have hcin : c ∈ Cfin := by
      have hset : c ∈ (Cfin : Set X) := by
        exact h2 ▸ hc
      exact hset
    have hdist : dist q c ≤ (ε : ℝ) := by
      have h5 : edist q c ≤ (ε : ENNReal) := by simpa using hedist
      have h6 : edist q c = ENNReal.ofReal (dist q c) := by exact edist_dist q c
      have h7 : (ε : ENNReal) = ENNReal.ofReal ((ε : ℝ)) := by simp
      rw [h6, h7] at h5
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h5
    have h6 : q ∈ P.filter (fun q => dist q c ≤ (ε : ℝ)) := by
      simp only [Finset.mem_filter] <;> exact ⟨hq, hdist⟩
    exact Finset.mem_biUnion.mpr ⟨c, hcin, h6⟩
  have h6 : P.card ≤ B.card := Finset.card_le_card h4
  have h7 : B.card ≤ ∑ c ∈ Cfin, (P.filter (fun q => dist q c ≤ (ε : ℝ))).card :=
    Finset.card_biUnion_le
  have h8 : ∑ c ∈ Cfin, (P.filter (fun q => dist q c ≤ (ε : ℝ))).card ≤ ∑ c ∈ Cfin, 9 :=
    Finset.sum_le_sum h3
  have h9' : ∑ c ∈ Cfin, (9 : ℕ) = 9 * Cfin.card := by
    simp [Finset.sum_const] <;> ring
  rw [h9'] at h8
  have h10 : (P.card : ENat) ≤ (9 * Cfin.card : ENat) := by
    exact_mod_cast le_trans (le_trans h6 h7) h8
  have h11 : 𝒞.encard = (Cfin.card : ENat) := by
    rw [←h2] <;> simp
  rw [h11] <;> exact h10

/-- |P| ≤ 9 * Ncover(P) when each ε-ball contains ≤ 9 points of P. -/
lemma finset_card_le_9_times_cover {X : Type*} [MetricSpace X] [DecidableEq X] {ε : NNReal} {P : Finset X}
    (h9 : ∀ (A : Finset X) (c : X), (A.filter (fun q => dist q c ≤ (ε : ℝ))).card ≤ 9) :
    (P.card : ENat) ≤ (9 : ENat) * Metric.externalCoveringNumber ε (P : Set X) := by
  have h_main : ∀ (𝒞 : Set X), Metric.IsCover ε (P : Set X) 𝒞 →
      (P.card : ENat) ≤ (9 : ENat) * 𝒞.encard := by
    intro 𝒞 hcover
    by_cases hCfin : Set.Finite 𝒞
    · exact finset_card_le_9_times_cover_finite h9 hcover hCfin
    · have h10 : 𝒞.encard = ⊤ := by
        rw [Set.encard_eq_top_iff] <;> exact hCfin
      rw [h10] <;> simp
  have h_iInf : (P.card : ENat) ≤
      ⨅ (𝒞 : Set X) (_ : Metric.IsCover ε (P : Set X) 𝒞), (9 : ENat) * 𝒞.encard :=
    le_iInf₂ h_main
  have h_step1 : ∀ (𝒞 : Set X),
      (⨅ (_ : Metric.IsCover ε (P : Set X) 𝒞), (9 : ENat) * 𝒞.encard) =
      (9 : ENat) * (⨅ (_ : Metric.IsCover ε (P : Set X) 𝒞), 𝒞.encard) := by
    intro 𝒞
    rw [ENat.mul_iInf_of_ne (by norm_num : (9 : ENat) ≠ 0)]
  have h_step2 : (⨅ (𝒞 : Set X), (9 : ENat) * (⨅ (_ : Metric.IsCover ε (P : Set X) 𝒞), 𝒞.encard)) =
      (9 : ENat) * (⨅ (𝒞 : Set X), (⨅ (_ : Metric.IsCover ε (P : Set X) 𝒞), 𝒞.encard)) := by
    rw [←ENat.mul_iInf_of_ne (by norm_num : (9 : ENat) ≠ 0)]
  have h_eq : (⨅ (𝒞 : Set X) (_ : Metric.IsCover ε (P : Set X) 𝒞), (9 : ENat) * 𝒞.encard) =
      (9 : ENat) * Metric.externalCoveringNumber ε (P : Set X) := by
    have h_eq1 : (⨅ (𝒞 : Set X) (_ : Metric.IsCover ε (P : Set X) 𝒞), (9 : ENat) * 𝒞.encard) =
        ⨅ (𝒞 : Set X), (9 : ENat) * (⨅ (_ : Metric.IsCover ε (P : Set X) 𝒞), 𝒞.encard) := by
      apply congr_arg (fun g => iInf g)
      funext 𝒞
      exact h_step1 𝒞
    rw [h_eq1]
    have h9_ne : (9 : ENat) ≠ 0 := by norm_num
    rw [←ENat.mul_iInf_of_ne h9_ne]
    <;> rfl
  rw [h_eq] at h_iInf
  exact h_iInf

/-- Finite-case helper for image: |A| ≤ 9 * |𝒞| when each ball contains ≤ 9 image-points. -/
lemma finset_card_le_9_times_cover_image_finite {X Y : Type*} [MetricSpace X] [MetricSpace Y] [DecidableEq X]
    {ε : NNReal} {A : Finset X} {f : X → Y} {S : Set Y} {𝒞 : Set Y}
    (h9 : ∀ (B : Finset X) (c : Y), (B.filter (fun q => dist (f q) c ≤ (ε : ℝ))).card ≤ 9)
    (h_image : f '' (A : Set X) ⊆ S)
    (hcover : Metric.IsCover ε S 𝒞)
    (hCfin : Set.Finite 𝒞) :
    (A.card : ENat) ≤ (9 : ENat) * 𝒞.encard := by
  let Cfin : Finset Y := hCfin.toFinset
  have h2 : (Cfin : Set Y) = 𝒞 := Set.Finite.coe_toFinset hCfin
  have h3 : ∀ c ∈ Cfin, (A.filter (fun q => dist (f q) c ≤ (ε : ℝ))).card ≤ 9 :=
    fun c _ => h9 A c
  let B : Finset X := Cfin.biUnion (fun c => A.filter (fun q => dist (f q) c ≤ (ε : ℝ)))
  have h4 : A ⊆ B := by
    intro q hq
    have hfq : f q ∈ f '' (A : Set X) := ⟨q, hq, rfl⟩
    have hfs : f q ∈ S := h_image hfq
    rcases hcover hfs with ⟨c, hc, hedist⟩
    have hcin : c ∈ Cfin := by
      have hset : c ∈ (Cfin : Set Y) := by exact h2 ▸ hc
      exact hset
    have hdist : dist (f q) c ≤ (ε : ℝ) := by
      have h5 : edist (f q) c ≤ (ε : ENNReal) := by simpa using hedist
      have h6 : edist (f q) c = ENNReal.ofReal (dist (f q) c) := by exact edist_dist (f q) c
      have h7 : (ε : ENNReal) = ENNReal.ofReal ((ε : ℝ)) := by simp
      rw [h6, h7] at h5
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h5
    have h8 : q ∈ A.filter (fun q => dist (f q) c ≤ (ε : ℝ)) := by
      simp only [Finset.mem_filter] <;> exact ⟨hq, hdist⟩
    exact Finset.mem_biUnion.mpr ⟨c, hcin, h8⟩
  have h6 : A.card ≤ B.card := Finset.card_le_card h4
  have h7 : B.card ≤ ∑ c ∈ Cfin, (A.filter (fun q => dist (f q) c ≤ (ε : ℝ))).card :=
    Finset.card_biUnion_le
  have h8 : ∑ c ∈ Cfin, (A.filter (fun q => dist (f q) c ≤ (ε : ℝ))).card ≤ ∑ c ∈ Cfin, 9 :=
    Finset.sum_le_sum h3
  have h9' : ∑ c ∈ Cfin, (9 : ℕ) = 9 * Cfin.card := by
    simp [Finset.sum_const] <;> ring
  rw [h9'] at h8
  have h10 : (A.card : ENat) ≤ (9 * Cfin.card : ENat) := by
    exact_mod_cast le_trans (le_trans h6 h7) h8
  have h11 : 𝒞.encard = (Cfin.card : ENat) := by
    rw [←h2] <;> simp
  rw [h11] <;> exact h10

/-- |A| ≤ 9 * Ncover(S) when f '' A ⊆ S and each ε-ball contains ≤ 9 image-points. -/
lemma finset_card_le_9_times_cover_image {X Y : Type*} [MetricSpace X] [MetricSpace Y] [DecidableEq X]
    {ε : NNReal} {A : Finset X} {f : X → Y} {S : Set Y}
    (h9 : ∀ (B : Finset X) (c : Y), (B.filter (fun q => dist (f q) c ≤ (ε : ℝ))).card ≤ 9)
    (h_image : f '' (A : Set X) ⊆ S) :
    (A.card : ENat) ≤ (9 : ENat) * Metric.externalCoveringNumber ε S := by
  have h_main : ∀ (𝒞 : Set Y), Metric.IsCover ε S 𝒞 →
      (A.card : ENat) ≤ (9 : ENat) * 𝒞.encard := by
    intro 𝒞 hcover
    by_cases hCfin : Set.Finite 𝒞
    · exact finset_card_le_9_times_cover_image_finite h9 h_image hcover hCfin
    · have h10 : 𝒞.encard = ⊤ := by
        rw [Set.encard_eq_top_iff] <;> exact hCfin
      rw [h10] <;> simp
  have h_iInf : (A.card : ENat) ≤
      ⨅ (𝒞 : Set Y) (_ : Metric.IsCover ε S 𝒞), (9 : ENat) * 𝒞.encard :=
    le_iInf₂ h_main
  have h_step1 : ∀ (𝒞 : Set Y),
      (⨅ (_ : Metric.IsCover ε S 𝒞), (9 : ENat) * 𝒞.encard) =
      (9 : ENat) * (⨅ (_ : Metric.IsCover ε S 𝒞), 𝒞.encard) := by
    intro 𝒞
    rw [ENat.mul_iInf_of_ne (by norm_num : (9 : ENat) ≠ 0)]
  have h_step2 : (⨅ (𝒞 : Set Y), (9 : ENat) * (⨅ (_ : Metric.IsCover ε S 𝒞), 𝒞.encard)) =
      (9 : ENat) * (⨅ (𝒞 : Set Y), (⨅ (_ : Metric.IsCover ε S 𝒞), 𝒞.encard)) := by
    rw [←ENat.mul_iInf_of_ne (by norm_num : (9 : ENat) ≠ 0)]
  have h_eq : (⨅ (𝒞 : Set Y) (_ : Metric.IsCover ε S 𝒞), (9 : ENat) * 𝒞.encard) =
      (9 : ENat) * Metric.externalCoveringNumber ε S := by
    have h_eq1 : (⨅ (𝒞 : Set Y) (_ : Metric.IsCover ε S 𝒞), (9 : ENat) * 𝒞.encard) =
        ⨅ (𝒞 : Set Y), (9 : ENat) * (⨅ (_ : Metric.IsCover ε S 𝒞), 𝒞.encard) := by
      apply congr_arg (fun g => iInf g)
      funext 𝒞
      exact h_step1 𝒞
    rw [h_eq1]
    have h9_ne : (9 : ENat) ≠ 0 := by norm_num
    rw [←ENat.mul_iInf_of_ne h9_ne]
    <;> rfl
  rw [h_eq] at h_iInf
  exact h_iInf

/-- Conversion: IsSetBetweenScales at scales (δ,1) implies the DSquare
    finset is a δ-s-set with explicit constant conversionKGeo s * C. -/
theorem isSetBetweenScales_to_isFinsetDeltaSSet
    {k : ℕ} {s C : ℝ} {P₀ : Finset (DyadicSquare k)}
    (hP_nonempty : P₀.Nonempty) (hs : 0 ≤ s)
    (h : IsSetBetweenScales (⋃ p ∈ P₀, (p.toSet : Set EuclideanPlane))
        (dyadicDelta k) 1 s C) :
    IsFinsetDeltaSSet (dyadicDelta k) s (conversionKGeo s * C)
      (finsetDyadicToDSquare P₀) := by
  set δ : ℝ := dyadicDelta k with hδ_def
  have hδ_pos : 0 < δ := dyadicDelta_pos k
  have hδ_le1 : δ ≤ 1 := dyadicDelta_le_one k
  have hC_pos : 0 < C := h.2.2.2.2.1
  let P : Set EuclideanPlane := ⋃ p ∈ P₀, (p.toSet : Set EuclideanPlane)
  let PS : Finset (DSquare k) := finsetDyadicToDSquare P₀
  let ε : NNReal := δ.toNNReal
  have hε_pos : ε ≠ 0 := by
    simp [ε, hδ_pos.ne'] <;> linarith
  have hε_eq : (ε : ℝ) = δ := by
    simp [ε, show 0 ≤ δ by linarith] <;> linarith
  have hP_nonempty' : P.Nonempty := by
    rcases hP_nonempty with ⟨p, hp⟩
    have hpt : (p.toSet : Set EuclideanPlane).Nonempty := DyadicSquare.toSet_nonempty p
    exact hpt.mono (Set.subset_biUnion_of_mem hp)

  -- C ≥ 1: take a point in P, find its unit square, apply S-set with r=1
  have hC_ge1 : 1 ≤ C := by
    rcases hP_nonempty with ⟨p, hp⟩
    rcases DyadicSquare.toSet_nonempty p with ⟨x, hx⟩
    have hxP : x ∈ P := Set.subset_biUnion_of_mem hp hx
    let i : ℤ := ⌊x 0⌋
    let j : ℤ := ⌊x 1⌋
    have hx_unit : x ∈ dyadicSquare 1 i j := by
      have h1 : (i : ℝ) ≤ x 0 := Int.floor_le (x 0)
      have h2 : x 0 < (i : ℝ) + 1 := Int.lt_floor_add_one (x 0)
      have h3 : (j : ℝ) ≤ x 1 := Int.floor_le (x 1)
      have h4 : x 1 < (j : ℝ) + 1 := Int.lt_floor_add_one (x 1)
      have h5 : x 0 ∈ Set.Ico ((i : ℝ)) ((i : ℝ) + 1) := ⟨h1, h2⟩
      have h6 : x 1 ∈ Set.Ico ((j : ℝ)) ((j : ℝ) + 1) := ⟨h3, h4⟩
      simpa [dyadicSquare, one_mul] using ⟨h5, h6⟩
    have hsq_nonempty : (P ∩ dyadicSquare 1 i j).Nonempty := ⟨x, hxP, hx_unit⟩
    have h1 := h.2.2.2.2.2 i j hsq_nonempty
    have hδ1 : δ / 1 = δ := by ring
    rw [hδ1] at h1
    let v : EuclideanPlane := WithLp.toLp (2 : ENNReal) ![ (i : ℝ), (j : ℝ)]
    have h_hom : ∀ (q : EuclideanPlane), homothetyS 1 i j q = q - v := by
      intro q; simp [homothetyS, v] <;> ext idx; fin_cases idx <;> simp <;> ring
    have h_image : homothetyS 1 i j '' (P ∩ dyadicSquare 1 i j) =
        (fun q => q - v) '' (P ∩ dyadicSquare 1 i j) := by
      congr; funext q; exact h_hom q
    rw [h_image] at h1
    have h2 : IsDeltaSSet δ s C (P ∩ dyadicSquare 1 i j) :=
      isDeltaSSet_of_translated'' h1
    have hne : (P ∩ dyadicSquare 1 i j).Nonempty := hsq_nonempty
    let N : ENNReal := ↑(Metric.externalCoveringNumber ε (P ∩ dyadicSquare 1 i j))
    have hN_pos : 0 < N := by
      have h_ne : (Metric.externalCoveringNumber ε (P ∩ dyadicSquare 1 i j)) ≠ 0 :=
        (Metric.externalCoveringNumber_pos_iff.mpr hne).ne'
      have h_coe_ne : (↑(Metric.externalCoveringNumber ε (P ∩ dyadicSquare 1 i j)) : ENNReal) ≠ 0 := by
        exact_mod_cast h_ne
      exact h_coe_ne.bot_lt
    have h_tb : TotallyBounded (P ∩ dyadicSquare 1 i j) := by
      let center : EuclideanPlane := WithLp.toLp (2 : ENNReal) ![ (i : ℝ) + 1 / 2, (j : ℝ) + 1 / 2]
      have h_sub1 : dyadicSquare 1 i j ⊆ Metric.closedBall center 1 := by
        intro z hz
        have hz1 : (i : ℝ) ≤ z 0 ∧ z 0 < (i : ℝ) + 1 := by
          simpa [dyadicSquare, one_mul] using hz.1
        have hz2 : (j : ℝ) ≤ z 1 ∧ z 1 < (j : ℝ) + 1 := by
          simpa [dyadicSquare, one_mul] using hz.2
        have h : dist z center ≤ 1 := by
          simp [center, dist_eq_norm, EuclideanSpace.norm_eq] <;> norm_num <;> nlinarith [sq_nonneg (z 0 - ((i : ℝ) + 1 / 2)), sq_nonneg (z 1 - ((j : ℝ) + 1 / 2))]
        exact h
      have h_sub2 : P ∩ dyadicSquare 1 i j ⊆ Metric.closedBall center 1 :=
        Set.inter_subset_right.trans h_sub1
      have h_compact : IsCompact (Metric.closedBall center 1) := by exact isCompact_closedBall center 1
      have h_tb_ball : TotallyBounded (Metric.closedBall center 1) := h_compact.totallyBounded
      exact TotallyBounded.subset h_sub2 h_tb_ball
    have hN_fin : N ≠ ⊤ := by
      rcases Metric.exists_finite_isCover_of_totallyBounded hε_pos h_tb with ⟨D, _, hDfin, hDcover⟩
      have h : (Metric.externalCoveringNumber ε (P ∩ dyadicSquare 1 i j)) ≤ D.encard :=
        Metric.IsCover.externalCoveringNumber_le_encard hDcover
      have h2 : D.encard ≠ ⊤ := (Set.Finite.encard_lt_top hDfin).ne
      have h3 : (Metric.externalCoveringNumber ε (P ∩ dyadicSquare 1 i j)) ≠ ⊤ :=
        ne_top_of_le_ne_top h2 h
      dsimp only [N]
      exact_mod_cast h3
    let center : EuclideanPlane := WithLp.toLp (2 : ENNReal) ![ (i : ℝ) + 1 / 2, (j : ℝ) + 1 / 2]
    have h4 : P ∩ dyadicSquare 1 i j ⊆ Metric.closedBall center 1 := by
      intro z hz
      have hz' : z ∈ dyadicSquare 1 i j := hz.2
      have hz1 : (i : ℝ) ≤ z 0 ∧ z 0 < (i : ℝ) + 1 := by
        simpa [dyadicSquare, one_mul] using hz'.1
      have hz2 : (j : ℝ) ≤ z 1 ∧ z 1 < (j : ℝ) + 1 := by
        simpa [dyadicSquare, one_mul] using hz'.2
      have h : dist z center ≤ 1 := by
        simp [center, dist_eq_norm, EuclideanSpace.norm_eq]
        <;> norm_num <;> nlinarith [sq_nonneg (z 0 - ((i : ℝ) + 1 / 2)),
          sq_nonneg (z 1 - ((j : ℝ) + 1 / 2))]
      exact h
    have h5 := h2.2.2.2.2 center 1 (by linarith [hδ_le1])
    have h_inter_eq : (P ∩ dyadicSquare 1 i j) ∩ Metric.closedBall center 1 = P ∩ dyadicSquare 1 i j :=
      Set.inter_eq_left.mpr h4
    have h6 : N ≤ ENNReal.ofReal C * (ENNReal.ofReal (1 : ℝ)) ^ s * N := by
      have h7 : (Metric.externalCoveringNumber ε ((P ∩ dyadicSquare 1 i j) ∩ Metric.closedBall center 1)) = N := by
        rw [h_inter_eq]
      rw [h7] at h5; exact h5
    have h9 : (ENNReal.ofReal (1 : ℝ)) ^ s = 1 := by simp
    rw [h9] at h6
    have h10 : N ≤ ENNReal.ofReal C * N := by simpa using h6
    by_contra h11
    have h12 : C < 1 := by linarith
    have h13 : ENNReal.ofReal C < 1 := by
      have h14 : ENNReal.ofReal C < ENNReal.ofReal (1 : ℝ) :=
        ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr h12
      simpa using h14
    have h15 : ENNReal.ofReal C * N < 1 * N := ENNReal.mul_lt_mul_left hN_pos.ne' hN_fin h13
    have h16 : ENNReal.ofReal C * N < N := by simpa [one_mul] using h15
    have h17 : ¬(N ≤ ENNReal.ofReal C * N) := not_le.mpr h16
    exact h17 h10

  -- Per-unit-square S-set property
  have h_per_square : ∀ (i j : ℤ), (P ∩ dyadicSquare 1 i j).Nonempty →
      IsDeltaSSet δ s C (P ∩ dyadicSquare 1 i j) := by
    intro i j hne
    have h1 := h.2.2.2.2.2 i j hne
    have hδ1 : δ / 1 = δ := by ring
    rw [hδ1] at h1
    let v : EuclideanPlane := WithLp.toLp (2 : ENNReal) ![ (i : ℝ), (j : ℝ)]
    have h_hom : ∀ (q : EuclideanPlane), homothetyS 1 i j q = q - v := by
      intro q; simp [homothetyS, v] <;> ext idx; fin_cases idx <;> simp <;> ring
    have h_image : homothetyS 1 i j '' (P ∩ dyadicSquare 1 i j) =
        (fun q => q - v) '' (P ∩ dyadicSquare 1 i j) := by
      congr; funext q; exact h_hom q
    rw [h_image] at h1
    exact isDeltaSSet_of_translated'' h1

  -- Global S-set for P with constant 10*C (valid since C ≥ 1)
  let C_eucl : ℝ := 10 * C
  have hC_eucl_pos : 0 < C_eucl := by positivity
  have h_global : IsDeltaSSet δ s C_eucl P := by
    refine ⟨hP_nonempty', hδ_pos, hC_eucl_pos, hs, fun x r hr => ?_⟩
    by_cases hr1 : r < 1
    · rcases ball_intersects_9_unit_squares'' x hr1 (by linarith) with ⟨S, hS9, hS_mem⟩
      let A : (ℤ × ℤ) → Set EuclideanPlane := fun p =>
        P ∩ dyadicSquare 1 p.1 p.2 ∩ Metric.closedBall x r
      have h_cover : P ∩ Metric.closedBall x r ⊆ ⋃ p ∈ S, A p := by
        intro z hz
        have hz1 : z ∈ P := hz.1
        have hz2 : z ∈ Metric.closedBall x r := hz.2
        have h_in_square : ∃ (i j : ℤ), z ∈ dyadicSquare 1 i j := by
          refine ⟨⌊z 0⌋, ⌊z 1⌋, ?_⟩
          simp only [dyadicSquare]
          constructor
          · exact ⟨by simpa [one_mul] using Int.floor_le (z 0), by simpa [one_mul] using Int.lt_floor_add_one (z 0)⟩
          · exact ⟨by simpa [one_mul] using Int.floor_le (z 1), by simpa [one_mul] using Int.lt_floor_add_one (z 1)⟩
        rcases h_in_square with ⟨i, j, hzsq⟩
        have h_inter : (Metric.closedBall x r ∩ dyadicSquare 1 i j).Nonempty := ⟨z, hz2, hzsq⟩
        have h_in_S : (i, j) ∈ S := hS_mem i j h_inter
        have h_goal : z ∈ A (i, j) := ⟨⟨hz1, hzsq⟩, hz2⟩
        have h_bunion : z ∈ (⋃ p ∈ S, A p) := by
          simp only [Set.mem_iUnion]
          exact ⟨(i, j), h_in_S, h_goal⟩
        exact h_bunion
      have h_sum : (Metric.externalCoveringNumber ε (P ∩ Metric.closedBall x r) : ENNReal) ≤
          ∑ p ∈ S, (Metric.externalCoveringNumber ε (A p) : ENNReal) := by
        have hmono : (Metric.externalCoveringNumber ε (P ∩ Metric.closedBall x r) : ENNReal) ≤
            (Metric.externalCoveringNumber ε (⋃ p ∈ S, A p) : ENNReal) := by
          exact_mod_cast Metric.externalCoveringNumber_mono_set h_cover
        have h_raw : Metric.externalCoveringNumber ε (⋃ p ∈ S, A p) ≤
            ∑ p ∈ S, Metric.externalCoveringNumber ε (A p) :=
          externalCoveringNumber_biUnion_le S A
        have h_coe_sum : (↑(∑ p ∈ S, Metric.externalCoveringNumber ε (A p)) : ENNReal) =
            ∑ p ∈ S, (Metric.externalCoveringNumber ε (A p) : ENNReal) :=
          ennreal_coe_finset_sum (s := S) (f := Metric.externalCoveringNumber ε ∘ A)
        have hunion : (Metric.externalCoveringNumber ε (⋃ p ∈ S, A p) : ENNReal) ≤
            ∑ p ∈ S, (Metric.externalCoveringNumber ε (A p) : ENNReal) := by
          have h' : (Metric.externalCoveringNumber ε (⋃ p ∈ S, A p) : ENNReal) ≤
              (↑(∑ p ∈ S, Metric.externalCoveringNumber ε (A p)) : ENNReal) := by
            exact_mod_cast h_raw
          rw [h_coe_sum] at h'
          exact h'
        exact le_trans hmono hunion
      have h1 : ∀ p ∈ S, (Metric.externalCoveringNumber ε (A p) : ENNReal) ≤
          ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber ε P : ENNReal) := by
        intro p hp
        by_cases hne : (P ∩ dyadicSquare 1 p.1 p.2).Nonempty
        · have h4 : IsDeltaSSet δ s C (P ∩ dyadicSquare 1 p.1 p.2) := h_per_square p.1 p.2 hne
          have h5 := h4.2.2.2.2 x r hr
          have h7 : (Metric.externalCoveringNumber ε (P ∩ dyadicSquare 1 p.1 p.2)) ≤
              Metric.externalCoveringNumber ε P :=
            Metric.externalCoveringNumber_mono_set Set.inter_subset_left
          have h7' : (Metric.externalCoveringNumber ε (P ∩ dyadicSquare 1 p.1 p.2) : ENNReal) ≤
              (Metric.externalCoveringNumber ε P : ENNReal) := by
            exact_mod_cast h7
          have hA : A p = P ∩ dyadicSquare 1 p.1 p.2 ∩ Metric.closedBall x r := by
            simp [A]
          have hA_eq' : (Metric.externalCoveringNumber ε (A p) : ENNReal) =
              (Metric.externalCoveringNumber ε (P ∩ dyadicSquare 1 p.1 p.2 ∩ Metric.closedBall x r) : ENNReal) := by
            rw [hA]
          calc (Metric.externalCoveringNumber ε (A p) : ENNReal)
            = (Metric.externalCoveringNumber ε (P ∩ dyadicSquare 1 p.1 p.2 ∩ Metric.closedBall x r) : ENNReal) := hA_eq'
          _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
                (Metric.externalCoveringNumber ε (P ∩ dyadicSquare 1 p.1 p.2) : ENNReal) := h5
          _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
                (Metric.externalCoveringNumber ε P : ENNReal) := by
            gcongr <;> exact h7'
        · have h_empty : P ∩ dyadicSquare 1 p.1 p.2 = ∅ := by
            simpa [Set.not_nonempty_iff_eq_empty] using hne
          have hA_empty : A p = ∅ := by simp [A, h_empty]
          rw [hA_empty] <;> simp
      have h_sum2 : ∑ p ∈ S, (Metric.externalCoveringNumber ε (A p) : ENNReal) ≤
          (S.card : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber ε P : ENNReal) := by
        have h_sum3 : ∑ p ∈ S, (Metric.externalCoveringNumber ε (A p) : ENNReal) ≤
            ∑ p ∈ S, (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
                  (Metric.externalCoveringNumber ε P : ENNReal)) :=
          Finset.sum_le_sum fun p hp => h1 p hp
        have h_sum4 : ∑ p ∈ S, (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
                  (Metric.externalCoveringNumber ε P : ENNReal)) =
            (S.card : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
              (Metric.externalCoveringNumber ε P : ENNReal) := by
          rw [Finset.sum_const] <;> ring
        rw [h_sum4] at h_sum3
        exact h_sum3
      have h_S9 : (S.card : ENNReal) ≤ (9 : ENNReal) := by exact_mod_cast hS9
      have h_main1 : (Metric.externalCoveringNumber ε (P ∩ Metric.closedBall x r) : ENNReal) ≤
          (9 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber ε P : ENNReal) := by
        calc (Metric.externalCoveringNumber ε (P ∩ Metric.closedBall x r) : ENNReal)
          ≤ ∑ p ∈ S, (Metric.externalCoveringNumber ε (A p) : ENNReal) := h_sum
        _ ≤ (S.card : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
              (Metric.externalCoveringNumber ε P : ENNReal) := h_sum2
        _ ≤ (9 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
              (Metric.externalCoveringNumber ε P : ENNReal) := by gcongr <;> exact h_S9
      have h10 : (9 : ENNReal) * ENNReal.ofReal C ≤ ENNReal.ofReal C_eucl := by
        have h11 : (9 : ℝ) * C ≤ C_eucl := by dsimp only [C_eucl] <;> linarith
        have h12 : (9 : ENNReal) * ENNReal.ofReal C = ENNReal.ofReal ((9 : ℝ) * C) := by
          simp [ENNReal.ofReal_mul] <;> ring
        rw [h12]
        exact ENNReal.ofReal_le_ofReal h11
      calc (Metric.externalCoveringNumber ε (P ∩ Metric.closedBall x r) : ENNReal)
        ≤ (9 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber ε P : ENNReal) := h_main1
      _ ≤ ENNReal.ofReal C_eucl * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber ε P : ENNReal) := by
          gcongr <;> exact h10
    · have hr_ge1 : r ≥ 1 := by linarith
      have h1 : (Metric.externalCoveringNumber ε (P ∩ Metric.closedBall x r) : ENNReal) ≤
          (Metric.externalCoveringNumber ε P : ENNReal) := by
        exact_mod_cast Metric.externalCoveringNumber_mono_set Set.inter_subset_left
      have h2 : (1 : ENNReal) ≤ ENNReal.ofReal C_eucl * (ENNReal.ofReal r) ^ s := by
        have h3 : (1 : ENNReal) ≤ ENNReal.ofReal C_eucl := by
          have h4 : (1 : ℝ) ≤ C_eucl := by dsimp only [C_eucl] <;> linarith [hC_ge1]
          simpa [ENNReal.ofReal_le_ofReal] using h4
        have h4 : (1 : ENNReal) ≤ (ENNReal.ofReal r) ^ s := by
          have h5 : (1 : ℝ) ≤ r := by linarith
          have h6 : (1 : ENNReal) ≤ ENNReal.ofReal r := by
            simpa [ENNReal.ofReal_le_ofReal] using h5
          have h7 : (1 : ENNReal) ^ s ≤ (ENNReal.ofReal r) ^ s := ENNReal.rpow_le_rpow h6 hs
          simpa using h7
        calc (1 : ENNReal)
          ≤ (1 : ENNReal) * (1 : ENNReal) := by simp
        _ ≤ ENNReal.ofReal C_eucl * (ENNReal.ofReal r) ^ s := by gcongr
      calc (Metric.externalCoveringNumber ε (P ∩ Metric.closedBall x r) : ENNReal)
        ≤ (Metric.externalCoveringNumber ε P : ENNReal) := h1
      _ = (1 : ENNReal) * (Metric.externalCoveringNumber ε P : ENNReal) := by simp
      _ ≤ ENNReal.ofReal C_eucl * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber ε P : ENNReal) := by gcongr <;> exact h2

  -- Corner map
  let corner (p : DSquare k) : EuclideanPlane :=
    WithLp.toLp (2 : ENNReal) ![ (p.i : ℝ) * δ, (p.j : ℝ) * δ]
  have h_corner_in_P : ∀ (p : DSquare k), p ∈ PS → corner p ∈ P := by
    intro p hp
    have h2 : ∃ (a : DyadicSquare k), a ∈ P₀ ∧ dyadicSquareToDSquare a = p := by
      simpa [PS, finsetDyadicToDSquare, Finset.mem_image] using hp
    rcases h2 with ⟨a, ha, rfl⟩
    have h3 : corner (dyadicSquareToDSquare a) ∈ a.toSet := by
      have h_i1 : (a.i : ℝ) * δ ≤ (corner (dyadicSquareToDSquare a)) 0 := by
        simp [corner, dyadicSquareToDSquare]
      have h_i2 : (corner (dyadicSquareToDSquare a)) 0 < ((a.i : ℝ) + 1) * δ := by
        simp [corner, dyadicSquareToDSquare, hδ_pos] <;> linarith
      have h_j1 : (a.j : ℝ) * δ ≤ (corner (dyadicSquareToDSquare a)) 1 := by
        simp [corner, dyadicSquareToDSquare]
      have h_j2 : (corner (dyadicSquareToDSquare a)) 1 < ((a.j : ℝ) + 1) * δ := by
        simp [corner, dyadicSquareToDSquare, hδ_pos] <;> linarith
      exact ⟨h_i1, h_i2, h_j1, h_j2⟩
    exact Set.subset_biUnion_of_mem ha h3
  have h_corner_inj : Set.InjOn corner (PS : Set (DSquare k)) := by
    intro p _ q _ h
    have h_eq1 : (corner p) 0 = (corner q) 0 := by rw [h]
    have h_eq2 : (corner p) 1 = (corner q) 1 := by rw [h]
    have hi : (p.i : ℝ) * δ = (q.i : ℝ) * δ := by simpa [corner] using h_eq1
    have hj : (p.j : ℝ) * δ = (q.j : ℝ) * δ := by simpa [corner] using h_eq2
    have hi' : p.i = q.i := by
      have h : (p.i : ℝ) = (q.i : ℝ) := by
        apply mul_left_cancel₀ hδ_pos.ne'
        linarith
      exact_mod_cast h
    have hj' : p.j = q.j := by
      have h : (p.j : ℝ) = (q.j : ℝ) := by
        apply mul_left_cancel₀ hδ_pos.ne'
        linarith
      exact_mod_cast h
    cases p with | mk pi pj =>
    cases q with | mk qi qj =>
    have hi'' : pi = qi := hi'
    have hj'' : pj = qj := hj'
    have h_eq : (⟨pi, pj⟩ : DSquare k) = ⟨qi, qj⟩ := by
      congr <;> tauto
    exact h_eq

  -- Grid packing: at most 9 corner-points per δ-ball
  have h_grid9 : ∀ (A : Finset (DSquare k)) (c : EuclideanPlane),
      (A.filter (fun q => dist (corner q) c ≤ δ)).card ≤ 9 := by
    intro A c
    let i0 : ℤ := Int.floor (c 0 / δ)
    let j0 : ℤ := Int.floor (c 1 / δ)
    have h1 : ∀ (q : DSquare k), dist (corner q) c ≤ δ →
        q.i ∈ Finset.Icc (i0 - 1) (i0 + 1) ∧ q.j ∈ Finset.Icc (j0 - 1) (j0 + 1) := by
      intro q h2
      have h3 : |(q.i : ℝ) * δ - c 0| ≤ δ := by
        have h4 : |(corner q) 0 - c 0| ≤ dist (corner q) c := coord_le_dist 0
        simpa [corner] using h4.trans h2
      have h4 : |(q.j : ℝ) * δ - c 1| ≤ δ := by
        have h5 : |(corner q) 1 - c 1| ≤ dist (corner q) c := coord_le_dist 1
        simpa [corner] using h5.trans h2
      have h_abs1 : |(q.i : ℝ) - c 0 / δ| ≤ 1 := by
        have h5 : |(q.i : ℝ) * δ - c 0| = |(q.i : ℝ) - c 0 / δ| * δ := by
          have h6 : (q.i : ℝ) * δ - c 0 = ((q.i : ℝ) - c 0 / δ) * δ := by field_simp [hδ_pos.ne'] <;> ring
          rw [h6, abs_mul, abs_of_pos hδ_pos]
        rw [h5] at h3
        calc |(q.i : ℝ) - c 0 / δ|
          = (|(q.i : ℝ) - c 0 / δ| * δ) / δ := by field_simp [hδ_pos.ne'] <;> ring
        _ ≤ δ / δ := by gcongr
        _ = 1 := by field_simp [hδ_pos.ne']
      have h_abs2 : |(q.j : ℝ) - c 1 / δ| ≤ 1 := by
        have h5 : |(q.j : ℝ) * δ - c 1| = |(q.j : ℝ) - c 1 / δ| * δ := by
          have h6 : (q.j : ℝ) * δ - c 1 = ((q.j : ℝ) - c 1 / δ) * δ := by field_simp [hδ_pos.ne'] <;> ring
          rw [h6, abs_mul, abs_of_pos hδ_pos]
        rw [h5] at h4
        calc |(q.j : ℝ) - c 1 / δ|
          = (|(q.j : ℝ) - c 1 / δ| * δ) / δ := by field_simp [hδ_pos.ne'] <;> ring
        _ ≤ δ / δ := by gcongr
        _ = 1 := by field_simp [hδ_pos.ne']
      have h_i0_le : (i0 : ℝ) ≤ c 0 / δ := Int.floor_le (c 0 / δ)
      have h_i0_gt : c 0 / δ < (i0 + 1 : ℝ) := Int.lt_floor_add_one (c 0 / δ)
      have h_j0_le : (j0 : ℝ) ≤ c 1 / δ := Int.floor_le (c 1 / δ)
      have h_j0_gt : c 1 / δ < (j0 + 1 : ℝ) := Int.lt_floor_add_one (c 1 / δ)
      have h_il : i0 - 1 ≤ q.i := by
        have h : (i0 - 1 : ℝ) ≤ (q.i : ℝ) := by linarith [abs_sub_le_iff.mp h_abs1, h_i0_le]
        exact_mod_cast h
      have h_ir : q.i ≤ i0 + 1 := by
        have h : (q.i : ℝ) < (i0 + 2 : ℝ) := by linarith [abs_sub_le_iff.mp h_abs1, h_i0_gt]
        have h' : q.i < i0 + 2 := by exact_mod_cast h
        omega
      have h_jl : j0 - 1 ≤ q.j := by
        have h : (j0 - 1 : ℝ) ≤ (q.j : ℝ) := by linarith [abs_sub_le_iff.mp h_abs2, h_j0_le]
        exact_mod_cast h
      have h_jr : q.j ≤ j0 + 1 := by
        have h : (q.j : ℝ) < (j0 + 2 : ℝ) := by linarith [abs_sub_le_iff.mp h_abs2, h_j0_gt]
        have h' : q.j < j0 + 2 := by exact_mod_cast h
        omega
      simp only [Finset.mem_Icc]; exact ⟨⟨h_il, h_ir⟩, ⟨h_jl, h_jr⟩⟩
    let G : Finset (DSquare k) :=
      (Finset.Icc (i0 - 1) (i0 + 1) ×ˢ Finset.Icc (j0 - 1) (j0 + 1)).image
        (fun p : ℤ × ℤ => ⟨p.1, p.2⟩)
    have h5 : A.filter (fun q => dist (corner q) c ≤ δ) ⊆ G := by
      intro q hq
      have h6 := h1 q ((Finset.mem_filter.mp hq).2)
      exact Finset.mem_image.mpr ⟨(q.i, q.j), Finset.mem_product.mpr h6, by
        cases q <;> simp <;> rfl⟩
    have h7 : (A.filter (fun q => dist (corner q) c ≤ δ)).card ≤ G.card := Finset.card_le_card h5
    have h8 : G.card ≤ 9 := by
      have h9 : G.card ≤ (Finset.Icc (i0 - 1) (i0 + 1) ×ˢ Finset.Icc (j0 - 1) (j0 + 1)).card := Finset.card_image_le
      have h10 : (Finset.Icc (i0 - 1) (i0 + 1) ×ˢ Finset.Icc (j0 - 1) (j0 + 1)).card = 9 := by
        have h11 : (Finset.Icc (i0 - 1) (i0 + 1)).card = 3 := by simp [Finset.card_eq_zero] <;> omega
        have h12 : (Finset.Icc (j0 - 1) (j0 + 1)).card = 3 := by simp [Finset.card_eq_zero] <;> omega
        simp [Finset.card_product, h11, h12] <;> omega
      linarith
    linarith

  -- Ncover(P) ≤ |P₀|: each dyadic square covered by one δ-ball at its center
  have h_ncover_P_le_card : (Metric.externalCoveringNumber ε P : ENNReal) ≤ (P₀.card : ENNReal) := by
    let centers : Finset EuclideanPlane := P₀.image (fun p =>
      WithLp.toLp (2 : ENNReal) ![((p.i : ℝ) + 1 / 2) * δ, ((p.j : ℝ) + 1 / 2) * δ])
    have hcover : Metric.IsCover ε P (centers : Set EuclideanPlane) := by
      intro x hx
      have h_exists : ∃ (p : DyadicSquare k), p ∈ P₀ ∧ x ∈ (p.toSet : Set EuclideanPlane) := by
        simpa [P, Finset.mem_biUnion] using hx
      rcases h_exists with ⟨p, hp, hxp⟩
      let c : EuclideanPlane := WithLp.toLp (2 : ENNReal) ![((p.i : ℝ) + 1 / 2) * δ, ((p.j : ℝ) + 1 / 2) * δ]
      have hc_in : c ∈ (centers : Set EuclideanPlane) := Finset.mem_image.mpr ⟨p, hp, rfl⟩
      have hxp' : (p.i : ℝ) * δ ≤ x 0 ∧ x 0 < ((p.i : ℝ) + 1) * δ ∧
                 (p.j : ℝ) * δ ≤ x 1 ∧ x 1 < ((p.j : ℝ) + 1) * δ := by
        simpa [DyadicSquare.toSet, hδ_def] using hxp
      have h1 : |x 0 - c 0| ≤ δ / 2 := by
        simp [c, abs_sub_le_iff] <;> constructor <;> linarith [hxp'.1, hxp'.2.1]
      have h2 : |x 1 - c 1| ≤ δ / 2 := by
        simp [c, abs_sub_le_iff] <;> constructor <;> linarith [hxp'.2.2.1, hxp'.2.2.2]
      have h31 : (x 0 - c 0) ^ 2 ≤ (δ / 2) ^ 2 := by
        have h : (x 0 - c 0) ^ 2 = |x 0 - c 0| ^ 2 := by rw [sq_abs]
        rw [h] <;> gcongr
      have h32 : (x 1 - c 1) ^ 2 ≤ (δ / 2) ^ 2 := by
        have h : (x 1 - c 1) ^ 2 = |x 1 - c 1| ^ 2 := by rw [sq_abs]
        rw [h] <;> gcongr
      have h33 : (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 ≤ (δ / 2) ^ 2 + (δ / 2) ^ 2 := by linarith
      have hdist : dist x c ≤ (ε : ℝ) := by
        rw [hε_eq]
        have h_dist_eq : dist x c = Real.sqrt ((x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2) := by
          simp [dist_eq_norm, EuclideanSpace.norm_eq] <;> rfl
        rw [h_dist_eq]
        have h4 : Real.sqrt ((x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2) ≤ Real.sqrt ((δ / 2) ^ 2 + (δ / 2) ^ 2) :=
          Real.sqrt_le_sqrt h33
        have h5 : 0 ≤ δ := by linarith
        have h6 : (δ / 2) ^ 2 + (δ / 2) ^ 2 ≤ δ ^ 2 := by nlinarith
        have h7 : Real.sqrt ((δ / 2) ^ 2 + (δ / 2) ^ 2) ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt h6
        have h8 : Real.sqrt (δ ^ 2) = δ := Real.sqrt_sq h5
        linarith
      have hdist' : edist x c ≤ (ε : ENNReal) := by
        rw [edist_dist]
        have h_eq : (ε : ENNReal) = ENNReal.ofReal ((ε : ℝ)) := by simp
        rw [h_eq]
        exact ENNReal.ofReal_le_ofReal hdist
      exact ⟨c, hc_in, hdist'⟩
    have h : Metric.externalCoveringNumber ε P ≤ (centers : Set EuclideanPlane).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hcover
    have h2 : (centers : Set EuclideanPlane).encard ≤ (P₀.card : ENat) := by
      exact_mod_cast Finset.card_image_le
    have h3 : Metric.externalCoveringNumber ε P ≤ (P₀.card : ENat) := le_trans h h2
    exact_mod_cast h3

  -- |PS| ≤ 9 * Ncover(PS)
  have h9_PS : ∀ (A : Finset (DSquare k)) (c : DSquare k),
      (A.filter (fun q => dist q c ≤ (ε : ℝ))).card ≤ 9 := by
    intro A c
    have h4 : ∀ q ∈ A, dist q c ≤ (ε : ℝ) →
        q.i ∈ Finset.Icc (c.i - 1) (c.i + 1) ∧
        q.j ∈ Finset.Icc (c.j - 1) (c.j + 1) := by
      intro q _ hdist
      have hδ_eq2 : DiscretisedFurstenbergEstimate.δ k = δ := by
        simp [DiscretisedFurstenbergEstimate.δ, dyadicDelta, hδ_def] <;> norm_cast
      have h_max : dist q c = δ * max |(q.i : ℝ) - (c.i : ℝ)| |(q.j : ℝ) - (c.j : ℝ)| := by
        have h_dist_def : dist q c = dist q.toPoint c.toPoint := by rfl
        rw [h_dist_def]
        have h : dist q.toPoint c.toPoint = max (dist q.toPoint.1 c.toPoint.1) (dist q.toPoint.2 c.toPoint.2) := by
          exact Prod.dist_eq
        rw [h]
        have h1 : dist q.toPoint.1 c.toPoint.1 = |(q.i : ℝ) - (c.i : ℝ)| * δ := by
          simp [DSquare.toPoint, Real.dist_eq, hδ_eq2]
          have h_eq : (q.i : ℝ) * δ - (c.i : ℝ) * δ = ((q.i : ℝ) - (c.i : ℝ)) * δ := by ring
          rw [h_eq, abs_mul, abs_of_pos hδ_pos] <;> ring
        have h2 : dist q.toPoint.2 c.toPoint.2 = |(q.j : ℝ) - (c.j : ℝ)| * δ := by
          simp [DSquare.toPoint, Real.dist_eq, hδ_eq2]
          have h_eq : (q.j : ℝ) * δ - (c.j : ℝ) * δ = ((q.j : ℝ) - (c.j : ℝ)) * δ := by ring
          rw [h_eq, abs_mul, abs_of_pos hδ_pos] <;> ring
        have h3 : max (|(q.i : ℝ) - (c.i : ℝ)| * δ) (|(q.j : ℝ) - (c.j : ℝ)| * δ) =
            δ * max |(q.i : ℝ) - (c.i : ℝ)| |(q.j : ℝ) - (c.j : ℝ)| := by
          have h4 : |(q.i : ℝ) - (c.i : ℝ)| * δ = δ * |(q.i : ℝ) - (c.i : ℝ)| := by ring
          have h5 : |(q.j : ℝ) - (c.j : ℝ)| * δ = δ * |(q.j : ℝ) - (c.j : ℝ)| := by ring
          rw [h4, h5]
          have hδnonneg : 0 ≤ δ := by positivity
          let a := |(q.i : ℝ) - (c.i : ℝ)|
          let b := |(q.j : ℝ) - (c.j : ℝ)|
          cases' le_total a b with h h
          · have h1 : δ * a ≤ δ * b := by gcongr
            rw [max_eq_right h1, max_eq_right h] <;> ring
          · have h2 : δ * b ≤ δ * a := by gcongr
            rw [max_eq_left h2, max_eq_left h] <;> ring
        rw [h1, h2, h3]
      have h5 : max |(q.i : ℝ) - (c.i : ℝ)| |(q.j : ℝ) - (c.j : ℝ)| ≤ 1 := by
        rw [h_max, hε_eq] at hdist
        have h9 : δ * max |(q.i : ℝ) - (c.i : ℝ)| |(q.j : ℝ) - (c.j : ℝ)| ≤ δ := hdist
        have h10 : 0 < δ := hδ_pos
        by_contra h11
        have h12 : 1 < max |(q.i : ℝ) - (c.i : ℝ)| |(q.j : ℝ) - (c.j : ℝ)| := by linarith
        have h13 : δ < δ * max |(q.i : ℝ) - (c.i : ℝ)| |(q.j : ℝ) - (c.j : ℝ)| := by
          have h14 : δ * (1 : ℝ) < δ * max |(q.i : ℝ) - (c.i : ℝ)| |(q.j : ℝ) - (c.j : ℝ)| :=
            mul_lt_mul_of_pos_left h12 h10
          have h15 : δ * (1 : ℝ) = δ := by ring
          rw [h15] at h14
          exact h14
        linarith
      have h7 : |(q.i : ℝ) - (c.i : ℝ)| ≤ 1 := le_trans (le_max_left _ _) h5
      have h8 : |(q.j : ℝ) - (c.j : ℝ)| ≤ 1 := le_trans (le_max_right _ _) h5
      have h_il : c.i - 1 ≤ q.i := by
        have h7' : -1 ≤ (q.i : ℝ) - (c.i : ℝ) := (abs_le.mp h7).1
        have h : (c.i - 1 : ℝ) ≤ (q.i : ℝ) := by linarith
        exact_mod_cast h
      have h_ir : q.i ≤ c.i + 1 := by
        have h7' : (q.i : ℝ) - (c.i : ℝ) ≤ 1 := (abs_le.mp h7).2
        have h : (q.i : ℝ) ≤ (c.i + 1 : ℝ) := by linarith
        exact_mod_cast h
      have h_jl : c.j - 1 ≤ q.j := by
        have h8' : -1 ≤ (q.j : ℝ) - (c.j : ℝ) := (abs_le.mp h8).1
        have h : (c.j - 1 : ℝ) ≤ (q.j : ℝ) := by linarith
        exact_mod_cast h
      have h_jr : q.j ≤ c.j + 1 := by
        have h8' : (q.j : ℝ) - (c.j : ℝ) ≤ 1 := (abs_le.mp h8).2
        have h : (q.j : ℝ) ≤ (c.j + 1 : ℝ) := by linarith
        exact_mod_cast h
      simp only [Finset.mem_Icc]
      exact ⟨⟨h_il, h_ir⟩, ⟨h_jl, h_jr⟩⟩
    let Gc : Finset (DSquare k) :=
      (Finset.Icc (c.i - 1) (c.i + 1) ×ˢ Finset.Icc (c.j - 1) (c.j + 1)).image
        (fun p : ℤ × ℤ => ⟨p.1, p.2⟩)
    have h5 : A.filter (fun q => dist q c ≤ (ε : ℝ)) ⊆ Gc := by
      intro q hq
      have h9 := h4 q (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2
      exact Finset.mem_image.mpr ⟨(q.i, q.j), Finset.mem_product.mpr h9, by
        cases q <;> simp <;> rfl⟩
    have h10 : (A.filter (fun q => dist q c ≤ (ε : ℝ))).card ≤ Gc.card := Finset.card_le_card h5
    have h11 : Gc.card ≤ 9 := by
      have h12 : Gc.card ≤ (Finset.Icc (c.i - 1) (c.i + 1) ×ˢ Finset.Icc (c.j - 1) (c.j + 1)).card := Finset.card_image_le
      have h13 : (Finset.Icc (c.i - 1) (c.i + 1) ×ˢ Finset.Icc (c.j - 1) (c.j + 1)).card = 9 := by
        have h14 : (Finset.Icc (c.i - 1) (c.i + 1)).card = 3 := by simp [Finset.card_eq_zero] <;> omega
        have h15 : (Finset.Icc (c.j - 1) (c.j + 1)).card = 3 := by simp [Finset.card_eq_zero] <;> omega
        simp [Finset.card_product, h14, h15] <;> omega
      linarith
    linarith
  have h_PS_card_le_cover : (PS.card : ENNReal) ≤
      (9 : ENNReal) * Metric.externalCoveringNumber ε (PS : Set (DSquare k)) := by
    have h : (PS.card : ENat) ≤ (9 : ENat) * Metric.externalCoveringNumber ε (PS : Set (DSquare k)) :=
      finset_card_le_9_times_cover h9_PS
    exact_mod_cast h

  -- Main S-set bound for PS (with 2r correction: Euclidean dist ≤ 2 * DSquare dist)
  let C_geo : ℝ := 81 * C_eucl * (2 : ℝ) ^ s
  have hC_geo_pos : 0 < C_geo := by positivity
  have h_main : IsDeltaSSet δ s C_geo (PS : Set (DSquare k)) := by
    refine ⟨?_, hδ_pos, hC_geo_pos, hs, fun p r hr => ?_⟩
    · have h1 : (PS : Set (DSquare k)).Nonempty := by
        rcases hP_nonempty with ⟨p, hp⟩
        exact ⟨dyadicSquareToDSquare p, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
      exact h1
    · let x : EuclideanPlane := corner p
      let A_sup : Finset (DSquare k) := PS.filter (fun q => dist q p ≤ r)
      have hA_sup_eq : (A_sup : Set (DSquare k)) = (PS : Set (DSquare k)) ∩ Metric.closedBall p r := by
        ext q; simp [A_sup]
      have h2r : δ ≤ 2 * r := by linarith
      have h_dist2 : ∀ (q : DSquare k), dist q p ≤ r → dist (corner q) x ≤ 2 * r := by
        intro q hq
        set v := corner q - x with hv
        have hδk : DiscretisedFurstenbergEstimate.δ k = δ := by
          simp [DiscretisedFurstenbergEstimate.δ, dyadicDelta, hδ_def] <;> norm_cast
        have h1 : |v 0| ≤ dist q p := by
          have h_eq : v 0 = (q.i : ℝ) * δ - (p.i : ℝ) * δ := by simp [v, corner, x] <;> ring
          rw [h_eq]
          have h_dist : dist q p = max (|(q.i : ℝ) * δ - (p.i : ℝ) * δ|) (|(q.j : ℝ) * δ - (p.j : ℝ) * δ|) := by
            have h_def : dist q p = dist q.toPoint p.toPoint := by rfl
            rw [h_def, Prod.dist_eq]
            have h11 : q.toPoint.1 = (q.i : ℝ) * DiscretisedFurstenbergEstimate.δ k := by
              simp [DSquare.toPoint]
            have h12 : p.toPoint.1 = (p.i : ℝ) * DiscretisedFurstenbergEstimate.δ k := by
              simp [DSquare.toPoint]
            have h21 : q.toPoint.2 = (q.j : ℝ) * DiscretisedFurstenbergEstimate.δ k := by
              simp [DSquare.toPoint]
            have h22 : p.toPoint.2 = (p.j : ℝ) * DiscretisedFurstenbergEstimate.δ k := by
              simp [DSquare.toPoint]
            rw [h11, h12, h21, h22, Real.dist_eq, Real.dist_eq, hδk] <;> rfl
          rw [h_dist]
          exact le_max_left _ _
        have h2 : |v 1| ≤ dist q p := by
          have h_eq : v 1 = (q.j : ℝ) * δ - (p.j : ℝ) * δ := by simp [v, corner, x] <;> ring
          rw [h_eq]
          have h_dist : dist q p = max (|(q.i : ℝ) * δ - (p.i : ℝ) * δ|) (|(q.j : ℝ) * δ - (p.j : ℝ) * δ|) := by
            have h_def : dist q p = dist q.toPoint p.toPoint := by rfl
            rw [h_def, Prod.dist_eq]
            have h11 : q.toPoint.1 = (q.i : ℝ) * DiscretisedFurstenbergEstimate.δ k := by
              simp [DSquare.toPoint]
            have h12 : p.toPoint.1 = (p.i : ℝ) * DiscretisedFurstenbergEstimate.δ k := by
              simp [DSquare.toPoint]
            have h21 : q.toPoint.2 = (q.j : ℝ) * DiscretisedFurstenbergEstimate.δ k := by
              simp [DSquare.toPoint]
            have h22 : p.toPoint.2 = (p.j : ℝ) * DiscretisedFurstenbergEstimate.δ k := by
              simp [DSquare.toPoint]
            rw [h11, h12, h21, h22, Real.dist_eq, Real.dist_eq, hδk] <;> rfl
          rw [h_dist]
          exact le_max_right _ _
        have h3 : dist (corner q) x ≤ |v 0| + |v 1| := by
          have h4 : dist (corner q) x = ‖v‖ := by simp [dist_eq_norm, hv] <;> rfl
          rw [h4]
          have h5 : ‖v‖ ^ 2 = |v 0| ^ 2 + |v 1| ^ 2 := by
            have h6 : ‖v‖ = Real.sqrt (∑ i : Fin 2, |v i| ^ 2) := by
              simpa [EuclideanSpace.norm_eq, norm_natAbs] using rfl
            have h7 : 0 ≤ ∑ i : Fin 2, |v i| ^ 2 := by positivity
            rw [h6, Real.sq_sqrt h7] <;> simp [Fin.sum_univ_two] <;> ring
          have h7 : ‖v‖ ^ 2 ≤ (|v 0| + |v 1|) ^ 2 := by
            rw [h5]
            have h8 : 0 ≤ |v 0| := abs_nonneg _
            have h9 : 0 ≤ |v 1| := abs_nonneg _
            have h10 : |v 0| ^ 2 + |v 1| ^ 2 ≤ (|v 0| + |v 1|) ^ 2 := by
              have h11 : (|v 0| + |v 1|) ^ 2 = |v 0| ^ 2 + 2 * |v 0| * |v 1| + |v 1| ^ 2 := by ring
              rw [h11]
              have h12 : 0 ≤ 2 * |v 0| * |v 1| := by positivity
              linarith
            exact h10
          have h10 : 0 ≤ ‖v‖ := norm_nonneg _
          have h11 : 0 ≤ |v 0| + |v 1| := by positivity
          nlinarith [h7, h10, h11]
        have h4 : |v 0| + |v 1| ≤ 2 * dist q p := by linarith
        have h5 : dist (corner q) x ≤ 2 * dist q p := le_trans h3 h4
        linarith
      have h1 : corner '' (A_sup : Set (DSquare k)) ⊆ P ∩ Metric.closedBall x (2 * r) := by
        intro y hy
        rcases hy with ⟨q, hq, rfl⟩
        have hq' : q ∈ PS := (Finset.mem_filter.mp hq).1
        have hdist : dist q p ≤ r := (Finset.mem_filter.mp hq).2
        have h3 : dist (corner q) x ≤ 2 * r := h_dist2 q hdist
        exact ⟨h_corner_in_P q hq', by simpa using h3⟩
      have h9_image : ∀ (B : Finset (DSquare k)) (c : EuclideanPlane),
          (B.filter (fun q => dist (corner q) c ≤ (ε : ℝ))).card ≤ 9 := by
        intro B c
        have h_eq : (B.filter (fun q => dist (corner q) c ≤ (ε : ℝ))) =
            B.filter (fun q => dist (corner q) c ≤ δ) := by
          ext q; simp [hε_eq]
        rw [h_eq]
        exact h_grid9 B c
      have h_grid_bound : (A_sup.card : ENat) ≤
          (9 : ENat) * Metric.externalCoveringNumber ε (P ∩ Metric.closedBall x (2 * r)) :=
        finset_card_le_9_times_cover_image h9_image h1
      have h6 := h_global.2.2.2.2 x (2 * r) h2r
      have h_rpow2 : (ENNReal.ofReal (2 * r)) ^ s =
          (2 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s := by
        have h_pos1 : 0 ≤ (2 * r : ℝ) := by linarith
        have h_pos2 : 0 ≤ (r : ℝ) := by linarith
        have h : ENNReal.ofReal (2 * r) = (2 : ENNReal) * ENNReal.ofReal r := by
          have h2 : ENNReal.ofReal (2 * r) = ENNReal.ofReal 2 * ENNReal.ofReal r := by
            rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
            <;> norm_num
          simpa using h2
        rw [h]
        have h_rpow : ((2 : ENNReal) * ENNReal.ofReal r) ^ s =
            (2 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s := by exact ENNReal.mul_rpow_of_nonneg 2 (ENNReal.ofReal r) hs
        exact h_rpow
      have h_first : (Metric.externalCoveringNumber ε (A_sup : Set (DSquare k)) : ENNReal) ≤ (A_sup.card : ENNReal) := by
        have h_self_cover : Metric.IsCover ε (A_sup : Set (DSquare k)) (A_sup : Set (DSquare k)) := by
          intro x hx
          exact ⟨x, hx, by simp⟩
        have h_le : Metric.externalCoveringNumber ε (A_sup : Set (DSquare k)) ≤ (A_sup : Set (DSquare k)).encard :=
          Metric.IsCover.externalCoveringNumber_le_encard h_self_cover
        have h_card : (A_sup : Set (DSquare k)).encard = (A_sup.card : ENat) := by simp
        rw [h_card] at h_le
        exact_mod_cast h_le
      have h_step2 : (A_sup.card : ENNReal) ≤
          (9 : ENNReal) * (Metric.externalCoveringNumber ε (P ∩ Metric.closedBall x (2 * r)) : ENNReal) := by
        exact_mod_cast h_grid_bound
      have h_step3 : (Metric.externalCoveringNumber ε (P ∩ Metric.closedBall x (2 * r)) : ENNReal) ≤
          ENNReal.ofReal C_eucl * (ENNReal.ofReal (2 * r)) ^ s * (Metric.externalCoveringNumber ε P : ENNReal) := h6
      have h_step4 : (Metric.externalCoveringNumber ε P : ENNReal) ≤ (P₀.card : ENNReal) := h_ncover_P_le_card
      have h_card_eq : P₀.card = PS.card := by
        have h_PS_def : PS = P₀.image dyadicSquareToDSquare := by
          simp [PS, finsetDyadicToDSquare]
        rw [h_PS_def]
        have h_inj : Set.InjOn dyadicSquareToDSquare (P₀ : Set (DyadicSquare k)) := by
          intro a _ b _ h
          have h' : a.i = b.i ∧ a.j = b.j := by simpa [dyadicSquareToDSquare] using h
          cases a with | mk ai aj =>
          cases b with | mk bi bj =>
          simp at h'
          rcases h' with ⟨rfl, rfl⟩
          rfl
        have h : (P₀.image dyadicSquareToDSquare).card = P₀.card :=
          Finset.card_image_of_injOn h_inj
        exact h.symm
      have h_step5 : (P₀.card : ENNReal) ≤
          (9 : ENNReal) * (Metric.externalCoveringNumber ε (PS : Set (DSquare k)) : ENNReal) := by
        rw [h_card_eq]
        exact h_PS_card_le_cover
      have h_rpow2' : (ENNReal.ofReal (2 * r)) ^ s =
          (2 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s := h_rpow2
      have h_main1 : (Metric.externalCoveringNumber ε (A_sup : Set (DSquare k)) : ENNReal) ≤
          (9 : ENNReal) * (ENNReal.ofReal C_eucl * ((2 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s) *
            ((9 : ENNReal) * (Metric.externalCoveringNumber ε (PS : Set (DSquare k)) : ENNReal))) := by
        calc (Metric.externalCoveringNumber ε (A_sup : Set (DSquare k)) : ENNReal)
          ≤ (A_sup.card : ENNReal) := h_first
        _ ≤ (9 : ENNReal) * (Metric.externalCoveringNumber ε (P ∩ Metric.closedBall x (2 * r)) : ENNReal) := h_step2
        _ ≤ (9 : ENNReal) * (ENNReal.ofReal C_eucl * (ENNReal.ofReal (2 * r)) ^ s * (Metric.externalCoveringNumber ε P : ENNReal)) := by
          gcongr <;> exact h_step3
        _ = (9 : ENNReal) * (ENNReal.ofReal C_eucl * ((2 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s) * (Metric.externalCoveringNumber ε P : ENNReal)) := by
          rw [h_rpow2']
        _ ≤ (9 : ENNReal) * (ENNReal.ofReal C_eucl * ((2 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s) * (P₀.card : ENNReal)) := by
          gcongr <;> exact h_step4
        _ ≤ (9 : ENNReal) * (ENNReal.ofReal C_eucl * ((2 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s) * ((9 : ENNReal) * (Metric.externalCoveringNumber ε (PS : Set (DSquare k)) : ENNReal))) := by
          gcongr <;> exact h_step5
      have h_const : ENNReal.ofReal C_geo =
          (9 : ENNReal) * (9 : ENNReal) * ENNReal.ofReal C_eucl * (2 : ENNReal) ^ s := by
        dsimp only [C_geo]
        have h12 : ENNReal.ofReal (81 * C_eucl * (2 : ℝ) ^ s) =
            (81 : ENNReal) * ENNReal.ofReal C_eucl * (2 : ENNReal) ^ s := by
          have h_pos1 : 0 ≤ (81 : ℝ) := by norm_num
          have h_pos2 : 0 ≤ C_eucl := by linarith
          have h_pos3 : 0 ≤ (2 : ℝ) ^ s := by positivity
          have h_mul1 : ENNReal.ofReal ((81 * C_eucl) * (2 : ℝ) ^ s) =
              ENNReal.ofReal (81 * C_eucl) * ENNReal.ofReal ((2 : ℝ) ^ s) :=
            ENNReal.ofReal_mul (by positivity)
          rw [h_mul1]
          have h_mul2 : ENNReal.ofReal (81 * C_eucl) = (81 : ENNReal) * ENNReal.ofReal C_eucl := by
            rw [ENNReal.ofReal_mul h_pos1] <;> norm_cast
          have h_rpow : ENNReal.ofReal ((2 : ℝ) ^ s) = (2 : ENNReal) ^ s := by
            have h_pos : 0 ≤ (2 : ℝ) := by norm_num
            have h_eq1 : ENNReal.ofReal ((2 : ℝ) ^ s) = ENNReal.ofReal (2 : ℝ) ^ s :=
              (ENNReal.ofReal_rpow_of_nonneg h_pos hs).symm
            have h_eq2 : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_cast
            rw [h_eq1, h_eq2]
          rw [h_mul2, h_rpow] <;> ring
        have h13 : (81 : ENNReal) = (9 : ENNReal) * (9 : ENNReal) := by norm_cast
        rw [h12, h13] <;> simp [mul_assoc] <;> ring_nf
      have h_final : (Metric.externalCoveringNumber ε (A_sup : Set (DSquare k)) : ENNReal) ≤
          ENNReal.ofReal C_geo * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber ε (PS : Set (DSquare k)) : ENNReal) := by
        rw [h_const]
        simpa [mul_assoc, mul_comm, mul_left_comm] using h_main1
      have h_ε : (ε : NNReal) = δ.toNNReal := by rfl
      have h_goal_lhs : Metric.externalCoveringNumber δ.toNNReal ((PS : Set (DSquare k)) ∩ Metric.closedBall p r) =
          Metric.externalCoveringNumber ε (A_sup : Set (DSquare k)) := by
        rw [hA_sup_eq] <;> rfl
      have h_goal_rhs : Metric.externalCoveringNumber δ.toNNReal (PS : Set (DSquare k)) =
          Metric.externalCoveringNumber ε (PS : Set (DSquare k)) := by rfl
      rw [h_goal_lhs, h_goal_rhs]
      exact h_final

  -- Weaken constant: C_geo = 81 * 10 * 2^s * C = 810 * 2^s * C ≤ 2000 * 2^s * C = conversionKGeo(s) * C
  have h_le : C_geo ≤ conversionKGeo s * C := by
    have h_pos1 : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
    have h_pos2 : 0 < C := hC_pos
    have h5 : C_geo = (810 : ℝ) * Real.rpow 2 s * C := by
      dsimp only [C_geo, C_eucl]
      have h_rpow : (2 : ℝ) ^ s = Real.rpow 2 s := by rfl
      rw [h_rpow] <;> ring
    have h6 : conversionKGeo s * C = (2000 : ℝ) * Real.rpow 2 s * C := by
      dsimp only [conversionKGeo] <;> ring
    have h_goal : C_geo ≤ conversionKGeo s * C := by
      calc C_geo
        = (810 : ℝ) * Real.rpow 2 s * C := h5
      _ ≤ (2000 : ℝ) * Real.rpow 2 s * C := by
        have h7 : (810 : ℝ) ≤ (2000 : ℝ) := by norm_num
        have h8 : 0 ≤ Real.rpow 2 s := h_pos1.le
        have h9 : 0 ≤ C := h_pos2.le
        nlinarith
      _ = conversionKGeo s * C := h6.symm
    exact h_goal
  exact finset_deltaSSet_weaken_constant h_main h_le

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
