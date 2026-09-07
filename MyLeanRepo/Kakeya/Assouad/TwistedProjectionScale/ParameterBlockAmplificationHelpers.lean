import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockAmplificationStatement
import Mathlib.Tactic

/-!
# Helper lemmas for parameter block amplification

Translation invariance of ballCount and IsKatzTao, biUnion ballCount bound,
and extraction of total cardinality from a Katz–Tao bound.
-/

noncomputable section

open Kakeya.Assouad

namespace Kakeya.Assouad

/-- Translation invariance of `ballCount`. -/
lemma ballCount_translate {A : DiscreteSet 3} {v x : Point 3} {r : ℝ} :
    DiscreteSet.ballCount (A.image (fun p : Point 3 => p + v)) (x + v) r =
      DiscreteSet.ballCount A x r := by
  have hinj : Function.Injective (fun p : Point 3 => p + v) := by
    intro a b h
    simpa using h
  have hfilter :
      (A.image (fun p : Point 3 => p + v)).filter
        (fun y : Point 3 => dist y (x + v) ≤ r) =
      (A.filter (fun p : Point 3 => dist p x ≤ r)).image
        (fun p : Point 3 => p + v) := by
    rw [Finset.filter_image]
    congr with p
    simp [dist_add_right]
  simp only [DiscreteSet.ballCount, hfilter]
  rw [Finset.card_image_of_injective _ hinj]

/-- Translation invariance of `IsKatzTao`. -/
lemma IsKatzTao_translate {A : DiscreteSet 3} {δ s : ℝ} {C : ENNReal}
    {v : Point 3} (h : DiscreteSet.IsKatzTao A δ s C) :
    DiscreteSet.IsKatzTao (A.image (fun p : Point 3 => p + v)) δ s C := by
  intro y r hδ hr
  have h1 : DiscreteSet.ballCount (A.image (fun p : Point 3 => p + v)) y r =
      DiscreteSet.ballCount A (y - v) r := by
    have h2 := ballCount_translate (A := A) (v := v) (x := y - v) (r := r)
    simpa [sub_add_cancel] using h2
  rw [h1]
  exact h (y - v) r hδ hr

/-- `ballCount` of a biUnion is bounded by the sum of `ballCount`s. -/
lemma ballCount_biUnion_le {α : Type*} {S : Finset α}
    {f : α → DiscreteSet 3} {x : Point 3} {r : ℝ} :
    DiscreteSet.ballCount (S.biUnion f) x r ≤
      ∑ i ∈ S, DiscreteSet.ballCount (f i) x r := by
  have hfilter :
      (S.biUnion f).filter (fun y : Point 3 => dist y x ≤ r) =
      S.biUnion (fun i => (f i).filter (fun y : Point 3 => dist y x ≤ r)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨i, hi, hy⟩, hdist⟩
      exact ⟨i, hi, ⟨hy, hdist⟩⟩
    · rintro ⟨i, hi, ⟨hy, hdist⟩⟩
      exact ⟨⟨i, hi, hy⟩, hdist⟩
  simp only [DiscreteSet.ballCount, hfilter]
  exact_mod_cast (Finset.card_biUnion_le : (S.biUnion (fun i => (f i).filter (fun y => dist y x ≤ r))).card ≤ ∑ i ∈ S, ((f i).filter (fun y => dist y x ≤ r)).card)

/-- `ballCount` is monotone in the set. -/
lemma ballCount_mono {A B : DiscreteSet 3} (h : A ⊆ B)
    {x : Point 3} {r : ℝ} :
    DiscreteSet.ballCount A x r ≤ DiscreteSet.ballCount B x r := by
  have h1 : A.filter (fun y : Point 3 => dist y x ≤ r) ⊆
      B.filter (fun y : Point 3 => dist y x ≤ r) := by
    intro y hy
    have hya : y ∈ A := (Finset.mem_filter.mp hy).1
    have hyr : dist y x ≤ r := (Finset.mem_filter.mp hy).2
    exact Finset.mem_filter.mpr ⟨h hya, hyr⟩
  simp only [DiscreteSet.ballCount]
  exact_mod_cast Finset.card_le_card h1

/-- Extract total cardinality from a Katz–Tao bound when all points fit in one ball. -/
lemma IsKatzTao_total_card {A : DiscreteSet 3} {δ s R : ℝ} {C : ENNReal}
    {c : Point 3} (hKT : DiscreteSet.IsKatzTao A δ s C)
    (hδ : δ ≤ R) (hR : R ≤ 1)
    (hcont : ∀ p ∈ A, dist p c ≤ R) :
    A.enncard ≤ C * Kakeya.realRpowENN (R / δ) s := by
  have h1 : A.filter (fun p : Point 3 => dist p c ≤ R) = A := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, _⟩
      tauto
    · intro hp
      exact ⟨hp, hcont p hp⟩
  have h2 : DiscreteSet.ballCount A c R = A.enncard := by
    simp only [DiscreteSet.ballCount, DiscreteSet.enncard, h1]
  rw [← h2]
  exact hKT c R hδ hR

/-- Bound cardinality of a finset of integers lying in `[a, b]` scaled by `h`. -/
private lemma int_set_in_interval_bound
    (h : ℝ) (hh : 0 < h) (a b : ℝ) (K : Finset ℤ)
    (hK : ∀ k ∈ K, a ≤ (k : ℝ) * h ∧ (k : ℝ) * h ≤ b)
    (hab : a ≤ b) :
    (K.card : ℝ) ≤ (b - a) / h + 1 := by
  by_cases h_empty : K = ∅
  · rw [h_empty]; simp
    have h_pos : 0 ≤ (b - a) / h + 1 := by
      have h1 : 0 ≤ b - a := by linarith
      have h2 : 0 ≤ (b - a) / h := by positivity
      linarith
    exact h_pos
  · have hne : K.Nonempty := by rwa [Finset.nonempty_iff_ne_empty]
    let kmin := K.min' hne
    let kmax := K.max' hne
    have h_kmin_in : kmin ∈ K := Finset.min'_mem K hne
    have h_kmax_in : kmax ∈ K := Finset.max'_mem K hne
    have h_le : kmin ≤ kmax := Finset.min'_le K kmax h_kmax_in
    let f : ℤ → ℕ := fun k => (k - kmin).toNat
    have h_inj : Set.InjOn f K := by
      intro k1 hk1 k2 hk2 h_eq
      have h1le : kmin ≤ k1 := Finset.min'_le K k1 hk1
      have h2le : kmin ≤ k2 := Finset.min'_le K k2 hk2
      have h1 : k1 - kmin ≥ 0 := by omega
      have h2 : k2 - kmin ≥ 0 := by omega
      have h_eq2 : ((k1 - kmin).toNat : ℤ) = ((k2 - kmin).toNat : ℤ) := by exact_mod_cast h_eq
      have h1' : ((k1 - kmin).toNat : ℤ) = k1 - kmin := by
        rw [Int.toNat_of_nonneg h1]
      have h2' : ((k2 - kmin).toNat : ℤ) = k2 - kmin := by
        rw [Int.toNat_of_nonneg h2]
      rw [h1', h2'] at h_eq2
      omega
    have h3 : ∀ k ∈ K, f k < (kmax - kmin + 1).toNat := by
      intro k hk
      have h4 : kmin ≤ k := Finset.min'_le K k hk
      have h5 : k ≤ kmax := Finset.le_max' K k hk
      have h6 : k - kmin ≥ 0 := by omega
      have h7 : 0 ≤ kmax - kmin + 1 := by omega
      have h8 : ((k - kmin).toNat : ℤ) = k - kmin := by
        rw [Int.toNat_of_nonneg h6]
      have h9 : ((kmax - kmin + 1).toNat : ℤ) = kmax - kmin + 1 := by
        rw [Int.toNat_of_nonneg h7]
      have h10 : (k - kmin).toNat < (kmax - kmin + 1).toNat := by
        by_contra h11
        have h12 : (kmax - kmin + 1).toNat ≤ (k - kmin).toNat := by omega
        have h13 : ((kmax - kmin + 1).toNat : ℤ) ≤ ((k - kmin).toNat : ℤ) := by exact_mod_cast h12
        rw [h9, h8] at h13
        omega
      exact h10
    have h4 : K.image f ⊆ Finset.range ((kmax - kmin + 1).toNat) := by
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
      exact Finset.mem_range.mpr (h3 k hk)
    have h5 : (K.image f).card ≤ (Finset.range ((kmax - kmin + 1).toNat)).card :=
      Finset.card_le_card h4
    have h6 : (K.image f).card = K.card := Finset.card_image_of_injOn h_inj
    have h7 : (Finset.range ((kmax - kmin + 1).toNat)).card = (kmax - kmin + 1).toNat := by simp
    rw [h6] at h5
    rw [h7] at h5
    have h8 : (K.card : ℝ) ≤ ((kmax - kmin + 1).toNat : ℝ) := by
      exact_mod_cast h5
    have h9 : 0 ≤ kmax - kmin + 1 := by omega
    have h10 : ((kmax - kmin + 1).toNat : ℤ) = kmax - kmin + 1 := by
      rw [Int.toNat_of_nonneg h9]
    have h11 : ((kmax - kmin + 1).toNat : ℝ) = (kmax : ℝ) - (kmin : ℝ) + 1 := by
      exact_mod_cast h10
    rw [h11] at h8
    have h11 : (kmin : ℝ) * h ≥ a := (hK kmin h_kmin_in).1
    have h12 : (kmax : ℝ) * h ≤ b := (hK kmax h_kmax_in).2
    have h13 : (kmax : ℝ) - (kmin : ℝ) ≤ (b - a) / h := by
      have h14 : ((kmax : ℝ) - (kmin : ℝ)) * h ≤ b - a := by linarith
      calc
        (kmax : ℝ) - (kmin : ℝ)
          = (((kmax : ℝ) - (kmin : ℝ)) * h) / h := by field_simp [hh.ne']
        _ ≤ (b - a) / h := by gcongr
    linarith

/--
Count lattice points `k : Fin 3 → ℤ` with `|k i * h - x i| ≤ R_ball` for all `i`.
Bound: `(2 * R_ball / h + 1)^3`.
-/
lemma lattice_point_count_bound
    (h : ℝ) (hh : 0 < h) (x : Point 3) (R_ball : ℝ)
    (hR : 0 ≤ R_ball)
    (S : Finset (Fin 3 → ℤ))
    (hS : ∀ k ∈ S, ∀ i : Fin 3, |(k i : ℝ) * h - x i| ≤ R_ball) :
    (S.card : ℝ) ≤ (2 * R_ball / h + 1)^3 := by
  let K : Fin 3 → Finset ℤ := fun i =>
    Finset.Icc (Int.ceil ((x i - R_ball) / h)) (Int.floor ((x i + R_ball) / h))
  have hK_bound : ∀ i : Fin 3, ((K i).card : ℝ) ≤ 2 * R_ball / h + 1 := by
    intro i
    have h_in : ∀ k ∈ K i, x i - R_ball ≤ (k : ℝ) * h ∧ (k : ℝ) * h ≤ x i + R_ball := by
      intro k hk
      simp only [K, Finset.mem_Icc] at hk
      have h1 : (x i - R_ball) / h ≤ (k : ℝ) := Int.ceil_le.mp hk.1
      have h2 : (k : ℝ) ≤ (x i + R_ball) / h := Int.le_floor.mp hk.2
      have h3 : x i - R_ball ≤ (k : ℝ) * h := by
        have h31 : ((x i - R_ball) / h) * h ≤ (k : ℝ) * h := mul_le_mul_of_nonneg_right h1 (by linarith)
        have h32 : ((x i - R_ball) / h) * h = x i - R_ball := by field_simp [hh.ne'] <;> ring
        rw [h32] at h31; exact h31
      have h4 : (k : ℝ) * h ≤ x i + R_ball := by
        have h41 : (k : ℝ) * h ≤ ((x i + R_ball) / h) * h := mul_le_mul_of_nonneg_right h2 (by linarith)
        have h42 : ((x i + R_ball) / h) * h = x i + R_ball := by field_simp [hh.ne'] <;> ring
        rw [h42] at h41; exact h41
      exact ⟨h3, h4⟩
    have h_main : ((K i).card : ℝ) ≤ ((x i + R_ball) - (x i - R_ball)) / h + 1 :=
      int_set_in_interval_bound h hh (x i - R_ball) (x i + R_ball) (K i) h_in (by linarith [hR])
    have h_simp : ((x i + R_ball) - (x i - R_ball)) / h + 1 = 2 * R_ball / h + 1 := by
      have h : (x i + R_ball) - (x i - R_ball) = 2 * R_ball := by ring
      rw [h]
    rw [h_simp] at h_main
    exact h_main
  let f : (Fin 3 → ℤ) → ℤ × (ℤ × ℤ) := fun k => (k 0, (k 1, k 2))
  have h_inj : Set.InjOn f S := by
    intro k1 hk1 k2 hk2 h_eq
    have h0 : k1 0 = k2 0 := by simp [Prod.ext_iff] at h_eq <;> tauto
    have h1 : k1 1 = k2 1 := by simp [Prod.ext_iff] at h_eq <;> tauto
    have h2 : k1 2 = k2 2 := by simp [Prod.ext_iff] at h_eq <;> tauto
    funext i; fin_cases i <;> tauto
  have h1 : ∀ k ∈ S, k 0 ∈ K 0 ∧ k 1 ∈ K 1 ∧ k 2 ∈ K 2 := by
    intro k hk
    have h_all : ∀ i : Fin 3, k i ∈ K i := by
      intro i
      have h2 : |(k i : ℝ) * h - x i| ≤ R_ball := hS k hk i
      have h3 : x i - R_ball ≤ (k i : ℝ) * h := by linarith [abs_le.mp h2]
      have h4 : (k i : ℝ) * h ≤ x i + R_ball := by linarith [abs_le.mp h2]
      have h5 : (x i - R_ball) / h ≤ (k i : ℝ) := by
        have h51 : (x i - R_ball) ≤ (k i : ℝ) * h := h3
        have h52 : ((x i - R_ball) / h) ≤ ((k i : ℝ) * h) / h := by gcongr
        have h53 : ((k i : ℝ) * h) / h = (k i : ℝ) := by field_simp [hh.ne'] <;> ring
        rw [h53] at h52; exact h52
      have h6 : (k i : ℝ) ≤ (x i + R_ball) / h := by
        have h61 : (k i : ℝ) * h ≤ x i + R_ball := h4
        have h62 : ((k i : ℝ) * h) / h ≤ (x i + R_ball) / h := by gcongr
        have h63 : ((k i : ℝ) * h) / h = (k i : ℝ) := by field_simp [hh.ne'] <;> ring
        rw [h63] at h62; exact h62
      simp only [K, Finset.mem_Icc]
      exact ⟨Int.ceil_le.mpr h5, Int.le_floor.mpr h6⟩
    exact ⟨h_all 0, h_all 1, h_all 2⟩
  have h2 : S.image f ⊆ (K 0) ×ˢ (K 1) ×ˢ (K 2) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨k, hk, rfl⟩
    have h3 := h1 k hk
    simp only [f, Finset.mem_product]
    exact ⟨h3.1, h3.2.1, h3.2.2⟩
  have h3 : (S.image f).card ≤ ((K 0) ×ˢ (K 1) ×ˢ (K 2)).card :=
    Finset.card_le_card h2
  have h4 : (S.image f).card = S.card :=
    Finset.card_image_of_injOn h_inj
  have h5 : ((K 0) ×ˢ (K 1) ×ˢ (K 2)).card = (K 0).card * (K 1).card * (K 2).card := by
    simp [Finset.card_product] <;> ring
  rw [h4] at h3
  rw [h5] at h3
  have h6 : (S.card : ℝ) ≤ ((K 0).card : ℝ) * ((K 1).card : ℝ) * ((K 2).card : ℝ) := by
    have h61 : S.card ≤ (K 0).card * (K 1).card * (K 2).card := h3
    have h62 : (S.card : ℝ) ≤ (((K 0).card * (K 1).card * (K 2).card : ℕ) : ℝ) := by
      exact Nat.cast_le.mpr h61
    simpa using h62
  have h7 : ((K 0).card : ℝ) * ((K 1).card : ℝ) * ((K 2).card : ℝ) ≤
      (2 * R_ball / h + 1)^3 := by
    have h8 : ((K 0).card : ℝ) ≤ 2 * R_ball / h + 1 := hK_bound 0
    have h9 : ((K 1).card : ℝ) ≤ 2 * R_ball / h + 1 := hK_bound 1
    have h10 : ((K 2).card : ℝ) ≤ 2 * R_ball / h + 1 := hK_bound 2
    have h11 : 0 ≤ 2 * R_ball / h + 1 := by linarith [hh, hR]
    calc
      ((K 0).card : ℝ) * ((K 1).card : ℝ) * ((K 2).card : ℝ)
        ≤ (2 * R_ball / h + 1) * ((K 1).card : ℝ) * ((K 2).card : ℝ) := by gcongr
      _ ≤ (2 * R_ball / h + 1) * (2 * R_ball / h + 1) * ((K 2).card : ℝ) := by gcongr
      _ ≤ (2 * R_ball / h + 1) * (2 * R_ball / h + 1) * (2 * R_ball / h + 1) := by gcongr
      _ = (2 * R_ball / h + 1)^3 := by ring
  exact h6.trans h7

/-- Half-box containment implies unit-ball containment in dimension 3. -/
lemma half_box_implies_unit_ball (p : Point 3)
    (h : ∀ i : Fin 3, |p i| ≤ 1 / 2) : dist p 0 ≤ 1 := by
  have h1 : ∀ i : Fin 3, (p i)^2 ≤ (1 / 2 : ℝ)^2 := by
    intro i
    have h2 : |p i| ≤ 1 / 2 := h i
    calc
      (p i)^2 = |p i|^2 := by rw [sq_abs]
      _ ≤ (1 / 2 : ℝ)^2 := by gcongr
  have h_sum_nonneg : 0 ≤ ∑ i : Fin 3, (p i)^2 := by positivity
  have h4 : dist p 0 = Real.sqrt (∑ i : Fin 3, (p i)^2) := by
    simp [dist_eq_norm, EuclideanSpace.norm_eq]
    <;> rfl
  have h5 : (∑ i : Fin 3, (p i)^2) ≤ 3 / 4 := by
    calc
      (∑ i : Fin 3, (p i)^2)
        ≤ ∑ i : Fin 3, (1 / 2 : ℝ)^2 := by
          apply Finset.sum_le_sum; intro i _; exact h1 i
      _ = 3 * (1 / 2 : ℝ)^2 := by simp [Finset.sum_const] <;> ring
      _ = 3 / 4 := by norm_num
  rw [h4]
  have h6 : Real.sqrt (∑ i : Fin 3, (p i)^2) ≤ Real.sqrt (3 / 4) :=
    Real.sqrt_le_sqrt h5
  have h7 : Real.sqrt (3 / 4) ≤ 1 := by
    rw [Real.sqrt_le_left (by norm_num)] <;> norm_num
  exact h6.trans h7

/--
If all points lie within `blockScale/10` of `localCenter`,
the diameter is at most `blockScale/5`.
-/
lemma localPoints_diameter
    {blockScale : ℝ}
    {localCenter : Point 3} {localPoints : DiscreteSet 3}
    (h : ∀ p ∈ localPoints, dist p localCenter ≤ blockScale / 10) :
    ∀ p ∈ localPoints, ∀ q ∈ localPoints, dist p q ≤ blockScale / 5 := by
  intro p hp q hq
  have h1 : dist p localCenter ≤ blockScale / 10 := h p hp
  have h2 : dist q localCenter ≤ blockScale / 10 := h q hq
  calc dist p q
    ≤ dist p localCenter + dist localCenter q := dist_triangle p localCenter q
  _ = dist p localCenter + dist q localCenter := by rw [dist_comm localCenter q]
  _ ≤ blockScale / 10 + blockScale / 10 := by linarith
  _ = blockScale / 5 := by ring

/--
If translations are coordinate-separated by `h` and `localPoints`
has diameter `≤ d < h`, then the translated sets are pairwise disjoint.
-/
lemma translated_sets_pairwise_disjoint
    {h d : ℝ} (hh : 0 < h) (hd : d < h)
    {localPoints : DiscreteSet 3}
    (h_diam : ∀ p ∈ localPoints, ∀ q ∈ localPoints, dist p q ≤ d)
    {translations : DiscreteSet 3}
    (h_sep : ∀ v ∈ translations, ∀ w ∈ translations, v ≠ w →
      ∃ c : Fin 3, |(v - w) c| ≥ h) :
    Set.PairwiseDisjoint (translations : Set (Point 3))
      (fun v : Point 3 => (translateParameterSet localPoints v : Set (Point 3))) := by
  intro v hv w hw hne
  rcases h_sep v hv w hw hne with ⟨c, hc⟩
  have h_goal : Disjoint (translateParameterSet localPoints v)
      (translateParameterSet localPoints w) := by
    rw [Finset.disjoint_left]
    intro x hxv hxw
    rcases Finset.mem_image.mp hxv with ⟨p, hp, hxp⟩
    rcases Finset.mem_image.mp hxw with ⟨q, hq, hxq⟩
    have heq : q + w = p + v := by
      simpa [translateParameterPoint] using hxq.trans hxp.symm
    have h_eq : (p - q) c = (w - v) c := by
      have h1 : (q + w) c = (p + v) c := by rw [heq]
      have h2 : q c + w c = p c + v c := by
        simpa [PiLp.add_apply] using h1
      have h3 : p c - q c = w c - v c := by linarith
      have h4 : (p - q) c = p c - q c := by simp [PiLp.sub_apply]
      have h5 : (w - v) c = w c - v c := by simp [PiLp.sub_apply]
      rw [h4, h5]; exact h3
    have h1 : |(p - q) c| = |(w - v) c| := by rw [h_eq]
    have h2 : |(w - v) c| = |(v - w) c| := by
      have h3 : (w - v) c = -((v - w) c) := by
        simp [PiLp.sub_apply]
      rw [h3, abs_neg]
    have h3 : |(p - q) c| ≥ h := by
      rw [h1, h2]; exact hc
    have h4 : |(p - q) c| ≤ dist p q := by
      have h5 : |(p - q) c| ≤ ‖p - q‖ := by
        have h6 : (p - q) c ^ 2 ≤ ‖p - q‖ ^ 2 := by
          have h7 : ‖p - q‖ ^ 2 = ∑ i : Fin 3, ((p - q) i) ^ 2 :=
            EuclideanSpace.real_norm_sq_eq (p - q)
          rw [h7]
          apply Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ c)
        have h8 : |(p - q) c| ^ 2 ≤ ‖p - q‖ ^ 2 := by
          rw [sq_abs] <;> exact h6
        exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp h8
      simpa [dist_eq_norm] using h5
    have h5 : dist p q ≤ d := h_diam p hp q hq
    have h6 : |(p - q) c| ≤ d := h4.trans h5
    linarith
  simpa [Set.PairwiseDisjoint] using h_goal

/--
Half-box containment of the amplified set.
-/
lemma amplified_half_box
    {blockScale : ℝ}
    {localCenter : Point 3} {localPoints : DiscreteSet 3}
    {translations : DiscreteSet 3}
    (h_local : ∀ p ∈ localPoints, dist p localCenter ≤ blockScale / 10)
    (h_trans : ∀ v ∈ translations, ∀ c : Fin 3,
      |(localCenter + v) c| ≤ 1 / 2 - blockScale / 10) :
    ∀ p ∈ amplifiedParameterSet localPoints translations,
      ∀ c : Fin 3, |p c| ≤ 1 / 2 := by
  intro p hp c
  rcases Finset.mem_biUnion.mp hp with ⟨v, hv, hpv⟩
  rcases Finset.mem_image.mp hpv with ⟨q, hq, rfl⟩
  have h1 : |(q - localCenter) c| ≤ dist q localCenter := by
    have h2 : |(q - localCenter) c| ≤ ‖q - localCenter‖ := by
      have h3 : (q - localCenter) c ^ 2 ≤ ‖q - localCenter‖ ^ 2 := by
        have h4 : ‖q - localCenter‖ ^ 2 = ∑ i : Fin 3, ((q - localCenter) i) ^ 2 :=
          EuclideanSpace.real_norm_sq_eq (q - localCenter)
        rw [h4]
        apply Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ c)
      have h5 : |(q - localCenter) c| ^ 2 ≤ ‖q - localCenter‖ ^ 2 := by
        rw [sq_abs] <;> exact h3
      exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp h5
    simpa [dist_eq_norm] using h2
  have h2 : dist q localCenter ≤ blockScale / 10 := h_local q hq
  have h3 : |(q - localCenter) c| ≤ blockScale / 10 := h1.trans h2
  have h4 : (q + v) c = (q - localCenter) c + (localCenter + v) c := by
    have h41 : (q + v) c = q c + v c := Pi.add_apply q v c
    have h42 : (q - localCenter) c = q c - localCenter c := Pi.sub_apply q localCenter c
    have h43 : (localCenter + v) c = localCenter c + v c := Pi.add_apply localCenter v c
    rw [h41, h42, h43] <;> ring
  have h_goal : |(q + v) c| ≤ 1 / 2 := by
    rw [h4]
    have h5 : |(localCenter + v) c| ≤ 1 / 2 - blockScale / 10 := h_trans v hv c
    have h6 : |(q - localCenter) c + (localCenter + v) c| ≤
        |(q - localCenter) c| + |(localCenter + v) c| :=
      abs_add_le ((q - localCenter) c) ((localCenter + v) c)
    calc |(q - localCenter) c + (localCenter + v) c|
      ≤ |(q - localCenter) c| + |(localCenter + v) c| := h6
    _ ≤ blockScale / 10 + (1 / 2 - blockScale / 10) := by gcongr
    _ = 1 / 2 := by ring
  simpa [translateParameterPoint] using h_goal

/--
Copy-source witness: every copy contains every original point translated.
-/
lemma copy_source_witness
    {localPoints translations : DiscreteSet 3}
    {v : Point 3} (hv : v ∈ translations)
    {p : Point 3} (hp : p ∈ localPoints) :
    p + v ∈ amplifiedParameterSet localPoints translations := by
  have h1 : p + v ∈ translateParameterSet localPoints v := by
    have h2 : translateParameterPoint v p = p + v := by rfl
    exact Finset.mem_image.mpr ⟨p, hp, h2⟩
  exact Finset.mem_biUnion.mpr ⟨v, hv, h1⟩

/--
Coordinate bound from distance: for Euclidean space, the absolute difference
in each coordinate is bounded by the distance.
-/
lemma coord_abs_le_dist {n : ℕ} (x y : Point n) (i : Fin n) :
    |x i - y i| ≤ dist x y := by
  have h1 : dist (x i) (y i) ≤ dist x y := PiLp.dist_apply_le x y i
  have h2 : dist (x i) (y i) = |x i - y i| := by
    simp [Real.dist_eq] <;> rfl
  rw [h2] at h1
  exact h1

/--
Distance bound for shifted center: if `p` is within `bs` of `localCenter` and
`p + v` is within `r` of `x`, then `v + localCenter` is within `r + bs` of `x`.
-/
lemma dist_translation_center {n : ℕ} {v localCenter p x : EuclideanSpace ℝ (Fin n)} {r bs : ℝ}
    (h1 : dist p localCenter ≤ bs) (h2 : dist (p + v) x ≤ r) :
    dist (v + localCenter) x ≤ r + bs := by
  have h3 : dist (v + localCenter) (p + v) = dist localCenter p := by
    have h4 : v + localCenter = localCenter + v := add_comm _ _
    rw [h4]
    exact dist_add_right localCenter p v
  have h1' : dist localCenter p ≤ bs := by
    rw [dist_comm] <;> exact h1
  calc
    dist (v + localCenter) x
      ≤ dist (v + localCenter) (p + v) + dist (p + v) x := dist_triangle _ _ _
    _ = dist localCenter p + dist (p + v) x := by rw [h3]
    _ ≤ bs + r := add_le_add h1' h2
    _ = r + bs := by ring

/--
The cubic lattice with spacing `blockScale^(1/3)` has at most
`8 * blockScale⁻¹` points in the half unit box.
-/
lemma parameterBlockTranslationCardUpper
    {blockScale h R : ℝ}
    {N : ℕ}
    (hblock_pos : 0 < blockScale)
    (hh_pos : 0 < h)
    (hh_le_one : h ≤ 1)
    (hR_le_half : R ≤ 1 / 2)
    (h_cube : h ^ 3 = blockScale)
    (hN : (N : ℝ) ≤ R / h) :
    (((2 * N + 1) ^ 3 : ℕ) : ENNReal) ≤
      8 * Kakeya.realRpowENN blockScale (-1) := by
  have h_one_le_inv : 1 ≤ 1 / h := by
    rw [le_div_iff₀ hh_pos]
    simpa using hh_le_one
  have h_count :
      ((2 * N + 1 : ℕ) : ℝ) ≤ 2 / h := by
    have h_cast :
        ((2 * N + 1 : ℕ) : ℝ) =
          2 * (N : ℝ) + 1 := by
      push_cast
      ring
    rw [h_cast]
    calc
      2 * (N : ℝ) + 1 ≤
          2 * (R / h) + 1 := by
        gcongr
      _ ≤ 2 * ((1 / 2 : ℝ) / h) + 1 := by
        gcongr
      _ = 1 / h + 1 := by
        field_simp [hh_pos.ne']
      _ ≤ 1 / h + 1 / h := by
        gcongr
      _ = 2 / h := by ring
  have h_real :
      (((2 * N + 1 : ℕ) : ℝ) ^ 3) ≤
        8 * Real.rpow blockScale (-1) := by
    calc
      (((2 * N + 1 : ℕ) : ℝ) ^ 3) ≤
          (2 / h : ℝ) ^ 3 := by
        gcongr
      _ = 8 / (h ^ 3) := by
        field_simp [hh_pos.ne']
        ring
      _ = 8 / blockScale := by rw [h_cube]
      _ = 8 * Real.rpow blockScale (-1) := by
        simp [Real.rpow_neg_one, div_eq_mul_inv]
  calc
    (((2 * N + 1) ^ 3 : ℕ) : ENNReal) =
        ENNReal.ofReal ((((2 * N + 1) ^ 3 : ℕ) : ℝ)) := by
      exact
        Eq.symm
          (ENNReal.ofReal_natCast ((2 * N + 1) ^ 3))
    _ = ENNReal.ofReal (((2 * N + 1 : ℕ) : ℝ) ^ 3) := by
      congr 1
      norm_num
    _ ≤ ENNReal.ofReal (8 * Real.rpow blockScale (-1)) :=
      ENNReal.ofReal_mono h_real
    _ = 8 * Kakeya.realRpowENN blockScale (-1) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num [Kakeya.realRpowENN]

/--
Active lattice coordinate bound: if a translated copy intersects the ball
`B(x, r)`, then its lattice coordinates lie within `r + blockScale/10` of `x`.
-/
lemma active_lattice_coord_bound
    (localPoints : DiscreteSet 3)
    (localCenter : Point 3)
    (blockScale : ℝ)
    (hcontain : ∀ p ∈ localPoints, dist p localCenter ≤ blockScale / 10)
    (v_of_k : (Fin 3 → ℤ) → Point 3)
    (h : ℝ)
    (v_coord : ∀ (k : Fin 3 → ℤ) (i : Fin 3),
        (v_of_k k + localCenter) i = (k i : ℝ) * h)
    (indices : Finset (Fin 3 → ℤ))
    (x : Point 3)
    (r : ℝ)
    (R_ball : ℝ)
    (hR_ball_eq : R_ball = r + blockScale / 10)
    (P : Point 3 → Prop)
    [DecidablePred P]
    (hP : ∀ y, P y ↔ dist y x ≤ r)
    (active_indices : Finset (Fin 3 → ℤ))
    (h_active_def : active_indices = indices.filter (fun k =>
        ((translateParameterSet localPoints (v_of_k k)).filter P).Nonempty)) :
    ∀ k ∈ active_indices, ∀ i : Fin 3, |(k i : ℝ) * h - x i| ≤ R_ball := by
  intro k hk i
  have h_in : ((translateParameterSet localPoints (v_of_k k)).filter P).Nonempty := by
    rw [h_active_def] at hk
    exact (Finset.mem_filter.mp hk).2
  rcases h_in with ⟨y, hy⟩
  have h_y_in : y ∈ translateParameterSet localPoints (v_of_k k) := (Finset.mem_filter.mp hy).1
  have h_ydist : dist y x ≤ r := (hP y).mp ((Finset.mem_filter.mp hy).2)
  rcases Finset.mem_image.mp h_y_in with ⟨p, hp, rfl⟩
  have h5 : dist p localCenter ≤ blockScale / 10 := hcontain p hp
  have h5' : dist localCenter p ≤ blockScale / 10 := by
    rw [dist_comm] <;> exact h5
  have h6 : dist (p + v_of_k k) x ≤ r := h_ydist
  have h_comm : v_of_k k + localCenter = localCenter + v_of_k k := by
    ext j; simp [Pi.add_apply] <;> ring
  have h1 : dist (v_of_k k + localCenter) x ≤ R_ball := by
    rw [h_comm]
    have h_tri : dist (localCenter + v_of_k k) x ≤
        dist (localCenter + v_of_k k) (p + v_of_k k) + dist (p + v_of_k k) x :=
      dist_triangle _ _ _
    have h_dist_add : dist (localCenter + v_of_k k) (p + v_of_k k) = dist localCenter p :=
      dist_add_right localCenter p (v_of_k k)
    rw [h_dist_add] at h_tri
    rw [hR_ball_eq]
    linarith
  have h2 : |(v_of_k k + localCenter) i - x i| ≤ dist (v_of_k k + localCenter) x :=
    coord_abs_le_dist (v_of_k k + localCenter) x i
  have h3 : (v_of_k k + localCenter) i = (k i : ℝ) * h := v_coord k i
  rw [h3] at h2
  exact le_trans h2 h1

/--
The lattice amplification of one local Katz--Tao block is globally
Katz--Tao.  This is separated from the construction theorem so the active
lattice count and the two radius regimes elaborate independently.
-/
lemma amplifiedParameterSet_isKatzTao
    {fineScale blockScale ktExponent h : ℝ}
    (hfine : 0 < fineScale)
    (hblock_pos : 0 < blockScale)
    (hfine_block : fineScale ≤ blockScale)
    (hkt_pos : 0 < ktExponent)
    (hkt_one : ktExponent ≤ 1)
    (h_pos : 0 < h)
    (h_gt_blockScale5 : blockScale / 5 < h)
    (h_cube : h ^ 3 = blockScale)
    (localCenter : Point 3)
    (localPoints : DiscreteSet 3)
    (hcontain : ∀ p ∈ localPoints, dist p localCenter ≤ blockScale / 10)
    (hkt : localPoints.IsKatzTao fineScale ktExponent 100)
    (local_card_upper :
      localPoints.enncard ≤
        100 * Kakeya.realRpowENN
          (blockScale / fineScale) ktExponent)
    (indices : Finset (Fin 3 → ℤ))
    (v_of_k : (Fin 3 → ℤ) → Point 3)
    (v_of_k_injective : Function.Injective v_of_k)
    (v_coord : ∀ (k : Fin 3 → ℤ) (i : Fin 3),
      (v_of_k k + localCenter) i = (k i : ℝ) * h) :
    (amplifiedParameterSet localPoints (indices.image v_of_k)).IsKatzTao
      fineScale 1 100000 := by
  classical
  intro x r hfine_r hr_one
  let P : Point 3 → Prop := fun y => dist y x ≤ r
  let active_indices : Finset (Fin 3 → ℤ) :=
    indices.filter
      (fun k => ((translateParameterSet localPoints (v_of_k k)).filter P).Nonempty)
  have h_sum1 :
      DiscreteSet.ballCount
          (amplifiedParameterSet localPoints (indices.image v_of_k)) x r ≤
        ∑ v ∈ indices.image v_of_k,
          DiscreteSet.ballCount (translateParameterSet localPoints v) x r := by
    simpa only [amplifiedParameterSet] using
      (ballCount_biUnion_le
        (S := indices.image v_of_k)
        (f := translateParameterSet localPoints)
        (x := x) (r := r))
  have h_sum2 :
      ∑ v ∈ indices.image v_of_k,
          DiscreteSet.ballCount (translateParameterSet localPoints v) x r =
        ∑ k ∈ indices,
          DiscreteSet.ballCount
            (translateParameterSet localPoints (v_of_k k)) x r := by
    have h_inj : Set.InjOn v_of_k indices := fun a _ b _ hab =>
      v_of_k_injective hab
    let weight : Point 3 → ENNReal := fun v =>
      DiscreteSet.ballCount (translateParameterSet localPoints v) x r
    exact Finset.sum_image (s := indices) (g := v_of_k) (f := weight) h_inj
  have h_sum3 :
      ∑ k ∈ indices,
          DiscreteSet.ballCount
            (translateParameterSet localPoints (v_of_k k)) x r =
        ∑ k ∈ active_indices,
          DiscreteSet.ballCount
            (translateParameterSet localPoints (v_of_k k)) x r := by
    have h_sub : active_indices ⊆ indices := Finset.filter_subset _ _
    have h_zero : ∀ k ∈ indices, k ∉ active_indices →
        DiscreteSet.ballCount
          (translateParameterSet localPoints (v_of_k k)) x r = 0 := by
      intro k hk hnk
      have h_not_active :
          ¬ ((translateParameterSet localPoints (v_of_k k)).filter P).Nonempty := by
        intro hnonempty
        exact hnk (Finset.mem_filter.mpr ⟨hk, hnonempty⟩)
      have h_empty :
          (translateParameterSet localPoints (v_of_k k)).filter P = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp h_not_active
      rw [DiscreteSet.ballCount, h_empty]
      simp
    exact (Finset.sum_subset h_sub h_zero).symm
  have h_sum4 :
      DiscreteSet.ballCount
          (amplifiedParameterSet localPoints (indices.image v_of_k)) x r ≤
        ∑ k ∈ active_indices,
          DiscreteSet.ballCount
            (translateParameterSet localPoints (v_of_k k)) x r :=
    h_sum1.trans (h_sum2.le.trans h_sum3.le)

  let R_ball : ℝ := r + blockScale / 10
  have hR_ball : 0 ≤ R_ball := by
    dsimp only [R_ball]
    exact add_nonneg (hfine.le.trans hfine_r) (by positivity)
  have hR_ball_eq : R_ball = r + blockScale / 10 := rfl
  have h_active_lattice : ∀ k ∈ active_indices, ∀ i : Fin 3,
      |(k i : ℝ) * h - x i| ≤ R_ball := by
    exact active_lattice_coord_bound
      localPoints localCenter blockScale hcontain v_of_k h v_coord
      indices x r R_ball hR_ball_eq P (fun _ => Iff.rfl)
      active_indices rfl
  have h_active_bound :
      (active_indices.card : ℝ) ≤ (2 * R_ball / h + 1) ^ 3 :=
    lattice_point_count_bound
      h h_pos x R_ball hR_ball active_indices h_active_lattice

  by_cases h_case : r ≤ h
  · have h_bound2 : 2 * R_ball / h + 1 < 4 := by
      rw [hR_ball_eq]
      have h1 : blockScale / 10 < h / 2 := by
        linarith [h_gt_blockScale5]
      have h2 : r + blockScale / 10 < 3 * h / 2 := by
        linarith [h_case, h1]
      have h3 : 2 * (r + blockScale / 10) < 3 * h := by
        linarith
      have h4 : 2 * (r + blockScale / 10) / h < 3 := by
        calc
          2 * (r + blockScale / 10) / h < (3 * h) / h := by gcongr
          _ = 3 := by field_simp [h_pos.ne'] <;> ring
      linarith
    have h_active_card : active_indices.card ≤ 64 := by
      have h_card_real : (active_indices.card : ℝ) < 64 := by
        calc
          (active_indices.card : ℝ) ≤ (2 * R_ball / h + 1) ^ 3 :=
            h_active_bound
          _ < 4 ^ 3 := by gcongr
          _ = 64 := by norm_num
      exact (Nat.cast_lt.mp h_card_real).le
    have h_each : ∀ k ∈ active_indices,
        DiscreteSet.ballCount
            (translateParameterSet localPoints (v_of_k k)) x r ≤
          100 * Kakeya.realRpowENN (r / fineScale) 1 := by
      intro k _
      have h_local :=
        (IsKatzTao_translate (v := v_of_k k) hkt)
          x r hfine_r hr_one
      have h_ratio : 1 ≤ r / fineScale := by
        rw [le_div_iff₀ hfine]
        simpa using hfine_r
      have h_power :
          Kakeya.realRpowENN (r / fineScale) ktExponent ≤
            Kakeya.realRpowENN (r / fineScale) 1 := by
        apply ENNReal.ofReal_mono
        exact
          Real.rpow_le_rpow_of_exponent_le
            h_ratio hkt_one
      exact h_local.trans (by gcongr)
    calc
      DiscreteSet.ballCount
          (amplifiedParameterSet localPoints (indices.image v_of_k)) x r
        ≤ ∑ k ∈ active_indices,
            DiscreteSet.ballCount
              (translateParameterSet localPoints (v_of_k k)) x r := h_sum4
      _ ≤ ∑ _k ∈ active_indices,
          100 * Kakeya.realRpowENN (r / fineScale) 1 := by
        exact Finset.sum_le_sum h_each
      _ = (active_indices.card : ENNReal) * 100 *
          Kakeya.realRpowENN (r / fineScale) 1 := by
        simp [Finset.sum_const] <;> ring
      _ ≤ (64 : ENNReal) * 100 *
          Kakeya.realRpowENN (r / fineScale) 1 := by
        gcongr
        exact_mod_cast h_active_card
      _ = 6400 * Kakeya.realRpowENN (r / fineScale) 1 := by norm_num
      _ ≤ 100000 * Kakeya.realRpowENN (r / fineScale) 1 := by
        gcongr
        norm_num
  · have h_r_gt_h : r > h := by linarith
    have h_rpos : 0 < r := h_pos.trans h_r_gt_h
    have h_ratio_bound : 2 * R_ball / h + 1 ≤ 5 * r / h := by
      rw [hR_ball_eq]
      have h2 : 2 * (r + blockScale / 10) ≤ 4 * r := by
        linarith [h_gt_blockScale5]
      have h3 : 1 ≤ r / h := by
        rw [one_le_div h_pos]
        exact h_r_gt_h.le
      have h4 : 2 * (r + blockScale / 10) / h ≤ 4 * r / h :=
        div_le_div_of_nonneg_right h2 h_pos.le
      have h5 : 2 * (r + blockScale / 10) / h + 1 ≤
          4 * r / h + 1 := by linarith
      have h6 : 4 * r / h + 1 ≤ 5 * r / h := by
        calc
          4 * r / h + 1 ≤ 4 * r / h + r / h := by gcongr
          _ = 5 * r / h := by ring
      exact h5.trans h6
    have h_active_card :
        (active_indices.card : ℝ) ≤
          125 * r ^ 3 / blockScale := by
      calc
        (active_indices.card : ℝ) ≤ (2 * R_ball / h + 1) ^ 3 :=
          h_active_bound
        _ ≤ (5 * r / h) ^ 3 := by gcongr
        _ = 125 * r ^ 3 / h ^ 3 := by ring
        _ = 125 * r ^ 3 / blockScale := by rw [h_cube]
    have h_each : ∀ k ∈ active_indices,
        DiscreteSet.ballCount
            (translateParameterSet localPoints (v_of_k k)) x r ≤
          localPoints.enncard := by
      intro k _
      let translated : DiscreteSet 3 :=
        translateParameterSet localPoints (v_of_k k)
      have h_count :
          DiscreteSet.ballCount translated x r ≤ (translated.card : ENNReal) := by
        dsimp only [DiscreteSet.ballCount]
        exact_mod_cast Finset.card_filter_le translated (fun y => dist y x ≤ r)
      have h_card : translated.card = localPoints.card := by
        simp only [translated, translateParameterSet]
        rw [Finset.card_image_of_injective]
        intro a b hab
        exact add_right_cancel hab
      simpa only [DiscreteSet.enncard, h_card] using h_count
    have h_rpow3 : r ^ 3 ≤ 8 * Real.rpow r ktExponent := by
      have h1 : Real.rpow r (3 : ℝ) ≤ Real.rpow r ktExponent :=
        Real.rpow_le_rpow_of_exponent_ge'
          h_rpos.le hr_one hkt_pos.le (by linarith [hkt_one])
      have h3 : r ^ 3 ≤ Real.rpow r ktExponent := by
        simpa [Real.rpow_natCast] using h1
      exact h3.trans (by
        have hnonneg : 0 ≤ Real.rpow r ktExponent :=
          Real.rpow_nonneg h_rpos.le _
        nlinarith)
    have h_div_bound :
        r ^ 3 / Real.rpow fineScale ktExponent ≤
          8 * (Real.rpow r ktExponent /
            Real.rpow fineScale ktExponent) := by
      calc
        r ^ 3 / Real.rpow fineScale ktExponent
          ≤ 8 * Real.rpow r ktExponent /
              Real.rpow fineScale ktExponent := by
            exact div_le_div_of_nonneg_right h_rpow3
              (Real.rpow_nonneg hfine.le ktExponent)
        _ = 8 * (Real.rpow r ktExponent /
            Real.rpow fineScale ktExponent) := by ring
    have hbs_le : 0 ≤ blockScale := hblock_pos.le
    have hfs_le : 0 ≤ fineScale := hfine.le
    have hr_le : 0 ≤ r := h_rpos.le
    calc
      DiscreteSet.ballCount
          (amplifiedParameterSet localPoints (indices.image v_of_k)) x r
        ≤ ∑ _k ∈ active_indices, localPoints.enncard := by
          exact h_sum4.trans (Finset.sum_le_sum h_each)
      _ = (active_indices.card : ENNReal) * localPoints.enncard := by
        simp [Finset.sum_const] <;> ring
      _ ≤ ENNReal.ofReal
          (125 * r ^ 3 / blockScale) * localPoints.enncard := by
        have hcard_cast :
            (active_indices.card : ENNReal) =
              ENNReal.ofReal (active_indices.card : ℝ) := by simp
        rw [hcard_cast]
        gcongr
      _ ≤ ENNReal.ofReal
          (125 * r ^ 3 / blockScale) *
            (100 * Kakeya.realRpowENN
              (blockScale / fineScale) ktExponent) := by
        gcongr
      _ ≤ 12500 * Kakeya.realRpowENN
          (r / fineScale) 1 := by
        have h_ratio_one :
            1 ≤ blockScale / fineScale := by
          rw [le_div_iff₀ hfine]
          simpa using hfine_block
        have h_rpow_ratio :
            Real.rpow (blockScale / fineScale) ktExponent ≤
              blockScale / fineScale := by
          have h :=
            Real.rpow_le_rpow_of_exponent_le
              h_ratio_one hkt_one
          simpa using h
        have h_r_cube : r ^ 3 ≤ r := by
          nlinarith [sq_nonneg r]
        have h_real :
            (125 * r ^ 3 / blockScale) *
                (100 * Real.rpow
                  (blockScale / fineScale) ktExponent) ≤
              12500 * (r / fineScale) := by
          calc
            (125 * r ^ 3 / blockScale) *
                  (100 * Real.rpow
                    (blockScale / fineScale) ktExponent) =
                12500 *
                  ((r ^ 3 / blockScale) *
                    Real.rpow
                      (blockScale / fineScale) ktExponent) := by ring
            _ ≤ 12500 *
                  ((r / blockScale) *
                    Real.rpow
                      (blockScale / fineScale) ktExponent) := by
              have hdiv_nonneg : 0 ≤ r / blockScale := by positivity
              have hrpow_nonneg :
                  0 ≤ Real.rpow
                    (blockScale / fineScale) ktExponent :=
                Real.rpow_nonneg (by positivity) _
              have hdiv :
                  r ^ 3 / blockScale ≤ r / blockScale :=
                div_le_div_of_nonneg_right h_r_cube hblock_pos.le
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hdiv hrpow_nonneg)
                (by norm_num)
            _ ≤ 12500 *
                  ((r / blockScale) *
                    (blockScale / fineScale)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left h_rpow_ratio
                  (by positivity))
                (by norm_num)
            _ = 12500 * (r / fineScale) := by
              field_simp [hblock_pos.ne', hfine.ne']
        have hleft :
            ENNReal.ofReal (125 * r ^ 3 / blockScale) *
                (100 * Kakeya.realRpowENN
                  (blockScale / fineScale) ktExponent) =
              ENNReal.ofReal
                ((125 * r ^ 3 / blockScale) *
                  (100 * Real.rpow
                    (blockScale / fineScale) ktExponent)) := by
          simp only [Kakeya.realRpowENN]
          have hA :
              0 ≤ 125 * r ^ 3 / blockScale := by positivity
          have hB :
              0 ≤ Real.rpow
                (blockScale / fineScale) ktExponent := by
            exact Real.rpow_nonneg (by positivity) _
          calc
            ENNReal.ofReal (125 * r ^ 3 / blockScale) *
                  (100 * ENNReal.ofReal
                    (Real.rpow
                      (blockScale / fineScale) ktExponent)) =
                ENNReal.ofReal (125 * r ^ 3 / blockScale) *
                  ENNReal.ofReal
                    (100 * Real.rpow
                      (blockScale / fineScale) ktExponent) := by
              rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 100)]
              norm_num
            _ = ENNReal.ofReal
                ((125 * r ^ 3 / blockScale) *
                  (100 * Real.rpow
                    (blockScale / fineScale) ktExponent)) := by
              exact (ENNReal.ofReal_mul hA).symm
        have hright :
            12500 * Kakeya.realRpowENN (r / fineScale) 1 =
              ENNReal.ofReal (12500 * (r / fineScale)) := by
          simp [Kakeya.realRpowENN, Real.rpow_one,
            ENNReal.ofReal_mul]
        rw [hleft, hright]
        exact ENNReal.ofReal_mono h_real
      _ ≤ 100000 * Kakeya.realRpowENN (r / fineScale) 1 := by
        gcongr
        norm_num

end Kakeya.Assouad
