import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# 1D covering number coarsening

For sets of real numbers, relates covering numbers at different scales.
An interval of length `2R` can be covered by `floor(2R/r) + 1` intervals
of length `2r`, giving a multiplicative bound on coarsening.
-/

namespace Kakeya.Assouad

open Metric

/--
For any `x ∈ closedBall c R`, there exists `n < K = floor(2*R/r) + 1`
such that `x ∈ closedBall (c - R + n*r) r`.
-/
lemma closed_ball_point_cover1D {c x : ℝ} {r R : ℝ} (hr : 0 < r) (hle : r ≤ R)
    (hx : x ∈ closedBall c R) :
    ∃ (n : ℕ), n < Nat.floor (2 * R / r) + 1 ∧
      x ∈ closedBall (c - R + (n : ℝ) * r) r := by
  let K : ℕ := Nat.floor (2 * R / r) + 1
  have h1 : dist x c ≤ R := hx
  have h2 : |x - c| ≤ R := by simpa [dist_eq_norm] using h1
  have h2l : c - R ≤ x := by linarith [abs_le.mp h2]
  have h2r : x ≤ c + R := by linarith [abs_le.mp h2]
  set t : ℝ := x - (c - R) with ht
  have ht_nonneg : 0 ≤ t := by linarith
  have ht_le : t ≤ 2 * R := by linarith
  have htr_pos : 0 ≤ t / r := by positivity
  let n : ℕ := Nat.floor (t / r)
  have hn1 : (n : ℝ) ≤ t / r := Nat.floor_le htr_pos
  have hn2 : t / r < (n : ℝ) + 1 := by
    simpa [n] using Nat.lt_floor_add_one (t / r)
  have hnK : n < K := by
    have h4 : t / r ≤ 2 * R / r := by gcongr
    have h6 : n ≤ Nat.floor (2 * R / r) := Nat.floor_mono h4
    simp [K] at * <;> omega
  have h7 : 0 ≤ t - (n : ℝ) * r := by
    have h8 : (n : ℝ) * r ≤ t := by
      calc (n : ℝ) * r ≤ (t / r) * r := by gcongr
        _ = t := by field_simp [hr.ne'] <;> ring
    linarith
  have h10 : t - (n : ℝ) * r < r := by
    have h12 : t < ((n : ℝ) + 1) * r := by
      calc t = (t / r) * r := by field_simp [hr.ne'] <;> ring
        _ < ((n : ℝ) + 1) * r := by gcongr
    linarith
  have h13 : dist x (c - R + (n : ℝ) * r) ≤ r := by
    have h14 : x - (c - R + (n : ℝ) * r) = t - (n : ℝ) * r := by simp [ht] <;> ring
    have h15 : dist x (c - R + (n : ℝ) * r) = |x - (c - R + (n : ℝ) * r)| := by
      simp [dist_eq_norm]
    rw [h15, h14]
    have h16 : |t - (n : ℝ) * r| = t - (n : ℝ) * r := by
      rw [abs_of_nonneg] <;> linarith
    rw [h16] <;> linarith
  exact ⟨n, hnK, h13⟩

/--
Coarsening inequality for external covering numbers in `ℝ`.

If `0 < r ≤ R`, then
`externalCoveringNumber r S ≤ (floor(2R/r) + 1) * externalCoveringNumber R S`.
-/
lemma external_covering_number_coarsen1D
    {r R : ℝ} (hr : 0 < r) (hle : r ≤ R) {S : Set ℝ} :
    externalCoveringNumber (Real.toNNReal r) S ≤
      ((Nat.floor (2 * R / r) + 1 : ℕ) : ℕ∞) *
      externalCoveringNumber (Real.toNNReal R) S := by
  let K : ℕ := Nat.floor (2 * R / r) + 1
  have hK_pos : 0 < K := by positivity
  have hR_nonneg : 0 ≤ R := by linarith
  have hr_nonneg : 0 ≤ r := by linarith

  have h_main : ∀ (C : Set ℝ), IsCover (Real.toNNReal R) S C →
      ∃ (D : Set ℝ), IsCover (Real.toNNReal r) S D ∧
        D.encard ≤ (K : ℕ∞) * C.encard := by
    intro C hC
    let D : Set ℝ := Set.image2 (fun (c : ℝ) (n : ℕ) => c - R + (n : ℝ) * r) C (Finset.range K)
    have hD_cover : IsCover (Real.toNNReal r) S D := by
      intro x hx
      have h1 : ∃ c ∈ C, edist x c ≤ (Real.toNNReal R : ENNReal) := hC hx
      rcases h1 with ⟨c, hc, hdist⟩
      have h21 : (Real.toNNReal R : ENNReal) = ENNReal.ofReal R := by
        have h_eq : Real.toNNReal R = NNReal.mk R hR_nonneg := Real.toNNReal_of_nonneg hR_nonneg
        have h_coe : (Real.toNNReal R : ℝ) = R := by
          calc (Real.toNNReal R : ℝ)
            = (NNReal.mk R hR_nonneg : ℝ) := by rw [h_eq]
          _ = R := by simp
        have h : (Real.toNNReal R : ENNReal) = ENNReal.ofReal (Real.toNNReal R : ℝ) :=
          ENNReal.coe_nnreal_eq (Real.toNNReal R)
        rw [h, h_coe]
      have h22 : edist x c ≤ ENNReal.ofReal R := by
        rw [h21] at hdist; exact hdist
      have h23 : edist x c = ENNReal.ofReal (dist x c) := edist_dist x c
      have h2 : dist x c ≤ R := by
        rw [h23] at h22
        exact (ENNReal.ofReal_le_ofReal_iff hR_nonneg).mp h22
      have h3 : x ∈ closedBall c R := by
        simpa [Metric.mem_closedBall] using h2
      rcases closed_ball_point_cover1D hr hle h3 with ⟨n, hnK, hxn⟩
      let d : ℝ := c - R + (n : ℝ) * r
      have hnK' : n ∈ (Finset.range K : Set ℕ) := Finset.mem_range.mpr hnK
      have hd_in_D : d ∈ D := Set.mem_image2.mpr ⟨c, hc, n, hnK', rfl⟩
      have h4 : dist x d ≤ r := by simpa [Metric.mem_closedBall] using hxn
      have h51 : (Real.toNNReal r : ENNReal) = ENNReal.ofReal r := by
        have h_eq : Real.toNNReal r = NNReal.mk r hr_nonneg := Real.toNNReal_of_nonneg hr_nonneg
        have h_coe : (Real.toNNReal r : ℝ) = r := by
          calc (Real.toNNReal r : ℝ)
            = (NNReal.mk r hr_nonneg : ℝ) := by rw [h_eq]
          _ = r := by simp
        have h : (Real.toNNReal r : ENNReal) = ENNReal.ofReal (Real.toNNReal r : ℝ) :=
          ENNReal.coe_nnreal_eq (Real.toNNReal r)
        rw [h, h_coe]
      have h5 : edist x d ≤ (Real.toNNReal r : ENNReal) := by
        have h52 : edist x d = ENNReal.ofReal (dist x d) := edist_dist x d
        rw [h52, h51]
        exact (ENNReal.ofReal_le_ofReal_iff hr_nonneg).mpr h4
      exact ⟨d, hd_in_D, h5⟩
    have h_encard : D.encard ≤ (K : ℕ∞) * C.encard := by
      let f : ℝ × ℕ → ℝ := fun p => p.1 - R + (p.2 : ℝ) * r
      have hD_eq : D = f '' (C ×ˢ (Finset.range K : Set ℕ)) := by
        ext z
        simp only [D, Set.mem_image2, Set.mem_image, Set.mem_prod]
        constructor
        · rintro ⟨c, hc, n, hn, rfl⟩
          exact ⟨(c, n), ⟨hc, hn⟩, rfl⟩
        · rintro ⟨p, hp, rfl⟩
          exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩
      rw [hD_eq]
      have h1 : (f '' (C ×ˢ (Finset.range K : Set ℕ))).encard ≤
          (C ×ˢ (Finset.range K : Set ℕ)).encard := Set.encard_image_le f _
      have h2 : (C ×ˢ (Finset.range K : Set ℕ)).encard =
          C.encard * (Finset.range K : Set ℕ).encard := Set.encard_prod
      have h3 : (Finset.range K : Set ℕ).encard = (K : ℕ∞) := by
        have h4 : (Finset.range K : Set ℕ).encard = ↑(Finset.range K).card :=
          Set.encard_coe_eq_coe_finsetCard (Finset.range K)
        rw [h4, Finset.card_range]
      calc (f '' (C ×ˢ (Finset.range K : Set ℕ))).encard
        ≤ (C ×ˢ (Finset.range K : Set ℕ)).encard := h1
        _ = C.encard * (Finset.range K : Set ℕ).encard := h2
        _ = C.encard * (K : ℕ∞) := by rw [h3]
        _ = (K : ℕ∞) * C.encard := by exact mul_comm _ _
    exact ⟨D, hD_cover, h_encard⟩

  have h1 : ∀ (C : Set ℝ), IsCover (Real.toNNReal R) S C →
      externalCoveringNumber (Real.toNNReal r) S ≤ (K : ℕ∞) * C.encard := by
    intro C hC
    rcases h_main C hC with ⟨D, hD_cover, hD_encard⟩
    exact le_trans (IsCover.externalCoveringNumber_le_encard hD_cover) hD_encard

  have h_iInf_pointwise : ∀ (C : Set ℝ),
      (⨅ (h : IsCover (Real.toNNReal R) S C), (K : ℕ∞) * C.encard) =
      (K : ℕ∞) * (⨅ (h : IsCover (Real.toNNReal R) S C), C.encard) := by
    intro C
    by_cases h : IsCover (Real.toNNReal R) S C
    · have h_iInf1 : (⨅ (h' : IsCover (Real.toNNReal R) S C), C.encard) = C.encard := by
        apply le_antisymm
        · exact iInf_le_iff.mpr fun b a => a h
        · exact le_iInf (fun (_ : IsCover (Real.toNNReal R) S C) => le_rfl)
      have h_iInf2 : (⨅ (h' : IsCover (Real.toNNReal R) S C), (K : ℕ∞) * C.encard) = (K : ℕ∞) * C.encard := by
        apply le_antisymm
        · exact iInf_le_iff.mpr fun b a => a h
        · exact le_iInf (fun (_ : IsCover (Real.toNNReal R) S C) => le_rfl)
      rw [h_iInf2, h_iInf1]
    · have h_empty : IsEmpty (IsCover (Real.toNNReal R) S C) := ⟨h⟩
      have h_iInf1 : (⨅ (h' : IsCover (Real.toNNReal R) S C), C.encard) = ⊤ := by
        simp [h_empty]
      have h_iInf2 : (⨅ (h' : IsCover (Real.toNNReal R) S C), (K : ℕ∞) * C.encard) = ⊤ := by
        simp [h_empty]
      rw [h_iInf2, h_iInf1]
      rw [ENat.mul_top (show (K : ℕ∞) ≠ 0 from by exact_mod_cast hK_pos.ne')]
  have h2 : (⨅ (C : Set ℝ), (⨅ (h : IsCover (Real.toNNReal R) S C), (K : ℕ∞) * C.encard)) =
      (K : ℕ∞) * (⨅ (C : Set ℝ), (⨅ (h : IsCover (Real.toNNReal R) S C), C.encard)) := by
    have h3 : (⨅ (C : Set ℝ), (⨅ (h : IsCover (Real.toNNReal R) S C), (K : ℕ∞) * C.encard)) =
        ⨅ (C : Set ℝ), (K : ℕ∞) * (⨅ (h : IsCover (Real.toNNReal R) S C), C.encard) := by
      congr with C
      exact h_iInf_pointwise C
    rw [h3]
    rw [ENat.mul_iInf]
  have h4 : externalCoveringNumber (Real.toNNReal r) S ≤
      ⨅ (C : Set ℝ) (_ : IsCover (Real.toNNReal R) S C), (K : ℕ∞) * C.encard := by
    exact le_iInf₂ h1
  have h5 : (⨅ (C : Set ℝ) (_ : IsCover (Real.toNNReal R) S C), (K : ℕ∞) * C.encard) =
      (K : ℕ∞) * externalCoveringNumber (Real.toNNReal R) S := by
    simpa [externalCoveringNumber] using h2
  rw [h5] at h4
  exact h4

/--
Transfer a one-dimensional covering through a pointwise approximation.

If every point of `S` is within distance `err` of a point of `T`, then every
radius-`r` cover of `T` is a radius-`r + err` cover of `S`.
-/
lemma external_covering_number_approx_transfer1D
    {r err : ℝ} (hr : 0 < r) (herr : 0 ≤ err)
    {S T : Set ℝ}
    (happrox : ∀ y ∈ S, ∃ x ∈ T, dist y x ≤ err) :
    externalCoveringNumber (Real.toNNReal (r + err)) S ≤
      externalCoveringNumber (Real.toNNReal r) T := by
  have hsum_nonneg : 0 ≤ r + err := by linarith
  have hr_coe :
      (Real.toNNReal r : ENNReal) = ENNReal.ofReal r := by
    rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal r hr.le]
  have hsum_coe :
      (Real.toNNReal (r + err) : ENNReal) =
        ENNReal.ofReal (r + err) := by
    rw [ENNReal.coe_nnreal_eq,
      Real.coe_toNNReal (r + err) hsum_nonneg]
  have hcover :
      ∀ (centers : Set ℝ),
        IsCover (Real.toNNReal r) T centers →
          IsCover (Real.toNNReal (r + err)) S centers := by
    intro centers hcenters y hy
    rcases happrox y hy with ⟨x, hx, hyx⟩
    rcases hcenters hx with ⟨center, hcenter, hxc⟩
    change edist x center ≤
      (Real.toNNReal r : ENNReal) at hxc
    have hyx_edist :
        edist y x ≤ ENNReal.ofReal err := by
      rw [edist_dist]
      exact
        (ENNReal.ofReal_le_ofReal_iff herr).2 hyx
    have hxc_edist :
        edist x center ≤ ENNReal.ofReal r := by
      simpa [hr_coe] using hxc
    refine ⟨center, hcenter, ?_⟩
    calc
      edist y center ≤ edist y x + edist x center :=
        edist_triangle y x center
      _ ≤ ENNReal.ofReal err + ENNReal.ofReal r := by
        exact add_le_add hyx_edist hxc_edist
      _ = ENNReal.ofReal (r + err) := by
        rw [add_comm r err,
          ENNReal.ofReal_add herr hr.le]
      _ = (Real.toNNReal (r + err) : ENNReal) :=
        hsum_coe.symm
  apply le_iInf₂
  intro centers hcenters
  exact
    IsCover.externalCoveringNumber_le_encard
      (hcover centers hcenters)

/--
Upper bound on 1D covering number from diameter.

For a finite nonempty set `S ⊆ ℝ` and `r > 0`,
`externalCoveringNumber r S ≤ diam(S)/(2r) + 1`.

Equivalently, if the covering number is at least `K`, then
`diam(S) ≥ 2r * (K - 1)`.
-/
lemma covering_upper_from_diam1D (S : Finset ℝ) (hne : S.Nonempty) {r : ℝ} (hr : 0 < r) :
    (Metric.externalCoveringNumber (Real.toNNReal r) (S : Set ℝ) : ENNReal) ≤
    ENNReal.ofReal ((S.max' hne - S.min' hne) / (2 * r) + 1) := by
  let m : ℝ := S.min' hne
  let M : ℝ := S.max' hne
  let diam : ℝ := M - m
  have h1 : ∀ x ∈ S, m ≤ x := fun x hx => Finset.min'_le S x hx
  have h2 : ∀ x ∈ S, x ≤ M := fun x hx => Finset.le_max' S x hx
  let K : ℕ := Nat.floor (diam / (2 * r)) + 1
  let centers : Finset ℝ := Finset.image (fun k : ℕ => m + r + 2 * (k : ℝ) * r) (Finset.range K)
  have hK_pos : 0 < K := by positivity
  have h_cover : ∀ x ∈ S, ∃ c ∈ centers, dist x c ≤ r := by
    intro x hx
    have hml : m ≤ x := h1 x hx
    have hmr : x ≤ M := h2 x hx
    let t : ℝ := x - m
    have ht0 : 0 ≤ t := by linarith
    have htd : t ≤ diam := by linarith
    let k : ℕ := Nat.floor (t / (2 * r))
    have hk1 : (k : ℝ) ≤ t / (2 * r) := Nat.floor_le (by positivity)
    have hk2 : t / (2 * r) < (k : ℝ) + 1 := Nat.lt_floor_add_one (t / (2 * r))
    have hkK : k < K := by
      have h4 : t / (2 * r) ≤ diam / (2 * r) := by gcongr
      have h5 : k ≤ Nat.floor (diam / (2 * r)) := Nat.floor_mono h4
      simp [K] at * <;> omega
    let c : ℝ := m + r + 2 * (k : ℝ) * r
    have hc : c ∈ centers := Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hkK, rfl⟩
    have hdist : dist x c ≤ r := by
      have h6 : x - c = t - r - 2 * (k : ℝ) * r := by simp [c, t] <;> ring
      have h7 : -r ≤ t - r - 2 * (k : ℝ) * r := by
        have h81 : (k : ℝ) * (2 * r) ≤ (t / (2 * r)) * (2 * r) :=
          mul_le_mul_of_nonneg_right hk1 (by positivity)
        have h82 : (t / (2 * r)) * (2 * r) = t := by field_simp [hr.ne'] <;> ring
        have h83 : 2 * (k : ℝ) * r = (k : ℝ) * (2 * r) := by ring
        rw [h83]
        linarith [h81, h82]
      have h9 : t - r - 2 * (k : ℝ) * r < r := by
        have h10 : t < ((k : ℝ) + 1) * (2 * r) := by
          calc t = (t / (2 * r)) * (2 * r) := by field_simp [hr.ne'] <;> ring
            _ < ((k : ℝ) + 1) * (2 * r) := by gcongr
        linarith
      have h10 : |t - r - 2 * (k : ℝ) * r| ≤ r := by
        rw [abs_le] <;> constructor <;> linarith
      simpa [dist_eq_norm, h6] using h10
    exact ⟨c, hc, hdist⟩
  have h_is_cover : Metric.IsCover (Real.toNNReal r) (S : Set ℝ) (centers : Set ℝ) := by
    intro x hx
    rcases h_cover x hx with ⟨c, hc, hdist⟩
    have h11 : 0 ≤ r := by linarith
    have h12 : edist x c ≤ (Real.toNNReal r : ENNReal) := by
      have h13 : edist x c = ENNReal.ofReal (dist x c) := edist_dist x c
      rw [h13]
      exact (ENNReal.ofReal_le_ofReal_iff h11).mpr hdist
    exact ⟨c, hc, h12⟩
  have h_card : (centers : Set ℝ).encard ≤ (K : ℕ∞) := by
    have h14 : (centers : Set ℝ).encard = ↑centers.card := Set.encard_coe_eq_coe_finsetCard centers
    rw [h14]
    have h15 : centers.card ≤ K := by
      have h151 : centers.card ≤ (Finset.range K).card := Finset.card_image_le
      have h152 : (Finset.range K).card = K := Finset.card_range K
      rw [h152] at h151
      exact h151
    exact_mod_cast h15
  have h_main_nat : Metric.externalCoveringNumber (Real.toNNReal r) (S : Set ℝ) ≤ (K : ℕ∞) :=
    le_trans (Metric.IsCover.externalCoveringNumber_le_encard h_is_cover) h_card
  have h_main : (Metric.externalCoveringNumber (Real.toNNReal r) (S : Set ℝ) : ENNReal) ≤ (K : ENNReal) := by
    exact_mod_cast h_main_nat
  have h_diam_nonneg : 0 ≤ diam := by
    have hml : m ≤ M := h1 M (Finset.max'_mem S hne)
    simp [diam] <;> linarith
  have hK_real : (K : ℝ) ≤ diam / (2 * r) + 1 := by
    have h16 : (Nat.floor (diam / (2 * r)) : ℝ) ≤ diam / (2 * r) := Nat.floor_le (by positivity)
    simp [K] <;> linarith
  have h_pos : 0 ≤ diam / (2 * r) + 1 := by
    have h17 : 0 ≤ diam / (2 * r) := by positivity
    linarith
  have h_final : (K : ENNReal) ≤ ENNReal.ofReal (diam / (2 * r) + 1) := by
    have h19 : (K : ENNReal) = ENNReal.ofReal (K : ℝ) := by simp
    rw [h19]
    exact (ENNReal.ofReal_le_ofReal_iff h_pos).mpr hK_real
  exact le_trans h_main h_final

/--
Diameter upper bound on the 1D covering number.

For a finite nonempty set `S ⊆ ℝ` with min `a` and max `b`,
the covering number at scale `r` satisfies
`N ≤ (b - a) / (2 * r) + 1`, hence `b - a ≥ 2 * r * (N - 1)`.

We explicitly cover `[a, b]` by `floor((b-a)/(2r)) + 1` intervals
of length `2r` centered at `a + r + 2*r*i`.
-/
lemma external_covering_number_le_diam1D {r : ℝ} (hr : 0 < r) {S : Set ℝ}
    (hfin : S.Finite) (hne : S.Nonempty) :
    ∃ (a b : ℝ), a ∈ S ∧ b ∈ S ∧ S ⊆ Set.Icc a b ∧
      (Metric.externalCoveringNumber (Real.toNNReal r) S : ENNReal) ≤
        ENNReal.ofReal ((b - a) / (2 * r) + 1) := by
  let sf : Finset ℝ := hfin.toFinset
  have hsf : (sf : Set ℝ) = S := hfin.coe_toFinset
  have hsfne : sf.Nonempty := by
    rcases hne with ⟨x, hx⟩
    exact ⟨x, by simpa [sf, hsf] using hx⟩
  let a := sf.min' hsfne
  let b := sf.max' hsfne
  have ha : a ∈ S := by simpa [sf, hsf] using sf.min'_mem hsfne
  have hb : b ∈ S := by simpa [sf, hsf] using sf.max'_mem hsfne
  have h_bounds : ∀ x ∈ S, a ≤ x ∧ x ≤ b := fun x hx =>
    have hx' : x ∈ sf := by simpa [sf, hsf] using hx
    ⟨sf.min'_le x hx', sf.le_max' x hx'⟩
  have h_S_sub : S ⊆ Set.Icc a b := by
    intro x hx
    exact ⟨(h_bounds x hx).1, (h_bounds x hx).2⟩
  let K : ℕ := Nat.floor ((b - a) / (2 * r)) + 1
  have hK_pos : 0 < K := by positivity
  let centers : Finset ℝ := Finset.image (fun i : ℕ => a + r + 2 * r * (i : ℝ)) (Finset.range K)
  have h_cover : ∀ x ∈ S, ∃ c ∈ centers, dist x c ≤ r := by
    intro x hx
    have h1 : a ≤ x := (h_bounds x hx).1
    have h2 : x ≤ b := (h_bounds x hx).2
    let t : ℝ := x - a
    have ht0 : 0 ≤ t := by linarith
    have htb : t ≤ b - a := by linarith
    let i : ℕ := Nat.floor (t / (2 * r))
    have hi1 : (i : ℝ) ≤ t / (2 * r) := Nat.floor_le (by positivity)
    have hi2 : t / (2 * r) < (i : ℝ) + 1 := Nat.lt_floor_add_one _
    have hiK : i < K := by
      have h4 : t / (2 * r) ≤ (b - a) / (2 * r) := by gcongr
      have h5 : i ≤ Nat.floor ((b - a) / (2 * r)) := Nat.floor_mono h4
      simp [K] at * <;> omega
    let c : ℝ := a + r + 2 * r * (i : ℝ)
    have hc_in : c ∈ centers := Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hiK, by simp [c]⟩
    have h6 : 0 ≤ t - 2 * r * (i : ℝ) := by
      have h7 : 2 * r * (i : ℝ) ≤ t := by
        calc 2 * r * (i : ℝ) ≤ 2 * r * (t / (2 * r)) := by gcongr
          _ = t := by field_simp [hr.ne'] <;> ring
      linarith
    have h8 : t - 2 * r * (i : ℝ) < 2 * r := by
      have h9 : t < 2 * r * ((i : ℝ) + 1) := by
        have h91 : t / (2 * r) < (i : ℝ) + 1 := hi2
        have h92 : t = (t / (2 * r)) * (2 * r) := by field_simp [hr.ne'] <;> ring
        rw [h92]
        have h93 : (t / (2 * r)) * (2 * r) < 2 * r * ((i : ℝ) + 1) := by
          have h94 : (t / (2 * r)) * (2 * r) < ((i : ℝ) + 1) * (2 * r) := by
            exact mul_lt_mul_of_pos_right h91 (by positivity)
          have h95 : ((i : ℝ) + 1) * (2 * r) = 2 * r * ((i : ℝ) + 1) := by ring
          rw [h95] at h94
          exact h94
        exact h93
      linarith
    have h_dist : dist x c ≤ r := by
      have h_eq : x - c = (t - 2 * r * (i : ℝ)) - r := by simp [c, t] <;> ring
      have h10 : |x - c| ≤ r := by
        rw [h_eq]
        have h11 : -r ≤ (t - 2 * r * (i : ℝ)) - r := by linarith
        have h12 : (t - 2 * r * (i : ℝ)) - r ≤ r := by linarith
        exact abs_le.mpr ⟨h11, h12⟩
      simpa [dist_eq_norm] using h10
    exact ⟨c, hc_in, h_dist⟩
  have hr_nonneg : 0 ≤ r := by linarith
  have h_is_cover : IsCover (Real.toNNReal r) S (centers : Set ℝ) := by
    intro x hx
    rcases h_cover x hx with ⟨c, hc, hdist⟩
    have h51 : (Real.toNNReal r : ENNReal) = ENNReal.ofReal r := by
      have h_eq : Real.toNNReal r = NNReal.mk r hr_nonneg := Real.toNNReal_of_nonneg hr_nonneg
      have h_coe : (Real.toNNReal r : ℝ) = r := by
        calc (Real.toNNReal r : ℝ) = (NNReal.mk r hr_nonneg : ℝ) := by rw [h_eq]
          _ = r := by simp
      have h : (Real.toNNReal r : ENNReal) = ENNReal.ofReal (Real.toNNReal r : ℝ) := ENNReal.coe_nnreal_eq (Real.toNNReal r)
      rw [h, h_coe]
    have h5 : edist x c ≤ (Real.toNNReal r : ENNReal) := by
      have h52 : edist x c = ENNReal.ofReal (dist x c) := edist_dist x c
      rw [h52, h51]
      exact (ENNReal.ofReal_le_ofReal_iff hr_nonneg).mpr hdist
    exact ⟨c, hc, h5⟩
  have h_card : (centers : Set ℝ).encard ≤ (K : ℕ∞) := by
    have h1 : (centers : Set ℝ).encard = ↑(centers.card) := Set.encard_coe_eq_coe_finsetCard centers
    have h2 : centers.card ≤ K := Finset.card_image_le.trans (by simp)
    rw [h1]
    exact_mod_cast h2
  have h_main : Metric.externalCoveringNumber (Real.toNNReal r) S ≤ (K : ℕ∞) :=
    le_trans (IsCover.externalCoveringNumber_le_encard h_is_cover) h_card
  have hba : a ≤ b := sf.min'_le_max' hsfne
  have hK_real : (K : ℝ) ≤ (b - a) / (2 * r) + 1 := by
    have h_nonneg : 0 ≤ (b - a) / (2 * r) := by
      have h : 0 ≤ b - a := by linarith
      positivity
    have h1 : (Nat.floor ((b - a) / (2 * r)) : ℝ) ≤ (b - a) / (2 * r) := Nat.floor_le h_nonneg
    simp [K] <;> linarith
  have h_pos : 0 ≤ (b - a) / (2 * r) + 1 := by
    have h : 0 ≤ b - a := by linarith
    positivity
  refine ⟨a, b, ha, hb, h_S_sub, ?_⟩
  have h3 : (Metric.externalCoveringNumber (Real.toNNReal r) S : ENNReal) ≤ ENNReal.ofReal (K : ℝ) := by
    exact_mod_cast h_main
  have h4 : ENNReal.ofReal (K : ℝ) ≤ ENNReal.ofReal ((b - a) / (2 * r) + 1) := by
    exact (ENNReal.ofReal_le_ofReal_iff h_pos).mpr hK_real
  exact h3.trans h4

/--
Diameter lower bound from a covering number lower bound in `ℝ`.

If a finite nonempty set `S ⊆ ℝ` has external covering number at scale `r`
at least `M` (a natural number), then its diameter `b - a` satisfies
`b - a ≥ 2 * r * (M - 1)`.

This is the contrapositive of `external_covering_number_le_diam1D`.
-/
lemma diam_lower_from_covering1D {r : ℝ} (hr : 0 < r) {S : Set ℝ}
    (hfin : S.Finite) (hne : S.Nonempty) {M : ℕ} (hM : M ≥ 1)
    (hcover : (M : ENNReal) ≤ (Metric.externalCoveringNumber (Real.toNNReal r) S : ENNReal)) :
    ∃ (a b : ℝ), a ∈ S ∧ b ∈ S ∧ S ⊆ Set.Icc a b ∧
      (b - a : ℝ) ≥ 2 * r * ((M : ℝ) - 1) := by
  rcases external_covering_number_le_diam1D hr hfin hne with ⟨a, b, ha, hb, hsub, hle⟩
  have h1 : (M : ENNReal) ≤ ENNReal.ofReal ((b - a) / (2 * r) + 1) :=
    hcover.trans hle
  have hba : a ≤ b := (hsub ha).2
  have h_pos : 0 ≤ (b - a) / (2 * r) + 1 := by
    have h : 0 ≤ b - a := by linarith
    positivity
  have h2 : (M : ℝ) ≤ (b - a) / (2 * r) + 1 := by
    have h21 : (M : ENNReal) = ENNReal.ofReal (M : ℝ) := by simp
    rw [h21] at h1
    exact (ENNReal.ofReal_le_ofReal_iff h_pos).mp h1
  have h3 : (b - a : ℝ) ≥ 2 * r * ((M : ℝ) - 1) := by
    have h4 : (M : ℝ) - 1 ≤ (b - a) / (2 * r) := by linarith
    have h5 : 2 * r * ((M : ℝ) - 1) ≤ 2 * r * ((b - a) / (2 * r)) := by
      gcongr
      <;> linarith
    have h6 : 2 * r * ((b - a) / (2 * r)) = b - a := by
      field_simp [hr.ne'] <;> ring
    linarith
  exact ⟨a, b, ha, hb, hsub, h3⟩

end Kakeya.Assouad
