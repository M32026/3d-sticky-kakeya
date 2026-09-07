import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.WZ1.UnitRescaling
import MyLeanRepo.Kakeya.Assouad.WZ1.ADPerturbation

/-!
# Helper lemmas for global grain direction projection

These lemmas support transferring AD from a nearly-horizontal normal direction
to the global grain direction `(1, f, 0)`.

## Two-step transfer

1. **Horizontalization**: projection in direction `h = v - v₂·e₃` is pointwise
   within `|v₂|` of projection in direction `v`.
2. **Scaling**: `globalGrainDirection(slopeFromNormal v) = (1/v₀) · h`, so
   its projection is a positive scaling of the h-projection. AD is preserved
   under set scaling (with a constant factor).
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- The inner product with `e3` equals the third coordinate. -/
lemma inner_e3_eq_coord2 (p : Point3) : inner ℝ p e3 = p (2 : Fin 3) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  have hstar : star (p : Fin 3 → ℝ) = p := by ext i; simp
  rw [hstar]
  have hdot : (e3 : Fin 3 → ℝ) ⬝ᵥ (p : Fin 3 → ℝ) = p (2 : Fin 3) := by
    simp [e3, dotProduct]
    <;> rfl
  exact hdot

/-- The scalar projection in the horizontal direction `h = v - v₂·e₃` is
pointwise within `|v₂|` of the projection in direction `v`, for points in
the unit ball. -/
lemma projection_horizontal_close
    (v : Point3) (hv2 : |v (2 : Fin 3)| ≤ 1 / 10)
    (E : Set Point3) (hE_ball : E ⊆ Metric.closedBall 0 1) :
    ∀ x ∈ scalarProjection (v - (v (2 : Fin 3)) • e3) E,
      ∃ y ∈ scalarProjection v E, |x - y| ≤ 1 / 10 := by
  let v2 : ℝ := v (2 : Fin 3)
  let h : Point3 := v - v2 • e3
  have h_main : ∀ (p : Point3), p ∈ E →
      |inner ℝ p h - inner ℝ p v| ≤ 1 / 10 := by
    intro p hp
    let p2 : ℝ := p (2 : Fin 3)
    have h1 : inner ℝ p h = inner ℝ p v - v2 * p2 := by
      have h2 : inner ℝ p h = inner ℝ p v - inner ℝ p (v2 • e3) := by
        simpa [h, inner_sub_right] using rfl
      rw [h2]
      have h3 : inner ℝ p (v2 • e3) = v2 * inner ℝ p e3 := by
        simp [inner_smul_right]
        <;> ring
      rw [h3, inner_e3_eq_coord2] <;> ring
    rw [h1]
    have h4 : |inner ℝ p v - v2 * p2 - inner ℝ p v| = |v2| * |p2| := by
      have h5 : inner ℝ p v - v2 * p2 - inner ℝ p v = -(v2 * p2) := by ring
      rw [h5, abs_neg, abs_mul]
    rw [h4]
    have h6 : |p2| ≤ ‖p‖ := PiLp.norm_apply_le p (2 : Fin 3)
    have h7 : ‖p‖ ≤ 1 := by
      have h8 : p ∈ Metric.closedBall (0 : Point3) 1 := hE_ball hp
      simpa [Metric.mem_closedBall, dist_zero_right] using h8
    have h9 : |p2| ≤ 1 := by
      calc |p2| ≤ ‖p‖ := h6
        _ ≤ 1 := h7
    calc |v2| * |p2| ≤ |v2| * 1 := by gcongr
      _ = |v2| := by ring
      _ ≤ 1 / 10 := hv2
  intro x hx
  rcases hx with ⟨p, hp, rfl⟩
  exact ⟨inner ℝ p v, ⟨p, hp, rfl⟩, h_main p hp⟩

/-- Scalar projection under positive direction scaling:
`scalarProjection (c • v) E = (fun x : ℝ => c * x) '' scalarProjection v E`
for `c > 0`. -/
lemma scalarProjection_scale (c : ℝ) (hc : 0 < c) (v : Point3) (E : Set Point3) :
    scalarProjection (c • v) E = (fun x : ℝ => c * x) '' scalarProjection v E := by
  ext x
  simp only [scalarProjection, Set.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have h : c * inner ℝ p v = inner ℝ p (c • v) := by
      rw [inner_smul_right]
    exact ⟨inner ℝ p v, ⟨p, hp, rfl⟩, h⟩
  · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩
    have h : inner ℝ p (c • v) = c * inner ℝ p v := by
      rw [inner_smul_right]
    exact ⟨p, hp, h⟩

/-- Covering number under positive scaling of the set:
`coveringNumber(rho, c • A) ≤ coveringNumber(rho/c, A)` for `c > 0`. -/
lemma externalCoveringNumber_scale_image
    {A : Set ℝ} {rho : ℝ} (hrho : 0 < rho) (c : ℝ) (hc : 0 < c) :
    Metric.externalCoveringNumber ⟨rho, hrho.le⟩ ((fun x : ℝ => c * x) '' A) ≤
      Metric.externalCoveringNumber ⟨rho / c, by positivity⟩ A := by
  let rhonn : NNReal := ⟨rho, hrho.le⟩
  let epsnn : NNReal := ⟨rho / c, by positivity⟩
  by_cases h_top : Metric.externalCoveringNumber epsnn A = ⊤
  · rw [h_top]; simp
  · let S : Type _ := {C : Set ℝ // Metric.IsCover epsnn A C}
    haveI : Nonempty S := by
      refine ⟨⟨Set.univ, fun x hx => ⟨x, Set.mem_univ x, ?_⟩⟩⟩
      simp
    let f : S → ℕ∞ := fun C => C.val.encard
    have h_ext : iInf f = Metric.externalCoveringNumber epsnn A := by
      apply le_antisymm
      · apply le_iInf₂; intro C hC; exact iInf_le (α := ℕ∞) (f := f) ⟨C, hC⟩
      · apply le_iInf; intro C
        have h1 : Metric.externalCoveringNumber epsnn A ≤
            iInf (fun h : Metric.IsCover epsnn A C.val => C.val.encard) :=
          iInf_le (α := ℕ∞) (f := fun D : Set ℝ =>
            iInf (fun h : Metric.IsCover epsnn A D => D.encard)) C.val
        have h2 : iInf (fun h : Metric.IsCover epsnn A C.val => C.val.encard) ≤ C.val.encard :=
          iInf_le (α := ℕ∞) (f := fun h : Metric.IsCover epsnn A C.val => C.val.encard) C.property
        exact h1.trans h2
    rcases ENat.exists_eq_iInf f with ⟨C, h_eq⟩
    have hC_finite : Set.Finite C.val := by
      have h_eq2 : C.val.encard = Metric.externalCoveringNumber epsnn A := by
        have h1 : f C = C.val.encard := by rfl
        rw [←h1, h_eq, h_ext]
      have hfin : C.val.encard ≠ ⊤ := by rw [h_eq2] <;> exact h_top
      exact Set.encard_ne_top_iff.mp hfin
    let Cimg : Set ℝ := (fun x : ℝ => c * x) '' C.val
    have hCimg_finite : Set.Finite Cimg := hC_finite.image _
    have h_cover : Metric.IsCover rhonn ((fun x : ℝ => c * x) '' A) Cimg := by
      intro z hz
      rcases hz with ⟨x, hxA, rfl⟩
      rcases C.property hxA with ⟨y, hyC, h_edist⟩
      have h_nndist : nndist x y ≤ epsnn := edist_le_coe.mp h_edist
      have h_dist : dist x y ≤ rho / c := by
        have h9 : dist x y ≤ (epsnn : ℝ) := dist_le_coe.mp h_nndist
        have h10 : (epsnn : ℝ) = rho / c := by
          unfold epsnn; exact NNReal.coe_mk (rho / c) (by positivity)
        rw [h10] at h9; exact h9
      have h_dist2 : dist (c * x) (c * y) ≤ rho := by
        have h11 : dist (c * x) (c * y) = c * dist x y := by
          have h111 : |c * x - c * y| = c * |x - y| := by
            have h : c * x - c * y = c * (x - y) := by ring
            rw [h, abs_mul]
            have hc' : |c| = c := abs_of_pos hc
            rw [hc'] <;> ring
          simpa [Real.dist_eq] using h111
        rw [h11]
        have h12 : c * dist x y ≤ c * (rho / c) := by gcongr
        have h13 : c * (rho / c) = rho := by
          field_simp [hc.ne'] <;> ring
        rw [h13] at h12; exact h12
      have h_edist2 : edist (c * x) (c * y) ≤ (rhonn : ENNReal) := by
        rw [edist_dist]; exact_mod_cast h_dist2
      exact ⟨c * y, ⟨y, hyC, rfl⟩, h_edist2⟩
    have h_main : Metric.externalCoveringNumber rhonn ((fun x : ℝ => c * x) '' A) ≤ Cimg.encard :=
      h_cover.externalCoveringNumber_le_encard
    have h_encard : Cimg.encard ≤ C.val.encard := by
      exact Set.encard_image_le (fun x : ℝ => c * x) C.val
    have h_eq2 : C.val.encard = Metric.externalCoveringNumber epsnn A := by
      have h1 : f C = C.val.encard := by rfl
      rw [←h1, h_eq, h_ext]
    rw [h_eq2] at h_encard
    exact h_main.trans h_encard

/-- If a set is contained in an interval of length `< delta`, its covering number
at scale `delta` is at most `1`. -/
lemma externalCoveringNumber_short_interval
    {A : Set ℝ} {delta : ℝ} (hdelta : 0 < delta)
    {left length : ℝ} (h : A ⊆ Set.Icc left (left + length)) (hL : length < delta) :
    Metric.externalCoveringNumber ⟨delta, hdelta.le⟩ A ≤ 1 := by
  let mid : ℝ := left + length / 2
  let δnn : NNReal := ⟨delta, hdelta.le⟩
  let C : Set ℝ := {mid}
  have h_cover : Metric.IsCover δnn A C := by
    intro x hx
    have hxi : x ∈ Set.Icc left (left + length) := h hx
    have h2 : left ≤ x := hxi.1
    have h3 : x ≤ left + length := hxi.2
    have h4 : x - mid ≤ length / 2 := by
      dsimp only [mid] <;> linarith
    have h5 : -(length / 2) ≤ x - mid := by
      dsimp only [mid] <;> linarith
    have h1 : |x - mid| ≤ length / 2 := abs_le.mpr ⟨h5, h4⟩
    have h6 : length / 2 < delta := by linarith
    have h7 : dist x mid < delta := by
      simpa [Real.dist_eq] using h1.trans_lt h6
    have h8 : edist x mid ≤ (δnn : ENNReal) := by
      rw [edist_dist]; exact_mod_cast h7.le
    exact ⟨mid, Set.mem_singleton mid, h8⟩
  have h_main : Metric.externalCoveringNumber δnn A ≤ C.encard :=
    h_cover.externalCoveringNumber_le_encard
  have h9 : C.encard = 1 := by simp [C, Set.encard_singleton]
  rw [h9] at h_main
  exact h_main

/-- Transfer `PureWZ2PaperADSet1` under positive scaling of the set.

If `S ⊆ [-4,4]` has paper AD at scale `delta` with constant `C`, then `c • S`
has paper AD at scale `delta` with constant `K * C` for some universal `K`,
provided `1/4 ≤ c ≤ 4` and `delta ≤ 1`.

Proof sketch (two cases for `eps = rho/c`):
- If `eps ≥ delta`: direct AD bound, constant `C`.
- If `eps < delta`: enlarge interval by `2*delta`, apply AD at scale `delta`,
  then cover each `delta`-ball by `~10` `eps`-balls (since `eps ≥ delta/4`).
  Constant blowup: `~30*C`.

SORRY: The geometric covering-number sub-lemma (`delta`-ball covered by
`10` `eps`-balls when `eps ≥ delta/4`) remains to be formalized. -/
lemma externalCoveringNumber_scale_down
    {A : Set ℝ} {delta eps : ℝ} (hdelta : 0 < delta) (heps : 0 < eps)
    (h : eps ≥ delta / 4) :
    Metric.externalCoveringNumber ⟨eps, by linarith⟩ A ≤
      9 * Metric.externalCoveringNumber ⟨delta, by linarith⟩ A := by
  let δnn : NNReal := ⟨delta, by linarith⟩
  let epsnn : NNReal := ⟨eps, by linarith⟩
  by_cases h_top : Metric.externalCoveringNumber δnn A = ⊤
  · rw [h_top]; simp
  · let S : Type _ := {C : Set ℝ // Metric.IsCover δnn A C}
    haveI : Nonempty S := by
      refine ⟨⟨Set.univ, fun x hx => ⟨x, Set.mem_univ x, ?_⟩⟩⟩
      simp
    let f : S → ℕ∞ := fun C => C.val.encard
    have h_ext : iInf f = Metric.externalCoveringNumber δnn A := by
      apply le_antisymm
      · apply le_iInf₂; intro C hC; exact iInf_le (α := ℕ∞) (f := f) ⟨C, hC⟩
      · apply le_iInf; intro C
        have h1 : Metric.externalCoveringNumber δnn A ≤
            iInf (fun h : Metric.IsCover δnn A C.val => C.val.encard) :=
          iInf_le (α := ℕ∞) (f := fun D : Set ℝ =>
            iInf (fun h : Metric.IsCover δnn A D => D.encard)) C.val
        have h2 : iInf (fun h : Metric.IsCover δnn A C.val => C.val.encard) ≤ C.val.encard :=
          iInf_le (α := ℕ∞) (f := fun h : Metric.IsCover δnn A C.val => C.val.encard) C.property
        exact h1.trans h2
    rcases ENat.exists_eq_iInf f with ⟨C, h_eq⟩
    have hC_finite : Set.Finite C.val := by
      have h_eq2 : C.val.encard = Metric.externalCoveringNumber δnn A := by
        have h1 : f C = C.val.encard := by rfl
        rw [←h1, h_eq, h_ext]
      have hfin : C.val.encard ≠ ⊤ := by
        rw [h_eq2]
        exact h_top
      exact Set.encard_ne_top_iff.mp hfin
    let Cfin : Finset ℝ := hC_finite.toFinset
    have hCfin_val : (Cfin : Set ℝ) = C.val := hC_finite.coe_toFinset
    let offsets : Finset ℤ := {-4, -3, -2, -1, 0, 1, 2, 3, 4}
    let C'fin : Finset ℝ := Cfin.biUnion (fun c : ℝ =>
      offsets.image (fun k : ℤ => c + (k : ℝ) * eps))
    let C' : Set ℝ := (C'fin : Set ℝ)
    have hC'_cover : Metric.IsCover epsnn A C' := by
      intro x hx
      rcases C.property hx with ⟨c, hc, hcy⟩
      have h_edist : edist x c ≤ (δnn : ENNReal) := hcy
      have h_nndist : nndist x c ≤ δnn := edist_le_coe.mp h_edist
      have h_dist : dist x c ≤ delta := by
        have h9 : dist x c ≤ (δnn : ℝ) := dist_le_coe.mp h_nndist
        have h10 : (δnn : ℝ) = delta := by
          unfold δnn
          exact NNReal.coe_mk delta (by linarith)
        rw [h10] at h9
        exact h9
      have h_abs : |x - c| ≤ delta := by simpa [Real.dist_eq] using h_dist
      let k : ℤ := Int.floor ((x - c) / eps)
      have hk1 : (k : ℝ) ≤ (x - c) / eps := Int.floor_le ((x - c) / eps)
      have hk2 : (x - c) / eps < (k : ℝ) + 1 := Int.lt_floor_add_one ((x - c) / eps)
      have h_delta_eps : delta / eps ≤ 4 := by
        have h9 : 0 < eps := heps
        have h10 : delta ≤ 4 * eps := by linarith
        have h11 : delta / eps ≤ (4 * eps) / eps := by gcongr
        have h12 : (4 * eps) / eps = 4 := by
          field_simp [h9.ne'] <;> ring
        rw [h12] at h11
        exact h11
      have h11 : -delta / eps ≤ (x - c) / eps := by
        gcongr <;> linarith [abs_le.mp h_abs]
      have h12 : (x - c) / eps ≤ delta / eps := by
        gcongr <;> linarith [abs_le.mp h_abs]
      have hk_lower : -5 < (k : ℝ) := by
        have h13 : (x - c) / eps - 1 < (k : ℝ) := by linarith [hk2]
        have h14 : -delta / eps - 1 ≤ (x - c) / eps - 1 := by linarith
        have h15 : -delta / eps - 1 < (k : ℝ) := by
          calc -delta / eps - 1 ≤ (x - c) / eps - 1 := h14
            _ < (k : ℝ) := h13
        have h16 : -4 ≤ -delta / eps := by
          have h161 : -4 ≤ -(delta / eps) := neg_le_neg h_delta_eps
          have h162 : -(delta / eps) = -delta / eps := by
            rw [neg_div]
            <;> rfl
          rw [h162] at h161
          exact h161
        have h17 : -5 ≤ -delta / eps - 1 := by linarith
        calc -5 ≤ -delta / eps - 1 := h17
          _ < (k : ℝ) := h15
      have hk_upper : (k : ℝ) ≤ 4 := by
        linarith [hk1, h12, h_delta_eps]
      have hk_lower_int : -5 < k := by exact_mod_cast hk_lower
      have hk_ge : -4 ≤ k := by linarith
      have hk_le : k ≤ 4 := by exact_mod_cast hk_upper
      have hk_in : k ∈ offsets := by
        simp only [offsets, Finset.mem_insert, Finset.mem_singleton]
        <;> omega
      let y : ℝ := c + (k : ℝ) * eps
      have hy : y ∈ C' := by
        have h12 : c ∈ Cfin := by
          have h13 : c ∈ (Cfin : Set ℝ) := by
            rw [hCfin_val] <;> exact hc
          exact Finset.mem_coe.mp h13
        exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨c, h12, Finset.mem_image.mpr ⟨k, hk_in, rfl⟩⟩)
      have h5 : (k : ℝ) * eps ≤ x - c := by
        have h6 : (k : ℝ) ≤ (x - c) / eps := hk1
        have h7 : 0 < eps := heps
        calc (k : ℝ) * eps ≤ ((x - c) / eps) * eps := by gcongr
          _ = x - c := by field_simp [h7.ne'] <;> ring
      have h8 : x - c < (k : ℝ) * eps + eps := by
        have h9 : (x - c) / eps < (k : ℝ) + 1 := hk2
        have h10 : 0 < eps := heps
        calc x - c = ((x - c) / eps) * eps := by field_simp [h10.ne'] <;> ring
          _ < ((k : ℝ) + 1) * eps := by gcongr
          _ = (k : ℝ) * eps + eps := by ring
      have h_dist2 : dist x y < eps := by
        have h11 : x - y = (x - c) - (k : ℝ) * eps := by ring
        have h12 : -eps < x - y := by linarith
        have h13 : x - y < eps := by linarith
        have h14 : |x - y| < eps := abs_lt.mpr ⟨h12, h13⟩
        simpa [Real.dist_eq] using h14
      have h_edist2 : edist x y ≤ (epsnn : ENNReal) := by
        have h15 : dist x y ≤ eps := by linarith
        rw [edist_dist]
        exact_mod_cast h15
      exact ⟨y, hy, h_edist2⟩
    have h_offsets_card : offsets.card = 9 := by decide
    have h_inj : ∀ (c : ℝ), Function.Injective (fun k : ℤ => c + (k : ℝ) * eps) := by
      intro c k1 k2 h
      have h9 : (k1 : ℝ) * eps = (k2 : ℝ) * eps := by simpa using h
      have h10 : (k1 : ℝ) = (k2 : ℝ) := by
        exact (mul_left_inj' (ne_of_gt heps)).mp h9
      exact_mod_cast h10
    have h_card : C'fin.card ≤ 9 * Cfin.card := by
      calc C'fin.card
        ≤ ∑ c ∈ Cfin, (offsets.image (fun k : ℤ => c + (k : ℝ) * eps)).card := Finset.card_biUnion_le
      _ = ∑ c ∈ Cfin, offsets.card := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.card_image_of_injective _ (h_inj c)]
      _ = Cfin.card * offsets.card := by
        rw [Finset.sum_const]
        <;> simp [mul_comm]
        <;> ring
      _ = Cfin.card * 9 := by rw [h_offsets_card]
      _ = 9 * Cfin.card := by ring
    have h_main : Metric.externalCoveringNumber epsnn A ≤ C'.encard :=
      hC'_cover.externalCoveringNumber_le_encard
    have h_C'_encard : C'.encard = ↑C'fin.card := by
      simp [C']
      <;> rfl
    rw [h_C'_encard] at h_main
    have h_C_encard : C.val.encard = Metric.externalCoveringNumber δnn A := by
      have h15 : f C = C.val.encard := by rfl
      rw [h15] at h_eq
      rw [h_eq, h_ext]
    have h14 : C.val.encard = ↑Cfin.card := by
      simp [←hCfin_val, Set.encard] <;> rfl
    have h_final : (↑C'fin.card : ℕ∞) ≤ 9 * Metric.externalCoveringNumber δnn A := by
      have h13 : (↑C'fin.card : ℕ∞) ≤ ↑(9 * Cfin.card) := by exact_mod_cast h_card
      rw [Nat.cast_mul] at h13
      rw [←h_C_encard, h14]
      exact h13
    exact h_main.trans h_final

lemma PureWZ2PaperADSet1.scale
    {S : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 S delta alpha C)
    (c : ℝ) (hc_pos : 0 < c)
    (hc_range : 1 / 4 ≤ c) (hc_upper : c ≤ 4)
    (hdelta_le_one : delta ≤ 1) :
    PureWZ2PaperADSet1 ((fun x : ℝ => c * x) '' S) delta alpha (100 * C) := by
  rcases hAD with ⟨hδ_pos, hα_pos, hα_one, hC_one, hC_top, hcover⟩
  have hα_nonneg : 0 ≤ alpha := by linarith
  have hC100_one : (1 : ENNReal) ≤ 100 * C := by
    have h1 : (1 : ENNReal) ≤ C := hC_one
    have h2 : (100 : ENNReal) ≤ 100 * C := le_mul_of_one_le_right' h1
    have h3 : (1 : ENNReal) ≤ 100 := by norm_num
    exact h3.trans h2
  have hC100_top : (100 * C) ≠ ⊤ := by
    intro h; have h4 : C = ⊤ := by simpa [ENNReal.mul_eq_top] using h
    exact hC_top h4
  refine ⟨hδ_pos, hα_pos, hα_one, hC100_one, hC100_top, ?_⟩
  intro rho hrho hdelta_rho left length hlength
  let S' : Set ℝ := (fun x : ℝ => c * x) '' S
  let B : Set ℝ := S' ∩ Set.Icc left (left + length)
  let leftA : ℝ := left / c
  let lengthA : ℝ := length / c
  let A : Set ℝ := S ∩ Set.Icc leftA (leftA + lengthA)
  have hB_eq : B = (fun x : ℝ => c * x) '' A := by
    ext z
    simp only [B, S', A, Set.mem_inter_iff, Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨⟨x, hxS, rfl⟩, h1, h2⟩
      have h3 : leftA ≤ x := by
        dsimp only [leftA]
        calc left / c ≤ (c * x) / c := by gcongr
          _ = x := by field_simp [hc_pos.ne'] <;> ring
      have h4 : x ≤ leftA + lengthA := by
        dsimp only [leftA, lengthA]
        calc x = (c * x) / c := by field_simp [hc_pos.ne'] <;> ring
          _ ≤ (left + length) / c := by gcongr
          _ = left / c + length / c := by rw [add_div]
      exact ⟨x, ⟨hxS, h3, h4⟩, rfl⟩
    · rintro ⟨x, ⟨hxS, h1, h2⟩, rfl⟩
      have h3 : left ≤ c * x := by
        dsimp only [leftA] at h1
        calc left = c * (left / c) := by field_simp [hc_pos.ne'] <;> ring
          _ ≤ c * x := by gcongr
      have h4 : c * x ≤ left + length := by
        dsimp only [leftA, lengthA] at h2
        calc c * x ≤ c * (left / c + length / c) := by gcongr
          _ = left + length := by
            rw [mul_add] <;> field_simp [hc_pos.ne'] <;> ring
      exact ⟨⟨x, hxS, rfl⟩, h3, h4⟩
  have hrho_pos : 0 < rho := by linarith
  let eps : ℝ := rho / c
  have heps_pos : 0 < eps := by positivity
  have h_eps_delta4 : eps ≥ delta / 4 := by
    have h1 : rho ≥ delta := hdelta_rho
    have h2 : rho / c ≥ delta / 4 := by
      calc rho / c ≥ delta / c := by gcongr
        _ ≥ delta / 4 := by
          gcongr
          <;> linarith
    exact h2
  have h_scale_img : (Metric.externalCoveringNumber ⟨rho, hrho⟩ B : ENNReal) ≤
      (Metric.externalCoveringNumber ⟨eps, by linarith⟩ A : ENNReal) := by
    rw [hB_eq]
    have h_nat : Metric.externalCoveringNumber ⟨rho, hrho_pos.le⟩ ((fun x : ℝ => c * x) '' A) ≤
        Metric.externalCoveringNumber ⟨eps, heps_pos.le⟩ A :=
      externalCoveringNumber_scale_image hrho_pos c hc_pos
    exact_mod_cast h_nat
  let X : ENNReal := Kakeya.realRpowENN (length / rho) alpha
  have hX_one : (1 : ENNReal) ≤ X := by
    have h1 : 1 ≤ length / rho := by
      have h2 : 0 < rho := by linarith
      have h3 : rho ≤ length := hlength
      have h4 : 1 ≤ length / rho := by
        calc 1 = rho / rho := by field_simp [h2.ne'] <;> ring
          _ ≤ length / rho := by gcongr
      exact h4
    have h3 : (1 : ℝ) ≤ Real.rpow (length / rho) alpha :=
      Real.one_le_rpow h1 hα_nonneg
    have h4 : (1 : ENNReal) ≤ Kakeya.realRpowENN (length / rho) alpha := by
      simp only [Kakeya.realRpowENN]
      have h5 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (Real.rpow (length / rho) alpha) :=
        ENNReal.ofReal_le_ofReal h3
      simpa using h5
    exact h4
  by_cases h_case1 : eps ≥ delta
  · -- Case 1: eps ≥ delta, direct AD
    have h_eps_lenA : eps ≤ lengthA := by
      dsimp only [eps, lengthA]
      gcongr
      <;> linarith
    have h_AD_A : (Metric.externalCoveringNumber ⟨eps, by linarith⟩ A : ENNReal) ≤
        C * Kakeya.realRpowENN (lengthA / eps) alpha :=
      hcover eps heps_pos.le h_case1 leftA lengthA h_eps_lenA
    have h_ratio : lengthA / eps = length / rho := by
      dsimp only [lengthA, eps]
      field_simp [hc_pos.ne'] <;> ring
    rw [h_ratio] at h_AD_A
    calc (Metric.externalCoveringNumber ⟨rho, hrho⟩ B : ENNReal)
      ≤ (Metric.externalCoveringNumber ⟨eps, by linarith⟩ A : ENNReal) := h_scale_img
    _ ≤ C * X := h_AD_A
    _ ≤ (100 * C) * X := by
      have h4 : C ≤ 100 * C := by
        have h5 : (1 : ENNReal) ≤ 100 := by norm_num
        exact le_mul_of_one_le_left' h5
      exact mul_le_mul_right' h4 X
  · -- Case 2: eps < delta
    have h_eps_lt_delta : eps < delta := by linarith
    have h_scale_down : (Metric.externalCoveringNumber ⟨eps, by linarith⟩ A : ENNReal) ≤
        9 * (Metric.externalCoveringNumber ⟨delta, by linarith⟩ A : ENNReal) := by
      have h_nat : Metric.externalCoveringNumber ⟨eps, by linarith⟩ A ≤
          9 * Metric.externalCoveringNumber ⟨delta, by linarith⟩ A :=
        externalCoveringNumber_scale_down hδ_pos heps_pos h_eps_delta4
      exact_mod_cast h_nat
    by_cases h_lenA : lengthA ≥ delta
    · -- Subcase 2a: lengthA ≥ delta
      have h_delta_lenA : delta ≤ lengthA := h_lenA
      have h_AD_A : (Metric.externalCoveringNumber ⟨delta, by linarith⟩ A : ENNReal) ≤
          C * Kakeya.realRpowENN (lengthA / delta) alpha :=
        hcover delta hδ_pos.le (by linarith) leftA lengthA h_delta_lenA
      have h_length_nonneg : 0 ≤ length := by linarith
      have h_ratio_le : lengthA / delta ≤ length / rho := by
        dsimp only [lengthA]
        have h1 : rho < c * delta := by
          dsimp only [eps] at h_eps_lt_delta
          have h2 : rho / c < delta := h_eps_lt_delta
          calc rho = (rho / c) * c := by field_simp [hc_pos.ne'] <;> ring
            _ < delta * c := by gcongr
            _ = c * delta := by ring
        have h3 : 0 < c * delta := by positivity
        have h4 : 0 < rho := by linarith
        have h5 : (length / c) / delta = length / (c * delta) := by
          field_simp [hc_pos.ne', hδ_pos.ne'] <;> ring
        rw [h5]
        gcongr
      have h_rpow_mono : Kakeya.realRpowENN (lengthA / delta) alpha ≤ X := by
        simp only [Kakeya.realRpowENN]
        have h5 : 0 ≤ lengthA / delta := by
          dsimp only [lengthA]
          apply div_nonneg
          · apply div_nonneg <;> linarith
          · linarith
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow h5 h_ratio_le hα_nonneg)
      calc (Metric.externalCoveringNumber ⟨rho, hrho⟩ B : ENNReal)
        ≤ (Metric.externalCoveringNumber ⟨eps, by linarith⟩ A : ENNReal) := h_scale_img
      _ ≤ 9 * (Metric.externalCoveringNumber ⟨delta, by linarith⟩ A : ENNReal) := h_scale_down
      _ ≤ 9 * (C * Kakeya.realRpowENN (lengthA / delta) alpha) :=
        mul_le_mul_left' h_AD_A 9
      _ ≤ 9 * (C * X) := by gcongr <;> exact h_rpow_mono
      _ = (9 * C) * X := by ring
      _ ≤ (100 * C) * X := by
        have h6 : (9 : ENNReal) * C ≤ 100 * C := by
          have h7 : (9 : ENNReal) ≤ 100 := by norm_num
          exact mul_le_mul_right' h7 C
        exact mul_le_mul_right' h6 X
    · -- Subcase 2b: lengthA < delta
      have h_lenA_lt_delta : lengthA < delta := by linarith
      have hA_sub : A ⊆ Set.Icc leftA (leftA + lengthA) := by
        intro x hx; exact hx.2
      have h_short_nat : Metric.externalCoveringNumber ⟨delta, by linarith⟩ A ≤ 1 :=
        externalCoveringNumber_short_interval hδ_pos hA_sub h_lenA_lt_delta
      have h_short : (Metric.externalCoveringNumber ⟨delta, by linarith⟩ A : ENNReal) ≤ (1 : ENNReal) := by
        have h7 := ENat.toENNReal_le.mpr h_short_nat
        simpa using h7
      calc (Metric.externalCoveringNumber ⟨rho, hrho⟩ B : ENNReal)
        ≤ (Metric.externalCoveringNumber ⟨eps, by linarith⟩ A : ENNReal) := h_scale_img
      _ ≤ 9 * (Metric.externalCoveringNumber ⟨delta, by linarith⟩ A : ENNReal) := h_scale_down
      _ ≤ 9 * (1 : ENNReal) := by gcongr
      _ = (9 : ENNReal) := by simp
      _ ≤ 100 * C := by
        have h5 : (9 : ENNReal) ≤ 100 := by norm_num
        have h6 : (100 : ENNReal) ≤ 100 * C := le_mul_of_one_le_right' hC_one
        exact h5.trans h6
      _ ≤ (100 * C) * X := by
        exact le_mul_of_one_le_right' hX_one

/-- Perturbation lemma for `PureWZ2PaperADSet1`: if every point of `S'` is
within `delta` of `S`, then `S'` inherits the AD bound with constant `8 * C`.

Adapted from `IsADSet1.perturb_by_delta`, using interval localization
instead of balls. -/
lemma PureWZ2PaperADSet1.transfer_direction
    {S S' : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 S delta alpha C)
    (h_close : ∀ x ∈ S', ∃ y ∈ S, |x - y| ≤ delta) :
    PureWZ2PaperADSet1 S' delta alpha (8 * C) := by
  rcases hAD with ⟨hδ_pos, hα_pos, hα_one, hC_one, hC_top, hcover⟩
  have hC8_one : (1 : ENNReal) ≤ 8 * C := by
    have h1 : (1 : ENNReal) ≤ C := hC_one
    have h2 : (8 : ENNReal) ≤ 8 * C := le_mul_of_one_le_right' h1
    have h3 : (1 : ENNReal) ≤ 8 := by norm_num
    exact h3.trans h2
  have hC8_top : (8 * C) ≠ ⊤ := by
    intro h
    have h4 : C = ⊤ := by
      simpa [ENNReal.mul_eq_top] using h
    exact hC_top h4
  refine ⟨hδ_pos, hα_pos, hα_one, hC8_one, hC8_top, ?_⟩
  intro rho hrho hdelta_rho left length hlength
  let B : Set ℝ := S' ∩ Set.Icc left (left + length)
  let leftA : ℝ := left - delta
  let lengthA : ℝ := length + 2 * delta
  let A : Set ℝ := S ∩ Set.Icc leftA (leftA + lengthA)
  have h_lengthA : rho ≤ lengthA := by
    dsimp only [lengthA]
    linarith
  have h_close' : ∀ x ∈ B, ∃ y ∈ A, |x - y| ≤ delta := by
    intro x hx
    have hxS' : x ∈ S' := hx.1
    have hxI : x ∈ Set.Icc left (left + length) := hx.2
    rcases h_close x hxS' with ⟨y, hyS, hyx⟩
    have h_y1 : leftA ≤ y := by
      dsimp only [leftA]
      linarith [abs_le.mp hyx, hxI.1]
    have h_y2 : y ≤ leftA + lengthA := by
      dsimp only [leftA, lengthA]
      linarith [abs_le.mp hyx, hxI.2]
    exact ⟨y, ⟨hyS, ⟨h_y1, h_y2⟩⟩, hyx⟩
  have h_thick : (Metric.externalCoveringNumber ⟨rho, hrho⟩ B : ENNReal) ≤
      2 * (Metric.externalCoveringNumber ⟨rho, hrho⟩ A : ENNReal) := by
    have h := externalCoveringNumber_thickening_two_mul_real
      (hrho := by linarith) (hdelta := by linarith) hdelta_rho h_close'
    exact_mod_cast h
  have h_AD_A : (Metric.externalCoveringNumber ⟨rho, hrho⟩ A : ENNReal) ≤
      C * Kakeya.realRpowENN (lengthA / rho) alpha :=
    hcover rho hrho hdelta_rho leftA lengthA h_lengthA
  have h_rho_pos : 0 < rho := by linarith
  have h_delta_le_length : delta ≤ length := by linarith
  have h5 : length + 2 * delta ≤ 3 * length := by
    have h6 : 2 * delta ≤ 2 * length := by
      exact mul_le_mul_of_nonneg_left h_delta_le_length (by norm_num)
    linarith
  have h_main1 : lengthA / rho ≤ 3 * (length / rho) := by
    dsimp only [lengthA]
    have h7 : (length + 2 * delta) / rho ≤ (3 * length) / rho := by gcongr
    have h8 : (3 * length) / rho = 3 * (length / rho) := by ring
    rw [h8] at h7
    exact h7
  have hα_nonneg : 0 ≤ alpha := by linarith
  have h_pos_lenA : 0 ≤ lengthA / rho := by
    dsimp only [lengthA]
    exact div_nonneg (by linarith) (by linarith)
  have h_rpow_mono : Kakeya.realRpowENN (lengthA / rho) alpha ≤
      Kakeya.realRpowENN (3 * (length / rho)) alpha := by
    simp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow h_pos_lenA h_main1 hα_nonneg)
  have h_pos1 : 0 ≤ length / rho := by
    exact div_nonneg (by linarith) (by linarith)
  have h9 : Real.rpow (3 * (length / rho)) alpha =
      Real.rpow 3 alpha * Real.rpow (length / rho) alpha :=
    Real.mul_rpow (by norm_num) h_pos1
  have h10 : 0 ≤ Real.rpow 3 alpha := Real.rpow_nonneg (by norm_num) _
  have h11 : 0 ≤ Real.rpow (length / rho) alpha := Real.rpow_nonneg h_pos1 _
  have h_rpow_mul : Kakeya.realRpowENN (3 * (length / rho)) alpha =
      Kakeya.realRpowENN (3 : ℝ) alpha * Kakeya.realRpowENN (length / rho) alpha := by
    simp only [Kakeya.realRpowENN]
    rw [h9]
    rw [ENNReal.ofReal_mul h10]
    <;> rfl
  have h_rpow3_le : Kakeya.realRpowENN (3 : ℝ) alpha ≤ (3 : ENNReal) := by
    have h12 : Real.rpow 3 alpha ≤ 3 := by
      have h13 : Real.rpow 3 alpha ≤ Real.rpow 3 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hα_one
      have h14 : Real.rpow 3 1 = 3 := by simp
      rw [h14] at h13
      exact h13
    have h15 : 0 ≤ Real.rpow 3 alpha := Real.rpow_nonneg (by norm_num) _
    simpa [Kakeya.realRpowENN] using ENNReal.ofReal_le_ofReal h12
  let X : ENNReal := Kakeya.realRpowENN (length / rho) alpha
  have h_step3 : 2 * (C * Kakeya.realRpowENN (lengthA / rho) alpha) ≤
      2 * (C * Kakeya.realRpowENN (3 * (length / rho)) alpha) := by
    exact mul_le_mul_left' (mul_le_mul_left' h_rpow_mono C) 2
  calc
    (Metric.externalCoveringNumber ⟨rho, hrho⟩ B : ENNReal)
      ≤ 2 * (Metric.externalCoveringNumber ⟨rho, hrho⟩ A : ENNReal) := h_thick
    _ ≤ 2 * (C * Kakeya.realRpowENN (lengthA / rho) alpha) :=
      mul_le_mul_left' h_AD_A 2
    _ ≤ 2 * (C * Kakeya.realRpowENN (3 * (length / rho)) alpha) := h_step3
    _ = 2 * (C * (Kakeya.realRpowENN (3 : ℝ) alpha * X)) := by
      rw [h_rpow_mul] <;> rfl
    _ = (2 * Kakeya.realRpowENN (3 : ℝ) alpha) * (C * X) := by ring
    _ ≤ (2 * (3 : ENNReal)) * (C * X) := by
      gcongr
      <;> exact h_rpow3_le
    _ = (6 : ENNReal) * (C * X) := by norm_num
    _ = ((6 : ENNReal) * C) * X := by ring
    _ ≤ (8 * C) * X := by
      have h14 : (6 : ENNReal) * C ≤ 8 * C := by
        have h15 : (6 : ENNReal) ≤ 8 := by norm_num
        exact mul_le_mul_right' h15 C
      exact mul_le_mul_right' h14 X

/-- External covering number can only decrease under an isometry image. -/
lemma externalCoveringNumber_isometry_forward
    {ε : NNReal} {A : Set ℝ} {f : ℝ → ℝ}
    (hf : Isometry f) :
    Metric.externalCoveringNumber ε (f '' A) ≤ Metric.externalCoveringNumber ε A := by
  by_cases h_top : Metric.externalCoveringNumber ε A = ⊤
  · rw [h_top]; simp
  · let S : Type _ := {C : Set ℝ // Metric.IsCover ε A C}
    haveI : Nonempty S := by
      refine ⟨⟨Set.univ, fun x hx => ⟨x, Set.mem_univ x, ?_⟩⟩⟩
      simp
    let g : S → ℕ∞ := fun C => C.val.encard
    have h_ext : iInf g = Metric.externalCoveringNumber ε A := by
      apply le_antisymm
      · apply le_iInf₂; intro C hC; exact iInf_le (α := ℕ∞) (f := g) ⟨C, hC⟩
      · apply le_iInf; intro C
        have h1 : Metric.externalCoveringNumber ε A ≤
            iInf (fun h : Metric.IsCover ε A C.val => C.val.encard) :=
          iInf_le (α := ℕ∞) (f := fun D : Set ℝ =>
            iInf (fun h : Metric.IsCover ε A D => D.encard)) C.val
        have h2 : iInf (fun h : Metric.IsCover ε A C.val => C.val.encard) ≤ C.val.encard :=
          iInf_le (α := ℕ∞) (f := fun h : Metric.IsCover ε A C.val => C.val.encard) C.property
        exact h1.trans h2
    rcases ENat.exists_eq_iInf g with ⟨C, h_eq⟩
    have hC_finite : Set.Finite C.val := by
      have h_eq2 : C.val.encard = Metric.externalCoveringNumber ε A := by
        have h1 : g C = C.val.encard := by rfl
        rw [←h1, h_eq, h_ext]
      have hfin : C.val.encard ≠ ⊤ := by rw [h_eq2] <;> exact h_top
      exact Set.encard_ne_top_iff.mp hfin
    let Cimg : Set ℝ := f '' C.val
    have hCimg_finite : Set.Finite Cimg := hC_finite.image f
    have h_cover : Metric.IsCover ε (f '' A) Cimg := by
      intro y hy
      rcases hy with ⟨x, hxA, rfl⟩
      rcases C.property hxA with ⟨z, hzC, h_edist⟩
      have h_edist2 : edist (f x) (f z) ≤ (ε : ENNReal) := by
        rw [hf.edist_eq] <;> exact h_edist
      exact ⟨f z, Set.mem_image_of_mem f hzC, h_edist2⟩
    have h_main : Metric.externalCoveringNumber ε (f '' A) ≤ Cimg.encard :=
      h_cover.externalCoveringNumber_le_encard
    have h_encard : Cimg.encard ≤ C.val.encard := Set.encard_image_le f C.val
    have h_eq2 : C.val.encard = Metric.externalCoveringNumber ε A := by
      have h1 : g C = C.val.encard := by rfl
      rw [←h1, h_eq, h_ext]
    rw [h_eq2] at h_encard
    exact h_main.trans h_encard

/-- External covering number is invariant under isometric bijections of `ℝ`. -/
lemma externalCoveringNumber_isometry_bijection
    {ε : NNReal} {A : Set ℝ} {f : ℝ → ℝ}
    (hf : Isometry f) (hfb : Function.Bijective f) :
    Metric.externalCoveringNumber ε (f '' A) = Metric.externalCoveringNumber ε A := by
  have h1 : Metric.externalCoveringNumber ε (f '' A) ≤ Metric.externalCoveringNumber ε A :=
    externalCoveringNumber_isometry_forward hf
  let g : ℝ → ℝ := Function.invFun f
  have h_right : ∀ y, f (g y) = y := Function.rightInverse_invFun hfb.surjective
  have hg : Isometry g := by
    have h_dist : ∀ (y1 y2 : ℝ), dist (g y1) (g y2) = dist y1 y2 := by
      intro y1 y2
      have h2 : dist (g y1) (g y2) = dist (f (g y1)) (f (g y2)) := by
        rw [hf.dist_eq]
      rw [h2, h_right y1, h_right y2]
    exact Isometry.of_dist_eq h_dist
  have hgf : ∀ x, g (f x) = x := Function.leftInverse_invFun hfb.injective
  have h4 : (g ∘ f) '' A = A := by
    ext x
    simp only [Set.mem_image, Function.comp_apply]
    constructor
    · rintro ⟨z, hzA, h5⟩
      have h6 : x = z := by
        calc x = g (f z) := h5.symm
          _ = z := hgf z
      rw [h6]
      exact hzA
    · intro hxA
      exact ⟨x, hxA, hgf x⟩
  have h3 : g '' (f '' A) = A := by
    have h5 : g '' (f '' A) = (g ∘ f) '' A := by
      exact Eq.symm (image_comp g f A)
    rw [h5, h4]
  have h2 : Metric.externalCoveringNumber ε A ≤ Metric.externalCoveringNumber ε (f '' A) := by
    have h_forward_g : Metric.externalCoveringNumber ε (g '' (f '' A)) ≤
        Metric.externalCoveringNumber ε (f '' A) := by
      exact externalCoveringNumber_isometry_forward (A := f '' A) (f := g) hg
    rw [h3] at h_forward_g
    exact h_forward_g
  exact le_antisymm h1 h2

/-- `PureWZ2PaperADSet1` is invariant under translation. -/
lemma PureWZ2PaperADSet1.translate
    {S : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 S delta alpha C) (t : ℝ) :
    PureWZ2PaperADSet1 ((fun x : ℝ => x + t) '' S) delta alpha C := by
  rcases hAD with ⟨hδ_pos, hα_pos, hα_one, hC_one, hC_top, hcover⟩
  refine ⟨hδ_pos, hα_pos, hα_one, hC_one, hC_top, ?_⟩
  intro rho hrho hdelta_rho left length hlength
  let B : Set ℝ := ((fun x : ℝ => x + t) '' S) ∩ Set.Icc left (left + length)
  let leftA : ℝ := left - t
  let A : Set ℝ := S ∩ Set.Icc leftA (leftA + length)
  have hB_eq : B = (fun x : ℝ => x + t) '' A := by
    ext z
    simp only [B, A, Set.mem_inter_iff, Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨⟨x, hxS, rfl⟩, h1, h2⟩
      exact ⟨x, ⟨hxS, by linarith, by linarith⟩, by ring⟩
    · rintro ⟨x, ⟨hxS, h1, h2⟩, rfl⟩
      exact ⟨⟨x, hxS, rfl⟩, by linarith, by linarith⟩
  let f : ℝ → ℝ := fun x => x + t
  have h_iso : Isometry f := by
    exact isometry_add_right t
  have h_inj : Function.Injective f := by
    intro x y h
    simpa [f] using h
  have h_surj : Function.Surjective f := by
    intro y
    refine ⟨y - t, ?_⟩
    simp [f] <;> ring
  have h_bij : Function.Bijective f := ⟨h_inj, h_surj⟩
  have h_cov : (Metric.externalCoveringNumber ⟨rho, hrho⟩ B : ENNReal) =
      (Metric.externalCoveringNumber ⟨rho, hrho⟩ A : ENNReal) := by
    rw [hB_eq]
    exact_mod_cast externalCoveringNumber_isometry_bijection h_iso h_bij
  rw [h_cov]
  exact hcover rho hrho hdelta_rho leftA length hlength

/-- `PureWZ2PaperADSet1` is invariant under negation. -/
lemma PureWZ2PaperADSet1.negate
    {S : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 S delta alpha C) :
    PureWZ2PaperADSet1 ((fun x : ℝ => -x) '' S) delta alpha C := by
  rcases hAD with ⟨hδ_pos, hα_pos, hα_one, hC_one, hC_top, hcover⟩
  refine ⟨hδ_pos, hα_pos, hα_one, hC_one, hC_top, ?_⟩
  intro rho hrho hdelta_rho left length hlength
  let B : Set ℝ := ((fun x : ℝ => -x) '' S) ∩ Set.Icc left (left + length)
  let leftA : ℝ := -(left + length)
  let A : Set ℝ := S ∩ Set.Icc leftA (leftA + length)
  have hB_eq : B = (fun x : ℝ => -x) '' A := by
    ext z
    simp only [B, A, Set.mem_inter_iff, Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨⟨x, hxS, rfl⟩, h1, h2⟩
      exact ⟨x, ⟨hxS, by linarith, by linarith⟩, by ring⟩
    · rintro ⟨x, ⟨hxS, h1, h2⟩, rfl⟩
      exact ⟨⟨x, hxS, rfl⟩, by linarith, by linarith⟩
  let f : ℝ → ℝ := fun x => -x
  have h_iso : Isometry f := by
    exact isometry_neg
  have h_inj : Function.Injective f := by
    intro x y h
    simpa [f] using h
  have h_surj : Function.Surjective f := by
    intro y
    refine ⟨-y, ?_⟩
    simp [f] <;> ring
  have h_bij : Function.Bijective f := ⟨h_inj, h_surj⟩
  have h_cov : (Metric.externalCoveringNumber ⟨rho, hrho⟩ B : ENNReal) =
      (Metric.externalCoveringNumber ⟨rho, hrho⟩ A : ENNReal) := by
    rw [hB_eq]
    exact_mod_cast externalCoveringNumber_isometry_bijection h_iso h_bij
  rw [h_cov]
  exact hcover rho hrho hdelta_rho leftA length hlength

/-- Two-step transfer from direction v to global grain direction (1, v₁/v₀, 0).

For E in a horizontal plane at height z:
1. scalarProjection(h,E) = scalarProjection(v,E) - v₂*z (translation, exact AD)
2. global direction = (1/v₀)·h or -(1/|v₀|)·h (scaling + optional negation, 100*C) -/
lemma PureWZ2PaperADSet1.transfer_to_global_direction
    {E : Set Point3} {delta alpha : ℝ} {C : ENNReal}
    {v : Point3} (z : ℝ)
    (hE_height : ∀ p ∈ E, inner ℝ p e3 = z)
    (hv_unit : ‖v‖ = 1)
    (hv2 : |v (2 : Fin 3)| ≤ 1 / 10)
    (hv0 : 1 / 3 ≤ |v (0 : Fin 3)|)
    (hAD : PureWZ2PaperADSet1 (scalarProjection v E) delta alpha C)
    (hdelta_le_one : delta ≤ 1) :
    PureWZ2PaperADSet1
      (scalarProjection (globalGrainDirection (v 1 / v 0)) E)
      delta alpha (100 * C) := by
  let v0 : ℝ := v 0
  let v1 : ℝ := v 1
  let v2 : ℝ := v 2
  let h : Point3 := v - v2 • e3
  have h_e30 : e3 0 = 0 := by simp [e3, EuclideanSpace.single]
  have h_e31 : e3 1 = 0 := by simp [e3, EuclideanSpace.single]
  have h_e32 : e3 2 = 1 := by simp [e3, EuclideanSpace.single]
  have h_h0 : h 0 = v0 := by
    dsimp only [h, v0]
    simp [Pi.smul_apply, h_e30] <;> ring
  have h_h1 : h 1 = v1 := by
    dsimp only [h, v1]
    simp [Pi.smul_apply, h_e31] <;> ring
  have h_h2 : h 2 = 0 := by
    dsimp only [h, v2]
    simp [Pi.smul_apply, h_e32] <;> ring
  have h_proj_h : scalarProjection h E =
      (fun x : ℝ => x - v2 * z) '' scalarProjection v E := by
    ext y
    simp only [scalarProjection, Set.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hz : inner ℝ p e3 = z := hE_height p hp
      have h_eq : inner ℝ p h = inner ℝ p v - v2 * z := by
        have h1 : inner ℝ p h = inner ℝ p v - inner ℝ p (v2 • e3) := by
          simpa [h, inner_sub_right] using rfl
        rw [h1]
        have h2 : inner ℝ p (v2 • e3) = v2 * inner ℝ p e3 := by
          simp [inner_smul_right] <;> ring
        rw [h2, hz] <;> ring
      exact ⟨inner ℝ p v, ⟨p, hp, rfl⟩, h_eq.symm⟩
    · rintro ⟨x, ⟨p, hp, rfl⟩, rfl⟩
      have hz : inner ℝ p e3 = z := hE_height p hp
      have h_eq : inner ℝ p h = inner ℝ p v - v2 * z := by
        have h1 : inner ℝ p h = inner ℝ p v - inner ℝ p (v2 • e3) := by
          simpa [h, inner_sub_right] using rfl
        rw [h1]
        have h2 : inner ℝ p (v2 • e3) = v2 * inner ℝ p e3 := by
          simp [inner_smul_right] <;> ring
        rw [h2, hz] <;> ring
      exact ⟨p, hp, h_eq⟩
  have hAD_h : PureWZ2PaperADSet1 (scalarProjection h E) delta alpha C := by
    rw [h_proj_h]
    have h_trans := hAD.translate (-v2 * z)
    have h_eq : (fun x : ℝ => x + -v2 * z) = (fun x : ℝ => x - v2 * z) := by
      funext x; ring
    rw [h_eq] at h_trans
    exact h_trans
  have h_v0_nonzero : v0 ≠ 0 := by
    have h : 1 / 3 ≤ |v0| := hv0
    have h' : |v0| ≠ 0 := by linarith
    simpa [abs_eq_zero] using h'
  have h_abs_lower : 1 / 3 ≤ |v0| := hv0
  have h_abs_upper : |v0| ≤ 1 := by
    have h6 : |v0| ≤ ‖v‖ := PiLp.norm_apply_le v (0 : Fin 3)
    linarith [hv_unit]
  have h_abs_pos : 0 < |v0| := by linarith
  have h_inv_lower : 1 / 4 ≤ 1 / |v0| := by
    have h_pos : 0 < |v0| := h_abs_pos
    have h_le : |v0| ≤ 4 := by linarith
    have h5 : 1 / (4 : ℝ) ≤ 1 / |v0| := one_div_le_one_div_of_le h_pos h_le
    exact h5
  have h_inv_upper : 1 / |v0| ≤ 3 := by
    have h_pos : 0 < |v0| := h_abs_pos
    have h_ge : 1 ≤ 3 * |v0| := by linarith
    have h_diff : 3 - 1 / |v0| = (3 * |v0| - 1) / |v0| := by
      field_simp [h_pos.ne'] <;> ring
    have h_nonneg : 0 ≤ (3 * |v0| - 1) / |v0| := by
      apply div_nonneg
      · linarith
      · exact abs_nonneg v0
    linarith [h_diff, h_nonneg]
  have h_cases : 0 < v0 ∨ v0 < 0 := by
    by_cases h : 0 ≤ v0
    · have h' : 0 < v0 := by
        exact lt_of_le_of_ne h h_v0_nonzero.symm
      exact Or.inl h'
    · have h' : v0 < 0 := by linarith
      exact Or.inr h'
  rcases h_cases with (h_v0_pos | h_v0_neg)
  · let c : ℝ := 1 / v0
    have hc_pos : 0 < c := by positivity
    have hc_range : 1 / 4 ≤ c := by
      dsimp only [c]
      have h_eq : 1 / v0 = 1 / |v0| := by
        have h_abs : |v0| = v0 := abs_of_pos h_v0_pos
        rw [h_abs]
      rw [h_eq]
      exact h_inv_lower
    have hc_upper : c ≤ 4 := by
      dsimp only [c]
      have h_eq : 1 / v0 = 1 / |v0| := by
        have h_abs : |v0| = v0 := abs_of_pos h_v0_pos
        rw [h_abs]
      rw [h_eq]
      have h : 1 / |v0| ≤ 3 := h_inv_upper
      linarith
    have h_dir : globalGrainDirection (v1 / v0) = c • h := by
      ext i
      fin_cases i
      · simp [globalGrainDirection, h_h0, c] <;> field_simp [h_v0_nonzero] <;> ring
      · simp [globalGrainDirection, h_h1, c] <;> field_simp [h_v0_nonzero] <;> ring
      · simp [globalGrainDirection, h_h2] <;> ring
    rw [h_dir]
    have h_scale : scalarProjection (c • h) E =
        (fun x : ℝ => c * x) '' scalarProjection h E :=
      scalarProjection_scale c hc_pos h E
    rw [h_scale]
    exact hAD_h.scale c hc_pos hc_range hc_upper hdelta_le_one
  · let c : ℝ := 1 / |v0|
    have hc_pos : 0 < c := by
      dsimp only [c]
      exact one_div_pos.mpr h_abs_pos
    have hc_range : 1 / 4 ≤ c := by
      dsimp only [c]
      exact h_inv_lower
    have hc_upper : c ≤ 4 := by
      dsimp only [c]
      have h : 1 / |v0| ≤ 3 := h_inv_upper
      linarith
    have h_dir : globalGrainDirection (v1 / v0) = -c • h := by
      ext i
      fin_cases i
      · simp [globalGrainDirection, h_h0, c, abs_of_neg h_v0_neg]
        <;> field_simp [h_v0_nonzero] <;> ring
      · simp [globalGrainDirection, h_h1, c, abs_of_neg h_v0_neg]
        <;> field_simp [h_v0_nonzero] <;> ring
      · simp [globalGrainDirection, h_h2] <;> ring
    have hAD_scale : PureWZ2PaperADSet1 ((fun x : ℝ => c * x) '' scalarProjection h E)
        delta alpha (100 * C) :=
      hAD_h.scale c hc_pos hc_range hc_upper hdelta_le_one
    have h_neg_proj : scalarProjection (-c • h) E =
        (fun x : ℝ => -x) '' ((fun x : ℝ => c * x) '' scalarProjection h E) := by
      have h1 : -c • h = c • (-h) := by ext j; simp <;> ring
      rw [h1]
      have h3 := scalarProjection_scale c hc_pos (-h) E
      rw [h3]
      have h4 : scalarProjection (-h) E = (fun x : ℝ => -x) '' scalarProjection h E := by
        ext y
        simp only [scalarProjection, Set.mem_image]
        constructor
        · rintro ⟨p, hp, rfl⟩
          exact ⟨inner ℝ p h, ⟨p, hp, rfl⟩, by simp [inner_neg_right]⟩
        · rintro ⟨x, ⟨p, hp, rfl⟩, rfl⟩
          exact ⟨p, hp, by simp [inner_neg_right]⟩
      rw [h4]
      ext y
      simp only [Set.mem_image]
      constructor
      · rintro ⟨x, ⟨w, hw, hx : -w = x⟩, hy : c * x = y⟩
        refine ⟨c * w, ⟨w, hw, rfl⟩, ?_⟩
        have h : -(c * w) = y := by
          calc -(c * w) = c * (-w) := by ring
            _ = c * x := by rw [hx]
            _ = y := hy
        exact h
      · rintro ⟨z2, ⟨w, hw, hz : c * w = z2⟩, hy : -z2 = y⟩
        refine ⟨-w, ⟨w, hw, rfl⟩, ?_⟩
        have h : c * (-w) = y := by
          calc c * (-w) = -(c * w) := by ring
            _ = -z2 := by rw [hz]
            _ = y := hy
        exact h
    rw [h_dir, h_neg_proj]
    exact hAD_scale.negate

end Kakeya.Assouad
