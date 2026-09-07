import MyLeanRepo.Kakeya.Assouad.WZ1.GlobalSlabADTransportStatements
import MyLeanRepo.Kakeya.Assouad.LargeSlope.ExternalCoveringNumberIsometry
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.Cover

/-!
# Fresh proof of WZ1 ADAffineThickeningTransport

Clean implementation built lemma by lemma.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

-- ===== 1. Cover existence =====

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

-- ===== 2. Dilation invariance =====

lemma externalCoveringNumber_dilation_eq {a : ℝ} (ha : 0 < a)
    {ε : NNReal} {A : Set ℝ} :
    externalCoveringNumber ⟨a * ε, by positivity⟩ ((fun x => a * x) '' A) =
    externalCoveringNumber ε A := by
  let f : ℝ → ℝ := fun x => a * x
  let g : ℝ → ℝ := fun y => y / a
  have h_a_nn : 0 ≤ a := by linarith
  have h_inv_nn : 0 ≤ 1 / a := by positivity
  have hf_lip : LipschitzWith (Real.toNNReal a) f := by
    apply LipschitzWith.of_dist_le'; intro x y
    have h : |a * x - a * y| = a * |x - y| := by
      have h1 : a * x - a * y = a * (x - y) := by ring
      rw [h1, abs_mul, abs_of_pos ha]
    simpa [f, dist_eq_norm] using le_of_eq h
  have hg_lip : LipschitzWith (Real.toNNReal (1 / a)) g := by
    apply LipschitzWith.of_dist_le'; intro x y
    have h : |x / a - y / a| = (1 / a) * |x - y| := by
      have h1 : x / a - y / a = (1 / a) * (x - y) := by ring
      rw [h1, abs_mul, abs_of_pos (show (0 : ℝ) < 1 / a by positivity)]
    simpa [g, dist_eq_norm] using le_of_eq h
  have hgf : ∀ x, g (f x) = x := by
    intro x; have h : g (f x) = (a * x) / a := by simp [f, g]
    rw [h]; field_simp [ha.ne']
  have h_coe_a : (Real.toNNReal a : ℝ) = a := by
    have h3 : (Real.toNNReal a : ℝ) = max a 0 := by simp [Real.toNNReal]
    rw [h3, max_eq_left h_a_nn]
  have h_coe_inv : (Real.toNNReal (1 / a) : ℝ) = 1 / a := by
    have h3 : (Real.toNNReal (1 / a) : ℝ) = max (1 / a) 0 := by simp [Real.toNNReal]
    rw [h3, max_eq_left h_inv_nn]
  have h_radius1 : Real.toNNReal a * ε = ⟨a * ε, by positivity⟩ := by
    have h_main : ((Real.toNNReal a * ε : NNReal) : ℝ) = a * (ε : ℝ) := by
      rw [NNReal.coe_mul, h_coe_a]
    let target : NNReal := ⟨a * ε, by positivity⟩
    have h4 : (target : ℝ) = a * ε := Subtype.coe_mk (a * ε) (by positivity)
    have h5 : ((Real.toNNReal a * ε : NNReal) : ℝ) = (target : ℝ) := by rw [h_main, h4]
    exact NNReal.coe_injective h5
  have h_radius2 : Real.toNNReal (1 / a) * ⟨a * ε, by positivity⟩ = ε := by
    let target : NNReal := ⟨a * ε, by positivity⟩
    have h4 : (target : ℝ) = a * ε := Subtype.coe_mk (a * ε) (by positivity)
    have h_main : ((Real.toNNReal (1 / a) * target : NNReal) : ℝ) = (ε : ℝ) := by
      rw [NNReal.coe_mul, h_coe_inv, h4]; field_simp [ha.ne']
    exact NNReal.coe_injective h_main
  have h1 : externalCoveringNumber ⟨a * ε, by positivity⟩ (f '' A) ≤ externalCoveringNumber ε A := by
    simp only [externalCoveringNumber, le_iInf_iff]; intro C hC
    have hcover : IsCover (Real.toNNReal a * ε) (f '' A) (f '' C) := hC.image_lipschitz hf_lip
    rw [h_radius1] at hcover
    exact iInf_le_of_le (f '' C) (iInf_le_of_le hcover (encard_image_le f C))
  have h2 : externalCoveringNumber ε A ≤ externalCoveringNumber ⟨a * ε, by positivity⟩ (f '' A) := by
    simp only [externalCoveringNumber, le_iInf_iff]; intro C hC
    have hcover : IsCover (Real.toNNReal (1 / a) * ⟨a * ε, by positivity⟩) (g '' (f '' A)) (g '' C) :=
      hC.image_lipschitz hg_lip
    rw [h_radius2] at hcover
    have h_image : g '' (f '' A) = A := by
      ext y; simp only [Set.mem_image]; constructor
      · rintro ⟨z, hz, rfl⟩; rcases hz with ⟨x, hx, rfl⟩; have h4 : g (f x) = x := hgf x; rw [h4]; exact hx
      · intro hy; refine ⟨f y, ⟨y, hy, rfl⟩, ?_⟩; exact hgf y
    rw [h_image] at hcover
    exact iInf_le_of_le (g '' C) (iInf_le_of_le hcover (encard_image_le g C))
  exact le_antisymm h1 h2

lemma dilation_inter_closedBall
    {a : ℝ} (ha : 0 < a) {S : Set ℝ} {x r : ℝ} :
    (fun u : ℝ => a * u) '' (S ∩ Metric.closedBall x r) =
    ((fun u : ℝ => a * u) '' S) ∩ Metric.closedBall (a * x) (a * r) := by
  have h_inj : Function.Injective (fun u : ℝ => a * u) := by
    intro u v h; apply mul_left_cancel₀ ha.ne'; exact h
  rw [Set.image_inter h_inj]
  have h2 : (fun u : ℝ => a * u) '' Metric.closedBall x r = Metric.closedBall (a * x) (a * r) := by
    ext y; simp only [Set.mem_image, Metric.mem_closedBall]; constructor
    · rintro ⟨z, hz, rfl⟩
      have h3 : dist z x ≤ r := hz
      have h4 : dist (a * z) (a * x) ≤ a * r := by
        have h5 : dist (a * z) (a * x) = a * dist z x := by
          rw [Real.dist_eq, Real.dist_eq]
          have h6 : |a * z - a * x| = a * |z - x| := by
            have h7 : a * z - a * x = a * (z - x) := by ring
            rw [h7, abs_mul, abs_of_pos ha]
          rw [h6]
        rw [h5]; exact mul_le_mul_of_nonneg_left h3 (by linarith)
      simpa using h4
    · intro h3
      refine ⟨y / a, ?_, ?_⟩
      · have h4 : dist (y / a) x ≤ r := by
          have h5 : dist (y / a) x = dist y (a * x) / a := by
            rw [Real.dist_eq, Real.dist_eq]
            have h6 : |y / a - x| = |y - a * x| / a := by
              have h7 : y / a - x = (y - a * x) / a := by field_simp [ha.ne']
              rw [h7, abs_div, abs_of_pos ha]
            rw [h6]
          rw [h5]
          have h6 : dist y (a * x) ≤ a * r := h3
          have h7 : dist y (a * x) / a ≤ r := by
            calc dist y (a * x) / a ≤ (a * r) / a := by gcongr
                 _ = r := by field_simp [ha.ne']
          exact h7
        simpa using h4
      · field_simp [ha.ne']
  rw [h2]

-- ===== 3. Union bounds =====

private lemma externalCoveringNumber_two_union_le
    {ε : NNReal} {A1 A2 : Set ℝ} :
    (↑(externalCoveringNumber ε (A1 ∪ A2)) : ENNReal) ≤
    (↑(externalCoveringNumber ε A1) : ENNReal) + (↑(externalCoveringNumber ε A2) : ENNReal) := by
  by_cases hA : externalCoveringNumber ε A1 = ⊤
  · rw [hA]; simp
  · by_cases hB : externalCoveringNumber ε A2 = ⊤
    · rw [hB]; simp
    · rcases externalCoveringNumber_exists hA with ⟨CA, hCA, eCA⟩
      rcases externalCoveringNumber_exists hB with ⟨CB, hCB, eCB⟩
      have h_cover : IsCover ε (A1 ∪ A2) (CA ∪ CB) := by
        intro x hx; rcases hx with (hxA | hxB)
        · rcases hCA hxA with ⟨c, hc, hdist⟩; exact ⟨c, Or.inl hc, hdist⟩
        · rcases hCB hxB with ⟨c, hc, hdist⟩; exact ⟨c, Or.inr hc, hdist⟩
      have h_le : externalCoveringNumber ε (A1 ∪ A2) ≤ (CA ∪ CB).encard :=
        IsCover.externalCoveringNumber_le_encard h_cover
      have h_encard : (CA ∪ CB).encard ≤ CA.encard + CB.encard := Set.encard_union_le CA CB
      have h_main : (↑(externalCoveringNumber ε (A1 ∪ A2)) : ENNReal) ≤
          (↑(CA.encard) : ENNReal) + (↑(CB.encard) : ENNReal) := by
        have h5 : (↑(externalCoveringNumber ε (A1 ∪ A2)) : ENNReal) ≤ (↑((CA ∪ CB).encard) : ENNReal) := by exact_mod_cast h_le
        have h6 : (↑((CA ∪ CB).encard) : ENNReal) ≤ (↑(CA.encard) : ENNReal) + (↑(CB.encard) : ENNReal) := by exact_mod_cast h_encard
        exact h5.trans h6
      rw [eCA, eCB] at h_main; exact h_main

lemma externalCoveringNumber_three_union_le
    {ε : NNReal} {A1 A2 A3 : Set ℝ} :
    (↑(externalCoveringNumber ε (A1 ∪ A2 ∪ A3)) : ENNReal) ≤
    (↑(externalCoveringNumber ε A1) : ENNReal) + (↑(externalCoveringNumber ε A2) : ENNReal) +
    (↑(externalCoveringNumber ε A3) : ENNReal) := by
  let B := A1 ∪ A2
  have h1 : (↑(externalCoveringNumber ε (B ∪ A3)) : ENNReal) ≤
      (↑(externalCoveringNumber ε B) : ENNReal) + (↑(externalCoveringNumber ε A3) : ENNReal) :=
    externalCoveringNumber_two_union_le
  have h2 : (↑(externalCoveringNumber ε B) : ENNReal) ≤
      (↑(externalCoveringNumber ε A1) : ENNReal) + (↑(externalCoveringNumber ε A2) : ENNReal) :=
    externalCoveringNumber_two_union_le
  have h3 : A1 ∪ A2 ∪ A3 = B ∪ A3 := by
    ext z; simp [B]
  rw [h3]
  have h4 : (↑(externalCoveringNumber ε B) : ENNReal) + (↑(externalCoveringNumber ε A3) : ENNReal) ≤
      (↑(externalCoveringNumber ε A1) : ENNReal) + (↑(externalCoveringNumber ε A2) : ENNReal) +
      (↑(externalCoveringNumber ε A3) : ENNReal) := by
    exact add_le_add h2 (le_refl _)
  exact h1.trans h4

private lemma externalCoveringNumber_four_union_le
    {ε : NNReal} {A1 A2 A3 A4 : Set ℝ} :
    (↑(externalCoveringNumber ε (A1 ∪ A2 ∪ A3 ∪ A4)) : ENNReal) ≤
    (↑(externalCoveringNumber ε A1) : ENNReal) + (↑(externalCoveringNumber ε A2) : ENNReal) +
    (↑(externalCoveringNumber ε A3) : ENNReal) + (↑(externalCoveringNumber ε A4) : ENNReal) := by
  let B1 := A1 ∪ A2; let B2 := A3 ∪ A4
  have h4 : A1 ∪ A2 ∪ A3 ∪ A4 = B1 ∪ B2 := by ext z; simp [B1, B2]; tauto
  rw [h4]
  have h_union : (↑(externalCoveringNumber ε (B1 ∪ B2)) : ENNReal) ≤
      (↑(externalCoveringNumber ε B1) : ENNReal) + (↑(externalCoveringNumber ε B2) : ENNReal) :=
    externalCoveringNumber_two_union_le
  have h2 : (↑(externalCoveringNumber ε B1) : ENNReal) ≤
      (↑(externalCoveringNumber ε A1) : ENNReal) + (↑(externalCoveringNumber ε A2) : ENNReal) :=
    externalCoveringNumber_two_union_le
  have h3 : (↑(externalCoveringNumber ε B2) : ENNReal) ≤
      (↑(externalCoveringNumber ε A3) : ENNReal) + (↑(externalCoveringNumber ε A4) : ENNReal) :=
    externalCoveringNumber_two_union_le
  calc
    _ ≤ (↑(externalCoveringNumber ε B1) : ENNReal) + (↑(externalCoveringNumber ε B2) : ENNReal) := h_union
    _ ≤ (↑(externalCoveringNumber ε A1) : ENNReal) + (↑(externalCoveringNumber ε A2) : ENNReal) +
          (↑(externalCoveringNumber ε A3) : ENNReal) + (↑(externalCoveringNumber ε A4) : ENNReal) := by
      have h4 := add_le_add h2 h3
      simpa [add_assoc] using h4

-- ===== 4. rpow helpers =====

private lemma realRpowENN_mono_base
    {x y : ℝ} {s : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hs : 0 ≤ s) :
    Kakeya.realRpowENN x s ≤ Kakeya.realRpowENN y s := by
  apply ENNReal.ofReal_le_ofReal; exact Real.rpow_le_rpow hx hxy hs

private lemma realRpowENN_ge_one {x : ℝ} {s : ℝ} (hx : 1 ≤ x) (hs : 0 ≤ s) :
    (1 : ENNReal) ≤ Kakeya.realRpowENN x s := by
  have h1 : Real.rpow 1 s ≤ Real.rpow x s := Real.rpow_le_rpow (by norm_num) hx hs
  have h2 : Real.rpow 1 s = 1 := by simp
  have h3 : (1 : ℝ) ≤ Real.rpow x s := by linarith [h1, h2]
  have h4 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (Real.rpow x s) := ENNReal.ofReal_le_ofReal h3
  have h5 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
  rw [h5]; exact h4

-- ===== 5. Four unit balls cover [-4,4] =====

private lemma icc_four_four_cover_by_four_balls :
    IsCover (1 : NNReal) (Set.Icc (-4 : ℝ) 4) ({-3, -1, 1, 3} : Set ℝ) := by
  intro x hx
  have h1 : -4 ≤ x := hx.1
  have h2 : x ≤ 4 := hx.2
  have h_main : ∃ (c : ℝ), c ∈ ({-3, -1, 1, 3} : Set ℝ) ∧ dist x c ≤ 1 := by
    by_cases h3 : x ≤ -2
    · refine ⟨-3, by simp, ?_⟩
      rw [Real.dist_eq, sub_eq_add_neg]; exact abs_le.mpr ⟨by linarith, by linarith⟩
    · by_cases h4 : x ≤ 0
      · refine ⟨-1, by simp, ?_⟩
        rw [Real.dist_eq, sub_eq_add_neg]; exact abs_le.mpr ⟨by linarith, by linarith⟩
      · by_cases h5 : x ≤ 2
        · refine ⟨1, by simp, ?_⟩
          rw [Real.dist_eq]; exact abs_le.mpr ⟨by linarith, by linarith⟩
        · refine ⟨3, by simp, ?_⟩
          rw [Real.dist_eq]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  rcases h_main with ⟨c, hc, hdist⟩
  have h_edist : edist x c ≤ ↑(1 : NNReal) := by
    rw [edist_dist]
    have h7 : ENNReal.ofReal (dist x c) ≤ ENNReal.ofReal (1 : ℝ) := ENNReal.ofReal_le_ofReal hdist
    have h8 : ENNReal.ofReal (1 : ℝ) = ↑(1 : NNReal) := by simp
    rw [h8] at h7; exact h7
  exact ⟨c, hc, h_edist⟩

-- ===== 6. Five-ball refinement =====

private lemma closedBall_five_cover {δ : ℝ} {ε : NNReal} (hε : 0 < (ε : ℝ))
    (h : δ ≤ 4 * (ε : ℝ)) (x : ℝ) :
    IsCover ε (Metric.closedBall x δ)
        ({x - 4 * (ε : ℝ), x - 2 * (ε : ℝ), x, x + 2 * (ε : ℝ), x + 4 * (ε : ℝ)} : Set ℝ) := by
  let e : ℝ := (ε : ℝ)
  intro y hy
  have h1 : dist y x ≤ δ := hy
  have h2 : |y - x| ≤ 4 * e := by
    rw [Real.dist_eq] at h1
    exact h1.trans h
  have h_main : ∃ (c : ℝ), c ∈ ({x - 4 * e, x - 2 * e, x, x + 2 * e, x + 4 * e} : Set ℝ) ∧ dist y c ≤ e := by
    by_cases h3 : y - x ≥ 0
    · have h4 : y - x ≤ 4 * e := by
        have h5 : |y - x| ≤ 4 * e := h2
        have h6 : y - x ≤ 4 * e := by linarith [abs_le.mp h5]
        exact h6
      by_cases h5 : y - x ≤ e
      · refine ⟨x, by simp, ?_⟩
        rw [Real.dist_eq]; exact abs_le.mpr ⟨by linarith, by linarith⟩
      · by_cases h6 : y - x ≤ 3 * e
        · refine ⟨x + 2 * e, by simp, ?_⟩
          rw [Real.dist_eq]; exact abs_le.mpr ⟨by linarith, by linarith⟩
        · refine ⟨x + 4 * e, by simp, ?_⟩
          rw [Real.dist_eq]; exact abs_le.mpr ⟨by linarith, by linarith⟩
    · have h4 : -(4 * e) ≤ y - x := by
        have h5 : |y - x| ≤ 4 * e := h2
        exact (abs_le.mp h5).1
      by_cases h5 : -e ≤ y - x
      · refine ⟨x, by simp, ?_⟩
        rw [Real.dist_eq]; exact abs_le.mpr ⟨by linarith, by linarith⟩
      · by_cases h6 : -(3 * e) ≤ y - x
        · refine ⟨x - 2 * e, by simp, ?_⟩
          rw [Real.dist_eq]; exact abs_le.mpr ⟨by linarith, by linarith⟩
        · refine ⟨x - 4 * e, by simp, ?_⟩
          rw [Real.dist_eq]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  rcases h_main with ⟨c, hc, hdist⟩
  have h_edist : edist y c ≤ ↑ε := by
    rw [edist_dist]
    have h7 : ENNReal.ofReal (dist y c) ≤ ENNReal.ofReal e := ENNReal.ofReal_le_ofReal hdist
    have h8 : ENNReal.ofReal e = ↑ε := by simp [e]
    rw [h8] at h7
    exact h7
  exact ⟨c, hc, h_edist⟩

private lemma externalCoveringNumber_refine_five
    {δ ε : NNReal} (h : (δ : ℝ) ≤ 4 * (ε : ℝ)) {S : Set ℝ} :
    externalCoveringNumber ε S ≤ 5 * externalCoveringNumber δ S := by
  by_cases hε0 : ε = 0
  · have hδ0 : δ = 0 := by
      have h1 : (δ : ℝ) ≤ 4 * (ε : ℝ) := h
      rw [hε0] at h1
      have h2 : (δ : ℝ) ≤ 0 := by simpa using h1
      have h3 : 0 ≤ (δ : ℝ) := δ.prop
      have h4 : (δ : ℝ) = 0 := le_antisymm h2 h3
      exact_mod_cast h4
    rw [hδ0, hε0]
    have h_goal : externalCoveringNumber (0 : NNReal) S ≤ 5 * externalCoveringNumber (0 : NNReal) S := by
      calc externalCoveringNumber (0 : NNReal) S
        = 1 * externalCoveringNumber (0 : NNReal) S := by simp
      _ ≤ 5 * externalCoveringNumber (0 : NNReal) S := by gcongr <;> norm_num
    exact h_goal
  · have hε_pos : 0 < (ε : ℝ) := by
      have h1 : 0 ≤ (ε : ℝ) := ε.prop
      have h2 : ε ≠ 0 := hε0
      have h3 : (ε : ℝ) ≠ 0 := by
        intro h4
        have h5 : ε = 0 := NNReal.coe_eq_zero.mp h4
        exact h2 h5
      exact lt_of_le_of_ne h1 h3.symm
    by_cases htop : externalCoveringNumber δ S = ⊤
    · rw [htop]; simp
    · rcases externalCoveringNumber_exists htop with ⟨Cδ, hCδ, eCδ⟩
      have hfin : Cδ.Finite := by
        have h : Cδ.encard ≠ ⊤ := by rw [eCδ]; exact htop
        exact encard_ne_top_iff.mp h
      let Cδ' : Finset ℝ := hfin.toFinset
      have hCδ'_coe : (Cδ' : Set ℝ) = Cδ := by
        simp [Cδ', hfin.coe_toFinset]
      let idx : Finset ℤ := {-2, -1, 0, 1, 2}
      let centers (c : ℝ) : Finset ℝ :=
        Finset.image (fun k : ℤ => c + (k : ℝ) * 2 * (ε : ℝ)) idx
      let Cε : Finset ℝ := Finset.biUnion Cδ' centers
      have h_cover : IsCover ε S (Cε : Set ℝ) := by
        intro y hy
        rcases hCδ hy with ⟨c, hcδ, hdist⟩
        have h_in_ball : y ∈ Metric.closedBall c (δ : ℝ) := by
          simpa [Metric.mem_closedBall, edist_dist] using hdist
        have h11 := closedBall_five_cover hε_pos h c
        rcases h11 h_in_ball with ⟨z, hz, hzdist⟩
        have h5 : z = c - 4 * (ε : ℝ) ∨ z = c - 2 * (ε : ℝ) ∨ z = c ∨ z = c + 2 * (ε : ℝ) ∨ z = c + 4 * (ε : ℝ) := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hz
        have hz' : z ∈ centers c := by
          rcases h5 with (rfl | rfl | rfl | rfl | rfl)
          · exact Finset.mem_image.mpr ⟨(-2 : ℤ), by simp [idx], by ring⟩
          · exact Finset.mem_image.mpr ⟨(-1 : ℤ), by simp [idx], by ring⟩
          · exact Finset.mem_image.mpr ⟨(0 : ℤ), by simp [idx], by ring⟩
          · exact Finset.mem_image.mpr ⟨(1 : ℤ), by simp [idx], by ring⟩
          · exact Finset.mem_image.mpr ⟨(2 : ℤ), by simp [idx], by ring⟩
        exact ⟨z, Finset.mem_biUnion.mpr ⟨c, by simpa [Cδ'] using hcδ, hz'⟩, hzdist⟩
      have h_le : externalCoveringNumber ε S ≤ (Cε : Set ℝ).encard :=
        IsCover.externalCoveringNumber_le_encard h_cover
      have h_inj : ∀ (c : ℝ), Function.Injective (fun k : ℤ => c + (k : ℝ) * 2 * (ε : ℝ)) := by
        intro c i j h
        have h9 : (i : ℝ) = (j : ℝ) := by
          have h10 : c + (i : ℝ) * 2 * (ε : ℝ) = c + (j : ℝ) * 2 * (ε : ℝ) := h
          have h11 : (i : ℝ) * 2 * (ε : ℝ) = (j : ℝ) * 2 * (ε : ℝ) := by linarith
          have h12 : (2 * (ε : ℝ)) ≠ 0 := by linarith
          apply mul_left_cancel₀ h12
          linarith
        exact_mod_cast h9
      have h_card5 : ∀ (c : ℝ), (centers c).card = 5 := by
        intro c
        have h1 : (centers c).card = idx.card := by
          rw [Finset.card_image_of_injective _ (h_inj c)]
        rw [h1]
        decide
      have h_card : Cε.card ≤ 5 * Cδ'.card := by
        calc
          Cε.card ≤ ∑ c ∈ Cδ', (centers c).card := Finset.card_biUnion_le
          _ ≤ ∑ _ ∈ Cδ', 5 := by
            apply Finset.sum_le_sum; intro i _
            rw [h_card5 i] <;> norm_num
          _ = 5 * Cδ'.card := by simp [mul_comm] <;> ring
      have h13 : (Cε : Set ℝ).encard = ↑Cε.card := by
        exact encard_coe_eq_coe_finsetCard Cε
      have h14 : Cδ.encard = ↑Cδ'.card := by
        have h15 : (Cδ' : Set ℝ) = Cδ := hCδ'_coe
        rw [←h15]
        exact encard_coe_eq_coe_finsetCard Cδ'
      have h_encard : (Cε : Set ℝ).encard ≤ 5 * Cδ.encard := by
        rw [h13, h14]
        exact_mod_cast h_card
      calc
        externalCoveringNumber ε S ≤ (Cε : Set ℝ).encard := h_le
        _ ≤ 5 * Cδ.encard := h_encard
        _ = 5 * externalCoveringNumber δ S := by rw [eCδ]

-- ===== 7. Helper: isometry reduction for affine image =====

private lemma affine_reduction {a b x r : ℝ} {E : Set ℝ} {rho : NNReal} (ha : a ≠ 0) :
    externalCoveringNumber rho (((fun u => a * u + b) '' E) ∩ Metric.closedBall x r) =
    externalCoveringNumber rho (((fun u => |a| * u) '' E) ∩ Metric.closedBall (if 0 ≤ a then x - b else b - x) r) := by
  by_cases ha_sign : 0 ≤ a
  · -- a ≥ 0 ⇒ a > 0
    have ha_pos : 0 < a := by
      exact lt_of_le_of_ne ha_sign (Ne.symm ha)
    have h_abs : |a| = a := abs_of_nonneg ha_sign
    let T : ℝ → ℝ := fun v => v + b
    have hT_isom : Isometry T := isometry_add_right b
    have hT_surj : Function.Surjective T := by intro y; exact ⟨y - b, by ring⟩
    let A : Set ℝ := ((fun u => a * u) '' E) ∩ Metric.closedBall (x - b) r
    have h_image1 : (fun u => a * u + b) '' E = T '' ((fun u => a * u) '' E) := by
      ext y
      simp only [T, Set.mem_image]
      constructor
      · rintro ⟨u, hu, h_eq⟩
        refine ⟨a * u, ⟨u, hu, rfl⟩, ?_⟩
        linarith
      · rintro ⟨v, ⟨u, hu, h_eq1⟩, h_eq2⟩
        exact ⟨u, hu, by linarith⟩
    have h_ball : T '' Metric.closedBall (x - b) r = Metric.closedBall x r := by
      ext z
      simp only [T, Set.mem_image, Metric.mem_closedBall]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [Real.dist_eq] using hy
      · intro hz
        refine ⟨z - b, ?_, ?_⟩
        · simpa [Real.dist_eq] using hz
        · ring
    have h_TA : T '' A = ((fun u => a * u + b) '' E) ∩ Metric.closedBall x r := by
      rw [Set.image_inter hT_isom.injective, h_image1, h_ball]
    have h4 := Isometry.externalCoveringNumber_image hT_isom hT_surj (A := A) (ε := rho)
    rw [h_TA] at h4
    have h5 : ((fun u => |a| * u) '' E) = ((fun u => a * u) '' E) := by
      ext z; simp [h_abs]
    have h6 : (if 0 ≤ a then x - b else b - x) = x - b := by simp [ha_sign]
    have hA_eq : A = ((fun u => |a| * u) '' E) ∩ Metric.closedBall (x - b) r := by
      ext z
      simp [A, h_abs]
      <;> tauto
    rw [h6]
    rw [h4, hA_eq]
  · -- a < 0
    have ha_neg : a < 0 := by linarith
    have h_abs : |a| = -a := abs_of_neg ha_neg
    let T : ℝ → ℝ := fun v => b - v
    have hT_isom : Isometry T := by
      apply Isometry.of_dist_eq; intro y z
      have h : dist (T y) (T z) = dist y z := by
        simp only [T, Real.dist_eq]
        have h2 : |(b - y) - (b - z)| = |y - z| := by
          have h3 : (b - y) - (b - z) = -(y - z) := by ring
          rw [h3, abs_neg]
        exact h2
      exact h
    have hT_surj : Function.Surjective T := by intro y; exact ⟨b - y, by ring⟩
    let A : Set ℝ := ((fun u => |a| * u) '' E) ∩ Metric.closedBall (b - x) r
    have h_image1 : (fun u => a * u + b) '' E = T '' ((fun u => |a| * u) '' E) := by
      apply Set.ext; intro y
      constructor
      · intro hy; rcases hy with ⟨u, hu, h_eq⟩
        have h1 : |a| * u ∈ (fun u : ℝ => |a| * u) '' E := ⟨u, hu, rfl⟩
        have h2 : T (|a| * u) = a * u + b := by simp [T, h_abs] <;> ring
        exact ⟨|a| * u, h1, by linarith⟩
      · intro hy; rcases hy with ⟨v, hv, h_eq⟩
        rcases hv with ⟨u, hu, h_eq2⟩
        exact ⟨u, hu, by
          have h3 : b - v = y := by simpa [T] using h_eq
          have h4 : v = |a| * u := h_eq2.symm
          rw [h4, h_abs] at h3
          linarith⟩
    have h_ball : T '' Metric.closedBall (b - x) r = Metric.closedBall x r := by
      ext z
      simp only [T, Set.mem_image, Metric.mem_closedBall]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have h4 : dist (b - y) x ≤ r := by
          have h5 : dist (b - y) x = dist y (b - x) := by
            rw [Real.dist_eq, Real.dist_eq]
            have h6 : |(b - y) - x| = |y - (b - x)| := by
              have h7 : (b - y) - x = -(y - (b - x)) := by ring
              rw [h7, abs_neg]
            exact h6
          rw [h5]; exact hy
        exact h4
      · intro hz
        refine ⟨b - z, ?_, ?_⟩
        · have h6 : dist (b - z) (b - x) ≤ r := by
            have h7 : dist (b - z) (b - x) = dist z x := by
              rw [Real.dist_eq, Real.dist_eq]
              have h8 : |(b - z) - (b - x)| = |z - x| := by
                have h9 : (b - z) - (b - x) = x - z := by ring
                rw [h9]
                have h10 : |x - z| = |z - x| := by
                  exact abs_sub_comm x z
                exact h10
              exact h8
            rw [h7]; exact hz
          exact h6
        · ring
    have h_TA : T '' A = ((fun u => a * u + b) '' E) ∩ Metric.closedBall x r := by
      rw [Set.image_inter hT_isom.injective, h_image1, h_ball]
    have h4 := Isometry.externalCoveringNumber_image hT_isom hT_surj (A := A) (ε := rho)
    rw [h_TA] at h4
    have h6 : (if 0 ≤ a then x - b else b - x) = b - x := by simp [ha_sign]
    rw [h6]
    exact h4

-- ===== 8. Affine image covering bound =====

/-- Covering-number bound for a uniformly nondegenerate affine image of an AD set. -/
lemma IsADSet1.affine_image_covering
    {E : Set ℝ} {delta alpha a b : ℝ} {C : ENNReal}
    (hE : IsADSet1 E delta alpha C)
    (ha1 : 1/4 ≤ |a|) (ha2 : |a| ≤ 4) :
    ∀ (rho : ℝ) (hrho : 0 ≤ rho) (hdelta_rho : delta ≤ rho) (hrho_one : rho ≤ 1)
      (x : ℝ) (r : ℝ) (hrho_r : rho ≤ r) (hr_one : r ≤ 1),
      (↑(externalCoveringNumber ⟨rho, hrho⟩
          (((fun u : ℝ => a * u + b) '' E) ∩ Metric.closedBall x r)) : ENNReal) ≤
        (10 * C) * Kakeya.realRpowENN (r / rho) alpha := by
  rcases hE with ⟨hδ, hα, hα1, hC, hE_bounded, hcover⟩
  let a' := |a|
  have ha'_pos : 0 < a' := by
    have h : 0 < |a| := by linarith [abs_nonneg a]
    exact h
  have ha'_le_four : a' ≤ 4 := ha2
  have ha'_ge_quarter : (1 / 4 : ℝ) ≤ a' := ha1
  have hα' : 0 ≤ alpha := by linarith

  intro rho hrho hdelta_rho hrho_one x r hrho_r hr_one
  have h_rho_pos : 0 < rho := by linarith
  let x' : ℝ := if 0 ≤ a then x - b else b - x
  have ha_ne_zero : a ≠ 0 := by
    intro h; rw [h] at ha1; norm_num at ha1 <;> linarith
  have h_reduce := affine_reduction (a := a) (b := b) (x := x) (r := r) (E := E) (rho := ⟨rho, hrho⟩) (ha := ha_ne_zero)
  rw [h_reduce]

  let eps : ℝ := rho / a'
  let R : ℝ := r / a'
  let X : ℝ := x' / a'
  let eps_nn : NNReal := ⟨eps, by positivity⟩
  have h_radius_eq : a' * eps = rho := by
    simp only [eps]
    field_simp [ha'_pos.ne'] <;> ring
  have h_image_eq : ((fun u : ℝ => a' * u) '' E) ∩ Metric.closedBall x' r =
      (fun u : ℝ => a' * u) '' (E ∩ Metric.closedBall X R) := by
    have h1 : a' * X = x' := by
      simp only [X]
      field_simp [ha'_pos.ne'] <;> ring
    have h2 : a' * R = r := by
      simp only [R]
      field_simp [ha'_pos.ne'] <;> ring
    have h := dilation_inter_closedBall (ha := ha'_pos) (S := E) (x := X) (r := R)
    rw [h1, h2] at h
    exact h.symm
  let eps2 : NNReal := ⟨a' * (eps_nn : ℝ), by positivity⟩
  have h_nn : eps2 = ⟨rho, hrho⟩ := by
    apply NNReal.coe_injective
    have h_coe2 : (eps2 : ℝ) = a' * (eps_nn : ℝ) := by
      exact Subtype.coe_mk (a' * (eps_nn : ℝ)) (by positivity)
    rw [h_coe2]
    have h : a' * (eps_nn : ℝ) = rho := by
      have h_coe : (eps_nn : ℝ) = eps := by rfl
      rw [h_coe]
      exact h_radius_eq
    exact h
  have h_cover_eq : externalCoveringNumber ⟨rho, hrho⟩
        (((fun u : ℝ => a' * u) '' E) ∩ Metric.closedBall x' r) =
      externalCoveringNumber eps_nn (E ∩ Metric.closedBall X R) := by
    rw [h_image_eq]
    have h_dilation : externalCoveringNumber eps2 ((fun u : ℝ => a' * u) '' (E ∩ Metric.closedBall X R)) =
        externalCoveringNumber eps_nn (E ∩ Metric.closedBall X R) :=
      externalCoveringNumber_dilation_eq (a := a') (ha := ha'_pos) (ε := eps_nn) (A := E ∩ Metric.closedBall X R)
    rw [h_nn] at h_dilation
    exact h_dilation
  rw [h_cover_eq]

  have h_ratio_main : R / eps = r / rho := by
    simp [R, eps] <;> field_simp [ha'_pos.ne', h_rho_pos.ne'] <;> ring

  -- Case split on a' ≤ 1 vs a' > 1
  by_cases h_a_le_one : a' ≤ 1
  · -- Case 1: a' ≤ 1, so eps ≥ delta
    have heps_ge_delta : delta ≤ eps := by
      have h2 : rho / a' ≥ rho := by
        have h3 : a' ≤ 1 := h_a_le_one
        have h4 : 0 < a' := ha'_pos
        calc rho / a' ≥ rho / 1 := by gcongr
             _ = rho := by ring
      have h5 : eps = rho / a' := by rfl
      rw [h5]
      linarith [hdelta_rho]
    by_cases hR_le_one : R ≤ 1
    · -- R ≤ 1: direct AD bound
      have heps_le_one : eps ≤ 1 := by
        simp only [eps]
        have h1 : rho ≤ r := hrho_r
        have h2 : r ≤ a' := by
          simp only [R] at hR_le_one
          exact (div_le_one ha'_pos).mp hR_le_one
        have h3 : rho ≤ a' := by linarith
        exact (div_le_one ha'_pos).mpr h3
      have heps_le_R : eps ≤ R := by
        simp only [eps, R]
        gcongr <;> linarith
      have h_old := hcover eps (by positivity) heps_ge_delta heps_le_one X R heps_le_R hR_le_one
      rw [h_ratio_main] at h_old
      have h : C * Kakeya.realRpowENN (r / rho) alpha ≤ (10 * C) * Kakeya.realRpowENN (r / rho) alpha := by
        have hC_le_10C : C ≤ 10 * C := by
          have h1 : (1 : ENNReal) ≤ 10 := by norm_num
          have h2 : (1 : ENNReal) * C ≤ 10 * C := mul_le_mul_left h1 C
          simpa using h2
        exact mul_le_mul_left hC_le_10C (Kakeya.realRpowENN (r / rho) alpha)
      exact h_old.trans h
    · -- R > 1: four-ball decomposition
      have hR_gt_one : 1 < R := by linarith
      let B1 := E ∩ Metric.closedBall (-3 : ℝ) 1
      let B2 := E ∩ Metric.closedBall (-1 : ℝ) 1
      let B3 := E ∩ Metric.closedBall (1 : ℝ) 1
      let B4 := E ∩ Metric.closedBall (3 : ℝ) 1
      have hS_cover : E ⊆ B1 ∪ B2 ∪ B3 ∪ B4 := by
        intro p hp
        have h_p_in_Icc : p ∈ Set.Icc (-4 : ℝ) 4 := hE_bounded hp
        rcases icc_four_four_cover_by_four_balls h_p_in_Icc with ⟨c, hc, hdist⟩
        have h_in_ball : p ∈ Metric.closedBall c 1 := by
          simpa [Metric.mem_closedBall, edist_dist] using hdist
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        rcases hc with (rfl | rfl | rfl | rfl) <;> simp [B1, B2, B3, B4, h_in_ball] <;> tauto
      have h_sub : E ∩ Metric.closedBall X R ⊆ B1 ∪ B2 ∪ B3 ∪ B4 := by
        intro p hp; exact hS_cover hp.1
      have h_mono : externalCoveringNumber eps_nn (E ∩ Metric.closedBall X R) ≤
          externalCoveringNumber eps_nn (B1 ∪ B2 ∪ B3 ∪ B4) :=
        externalCoveringNumber_mono_set h_sub
      by_cases heps_gt_one : 1 < eps
      · -- eps > 1: each unit ball covered by one point
        have h_each : ∀ (c : ℝ), (↑(externalCoveringNumber eps_nn (E ∩ Metric.closedBall c 1)) : ENNReal) ≤ 1 := by
          intro c
          have h10 : IsCover eps_nn (E ∩ Metric.closedBall c 1) ({c} : Set ℝ) := by
            intro y hy
            have h11 : dist y c ≤ 1 := hy.2
            have h12 : dist y c ≤ eps := by linarith
            have h13 : edist y c ≤ ↑eps_nn := by
              rw [edist_dist]
              have h14 : ENNReal.ofReal (dist y c) ≤ ENNReal.ofReal eps := ENNReal.ofReal_le_ofReal h12
              have h15 : ENNReal.ofReal eps = ↑eps_nn := by
                have h16 : (eps_nn : ℝ) = eps := by rfl
                have h17 : ENNReal.ofReal (eps_nn : ℝ) = ↑eps_nn := by simp
                rw [h16] at h17
                exact h17
              rw [h15] at h14
              exact h14
            exact ⟨c, by simp, h13⟩
          have h15 : externalCoveringNumber eps_nn (E ∩ Metric.closedBall c 1) ≤ ({c} : Set ℝ).encard :=
            IsCover.externalCoveringNumber_le_encard h10
          have h16 : ({c} : Set ℝ).encard = 1 := by simp
          exact_mod_cast h15.trans (by rw [h16] <;> norm_num)
        have h_union : (↑(externalCoveringNumber eps_nn (B1 ∪ B2 ∪ B3 ∪ B4)) : ENNReal) ≤ 4 := by
          have h4 := externalCoveringNumber_four_union_le (ε := eps_nn) (A1 := B1) (A2 := B2) (A3 := B3) (A4 := B4)
          calc
            _ ≤ _ + _ + _ + _ := h4
            _ ≤ 1 + 1 + 1 + 1 := by gcongr <;> exact h_each _
            _ = 4 := by norm_num
        have h1_rho : 1 ≤ r / rho := by
          apply (one_le_div h_rho_pos).mpr
          exact hrho_r
        have h2_rpow : (1 : ENNReal) ≤ Kakeya.realRpowENN (r / rho) alpha := realRpowENN_ge_one h1_rho hα'
        have h3 : (4 : ENNReal) ≤ 10 * C := by
          have h4 : (1 : ENNReal) ≤ C := hC
          have h5 : (10 : ENNReal) ≤ 10 * C := by
            have h6 : (10 : ENNReal) = 10 * (1 : ENNReal) := by simp
            rw [h6]; exact le_mul_of_one_le_right' h4
          have h7 : (4 : ENNReal) ≤ 10 := by norm_num
          exact h7.trans h5
        have h_final : (4 : ENNReal) ≤ (10 * C) * Kakeya.realRpowENN (r / rho) alpha := by
          calc (4 : ENNReal) ≤ 10 * C := h3
               _ ≤ (10 * C) * Kakeya.realRpowENN (r / rho) alpha := by
                have h10 : (1 : ENNReal) ≤ Kakeya.realRpowENN (r / rho) alpha := h2_rpow
                have h11 : (10 * C) * (1 : ENNReal) ≤ (10 * C) * Kakeya.realRpowENN (r / rho) alpha :=
                  mul_le_mul_right h10 (10 * C)
                simpa using h11
        have h_mono' : (↑(externalCoveringNumber eps_nn (E ∩ Metric.closedBall X R)) : ENNReal) ≤
            (↑(externalCoveringNumber eps_nn (B1 ∪ B2 ∪ B3 ∪ B4)) : ENNReal) := by
          exact_mod_cast h_mono
        exact h_mono'.trans (h_union.trans h_final)
      · -- eps ≤ 1: apply AD bound to each unit ball
        have heps_le_one : eps ≤ 1 := by linarith
        let Xval := Kakeya.realRpowENN (1 / eps) alpha
        have h_old1 := hcover eps (by positivity) heps_ge_delta heps_le_one (-3) 1 (by linarith) (by norm_num)
        have h_old2 := hcover eps (by positivity) heps_ge_delta heps_le_one (-1) 1 (by linarith) (by norm_num)
        have h_old3 := hcover eps (by positivity) heps_ge_delta heps_le_one 1 1 (by linarith) (by norm_num)
        have h_old4 := hcover eps (by positivity) heps_ge_delta heps_le_one 3 1 (by linarith) (by norm_num)
        have h_ratio2 : 1 / eps ≤ r / rho := by
          have h1 : 1 < R := hR_gt_one
          have h2 : r > a' := by
            have h21 : r / a' > 1 := h1
            calc r = (r / a') * a' := by field_simp [ha'_pos.ne'] <;> ring
                 _ > 1 * a' := by gcongr
                 _ = a' := by ring
          have h3 : 1 / eps = a' / rho := by
            simp [eps] <;> field_simp [ha'_pos.ne'] <;> ring
          rw [h3]
          have h4 : a' / rho ≤ r / rho := by
            apply div_le_div_of_nonneg_right
            <;> linarith
          exact h4
        have h_rpow : Xval ≤ Kakeya.realRpowENN (r / rho) alpha :=
          realRpowENN_mono_base (by positivity) h_ratio2 hα'
        have h_sum : (↑(externalCoveringNumber eps_nn (B1 ∪ B2 ∪ B3 ∪ B4)) : ENNReal) ≤
            4 * (C * Xval) := by
          have h4 := externalCoveringNumber_four_union_le (ε := eps_nn) (A1 := B1) (A2 := B2) (A3 := B3) (A4 := B4)
          calc
            _ ≤ _ + _ + _ + _ := h4
            _ ≤ (C * Xval) + (C * Xval) + (C * Xval) + (C * Xval) := by
              exact add_le_add (add_le_add (add_le_add h_old1 h_old2) h_old3) h_old4
            _ = 4 * (C * Xval) := by ring
        have h_final : 4 * (C * Xval) ≤ (10 * C) * Kakeya.realRpowENN (r / rho) alpha := by
          calc
            4 * (C * Xval) ≤ 4 * (C * Kakeya.realRpowENN (r / rho) alpha) := by gcongr
            _ = (4 * C) * Kakeya.realRpowENN (r / rho) alpha := by simp [mul_assoc]
            _ ≤ (10 * C) * Kakeya.realRpowENN (r / rho) alpha := by
              let Y := Kakeya.realRpowENN (r / rho) alpha
              have h5 : (4 : ENNReal) * C ≤ (10 : ENNReal) * C := by
                have h6 : (4 : ENNReal) ≤ 10 := by norm_num
                exact mul_le_mul_left h6 C
              exact mul_le_mul_left h5 Y
        have h_mono' : (↑(externalCoveringNumber eps_nn (E ∩ Metric.closedBall X R)) : ENNReal) ≤
            (↑(externalCoveringNumber eps_nn (B1 ∪ B2 ∪ B3 ∪ B4)) : ENNReal) := by
          exact_mod_cast h_mono
        exact h_mono'.trans (h_sum.trans h_final)

  · -- Case 2: a' > 1
    have ha'_gt_one : 1 < a' := by linarith
    have hR_le_one : R ≤ 1 := by
      have h1 : r / a' ≤ r := by
        apply div_le_self
        · linarith
        · linarith
      linarith [hr_one]
    by_cases heps_ge_delta : delta ≤ eps
    · -- eps ≥ delta: direct AD bound
      have heps_le_one : eps ≤ 1 := by
        simp only [eps]
        have h1 : rho ≤ 1 := hrho_one
        have h2 : 1 < a' := ha'_gt_one
        have h3 : rho / a' ≤ rho / 1 := by gcongr
        have h4 : rho / 1 = rho := by ring
        linarith
      have heps_le_R : eps ≤ R := by
        simp only [eps, R]
        gcongr <;> linarith
      have h_old := hcover eps (by positivity) heps_ge_delta heps_le_one X R heps_le_R hR_le_one
      rw [h_ratio_main] at h_old
      have h : C * Kakeya.realRpowENN (r / rho) alpha ≤ (10 * C) * Kakeya.realRpowENN (r / rho) alpha := by
        have hC_le_10C : C ≤ 10 * C := by
          have h1 : (1 : ENNReal) ≤ 10 := by norm_num
          have h2 : (1 : ENNReal) * C ≤ 10 * C := mul_le_mul_left h1 C
          simpa using h2
        exact mul_le_mul_left hC_le_10C (Kakeya.realRpowENN (r / rho) alpha)
      exact h_old.trans h
    · -- eps < delta: use refinement
      have heps_lt_delta : eps < delta := by linarith
      have h_refine_ratio : delta ≤ 4 * eps := by
        have h1 : delta / eps ≤ a' := by
          simp [eps] <;> field_simp [ha'_pos.ne'] <;> linarith
        have h2 : delta / eps ≤ 4 := h1.trans ha'_le_four
        have h3 : 0 < eps := by positivity
        calc delta = (delta / eps) * eps := by field_simp [h3.ne'] <;> ring
             _ ≤ 4 * eps := by gcongr
      let delta_nn : NNReal := ⟨delta, by linarith⟩
      have h_refine_ratio' : (delta_nn : ℝ) ≤ 4 * (eps_nn : ℝ) := h_refine_ratio
      have h_refine : externalCoveringNumber eps_nn (E ∩ Metric.closedBall X R) ≤
          5 * externalCoveringNumber delta_nn (E ∩ Metric.closedBall X R) :=
        externalCoveringNumber_refine_five h_refine_ratio'
      have h_refine' : (↑(externalCoveringNumber eps_nn (E ∩ Metric.closedBall X R)) : ENNReal) ≤
          5 * (↑(externalCoveringNumber delta_nn (E ∩ Metric.closedBall X R)) : ENNReal) := by
        exact_mod_cast h_refine
      by_cases hR_ge_delta : R ≥ delta
      · -- R ≥ delta: apply AD at scale delta
        have h_old := hcover delta (by linarith) (by linarith) (by linarith) X R hR_ge_delta hR_le_one
        have h_bound : (↑(externalCoveringNumber delta_nn (E ∩ Metric.closedBall X R)) : ENNReal) ≤
            C * Kakeya.realRpowENN (R / delta) alpha := h_old
        have h4 : rho ≤ a' * delta := by
          have h5 : rho / a' < delta := heps_lt_delta
          have h6 : rho < a' * delta := by
            calc rho = (rho / a') * a' := by field_simp [ha'_pos.ne'] <;> ring
                 _ < delta * a' := by gcongr
                 _ = a' * delta := by ring
          exact h6.le
        have h_ratio1 : R / delta ≤ r / rho := by
          have h_pos1 : 0 < r := by linarith
          have h_pos2 : 0 < delta := hδ
          have h_pos3 : 0 < rho := h_rho_pos
          have h_pos4 : 0 < a' := ha'_pos
          calc (r / a') / delta
            = r / (a' * delta) := by field_simp [h_pos4.ne'] <;> ring
          _ ≤ r / rho := by gcongr
        have hR_div_delta_pos : 0 ≤ R / delta := by
          have h1 : 0 < delta := hδ
          have h2 : 0 ≤ R := by linarith [hR_ge_delta]
          exact div_nonneg h2 h1.le
        have h_rpow : Kakeya.realRpowENN (R / delta) alpha ≤ Kakeya.realRpowENN (r / rho) alpha :=
          realRpowENN_mono_base hR_div_delta_pos h_ratio1 hα'
        have h_main : 5 * (C * Kakeya.realRpowENN (R / delta) alpha) ≤
            (10 * C) * Kakeya.realRpowENN (r / rho) alpha := by
          calc
            5 * (C * Kakeya.realRpowENN (R / delta) alpha)
              ≤ 5 * (C * Kakeya.realRpowENN (r / rho) alpha) := by gcongr
            _ = (5 * C) * Kakeya.realRpowENN (r / rho) alpha := by simp [mul_assoc]
            _ ≤ (10 * C) * Kakeya.realRpowENN (r / rho) alpha := by
              let Y := Kakeya.realRpowENN (r / rho) alpha
              have h5 : (5 : ENNReal) * C ≤ (10 : ENNReal) * C := by
                have h6 : (5 : ENNReal) ≤ 10 := by norm_num
                exact mul_le_mul_left h6 C
              exact mul_le_mul_left h5 Y
        have h_coeff : (1 : ENNReal) ≤ 5 := by norm_num
        have h_step : (5 : ENNReal) * (↑(externalCoveringNumber delta_nn (E ∩ Metric.closedBall X R)) : ENNReal) ≤
            (5 : ENNReal) * (C * Kakeya.realRpowENN (R / delta) alpha) :=
          mul_le_mul' (le_refl (5 : ENNReal)) h_bound
        exact h_refine'.trans (h_step.trans h_main)
      · -- R < delta: one delta-ball suffices
        have hR_lt_delta : R < delta := by linarith
        have h_one_cover : IsCover delta_nn (E ∩ Metric.closedBall X R) ({X} : Set ℝ) := by
          intro y hy
          have h4 : dist y X ≤ R := hy.2
          have h5 : dist y X ≤ delta := by linarith
          have h6 : edist y X ≤ ↑delta_nn := by
            rw [edist_dist]
            have h7 : ENNReal.ofReal (dist y X) ≤ ENNReal.ofReal delta := ENNReal.ofReal_le_ofReal h5
            have h8 : ENNReal.ofReal delta = ↑delta_nn := by
              have h9 : (delta_nn : ℝ) = delta := by rfl
              have h10 : ENNReal.ofReal (delta_nn : ℝ) = ↑delta_nn := by simp
              rw [h9] at h10
              exact h10
            rw [h8] at h7
            exact h7
          exact ⟨X, by simp, h6⟩
        have h_le : externalCoveringNumber delta_nn (E ∩ Metric.closedBall X R) ≤ ({X} : Set ℝ).encard :=
          IsCover.externalCoveringNumber_le_encard h_one_cover
        have h_encard : ({X} : Set ℝ).encard = 1 := by simp
        have h_bound : (↑(externalCoveringNumber delta_nn (E ∩ Metric.closedBall X R)) : ENNReal) ≤ (1 : ENNReal) := by
          exact_mod_cast h_le.trans (by rw [h_encard] <;> norm_num)
        have h1_rho : 1 ≤ r / rho := by
          apply (one_le_div h_rho_pos).mpr
          exact hrho_r
        have h2_rpow : (1 : ENNReal) ≤ Kakeya.realRpowENN (r / rho) alpha := realRpowENN_ge_one h1_rho hα'
        have h3 : (5 : ENNReal) ≤ 10 * C := by
          have h4 : (1 : ENNReal) ≤ C := hC
          have h5 : (10 : ENNReal) ≤ 10 * C := by
            have h6 : (10 : ENNReal) = 10 * (1 : ENNReal) := by simp
            rw [h6]; exact le_mul_of_one_le_right' h4
          have h7 : (5 : ENNReal) ≤ 10 := by norm_num
          exact h7.trans h5
        have h_final : (5 : ENNReal) ≤ (10 * C) * Kakeya.realRpowENN (r / rho) alpha := by
          calc (5 : ENNReal) ≤ 10 * C := h3
               _ ≤ (10 * C) * Kakeya.realRpowENN (r / rho) alpha := by
                have h10 : (1 : ENNReal) ≤ Kakeya.realRpowENN (r / rho) alpha := h2_rpow
                have h11 : (10 * C) * (1 : ENNReal) ≤ (10 * C) * Kakeya.realRpowENN (r / rho) alpha :=
                  mul_le_mul_right h10 (10 * C)
                simpa using h11
        calc
          (↑(externalCoveringNumber eps_nn (E ∩ Metric.closedBall X R)) : ENNReal)
            ≤ 5 * (↑(externalCoveringNumber delta_nn (E ∩ Metric.closedBall X R)) : ENNReal) := h_refine'
          _ ≤ 5 * (1 : ENNReal) := by gcongr
          _ = (5 : ENNReal) := by simp
          _ ≤ (10 * C) * Kakeya.realRpowENN (r / rho) alpha := h_final

-- ===== 9. Thickening helpers =====

private lemma abs_split_helper
    {x c delta r : ℝ} (h : delta ≤ r) (hdist : |x - c| ≤ r + delta) :
    |x - (c - delta)| ≤ r ∨ |x - (c + delta)| ≤ r := by
  by_cases hcase : x ≤ c
  · left
    have h1 : -r ≤ x - c + delta := by linarith [abs_le.mp hdist]
    have h2 : x - c + delta ≤ r := by linarith [abs_le.mp hdist]
    have h3 : x - (c - delta) = x - c + delta := by ring
    rw [h3]; exact abs_le.mpr ⟨h1, h2⟩
  · right
    have h1 : -r ≤ x - c - delta := by linarith [abs_le.mp hdist]
    have h2 : x - c - delta ≤ r := by linarith [abs_le.mp hdist]
    have h3 : x - (c + delta) = x - c - delta := by ring
    rw [h3]; exact abs_le.mpr ⟨h1, h2⟩

private lemma finite_cover_cthickening
    {C : Finset ℝ} {S : Set ℝ} {rho delta : ℝ}
    (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hC : IsCover ⟨rho, hrho⟩ S (C : Set ℝ))
    {x : ℝ} (hx : x ∈ cthickening delta S) :
    ∃ c ∈ C, dist x c ≤ rho + delta := by
  let eps_nn : NNReal := ⟨rho, hrho⟩
  let eps_en : ENNReal := ↑eps_nn
  have h1 : (eps_nn : ℝ) = rho := NNReal.coe_mk rho hrho
  have h2 : (eps_en : ENNReal) = ENNReal.ofReal (↑eps_nn : ℝ) := by
    exact ENNReal.coe_nnreal_eq eps_nn
  have h_eps_en : eps_en = ENNReal.ofReal rho := by
    rw [h2, h1]
  by_cases h_empty : C = ∅
  · have hS_empty : S = ∅ := by
      by_contra hS
      obtain ⟨s, hs⟩ := Set.nonempty_iff_ne_empty.mpr hS
      rcases hC hs with ⟨c, hc, _⟩
      rw [h_empty] at hc; simp at hc <;> tauto
    rw [hS_empty] at hx
    simp [cthickening] at hx
  · have hC_nonempty : C.Nonempty := by
      simpa [Finset.nonempty_iff_ne_empty] using h_empty
    by_contra h
    push Not at h
    let dists : Finset ℝ := C.image (fun c => dist x c - (rho + delta))
    rcases hC_nonempty with ⟨c0, hc0⟩
    have h_dists_nonempty : dists.Nonempty := by
      refine ⟨_, Finset.mem_image.mpr ⟨c0, hc0, rfl⟩⟩
    let ε := dists.min' h_dists_nonempty
    have hε_in : ε ∈ dists := Finset.min'_mem dists h_dists_nonempty
    have hε_pos : 0 < ε := by
      rcases Finset.mem_image.mp hε_in with ⟨c, hc, h_eq⟩
      have h_gt : rho + delta < dist x c := h c hc
      rw [←h_eq]
      exact sub_pos.mpr h_gt
    have h_ge : ∀ c ∈ C, dist x c - (rho + delta) ≥ ε := by
      intro c hc
      have h1 : dist x c - (rho + delta) ∈ dists :=
        Finset.mem_image.mpr ⟨c, hc, rfl⟩
      exact Finset.min'_le dists _ h1
    have h_ge' : ∀ c ∈ C, dist x c ≥ rho + delta + ε := by
      intro c hc
      have h1 := h_ge c hc
      linarith
    have h_all : ∀ s ∈ S, dist x s ≥ delta + ε := by
      intro s hs
      rcases hC hs with ⟨c, hc, hedist⟩
      have hedist' : edist s c ≤ eps_en := hedist
      have hdist_sc : dist s c ≤ rho := by
        have h_eq1 : edist s c = ENNReal.ofReal (dist s c) := edist_dist s c
        rw [h_eq1, h_eps_en] at hedist'
        have h : ENNReal.ofReal (dist s c) ≤ ENNReal.ofReal rho := hedist'
        have h_iff : ENNReal.ofReal (dist s c) ≤ ENNReal.ofReal rho ↔ dist s c ≤ rho :=
          ENNReal.ofReal_le_ofReal_iff (by linarith)
        exact h_iff.mp hedist'
      have h1 : dist x c ≥ rho + delta + ε := h_ge' c hc
      have h2 : dist x c ≤ dist x s + dist s c := dist_triangle x s c
      linarith
    have h_infEDist_ge : ∀ s ∈ S, edist x s ≥ ENNReal.ofReal (delta + ε) := by
      intro s hs
      have h3 : dist x s ≥ delta + ε := h_all s hs
      have h4 : edist x s = ENNReal.ofReal (dist x s) := edist_dist x s
      rw [h4]
      exact ENNReal.ofReal_le_ofReal h3
    have h5 : ENNReal.ofReal (delta + ε) ≤ infEDist x S := by
      rw [Metric.le_infEDist]
      exact h_infEDist_ge
    have h6 : infEDist x S ≤ ENNReal.ofReal delta := by
      simpa [cthickening, Set.mem_setOf_eq] using hx
    have h7 : ENNReal.ofReal delta < ENNReal.ofReal (delta + ε) := by
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)] <;> linarith
    have h8 : ENNReal.ofReal (delta + ε) ≤ ENNReal.ofReal delta := le_trans h5 h6
    exact not_le.mpr h7 h8

lemma externalCoveringNumber_cthickening_le_two
    {delta rho : ℝ} {hrho : 0 ≤ rho} {hdelta : 0 ≤ delta} (h : delta ≤ rho)
    {S : Set ℝ} :
    externalCoveringNumber ⟨rho, hrho⟩ (cthickening delta S) ≤
    2 * externalCoveringNumber ⟨rho, hrho⟩ S := by
  by_cases htop : externalCoveringNumber ⟨rho, hrho⟩ S = ⊤
  · rw [htop]; simp
  · rcases externalCoveringNumber_exists htop with ⟨C, hCcover, hCcard⟩
    have hC_finite : Set.Finite C := by
      have h : C.encard ≠ ⊤ := by rw [hCcard]; exact htop
      exact encard_ne_top_iff.mp h
    let Cfin : Finset ℝ := hC_finite.toFinset
    have hCfin_coe : (Cfin : Set ℝ) = C := by
      simp [Cfin, hC_finite.coe_toFinset]
    have hCcover' : IsCover ⟨rho, hrho⟩ S (Cfin : Set ℝ) := by
      rw [hCfin_coe]; exact hCcover
    let C' : Finset ℝ := Cfin.image (fun c => c - delta) ∪ Cfin.image (fun c => c + delta)
    let eps_nn : NNReal := ⟨rho, hrho⟩
    have h_coe1 : (eps_nn : ℝ) = rho := NNReal.coe_mk rho hrho
    have h_coe : (↑eps_nn : ENNReal) = ENNReal.ofReal rho := by
      have h : (↑eps_nn : ENNReal) = ENNReal.ofReal (↑eps_nn : ℝ) := by exact ENNReal.coe_nnreal_eq eps_nn
      rw [h, h_coe1]
    have hcover : IsCover eps_nn (cthickening delta S) (C' : Set ℝ) := by
      intro x hx
      rcases finite_cover_cthickening hrho hdelta hCcover' hx with ⟨c, hc, hdist⟩
      have h_abs : |x - c| ≤ rho + delta := by simpa [Real.dist_eq] using hdist
      rcases abs_split_helper h h_abs with (hleft | hright)
      · have hmem1 : c - delta ∈ Cfin.image (fun c : ℝ => c - delta) :=
          Finset.mem_image_of_mem _ hc
        have hmem : c - delta ∈ C' := Finset.mem_union_left _ hmem1
        have h_edist : edist x (c - delta) ≤ (↑eps_nn : ENNReal) := by
          rw [edist_dist, h_coe]
          exact ENNReal.ofReal_le_ofReal hleft
        exact ⟨c - delta, hmem, by simpa [Set.mem_setOf_eq] using h_edist⟩
      · have hmem2 : c + delta ∈ Cfin.image (fun c : ℝ => c + delta) :=
          Finset.mem_image_of_mem _ hc
        have hmem : c + delta ∈ C' := Finset.mem_union_right _ hmem2
        have h_edist : edist x (c + delta) ≤ (↑eps_nn : ENNReal) := by
          rw [edist_dist, h_coe]
          exact ENNReal.ofReal_le_ofReal hright
        exact ⟨c + delta, hmem, by simpa [Set.mem_setOf_eq] using h_edist⟩
    have h_img1 : (Cfin.image (fun c => c - delta)).card ≤ Cfin.card := by
      exact Finset.card_image_le
    have h_img2 : (Cfin.image (fun c => c + delta)).card ≤ Cfin.card := by
      exact Finset.card_image_le
    have h_card : C'.card ≤ 2 * Cfin.card := by
      calc C'.card
          ≤ (Cfin.image (fun c => c - delta)).card + (Cfin.image (fun c => c + delta)).card :=
            Finset.card_union_le _ _
        _ ≤ Cfin.card + Cfin.card := by gcongr
        _ = 2 * Cfin.card := by ring
    have h_main : externalCoveringNumber eps_nn (cthickening delta S) ≤ (C' : Set ℝ).encard :=
      IsCover.externalCoveringNumber_le_encard hcover
    have h_encard : (C' : Set ℝ).encard = ↑C'.card := by simp
    rw [h_encard] at h_main
    have h2 : C.encard = ↑Cfin.card := by
      have h3 : C.encard = (Cfin : Set ℝ).encard := by rw [hCfin_coe]
      rw [h3]; simp
    have h_final : (↑C'.card : ENat) ≤ 2 * externalCoveringNumber eps_nn S := by
      have h1 : (↑C'.card : ENat) ≤ ↑(2 * Cfin.card) := by exact_mod_cast h_card
      have h4 : (↑C'.card : ENat) ≤ 2 * C.encard := by
        rw [h2]
        simpa [mul_comm] using h1
      rw [hCcard] at h4
      exact h4
    exact h_main.trans h_final

lemma closedBall_split_three
    {x r delta : ℝ} (h : delta ≤ r) :
    Metric.closedBall x (r + 2 * delta) ⊆
    Metric.closedBall (x - 2 * r) r ∪
    Metric.closedBall x r ∪
    Metric.closedBall (x + 2 * r) r := by
  intro y hy
  have hdist : dist y x ≤ r + 2 * delta := by simpa [Metric.mem_closedBall] using hy
  have h_abs : |y - x| ≤ r + 2 * delta := by simpa [Real.dist_eq] using hdist
  have h_bound : r + 2 * delta ≤ 3 * r := by linarith
  have h_abs3 : |y - x| ≤ 3 * r := by linarith
  by_cases h1 : y ≤ x - r
  · have h2 : dist y (x - 2 * r) ≤ r := by
      rw [Real.dist_eq]
      have h3 : |y - (x - 2 * r)| ≤ r := by
        have h4 : y - (x - 2 * r) = y - x + 2 * r := by ring
        rw [h4]
        have h5 : -r ≤ y - x + 2 * r := by linarith [abs_le.mp h_abs3]
        have h6 : y - x + 2 * r ≤ r := by linarith
        exact abs_le.mpr ⟨h5, h6⟩
      exact h3
    have h_in : y ∈ Metric.closedBall (x - 2 * r) r := by
      simpa [Metric.mem_closedBall] using h2
    exact Or.inl (Or.inl h_in)
  · by_cases h2 : y ≤ x + r
    · have h3 : dist y x ≤ r := by
        rw [Real.dist_eq]
        have h4 : |y - x| ≤ r := by
          have h5 : -r ≤ y - x := by linarith
          have h6 : y - x ≤ r := by linarith
          exact abs_le.mpr ⟨h5, h6⟩
        exact h4
      have h_in : y ∈ Metric.closedBall x r := by
        simpa [Metric.mem_closedBall] using h3
      exact Or.inl (Or.inr h_in)
    · have h_y_gt : y > x + r := by linarith
      have h_lower : -r ≤ y - x - 2 * r := by linarith
      have h_upper : y - x - 2 * r ≤ r := by
        have h9 : y - x ≤ r + 2 * delta := (abs_le.mp h_abs).2
        have h10 : r + 2 * delta ≤ 3 * r := by linarith
        linarith
      have h4 : |y - x - 2 * r| ≤ r := abs_le.mpr ⟨h_lower, h_upper⟩
      have h3 : dist y (x + 2 * r) ≤ r := by
        rw [Real.dist_eq]
        have h5 : y - (x + 2 * r) = y - x - 2 * r := by ring
        rw [h5]
        exact h4
      have h_in : y ∈ Metric.closedBall (x + 2 * r) r := by
        simpa [Metric.mem_closedBall] using h3
      exact Or.inr h_in

lemma thickening_inter_containment
    {A B : Set ℝ} {x r delta : ℝ} (hdelta_pos : 0 < delta)
    (hA_thick : A ⊆ cthickening delta B) :
    A ∩ Metric.closedBall x r ⊆
    cthickening delta (B ∩ Metric.closedBall x (r + 2 * delta)) := by
  intro y hy
  have hyA : y ∈ A := hy.1
  have hyball : dist y x ≤ r := by simpa [Metric.mem_closedBall] using hy.2
  have h_y_in : y ∈ cthickening delta B := hA_thick hyA
  have h_infEDist_B : infEDist y B ≤ ENNReal.ofReal delta := by
    simpa [cthickening, Set.mem_setOf_eq] using h_y_in
  by_contra h_not
  have h_infEDist_core_gt : infEDist y (B ∩ Metric.closedBall x (r + 2 * delta)) > ENNReal.ofReal delta := by
    simpa [cthickening, Set.mem_setOf_eq] using h_not
  have h_exists_eps : ∃ ε : ℝ, 0 < ε ∧
      infEDist y (B ∩ Metric.closedBall x (r + 2 * delta)) ≥ ENNReal.ofReal (delta + ε) := by
    let S' := B ∩ Metric.closedBall x (r + 2 * delta)
    by_cases h_top : infEDist y S' = ⊤
    · refine ⟨1, by norm_num, ?_⟩
      rw [h_top] <;> simp
    · have h_ne_top : infEDist y S' ≠ ⊤ := h_top
      let r' : ℝ := ENNReal.toReal (infEDist y S')
      have hr : ENNReal.ofReal r' = infEDist y S' := by
        exact ENNReal.ofReal_toReal_eq_iff.mpr h_top
      have h_gt : r' > delta := by
        have h1 : ENNReal.ofReal r' > ENNReal.ofReal delta := by
          rw [hr] <;> exact h_infEDist_core_gt
        have h2 : 0 ≤ delta := by linarith
        have h3 : ENNReal.ofReal r' > ENNReal.ofReal delta ↔ r' > delta :=
          ENNReal.ofReal_lt_ofReal_iff_of_nonneg h2
        exact h3.mp h1
      set ε : ℝ := (r' - delta) / 2 with hε_def
      have hε_pos : 0 < ε := by
        rw [hε_def]
        exact half_pos (sub_pos.mpr h_gt)
      have h4 : delta + ε ≤ r' := by rw [hε_def] <;> linarith
      have h5 : ENNReal.ofReal (delta + ε) ≤ ENNReal.ofReal r' := ENNReal.ofReal_le_ofReal h4
      refine ⟨ε, hε_pos, ?_⟩
      rw [←hr]; exact h5
  rcases h_exists_eps with ⟨ε, hε_pos, h_core_ge⟩
  let ε' := min ε delta
  have hε'_pos : 0 < ε' := by positivity
  have hε'_le_eps : ε' ≤ ε := by exact min_le_left _ _
  have hε'_le_delta : ε' ≤ delta := by exact min_le_right _ _
  have h_core_ge' : ∀ b ∈ B ∩ Metric.closedBall x (r + 2 * delta), dist y b ≥ delta + ε' := by
    intro b hb
    have h1 : edist y b ≥ ENNReal.ofReal (delta + ε) := by
      have h2 : infEDist y (B ∩ Metric.closedBall x (r + 2 * delta)) ≤ edist y b :=
        Metric.infEDist_le_edist_of_mem hb
      exact h_core_ge.trans h2
    have h3 : dist y b ≥ delta + ε := by
      have h4 : edist y b = ENNReal.ofReal (dist y b) := edist_dist y b
      rw [h4] at h1
      have h5 : ENNReal.ofReal (delta + ε) ≤ ENNReal.ofReal (dist y b) := h1
      have h6b : 0 ≤ dist y b := by positivity
      have h7 : (ENNReal.ofReal (delta + ε) ≤ ENNReal.ofReal (dist y b)) ↔ (delta + ε ≤ dist y b) :=
        ENNReal.ofReal_le_ofReal_iff h6b
      exact h7.mp h5
    linarith
  have h_all : ∀ b ∈ B, dist y b ≥ delta + ε' := by
    intro b hb
    by_cases hball : b ∈ Metric.closedBall x (r + 2 * delta)
    · exact h_core_ge' b ⟨hb, hball⟩
    · have h_dist_bx : dist b x > r + 2 * delta := by
        simpa [Metric.mem_closedBall, not_le] using hball
      have h_dist_yb : dist y b > 2 * delta := by
        have h1 : dist b x ≤ dist b y + dist y x := dist_triangle b y x
        have h2 : dist y x ≤ r := hyball
        have h3 : dist b y = dist y b := dist_comm b y
        rw [h3] at h1
        nlinarith
      have h3 : dist y b ≥ delta + ε' := by linarith
      exact h3
  have h_infEDist_B_ge : ENNReal.ofReal (delta + ε') ≤ infEDist y B := by
    rw [Metric.le_infEDist]
    intro b hb
    have h4 : dist y b ≥ delta + ε' := h_all b hb
    have h5 : edist y b = ENNReal.ofReal (dist y b) := edist_dist y b
    rw [h5]
    exact ENNReal.ofReal_le_ofReal h4
  have h6 : ENNReal.ofReal (delta + ε') > ENNReal.ofReal delta := by
    have h_pos : 0 ≤ delta := by linarith
    have h_iff : ENNReal.ofReal delta < ENNReal.ofReal (delta + ε') ↔ delta < delta + ε' :=
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg h_pos
    exact h_iff.mpr (by linarith)
  have h7 : ENNReal.ofReal (delta + ε') ≤ ENNReal.ofReal delta :=
    le_trans h_infEDist_B_ge h_infEDist_B
  exact not_le.mpr h6 h7

-- ===== 10. Main theorem =====

theorem wz1_ad_affine_thickening_transport :
    WZ1ADAffineThickeningTransportStatement := by
  intro E A delta alpha a b C hdelta hdelta_one halpha halpha_one ha_lower ha_upper hAD hA_bounded hthick
  have h_affine := @IsADSet1.affine_image_covering E delta alpha a b C hAD ha_lower ha_upper
  rcases hAD with ⟨hδ_pos, hα_pos, hα_one, hC_one, hE_bounded, hcover⟩
  let S : Set ℝ := (fun u : ℝ => a * u + b) '' E
  have h60C_one : (1 : ENNReal) ≤ 60 * C := by
    have h1 : (1 : ENNReal) ≤ C := hC_one
    have h2 : (1 : ENNReal) ≤ 60 := by norm_num
    have h3 : (1 : ENNReal) ≤ 60 * C := by
      calc (1 : ENNReal) ≤ 60 := by norm_num
           _ ≤ 60 * C := le_mul_of_one_le_right' h1
    exact h3
  have h_main_cover : ∀ (rho : ℝ) (hrho : 0 ≤ rho) (hdelta_rho : delta ≤ rho) (hrho_one : rho ≤ 1)
      (x : ℝ) (r : ℝ) (hrho_r : rho ≤ r) (hr_one : r ≤ 1),
      (↑(externalCoveringNumber ⟨rho, hrho⟩ (A ∩ Metric.closedBall x r)) : ENNReal) ≤
        (60 * C) * Kakeya.realRpowENN (r / rho) alpha := by
    intro rho hrho hdelta_rho hrho_one x r hrho_r hr_one
    have hdelta_le_r : delta ≤ r := by linarith
    let c1 := x - 2 * r
    let c2 := x
    let c3 := x + 2 * r
    let S1 := S ∩ Metric.closedBall c1 r
    let S2 := S ∩ Metric.closedBall c2 r
    let S3 := S ∩ Metric.closedBall c3 r
    have h_contain : A ∩ Metric.closedBall x r ⊆
        cthickening delta (S ∩ Metric.closedBall x (r + 2 * delta)) :=
      thickening_inter_containment hdelta hthick
    have h_split : S ∩ Metric.closedBall x (r + 2 * delta) ⊆ S1 ∪ S2 ∪ S3 := by
      intro y hy
      have hball : y ∈ Metric.closedBall x (r + 2 * delta) := hy.2
      have h : y ∈ (Metric.closedBall c1 r ∪ Metric.closedBall c2 r ∪ Metric.closedBall c3 r) :=
        closedBall_split_three hdelta_le_r hball
      have hyS : y ∈ S := hy.1
      have h4 : S ∩ (Metric.closedBall c1 r ∪ Metric.closedBall c2 r ∪ Metric.closedBall c3 r) ⊆ S1 ∪ S2 ∪ S3 := by
        intro z hz
        have hzS : z ∈ S := hz.1
        have hzU : z ∈ (Metric.closedBall c1 r ∪ Metric.closedBall c2 r ∪ Metric.closedBall c3 r) := hz.2
        have h5 : z ∈ S1 ∪ S2 ∪ S3 := by
          simp only [S1, S2, S3, Set.mem_union] at hzU ⊢
          tauto
        exact h5
      exact h4 ⟨hyS, h⟩
    have h_mono1 : externalCoveringNumber ⟨rho, hrho⟩ (A ∩ Metric.closedBall x r) ≤
        externalCoveringNumber ⟨rho, hrho⟩ (cthickening delta (S ∩ Metric.closedBall x (r + 2 * delta))) :=
      externalCoveringNumber_mono_set h_contain
    have h_thick : externalCoveringNumber ⟨rho, hrho⟩ (cthickening delta (S ∩ Metric.closedBall x (r + 2 * delta))) ≤
        2 * externalCoveringNumber ⟨rho, hrho⟩ (S ∩ Metric.closedBall x (r + 2 * delta)) :=
      externalCoveringNumber_cthickening_le_two (hdelta := by linarith) hdelta_rho
    have h_mono2 : externalCoveringNumber ⟨rho, hrho⟩ (S ∩ Metric.closedBall x (r + 2 * delta)) ≤
        externalCoveringNumber ⟨rho, hrho⟩ (S1 ∪ S2 ∪ S3) :=
      externalCoveringNumber_mono_set h_split
    have h_union : (↑(externalCoveringNumber ⟨rho, hrho⟩ (S1 ∪ S2 ∪ S3)) : ENNReal) ≤
        (↑(externalCoveringNumber ⟨rho, hrho⟩ S1) : ENNReal) +
        (↑(externalCoveringNumber ⟨rho, hrho⟩ S2) : ENNReal) +
        (↑(externalCoveringNumber ⟨rho, hrho⟩ S3) : ENNReal) :=
      externalCoveringNumber_three_union_le
    have h_aff1 := h_affine rho hrho hdelta_rho hrho_one c1 r hrho_r hr_one
    have h_aff2 := h_affine rho hrho hdelta_rho hrho_one c2 r hrho_r hr_one
    have h_aff3 := h_affine rho hrho hdelta_rho hrho_one c3 r hrho_r hr_one
    have h_sum : (↑(externalCoveringNumber ⟨rho, hrho⟩ (S1 ∪ S2 ∪ S3)) : ENNReal) ≤
        3 * ((10 * C) * Kakeya.realRpowENN (r / rho) alpha) := by
      calc
        _ ≤ _ + _ + _ := h_union
        _ ≤ (10 * C) * Kakeya.realRpowENN (r / rho) alpha +
              (10 * C) * Kakeya.realRpowENN (r / rho) alpha +
              (10 * C) * Kakeya.realRpowENN (r / rho) alpha := by gcongr
        _ = 3 * ((10 * C) * Kakeya.realRpowENN (r / rho) alpha) := by ring
    have h_final : (↑(externalCoveringNumber ⟨rho, hrho⟩ (A ∩ Metric.closedBall x r)) : ENNReal) ≤
        (60 * C) * Kakeya.realRpowENN (r / rho) alpha := by
      have h1 : (↑(externalCoveringNumber ⟨rho, hrho⟩ (A ∩ Metric.closedBall x r)) : ENNReal) ≤
          (↑(2 * externalCoveringNumber ⟨rho, hrho⟩ (S ∩ Metric.closedBall x (r + 2 * delta))) : ENNReal) := by
        exact_mod_cast h_mono1.trans h_thick
      have h2 : (↑(2 * externalCoveringNumber ⟨rho, hrho⟩ (S ∩ Metric.closedBall x (r + 2 * delta))) : ENNReal) ≤
          2 * (↑(externalCoveringNumber ⟨rho, hrho⟩ (S1 ∪ S2 ∪ S3)) : ENNReal) := by
        exact_mod_cast mul_le_mul_of_nonneg_left h_mono2 (by norm_num)
      have h3 : 2 * (↑(externalCoveringNumber ⟨rho, hrho⟩ (S1 ∪ S2 ∪ S3)) : ENNReal) ≤
          2 * (3 * ((10 * C) * Kakeya.realRpowENN (r / rho) alpha)) := by
        gcongr
      have h4 : 2 * (3 * ((10 * C) * Kakeya.realRpowENN (r / rho) alpha)) =
          (60 * C) * Kakeya.realRpowENN (r / rho) alpha := by
        simp [mul_assoc] <;> ring
      rw [h4] at h3
      exact h1.trans (h2.trans h3)
    exact h_final
  have hAD_A : IsADSet1 A delta alpha (60 * C) :=
    ⟨hdelta, halpha, halpha_one, h60C_one, hA_bounded, h_main_cover⟩
  have h_weaken : (60 : ENNReal) * C ≤ 100000 * C := by
    have h5 : (60 : ENNReal) ≤ 100000 := by norm_num
    exact mul_le_mul_left h5 C
  exact hAD_A.mono_constant h_weaken

end Kakeya.Assouad
