module

/-
  Format conversion lemmas for the combining theorem (SL-7).

  M4: Scale sequence reindexing after removing the first block.
  M3: Between-scales property restriction under homothety.

  Whiteprint node: combining_sl7_format_conversion
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ElementaryIncidence
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

open DiscretisedFurstenbergEstimate.CombiningTheorem

namespace DirecretisedFurstenbergEstimate.FormatConversion

open DiscretisedFurstenbergEstimate

/-! ============================================================================
   M4: Scale sequence reindexing

   Original: m+1 blocks, scale sequence Δ : Fin (m+2) → ℝ
   After removing first block: m blocks, scale sequence Δ' : Fin (m+1) → ℝ

   The new sequence is rescaled by Δ 1:
     Δ' i = Δ (i+1) / Δ 1
   ============================================================================ -/

/-- Drop the first scale point and rescale by Δ 1.
    Original has m+1 blocks (m+2 scale points); result has m blocks (m+1 points). -/
def dropFirstScale (m : ℕ) (Δ : Fin (m + 2) → ℝ) : Fin (m + 1) → ℝ :=
  fun i : Fin (m + 1) => Δ (Fin.succ i) / Δ 1

/-- Drop the first scale classification.
    Original has m+1 blocks; result has m blocks. -/
def dropFirstScaleClass (m : ℕ) (scaleClass : Fin (m + 1) → ScaleClass) :
    Fin m → ScaleClass :=
  fun j : Fin m => scaleClass (Fin.succ j)

namespace M4

variable {m : ℕ} {Δ : Fin (m + 2) → ℝ} {scaleClass : Fin (m + 1) → ScaleClass}

/-- The first point of the rescaled sequence is 1. -/
lemma dropFirstScale_zero (hΔ1_pos : 0 < Δ 1) :
    dropFirstScale m Δ 0 = 1 := by
  have h : dropFirstScale m Δ 0 = Δ (Fin.succ (0 : Fin (m + 1))) / Δ 1 := by rfl
  rw [h]
  have h2 : Fin.succ (0 : Fin (m + 1)) = (1 : Fin (m + 2)) := by
    apply Fin.ext
    <;> simp
  rw [h2]
  <;> field_simp [hΔ1_pos.ne'] <;> ring

/-- Strict decrease is preserved. -/
lemma dropFirstScale_strict
    (hΔ_strict : ∀ i : Fin (m + 1), Δ (Fin.succ i) < Δ i.castSucc)
    (hΔ1_pos : 0 < Δ 1) :
    ∀ i : Fin m,
      dropFirstScale m Δ (Fin.succ i) < dropFirstScale m Δ i.castSucc := by
  intro i
  have h1 : Δ (Fin.succ (Fin.succ i)) < Δ (Fin.succ i).castSucc :=
    hΔ_strict (Fin.succ i)
  have h_goal : (Δ (Fin.succ (Fin.succ i)) / Δ 1) < (Δ (Fin.succ i).castSucc / Δ 1) := by
    gcongr
    <;> exact h1
  simpa [dropFirstScale] using h_goal

/-- Positivity is preserved. -/
lemma dropFirstScale_pos (hΔ_pos : ∀ i : Fin (m + 2), 0 < Δ i) :
    ∀ i : Fin (m + 1), 0 < dropFirstScale m Δ i := by
  intro i
  apply div_pos (hΔ_pos (Fin.succ i)) (hΔ_pos 1)

/-- Ratio identity: for j : Fin m, the coarse/fine ratio in the rescaled
    sequence equals the ratio in the original sequence at block j+1. -/
lemma ratio_preserved (j : Fin m) (hΔ1_pos : 0 < Δ 1) :
    dropFirstScale m Δ j.castSucc / dropFirstScale m Δ (Fin.succ j) =
      Δ (Fin.succ j).castSucc / Δ (Fin.succ (Fin.succ j)) := by
  simp [dropFirstScale]
  <;> field_simp [hΔ1_pos.ne'] <;> ring

/-- Bad ratio identity (fine/coarse). -/
lemma badRatio_preserved (j : Fin m) (hΔ1_pos : 0 < Δ 1) :
    dropFirstScale m Δ (Fin.succ j) / dropFirstScale m Δ j.castSucc =
      Δ (Fin.succ (Fin.succ j)) / Δ (Fin.succ j).castSucc := by
  simp [dropFirstScale]
  <;> field_simp [hΔ1_pos.ne'] <;> ring

/-- The good set after dropping the first block corresponds to the original
    good set with block 0 removed, under Fin.succ. -/
lemma goodSet_image :
    Finset.image Fin.succ ((Finset.univ : Finset (Fin m)).filter
      (fun j => (dropFirstScaleClass m scaleClass j).isGood)) =
    (Finset.univ.filter (fun j : Fin (m + 1) => (scaleClass j).isGood)).erase 0 := by
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, dropFirstScaleClass]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Fin.succ_ne_zero j, hj⟩
  · rintro ⟨hne, hgood⟩
    have h_eq : (scaleClass (Fin.succ (x.pred hne))).isGood = (scaleClass x).isGood := by
      have h_succ : Fin.succ (x.pred hne) = x := Fin.succ_pred x hne
      rw [h_succ]
    refine' ⟨x.pred hne, by rwa [h_eq], _⟩
    simp

/-- The bad set after dropping the first block corresponds to the original
    bad set with block 0 removed, under Fin.succ. -/
lemma badSet_image :
    Finset.image Fin.succ ((Finset.univ : Finset (Fin m)).filter
      (fun j => (dropFirstScaleClass m scaleClass j).isBad)) =
    (Finset.univ.filter (fun j : Fin (m + 1) => (scaleClass j).isBad)).erase 0 := by
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, dropFirstScaleClass]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Fin.succ_ne_zero j, hj⟩
  · rintro ⟨hne, hbad⟩
    have h_eq : (scaleClass (Fin.succ (x.pred hne))).isBad = (scaleClass x).isBad := by
      have h_succ : Fin.succ (x.pred hne) = x := Fin.succ_pred x hne
      rw [h_succ]
    refine' ⟨x.pred hne, by rwa [h_eq], _⟩
    simp

/-- Good product over remaining blocks equals original good product
    excluding block 0. -/
lemma goodProduct_restrict (hΔ1_pos : 0 < Δ 1) (η : ℝ) :
    ∏ j ∈ (Finset.univ : Finset (Fin m)).filter
          (fun j => (dropFirstScaleClass m scaleClass j).isGood),
        Real.rpow (dropFirstScale m Δ j.castSucc /
                      dropFirstScale m Δ (Fin.succ j)) η =
    ∏ j ∈ (Finset.univ.filter (fun j : Fin (m + 1) => (scaleClass j).isGood)).erase 0,
        Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η := by
  let s : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter
      (fun j => (dropFirstScaleClass m scaleClass j).isGood)
  have h_inj : Set.InjOn (Fin.succ : Fin m → Fin (m + 1)) (s : Set (Fin m)) :=
    fun x _ y _ h => Fin.succ_injective m h
  have h_main : ∏ j ∈ s, Real.rpow (dropFirstScale m Δ j.castSucc /
                      dropFirstScale m Δ (Fin.succ j)) η =
      ∏ k ∈ Finset.image Fin.succ s, Real.rpow (Δ k.castSucc / Δ (Fin.succ k)) η := by
    rw [Finset.prod_image h_inj]
    apply Finset.prod_congr rfl
    intro j _
    exact congr_arg (fun x : ℝ => Real.rpow x η) (ratio_preserved j hΔ1_pos)
  rw [h_main, goodSet_image]

/-- Bad product over remaining blocks equals original bad product
    excluding block 0. -/
lemma badProduct_restrict (hΔ1_pos : 0 < Δ 1) :
    ∏ j ∈ (Finset.univ : Finset (Fin m)).filter
          (fun j => (dropFirstScaleClass m scaleClass j).isBad),
        dropFirstScale m Δ (Fin.succ j) / dropFirstScale m Δ j.castSucc =
    ∏ j ∈ (Finset.univ.filter (fun j : Fin (m + 1) => (scaleClass j).isBad)).erase 0,
        Δ (Fin.succ j) / Δ j.castSucc := by
  let s : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter
      (fun j => (dropFirstScaleClass m scaleClass j).isBad)
  have h_inj : Set.InjOn (Fin.succ : Fin m → Fin (m + 1)) (s : Set (Fin m)) :=
    fun x _ y _ h => Fin.succ_injective m h
  have h_main : ∏ j ∈ s, dropFirstScale m Δ (Fin.succ j) / dropFirstScale m Δ j.castSucc =
      ∏ k ∈ Finset.image Fin.succ s, Δ (Fin.succ k) / Δ k.castSucc := by
    rw [Finset.prod_image h_inj]
    apply Finset.prod_congr rfl
    intro j _
    exact badRatio_preserved j hΔ1_pos
  rw [h_main, badSet_image]

end M4

/-! ============================================================================
   M3: Homothety invariance of IsDeltaSSet in EuclideanPlane

   If P is a (δ, s, C)-set and a > 0, then a • P is an
   (a*δ, s, C*a^{-s})-set.
   ============================================================================ -/

namespace M3

/-- Homothety invariance of IsDeltaSSet in EuclideanPlane.

    If P is a (δ, s, C)-set and a > 0, then a • P is an
    (a*δ, s, C*a^{-s})-set. -/
lemma rescale_sset_euclidean {δ s C : ℝ} {P : Set EuclideanPlane} {a : ℝ}
    (ha_pos : 0 < a) (hP : IsDeltaSSet δ s C P) :
    IsDeltaSSet (a * δ) s (C * a ^ (-s))
      ((fun x : EuclideanPlane => a • x) '' P) := by
  rcases hP with ⟨hP_nonempty, hδ_pos, hC_pos, hs_nonneg, hmain⟩
  have haδ_pos : 0 < a * δ := mul_pos ha_pos hδ_pos
  have hC'_pos : 0 < C * a ^ (-s) := by positivity
  set f : EuclideanPlane → EuclideanPlane := fun x => a • x with hf_def
  set g : EuclideanPlane → EuclideanPlane := fun x => (1 / a) • x with hg_def
  set P' := f '' P with hP'_def
  have hP'_nonempty : P'.Nonempty := hP_nonempty.image f

  let K : NNReal := ⟨a, ha_pos.le⟩
  let Kinv : NNReal := ⟨1 / a, by positivity⟩

  have h_dist_f : ∀ x y : EuclideanPlane, dist (f x) (f y) = a * dist x y := by
    intro x y
    have h1 : f x - f y = a • (x - y) := by
      simp [hf_def, smul_sub] <;> abel
    have h2 : ‖f x - f y‖ = a * ‖x - y‖ := by
      have h3 : ‖a • (x - y)‖ = ‖a‖ * ‖x - y‖ := norm_smul a (x - y)
      rw [h1, h3]
      have h4 : ‖a‖ = |a| := by exact Real.norm_eq_abs a
      rw [h4, abs_of_pos ha_pos] <;> ring
    simpa [dist_eq_norm] using h2

  have h_dist_g : ∀ x y : EuclideanPlane, dist (g x) (g y) = (1 / a) * dist x y := by
    intro x y
    have h1 : g x - g y = (1 / a) • (x - y) := by
      simp [hg_def, smul_sub] <;> abel
    have h2 : ‖g x - g y‖ = (1 / a) * ‖x - y‖ := by
      have h3 : ‖(1 / a) • (x - y)‖ = ‖(1 / a)‖ * ‖x - y‖ := norm_smul (1 / a) (x - y)
      rw [h1, h3]
      have h4 : ‖(1 / a)‖ = |1 / a| := by exact Real.norm_eq_abs (1 / a)
      have h5 : 0 < (1 / a : ℝ) := by positivity
      rw [h4, abs_of_pos h5] <;> ring
    simpa [dist_eq_norm] using h2

  have hf_lip : LipschitzWith K f :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [h_dist_f x y] <;> exact le_refl _

  have hg_lip : LipschitzWith Kinv g :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [h_dist_g x y] <;> exact le_refl _

  have hgf : ∀ x, g (f x) = x := by
    intro x
    have h : g (f x) = (1 / a) • (a • x) := by rfl
    rw [h]
    have h2 : (1 / a) • (a • x) = ((1 / a) * a) • x := by
      rw [smul_smul]
    rw [h2]
    have h3 : (1 / a) * a = 1 := by field_simp [ha_pos.ne']
    rw [h3, one_smul]

  have hfg : ∀ y, f (g y) = y := by
    intro y
    have h : f (g y) = a • ((1 / a) • y) := by rfl
    rw [h]
    have h2 : a • ((1 / a) • y) = (a * (1 / a)) • y := by rw [smul_smul]
    rw [h2]
    have h3 : a * (1 / a) = 1 := by field_simp [ha_pos.ne']
    rw [h3, one_smul]

  have hδ_nonneg : 0 ≤ δ := by linarith
  have haδ_nonneg : 0 ≤ a * δ := by positivity

  have hK_coe : (↑K : ℝ) = a := by exact Real.ext_cauchy rfl
  have hKinv_coe : (↑Kinv : ℝ) = 1 / a := by exact Eq.symm (Real.ext_cauchy rfl)

  have hK_eq : (K * δ.toNNReal : NNReal) = (a * δ).toNNReal := by
    apply NNReal.coe_injective
    simp [hK_coe, NNReal.coe_mul, Real.toNNReal_of_nonneg hδ_nonneg,
      Real.toNNReal_of_nonneg haδ_nonneg] <;> ring

  have hKinv_eq : (Kinv * (a * δ).toNNReal : NNReal) = δ.toNNReal := by
    apply NNReal.coe_injective
    simp [hKinv_coe, NNReal.coe_mul, Real.toNNReal_of_nonneg haδ_nonneg,
      Real.toNNReal_of_nonneg hδ_nonneg] <;> field_simp [ha_pos.ne'] <;> ring

  -- Covering number equality under scaling
  have h_cover_eq : ∀ (A : Set EuclideanPlane),
      Metric.externalCoveringNumber (a * δ).toNNReal (f '' A) =
      Metric.externalCoveringNumber δ.toNNReal A := by
    intro A
    have h1 : Metric.externalCoveringNumber (K * δ.toNNReal) (f '' A) ≤
        Metric.externalCoveringNumber δ.toNNReal A :=
      DiscretisedFurstenbergEstimate.CoveringUtils.externalCoveringNumber_image_lipschitz (hf := hf_lip)
    have h2 : Metric.externalCoveringNumber (Kinv * (a * δ).toNNReal) (g '' (f '' A)) ≤
        Metric.externalCoveringNumber (a * δ).toNNReal (f '' A) :=
      DiscretisedFurstenbergEstimate.CoveringUtils.externalCoveringNumber_image_lipschitz (hf := hg_lip)
    have h3 : g '' (f '' A) = A := by
      ext z
      simp only [Set.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases hy with ⟨x, hx, rfl⟩
        have h_eq : g (f x) = x := hgf x
        rw [h_eq]
        exact hx
      · intro hz
        refine' ⟨f z, ⟨z, hz, rfl⟩, _⟩
        exact hgf z
    rw [hK_eq] at h1
    rw [hKinv_eq, h3] at h2
    exact le_antisymm h1 h2

  refine' ⟨hP'_nonempty, haδ_pos, hC'_pos, hs_nonneg, _⟩
  intro y r hr
  let x := g y
  set r' : ℝ := r / a with hr'_def
  have har' : a * r' = r := by
    rw [hr'_def] <;> field_simp [ha_pos.ne'] <;> ring
  have hr'_pos : 0 ≤ r' := by
    have h : 0 ≤ r := by linarith [haδ_pos, hr]
    positivity
  have hδ_le_r' : δ ≤ r' := by
    have h : a * δ ≤ r := hr
    have h2 : δ ≤ r / a := by
      calc δ = (a * δ) / a := by field_simp [ha_pos.ne'] <;> ring
        _ ≤ r / a := by gcongr
    exact h2
  have hball : f '' (P ∩ Metric.closedBall x r') = P' ∩ Metric.closedBall y r := by
    ext z
    simp only [Set.mem_image, Set.mem_inter_iff]
    constructor
    · rintro ⟨w, ⟨hwP, hwball⟩, rfl⟩
      have hwr : dist w x ≤ r' := hwball
      have hdist : dist (f w) y ≤ r := by
        calc dist (f w) y = dist (f w) (f x) := by rw [hfg y]
          _ = a * dist w x := h_dist_f w x
          _ ≤ a * r' := by exact mul_le_mul_of_nonneg_left hwr (by linarith)
          _ = r := har'
      exact ⟨Set.mem_image_of_mem f hwP, hdist⟩
    · rintro ⟨⟨w, hwP, rfl⟩, hdist⟩
      have hdist' : dist w x ≤ r' := by
        have h : dist (f w) (f x) = a * dist w x := h_dist_f w x
        have h9 : dist (f w) y ≤ r := hdist
        rw [show dist (f w) y = dist (f w) (f x) from by rw [hfg y]] at h9
        rw [h] at h9
        have h10 : a * dist w x ≤ r := h9
        have h11 : dist w x ≤ r / a := by
          calc dist w x = (a * dist w x) / a := by field_simp [ha_pos.ne'] <;> ring
            _ ≤ r / a := by gcongr
        exact h11
      exact ⟨w, ⟨hwP, hdist'⟩, rfl⟩

  have h4 : (Metric.externalCoveringNumber (a * δ).toNNReal
        (P' ∩ Metric.closedBall y r) : ENNReal) =
      (Metric.externalCoveringNumber δ.toNNReal
        (P ∩ Metric.closedBall x r') : ENNReal) := by
    rw [←hball]
    exact_mod_cast h_cover_eq (P ∩ Metric.closedBall x r')

  have h5 : (Metric.externalCoveringNumber δ.toNNReal
        (P ∩ Metric.closedBall x r') : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r') ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) :=
    hmain x r' hδ_le_r'

  have h6 : (Metric.externalCoveringNumber (a * δ).toNNReal P' : ENNReal) =
      (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
    exact_mod_cast h_cover_eq P

  have h7 : ENNReal.ofReal (C * a ^ (-s)) * (ENNReal.ofReal r) ^ s =
      ENNReal.ofReal C * (ENNReal.ofReal r') ^ s := by
    have h_r_nonneg : 0 ≤ r := by linarith
    have h_r'_nonneg : 0 ≤ r' := by
      have h : 0 ≤ r := by linarith
      positivity
    have h_real_eq : C * a ^ (-s) * r ^ s = C * (r') ^ s := by
      have h1 : r' = r / a := by rw [hr'_def] <;> ring
      rw [h1]
      have h2 : a ^ (-s) * r ^ s = (r / a) ^ s := by
        have h3 : a ^ (-s) = (1 / a) ^ s := by
          have h4 : (1 / a) ^ s = a ^ (-s) := by
            have h5 : (1 / a) = a⁻¹ := by field_simp [ha_pos.ne']
            rw [h5] <;> exact Eq.symm (Real.rpow_neg_eq_inv_rpow a s)
          exact h4.symm
        rw [h3]
        have h_pos1 : 0 ≤ (1 / a : ℝ) := by positivity
        have h_pos2 : 0 ≤ r := by linarith
        have h6 : ((1 / a) ^ s) * r ^ s = ((1 / a) * r) ^ s := by
          have h_rpow : ∀ (x y : ℝ), 0 ≤ x → 0 ≤ y → (x * y) ^ s = x ^ s * y ^ s := by
            intro x y hx hy
            exact Real.mul_rpow hx hy
          exact (h_rpow (1 / a) r h_pos1 h_pos2).symm
        rw [h6]
        have h7 : (1 / a) * r = r / a := by ring
        rw [h7]
      have h_goal : C * (a ^ (-s) * r ^ s) = C * (r / a) ^ s := by
        rw [h2]
      simpa [mul_assoc] using h_goal
    have hA : ENNReal.ofReal (C * a ^ (-s)) * (ENNReal.ofReal r) ^ s =
        ENNReal.ofReal (C * a ^ (-s) * r ^ s) := by
      have hB : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg h_r_nonneg hs_nonneg] <;> rfl
      rw [hB]
      rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
    have hC : ENNReal.ofReal C * (ENNReal.ofReal r') ^ s =
        ENNReal.ofReal (C * (r') ^ s) := by
      have hD : (ENNReal.ofReal r') ^ s = ENNReal.ofReal ((r') ^ s) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg h_r'_nonneg hs_nonneg] <;> rfl
      rw [hD]
      rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
    rw [hA, hC, h_real_eq]
  rw [h4, h6, h7]
  exact h5

end M3

/-! ============================================================================
   M1: prop5 wrapper for NiceConfiguration

   Converts a NiceConfiguration to DSquare/DTube format, applies prop5,
   and returns the incidence bound in NiceConfiguration terms.

   Constant blowup: tube S-set constant C₁ → 13 · C₁ · 2^s
   (from deltaSSet_dyadicToDTube).
   ============================================================================ -/

namespace M1

open DiscretisedFurstenbergEstimate.DyadicConversion

/-- Tube-toSet correspondence: a DTube and its DyadicTube counterpart
    describe the same geometric strip under EuclideanPlane ↔ ℝ×ℝ. -/
lemma tubeToSet_correspondence {n : ℕ} (T : DTube n) (x : EuclideanPlane) :
    x ∈ (dTubeToDyadicTube T).toSet ↔
      (x 0, x 1) ∈ T.toSet := by
  have hδ : δ n = dyadicDelta n := scale_eq
  have hsl : (dTubeToDyadicTube T).slope = T.slope := slope_eq T
  have hsi : (dTubeToDyadicTube T).intercept = T.intercept := intercept_eq T
  simp [DyadicTube.toSet, DTube.toSet, hsl, hsi, hδ] <;> rfl

/-- prop5 wrapper: given a NiceConfiguration with point-set S-set property
    and slope-bounded tubes, produce the elementary incidence lower bound.

    The tube S-set constant C₁ blows up to 13 · C₁ · 2^s under the
    DyadicTube → DTube conversion. -/
lemma prop5_wrapper
    {n : ℕ} {s t C₁ C_P : ℝ} {M : ℕ}
    (config : NiceConfiguration n s C₁ M)
    (hn_ge_2 : 2 ≤ n)
    (hM_pos : 0 < M)
    (hP_nonempty : config.P₀.Nonempty)
    (h_st : 0 ≤ s ∧ s ≤ t ∧ t ≤ 1)
    (hCP : 0 < C_P)
    (hC₁ : 0 < C₁)
    (hs_nonneg : 0 ≤ s)
    -- Point set S-set property (not provided by NiceConfiguration)
    (hP_set : IsFinsetDeltaSSet (dyadicDelta n) t C_P
      (finsetDyadicToDSquare config.P₀))
    -- Slope bound (not provided by NiceConfiguration)
    (h_slope : ∀ T ∈ config.T₀, |T.slope| ≤ 1) :
    ∃ (K : ℝ), 0 < K ∧
      (config.T₀.card : ℝ) ≥
        (1 / K) * Real.log (1 / dyadicDelta n) ^ (-K) *
          (1 / (C_P * (13 * C₁ * 2 ^ s))) * (M : ℝ) *
          (dyadicDelta n) ^ (-s) *
          ((M : ℝ) * (dyadicDelta n) ^ s) ^ ((t - s) / (1 - s)) := by
  classical
  let P' : Finset (DSquare n) := finsetDyadicToDSquare config.P₀
  let C_T : ℝ := 13 * C₁ * 2 ^ s
  have hCT_pos : 0 < C_T := by positivity

  -- Key equivalence: p' ∈ P' ↔ dSquareToDyadicSquare p' ∈ config.P₀
  have h_mem_iff : ∀ (p' : DSquare n), p' ∈ P' ↔ dSquareToDyadicSquare p' ∈ config.P₀ := by
    intro p'
    simp [P', finsetDyadicToDSquare, Finset.mem_image]
    constructor
    · rintro ⟨p_dy, hpin, rfl⟩
      have h_rt : dSquareToDyadicSquare (dyadicSquareToDSquare p_dy) = p_dy := by
        cases p_dy
        rfl
      rw [h_rt] <;> exact hpin
    · intro hpin
      refine' ⟨dSquareToDyadicSquare p', hpin, _⟩
      cases p'
      rfl

  -- Key equivalence for tubes: t' ∈ finsetDyadicToDTube F ↔ dTubeToDyadicTube t' ∈ F
  have h_tube_mem_iff : ∀ (F : Finset (DyadicTube n)) (t' : DTube n),
      t' ∈ finsetDyadicToDTube F ↔ dTubeToDyadicTube t' ∈ F := by
    intro F t'
    simp [finsetDyadicToDTube, Finset.mem_image]
    constructor
    · rintro ⟨T_dy, hT, rfl⟩
      have h_rt : dTubeToDyadicTube (dyadicTubeToDTube T_dy) = T_dy := roundtrip_dyadic T_dy
      rw [h_rt] <;> exact hT
    · intro hT
      refine' ⟨dTubeToDyadicTube t', hT, _⟩
      exact roundtrip_dtube t'

  -- Preimage = image equivalence for deltaSSet_dyadicToDTube
  have h_preimage_eq_image : ∀ (F : Finset (DyadicTube n)),
      (dTubeToDyadicTube ⁻¹' (F : Set (DyadicTube n))) =
      (finsetDyadicToDTube F : Set (DTube n)) := by
    intro F
    ext t'
    simp only [Set.mem_preimage, Finset.mem_coe]
    exact (h_tube_mem_iff F t').symm

  -- Define tube family in DSquare/DTube format
  let Tp : DSquare n → Finset (DTube n) := fun p' =>
    let p_dy := dSquareToDyadicSquare p'
    if h : p_dy ∈ config.P₀ then
      finsetDyadicToDTube (config.tubeFamily p_dy h)
    else
      ∅

  have hP'_nonempty : P'.Nonempty := by
    rcases hP_nonempty with ⟨p, hp⟩
    refine' ⟨dyadicSquareToDSquare p, _⟩
    simp [P', finsetDyadicToDSquare, Finset.mem_image, hp]
    <;> exact ⟨p, hp, rfl⟩

  -- Tube family S-set transfer
  have hTp_set : ∀ p' ∈ P', IsFinsetDeltaSSet (δ n) s C_T (Tp p') := by
    intro p' hp'
    let p_dy := dSquareToDyadicSquare p'
    have h_p_in : p_dy ∈ config.P₀ := (h_mem_iff p').mp hp'
    have h1 : Tp p' = finsetDyadicToDTube (config.tubeFamily p_dy h_p_in) := by
      unfold Tp
      rw [dif_pos h_p_in]
    rw [h1]
    have h2 : IsDeltaSSet (dyadicDelta n) s C₁
        (config.tubeFamily p_dy h_p_in : Set (DyadicTube n)) :=
      config.h_delta_s_set p_dy h_p_in
    have h3 : IsDeltaSSet (dyadicDelta n) s C_T
        (dTubeToDyadicTube ⁻¹' (config.tubeFamily p_dy h_p_in : Set (DyadicTube n))) :=
      deltaSSet_dyadicToDTube hs_nonneg hC₁ h2
    rw [h_preimage_eq_image (config.tubeFamily p_dy h_p_in)] at h3
    have hδ : (dyadicDelta n) = δ n := scale_eq.symm
    rw [hδ] at h3
    exact h3

  -- Incidence transfer
  have hTp_int : ∀ p' ∈ P', ∀ t' ∈ Tp p', (t'.toSet ∩ p'.toSet).Nonempty := by
    intro p' hp' t' ht'
    let p_dy := dSquareToDyadicSquare p'
    have h_p_in : p_dy ∈ config.P₀ := (h_mem_iff p').mp hp'
    let T_dy := dTubeToDyadicTube t'
    have hT_in : T_dy ∈ config.tubeFamily p_dy h_p_in := by
      have h1 : t' ∈ finsetDyadicToDTube (config.tubeFamily p_dy h_p_in) := by
        unfold Tp at ht'
        rw [dif_pos h_p_in] at ht'
        exact ht'
      exact (h_tube_mem_iff (config.tubeFamily p_dy h_p_in) t').mp h1
    have h_inc : (T_dy.toSet ∩ p_dy.toSet).Nonempty :=
      config.h_intersect p_dy h_p_in T_dy hT_in
    rcases h_inc with ⟨x, hxT, hxp⟩
    refine' ⟨(x 0, x 1), _⟩
    have h6 : (x 0, x 1) ∈ t'.toSet := by
      rw [←tubeToSet_correspondence t' x] <;> exact hxT
    have h7 : (x 0, x 1) ∈ p'.toSet := by
      rw [←toSet_correspondence p' x] <;> exact hxp
    exact ⟨h6, h7⟩

  -- Slope bound transfer
  have hTp_slope : ∀ p' ∈ P', ∀ t' ∈ Tp p', |t'.slope| ≤ 1 := by
    intro p' hp' t' ht'
    let p_dy := dSquareToDyadicSquare p'
    have h_p_in : p_dy ∈ config.P₀ := (h_mem_iff p').mp hp'
    let T_dy := dTubeToDyadicTube t'
    have hT_in_family : T_dy ∈ config.tubeFamily p_dy h_p_in := by
      have h1 : t' ∈ finsetDyadicToDTube (config.tubeFamily p_dy h_p_in) := by
        unfold Tp at ht'
        rw [dif_pos h_p_in] at ht'
        exact ht'
      exact (h_tube_mem_iff (config.tubeFamily p_dy h_p_in) t').mp h1
    have hT_in_T0 : T_dy ∈ config.T₀ := config.h_subset p_dy h_p_in hT_in_family
    have h3 : |T_dy.slope| ≤ 1 := h_slope T_dy hT_in_T0
    have h4 : t'.slope = T_dy.slope := (slope_eq t').symm
    rw [h4] <;> exact h3

  -- Card transfer
  have hTp_card : ∀ p' ∈ P', (M : ℝ) / 2 < (Tp p').card := by
    intro p' hp'
    let p_dy := dSquareToDyadicSquare p'
    have h_p_in : p_dy ∈ config.P₀ := (h_mem_iff p').mp hp'
    have h1 : (Tp p').card = (config.tubeFamily p_dy h_p_in).card := by
      unfold Tp
      rw [dif_pos h_p_in]
      exact card_dyadicToDTube _
    have h2 : M ≤ (config.tubeFamily p_dy h_p_in).card :=
      le_of_eq (config.h_size p_dy h_p_in).symm
    have hM_pos' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
    rw [h1]
    have h3 : (M : ℝ) ≤ ((config.tubeFamily p_dy h_p_in).card : ℝ) := by exact_mod_cast h2
    have h4 : (M : ℝ) / 2 < ((config.tubeFamily p_dy h_p_in).card : ℝ) := by linarith
    exact_mod_cast h4

  have hδ_eq : δ n = dyadicDelta n := scale_eq

  -- Apply prop5
  have h_main := prop5 s t h_st C_P C_T (M : ℝ) hCP hCT_pos
    (by exact_mod_cast (show 1 ≤ M from Nat.succ_le_iff.mpr hM_pos))
    hn_ge_2 P' hP'_nonempty
    (by simpa [IsFinsetDeltaSSet, hδ_eq] using hP_set)
    Tp hTp_int hTp_slope hTp_set hTp_card

  rcases h_main with ⟨K, hK_pos, h_bound⟩
  refine' ⟨K, hK_pos, _⟩

  -- The union T = P'.biUnion Tp is a subset of the DTube-image of config.T₀
  let T_dtube : Finset (DTube n) := P'.biUnion Tp
  have h_sub : T_dtube ⊆ finsetDyadicToDTube config.T₀ := by
    intro t' ht'
    rcases Finset.mem_biUnion.mp ht' with ⟨p', hp', ht'⟩
    let p_dy := dSquareToDyadicSquare p'
    have h_p_in : p_dy ∈ config.P₀ := (h_mem_iff p').mp hp'
    have h1 : t' ∈ finsetDyadicToDTube (config.tubeFamily p_dy h_p_in) := by
      unfold Tp at ht'
      rw [dif_pos h_p_in] at ht'
      exact ht'
    have h2 : dTubeToDyadicTube t' ∈ config.tubeFamily p_dy h_p_in :=
      (h_tube_mem_iff (config.tubeFamily p_dy h_p_in) t').mp h1
    have hT_in_T0 : dTubeToDyadicTube t' ∈ config.T₀ :=
      config.h_subset p_dy h_p_in h2
    exact (h_tube_mem_iff config.T₀ t').mpr hT_in_T0

  have h_card_le : T_dtube.card ≤ (finsetDyadicToDTube config.T₀).card :=
    Finset.card_le_card h_sub
  have h_card_eq : (finsetDyadicToDTube config.T₀).card = config.T₀.card :=
    card_dyadicToDTube config.T₀

  have h_final : (T_dtube.card : ℝ) ≥ (1 / K) * Real.log (1 / δ n) ^ (-K) *
      (1 / (C_P * C_T)) * (M : ℝ) * (δ n) ^ (-s) *
      ((M : ℝ) * (δ n) ^ s) ^ ((t - s) / (1 - s)) := h_bound

  rw [hδ_eq] at h_final
  have h : (config.T₀.card : ℝ) ≥ (T_dtube.card : ℝ) := by
    have h9 : (T_dtube.card : ℝ) ≤ ((finsetDyadicToDTube config.T₀).card : ℝ) := by exact_mod_cast h_card_le
    have h10 : ((finsetDyadicToDTube config.T₀).card : ℝ) = (config.T₀.card : ℝ) := by
      exact_mod_cast h_card_eq
    rw [h10] at h9
    exact h9
  exact le_trans h_final h

end M1

/-! ============================================================================
   M2: B1 bridge hypothesis preparation

   Packages the geometric boundedness hypotheses required by
   inductionOnScalesBridge_expanded_concrete.

   For arbitrary NiceConfigurations, these are taken as assumptions
   since they don't follow from the S-set property alone.
   ============================================================================ -/

namespace M2

open DiscretisedFurstenbergEstimate.InductionConfigurations

/-- Packages the three geometric boundedness hypotheses required by the
    B1 bridge. For configurations constructed from continuous data, these
    are proved by DyadicBridge. For arbitrary configurations, they must
    be verified separately. -/
structure B1BridgeHypotheses (n : ℕ) {s C : ℝ} {M : ℕ}
    (config : NiceConfiguration n s C M) where
  h_squares_unit : ∀ p ∈ config.P₀,
    0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ n : ℤ)
  h_tubes_strip : ∀ T ∈ config.T₀,
    -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ)
  h_tubes_bounded : config.T₀.card ≤ 12 * 16 ^ n

/-- If the point set is contained in the unit ball [0,1]^2, then square
    indices satisfy the unit bound. -/
lemma squares_unit_from_pointSet_bounded
    {n : ℕ} {s C : ℝ} {M : ℕ} {config : NiceConfiguration n s C M}
    (h : config.pointSet ⊆ {p : EuclideanPlane | p 0 ∈ Set.Icc (0 : ℝ) 1 ∧ p 1 ∈ Set.Icc (0 : ℝ) 1}) :
    ∀ p ∈ config.P₀, 0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧
      0 ≤ p.j ∧ p.j < (2 ^ n : ℤ) := by
  intro p hp
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  -- Use midpoint of the square to get strict index bounds
  let x : EuclideanPlane := WithLp.toLp (2 : ENNReal) fun i : Fin 2 =>
    if i = 0 then ((p.i : ℝ) + 1 / 2) * dyadicDelta n
    else ((p.j : ℝ) + 1 / 2) * dyadicDelta n
  have hx0 : x 0 = ((p.i : ℝ) + 1 / 2) * dyadicDelta n := by
    simp [x] <;> norm_num
  have hx1 : x 1 = ((p.j : ℝ) + 1 / 2) * dyadicDelta n := by
    simp [x] <;> norm_num
  have hx : x ∈ p.toSet := by
    simp only [DyadicSquare.toSet, Set.mem_setOf_eq]
    rw [hx0, hx1]
    exact ⟨by linarith [hδ_pos], by linarith [hδ_pos], by linarith [hδ_pos], by linarith [hδ_pos]⟩
  have h1 : p.toSet ⊆ config.pointSet := by
    intro y hy
    simp only [NiceConfiguration.pointSet, Set.mem_iUnion]
    exact ⟨p, hp, hy⟩
  have h2 : x ∈ config.pointSet := h1 hx
  have h3 : x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ x 1 ∈ Set.Icc (0 : ℝ) 1 := h h2
  have h4 : 0 ≤ x 0 := h3.1.1
  have h5 : x 0 ≤ 1 := h3.1.2
  have h6 : 0 ≤ x 1 := h3.2.1
  have h7 : x 1 ≤ 1 := h3.2.2
  have hδ_eq : dyadicDelta n = 1 / (2 ^ n : ℝ) := by
    simp [dyadicDelta] <;> field_simp <;> ring
  have h12 : 0 ≤ (p.i : ℝ) := by
    have h_nonneg : (p.i : ℝ) + 1 / 2 ≥ 0 := by nlinarith [h4, hx0, hδ_pos]
    by_cases h : 0 ≤ p.i
    · exact_mod_cast h
    · have h' : p.i ≤ -1 := by omega
      have h3 : (p.i : ℝ) ≤ -1 := by exact_mod_cast h'
      linarith
  have h13 : (p.i : ℝ) < (2 ^ n : ℝ) := by
    have h : ((p.i : ℝ) + 1 / 2) * dyadicDelta n ≤ 1 := by linarith [h5, hx0]
    have hδ : dyadicDelta n = 1 / (2 ^ n : ℝ) := hδ_eq
    rw [hδ] at h
    have hpos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
    have h' : (p.i : ℝ) + 1 / 2 ≤ (2 ^ n : ℝ) := by
      calc (p.i : ℝ) + 1 / 2
        = (((p.i : ℝ) + 1 / 2) * (1 / (2 ^ n : ℝ))) * (2 ^ n : ℝ) := by field_simp [hpos.ne'] <;> ring
      _ ≤ (1 : ℝ) * (2 ^ n : ℝ) := by gcongr
      _ = (2 ^ n : ℝ) := by ring
    linarith
  have h15 : 0 ≤ (p.j : ℝ) := by
    have h_nonneg : (p.j : ℝ) + 1 / 2 ≥ 0 := by nlinarith [h6, hx1, hδ_pos]
    by_cases h : 0 ≤ p.j
    · exact_mod_cast h
    · have h' : p.j ≤ -1 := by omega
      have h3 : (p.j : ℝ) ≤ -1 := by exact_mod_cast h'
      linarith
  have h16 : (p.j : ℝ) < (2 ^ n : ℝ) := by
    have h : ((p.j : ℝ) + 1 / 2) * dyadicDelta n ≤ 1 := by linarith [h7, hx1]
    have hδ : dyadicDelta n = 1 / (2 ^ n : ℝ) := hδ_eq
    rw [hδ] at h
    have hpos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
    have h' : (p.j : ℝ) + 1 / 2 ≤ (2 ^ n : ℝ) := by
      calc (p.j : ℝ) + 1 / 2
        = (((p.j : ℝ) + 1 / 2) * (1 / (2 ^ n : ℝ))) * (2 ^ n : ℝ) := by field_simp [hpos.ne'] <;> ring
      _ ≤ (1 : ℝ) * (2 ^ n : ℝ) := by gcongr
      _ = (2 ^ n : ℝ) := by ring
    linarith
  exact ⟨by exact_mod_cast h12, by exact_mod_cast h13,
    by exact_mod_cast h15, by exact_mod_cast h16⟩

end M2

/-! ============================================================================
   M5: Point set transfer through B1 bridge

   Connects fine configuration point sets to the original point set
   intersected with a coarse square, under the homothety.
   ============================================================================ -/

namespace M5

open DiscretisedFurstenbergEstimate.InductionConfigurations

/-- Geometric correspondence: the homothety mapping a coarse square Q to
    [0,1)^2 maps a fine square p to the square squareHomothety Q p. -/
lemma squareHomothety_toSet
    {n m : ℕ} (hnm : m ≤ n) (Q : DyadicSquare m) (p : DyadicSquare n) :
    homothetyS (dyadicDelta m) Q.i Q.j '' p.toSet =
      (squareHomothety hnm Q p).toSet := by
  set k : ℕ := 2 ^ (n - m) with hk_def
  set p' : DyadicSquare (n - m) := squareHomothety hnm Q p with hp'_def
  have hδm_pos : 0 < dyadicDelta m := dyadicDelta_pos m
  have h_pow : (2 ^ (n - m) : ℝ) * (2 ^ m : ℝ) = (2 ^ n : ℝ) := by
    have h : n - m + m = n := by omega
    rw [← pow_add] <;> rw [h]
  have h_k1 : (k : ℝ) = (2 ^ (n - m) : ℝ) := by
    simp [hk_def] <;> norm_cast
  have h_dn : dyadicDelta n = 1 / (2 ^ n : ℝ) := by
    simp [dyadicDelta] <;> field_simp <;> ring
  have h_dm : dyadicDelta m = 1 / (2 ^ m : ℝ) := by
    simp [dyadicDelta] <;> field_simp <;> ring
  have h_dnm : dyadicDelta (n - m) = 1 / (2 ^ (n - m) : ℝ) := by
    simp [dyadicDelta] <;> field_simp <;> ring
  have h_ratio1 : (k : ℝ) * dyadicDelta n = dyadicDelta m := by
    calc (k : ℝ) * dyadicDelta n
      = (2 ^ (n - m) : ℝ) * (1 / (2 ^ n : ℝ)) := by rw [h_k1, h_dn]
    _ = 1 / (2 ^ m : ℝ) := by
      have h2 : (2 ^ n : ℝ) = (2 ^ (n - m) : ℝ) * (2 ^ m : ℝ) := h_pow.symm
      rw [h2]
      have h3 : (2 ^ (n - m) : ℝ) ≠ 0 := by positivity
      have h4 : (2 ^ m : ℝ) ≠ 0 := by positivity
      field_simp [h3, h4] <;> ring
    _ = dyadicDelta m := by rw [h_dm]
  have h_ratio2 : dyadicDelta (n - m) * dyadicDelta m = dyadicDelta n := by
    calc dyadicDelta (n - m) * dyadicDelta m
      = (1 / (2 ^ (n - m) : ℝ)) * (1 / (2 ^ m : ℝ)) := by rw [h_dnm, h_dm]
    _ = 1 / ((2 ^ (n - m) : ℝ) * (2 ^ m : ℝ)) := by
      have h3 : (2 ^ (n - m) : ℝ) ≠ 0 := by positivity
      have h4 : (2 ^ m : ℝ) ≠ 0 := by positivity
      field_simp [h3, h4] <;> ring
    _ = 1 / (2 ^ n : ℝ) := by rw [h_pow]
    _ = dyadicDelta n := by rw [h_dn]
  have hpi : (p'.i : ℝ) = (p.i : ℝ) - (Q.i : ℝ) * (k : ℝ) := by
    have h1 : p'.i = p.i - Q.i * (k : ℤ) := by
      simp [hp'_def, squareHomothety, refinementFactor, hk_def] <;> norm_cast
    exact_mod_cast h1
  have hpj : (p'.j : ℝ) = (p.j : ℝ) - (Q.j : ℝ) * (k : ℝ) := by
    have h1 : p'.j = p.j - Q.j * (k : ℤ) := by
      simp [hp'_def, squareHomothety, refinementFactor, hk_def] <;> norm_cast
    exact_mod_cast h1
  have h_expand_i_n : (p'.i : ℝ) * dyadicDelta n =
      (p.i : ℝ) * dyadicDelta n - (Q.i : ℝ) * dyadicDelta m := by
    calc (p'.i : ℝ) * dyadicDelta n
      = ((p.i : ℝ) - (Q.i : ℝ) * (k : ℝ)) * dyadicDelta n := by rw [hpi]
    _ = (p.i : ℝ) * dyadicDelta n - (Q.i : ℝ) * ((k : ℝ) * dyadicDelta n) := by ring
    _ = (p.i : ℝ) * dyadicDelta n - (Q.i : ℝ) * dyadicDelta m := by rw [h_ratio1] <;> ring
  have h_expand_i1_n : ((p'.i : ℝ) + 1) * dyadicDelta n =
      ((p.i : ℝ) + 1) * dyadicDelta n - (Q.i : ℝ) * dyadicDelta m := by
    calc ((p'.i : ℝ) + 1) * dyadicDelta n
      = (p'.i : ℝ) * dyadicDelta n + dyadicDelta n := by ring
    _ = (p.i : ℝ) * dyadicDelta n - (Q.i : ℝ) * dyadicDelta m + dyadicDelta n := by rw [h_expand_i_n]
    _ = ((p.i : ℝ) + 1) * dyadicDelta n - (Q.i : ℝ) * dyadicDelta m := by ring
  have h_expand_j_n : (p'.j : ℝ) * dyadicDelta n =
      (p.j : ℝ) * dyadicDelta n - (Q.j : ℝ) * dyadicDelta m := by
    calc (p'.j : ℝ) * dyadicDelta n
      = ((p.j : ℝ) - (Q.j : ℝ) * (k : ℝ)) * dyadicDelta n := by rw [hpj]
    _ = (p.j : ℝ) * dyadicDelta n - (Q.j : ℝ) * ((k : ℝ) * dyadicDelta n) := by ring
    _ = (p.j : ℝ) * dyadicDelta n - (Q.j : ℝ) * dyadicDelta m := by rw [h_ratio1] <;> ring
  have h_expand_j1_n : ((p'.j : ℝ) + 1) * dyadicDelta n =
      ((p.j : ℝ) + 1) * dyadicDelta n - (Q.j : ℝ) * dyadicDelta m := by
    calc ((p'.j : ℝ) + 1) * dyadicDelta n
      = (p'.j : ℝ) * dyadicDelta n + dyadicDelta n := by ring
    _ = (p.j : ℝ) * dyadicDelta n - (Q.j : ℝ) * dyadicDelta m + dyadicDelta n := by rw [h_expand_j_n]
    _ = ((p.j : ℝ) + 1) * dyadicDelta n - (Q.j : ℝ) * dyadicDelta m := by ring
  -- Homothety coordinate formulas
  have h_hom0 : ∀ (x : EuclideanPlane),
      (homothetyS (dyadicDelta m) Q.i Q.j x) 0 = (x 0 - (Q.i : ℝ) * dyadicDelta m) / dyadicDelta m := by
    intro x
    simp [homothetyS] <;> field_simp [hδm_pos.ne'] <;> ring
  have h_hom1 : ∀ (x : EuclideanPlane),
      (homothetyS (dyadicDelta m) Q.i Q.j x) 1 = (x 1 - (Q.j : ℝ) * dyadicDelta m) / dyadicDelta m := by
    intro x
    simp [homothetyS] <;> field_simp [hδm_pos.ne'] <;> ring
  apply Set.ext
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [DyadicSquare.toSet, Set.mem_setOf_eq, hp'_def]
    rw [h_hom0 x, h_hom1 x]
    have h_pos : 0 < dyadicDelta m := hδm_pos
    have h_i1 : (p'.i : ℝ) * dyadicDelta (n - m) ≤ (x 0 - (Q.i : ℝ) * dyadicDelta m) / dyadicDelta m := by
      have h : (p'.i : ℝ) * dyadicDelta n ≤ x 0 - (Q.i : ℝ) * dyadicDelta m := by
        rw [h_expand_i_n] <;> linarith [hx.1]
      have h' : (p'.i : ℝ) * dyadicDelta (n - m) * dyadicDelta m = (p'.i : ℝ) * dyadicDelta n := by
        rw [←h_ratio2] <;> ring
      calc (p'.i : ℝ) * dyadicDelta (n - m)
        = ((p'.i : ℝ) * dyadicDelta (n - m) * dyadicDelta m) / dyadicDelta m := by field_simp [h_pos.ne'] <;> ring
      _ = ((p'.i : ℝ) * dyadicDelta n) / dyadicDelta m := by rw [h']
      _ ≤ ((x 0 - (Q.i : ℝ) * dyadicDelta m) / dyadicDelta m) := by gcongr
    have h_i2 : (x 0 - (Q.i : ℝ) * dyadicDelta m) / dyadicDelta m < ((p'.i : ℝ) + 1) * dyadicDelta (n - m) := by
      have h : x 0 - (Q.i : ℝ) * dyadicDelta m < ((p'.i : ℝ) + 1) * dyadicDelta n := by
        rw [h_expand_i1_n] <;> linarith [hx.2.1]
      have h' : ((p'.i : ℝ) + 1) * dyadicDelta (n - m) * dyadicDelta m = ((p'.i : ℝ) + 1) * dyadicDelta n := by
        rw [←h_ratio2] <;> ring
      calc (x 0 - (Q.i : ℝ) * dyadicDelta m) / dyadicDelta m
        < (((p'.i : ℝ) + 1) * dyadicDelta n) / dyadicDelta m := by gcongr
      _ = (((p'.i : ℝ) + 1) * dyadicDelta (n - m)) := by
        rw [←h'] <;> field_simp [h_pos.ne'] <;> ring
    have h_j1 : (p'.j : ℝ) * dyadicDelta (n - m) ≤ (x 1 - (Q.j : ℝ) * dyadicDelta m) / dyadicDelta m := by
      have h : (p'.j : ℝ) * dyadicDelta n ≤ x 1 - (Q.j : ℝ) * dyadicDelta m := by
        rw [h_expand_j_n] <;> linarith [hx.2.2.1]
      have h' : (p'.j : ℝ) * dyadicDelta (n - m) * dyadicDelta m = (p'.j : ℝ) * dyadicDelta n := by
        rw [←h_ratio2] <;> ring
      calc (p'.j : ℝ) * dyadicDelta (n - m)
        = ((p'.j : ℝ) * dyadicDelta (n - m) * dyadicDelta m) / dyadicDelta m := by field_simp [h_pos.ne'] <;> ring
      _ = ((p'.j : ℝ) * dyadicDelta n) / dyadicDelta m := by rw [h']
      _ ≤ ((x 1 - (Q.j : ℝ) * dyadicDelta m) / dyadicDelta m) := by gcongr
    have h_j2 : (x 1 - (Q.j : ℝ) * dyadicDelta m) / dyadicDelta m < ((p'.j : ℝ) + 1) * dyadicDelta (n - m) := by
      have h : x 1 - (Q.j : ℝ) * dyadicDelta m < ((p'.j : ℝ) + 1) * dyadicDelta n := by
        rw [h_expand_j1_n] <;> linarith [hx.2.2.2]
      have h' : ((p'.j : ℝ) + 1) * dyadicDelta (n - m) * dyadicDelta m = ((p'.j : ℝ) + 1) * dyadicDelta n := by
        rw [←h_ratio2] <;> ring
      calc (x 1 - (Q.j : ℝ) * dyadicDelta m) / dyadicDelta m
        < (((p'.j : ℝ) + 1) * dyadicDelta n) / dyadicDelta m := by gcongr
      _ = (((p'.j : ℝ) + 1) * dyadicDelta (n - m)) := by
        rw [←h'] <;> field_simp [h_pos.ne'] <;> ring
    exact ⟨h_i1, h_i2, h_j1, h_j2⟩
  · intro hy
    simp only [DyadicSquare.toSet, Set.mem_setOf_eq, hp'_def] at hy
    let x : EuclideanPlane := WithLp.toLp (2 : ENNReal) fun i : Fin 2 =>
      (if i = 0 then (Q.i : ℝ) else (Q.j : ℝ)) * dyadicDelta m + y i * dyadicDelta m
    have hx0 : x 0 = (Q.i : ℝ) * dyadicDelta m + y 0 * dyadicDelta m := by
      simp [x] <;> norm_num <;> ring
    have hx1 : x 1 = (Q.j : ℝ) * dyadicDelta m + y 1 * dyadicDelta m := by
      simp [x] <;> norm_num <;> ring
    have h_pos : 0 < dyadicDelta m := hδm_pos
    refine' ⟨x, _, _⟩
    · simp only [DyadicSquare.toSet, Set.mem_setOf_eq]
      have h_i1 : (p.i : ℝ) * dyadicDelta n ≤ x 0 := by
        have h : (p'.i : ℝ) * dyadicDelta n ≤ y 0 * dyadicDelta m := by
          have h'' : (p'.i : ℝ) * dyadicDelta (n - m) * dyadicDelta m = (p'.i : ℝ) * dyadicDelta n := by
            rw [←h_ratio2] <;> ring
          calc (p'.i : ℝ) * dyadicDelta n
            = (p'.i : ℝ) * dyadicDelta (n - m) * dyadicDelta m := by rw [h'']
          _ ≤ y 0 * dyadicDelta m := by gcongr; exact hy.1
        linarith [h, h_expand_i_n, hx0]
      have h_i2 : x 0 < ((p.i : ℝ) + 1) * dyadicDelta n := by
        have h : y 0 * dyadicDelta m < ((p'.i : ℝ) + 1) * dyadicDelta n := by
          have h'' : ((p'.i : ℝ) + 1) * dyadicDelta (n - m) * dyadicDelta m = ((p'.i : ℝ) + 1) * dyadicDelta n := by
            rw [←h_ratio2] <;> ring
          calc y 0 * dyadicDelta m
            < ((p'.i : ℝ) + 1) * dyadicDelta (n - m) * dyadicDelta m := by gcongr; exact hy.2.1
          _ = ((p'.i : ℝ) + 1) * dyadicDelta n := by rw [h'']
        linarith [h, h_expand_i1_n, hx0]
      have h_j1 : (p.j : ℝ) * dyadicDelta n ≤ x 1 := by
        have h : (p'.j : ℝ) * dyadicDelta n ≤ y 1 * dyadicDelta m := by
          have h'' : (p'.j : ℝ) * dyadicDelta (n - m) * dyadicDelta m = (p'.j : ℝ) * dyadicDelta n := by
            rw [←h_ratio2] <;> ring
          calc (p'.j : ℝ) * dyadicDelta n
            = (p'.j : ℝ) * dyadicDelta (n - m) * dyadicDelta m := by rw [h'']
          _ ≤ y 1 * dyadicDelta m := by gcongr; exact hy.2.2.1
        linarith [h, h_expand_j_n, hx1]
      have h_j2 : x 1 < ((p.j : ℝ) + 1) * dyadicDelta n := by
        have h : y 1 * dyadicDelta m < ((p'.j : ℝ) + 1) * dyadicDelta n := by
          have h'' : ((p'.j : ℝ) + 1) * dyadicDelta (n - m) * dyadicDelta m = ((p'.j : ℝ) + 1) * dyadicDelta n := by
            rw [←h_ratio2] <;> ring
          calc y 1 * dyadicDelta m
            < ((p'.j : ℝ) + 1) * dyadicDelta (n - m) * dyadicDelta m := by gcongr; exact hy.2.2.2
          _ = ((p'.j : ℝ) + 1) * dyadicDelta n := by rw [h'']
        linarith [h, h_expand_j1_n, hx1]
      exact ⟨h_i1, h_i2, h_j1, h_j2⟩
    · ext i
      fin_cases i <;> simp [homothetyS, hx0, hx1] <;> field_simp [hδm_pos.ne'] <;> ring

/-- IsSetBetweenScales is invariant under uniform scaling: if P is an
    (s,C)-set between δ and Δ, then a•P is an (s,C)-set between aδ and aΔ.
    The constant C is unchanged because the homothety normalization cancels
    the outer scaling. -/
lemma IsSetBetweenScales.rescale
    {P : Set EuclideanPlane} {δ Δ s C a : ℝ}
    (ha_pos : 0 < a)
    (h : IsSetBetweenScales P δ Δ s C) :
    IsSetBetweenScales ((fun x => a • x) '' P) (a * δ) (a * Δ) s C := by
  rcases h with ⟨hδ_pos, hΔ_pos, hδ_le_Δ, hs_nonneg, hC_pos, hmain⟩
  have haδ_pos : 0 < a * δ := mul_pos ha_pos hδ_pos
  have haΔ_pos : 0 < a * Δ := mul_pos ha_pos hΔ_pos
  have haδ_le_aΔ : a * δ ≤ a * Δ := by gcongr
  refine' ⟨haδ_pos, haΔ_pos, haδ_le_aΔ, hs_nonneg, hC_pos, _⟩
  intro i j hnonempty
  let Q := dyadicSquare (a * Δ) i j
  let Q_orig := dyadicSquare Δ i j
  let f : EuclideanPlane → EuclideanPlane := fun x => a • x
  -- Scaling maps dyadic squares to dyadic squares
  have hQ_eq : f '' Q_orig = Q := by
    ext z
    simp only [Set.mem_image, dyadicSquare, Set.mem_setOf_eq, f]
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      have h11 : (i : ℝ) * Δ ≤ x 0 := hx1.1
      have h12 : x 0 < ((i : ℝ) + 1) * Δ := hx1.2
      have h21 : (j : ℝ) * Δ ≤ x 1 := hx2.1
      have h22 : x 1 < ((j : ℝ) + 1) * Δ := hx2.2
      have h1 : (i : ℝ) * (a * Δ) ≤ a * x 0 := by
        calc (i : ℝ) * (a * Δ) = a * ((i : ℝ) * Δ) := by ring
          _ ≤ a * x 0 := by gcongr
      have h2 : a * x 0 < ((i : ℝ) + 1) * (a * Δ) := by
        calc a * x 0 < a * (((i : ℝ) + 1) * Δ) := by gcongr
          _ = ((i : ℝ) + 1) * (a * Δ) := by ring
      have h3 : (j : ℝ) * (a * Δ) ≤ a * x 1 := by
        calc (j : ℝ) * (a * Δ) = a * ((j : ℝ) * Δ) := by ring
          _ ≤ a * x 1 := by gcongr
      have h4 : a * x 1 < ((j : ℝ) + 1) * (a * Δ) := by
        calc a * x 1 < a * (((j : ℝ) + 1) * Δ) := by gcongr
          _ = ((j : ℝ) + 1) * (a * Δ) := by ring
      exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    · intro hz
      let x : EuclideanPlane := (1 / a) • z
      have hx0 : x 0 = z 0 / a := by simp [x] <;> field_simp [ha_pos.ne'] <;> ring
      have hx1 : x 1 = z 1 / a := by simp [x] <;> field_simp [ha_pos.ne'] <;> ring
      have hz11 : (i : ℝ) * (a * Δ) ≤ z 0 := hz.1.1
      have hz12 : z 0 < ((i : ℝ) + 1) * (a * Δ) := hz.1.2
      have hz21 : (j : ℝ) * (a * Δ) ≤ z 1 := hz.2.1
      have hz22 : z 1 < ((j : ℝ) + 1) * (a * Δ) := hz.2.2
      have h1 : (i : ℝ) * Δ ≤ x 0 := by
        rw [hx0]
        have h : (i : ℝ) * Δ ≤ z 0 / a := by
          calc (i : ℝ) * Δ
            = ((i : ℝ) * (a * Δ)) / a := by field_simp [ha_pos.ne'] <;> ring
          _ ≤ z 0 / a := by gcongr
        exact h
      have h2 : x 0 < ((i : ℝ) + 1) * Δ := by
        rw [hx0]
        have h : z 0 / a < ((i : ℝ) + 1) * Δ := by
          calc z 0 / a
            < (((i : ℝ) + 1) * (a * Δ)) / a := by gcongr
          _ = ((i : ℝ) + 1) * Δ := by field_simp [ha_pos.ne'] <;> ring
        exact h
      have h3 : (j : ℝ) * Δ ≤ x 1 := by
        rw [hx1]
        have h : (j : ℝ) * Δ ≤ z 1 / a := by
          calc (j : ℝ) * Δ
            = ((j : ℝ) * (a * Δ)) / a := by field_simp [ha_pos.ne'] <;> ring
          _ ≤ z 1 / a := by gcongr
        exact h
      have h4 : x 1 < ((j : ℝ) + 1) * Δ := by
        rw [hx1]
        have h : z 1 / a < ((j : ℝ) + 1) * Δ := by
          calc z 1 / a
            < (((j : ℝ) + 1) * (a * Δ)) / a := by gcongr
          _ = ((j : ℝ) + 1) * Δ := by field_simp [ha_pos.ne'] <;> ring
        exact h
      refine' ⟨x, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, _⟩
      ext k; simp [x, smul_smul] <;> field_simp [ha_pos.ne'] <;> ring
  -- Scaling is injective, so image commutes with intersection
  have h_inter_eq : f '' P ∩ Q = f '' (P ∩ Q_orig) := by
    rw [←hQ_eq]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_image, f]
    constructor
    · rintro ⟨⟨x, hxP, rfl⟩, ⟨w, hwQ, h_eq⟩⟩
      have h_wx : w = x := by
        have h : a • w = a • x := h_eq
        have h3 : a • (w - x) = 0 := by
          rw [smul_sub, h] <;> simp
        have h4 : w - x = 0 := by
          simpa [smul_eq_zero, ha_pos.ne'] using h3
        exact sub_eq_zero.mp h4
      rw [h_wx] at hwQ
      exact ⟨x, ⟨hxP, hwQ⟩, rfl⟩
    · rintro ⟨x, ⟨hxP, hxQ⟩, rfl⟩
      exact ⟨⟨x, hxP, rfl⟩, ⟨x, hxQ, rfl⟩⟩
  -- Extract original witness
  rcases hnonempty with ⟨z, ⟨x, hxP, rfl⟩, hzQ⟩
  have hxQ : x ∈ Q_orig := by
    have h1 : a • x ∈ f '' Q_orig := by
      rw [hQ_eq] <;> exact hzQ
    rcases h1 with ⟨w, hwQ, h_eq⟩
    have h_wx : w = x := by
      have h : a • w = a • x := h_eq
      have h3 : a • (w - x) = 0 := by
        rw [smul_sub, h] <;> simp
      have h4 : w - x = 0 := by
        simpa [smul_eq_zero, ha_pos.ne'] using h3
      exact sub_eq_zero.mp h4
    rw [h_wx] at hwQ
    exact hwQ
  have h_orig_nonempty : (P ∩ Q_orig).Nonempty := ⟨x, hxP, hxQ⟩
  -- Key: homothety at scaled scale composed with scaling = homothety at original scale
  have h_homothety_comp : ∀ (v : EuclideanPlane),
      homothetyS (a * Δ) i j (a • v) = homothetyS Δ i j v := by
    intro v
    ext k
    simp [homothetyS, smul_smul, sub_smul]
    <;> split_ifs <;> field_simp [ha_pos.ne'] <;> ring
  -- Image equality
  have h_image_eq : homothetyS (a * Δ) i j '' (f '' P ∩ Q) =
      homothetyS Δ i j '' (P ∩ Q_orig) := by
    rw [h_inter_eq]
    ext w
    simp only [Set.mem_image]
    constructor
    · rintro ⟨u, ⟨v, ⟨hvP, hvQ⟩, rfl⟩, rfl⟩
      exact ⟨v, ⟨hvP, hvQ⟩, (h_homothety_comp v).symm⟩
    · rintro ⟨v, ⟨hvP, hvQ⟩, rfl⟩
      exact ⟨a • v, ⟨v, ⟨hvP, hvQ⟩, rfl⟩, h_homothety_comp v⟩
  -- Scale ratio is unchanged
  have h_scale_eq : (a * δ) / (a * Δ) = δ / Δ := by
    field_simp [ha_pos.ne', hΔ_pos.ne'] <;> ring
  rw [h_image_eq, h_scale_eq]
  exact hmain i j h_orig_nonempty

end M5

end DirecretisedFurstenbergEstimate.FormatConversion
