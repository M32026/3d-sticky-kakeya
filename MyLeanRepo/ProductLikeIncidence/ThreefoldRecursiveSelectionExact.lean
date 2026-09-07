module

/-
# Threefold Recursive Direction Selection (Exact Constants Interface)

One-step recursive direction selection with exact constant retention:
- Retention per step: (c/2) * |F|
- Kaufman bad mass ≤ c/8
- Excluded-neighborhood mass ≤ c/8
- Independent separation radius r

After 3 steps: |E3| ≥ (c/2)^3 * |E|, with 3 directions pairwise separated by ≥ r.

Exponent conversion (δ^rho_sel ≤ c/2, r = δ^rho_sep) happens downstream.

## Whiteprint node
`phase2_threefold_recursive_selection`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.Energy.AverageProjectionEnergy
public import MyLeanRepo.OSWPrelude

@[expose] public section


open MeasureTheory ENNReal Set Bornology Finset Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- Normalized counting measure on finite Y. -/
private lemma normalized_measure_card'
    {Y : Set ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hY_fin : Y.Finite) (hY_nonempty : Y.Nonempty)
    (hν_counting : ∀ y ∈ Y, ν {y} = ENNReal.ofReal (1 / (Y.ncard : ℝ)))
    {S : Set ℝ} (hS_sub : S ⊆ Y) :
    ν S = ENNReal.ofReal ((S.ncard : ℝ) / (Y.ncard : ℝ)) := by
  let Sf : Finset ℝ := (hY_fin.subset hS_sub).toFinset
  have hS_eq : S = (Sf : Set ℝ) := by
    have h : (Sf : Set ℝ) = S := by
      exact Set.Finite.coe_toFinset (hY_fin.subset hS_sub)
    exact h.symm
  have h_sum : ∀ (s : Finset ℝ), ν (s : Set ℝ) = ∑ y ∈ s, ν {y} := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert a s ha ih =>
      have h_disj : Disjoint ({a} : Set ℝ) (s : Set ℝ) := by simp [ha]
      have h_meas : MeasurableSet (s : Set ℝ) := by exact Finset.measurableSet s
      have h_coe : (↑(insert a s) : Set ℝ) = insert a (↑s : Set ℝ) := by
        rw [Finset.coe_insert]
      have h4 : insert a (↑s : Set ℝ) = ({a} : Set ℝ) ∪ (↑s : Set ℝ) := by
        ext x; simp [ha] <;> tauto
      rw [h_coe, h4, MeasureTheory.measure_union h_disj h_meas, ih, Finset.sum_insert ha]
  have h1 : ν S = ∑ y ∈ Sf, ν {y} := by
    rw [hS_eq]; exact h_sum Sf
  rw [h1]
  have h4 : ∑ y ∈ Sf, ν {y} = ∑ y ∈ Sf, ENNReal.ofReal (1 / (Y.ncard : ℝ)) := by
    apply Finset.sum_congr rfl; intro y hy
    have h_y_in_S : y ∈ S := hS_eq.symm ▸ hy
    exact hν_counting y (hS_sub h_y_in_S)
  rw [h4]
  have h5 : ∑ y ∈ Sf, ENNReal.ofReal (1 / (Y.ncard : ℝ)) =
      (Sf.card : ENNReal) * ENNReal.ofReal (1 / (Y.ncard : ℝ)) := by
    rw [Finset.sum_const] <;> ring
  rw [h5]
  have h_nY_pos : 0 < (Y.ncard : ℝ) := by
    have h : 0 < Y.ncard := (Set.ncard_pos (hs := hY_fin)).mpr hY_nonempty
    exact_mod_cast h
  have h_card_S : (Sf.card : ℝ) = (S.ncard : ℝ) := by
    have h : Sf.card = S.ncard := by exact Eq.symm (ncard_eq_toFinset_card S (Finite.subset hY_fin hS_sub))
    exact_mod_cast h
  rw [show (Sf.card : ENNReal) = ENNReal.ofReal (Sf.card : ℝ) from by norm_cast]
  rw [h_card_S]
  have h_pos1 : 0 ≤ (S.ncard : ℝ) := by positivity
  have h_pos2 : 0 ≤ (1 / (Y.ncard : ℝ)) := by positivity
  have h_mul : ENNReal.ofReal (S.ncard : ℝ) * ENNReal.ofReal (1 / (Y.ncard : ℝ)) =
      ENNReal.ofReal ((S.ncard : ℝ) * (1 / (Y.ncard : ℝ))) := by exact Eq.symm (ofReal_mul h_pos1)
  rw [h_mul]
  have h_div : (S.ncard : ℝ) * (1 / (Y.ncard : ℝ)) = (S.ncard : ℝ) / (Y.ncard : ℝ) := by
    field_simp [h_nY_pos.ne'] <;> ring
  rw [h_div]

/-- One-step recursive direction selection with exact constant retention.

Given a nonempty finite F ⊆ E ⊆ Pbar, a popularity fraction c, and a separation
radius r, selects a direction y' ∈ Ybar such that:
- y' has good projection energy (≤ δ^{-q_bad})
- y' is separated by ≥ r from all directions in Ω
- The fiber F' = F ∩ T_y(y') has size ≥ (c/2) * |F|
- The projection of F' has small Nreal bound
-/
lemma recursive_direction_selection_corrected
    {δ κ0 L η c τ C_ν r : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hkappa_pos : 0 < κ0)
    (hc_pos : 0 < c) (hL_pos : 0 < L) (hη_pos : 0 < η)
    (hτ_pos : 0 < τ) (hC_ν_pos : 0 < C_ν)
    (hr_pos : 0 < r)
    (q_bad : ℝ) (hq_bad_pos : 0 < q_bad)
    {Ybar : Set ℝ} {Pbar : Set (EuclideanSpace ℝ (Fin 2))}
    {T_y : ℝ → Set (EuclideanSpace ℝ (Fin 2))}
    (hT_y_sub : ∀ y ∈ Ybar, T_y y ⊆ Pbar)
    (hYbar_fin : Ybar.Finite) (hYbar_nonempty : Ybar.Nonempty)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν_counting : ∀ y ∈ Ybar, ν {y} = ENNReal.ofReal (1 / (Ybar.ncard : ℝ)))
    (hν_supp : ν.support = Ybar)
    (hν_frost : IsDirectionFrostman δ τ C_ν ν)
    (h_multiplicity : ∀ p ∈ Pbar,
      ENat.toENNReal {y ∈ Ybar | p ∈ T_y y}.encard ≥
        ENNReal.ofReal c * ENat.toENNReal Ybar.encard)
    (h_proj_bound : ∀ y ∈ Ybar,
      Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) (T_y y)) ≤
      ENNReal.ofReal (δ ^ (-(L * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal)))
    {μE : Measure (EuclideanSpace ℝ (Fin 2))} [IsProbabilityMeasure μE]
    (hΘ_bad : ν {y : ℝ | robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) μE) >
      ENNReal.ofReal (δ ^ (-q_bad))} ≤ ENNReal.ofReal (c / 8))
    {E : Finset (EuclideanSpace ℝ (Fin 2))}
    (hE_sub : (E : Set _) ⊆ Pbar)
    (hE_nonempty : E.Nonempty)
    {F : Set (EuclideanSpace ℝ (Fin 2))}
    (hF_sub : F ⊆ (E : Set _)) (hF_fin : F.Finite) (hF_nonempty : F.Nonempty)
    {Ω : Set ℝ} (hΩ_card : Ω.encard ≤ 2)
    (h_neighborhoods_small :
      ν (⋃ y ∈ Ω, Metric.ball y r) ≤ ENNReal.ofReal (c / 8)) :
    ∃ (y' : ℝ) (F' : Set (EuclideanSpace ℝ (Fin 2))),
      y' ∈ Ybar ∧
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y' + p 1) μE) ≤
        ENNReal.ofReal (δ ^ (-q_bad)) ∧
      (∀ y ∈ Ω, |y' - y| ≥ r) ∧
      F' ⊆ F ∩ T_y y' ∧
      ENat.toENNReal F'.encard ≥
        ENNReal.ofReal (c / 2) * ENat.toENNReal F.encard ∧
      Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y' + p 1) F') ≤
        ENNReal.ofReal (δ ^ (-(L * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal)) := by
  -- Step 1: Pbar.Nonempty and c ≤ 1
  have hPbar_nonempty : Pbar.Nonempty := by
    rcases hE_nonempty with ⟨p, hp⟩
    exact ⟨p, hE_sub hp⟩
  rcases hPbar_nonempty with ⟨p0, hp0⟩
  have hc_le_one : c ≤ 1 := by
    let S : Set ℝ := {y ∈ Ybar | p0 ∈ T_y y}
    have hS_sub : S ⊆ Ybar := by intro y hy; exact hy.1
    have h1 : ENat.toENNReal S.encard ≥ ENNReal.ofReal c * ENat.toENNReal Ybar.encard :=
      h_multiplicity p0 hp0
    have h21 : S.encard ≤ Ybar.encard := Set.encard_mono hS_sub
    have h2 : ENat.toENNReal S.encard ≤ ENat.toENNReal Ybar.encard :=
      ENat.toENNReal_le.mpr h21
    let r : ENNReal := ENat.toENNReal Ybar.encard
    have h3 : ENNReal.ofReal c * r ≤ r := h1.trans h2
    have h41 : 0 < Ybar.encard := Set.encard_pos.mpr hYbar_nonempty
    have hY_enc : Ybar.encard = ↑Ybar.ncard := by
      have h1 : Ybar.encard = ↑hYbar_fin.toFinset.card := Set.Finite.encard_eq_coe_toFinset_card hYbar_fin
      have h2 : hYbar_fin.toFinset.card = Ybar.ncard := by exact Eq.symm (ncard_eq_toFinset_card Ybar hYbar_fin)
      rw [h1, h2]
    have h_nY_pos : 0 < Ybar.ncard := by
      rcases hYbar_nonempty with ⟨y, hy⟩
      have h1 : ({y} : Set ℝ) ⊆ Ybar := by simp [hy]
      have h2 : ({y} : Set ℝ).ncard ≤ Ybar.ncard := by exact ncard_le_ncard h1 hYbar_fin
      have h3 : ({y} : Set ℝ).ncard = 1 := by simp
      rw [h3] at h2
      omega
    have h_r_ne_zero : r ≠ 0 := by
      have h_eq : r = ENat.toENNReal (↑Ybar.ncard) := by
        simp [r, hY_enc]
      rw [h_eq]
      rw [ENat.toENNReal_coe Ybar.ncard]
      have h_pos : (0 : ENNReal) < (↑Ybar.ncard : ENNReal) := by exact_mod_cast h_nY_pos
      exact h_pos.ne'
    have h_r_ne_top : r ≠ ⊤ := by
      have h_eq : r = ENat.toENNReal (↑Ybar.ncard) := by
        simp [r, hY_enc]
      rw [h_eq]
      rw [ENat.toENNReal_coe Ybar.ncard]
      simp
    have h4 : r * ENNReal.ofReal c ≤ r := by
      have h5 : ENNReal.ofReal c * r ≤ r := h3
      have h6 : ENNReal.ofReal c * r = r * ENNReal.ofReal c := by
        exact mul_comm _ _
      rw [h6] at h5
      exact h5
    have h7 : ENNReal.ofReal c ≤ r⁻¹ * r :=
      (ENNReal.mul_le_iff_le_inv h_r_ne_zero h_r_ne_top).mp h4
    have h8 : r⁻¹ * r = 1 := by exact ENNReal.inv_mul_cancel h_r_ne_zero h_r_ne_top
    rw [h8] at h7
    have h9 : ENNReal.ofReal c ≤ 1 := h7
    exact_mod_cast h9

  let Yf : Finset ℝ := hYbar_fin.toFinset
  let Ff : Finset (EuclideanSpace ℝ (Fin 2)) := hF_fin.toFinset
  let fiber (y : ℝ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
    Ff.filter (fun p => p ∈ T_y y)
  let dirs (p : EuclideanSpace ℝ (Fin 2)) : Finset ℝ :=
    Yf.filter (fun y => p ∈ T_y y)

  have hYf_eq : (Yf : Set ℝ) = Ybar := Set.Finite.coe_toFinset hYbar_fin
  have hFf_eq : (Ff : Set _) = F := Set.Finite.coe_toFinset hF_fin
  have hFf_pos : 0 < Ff.card := by
    rcases hF_nonempty with ⟨x, hx⟩
    have h2 : x ∈ (Ff : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [hFf_eq]; exact hx
    have h3 : Ff.Nonempty := ⟨x, h2⟩
    have h4 : 0 < Ff.card := by exact Nonempty.card_pos h3
    exact h4

  -- Step 2: Double counting
  have h_sum_swap : ∑ p ∈ Ff, (dirs p).card = ∑ y ∈ Yf, (fiber y).card := by
    have h1 : ∀ p, (dirs p).card = ∑ y ∈ Yf, if p ∈ T_y y then 1 else 0 := by
      intro p; rw [Finset.card_filter] <;> rfl
    have h2 : ∀ y, (fiber y).card = ∑ p ∈ Ff, if p ∈ T_y y then 1 else 0 := by
      intro y; rw [Finset.card_filter] <;> rfl
    have h3 : ∑ p ∈ Ff, (dirs p).card = ∑ p ∈ Ff, ∑ y ∈ Yf, (if p ∈ T_y y then 1 else 0) :=
      Finset.sum_congr rfl (fun p _ => h1 p)
    have h4 : ∑ p ∈ Ff, ∑ y ∈ Yf, (if p ∈ T_y y then 1 else 0) =
        ∑ y ∈ Yf, ∑ p ∈ Ff, (if p ∈ T_y y then 1 else 0) := by rw [Finset.sum_comm]
    have h5 : ∑ y ∈ Yf, ∑ p ∈ Ff, (if p ∈ T_y y then 1 else 0) = ∑ y ∈ Yf, (fiber y).card :=
      Finset.sum_congr rfl (fun y _ => (h2 y).symm)
    rw [h3, h4, h5]

  have hY_enc2 : Ybar.encard = ↑Ybar.ncard := by
    have h1 : Ybar.encard = ↑hYbar_fin.toFinset.card := Set.Finite.encard_eq_coe_toFinset_card hYbar_fin
    have h2 : hYbar_fin.toFinset.card = Ybar.ncard := by exact Eq.symm (ncard_eq_toFinset_card Ybar hYbar_fin)
    rw [h1, h2]
  have h_dirs_lower : ∀ p ∈ Ff, ((dirs p).card : ℝ) ≥ c * (Yf.card : ℝ) := by
    intro p hp
    have hpF : p ∈ F := by
      have h : p ∈ (Ff : Set _) := hp
      rw [hFf_eq] at h; exact h
    have hpE : p ∈ (E : Set _) := hF_sub hpF
    have hpP : p ∈ Pbar := hE_sub hpE
    let S : Set ℝ := {y ∈ Ybar | p ∈ T_y y}
    have hS_eq : (dirs p : Set ℝ) = S := by
      ext y
      simp only [dirs, S, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hyY, hyT⟩
        have hY : y ∈ Ybar := by
          have h : y ∈ (Yf : Set ℝ) := hyY
          rw [hYf_eq] at h; exact h
        exact ⟨hY, hyT⟩
      · rintro ⟨hY, hyT⟩
        have hyY : y ∈ (Yf : Set ℝ) := by
          rw [hYf_eq]; exact hY
        exact ⟨hyY, hyT⟩
    have h1 : ENat.toENNReal S.encard ≥ ENNReal.ofReal c * ENat.toENNReal Ybar.encard :=
      h_multiplicity p hpP
    rw [← hS_eq] at h1
    have h2 : (dirs p : Set ℝ).encard = ↑(dirs p).card := by exact encard_coe_eq_coe_finsetCard (dirs p)
    rw [h2, hY_enc2] at h1
    have h4 : (Ybar.ncard : ℝ) = (Yf.card : ℝ) := by
      have h7 : (Yf : Set ℝ).ncard = Yf.card := by simp
      have h8 : Ybar.ncard = (Yf : Set ℝ).ncard := by
        congr; exact hYf_eq.symm
      have h9 : Ybar.ncard = Yf.card := h8.trans h7
      exact_mod_cast h9
    have h6 : (↑(dirs p).card : ENNReal) ≥ ENNReal.ofReal c * (↑Ybar.ncard : ENNReal) := h1
    have h_ncardY : (↑Ybar.ncard : ENNReal) = ENNReal.ofReal (Ybar.ncard : ℝ) := by
      simp [ENat.toENNReal_coe] <;> norm_cast
    rw [h_ncardY] at h6
    have h7 : ENNReal.ofReal c * ENNReal.ofReal (Ybar.ncard : ℝ) = ENNReal.ofReal (c * (Ybar.ncard : ℝ)) :=
      (ENNReal.ofReal_mul (show 0 ≤ c from by positivity)).symm
    rw [h7] at h6
    have h8 : (↑(dirs p).card : ENNReal) = ENNReal.ofReal ((dirs p).card : ℝ) := by
      simp [ENat.toENNReal_coe] <;> norm_cast
    rw [h8] at h6
    have h_iff : ENNReal.ofReal (c * (Ybar.ncard : ℝ)) ≤ ENNReal.ofReal ((dirs p).card : ℝ) ↔
        c * (Ybar.ncard : ℝ) ≤ ((dirs p).card : ℝ) :=
      ENNReal.ofReal_le_ofReal_iff (show 0 ≤ ((dirs p).card : ℝ) from by positivity)
    have h9 : c * (Ybar.ncard : ℝ) ≤ ((dirs p).card : ℝ) := h_iff.mp h6
    rw [h4] at h9
    exact h9

  have h_sum_lower : (∑ p ∈ Ff, ((dirs p).card : ℝ)) ≥
      (Ff.card : ℝ) * c * (Yf.card : ℝ) := by
    calc ∑ p ∈ Ff, ((dirs p).card : ℝ)
      ≥ ∑ p ∈ Ff, (c * (Yf.card : ℝ)) :=
        Finset.sum_le_sum (fun p hp => h_dirs_lower p hp)
    _ = (Ff.card : ℝ) * c * (Yf.card : ℝ) := by
      rw [Finset.sum_const] <;> ring

  -- Step 3: G = {y : |fiber(y)| ≥ (c/2)·|F|} has |G| ≥ (c/2)·|Ybar|
  let Gf : Finset ℝ := Yf.filter (fun y =>
    (fiber y).card ≥ (c / 2 : ℝ) * (Ff.card : ℝ))
  let G : Set ℝ := (Gf : Set ℝ)

  have hGf_card : (Gf.card : ℝ) ≥ (c / 2) * (Yf.card : ℝ) := by
    by_contra h
    have h' : (Gf.card : ℝ) < (c / 2) * (Yf.card : ℝ) := by linarith
    set g : ℝ := (Gf.card : ℝ) with hg
    set n : ℝ := (Yf.card : ℝ) with hn
    set m : ℝ := (Ff.card : ℝ) with hm
    have hGf_sub : Gf ⊆ Yf := Finset.filter_subset _ _
    have h_sum_upper : (∑ y ∈ Yf, ((fiber y).card : ℝ)) < m * c * n := by
      have h1 : ∑ y ∈ Yf, ((fiber y).card : ℝ) =
          ∑ y ∈ Gf, ((fiber y).card : ℝ) + ∑ y ∈ (Yf \ Gf), ((fiber y).card : ℝ) := by
        have h_sum : ∑ y ∈ (Yf \ Gf), ((fiber y).card : ℝ) + ∑ y ∈ Gf, ((fiber y).card : ℝ) =
            ∑ y ∈ Yf, ((fiber y).card : ℝ) := by exact sum_sdiff hGf_sub
        linarith
      rw [h1]
      have h21 : ∀ y ∈ Gf, ((fiber y).card : ℝ) ≤ m := by
        intro y _
        have h_card : (fiber y).card ≤ Ff.card := Finset.card_le_card (Finset.filter_subset _ _)
        exact Nat.cast_le.mpr h_card
      have h2 : ∑ y ∈ Gf, ((fiber y).card : ℝ) ≤ g * m := by
        have h22 : ∑ y ∈ Gf, ((fiber y).card : ℝ) ≤ ∑ y ∈ Gf, m := Finset.sum_le_sum h21
        have h23 : ∑ y ∈ Gf, (m : ℝ) = g * m := by
          rw [Finset.sum_const] <;> simp [hg] <;> ring
        linarith
      have h31 : ∀ y ∈ (Yf \ Gf), ((fiber y).card : ℝ) < (c / 2) * m := by
        intro y hy
        have h4 : y ∈ Yf := (Finset.mem_sdiff.mp hy).1
        have h5 : y ∉ Gf := (Finset.mem_sdiff.mp hy).2
        have h7 : ¬((fiber y).card ≥ (c / 2 : ℝ) * (Ff.card : ℝ)) := by
          simp only [Gf, Finset.mem_filter, h4, true_and] at h5
          exact h5
        simpa [hm] using lt_of_not_ge h7
      have h32 : ∑ y ∈ (Yf \ Gf), ((fiber y).card : ℝ) ≤ ∑ y ∈ (Yf \ Gf), ((c / 2) * m) :=
        Finset.sum_le_sum (fun y hy => le_of_lt (h31 y hy))
      have h33 : ∑ y ∈ (Yf \ Gf), ((c / 2) * m) = ((Yf \ Gf).card : ℝ) * ((c / 2) * m) := by
        rw [Finset.sum_const] <;> ring
      have h34 : ((Yf \ Gf).card : ℝ) = n - g := by
        have h35 : (Yf \ Gf).card = Yf.card - Gf.card := by exact card_sdiff_of_subset hGf_sub
        have hG_le : Gf.card ≤ Yf.card := Finset.card_le_card (Finset.filter_subset _ _)
        have h36 : ((Yf \ Gf).card : ℝ) = (Yf.card : ℝ) - (Gf.card : ℝ) := by
          rw [h35]; rw [Nat.cast_sub hG_le]
        rw [h36, hn, hg] <;> ring
      have h3 : ∑ y ∈ (Yf \ Gf), ((fiber y).card : ℝ) ≤ (n - g) * ((c / 2) * m) := by
        calc _ ≤ ∑ y ∈ (Yf \ Gf), ((c / 2) * m) := h32
             _ = ((Yf \ Gf).card : ℝ) * ((c / 2) * m) := h33
             _ = (n - g) * ((c / 2) * m) := by rw [h34]
      have h4 : g * m + (n - g) * ((c / 2) * m) < m * c * n := by
        have h5 : g < (c / 2) * n := h'
        have h6 : 0 < c := hc_pos
        have h7 : c ≤ 1 := hc_le_one
        have hg_nonneg : 0 ≤ g := by positivity
        have hn_pos : 0 < n := by
          rw [hn]
          have hYf_pos : 0 < Yf.card := by
            have h : (Yf : Set ℝ).Nonempty := by
              rw [hYf_eq]; exact hYbar_nonempty
            exact Finset.card_pos.mpr (by simpa [Finset.coe_nonempty] using h)
          exact Nat.cast_pos.mpr hYf_pos
        have hm_pos : 0 < m := by positivity
        have hg_le_n : g ≤ n := by
          have h : Gf ⊆ Yf := Finset.filter_subset _ _
          have h2 : Gf.card ≤ Yf.card := Finset.card_le_card h
          exact Nat.cast_le.mpr h2
        nlinarith [mul_pos hm_pos h6, mul_nonneg hg_nonneg (show (0 : ℝ) ≤ 1 - c / 2 by linarith)]
      linarith
    have h5 : (∑ y ∈ Yf, ((fiber y).card : ℝ)) =
        (∑ p ∈ Ff, ((dirs p).card : ℝ)) := by
      have h6 : (∑ y ∈ Yf, ((fiber y).card : ℕ)) = (∑ p ∈ Ff, ((dirs p).card : ℕ)) := h_sum_swap.symm
      have h7 : (∑ y ∈ Yf, ((fiber y).card : ℝ)) = ↑(∑ y ∈ Yf, ((fiber y).card : ℕ)) := by
        simp [Nat.cast_sum]
      have h8 : (∑ p ∈ Ff, ((dirs p).card : ℝ)) = ↑(∑ p ∈ Ff, ((dirs p).card : ℕ)) := by
        simp [Nat.cast_sum]
      rw [h7, h8, h6]
    rw [h5] at h_sum_upper
    exact not_le.mpr h_sum_upper h_sum_lower

  -- ν(G) ≥ c/2
  have hG_sub : G ⊆ Ybar := by
    intro x hx
    have h : x ∈ Gf := by simpa [G] using hx
    have h2 : x ∈ Yf := (Finset.mem_filter.mp h).1
    have h3 : x ∈ (Yf : Set ℝ) := h2
    rw [hYf_eq] at h3
    exact h3
  have hν_G : ν G ≥ ENNReal.ofReal (c / 2) := by
    have h_card0 : ν G = ENNReal.ofReal ((G.ncard : ℝ) / (Ybar.ncard : ℝ)) :=
      normalized_measure_card' hYbar_fin hYbar_nonempty hν_counting hG_sub
    have hG_ncard : G.ncard = Gf.card := by simp [G]
    have hY_ncard : Ybar.ncard = Yf.card := by
      have h : (Yf : Set ℝ) = Ybar := hYf_eq
      have h2 : (Yf : Set ℝ).ncard = Ybar.ncard := by
        congr
      have h3 : (Yf : Set ℝ).ncard = Yf.card := by simp
      linarith
    have h_card : ν G = ENNReal.ofReal ((Gf.card : ℝ) / (Yf.card : ℝ)) := by
      rw [h_card0]; congr 1 <;> norm_cast <;> simp [hG_ncard, hY_ncard] <;> ring
    rw [h_card]
    have h_nY_pos : 0 < (Yf.card : ℝ) := by
      have h : 0 < Ybar.ncard := by exact Nonempty.ncard_pos hYbar_fin hYbar_nonempty
      have h2 : Ybar.ncard = Yf.card := hY_ncard
      rw [h2] at h; exact_mod_cast h
    have h_ineq : (Gf.card : ℝ) / (Yf.card : ℝ) ≥ c / 2 := by
      calc (Gf.card : ℝ) / (Yf.card : ℝ)
        ≥ ((c / 2) * (Yf.card : ℝ)) / (Yf.card : ℝ) := by gcongr
      _ = c / 2 := by field_simp [h_nY_pos.ne'] <;> ring
    exact ENNReal.ofReal_le_ofReal h_ineq

  let Θ_bad_set : Set ℝ := {y | robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
      (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) μE) >
    ENNReal.ofReal (δ ^ (-q_bad))}
  let Θ_Ω : Set ℝ := ⋃ y ∈ Ω, Metric.ball y r

  -- ν(Θ_bad ∪ Θ_Ω) < c/2  (since each ≤ c/8, sum ≤ c/4 < c/2)
  have h_bad_union : ν (Θ_bad_set ∪ Θ_Ω) < ENNReal.ofReal (c / 2) := by
    have h1 : ν (Θ_bad_set ∪ Θ_Ω) ≤ ν Θ_bad_set + ν Θ_Ω := MeasureTheory.measure_union_le _ _
    have h4 : ν (Θ_bad_set ∪ Θ_Ω) ≤ ENNReal.ofReal (c / 8) + ENNReal.ofReal (c / 8) := by
      calc ν (Θ_bad_set ∪ Θ_Ω) ≤ ν Θ_bad_set + ν Θ_Ω := h1
        _ ≤ ENNReal.ofReal (c / 8) + ENNReal.ofReal (c / 8) := by gcongr
    have h5 : ENNReal.ofReal (c / 8) + ENNReal.ofReal (c / 8) =
        ENNReal.ofReal (c / 4) := by
      have h51 : 0 ≤ c / 8 := by positivity
      rw [← ENNReal.ofReal_add h51 h51]
      <;> ring_nf
    rw [h5] at h4
    have h6 : c / 4 < c / 2 := by linarith
    have h7 : ENNReal.ofReal (c / 4) < ENNReal.ofReal (c / 2) := by
      exact (ENNReal.ofReal_lt_ofReal_iff (show 0 < c / 2 from by positivity)).mpr h6
    exact h4.trans_lt h7

  -- G \ (Θ_bad ∪ Θ_Ω) is nonempty
  have hG_diff_pos : ν (G \ (Θ_bad_set ∪ Θ_Ω)) > 0 := by
    have h2 : G = (G \ (Θ_bad_set ∪ Θ_Ω)) ∪ (G ∩ (Θ_bad_set ∪ Θ_Ω)) := by
      ext x; simp [Set.mem_sdiff, Set.mem_inter_iff] <;> tauto
    have h_disj : Disjoint (G \ (Θ_bad_set ∪ Θ_Ω)) (G ∩ (Θ_bad_set ∪ Θ_Ω)) := by
      simp [Set.disjoint_left, Set.mem_sdiff] <;> tauto
    have h3 : ν G = ν (G \ (Θ_bad_set ∪ Θ_Ω)) + ν (G ∩ (Θ_bad_set ∪ Θ_Ω)) := by
      have hG_fin : G.Finite := by exact finite_toSet Gf
      have h1_sub : (G \ (Θ_bad_set ∪ Θ_Ω)) ⊆ G := by simp
      have h2_sub : (G ∩ (Θ_bad_set ∪ Θ_Ω)) ⊆ G := by simp
      have h1_fin : (G \ (Θ_bad_set ∪ Θ_Ω)).Finite := by exact Finite.sdiff hG_fin
      have h2_fin : (G ∩ (Θ_bad_set ∪ Θ_Ω)).Finite := by exact Finite.inter_of_left hG_fin (Θ_bad_set ∪ Θ_Ω)
      have h_meas1 : MeasurableSet (G \ (Θ_bad_set ∪ Θ_Ω)) := h1_fin.measurableSet
      have h_meas2 : MeasurableSet (G ∩ (Θ_bad_set ∪ Θ_Ω)) := h2_fin.measurableSet
      have h_meas_union : ν ((G \ (Θ_bad_set ∪ Θ_Ω)) ∪ (G ∩ (Θ_bad_set ∪ Θ_Ω))) =
          ν (G \ (Θ_bad_set ∪ Θ_Ω)) + ν (G ∩ (Θ_bad_set ∪ Θ_Ω)) :=
        MeasureTheory.measure_union h_disj h_meas2
      have h9 : ν G = ν ((G \ (Θ_bad_set ∪ Θ_Ω)) ∪ (G ∩ (Θ_bad_set ∪ Θ_Ω))) := by
        exact congr_arg ν h2
      exact Eq.trans h9 h_meas_union
    have h4 : ν (G ∩ (Θ_bad_set ∪ Θ_Ω)) ≤ ν (Θ_bad_set ∪ Θ_Ω) := by
      apply measure_mono; exact Set.inter_subset_right
    by_contra h5
    have h6 : ν (G \ (Θ_bad_set ∪ Θ_Ω)) = 0 := by simpa [not_lt] using h5
    rw [h6] at h3
    have h7 : ν G ≤ ν (Θ_bad_set ∪ Θ_Ω) := by
      rw [h3, zero_add] <;> exact h4
    have h8 : ENNReal.ofReal (c / 2) ≤ ν G := hν_G
    have h9 : ν G < ENNReal.ofReal (c / 2) := h7.trans_lt h_bad_union
    exact not_le.mpr h9 h8

  have hG_diff_nonempty : (G \ (Θ_bad_set ∪ Θ_Ω)).Nonempty := by
    by_contra h
    have h10 : G \ (Θ_bad_set ∪ Θ_Ω) = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have h11 : ν (G \ (Θ_bad_set ∪ Θ_Ω)) = 0 := by rw [h10]; simp
    rw [h11] at hG_diff_pos; simpa using hG_diff_pos

  rcases hG_diff_nonempty with ⟨y', hy'⟩
  have hy'_G : y' ∈ G := by
    have h' : y' ∈ G ∧ y' ∉ (Θ_bad_set ∪ Θ_Ω) := by simpa [Set.mem_sdiff] using hy'
    exact h'.1
  have hy'_not_union : y' ∉ (Θ_bad_set ∪ Θ_Ω) := by
    have h' : y' ∈ G ∧ y' ∉ (Θ_bad_set ∪ Θ_Ω) := by simpa [Set.mem_sdiff] using hy'
    exact h'.2
  have hy'_Ybar : y' ∈ Ybar := hG_sub hy'_G
  have hy'_Gf : y' ∈ Gf := by simpa [G] using hy'_G
  have h_fiber_large : (fiber y').card ≥ (c / 2 : ℝ) * (Ff.card : ℝ) :=
    (Finset.mem_filter.mp hy'_Gf).2

  -- y' not in Θ_bad
  have hy'_not_bad : y' ∉ Θ_bad_set := by
    intro h; exact hy'_not_union (Or.inl h)
  have hy'_not_Ω : y' ∉ Θ_Ω := by
    intro h; exact hy'_not_union (Or.inr h)
  have h_energy : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
      (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y' + p 1) μE) ≤
      ENNReal.ofReal (δ ^ (-q_bad)) := by
    have h10 : ¬(robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y' + p 1) μE) >
        ENNReal.ofReal (δ ^ (-q_bad))) := hy'_not_bad
    exact le_of_not_gt h10

  -- y' not in Θ_Ω → separated from all y ∈ Ω
  have h_sep : ∀ y ∈ Ω, |y' - y| ≥ r := by
    intro y hy
    by_contra h
    have h10 : |y' - y| < r := by linarith
    have h11 : y' ∈ Metric.ball y r := by
      simpa [Metric.mem_ball, Real.dist_eq] using h10
    have h12 : y' ∈ Θ_Ω := Set.mem_iUnion₂.mpr ⟨y, hy, h11⟩
    exact hy'_not_Ω h12

  -- Define F' = fiber y'
  let F' : Set (EuclideanSpace ℝ (Fin 2)) := (fiber y' : Set _)
  have hF'_sub1 : F' ⊆ F := by
    intro x hx
    have h1 : x ∈ Ff := (Finset.mem_filter.mp hx).1
    have h2 : x ∈ (Ff : Set _) := h1
    rw [hFf_eq] at h2; exact h2
  have hF'_sub2 : F' ⊆ T_y y' := by
    intro x hx
    have h : x ∈ T_y y' := (Finset.mem_filter.mp hx).2
    exact h
  have hF'_sub : F' ⊆ F ∩ T_y y' := by
    intro x hx
    exact ⟨hF'_sub1 hx, hF'_sub2 hx⟩

  have hF'_card : ENat.toENNReal F'.encard ≥
      ENNReal.ofReal (c / 2) * ENat.toENNReal F.encard := by
    have h1 : ENat.toENNReal F'.encard = ENNReal.ofReal ((fiber y').card : ℝ) := by
      have h2 : F'.Finite := Set.Finite.subset hF_fin hF'_sub1
      have h3 : F'.encard = ↑(fiber y').card := by
        have h4 : F' = (fiber y' : Set _) := rfl
        rw [h4]; simp
      rw [h3] <;> norm_cast
    rw [h1]
    have h4 : (fiber y').card ≥ (c / 2 : ℝ) * (Ff.card : ℝ) := h_fiber_large
    have h8 : ENat.toENNReal F.encard = ENNReal.ofReal (Ff.card : ℝ) := by
      have h9 : F.encard = ↑Ff.card := by
        have h10 : F.encard = ↑F.ncard := by
          exact Set.Finite.encard_eq_coe hF_fin
        have h11 : F.ncard = Ff.card := by
          have h12 : (Ff : Set _) = F := hFf_eq
          simpa using congr_arg Set.ncard h12.symm
        rw [h10, h11]
      have h13 : ENat.toENNReal F.encard = ENat.toENNReal (↑Ff.card) := by rw [h9]
      rw [h13]
      have h14 : ENat.toENNReal (↑Ff.card) = (↑Ff.card : ENNReal) := by
        exact ENat.toENNReal_coe Ff.card
      rw [h14]
      have h15 : (↑Ff.card : ENNReal) = ENNReal.ofReal (Ff.card : ℝ) := by simp
      exact h15
    rw [h8]
    have h10 : ENNReal.ofReal ((fiber y').card : ℝ) ≥
        ENNReal.ofReal ((c / 2) * (Ff.card : ℝ)) := by gcongr <;> linarith
    have h11 : ENNReal.ofReal ((c / 2) * (Ff.card : ℝ)) =
        ENNReal.ofReal (c / 2) * ENNReal.ofReal (Ff.card : ℝ) := by
      rw [← ENNReal.ofReal_mul] <;> positivity
    rw [h11] at h10
    exact h10

  -- Projection bound for F'
  have h_proj : Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y' + p 1) F') ≤
      ENNReal.ofReal (δ ^ (-(L * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal)) := by
    have h1 : Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y' + p 1) F' ⊆
        Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y' + p 1) (T_y y') := by
      have h10 : F' ⊆ T_y y' := hF'_sub2
      exact Set.image_mono h10
    have hN_mono : ∀ {A B : Set ℝ}, A ⊆ B → Nreal δ A ≤ Nreal δ B := by
      intro A B h
      have h1 : realLineCopy A ⊆ realLineCopy B := by
        intro x hx; simpa [realLineCopy] using h hx
      have h2 : dyadicCubesMeeting δ (realLineCopy A) ⊆ dyadicCubesMeeting δ (realLineCopy B) := by
        intro Q hQ
        have hQ' : Q ∈ dyadicCubes 1 δ ∧ (Q ∩ realLineCopy A).Nonempty := by
          simpa [dyadicCubesMeeting] using hQ
        have h3 : Q ∈ dyadicCubes 1 δ := hQ'.1
        have h4 : (Q ∩ realLineCopy A).Nonempty := hQ'.2
        have h5 : (Q ∩ realLineCopy B).Nonempty := h4.mono (Set.inter_subset_inter_right _ h1)
        exact ⟨h3, h5⟩
      have h3 : (dyadicCubesMeeting δ (realLineCopy A)).encard ≤ (dyadicCubesMeeting δ (realLineCopy B)).encard :=
        Set.encard_mono h2
      exact ENat.toENNReal_mono h3
    have h_main : Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y' + p 1) F') ≤
        Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y' + p 1) (T_y y')) := hN_mono h1
    exact h_main.trans (h_proj_bound y' hy'_Ybar)

  exact ⟨y', F', hy'_Ybar, h_energy, h_sep, hF'_sub, hF'_card, h_proj⟩

/-- Transfer small projection bound from T_y y to any subset S ⊆ T_y y. -/
lemma projection_bound_transfer
    {δ L η : ℝ} {Pbar : Set (EuclideanSpace ℝ (Fin 2))}
    {T_y : ℝ → Set (EuclideanSpace ℝ (Fin 2))}
    {y : ℝ} {S : Set (EuclideanSpace ℝ (Fin 2))}
    (h_proj_bound_y : Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) (T_y y)) ≤
      ENNReal.ofReal (δ ^ (-(L * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal)))
    (hS_sub : S ⊆ T_y y) :
    Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) S) ≤
      ENNReal.ofReal (δ ^ (-(L * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal)) := by
  let π_y : EuclideanSpace ℝ (Fin 2) → ℝ := fun p => p 0 * y + p 1
  have h1 : Set.image π_y S ⊆ Set.image π_y (T_y y) := by
    intro z hz
    simp only [Set.mem_image] at hz
    rcases hz with ⟨x, hx, rfl⟩
    exact Set.mem_image_of_mem π_y (hS_sub hx)
  have hN_mono : ∀ {A B : Set ℝ}, A ⊆ B → Nreal δ A ≤ Nreal δ B := by
    intro A B hAB
    simp only [Nreal]
    exact ENat.toENNReal_mono (dyadicCoveringNumber_mono (show realLineCopy A ⊆ realLineCopy B from by
      intro x hx
      have h2 : x 0 ∈ A := by simpa [realLineCopy] using hx
      have h3 : x 0 ∈ B := hAB h2
      simpa [realLineCopy] using h3))
  exact hN_mono h1 |>.trans h_proj_bound_y

/-- Given three distinct reals, return them in strictly increasing order. -/
lemma sort_three_reals (x y z : ℝ) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ (a b c : ℝ), ({a, b, c} : Set ℝ) = ({x, y, z} : Set ℝ) ∧ a < b ∧ b < c := by
  by_cases h12 : x < y
  · by_cases h23 : y < z
    · exact ⟨x, y, z, rfl, h12, h23⟩
    · have h32 : z < y := by
        have h_le : z ≤ y := by linarith
        exact lt_of_le_of_ne h_le hyz.symm
      by_cases h13 : x < z
      · exact ⟨x, z, y, by ext w; simp [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto, h13, h32⟩
      · have h31 : z < x := by
          have h_le : z ≤ x := by linarith
          exact lt_of_le_of_ne h_le hxz.symm
        exact ⟨z, x, y, by ext w; simp [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto, h31, h12⟩
  · have h21 : y < x := by
      have h_le : y ≤ x := by linarith
      exact lt_of_le_of_ne h_le hxy.symm
    by_cases h13 : x < z
    · exact ⟨y, x, z, by ext w; simp [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto, h21, h13⟩
    · have h31 : z < x := by
        have h_le : z ≤ x := by linarith
        exact lt_of_le_of_ne h_le hxz.symm
      by_cases h23 : y < z
      · exact ⟨y, z, x, by ext w; simp [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto, h23, h31⟩
      · have h32 : z < y := by
          have h_le : z ≤ y := by linarith
          exact lt_of_le_of_ne h_le hyz.symm
        exact ⟨z, y, x, by ext w; simp [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto, h32, h21⟩

/-- Threefold recursive direction selection with exact constant retention.

After 3 steps: E3 ⊆ E2 ⊆ E1 ⊆ E, with |E1| ≥ (c/2)|E|, |E2| ≥ (c/2)|E1|,
|E3| ≥ (c/2)|E2|, and three directions pairwise separated by ≥ r.
-/
lemma threefold_recursive_selection
    {δ κ0 L η c τ C_ν r : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hkappa_pos : 0 < κ0)
    (hc_pos : 0 < c) (hL_pos : 0 < L) (hη_pos : 0 < η)
    (hτ_pos : 0 < τ) (hC_ν_pos : 0 < C_ν)
    (hr_pos : 0 < r)
    (q_bad : ℝ) (hq_bad_pos : 0 < q_bad)
    {Ybar : Set ℝ} {Pbar : Set (EuclideanSpace ℝ (Fin 2))}
    {T_y : ℝ → Set (EuclideanSpace ℝ (Fin 2))}
    (hT_y_sub : ∀ y ∈ Ybar, T_y y ⊆ Pbar)
    (hYbar_fin : Ybar.Finite) (hYbar_nonempty : Ybar.Nonempty)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν_counting : ∀ y ∈ Ybar, ν {y} = ENNReal.ofReal (1 / (Ybar.ncard : ℝ)))
    (hν_supp : ν.support = Ybar)
    (hν_frost : IsDirectionFrostman δ τ C_ν ν)
    (h_multiplicity : ∀ p ∈ Pbar,
      ENat.toENNReal {y ∈ Ybar | p ∈ T_y y}.encard ≥
        ENNReal.ofReal c * ENat.toENNReal Ybar.encard)
    (h_proj_bound : ∀ y ∈ Ybar,
      Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) (T_y y)) ≤
      ENNReal.ofReal (δ ^ (-(L * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal)))
    {μE : Measure (EuclideanSpace ℝ (Fin 2))}
    [IsProbabilityMeasure μE]
    (hΘ_bad : ν {y : ℝ | robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) μE) >
      ENNReal.ofReal (δ ^ (-q_bad))} ≤ ENNReal.ofReal (c / 8))
    {E : Finset (EuclideanSpace ℝ (Fin 2))}
    (hE_sub : (E : Set _) ⊆ Pbar)
    (hE_nonempty : E.Nonempty)
    -- Neighborhood-mass premise for any Ω of size ≤ 2
    (h_neighborhoods_general : ∀ (Ω : Set ℝ), Ω.encard ≤ 2 →
      ν (⋃ y ∈ Ω, Metric.ball y r) ≤ ENNReal.ofReal (c / 8)) :
    ∃ (θ1 θ2 θ3 : ℝ)
      (E1 E2 E3 : Set (EuclideanSpace ℝ (Fin 2))),
      -- Nesting
      E3 ⊆ E2 ∧ E2 ⊆ E1 ∧ E1 ⊆ (E : Set _) ∧
      -- E3 nonempty
      E3.Nonempty ∧
      -- Mass retention: (c/2) per step
      ENat.toENNReal E1.encard ≥ ENNReal.ofReal (c / 2) * (E.card : ENNReal) ∧
      ENat.toENNReal E2.encard ≥ ENNReal.ofReal (c / 2) * ENat.toENNReal E1.encard ∧
      ENat.toENNReal E3.encard ≥ ENNReal.ofReal (c / 2) * ENat.toENNReal E2.encard ∧
      -- Pairwise separation r
      |θ1 - θ2| ≥ r ∧
      |θ1 - θ3| ≥ r ∧
      |θ2 - θ3| ≥ r ∧
      -- Sorted θ1 < θ3 < θ2
      θ1 < θ3 ∧ θ3 < θ2 ∧
      -- All directions come from Ybar
      θ1 ∈ Ybar ∧ θ2 ∈ Ybar ∧ θ3 ∈ Ybar ∧
      -- All three directions outside Theta_bad (energy bound)
      (∀ y ∈ ({θ1, θ2, θ3} : Set ℝ),
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) μE) ≤
        ENNReal.ofReal (δ ^ (-q_bad))) ∧
      -- All three small projection bounds on E3
      (∀ y ∈ ({θ1, θ2, θ3} : Set ℝ),
        Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) E3) ≤
        ENNReal.ofReal (δ ^ (-(L * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal))) := by
  have hE_encard : ENat.toENNReal (↑E : Set (EuclideanSpace ℝ (Fin 2))).encard = (E.card : ENNReal) := by
    simp

  -- Step 1: select y1, E1 (F = E, Ω = ∅)
  have h_step1 := recursive_direction_selection_corrected
    hδ_pos hδ_lt_one hkappa_pos hc_pos hL_pos hη_pos hτ_pos hC_ν_pos hr_pos
    q_bad hq_bad_pos
    hT_y_sub hYbar_fin hYbar_nonempty hν_counting hν_supp hν_frost h_multiplicity h_proj_bound
    hΘ_bad hE_sub hE_nonempty (F := (E : Set _))
    (by simp) (by exact finite_toSet E) (by exact coe_nonempty.mpr hE_nonempty)
    (Ω := (∅ : Set ℝ)) (by simp) (by simp)
  rcases h_step1 with ⟨y1, E1, hy1_Ybar, hE1_energy, hE1_sep, hE1_sub, hE1_card, hE1_proj⟩

  have hE1_card' : ENat.toENNReal E1.encard ≥ ENNReal.ofReal (c / 2) * (E.card : ENNReal) := by
    rw [hE_encard] at hE1_card; exact hE1_card

  -- E1 nonempty
  have hE1_nonempty : E1.Nonempty := by
    have hEcard_pos : 0 < (E.card : ENNReal) := by
      exact_mod_cast Finset.card_pos.mpr hE_nonempty
    have h_pos : 0 < ENNReal.ofReal (c / 2) * (E.card : ENNReal) := by positivity
    have h : 0 < ENat.toENNReal E1.encard := h_pos.trans_le hE1_card'
    have h4 : E1.encard ≠ 0 := by
      intro h5; rw [h5] at h; simp at h
    have h6 : 0 < E1.encard := bot_lt_iff_ne_bot.mpr h4
    exact Set.encard_pos.mp h6
  have hE1_fin : E1.Finite := by
    have h : E1 ⊆ (E : Set _) := hE1_sub.trans Set.inter_subset_left
    exact Finset.finite_toSet E |>.subset h

  -- Step 2: select y2, E2 (F = E1, Ω = {y1})
  have h_step2 := recursive_direction_selection_corrected
    hδ_pos hδ_lt_one hkappa_pos hc_pos hL_pos hη_pos hτ_pos hC_ν_pos hr_pos
    q_bad hq_bad_pos
    hT_y_sub hYbar_fin hYbar_nonempty hν_counting hν_supp hν_frost h_multiplicity h_proj_bound
    hΘ_bad hE_sub hE_nonempty (F := E1)
    (hE1_sub.trans Set.inter_subset_left) hE1_fin hE1_nonempty
    (Ω := {y1}) (by simp) (h_neighborhoods_general {y1} (by simp))
  rcases h_step2 with ⟨y2, E2, hy2_Ybar, hE2_energy, hE2_sep, hE2_sub, hE2_card, hE2_proj⟩

  -- E2 nonempty
  have hE2_nonempty : E2.Nonempty := by
    have h_pos1 : 0 < ENat.toENNReal E1.encard := by
      have h4 : 0 < E1.encard := Set.encard_pos.mpr hE1_nonempty
      exact_mod_cast h4
    have h_pos2 : 0 < ENNReal.ofReal (c / 2) * ENat.toENNReal E1.encard := by positivity
    have h : 0 < ENat.toENNReal E2.encard := h_pos2.trans_le hE2_card
    have h5 : E2.encard ≠ 0 := by
      intro h6; rw [h6] at h; simp at h
    have h7 : 0 < E2.encard := bot_lt_iff_ne_bot.mpr h5
    exact Set.encard_pos.mp h7
  have hE2_fin : E2.Finite := hE1_fin.subset (hE2_sub.trans Set.inter_subset_left)

  -- Step 3: select y3, E3 (F = E2, Ω = {y1, y2})
  have h_step3 := recursive_direction_selection_corrected
    hδ_pos hδ_lt_one hkappa_pos hc_pos hL_pos hη_pos hτ_pos hC_ν_pos hr_pos
    q_bad hq_bad_pos
    hT_y_sub hYbar_fin hYbar_nonempty hν_counting hν_supp hν_frost h_multiplicity h_proj_bound
    hΘ_bad hE_sub hE_nonempty (F := E2)
      ((hE2_sub.trans Set.inter_subset_left).trans (hE1_sub.trans Set.inter_subset_left))
      hE2_fin hE2_nonempty
    (Ω := {y1, y2}) (by
      by_cases h : y1 = y2
      · simp [h]
      · have h' : ({y1, y2} : Set ℝ).encard = 2 := Set.encard_pair h
        exact h'.le) (h_neighborhoods_general {y1, y2} (by
      by_cases h : y1 = y2
      · simp [h]
      · have h' : ({y1, y2} : Set ℝ).encard = 2 := Set.encard_pair h
        exact h'.le))
  rcases h_step3 with ⟨y3, E3, hy3_Ybar, hE3_energy, hE3_sep, hE3_sub, hE3_card, hE3_proj⟩

  -- Nesting
  have hE3_sub_E2 : E3 ⊆ E2 := hE3_sub.trans Set.inter_subset_left
  have hE2_sub_E1 : E2 ⊆ E1 := hE2_sub.trans Set.inter_subset_left
  have hE1_sub_E : E1 ⊆ (E : Set _) := hE1_sub.trans Set.inter_subset_left

  -- E3 nonempty
  have hE3_nonempty : E3.Nonempty := by
    have hE1_encard_pos : 0 < ENat.toENNReal E1.encard := by
      have h : 0 < E1.encard := Set.encard_pos.mpr hE1_nonempty
      exact_mod_cast h
    have hE2_encard_pos : 0 < ENat.toENNReal E2.encard := by
      have h_pos : 0 < ENNReal.ofReal (c / 2) * ENat.toENNReal E1.encard :=
        ENNReal.mul_pos (by positivity) (ne_of_gt hE1_encard_pos)
      have h : 0 < ENat.toENNReal E2.encard := h_pos.trans_le hE2_card
      exact h
    have h_pos2 : 0 < ENNReal.ofReal (c / 2) * ENat.toENNReal E2.encard :=
      ENNReal.mul_pos (by positivity) (ne_of_gt hE2_encard_pos)
    have h : 0 < ENat.toENNReal E3.encard := h_pos2.trans_le hE3_card
    have h7 : E3.encard ≠ 0 := by
      intro h8; rw [h8] at h; simp at h
    exact Set.encard_pos.mp (bot_lt_iff_ne_bot.mpr h7)

  -- E3 ⊆ T_y(yi) for all i (key for projection bounds)
  have hE3_sub_Ty1 : E3 ⊆ T_y y1 := by
    calc E3 ⊆ E1 := hE3_sub_E2.trans hE2_sub_E1
         _ ⊆ T_y y1 := hE1_sub.trans Set.inter_subset_right
  have hE3_sub_Ty2 : E3 ⊆ T_y y2 := by
    calc E3 ⊆ E2 := hE3_sub_E2
         _ ⊆ T_y y2 := hE2_sub.trans Set.inter_subset_right
  have hE3_sub_Ty3 : E3 ⊆ T_y y3 := hE3_sub.trans Set.inter_subset_right

  -- Projection bounds for E3 at each direction
  have h_proj1 := projection_bound_transfer (h_proj_bound y1 hy1_Ybar) hE3_sub_Ty1
  have h_proj2 := projection_bound_transfer (h_proj_bound y2 hy2_Ybar) hE3_sub_Ty2
  have h_proj3 := projection_bound_transfer (h_proj_bound y3 hy3_Ybar) hE3_sub_Ty3
  have h_proj_all : ∀ y ∈ ({y1, y2, y3} : Set ℝ),
      Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) E3) ≤
        ENNReal.ofReal (δ ^ (-(L * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal)) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with (rfl | rfl | rfl)
    · exact h_proj1
    · exact h_proj2
    · exact h_proj3

  -- Energy bounds for all three
  have h_energy_all : ∀ y ∈ ({y1, y2, y3} : Set ℝ),
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) μE) ≤
      ENNReal.ofReal (δ ^ (-q_bad)) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with (rfl | rfl | rfl)
    · exact hE1_energy
    · exact hE2_energy
    · exact hE3_energy

  -- Separation
  have h_sep12 : |y1 - y2| ≥ r := by
    have h := hE2_sep y1 (by simp)
    rw [abs_sub_comm] at h; exact h
  have h_sep13 : |y1 - y3| ≥ r := by
    have h := hE3_sep y1 (by simp)
    rw [abs_sub_comm] at h; exact h
  have h_sep23 : |y2 - y3| ≥ r := by
    have h := hE3_sep y2 (by simp)
    rw [abs_sub_comm] at h; exact h

  -- Distinctness
  have h_sep_pos : 0 < r := hr_pos
  have h_distinct12 : y1 ≠ y2 := by
    intro h; rw [h] at h_sep12; simp at h_sep12; linarith [h_sep_pos]
  have h_distinct13 : y1 ≠ y3 := by
    intro h; rw [h] at h_sep13; simp at h_sep13; linarith [h_sep_pos]
  have h_distinct23 : y2 ≠ y3 := by
    intro h; rw [h] at h_sep23; simp at h_sep23; linarith [h_sep_pos]

  -- Sort directions: find a < b < c that are a permutation of y1,y2,y3
  have h_sorted := sort_three_reals y1 y2 y3 h_distinct12 h_distinct13 h_distinct23
  rcases h_sorted with ⟨a, b, c, h_abc_set, h_a_lt_b, h_b_lt_c⟩

  -- Transfer bounds to permutation
  have h_proj_perm : ∀ y ∈ ({a, b, c} : Set ℝ),
      Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) E3) ≤
        ENNReal.ofReal (δ ^ (-(L * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal)) := by
    rw [h_abc_set]; exact h_proj_all
  have h_energy_perm : ∀ y ∈ ({a, b, c} : Set ℝ),
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) μE) ≤
      ENNReal.ofReal (δ ^ (-q_bad)) := by
    rw [h_abc_set]; exact h_energy_all
  have h_sep_perm : ∀ (x y : ℝ), x ∈ ({a, b, c} : Set ℝ) → y ∈ ({a, b, c} : Set ℝ) → x ≠ y →
      |x - y| ≥ r := by
    rw [h_abc_set]
    intro x y hx hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with (rfl | rfl | rfl)
    · rcases hy with (rfl | rfl | rfl)
      · exfalso; exact hxy rfl
      · exact h_sep12
      · exact h_sep13
    · rcases hy with (rfl | rfl | rfl)
      · rw [abs_sub_comm]; exact h_sep12
      · exfalso; exact hxy rfl
      · exact h_sep23
    · rcases hy with (rfl | rfl | rfl)
      · rw [abs_sub_comm]; exact h_sep13
      · rw [abs_sub_comm]; exact h_sep23
      · exfalso; exact hxy rfl

  -- Final versions with θ1=a, θ2=c, θ3=b ordering
  have h_acb_set : ({a, c, b} : Set ℝ) = ({a, b, c} : Set ℝ) := by
    ext z; simp [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have h_energy_final : ∀ y ∈ ({a, c, b} : Set ℝ),
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) μE) ≤
      ENNReal.ofReal (δ ^ (-q_bad)) := by
    rw [h_acb_set]; exact h_energy_perm
  have h_proj_final : ∀ y ∈ ({a, c, b} : Set ℝ),
      Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) E3) ≤
      ENNReal.ofReal (δ ^ (-(L * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal)) := by
    rw [h_acb_set]; exact h_proj_perm

  -- Output: θ1=a, θ2=c, θ3=b so θ1 < θ3 < θ2
  have ha_in_Ybar : a ∈ Ybar := by
    have h : a ∈ ({a, b, c} : Set ℝ) := by simp
    rw [h_abc_set] at h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with (rfl | rfl | rfl) <;> tauto
  have hb_in_Ybar : b ∈ Ybar := by
    have h : b ∈ ({a, b, c} : Set ℝ) := by simp
    rw [h_abc_set] at h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with (rfl | rfl | rfl) <;> tauto
  have hc_in_Ybar : c ∈ Ybar := by
    have h : c ∈ ({a, b, c} : Set ℝ) := by simp
    rw [h_abc_set] at h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with (rfl | rfl | rfl) <;> tauto
  exact ⟨a, c, b, E1, E2, E3,
    hE3_sub_E2, hE2_sub_E1, hE1_sub_E, hE3_nonempty,
    hE1_card', hE2_card, hE3_card,
    h_sep_perm a c (by simp) (by simp) (by linarith),
    h_sep_perm a b (by simp) (by simp) (by linarith),
    h_sep_perm c b (by simp) (by simp) (by linarith),
    h_a_lt_b, h_b_lt_c,
    ha_in_Ybar, hc_in_Ybar, hb_in_Ybar,
    h_energy_final, h_proj_final⟩

/-- Neighborhood mass bound from Frostman: union of ≤2 balls of radius r
    has mass ≤ c/8. Generalized to arbitrary separation radius r. -/
lemma neighborhood_mass_from_frostman
    {δ r κ C_ν c : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hr_pos : 0 < r)
    (hκ_pos : 0 < κ) (hC_ν_pos : 0 < C_ν) (hc_pos : 0 < c)
    (hδ_le_r : δ ≤ r)
    (hr_le_one : r ≤ 1)
    (h_small : 2 * C_ν * r ^ κ ≤ c / 8)
    {ν : Measure ℝ} (hν_frost : IsDirectionFrostman δ κ C_ν ν) :
    ∀ (Ω : Set ℝ), Ω.encard ≤ 2 →
      ν (⋃ y ∈ Ω, Metric.ball y r) ≤ ENNReal.ofReal (c / 8) := by
  have h_frost1 : ∀ (a r' : ℝ), δ ≤ r' → r' ≤ 1 →
      ν (Set.Icc (a - r') (a + r')) ≤ ENNReal.ofReal (C_ν * r' ^ κ) :=
    hν_frost.2.2
  have h_ball_sub : ∀ (y : ℝ), Metric.ball y r ⊆ Set.Icc (y - r) (y + r) := by
    intro y x hx
    have h4 : dist x y < r := hx
    have h5 : dist x y = |x - y| := by simp [Real.dist_eq]
    rw [h5] at h4
    have h6 : |x - y| < r := h4
    have h7 : y - r ≤ x := by linarith [abs_lt.mp h6]
    have h8 : x ≤ y + r := by linarith [abs_lt.mp h6]
    exact ⟨h7, h8⟩
  have h_ball_mass : ∀ (y : ℝ), ν (Metric.ball y r) ≤ ENNReal.ofReal (C_ν * r ^ κ) := by
    intro y
    have h7 : ν (Metric.ball y r) ≤ ν (Set.Icc (y - r) (y + r)) :=
      measure_mono (h_ball_sub y)
    have h8 : ν (Set.Icc (y - r) (y + r)) ≤ ENNReal.ofReal (C_ν * r ^ κ) :=
      h_frost1 y r hδ_le_r hr_le_one
    exact h7.trans h8
  intro Ω hΩ_encard
  have hΩ_ne_top : Ω.encard ≠ ⊤ := by
    intro h2
    rw [h2] at hΩ_encard <;> norm_num at hΩ_encard
  have hΩ_fin : Ω.Finite := by exact finite_of_encard_le_coe hΩ_encard
  let Ωf : Finset ℝ := hΩ_fin.toFinset
  have hΩf_eq : (Ωf : Set ℝ) = Ω := Set.Finite.coe_toFinset hΩ_fin
  have hΩf_card : Ωf.card = Ω.ncard := by exact Eq.symm (ncard_eq_toFinset_card Ω hΩ_fin)
  have hΩf_card_le_2 : Ωf.card ≤ 2 := by
    rw [hΩf_card]
    have h4 : (Ω.ncard : ENat) ≤ 2 := by
      have h5 : Ω.encard = ↑Ω.ncard := Set.Finite.encard_eq_coe hΩ_fin
      rw [h5] at hΩ_encard
      exact hΩ_encard
    exact_mod_cast h4
  have h_union : (⋃ y ∈ Ω, Metric.ball y r) = ⋃ y ∈ (Ωf : Set ℝ), Metric.ball y r := by
    rw [hΩf_eq]
  rw [h_union]
  have h9 : ν (⋃ y ∈ (Ωf : Set ℝ), Metric.ball y r) ≤ ∑ y ∈ Ωf, ν (Metric.ball y r) := by
    have h_ind : ∀ (s : Finset ℝ), ν (⋃ y ∈ (s : Set ℝ), Metric.ball y r) ≤ ∑ y ∈ s, ν (Metric.ball y r) := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | @insert a s ha ih =>
        have h_coe : (↑(insert a s) : Set ℝ) = insert a (↑s : Set ℝ) := by
          rw [Finset.coe_insert]
        rw [h_coe, Set.biUnion_insert]
        have h1 : ν (Metric.ball a r ∪ ⋃ y ∈ (s : Set ℝ), Metric.ball y r) ≤
            ν (Metric.ball a r) + ν (⋃ y ∈ (s : Set ℝ), Metric.ball y r) :=
          MeasureTheory.measure_union_le _ _
        have h2 : ν (Metric.ball a r) + ν (⋃ y ∈ (s : Set ℝ), Metric.ball y r) ≤
            ν (Metric.ball a r) + ∑ y ∈ s, ν (Metric.ball y r) := by gcongr
        have h3 : ν (Metric.ball a r) + ∑ y ∈ s, ν (Metric.ball y r) =
            ∑ y ∈ insert a s, ν (Metric.ball y r) := by
          rw [Finset.sum_insert ha] <;> ring
        have h4 : ν (Metric.ball a r ∪ ⋃ y ∈ (s : Set ℝ), Metric.ball y r) ≤
            ∑ y ∈ insert a s, ν (Metric.ball y r) := by
          calc _ ≤ ν (Metric.ball a r) + ν (⋃ y ∈ (s : Set ℝ), Metric.ball y r) := h1
               _ ≤ ν (Metric.ball a r) + ∑ y ∈ s, ν (Metric.ball y r) := h2
               _ = ∑ y ∈ insert a s, ν (Metric.ball y r) := h3
        exact h4
    exact h_ind Ωf
  have h10 : ∑ y ∈ Ωf, ν (Metric.ball y r) ≤ ∑ y ∈ Ωf, ENNReal.ofReal (C_ν * r ^ κ) :=
    Finset.sum_le_sum (fun y _ => h_ball_mass y)
  have h12 : (Ωf.card : ENNReal) ≤ 2 := by exact_mod_cast hΩf_card_le_2
  have h_two_coe : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_cast
  have h_pos_Cr : 0 ≤ C_ν * r ^ κ := by positivity
  calc ν (⋃ y ∈ (Ωf : Set ℝ), Metric.ball y r)
    ≤ ∑ y ∈ Ωf, ν (Metric.ball y r) := h9
  _ ≤ ∑ y ∈ Ωf, ENNReal.ofReal (C_ν * r ^ κ) := h10
  _ = (Ωf.card : ENNReal) * ENNReal.ofReal (C_ν * r ^ κ) := by rw [Finset.sum_const] <;> ring
  _ ≤ 2 * ENNReal.ofReal (C_ν * r ^ κ) := by gcongr <;> exact h12
  _ = ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (C_ν * r ^ κ) := by rw [h_two_coe]
  _ = ENNReal.ofReal (2 * (C_ν * r ^ κ)) := by
    have h_mul : ENNReal.ofReal (2 * (C_ν * r ^ κ)) =
        ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (C_ν * r ^ κ) :=
      ENNReal.ofReal_mul (p := (2 : ℝ)) (q := (C_ν * r ^ κ)) (by norm_num)
    exact h_mul.symm
  _ = ENNReal.ofReal (2 * C_ν * r ^ κ) := by ring_nf
  _ ≤ ENNReal.ofReal (c / 8) := ENNReal.ofReal_le_ofReal h_small

/-- Power corollary: convert exact (c/2)^3 retention to δ^(3*rho_sel) retention
    and express separation as δ^rho_sep. -/
lemma threefold_recursive_selection_power
    {δ κ0 L η c τ C_ν r rho_sel rho_sep : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hkappa_pos : 0 < κ0)
    (hc_pos : 0 < c) (hL_pos : 0 < L) (hη_pos : 0 < η)
    (hτ_pos : 0 < τ) (hC_ν_pos : 0 < C_ν)
    (hr_pos : 0 < r)
    (hrho_sel_pos : 0 < rho_sel)
    (hrho_sep_pos : 0 < rho_sep)
    (q_bad : ℝ) (hq_bad_pos : 0 < q_bad)
    (hδ_rho_sel_le_c2 : δ ^ rho_sel ≤ c / 2)
    (hr_eq : r = δ ^ rho_sep)
    {Ybar : Set ℝ} {Pbar : Set (EuclideanSpace ℝ (Fin 2))}
    {T_y : ℝ → Set (EuclideanSpace ℝ (Fin 2))}
    (hT_y_sub : ∀ y ∈ Ybar, T_y y ⊆ Pbar)
    (hYbar_fin : Ybar.Finite) (hYbar_nonempty : Ybar.Nonempty)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν_counting : ∀ y ∈ Ybar, ν {y} = ENNReal.ofReal (1 / (Ybar.ncard : ℝ)))
    (hν_supp : ν.support = Ybar)
    (hν_frost : IsDirectionFrostman δ τ C_ν ν)
    (h_multiplicity : ∀ p ∈ Pbar,
      ENat.toENNReal {y ∈ Ybar | p ∈ T_y y}.encard ≥
        ENNReal.ofReal c * ENat.toENNReal Ybar.encard)
    (h_proj_bound : ∀ y ∈ Ybar,
      Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) (T_y y)) ≤
      ENNReal.ofReal (δ ^ (-(L * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal)))
    {μE : Measure (EuclideanSpace ℝ (Fin 2))}
    [IsProbabilityMeasure μE]
    (hΘ_bad : ν {y : ℝ | robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) μE) >
      ENNReal.ofReal (δ ^ (-q_bad))} ≤ ENNReal.ofReal (c / 8))
    {E : Finset (EuclideanSpace ℝ (Fin 2))}
    (hE_sub : (E : Set _) ⊆ Pbar)
    (hE_nonempty : E.Nonempty)
    (h_neighborhoods_general : ∀ (Ω : Set ℝ), Ω.encard ≤ 2 →
      ν (⋃ y ∈ Ω, Metric.ball y r) ≤ ENNReal.ofReal (c / 8)) :
    ∃ (θ1 θ2 θ3 : ℝ)
      (E1 E2 E3 : Set (EuclideanSpace ℝ (Fin 2))),
      E3 ⊆ E2 ∧ E2 ⊆ E1 ∧ E1 ⊆ (E : Set _) ∧
      E3.Nonempty ∧
      -- Power retention: |E3| ≥ δ^(3*rho_sel) * |E|
      ENat.toENNReal E3.encard ≥ ENNReal.ofReal (δ ^ (3 * rho_sel)) * (E.card : ENNReal) ∧
      -- Separation: δ^rho_sep
      |θ1 - θ2| ≥ δ ^ rho_sep ∧
      |θ1 - θ3| ≥ δ ^ rho_sep ∧
      |θ2 - θ3| ≥ δ ^ rho_sep ∧
      θ1 < θ3 ∧ θ3 < θ2 ∧
      θ1 ∈ Ybar ∧ θ2 ∈ Ybar ∧ θ3 ∈ Ybar ∧
      (∀ y ∈ ({θ1, θ2, θ3} : Set ℝ),
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) μE) ≤
        ENNReal.ofReal (δ ^ (-q_bad))) ∧
      (∀ y ∈ ({θ1, θ2, θ3} : Set ℝ),
        Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) E3) ≤
        ENNReal.ofReal (δ ^ (-(L * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal))) := by
  have h_main := threefold_recursive_selection
    hδ_pos hδ_lt_one hkappa_pos hc_pos hL_pos hη_pos hτ_pos hC_ν_pos hr_pos
    q_bad hq_bad_pos
    hT_y_sub hYbar_fin hYbar_nonempty hν_counting hν_supp hν_frost h_multiplicity h_proj_bound
    hΘ_bad hE_sub hE_nonempty h_neighborhoods_general
  rcases h_main with ⟨θ1, θ2, θ3, E1, E2, E3,
    hE3_sub_E2, hE2_sub_E1, hE1_sub_E, hE3_nonempty,
    hE1_card, hE2_card, hE3_card,
    h_sep12, h_sep13, h_sep23,
    h_θ13_lt, h_θ32_lt,
    hθ1_Ybar, hθ2_Ybar, hθ3_Ybar,
    h_energy_all, h_proj_all⟩
  -- Convert (c/2)^3 retention to δ^(3*rho_sel)
  have h_c2_ge_drhosel : ENNReal.ofReal (c / 2) ≥ ENNReal.ofReal (δ ^ rho_sel) :=
    ENNReal.ofReal_le_ofReal hδ_rho_sel_le_c2
  have hE3_power : ENat.toENNReal E3.encard ≥
      ENNReal.ofReal (δ ^ (3 * rho_sel)) * (E.card : ENNReal) := by
    have h_c2_ge : ENNReal.ofReal (c / 2) ≥ ENNReal.ofReal (δ ^ rho_sel) :=
      ENNReal.ofReal_le_ofReal hδ_rho_sel_le_c2
    calc ENat.toENNReal E3.encard
      ≥ ENNReal.ofReal (c / 2) * ENat.toENNReal E2.encard := hE3_card
    _ ≥ ENNReal.ofReal (c / 2) * (ENNReal.ofReal (c / 2) * ENat.toENNReal E1.encard) := by gcongr
    _ ≥ ENNReal.ofReal (c / 2) * (ENNReal.ofReal (c / 2) * (ENNReal.ofReal (c / 2) * (E.card : ENNReal))) := by gcongr
    _ = (ENNReal.ofReal (c / 2) * ENNReal.ofReal (c / 2) * ENNReal.ofReal (c / 2)) * (E.card : ENNReal) := by ring
    _ ≥ (ENNReal.ofReal (δ ^ rho_sel) * ENNReal.ofReal (δ ^ rho_sel) * ENNReal.ofReal (δ ^ rho_sel)) * (E.card : ENNReal) := by gcongr
    _ = ENNReal.ofReal (δ ^ (3 * rho_sel)) * (E.card : ENNReal) := by
      have h_pos : 0 ≤ δ ^ rho_sel := by positivity
      have h_pos2 : 0 ≤ (δ ^ rho_sel) * (δ ^ rho_sel) := by positivity
      have h_mul1 : ENNReal.ofReal (δ ^ rho_sel) * ENNReal.ofReal (δ ^ rho_sel) =
          ENNReal.ofReal ((δ ^ rho_sel) * (δ ^ rho_sel)) :=
        (ENNReal.ofReal_mul h_pos).symm
      have h_mul2 : (ENNReal.ofReal (δ ^ rho_sel) * ENNReal.ofReal (δ ^ rho_sel)) * ENNReal.ofReal (δ ^ rho_sel) =
          ENNReal.ofReal (((δ ^ rho_sel) * (δ ^ rho_sel)) * (δ ^ rho_sel)) := by
        rw [h_mul1]
        exact (ENNReal.ofReal_mul h_pos2).symm
      have h_rpow : ((δ ^ rho_sel) * (δ ^ rho_sel)) * (δ ^ rho_sel) = δ ^ (3 * rho_sel) := by
        rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)] <;> ring_nf
      rw [h_mul2, h_rpow]
  -- Convert separation r to δ^rho_sep
  have h_sep12' : |θ1 - θ2| ≥ δ ^ rho_sep := by
    rw [hr_eq] at h_sep12; exact h_sep12
  have h_sep13' : |θ1 - θ3| ≥ δ ^ rho_sep := by
    rw [hr_eq] at h_sep13; exact h_sep13
  have h_sep23' : |θ2 - θ3| ≥ δ ^ rho_sep := by
    rw [hr_eq] at h_sep23; exact h_sep23
  exact ⟨θ1, θ2, θ3, E1, E2, E3,
    hE3_sub_E2, hE2_sub_E1, hE1_sub_E, hE3_nonempty,
    hE3_power,
    h_sep12', h_sep13', h_sep23',
    h_θ13_lt, h_θ32_lt,
    hθ1_Ybar, hθ2_Ybar, hθ3_Ybar,
    h_energy_all, h_proj_all⟩

end ProductLikeIncidence.ProductReduction
