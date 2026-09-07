import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# AD thickening lemma

Thickening a set on the real line by `L ≤ s` preserves the `IsADSet1` property
with an explicit constant blow-up.

Key technical point: for non-closed sets, `z ∈ cthickening L E` only gives
`infEDist z E ≤ L`, not an existential witness. We use `M > L` to get
an exact witness, paying a factor of 3 in the covering number when `M ≤ 2ρ`.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Metric Set

namespace Kakeya.Assouad

/--
If `C` is a finite `ρ`-cover of `A` and `M ≤ 2ρ`, then
`C' = {c - 2ρ, c, c + 2ρ | c ∈ C}` is a `ρ`-cover of `cthickening M A`,
with `|C'| ≤ 3|C|`.
-/
private lemma finite_cover_cthickening_real
    {A : Set ℝ} {rho M : ℝ} (hrho : 0 < rho) (hM : 0 ≤ M) (hM2rho : M ≤ 2 * rho)
    {C : Set ℝ} (hC_fin : C.Finite) (hC_cover : Metric.IsCover ⟨rho, hrho.le⟩ A C) :
    ∃ (C' : Set ℝ), Metric.IsCover ⟨rho, hrho.le⟩ (Metric.cthickening M A) C' ∧
      (C'.encard : ENNReal) ≤ 3 * (C.encard : ENNReal) := by
  let ε : NNReal := ⟨rho, hrho.le⟩
  let C1 : Set ℝ := (fun c : ℝ => c - 2 * rho) '' C
  let C2 : Set ℝ := C
  let C3 : Set ℝ := (fun c : ℝ => c + 2 * rho) '' C
  let C' : Set ℝ := C1 ∪ C2 ∪ C3
  have h_key : ∀ (z : ℝ), z ∈ Metric.cthickening M A → ∃ c ∈ C, dist z c ≤ M + rho := by
    intro z hz
    by_contra h
    push Not at h
    by_cases hC_empty : C = ∅
    · have hA_empty : A = ∅ := by
        by_contra hA
        have hA' : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA
        rcases hA' with ⟨a, ha⟩
        have h := hC_cover ha
        rw [hC_empty] at h
        simp at h
      rw [hA_empty] at hz
      simp at hz
    · have hC_nonempty : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_empty
      have h_min : ∃ c0 ∈ C, ∀ c ∈ C, dist z c0 ≤ dist z c :=
        Set.exists_min_image C (fun c => dist z c) hC_fin hC_nonempty
      rcases h_min with ⟨c0, hc0, hc0_min⟩
      have h_gt : M + rho < dist z c0 := h c0 hc0
      set δ : ℝ := (dist z c0 - (M + rho)) / 2 with hδ_def
      have hδ_pos : 0 < δ := by
        rw [hδ_def]
        have h_pos : 0 < dist z c0 - (M + rho) := by linarith
        linarith
      have h_all : ∀ c ∈ C, M + rho + δ < dist z c := by
        intro c hc
        have h4 : dist z c0 ≤ dist z c := hc0_min c hc
        linarith
      have h_contra : ∀ a ∈ A, M + δ < dist z a := by
        intro a ha
        have h5 : ∃ c ∈ C, nndist a c ≤ ε := by
          have h := hC_cover (ha)
          simpa [Metric.IsCover, SetRel.IsCover] using h
        rcases h5 with ⟨c, hc, h6⟩
        have h7 : dist a c ≤ rho := by
          have h71 : (nndist a c : ℝ) ≤ (ε : ℝ) := by exact_mod_cast h6
          have h72 : (nndist a c : ℝ) = dist a c := by
            exact coe_nndist a c
          have h73 : (ε : ℝ) = rho := by
            simp [ε]
            <;> rfl
          rw [h72, h73] at h71
          exact h71
        have h8 : dist z c ≤ dist z a + dist a c := dist_triangle z a c
        linarith [h_all c hc]
      have h9 : ∀ a ∈ A, ENNReal.ofReal (M + δ) ≤ edist z a := by
        intro a ha
        have h10 : M + δ < dist z a := h_contra a ha
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      have h10 : ENNReal.ofReal (M + δ) ≤ infEDist z A := by
        exact le_infEDist.mpr h9
      have h11 : ENNReal.ofReal M < ENNReal.ofReal (M + δ) := by
        rw [ENNReal.ofReal_lt_ofReal_iff] <;> linarith
      have h12 : ENNReal.ofReal M < infEDist z A := h11.trans_le h10
      have h13 : infEDist z A ≤ ENNReal.ofReal M := by
        simpa [Metric.mem_cthickening_iff] using hz
      exact False.elim (not_le.mpr h12 h13)
  have h_cover : Metric.IsCover ε (Metric.cthickening M A) C' := by
    intro z hz
    rcases h_key z hz with ⟨c, hc, hdist⟩
    have h2 : dist z c ≤ M + rho := hdist
    have h3 : dist z c ≤ 3 * rho := by linarith
    have h3' : c - 3 * rho ≤ z := by
      have h : |z - c| ≤ 3 * rho := by simpa [dist_eq_norm, Real.norm_eq_abs] using h3
      rw [abs_le] at h; linarith
    have h3'' : z ≤ c + 3 * rho := by
      have h : |z - c| ≤ 3 * rho := by simpa [dist_eq_norm, Real.norm_eq_abs] using h3
      rw [abs_le] at h; linarith
    by_cases h4 : z ≤ c - rho
    · -- z ∈ [c-3ρ, c-ρ], center c-2ρ
      have h5 : c - 2 * rho ∈ C' := Or.inl (Or.inl ⟨c, hc, by ring⟩)
      have h61 : c - 3 * rho ≤ z := h3'
      have h62 : z ≤ c - rho := h4
      have h6 : dist z (c - 2 * rho) ≤ rho := by
        simp [dist_eq_norm, Real.norm_eq_abs, abs_le] <;> constructor <;> linarith
      have h7 : edist z (c - 2 * rho) ≤ (ε : ENNReal) := by
        rw [edist_dist]
        have h_ε : (ε : ℝ) = rho := Subtype.coe_mk rho hrho.le
        have h_dist_le : dist z (c - 2 * rho) ≤ (ε : ℝ) := by
          rw [h_ε] <;> exact h6
        exact ENNReal.ofReal_le_coe.mpr h_dist_le
      exact ⟨c - 2 * rho, h5, by simpa using h7⟩
    · -- z > c - ρ
      have h4' : c - rho < z := by linarith
      by_cases h5 : z ≤ c + rho
      · -- z ∈ (c-ρ, c+ρ], center c
        have h6 : c ∈ C' := Or.inl (Or.inr hc)
        have h7 : dist z c ≤ rho := by
          simp [dist_eq_norm, Real.norm_eq_abs, abs_le] <;> constructor <;> linarith
        have h8 : edist z c ≤ (ε : ENNReal) := by
          rw [edist_dist]
          have h_ε : (ε : ℝ) = rho := Subtype.coe_mk rho hrho.le
          have h_dist_le : dist z c ≤ (ε : ℝ) := by rw [h_ε] <;> exact h7
          exact ENNReal.ofReal_le_coe.mpr h_dist_le
        exact ⟨c, h6, by simpa using h8⟩
      · -- z > c + ρ, so z ∈ (c+ρ, c+3ρ], center c+2ρ
        have h5' : c + rho < z := by linarith
        have h9 : c + 2 * rho ∈ C' := Or.inr ⟨c, hc, by ring⟩
        have h10 : dist z (c + 2 * rho) ≤ rho := by
          simp [dist_eq_norm, Real.norm_eq_abs, abs_le] <;> constructor <;> linarith
        have h11 : edist z (c + 2 * rho) ≤ (ε : ENNReal) := by
          rw [edist_dist]
          have h_ε : (ε : ℝ) = rho := Subtype.coe_mk rho hrho.le
          have h_dist_le : dist z (c + 2 * rho) ≤ (ε : ℝ) := by rw [h_ε] <;> exact h10
          exact ENNReal.ofReal_le_coe.mpr h_dist_le
        exact ⟨c + 2 * rho, h9, by simpa using h11⟩
  have h_inj1 : Set.InjOn (fun c : ℝ => c - 2 * rho) C := by
    intro x _ y _ h; simpa using h
  have h_inj3 : Set.InjOn (fun c : ℝ => c + 2 * rho) C := by
    intro x _ y _ h; simpa using h
  have h_card : (C'.encard : ENNReal) ≤ 3 * (C.encard : ENNReal) := by
    have h_union1 : ((C1 ∪ C2 ∪ C3).encard : ENNReal) ≤
        ((C1 ∪ C2).encard : ENNReal) + (C3.encard : ENNReal) := by
      have h := Set.encard_union_le (C1 ∪ C2) C3
      exact_mod_cast h
    have h_union2 : ((C1 ∪ C2).encard : ENNReal) ≤
        (C1.encard : ENNReal) + (C2.encard : ENNReal) := by
      have h := Set.encard_union_le C1 C2
      exact_mod_cast h
    have h1 : (C'.encard : ENNReal) ≤ (C1.encard : ENNReal) + (C2.encard : ENNReal) + (C3.encard : ENNReal) := by
      calc (C'.encard : ENNReal)
          ≤ ((C1 ∪ C2).encard : ENNReal) + (C3.encard : ENNReal) := h_union1
        _ ≤ (C1.encard : ENNReal) + (C2.encard : ENNReal) + (C3.encard : ENNReal) := by
          gcongr
    have h2 : (C1.encard : ENNReal) = (C.encard : ENNReal) := by rw [h_inj1.encard_image]
    have h3 : (C3.encard : ENNReal) = (C.encard : ENNReal) := by rw [h_inj3.encard_image]
    have h4 : (C2.encard : ENNReal) = (C.encard : ENNReal) := by rfl
    rw [h2, h3, h4] at h1
    have h_sum : (C.encard : ENNReal) + (C.encard : ENNReal) + (C.encard : ENNReal) =
        3 * (C.encard : ENNReal) := by ring
    rw [h_sum] at h1
    exact h1
  exact ⟨C', h_cover, h_card⟩

/--
Thickening a set of reals by `M ≤ 2ρ` increases its `ρ`-covering number
by at most a factor of 3.
-/
lemma externalCoveringNumber_cthickening_real3
    {A : Set ℝ} {rho M : ℝ} (hrho : 0 < rho) (hM : 0 ≤ M) (hM2rho : M ≤ 2 * rho) :
    (Metric.externalCoveringNumber ⟨rho, hrho.le⟩ (Metric.cthickening M A) : ENNReal) ≤
    3 * (Metric.externalCoveringNumber ⟨rho, hrho.le⟩ A : ENNReal) := by
  let ε : NNReal := ⟨rho, hrho.le⟩
  let N := Metric.externalCoveringNumber ε A
  by_cases hN : N = ⊤
  · have h_goal : (Metric.externalCoveringNumber ε (Metric.cthickening M A) : ENNReal) ≤
        3 * (N : ENNReal) := by
      rw [hN] <;> simp
    exact h_goal
  · let ι := {C : Set ℝ // Metric.IsCover ε A C}
    have hι_nonempty : Nonempty ι := by
      refine ⟨⟨Set.univ, ?_⟩⟩
      intro x hx
      refine ⟨x, Set.mem_univ x, ?_⟩
      simp
    let f : ι → ENat := fun p => p.val.encard
    have h_main_eq : (⨅ (p : ι), f p) = N := by
      have h1 : (⨅ (p : ι), f p) = ⨅ (C : Set ℝ) (h : Metric.IsCover ε A C), C.encard := by
        rw [iInf_subtype] <;> rfl
      have h2 : N = ⨅ (C : Set ℝ) (h : Metric.IsCover ε A C), C.encard := by
        rfl
      rw [h1, ←h2]
    have h_exists : ∃ (p : ι), f p = N := by
      have h := ENat.exists_eq_iInf f
      rw [h_main_eq] at *
      exact h
    rcases h_exists with ⟨p, hp_encard⟩
    let C := p.val
    have hC_cover : Metric.IsCover ε A C := p.property
    have hC_encard : C.encard = N := hp_encard
    have hC_fin : C.Finite := by
      have h_ne : C.encard ≠ ⊤ := by rw [hC_encard]; exact hN
      have h_lt : C.encard < ⊤ := by
        exact Ne.lt_top' (id (Ne.symm h_ne))
      have h_iff : C.encard < ⊤ ↔ C.Finite := Set.encard_lt_top_iff
      exact h_iff.mp h_lt
    have h_main := finite_cover_cthickening_real hrho hM hM2rho hC_fin hC_cover
    rcases h_main with ⟨C', hC'_cover, hC'_card⟩
    have h_le_enat : Metric.externalCoveringNumber ε (Metric.cthickening M A) ≤ C'.encard :=
      IsCover.externalCoveringNumber_le_encard hC'_cover
    have h_le : (Metric.externalCoveringNumber ε (Metric.cthickening M A) : ENNReal) ≤
        (C'.encard : ENNReal) := by
      exact_mod_cast h_le_enat
    calc (Metric.externalCoveringNumber ε (Metric.cthickening M A) : ENNReal)
        ≤ (C'.encard : ENNReal) := h_le
      _ ≤ 3 * (C.encard : ENNReal) := hC'_card
      _ = 3 * (N : ENNReal) := by rw [hC_encard]

/-- Finite union bound for external covering numbers. -/
private lemma externalCoveringNumber_finset_biUnion_le
    {ι : Type*} {s : Finset ι} {f : ι → Set ℝ} {ε : NNReal} :
    (Metric.externalCoveringNumber ε (⋃ i ∈ s, f i) : ENNReal) ≤
    ∑ i ∈ s, (Metric.externalCoveringNumber ε (f i) : ENNReal) := by
  induction s using Finset.induction with
  | empty =>
    simp
  | @insert i s hi ih =>
    have h_eq : (⋃ j ∈ (insert i s), f j) = f i ∪ (⋃ j ∈ s, f j) := by
      ext x; simp [hi] <;> tauto
    rw [h_eq, Finset.sum_insert hi]
    have h_union : (Metric.externalCoveringNumber ε (f i ∪ (⋃ j ∈ s, f j)) : ENNReal) ≤
        (Metric.externalCoveringNumber ε (f i) : ENNReal) +
        (Metric.externalCoveringNumber ε (⋃ j ∈ s, f j) : ENNReal) := by
      exact_mod_cast externalCoveringNumber_union_le
    have h_ih' : (Metric.externalCoveringNumber ε (f i) : ENNReal) +
        (Metric.externalCoveringNumber ε (⋃ j ∈ s, f j) : ENNReal) ≤
        (Metric.externalCoveringNumber ε (f i) : ENNReal) + ∑ j ∈ s, (Metric.externalCoveringNumber ε (f j) : ENNReal) := by
      gcongr
    exact le_trans h_union h_ih'

/--
Cover [-4,4] by 4 closed balls of radius 1 centered at -3, -1, 1, 3.
-/
private lemma icc_four_four_cover_by_four_balls :
    Set.Icc (-4 : ℝ) 4 ⊆
      Metric.closedBall (-3) 1 ∪ Metric.closedBall (-1) 1 ∪
      Metric.closedBall 1 1 ∪ Metric.closedBall 3 1 := by
  intro x hx
  have h1 : -4 ≤ x := hx.1
  have h2 : x ≤ 4 := hx.2
  by_cases h3 : x ≤ -2
  · exact Or.inl (Or.inl (Or.inl (by
      simp [dist_eq_norm, Real.norm_eq_abs, abs_le]
      <;> constructor <;> linarith)))
  · by_cases h4 : x ≤ 0
    · exact Or.inl (Or.inl (Or.inr (by
        simp [dist_eq_norm, Real.norm_eq_abs, abs_le]
        <;> constructor <;> linarith)))
    · by_cases h5 : x ≤ 2
      · exact Or.inl (Or.inr (by
          simp [dist_eq_norm, Real.norm_eq_abs, abs_le]
          <;> constructor <;> linarith))
      · exact Or.inr (by
          simp [dist_eq_norm, Real.norm_eq_abs, abs_le]
          <;> constructor <;> linarith)

/--
Thickening preserves `IsADSet1` with an explicit constant.

Uses a global 4-ball cover of [-4,4], giving constant `12 * C * (1/s)^α`.
This is a coarse global fallback.  The normalized Step 4 prism-cardinality
argument should use `externalCoveringNumber_cthickening_real2` at the selected
scale, which loses only the absolute factor two.
-/
lemma IsADSet1.cthickening_simple
    {E : Set ℝ} {s α : ℝ} {C : ENNReal} {M : ℝ}
    (hAD : IsADSet1 E s α C)
    (hM : 0 ≤ M) (hMs : M ≤ s) (hs_one : s ≤ 1)
    (h_bounded : Metric.cthickening M E ⊆ Set.Icc (-4 : ℝ) 4) :
    IsADSet1 (Metric.cthickening M E) s α
      (12 * C * Kakeya.realRpowENN (1 / s) α) := by
  rcases hAD with ⟨hs_pos, hα_pos, hα_one, hC_one, hE_bounded, h_cover⟩
  have hα_nonneg : 0 ≤ α := by linarith
  let c1 := (-3 : ℝ)
  let c2 := (-1 : ℝ)
  let c3 := (1 : ℝ)
  let c4 := (3 : ℝ)
  let B : ℝ → Set ℝ := fun c => Metric.closedBall c 1
  have h_cover4 : Set.Icc (-4 : ℝ) 4 ⊆ B c1 ∪ B c2 ∪ B c3 ∪ B c4 :=
    icc_four_four_cover_by_four_balls
  have h_rpow_one : (1 : ENNReal) ≤ Kakeya.realRpowENN (1 / s) α := by
    dsimp only [Kakeya.realRpowENN]
    have h4 : 1 ≤ 1 / s := by
      have h5 : 0 < s := hs_pos
      have h6 : s ≤ 1 := hs_one
      calc 1 = 1 / 1 := by norm_num
        _ ≤ 1 / s := by gcongr
    have h3 : (1 : ℝ) ≤ Real.rpow (1 / s) α := Real.one_le_rpow h4 hα_nonneg
    have h4' : (1 : ENNReal) ≤ ENNReal.ofReal (Real.rpow (1 / s) α) := by
      simpa using ENNReal.ofReal_le_ofReal h3
    exact h4'
  have hC'_one : (1 : ENNReal) ≤ 12 * C * Kakeya.realRpowENN (1 / s) α := by
    have h1 : (1 : ENNReal) ≤ C := hC_one
    set X := Kakeya.realRpowENN (1 / s) α with hX
    have h3 : C ≤ C * X := le_mul_of_one_le_right' h_rpow_one
    have h4 : C * X ≤ 12 * C * X := by
      have h5 : (1 : ENNReal) ≤ 12 := by norm_num
      have h6 : C * X ≤ (12 : ENNReal) * (C * X) := le_mul_of_one_le_left' h5
      simpa [mul_assoc] using h6
    exact le_trans h1 (le_trans h3 h4)
  refine' ⟨hs_pos, hα_pos, hα_one, hC'_one, h_bounded, _⟩
  intro rho hrho_nonneg hs_rho rho_one x r hr_ge_rho hr_one
  set E' := Metric.cthickening M E with hE'
  have hrho_pos : 0 < rho := by linarith
  let ε : NNReal := ⟨rho, hrho_nonneg⟩
  let A1 := E ∩ B c1
  let A2 := E ∩ B c2
  let A3 := E ∩ B c3
  let A4 := E ∩ B c4
  let S : Finset ℝ := ({-3, -1, 1, 3} : Finset ℝ)
  have hS_card : S.card = 4 := by
    simp [S] <;> norm_num
  have h4 : E ⊆ Set.Icc (-4 : ℝ) 4 := hE_bounded
  have h5 : E ⊆ B c1 ∪ B c2 ∪ B c3 ∪ B c4 := Set.Subset.trans h4 h_cover4
  have h6' : E ⊆ ⋃ c ∈ S, (E ∩ B c) := by
    intro z hz
    have h7 : z ∈ B c1 ∪ B c2 ∪ B c3 ∪ B c4 := h5 hz
    have h9 : z ∈ B c1 ∨ z ∈ B c2 ∨ z ∈ B c3 ∨ z ∈ B c4 := by
      simp only [Set.mem_union] at h7
      tauto
    rcases h9 with (h9 | h9 | h9 | h9)
    · have h11 : c1 ∈ (S : Set ℝ) := by
        have h_eq : c1 = -3 := by rfl
        rw [h_eq]
        simp [S] <;> norm_num
      have h12 : z ∈ E ∩ B c1 := ⟨hz, h9⟩
      exact Set.mem_biUnion h11 h12
    · have h11 : c2 ∈ (S : Set ℝ) := by
        have h_eq : c2 = -1 := by rfl
        rw [h_eq]
        simp [S] <;> norm_num
      have h12 : z ∈ E ∩ B c2 := ⟨hz, h9⟩
      exact Set.mem_biUnion h11 h12
    · have h11 : c3 ∈ (S : Set ℝ) := by
        have h_eq : c3 = 1 := by rfl
        rw [h_eq]
        simp [S] <;> norm_num
      have h12 : z ∈ E ∩ B c3 := ⟨hz, h9⟩
      exact Set.mem_biUnion h11 h12
    · have h11 : c4 ∈ (S : Set ℝ) := by
        have h_eq : c4 = 3 := by rfl
        rw [h_eq]
        simp [S] <;> norm_num
      have h12 : z ∈ E ∩ B c4 := ⟨hz, h9⟩
      exact Set.mem_biUnion h11 h12
  have h7_enat : Metric.externalCoveringNumber ε E ≤
      Metric.externalCoveringNumber ε (⋃ c ∈ S, (E ∩ B c)) :=
    Metric.externalCoveringNumber_mono_set h6'
  have h7 : (Metric.externalCoveringNumber ε E : ENNReal) ≤
      (Metric.externalCoveringNumber ε (⋃ c ∈ S, (E ∩ B c)) : ENNReal) := by
    exact_mod_cast h7_enat
  have h8 : (Metric.externalCoveringNumber ε (⋃ c ∈ S, (E ∩ B c)) : ENNReal) ≤
      ∑ c ∈ S, (Metric.externalCoveringNumber ε (E ∩ B c) : ENNReal) :=
    externalCoveringNumber_finset_biUnion_le
  have h9 : ∀ c ∈ S, (Metric.externalCoveringNumber ε (E ∩ B c) : ENNReal) ≤
      C * Kakeya.realRpowENN (1 / rho) α := by
    intro c hc
    exact h_cover rho hrho_nonneg hs_rho rho_one c 1 (by linarith) (by norm_num)
  have h10 : (∑ c ∈ S, (Metric.externalCoveringNumber ε (E ∩ B c) : ENNReal)) ≤
      ∑ c ∈ S, C * Kakeya.realRpowENN (1 / rho) α := by
    apply Finset.sum_le_sum
    intro c hc
    exact h9 c hc
  have h11 : ∑ c ∈ S, C * Kakeya.realRpowENN (1 / rho) α =
      4 * (C * Kakeya.realRpowENN (1 / rho) α) := by
    rw [Finset.sum_const, hS_card] <;> ring
  have h12 : E' ∩ Metric.closedBall x r ⊆ E' := by intro z hz; exact hz.1
  have h13_enat : Metric.externalCoveringNumber ε (E' ∩ Metric.closedBall x r) ≤
      Metric.externalCoveringNumber ε E' :=
    Metric.externalCoveringNumber_mono_set h12
  have h13 : (Metric.externalCoveringNumber ε (E' ∩ Metric.closedBall x r) : ENNReal) ≤
      (Metric.externalCoveringNumber ε E' : ENNReal) := by
    exact_mod_cast h13_enat
  have h14 : (Metric.externalCoveringNumber ε E' : ENNReal) ≤
      3 * (Metric.externalCoveringNumber ε E : ENNReal) :=
    externalCoveringNumber_cthickening_real3 hrho_pos hM (by linarith)
  have hr_pos : 0 < r := by linarith
  have h15 : (1 / rho : ℝ) = (r / rho) * (1 / r) := by
    field_simp [hr_pos.ne', hrho_pos.ne'] <;> ring
  have h16 : Kakeya.realRpowENN (1 / rho) α =
      Kakeya.realRpowENN (r / rho) α * Kakeya.realRpowENN (1 / r) α := by
    have hpos1 : 0 < r / rho := by positivity
    have hpos2 : 0 < 1 / r := by positivity
    rw [h15, realRpowENN_mul hpos1 hpos2 α] <;> ring
  have h17 : Kakeya.realRpowENN (1 / r) α ≤ Kakeya.realRpowENN (1 / s) α := by
    have h18 : 1 / r ≤ 1 / s := by
      have hr_pos : 0 < r := by linarith
      have hs_pos2 : 0 < s := hs_pos
      gcongr <;> linarith
    dsimp only [Kakeya.realRpowENN]
    have hpos3 : 0 ≤ 1 / r := by positivity
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hpos3 h18 hα_nonneg)
  have h18 : (Metric.externalCoveringNumber ε E : ENNReal) ≤
      ∑ c ∈ S, (Metric.externalCoveringNumber ε (E ∩ B c) : ENNReal) :=
    le_trans h7 h8
  calc (Metric.externalCoveringNumber ε (E' ∩ Metric.closedBall x r) : ENNReal)
      ≤ (Metric.externalCoveringNumber ε E' : ENNReal) := h13
    _ ≤ 3 * (Metric.externalCoveringNumber ε E : ENNReal) := h14
    _ ≤ 3 * (∑ c ∈ S, (Metric.externalCoveringNumber ε (E ∩ B c) : ENNReal)) := by
      gcongr
    _ ≤ 3 * (∑ c ∈ S, C * Kakeya.realRpowENN (1 / rho) α) := by
      gcongr
    _ = 3 * (4 * (C * Kakeya.realRpowENN (1 / rho) α)) := by rw [h11]
    _ = 12 * C * Kakeya.realRpowENN (1 / rho) α := by ring
    _ = 12 * C * (Kakeya.realRpowENN (r / rho) α * Kakeya.realRpowENN (1 / r) α) := by
      rw [h16] <;> ring
    _ ≤ 12 * C * (Kakeya.realRpowENN (r / rho) α * Kakeya.realRpowENN (1 / s) α) := by gcongr
    _ = (12 * C * Kakeya.realRpowENN (1 / s) α) * Kakeya.realRpowENN (r / rho) α := by ring

/--
If C is a finite s-cover of A and M ≤ s, then
C' = {c - M, c + M | c ∈ C} is an s-cover of cthickening M A,
with |C'| ≤ 2|C|.
-/
private lemma finite_cover_cthickening2_real
    {A : Set ℝ} {s M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (hMs : M ≤ s)
    {C : Set ℝ} (hC_fin : C.Finite) (hC_cover : Metric.IsCover ⟨s, hs.le⟩ A C) :
    ∃ (C' : Set ℝ), Metric.IsCover ⟨s, hs.le⟩ (Metric.cthickening M A) C' ∧
      (C'.encard : ENNReal) ≤ 2 * (C.encard : ENNReal) := by
  let ε : NNReal := ⟨s, hs.le⟩
  by_cases hC_empty : C = ∅
  · have hA_empty : A = ∅ := by
      by_contra hA
      have hA' : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA
      rcases hA' with ⟨a, ha⟩
      have h := hC_cover ha
      rw [hC_empty] at h
      simp at h
    refine' ⟨∅, _ , _⟩
    · rw [hA_empty]; simp
    · simp
  · have hC_nonempty : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_empty
    let C1 : Set ℝ := (fun c : ℝ => c - M) '' C
    let C2 : Set ℝ := (fun c : ℝ => c + M) '' C
    let C' : Set ℝ := C1 ∪ C2
    have h_main : ∀ (z : ℝ), z ∈ Metric.cthickening M A → ∃ c ∈ C, dist z c ≤ s + M := by
      intro z hz
      by_contra h
      push Not at h
      have h1 : ∀ c ∈ C, s + M < dist z c := by simpa using h
      let f : ℝ → ℝ := fun c => dist z c - (s + M)
      have h2 : ∀ c ∈ C, 0 < f c := by
        intro c hc
        have h3 : s + M < dist z c := h1 c hc
        linarith
      have h3 : ∃ c0 ∈ C, ∀ c ∈ C, f c0 ≤ f c :=
        Set.exists_min_image C f hC_fin hC_nonempty
      rcases h3 with ⟨c0, hc0, hmin⟩
      let δ : ℝ := f c0
      have hδ_pos : 0 < δ := h2 c0 hc0
      have h4 : ∀ c ∈ C, s + M + δ ≤ dist z c := by
        intro c hc
        have h5 : f c0 ≤ f c := hmin c hc
        dsimp only [f] at h5
        linarith
      have h5 : ∀ a ∈ A, M + δ / 2 < dist z a := by
        intro a ha
        have h6 : ∃ c ∈ C, nndist a c ≤ ε := by
          simpa [Metric.IsCover, SetRel.IsCover] using hC_cover ha
        rcases h6 with ⟨c, hc, h7⟩
        have h8 : dist a c ≤ s := by
          have h9 : (nndist a c : ℝ) ≤ s := by exact_mod_cast h7
          have h10 : (nndist a c : ℝ) = dist a c := coe_nndist a c
          rw [h10] at h9
          exact h9
        have h11 : dist z c ≤ dist z a + dist a c := dist_triangle z a c
        have h12 : M + δ ≤ dist z a := by linarith [h4 c hc, h11, h8]
        have h13 : M + δ / 2 < dist z a := by linarith
        exact h13
      have h6 : ∀ a ∈ A, ENNReal.ofReal (M + δ / 2) ≤ edist z a := by
        intro a ha
        have h7 : M + δ / 2 < dist z a := h5 a ha
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      have h7 : ENNReal.ofReal (M + δ / 2) ≤ infEDist z A :=
        le_infEDist.mpr h6
      have h8 : ENNReal.ofReal M < ENNReal.ofReal (M + δ / 2) := by
        rw [ENNReal.ofReal_lt_ofReal_iff] <;> linarith
      have h9 : ENNReal.ofReal M < infEDist z A := h8.trans_le h7
      have h10 : infEDist z A ≤ ENNReal.ofReal M := by
        simpa [Metric.mem_cthickening_iff] using hz
      exact False.elim (not_le.mpr h9 h10)
    have h_cover : Metric.IsCover ε (Metric.cthickening M A) C' := by
      intro z hz
      rcases h_main z hz with ⟨c, hc, hdist⟩
      have h2 : dist z c ≤ s + M := hdist
      have h3 : c - (s + M) ≤ z := by
        have h : |z - c| ≤ s + M := by simpa [dist_eq_norm, Real.norm_eq_abs] using h2
        rw [abs_le] at h <;> linarith
      have h4 : z ≤ c + (s + M) := by
        have h : |z - c| ≤ s + M := by simpa [dist_eq_norm, Real.norm_eq_abs] using h2
        rw [abs_le] at h <;> linarith
      have hε_real : (ε : ℝ) = s := by
        rfl
      by_cases h5 : z ≤ c
      · have h6 : c - M ∈ C' := Or.inl ⟨c, hc, by ring⟩
        have h7 : dist z (c - M) ≤ s := by
          simp [dist_eq_norm, Real.norm_eq_abs, abs_le] <;> constructor <;> linarith
        have h7' : dist z (c - M) ≤ (ε : ℝ) := by rw [hε_real]; exact h7
        have h8 : edist z (c - M) ≤ (↑ε : ENNReal) := by exact_mod_cast h7'
        exact ⟨c - M, h6, h8⟩
      · have h5' : c < z := by linarith
        have h6 : c + M ∈ C' := Or.inr ⟨c, hc, by ring⟩
        have h7 : dist z (c + M) ≤ s := by
          simp [dist_eq_norm, Real.norm_eq_abs, abs_le] <;> constructor <;> linarith
        have h7' : dist z (c + M) ≤ (ε : ℝ) := by rw [hε_real]; exact h7
        have h8 : edist z (c + M) ≤ (↑ε : ENNReal) := by exact_mod_cast h7'
        exact ⟨c + M, h6, h8⟩
    have h_inj1 : Set.InjOn (fun c : ℝ => c - M) C := by
      intro x _ y _ h; simpa using h
    have h_inj2 : Set.InjOn (fun c : ℝ => c + M) C := by
      intro x _ y _ h; simpa using h
    have h_card : (C'.encard : ENNReal) ≤ 2 * (C.encard : ENNReal) := by
      have h_union1 : ((C1 ∪ C2).encard : ENNReal) ≤
          (C1.encard : ENNReal) + (C2.encard : ENNReal) := by
        have h := Set.encard_union_le C1 C2
        exact_mod_cast h
      have h1 : (C1.encard : ENNReal) = (C.encard : ENNReal) := by rw [h_inj1.encard_image]
      have h2 : (C2.encard : ENNReal) = (C.encard : ENNReal) := by rw [h_inj2.encard_image]
      rw [h1, h2] at h_union1
      have h_sum : (C.encard : ENNReal) + (C.encard : ENNReal) = 2 * (C.encard : ENNReal) := by ring
      rw [h_sum] at h_union1
      exact h_union1
    exact ⟨C', h_cover, h_card⟩

/--
Thickening a set of reals by `M ≤ s` increases its `s`-covering number
by at most a factor of 2.
-/
lemma externalCoveringNumber_cthickening_real2
    {A : Set ℝ} {s M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (hMs : M ≤ s) :
    (Metric.externalCoveringNumber ⟨s, hs.le⟩ (Metric.cthickening M A) : ENNReal) ≤
    2 * (Metric.externalCoveringNumber ⟨s, hs.le⟩ A : ENNReal) := by
  let ε : NNReal := ⟨s, hs.le⟩
  let N := Metric.externalCoveringNumber ε A
  by_cases hN : N = ⊤
  · have h_top : (Metric.externalCoveringNumber ε A : ENNReal) = ⊤ := by
      exact_mod_cast hN
    rw [h_top] <;> simp
  · let ι := {C : Set ℝ // Metric.IsCover ε A C}
    have hι_nonempty : Nonempty ι := by
      refine ⟨⟨Set.univ, ?_⟩⟩
      intro x hx
      refine ⟨x, Set.mem_univ x, ?_⟩
      simp
    let f : ι → ENat := fun p => p.val.encard
    have h_main_eq : (⨅ (p : ι), f p) = N := by
      have h1 : (⨅ (p : ι), f p) = ⨅ (C : Set ℝ) (h : Metric.IsCover ε A C), C.encard := by
        rw [iInf_subtype]
      rw [h1] <;> rfl
    have h_exists : ∃ (p : ι), f p = N := by
      have h := ENat.exists_eq_iInf f
      rw [h_main_eq] at *
      exact h
    rcases h_exists with ⟨p, hp_encard⟩
    let C := p.val
    have hC_cover : Metric.IsCover ε A C := p.property
    have hC_encard : C.encard = N := hp_encard
    have hC_fin : C.Finite := by
      have h_ne : C.encard ≠ ⊤ := by rw [hC_encard]; exact hN
      have h_lt : C.encard < ⊤ := Ne.lt_top' (Ne.symm h_ne)
      have h_iff : C.encard < ⊤ ↔ C.Finite := Set.encard_lt_top_iff
      exact h_iff.mp h_lt
    have h_main := finite_cover_cthickening2_real hs hM hMs hC_fin hC_cover
    rcases h_main with ⟨C', hC'_cover, hC'_card⟩
    have h_le : (Metric.externalCoveringNumber ε (Metric.cthickening M A) : ENNReal) ≤
        (C'.encard : ENNReal) := by
      exact_mod_cast IsCover.externalCoveringNumber_le_encard hC'_cover
    calc (Metric.externalCoveringNumber ε (Metric.cthickening M A) : ENNReal)
        ≤ (C'.encard : ENNReal) := h_le
      _ ≤ 2 * (C.encard : ENNReal) := hC'_card
      _ = 2 * (N : ENNReal) := by rw [hC_encard]
