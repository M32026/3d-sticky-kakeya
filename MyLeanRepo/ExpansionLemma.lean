module

/-
# Expansion Lemma (Lemma 3.2)

Definitions and proof of the Expansion Lemma from the paper
"An easier proof of Bourgain's discretized projection theorem".
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.BlichfeldtN
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Measure Set Metric
open scoped BigOperators Pointwise

namespace ExpansionLemma

/-! ## Definitions -/

def iteratedSumset (A : Set ℝ) : ℕ → Set ℝ
  | 0 => {0}
  | n + 1 => Set.image2 (· + ·) A (iteratedSumset A n)

def productSet (A : Set ℝ) (n : ℕ) : Set ℝ :=
  {x | ∃ (f : Fin n → ℝ), (∀ i, f i ∈ A) ∧ x = ∏ i : Fin n, f i}

def cartesianPower (A : Set ℝ) (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun (_ : Fin n) => A)

def scaledSumset {ι : Type*} [Fintype ι] (v : ι → ℝ) (A : Set ℝ) : Set ℝ :=
  {x | ∃ (a : ι → ℝ), (∀ i, a i ∈ A) ∧ x = ∑ i : ι, v i * a i}

def scaledSumsetExcept {n : ℕ} (v : Fin n → ℝ) (j : Fin n) (A : Set ℝ) : Set ℝ :=
  scaledSumset (fun (i : {i : Fin n // i ≠ j}) => v i) A

def iteratedDifference (S : Set ℝ) (N : ℕ) : Set ℝ :=
  Set.image2 (· - ·) (iteratedSumset S N) (iteratedSumset S N)

/-! ## Basic properties -/

lemma scaledSumset_eq_image {n : ℕ} {v : Fin n → ℝ} {A : Set ℝ} :
    scaledSumset v A = (fun x : Fin n → ℝ => ∑ i, v i * x i) '' cartesianPower A n := by
  ext x; simp only [scaledSumset, cartesianPower, Set.mem_image, Set.mem_univ_pi]
  <;> constructor <;> rintro ⟨a, ha, rfl⟩ <;> exact ⟨a, ha, rfl⟩

lemma scaledSumset_compact {n : ℕ} {v : Fin n → ℝ} {A : Set ℝ}
    (hA : IsCompact A) : IsCompact (scaledSumset v A) := by
  rw [scaledSumset_eq_image]
  have h1 : IsCompact (cartesianPower A n) := by
    rw [cartesianPower]; simpa using isCompact_univ_pi (fun _ => hA)
  exact h1.image (by fun_prop)

lemma scaledSumset_measurableSet {n : ℕ} {v : Fin n → ℝ} {A : Set ℝ}
    (hA : IsCompact A) : MeasurableSet (scaledSumset v A) :=
  (scaledSumset_compact hA).measurableSet

/-! ## Helper lemmas -/

lemma measure_pigeonhole {α : Type*} [Fintype α] {μ : Measure ℝ}
    {S : α → Set ℝ} (hS_meas : ∀ i, MeasurableSet (S i))
    {lam C : ENNReal} (hlam : ∀ i, μ (S i) ≥ lam)
    (hC : μ (⋃ i, S i) ≤ C) (h : (Fintype.card α : ENNReal) * lam > C) :
    ∃ (i j : α), i ≠ j ∧ (S i ∩ S j).Nonempty := by
  by_contra h'
  have h_no_inter : ∀ (i j : α), i ≠ j → S i ∩ S j = ∅ := by
    intro i j hne
    have h5 : ¬(S i ∩ S j).Nonempty := by intro h6; exact h' ⟨i, j, hne, h6⟩
    exact Set.not_nonempty_iff_eq_empty.mp h5
  have h_disj : ∀ (i j : α), i ≠ j → Disjoint (S i) (S j) := by
    intro i j hne; rw [Set.disjoint_iff_inter_eq_empty]; exact h_no_inter i j hne
  have h2 : μ (⋃ i, S i) = ∑' i, μ (S i) :=
    measure_iUnion (fun i j hne => h_disj i j hne) hS_meas
  rw [h2] at hC
  have h3 : ∑' i : α, μ (S i) ≥ ∑' i : α, lam := ENNReal.tsum_le_tsum hlam
  have h4 : ∑' i : α, lam = (Fintype.card α : ENNReal) * lam := by
    simp [tsum_fintype] <;> ring
  rw [h4] at h3; exact not_le.mpr h (le_trans h3 hC)

lemma exists_orthogonal_map_first {n : ℕ} (hn : 0 < n)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) :
    ∃ (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
      (e0 : EuclideanSpace ℝ (Fin n)),
      ‖e0‖ = 1 ∧ U e0 = v ∧
      ∀ i : Fin n, e0 i = if i = (⟨0, hn⟩ : Fin n) then (1 : ℝ) else (0 : ℝ) := by
  let i0 : Fin n := ⟨0, hn⟩
  let e0 : EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm (Pi.single i0 (1 : ℝ))
  have h_e0_coord : ∀ i : Fin n, e0 i = if i = i0 then (1 : ℝ) else (0 : ℝ) := by
    intro i
    have h_eq : (EuclideanSpace.equiv (Fin n) ℝ e0) i = e0 i :=
      PiLp.continuousLinearEquiv_apply 2 ℝ (fun _ => ℝ) e0 i
    rw [←h_eq]; simp [e0]
  have h1 : ∀ i : Fin n, |e0 i| ^ 2 = if i = i0 then (1 : ℝ) else (0 : ℝ) := by
    intro i; rw [h_e0_coord i]; split_ifs <;> norm_num
  have h_sum : ∑ i : Fin n, |e0 i| ^ 2 = 1 := by
    calc
      ∑ i : Fin n, |e0 i| ^ 2
        = ∑ i : Fin n, (if i = i0 then (1 : ℝ) else (0 : ℝ)) := by
          apply Finset.sum_congr rfl; intro i _; exact h1 i
      _ = 1 := by simp [Finset.sum_ite_eq', i0] <;> norm_num
  have h_abs : ∀ i : Fin n, ‖e0 i‖ = |e0 i| := by
    intro i; exact Real.norm_eq_abs (e0.ofLp i)
  have h_sum2 : ∑ i : Fin n, ‖e0 i‖ ^ 2 = ∑ i : Fin n, |e0 i| ^ 2 := by
    apply Finset.sum_congr rfl; intro i _; rw [h_abs i]
  have he0 : ‖e0‖ = 1 := by
    have h_norm : ‖e0‖ = Real.sqrt (∑ i : Fin n, ‖e0 i‖ ^ 2) := EuclideanSpace.norm_eq e0
    rw [h_norm, h_sum2, h_sum] <;> norm_num
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := (Submodule.span ℝ {e0 - v})ᗮ
  let U := K.reflection
  have h_main : U e0 = v := Submodule.reflection_sub (he0.trans hv.symm)
  exact ⟨U, e0, he0, h_main, h_e0_coord⟩

/-! ## Sum helper -/

lemma sum_fin_split {n : ℕ} (k : Fin n) (f : Fin n → ℝ) :
    ∑ i : Fin n, f i = f k + ∑ i : {i : Fin n // i ≠ k}, f i := by
  classical
  let s : Finset (Fin n) := Finset.univ.erase k
  have h_k_notin : k ∉ s := by simp [s]
  have h1 : ∑ i : Fin n, f i = f k + ∑ i ∈ s, f i := by
    have h2 : (insert k s : Finset (Fin n)) = Finset.univ := by
      simp [s, Finset.insert_erase]
    have h3 : ∑ i ∈ (insert k s : Finset (Fin n)), f i = f k + ∑ i ∈ s, f i :=
      Finset.sum_insert h_k_notin
    rw [←h3, h2]
  have h4 : ∑ (i : {i : Fin n // i ≠ k}), f i = ∑ i ∈ s, f i := by
    apply Finset.sum_bij' (fun (x : {i : Fin n // i ≠ k}) _ => (x : Fin n))
      (fun (y : Fin n) hy => ⟨y, by simpa [s, Finset.mem_erase] using hy⟩)
    <;> simp [s, Finset.mem_erase] <;> tauto
  rw [h1, h4]

/-! ## Proof-specific definitions and lemmas -/

def boxC {n : ℕ} (hn : 0 < n) (R : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  let i0 : Fin n := ⟨0, hn⟩
  {x | |x i0| ≤ 1 ∧ ∀ i : Fin n, i ≠ i0 → |x i| ≤ R}

lemma blichfeldt_n_dim {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) {N : ℕ}
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : MeasurableSet V)
    (h : ENNReal.ofReal ((N : ℝ) * δ^n) < volume V) :
    ∃ (p : Fin (N + 1) → EuclideanSpace ℝ (Fin n)),
      Function.Injective p ∧ (∀ i, p i ∈ V) ∧
      (∀ i j, ∃ (m : Fin n → ℤ),
        p i - p j = (EuclideanSpace.equiv (Fin n) ℝ).symm (fun k => δ * (m k : ℝ))) := by
  have h_main := BlichfeldtN.blichfeldt_lattice_points_n (hδ := hδ) (hA := hV) h
  rcases h_main with ⟨p, hp_inj, hp_in_V, hp_lattice⟩
  refine ⟨p, hp_inj, hp_in_V, ?_⟩
  intro i j
  have h1 : p i - p j ∈ BlichfeldtN.euclideanDyadicLattice (n := n) δ := hp_lattice i j
  have h2 : (EuclideanSpace.equiv (Fin n) ℝ) (p i - p j) ∈ BlichfeldtN.dyadicLattice (n := n) δ := by
    simpa [BlichfeldtN.euclideanDyadicLattice] using h1
  rcases h2 with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  have h3 : (EuclideanSpace.equiv (Fin n) ℝ) (p i - p j) = BlichfeldtN.latticePoint (n := n) δ m := hm.symm
  have h4 : BlichfeldtN.latticePoint (n := n) δ m = (fun k : Fin n => δ * (m k : ℝ)) := by
    funext k; simp [BlichfeldtN.latticePoint]
  have h5 : (EuclideanSpace.equiv (Fin n) ℝ) (p i - p j) = (fun k : Fin n => δ * (m k : ℝ)) := by
    rw [h3, h4]
  exact (EuclideanSpace.equiv (Fin n) ℝ).injective h5

lemma boxC_volume_grows {n : ℕ} (hn : 1 < n) (target : ENNReal) (htarget : target < ⊤) :
    ∃ (R : ℝ), 1 ≤ R ∧ target < volume (boxC (n := n) (by omega) R) := by
  let i0 : Fin n := ⟨0, by linarith⟩
  let i1 : Fin n := ⟨1, by linarith⟩
  have hi1_ne : i1 ≠ i0 := by simp [i0, i1] <;> omega
  let r : ℝ := ENNReal.toReal target
  have hr_nonneg : 0 ≤ r := by positivity
  have hr : target = ENNReal.ofReal r := by
    rw [ENNReal.ofReal_toReal htarget.ne]
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have h_e_mp : MeasurePreserving e volume volume := by
    let toLp_eq : MeasurableEquiv (EuclideanSpace ℝ (Fin n)) (Fin n → ℝ) :=
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm
    have h_eq : (e : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) = (toLp_eq : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) := by
      funext x; rfl
    have h : MeasurePreserving (toLp_eq : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) volume volume :=
      EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (ι := Fin n)
    rw [h_eq] at *
    exact h
  let a_R : ℝ → (Fin n → ℝ) := fun R => fun i => if i = i0 then -1 else -R
  let b_R : ℝ → (Fin n → ℝ) := fun R => fun i => if i = i0 then 1 else R
  have h_apply : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n), e x i = x i := by
    intro x i; rfl
  have h_box_image : ∀ (R : ℝ), 0 ≤ R → e '' (boxC (n := n) (by omega) R) = Set.Icc (a_R R) (b_R R) := by
    intro R hR_nonneg
    ext y
    simp only [Set.mem_image, Set.mem_Icc, boxC]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : |x i0| ≤ 1 := hx.1
      have h2 : ∀ i, i ≠ i0 → |x i| ≤ R := hx.2
      constructor
      · intro i
        by_cases hi : i = i0
        · rw [hi]
          have h4 : -1 ≤ x i0 := (abs_le.mp h1).1
          simpa [a_R, h_apply] using h4
        · have h3 : |x i| ≤ R := h2 i hi
          have h4 : -R ≤ x i := (abs_le.mp h3).1
          simpa [a_R, hi, h_apply] using h4
      · intro i
        by_cases hi : i = i0
        · rw [hi]
          have h4 : x i0 ≤ 1 := (abs_le.mp h1).2
          simpa [b_R, h_apply] using h4
        · have h3 : |x i| ≤ R := h2 i hi
          have h4 : x i ≤ R := (abs_le.mp h3).2
          simpa [b_R, hi, h_apply] using h4
    · rintro ⟨h1, h2⟩
      let x : EuclideanSpace ℝ (Fin n) := e.symm y
      have hxe : e x = y := e.apply_symm_apply y
      have h_y_eq : ∀ i, y i = x i := by
        intro i; have h := congr_fun hxe i; rw [h_apply x i] at h; exact h.symm
      refine ⟨x, ?_, hxe⟩
      constructor
      · have h5 : a_R R i0 ≤ y i0 := h1 i0
        have h6 : y i0 ≤ b_R R i0 := h2 i0
        have h71 : a_R R i0 = -1 := by simp [a_R]
        have h72 : b_R R i0 = 1 := by simp [b_R]
        have h7 : -1 ≤ x i0 := by
          rw [h71] at h5; rw [h_y_eq i0] at h5; exact h5
        have h8 : x i0 ≤ 1 := by
          rw [h72] at h6; rw [h_y_eq i0] at h6; exact h6
        exact abs_le.mpr ⟨h7, h8⟩
      · intro i hi
        have h5 : a_R R i ≤ y i := h1 i
        have h6 : y i ≤ b_R R i := h2 i
        have h71 : a_R R i = -R := by dsimp only [a_R]; rw [if_neg hi]
        have h72 : b_R R i = R := by dsimp only [b_R]; rw [if_neg hi]
        have h7 : -R ≤ x i := by
          rw [h71] at h5; rw [h_y_eq i] at h5; exact h5
        have h8 : x i ≤ R := by
          rw [h72] at h6; rw [h_y_eq i] at h6; exact h6
        exact abs_le.mpr ⟨h7, h8⟩
  have h_box_meas : ∀ (R : ℝ), MeasurableSet (boxC (n := n) (by omega) R) := by
    intro R
    have hproj : ∀ (i : Fin n), Measurable (fun x : EuclideanSpace ℝ (Fin n) => x i) := by
      intro i; fun_prop
    have h1 : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | |x i0| ≤ 1} := by
      have h_eq : {x : EuclideanSpace ℝ (Fin n) | |x i0| ≤ 1} =
          (fun x : EuclideanSpace ℝ (Fin n) => x i0) ⁻¹' Set.Icc (-1 : ℝ) 1 := by
        ext x; simp [abs_le] <;> constructor <;> intro h <;> exact ⟨h.1, h.2⟩
      rw [h_eq]; exact measurableSet_Icc.preimage (hproj i0)
    let s : Finset (Fin n) := Finset.univ.erase i0
    have h2 : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, i ≠ i0 → |x i| ≤ R} := by
      have h_eq : {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, i ≠ i0 → |x i| ≤ R} =
          ⋂ i ∈ s, {x : EuclideanSpace ℝ (Fin n) | |x i| ≤ R} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_coe]
        constructor
        · intro h i hi
          have hni : i ≠ i0 := by simpa [s, Finset.mem_erase] using hi
          exact h i hni
        · intro h i hni
          have hi : i ∈ s := by simp [s, Finset.mem_erase, hni]
          exact h i hi
      rw [h_eq]
      have h_each : ∀ i ∈ s, MeasurableSet {x : EuclideanSpace ℝ (Fin n) | |x i| ≤ R} := by
        intro i _
        have h_i_eq : {x : EuclideanSpace ℝ (Fin n) | |x i| ≤ R} =
            (fun x : EuclideanSpace ℝ (Fin n) => x i) ⁻¹' Set.Icc (-R) R := by
          ext x; simp [abs_le] <;> constructor <;> intro h <;> exact ⟨h.1, h.2⟩
        rw [h_i_eq]; exact measurableSet_Icc.preimage (hproj i)
      exact Finset.measurableSet_biInter s h_each
    exact h1.inter h2
  have h_vol : ∀ (R : ℝ), 0 ≤ R → volume (boxC (n := n) (by omega) R) = ∏ i : Fin n, ENNReal.ofReal ((b_R R i) - (a_R R i)) := by
    intro R hR_nonneg
    have h_meas : Measurable e := by fun_prop
    have h_meas_symm : Measurable e.symm := by fun_prop
    have h_image_preimage : e '' (boxC (n := n) (by omega) R) = e.symm ⁻¹' (boxC (n := n) (by omega) R) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have h_eq : e.symm (e x) = x := e.symm_apply_apply x
        rw [h_eq]
        exact hx
      · intro hy
        refine ⟨e.symm y, hy, ?_⟩
        exact e.apply_symm_apply y
    have h3 : MeasurableSet (e '' (boxC (n := n) (by omega) R)) := by
      rw [h_image_preimage]
      exact (h_box_meas R).preimage h_meas_symm
    have h1 : volume (e '' (boxC (n := n) (by omega) R)) = volume (boxC (n := n) (by omega) R) := by
      have h_map : volume = Measure.map e volume := by
        have h : MeasurePreserving e volume volume := h_e_mp
        exact Eq.symm h_e_mp.map_eq
      have h2 : volume (e '' (boxC (n := n) (by omega) R)) = Measure.map e volume (e '' (boxC (n := n) (by omega) R)) := by
        rw [h_map]
      rw [h2, Measure.map_apply h_meas h3]
      have h4 : e ⁻¹' (e '' (boxC (n := n) (by omega) R)) = boxC (n := n) (by omega) R := by
        ext x; simp
      rw [h4]
    rw [←h1, h_box_image R hR_nonneg, Real.volume_Icc_pi]
  have h_main : ∃ (R : ℝ), 1 ≤ R ∧ target < ENNReal.ofReal (2 * R) := by
    refine ⟨max 1 (r / 2 + 1), le_max_left _ _, ?_⟩
    have h5 : r < 2 * max 1 (r / 2 + 1) := by
      have h6 : max 1 (r / 2 + 1) ≥ r / 2 + 1 := le_max_right _ _
      linarith
    rw [hr]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr_nonneg |>.mpr h5
  rcases h_main with ⟨R, hR1, hR_lt⟩
  have hR_nonneg : 0 ≤ R := by linarith
  have h_i1_val : (b_R R i1) - (a_R R i1) = 2 * R := by
    simp [a_R, b_R, hi1_ne] <;> ring
  have h_all_ge1 : ∀ i : Fin n, (1 : ENNReal) ≤ ENNReal.ofReal ((b_R R i) - (a_R R i)) := by
    intro i
    by_cases hi : i = i0
    · rw [hi]; simp [a_R, b_R] <;> norm_num
    · have h : (b_R R i) - (a_R R i) = 2 * R := by simp [a_R, b_R, hi] <;> ring
      rw [h]
      have h' : (1 : ℝ) ≤ 2 * R := by linarith
      have h'' : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (2 * R) := ENNReal.ofReal_le_ofReal h'
      have h1 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
      rw [h1]; exact h''
  have h_ge : ENNReal.ofReal ((b_R R i1) - (a_R R i1)) ≤ ∏ i : Fin n, ENNReal.ofReal ((b_R R i) - (a_R R i)) := by
    let g : Fin n → ENNReal := fun i => ENNReal.ofReal ((b_R R i) - (a_R R i))
    have h_all : ∀ i : Fin n, 1 ≤ g i := h_all_ge1
    have h_prod_eq : g i1 * ∏ i ∈ Finset.univ.erase i1, g i = ∏ i : Fin n, g i :=
      Finset.mul_prod_erase Finset.univ g (by simp)
    rw [←h_prod_eq]
    have h_rest : 1 ≤ ∏ i ∈ Finset.univ.erase i1, g i := by
      apply Finset.one_le_prod
      intro i _
      exact h_all i
    exact le_mul_of_one_le_right' h_rest
  have h_final : target < volume (boxC (n := n) (by omega) R) := by
    calc volume (boxC (n := n) (by omega) R)
      = ∏ i : Fin n, ENNReal.ofReal ((b_R R i) - (a_R R i)) := h_vol R hR_nonneg
      _ ≥ ENNReal.ofReal ((b_R R i1) - (a_R R i1)) := h_ge
      _ = ENNReal.ofReal (2 * R) := by rw [h_i1_val]
      _ > target := hR_lt
  exact ⟨R, hR1, h_final⟩

lemma diam_pos {A : Set ℝ} (hA : IsCompact A) (hA_nonempty : A.Nonempty)
    {n : ℕ} {v : Fin n → ℝ} (hpos : 0 < volume (scaledSumset v A)) :
    0 < diam A := by
  by_contra h
  have h0 : diam A ≤ 0 := by simpa [not_lt] using h
  have h_nonneg : 0 ≤ diam A := diam_nonneg
  have h_eq : diam A = 0 := by linarith
  rcases hA_nonempty with ⟨a, ha⟩
  have hA_sub : A ⊆ {a} := by
    intro x hx
    have hBdd : Bornology.IsBounded A := IsCompact.isBounded hA
    have h_dist : dist x a ≤ diam A := Metric.dist_le_diam_of_mem hBdd hx ha
    rw [h_eq] at h_dist
    have h_nonneg2 : 0 ≤ dist x a := dist_nonneg
    have h_eq2 : dist x a = 0 := by linarith
    have h_x_eq : x = a := by simpa [dist_eq_zero] using h_eq2
    exact Set.mem_singleton_iff.mpr h_x_eq
  have hA_single : A = {a} := Set.Subset.antisymm hA_sub (Set.singleton_subset_iff.mpr ha)
  have h1 : scaledSumset v ({a} : Set ℝ) = {∑ i : Fin n, v i * a} := by
    ext x
    simp only [scaledSumset, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a', ha', rfl⟩
      have h_all : a' = fun (_ : Fin n) => a := by funext i; exact ha' i
      rw [h_all] <;> simp
    · intro hx
      rw [Set.mem_singleton_iff.mp hx]
      exact ⟨fun _ => a, fun _ => by simp, by simp⟩
  rw [hA_single] at hpos
  rw [h1] at hpos
  simp at hpos

lemma diam_in_difference {A : Set ℝ} (hA : IsCompact A) (hA_nonempty : A.Nonempty) :
    diam A ∈ A - A := by
  have hBdd : Bornology.IsBounded A := IsCompact.isBounded hA
  have h_diam_eq : diam A = sSup A - sInf A := Real.diam_eq hBdd
  have h_sup_mem : sSup A ∈ A := hA.sSup_mem hA_nonempty
  have h_inf_mem : sInf A ∈ A := hA.sInf_mem hA_nonempty
  rw [h_diam_eq]
  exact ⟨sSup A, h_sup_mem, sInf A, h_inf_mem, by ring⟩

lemma set_diff_add {S T : Set ℝ} :
    (S - S) + (T - T) = (S + T) - (S + T) := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rcases ha with ⟨s1, hs1, s2, hs2, rfl⟩
    rcases hb with ⟨t1, ht1, t2, ht2, rfl⟩
    have h1 : s1 + t1 ∈ S + T := Set.mem_add.mpr ⟨s1, hs1, t1, ht1, rfl⟩
    have h2 : s2 + t2 ∈ S + T := Set.mem_add.mpr ⟨s2, hs2, t2, ht2, rfl⟩
    exact Set.mem_sub.mpr ⟨s1 + t1, h1, s2 + t2, h2, by ring⟩
  · rintro h
    rcases Set.mem_sub.mp h with ⟨y, hy, z, hz, rfl⟩
    rcases hy with ⟨s1, hs1, t1, ht1, rfl⟩
    rcases hz with ⟨s2, hs2, t2, ht2, rfl⟩
    have h1 : s1 - s2 ∈ S - S := Set.mem_sub.mpr ⟨s1, hs1, s2, hs2, rfl⟩
    have h2 : t1 - t2 ∈ T - T := Set.mem_sub.mpr ⟨t1, ht1, t2, ht2, rfl⟩
    exact Set.mem_add.mpr ⟨s1 - s2, h1, t1 - t2, h2, by ring⟩

lemma iteratedDifference_eq {A : Set ℝ} {N : ℕ} :
    iteratedSumset ((productSet A 2) - (productSet A 2)) N =
    iteratedDifference (productSet A 2) N := by
  let S := productSet A 2
  have h_main : ∀ n : ℕ, iteratedSumset (S - S) n = iteratedDifference S n := by
    intro n
    induction n with
    | zero =>
      simp [iteratedSumset, iteratedDifference]
      <;> ext x <;> simp
    | succ n ih =>
      have h_ih' : iteratedSumset (S - S) n = (iteratedSumset S n) - (iteratedSumset S n) := by
        rw [ih] <;> rfl
      calc
        iteratedSumset (S - S) (n + 1)
          = (S - S) + iteratedSumset (S - S) n := by rfl
        _ = (S - S) + ((iteratedSumset S n) - (iteratedSumset S n)) := by rw [h_ih']
        _ = (S + iteratedSumset S n) - (S + iteratedSumset S n) := set_diff_add
        _ = iteratedSumset S (n + 1) - iteratedSumset S (n + 1) := by rfl
        _ = iteratedDifference S (n + 1) := by rfl
  exact h_main N

/-! ## Fin-based iterated sumset (for main_containment proof) -/

/-- Sum of N elements from S, using Fin-indexed tuples. -/
def iteratedSumsetFin (S : Set ℝ) (N : ℕ) : Set ℝ :=
  {x | ∃ (f : Fin N → ℝ), (∀ i, f i ∈ S) ∧ ∑ i : Fin N, f i = x}

def productSet2 (A : Set ℝ) : Set ℝ := Set.image2 (· * ·) A A

lemma productSet2_eq {A : Set ℝ} : productSet2 A = productSet A 2 := by
  ext x
  simp only [productSet2, productSet, Set.mem_image2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    let f : Fin 2 → ℝ := fun i => if i = 0 then a else b
    have hf : ∀ i, f i ∈ A := by
      intro i
      by_cases h : i = 0
      · rw [h]; simpa [f] using ha
      · have h' : i = 1 := by omega
        rw [h']; simpa [f] using hb
    have hprod : ∏ i : Fin 2, f i = a * b := by
      rw [Fin.prod_univ_two] <;> simp [f] <;> ring
    exact ⟨f, hf, hprod.symm⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f 0, hf 0, f 1, hf 1, by simp [Fin.prod_univ_two]⟩

lemma iteratedSumsetFin_succ {S : Set ℝ} {n : ℕ} :
    iteratedSumsetFin S (n + 1) = S + iteratedSumsetFin S n := by
  ext x
  constructor
  · rintro ⟨f, hf, hsum⟩
    let g : Fin n → ℝ := fun i => f i.succ
    have hg : ∀ i, g i ∈ S := fun i => hf i.succ
    have h_eq : ∑ i : Fin (n + 1), f i = f 0 + ∑ i : Fin n, g i := by
      rw [Fin.sum_univ_succ] <;> rfl
    rw [hsum] at h_eq
    exact ⟨f 0, hf 0, ∑ i : Fin n, g i, ⟨g, hg, rfl⟩, h_eq.symm⟩
  · rintro ⟨x0, hx0, y, ⟨g, hg, rfl⟩, rfl⟩
    let f : Fin (n + 1) → ℝ := Fin.cons x0 g
    have hf : ∀ i, f i ∈ S := by
      intro i
      by_cases h : i = 0
      · rw [h]; simpa [f, Fin.cons] using hx0
      · have h_i_succ : ∃ (j : Fin n), i = j.succ := by
          refine ⟨i.pred h, (Fin.succ_pred i h).symm⟩
        rcases h_i_succ with ⟨j, rfl⟩
        simpa [f, Fin.cons] using hg j
    have hsum : ∑ i : Fin (n + 1), f i = x0 + ∑ i : Fin n, g i := by
      rw [Fin.sum_univ_succ] <;> rfl
    exact ⟨f, hf, hsum⟩

lemma iteratedSumsetFin_eq_recursive {S : Set ℝ} {N : ℕ} :
    iteratedSumsetFin S N = iteratedSumset S N := by
  induction N with
  | zero =>
    ext x
    simp [iteratedSumsetFin, iteratedSumset]
    <;> aesop
  | succ N ih =>
    calc
      iteratedSumsetFin S (N + 1)
        = S + iteratedSumsetFin S N := iteratedSumsetFin_succ
    _ = S + iteratedSumset S N := by rw [ih]
    _ = iteratedSumset S (N + 1) := by rfl

lemma iteratedSumsetFin_mono {S : Set ℝ} {k l : ℕ} (h : k ≤ l)
    (h0 : (0 : ℝ) ∈ S) :
    iteratedSumsetFin S k ⊆ iteratedSumsetFin S l := by
  induction' h with l h ih
  · exact subset_refl _
  · calc
      iteratedSumsetFin S k ⊆ iteratedSumsetFin S l := ih
      _ ⊆ iteratedSumsetFin S (l + 1) := by
        rw [iteratedSumsetFin_succ]
        intro x hx
        exact ⟨0, h0, x, hx, by ring⟩

lemma iteratedSumsetFin_add {S : Set ℝ} {k l : ℕ} {x y : ℝ}
    (hx : x ∈ iteratedSumsetFin S k) (hy : y ∈ iteratedSumsetFin S l) :
    x + y ∈ iteratedSumsetFin S (k + l) := by
  have h_main : ∀ (l' : ℕ), ∀ (y' : ℝ), y' ∈ iteratedSumsetFin S l' →
      x + y' ∈ iteratedSumsetFin S (k + l') := by
    intro l'
    induction l' with
    | zero =>
      intro y' hy'
      have hy0 : y' = 0 := by
        rcases hy' with ⟨f, hf, hsum⟩
        exact hsum.symm
      rw [hy0]
      simpa using hx
    | succ l' ih =>
      intro y' hy'
      rw [iteratedSumsetFin_succ] at hy'
      rcases hy' with ⟨y0, hy0, z, hz, rfl⟩
      have h_ih' : x + z ∈ iteratedSumsetFin S (k + l') := ih z hz
      have h_idx : k + (l' + 1) = (k + l') + 1 := by omega
      rw [h_idx, iteratedSumsetFin_succ]
      have h_comm : x + (y0 + z) = y0 + (x + z) := by ring
      rw [h_comm]
      exact ⟨y0, hy0, x + z, h_ih', by ring⟩
  exact h_main l y hy

lemma single_in_iteratedFin {S : Set ℝ} {x : ℝ} (hx : x ∈ S) :
    x ∈ iteratedSumsetFin S 1 := by
  let f : Fin 1 → ℝ := fun _ => x
  have hf : ∀ i, f i ∈ S := by intro i; exact hx
  have hsum : ∑ i : Fin 1, f i = x := by
    rw [Fin.sum_univ_one] <;> rfl
  exact ⟨f, hf, hsum⟩

lemma zero_in_productDiff {A : Set ℝ} (hA : A.Nonempty) :
    (0 : ℝ) ∈ productSet2 A - productSet2 A := by
  rcases hA with ⟨a, ha⟩
  have h1 : a * a ∈ productSet2 A := ⟨a, ha, a, ha, by ring⟩
  exact ⟨a * a, h1, a * a, h1, by ring⟩

lemma productDiff_neg_closed {A : Set ℝ} {x : ℝ}
    (hx : x ∈ productSet2 A - productSet2 A) :
    -x ∈ productSet2 A - productSet2 A := by
  rcases hx with ⟨u, hu, v, hv, rfl⟩
  exact ⟨v, hv, u, hu, by ring⟩

lemma diff_smul_in_productDiff {A : Set ℝ} {u v x : ℝ}
    (hu : u ∈ A) (hv : v ∈ A) (hx : x ∈ A) :
    (u - v) * x ∈ productSet2 A - productSet2 A := by
  have h1 : u * x ∈ productSet2 A := ⟨u, hu, x, hx, by ring⟩
  have h2 : v * x ∈ productSet2 A := ⟨v, hv, x, hx, by ring⟩
  exact ⟨u * x, h1, v * x, h2, by ring⟩

lemma two_c_x_in_sumset2Fin {A : Set ℝ} {c x : ℝ}
    (hc : c ∈ A - A) (hx : x ∈ A) :
    2 * c * x ∈ iteratedSumsetFin (productSet2 A - productSet2 A) 2 := by
  rcases hc with ⟨p, hp, q, hq, h_eq⟩
  let Sdiff := productSet2 A - productSet2 A
  have h1 : (p - q) * x ∈ Sdiff := diff_smul_in_productDiff hp hq hx
  let f : Fin 2 → ℝ := fun _ => (p - q) * x
  have hf : ∀ i, f i ∈ Sdiff := by intro i; exact h1
  have hsum : ∑ i : Fin 2, f i = 2 * ((p - q) * x) := by
    rw [Fin.sum_univ_two] <;> ring
  have h_eq2 : p - q = c := by simpa using h_eq
  have h_final : 2 * ((p - q) * x) = 2 * c * x := by
    rw [h_eq2] <;> ring
  exact ⟨f, hf, hsum.trans h_final⟩

lemma nat_multiple_in_iteratedFin {A : Set ℝ} {c x : ℝ} {m : ℕ}
    (hc : c ∈ A - A) (hx : x ∈ A) :
    2 * c * (m : ℝ) * x ∈ iteratedSumsetFin (productSet2 A - productSet2 A) (2 * m) := by
  let Sdiff := productSet2 A - productSet2 A
  induction m with
  | zero =>
    let f : Fin 0 → ℝ := fun i => Fin.elim0 i
    have hf : ∀ i, f i ∈ Sdiff := by intro i; exact Fin.elim0 i
    have hsum : ∑ i : Fin 0, f i = 0 := by simp
    have h_final : 2 * c * (0 : ℕ) * x = 0 := by ring
    rw [h_final]
    exact ⟨f, hf, hsum⟩
  | succ m ih =>
    have h3 : 2 * c * ((m + 1 : ℕ) : ℝ) * x =
        2 * c * (m : ℝ) * x + 2 * c * x := by
      simp [Nat.cast_add, Nat.cast_one] <;> ring
    rw [h3]
    have h5 : 2 * c * x ∈ iteratedSumsetFin Sdiff 2 := two_c_x_in_sumset2Fin hc hx
    have h6 := iteratedSumsetFin_add ih h5
    have h_idx : (2 * m + 2) = 2 * (m + 1) := by omega
    rwa [h_idx] at h6

lemma int_multiple_in_iteratedFin {A : Set ℝ} {c x : ℝ} {m : ℤ}
    (hc : c ∈ A - A) (hx : x ∈ A) :
    2 * c * (m : ℝ) * x ∈ iteratedSumsetFin (productSet2 A - productSet2 A) (2 * m.natAbs) := by
  let Sdiff := productSet2 A - productSet2 A
  by_cases hm : 0 ≤ m
  · have h2 : (m : ℤ) = ↑(m.natAbs) := by exact Int.eq_natAbs_of_nonneg hm
    have hme : (m : ℝ) = ↑(m.natAbs) := by
      exact congr_arg (fun z : ℤ => (z : ℝ)) h2
    rw [hme]
    exact nat_multiple_in_iteratedFin hc hx
  · have hneg : m < 0 := by linarith
    have h_pos : 2 * c * (↑(m.natAbs) : ℝ) * x ∈
        iteratedSumsetFin Sdiff (2 * m.natAbs) :=
      nat_multiple_in_iteratedFin hc hx
    have h3 : (m.natAbs : ℤ) = -m := by
      have h4 : 0 ≤ -m := by linarith
      have h5 : ((-m).natAbs : ℤ) = -m := Int.natAbs_of_nonneg h4
      have h6 : m.natAbs = (-m).natAbs := by exact Eq.symm (Int.natAbs_neg m)
      rw [h6]; exact h5
    have h3' : (m.natAbs : ℝ) = -(m : ℝ) := by
      have h4 : ((m.natAbs : ℤ) : ℝ) = ((-m : ℤ) : ℝ) := by rw [h3]
      have h5 : ((-m : ℤ) : ℝ) = -((m : ℤ) : ℝ) := by rw [Int.cast_neg]
      rw [h5] at h4; simpa using h4
    have h1 : (m : ℝ) = -↑(m.natAbs) := by linarith
    have h_eq : 2 * c * (m : ℝ) * x = -(2 * c * (↑(m.natAbs) : ℝ) * x) := by
      rw [h1] <;> ring
    rw [h_eq]
    rcases h_pos with ⟨f, hf, hsum⟩
    let g : Fin (2 * m.natAbs) → ℝ := fun i => -(f i)
    have hg1 : ∀ i, g i ∈ Sdiff := by
      intro i; exact productDiff_neg_closed (hf i)
    have hg2 : ∑ i, g i = -(∑ i, f i) := by
      rw [Finset.sum_neg_distrib] <;> rfl
    rw [hsum] at hg2
    exact ⟨g, hg1, hg2⟩

lemma iteratedDifferenceFin_eq {A : Set ℝ} {N : ℕ} :
    iteratedSumsetFin (productSet2 A - productSet2 A) N =
    Set.image2 (· - ·) (iteratedSumsetFin (productSet2 A) N) (iteratedSumsetFin (productSet2 A) N) := by
  let S := productSet2 A
  have h_main : ∀ n : ℕ,
      iteratedSumsetFin (S - S) n =
      iteratedSumsetFin S n - iteratedSumsetFin S n := by
    intro n
    induction n with
    | zero =>
      ext x
      simp [iteratedSumsetFin]
      <;> aesop
    | succ n ih =>
      calc
        iteratedSumsetFin (S - S) (n + 1)
          = (S - S) + iteratedSumsetFin (S - S) n := iteratedSumsetFin_succ
        _ = (S - S) + (iteratedSumsetFin S n - iteratedSumsetFin S n) := by rw [ih]
        _ = (S + iteratedSumsetFin S n) - (S + iteratedSumsetFin S n) := set_diff_add
        _ = iteratedSumsetFin S (n + 1) - iteratedSumsetFin S (n + 1) := by
          rw [iteratedSumsetFin_succ]
  exact h_main N

lemma main_containment {A : Set ℝ} (hA : IsCompact A) (hA_nonempty : A.Nonempty)
    {n : ℕ} (a b z' : Fin n → ℝ) (d : ℝ)
    (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ A)
    (k : Fin n) (ℓ_vec : Fin n → ℝ)
    (hz' : ∀ i, z' i = b i + ℓ_vec i) (hd : d = z' k - a k)
    (hℓ : ∀ i, ∃ (m : ℤ), ℓ_vec i = 2 * diam A * (m : ℝ))
    (h_diam_in_diff : diam A ∈ A - A) :
    ∃ (N' : ℕ), 0 < N' ∧
      (∀ (i : {i : Fin n // i ≠ k}),
        ((a i - z' i) • A) + (d • A) ⊆
          iteratedSumset ((productSet A 2) - (productSet A 2)) N') ∧
      iteratedSumset ((productSet A 2) - (productSet A 2)) N' =
        iteratedDifference (productSet A 2) N' := by
  let c := diam A
  have hc_in_diff : c ∈ A - A := h_diam_in_diff
  choose m hm using hℓ
  let M : ℕ := Finset.sup Finset.univ (fun i : Fin n => (m i).natAbs)
  let N' : ℕ := 2 + 4 * M
  have hN'_pos : (0 : ℕ) < N' := by
    dsimp only [N'] <;> omega
  have hM_ge : ∀ i : Fin n, (m i).natAbs ≤ M := by
    intro i
    have h_univ : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
    have h : (m i).natAbs ≤ Finset.sup (Finset.univ : Finset (Fin n)) (fun j : Fin n => (m j).natAbs) :=
      Finset.le_sup (s := (Finset.univ : Finset (Fin n))) (f := fun j : Fin n => (m j).natAbs) h_univ
    exact h
  let Sdiff2 := productSet2 A - productSet2 A
  have h0_in_Sdiff2 : (0 : ℝ) ∈ Sdiff2 := zero_in_productDiff hA_nonempty
  have h_mono : ∀ (k l : ℕ), k ≤ l → iteratedSumsetFin Sdiff2 k ⊆ iteratedSumsetFin Sdiff2 l :=
    fun k l h => iteratedSumsetFin_mono h h0_in_Sdiff2
  have h_pset_eq : productSet2 A = productSet A 2 := productSet2_eq
  have h_main_goal : ∀ (i : {i : Fin n // i ≠ k}),
      ((a i - z' i) • A) + (d • A) ⊆ iteratedSumsetFin Sdiff2 N' := by
    intro i
    intro w hw
    have h_add : ∃ (u : ℝ), u ∈ ((a i - z' i) • A) ∧ ∃ (v : ℝ), v ∈ (d • A) ∧ u + v = w := by
      simpa [Set.mem_add] using hw
    rcases h_add with ⟨u, hu, v, hv, h_uv⟩
    have h_eq1 : w = u + v := h_uv.symm
    have h_smul1 : ∃ (x : ℝ), x ∈ A ∧ (a i - z' i) * x = u := by
      simpa [Set.mem_smul_set] using hu
    rcases h_smul1 with ⟨x, hx, h_ux⟩
    have h_eq2 : u = (a i - z' i) * x := h_ux.symm
    have h_smul2 : ∃ (y : ℝ), y ∈ A ∧ d * y = v := by
      simpa [Set.mem_smul_set] using hv
    rcases h_smul2 with ⟨y, hy, h_vy⟩
    have h_eq3 : v = d * y := h_vy.symm
    rw [h_eq1, h_eq2, h_eq3]
    have h_expand : (a i - z' i) * x + d * y =
        (a i - b i) * x + (b k - a k) * y - ℓ_vec i * x + ℓ_vec k * y := by
      simp [hz', hd] <;> ring
    rw [h_expand]
    have h1 : (a i - b i) * x ∈ Sdiff2 := diff_smul_in_productDiff (ha i) (hb i) hx
    have h2 : (b k - a k) * y ∈ Sdiff2 := diff_smul_in_productDiff (hb k) (ha k) hy
    have h12 : (a i - b i) * x + (b k - a k) * y ∈ iteratedSumsetFin Sdiff2 2 :=
      iteratedSumsetFin_add (single_in_iteratedFin h1) (single_in_iteratedFin h2)
    have h3 : -ℓ_vec i * x ∈ iteratedSumsetFin Sdiff2 (2 * (m i).natAbs) := by
      have h31 : ℓ_vec i * x ∈ iteratedSumsetFin Sdiff2 (2 * (m i).natAbs) := by
        rw [hm i]
        exact int_multiple_in_iteratedFin hc_in_diff hx
      rcases h31 with ⟨f, hf, hsum⟩
      let g : Fin (2 * (m i).natAbs) → ℝ := fun j => -(f j)
      have hg1 : ∀ j, g j ∈ Sdiff2 := by intro j; exact productDiff_neg_closed (hf j)
      have hg2 : ∑ j, g j = -(∑ j, f j) := by
        rw [Finset.sum_neg_distrib] <;> rfl
      rw [hsum] at hg2
      have hg3 : ∑ (j : Fin (2 * (m i).natAbs)), g j = -ℓ_vec i * x := by
        rw [hg2] <;> ring
      exact ⟨g, hg1, hg3⟩
    have h4 : ℓ_vec k * y ∈ iteratedSumsetFin Sdiff2 (2 * (m k).natAbs) := by
      rw [hm k]
      exact int_multiple_in_iteratedFin hc_in_diff hy
    have h123 : (a i - b i) * x + (b k - a k) * y - ℓ_vec i * x ∈
        iteratedSumsetFin Sdiff2 (2 + 2 * (m i).natAbs) := by
      have h_eq : (a i - b i) * x + (b k - a k) * y - ℓ_vec i * x =
          ((a i - b i) * x + (b k - a k) * y) + (-ℓ_vec i * x) := by ring
      rw [h_eq]
      exact iteratedSumsetFin_add h12 h3
    have h_final : (a i - b i) * x + (b k - a k) * y - ℓ_vec i * x + ℓ_vec k * y ∈
        iteratedSumsetFin Sdiff2 (2 + 2 * (m i).natAbs + 2 * (m k).natAbs) :=
      iteratedSumsetFin_add h123 h4
    have h_le : 2 + 2 * (m i).natAbs + 2 * (m k).natAbs ≤ N' := by
      dsimp only [N']
      have h5 : (m i).natAbs ≤ M := hM_ge i
      have h6 : (m k).natAbs ≤ M := hM_ge k
      omega
    exact h_mono _ _ h_le h_final
  have h_fin_eq1 : iteratedSumsetFin Sdiff2 N' =
      iteratedSumset ((productSet A 2) - (productSet A 2)) N' := by
    have hSdiff_eq : Sdiff2 = (productSet A 2) - (productSet A 2) := by
      have h1 : Sdiff2 = productSet2 A - productSet2 A := rfl
      rw [h1]
      exact congr_arg (fun x => x - x) h_pset_eq
    rw [hSdiff_eq, iteratedSumsetFin_eq_recursive]
  have h_fin_eq2 : iteratedSumsetFin (productSet2 A) N' = iteratedSumset (productSet A 2) N' := by
    rw [h_pset_eq, iteratedSumsetFin_eq_recursive]
  have h_ideq : iteratedSumset ((productSet A 2) - (productSet A 2)) N' =
      iteratedDifference (productSet A 2) N' := by
    have h := iteratedDifferenceFin_eq (A := A) (N := N')
    rw [h_fin_eq1] at *
    <;> simpa [iteratedDifference, h_fin_eq2] using h
  refine ⟨N', hN'_pos, ?_, h_ideq⟩
  intro i
  have h := h_main_goal i
  rw [h_fin_eq1] at *
  exact h

lemma volume_smul_set {c : ℝ} (hc : c ≠ 0) {S : Set ℝ} (hS : MeasurableSet S) :
    volume (c • S) = ENNReal.ofReal (|c|) * volume S := by
  have h2 : (fun y : ℝ => c⁻¹ * y) ⁻¹' S = c • S := by
    ext z
    simp [Set.mem_preimage, Set.mem_smul_set]
    <;> constructor
    · intro hz
      refine ⟨c⁻¹ * z, ?_, ?_⟩
      · simpa using hz
      · field_simp [hc] <;> ring
    · rintro ⟨s, hs, rfl⟩
      have h_goal : c⁻¹ * (c * s) = s := by field_simp [hc] <;> ring
      rw [h_goal]
      exact hs
  have h3 : volume ((fun y : ℝ => c⁻¹ * y) ⁻¹' S) =
      ENNReal.ofReal |(c⁻¹)⁻¹| * volume S :=
    Real.volume_preimage_mul_left (inv_ne_zero hc) S
  have h4 : |(c⁻¹)⁻¹| = |c| := by
    field_simp [hc] <;> rfl
  rw [←h2, h3, h4]

lemma scaledSumset_diam_bound {A : Set ℝ} (hA : IsCompact A)
    {n : ℕ} {v : Fin n → ℝ} (hv : ∀ i, v i ∈ Set.Icc (1/2) 1)
    (s1 s2 : ℝ) (hs1 : s1 ∈ scaledSumset v A) (hs2 : s2 ∈ scaledSumset v A) :
    |s1 - s2| ≤ (n : ℝ) * diam A := by
  rcases hs1 with ⟨a1, ha1, rfl⟩
  rcases hs2 with ⟨a2, ha2, rfl⟩
  have hBdd : Bornology.IsBounded A := IsCompact.isBounded hA
  have h_each : ∀ i, |v i * (a1 i - a2 i)| ≤ diam A := by
    intro i
    have hvi1 : 0 ≤ v i := by have h := (hv i).1; linarith
    have hvi2 : v i ≤ 1 := (hv i).2
    have hvi_abs : |v i| ≤ 1 := by rw [abs_of_nonneg hvi1] <;> linarith
    have h_dist : |a1 i - a2 i| ≤ diam A := by
      have h : dist (a1 i) (a2 i) ≤ diam A := Metric.dist_le_diam_of_mem hBdd (ha1 i) (ha2 i)
      simpa [dist_eq_norm, Real.norm_eq_abs] using h
    calc |v i * (a1 i - a2 i)|
      = |v i| * |a1 i - a2 i| := by rw [abs_mul]
    _ ≤ 1 * |a1 i - a2 i| := by gcongr
    _ ≤ diam A := by linarith
  have h_main : |(∑ i : Fin n, v i * a1 i) - (∑ i : Fin n, v i * a2 i)| ≤
      ∑ i : Fin n, |v i * (a1 i - a2 i)| := by
    have h : |∑ i : Fin n, (v i * a1 i - v i * a2 i)| ≤ ∑ i : Fin n, |v i * a1 i - v i * a2 i| :=
      Finset.abs_sum_le_sum_abs _ _
    have h' : ∑ i : Fin n, (v i * a1 i - v i * a2 i) =
        (∑ i : Fin n, v i * a1 i) - (∑ i : Fin n, v i * a2 i) := by
      rw [Finset.sum_sub_distrib]
    rw [h'] at h
    simpa [mul_sub] using h
  calc |(∑ i : Fin n, v i * a1 i) - (∑ i : Fin n, v i * a2 i)|
    ≤ ∑ i : Fin n, |v i * (a1 i - a2 i)| := h_main
  _ ≤ ∑ i : Fin n, diam A := Finset.sum_le_sum (fun i _ => h_each i)
  _ = (n : ℝ) * diam A := by simp [Finset.sum_const] <;> ring

/-! ## Main theorem -/

theorem expansion_lemma {A : Set ℝ} (hA : IsCompact A) (hA_nonempty : A.Nonempty)
    {n : ℕ} (hn : 2 ≤ n)
    {v : Fin n → ℝ} (hv : ∀ i, v i ∈ Set.Icc (1/2) 1)
    (hpos : 0 < volume (scaledSumset v A)) :
    ∃ (N : ℕ), 0 < N ∧
      ∃ (j : Fin n),
        volume (scaledSumsetExcept v j (iteratedDifference (productSet A 2) N))
          ≥ ENNReal.ofReal (diam A) * volume (scaledSumset v A) := by
  let S := scaledSumset v A
  let π : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ∑ i : Fin n, v i * x i
  have hS_compact : IsCompact S := scaledSumset_compact hA
  have hS_meas : MeasurableSet S := hS_compact.measurableSet
  have hS_nonempty : S.Nonempty := by
    obtain ⟨a, ha⟩ := hA_nonempty
    exact ⟨∑ i : Fin n, v i * a, ⟨fun _ => a, fun _ => ha, rfl⟩⟩
  let volS : ENNReal := volume S
  have hvolS_pos : 0 < volS := hpos
  have hvolS_lt_top : volS < ⊤ := hS_compact.measure_lt_top

  have h_diam_pos : 0 < diam A := diam_pos hA hA_nonempty (hpos := hpos)
  let c := diam A
  have h_diam_in_diff : c ∈ A - A := diam_in_difference hA hA_nonempty

  let v_eucl : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm v
  let i0 : Fin n := ⟨0, by linarith⟩
  have h_v_norm_pos : 0 < ‖v_eucl‖ := by
    have h1 : v_eucl i0 = v i0 := by
      simp [v_eucl] <;> rfl
    have h2 : 0 < v i0 := by have h := (hv i0).1; linarith
    have h3 : 0 < |v_eucl i0| := by
      have h31 : v_eucl i0 = v i0 := h1
      rw [h31]
      exact abs_pos.mpr (ne_of_gt h2)
    have h4 : 0 < ‖v_eucl i0‖ := by
      simpa [Real.norm_eq_abs] using h3
    have h5 : 0 < ‖v_eucl‖ := by
      have h6 : ‖v_eucl i0‖ ≤ ‖v_eucl‖ := by
        exact PiLp.norm_apply_le v_eucl i0
      exact lt_of_lt_of_le h4 h6
    exact h5
  let v_norm := ‖v_eucl‖
  let C_val : ℝ := (n : ℝ) * c + 2 * v_norm
  have hC_val_pos : 0 < C_val := by positivity

  have hvolS_real_pos : 0 < ENNReal.toReal volS := by
    have h : 0 < volS ∧ volS < ⊤ := ⟨hvolS_pos, hvolS_lt_top⟩
    exact ENNReal.toReal_pos_iff.mpr h

  have hN_real : ∃ (N : ℕ), (N + 1 : ℝ) * ENNReal.toReal volS > C_val := by
    let x := ENNReal.toReal volS
    have hx_pos : 0 < x := hvolS_real_pos
    have h : ∃ (N : ℕ), C_val / x < (N : ℝ) := exists_nat_gt (C_val / x)
    rcases h with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    have h2 : C_val / x < (N : ℝ) := hN
    have h3 : C_val < (N : ℝ) * x := by
      calc C_val
        = (C_val / x) * x := by field_simp [hx_pos.ne'] <;> ring
      _ < (N : ℝ) * x := by gcongr
    have h4 : (N + 1 : ℝ) * x > C_val := by
      have h5 : ((N + 1 : ℝ) * x) > (N : ℝ) * x := by
        have h6 : 0 < x := hx_pos
        nlinarith
      linarith
    have h4' : (N + 1 : ℝ) * ENNReal.toReal volS > C_val := by
      simpa [show x = ENNReal.toReal volS from rfl] using h4
    exact h4'
  rcases hN_real with ⟨N, hN_ineq_real⟩

  have hN_ineq : (N + 1 : ENNReal) * volS > ENNReal.ofReal C_val := by
    have h1 : ENNReal.ofReal ((N + 1 : ℝ) * ENNReal.toReal volS) =
        (N + 1 : ENNReal) * volS := by
      have h2 : ENNReal.ofReal (ENNReal.toReal volS) = volS :=
        ENNReal.ofReal_toReal hvolS_lt_top.ne
      have h3 : ENNReal.ofReal ((N + 1 : ℝ) * ENNReal.toReal volS) =
          ENNReal.ofReal (N + 1 : ℝ) * ENNReal.ofReal (ENNReal.toReal volS) := by
        rw [ENNReal.ofReal_mul] <;> positivity
      rw [h3, h2] <;> norm_cast
    rw [←h1]
    have h5 : ENNReal.ofReal C_val < ENNReal.ofReal ((N + 1 : ℝ) * ENNReal.toReal volS) := by
      have h6 : C_val < (N + 1 : ℝ) * ENNReal.toReal volS := hN_ineq_real
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr h6
    exact h5

  let δ := 2 * c
  have hδ_pos : 0 < δ := by positivity

  have hR : ∃ (R : ℝ), 1 ≤ R ∧ ENNReal.ofReal ((N : ℝ) * δ^n) < volume (boxC (n := n) (by omega) R) :=
    boxC_volume_grows (by linarith) (ENNReal.ofReal ((N : ℝ) * δ^n)) ENNReal.ofReal_lt_top
  rcases hR with ⟨R, hR1, hR_vol⟩

  let w : EuclideanSpace ℝ (Fin n) := (1 / v_norm) • v_eucl
  have hw_norm : ‖w‖ = 1 := by
    have h1 : ‖w‖ = |(1 / v_norm : ℝ)| * ‖v_eucl‖ := norm_smul (1 / v_norm) v_eucl
    rw [h1]
    have h2 : |(1 / v_norm : ℝ)| = 1 / v_norm := by
      have h_pos2 : 0 < (1 / v_norm : ℝ) := by positivity
      rw [abs_of_pos h_pos2]
    rw [h2]
    have h3 : (1 / v_norm) * ‖v_eucl‖ = 1 := by
      have h4 : ‖v_eucl‖ = v_norm := rfl
      rw [h4]
      have h5 : (1 / v_norm) * v_norm = 1 := by
        have hnz : v_norm ≠ 0 := h_v_norm_pos.ne'
        exact one_div_mul_cancel hnz
      exact h5
    exact h3

  rcases exists_orthogonal_map_first (by linarith) w hw_norm with ⟨U, e0, he0, hUe0, h_e0_coord⟩

  let V := U '' (boxC (n := n) (by omega) R)
  have hboxC_meas : MeasurableSet (boxC (n := n) (by omega) R) := by
    have h_closed1 : IsClosed {x : EuclideanSpace ℝ (Fin n) | |x i0| ≤ 1} := by
      exact isClosed_le (continuous_abs.comp (by fun_prop)) continuous_const
    let s : Finset (Fin n) := Finset.univ.erase i0
    have h_closed2 : IsClosed {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, i ≠ i0 → |x i| ≤ R} := by
      have h_eq : {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, i ≠ i0 → |x i| ≤ R} =
          ⋂ i ∈ s, {x : EuclideanSpace ℝ (Fin n) | |x i| ≤ R} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_coe]
        constructor
        · intro h i hi
          have hni : i ≠ i0 := by simpa [s, Finset.mem_erase] using hi
          exact h i hni
        · intro h i hni
          have hi : i ∈ s := by simp [s, Finset.mem_erase, hni]
          exact h i hi
      rw [h_eq]
      exact isClosed_biInter (h := fun i _ =>
        isClosed_le (continuous_abs.comp (by fun_prop)) continuous_const)
    have h_closed : IsClosed (boxC (n := n) (by omega) R) := h_closed1.inter h_closed2
    exact h_closed.measurableSet
  have hU_meas : Measurable U := U.continuous.measurable
  have hU_symm_meas : Measurable U.symm := U.symm.continuous.measurable
  have hV_preimage : V = U.symm ⁻¹' (boxC (n := n) (by omega) R) := by
    ext y
    simp only [V, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h : U.symm (U x) = x := U.symm_apply_apply x
      rw [h] <;> exact hx
    · intro hy
      refine ⟨U.symm y, hy, ?_⟩
      exact U.apply_symm_apply y
  have hV_meas : MeasurableSet V := by
    rw [hV_preimage]
    exact hboxC_meas.preimage hU_symm_meas
  have hU_mp : MeasurePreserving U volume volume := by exact LinearIsometryEquiv.measurePreserving U
  have hV_vol : volume V = volume (boxC (n := n) (by omega) R) := by
    have h3 : U ⁻¹' V = boxC (n := n) (by omega) R := by
      ext x; simp [V]
    have h4 : volume (U ⁻¹' V) = volume V := hU_mp.measure_preimage hV_meas.nullMeasurableSet
    rw [h3] at h4
    exact h4.symm

  have hπV : ∀ y ∈ V, |π y| ≤ v_norm := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h_symm : U.symm v_eucl = v_norm • e0 := by
      have h3 : U e0 = (1 / v_norm) • v_eucl := hUe0
      have h4 : U.symm (U e0) = e0 := U.symm_apply_apply e0
      have h5 : U.symm ((1 / v_norm) • v_eucl) = e0 := by
        rw [←h3] <;> exact h4
      have h6 : (1 / v_norm) • U.symm v_eucl = e0 := by
        simpa [map_smul] using h5
      have h9 : v_norm • ((1 / v_norm) • U.symm v_eucl) = U.symm v_eucl := by
        rw [smul_smul]
        have h10 : v_norm * (1 / v_norm) = 1 := by
          have hnz : v_norm ≠ 0 := h_v_norm_pos.ne'
          exact mul_one_div_cancel hnz
        rw [h10, one_smul]
      have h11 : v_norm • ((1 / v_norm) • U.symm v_eucl) = v_norm • e0 := by rw [h6]
      rw [h9] at h11
      exact h11
    have h_inner_eq : ∀ (a b : EuclideanSpace ℝ (Fin n)), inner ℝ a b = ∑ i : Fin n, a i * b i := by
      intro a b
      have h1 : inner ℝ a b = ∑ i : Fin n, inner ℝ (a i) (b i) := by
        exact PiLp.inner_apply (𝕜 := ℝ) a b
      rw [h1]
      apply Finset.sum_congr rfl
      intro i _
      have h2 : inner ℝ (a i) (b i) = a i * b i := by
        exact Real.inner_apply (a.ofLp i) (b.ofLp i)
      exact h2
    have h1 : π (U x) = inner ℝ v_eucl (U x) := by
      have h2 : inner ℝ v_eucl (U x) = ∑ i : Fin n, v_eucl i * (U x) i := h_inner_eq v_eucl (U x)
      rw [h2]
      have h3 : ∑ i : Fin n, v_eucl i * (U x) i = ∑ i : Fin n, v i * (U x) i := by
        apply Finset.sum_congr rfl
        intro i _
        have h4 : v_eucl i = v i := by
          simp [v_eucl] <;> rfl
        rw [h4]
      rw [h3] <;> rfl
    rw [h1]
    have h3 : inner ℝ v_eucl (U x) = inner ℝ (U (U.symm v_eucl)) (U x) := by
      have h_eq : U (U.symm v_eucl) = v_eucl := U.apply_symm_apply v_eucl
      rw [h_eq]
    rw [h3]
    have h4 : inner ℝ (U (U.symm v_eucl)) (U x) = inner ℝ (U.symm v_eucl) x := by
      exact LinearIsometryEquiv.inner_map_map U (U.symm v_eucl) x
    rw [h4, h_symm]
    have h5 : inner ℝ (v_norm • e0) x = v_norm * inner ℝ e0 x := by
      simp [inner_smul_left]
    rw [h5]
    have h6 : inner ℝ e0 x = x i0 := by
      have h7 : inner ℝ e0 x = ∑ i : Fin n, e0 i * x i := h_inner_eq e0 x
      rw [h7]
      have h8 : ∀ j, e0 j * x j = if j = i0 then x j else 0 := by
        intro j
        by_cases hj : j = i0
        · rw [hj, h_e0_coord i0, if_pos rfl] <;> simp
        · have hz : e0 j = 0 := by
            rw [h_e0_coord j]
            have hif : (if j = i0 then (1 : ℝ) else 0) = 0 := by simp [hj]
            rw [hif] <;> rfl
          rw [hz, if_neg hj] <;> ring
      have h9 : ∑ i : Fin n, e0 i * x i = ∑ i : Fin n, (if i = i0 then x i else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h8 i
      rw [h9]
      simp
    rw [h6]
    have h7 : |x i0| ≤ 1 := hx.1
    have h8 : |v_norm * x i0| = v_norm * |x i0| := by
      rw [abs_mul, abs_of_pos h_v_norm_pos]
    rw [h8]
    have h9 : v_norm * |x i0| ≤ v_norm := by
      have h10 : |x i0| ≤ 1 := h7
      have h11 : v_norm * |x i0| ≤ v_norm * 1 := by gcongr
      linarith
    exact h9

  have hBlich : ENNReal.ofReal ((N : ℝ) * δ^n) < volume V := by
    rw [hV_vol]; exact hR_vol
  rcases blichfeldt_n_dim (by linarith) hδ_pos hV_meas hBlich with ⟨p, hp_inj, hp_in_V, hp_lattice⟩

  let S_k : Fin (N + 1) → Set ℝ := fun k => S + {π (p k)}
  have hSk_meas : ∀ k, MeasurableSet (S_k k) := by
    intro k
    have h_cont : Continuous (fun x : ℝ => x + π (p k)) := by continuity
    have h_compact : IsCompact (S_k k) := by
      have h_eq2 : S_k k = (fun x : ℝ => x + π (p k)) '' S := by
        ext z; simp [S_k, Set.mem_add, Set.mem_image] <;> aesop
      rw [h_eq2]
      exact hS_compact.image h_cont
    exact h_compact.measurableSet
  have hSk_vol : ∀ k, volume (S_k k) = volS := by
    intro k
    have h_eq : S_k k = (fun x : ℝ => x + π (p k)) '' S := by
      ext z
      simp [S_k, Set.mem_add, Set.mem_image]
      <;> aesop
    rw [h_eq]
    have h_trans : MeasurePreserving (fun x : ℝ => x + π (p k)) volume volume := by
      exact measurePreserving_add_right volume (π (p k))
    have h : volume ((fun x : ℝ => x + π (p k)) '' S) = volS := by
      have h_preimage : (fun x : ℝ => x + π (p k)) ⁻¹' ((fun x : ℝ => x + π (p k)) '' S) = S := by
        ext z; simp
      have h_image_meas : MeasurableSet ((fun x : ℝ => x + π (p k)) '' S) := by
        rw [←h_eq]
        exact hSk_meas k
      have h4 : volume ((fun x : ℝ => x + π (p k)) ⁻¹' ((fun x : ℝ => x + π (p k)) '' S)) =
          volume ((fun x : ℝ => x + π (p k)) '' S) :=
        h_trans.measure_preimage (s := (fun x : ℝ => x + π (p k)) '' S) h_image_meas.nullMeasurableSet
      rw [h_preimage] at h4
      exact h4.symm
    exact h
  have hSk_vol' : ∀ k, volume (S_k k) ≥ volS := by intro k; rw [hSk_vol k]

  let minS := sInf S
  let maxS := sSup S
  have hS_subset : S ⊆ Set.Icc minS maxS := by
    intro x hx
    have h_bdd_below : BddBelow S := hS_compact.bddBelow
    have h_bdd_above : BddAbove S := hS_compact.bddAbove
    have h1 : minS ≤ x := by exact (csInf_le_iff h_bdd_below hS_nonempty).mpr fun b a => a hx
    have h2 : x ≤ maxS := le_csSup h_bdd_above hx
    exact ⟨h1, h2⟩

  have hS_diam : maxS - minS ≤ (n : ℝ) * c := by
    have hBdd : Bornology.IsBounded S := hS_compact.isBounded
    have h_diam_eq : diam S = maxS - minS := Real.diam_eq hBdd
    have h_diam_le : diam S ≤ (n : ℝ) * c :=
      Metric.diam_le_of_forall_dist_le_of_nonempty hS_nonempty
        (fun x hx y hy => scaledSumset_diam_bound hA hv x y hx hy)
    linarith [h_diam_eq, h_diam_le]

  have hSk_subset : ∀ k, S_k k ⊆ Set.Icc (minS - v_norm) (maxS + v_norm) := by
    intro k z hz
    rcases Set.mem_add.mp hz with ⟨s, hs, t, ht, rfl⟩
    have h_t_eq : t = π (p k) := Set.mem_singleton_iff.mp ht
    rw [h_t_eq]
    have h1 : minS ≤ s := (hS_subset hs).1
    have h2 : s ≤ maxS := (hS_subset hs).2
    have h3 : |π (p k)| ≤ v_norm := hπV (p k) (hp_in_V k)
    have h4 : -v_norm ≤ π (p k) := by linarith [abs_le.mp h3]
    have h5 : π (p k) ≤ v_norm := by linarith [abs_le.mp h3]
    constructor <;> linarith

  have hUnion_bound : volume (⋃ k, S_k k) ≤ ENNReal.ofReal C_val := by
    have h_sub : (⋃ k, S_k k) ⊆ Set.Icc (minS - v_norm) (maxS + v_norm) := by
      intro z hz
      have h_exists : ∃ (k : Fin (N + 1)), z ∈ S_k k := Set.mem_iUnion.mp hz
      rcases h_exists with ⟨k, hk⟩
      exact hSk_subset k hk
    have h_bdd_below : BddBelow S := hS_compact.bddBelow
    have h_bdd_above : BddAbove S := hS_compact.bddAbove
    have h_min_le_max : minS ≤ maxS := csInf_le_csSup hS_nonempty (hb := h_bdd_below) (ha := h_bdd_above)
    have h_len : minS - v_norm ≤ maxS + v_norm := by
      have h_vnorm_nonneg : 0 ≤ v_norm := by positivity
      linarith
    have h_vol_Icc : volume (Set.Icc (minS - v_norm) (maxS + v_norm)) =
        ENNReal.ofReal ((maxS + v_norm) - (minS - v_norm)) := by
      rw [Real.volume_Icc] <;> linarith
    calc volume (⋃ k, S_k k)
      ≤ volume (Set.Icc (minS - v_norm) (maxS + v_norm)) := measure_mono h_sub
    _ = ENNReal.ofReal ((maxS + v_norm) - (minS - v_norm)) := h_vol_Icc
    _ ≤ ENNReal.ofReal C_val := by
      have h : (maxS + v_norm) - (minS - v_norm) ≤ C_val := by
        have h2 : maxS - minS ≤ (n : ℝ) * c := hS_diam
        have h3 : (maxS + v_norm) - (minS - v_norm) = (maxS - minS) + 2 * v_norm := by ring
        rw [h3]
        have h4 : C_val = (n : ℝ) * c + 2 * v_norm := by
          simp [C_val] <;> ring
        rw [h4]
        linarith
      exact ENNReal.ofReal_le_ofReal h

  have h_card : Fintype.card (Fin (N + 1)) = N + 1 := by simp
  have h_cast : (↑(N + 1) : ENNReal) = (↑N + 1 : ENNReal) := by
    norm_cast
  have hN_ineq' : (↑(Fintype.card (Fin (N + 1))) : ENNReal) * volS > ENNReal.ofReal C_val := by
    rw [h_card, h_cast]
    exact hN_ineq
  have h_collision : ∃ (i j : Fin (N + 1)), i ≠ j ∧ (S_k i ∩ S_k j).Nonempty :=
    measure_pigeonhole (μ := volume) (S := S_k) hSk_meas hSk_vol' hUnion_bound hN_ineq'

  rcases h_collision with ⟨i, j, hne, h_inter⟩
  have h_main_extract : ∃ (a b : Fin n → ℝ), (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ A) ∧
      (∑ k : Fin n, v k * a k) + π (p i) = (∑ k : Fin n, v k * b k) + π (p j) := by
    rcases h_inter with ⟨z, hzi, hzj⟩
    rcases Set.mem_add.mp hzi with ⟨s1, hs1, t1, ht1, hz1⟩
    rcases Set.mem_add.mp hzj with ⟨s2, hs2, t2, ht2, hz2⟩
    have ht1 : t1 = π (p i) := Set.mem_singleton_iff.mp ht1
    have ht2 : t2 = π (p j) := Set.mem_singleton_iff.mp ht2
    have h_eq : s1 + t1 = s2 + t2 := by
      rw [hz1, hz2]
    rcases hs1 with ⟨a, ha, rfl⟩
    rcases hs2 with ⟨b, hb, rfl⟩
    refine ⟨a, b, ha, hb, ?_⟩
    simpa [ht1, ht2] using h_eq
  rcases h_main_extract with ⟨a, b, ha, hb, h_eq⟩

  let ℓ_vec := p j - p i
  have hℓ_nonzero : ℓ_vec ≠ 0 := by
    intro h; have h' : p j = p i := by
      have h1 : p j - p i = 0 := h
      exact sub_eq_zero.mp h1
    have h2 : j = i := hp_inj h'
    exact hne h2.symm
  let z' := b + ℓ_vec

  rcases hp_lattice j i with ⟨m, hm⟩
  have hℓ_coord : ∀ k : Fin n, ∃ (mi : ℤ), ℓ_vec k = δ * (mi : ℝ) := by
    intro k
    refine ⟨m k, ?_⟩
    have h5 := congr_fun (congr_arg (EuclideanSpace.equiv (Fin n) ℝ) hm) k
    simpa [ℓ_vec] using h5

  have h_coord : ∃ (k : Fin n), ℓ_vec k ≠ 0 := by
    by_contra h; push Not at h
    have h7 : ℓ_vec = 0 := by ext k; exact h k
    exact hℓ_nonzero h7
  rcases h_coord with ⟨k, hk_nonzero⟩

  have hℓ_k_bound : |ℓ_vec k| ≥ δ := by
    rcases hℓ_coord k with ⟨mi, hmi⟩
    have hmi_ne_zero : (mi : ℝ) ≠ 0 := by
      intro h
      have h' : ℓ_vec k = 0 := by rw [hmi, h] <;> ring
      exact hk_nonzero h'
    have h_abs_one : 1 ≤ |(mi : ℝ)| := by
      have h : (mi : ℤ) ≠ 0 := by exact_mod_cast hmi_ne_zero
      have h' : 1 ≤ |mi| := Int.one_le_abs h
      exact_mod_cast h'
    calc |ℓ_vec k|
      = |δ * (mi : ℝ)| := by rw [hmi]
    _ = |δ| * |(mi : ℝ)| := by rw [abs_mul]
    _ = δ * |(mi : ℝ)| := by rw [abs_of_pos hδ_pos]
    _ ≥ δ * 1 := by gcongr
    _ = δ := by ring

  let d := (z' k - a k)
  have hd_bound : |d| ≥ c := by
    have h_d_eq : d = b k + ℓ_vec k - a k := by
      simp [d, z'] <;> ring
    rw [h_d_eq]
    set e := b k - a k with he
    have h_abs_e : |e| ≤ c := by
      have hBdd : Bornology.IsBounded A := hA.isBounded
      have h : dist (b k) (a k) ≤ diam A := Metric.dist_le_diam_of_mem hBdd (hb k) (ha k)
      simpa [dist_eq_norm, Real.norm_eq_abs, he] using h
    have h_rev : |e + ℓ_vec k| ≥ |ℓ_vec k| - |e| := by
      have h : |ℓ_vec k| ≤ |e + ℓ_vec k| + |e| := by
        calc |ℓ_vec k|
          = |(e + ℓ_vec k) - e| := by ring_nf
        _ ≤ |e + ℓ_vec k| + |e| := by exact abs_sub _ _
      linarith
    have h_final : |ℓ_vec k| - |e| ≥ c := by
      have hδ2c : δ = 2 * c := by simp [δ, c]
      rw [hδ2c] at hℓ_k_bound
      linarith
    have h_d_eq3 : d = e + ℓ_vec k := by
      simp [e, d, z'] <;> ring
    have h_rev' : |ℓ_vec k| - |e| ≤ |d| := by
      rw [h_d_eq3]
      exact h_rev
    exact le_trans h_final h_rev'

  have hd_ne_zero : d ≠ 0 := by
    have h : |d| ≥ c := hd_bound
    have hc_pos : 0 < c := h_diam_pos
    have h' : 0 < |d| := by linarith
    exact abs_ne_zero.mp (ne_of_gt h')

  have hℓ_sum : ∑ idx : Fin n, v idx * ℓ_vec idx = π (p j) - π (p i) := by
    have h2 : ℓ_vec = p j - p i := by simp [ℓ_vec]
    have h3 : ∑ idx : Fin n, v idx * ℓ_vec idx = ∑ idx : Fin n, v idx * ((p j - p i) idx) := by
      apply Finset.sum_congr rfl
      intro idx _
      rw [h2]
    rw [h3]
    have h4 : ∑ idx : Fin n, v idx * ((p j - p i) idx) = ∑ idx : Fin n, v idx * ((p j) idx - (p i) idx) := by
      apply Finset.sum_congr rfl
      intro idx _
      rfl
    rw [h4]
    have h5 : ∑ idx : Fin n, v idx * ((p j) idx - (p i) idx) = π (p j) - π (p i) := by
      have h6 : ∑ idx : Fin n, v idx * ((p j) idx - (p i) idx) = ∑ idx : Fin n, (v idx * (p j) idx - v idx * (p i) idx) := by
        apply Finset.sum_congr rfl; intro idx _; ring
      rw [h6, Finset.sum_sub_distrib]
      <;> rfl
    exact h5
  have h1 : ∑ idx : Fin n, v idx * (a idx - z' idx) = 0 := by
    have h2 : (∑ idx : Fin n, v idx * a idx) + π (p i) = (∑ idx : Fin n, v idx * b idx) + π (p j) := h_eq
    have h3 : ∑ idx : Fin n, v idx * (a idx - z' idx) = (∑ idx : Fin n, v idx * a idx) - (∑ idx : Fin n, v idx * z' idx) := by
      have h4 : ∑ idx : Fin n, v idx * (a idx - z' idx) = ∑ idx : Fin n, (v idx * a idx - v idx * z' idx) := by
        apply Finset.sum_congr rfl; intro idx _; ring
      rw [h4, Finset.sum_sub_distrib]
    rw [h3]
    have h4 : ∑ idx : Fin n, v idx * z' idx = ∑ idx : Fin n, v idx * (b idx + ℓ_vec idx) := by
      apply Finset.sum_congr rfl
      intro idx _
      have h5 : z' idx = b idx + ℓ_vec idx := by simp [z'] <;> ring
      rw [h5]
    rw [h4]
    have h5 : ∑ idx : Fin n, v idx * (b idx + ℓ_vec idx) = (∑ idx : Fin n, v idx * b idx) + ∑ idx : Fin n, v idx * ℓ_vec idx := by
      have h6 : ∑ idx : Fin n, v idx * (b idx + ℓ_vec idx) = ∑ idx : Fin n, (v idx * b idx + v idx * ℓ_vec idx) := by
        apply Finset.sum_congr rfl; intro idx _; ring
      rw [h6, Finset.sum_add_distrib]
    rw [h5]
    rw [hℓ_sum]
    have h7 : (∑ idx : Fin n, v idx * a idx) + π (p i) = (∑ idx : Fin n, v idx * b idx) + π (p j) := h2
    have h8 : (∑ idx : Fin n, v idx * a idx) - ((∑ idx : Fin n, v idx * b idx) + (π (p j) - π (p i))) = 0 := by
      linarith
    exact h8
  have h_split : ∑ i : Fin n, v i * (a i - z' i) =
      v k * (a k - z' k) + ∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i) :=
    sum_fin_split k (fun i => v i * (a i - z' i))
  rw [h_split] at h1
  have h6 : v k * (a k - z' k) + ∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i) = 0 := h1
  have h7 : v k * (a k - z' k) = -∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i) := by linarith
  have h8 : a k - z' k = -d := by
    simp [d, z'] <;> ring
  have h9 : v k * d = ∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i) := by
    have h10 : v k * (a k - z' k) = v k * (-d) := by rw [h8]
    rw [h10] at h7
    have h11 : v k * (-d) = -∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i) := h7
    have h12 : -v k * d = -∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i) := by
      have h13 : v k * (-d) = -v k * d := by ring
      rw [h13] at h11
      exact h11
    have h14 : v k * d = ∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i) := by
      linarith [h12]
    exact h14
  have h_id : v k * d = ∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i) := h9

  have h_contain := main_containment hA hA_nonempty a b z' d ha hb k ℓ_vec
    (fun i => rfl) (by simp [d]) hℓ_coord h_diam_in_diff
  rcases h_contain with ⟨N', hN'_pos, hN'_contain, hN'_eq⟩

  have h_main_set : d • S ⊆ scaledSumsetExcept v k (iteratedDifference (productSet A 2) N') := by
    intro x hx
    rcases hx with ⟨s, hs, rfl⟩
    rcases hs with ⟨a', ha', h_s_eq⟩
    let t : {i : Fin n // i ≠ k} → ℝ := fun i => (a i - z' i) * a' k + d * a' i
    have h_t_in : ∀ i : {i : Fin n // i ≠ k}, t i ∈ iteratedDifference (productSet A 2) N' := by
      intro i
      have h1 : (a i - z' i) * a' k ∈ (a i - z' i) • A := ⟨a' k, ha' k, rfl⟩
      have h2 : d * a' i ∈ d • A := ⟨a' i, ha' i, rfl⟩
      have h3 : (a i - z' i) * a' k + d * a' i ∈ ((a i - z' i) • A) + (d • A) :=
        ⟨(a i - z' i) * a' k, h1, d * a' i, h2, by ring⟩
      have h4 := hN'_contain i h3
      rw [hN'_eq] at h4
      exact h4
    have h_sum_eq : d * s = ∑ i : {i : Fin n // i ≠ k}, v i * t i := by
      have h_s_eq' : s = ∑ i : Fin n, v i * a' i := h_s_eq
      rw [h_s_eq']
      have h_split1 : ∑ i : Fin n, v i * a' i = v k * a' k + ∑ i : {i : Fin n // i ≠ k}, v i * a' i :=
        sum_fin_split k (fun i => v i * a' i)
      rw [h_split1]
      have h_distrib : d * (v k * a' k + ∑ i : {i : Fin n // i ≠ k}, v i * a' i) =
          v k * d * a' k + ∑ i : {i : Fin n // i ≠ k}, v i * (d * a' i) := by
        rw [mul_add]
        have h1 : d * (v k * a' k) = v k * d * a' k := by ring
        have h2 : d * (∑ i : {i : Fin n // i ≠ k}, v i * a' i) =
            ∑ i : {i : Fin n // i ≠ k}, v i * (d * a' i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [h1, h2]
      rw [h_distrib]
      have h3 : v k * d * a' k = (∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i)) * a' k := by
        rw [h_id] <;> ring
      rw [h3]
      have h4 : (∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i)) * a' k =
          ∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i) * a' k := by
        rw [Finset.sum_mul] <;> rfl
      rw [h4]
      have h5 : ∑ i : {i : Fin n // i ≠ k}, v i * (a i - z' i) * a' k +
          ∑ i : {i : Fin n // i ≠ k}, v i * (d * a' i) =
          ∑ i : {i : Fin n // i ≠ k}, v i * t i := by
        rw [←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp [t] <;> ring
      exact h5
    have h_member : (∑ i : {i : Fin n // i ≠ k}, v i * t i) ∈ scaledSumsetExcept v k (iteratedDifference (productSet A 2) N') :=
      ⟨t, h_t_in, rfl⟩
    convert h_member using 1
    exact h_sum_eq

  have h_vol_scale : volume (d • S) = ENNReal.ofReal (|d|) * volS :=
    volume_smul_set hd_ne_zero hS_meas

  have h_final : volume (scaledSumsetExcept v k (iteratedDifference (productSet A 2) N')) ≥
      ENNReal.ofReal c * volS := by
    calc
      volume (scaledSumsetExcept v k (iteratedDifference (productSet A 2) N'))
        ≥ volume (d • S) := measure_mono h_main_set
    _ = ENNReal.ofReal (|d|) * volS := h_vol_scale
    _ ≥ ENNReal.ofReal c * volS := by
      have h9 : |d| ≥ c := hd_bound
      have h10 : ENNReal.ofReal c ≤ ENNReal.ofReal (|d|) := by gcongr
      have h11 : ENNReal.ofReal c * volS ≤ ENNReal.ofReal (|d|) * volS := by
        gcongr
      exact h11

  exact ⟨N', hN'_pos, k, h_final⟩

end ExpansionLemma
