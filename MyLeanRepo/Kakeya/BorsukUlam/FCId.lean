/-
# f_C = id on top homology

Proves `fC_id`: odd self-map induces identity on H_n(C; Z/2).

## Proof

Assume fC_n = 0. Split on qStar = 0 vs qStar ≠ 0.

Case qStar = 0:
- qStar = 0 gives Mono δ (exactness)
- fD_n3 ≫ δ = δ and Mono δ ⇒ fD_n3 = id
- bridge gives fD_n1 = id
- fD_n1 ≫ iStar = 0 and fD_n1 = id ⇒ iStar = 0
- qStar = 0 gives Epi iStar (exactness)
- Epi iStar and iStar = 0 ⇒ H_n(C) = 0, contradiction (H_n(C) ≅ Z/2)

Case qStar ≠ 0:
- H_n(D) ≅ Z/2 (topological fact: D computes RP^n homology)
- qStar : H_n(C) → H_n(D) is nonzero between Z/2 objects, hence epi
- qStar ≫ fD_n3 = 0 and Epi qStar ⇒ fD_n3 = 0
- fD_n3 ≫ δ = δ and fD_n3 = 0 ⇒ δ = 0
- Epi δ and δ = 0 ⇒ H_{n-1}(D) = 0, contradiction (H_{n-1}(D) ≅ Z/2)

Thus fC_n ≠ 0, and since H_n(C) ≅ Z/2, fC_n = id.

## Whiteprint Node
- odd_degree_lemma_homology
-/

import MyLeanRepo.Kakeya.BorsukUlam.OddDegreeHomology
import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.CategoryBridge
import MyLeanRepo.Kakeya.BorsukUlam.HDTopIso

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex
open SeedMathlib.AlgebraicTopology.Degree
open BorsukUlamBackup

variable {n : ℕ}

namespace BorsukUlam.OddDegreeHomology

/-! ### Helper lemmas -/

/-- Any element of Z/2 is 0 or 1. -/
lemma z2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z <;> tauto

/-- δ at degree n is epi. -/
lemma delta_n_epi (n : ℕ) (hn : 1 ≤ n) :
    Epi ((hS_Add n).δ n (n - 1) (by simp [ComplexShape.down_Rel] <;> omega)) := by
  let hS := hS_Add n
  let j := n - 1
  have hij : (ComplexShape.down ℕ).Rel n j := by
    simp [ComplexShape.down_Rel, j] <;> omega
  let δ := hS.δ n j hij
  let iStar := HomologicalComplex.homologyMap (S_Add n).f j
  by_cases h_n1 : n = 1
  · subst h_n1
    have h_i0 : iStar = 0 := iStarZero_Add 1 (by norm_num)
    have h_exact1 : (ShortComplex.mk δ iStar _).Exact := hS.homology_exact₁ 1 0 hij
    exact h_exact1.epi_f_iff.mpr h_i0
  · have h_j_pos : 0 < j := by omega
    have h_j_lt : j < n := by omega
    have hCj : IsZero ((S_Add n).X₂.homology j) := hC_vanishing n j h_j_pos h_j_lt
    have h_i0 : iStar = 0 := IsZero.eq_zero_of_tgt hCj iStar
    have h_exact1 : (ShortComplex.mk δ iStar _).Exact := hS.homology_exact₁ n j hij
    exact h_exact1.epi_f_iff.mpr h_i0

/-- Any nonzero endomorphism of an object isomorphic to Z/2 is the identity. -/
lemma nonzero_endo_z2_id {X : AddCommGrpCat}
    (e : X ≅ BorsukUlam.BackupRoute.R2)
    {g : X ⟶ X} (hg : g ≠ 0) : g = 𝟙 X := by
  let g' : BorsukUlam.BackupRoute.R2 ⟶ BorsukUlam.BackupRoute.R2 :=
    e.inv ≫ g ≫ e.hom
  have h_g'_ne : g' ≠ 0 := by
    intro h
    have h2 : g = 0 := by
      calc g
        = e.hom ≫ g' ≫ e.inv := by simp [g', Category.assoc] <;> rfl
      _ = 0 := by rw [h] <;> simp
    exact hg h2
  have h1 : (g' : BorsukUlam.BackupRoute.R2 → BorsukUlam.BackupRoute.R2) 1 ≠ 0 := by
    intro h2
    have h3 : g' = 0 := by
      apply AddCommGrpCat.ext
      intro z
      have h4 := z2_cases z
      rcases h4 with (rfl | rfl) <;> simp [h2]
    exact h_g'_ne h3
  have h2 : (g' : BorsukUlam.BackupRoute.R2 → BorsukUlam.BackupRoute.R2) 1 = 1 := by
    have h4 := z2_cases ((g' : BorsukUlam.BackupRoute.R2 → BorsukUlam.BackupRoute.R2) 1)
    rcases h4 with (h4 | h4)
    · exfalso; exact h1 h4
    · exact h4
  have h_g'_id : g' = 𝟙 _ := by
    apply AddCommGrpCat.ext
    intro y
    have h4 := z2_cases y
    rcases h4 with (rfl | rfl)
    · simp
    · exact h2
  calc g
    = e.hom ≫ g' ≫ e.inv := by simp [g', Category.assoc] <;> rfl
  _ = e.hom ≫ 𝟙 _ ≫ e.inv := by rw [h_g'_id]
  _ = 𝟙 X := by simp

/-- Any nonzero map between objects both isomorphic to Z/2 is epi. -/
lemma nonzero_between_z2_is_epi {X Y : AddCommGrpCat}
    (eX : X ≅ BorsukUlam.BackupRoute.R2)
    (eY : Y ≅ BorsukUlam.BackupRoute.R2)
    {f : X ⟶ Y} (hf : f ≠ 0) : Epi f := by
  let g : BorsukUlam.BackupRoute.R2 ⟶ BorsukUlam.BackupRoute.R2 :=
    eX.inv ≫ f ≫ eY.hom
  have hg_ne : g ≠ 0 := by
    intro h
    have h2 : f = 0 := by
      calc f
        = eX.hom ≫ g ≫ eY.inv := by simp [g, Category.assoc] <;> rfl
      _ = 0 := by rw [h] <;> simp
    exact hf h2
  have h1 : (g : BorsukUlam.BackupRoute.R2 → BorsukUlam.BackupRoute.R2) 1 ≠ 0 := by
    intro h2
    have h3 : g = 0 := by
      apply AddCommGrpCat.ext
      intro z
      have h4 := z2_cases z
      rcases h4 with (rfl | rfl) <;> simp [h2]
    exact hg_ne h3
  have h_surj : Function.Surjective (g : BorsukUlam.BackupRoute.R2 → BorsukUlam.BackupRoute.R2) := by
    intro y
    by_cases hy : y = 0
    · refine' ⟨0, _⟩
      rw [hy] <;> simp
    · have h_y1 : y = 1 := by
        have h4 := z2_cases y
        rcases h4 with (h4 | h4) <;> tauto
      have h6 : (g : BorsukUlam.BackupRoute.R2 → BorsukUlam.BackupRoute.R2) 1 = 1 := by
        have h7 := z2_cases ((g : BorsukUlam.BackupRoute.R2 → BorsukUlam.BackupRoute.R2) 1)
        rcases h7 with (h7 | h7) <;> tauto
      rw [h_y1]
      exact ⟨1, h6⟩
  have h_epi_g : Epi g := by
    rw [AddCommGrpCat.epi_iff_surjective]
    exact h_surj
  have h_eq : f = eX.hom ≫ g ≫ eY.inv := by simp [g, Category.assoc] <;> rfl
  letI : Epi g := h_epi_g
  rw [h_eq] <;> infer_instance

/-! ### f_C = id on H_n(C) -/

/-- f_C = id on H_n(C). -/
theorem fC_id (n : ℕ) (hn : 1 ≤ n)
    (f : C(Sphere n, Sphere n)) (hf_odd : ∀ x, f (ap x) = ap (f x)) :
    HomologicalComplex.homologyMap (f_C_Add f) n =
    𝟙 ((S_Add n).X₂.homology n) := by
  let hS := hS_Add n
  let j := n - 1
  have hij : (ComplexShape.down ℕ).Rel n j := by
    simp [ComplexShape.down_Rel, j] <;> omega
  let δ : (S_Add n).X₃.homology n ⟶ (S_Add n).X₁.homology j := hS.δ n j hij
  let Φ := φ n f hf_odd
  let iStar := HomologicalComplex.homologyMap (S_Add n).f n
  let qStar := HomologicalComplex.homologyMap (S_Add n).g n
  let fD_n3 := HomologicalComplex.homologyMap Φ.τ₃ n
  let fD_n1 := HomologicalComplex.homologyMap Φ.τ₁ n
  let fC_n := HomologicalComplex.homologyMap Φ.τ₂ n

  have hδ_epi : Epi δ := delta_n_epi n hn
  letI : Epi δ := hδ_epi

  have h_fD_j : HomologicalComplex.homologyMap Φ.τ₁ j =
      𝟙 ((S_Add n).X₁.homology j) := fD_id n hn f hf_odd j (by omega)

  have h_exact2 : (ShortComplex.mk iStar qStar _).Exact := hS.homology_exact₂ n
  have h_exact3 : (ShortComplex.mk qStar δ _).Exact := hS.homology_exact₃ n j hij

  have hX : (S_Add n).X₁ = (S_Add n).X₃ := by rfl
  let e_bridge : (S_Add n).X₁.homology n ≅ (S_Add n).X₃.homology n :=
    eqToIso (congr_arg (fun X : ChainComplex AddCommGrpCat ℕ => X.homology n) hX)
  have h_comm : fD_n1 ≫ e_bridge.hom = e_bridge.hom ≫ fD_n3 := by
    simp [e_bridge, eqToIso, fD_n1, fD_n3, Φ] <;> rfl

  have h_nat_δ : fD_n3 ≫ δ = δ := by
    have h : fD_n3 ≫ δ = δ ≫ HomologicalComplex.homologyMap Φ.τ₁ j :=
      (HomologicalComplex.HomologySequence.δ_naturality Φ hS hS n j hij).symm
    rw [h, h_fD_j, Category.comp_id]

  have h_nat_q : fC_n ≫ qStar = qStar ≫ fD_n3 := by
    have h : Φ.τ₂ ≫ (S_Add n).g = (S_Add n).g ≫ Φ.τ₃ := Φ.comm₂₃
    have h' := congr_arg (fun (k : _) => HomologicalComplex.homologyMap k n) h
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h'
    exact h'

  have h_nat_i : fD_n1 ≫ iStar = iStar ≫ fC_n := by
    have h : Φ.τ₁ ≫ (S_Add n).f = (S_Add n).f ≫ Φ.τ₂ := Φ.comm₁₂
    have h' := congr_arg (fun (k : _) => HomologicalComplex.homologyMap k n) h
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h'
    exact h'

  have h_iso_C : (S_Add n).X₂.homology n ≅ BorsukUlam.BackupRoute.R2 := hC_topIso n hn
  have hD_iso : (S_Add n).X₁.homology n ≅ BorsukUlam.BackupRoute.R2 := hD_top_iso n hn
  let eD3 : (S_Add n).X₃.homology n ≅ BorsukUlam.BackupRoute.R2 :=
    e_bridge.symm ≪≫ hD_iso

  by_cases h_fC : fC_n = 0
  · -- Assume fC_n = 0, split on qStar = 0 vs qStar ≠ 0
    have h_q_fd3 : qStar ≫ fD_n3 = 0 := by
      rw [h_fC] at h_nat_q
      simpa [zero_comp] using h_nat_q.symm

    have h_fd1_iStar : fD_n1 ≫ iStar = 0 := by
      rw [h_fC] at h_nat_i
      simpa [comp_zero] using h_nat_i

    by_cases h_q : qStar = 0
    · -- qStar = 0: Mono δ ⇒ fD_n3 = id ⇒ fD_n1 = id ⇒ iStar = 0, but Epi iStar
      have hδ_mono : Mono δ := h_exact3.mono_g_iff.mpr h_q
      letI : Mono δ := hδ_mono

      have h_fD3_id : fD_n3 = 𝟙 _ := by
        have h : fD_n3 ≫ δ = (𝟙 _) ≫ δ := by
          rw [h_nat_δ, Category.id_comp]
        exact (cancel_mono δ).mp h

      have h_fD1_id : fD_n1 = 𝟙 _ := by
        have h_fD1_eq : fD_n1 = e_bridge.hom ≫ fD_n3 ≫ e_bridge.inv := by
          calc fD_n1
            = fD_n1 ≫ 𝟙 _ := by simp
          _ = fD_n1 ≫ (e_bridge.hom ≫ e_bridge.inv) := by rw [e_bridge.hom_inv_id]
          _ = (fD_n1 ≫ e_bridge.hom) ≫ e_bridge.inv := by rw [Category.assoc]
          _ = (e_bridge.hom ≫ fD_n3) ≫ e_bridge.inv := by rw [h_comm]
          _ = e_bridge.hom ≫ fD_n3 ≫ e_bridge.inv := by rw [Category.assoc]
        rw [h_fD1_eq, h_fD3_id] <;> simp

      have h_i0 : iStar = 0 := by
        rw [h_fD1_id] at h_fd1_iStar
        simpa [Category.id_comp] using h_fd1_iStar

      have h_i_epi : Epi iStar := h_exact2.epi_f_iff.mpr h_q
      let z : (S_Add n).X₁.homology n ⟶ (S_Add n).X₂.homology n := 0
      have hz : z = iStar := h_i0.symm
      letI : Epi z := by convert h_i_epi using 1 <;> exact hz
      have h_contra : IsZero ((S_Add n).X₂.homology n) :=
        IsZero.of_epi_eq_zero z rfl
      have h' : IsZero BorsukUlam.BackupRoute.R2 := h_contra.of_iso h_iso_C.symm
      have h_id2 : 𝟙 BorsukUlam.BackupRoute.R2 = 0 := h'.eq_of_src (𝟙 _) 0
      have h12 : (1 : ZMod 2) = 0 := by
        have h13 := congr_arg (fun (g : BorsukUlam.BackupRoute.R2 ⟶ BorsukUlam.BackupRoute.R2) =>
          (g : BorsukUlam.BackupRoute.R2 → BorsukUlam.BackupRoute.R2) 1) h_id2
        simpa using h13
      contradiction

    · -- qStar ≠ 0: H_n(D) ≅ Z/2, so qStar epi ⇒ fD_n3 = 0 ⇒ δ = 0, contradiction
      have h_q_epi : Epi qStar := nonzero_between_z2_is_epi h_iso_C eD3 h_q
      letI : Epi qStar := h_q_epi

      have h_fD3_0 : fD_n3 = 0 := by
        have h : qStar ≫ fD_n3 = qStar ≫ (0 : _) := by simpa using h_q_fd3
        exact (cancel_epi qStar).mp h

      have hδ0 : δ = 0 := by
        rw [h_fD3_0] at h_nat_δ
        simpa [zero_comp] using h_nat_δ.symm

      let z2 : (S_Add n).X₃.homology n ⟶ (S_Add n).X₁.homology j := 0
      have hz2 : z2 = δ := hδ0.symm
      letI : Epi z2 := by convert hδ_epi using 1 <;> exact hz2
      have h_contra : IsZero ((S_Add n).X₁.homology j) :=
        IsZero.of_epi_eq_zero z2 rfl
      have hD_j_iso : (S_Add n).X₁.homology j ≅ BorsukUlam.BackupRoute.R2 :=
        hD_k_iso n hn j (by omega)
      have h' : IsZero BorsukUlam.BackupRoute.R2 := h_contra.of_iso hD_j_iso.symm
      have h_id2 : 𝟙 BorsukUlam.BackupRoute.R2 = 0 := h'.eq_of_src (𝟙 _) 0
      have h12 : (1 : ZMod 2) = 0 := by
        have h13 := congr_arg (fun (g : BorsukUlam.BackupRoute.R2 ⟶ BorsukUlam.BackupRoute.R2) =>
          (g : BorsukUlam.BackupRoute.R2 → BorsukUlam.BackupRoute.R2) 1) h_id2
        simpa using h13
      contradiction

  · -- fC_n ≠ 0, so fC_n = id since H_n(C) ≅ Z/2
    exact nonzero_endo_z2_id h_iso_C h_fC

end BorsukUlam.OddDegreeHomology

end
