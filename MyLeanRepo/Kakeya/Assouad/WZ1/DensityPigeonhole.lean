import MyLeanRepo.Kakeya.Assouad.WZ1.GridCenter
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.ThinTubesLargeDotProduct
import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellScaleHelpers
import Mathlib.Tactic

/-!
# Density-preserving cell pigeonhole for fixed cell selection

Provides three helper lemmas:

1. `finset_exists_density_le`: general averaging pigeonhole over ENNReal.
2. `density_cell_triple_pigeonhole`: select a grid-cell triple that preserves
   the uniform density lower bound relative to ambient cell cardinalities.
3. `small_scale_absorb_constant`: absorb a fixed constant into a negative
   real-rpow power of the scale, for sufficiently small `delta`.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal
open Classical Finset

/--
General averaging pigeonhole: if `C * ∑ w ≤ ∑ c`, then some index has
`C * w i ≤ c i`.
-/
lemma finset_exists_density_le {α : Type*} [DecidableEq α]
    (s : Finset α) (w c : α → ENNReal) (C : ENNReal)
    (h : C * ∑ i ∈ s, w i ≤ ∑ i ∈ s, c i)
    (hne : s.Nonempty) :
    ∃ i ∈ s, C * w i ≤ c i := by
  by_contra h'
  push Not at h'
  have h1 : ∀ i ∈ s, c i < C * w i := fun i hi => h' i hi
  have h2 : ∑ i ∈ s, c i < ∑ i ∈ s, C * w i :=
    ENNReal.sum_lt_sum_of_nonempty hne h1
  have h3 : ∑ i ∈ s, C * w i = C * ∑ i ∈ s, w i := by
    rw [Finset.mul_sum]
  rw [h3] at h2
  exact not_le.mpr h2 h

/--
Select a grid-cell triple from a uniformly dense tripartite graph such that
the induced edge set satisfies the same density lower bound relative to the
ambient cell cardinalities.
-/
lemma density_cell_triple_pigeonhole
    {c : ENNReal}
    {F G1 G2 : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hDensity : WZ1UniformTripleDensity c F G1 G2 H)
    (rho : ℝ) (hrho : 0 < rho) :
    ∃ (centerF centerG1 centerG2 : Point2),
      let ambientF : DiscreteSet 2 := F.filter (fun p => gridCenter rho p = centerF)
      let ambientG1 : DiscreteSet 2 := G1.filter (fun p => gridCenter rho p = centerG1)
      let ambientG2 : DiscreteSet 2 := G2.filter (fun p => gridCenter rho p = centerG2)
      let inducedH := H.filter (fun e =>
        gridCenter rho e.1 = centerF ∧
        gridCenter rho e.2.1 = centerG1 ∧
        gridCenter rho e.2.2 = centerG2)
      ambientF.Nonempty ∧ ambientG1.Nonempty ∧ ambientG2.Nonempty ∧
      inducedH.Nonempty ∧
      c * ambientF.enncard * ambientG1.enncard * ambientG2.enncard ≤
        (inducedH.card : ENNReal) := by
  let centersF := F.image (gridCenter rho)
  let centersG1 := G1.image (gridCenter rho)
  let centersG2 := G2.image (gridCenter rho)
  let cells : Finset (Point2 × Point2 × Point2) :=
    centersF ×ˢ (centersG1 ×ˢ centersG2)

  let ambientF (cF : Point2) : DiscreteSet 2 :=
    F.filter (fun p => gridCenter rho p = cF)
  let ambientG1 (cG1 : Point2) : DiscreteSet 2 :=
    G1.filter (fun p => gridCenter rho p = cG1)
  let ambientG2 (cG2 : Point2) : DiscreteSet 2 :=
    G2.filter (fun p => gridCenter rho p = cG2)
  let inducedH (ct : Point2 × Point2 × Point2) : Finset (Point2 × Point2 × Point2) :=
    H.filter (fun e =>
      gridCenter rho e.1 = ct.1 ∧
      gridCenter rho e.2.1 = ct.2.1 ∧
      gridCenter rho e.2.2 = ct.2.2)

  let w : (Point2 × Point2 × Point2) → ENNReal := fun ct =>
    (ambientF ct.1).enncard * (ambientG1 ct.2.1).enncard *
      (ambientG2 ct.2.2).enncard
  let cnt : (Point2 × Point2 × Point2) → ENNReal := fun ct =>
    (inducedH ct).card

  let cells' : Finset (Point2 × Point2 × Point2) :=
    cells.filter (fun ct => (inducedH ct).Nonempty)

  have h_partF : ∑ cF ∈ centersF, (ambientF cF).card = F.card := by
    exact Eq.symm (Finset.card_eq_sum_card_image (gridCenter rho) F)
  have h_partG1 : ∑ cG1 ∈ centersG1, (ambientG1 cG1).card = G1.card := by
    exact Eq.symm (Finset.card_eq_sum_card_image (gridCenter rho) G1)
  have h_partG2 : ∑ cG2 ∈ centersG2, (ambientG2 cG2).card = G2.card := by
    exact Eq.symm (Finset.card_eq_sum_card_image (gridCenter rho) G2)

  have h_ennF : (∑ cF ∈ centersF, (ambientF cF).enncard) = F.enncard := by
    simpa [DiscreteSet.enncard, Nat.cast_sum] using
      congr_arg (fun x : ℕ => (x : ENNReal)) h_partF
  have h_ennG1 : (∑ cG1 ∈ centersG1, (ambientG1 cG1).enncard) = G1.enncard := by
    simpa [DiscreteSet.enncard, Nat.cast_sum] using
      congr_arg (fun x : ℕ => (x : ENNReal)) h_partG1
  have h_ennG2 : (∑ cG2 ∈ centersG2, (ambientG2 cG2).enncard) = G2.enncard := by
    simpa [DiscreteSet.enncard, Nat.cast_sum] using
      congr_arg (fun x : ℕ => (x : ENNReal)) h_partG2

  have h_inner :
      ∑ p ∈ centersG1 ×ˢ centersG2,
          (ambientG1 p.1).enncard * (ambientG2 p.2).enncard =
        (∑ cG1 ∈ centersG1, (ambientG1 cG1).enncard) *
          (∑ cG2 ∈ centersG2, (ambientG2 cG2).enncard) := by
    let S2 := ∑ cG2 ∈ centersG2, (ambientG2 cG2).enncard
    calc
      ∑ p ∈ centersG1 ×ˢ centersG2,
          (ambientG1 p.1).enncard * (ambientG2 p.2).enncard
        = ∑ cG1 ∈ centersG1, ∑ cG2 ∈ centersG2,
            (ambientG1 cG1).enncard * (ambientG2 cG2).enncard := by
          rw [Finset.sum_product]
      _ = ∑ cG1 ∈ centersG1, (ambientG1 cG1).enncard * S2 := by
          apply Finset.sum_congr rfl
          intro cG1 _
          rw [Finset.mul_sum]
      _ = (∑ cG1 ∈ centersG1, (ambientG1 cG1).enncard) * S2 := by
          rw [Finset.sum_mul]
      _ = (∑ cG1 ∈ centersG1, (ambientG1 cG1).enncard) *
            (∑ cG2 ∈ centersG2, (ambientG2 cG2).enncard) := by rfl

  have h_sum_w : ∑ ct ∈ cells, w ct =
      F.enncard * G1.enncard * G2.enncard := by
    calc
      ∑ ct ∈ cells, w ct
        = ∑ cF ∈ centersF, ∑ p ∈ centersG1 ×ˢ centersG2,
            (ambientF cF).enncard * (ambientG1 p.1).enncard *
              (ambientG2 p.2).enncard := by
          rw [Finset.sum_product]
      _ = ∑ cF ∈ centersF, (ambientF cF).enncard *
            ∑ p ∈ centersG1 ×ˢ centersG2,
              (ambientG1 p.1).enncard * (ambientG2 p.2).enncard := by
          apply Finset.sum_congr rfl
          intro cF _
          rw [Finset.mul_sum]
          <;> simp [mul_assoc]
      _ = (∑ cF ∈ centersF, (ambientF cF).enncard) *
            ∑ p ∈ centersG1 ×ˢ centersG2,
              (ambientG1 p.1).enncard * (ambientG2 p.2).enncard := by
          rw [Finset.sum_mul]
      _ = (∑ cF ∈ centersF, (ambientF cF).enncard) *
            ((∑ cG1 ∈ centersG1, (ambientG1 cG1).enncard) *
              (∑ cG2 ∈ centersG2, (ambientG2 cG2).enncard)) := by
          rw [h_inner]
      _ = F.enncard * G1.enncard * G2.enncard := by
          rw [h_ennF, h_ennG1, h_ennG2] <;> ring

  have h_disj : ∀ ct1 ∈ cells, ∀ ct2 ∈ cells, ct1 ≠ ct2 →
      Disjoint (inducedH ct1) (inducedH ct2) := by
    intro ct1 _ ct2 _ hne
    simp only [inducedH, Finset.disjoint_left, Finset.mem_filter]
    intro x hx1 hx2
    have h1 : gridCenter rho x.1 = ct1.1 := hx1.2.1
    have h2 : gridCenter rho x.1 = ct2.1 := hx2.2.1
    have h3 : ct1.1 = ct2.1 := h1.symm.trans h2
    have h4 : gridCenter rho x.2.1 = ct1.2.1 := hx1.2.2.1
    have h5 : gridCenter rho x.2.1 = ct2.2.1 := hx2.2.2.1
    have h6 : ct1.2.1 = ct2.2.1 := h4.symm.trans h5
    have h7 : gridCenter rho x.2.2 = ct1.2.2 := hx1.2.2.2
    have h8 : gridCenter rho x.2.2 = ct2.2.2 := hx2.2.2.2
    have h9 : ct1.2.2 = ct2.2.2 := h7.symm.trans h8
    have h10 : ct1 = ct2 := by ext <;> tauto
    exact hne h10

  have h_union : cells.biUnion inducedH = H := by
    ext e
    simp only [Finset.mem_biUnion, inducedH, Finset.mem_filter]
    constructor
    · rintro ⟨ct, _, ⟨he, _⟩⟩
      exact he
    · intro he
      let p1 := gridCenter rho e.1
      let p2 := gridCenter rho e.2.1
      let p3 := gridCenter rho e.2.2
      let ct : Point2 × Point2 × Point2 := (p1, (p2, p3))
      have h_support := density_vertex_containment hDensity e he
      have hp1 : p1 ∈ centersF :=
        Finset.mem_image.mpr ⟨e.1, h_support.1, rfl⟩
      have hp2 : p2 ∈ centersG1 :=
        Finset.mem_image.mpr ⟨e.2.1, h_support.2.1, rfl⟩
      have hp3 : p3 ∈ centersG2 :=
        Finset.mem_image.mpr ⟨e.2.2, h_support.2.2, rfl⟩
      have hpair : (p2, p3) ∈ centersG1 ×ˢ centersG2 :=
        Finset.mem_product.mpr ⟨hp2, hp3⟩
      have hct_in : ct ∈ cells :=
        Finset.mem_product.mpr ⟨hp1, hpair⟩
      exact ⟨ct, hct_in, ⟨he, by simp [ct, p1, p2, p3]⟩⟩

  have h_sum_cnt : ∑ ct ∈ cells, cnt ct = (H.card : ENNReal) := by
    have h_card_biunion :
        (cells.biUnion inducedH).card =
          ∑ ct ∈ cells, (inducedH ct).card :=
      Finset.card_biUnion h_disj
    have h' : ∑ ct ∈ cells, (inducedH ct).card = H.card := by
      rw [← h_card_biunion, h_union]
    have h_cnt :
        ∑ ct ∈ cells, cnt ct =
          (↑(∑ ct ∈ cells, (inducedH ct).card) : ENNReal) := by
      have h1 :
          ∑ ct ∈ cells, cnt ct =
            ∑ ct ∈ cells, ((inducedH ct).card : ENNReal) := by
        apply Finset.sum_congr rfl
        intro _ _
        rfl
      rw [h1, Nat.cast_sum]
    rw [h_cnt]
    exact_mod_cast h'

  have hcells'_nonempty : cells'.Nonempty := by
    rcases hDensity.1 with ⟨edge, hedge⟩
    let p1 := gridCenter rho edge.1
    let p2 := gridCenter rho edge.2.1
    let p3 := gridCenter rho edge.2.2
    let ct : Point2 × Point2 × Point2 := (p1, (p2, p3))
    have h_support := density_vertex_containment hDensity edge hedge
    have hp1 : p1 ∈ centersF :=
      Finset.mem_image.mpr ⟨edge.1, h_support.1, rfl⟩
    have hp2 : p2 ∈ centersG1 :=
      Finset.mem_image.mpr ⟨edge.2.1, h_support.2.1, rfl⟩
    have hp3 : p3 ∈ centersG2 :=
      Finset.mem_image.mpr ⟨edge.2.2, h_support.2.2, rfl⟩
    have hpair : (p2, p3) ∈ centersG1 ×ˢ centersG2 :=
      Finset.mem_product.mpr ⟨hp2, hp3⟩
    have hct_in : ct ∈ cells :=
      Finset.mem_product.mpr ⟨hp1, hpair⟩
    have h_edge_in : edge ∈ inducedH ct := by
      rw [Finset.mem_filter]
      exact ⟨hedge, by simp [ct, p1, p2, p3]⟩
    have h_induced : (inducedH ct).Nonempty := ⟨edge, h_edge_in⟩
    have hct_in' : ct ∈ cells' := by
      simp only [cells', Finset.mem_filter]
      exact ⟨hct_in, h_induced⟩
    exact ⟨ct, hct_in'⟩

  have h_sum_cnt' : ∑ ct ∈ cells', cnt ct = ∑ ct ∈ cells, cnt ct := by
    have h1 : ∀ ct ∈ cells, ct ∉ cells' → cnt ct = 0 := by
      intro ct _ hnot
      simp only [cells', Finset.mem_filter] at hnot
      have h2 : ¬(inducedH ct).Nonempty := by tauto
      have h3 : inducedH ct = ∅ := by
        simpa [Finset.not_nonempty_iff_eq_empty] using h2
      simp [cnt, h3]
    rw [Finset.sum_subset
      (show cells' ⊆ cells from Finset.filter_subset _ _) h1]

  have h_sum_w' : ∑ ct ∈ cells', w ct ≤ ∑ ct ∈ cells, w ct :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun _ _ _ => by positivity)

  have h_global :
      c * (F.enncard * G1.enncard * G2.enncard) ≤
        (H.card : ENNReal) := by
    have h_uhd : WZ1UniformHypergraphDensity c
        (wz1TripleVertexClasses F G1 G2) (wz1EncodeTriples H) :=
      hDensity.2
    rcases hDensity.1 with ⟨edge, hedge⟩
    let encEdge := wz1TripleCoordinate edge
    have hencEdge : encEdge ∈ wz1EncodeTriples H :=
      Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
    have h := h_uhd.2 encEdge hencEdge (∅ : Finset (Fin 3))
    have h_fiber :
        wz1HypergraphFiber (wz1EncodeTriples H)
            (∅ : Finset (Fin 3)) encEdge =
          wz1EncodeTriples H := by
      ext x
      simp [wz1HypergraphFiber] <;> tauto
    have h_prod :
        wz1VertexCardProduct
            (wz1TripleVertexClasses F G1 G2)
            (Finset.univ \ (∅ : Finset (Fin 3))) =
          F.enncard * G1.enncard * G2.enncard := by
      simp [wz1VertexCardProduct, wz1TripleVertexClasses, Fin.prod_univ_succ]
      <;> simp [DiscreteSet.enncard] <;> ring
    have h_card : (wz1EncodeTriples H).card = H.card := by
      apply Finset.card_image_of_injective
      intro a b hab
      have h0 : a.1 = b.1 := by
        simpa [wz1TripleCoordinate] using congr_fun hab 0
      have h1 : a.2.1 = b.2.1 := by
        simpa [wz1TripleCoordinate] using congr_fun hab 1
      have h2 : a.2.2 = b.2.2 := by
        simpa [wz1TripleCoordinate] using congr_fun hab 2
      exact Prod.ext h0 (Prod.ext h1 h2)
    rw [h_fiber, h_prod, h_card] at h
    exact h

  have h_main : c * ∑ ct ∈ cells', w ct ≤ ∑ ct ∈ cells', cnt ct := by
    calc
      c * ∑ ct ∈ cells', w ct
        ≤ c * ∑ ct ∈ cells, w ct := by gcongr
      _ = c * (F.enncard * G1.enncard * G2.enncard) := by rw [h_sum_w]
      _ ≤ (H.card : ENNReal) := h_global
      _ = ∑ ct ∈ cells, cnt ct := h_sum_cnt.symm
      _ = ∑ ct ∈ cells', cnt ct := h_sum_cnt'.symm

  rcases finset_exists_density_le cells' w cnt c h_main hcells'_nonempty with
    ⟨ct, hct_in', hle⟩
  let centerF := ct.1
  let centerG1 := ct.2.1
  let centerG2 := ct.2.2

  have hct_in : ct ∈ cells := (Finset.mem_filter.mp hct_in').1
  have h_inducedH_nonempty : (inducedH ct).Nonempty :=
    (Finset.mem_filter.mp hct_in').2

  have h_ambientF_nonempty : (ambientF centerF).Nonempty := by
    have h1 : centerF ∈ centersF := (Finset.mem_product.mp hct_in).1
    rcases Finset.mem_image.mp h1 with ⟨p, hp, h_eq⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, h_eq⟩⟩

  have h_ambientG1_nonempty : (ambientG1 centerG1).Nonempty := by
    have h1 : (centerG1, centerG2) ∈ centersG1 ×ˢ centersG2 :=
      (Finset.mem_product.mp hct_in).2
    have h2 : centerG1 ∈ centersG1 := (Finset.mem_product.mp h1).1
    rcases Finset.mem_image.mp h2 with ⟨p, hp, h_eq⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, h_eq⟩⟩

  have h_ambientG2_nonempty : (ambientG2 centerG2).Nonempty := by
    have h1 : (centerG1, centerG2) ∈ centersG1 ×ˢ centersG2 :=
      (Finset.mem_product.mp hct_in).2
    have h2 : centerG2 ∈ centersG2 := (Finset.mem_product.mp h1).2
    rcases Finset.mem_image.mp h2 with ⟨p, hp, h_eq⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, h_eq⟩⟩

  have hle' :
      c * (ambientF centerF).enncard * (ambientG1 centerG1).enncard *
          (ambientG2 centerG2).enncard ≤
        ((inducedH ct).card : ENNReal) := by
    have h_eq1 :
        w ct =
          (ambientF centerF).enncard * (ambientG1 centerG1).enncard *
            (ambientG2 centerG2).enncard := by
      dsimp only [w, centerF, centerG1, centerG2] <;> rfl
    have h_eq2 : cnt ct = ((inducedH ct).card : ENNReal) := by
      simp [cnt] <;> rfl
    rw [h_eq1, h_eq2] at hle
    simpa [mul_assoc] using hle

  exact ⟨centerF, centerG1, centerG2,
    h_ambientF_nonempty, h_ambientG1_nonempty, h_ambientG2_nonempty,
    h_inducedH_nonempty, hle'⟩

/--
Absorb a fixed constant `K` into `scale^(-gamma)` for sufficiently small
`delta`.
-/
lemma small_scale_absorb_constant
    {K : ENNReal} (hK : K ≠ ⊤) {gamma : ℝ} (hgamma : 0 < gamma)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
      ∀ (width scale : ℝ), 0 < width → scale = delta / width →
      Real.rpow delta (1 - epsilon / 10) < width →
      K ≤ Kakeya.realRpowENN scale (-gamma) := by
  by_cases hK0 : K = 0
  · refine ⟨1, by norm_num, by norm_num, ?_⟩
    intro delta hdelta _ width scale _ _ _
    rw [hK0] <;> simp
  · let Kreal : ℝ := ENNReal.toReal K
    have hKpos : 0 < K := Ne.bot_lt hK0
    have hK_lt_top : K < ⊤ := Ne.lt_top hK
    have hKreal_pos : 0 < Kreal := by
      rw [ENNReal.toReal_pos_iff]
      exact ⟨hKpos, hK_lt_top⟩
    have hK_eq : K = ENNReal.ofReal Kreal := by
      rw [ENNReal.ofReal_toReal hK]
    set exp : ℝ := gamma * epsilon / 10 with hexp_def
    have hexp_pos : 0 < exp := by positivity
    let b : ℝ := Kreal⁻¹
    have hb_pos : 0 < b := by positivity
    let delta₀ : ℝ := min (Real.rpow b (1 / exp)) 1
    have hdelta₀_pos : 0 < delta₀ := by
      have h1 : 0 < Real.rpow b (1 / exp) :=
        Real.rpow_pos_of_pos hb_pos _
      exact lt_min h1 (by norm_num)
    have hdelta₀_one : delta₀ ≤ 1 := min_le_right _ _
    have hdelta₀_exp : Real.rpow delta₀ exp ≤ b := by
      dsimp only [delta₀]
      by_cases hcase : Real.rpow b (1 / exp) ≤ 1
      · rw [min_eq_left hcase]
        have h_mul :
            Real.rpow (Real.rpow b (1 / exp)) exp =
              Real.rpow b ((1 / exp) * exp) :=
          (Real.rpow_mul hb_pos.le (1 / exp) exp).symm
        rw [h_mul]
        have h2 : (1 / exp) * exp = 1 := by
          field_simp [hexp_pos.ne'] <;> ring
        rw [h2]
        have h3 : Real.rpow b 1 = b := by simp
        rw [h3] <;> linarith
      · have h_b_gt_one : 1 < b := by
          by_contra h
          have h' : b ≤ 1 := by linarith
          have h'' : Real.rpow b (1 / exp) ≤ 1 :=
            Real.rpow_le_one hb_pos.le h' (by positivity)
          exact hcase h''
        rw [min_eq_right (by linarith)]
        have h3 : Real.rpow (1 : ℝ) exp = 1 := by simp
        rw [h3]
        <;> linarith
    refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
    intro delta hdelta hdelta_le width scale hwidth hscale_eq hthin
    have hscale_lt : scale < Real.rpow delta (epsilon / 10) :=
      wide_coarse_scale_lt_rpow
        hdelta hepsilon hwidth hscale_eq hthin
    have hscale_pos : 0 < scale := by
      rw [hscale_eq] <;> positivity
    have hbase_pos : 0 < Real.rpow delta (epsilon / 10) :=
      Real.rpow_pos_of_pos hdelta _
    have hdelta_exp : Real.rpow delta exp ≤ b := by
      have h : Real.rpow delta exp ≤ Real.rpow delta₀ exp :=
        Real.rpow_le_rpow hdelta.le hdelta_le hexp_pos.le
      exact h.trans hdelta₀_exp
    have hdelta_neg_exp : Real.rpow delta (-exp) ≥ Kreal := by
      have h1 : Real.rpow delta (-exp) = (Real.rpow delta exp)⁻¹ :=
        Real.rpow_neg hdelta.le exp
      rw [h1]
      have h2 : 0 < Real.rpow delta exp :=
        Real.rpow_pos_of_pos hdelta _
      have h3 : (Real.rpow delta exp)⁻¹ ≥ b⁻¹ := by gcongr
      have h4 : b⁻¹ = Kreal := by
        simp [b, hKreal_pos.ne'] <;> field_simp <;> ring
      rw [h4] at h3
      exact h3
    have h51 :
        Real.rpow scale gamma ≤
          Real.rpow (Real.rpow delta (epsilon / 10)) gamma :=
      Real.rpow_le_rpow hscale_pos.le hscale_lt.le hgamma.le
    have h_pos1 : 0 < Real.rpow scale gamma :=
      Real.rpow_pos_of_pos hscale_pos _
    have h_pos2 :
        0 < Real.rpow (Real.rpow delta (epsilon / 10)) gamma :=
      Real.rpow_pos_of_pos hbase_pos _
    have h5 :
        Real.rpow scale (-gamma) ≥
          Real.rpow (Real.rpow delta (epsilon / 10)) (-gamma) := by
      have h52 :
          Real.rpow scale (-gamma) = (Real.rpow scale gamma)⁻¹ :=
        Real.rpow_neg hscale_pos.le gamma
      have h53 :
          Real.rpow (Real.rpow delta (epsilon / 10)) (-gamma) =
            (Real.rpow (Real.rpow delta (epsilon / 10)) gamma)⁻¹ :=
        Real.rpow_neg hbase_pos.le gamma
      rw [h52, h53]
      have h_inv :
          (Real.rpow (Real.rpow delta (epsilon / 10)) gamma)⁻¹ ≤
            (Real.rpow scale gamma)⁻¹ := by
        gcongr
      exact h_inv
    have h_mul2 :
        Real.rpow (Real.rpow delta (epsilon / 10)) (-gamma) =
          Real.rpow delta ((epsilon / 10) * (-gamma)) :=
      (Real.rpow_mul hdelta.le (epsilon / 10) (-gamma)).symm
    have h7 : (epsilon / 10) * (-gamma) = -exp := by
      simp [hexp_def] <;> ring
    have h6 :
        Real.rpow (Real.rpow delta (epsilon / 10)) (-gamma) =
          Real.rpow delta (-exp) := by
      rw [h_mul2, h7]
    have h8 : Real.rpow scale (-gamma) ≥ Kreal := by
      calc
        Real.rpow scale (-gamma)
          ≥ Real.rpow (Real.rpow delta (epsilon / 10)) (-gamma) := h5
        _ = Real.rpow delta (-exp) := h6
        _ ≥ Kreal := hdelta_neg_exp
    have h_goal : K ≤ Kakeya.realRpowENN scale (-gamma) := by
      rw [hK_eq]
      simp only [Kakeya.realRpowENN]
      exact ENNReal.ofReal_mono h8
    exact h_goal

end Kakeya.Assouad
