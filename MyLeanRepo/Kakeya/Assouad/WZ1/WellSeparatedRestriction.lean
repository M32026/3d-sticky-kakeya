import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremLocalizationStatements
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.ExponentArithmetic

/-!
# Restriction infrastructure for WZ1 Proposition 45

These lemmas retain the actual graph while restricting one active vertex
class.  They provide the cardinality and Frostman estimates needed before
applying the supplied hypergraph refinement theorem.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
If `B ⊆ A` retains an `f` fraction of the points of `A`, then the Frostman
constant degrades by at most `1 / f`.
-/
lemma frostman_retained_subset
    {A B : DiscreteSet 2} {delta s : ℝ} {C f : ENNReal}
    (hA_frost : A.IsFrostman delta s C)
    (hB_sub : B ⊆ A)
    (h_ret : f * A.enncard ≤ B.enncard)
    (hf_pos : 0 < f) (hf_ne_top : f ≠ ⊤) :
    B.IsFrostman delta s (C / f) := by
  intro x r hr1 hr2
  have h_ball_mono : B.ballCount x r ≤ A.ballCount x r := by
    simp only [DiscreteSet.ballCount]
    exact_mod_cast
      Finset.card_le_card
        (Finset.filter_subset_filter
          (fun y => dist y x ≤ r) hB_sub)
  have hA_card : A.enncard ≤ B.enncard / f := by
    have h_scaled :
        f⁻¹ * (f * A.enncard) ≤ f⁻¹ * B.enncard := by
      gcongr
    have h_cancel : f⁻¹ * f = 1 :=
      ENNReal.inv_mul_cancel hf_pos.ne' hf_ne_top
    have h_left : f⁻¹ * (f * A.enncard) = A.enncard := by
      rw [← mul_assoc, h_cancel, one_mul]
    have h_right : B.enncard / f = f⁻¹ * B.enncard := by
      simp [div_eq_mul_inv, mul_comm]
    rw [h_left] at h_scaled
    rwa [h_right]
  calc
    B.ballCount x r
        ≤ A.ballCount x r := h_ball_mono
    _ ≤ C * Kakeya.realRpowENN r s * A.enncard :=
      hA_frost x r hr1 hr2
    _ ≤ C * Kakeya.realRpowENN r s * (B.enncard / f) := by
      gcongr
    _ = (C / f) * Kakeya.realRpowENN r s * B.enncard := by
      simp only [div_eq_mul_inv]
      ac_rfl

/--
After restricting an actual tripartite graph to active `F'` vertices, its
cardinality is at least
`c * |F'| * |G₁| * |G₂|`.
-/
lemma restrict_f_card_lower
    {c : ENNReal} {F G₁ G₂ F' : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hDensity : WZ1UniformTripleDensity c F G₁ G₂ H)
    (hF'_active :
      ∀ vertex ∈ F', ∃ edge ∈ H, edge.1 = vertex) :
    c * (F'.card : ENNReal) * (G₁.card : ENNReal) *
        (G₂.card : ENNReal) ≤
      ((H.filter fun edge => edge.1 ∈ F').card : ENNReal) := by
  classical
  let encoded := wz1EncodeTriples H
  let classes := wz1TripleVertexClasses F G₁ G₂
  have h_density :
      WZ1UniformHypergraphDensity c classes encoded :=
    hDensity.2
  have h_fiber_bound :
      ∀ vertex ∈ F',
        c * (G₁.card : ENNReal) * (G₂.card : ENNReal) ≤
          ((encoded.filter fun edge => edge 0 = vertex).card :
            ENNReal) := by
    intro vertex hvertex
    rcases hF'_active vertex hvertex with
      ⟨edge, hedge, hedge_eq⟩
    let encodedEdge : Fin 3 → Point2 :=
      wz1TripleCoordinate edge
    have hencodedEdge : encodedEdge ∈ encoded :=
      Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
    have hcoord : encodedEdge 0 = vertex := by
      simp [encodedEdge, wz1TripleCoordinate, hedge_eq]
    have h :=
      h_density.2 encodedEdge hencodedEdge ({0} : Finset (Fin 3))
    have h_complement :
        (Finset.univ : Finset (Fin 3)) \ {0} = {1, 2} := by
      ext index
      fin_cases index <;> simp
    have h_product :
        wz1VertexCardProduct classes ({1, 2} : Finset (Fin 3)) =
          (G₁.card : ENNReal) * (G₂.card : ENNReal) := by
      simp [classes, wz1VertexCardProduct,
        wz1TripleVertexClasses, Finset.prod]
    have h_fiber :
        wz1HypergraphFiber encoded {0} encodedEdge =
          encoded.filter fun other => other 0 = vertex := by
      ext other
      simp [wz1HypergraphFiber, hcoord]
    rw [h_complement, h_product, h_fiber] at h
    simpa [mul_assoc] using h
  have h_disjoint :
      Set.PairwiseDisjoint (↑F')
        (fun vertex => encoded.filter fun edge => edge 0 = vertex) := by
    intro first _ second _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro edge hedgeFirst hedgeSecond
    have h1 : edge 0 = first :=
      (Finset.mem_filter.mp hedgeFirst).2
    have h2 : edge 0 = second :=
      (Finset.mem_filter.mp hedgeSecond).2
    exact hne (h1.symm.trans h2)
  have h_union :
      encoded.filter (fun edge => edge 0 ∈ F') =
        F'.biUnion
          (fun vertex => encoded.filter fun edge => edge 0 = vertex) := by
    ext edge
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hedge, hcoord⟩
      exact ⟨edge 0, hcoord, hedge, rfl⟩
    · rintro ⟨vertex, hvertex, hedge, hcoord⟩
      exact ⟨hedge, hcoord.symm ▸ hvertex⟩
  have h_card_union :
      ((F'.biUnion
          (fun vertex => encoded.filter fun edge => edge 0 = vertex)).card :
        ENNReal) =
        ∑ vertex ∈ F',
          ((encoded.filter fun edge => edge 0 = vertex).card :
            ENNReal) := by
    exact_mod_cast Finset.card_biUnion h_disjoint
  have h_sum_lower :
      ((encoded.filter fun edge => edge 0 ∈ F').card : ENNReal) ≥
        ∑ vertex ∈ F',
          c * (G₁.card : ENNReal) * (G₂.card : ENNReal) := by
    rw [h_union, h_card_union]
    apply Finset.sum_le_sum
    intro vertex hvertex
    exact h_fiber_bound vertex hvertex
  have h_encoded_filter :
      encoded.filter (fun edge => edge 0 ∈ F') =
        wz1EncodeTriples
          (H.filter fun edge => edge.1 ∈ F') := by
    ext encodedEdge
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hencoded, hcoord⟩
      rcases Finset.mem_image.mp hencoded with ⟨edge, hedge, rfl⟩
      exact Finset.mem_image.mpr
        ⟨edge, Finset.mem_filter.mpr
          ⟨hedge, by simpa [wz1TripleCoordinate] using hcoord⟩, rfl⟩
    · intro hencoded
      rcases Finset.mem_image.mp hencoded with ⟨edge, hedge, rfl⟩
      exact
        ⟨Finset.mem_image.mpr
            ⟨edge, (Finset.mem_filter.mp hedge).1, rfl⟩,
          by simpa [wz1TripleCoordinate] using
            (Finset.mem_filter.mp hedge).2⟩
  have h_encode_card :
      (wz1EncodeTriples
          (H.filter fun edge => edge.1 ∈ F')).card =
        (H.filter fun edge => edge.1 ∈ F').card :=
    by
      rw [wz1EncodeTriples,
        Finset.card_image_of_injective]
      intro first second h
      have h0 := congr_fun h 0
      have h1 := congr_fun h 1
      have h2 := congr_fun h 2
      exact Prod.ext h0 (Prod.ext h1 h2)
  rw [h_encoded_filter, h_encode_card] at h_sum_lower
  simpa [Finset.sum_const, mul_assoc, mul_comm, mul_left_comm]
    using h_sum_lower

/--
After restricting an actual tripartite graph to active `G₁'` vertices, its
cardinality is at least
`c * |F| * |G₁'| * |G₂|`.
-/
lemma restrict_g1_card_lower
    {c : ENNReal} {F G₁ G₂ G₁' : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hDensity : WZ1UniformTripleDensity c F G₁ G₂ H)
    (hG₁'_active :
      ∀ vertex ∈ G₁', ∃ edge ∈ H, edge.2.1 = vertex) :
    c * (F.card : ENNReal) * (G₁'.card : ENNReal) *
        (G₂.card : ENNReal) ≤
      ((H.filter fun edge => edge.2.1 ∈ G₁').card : ENNReal) := by
  classical
  let encoded := wz1EncodeTriples H
  let classes := wz1TripleVertexClasses F G₁ G₂
  have h_density :
      WZ1UniformHypergraphDensity c classes encoded :=
    hDensity.2
  have h_fiber_bound :
      ∀ vertex ∈ G₁',
        c * (F.card : ENNReal) * (G₂.card : ENNReal) ≤
          ((encoded.filter fun edge => edge 1 = vertex).card :
            ENNReal) := by
    intro vertex hvertex
    rcases hG₁'_active vertex hvertex with
      ⟨edge, hedge, hedge_eq⟩
    let encodedEdge : Fin 3 → Point2 :=
      wz1TripleCoordinate edge
    have hencodedEdge : encodedEdge ∈ encoded := by
      exact Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
    have hcoord : encodedEdge 1 = vertex := by
      simp [encodedEdge, wz1TripleCoordinate, hedge_eq]
    have h :=
      h_density.2 encodedEdge hencodedEdge ({1} : Finset (Fin 3))
    have h_complement :
        (Finset.univ : Finset (Fin 3)) \ {1} = {0, 2} := by
      ext index
      fin_cases index <;> simp
    have h_product :
        wz1VertexCardProduct classes ({0, 2} : Finset (Fin 3)) =
          (F.card : ENNReal) * (G₂.card : ENNReal) := by
      simp [classes, wz1VertexCardProduct,
        wz1TripleVertexClasses, Finset.prod]
      <;> ac_rfl
    have h_fiber :
        wz1HypergraphFiber encoded {1} encodedEdge =
          encoded.filter fun other => other 1 = vertex := by
      ext other
      simp [wz1HypergraphFiber, hcoord]
      <;> aesop
    rw [h_complement, h_product, h_fiber] at h
    simpa [mul_assoc] using h
  have h_disjoint :
      Set.PairwiseDisjoint (↑G₁')
        (fun vertex => encoded.filter fun edge => edge 1 = vertex) := by
    intro first hfirst second hsecond hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro edge hedgeFirst hedgeSecond
    have h1 : edge 1 = first :=
      (Finset.mem_filter.mp hedgeFirst).2
    have h2 : edge 1 = second :=
      (Finset.mem_filter.mp hedgeSecond).2
    exact hne (h1.symm.trans h2)
  have h_union :
      encoded.filter (fun edge => edge 1 ∈ G₁') =
        G₁'.biUnion
          (fun vertex => encoded.filter fun edge => edge 1 = vertex) := by
    ext edge
    simp [Finset.mem_biUnion]
    <;> tauto
  have h_card_union :
      ((G₁'.biUnion
          (fun vertex => encoded.filter fun edge => edge 1 = vertex)).card :
        ENNReal) =
        ∑ vertex ∈ G₁',
          ((encoded.filter fun edge => edge 1 = vertex).card :
            ENNReal) := by
    have h :=
      Finset.card_biUnion h_disjoint
    exact_mod_cast h
  have h_sum_lower :
      ((encoded.filter fun edge => edge 1 ∈ G₁').card : ENNReal) ≥
        ∑ vertex ∈ G₁',
          c * (F.card : ENNReal) * (G₂.card : ENNReal) := by
    rw [h_union, h_card_union]
    apply Finset.sum_le_sum
    intro vertex hvertex
    exact h_fiber_bound vertex hvertex
  have h_encoded_filter :
      encoded.filter (fun edge => edge 1 ∈ G₁') =
        wz1EncodeTriples
          (H.filter fun edge => edge.2.1 ∈ G₁') := by
    ext encodedEdge
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hencoded, hcoord⟩
      rcases Finset.mem_image.mp hencoded with ⟨edge, hedge, rfl⟩
      exact Finset.mem_image.mpr
        ⟨edge, Finset.mem_filter.mpr
          ⟨hedge, by simpa [wz1TripleCoordinate] using hcoord⟩, rfl⟩
    · intro hencoded
      rcases Finset.mem_image.mp hencoded with ⟨edge, hedge, rfl⟩
      exact
        ⟨Finset.mem_image.mpr
            ⟨edge, (Finset.mem_filter.mp hedge).1, rfl⟩,
          by simpa [wz1TripleCoordinate] using
            (Finset.mem_filter.mp hedge).2⟩
  have h_encode_card :
      (wz1EncodeTriples
          (H.filter fun edge => edge.2.1 ∈ G₁')).card =
        (H.filter fun edge => edge.2.1 ∈ G₁').card := by
    rw [wz1EncodeTriples,
      Finset.card_image_of_injective]
    intro first second h
    have h0 := congr_fun h 0
    have h1 := congr_fun h 1
    have h2 := congr_fun h 2
    exact Prod.ext h0 (Prod.ext h1 h2)
  rw [h_encoded_filter, h_encode_card] at h_sum_lower
  simpa [Finset.sum_const, mul_assoc, mul_comm, mul_left_comm]
    using h_sum_lower

/--
After restricting an actual tripartite graph to active `G₂'` vertices, its
cardinality is at least
`c * |F| * |G₁| * |G₂'|`.
-/
lemma restrict_g2_card_lower
    {c : ENNReal} {F G₁ G₂ G₂' : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hDensity : WZ1UniformTripleDensity c F G₁ G₂ H)
    (hG₂'_active :
      ∀ vertex ∈ G₂', ∃ edge ∈ H, edge.2.2 = vertex) :
    c * (F.card : ENNReal) * (G₁.card : ENNReal) *
        (G₂'.card : ENNReal) ≤
      ((H.filter fun edge => edge.2.2 ∈ G₂').card : ENNReal) := by
  classical
  let encoded := wz1EncodeTriples H
  let classes := wz1TripleVertexClasses F G₁ G₂
  have h_density :
      WZ1UniformHypergraphDensity c classes encoded :=
    hDensity.2
  have h_fiber_bound :
      ∀ vertex ∈ G₂',
        c * (F.card : ENNReal) * (G₁.card : ENNReal) ≤
          ((encoded.filter fun edge => edge 2 = vertex).card :
            ENNReal) := by
    intro vertex hvertex
    rcases hG₂'_active vertex hvertex with
      ⟨edge, hedge, hedge_eq⟩
    let encodedEdge : Fin 3 → Point2 :=
      wz1TripleCoordinate edge
    have hencodedEdge : encodedEdge ∈ encoded :=
      Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
    have hcoord : encodedEdge 2 = vertex := by
      simp [encodedEdge, wz1TripleCoordinate, hedge_eq]
    have h :=
      h_density.2 encodedEdge hencodedEdge ({2} : Finset (Fin 3))
    have h_complement :
        (Finset.univ : Finset (Fin 3)) \ {2} = {0, 1} := by
      ext index
      fin_cases index <;> simp
    have h_product :
        wz1VertexCardProduct classes ({0, 1} : Finset (Fin 3)) =
          (F.card : ENNReal) * (G₁.card : ENNReal) := by
      simp [classes, wz1VertexCardProduct,
        wz1TripleVertexClasses, Finset.prod]
      <;> ac_rfl
    have h_fiber :
        wz1HypergraphFiber encoded {2} encodedEdge =
          encoded.filter fun other => other 2 = vertex := by
      ext other
      simp [wz1HypergraphFiber, hcoord]
      <;> aesop
    rw [h_complement, h_product, h_fiber] at h
    simpa [mul_assoc] using h
  have h_disjoint :
      Set.PairwiseDisjoint (↑G₂')
        (fun vertex => encoded.filter fun edge => edge 2 = vertex) := by
    intro first hfirst second hsecond hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro edge hedgeFirst hedgeSecond
    have h1 : edge 2 = first :=
      (Finset.mem_filter.mp hedgeFirst).2
    have h2 : edge 2 = second :=
      (Finset.mem_filter.mp hedgeSecond).2
    exact hne (h1.symm.trans h2)
  have h_union :
      encoded.filter (fun edge => edge 2 ∈ G₂') =
        G₂'.biUnion
          (fun vertex => encoded.filter fun edge => edge 2 = vertex) := by
    ext edge
    simp [Finset.mem_biUnion]
    <;> tauto
  have h_card_union :
      ((G₂'.biUnion
          (fun vertex => encoded.filter fun edge => edge 2 = vertex)).card :
        ENNReal) =
        ∑ vertex ∈ G₂',
          ((encoded.filter fun edge => edge 2 = vertex).card :
            ENNReal) := by
    have h :=
      Finset.card_biUnion h_disjoint
    exact_mod_cast h
  have h_sum_lower :
      ((encoded.filter fun edge => edge 2 ∈ G₂').card : ENNReal) ≥
        ∑ vertex ∈ G₂',
          c * (F.card : ENNReal) * (G₁.card : ENNReal) := by
    rw [h_union, h_card_union]
    apply Finset.sum_le_sum
    intro vertex hvertex
    exact h_fiber_bound vertex hvertex
  have h_encoded_filter :
      encoded.filter (fun edge => edge 2 ∈ G₂') =
        wz1EncodeTriples
          (H.filter fun edge => edge.2.2 ∈ G₂') := by
    ext encodedEdge
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hencoded, hcoord⟩
      rcases Finset.mem_image.mp hencoded with ⟨edge, hedge, rfl⟩
      exact Finset.mem_image.mpr
        ⟨edge, Finset.mem_filter.mpr
          ⟨hedge, by simpa [wz1TripleCoordinate] using hcoord⟩, rfl⟩
    · intro hencoded
      rcases Finset.mem_image.mp hencoded with ⟨edge, hedge, rfl⟩
      exact
        ⟨Finset.mem_image.mpr
            ⟨edge, (Finset.mem_filter.mp hedge).1, rfl⟩,
          by simpa [wz1TripleCoordinate] using
            (Finset.mem_filter.mp hedge).2⟩
  have h_encode_card :
      (wz1EncodeTriples
          (H.filter fun edge => edge.2.2 ∈ G₂')).card =
        (H.filter fun edge => edge.2.2 ∈ G₂').card := by
    rw [wz1EncodeTriples,
      Finset.card_image_of_injective]
    intro first second h
    have h0 := congr_fun h 0
    have h1 := congr_fun h 1
    have h2 := congr_fun h 2
    exact Prod.ext h0 (Prod.ext h1 h2)
  rw [h_encoded_filter, h_encode_card] at h_sum_lower
  simpa [Finset.sum_const, mul_assoc, mul_comm, mul_left_comm]
    using h_sum_lower

/--
Two nested retained subsets degrade a Frostman constant by exactly the two
retention factors.  In the Proposition 45 hierarchy this gives
`2 * delta^(-(2 * eta + zeta))`.
-/
lemma frostman_two_step_retention
    {G active selected : DiscreteSet 2}
    {delta eta zeta : ℝ}
    (hG_frost :
      G.IsFrostman delta 1
        (Kakeya.realRpowENN delta (-eta)))
    (hactive_sub : active ⊆ G)
    (hactive_ret :
      Kakeya.realRpowENN delta eta * G.enncard ≤ active.enncard)
    (hselected_sub : selected ⊆ active)
    (hselected_ret :
      (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta zeta * active.enncard ≤
        selected.enncard)
    (heta : 0 < eta) (hzeta : 0 < zeta)
    (hdelta : 0 < delta) :
    selected.IsFrostman delta 1
      ((2 : ENNReal) *
        Kakeya.realRpowENN delta (-(2 * eta + zeta))) := by
  let firstRetention : ENNReal :=
    Kakeya.realRpowENN delta eta
  let secondRetention : ENNReal :=
    (1 / 2 : ENNReal) * Kakeya.realRpowENN delta zeta
  have hfirst_pos : 0 < firstRetention := by
    simp [firstRetention, Kakeya.realRpowENN,
      ENNReal.ofReal_pos, Real.rpow_pos_of_pos hdelta]
  have hfirst_top : firstRetention ≠ ⊤ := by
    simp [firstRetention, Kakeya.realRpowENN]
  have hsecond_pos : 0 < secondRetention := by
    have hpow :
        0 < Kakeya.realRpowENN delta zeta := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_pos,
        Real.rpow_pos_of_pos hdelta]
    exact ENNReal.mul_pos (by norm_num) hpow.ne'
  have hsecond_top : secondRetention ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp)
      (by simp [Kakeya.realRpowENN])
  have hactive_frost :
      active.IsFrostman delta 1
        (Kakeya.realRpowENN delta (-eta) / firstRetention) :=
    frostman_retained_subset
      hG_frost hactive_sub hactive_ret hfirst_pos hfirst_top
  have hselected_frost :
      selected.IsFrostman delta 1
        ((Kakeya.realRpowENN delta (-eta) / firstRetention) /
          secondRetention) :=
    frostman_retained_subset
      hactive_frost hselected_sub hselected_ret
      hsecond_pos hsecond_top
  have hconstant :
      (Kakeya.realRpowENN delta (-eta) / firstRetention) /
          secondRetention =
        (2 : ENNReal) *
          Kakeya.realRpowENN delta (-(2 * eta + zeta)) := by
    have hreal :
        delta ^ (-eta) / delta ^ eta /
            ((1 / 2 : ℝ) * delta ^ zeta) =
          (2 : ℝ) * delta ^ (-(2 * eta + zeta)) := by
      have h1 :
          delta ^ (-eta) / delta ^ eta =
            delta ^ (-2 * eta) := by
        rw [← Real.rpow_sub hdelta]
        congr 1
        ring
      rw [h1]
      have hpow : 0 < delta ^ zeta := by positivity
      have h2 :
          delta ^ (-2 * eta) /
              ((1 / 2 : ℝ) * delta ^ zeta) =
            (2 : ℝ) *
              (delta ^ (-2 * eta) / delta ^ zeta) := by
        field_simp [hpow.ne']
      rw [h2]
      have h3 :
          delta ^ (-2 * eta) / delta ^ zeta =
            delta ^ (-(2 * eta + zeta)) := by
        rw [← Real.rpow_sub hdelta]
        congr 1
        ring
      rw [h3]
    have hleft_top :
        (Kakeya.realRpowENN delta (-eta) / firstRetention) /
            secondRetention ≠ ⊤ := by
      exact ENNReal.div_ne_top
        (ENNReal.div_ne_top (by simp [Kakeya.realRpowENN])
          hfirst_pos.ne')
        hsecond_pos.ne'
    have hright_top :
        (2 : ENNReal) *
            Kakeya.realRpowENN delta (-(2 * eta + zeta)) ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by simp)
        (by simp [Kakeya.realRpowENN])
    have hleft_real :
        ENNReal.toReal
            ((Kakeya.realRpowENN delta (-eta) / firstRetention) /
              secondRetention) =
          delta ^ (-eta) / delta ^ eta /
            ((1 / 2 : ℝ) * delta ^ zeta) := by
      rw [ENNReal.toReal_div, ENNReal.toReal_div]
      have h_a :
          ENNReal.toReal (Kakeya.realRpowENN delta (-eta)) =
            delta ^ (-eta) := by
        simp [Kakeya.realRpowENN, ENNReal.toReal_ofReal]
        <;> positivity
      have h_b : ENNReal.toReal firstRetention = delta ^ eta := by
        simp [firstRetention, Kakeya.realRpowENN,
          ENNReal.toReal_ofReal]
        <;> positivity
      have h_c :
          ENNReal.toReal secondRetention =
            (1 / 2 : ℝ) * delta ^ zeta := by
        simp [secondRetention, Kakeya.realRpowENN,
          ENNReal.toReal_ofReal, ENNReal.toReal_mul]
        <;> positivity
      rw [h_a, h_b, h_c]
    have hright_real :
        ENNReal.toReal
            ((2 : ENNReal) *
              Kakeya.realRpowENN delta (-(2 * eta + zeta))) =
          (2 : ℝ) * delta ^ (-(2 * eta + zeta)) := by
      rw [ENNReal.toReal_mul]
      simp [Kakeya.realRpowENN, ENNReal.toReal_ofReal]
      <;> positivity
    apply (ENNReal.toReal_eq_toReal_iff' hleft_top hright_top).mp
    rw [hleft_real, hright_real, hreal]
  rwa [hconstant] at hselected_frost

/--
Choose one scale threshold that simultaneously absorbs the factor two in the
two-step Frostman loss and the factor `1 / 16` in the Lemma 37 density
constant.
-/
lemma exists_restriction_absorption_threshold
    (eta eta' zeta : ℝ)
    (heta : 0 ≤ eta) (hzeta : 0 ≤ zeta)
    (hgap : 2 * eta + zeta < eta') :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        (2 : ENNReal) *
            Kakeya.realRpowENN delta (-(2 * eta + zeta)) ≤
          Kakeya.realRpowENN delta (-eta') ∧
        Kakeya.realRpowENN delta eta' ≤
          (1 / 16 : ENNReal) *
            Kakeya.realRpowENN delta eta := by
  have hbase : 0 ≤ 2 * eta + zeta := by linarith
  rcases exists_scale_absorb_constant
      (2 : ENNReal) (by norm_num) hbase hgap with
    ⟨deltaFrostman, hdeltaFrostman, hdeltaFrostmanOne,
      hFrostman⟩
  have heta_eta' : eta < eta' := by linarith
  rcases exists_delta₀_const_mul_rpow_le
      16 (by norm_num) eta eta' heta_eta' with
    ⟨deltaDensity, hdeltaDensity, hdeltaDensityOne,
      hDensity⟩
  let delta₀ := min deltaFrostman deltaDensity
  have hdelta₀ : 0 < delta₀ := by positivity
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans hdeltaFrostmanOne
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaLe
  have hdeltaFrostmanLe : delta ≤ deltaFrostman :=
    hdeltaLe.trans (min_le_left _ _)
  have hdeltaDensityLe : delta ≤ deltaDensity :=
    hdeltaLe.trans (min_le_right _ _)
  have hFrostman' :=
    hFrostman delta hdelta hdeltaFrostmanLe
  have hDensity' :
      (16 : ENNReal) * Kakeya.realRpowENN delta eta' ≤
        Kakeya.realRpowENN delta eta := by
    simpa using hDensity delta hdelta hdeltaDensityLe
  have hDensityDiv :
      Kakeya.realRpowENN delta eta' ≤
        Kakeya.realRpowENN delta eta / 16 := by
    rw [ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    simpa [mul_comm] using hDensity'
  refine ⟨hFrostman', ?_⟩
  simpa [div_eq_mul_inv, mul_comm] using hDensityDiv

/--
Transport Lemma 49's long-projection conclusion from an actual subgraph to
the original graph while weakening the loss exponent and the covering
exponent.
-/
lemma long_projection_mono
    {delta epsilon epsilon' eta eta' : ℝ}
    {Hsmall H : Finset (Point2 × Point2 × Point2)}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hepsilon : epsilon' ≤ epsilon)
    (heta : eta ≤ eta') (heta' : 0 < eta')
    (hsub : Hsmall ⊆ H)
    (h :
      WZ1StripLocalizationLongProjection
        delta epsilon' eta' Hsmall) :
    WZ1StripLocalizationLongProjection
      delta epsilon eta H := by
  rcases h with
    ⟨rho, center, radius, hdelta_rho, hrho_one,
      hradius, hlength, hcover⟩
  have hrho_pos : 0 < rho := hdelta.trans_le hdelta_rho
  have hrho_nonneg : 0 ≤ rho := hrho_pos.le
  have hlength' :
      Real.rpow delta (-eta) * rho ≤ 2 * radius := by
    have hpower :
        Real.rpow delta (-eta) ≤ Real.rpow delta (-eta') :=
      Real.rpow_le_rpow_of_exponent_ge
        hdelta hdelta_one (by linarith)
    exact
      (mul_le_mul_of_nonneg_right hpower hrho_nonneg).trans hlength
  have hratio : 1 ≤ 2 * radius / rho := by
    have hpower_one :
        1 ≤ Real.rpow delta (-eta') :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        hdelta hdelta_one (by linarith)
    have hrho_le : rho ≤ 2 * radius := by
      calc
        rho = 1 * rho := by ring
        _ ≤ Real.rpow delta (-eta') * rho := by gcongr
        _ ≤ 2 * radius := hlength
    exact (le_div_iff₀ hrho_pos).2 (by simpa using hrho_le)
  have hpower_cover :
      Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon) ≤
        Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon') := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_le hratio (by linarith)
  have hdot :
      wz1DotDifferenceSet Hsmall ⊆ wz1DotDifferenceSet H := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with
      ⟨edge, hedge, rfl⟩
    exact Finset.mem_image.mpr ⟨edge, hsub hedge, rfl⟩
  have hintersection :
      wz1DotDifferenceSet Hsmall ∩ Metric.closedBall center radius ⊆
        wz1DotDifferenceSet H ∩ Metric.closedBall center radius :=
    Set.inter_subset_inter_left _ hdot
  have hcover_mono :
      (↑(Metric.externalCoveringNumber
          (Real.toNNReal rho)
          (wz1DotDifferenceSet Hsmall ∩
            Metric.closedBall center radius)) : ENNReal) ≤
        (↑(Metric.externalCoveringNumber
          (Real.toNNReal rho)
          (wz1DotDifferenceSet H ∩
            Metric.closedBall center radius)) : ENNReal) := by
    exact_mod_cast
      Metric.externalCoveringNumber_mono_set hintersection
  exact
    ⟨rho, center, radius, hdelta_rho, hrho_one,
      hradius, hlength',
      hpower_cover.trans (hcover.trans hcover_mono)⟩

end Kakeya.Assouad
