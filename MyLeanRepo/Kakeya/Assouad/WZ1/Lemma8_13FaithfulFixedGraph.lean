import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.InducedTripleRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.WellSeparatedRestriction

/-!
# Fixed-viewpoint graph cardinality for faithful PDF Lemma 8.13

Restricting a uniformly dense tripartite graph to actual selected second
coordinates and one fixed third-coordinate viewpoint retains the expected
first-coordinate fiber mass.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
After restricting an actual tripartite graph to active `selected` second
coordinates and a fixed third-coordinate viewpoint, its cardinality is at
least `c * |F| * |selected|`.
-/
lemma restrict_g1_g2_card_lower
    {c : ENNReal} {F G₁ G₂ : DiscreteSet 2}
    {selected : DiscreteSet 2} {viewpoint : Point2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hDensity : WZ1UniformTripleDensity c F G₁ G₂ H)
    (hselected_active :
      ∀ b ∈ selected,
        ∃ edge ∈ H,
          edge.2.1 = b ∧ edge.2.2 = viewpoint) :
    c * F.enncard * selected.enncard ≤
      ((H.filter fun edge =>
        edge.2.1 ∈ selected ∧ edge.2.2 = viewpoint).card : ENNReal) := by
  classical
  let encoded := wz1EncodeTriples H
  let classes := wz1TripleVertexClasses F G₁ G₂
  have hDensityEncoded :
      WZ1UniformHypergraphDensity c classes encoded :=
    hDensity.2
  have hfiberBound :
      ∀ b ∈ selected,
        c * F.enncard ≤
          ((encoded.filter fun edge =>
            edge 1 = b ∧ edge 2 = viewpoint).card : ENNReal) := by
    intro b hb
    rcases hselected_active b hb with
      ⟨edge, hedge, hsecond, hthird⟩
    let encodedEdge : Fin 3 → Point2 :=
      wz1TripleCoordinate edge
    have hencodedEdge : encodedEdge ∈ encoded :=
      Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
    have hcoordSecond : encodedEdge 1 = b := by
      simp [encodedEdge, wz1TripleCoordinate, hsecond]
    have hcoordThird : encodedEdge 2 = viewpoint := by
      simp [encodedEdge, wz1TripleCoordinate, hthird]
    have hfiber :=
      hDensityEncoded.2 encodedEdge hencodedEdge
        ({1, 2} : Finset (Fin 3))
    have hcomplement :
        (Finset.univ : Finset (Fin 3)) \
            ({1, 2} : Finset (Fin 3)) = {0} := by
      ext index
      fin_cases index <;> simp
    have hproduct :
        wz1VertexCardProduct classes ({0} : Finset (Fin 3)) =
          F.enncard := by
      simp [classes, wz1VertexCardProduct,
        wz1TripleVertexClasses, Finset.prod,
        DiscreteSet.enncard]
    have hfiberEq :
        wz1HypergraphFiber encoded
            ({1, 2} : Finset (Fin 3)) encodedEdge =
          encoded.filter fun other =>
            other 1 = b ∧ other 2 = viewpoint := by
      ext other
      simp [wz1HypergraphFiber, hcoordSecond, hcoordThird]
    rw [hcomplement, hproduct, hfiberEq] at hfiber
    exact hfiber
  have hdisjoint :
      Set.PairwiseDisjoint (↑selected)
        (fun b =>
          encoded.filter fun edge =>
            edge 1 = b ∧ edge 2 = viewpoint) := by
    intro first _ second _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro edge hedgeFirst hedgeSecond
    have hfirst :
        edge 1 = first :=
      (Finset.mem_filter.mp hedgeFirst).2.1
    have hsecond :
        edge 1 = second :=
      (Finset.mem_filter.mp hedgeSecond).2.1
    exact hne (hfirst.symm.trans hsecond)
  have hunion :
      encoded.filter (fun edge =>
          edge 1 ∈ selected ∧ edge 2 = viewpoint) =
        selected.biUnion fun b =>
          encoded.filter fun edge =>
            edge 1 = b ∧ edge 2 = viewpoint := by
    ext edge
    simp [Finset.mem_biUnion]
    tauto
  have hcardUnion :
      ((selected.biUnion fun b =>
          encoded.filter fun edge =>
            edge 1 = b ∧ edge 2 = viewpoint).card : ENNReal) =
        ∑ b ∈ selected,
          ((encoded.filter fun edge =>
            edge 1 = b ∧ edge 2 = viewpoint).card : ENNReal) := by
    exact_mod_cast Finset.card_biUnion hdisjoint
  have hsumLower :
      ((encoded.filter fun edge =>
          edge 1 ∈ selected ∧ edge 2 = viewpoint).card : ENNReal) ≥
        ∑ b ∈ selected, c * F.enncard := by
    rw [hunion, hcardUnion]
    exact Finset.sum_le_sum hfiberBound
  have hencodedFilter :
      encoded.filter (fun edge =>
          edge 1 ∈ selected ∧ edge 2 = viewpoint) =
        wz1EncodeTriples
          (H.filter fun edge =>
            edge.2.1 ∈ selected ∧ edge.2.2 = viewpoint) := by
    ext encodedEdge
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hencoded, hcoordinates⟩
      rcases Finset.mem_image.mp hencoded with
        ⟨edge, hedge, rfl⟩
      exact Finset.mem_image.mpr
        ⟨edge,
          Finset.mem_filter.mpr
            ⟨hedge,
              by simpa [wz1TripleCoordinate] using hcoordinates⟩,
          rfl⟩
    · intro hencoded
      rcases Finset.mem_image.mp hencoded with
        ⟨edge, hedge, rfl⟩
      exact
        ⟨Finset.mem_image.mpr
            ⟨edge, (Finset.mem_filter.mp hedge).1, rfl⟩,
          by
            simpa [wz1TripleCoordinate] using
              (Finset.mem_filter.mp hedge).2⟩
  have hencodeCard :
      (wz1EncodeTriples
        (H.filter fun edge =>
          edge.2.1 ∈ selected ∧
            edge.2.2 = viewpoint)).card =
        (H.filter fun edge =>
          edge.2.1 ∈ selected ∧
            edge.2.2 = viewpoint).card := by
    rw [wz1EncodeTriples, Finset.card_image_of_injective]
    intro first second heq
    have hfirst := congr_fun heq 0
    have hsecond := congr_fun heq 1
    have hthird := congr_fun heq 2
    exact Prod.ext hfirst (Prod.ext hsecond hthird)
  rw [hencodedFilter, hencodeCard] at hsumLower
  rw [show selected.enncard =
      (selected.card : ENNReal) by
        simp [DiscreteSet.enncard]]
  simpa [Finset.sum_const, mul_assoc, mul_comm,
    mul_left_comm] using hsumLower

/--
The separated-source count and one fixed-viewpoint refinement give the
frozen `3 * eta` normalized endpoint cardinality.

The first `2 * eta` comes from cancelling the source Frostman constant
`delta^(-eta)` against its density `delta^eta`.  The final active projection
pays the remaining density factor `delta^eta / 16`.
-/
lemma wz1Lemma8_13_normalized_source_cardinality
    {delta eta u : ℝ}
    (hdelta : 0 < delta)
    {F selected G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hselected :
      Kakeya.realRpowENN delta eta ≤
        Kakeya.realRpowENN delta (-eta) *
          Kakeya.realRpowENN u 1 * selected.enncard)
    (hDensity :
      WZ1UniformTripleDensity
        (Kakeya.realRpowENN delta eta / 16)
        F selected G₂ H)
    (endpointMap : Point2 ≃ Point2) :
    let mapped : DiscreteSet 2 :=
      (wz1ActiveTripleProjection H 1).image endpointMap
    Kakeya.realRpowENN delta (3 * eta) ≤
      16 * Kakeya.realRpowENN u 1 *
        mapped.enncard := by
  dsimp only
  let density := Kakeya.realRpowENN delta eta
  let inverseDensity := Kakeya.realRpowENN delta (-eta)
  let scale := Kakeya.realRpowENN u 1
  let source := wz1ActiveTripleProjection H 1
  have hdensityInverse :
      density * inverseDensity = 1 := by
    dsimp only [density, inverseDensity]
    rw [← realRpowENN_add hdelta]
    convert
      (show Kakeya.realRpowENN delta 0 = 1 by
        simp [Kakeya.realRpowENN]) using 1 <;> ring
  have hselectedScaled :
      density * density ≤ scale * selected.enncard := by
    calc
      density * density ≤
          density *
            (inverseDensity * scale * selected.enncard) :=
        mul_le_mul_left' hselected density
      _ = (density * inverseDensity) *
          scale * selected.enncard := by ring
      _ = scale * selected.enncard := by
        rw [hdensityInverse, one_mul]
  have hprojection :
      (density / 16) * selected.enncard ≤ source.enncard := by
    simpa [density, source, wz1TripleVertexClasses] using
      active_triple_projection_card_lower hDensity 1
  have hprojectionScaled :
      density * selected.enncard ≤ 16 * source.enncard := by
    calc
      density * selected.enncard =
          16 * ((density / 16) * selected.enncard) := by
            symm
            calc
              16 * ((density / 16) * selected.enncard) =
                  (density / 16 * 16) * selected.enncard := by
                    ring
              _ = density * selected.enncard := by
                rw [ENNReal.div_mul_cancel] <;> norm_num
      _ ≤ 16 * source.enncard :=
        mul_le_mul_left' hprojection 16
  have hpower :
      density * density * density =
        Kakeya.realRpowENN delta (3 * eta) := by
    calc
      density * density * density =
          Kakeya.realRpowENN delta (eta + eta) *
            Kakeya.realRpowENN delta eta := by
              rw [realRpowENN_add hdelta]
      _ =
          Kakeya.realRpowENN delta ((eta + eta) + eta) := by
            exact
              (realRpowENN_add hdelta (eta + eta) eta).symm
      _ = Kakeya.realRpowENN delta (3 * eta) := by
        congr 1
        ring
  have hsource :
      Kakeya.realRpowENN delta (3 * eta) ≤
        16 * scale * source.enncard := by
    rw [← hpower]
    calc
      density * density * density ≤
          (scale * selected.enncard) * density := by
            gcongr
      _ = scale * (density * selected.enncard) := by ring
      _ ≤ scale * (16 * source.enncard) :=
        mul_le_mul_left' hprojectionScaled scale
      _ = 16 * scale * source.enncard := by ring
  have himage :
      DiscreteSet.enncard (source.image endpointMap) =
        source.enncard := by
    simp [DiscreteSet.enncard,
      Finset.card_image_of_injective _ endpointMap.injective]
  simpa [source, scale, himage] using hsource

end Kakeya.Assouad
