import MyLeanRepo.Kakeya.Streamlined.Basic
import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.ConflictColoring
import MyLeanRepo.Kakeya.Streamlined.CombinatorialLemmas.EssentiallyDistinctSubfamily
import Mathlib.Tactic

/-!
# Bicriteria extraction from a total conflict bound

A total count of non-essential-distinctness conflicts does not itself give a
uniform degree bound. Removing the high-degree vertices first converts it
into one while retaining both most indices and most shaded mass. A bounded
conflict coloring then extracts an essentially-distinct subfamily.
-/

noncomputable section

open MeasureTheory Finset Classical

namespace Kakeya.Streamlined

/-- Number of tubes conflicting with the tube indexed by `i`. -/
def tubeConflictDegree {δ : ℝ} (G : TubeFamily δ) (i : Fin G.card) : ℕ :=
  (Finset.univ.filter (fun j =>
    j ≠ i ∧ ¬(G.tube i).EssentiallyDistinct (G.tube j))).card

/-- Sum of all tube conflict degrees. -/
def tubeTotalConflictDegree {δ : ℝ} (G : TubeFamily δ) : ℕ :=
  ∑ i : Fin G.card, tubeConflictDegree G i

/--
Extract an essentially-distinct subfamily from a total conflict bound while
retaining quantitative fractions of both cardinality and shaded mass.
-/
lemma extract_bicriteria_ed_of_total_conflicts
    {δ : ℝ} {G : TubeFamily δ} (Y : TubeShading G)
    (V : ENNReal) (hV_pos : 0 < V) (hV_ne_top : V ≠ ⊤)
    (h_vol : ∀ i, (G.tube i).volume = V)
    (M : ℕ) (hM : tubeTotalConflictDegree G ≤ M)
    (W : ENNReal) (hW : Y.mass = W)
    (D : ℕ) (hD : (D : ENNReal) * W ≥ 4 * (M : ENNReal) * V) :
    ∃ S : TubeSubfamily G,
      S.family.IsEssentiallyDistinct ∧
      S.family.enncard ≥ G.enncard / (2 * ((D : ENNReal) + 1)) ∧
      (S.restrictShading Y).mass ≥ W / (4 * ((D : ENNReal) + 1)) := by
  classical
  let weight : Fin G.card → ENNReal := fun i => volume (Y.carrier i)
  have hW_def : Y.mass = ∑ i : Fin G.card, weight i := by
    rfl
  have h_weight_le_V : ∀ i, weight i ≤ V := by
    intro i
    have h1 : volume (Y.carrier i) ≤ (G.tube i).volume :=
      MeasureTheory.measure_mono (Y.subset_body i)
    rw [h_vol i] at h1
    exact h1
  have hW_ne_top : W ≠ ⊤ := by
    rw [← hW, hW_def, ENNReal.sum_ne_top]
    intro i _
    exact ne_top_of_le_ne_top hV_ne_top (h_weight_le_V i)

  let conflict : Fin G.card → Fin G.card → Prop :=
    fun i j => ¬(G.tube i).EssentiallyDistinct (G.tube j)
  have hsymm : ∀ ⦃i j⦄, conflict i j → conflict j i := by
    intro i j h
    exact essentiallyDistinct_symm.not.mp h

  let low : Finset (Fin G.card) :=
    Finset.univ.filter fun i => tubeConflictDegree G i ≤ D
  let high : Finset (Fin G.card) := Finset.univ \ low

  have hhigh_degree : ∀ i ∈ high, D < tubeConflictDegree G i := by
    intro i hi
    have hnot : ¬tubeConflictDegree G i ≤ D := by
      simpa [high, low] using (Finset.mem_sdiff.mp hi).2
    exact Nat.lt_of_not_ge hnot
  have hhigh_sum :
      ∑ i ∈ high, tubeConflictDegree G i ≤ M := by
    calc
      ∑ i ∈ high, tubeConflictDegree G i
          ≤ ∑ i : Fin G.card, tubeConflictDegree G i := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.subset_univ high)
            intro _ _ _
            exact Nat.zero_le _
      _ = tubeTotalConflictDegree G := rfl
      _ ≤ M := hM
  have hhigh_card_mul : high.card * (D + 1) ≤ M := by
    calc
      high.card * (D + 1) = ∑ _i ∈ high, (D + 1) := by
        simp [Finset.sum_const]
      _ ≤ ∑ i ∈ high, tubeConflictDegree G i := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.succ_le_iff.mpr (hhigh_degree i hi)
      _ ≤ M := hhigh_sum

  have hW_le_cardV : W ≤ (G.card : ENNReal) * V := by
    calc
      W = ∑ i : Fin G.card, weight i := by rw [← hW_def, hW]
      _ ≤ ∑ _i : Fin G.card, V := by
        apply Finset.sum_le_sum
        intro i _
        exact h_weight_le_V i
      _ = (G.card : ENNReal) * V := by simp
  have hDcard : (D : ENNReal) * (G.card : ENNReal) ≥ 4 * (M : ENNReal) := by
    have hmul :
        ((D : ENNReal) * (G.card : ENNReal)) * V ≥
          (4 * (M : ENNReal)) * V := by
      calc
        ((D : ENNReal) * (G.card : ENNReal)) * V
            = (D : ENNReal) * ((G.card : ENNReal) * V) := by ring
        _ ≥ (D : ENNReal) * W := by gcongr
        _ ≥ 4 * (M : ENNReal) * V := hD
    exact (ENNReal.mul_le_mul_iff_right hV_pos.ne' hV_ne_top).mp
      (by simpa [mul_comm] using hmul)
  have hDcard_nat : D * G.card ≥ 4 * M := by
    exact_mod_cast hDcard
  have hhigh_card_le : 4 * high.card ≤ G.card := by
    have h1 : 4 * high.card * (D + 1) ≤ 4 * M := by
      nlinarith [hhigh_card_mul]
    have h2 : 4 * high.card * (D + 1) ≤ D * G.card :=
      h1.trans hDcard_nat
    have h3 : 4 * high.card * (D + 1) ≤ (D + 1) * G.card := by
      exact h2.trans (by nlinarith)
    nlinarith

  have hdisj : Disjoint low high := by
    simp [low, high, Finset.disjoint_left] <;> tauto
  have hunion : low ∪ high = Finset.univ := by
    simp [low, high]
  have hcard_partition : low.card + high.card = G.card := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion] at h
    simpa using h.symm
  have hlow_card : 3 * G.card ≤ 4 * low.card := by
    omega

  let highMass : ENNReal := ∑ i ∈ high, weight i
  have hhigh_mass_le : highMass ≤ (high.card : ENNReal) * V := by
    calc
      highMass = ∑ i ∈ high, weight i := rfl
      _ ≤ ∑ _i ∈ high, V := by
        apply Finset.sum_le_sum
        intro i hi
        exact h_weight_le_V i
      _ = (high.card : ENNReal) * V := by
        simp [Finset.sum_const]
  have hfour_high_mass : 4 * highMass ≤ W := by
    have h1 :
        4 * highMass * ((D : ENNReal) + 1) ≤
          4 * (M : ENNReal) * V := by
      calc
        4 * highMass * ((D : ENNReal) + 1)
            ≤ 4 * ((high.card : ENNReal) * V) *
                ((D : ENNReal) + 1) := by gcongr
        _ = 4 * ((high.card : ENNReal) *
                ((D : ENNReal) + 1)) * V := by ring
        _ ≤ 4 * (M : ENNReal) * V := by
          gcongr
          exact_mod_cast hhigh_card_mul
    have h2 :
        4 * (M : ENNReal) * V ≤ ((D : ENNReal) + 1) * W := by
      calc
        4 * (M : ENNReal) * V ≤ (D : ENNReal) * W := hD
        _ ≤ ((D : ENNReal) + 1) * W := by
          have h4 : (D : ENNReal) ≤ (D : ENNReal) + 1 := by simp
          exact mul_le_mul_of_nonneg_right h4 (by positivity)
    have h3 :
        (4 * highMass) * ((D : ENNReal) + 1) ≤
          W * ((D : ENNReal) + 1) := by
      calc
        (4 * highMass) * ((D : ENNReal) + 1)
            ≤ 4 * (M : ENNReal) * V := h1
        _ ≤ ((D : ENNReal) + 1) * W := h2
        _ = W * ((D : ENNReal) + 1) := mul_comm _ _
    have hD1_pos : 0 < ((D : ENNReal) + 1) := by positivity
    have hD1_ne_top : ((D : ENNReal) + 1) ≠ ⊤ := by simp
    exact (ENNReal.mul_le_mul_iff_left hD1_pos.ne' hD1_ne_top).mp h3

  let lowMass : ENNReal := ∑ i ∈ low, weight i
  have hmass_partition : lowMass + highMass = W := by
    have h :
        (∑ i ∈ low ∪ high, weight i) = lowMass + highMass :=
      Finset.sum_union hdisj
    rw [hunion] at h
    have h' :
        (∑ i ∈ (Finset.univ : Finset (Fin G.card)), weight i) = W := by
      rw [← hW_def, hW]
    rw [h] at h'
    exact h'
  have hlow_mass : 3 * W ≤ 4 * lowMass := by
    have hsum : 4 * lowMass + 4 * highMass = 4 * W := by
      rw [← mul_add, hmass_partition]
    have hmain : 4 * W ≤ 4 * lowMass + W := by
      calc
        4 * W = 4 * lowMass + 4 * highMass := hsum.symm
        _ ≤ 4 * lowMass + W := by gcongr
    have hrewrite : 3 * W + W = 4 * W := by ring
    rw [← hrewrite] at hmain
    exact (ENNReal.add_le_add_iff_right hW_ne_top).mp hmain

  have hdegree : ∀ i ∈ low,
      (low.filter fun j => j ≠ i ∧ conflict i j).card ≤ D := by
    intro i hi
    have h1 : tubeConflictDegree G i ≤ D :=
      (Finset.mem_filter.mp hi).2
    have h2 :
        (low.filter fun j => j ≠ i ∧ conflict i j) ⊆
          (Finset.univ.filter fun j => j ≠ i ∧ conflict i j) := by
      intro j hj
      simp only [Finset.mem_filter] at hj ⊢
      exact ⟨Finset.mem_univ j, hj.2⟩
    calc
      (low.filter fun j => j ≠ i ∧ conflict i j).card
          ≤ (Finset.univ.filter fun j => j ≠ i ∧ conflict i j).card :=
        Finset.card_le_card h2
      _ = tubeConflictDegree G i := rfl
      _ ≤ D := h1

  rcases exists_bicriteria_bounded_conflict_free_class
      low D weight conflict hsymm hdegree with
    ⟨selected, hselected_sub, hselected_free, hselected_card,
      hselected_mass⟩
  let S : TubeSubfamily G := TubeSubfamily.fromFinset G selected
  have hS_distinct : S.family.IsEssentiallyDistinct := by
    intro i j hij
    have hi : S.embedding i ∈ selected :=
      Finset.orderEmbOfFin_mem selected rfl i
    have hj : S.embedding j ∈ selected :=
      Finset.orderEmbOfFin_mem selected rfl j
    have hne : S.embedding i ≠ S.embedding j :=
      fun h => hij (S.embedding.injective h)
    rw [S.tube_eq i, S.tube_eq j]
    exact Classical.byContradiction fun hconflict =>
      hselected_free (S.embedding i) hi (S.embedding j) hj hne hconflict

  have hselected_card_main :
      G.card ≤ 2 * (D + 1) * selected.card := by
    have h1 : 3 * G.card ≤ 4 * (D + 1) * selected.card := by
      calc
        3 * G.card ≤ 4 * low.card := hlow_card
        _ ≤ 4 * ((D + 1) * selected.card) := by gcongr
        _ = 4 * (D + 1) * selected.card := by ring
    nlinarith
  have hS_card :
      S.family.enncard ≥ G.enncard / (2 * ((D : ENNReal) + 1)) := by
    have hS_card_eq : S.family.enncard = (selected.card : ENNReal) := by
      simp [S, TubeSubfamily.fromFinset, TubeFamily.enncard] <;> rfl
    rw [hS_card_eq]
    have hcast :
        (2 * ((D : ENNReal) + 1)) * (selected.card : ENNReal) ≥
          (G.card : ENNReal) := by
      exact_mod_cast hselected_card_main
    let denom := 2 * ((D : ENNReal) + 1)
    have hdenom_pos : denom ≠ 0 := by positivity
    have hdenom_top : denom ≠ ⊤ := by
      simp only [denom]
      have h : (2 : ENNReal) * ((D : ENNReal) + 1) =
          ↑(2 * (D + 1)) := by
        push_cast <;> ring
      rw [h]
      exact ENNReal.coe_ne_top
    have hmain : G.enncard / denom ≤ (selected.card : ENNReal) := by
      rw [ENNReal.div_le_iff hdenom_pos hdenom_top]
      have hG : G.enncard = (G.card : ENNReal) := by
        simp [TubeFamily.enncard]
      rw [hG]
      simpa [denom, mul_comm] using hcast
    exact hmain

  have hselected_mass_main :
      W ≤ 4 * ((D : ENNReal) + 1) * ∑ i ∈ selected, weight i := by
    have hselected_mass' :
        lowMass ≤ ((D : ENNReal) + 1) * ∑ i ∈ selected, weight i := by
      simpa [lowMass] using hselected_mass
    have hW_le_three : W ≤ 3 * W := by
      have h : (1 : ENNReal) * W ≤ 3 * W := by
        gcongr
        norm_num
      simpa using h
    calc
      W ≤ 3 * W := hW_le_three
      _ ≤ 4 * lowMass := hlow_mass
      _ ≤ 4 * (((D : ENNReal) + 1) *
          ∑ i ∈ selected, weight i) :=
        mul_le_mul_left' hselected_mass' 4
      _ = 4 * ((D : ENNReal) + 1) *
          ∑ i ∈ selected, weight i := by ring
  have hS_mass_eq :
      (S.restrictShading Y).mass = ∑ i ∈ selected, weight i := by
    dsimp only [TubeSubfamily.restrictShading, Shading.mass, weight]
    calc
      ∑ i : Fin S.family.card, volume (Y.carrier (S.embedding i))
          = ∑ i ∈ Finset.map S.embedding Finset.univ,
              volume (Y.carrier i) := by rw [Finset.sum_map]
      _ = ∑ i ∈ selected, volume (Y.carrier i) := by
        have himage :
            Finset.map S.embedding Finset.univ = selected :=
          Finset.map_orderEmbOfFin_univ selected rfl
        rw [himage]
  have hS_mass :
      (S.restrictShading Y).mass ≥ W / (4 * ((D : ENNReal) + 1)) := by
    rw [hS_mass_eq]
    let denom := 4 * ((D : ENNReal) + 1)
    have hdenom_pos : denom ≠ 0 := by positivity
    have hdenom_top : denom ≠ ⊤ := by
      simp only [denom]
      have h : (4 : ENNReal) * ((D : ENNReal) + 1) =
          ↑(4 * (D + 1)) := by
        push_cast <;> ring
      rw [h]
      exact ENNReal.coe_ne_top
    have hmain : W / denom ≤ ∑ i ∈ selected, weight i := by
      rw [ENNReal.div_le_iff hdenom_pos hdenom_top]
      simpa [denom, mul_assoc, mul_comm, mul_left_comm] using
        hselected_mass_main
    exact hmain
  exact ⟨S, hS_distinct, hS_card, hS_mass⟩

end Kakeya.Streamlined
