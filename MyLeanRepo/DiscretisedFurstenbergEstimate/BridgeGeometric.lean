module

/-
  BridgeGeometric.lean

  Geometric support lemmas for the B1 induction bridge.

  Main results:
  1. cell_to_strip_cover: C(a,b) ∩ unitSquare ⊆ S(a,b+1).
  2. strip_to_cells_cover: S(a,b) ∩ unitSquare ⊆ C(a,b-1) ∪ C(a,b) ∪ C(a,b+1).
  3. coveringCells_card: each strip maps to exactly 3 cells.
  4. all_cells_expansion: |all cells| ≤ 3 * |strips|.
  5. incidence_preserved_by_expansion: strip-square incidence → cell-square incidence.
  6. pigeonhole3: given 3 candidates per element, one choice retains ≥ 1/3 total.

  Whiteprint node: B1_induction_on_scales / bridge_geometric
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

namespace DiscretisedFurstenbergEstimate.Bridge.Geometric

open _root_ (DyadicTube DyadicSquare unitSquare)

/-! ============================================================================
   Basic facts about dyadicDelta
   ============================================================================ -/

lemma dyadicDelta_pos' (n : ℕ) : 0 < _root_.dyadicDelta n := by
  have h_pos : 0 < (2 : ℝ) := by norm_num
  simpa [_root_.dyadicDelta] using Real.rpow_pos_of_pos h_pos _

/-! ============================================================================
   Geometric conditions on ℝ×ℝ
   ============================================================================ -/

/-- Centered strip condition on ℝ×ℝ: |y - aδ*x - bδ| ≤ δ. -/
def mainStrip (n : ℕ) (a b : ℤ) (p : ℝ × ℝ) : Prop :=
  |p.2 - (a : ℝ) * _root_.dyadicDelta n * p.1 - (b : ℝ) * _root_.dyadicDelta n| ≤ _root_.dyadicDelta n

/-- Exact cell condition on ℝ×ℝ. -/
def standCell (n : ℕ) (a b : ℤ) (p : ℝ × ℝ) : Prop :=
  ∃ slope ∈ Set.Ico ((a : ℝ) * _root_.dyadicDelta n) ((a + 1 : ℝ) * _root_.dyadicDelta n),
    ∃ intercept ∈ Set.Ico ((b : ℝ) * _root_.dyadicDelta n) ((b + 1 : ℝ) * _root_.dyadicDelta n),
      p.2 = slope * p.1 + intercept

abbrev unitSquare' : Set (ℝ × ℝ) := unitSquare

/-! ============================================================================
   Lemma 1: Cell → Strip covering
   ============================================================================ -/

lemma cell_to_strip_cover {n : ℕ} (a b : ℤ) (p : ℝ × ℝ)
    (hp_unit : p ∈ unitSquare') (h_cell : standCell n a b p) :
    mainStrip n a (b + 1) p := by
  rcases h_cell with ⟨slope, hs, intercept, hi, heq⟩
  set δ : ℝ := _root_.dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos' n
  have hx0 : 0 ≤ p.1 := hp_unit.1.1
  have hx1 : p.1 < 1 := hp_unit.1.2
  have hs1 : (a : ℝ) * δ ≤ slope := hs.1
  have hs2 : slope < ((a + 1 : ℝ) * δ) := hs.2
  have hi1 : (b : ℝ) * δ ≤ intercept := hi.1
  have hi2 : intercept < ((b + 1 : ℝ) * δ) := hi.2
  set ds : ℝ := slope - (a : ℝ) * δ with hds
  set di : ℝ := intercept - (b : ℝ) * δ with hdi
  have hds0 : 0 ≤ ds := by linarith
  have hds1 : ds < δ := by linarith
  have hdi0 : 0 ≤ di := by linarith
  have hdi1 : di < δ := by linarith
  have h_goal : p.2 - (a : ℝ) * δ * p.1 - ((b + 1 : ℝ) * δ) =
      ds * p.1 + di - δ := by
    simp [hds, hdi, heq] <;> ring
  have h_main : |p.2 - (a : ℝ) * δ * p.1 - ((b + 1 : ℝ) * δ)| ≤ δ := by
    rw [h_goal]
    have h5 : 0 ≤ ds * p.1 := by positivity
    have h6 : ds * p.1 < δ := by nlinarith
    have h9 : -δ ≤ ds * p.1 + di - δ := by linarith
    have h10 : ds * p.1 + di - δ < δ := by linarith
    rw [abs_le] <;> constructor <;> linarith
  simpa [mainStrip, hδ] using h_main

/-! ============================================================================
   Lemma 2: Strip → Cells covering
   ============================================================================ -/

lemma strip_to_cells_cover {n : ℕ} (a b : ℤ) (p : ℝ × ℝ)
    (hp_unit : p ∈ unitSquare') (h_strip : mainStrip n a b p) :
    standCell n a (b - 1) p ∨ standCell n a b p ∨ standCell n a (b + 1) p := by
  set δ : ℝ := _root_.dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos' n
  have h_abs : |p.2 - (a : ℝ) * δ * p.1 - (b : ℝ) * δ| ≤ δ := h_strip
  set slope : ℝ := (a : ℝ) * δ with hslope
  set intercept : ℝ := p.2 - slope * p.1 with hintercept
  have h_slope_in : slope ∈ Set.Ico ((a : ℝ) * δ) ((a + 1 : ℝ) * δ) := by
    constructor <;> linarith [hδ_pos]
  have h_i1 : ((b - 1 : ℤ) : ℝ) * δ ≤ intercept := by
    simp only [hintercept, hslope]
    have h : (b : ℝ) * δ - δ ≤ p.2 - (a : ℝ) * δ * p.1 := by
      linarith [abs_le.mp h_abs]
    have h2 : (b : ℝ) * δ - δ = ((b - 1 : ℤ) : ℝ) * δ := by
      simp [sub_mul] <;> ring
    linarith
  have h_i2 : intercept ≤ ((b + 1 : ℤ) : ℝ) * δ := by
    simp only [hintercept, hslope]
    have h : p.2 - (a : ℝ) * δ * p.1 ≤ (b : ℝ) * δ + δ := by
      linarith [abs_le.mp h_abs]
    have h2 : (b : ℝ) * δ + δ = ((b + 1 : ℤ) : ℝ) * δ := by
      simp [add_mul] <;> ring
    linarith
  have h_eq : p.2 = slope * p.1 + intercept := by
    simp [hintercept, hslope] <;> ring
  by_cases h1 : intercept < (b : ℝ) * δ
  · have h_ico : intercept ∈ Set.Ico (((b - 1 : ℤ) : ℝ) * δ) ((b : ℝ) * δ) :=
      ⟨h_i1, h1⟩
    have h_ico' : intercept ∈ Set.Ico (((b - 1 : ℤ) : ℝ) * _root_.dyadicDelta n) (((b - 1 : ℤ) + 1) * _root_.dyadicDelta n) := by
      have h_eq3 : ((b - 1 : ℤ) + 1 : ℝ) = (b : ℝ) := by simp
      rw [h_eq3]
      simpa [hδ] using h_ico
    have h_cell : standCell n a (b - 1) p :=
      ⟨slope, h_slope_in, intercept, h_ico', h_eq⟩
    exact Or.inl h_cell
  · have h1' : (b : ℝ) * δ ≤ intercept := by linarith
    by_cases h2 : intercept < ((b + 1 : ℝ) * δ)
    · have h_ico : intercept ∈ Set.Ico ((b : ℝ) * δ) (((b + 1 : ℝ) * δ)) :=
        ⟨h1', h2⟩
      have h_cell : standCell n a b p :=
        ⟨slope, h_slope_in, intercept, h_ico, h_eq⟩
      exact Or.inr (Or.inl h_cell)
    · have h2' : intercept ≥ ((b + 1 : ℝ) * δ) := by linarith
      have h_b1 : ((b + 1 : ℤ) : ℝ) * δ = (b + 1 : ℝ) * δ := by simp
      have h_eq2 : intercept = ((b + 1 : ℝ) * δ) := by
        have h_ge : intercept ≥ ((b + 1 : ℝ) * δ) := by linarith
        have h_le : intercept ≤ ((b + 1 : ℝ) * δ) := by
          rw [h_b1] at h_i2; exact h_i2
        linarith
      have h_ico : intercept ∈ Set.Ico (((b + 1 : ℤ) : ℝ) * δ) (((b + 2 : ℤ) : ℝ) * δ) := by
        rw [h_eq2]
        constructor
        · simp [hδ_pos] <;> ring_nf <;> linarith
        · simp [hδ_pos] <;> ring_nf <;> linarith
      have h_ico' : intercept ∈ Set.Ico (((b + 1 : ℤ) : ℝ) * _root_.dyadicDelta n) (((b + 1 : ℤ) + 1) * _root_.dyadicDelta n) := by
        have h_eq3 : ((b + 1 : ℤ) + 1 : ℝ) = ((b + 2 : ℤ) : ℝ) := by
          norm_cast <;> ring
        rw [h_eq3]
        simpa [hδ] using h_ico
      have h_cell : standCell n a (b + 1) p :=
        ⟨slope, h_slope_in, intercept, h_ico', h_eq⟩
      exact Or.inr (Or.inr h_cell)

/-! ============================================================================
   Lemma 3: Covering cells Finset and cardinality
   ============================================================================ -/

noncomputable def coveringCells (n : ℕ) (a b : ℤ) : Finset (_root_.DyadicTube n) :=
  {⟨a, b - 1⟩, ⟨a, b⟩, ⟨a, b + 1⟩}

lemma coveringCells_card (n : ℕ) (a b : ℤ) :
    (coveringCells n a b).card = 3 := by
  have h1 : (⟨a, b - 1⟩ : _root_.DyadicTube n) ≠ (⟨a, b⟩ : _root_.DyadicTube n) := by
    intro h; injection h with h4; omega
  have h2 : (⟨a, b - 1⟩ : _root_.DyadicTube n) ≠ (⟨a, b + 1⟩ : _root_.DyadicTube n) := by
    intro h; injection h with h4; omega
  have h3 : (⟨a, b⟩ : _root_.DyadicTube n) ≠ (⟨a, b + 1⟩ : _root_.DyadicTube n) := by
    intro h; injection h with h4; omega
  simp [coveringCells, h1, h2, h3] <;> rfl

/-! ============================================================================
   Lemma 4: All-cells expansion bound
   ============================================================================ -/

lemma all_cells_expansion
    {T : Type*} [DecidableEq T]
    (n : ℕ)
    (strips : Finset T)
    (strip_a : T → ℤ) (strip_b : T → ℤ) :
    (strips.biUnion (fun t => coveringCells n (strip_a t) (strip_b t))).card ≤
      3 * strips.card := by
  calc (strips.biUnion (fun t => coveringCells n (strip_a t) (strip_b t))).card
    ≤ ∑ t ∈ strips, (coveringCells n (strip_a t) (strip_b t)).card :=
      Finset.card_biUnion_le
  _ = ∑ t ∈ strips, 3 := by
      apply Finset.sum_congr rfl
      intro t _
      exact coveringCells_card n (strip_a t) (strip_b t)
  _ = 3 * strips.card := by
      simp [Finset.sum_const] <;> ring

/-! ============================================================================
   Lemma 5: Incidence preservation under expansion
   ============================================================================ -/

lemma incidence_preserved_by_expansion
    {n : ℕ} {a b : ℤ} {Q : Set (ℝ × ℝ)}
    (hQ_sub : Q ⊆ unitSquare')
    (h_strip_hit : ∃ p ∈ Q, mainStrip n a b p) :
    ∃ (c : _root_.DyadicTube n), c ∈ coveringCells n a b ∧
      ∃ p ∈ Q, standCell n c.a c.b p := by
  rcases h_strip_hit with ⟨p, hpQ, h_strip⟩
  have hp_unit : p ∈ unitSquare' := hQ_sub hpQ
  have h_cells := strip_to_cells_cover a b p hp_unit h_strip
  rcases h_cells with (h | h | h)
  · refine' ⟨⟨a, b - 1⟩, by simp [coveringCells], p, hpQ, h⟩
  · refine' ⟨⟨a, b⟩, by simp [coveringCells], p, hpQ, h⟩
  · refine' ⟨⟨a, b + 1⟩, by simp [coveringCells], p, hpQ, h⟩

/-! ============================================================================
   Lemma 6: Pigeonhole principle for 3 choices

   Given a finite type α, for each a three candidates c0,a, c1,a, c2,a,
   and a "good" predicate on candidates, there exists a choice function
   f : α → β picking one of the three candidates for each a, such that
   the total weight of "good" choices is at least 1/3 of the total weight
   of elements for which at least one candidate is good.

   This is proved by averaging over the 3 constant choice functions
   (always pick candidate i for every a).
   ============================================================================ -/

/-- Helper to pick candidate i for element a. -/
def pick3 {α β : Type*} (c0 c1 c2 : α → β) (i : Fin 3) (a : α) : β :=
  match i with
  | 0 => c0 a
  | 1 => c1 a
  | 2 => c2 a

lemma pigeonhole3
    {α β : Type*} [Fintype α]
    (c0 c1 c2 : α → β)
    (weight : α → ℕ)
    (good : α → β → Prop)
    [∀ a, DecidablePred (good a)]
    (h_at_least_one : ∀ a, good a (c0 a) ∨ good a (c1 a) ∨ good a (c2 a)) :
    ∃ (i : Fin 3),
      ∑ a : α, (if good a (pick3 c0 c1 c2 i a) then weight a else 0) ≥
        (∑ a : α, weight a) / 3 := by
  let s0 := ∑ a : α, (if good a (c0 a) then weight a else 0)
  let s1 := ∑ a : α, (if good a (c1 a) then weight a else 0)
  let s2 := ∑ a : α, (if good a (c2 a) then weight a else 0)
  let W := ∑ a : α, weight a
  have h : ∀ a, (if good a (c0 a) then weight a else 0) +
      (if good a (c1 a) then weight a else 0) +
      (if good a (c2 a) then weight a else 0) ≥ weight a := by
    intro a
    rcases h_at_least_one a with (h | h | h) <;> simp [h] <;> omega
  have h_sum_eq : s0 + s1 + s2 =
      ∑ a : α, ((if good a (c0 a) then weight a else 0) +
        (if good a (c1 a) then weight a else 0) +
        (if good a (c2 a) then weight a else 0)) := by
    simp only [s0, s1, s2, Finset.sum_add_distrib] <;> rfl
  have h_sum : s0 + s1 + s2 ≥ W := by
    rw [h_sum_eq]
    exact Finset.sum_le_sum (fun a _ => h a)
  by_cases h0 : s0 ≥ W / 3
  · refine' ⟨0, _⟩
    have h_eq : ∑ a : α, (if good a (pick3 c0 c1 c2 0 a) then weight a else 0) = s0 := by
      apply Finset.sum_congr rfl
      intro x _
      simp [pick3]
    rw [h_eq]
    exact h0
  · by_cases h1 : s1 ≥ W / 3
    · refine' ⟨1, _⟩
      have h_eq : ∑ a : α, (if good a (pick3 c0 c1 c2 1 a) then weight a else 0) = s1 := by
        apply Finset.sum_congr rfl
        intro x _
        simp [pick3]
      rw [h_eq]
      exact h1
    · have h2 : s2 ≥ W / 3 := by omega
      refine' ⟨2, _⟩
      have h_eq : ∑ a : α, (if good a (pick3 c0 c1 c2 2 a) then weight a else 0) = s2 := by
        apply Finset.sum_congr rfl
        intro x _
        simp [pick3]
      rw [h_eq]
      exact h2

/-! ============================================================================
   Connection lemmas to actual DyadicTube.toSet definitions

   The main repo uses EuclideanSpace ℝ (Fin 2) while the standalone uses ℝ×ℝ.
   We provide conversion functions and equivalence lemmas.
   ============================================================================ -/

/-- Convert ℝ×ℝ to EuclideanSpace ℝ (Fin 2). -/
def toEuclidean (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then p.1 else p.2)

/-- Convert EuclideanSpace ℝ (Fin 2) to ℝ×ℝ. -/
def fromEuclidean (p : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ := (p 0, p 1)

lemma toEuclidean_fst (p : ℝ × ℝ) : (toEuclidean p) 0 = p.1 := by simp [toEuclidean]
lemma toEuclidean_snd (p : ℝ × ℝ) : (toEuclidean p) 1 = p.2 := by simp [toEuclidean]

/-- mainStrip matches main DyadicTube.toSet after point conversion. -/
lemma mainStrip_iff_mainTube {n : ℕ} {T : DiscretisedFurstenbergEstimate.DyadicTube n}
    {p : EuclideanSpace ℝ (Fin 2)} :
    p ∈ T.toSet ↔ mainStrip n T.a T.b (fromEuclidean p) := by
  have h1 : p ∈ T.toSet ↔
      |p 1 - T.slope * p 0 - T.intercept| ≤ DiscretisedFurstenbergEstimate.dyadicDelta n := by
    exact Iff.rfl
  rw [h1]
  have h2 : T.slope = (T.a : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta n := by
    simp [DiscretisedFurstenbergEstimate.DyadicTube.slope]
    <;> rfl
  have h3 : T.intercept = (T.b : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta n := by
    simp [DiscretisedFurstenbergEstimate.DyadicTube.intercept]
    <;> rfl
  have h4 : DiscretisedFurstenbergEstimate.dyadicDelta n = _root_.dyadicDelta n := by
    simp [DiscretisedFurstenbergEstimate.dyadicDelta, _root_.dyadicDelta]
    <;> field_simp <;> ring
  rw [h2, h3, h4]
  <;> simp [mainStrip, fromEuclidean]
  <;> rfl

/-- standCell matches standalone DyadicTube.toSet. -/
lemma standCell_iff_standTube {n : ℕ} {T : _root_.DyadicTube n} {p : ℝ × ℝ} :
    p ∈ T.toSet ↔ standCell n T.a T.b p := by
  constructor
  · intro h
    rcases h with ⟨slope, hs, intercept, hi, heq⟩
    exact ⟨slope, hs, intercept, hi, heq⟩
  · intro h
    rcases h with ⟨slope, hs, intercept, hi, heq⟩
    exact ⟨slope, hs, intercept, hi, heq⟩

/-- Direct bridge lemma: given a main centered strip described by indices (a,b)
    and a set Q ⊆ unitSquare, if the strip intersects Q, then at least one of
    the 3 covering standalone cells also intersects Q.

    This is the key lemma for repairing the false forward incidence assumption
    in the bridge.
-/
lemma mainStrip_intersection_gives_cell
    {n : ℕ} {a b : ℤ} {Q : Set (ℝ × ℝ)}
    (hQ_sub : Q ⊆ unitSquare')
    (h_inc : ∃ p ∈ Q, mainStrip n a b p) :
    ∃ (C : _root_.DyadicTube n), C ∈ coveringCells n a b ∧
      (C.toSet ∩ Q).Nonempty := by
  rcases h_inc with ⟨p, hpQ, h_strip⟩
  have hp_unit : p ∈ unitSquare' := hQ_sub hpQ
  have h_cells := strip_to_cells_cover a b p hp_unit h_strip
  rcases h_cells with (h | h | h)
  · let C : _root_.DyadicTube n := ⟨a, b - 1⟩
    have hC_mem : C ∈ coveringCells n a b := by simp [coveringCells, C]
    have h5 : p ∈ C.toSet := by
      rw [standCell_iff_standTube] <;> exact h
    exact ⟨C, hC_mem, ⟨p, h5, hpQ⟩⟩
  · let C : _root_.DyadicTube n := ⟨a, b⟩
    have hC_mem : C ∈ coveringCells n a b := by simp [coveringCells, C]
    have h5 : p ∈ C.toSet := by
      rw [standCell_iff_standTube] <;> exact h
    exact ⟨C, hC_mem, ⟨p, h5, hpQ⟩⟩
  · let C : _root_.DyadicTube n := ⟨a, b + 1⟩
    have hC_mem : C ∈ coveringCells n a b := by simp [coveringCells, C]
    have h5 : p ∈ C.toSet := by
      rw [standCell_iff_standTube] <;> exact h
    exact ⟨C, hC_mem, ⟨p, h5, hpQ⟩⟩

end DiscretisedFurstenbergEstimate.Bridge.Geometric
