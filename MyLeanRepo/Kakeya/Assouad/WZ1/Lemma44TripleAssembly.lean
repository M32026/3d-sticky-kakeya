import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44CloseAndLineBounds
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44BadPairStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44ENNRealHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44Cardinality
import Mathlib.Algebra.Order.Chebyshev

/-!
# Triple count assembly for WZ1 Lemma 44

Combines the three geometric case bounds with Cauchy–Schwarz to bound
the number of bad pairs at one scale.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- `|{(x,y) ∈ s×t | P x y}| = Σ_{x∈s} |{y∈t | P x y}|`. -/
private lemma card_filter_product {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (P : α → β → Prop) :
    ((s ×ˢ t).filter (fun p : α × β => P p.1 p.2)).card =
    ∑ x ∈ s, (t.filter (fun y => P x y)).card := by
  let f : α → Finset (α × β) := fun x =>
    (t.filter (fun y => P x y)).map
      ⟨fun y : β => (x, y), fun {a b : β} (h : (x, a) = (x, b)) =>
        (Prod.ext_iff.mp h).2⟩
  have h_disj : ∀ x ∈ s, ∀ x' ∈ s, x ≠ x' → Disjoint (f x) (f x') := by
    intro x _ x' _ hne
    simp only [f, Finset.disjoint_left, Finset.mem_map]
    intro p hp1 hp2
    rcases hp1 with ⟨y, _, rfl⟩
    rcases hp2 with ⟨y', _, hxy⟩
    have h_eq : x = x' := (congr_arg Prod.fst hxy).symm
    exact hne h_eq
  have h_eq : (s ×ˢ t).filter (fun p : α × β => P p.1 p.2) = s.biUnion f := by
    ext ⟨x, y⟩
    simp [f, Finset.mem_biUnion, Finset.mem_map, Finset.mem_product]
    <;> tauto
  rw [h_eq, Finset.card_biUnion h_disj]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.card_map]
  <;> rfl

/-- `|{(x,y) ∈ s×t | P x y}| = Σ_{y∈t} |{x∈s | P x y}|`. -/
private lemma card_filter_product_comm {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (P : α → β → Prop) :
    ((s ×ˢ t).filter (fun p : α × β => P p.1 p.2)).card =
    ∑ y ∈ t, (s.filter (fun x => P x y)).card := by
  let Q : β → α → Prop := fun y x => P x y
  let swap : α × β → β × α := fun p => (p.2, p.1)
  let A : Finset (α × β) := (s ×ˢ t).filter (fun p => P p.1 p.2)
  let B : Finset (β × α) := (t ×ˢ s).filter (fun p => Q p.1 p.2)
  have h_image : A.image swap = B := by
    ext ⟨y, x⟩
    simp [A, B, swap, Q, Finset.mem_image, Finset.mem_product]
    <;> tauto
  have h_inj : Set.InjOn swap (A : Set (α × β)) := by
    intro p _ q _ h
    exact Prod.ext (congr_arg Prod.snd h) (congr_arg Prod.fst h)
  have h1 : A.card = B.card := by
    rw [← h_image, Finset.card_image_of_injOn h_inj]
  rw [h1]
  exact card_filter_product t s Q

/-- Filtering a product by independent predicates factors. -/
private lemma filter_product_and {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (P : α → Prop) (Q : β → Prop) :
    ((s ×ˢ t).filter (fun p : α × β => P p.1 ∧ Q p.2)) =
    (s.filter P) ×ˢ (t.filter Q) := by
  ext ⟨x, y⟩
  simp [Finset.mem_product]
  <;> tauto

lemma triple_count_assembly
    (delta lambda zeta alpha : ℝ)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hlambda : 0 < lambda) (hzeta : 0 < zeta) (halpha : 0 < alpha)
    (G₁ G₂ : DiscreteSet 2)
    (hG1_nonempty : G₁.Nonempty) (hG2_nonempty : G₂.Nonempty)
    (hG1_ball : G₁.IsInUnitBall) (hG2_ball : G₂.IsInUnitBall)
    (hFrost1 : G₁.IsFrostman delta 1 (Kakeya.realRpowENN delta (-lambda)))
    (hFrost2 : G₂.IsFrostman delta 1 (Kakeya.realRpowENN delta (-lambda)))
    (h_nonconc : WZ1LineNonConcentration delta lambda zeta G₂)
    (K scale : ℝ)
    (hK : 1 ≤ K) (hscale_pos : 0 < scale)
    (hdelta_scale : delta ≤ scale)
    (hscale1 : scale ≤ 1)
    (h13scale : 13 * scale ≤ 1)
    (hD_delta : delta ≤ Real.rpow delta (lambda + 4 * alpha))
    (hs_delta : delta ≤ Real.rpow delta (lambda + 4 * alpha / zeta))
    (hprem2 : 8 * (13 * scale) ≤
        Real.rpow delta (lambda + 4 * alpha) *
        Real.rpow delta (lambda + 4 * alpha / zeta))
    (hprem3 : (312000 : ℝ) / K ^ 4 *
        Real.rpow delta (-(3 * lambda + 4 * alpha + 4 * alpha / zeta)) ≤
        Real.rpow delta (4 * alpha))
    (badLines : Point2 → Finset (AffineSubspace ℝ Point2))
    (M : ℕ)
    (hM_card : ∀ b1 ∈ G₁, (badLines b1).card ≤ M)
    (hM_lines_through : ∀ b1 ∈ G₁, ∀ ℓ ∈ badLines b1, b1 ∈ (ℓ : Set Point2))
    (hM_fin : ∀ b1 ∈ G₁, ∀ ℓ ∈ badLines b1, Module.finrank ℝ ℓ.direction = 1)
    (h_coverage : ∀ b1 ∈ G₁, ∀ b2 ∈ G₂,
        WZ1BadAtScale G₁ G₂ scale K b1 b2 →
        ∃ ℓ ∈ badLines b1,
          b2 ∈ Metric.thickening (13 * scale) (ℓ : Set Point2))
    (hM_bound : (M : ℝ) ≤ 20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ))) :
    (((G₁ ×ˢ G₂).filter fun pair =>
        WZ1BadAtScale G₁ G₂ scale K pair.1 pair.2).card : ℝ) ≤
      Real.sqrt 312002 * Real.rpow delta (2 * alpha) *
        (G₁.card : ℝ) * (G₂.card : ℝ) := by
  -- Parameter definitions
  set D : ℝ := Real.rpow delta (lambda + 4 * alpha) with hD_def
  set s : ℝ := Real.rpow delta (lambda + 4 * alpha / zeta) with hs_def
  set r' : ℝ := 13 * scale with hr'_def
  set C_F : ENNReal := Kakeya.realRpowENN delta (-lambda) with hC_F_def
  set badPred : Point2 → Point2 → Prop := fun b1 b2 =>
    WZ1BadAtScale G₁ G₂ scale K b1 b2 with hbadPred_def

  -- Parameter bounds
  have hD_pos : 0 < D := Real.rpow_pos_of_pos hdelta _
  have hD1 : D ≤ 1 := by
    rw [hD_def]
    exact Real.rpow_le_one (by linarith) (by linarith) (by linarith)
  have hs_pos : 0 < s := Real.rpow_pos_of_pos hdelta _
  have hs1 : s ≤ 1 := by
    rw [hs_def]
    exact Real.rpow_le_one (by linarith) (by linarith) (by positivity)
  have hr'_pos : 0 < r' := by positivity
  have hr'1 : r' ≤ 1 := h13scale
  have hdelta_r' : delta ≤ r' := by
    calc delta ≤ scale := hdelta_scale
      _ ≤ 13 * scale := by linarith
      _ = r' := by simp [hr'_def]
  have hDsr : 8 * r' ≤ D * s := by
    simpa [hr'_def, hD_def, hs_def] using hprem2
  have hC_F_ge1 : 1 ≤ C_F := by
    rw [hC_F_def, Kakeya.realRpowENN]
    have h4 : 1 ≤ Real.rpow delta (-lambda) := by
      have h5 : Real.rpow delta (-lambda) = (Real.rpow delta lambda)⁻¹ := by
        simpa using Real.rpow_neg (by linarith) lambda
      rw [h5]
      have h6 : Real.rpow delta lambda ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) (by linarith)
      have h7 : 0 < Real.rpow delta lambda := Real.rpow_pos_of_pos hdelta _
      have h8 : (Real.rpow delta lambda)⁻¹ ≥ 1 := by
        calc (Real.rpow delta lambda)⁻¹
          ≥ (1 : ℝ)⁻¹ := by gcongr
        _ = 1 := by norm_num
      exact h8
    have h9 : (1 : ENNReal) ≤ ENNReal.ofReal (Real.rpow delta (-lambda)) := by
      simpa [ENNReal.ofReal_le_ofReal_iff] using h4
    exact h9

  -- Step 1: Define bad pairs and counts
  let B : Finset (Point2 × Point2) :=
    (G₁ ×ˢ G₂).filter (fun p => badPred p.1 p.2)
  let d : Point2 → ℕ := fun b2 =>
    (G₁.filter (fun b1 => badPred b1 b2)).card
  let N_bad : ℝ := (B.card : ℝ)

  have hN_bad_sum : (B.card : ℝ) = ∑ b2 ∈ G₂, (d b2 : ℝ) := by
    have h1 : B.card = ∑ b2 ∈ G₂, (G₁.filter (fun b1 => badPred b1 b2)).card :=
      card_filter_product_comm G₁ G₂ badPred
    exact_mod_cast h1

  -- Step 2: Triple sets
  let AllTriples : Finset ((Point2 × Point2) × Point2) := (G₁ ×ˢ G₁) ×ˢ G₂
  let BadTriples := AllTriples.filter (fun t => badPred t.1.1 t.2 ∧ badPred t.1.2 t.2)
  let Case1Triples := AllTriples.filter (fun t => dist t.1.1 t.1.2 ≤ D)
  let Case2Triples := AllTriples.filter (fun t =>
      t.1.1 ≠ t.1.2 ∧ t.2 ∈ Metric.thickening s ((lineThrough t.1.1 t.1.2) : Set Point2))
  let Case3Triples := AllTriples.filter (fun t =>
      D < dist t.1.1 t.1.2 ∧
      t.2 ∉ Metric.thickening s ((lineThrough t.1.1 t.1.2) : Set Point2) ∧
      (∃ ℓ1 ∈ badLines t.1.1, t.2 ∈ Metric.thickening r' (ℓ1 : Set Point2)) ∧
      (∃ ℓ2 ∈ badLines t.1.2, t.2 ∈ Metric.thickening r' (ℓ2 : Set Point2)))

  have h_cover : BadTriples ⊆ Case1Triples ∪ Case2Triples ∪ Case3Triples := by
    intro t ht
    have hpin : t ∈ AllTriples := (Finset.mem_filter.mp ht).1
    have hbad1 : badPred t.1.1 t.2 := (Finset.mem_filter.mp ht).2.1
    have hbad2 : badPred t.1.2 t.2 := (Finset.mem_filter.mp ht).2.2
    have hb1 : t.1.1 ∈ G₁ := (Finset.mem_product.mp (Finset.mem_product.mp hpin).1).1
    have hb2 : t.2 ∈ G₂ := (Finset.mem_product.mp hpin).2
    have hcov1 : ∃ ℓ1 ∈ badLines t.1.1, t.2 ∈ Metric.thickening r' (ℓ1 : Set Point2) :=
      h_coverage t.1.1 hb1 t.2 hb2 hbad1
    have hcov2 : ∃ ℓ2 ∈ badLines t.1.2, t.2 ∈ Metric.thickening r' (ℓ2 : Set Point2) :=
      h_coverage t.1.2 (Finset.mem_product.mp (Finset.mem_product.mp hpin).1).2 t.2 hb2 hbad2
    by_cases hclose : dist t.1.1 t.1.2 ≤ D
    · have h : t ∈ Case1Triples := by
        simp only [Case1Triples, Finset.mem_filter]
        exact ⟨hpin, hclose⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
    · have hfar : D < dist t.1.1 t.1.2 := by linarith
      have hne : t.1.1 ≠ t.1.2 := by
        intro h
        rw [h] at hfar
        simp at hfar <;> linarith
      by_cases hnear : t.2 ∈ Metric.thickening s ((lineThrough t.1.1 t.1.2) : Set Point2)
      · have h : t ∈ Case2Triples := by
          simp only [Case2Triples, Finset.mem_filter]
          exact ⟨hpin, ⟨hne, hnear⟩⟩
        exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
      · have h : t ∈ Case3Triples := by
          simp only [Case3Triples, Finset.mem_filter]
          exact ⟨hpin, ⟨hfar, hnear, hcov1, hcov2⟩⟩
        exact Finset.mem_union_right _ h

  -- BadTriples.card = sum of d(b2)^2
  have h_bad_card : (BadTriples.card : ENNReal) = ∑ b2 ∈ G₂, (d b2 : ENNReal)^2 := by
    have h_BadTriples_eq : BadTriples = ((G₁ ×ˢ G₁) ×ˢ G₂).filter
        (fun t : (Point2 × Point2) × Point2 => badPred t.1.1 t.2 ∧ badPred t.1.2 t.2) := by
      ext ⟨p, b2⟩
      simp [BadTriples, AllTriples]
      <;> rfl
    have h1 : BadTriples.card = ∑ b2 ∈ G₂,
        ((G₁ ×ˢ G₁).filter (fun p => badPred p.1 b2 ∧ badPred p.2 b2)).card := by
      rw [h_BadTriples_eq]
      let h := card_filter_product_comm (G₁ ×ˢ G₁) G₂ (fun p b2 => badPred p.1 b2 ∧ badPred p.2 b2)
      convert h <;> simp [badPred] <;> rfl
    have h2 : (BadTriples.card : ENNReal) = ∑ b2 ∈ G₂,
        (((G₁ ×ˢ G₁).filter (fun p => badPred p.1 b2 ∧ badPred p.2 b2)).card : ENNReal) := by
      rw [h1, Nat.cast_sum] <;> rfl
    rw [h2]
    apply Finset.sum_congr rfl
    intro b2 _
    have h3 : (G₁ ×ˢ G₁).filter (fun p : Point2 × Point2 => badPred p.1 b2 ∧ badPred p.2 b2) =
        (G₁.filter (fun b1 => badPred b1 b2)) ×ˢ (G₁.filter (fun b1 => badPred b1 b2)) :=
      filter_product_and G₁ G₁ (fun b1 => badPred b1 b2) (fun b1 => badPred b1 b2)
    rw [h3, Finset.card_product]
    <;> simp [d] <;> ring

  let T_enn : ENNReal := ∑ b2 ∈ G₂, (d b2 : ENNReal)^2
  have h_T_enn : T_enn = (BadTriples.card : ENNReal) := h_bad_card.symm

  -- Case 1 cardinality
  have h_card1 : (Case1Triples.card : ENNReal) =
      ∑ b1 ∈ G₁, ((G₁.filter (fun b1' => dist b1 b1' ≤ D)).card : ENNReal) * G₂.enncard := by
    have h : Case1Triples = ((G₁ ×ˢ G₁).filter (fun p => dist p.1 p.2 ≤ D)) ×ˢ G₂ := by
      ext ⟨p, b2⟩
      simp [Case1Triples, AllTriples, Finset.mem_product]
      <;> tauto
    rw [h]
    rw [Finset.card_product]
    have h2 : ((G₁ ×ˢ G₁).filter (fun p : Point2 × Point2 => dist p.1 p.2 ≤ D)).card =
        ∑ b1 ∈ G₁, (G₁.filter (fun b1' => dist b1 b1' ≤ D)).card :=
      card_filter_product G₁ G₁ (fun b1 b1' => dist b1 b1' ≤ D)
    rw [h2]
    have h4 : ↑((∑ b1 ∈ G₁, (G₁.filter (fun b1' => dist b1 b1' ≤ D)).card) * G₂.card) =
        ∑ b1 ∈ G₁, ((G₁.filter (fun b1' => dist b1 b1' ≤ D)).card : ENNReal) * (G₂.card : ENNReal) := by
      rw [Nat.cast_mul, Nat.cast_sum, Finset.sum_mul]
      <;> rfl
    rw [h4]
    <;> rfl

  -- Case 2 cardinality
  have h_card2 : (Case2Triples.card : ENNReal) =
      ∑ b1 ∈ G₁, ∑ b1' ∈ G₁.erase b1,
        ((G₂.filter (fun b2 => b2 ∈ Metric.thickening s
          ((lineThrough b1 b1') : Set Point2))).card : ENNReal) := by
    let P : (Point2 × Point2) → Point2 → Prop := fun p b2 =>
      p.1 ≠ p.2 ∧ b2 ∈ Metric.thickening s ((lineThrough p.1 p.2) : Set Point2)
    let f : Point2 → Point2 → ENNReal := fun b1 b1' =>
      (G₂.filter (fun b2 => b1 ≠ b1' ∧ b2 ∈ Metric.thickening s ((lineThrough b1 b1') : Set Point2))).card
    let g : Point2 → Point2 → ENNReal := fun b1 b1' =>
      (G₂.filter (fun b2 => b2 ∈ Metric.thickening s ((lineThrough b1 b1') : Set Point2))).card
    have h_Case2_eq : Case2Triples = ((G₁ ×ˢ G₁) ×ˢ G₂).filter (fun t : (Point2 × Point2) × Point2 => P t.1 t.2) := by
      ext ⟨p, b2⟩
      simp [Case2Triples, AllTriples, P] <;> rfl
    have h_eq1 : (Case2Triples.card : ENNReal) = ∑ b1 ∈ G₁, ∑ b1' ∈ G₁, f b1 b1' := by
      let f2 : Point2 × Point2 → Finset ((Point2 × Point2) × Point2) := fun p =>
        (G₂.filter (fun b2 => P p b2)).map
          ⟨fun b2 : Point2 => (p, b2), fun {a b : Point2} (h : (p, a) = (p, b)) =>
            (Prod.ext_iff.mp h).2⟩
      have h_disj : ∀ p ∈ G₁ ×ˢ G₁, ∀ p' ∈ G₁ ×ˢ G₁, p ≠ p' → Disjoint (f2 p) (f2 p') := by
        intro p _ p' _ hne
        simp only [f2, Finset.disjoint_left, Finset.mem_map]
        intro x hp1 hp2
        rcases hp1 with ⟨b2, _, rfl⟩
        rcases hp2 with ⟨b2', _, hxy⟩
        have h_eq : p = p' := (congr_arg Prod.fst hxy).symm
        exact hne h_eq
      have h_union : ((G₁ ×ˢ G₁) ×ˢ G₂).filter (fun t : (Point2 × Point2) × Point2 => P t.1 t.2) =
          (G₁ ×ˢ G₁).biUnion f2 := by
        ext ⟨p, b2⟩
        simp only [f2, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_map, Finset.mem_product]
        <;> aesop
      have h_union2 : Case2Triples = (G₁ ×ˢ G₁).biUnion f2 := by
        rw [h_Case2_eq, h_union]
      have h_card : Case2Triples.card = ∑ p ∈ G₁ ×ˢ G₁, (G₂.filter (fun b2 => P p b2)).card := by
        rw [h_union2, Finset.card_biUnion h_disj]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.card_map] <;> rfl
      rw [h_card, Nat.cast_sum, Finset.sum_product] <;> rfl
    rw [h_eq1]
    apply Finset.sum_congr rfl
    intro b1 hb1
    have h_f_b1 : f b1 b1 = 0 := by
      simp [f, Finset.filter_false] <;> rfl
    have h_sum : ∑ b1' ∈ G₁, f b1 b1' = ∑ b1' ∈ G₁.erase b1, f b1 b1' := by
      have h1 : G₁ = insert b1 (G₁.erase b1) := by
        rw [Finset.insert_erase hb1]
      rw [h1]
      have h_not : b1 ∉ G₁.erase b1 := by simp [Finset.mem_erase]
      rw [Finset.sum_insert h_not]
      rw [h_f_b1] <;> simp
    rw [h_sum]
    apply Finset.sum_congr rfl
    intro b1' hb1'
    have hne : b1 ≠ b1' := (Finset.mem_erase.mp hb1').1.symm
    have hfg : f b1 b1' = g b1 b1' := by
      have h_filter : G₂.filter (fun b2 => b1 ≠ b1' ∧ b2 ∈ Metric.thickening s ((lineThrough b1 b1') : Set Point2)) =
          G₂.filter (fun b2 => b2 ∈ Metric.thickening s ((lineThrough b1 b1') : Set Point2)) := by
        apply Finset.filter_congr
        intro b2 _
        simp [hne]
        <;> tauto
      have h_f_def : f b1 b1' = (G₂.filter (fun b2 => b1 ≠ b1' ∧ b2 ∈ Metric.thickening s ((lineThrough b1 b1') : Set Point2))).card := by
        rfl
      have h_g_def : g b1 b1' = (G₂.filter (fun b2 => b2 ∈ Metric.thickening s ((lineThrough b1 b1') : Set Point2))).card := by
        rfl
      rw [h_f_def, h_g_def, h_filter]
    exact hfg

  -- Case 3 cardinality
  have h_card3 : (Case3Triples.card : ENNReal) =
      ∑ b1 ∈ G₁, ∑ b1' ∈ G₁,
        ((G₂.filter (fun b2 =>
          D < dist b1 b1' ∧
          b2 ∉ Metric.thickening s ((lineThrough b1 b1') : Set Point2) ∧
          (∃ ℓ1 ∈ badLines b1, b2 ∈ Metric.thickening r' (ℓ1 : Set Point2)) ∧
          (∃ ℓ2 ∈ badLines b1', b2 ∈ Metric.thickening r' (ℓ2 : Set Point2)))).card : ENNReal) := by
    let P : (Point2 × Point2) → Point2 → Prop := fun p b2 =>
      D < dist p.1 p.2 ∧
      b2 ∉ Metric.thickening s ((lineThrough p.1 p.2) : Set Point2) ∧
      (∃ ℓ1 ∈ badLines p.1, b2 ∈ Metric.thickening r' (ℓ1 : Set Point2)) ∧
      (∃ ℓ2 ∈ badLines p.2, b2 ∈ Metric.thickening r' (ℓ2 : Set Point2))
    have h_Case3_eq : Case3Triples = ((G₁ ×ˢ G₁) ×ˢ G₂).filter (fun t : (Point2 × Point2) × Point2 => P t.1 t.2) := by
      ext ⟨p, b2⟩
      simp [Case3Triples, AllTriples, P] <;> rfl
    let f3 : Point2 × Point2 → Finset ((Point2 × Point2) × Point2) := fun p =>
      (G₂.filter (fun b2 => P p b2)).map
        ⟨fun b2 : Point2 => (p, b2), fun {a b : Point2} (h : (p, a) = (p, b)) =>
          (Prod.ext_iff.mp h).2⟩
    have h_disj3 : ∀ p ∈ G₁ ×ˢ G₁, ∀ p' ∈ G₁ ×ˢ G₁, p ≠ p' → Disjoint (f3 p) (f3 p') := by
      intro p _ p' _ hne
      simp only [f3, Finset.disjoint_left, Finset.mem_map]
      intro x hp1 hp2
      rcases hp1 with ⟨b2, _, rfl⟩
      rcases hp2 with ⟨b2', _, hxy⟩
      have h_eq : p = p' := (congr_arg Prod.fst hxy).symm
      exact hne h_eq
    have h_union3 : ((G₁ ×ˢ G₁) ×ˢ G₂).filter (fun t : (Point2 × Point2) × Point2 => P t.1 t.2) =
        (G₁ ×ˢ G₁).biUnion f3 := by
      ext ⟨p, b2⟩
      constructor
      · intro h
        have h1 : (p, b2) ∈ (G₁ ×ˢ G₁) ×ˢ G₂ := (Finset.mem_filter.mp h).1
        have h2 : P p b2 := (Finset.mem_filter.mp h).2
        have hp : p ∈ G₁ ×ˢ G₁ := (Finset.mem_product.mp h1).1
        have hb2 : b2 ∈ G₂ := (Finset.mem_product.mp h1).2
        apply Finset.mem_biUnion.mpr
        refine ⟨p, hp, ?_⟩
        apply Finset.mem_map.mpr
        refine ⟨b2, Finset.mem_filter.mpr ⟨hb2, h2⟩, rfl⟩
      · intro h
        rcases Finset.mem_biUnion.mp h with ⟨p', hp', hq2⟩
        have h_main : ∃ (b2' : Point2), b2' ∈ G₂.filter (fun b2 => P p' b2) ∧ (p', b2') = (p, b2) := by
          simpa [f3, Finset.mem_map] using hq2
        rcases h_main with ⟨b2', hb2', h_eq⟩
        have h1 : b2' ∈ G₂ ∧ P p' b2' := Finset.mem_filter.mp hb2'
        have hpe : p' = p := congr_arg Prod.fst h_eq
        have hbe : b2' = b2 := congr_arg Prod.snd h_eq
        subst hpe hbe
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp', h1.1⟩, h1.2⟩
    have h_union4 : Case3Triples = (G₁ ×ˢ G₁).biUnion f3 := by
      rw [h_Case3_eq, h_union3]
    have h2 : Case3Triples.card = ∑ p ∈ G₁ ×ˢ G₁, (G₂.filter (fun b2 => P p b2)).card := by
      rw [h_union4, Finset.card_biUnion h_disj3]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.card_map] <;> rfl
    rw [h2, Nat.cast_sum, Finset.sum_product] <;> rfl

  -- Define badLines' for case 3 (empty outside G₁)
  let badLines' : Point2 → Finset (AffineSubspace ℝ Point2) := fun b1 =>
    if b1 ∈ G₁ then badLines b1 else ∅

  have h_badLines'_eq : ∀ b1 ∈ G₁, badLines' b1 = badLines b1 := by
    intro b1 hb1
    simp [badLines', hb1]

  have h_lines_through' : ∀ b1, ∀ ℓ ∈ badLines' b1, b1 ∈ (ℓ : Set Point2) := by
    intro b1 ℓ hℓ
    by_cases h : b1 ∈ G₁
    · rw [h_badLines'_eq b1 h] at hℓ
      exact hM_lines_through b1 h ℓ hℓ
    · simp [badLines', h] at hℓ <;> tauto

  have h_fin' : ∀ b1, ∀ ℓ ∈ badLines' b1, Module.finrank ℝ ℓ.direction = 1 := by
    intro b1 ℓ hℓ
    by_cases h : b1 ∈ G₁
    · rw [h_badLines'_eq b1 h] at hℓ
      exact hM_fin b1 h ℓ hℓ
    · simp [badLines', h] at hℓ <;> tauto

  have h_max_strips' : ∀ b1, (badLines' b1).card ≤ M := by
    intro b1
    by_cases h : b1 ∈ G₁
    · rw [h_badLines'_eq b1 h]
      exact hM_card b1 h
    · simp [badLines', h] <;> omega

  -- Sum with badLines' equals Case3Triples card
  have h_card3' : (∑ b1 ∈ G₁, ∑ b1' ∈ G₁,
        ((G₂.filter (fun b2 =>
          D < dist b1 b1' ∧
          b2 ∉ Metric.thickening s ((lineThrough b1 b1') : Set Point2) ∧
          (∃ ℓ1 ∈ badLines' b1, b2 ∈ Metric.thickening r' (ℓ1 : Set Point2)) ∧
          (∃ ℓ2 ∈ badLines' b1', b2 ∈ Metric.thickening r' (ℓ2 : Set Point2)))).card : ENNReal)) =
      (Case3Triples.card : ENNReal) := by
    have h_eq : ∑ b1 ∈ G₁, ∑ b1' ∈ G₁,
          ((G₂.filter (fun b2 =>
            D < dist b1 b1' ∧
            b2 ∉ Metric.thickening s ((lineThrough b1 b1') : Set Point2) ∧
            (∃ ℓ1 ∈ badLines' b1, b2 ∈ Metric.thickening r' (ℓ1 : Set Point2)) ∧
            (∃ ℓ2 ∈ badLines' b1', b2 ∈ Metric.thickening r' (ℓ2 : Set Point2)))).card : ENNReal) =
        ∑ b1 ∈ G₁, ∑ b1' ∈ G₁,
          ((G₂.filter (fun b2 =>
            D < dist b1 b1' ∧
            b2 ∉ Metric.thickening s ((lineThrough b1 b1') : Set Point2) ∧
            (∃ ℓ1 ∈ badLines b1, b2 ∈ Metric.thickening r' (ℓ1 : Set Point2)) ∧
            (∃ ℓ2 ∈ badLines b1', b2 ∈ Metric.thickening r' (ℓ2 : Set Point2)))).card : ENNReal) := by
      apply Finset.sum_congr rfl
      intro b1 hb1
      apply Finset.sum_congr rfl
      intro b1' hb1'
      have h_eq1 : badLines' b1 = badLines b1 := h_badLines'_eq b1 hb1
      have h_eq2 : badLines' b1' = badLines b1' := h_badLines'_eq b1' hb1'
      congr
      <;> funext b2
      <;> simp [h_eq1, h_eq2]
      <;> tauto
    rw [h_eq]
    exact h_card3.symm

  -- Apply three case lemmas
  have h_case1 : (Case1Triples.card : ENNReal) ≤
      C_F * Kakeya.realRpowENN D 1 * G₁.enncard * G₁.enncard * G₂.enncard := by
    rw [h_card1]
    exact threeCase_case1 hdelta hD_delta hD1 (C_F := C_F) hFrost1

  have h_case2 : (Case2Triples.card : ENNReal) ≤
      Kakeya.realRpowENN (Real.rpow delta (-lambda) * s) zeta *
        G₁.enncard * G₁.enncard * G₂.enncard := by
    rw [h_card2]
    exact threeCase_case2 (hdelta := hdelta) (hlambda := hlambda) (hzeta := hzeta)
      (hs := hs_delta) (hs1 := hs1) (hNonConc := h_nonconc)

  have h_case3 : (Case3Triples.card : ENNReal) ≤
      C_F * Kakeya.realRpowENN (60 * r' / (D * s)) 1 * (M : ENNReal) * (M : ENNReal) *
        G₁.enncard * G₁.enncard * G₂.enncard := by
    have h_main := threeCase_case3 (hδ := hdelta) (hlam := hlambda) (hr := hdelta_r') (hr1 := hr'1)
      (hD := hD_pos) (hs := hs_pos) (hDsr := hDsr)
      (C_F := C_F) (hC_F := hC_F_ge1) (hFrost2 := hFrost2)
      (hG2_ball := hG2_ball) (hG1_ball := hG1_ball)
      (M := M) (badLines := badLines')
      (h_lines_through := h_lines_through')
      (h_fin := h_fin')
      (h_max_strips := h_max_strips')
    rw [← h_card3']
    exact h_main

  -- Evaluate case bound 1
  have h_pos_a : 0 ≤ Real.rpow delta (-lambda) := Real.rpow_nonneg (by linarith) _
  have h_pos_b : 0 ≤ Real.rpow D 1 := Real.rpow_nonneg (by positivity) _
  have h_exp1 : C_F * Kakeya.realRpowENN D 1 = Kakeya.realRpowENN delta (4 * alpha) := by
    have h2 : C_F = ENNReal.ofReal (Real.rpow delta (-lambda)) := by
      simp [hC_F_def, Kakeya.realRpowENN]
    have h3 : Kakeya.realRpowENN D 1 = ENNReal.ofReal (Real.rpow D 1) := by
      simp [Kakeya.realRpowENN]
    have h4 : C_F * Kakeya.realRpowENN D 1 =
        ENNReal.ofReal (Real.rpow delta (-lambda) * Real.rpow D 1) := by
      rw [h2, h3]
      rw [ENNReal.ofReal_mul h_pos_a]
    rw [h4]
    have h5 : Real.rpow D 1 = D := Real.rpow_one D
    have h6 : Real.rpow delta (-lambda) * Real.rpow D 1 = Real.rpow delta (4 * alpha) := by
      have hD1 : Real.rpow D 1 = D := Real.rpow_one D
      rw [hD1, hD_def]
      have h_sum : Real.rpow delta (-lambda) * Real.rpow delta (lambda + 4 * alpha) =
          Real.rpow delta ((-lambda) + (lambda + 4 * alpha)) :=
        (Real.rpow_add hdelta (-lambda) (lambda + 4 * alpha)).symm
      rw [h_sum]
      have h_exp : (-lambda) + (lambda + 4 * alpha) = 4 * alpha := by ring
      rw [h_exp]
    rw [h6]
    <;> simp [Kakeya.realRpowENN]

  -- Evaluate case bound 2
  have h_exp2 : Kakeya.realRpowENN (Real.rpow delta (-lambda) * s) zeta =
      Kakeya.realRpowENN delta (4 * alpha) := by
    have h1 : Real.rpow delta (-lambda) * s = Real.rpow delta (4 * alpha / zeta) := by
      rw [hs_def]
      have h_sum : Real.rpow delta (-lambda) * Real.rpow delta (lambda + 4 * alpha / zeta) =
          Real.rpow delta ((-lambda) + (lambda + 4 * alpha / zeta)) :=
        (Real.rpow_add hdelta (-lambda) (lambda + 4 * alpha / zeta)).symm
      rw [h_sum]
      have h_exp : (-lambda) + (lambda + 4 * alpha / zeta) = 4 * alpha / zeta := by ring
      rw [h_exp]
    rw [h1]
    have h2 : Real.rpow (Real.rpow delta (4 * alpha / zeta)) zeta =
        Real.rpow delta (4 * alpha) := by
      have h_mul : Real.rpow delta ((4 * alpha / zeta) * zeta) =
          Real.rpow (Real.rpow delta (4 * alpha / zeta)) zeta :=
        Real.rpow_mul (by linarith) (4 * alpha / zeta) zeta
      have h_eq : Real.rpow (Real.rpow delta (4 * alpha / zeta)) zeta =
          Real.rpow delta ((4 * alpha / zeta) * zeta) := h_mul.symm
      rw [h_eq]
      have h3 : (4 * alpha / zeta) * zeta = 4 * alpha := by
        field_simp [hzeta.ne'] <;> ring
      rw [h3]
    have h4 : Kakeya.realRpowENN (Real.rpow delta (4 * alpha / zeta)) zeta =
        Kakeya.realRpowENN delta (4 * alpha) := by
      simp only [Kakeya.realRpowENN]
      exact congr_arg ENNReal.ofReal h2
    exact h4

  have hK_pos : 0 < K := by linarith
  have h_scale_sq : Real.rpow scale (1 / 2 : ℝ) ^ 2 = scale := by
    have h : Real.rpow scale (1 / 2 : ℝ) * Real.rpow scale (1 / 2 : ℝ) =
        Real.rpow scale ((1 / 2 : ℝ) + (1 / 2 : ℝ)) :=
      (Real.rpow_add hscale_pos _ _).symm
    have h2 : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
    have h3 : Real.rpow scale (1 / 2 : ℝ) ^ 2 =
        Real.rpow scale (1 / 2 : ℝ) * Real.rpow scale (1 / 2 : ℝ) := by ring
    rw [h3, h, h2] <;> simp

  have hM2_bound : (M : ENNReal)^2 ≤
      ENNReal.ofReal (400 / (K ^ 4 * scale)) := by
    have h_real : (M : ℝ)^2 ≤ 400 / (K ^ 4 * scale) := by
      have h_a : (M : ℝ)^2 ≤ (20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ))) ^ 2 := by
        gcongr <;> linarith
      have h_simp : (20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ))) ^ 2 =
          400 / (K ^ 4 * Real.rpow scale (1 / 2 : ℝ) ^ 2) := by ring
      rw [h_simp, h_scale_sq] at h_a
      exact h_a
    have h_cast : (M : ENNReal)^2 = ENNReal.ofReal ((M : ℝ)^2) := by
      simp [pow_two]
      <;> norm_cast
    rw [h_cast]
    exact ENNReal.ofReal_le_ofReal h_real

  -- Evaluate case bound 3 using helper lemma
  have hK_pos : 0 < K := by linarith
  have hDs : D * s = Real.rpow delta (2 * lambda + 4 * alpha + 4 * alpha / zeta) := by
    have h1 : D * s = Real.rpow delta (lambda + 4 * alpha) * Real.rpow delta (lambda + 4 * alpha / zeta) := by
      rw [hD_def, hs_def]
    rw [h1]
    have h_add : Real.rpow delta (lambda + 4 * alpha) * Real.rpow delta (lambda + 4 * alpha / zeta) =
        Real.rpow delta ((lambda + 4 * alpha) + (lambda + 4 * alpha / zeta)) :=
      (Real.rpow_add hdelta (lambda + 4 * alpha) (lambda + 4 * alpha / zeta)).symm
    rw [h_add]
    have h_exp_eq : (lambda + 4 * alpha) + (lambda + 4 * alpha / zeta) =
        2 * lambda + 4 * alpha + 4 * alpha / zeta := by ring
    rw [h_exp_eq]
  have h_exp3 : C_F * Kakeya.realRpowENN (60 * r' / (D * s)) 1 * (M : ENNReal)^2 ≤
      Kakeya.realRpowENN delta (4 * alpha) := by
    have h_main := case3_ENNReal_bound hdelta hlambda hzeta halpha hscale_pos hK_pos hD_pos hs_pos hDs hM_bound hprem3
    have h_eq1 : C_F = Kakeya.realRpowENN delta (-lambda) := by
      simp [hC_F_def]
    have h_eq2 : (60 * r' / (D * s)) = 60 * (13 * scale) / (D * s) := by
      rw [hr'_def] <;> ring
    have h_eq3 : (M : ENNReal)^2 = (M : ENNReal) * (M : ENNReal) := by ring
    have h_lhs_eq : C_F * Kakeya.realRpowENN (60 * r' / (D * s)) 1 * (M : ENNReal)^2 =
        Kakeya.realRpowENN delta (-lambda) * Kakeya.realRpowENN (60 * (13 * scale) / (D * s)) 1 *
          (M : ENNReal) * (M : ENNReal) := by
      rw [h_eq1, h_eq2]
      <;> ring
    rw [h_lhs_eq]
    exact h_main

  -- Combine case bounds
  have h_bound1 : (Case1Triples.card : ENNReal) ≤
      Kakeya.realRpowENN delta (4 * alpha) * G₁.enncard * G₁.enncard * G₂.enncard := by
    rw [h_exp1] at h_case1
    exact h_case1
  have h_bound2 : (Case2Triples.card : ENNReal) ≤
      Kakeya.realRpowENN delta (4 * alpha) * G₁.enncard * G₁.enncard * G₂.enncard := by
    rw [h_exp2] at h_case2
    exact h_case2
  have h_bound3 : (Case3Triples.card : ENNReal) ≤
      Kakeya.realRpowENN delta (4 * alpha) * G₁.enncard * G₁.enncard * G₂.enncard := by
    have hM_sq : (M : ENNReal) * (M : ENNReal) = (M : ENNReal)^2 := by ring
    have h_case3' : (Case3Triples.card : ENNReal) ≤
        C_F * Kakeya.realRpowENN (60 * r' / (D * s)) 1 * (M : ENNReal)^2 *
        G₁.enncard * G₁.enncard * G₂.enncard := by
      convert h_case3 using 1
      <;> ring
    calc (Case3Triples.card : ENNReal)
      ≤ C_F * Kakeya.realRpowENN (60 * r' / (D * s)) 1 * (M : ENNReal)^2 *
          G₁.enncard * G₁.enncard * G₂.enncard := h_case3'
    _ = (C_F * Kakeya.realRpowENN (60 * r' / (D * s)) 1 * (M : ENNReal)^2) *
          G₁.enncard * G₁.enncard * G₂.enncard := by ring
    _ ≤ Kakeya.realRpowENN delta (4 * alpha) *
          G₁.enncard * G₁.enncard * G₂.enncard := by
      have h_factor : 0 ≤ G₁.enncard * G₁.enncard * G₂.enncard := by positivity
      have h : (C_F * Kakeya.realRpowENN (60 * r' / (D * s)) 1 * (M : ENNReal)^2) *
          (G₁.enncard * G₁.enncard * G₂.enncard) ≤
          Kakeya.realRpowENN delta (4 * alpha) *
          (G₁.enncard * G₁.enncard * G₂.enncard) :=
        mul_le_mul_of_nonneg_right h_exp3 h_factor
      simpa [mul_assoc] using h

  have h_T_bound : T_enn ≤
      3 * Kakeya.realRpowENN delta (4 * alpha) * G₁.enncard * G₁.enncard * G₂.enncard := by
    have h_card_union : BadTriples.card ≤
        Case1Triples.card + Case2Triples.card + Case3Triples.card := by
      have hsub : BadTriples ⊆ Case1Triples ∪ Case2Triples ∪ Case3Triples := h_cover
      have h1 : BadTriples.card ≤ (Case1Triples ∪ Case2Triples ∪ Case3Triples).card :=
        Finset.card_le_card hsub
      have h2 : (Case1Triples ∪ Case2Triples ∪ Case3Triples).card ≤
          Case1Triples.card + Case2Triples.card + Case3Triples.card := by
        calc (Case1Triples ∪ Case2Triples ∪ Case3Triples).card
          ≤ (Case1Triples ∪ Case2Triples).card + Case3Triples.card := Finset.card_union_le _ _
        _ ≤ Case1Triples.card + Case2Triples.card + Case3Triples.card := by
          have h3 : (Case1Triples ∪ Case2Triples).card ≤ Case1Triples.card + Case2Triples.card :=
            Finset.card_union_le _ _
          linarith
      linarith
    have h_enn : (BadTriples.card : ENNReal) ≤
        (Case1Triples.card : ENNReal) + (Case2Triples.card : ENNReal) + (Case3Triples.card : ENNReal) := by
      exact_mod_cast h_card_union
    rw [h_T_enn]
    calc (BadTriples.card : ENNReal)
      ≤ (Case1Triples.card : ENNReal) + (Case2Triples.card : ENNReal) + (Case3Triples.card : ENNReal) := h_enn
    _ ≤ Kakeya.realRpowENN delta (4 * alpha) * G₁.enncard * G₁.enncard * G₂.enncard +
          Kakeya.realRpowENN delta (4 * alpha) * G₁.enncard * G₁.enncard * G₂.enncard +
          Kakeya.realRpowENN delta (4 * alpha) * G₁.enncard * G₁.enncard * G₂.enncard := by
        gcongr <;> tauto
    _ = 3 * Kakeya.realRpowENN delta (4 * alpha) * G₁.enncard * G₁.enncard * G₂.enncard := by ring

  -- Convert to real and Cauchy-Schwarz
  have h_LHS_cast : (∑ b2 ∈ G₂, (d b2 : ENNReal)^2) =
      ENNReal.ofReal (∑ b2 ∈ G₂, (d b2 : ℝ)^2) := by
    have h1 : ∀ b2 ∈ G₂, (d b2 : ENNReal)^2 = ENNReal.ofReal ((d b2 : ℝ)^2) := by
      intro b2 _
      simp [pow_two]
      <;> norm_cast
    have h_sum : (∑ b2 ∈ G₂, (d b2 : ENNReal)^2) =
        ∑ b2 ∈ G₂, ENNReal.ofReal ((d b2 : ℝ)^2) := by
      apply Finset.sum_congr rfl
      intro b2 hb2
      exact h1 b2 hb2
    rw [h_sum]
    have h_ofReal_sum : ENNReal.ofReal (∑ b2 ∈ G₂, (d b2 : ℝ)^2) =
        ∑ b2 ∈ G₂, ENNReal.ofReal ((d b2 : ℝ)^2) := by
      have h_nonneg : ∀ b2 ∈ G₂, 0 ≤ (d b2 : ℝ)^2 := by intro b2 _; positivity
      rw [ENNReal.ofReal_sum_of_nonneg h_nonneg]
    exact h_ofReal_sum.symm
  have h_RHS_cast : 3 * Kakeya.realRpowENN delta (4 * alpha) * G₁.enncard * G₁.enncard * G₂.enncard =
      ENNReal.ofReal (3 * Real.rpow delta (4 * alpha) * (G₁.card : ℝ)^2 * (G₂.card : ℝ)) := by
    have h1 : G₁.enncard = ENNReal.ofReal (G₁.card : ℝ) := by
      have h : G₁.enncard = (G₁.card : ENNReal) := by rfl
      rw [h]
      have h' : ENNReal.ofReal (G₁.card : ℝ) = (G₁.card : ENNReal) := by
        simpa using ENNReal.ofReal_natCast G₁.card
      exact h'.symm
    have h2 : G₂.enncard = ENNReal.ofReal (G₂.card : ℝ) := by
      have h : G₂.enncard = (G₂.card : ENNReal) := by rfl
      rw [h]
      have h' : ENNReal.ofReal (G₂.card : ℝ) = (G₂.card : ENNReal) := by
        simpa using ENNReal.ofReal_natCast G₂.card
      exact h'.symm
    have h3 : Kakeya.realRpowENN delta (4 * alpha) = ENNReal.ofReal (Real.rpow delta (4 * alpha)) := by
      rfl
    have h4 : (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) := by
      norm_cast
    rw [h1, h2, h3, h4]
    have ha : 0 ≤ (3 : ℝ) := by norm_num
    have hb : 0 ≤ Real.rpow delta (4 * alpha) := Real.rpow_nonneg (by linarith) _
    have hc : 0 ≤ (G₁.card : ℝ) := Nat.cast_nonneg _
    have hd : 0 ≤ (G₂.card : ℝ) := Nat.cast_nonneg _
    have hab : 0 ≤ (3 : ℝ) * Real.rpow delta (4 * alpha) := mul_nonneg ha hb
    have habc : 0 ≤ (3 : ℝ) * Real.rpow delta (4 * alpha) * (G₁.card : ℝ) := mul_nonneg hab hc
    have habcd : 0 ≤ (3 : ℝ) * Real.rpow delta (4 * alpha) * (G₁.card : ℝ) * (G₁.card : ℝ) := mul_nonneg habc hc
    have h_s1 : ENNReal.ofReal (3 : ℝ) * ENNReal.ofReal (Real.rpow delta (4 * alpha)) =
        ENNReal.ofReal ((3 : ℝ) * Real.rpow delta (4 * alpha)) :=
      (ENNReal.ofReal_mul ha).symm
    have h_s2 : ENNReal.ofReal ((3 : ℝ) * Real.rpow delta (4 * alpha)) * ENNReal.ofReal (G₁.card : ℝ) =
        ENNReal.ofReal (((3 : ℝ) * Real.rpow delta (4 * alpha)) * (G₁.card : ℝ)) :=
      (ENNReal.ofReal_mul hab).symm
    have h_s3 : ENNReal.ofReal (((3 : ℝ) * Real.rpow delta (4 * alpha)) * (G₁.card : ℝ)) * ENNReal.ofReal (G₁.card : ℝ) =
        ENNReal.ofReal ((((3 : ℝ) * Real.rpow delta (4 * alpha)) * (G₁.card : ℝ)) * (G₁.card : ℝ)) :=
      (ENNReal.ofReal_mul habc).symm
    have h_s4 : ENNReal.ofReal ((((3 : ℝ) * Real.rpow delta (4 * alpha)) * (G₁.card : ℝ)) * (G₁.card : ℝ)) * ENNReal.ofReal (G₂.card : ℝ) =
        ENNReal.ofReal (((((3 : ℝ) * Real.rpow delta (4 * alpha)) * (G₁.card : ℝ)) * (G₁.card : ℝ)) * (G₂.card : ℝ)) :=
      (ENNReal.ofReal_mul habcd).symm
    rw [h_s1, h_s2, h_s3, h_s4]
    <;> congr 1 <;> ring
  have h9' : ENNReal.ofReal (∑ b2 ∈ G₂, (d b2 : ℝ)^2) ≤
      ENNReal.ofReal (3 * Real.rpow delta (4 * alpha) * (G₁.card : ℝ)^2 * (G₂.card : ℝ)) := by
    rw [← h_LHS_cast, ← h_RHS_cast]
    exact h_T_bound
  have h_LHS_nonneg : 0 ≤ ∑ b2 ∈ G₂, (d b2 : ℝ)^2 := by
    apply Finset.sum_nonneg
    intro b2 _
    exact sq_nonneg _
  have h_RHS_nonneg : 0 ≤ 3 * Real.rpow delta (4 * alpha) * (G₁.card : ℝ)^2 * (G₂.card : ℝ) := by
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · norm_num
        · exact Real.rpow_nonneg (by linarith) _
      · exact sq_nonneg _
    · exact Nat.cast_nonneg _
  have hT_real : ∑ b2 ∈ G₂, (d b2 : ℝ)^2 ≤
      3 * Real.rpow delta (4 * alpha) * (G₁.card : ℝ)^2 * (G₂.card : ℝ) :=
    ENNReal_bound_to_real h_LHS_nonneg h_RHS_nonneg h9'

  have hN_sum_real : N_bad = ∑ b2 ∈ G₂, (d b2 : ℝ) := hN_bad_sum

  have h_cs : N_bad ^ 2 ≤ (G₂.card : ℝ) * (∑ b2 ∈ G₂, (d b2 : ℝ)^2) := by
    rw [hN_sum_real]
    exact sq_sum_le_card_mul_sum_sq

  have h_final : N_bad ^ 2 ≤
      3 * Real.rpow delta (4 * alpha) * (G₁.card : ℝ)^2 * (G₂.card : ℝ)^2 := by
    calc N_bad ^ 2
      ≤ (G₂.card : ℝ) * (∑ b2 ∈ G₂, (d b2 : ℝ)^2) := h_cs
    _ ≤ (G₂.card : ℝ) * (3 * Real.rpow delta (4 * alpha) * (G₁.card : ℝ)^2 * (G₂.card : ℝ)) := by
      have hG2_nonneg : 0 ≤ (G₂.card : ℝ) := Nat.cast_nonneg _
      exact mul_le_mul_of_nonneg_left hT_real hG2_nonneg
    _ = 3 * Real.rpow delta (4 * alpha) * (G₁.card : ℝ)^2 * (G₂.card : ℝ)^2 := by ring

  have hN_nonneg : 0 ≤ N_bad := by
    simp only [N_bad]
    exact Nat.cast_nonneg _
  have h13 : 0 ≤ Real.rpow delta (4 * alpha) := Real.rpow_nonneg (by linarith) _
  set X : ℝ := Real.sqrt 3 * Real.sqrt (Real.rpow delta (4 * alpha)) *
      (G₁.card : ℝ) * (G₂.card : ℝ) with hX_def
  have hX_nonneg : 0 ≤ X := by
    rw [hX_def]
    have h1 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    have h2 : 0 ≤ Real.sqrt (Real.rpow delta (4 * alpha)) := Real.sqrt_nonneg _
    have h3 : 0 ≤ (G₁.card : ℝ) := Nat.cast_nonneg _
    have h4 : 0 ≤ (G₂.card : ℝ) := Nat.cast_nonneg _
    have h5 : 0 ≤ Real.sqrt 3 * Real.sqrt (Real.rpow delta (4 * alpha)) := mul_nonneg h1 h2
    have h6 : 0 ≤ Real.sqrt 3 * Real.sqrt (Real.rpow delta (4 * alpha)) * (G₁.card : ℝ) := mul_nonneg h5 h3
    exact mul_nonneg h6 h4
  have hX_sq : X ^ 2 = 3 * Real.rpow delta (4 * alpha) * (G₁.card : ℝ)^2 * (G₂.card : ℝ)^2 := by
    rw [hX_def]
    have h_expand : ∀ (a b c d : ℝ), (a * b * c * d) ^ 2 = a^2 * b^2 * c^2 * d^2 := by
      intro a b c d; ring
    rw [h_expand]
    have h_sq3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h_sq_rpow : (Real.sqrt (Real.rpow delta (4 * alpha))) ^ 2 = Real.rpow delta (4 * alpha) :=
      Real.sq_sqrt (by linarith)
    rw [h_sq3, h_sq_rpow] <;> ring
  have h_sqrt : N_bad ≤ X := by
    have h14 : N_bad ^ 2 ≤ X ^ 2 := by
      rw [hX_sq]
      exact h_final
    have h15 : 0 ≤ N_bad := by
      dsimp only [N_bad]
      exact Nat.cast_nonneg _
    have h16 : 0 ≤ X := hX_nonneg
    have h17 : abs N_bad ≤ abs X := sq_le_sq.mp h14
    rw [abs_of_nonneg h15, abs_of_nonneg h16] at h17
    exact h17
  have h17_rpow : Real.sqrt (Real.rpow delta (4 * alpha)) = Real.rpow delta (2 * alpha) := by
    have h_nonneg : 0 ≤ Real.rpow delta (4 * alpha) := Real.rpow_nonneg (by linarith) _
    have h_sqrt_eq : Real.sqrt (Real.rpow delta (4 * alpha)) = Real.rpow (Real.rpow delta (4 * alpha)) (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow (Real.rpow delta (4 * alpha))
    rw [h_sqrt_eq]
    have hdelta_le : 0 ≤ delta := by exact le_of_lt hdelta
    have h_mul : Real.rpow (Real.rpow delta (4 * alpha)) (1 / 2 : ℝ) = Real.rpow delta ((4 * alpha) * (1 / 2 : ℝ)) :=
      (Real.rpow_mul hdelta_le (4 * alpha) (1 / 2 : ℝ)).symm
    rw [h_mul]
    have h_exp : (4 * alpha) * (1 / 2 : ℝ) = 2 * alpha := by ring
    rw [h_exp]
  have h_sqrt2 : N_bad ≤ Real.sqrt 3 * Real.rpow delta (2 * alpha) * (G₁.card : ℝ) * (G₂.card : ℝ) := by
    have h : N_bad ≤ X := h_sqrt
    rw [hX_def] at h
    rw [h17_rpow] at h
    exact h
  have h18 : Real.sqrt 3 ≤ Real.sqrt 312002 := by
    gcongr <;> norm_num
  have h19 : N_bad ≤ Real.sqrt 312002 * Real.rpow delta (2 * alpha) *
      (G₁.card : ℝ) * (G₂.card : ℝ) := by
    calc N_bad
      ≤ Real.sqrt 3 * Real.rpow delta (2 * alpha) * (G₁.card : ℝ) * (G₂.card : ℝ) := h_sqrt2
    _ = (Real.sqrt 3) * (Real.rpow delta (2 * alpha) * (G₁.card : ℝ) * (G₂.card : ℝ)) := by ring
    _ ≤ (Real.sqrt 312002) * (Real.rpow delta (2 * alpha) * (G₁.card : ℝ) * (G₂.card : ℝ)) := by
      have h_pos_tail : 0 ≤ Real.rpow delta (2 * alpha) * (G₁.card : ℝ) * (G₂.card : ℝ) :=
        mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right h18 h_pos_tail
    _ = Real.sqrt 312002 * Real.rpow delta (2 * alpha) * (G₁.card : ℝ) * (G₂.card : ℝ) := by ring
  exact h19

end Kakeya.Assouad
