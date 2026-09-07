module

public import Mathlib.Combinatorics.Additive.Energy
public import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith

@[expose] public section

set_option maxHeartbeats 500000

/-!
# Balog-Szemerédi-Gowers Theorem

This file formalizes the Balog-Szemerédi-Gowers theorem for finite sets in an
additive commutative group.

## Main result

`balog_szemeredi_gowers`: Given a bipartite graph `G ⊂ A × B` with density
at least `1/K` and restricted sumset size at most `K * sqrt(|A||B|)`, there
exist large subsets `A' ⊂ A`, `B' ⊂ B` with polynomially small sumset.

## Proof route

Following Tao-Vu and the dependent-random-choice approach:
1. Restricted additive energy via Cauchy-Schwarz.
2. Path counting in the bipartite graph.
3. Averaging to find subsets with many length-3 paths.
4. Path-to-sumset lemma: many paths imply small sumset.

## References

* [Tao, Vu, *Additive Combinatorics*, Theorem 6.10][tao-vu]
* [Bourgain, *The discretized sum-product and projection theorems*][bourgain2010]
-/

open scoped Pointwise Combinatorics.Additive

namespace AdditiveCombinatorics.BSG

section Definitions

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The restricted sumset `A +_G B` of a bipartite graph `Gph ⊂ A × B`. -/
def restrictedSum (A B : Finset G) (Gph : Finset (G × G)) : Finset G :=
  Gph.image (fun p : G × G => p.1 + p.2)

/-- The restricted representation function
`r_{Gph}(x) = |{(a,b) ∈ Gph : a+b = x}|`. -/
def restrictedRepFunction (Gph : Finset (G × G)) (x : G) : ℕ :=
  (Gph.filter (fun p : G × G => p.1 + p.2 = x)).card

/-- The restricted additive energy
`E_G(A,B) = ∑_{x ∈ A+_G B} r_{Gph}(x)^2`.
This counts quadruples `(a,b,a',b') ∈ Gph²` with `a+b = a'+b'`. -/
def restrictedAddEnergy (A B : Finset G) (Gph : Finset (G × G)) : ℕ :=
  ∑ x ∈ restrictedSum A B Gph, (restrictedRepFunction Gph x)^2

/-- Degree of `a` in the bipartite graph `Gph`. -/
def degLeft (Gph : Finset (G × G)) (a : G) : ℕ :=
  (Gph.filter (fun p => p.1 = a)).card

/-- Degree of `b` in the bipartite graph `Gph`. -/
def degRight (Gph : Finset (G × G)) (b : G) : ℕ :=
  (Gph.filter (fun p => p.2 = b)).card

/-- Number of length-2 paths between `a` and `a'` (through `B`):
`p₂(a,a') = |{b : (a,b) ∈ Gph ∧ (a',b) ∈ Gph}|`. -/
def path2 (Gph : Finset (G × G)) (a a' : G) : ℕ :=
  (((Gph.filter (fun p => p.1 = a)).image Prod.snd) ∩
   ((Gph.filter (fun p => p.1 = a')).image Prod.snd)).card

/-- The set of intermediate pairs `(b₁, a₁)` forming a length-3 path
    `a → b₁ → a₁ → b` in the bipartite graph `Gph`. -/
def path3Set (Gph : Finset (G × G)) (a b : G) : Finset (G × G) :=
  (Gph.filter (fun e => e.1 = a)).biUnion (fun e1 =>
    (Gph.filter (fun e => e.2 = e1.2)).biUnion (fun e2 =>
      if (e2.1, b) ∈ Gph then ({(e1.2, e2.1)} : Finset (G × G)) else ∅))

/-- Number of length-3 paths from `a` to `b`:
`p₃(a,b) = |{(b₁,a₁) : (a,b₁)∈Gph, (a₁,b₁)∈Gph, (a₁,b)∈Gph}|`. -/
def path3 (Gph : Finset (G × G)) (a b : G) : ℕ :=
  (path3Set Gph a b).card

/-- Characterization of membership in `path3Set`. -/
lemma mem_path3Set_iff (Gph : Finset (G × G)) (a b b₁ a₁ : G) :
    (b₁, a₁) ∈ path3Set Gph a b ↔
      (a, b₁) ∈ Gph ∧ (a₁, b₁) ∈ Gph ∧ (a₁, b) ∈ Gph := by
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨e1, he1_filter, h_inner⟩
    have he1 : e1 ∈ Gph := (Finset.mem_filter.mp he1_filter).1
    have h_e11 : e1.1 = a := (Finset.mem_filter.mp he1_filter).2
    rcases Finset.mem_biUnion.mp h_inner with ⟨e2, he2_filter, hcond⟩
    have he2 : e2 ∈ Gph := (Finset.mem_filter.mp he2_filter).1
    have h_e22 : e2.2 = e1.2 := (Finset.mem_filter.mp he2_filter).2
    have h_if : (e2.1, b) ∈ Gph := by
      by_cases h : (e2.1, b) ∈ Gph
      · exact h
      · rw [if_neg h] at hcond <;> simp at hcond
    have h_pair : (e1.2, e2.1) = (b₁, a₁) := by
      by_cases h : (e2.1, b) ∈ Gph
      · rw [if_pos h] at hcond
        have h' : (b₁, a₁) = (e1.2, e2.1) := by simpa using hcond
        exact h'.symm
      · exfalso
        rw [if_neg h] at hcond <;> simp at hcond
    have h_b1 : e1.2 = b₁ := (Prod.ext_iff.1 h_pair).1
    have h_a1 : e2.1 = a₁ := (Prod.ext_iff.1 h_pair).2
    have h_e1_eq : e1 = (a, b₁) := by
      exact Prod.ext h_e11 h_b1
    have h_e22' : e2.2 = b₁ := by
      rw [h_e22, h_b1]
    have h_e2_eq : e2 = (a₁, b₁) := by
      exact Prod.ext h_a1 h_e22'
    exact ⟨by rw [h_e1_eq] at he1; exact he1,
      by rw [h_e2_eq] at he2; exact he2,
      by simpa [h_a1] using h_if⟩
  · rintro ⟨h1, h2, h3⟩
    have h_outer : (a, b₁) ∈ Gph.filter (fun e : G × G => e.1 = a) := by
      simp [h1]
    have h_inner2 : (a₁, b₁) ∈ (Gph.filter (fun e : G × G => e.2 = (a, b₁).2)) := by
      simp [h2]
    have h_final : (b₁, a₁) ∈ if ((a₁, b₁).1, b) ∈ Gph then
        ({((a, b₁).2, (a₁, b₁).1)} : Finset (G × G)) else ∅ := by
      rw [if_pos h3]
      simp
    exact Finset.mem_biUnion.mpr ⟨(a, b₁), h_outer,
      Finset.mem_biUnion.mpr ⟨(a₁, b₁), h_inner2, h_final⟩⟩

end Definitions

section Neighborhoods

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Right-neighborhood of b in Gph: {a : (a,b) ∈ Gph}. -/
def neighRight (Gph : Finset (G × G)) (b : G) : Finset G :=
  (Gph.filter (fun p => p.2 = b)).image Prod.fst

/-- Left-neighborhood of a in Gph: {b : (a,b) ∈ Gph}. -/
def neighLeft (Gph : Finset (G × G)) (a : G) : Finset G :=
  (Gph.filter (fun p => p.1 = a)).image Prod.snd

/-- Number of common left-neighbors of b₁, b₂. -/
def commonNeighRight (Gph : Finset (G × G)) (b₁ b₂ : G) : ℕ :=
  (neighRight Gph b₁ ∩ neighRight Gph b₂).card

/-- Cardinality of neighLeft equals degLeft. -/
lemma card_neighLeft_eq_degLeft (Gph : Finset (G × G)) (a : G) :
    (neighLeft Gph a).card = degLeft Gph a := by
  have h_inj : Set.InjOn Prod.snd ((Gph.filter (fun p : G × G => p.1 = a)) : Set (G × G)) := by
    intro p hp q hq h
    have hpf : p.1 = a := (Finset.mem_filter.mp hp).2
    have hqf : q.1 = a := (Finset.mem_filter.mp hq).2
    have h_eq : p.1 = q.1 := by rw [hpf, hqf]
    exact Prod.ext h_eq h
  simpa [neighLeft, degLeft, Finset.card_image_of_injOn h_inj] using rfl

end Neighborhoods

section EnergyBound

variable {G : Type*} [AddCommGroup G] [DecidableEq G]
  {A B : Finset G} {Gph : Finset (G × G)}

/-- The sum of restricted representation functions equals the number of edges. -/
lemma sum_restrictedRepFunction :
    ∑ x ∈ restrictedSum A B Gph, restrictedRepFunction Gph x = Gph.card := by
  let f : G × G → G := fun p => p.1 + p.2
  let t := restrictedSum A B Gph
  have h_maps : (Gph : Set (G × G)).MapsTo f t := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have h : Gph.card = ∑ x ∈ t, (Gph.filter (fun p => f p = x)).card :=
    Finset.card_eq_sum_card_fiberwise (H := h_maps)
  exact Eq.symm h

/-- Restricted additive energy counts additive quadruples in `Gph`. -/
lemma restrictedAddEnergy_eq_card_quadruples :
    restrictedAddEnergy A B Gph =
    ((Gph.product Gph).filter
      (fun p : (G × G) × (G × G) => p.1.1 + p.1.2 = p.2.1 + p.2.2)).card := by
  let f : G × G → G := fun p => p.1 + p.2
  let t := restrictedSum A B Gph
  let P : Finset ((G × G) × (G × G)) :=
    (Gph.product Gph).filter (fun pair => f pair.1 = f pair.2)
  have h_r : ∀ x, (P.filter (fun pair => f pair.1 = x)).card =
      (Gph.filter (fun p => f p = x)).card ^ 2 := by
    intro x
    let Fx := Gph.filter (fun p => f p = x)
    have h_eq : (P.filter (fun pair => f pair.1 = x)) = Fx.product Fx := by
      apply Finset.ext
      intro z
      rcases z with ⟨p1, p2⟩
      have h : (p1, p2) ∈ P.filter (fun pair => f pair.1 = x) ↔ p1 ∈ Fx ∧ p2 ∈ Fx := by
        simp only [P, Fx, Finset.mem_filter, Finset.mem_product, f]
        <;> aesop
      have h_prod : (p1, p2) ∈ Fx.product Fx ↔ p1 ∈ Fx ∧ p2 ∈ Fx := by
        simp [Finset.mem_product]
      have h' : (p1, p2) ∈ P.filter (fun pair => f pair.1 = x) ↔ (p1, p2) ∈ Fx.product Fx := by
        rw [h_prod]
        exact h
      exact h'
    rw [h_eq]
    have h_card : (Fx.product Fx).card = Fx.card * Fx.card := Finset.card_product _ _
    rw [h_card]
    <;> ring
  have h_main : P.card = ∑ x ∈ t, (P.filter (fun pair => f pair.1 = x)).card := by
    let g : (G × G) × (G × G) → G := fun pair => f pair.1
    have h_maps : (P : Set ((G × G) × (G × G))).MapsTo g t := by
      intro pair hp
      have h4 : pair.1 ∈ Gph := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      exact Finset.mem_image.mpr ⟨pair.1, h4, rfl⟩
    exact Finset.card_eq_sum_card_fiberwise (H := h_maps)
  have h1 : restrictedAddEnergy A B Gph =
      ∑ x ∈ t, (Gph.filter (fun p => f p = x)).card ^ 2 := by rfl
  rw [h1]
  have h2 : ∑ x ∈ t, (Gph.filter (fun p => f p = x)).card ^ 2 =
      ∑ x ∈ t, (P.filter (fun pair => f pair.1 = x)).card := by
    apply Finset.sum_congr rfl
    intro x _
    exact (h_r x).symm
  rw [h2, h_main]

/-- **Cauchy-Schwarz lower bound on restricted additive energy.** -/
theorem restrictedAddEnergy_ge :
    Gph.card ^ 2 ≤ (restrictedSum A B Gph).card * restrictedAddEnergy A B Gph := by
  have h1 : ∑ x ∈ restrictedSum A B Gph, restrictedRepFunction Gph x = Gph.card :=
    sum_restrictedRepFunction
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq (restrictedSum A B Gph)
    (fun _ => (1 : ℕ)) (fun x => restrictedRepFunction Gph x)
  have h3 : (∑ x ∈ restrictedSum A B Gph, restrictedRepFunction Gph x) ^ 2 ≤
      (restrictedSum A B Gph).card * restrictedAddEnergy A B Gph := by
    simpa [restrictedAddEnergy] using h2
  rw [h1] at h3
  exact h3

end EnergyBound

section PathCounting

variable {G : Type*} [AddCommGroup G] [DecidableEq G]
  {A B : Finset G} {Gph : Finset (G × G)}

/-- `∑_b d_B(b) = |Gph|`. -/
lemma sum_degRight_eq_card (hG : Gph ⊆ A ×ˢ B) :
    ∑ b ∈ B, degRight Gph b = Gph.card := by
  let f : G × G → G := fun p => p.2
  have h_maps : (Gph : Set (G × G)).MapsTo f B := by
    intro p hp
    have h4 : p ∈ A ×ˢ B := hG hp
    exact (Finset.mem_product.mp h4).2
  have h : Gph.card = ∑ b ∈ B, (Gph.filter (fun p => f p = b)).card :=
    Finset.card_eq_sum_card_fiberwise (H := h_maps)
  exact Eq.symm h

/-- Total length-2 paths equals `∑_b d_B(b)^2`. -/
lemma total_path2_eq_sum_deg_sq (hG : Gph ⊆ A ×ˢ B) :
    ∑ a ∈ A, ∑ a' ∈ A, path2 Gph a a' =
    ∑ b ∈ B, (degRight Gph b)^2 := by
  let P : Finset ((G × G) × (G × G)) :=
    (Gph.product Gph).filter (fun pair => pair.1.2 = pair.2.2)
  have hR : P.card = ∑ b ∈ B, (degRight Gph b)^2 := by
    let g : (G × G) × (G × G) → G := fun pair => pair.1.2
    have h_maps : (P : Set ((G × G) × (G × G))).MapsTo g B := by
      intro pair hp
      have h4 : pair.1 ∈ Gph := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      have h5 : pair.1 ∈ A ×ˢ B := hG h4
      exact (Finset.mem_product.mp h5).2
    have h : P.card = ∑ b ∈ B, (P.filter (fun pair => g pair = b)).card :=
      Finset.card_eq_sum_card_fiberwise (H := h_maps)
    rw [h]
    apply Finset.sum_congr rfl
    intro b _
    have h2 : (P.filter (fun pair => g pair = b)) =
        (Gph.filter (fun p => p.2 = b)).product (Gph.filter (fun p => p.2 = b)) := by
      apply Finset.ext
      intro z
      rcases z with ⟨p1, p2⟩
      have h : (p1, p2) ∈ P.filter (fun pair => g pair = b) ↔
          p1 ∈ Gph.filter (fun p => p.2 = b) ∧ p2 ∈ Gph.filter (fun p => p.2 = b) := by
        simp only [P, g, Finset.mem_filter, Finset.mem_product]
        <;> aesop
      let Fb := Gph.filter (fun p => p.2 = b)
      have h_prod : (p1, p2) ∈ Fb.product Fb ↔ p1 ∈ Fb ∧ p2 ∈ Fb := by
        simp [Finset.mem_product]
      have h' : (p1, p2) ∈ P.filter (fun pair => g pair = b) ↔
          (p1, p2) ∈ Fb.product Fb := by
        rw [h_prod]
        exact h
      exact h'
    rw [h2]
    have h_card : ((Gph.filter (fun p => p.2 = b)).product
        (Gph.filter (fun p => p.2 = b))).card =
        (Gph.filter (fun p => p.2 = b)).card * (Gph.filter (fun p => p.2 = b)).card :=
      Finset.card_product _ _
    rw [h_card]
    have h_deg : degRight Gph b = (Gph.filter (fun p => p.2 = b)).card := by
      rfl
    rw [h_deg]
    <;> ring
  have hL : P.card = ∑ a ∈ A, ∑ a' ∈ A, path2 Gph a a' := by
    let g : (G × G) × (G × G) → G × G := fun pair => (pair.1.1, pair.2.1)
    let t := A ×ˢ A
    have h_maps : (P : Set ((G × G) × (G × G))).MapsTo g t := by
      intro pair hp
      have h4 : pair.1 ∈ Gph := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      have h5 : pair.2 ∈ Gph := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
      have h6 : pair.1 ∈ A ×ˢ B := hG h4
      have h7 : pair.2 ∈ A ×ˢ B := hG h5
      exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp h6).1, (Finset.mem_product.mp h7).1⟩
    have h : P.card = ∑ aa' ∈ t, (P.filter (fun pair => g pair = aa')).card :=
      Finset.card_eq_sum_card_fiberwise (H := h_maps)
    rw [h, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro a' _
    let Qb : Finset G :=
      ((Gph.filter (fun p : G × G => p.1 = a)).image Prod.snd) ∩
      ((Gph.filter (fun p : G × G => p.1 = a')).image Prod.snd)
    have hQb : Qb.card = path2 Gph a a' := by rfl
    let e : ((G × G) × (G × G)) → G := fun pair => pair.1.2
    let F : Finset ((G × G) × (G × G)) := P.filter (fun pair => g pair = (a, a'))
    have h_inj : Set.InjOn e (F : Set ((G × G) × (G × G))) := by
      rintro ⟨p1, p2⟩ hpF ⟨q1, q2⟩ hqF h_eq
      have hpf1 : (p1, p2) ∈ P := (Finset.mem_filter.mp hpF).1
      have hpf2 : g (p1, p2) = (a, a') := (Finset.mem_filter.mp hpF).2
      have hqf1 : (q1, q2) ∈ P := (Finset.mem_filter.mp hqF).1
      have hqf2 : g (q1, q2) = (a, a') := (Finset.mem_filter.mp hqF).2
      have hP_p : (p1, p2) ∈ Gph.product Gph := (Finset.mem_filter.mp hpf1).1
      have hPp2 : p1.2 = p2.2 := (Finset.mem_filter.mp hpf1).2
      have hP_q : (q1, q2) ∈ Gph.product Gph := (Finset.mem_filter.mp hqf1).1
      have hPq2 : q1.2 = q2.2 := (Finset.mem_filter.mp hqf1).2
      have h_p11 : p1.1 = a := by
        have h : (p1.1, p2.1) = (a, a') := hpf2
        exact Prod.ext_iff.mp h |>.1
      have h_p21 : p2.1 = a' := by
        have h : (p1.1, p2.1) = (a, a') := hpf2
        exact Prod.ext_iff.mp h |>.2
      have h_q11 : q1.1 = a := by
        have h : (q1.1, q2.1) = (a, a') := hqf2
        exact Prod.ext_iff.mp h |>.1
      have h_q21 : q2.1 = a' := by
        have h : (q1.1, q2.1) = (a, a') := hqf2
        exact Prod.ext_iff.mp h |>.2
      have h_p12_eq_q12 : p1.2 = q1.2 := h_eq
      have h_p22 : p2.2 = q2.2 := by
        rw [← hPp2, h_p12_eq_q12, hPq2]
      have h_p1 : p1 = q1 := by
        ext <;> simp [h_p11, h_q11, h_p12_eq_q12] <;> tauto
      have h_p2 : p2 = q2 := by
        ext <;> simp [h_p21, h_q21, h_p22] <;> tauto
      exact Prod.ext h_p1 h_p2
    have h_img : F.image e = Qb := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨pair, hF, rfl⟩
        have hP : pair ∈ P := (Finset.mem_filter.mp hF).1
        have hg : g pair = (a, a') := (Finset.mem_filter.mp hF).2
        have hP_prod : pair.1 ∈ Gph ∧ pair.2 ∈ Gph :=
          Finset.mem_product.mp (Finset.mem_filter.mp hP).1
        have hP3 : pair.1.2 = pair.2.2 := (Finset.mem_filter.mp hP).2
        have h4 : pair.1.1 = a := (Prod.ext_iff.mp hg).1
        have h5 : pair.2.1 = a' := (Prod.ext_iff.mp hg).2
        have h6 : pair.1 ∈ Gph.filter (fun p : G × G => p.1 = a) :=
          Finset.mem_filter.mpr ⟨hP_prod.1, h4⟩
        have h7 : pair.2 ∈ Gph.filter (fun p : G × G => p.1 = a') :=
          Finset.mem_filter.mpr ⟨hP_prod.2, h5⟩
        have h8 : pair.1.2 ∈ (Gph.filter (fun p : G × G => p.1 = a)).image Prod.snd :=
          Finset.mem_image.mpr ⟨pair.1, h6, rfl⟩
        have h9 : pair.2.2 ∈ (Gph.filter (fun p : G × G => p.1 = a')).image Prod.snd :=
          Finset.mem_image.mpr ⟨pair.2, h7, rfl⟩
        have h10 : pair.2.2 = pair.1.2 := hP3.symm
        rw [h10] at h9
        exact Finset.mem_inter.mpr ⟨h8, h9⟩
      · intro hx
        have h8 : x ∈ (Gph.filter (fun p : G × G => p.1 = a)).image Prod.snd :=
          (Finset.mem_inter.mp hx).1
        have h9 : x ∈ (Gph.filter (fun p : G × G => p.1 = a')).image Prod.snd :=
          (Finset.mem_inter.mp hx).2
        rcases Finset.mem_image.mp h8 with ⟨p1, hp1, hx1⟩
        rcases Finset.mem_image.mp h9 with ⟨p2, hp2, hx2⟩
        have h_x : x = p1.2 := hx1.symm
        have h_eq2 : p2.2 = p1.2 := by
          rw [h_x] at hx2
          exact hx2
        have hp1' : p1 ∈ Gph ∧ p1.1 = a := Finset.mem_filter.mp hp1
        have hp2' : p2 ∈ Gph ∧ p2.1 = a' := Finset.mem_filter.mp hp2
        have hP : (p1, p2) ∈ P := by
          have h10 : (p1, p2) ∈ Gph.product Gph :=
            Finset.mem_product.mpr ⟨hp1'.1, hp2'.1⟩
          exact Finset.mem_filter.mpr ⟨h10, h_eq2.symm⟩
        have hg : g (p1, p2) = (a, a') := by
          simp [g, hp1'.2, hp2'.2]
          <;> aesop
        have hF : (p1, p2) ∈ F := Finset.mem_filter.mpr ⟨hP, hg⟩
        exact Finset.mem_image.mpr ⟨(p1, p2), hF, h_x.symm⟩
    have h_eq : F.card = Qb.card := by
      rw [← Finset.card_image_of_injOn h_inj, h_img]
    rw [h_eq, hQb]
  rw [← hL, hR]

/-- Total length-2 paths ≥ `|Gph|² / |B|` by Cauchy-Schwarz. -/
theorem total_path2_ge (hG : Gph ⊆ A ×ˢ B) (hB : B.Nonempty) :
    Gph.card ^ 2 ≤ B.card * ∑ a ∈ A, ∑ a' ∈ A, path2 Gph a a' := by
  have h1 : ∑ b ∈ B, degRight Gph b = Gph.card := sum_degRight_eq_card hG
  have h2 : (∑ b ∈ B, degRight Gph b)^2 ≤
      B.card * ∑ b ∈ B, (degRight Gph b)^2 := by
    have h3 := Finset.sum_mul_sq_le_sq_mul_sq B (fun _ => (1 : ℕ)) (degRight Gph)
    simpa using h3
  have h4 : ∑ a ∈ A, ∑ a' ∈ A, path2 Gph a a' =
      ∑ b ∈ B, (degRight Gph b)^2 := total_path2_eq_sum_deg_sq hG
  rw [h4]
  rw [h1] at h2
  exact h2

end PathCounting

section PathToSumset

variable {G : Type*} [AddCommGroup G] [DecidableEq G]
  {A B A' B' : Finset G} {Gph : Finset (G × G)}

/-- Auxiliary choice function for sumset representations. -/
noncomputable def pickRep (A' B' : Finset G) (s : G) : G × G :=
  if hs : s ∈ A' + B' then
    Classical.choose (show ∃ (p : G × G), p.1 ∈ A' ∧ p.2 ∈ B' ∧ p.1 + p.2 = s from by
      have h_sum : ∃ (x : G), x ∈ A' ∧ ∃ (y : G), y ∈ B' ∧ x + y = s := by exact Finset.mem_image₂.mp hs
      rcases h_sum with ⟨x, hx, y, hy, hxy⟩
      exact ⟨(x, y), hx, hy, hxy⟩)
  else (0, 0)

lemma pickRep_spec (A' B' : Finset G) {s : G} (hs : s ∈ A' + B') :
    (pickRep A' B' s).1 ∈ A' ∧
    (pickRep A' B' s).2 ∈ B' ∧
    (pickRep A' B' s).1 + (pickRep A' B' s).2 = s := by
  have h_exists : ∃ (p : G × G), p.1 ∈ A' ∧ p.2 ∈ B' ∧ p.1 + p.2 = s := by
    have h_sum : ∃ (x : G), x ∈ A' ∧ ∃ (y : G), y ∈ B' ∧ x + y = s := by exact Finset.mem_image₂.mp hs
    rcases h_sum with ⟨x, hx, y, hy, hxy⟩
    exact ⟨(x, y), hx, hy, hxy⟩
  have h_eq : pickRep A' B' s = Classical.choose h_exists := by
    rw [pickRep, dif_pos hs]
  rw [h_eq]
  exact Classical.choose_spec h_exists

/-- **Path-to-sumset lemma.** If every pair `(a,b) ∈ A' × B'` has at least `p`
length-3 paths in `Gph`, then `|A' + B'| ≤ |S|³ / p`. -/
theorem path_to_sumset_bound
    (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    (S : Finset G) (hS : S = restrictedSum A B Gph)
    (p : ℕ) (hp_pos : 0 < p)
    (h_paths : ∀ a ∈ A', ∀ b ∈ B', p ≤ path3 Gph a b) :
    p * (A' + B').card ≤ S.card ^ 3 := by
  classical
  let H := restrictedSum A B Gph
  let S_sum : Finset G := A' + B'
  let a_fun : G → G := fun s => (pickRep A' B' s).1
  let b_fun : G → G := fun s => (pickRep A' B' s).2
  have h_a : ∀ s ∈ S_sum, a_fun s ∈ A' := by
    intro s hs; exact (pickRep_spec A' B' hs).1
  have h_b : ∀ s ∈ S_sum, b_fun s ∈ B' := by
    intro s hs; exact (pickRep_spec A' B' hs).2.1
  have h_ab : ∀ s ∈ S_sum, a_fun s + b_fun s = s := by
    intro s hs; exact (pickRep_spec A' B' hs).2.2
  let f (s : G) : G × G → G × G × G :=
    fun (b₁, a₁) => (a_fun s + b₁, a₁ + b₁, a₁ + b_fun s)
  let S_img (s : G) : Finset (G × G × G) :=
    (path3Set Gph (a_fun s) (b_fun s)).image (f s)
  have hS' : S = H := hS
  -- S_img s ⊆ H × H × H for s ∈ S_sum
  have h1 : ∀ s ∈ S_sum, S_img s ⊆ H ×ˢ H ×ˢ H := by
    intro s hs z hz
    rcases Finset.mem_image.mp hz with ⟨⟨b₁, a₁⟩, hpath, rfl⟩
    have h_edges : (a_fun s, b₁) ∈ Gph ∧ (a₁, b₁) ∈ Gph ∧ (a₁, b_fun s) ∈ Gph :=
      (mem_path3Set_iff Gph (a_fun s) (b_fun s) b₁ a₁).mp hpath
    have hz1 : a_fun s + b₁ ∈ H := by
      apply Finset.mem_image.mpr; exact ⟨(a_fun s, b₁), h_edges.1, rfl⟩
    have hz2 : a₁ + b₁ ∈ H := by
      apply Finset.mem_image.mpr; exact ⟨(a₁, b₁), h_edges.2.1, rfl⟩
    have hz3 : a₁ + b_fun s ∈ H := by
      apply Finset.mem_image.mpr; exact ⟨(a₁, b_fun s), h_edges.2.2, rfl⟩
    exact Finset.mem_product.mpr ⟨hz1, Finset.mem_product.mpr ⟨hz2, hz3⟩⟩
  -- f s is injective on path3Set
  have h_inj : ∀ s ∈ S_sum, Set.InjOn (f s) (path3Set Gph (a_fun s) (b_fun s)) := by
    intro s hs ⟨b₁, a₁⟩ _ ⟨b₁', a₁'⟩ _ h
    have h_eq : (a_fun s + b₁, a₁ + b₁, a₁ + b_fun s) =
                   (a_fun s + b₁', a₁' + b₁', a₁' + b_fun s) := h
    have hb1 : b₁ = b₁' := by
      have : a_fun s + b₁ = a_fun s + b₁' := by
        exact congr_arg (fun (t : G × G × G) => t.1) h_eq
      exact add_left_cancel this
    have ha1 : a₁ = a₁' := by
      have : a₁ + b_fun s = a₁' + b_fun s := by
        exact congr_arg (fun (t : G × G × G) => t.2.2) h_eq
      exact add_right_cancel this
    exact Prod.ext hb1 ha1
  -- Images are pairwise disjoint for different s
  have h_disj : ∀ s1 ∈ S_sum, ∀ s2 ∈ S_sum, s1 ≠ s2 → Disjoint (S_img s1) (S_img s2) := by
    intro s1 hs1 s2 hs2 hne
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    rcases Finset.mem_image.mp hz1 with ⟨⟨b₁, a₁⟩, _, h_eq1⟩
    rcases Finset.mem_image.mp hz2 with ⟨⟨b₁', a₁'⟩, _, h_eq2⟩
    have h_z1 : z.1 - z.2.1 + z.2.2 = s1 := by
      have h : z = f s1 (b₁, a₁) := h_eq1.symm
      rw [h]
      dsimp only [f]
      have h_sum : a_fun s1 + b₁ - (a₁ + b₁) + (a₁ + b_fun s1) = a_fun s1 + b_fun s1 := by abel
      rw [h_sum, h_ab s1 hs1]
    have h_z2 : z.1 - z.2.1 + z.2.2 = s2 := by
      have h : z = f s2 (b₁', a₁') := h_eq2.symm
      rw [h]
      dsimp only [f]
      have h_sum : a_fun s2 + b₁' - (a₁' + b₁') + (a₁' + b_fun s2) = a_fun s2 + b_fun s2 := by abel
      rw [h_sum, h_ab s2 hs2]
    have h_eq : s1 = s2 := by
      rw [← h_z1, h_z2]
    exact hne h_eq
  -- Card of each image
  have h_card_image : ∀ s ∈ S_sum, (S_img s).card = path3 Gph (a_fun s) (b_fun s) := by
    intro s hs
    exact Finset.card_image_of_injOn (h_inj s hs)
  have h_ge : ∀ s ∈ S_sum, (S_img s).card ≥ p := by
    intro s hs
    rw [h_card_image s hs]
    exact h_paths (a_fun s) (h_a s hs) (b_fun s) (h_b s hs)
  -- Pairwise disjoint union
  have h_union_card : (S_sum.biUnion S_img).card = ∑ s ∈ S_sum, (S_img s).card := by
    rw [Finset.card_biUnion h_disj]
  have h_union_subset : S_sum.biUnion S_img ⊆ H ×ˢ H ×ˢ H := by
    rw [Finset.biUnion_subset]
    exact h1
  have h_main : S_sum.card * p ≤ (H ×ˢ H ×ˢ H).card := by
    calc
      S_sum.card * p
        = ∑ _s ∈ S_sum, p := by simp [mul_comm]
      _ ≤ ∑ s ∈ S_sum, (S_img s).card := by
          gcongr with s hs
          exact h_ge s hs
      _ = (S_sum.biUnion S_img).card := h_union_card.symm
      _ ≤ (H ×ˢ H ×ˢ H).card := Finset.card_le_card h_union_subset
  have hH3 : (H ×ˢ H ×ˢ H).card = H.card ^ 3 := by
    simp [Finset.card_product, pow_succ] <;> ring
  rw [hH3] at h_main
  have h_comm : S_sum.card * p = p * S_sum.card := by ring
  rw [h_comm] at h_main
  simpa [hS', S_sum] using h_main

end PathToSumset

section BSGHelpers

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- `∑_a d_A(a) = |Gph|`. -/
lemma sum_degLeft_eq_card {A B : Finset G} {Gph : Finset (G × G)}
    (hG : Gph ⊆ A ×ˢ B) :
    ∑ a ∈ A, degLeft Gph a = Gph.card := by
  let f : G × G → G := fun p => p.1
  have h_maps : (Gph : Set (G × G)).MapsTo f A := by
    intro p hp
    have h4 : p ∈ A ×ˢ B := hG hp
    exact (Finset.mem_product.mp h4).1
  have h : Gph.card = ∑ a ∈ A, (Gph.filter (fun p => f p = a)).card :=
    Finset.card_eq_sum_card_fiberwise (H := h_maps)
  exact Eq.symm h

/-- `degLeft Gph a ≤ |B|`. -/
lemma degLeft_le_card_B {A B : Finset G} {Gph : Finset (G × G)}
    (hG : Gph ⊆ A ×ˢ B) (a : G) : degLeft Gph a ≤ B.card := by
  let F : Finset (G × G) := Gph.filter (fun p => p.1 = a)
  have h1 : F.image Prod.snd ⊆ B := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨p, hp, rfl⟩
    have h2 : p ∈ Gph := (Finset.mem_filter.mp hp).1
    have h3 : p ∈ A ×ˢ B := hG h2
    exact (Finset.mem_product.mp h3).2
  have h_inj : Set.InjOn Prod.snd (F : Set (G × G)) := by
    intro p1 hp1 p2 hp2 h
    have h11 : p1.1 = a := (Finset.mem_filter.mp hp1).2
    have h21 : p2.1 = a := (Finset.mem_filter.mp hp2).2
    have h_eq1 : p1.1 = p2.1 := by rw [h11, h21]
    exact Prod.ext h_eq1 h
  have h3 : F.card = (F.image Prod.snd).card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h4 : (F.image Prod.snd).card ≤ B.card := Finset.card_le_card h1
  have h5 : degLeft Gph a = F.card := by rfl
  rw [h5, h3]
  exact h4

/-- Degree pruning: find `A₁ ⊆ A` with `|A₁| ≥ |A|/(2K)` and
`degLeft(a) ≥ |B|/(2K)` for all `a ∈ A₁`. -/
lemma degree_prune_left (A B : Finset G) (Gph : Finset (G × G))
    (hG : Gph ⊆ A ×ˢ B) (K : ℕ) (hK : 1 ≤ K)
    (h_density : (A.card : ℝ) * (B.card : ℝ) ≤ (K : ℝ) * (Gph.card : ℝ)) :
    ∃ (A₁ : Finset G), A₁ ⊆ A ∧
      (A₁.card : ℝ) ≥ (A.card : ℝ) / (2 * (K : ℝ)) ∧
      ∀ a ∈ A₁, (degLeft Gph a : ℝ) ≥ (B.card : ℝ) / (2 * (K : ℝ)) := by
  let threshold : ℝ := (B.card : ℝ) / (2 * (K : ℝ))
  let A₁ : Finset G := A.filter (fun a => (degLeft Gph a : ℝ) ≥ threshold)
  let f : G → ℝ := fun a => (degLeft Gph a : ℝ)
  have hA₁_sub : A₁ ⊆ A := Finset.filter_subset _ _
  have h_sum : ∑ a ∈ A, f a = (Gph.card : ℝ) := by
    have h : ∑ a ∈ A, (degLeft Gph a : ℝ) = (Gph.card : ℝ) := by
      exact_mod_cast sum_degLeft_eq_card hG
    exact h
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hG_lower : (Gph.card : ℝ) ≥ (A.card : ℝ) * (B.card : ℝ) / (K : ℝ) := by
    have h : (A.card : ℝ) * (B.card : ℝ) ≤ (K : ℝ) * (Gph.card : ℝ) := h_density
    have hK_ne : (K : ℝ) ≠ 0 := hK_pos.ne'
    have h' : (A.card : ℝ) * (B.card : ℝ) / (K : ℝ) ≤ ((K : ℝ) * (Gph.card : ℝ)) / (K : ℝ) := by
      gcongr
    have h'' : ((K : ℝ) * (Gph.card : ℝ)) / (K : ℝ) = (Gph.card : ℝ) := by
      field_simp [hK_ne] <;> ring
    rw [h''] at h'
    exact h'
  have h3 : ∀ a ∈ A \ A₁, f a < threshold := by
    intro a ha
    have h4 : a ∈ A := (Finset.mem_sdiff.mp ha).1
    have h5 : a ∉ A₁ := (Finset.mem_sdiff.mp ha).2
    by_cases h6 : f a ≥ threshold
    · have h7 : a ∈ A₁ := by
        simp only [A₁, Finset.mem_filter]; exact ⟨h4, h6⟩
      exact False.elim (h5 h7)
    · exact not_le.mp h6
  have h4 : ∀ a ∈ A \ A₁, f a ≤ threshold := by
    intro a ha; exact le_of_lt (h3 a ha)
  have h_sum_out : ∑ a ∈ A \ A₁, f a ≤ (A.card : ℝ) * threshold := by
    have h_step1 : ∑ a ∈ A \ A₁, f a ≤ ∑ a ∈ A \ A₁, threshold :=
      Finset.sum_le_sum (fun a ha => h4 a ha)
    have h_step2 : ∑ a ∈ A \ A₁, threshold = ((A \ A₁).card : ℝ) * threshold := by
      simp [Finset.sum_const] <;> ring
    have h_step3 : ((A \ A₁).card : ℝ) ≤ (A.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (show (A \ A₁) ⊆ A from by simp)
    calc ∑ a ∈ A \ A₁, f a
      ≤ ∑ a ∈ A \ A₁, threshold := h_step1
    _ = ((A \ A₁).card : ℝ) * threshold := h_step2
    _ ≤ (A.card : ℝ) * threshold := by
      have h : ((A \ A₁).card : ℝ) * threshold ≤ (A.card : ℝ) * threshold := by
        exact mul_le_mul_of_nonneg_right h_step3 (by positivity)
      exact h
  have h_sum_split : ∑ a ∈ A, f a = ∑ a ∈ A₁, f a + ∑ a ∈ (A \ A₁), f a := by
    have h : ∑ a ∈ (A \ A₁), f a + ∑ a ∈ A₁, f a = ∑ a ∈ A, f a := Finset.sum_sdiff hA₁_sub
    simpa [add_comm] using h.symm
  have h_sum_A₁ : ∑ a ∈ A₁, f a ≥ (A.card : ℝ) * threshold := by
    rw [h_sum_split] at h_sum
    have hth : threshold = (B.card : ℝ) / (2 * (K : ℝ)) := by rfl
    have h1 : (Gph.card : ℝ) ≥ (A.card : ℝ) * (B.card : ℝ) / (K : ℝ) := hG_lower
    have h2 : ∑ a ∈ (A \ A₁), f a ≤ (A.card : ℝ) * threshold := h_sum_out
    have h_eq1 : (A.card : ℝ) * (B.card : ℝ) / (K : ℝ) = (A.card : ℝ) * ((B.card : ℝ) / (K : ℝ)) := by ring
    have h_goal : (Gph.card : ℝ) - ∑ a ∈ (A \ A₁), f a ≥ (A.card : ℝ) * threshold := by
      have h_a : (Gph.card : ℝ) ≥ (A.card : ℝ) * ((B.card : ℝ) / (K : ℝ)) := by
        rw [h_eq1] at h1; exact h1
      have h_b : ∑ a ∈ (A \ A₁), f a ≤ (A.card : ℝ) * ((B.card : ℝ) / (2 * (K : ℝ))) := by
        have hth' : threshold = (B.card : ℝ) / (2 * (K : ℝ)) := by rfl
        rw [hth'] at h2; exact h2
      have h_c : (A.card : ℝ) * ((B.card : ℝ) / (K : ℝ)) - (A.card : ℝ) * ((B.card : ℝ) / (2 * (K : ℝ))) =
          (A.card : ℝ) * threshold := by
        have hth' : threshold = (B.card : ℝ) / (2 * (K : ℝ)) := by rfl
        rw [hth'] <;> ring
      linarith [h_a, h_b, h_c]
    have h_eq : ∑ a ∈ A₁, f a = (Gph.card : ℝ) - ∑ a ∈ (A \ A₁), f a := by linarith
    rw [h_eq]
    exact h_goal
  have h_bound : ∀ a ∈ A₁, f a ≤ (B.card : ℝ) := by
    intro a ha
    have h : (degLeft Gph a : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast degLeft_le_card_B hG a
    simpa [f] using h
  have h7 : ∑ a ∈ A₁, f a ≤ (A₁.card : ℝ) * (B.card : ℝ) := by
    have h_step1 : ∑ a ∈ A₁, f a ≤ ∑ a ∈ A₁, (B.card : ℝ) :=
      Finset.sum_le_sum (fun a ha => h_bound a ha)
    calc ∑ a ∈ A₁, f a
      ≤ ∑ a ∈ A₁, (B.card : ℝ) := h_step1
    _ = (A₁.card : ℝ) * (B.card : ℝ) := by simp [Finset.sum_const] <;> ring
  have h_card : (A₁.card : ℝ) ≥ (A.card : ℝ) / (2 * (K : ℝ)) := by
    by_cases hB : B.card = 0
    · have hB0 : (B.card : ℝ) = 0 := by exact_mod_cast hB
      have hth0 : threshold = 0 := by
        dsimp only [threshold]; rw [hB0] <;> ring
      have hA1_eq_A : A₁ = A := by
        ext a
        simp only [A₁, Finset.mem_filter, hth0]
        <;> aesop
      rw [hA1_eq_A]
      have h15 : (1 : ℝ) ≤ (2 * (K : ℝ)) := by
        have h16 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
        linarith
      have h19 : 0 ≤ (A.card : ℝ) := Nat.cast_nonneg A.card
      have h17 : (A.card : ℝ) / (2 * (K : ℝ)) ≤ (A.card : ℝ) :=
        div_le_self h19 h15
      exact h17
    · have hB_pos : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hB)
      have h9 : (A₁.card : ℝ) * (B.card : ℝ) ≥ (A.card : ℝ) * threshold := by
        linarith [h_sum_A₁, h7]
      have h10 : threshold = (B.card : ℝ) / (2 * (K : ℝ)) := by rfl
      rw [h10] at h9
      have hB_ne : (B.card : ℝ) ≠ 0 := hB_pos.ne'
      have h13 : (A₁.card : ℝ) * (B.card : ℝ) ≥
          (A.card : ℝ) * ((B.card : ℝ) / (2 * (K : ℝ))) := h9
      have h14 : (A₁.card : ℝ) ≥
          ((A.card : ℝ) * ((B.card : ℝ) / (2 * (K : ℝ)))) / (B.card : ℝ) := by
        have h15 : (A₁.card : ℝ) * (B.card : ℝ) / (B.card : ℝ) = (A₁.card : ℝ) := by
          field_simp [hB_ne] <;> ring
        calc (A₁.card : ℝ)
          = (A₁.card : ℝ) * (B.card : ℝ) / (B.card : ℝ) := h15.symm
        _ ≥ ((A.card : ℝ) * ((B.card : ℝ) / (2 * (K : ℝ)))) / (B.card : ℝ) := by gcongr
      have h16 : ((A.card : ℝ) * ((B.card : ℝ) / (2 * (K : ℝ)))) / (B.card : ℝ) =
          (A.card : ℝ) / (2 * (K : ℝ)) := by
        field_simp [hB_ne, hK_pos.ne'] <;> ring
      rw [h16] at h14
      exact h14
  exact ⟨A₁, hA₁_sub, h_card, fun a ha => by
    simp only [A₁, Finset.mem_filter] at ha
    exact ha.2⟩

/-- `p₃(a,b) = ∑_{a₁ ∈ N(b)} p₂(a,a₁)`. -/
lemma path3_eq_sum (Gph : Finset (G × G)) (a b : G) :
    path3 Gph a b =
    ∑ a₁ ∈ (Gph.filter (fun p => p.2 = b)).image Prod.fst, path2 Gph a a₁ := by
  let N_b := (Gph.filter (fun p => p.2 = b)).image Prod.fst
  let P := path3Set Gph a b
  have h_maps : (P : Set (G × G)).MapsTo Prod.snd N_b := by
    intro p hp
    have h := (mem_path3Set_iff Gph a b p.1 p.2).mp hp
    exact Finset.mem_image.mpr ⟨(p.2, b), Finset.mem_filter.mpr ⟨h.2.2, rfl⟩, rfl⟩
  have h1 : P.card = ∑ a₁ ∈ N_b, (P.filter (fun p => p.2 = a₁)).card :=
    Finset.card_eq_sum_card_fiberwise (H := h_maps)
  rw [path3, h1]
  apply Finset.sum_congr rfl
  intro a₁ ha₁
  let F := P.filter (fun p : G × G => p.2 = a₁)
  let N_a := (Gph.filter (fun p => p.1 = a)).image Prod.snd
  let N_a1 := (Gph.filter (fun p => p.1 = a₁)).image Prod.snd
  have hF : F.image Prod.fst = N_a ∩ N_a1 := by
    ext b₁
    constructor
    · intro h
      rcases Finset.mem_image.mp h with ⟨p, hp, rfl⟩
      have hP : p ∈ P := (Finset.mem_filter.mp hp).1
      have hp2 : p.2 = a₁ := (Finset.mem_filter.mp hp).2
      have hP' : (p.1, a₁) ∈ P := by
        have h_eq : p = (p.1, a₁) := by
          ext <;> simp [hp2] <;> tauto
        rw [h_eq] at hP; exact hP
      have h := (mem_path3Set_iff Gph a b p.1 a₁).mp hP'
      have h1 : p.1 ∈ N_a := Finset.mem_image.mpr ⟨(a, p.1), Finset.mem_filter.mpr ⟨h.1, rfl⟩, rfl⟩
      have h2 : p.1 ∈ N_a1 := Finset.mem_image.mpr ⟨(a₁, p.1), Finset.mem_filter.mpr ⟨h.2.1, rfl⟩, rfl⟩
      exact Finset.mem_inter.mpr ⟨h1, h2⟩
    · intro h
      have h5 : b₁ ∈ N_a := (Finset.mem_inter.mp h).1
      have h6 : b₁ ∈ N_a1 := (Finset.mem_inter.mp h).2
      rcases Finset.mem_image.mp h5 with ⟨p, hp, hpb⟩
      rcases Finset.mem_image.mp h6 with ⟨q, hq, hqb⟩
      have hp1 : p.1 = a := (Finset.mem_filter.mp hp).2
      have hpG : p ∈ Gph := (Finset.mem_filter.mp hp).1
      have hq1 : q.1 = a₁ := (Finset.mem_filter.mp hq).2
      have hqG : q ∈ Gph := (Finset.mem_filter.mp hq).1
      have hpb' : p.2 = b₁ := hpb
      have hqb' : q.2 = b₁ := hqb
      have h9 : (a, b₁) ∈ Gph := by
        have h : p = (a, b₁) := by ext <;> simp [hp1, hpb'] <;> tauto
        rw [h] at hpG; exact hpG
      have h10 : (a₁, b₁) ∈ Gph := by
        have h : q = (a₁, b₁) := by ext <;> simp [hq1, hqb'] <;> tauto
        rw [h] at hqG; exact hqG
      have h11 : (a₁, b) ∈ Gph := by
        rcases Finset.mem_image.mp ha₁ with ⟨r, hr, hr1⟩
        have h13 : r.1 = a₁ := hr1
        have h12 : r.2 = b := (Finset.mem_filter.mp hr).2
        have h14 : r ∈ Gph := (Finset.mem_filter.mp hr).1
        have h15 : r = (a₁, b) := by
          ext
          · exact h13
          · exact h12
        rw [h15] at h14; exact h14
      have h14 : (b₁, a₁) ∈ P := (mem_path3Set_iff Gph a b b₁ a₁).mpr ⟨h9, h10, h11⟩
      have h15 : (b₁, a₁) ∈ F := Finset.mem_filter.mpr ⟨h14, rfl⟩
      exact Finset.mem_image.mpr ⟨(b₁, a₁), h15, rfl⟩
  have h_inj : Set.InjOn Prod.fst (F : Set (G × G)) := by
    intro p hp q hq h
    have h1 : p.2 = a₁ := (Finset.mem_filter.mp hp).2
    have h2 : q.2 = a₁ := (Finset.mem_filter.mp hq).2
    exact Prod.ext h (by rw [h1, h2])
  have h3 : F.card = (F.image Prod.fst).card :=
    Eq.symm (Finset.card_image_of_injOn h_inj)
  rw [h3, hF]
  <;> rfl

end BSGHelpers

section Pruning

variable {G : Type*} [AddCommGroup G] [DecidableEq G]
variable {A B : Finset G} {Gph : Finset (G × G)} {K : ℕ}

/-- Prune B-vertices with degree * 2K < |A|. Returns the pruned graph. -/
def prunedGraph (A B : Finset G) (Gph : Finset (G × G)) (K : ℕ) : Finset (G × G) :=
  Gph.filter (fun p => A.card ≤ (neighRight Gph p.2).card * (2 * K))

lemma prunedGraph_subset : prunedGraph A B Gph K ⊆ Gph :=
  Finset.filter_subset _ _

/-- If p is removed, then deg(p.2) * 2K < |A|. -/
private lemma removed_edge_bad {p : G × G} (hp : p ∈ Gph \ prunedGraph A B Gph K) :
    (neighRight Gph p.2).card * (2 * K) < A.card := by
  have h1 : p ∈ Gph := (Finset.mem_sdiff.mp hp).1
  have h2 : p ∉ prunedGraph A B Gph K := (Finset.mem_sdiff.mp hp).2
  have h3 : ¬(p ∈ Gph ∧ A.card ≤ (neighRight Gph p.2).card * (2 * K)) := by
    simpa [prunedGraph, Finset.mem_filter] using h2
  have h4 : ¬(A.card ≤ (neighRight Gph p.2).card * (2 * K)) := by
    intro h5
    exact h3 ⟨h1, h5⟩
  exact Nat.lt_of_not_ge h4

/-- Edges removed by pruning are ≤ |A||B|/(2K). -/
lemma pruned_removed_bound (hG : Gph ⊆ A ×ˢ B) (hK : 1 ≤ K)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ((Gph \ prunedGraph A B Gph K).card : ℝ) ≤
      (A.card : ℝ) * (B.card : ℝ) / (2 * (K : ℝ)) := by
  set removed : Finset (G × G) := Gph \ prunedGraph A B Gph K with hremoved
  set removedB : Finset G := removed.image Prod.snd with hremovedB
  have hB_sub : removedB ⊆ B := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨p, hp, rfl⟩
    have h6 : p ∈ Gph := (Finset.mem_sdiff.mp hp).1
    exact (Finset.mem_product.mp (hG h6)).2
  -- For b ∈ removedB, every Gph-edge with endpoint b is in removed
  have h_fiber_eq : ∀ b ∈ removedB,
      removed.filter (fun p : G × G => p.2 = b) = Gph.filter (fun p : G × G => p.2 = b) := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨q, hq, hq2⟩
    have hb_eq : b = q.2 := hq2.symm
    have hbad : (neighRight Gph b).card * (2 * K) < A.card := by
      rw [hb_eq]
      exact removed_edge_bad hq
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hpin, hpeq⟩
      have hpinG : p ∈ Gph := (Finset.mem_sdiff.mp hpin).1
      exact ⟨hpinG, hpeq⟩
    · rintro ⟨hpin, hpeq⟩
      have h4 : (neighRight Gph p.2).card * (2 * K) < A.card := by
        have h5 : p.2 = b := hpeq
        rw [h5]
        exact hbad
      have h6 : p ∉ prunedGraph A B Gph K := by
        intro h7
        have h8 : A.card ≤ (neighRight Gph p.2).card * (2 * K) := by
          simp only [prunedGraph, Finset.mem_filter] at h7
          exact h7.2
        exact not_le.mpr h4 h8
      have h9 : p ∈ removed := by
        simp only [hremoved, Finset.mem_sdiff] <;> exact ⟨hpin, h6⟩
      exact ⟨h9, hpeq⟩
  -- removed.card = ∑_{b ∈ removedB} deg(b)
  let f : G × G → G := Prod.snd
  have h_maps : (removed : Set (G × G)).MapsTo f removedB := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have h_card : removed.card = ∑ b ∈ removedB, (removed.filter (fun p => p.2 = b)).card :=
    Finset.card_eq_sum_card_fiberwise (H := h_maps)
  have h_deg_eq : ∀ b ∈ removedB, (removed.filter (fun p => p.2 = b)).card =
      (neighRight Gph b).card := by
    intro b hb
    rw [h_fiber_eq b hb]
    have h_inj : Set.InjOn Prod.fst (Gph.filter (fun p : G × G => p.2 = b) : Set (G × G)) := by
      intro p hp q hq h
      have hpf : p.2 = b := (Finset.mem_filter.mp hp).2
      have hqf : q.2 = b := (Finset.mem_filter.mp hq).2
      have h2 : p.2 = q.2 := by rw [hpf, hqf]
      exact Prod.ext h h2
    simpa [neighRight, Finset.card_image_of_injOn h_inj] using rfl
  have h_card_nat : removed.card = ∑ b ∈ removedB, (neighRight Gph b).card := by
    calc
      removed.card
        = ∑ b ∈ removedB, (removed.filter (fun p => p.2 = b)).card := h_card
      _ = ∑ b ∈ removedB, (neighRight Gph b).card := by
        apply Finset.sum_congr rfl
        intro b hb
        exact h_deg_eq b hb
  have h_main1 : (removed.card : ℝ) = ∑ b ∈ removedB, ((neighRight Gph b).card : ℝ) := by
    rw [h_card_nat]
    rw [Nat.cast_sum]
  rw [h_main1]
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K from by omega)
  have h2Kpos : (0 : ℝ) < 2 * (K : ℝ) := by positivity
  have h5 : ∀ b ∈ removedB, ((neighRight Gph b).card : ℝ) ≤
      (A.card : ℝ) / (2 * (K : ℝ)) := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨q, hq, rfl⟩
    have hbad : (neighRight Gph q.2).card * (2 * K) < A.card := removed_edge_bad hq
    have hbad' : ((neighRight Gph q.2).card : ℝ) * (2 * (K : ℝ)) ≤ (A.card : ℝ) := by
      exact_mod_cast hbad.le
    have hdiv : ((neighRight Gph q.2).card : ℝ) ≤ (A.card : ℝ) / (2 * (K : ℝ)) := by
      calc
        ((neighRight Gph q.2).card : ℝ)
          = (((neighRight Gph q.2).card : ℝ) * (2 * (K : ℝ))) / (2 * (K : ℝ)) := by
            field_simp [h2Kpos.ne'] <;> ring
        _ ≤ (A.card : ℝ) / (2 * (K : ℝ)) := by
            exact div_le_div_of_nonneg_right hbad' (by positivity)
    exact hdiv
  have h_sum_le : ∑ b ∈ removedB, ((neighRight Gph b).card : ℝ) ≤
      ∑ _b ∈ removedB, (A.card : ℝ) / (2 * (K : ℝ)) :=
    Finset.sum_le_sum (fun b hb => h5 b hb)
  calc
    ∑ b ∈ removedB, ((neighRight Gph b).card : ℝ)
      ≤ ∑ _b ∈ removedB, (A.card : ℝ) / (2 * (K : ℝ)) := h_sum_le
    _ = (removedB.card : ℝ) * ((A.card : ℝ) / (2 * (K : ℝ))) := by
        simp [Finset.sum_const] <;> ring
    _ ≤ (B.card : ℝ) * ((A.card : ℝ) / (2 * (K : ℝ))) := by
        have h9 : (removedB.card : ℝ) ≤ (B.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hB_sub
        have h10 : 0 ≤ (A.card : ℝ) / (2 * (K : ℝ)) := by positivity
        nlinarith
    _ = (A.card : ℝ) * (B.card : ℝ) / (2 * (K : ℝ)) := by ring

/-- The pruned graph has ≥ |A||B|/(2K) edges. -/
lemma prunedGraph_density (hG : Gph ⊆ A ×ˢ B) (hK : 1 ≤ K)
    (h_density : (A.card : ℝ) * (B.card : ℝ) ≤ (K : ℝ) * (Gph.card : ℝ))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ((prunedGraph A B Gph K).card : ℝ) ≥
      (A.card : ℝ) * (B.card : ℝ) / (2 * (K : ℝ)) := by
  set Gph' : Finset (G × G) := prunedGraph A B Gph K with hGph'
  set removed : Finset (G × G) := Gph \ Gph' with hremoved
  have h_card : (Gph'.card : ℝ) + (removed.card : ℝ) = (Gph.card : ℝ) := by
    have h_disj : Disjoint Gph' removed := Finset.disjoint_sdiff
    have h_union : Gph' ∪ removed = Gph := by
      rw [Finset.union_sdiff_of_subset prunedGraph_subset]
    have h : Gph'.card + removed.card = Gph.card := by
      rw [← Finset.card_union_of_disjoint h_disj, h_union]
    exact_mod_cast h
  have h_rem : (removed.card : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) / (2 * (K : ℝ)) :=
    pruned_removed_bound hG hK hA hB
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K from by omega)
  have h_den : (Gph.card : ℝ) ≥ (A.card : ℝ) * (B.card : ℝ) / (K : ℝ) := by
    have h : (K : ℝ) * (Gph.card : ℝ) ≥ (A.card : ℝ) * (B.card : ℝ) := h_density
    have h9 : (Gph.card : ℝ) ≥ ((A.card : ℝ) * (B.card : ℝ)) / (K : ℝ) := by
      calc
        (Gph.card : ℝ)
          = ((K : ℝ) * (Gph.card : ℝ)) / (K : ℝ) := by
            field_simp [hKpos.ne'] <;> ring
        _ ≥ ((A.card : ℝ) * (B.card : ℝ)) / (K : ℝ) := by gcongr
    exact h9
  have h14 : (A.card : ℝ) * (B.card : ℝ) / (K : ℝ) -
      (A.card : ℝ) * (B.card : ℝ) / (2 * (K : ℝ)) =
      (A.card : ℝ) * (B.card : ℝ) / (2 * (K : ℝ)) := by
    have h15 : (K : ℝ) ≠ 0 := hKpos.ne'
    field_simp [h15] <;> ring
  have h_goal : (Gph'.card : ℝ) ≥ (A.card : ℝ) * (B.card : ℝ) / (2 * (K : ℝ)) := by
    have h10 : (Gph'.card : ℝ) = (Gph.card : ℝ) - (removed.card : ℝ) := by linarith
    rw [h10]
    linarith [h_rem, h_den, h14]
  exact h_goal

/-- Every edge p in the pruned graph satisfies degRight(p.2) * 2K ≥ |A|. -/
lemma prunedGraph_minDegree {p : G × G} (hp : p ∈ prunedGraph A B Gph K) :
    A.card ≤ (neighRight Gph p.2).card * (2 * K) := by
  simp only [prunedGraph, Finset.mem_filter] at hp
  exact hp.2

end Pruning

section KeyLemma

variable {G : Type*} [AddCommGroup G] [DecidableEq G]
variable {A B : Finset G} {Gph' : Finset (G × G)} {K : ℕ}

/-- A pair (u,w) is "bad" if they have fewer than |A|/(128K³) common neighbors. -/
def isBadPair (Gph' : Finset (G × G)) (A : Finset G) (K : ℕ) (u w : G) : Prop :=
  (commonNeighRight Gph' u w : ℝ) < (A.card : ℝ) / (128 * (K : ℝ)^3)

/-- Sum of bad pairs over neighborhoods equals sum of common neighbors over bad pairs. -/
lemma sum_badPairs_swap {Gph' : Finset (G × G)} {A B : Finset G} {badPair : G → G → Prop} [DecidableRel badPair]
    (hG : Gph' ⊆ A ×ˢ B) :
    ∑ v ∈ A, (((neighLeft Gph' v ×ˢ neighLeft Gph' v).filter (fun (p : G × G) => badPair p.1 p.2)).card : ℝ) =
    ∑ p ∈ (B ×ˢ B).filter (fun (q : G × G) => badPair q.1 q.2),
      ((neighRight Gph' p.1 ∩ neighRight Gph' p.2).card : ℝ) := by
  let badPairs : Finset (G × G) := (B ×ˢ B).filter (fun (p : G × G) => badPair p.1 p.2)
  let T : Finset (G × (G × G)) :=
    (A ×ˢ badPairs).filter (fun t => t.2.1 ∈ neighLeft Gph' t.1 ∧ t.2.2 ∈ neighLeft Gph' t.1)
  have hN_sub : ∀ v ∈ A, neighLeft Gph' v ⊆ B := by
    intro v _ b hb
    rcases Finset.mem_image.mp hb with ⟨e, he, rfl⟩
    have h_eG : e ∈ Gph' := (Finset.mem_filter.mp he).1
    exact (Finset.mem_product.mp (hG h_eG)).2
  have hR_sub : ∀ u : G, neighRight Gph' u ⊆ A := by
    intro u v hv
    rcases Finset.mem_image.mp hv with ⟨e, he, rfl⟩
    have h_eG : e ∈ Gph' := (Finset.mem_filter.mp he).1
    exact (Finset.mem_product.mp (hG h_eG)).1
  have h_left_iff : ∀ (v : G) (u : G), u ∈ neighLeft Gph' v ↔ (v, u) ∈ Gph' := by
    intro v u
    simp [neighLeft, Finset.mem_image, Finset.mem_filter]
    <;> constructor <;> rintro ⟨e, he, rfl⟩ <;> exact ⟨e, he, rfl⟩
  have h_right_iff : ∀ (v u : G), v ∈ neighRight Gph' u ↔ (v, u) ∈ Gph' := by
    intro v u
    simp [neighRight, Finset.mem_image, Finset.mem_filter]
    <;> constructor <;> rintro ⟨e, he, rfl⟩ <;> exact ⟨e, he, rfl⟩
  -- Fiber over v: T.filter(t.1=v) = {v} ×ˢ ((N(v)×N(v)).filter badPair)
  have h_fiber1_eq : ∀ v ∈ A, T.filter (fun t => Prod.fst t = v) =
      {v} ×ˢ ((neighLeft Gph' v ×ˢ neighLeft Gph' v).filter (fun p => badPair p.1 p.2)) := by
    intro v hv
    ext t
    simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨h_tA, h_pbad⟩, h_cond⟩, h_t1⟩
      have h_p1 : t.2.1 ∈ neighLeft Gph' v := by
        simpa [h_t1] using h_cond.1
      have h_p2 : t.2.2 ∈ neighLeft Gph' v := by
        simpa [h_t1] using h_cond.2
      have h_bad : badPair t.2.1 t.2.2 := (Finset.mem_filter.mp h_pbad).2
      exact ⟨h_t1, ⟨⟨h_p1, h_p2⟩, h_bad⟩⟩
    · rintro ⟨h_t1, ⟨⟨h_p1, h_p2⟩, h_bad⟩⟩
      have h_pbad : t.2 ∈ badPairs := by
        have h1 : t.2.1 ∈ B := hN_sub v hv h_p1
        have h2 : t.2.2 ∈ B := hN_sub v hv h_p2
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h2⟩, h_bad⟩
      have h_cond : t.2.1 ∈ neighLeft Gph' t.1 ∧ t.2.2 ∈ neighLeft Gph' t.1 := by
        rw [h_t1] <;> exact ⟨h_p1, h_p2⟩
      have h_tA : t.1 ∈ A := by rw [h_t1] <;> exact hv
      exact ⟨⟨⟨h_tA, h_pbad⟩, h_cond⟩, h_t1⟩
  -- Fiber over p: T.filter(t.2=p) = (neighRight(p.1) ∩ neighRight(p.2)) ×ˢ {p}
  have h_fiber2_eq : ∀ p ∈ badPairs, T.filter (fun t => Prod.snd t = p) =
      (neighRight Gph' p.1 ∩ neighRight Gph' p.2) ×ˢ {p} := by
    intro p hp
    ext t
    simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨h_tA, h_pbad⟩, h_cond⟩, h_t2⟩
      have h_v1 : t.1 ∈ neighRight Gph' p.1 := by
        have h1 : t.2.1 ∈ neighLeft Gph' t.1 := h_cond.1
        have h21 : t.2.1 = p.1 := by
          have h3 : t.2 = p := h_t2
          exact congr_arg (fun x : G × G => x.1) h3
        rw [h21] at h1
        have h4 : (t.1, p.1) ∈ Gph' := (h_left_iff t.1 p.1).mp h1
        exact (h_right_iff t.1 p.1).mpr h4
      have h_v2 : t.1 ∈ neighRight Gph' p.2 := by
        have h2 : t.2.2 ∈ neighLeft Gph' t.1 := h_cond.2
        have h22 : t.2.2 = p.2 := by
          have h3 : t.2 = p := h_t2
          exact congr_arg (fun x : G × G => x.2) h3
        rw [h22] at h2
        have h4 : (t.1, p.2) ∈ Gph' := (h_left_iff t.1 p.2).mp h2
        exact (h_right_iff t.1 p.2).mpr h4
      exact ⟨Finset.mem_inter.mpr ⟨h_v1, h_v2⟩, h_t2⟩
    · rintro ⟨h_v, h_t2⟩
      have h_v1 : t.1 ∈ neighRight Gph' p.1 := (Finset.mem_inter.mp h_v).1
      have h_v2 : t.1 ∈ neighRight Gph' p.2 := (Finset.mem_inter.mp h_v).2
      have h_tA : t.1 ∈ A := hR_sub p.1 h_v1
      have h_cond1 : p.1 ∈ neighLeft Gph' t.1 := by
        have h : (t.1, p.1) ∈ Gph' := (h_right_iff t.1 p.1).mp h_v1
        exact (h_left_iff t.1 p.1).mpr h
      have h_cond2 : p.2 ∈ neighLeft Gph' t.1 := by
        have h : (t.1, p.2) ∈ Gph' := (h_right_iff t.1 p.2).mp h_v2
        exact (h_left_iff t.1 p.2).mpr h
      have h_cond : t.2.1 ∈ neighLeft Gph' t.1 ∧ t.2.2 ∈ neighLeft Gph' t.1 := by
        have h3 : t.2 = p := h_t2
        rw [h3]
        exact ⟨h_cond1, h_cond2⟩
      have h_t2bad : t.2 ∈ badPairs := by
        rw [h_t2] <;> exact hp
      exact ⟨⟨⟨h_tA, h_t2bad⟩, h_cond⟩, h_t2⟩
  -- Count by v
  have h_maps1 : (T : Set (G × (G × G))).MapsTo Prod.fst A := by
    intro t ht
    have h : t ∈ A ×ˢ badPairs := (Finset.mem_filter.mp ht).1
    exact (Finset.mem_product.mp h).1
  have h_card1 : T.card = ∑ v ∈ A, (T.filter (fun t => Prod.fst t = v)).card :=
    Finset.card_eq_sum_card_fiberwise (H := h_maps1)
  have hS1 : (T.card : ℝ) = ∑ v ∈ A, (((neighLeft Gph' v ×ˢ neighLeft Gph' v).filter (fun p => badPair p.1 p.2)).card : ℝ) := by
    have h : (T.card : ℝ) = ∑ v ∈ A, ((T.filter (fun t => Prod.fst t = v)).card : ℝ) := by
      rw [h_card1, Nat.cast_sum]
    rw [h]
    apply Finset.sum_congr rfl
    intro v hv
    rw [h_fiber1_eq v hv, Finset.card_product, Finset.card_singleton] <;> ring_nf
  -- Count by p
  have h_maps2 : (T : Set (G × (G × G))).MapsTo Prod.snd badPairs := by
    intro t ht
    have h : t ∈ A ×ˢ badPairs := (Finset.mem_filter.mp ht).1
    exact (Finset.mem_product.mp h).2
  have h_card2 : T.card = ∑ p ∈ badPairs, (T.filter (fun t => Prod.snd t = p)).card :=
    Finset.card_eq_sum_card_fiberwise (H := h_maps2)
  have hS2 : (T.card : ℝ) = ∑ p ∈ badPairs, ((neighRight Gph' p.1 ∩ neighRight Gph' p.2).card : ℝ) := by
    have h : (T.card : ℝ) = ∑ p ∈ badPairs, ((T.filter (fun t => Prod.snd t = p)).card : ℝ) := by
      rw [h_card2, Nat.cast_sum]
    rw [h]
    apply Finset.sum_congr rfl
    intro p hp
    rw [h_fiber2_eq p hp, Finset.card_product, Finset.card_singleton] <;> ring_nf
  linarith

/-- **Key Lemma (Lemma 4.2).** Given a bipartite graph `Gph' ⊆ A × B` with
`|Gph'| ≥ |A||B|/(2K)` and every b in the graph has degree ≥ |A|/(2K),
there exist `A' ⊆ A`, `B' ⊆ B` with `|A'| ≥ |A|/(16K²)`, `|B'| ≥ |B|/(4K)`,
and every `a ∈ A'`, `b ∈ B'` has at least `|A||B|/(2^12 K^5)` length-3 paths. -/
theorem bsg_key_lemma (hG : Gph' ⊆ A ×ˢ B) (hK : 1 ≤ K)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (h_edges : (Gph'.card : ℝ) ≥ (A.card : ℝ) * (B.card : ℝ) / (2 * (K : ℝ)))
    (h_minDeg : ∀ p ∈ Gph', (A.card : ℝ) ≤ (neighRight Gph' p.2).card * (2 * (K : ℝ))) :
    ∃ (A' : Finset G) (B' : Finset G),
      A' ⊆ A ∧ B' ⊆ B ∧
      (A'.card : ℝ) ≥ (A.card : ℝ) / (16 * (K : ℝ)^2) ∧
      (B'.card : ℝ) ≥ (B.card : ℝ) / (4 * (K : ℝ)) ∧
      ∀ a ∈ A', ∀ b ∈ B',
        (path3 Gph' a b : ℝ) ≥
          (A.card : ℝ) * (B.card : ℝ) / (2^12 * (K : ℝ)^5) := by
  classical
  let N (v : G) : Finset G := neighLeft Gph' v
  let badPair := isBadPair Gph' A K
  letI : DecidableRel badPair := Classical.decRel badPair
  let badPairsIn (s : Finset G) : Finset (G × G) :=
    (s ×ˢ s).filter (fun p : G × G => badPair p.1 p.2)
  let Y (v : G) : ℕ := (badPairsIn (N v)).card
  let badPartners (v u : G) : Finset G :=
    (N v).filter (fun w => badPair u w)
  let S (v : G) : Finset G :=
    (N v).filter (fun u => ((badPartners v u).card : ℝ) ≥ (B.card : ℝ) / (32 * (K : ℝ)^2))
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K from by omega)
  have hBpos : (0 : ℝ) < (B.card : ℝ) := by
    have h : 0 < B.card := Finset.Nonempty.card_pos hB
    exact_mod_cast h
  let badPairsF : Finset (G × G) := (B ×ˢ B).filter (fun (q : G × G) => badPair q.1 q.2)
  -- Step 1: Bound ∑_v Y(v) using ordered-pair counting
  have h_main : ∑ v ∈ A, (Y v : ℝ) =
      ∑ p ∈ badPairsF, (commonNeighRight Gph' p.1 p.2 : ℝ) := by
    exact sum_badPairs_swap (Gph' := Gph') (A := A) (B := B) (badPair := badPair) hG
  have h1 : ∀ p ∈ badPairsF,
      (commonNeighRight Gph' p.1 p.2 : ℝ) < (A.card : ℝ) / (128 * (K : ℝ)^3) := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have h2 : ∑ p ∈ badPairsF, (commonNeighRight Gph' p.1 p.2 : ℝ) ≤
      ∑ _p ∈ badPairsF, (A.card : ℝ) / (128 * (K : ℝ)^3) :=
    Finset.sum_le_sum (fun p hp => (h1 p hp).le)
  have h3 : ∑ _p ∈ badPairsF, (A.card : ℝ) / (128 * (K : ℝ)^3) =
      (badPairsF.card : ℝ) * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := by
    simp [Finset.sum_const] <;> ring
  have h4 : (badPairsF.card : ℝ) ≤ ((B ×ˢ B).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have h_sumY : ∑ v ∈ A, (Y v : ℝ) ≤
      (A.card : ℝ) * (B.card : ℝ)^2 / (128 * (K : ℝ)^3) := by
    rw [h_main]
    have h5 : ∑ p ∈ badPairsF, (commonNeighRight Gph' p.1 p.2 : ℝ) ≤
        (badPairsF.card : ℝ) * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := by
      calc
        ∑ p ∈ badPairsF, (commonNeighRight Gph' p.1 p.2 : ℝ)
          ≤ ∑ _p ∈ badPairsF, (A.card : ℝ) / (128 * (K : ℝ)^3) := h2
        _ = (badPairsF.card : ℝ) * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := h3
    have h6 : (badPairsF.card : ℝ) * ((A.card : ℝ) / (128 * (K : ℝ)^3)) ≤
        ((B ×ˢ B).card : ℝ) * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := by
      gcongr <;> positivity
    have h7 : ((B ×ˢ B).card : ℝ) = (B.card : ℝ)^2 := by
      simp [Finset.card_product] <;> ring
    calc
      ∑ p ∈ badPairsF, (commonNeighRight Gph' p.1 p.2 : ℝ)
        ≤ (badPairsF.card : ℝ) * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := h5
      _ ≤ ((B ×ˢ B).card : ℝ) * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := h6
      _ = (B.card : ℝ)^2 * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := by rw [h7] <;> ring
      _ = (A.card : ℝ) * (B.card : ℝ)^2 / (128 * (K : ℝ)^3) := by ring
  -- Step 2: Bound ∑_v |S(v)|
  have hS1 : ∀ v ∈ A, ((S v).card : ℝ) * ((B.card : ℝ) / (32 * (K : ℝ)^2)) ≤ (Y v : ℝ) := by
    intro v _
    have h2 : ∑ u ∈ S v, ((badPartners v u).card : ℝ) ≤ (Y v : ℝ) := by
      have h3 : ∑ u ∈ S v, ((badPartners v u).card : ℝ) ≤
          ∑ u ∈ N v, ((badPartners v u).card : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro _ _ _; positivity
      have h4 : ∑ u ∈ N v, (badPartners v u).card = Y v := by
        let S : Finset (G × G) := (N v ×ˢ N v).filter (fun p => badPair p.1 p.2)
        let f : G × G → G := Prod.fst
        have h_maps : (S : Set (G × G)).MapsTo f (N v) := by
          intro p hp
          have h1 : p ∈ N v ×ˢ N v := (Finset.mem_filter.mp hp).1
          exact (Finset.mem_product.mp h1).1
        have h_card : S.card = ∑ u ∈ N v, (S.filter (fun p => p.1 = u)).card :=
          Finset.card_eq_sum_card_fiberwise (H := h_maps)
        have h_fiber : ∀ u ∈ N v, (S.filter (fun p => p.1 = u)).card = (badPartners v u).card := by
          intro u hu
          have h_set_eq : S.filter (fun p => p.1 = u) =
              (badPartners v u).image (fun w : G => (u, w)) := by
            ext p
            constructor
            · intro h
              have h1 : p ∈ S := (Finset.mem_filter.mp h).1
              have h2 : p.1 = u := (Finset.mem_filter.mp h).2
              have h3 : p ∈ N v ×ˢ N v := (Finset.mem_filter.mp h1).1
              have h4 : badPair p.1 p.2 := (Finset.mem_filter.mp h1).2
              have h5 : p.2 ∈ N v := (Finset.mem_product.mp h3).2
              have h6 : badPair u p.2 := by rw [h2] at h4; exact h4
              have h7 : p.2 ∈ badPartners v u := by
                simp only [badPartners, Finset.mem_filter] <;> exact ⟨h5, h6⟩
              have h8 : (u, p.2) = p := by
                apply Prod.ext <;> simp [h2] <;> tauto
              exact Finset.mem_image.mpr ⟨p.2, h7, h8⟩
            · intro h
              rcases Finset.mem_image.mp h with ⟨w, hw, rfl⟩
              have h5 : w ∈ badPartners v u := hw
              have h6 : w ∈ N v := (Finset.mem_filter.mp h5).1
              have h7 : badPair u w := (Finset.mem_filter.mp h5).2
              have h8 : (u, w) ∈ N v ×ˢ N v := Finset.mem_product.mpr ⟨hu, h6⟩
              have h9 : (u, w) ∈ S := Finset.mem_filter.mpr ⟨h8, h7⟩
              exact Finset.mem_filter.mpr ⟨h9, by simp⟩
          rw [h_set_eq]
          have h_inj : Set.InjOn (fun w : G => (u, w)) (badPartners v u : Set G) := by
            intro x _ y _ h
            exact Prod.ext_iff.mp h |>.2
          rw [Finset.card_image_of_injOn h_inj]
        have h_eq1 : S.card = ∑ u ∈ N v, (badPartners v u).card := by
          rw [h_card]
          apply Finset.sum_congr rfl
          intro u hu
          exact h_fiber u hu
        have h_eq2 : S.card = Y v := by rfl
        rw [← h_eq1, h_eq2]
      have h4' : ∑ u ∈ N v, ((badPartners v u).card : ℝ) = (Y v : ℝ) := by
        exact_mod_cast h4
      exact h3.trans_eq h4'
    have h5 : ∀ u ∈ S v, ((B.card : ℝ) / (32 * (K : ℝ)^2)) ≤ ((badPartners v u).card : ℝ) := by
      intro u hu
      exact (Finset.mem_filter.mp hu).2
    have h6 : ((S v).card : ℝ) * ((B.card : ℝ) / (32 * (K : ℝ)^2)) ≤
        ∑ u ∈ S v, ((badPartners v u).card : ℝ) := by
      calc
        ((S v).card : ℝ) * ((B.card : ℝ) / (32 * (K : ℝ)^2))
          = ∑ _u ∈ S v, ((B.card : ℝ) / (32 * (K : ℝ)^2)) := by
            simp [Finset.sum_const] <;> ring
        _ ≤ ∑ u ∈ S v, ((badPartners v u).card : ℝ) :=
          Finset.sum_le_sum (fun u hu => h5 u hu)
    exact h6.trans h2
  have hS2 : ∀ v ∈ A, ((S v).card : ℝ) ≤
      (32 * (K : ℝ)^2) / (B.card : ℝ) * (Y v : ℝ) := by
    intro v hv
    have h4 := hS1 v hv
    have h5 : ((S v).card : ℝ) ≤
        (Y v : ℝ) / ((B.card : ℝ) / (32 * (K : ℝ)^2)) := by
      calc
        ((S v).card : ℝ)
          = (((S v).card : ℝ) * ((B.card : ℝ) / (32 * (K : ℝ)^2))) / ((B.card : ℝ) / (32 * (K : ℝ)^2)) := by
            field_simp [hBpos.ne'] <;> ring
        _ ≤ (Y v : ℝ) / ((B.card : ℝ) / (32 * (K : ℝ)^2)) := by gcongr
    have h6 : (Y v : ℝ) / ((B.card : ℝ) / (32 * (K : ℝ)^2)) =
        (32 * (K : ℝ)^2) / (B.card : ℝ) * (Y v : ℝ) := by
      field_simp [hBpos.ne'] <;> ring
    rw [h6] at h5
    exact h5
  have h_sumS : ∑ v ∈ A, ((S v).card : ℝ) ≤
      (A.card : ℝ) * (B.card : ℝ) / (4 * (K : ℝ)) := by
    have h4 : ∑ v ∈ A, ((S v).card : ℝ) ≤
        ∑ v ∈ A, ((32 * (K : ℝ)^2) / (B.card : ℝ) * (Y v : ℝ)) :=
      Finset.sum_le_sum (fun v hv => hS2 v hv)
    have h5 : ∑ v ∈ A, ((32 * (K : ℝ)^2) / (B.card : ℝ) * (Y v : ℝ)) =
        (32 * (K : ℝ)^2) / (B.card : ℝ) * ∑ v ∈ A, (Y v : ℝ) := by
      rw [Finset.mul_sum] <;> rfl
    have h6 : ∑ v ∈ A, ((S v).card : ℝ) ≤
        (32 * (K : ℝ)^2) / (B.card : ℝ) * ∑ v ∈ A, (Y v : ℝ) := by
      calc
        ∑ v ∈ A, ((S v).card : ℝ)
          ≤ ∑ v ∈ A, ((32 * (K : ℝ)^2) / (B.card : ℝ) * (Y v : ℝ)) := h4
        _ = (32 * (K : ℝ)^2) / (B.card : ℝ) * ∑ v ∈ A, (Y v : ℝ) := h5
    have h7 : (32 * (K : ℝ)^2) / (B.card : ℝ) * ∑ v ∈ A, (Y v : ℝ) ≤
        (32 * (K : ℝ)^2) / (B.card : ℝ) *
          ((A.card : ℝ) * (B.card : ℝ)^2 / (128 * (K : ℝ)^3)) := by
      gcongr <;> exact h_sumY
    have h8 : (32 * (K : ℝ)^2) / (B.card : ℝ) *
          ((A.card : ℝ) * (B.card : ℝ)^2 / (128 * (K : ℝ)^3)) =
        (A.card : ℝ) * (B.card : ℝ) / (4 * (K : ℝ)) := by
      field_simp [hKpos.ne', hBpos.ne'] <;> ring
    calc
      ∑ v ∈ A, ((S v).card : ℝ)
        ≤ (32 * (K : ℝ)^2) / (B.card : ℝ) * ∑ v ∈ A, (Y v : ℝ) := h6
      _ ≤ (32 * (K : ℝ)^2) / (B.card : ℝ) *
            ((A.card : ℝ) * (B.card : ℝ)^2 / (128 * (K : ℝ)^3)) := h7
      _ = (A.card : ℝ) * (B.card : ℝ) / (4 * (K : ℝ)) := h8
  -- Step 3: ∑_v |N(v)| = |Gph'|
  have h_sumN : ∑ v ∈ A, (N v).card = Gph'.card := by
    have h_eq : ∀ v ∈ A, (N v).card = degLeft Gph' v := by
      intro v _
      exact card_neighLeft_eq_degLeft Gph' v
    rw [Finset.sum_congr rfl h_eq]
    exact sum_degLeft_eq_card hG
  have h_sumN' : ∑ v ∈ A, ((N v).card : ℝ) = (Gph'.card : ℝ) := by
    exact_mod_cast h_sumN
  have h_sum_diff : ∑ v ∈ A, (((N v).card : ℝ) - ((S v).card : ℝ)) ≥
      (A.card : ℝ) * (B.card : ℝ) / (4 * (K : ℝ)) := by
    have h3 : ∑ v ∈ A, (((N v).card : ℝ) - ((S v).card : ℝ)) =
        (∑ v ∈ A, ((N v).card : ℝ)) - ∑ v ∈ A, ((S v).card : ℝ) := by
      rw [Finset.sum_sub_distrib] <;> rfl
    rw [h3]
    have h4 : (∑ v ∈ A, ((N v).card : ℝ)) ≥ (A.card : ℝ) * (B.card : ℝ) / (2 * (K : ℝ)) := by
      rw [h_sumN'] <;> exact h_edges
    have h51 : (∑ v ∈ A, ((S v).card : ℝ)) ≤ (A.card : ℝ) * (B.card : ℝ) / (4 * (K : ℝ)) := h_sumS
    set sumN := (∑ v ∈ A, ((N v).card : ℝ)) with hsumN
    set sumS := (∑ v ∈ A, ((S v).card : ℝ)) with hsumS
    set a1 := (A.card : ℝ) * (B.card : ℝ) / (2 * (K : ℝ)) with ha1
    set a2 := (A.card : ℝ) * (B.card : ℝ) / (4 * (K : ℝ)) with ha2
    have h52 : a1 - sumS ≤ sumN - sumS := by
      exact sub_le_sub_right h4 sumS
    have h53 : a1 - a2 ≤ a1 - sumS := by
      exact sub_le_sub_left h51 a1
    have h5 : a1 - a2 ≤ sumN - sumS := le_trans h53 h52
    have h6 : a1 - a2 = a2 := by
      simp only [ha1, ha2]
      field_simp [hKpos.ne'] <;> ring
    have h7 : sumN - sumS ≥ a2 := by
      calc
        sumN - sumS ≥ a1 - a2 := h5
        _ = a2 := h6
    simpa [h3, ha2] using h7
  -- Step 4: Find v with |N(v)| - |S(v)| ≥ |B|/(4K)
  have h_exists : ∃ v ∈ A, ((N v).card : ℝ) - ((S v).card : ℝ) ≥
      (B.card : ℝ) / (4 * (K : ℝ)) := by
    by_contra h
    push Not at h
    have h5 : ∑ v ∈ A, (((N v).card : ℝ) - ((S v).card : ℝ)) <
        (A.card : ℝ) * ((B.card : ℝ) / (4 * (K : ℝ))) := by
      have h6 : ∑ v ∈ A, (((N v).card : ℝ) - ((S v).card : ℝ)) <
          ∑ _v ∈ A, ((B.card : ℝ) / (4 * (K : ℝ))) := by
        apply Finset.sum_lt_sum_of_nonempty hA
        intro v hv
        exact h v hv
      simpa [Finset.sum_const] using h6
    have h7 : (A.card : ℝ) * ((B.card : ℝ) / (4 * (K : ℝ))) =
        (A.card : ℝ) * (B.card : ℝ) / (4 * (K : ℝ)) := by ring
    rw [h7] at h5
    linarith [h_sum_diff]
  rcases h_exists with ⟨v, hvA, hv_good⟩
  let B' : Finset G := N v \ S v
  have hB'_sub : B' ⊆ B := by
    intro b hb
    have h7 : b ∈ N v := (Finset.mem_sdiff.mp hb).1
    have h8 : (v, b) ∈ Gph' := by simpa [N, neighLeft] using h7
    have h9 : (v, b) ∈ A ×ˢ B := hG h8
    exact (Finset.mem_product.mp h9).2
  have h11 : S v ⊆ N v := Finset.filter_subset _ _
  have hB'_card : (B'.card : ℝ) ≥ (B.card : ℝ) / (4 * (K : ℝ)) := by
    have h_disj : Disjoint (S v) B' := Finset.disjoint_sdiff
    have h_union : S v ∪ B' = N v := by
      simp [B', Finset.union_sdiff_of_subset h11]
    have h_card : (S v).card + B'.card = (N v).card := by
      rw [← Finset.card_union_of_disjoint h_disj, h_union]
    have h10' : (B'.card : ℝ) = ((N v).card : ℝ) - ((S v).card : ℝ) := by
      have h_card' : ((S v).card : ℝ) + (B'.card : ℝ) = ((N v).card : ℝ) := by
        exact_mod_cast h_card
      exact eq_sub_of_add_eq' h_card'
    rw [h10']
    exact hv_good
  -- Step 5: Define A' and count edges between A and B'
  let A' : Finset G := A.filter (fun a =>
    ((N a ∩ B').card : ℝ) ≥ (B.card : ℝ) / (16 * (K : ℝ)^2))
  have hA'_sub : A' ⊆ A := Finset.filter_subset _ _
  let edgesAB' : Finset (G × G) := Gph'.filter (fun p => p.2 ∈ B')
  have h_maps1 : (edgesAB' : Set (G × G)).MapsTo Prod.fst A := by
    intro p hp
    have h2 : p ∈ Gph' := (Finset.mem_filter.mp hp).1
    have h3 : p ∈ A ×ˢ B := hG h2
    exact (Finset.mem_product.mp h3).1
  have h_fiber1 : ∀ a ∈ A, (edgesAB'.filter (fun p => p.1 = a)).card = (N a ∩ B').card := by
    intro a _
    have h_inj : Set.InjOn Prod.snd ((edgesAB'.filter (fun p => p.1 = a)) : Set (G × G)) := by
      intro p hp q hq h
      have hpf : p.1 = a := (Finset.mem_filter.mp hp).2
      have hqf : q.1 = a := (Finset.mem_filter.mp hq).2
      have h_eq : p.1 = q.1 := by rw [hpf, hqf]
      exact Prod.ext h_eq h
    have h_img : (edgesAB'.filter (fun p => p.1 = a)).image Prod.snd = N a ∩ B' := by
      ext b
      constructor
      · intro h
        rcases Finset.mem_image.mp h with ⟨p, hp_filter, rfl⟩
        have hp_in : p ∈ edgesAB' := (Finset.mem_filter.mp hp_filter).1
        have hp1 : p.1 = a := (Finset.mem_filter.mp hp_filter).2
        have hpG : p ∈ Gph' := (Finset.mem_filter.mp hp_in).1
        have hpB' : p.2 ∈ B' := (Finset.mem_filter.mp hp_in).2
        have h_na : p.2 ∈ N a := by
          have h9 : p = (a, p.2) := by
            apply Prod.ext
            · exact hp1
            · rfl
          have h10 : (a, p.2) ∈ Gph' := by
            rw [← h9]
            exact hpG
          simpa [N, neighLeft] using h10
        exact Finset.mem_inter.mpr ⟨h_na, hpB'⟩
      · intro h
        have h_na : b ∈ N a := (Finset.mem_inter.mp h).1
        have h_b' : b ∈ B' := (Finset.mem_inter.mp h).2
        have hG : (a, b) ∈ Gph' := by simpa [N, neighLeft] using h_na
        have h_edge : (a, b) ∈ edgesAB' := Finset.mem_filter.mpr ⟨hG, h_b'⟩
        have h_filter : (a, b) ∈ edgesAB'.filter (fun p => p.1 = a) :=
          Finset.mem_filter.mpr ⟨h_edge, by simp⟩
        exact Finset.mem_image.mpr ⟨(a, b), h_filter, rfl⟩
    rw [← Finset.card_image_of_injOn h_inj, h_img]
  have h_left : (edgesAB'.card : ℝ) = ∑ a ∈ A, ((N a ∩ B').card : ℝ) := by
    have h_card1 : edgesAB'.card = ∑ a ∈ A, (edgesAB'.filter (fun p => p.1 = a)).card :=
      Finset.card_eq_sum_card_fiberwise (H := h_maps1)
    have h : (edgesAB'.card : ℝ) = ∑ a ∈ A, ((edgesAB'.filter (fun p => p.1 = a)).card : ℝ) := by
      rw [h_card1, Nat.cast_sum]
    rw [h]
    apply Finset.sum_congr rfl
    intro a ha
    exact_mod_cast h_fiber1 a ha
  have h_maps2 : (edgesAB' : Set (G × G)).MapsTo Prod.snd B' := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have h_fiber2 : ∀ b ∈ B', (edgesAB'.filter (fun p => p.2 = b)).card = (neighRight Gph' b).card := by
    intro b _
    have h_eq : edgesAB'.filter (fun p => p.2 = b) = Gph'.filter (fun p => p.2 = b) := by
      apply Finset.ext
      intro q
      constructor
      · intro h
        have h1 : q ∈ edgesAB' := (Finset.mem_filter.mp h).1
        have h2 : q.2 = b := (Finset.mem_filter.mp h).2
        have h3 : q ∈ Gph' := (Finset.mem_filter.mp h1).1
        exact Finset.mem_filter.mpr ⟨h3, h2⟩
      · intro h
        have h3 : q ∈ Gph' := (Finset.mem_filter.mp h).1
        have h4 : q.2 = b := (Finset.mem_filter.mp h).2
        have h5 : q.2 ∈ B' := by rw [h4] <;> exact ‹b ∈ B'›
        have h6 : q ∈ edgesAB' := Finset.mem_filter.mpr ⟨h3, h5⟩
        exact Finset.mem_filter.mpr ⟨h6, h4⟩
    rw [h_eq]
    have h_inj : Set.InjOn Prod.fst ((Gph'.filter (fun p => p.2 = b)) : Set (G × G)) := by
      intro p hp q hq h
      have hpf : p.2 = b := (Finset.mem_filter.mp hp).2
      have hqf : q.2 = b := (Finset.mem_filter.mp hq).2
      have h_eq : p.2 = q.2 := by rw [hpf, hqf]
      exact Prod.ext h h_eq
    have h_img : (Gph'.filter (fun p => p.2 = b)).image Prod.fst = neighRight Gph' b := by
      rfl
    rw [← Finset.card_image_of_injOn h_inj, h_img]
  have h_right : (edgesAB'.card : ℝ) = ∑ b ∈ B', ((neighRight Gph' b).card : ℝ) := by
    have h_card2 : edgesAB'.card = ∑ b ∈ B', (edgesAB'.filter (fun p => p.2 = b)).card :=
      Finset.card_eq_sum_card_fiberwise (H := h_maps2)
    have h : (edgesAB'.card : ℝ) = ∑ b ∈ B', ((edgesAB'.filter (fun p => p.2 = b)).card : ℝ) := by
      rw [h_card2, Nat.cast_sum]
    rw [h]
    apply Finset.sum_congr rfl
    intro b hb
    exact_mod_cast h_fiber2 b hb
  have h_eq_both : ∑ a ∈ A, ((N a ∩ B').card : ℝ) = ∑ b ∈ B', ((neighRight Gph' b).card : ℝ) := by
    rw [←h_left, h_right]
  have h_edgesAB : ∑ a ∈ A, ((N a ∩ B').card : ℝ) ≥
      (A.card : ℝ) * (B.card : ℝ) / (8 * (K : ℝ)^2) := by
    rw [h_eq_both]
    have h2 : ∀ b ∈ B', (A.card : ℝ) ≤ (neighRight Gph' b).card * (2 * (K : ℝ)) := by
      intro b hb
      have h3 : b ∈ N v := (Finset.mem_sdiff.mp hb).1
      have h4 : (v, b) ∈ Gph' := by simpa [N, neighLeft] using h3
      exact h_minDeg (v, b) h4
    have h3 : ∀ b ∈ B', ((neighRight Gph' b).card : ℝ) ≥ (A.card : ℝ) / (2 * (K : ℝ)) := by
      intro b hb
      have h4 := h2 b hb
      calc
        ((neighRight Gph' b).card : ℝ)
          = (((neighRight Gph' b).card : ℝ) * (2 * (K : ℝ))) / (2 * (K : ℝ)) := by
            field_simp [hKpos.ne'] <;> ring
        _ ≥ (A.card : ℝ) / (2 * (K : ℝ)) := by gcongr
    have h4 : ∑ b ∈ B', ((neighRight Gph' b).card : ℝ) ≥
        ∑ _b ∈ B', (A.card : ℝ) / (2 * (K : ℝ)) :=
      Finset.sum_le_sum (fun b hb => h3 b hb)
    have h5 : ∑ _b ∈ B', (A.card : ℝ) / (2 * (K : ℝ)) =
        (B'.card : ℝ) * ((A.card : ℝ) / (2 * (K : ℝ))) := by
      simp [Finset.sum_const] <;> ring
    have h6 : ∑ b ∈ B', ((neighRight Gph' b).card : ℝ) ≥
        (B'.card : ℝ) * ((A.card : ℝ) / (2 * (K : ℝ))) := by
      calc
        ∑ b ∈ B', ((neighRight Gph' b).card : ℝ)
          ≥ ∑ _b ∈ B', (A.card : ℝ) / (2 * (K : ℝ)) := h4
        _ = (B'.card : ℝ) * ((A.card : ℝ) / (2 * (K : ℝ))) := h5
    have h7 : (B'.card : ℝ) ≥ (B.card : ℝ) / (4 * (K : ℝ)) := hB'_card
    have h8 : (B'.card : ℝ) * ((A.card : ℝ) / (2 * (K : ℝ))) ≥
        ((B.card : ℝ) / (4 * (K : ℝ))) * ((A.card : ℝ) / (2 * (K : ℝ))) := by gcongr
    have h9 : ((B.card : ℝ) / (4 * (K : ℝ))) * ((A.card : ℝ) / (2 * (K : ℝ))) =
        (A.card : ℝ) * (B.card : ℝ) / (8 * (K : ℝ)^2) := by
      field_simp [hKpos.ne'] <;> ring
    linarith [h6, h8, h9]
  have hA'_card : (A'.card : ℝ) ≥ (A.card : ℝ) / (16 * (K : ℝ)^2) := by
    have h_disj : Disjoint A' (A \ A') := Finset.disjoint_sdiff
    have h_union : A' ∪ (A \ A') = A := by
      rw [Finset.union_sdiff_of_subset hA'_sub]
    have h_sum_split : ∑ a ∈ A, ((N a ∩ B').card : ℝ) =
        ∑ a ∈ A', ((N a ∩ B').card : ℝ) + ∑ a ∈ A \ A', ((N a ∩ B').card : ℝ) := by
      have h : ∑ a ∈ (A' ∪ (A \ A')), ((N a ∩ B').card : ℝ) =
          ∑ a ∈ A', ((N a ∩ B').card : ℝ) + ∑ a ∈ A \ A', ((N a ∩ B').card : ℝ) := by
        rw [Finset.sum_union h_disj] <;> rfl
      rw [h_union] at *
      <;> exact h
    have h7 : ∑ a ∈ A', ((N a ∩ B').card : ℝ) ≤ (A'.card : ℝ) * (B.card : ℝ) := by
      have h8 : ∀ a ∈ A', ((N a ∩ B').card : ℝ) ≤ (B.card : ℝ) := by
        intro a _
        have h9 : (N a ∩ B').card ≤ B'.card := by
          apply Finset.card_le_card
          exact Finset.inter_subset_right
        have h10 : B'.card ≤ B.card := Finset.card_le_card hB'_sub
        exact_mod_cast le_trans h9 h10
      calc
        ∑ a ∈ A', ((N a ∩ B').card : ℝ)
          ≤ ∑ _a ∈ A', (B.card : ℝ) := Finset.sum_le_sum (fun a ha => h8 a ha)
        _ = (A'.card : ℝ) * (B.card : ℝ) := by simp [Finset.sum_const] <;> ring
    have h9 : ∀ a ∈ A \ A', a ∈ A := fun a ha => (Finset.mem_sdiff.mp ha).1
    have h10 : ∀ a ∈ A \ A', ((N a ∩ B').card : ℝ) < (B.card : ℝ) / (16 * (K : ℝ)^2) := by
      intro a ha
      have h11 : a ∉ A' := (Finset.mem_sdiff.mp ha).2
      have h12 : ¬(((N a ∩ B').card : ℝ) ≥ (B.card : ℝ) / (16 * (K : ℝ)^2)) := by
        have h13 : a ∈ A := h9 a ha
        simpa [A', Finset.mem_filter, h13] using h11
      exact not_le.mp h12
    have h11 : ∑ a ∈ A \ A', ((N a ∩ B').card : ℝ) ≤
        (A.card : ℝ) * ((B.card : ℝ) / (16 * (K : ℝ)^2)) := by
      have h12 : ∑ a ∈ A \ A', ((N a ∩ B').card : ℝ) ≤
          ∑ _a ∈ A \ A', (B.card : ℝ) / (16 * (K : ℝ)^2) :=
        Finset.sum_le_sum (fun a ha => (h10 a ha).le)
      have h13 : ∑ _a ∈ A \ A', (B.card : ℝ) / (16 * (K : ℝ)^2) =
          ((A \ A').card : ℝ) * ((B.card : ℝ) / (16 * (K : ℝ)^2)) := by
        simp [Finset.sum_const] <;> ring
      have h14 : ((A \ A').card : ℝ) ≤ (A.card : ℝ) := by
        have h141 : A \ A' ⊆ A := by simp
        exact_mod_cast Finset.card_le_card h141
      have h15 : 0 ≤ (B.card : ℝ) / (16 * (K : ℝ)^2) := by positivity
      calc
        ∑ a ∈ A \ A', ((N a ∩ B').card : ℝ)
          ≤ ∑ _a ∈ A \ A', (B.card : ℝ) / (16 * (K : ℝ)^2) := h12
        _ = ((A \ A').card : ℝ) * ((B.card : ℝ) / (16 * (K : ℝ)^2)) := h13
        _ ≤ (A.card : ℝ) * ((B.card : ℝ) / (16 * (K : ℝ)^2)) := by
          gcongr <;> exact h14
    have h5 : ∑ a ∈ A, ((N a ∩ B').card : ℝ) ≤
        (A'.card : ℝ) * (B.card : ℝ) + (A.card : ℝ) * ((B.card : ℝ) / (16 * (K : ℝ)^2)) := by
      rw [h_sum_split]
      linarith [h7, h11]
    have h5_norm : (A.card : ℝ) * ((B.card : ℝ) / (16 * (K : ℝ)^2)) =
        (A.card : ℝ) * (B.card : ℝ) / (16 * (K : ℝ)^2) := by
      field_simp [hKpos.ne'] <;> ring
    have h5' : ∑ a ∈ A, ((N a ∩ B').card : ℝ) ≤
        (A'.card : ℝ) * (B.card : ℝ) + (A.card : ℝ) * (B.card : ℝ) / (16 * (K : ℝ)^2) := by
      rw [h5_norm] at h5
      exact h5
    have h10 : (A'.card : ℝ) * (B.card : ℝ) ≥
        (A.card : ℝ) * (B.card : ℝ) / (16 * (K : ℝ)^2) := by
      have h1 : (A.card : ℝ) * (B.card : ℝ) / (8 * (K : ℝ)^2) ≤
          (A'.card : ℝ) * (B.card : ℝ) + (A.card : ℝ) * (B.card : ℝ) / (16 * (K : ℝ)^2) :=
        le_trans h_edgesAB h5'
      set c := (A.card : ℝ) * (B.card : ℝ) / (16 * (K : ℝ)^2) with hc
      have h2 : (A.card : ℝ) * (B.card : ℝ) / (8 * (K : ℝ)^2) - c ≤
          (A'.card : ℝ) * (B.card : ℝ) + c - c := sub_le_sub_right h1 c
      have h3 : (A'.card : ℝ) * (B.card : ℝ) + c - c = (A'.card : ℝ) * (B.card : ℝ) := by ring
      have h4 : (A.card : ℝ) * (B.card : ℝ) / (8 * (K : ℝ)^2) - c = c := by
        simp only [hc]
        field_simp [hKpos.ne'] <;> ring
      rw [h3, h4] at h2
      exact h2
    have h10' : ((A.card : ℝ) / (16 * (K : ℝ)^2)) * (B.card : ℝ) ≤ (A'.card : ℝ) * (B.card : ℝ) := by
      have h_eq : (A.card : ℝ) * (B.card : ℝ) / (16 * (K : ℝ)^2) =
          ((A.card : ℝ) / (16 * (K : ℝ)^2)) * (B.card : ℝ) := by ring
      rw [h_eq] at h10
      exact h10
    exact le_of_mul_le_mul_right h10' hBpos
  -- Step 6: Path count
  have h_path : ∀ a ∈ A', ∀ b ∈ B',
      (path3 Gph' a b : ℝ) ≥
        (A.card : ℝ) * (B.card : ℝ) / (2^12 * (K : ℝ)^5) := by
    intro a ha b hb
    have h_na : ((N a ∩ B').card : ℝ) ≥ (B.card : ℝ) / (16 * (K : ℝ)^2) :=
      (Finset.mem_filter.mp ha).2
    have h_bad_count : ((badPartners v b).card : ℝ) <
        (B.card : ℝ) / (32 * (K : ℝ)^2) := by
      have h1 : b ∉ S v := (Finset.mem_sdiff.mp hb).2
      have h2 : b ∈ N v := (Finset.mem_sdiff.mp hb).1
      have h3 : ¬(((badPartners v b).card : ℝ) ≥ (B.card : ℝ) / (32 * (K : ℝ)^2)) := by
        simpa [S, Finset.mem_filter, h2] using h1
      exact not_le.mp h3
    have h_bad_subset : (N a ∩ B').filter (fun w => badPair b w) ⊆ badPartners v b := by
      intro w hw
      have h4 : w ∈ N a ∩ B' := (Finset.mem_filter.mp hw).1
      have h5 : w ∈ N v := by
        have h6 : w ∈ B' := (Finset.mem_inter.mp h4).2
        exact (Finset.mem_sdiff.mp h6).1
      simp only [badPartners, Finset.mem_filter]
      exact ⟨h5, (Finset.mem_filter.mp hw).2⟩
    let badInNab : Finset G := (N a ∩ B').filter (fun w => badPair b w)
    let goodB : Finset G := (N a ∩ B').filter (fun w => ¬badPair b w)
    have h_disj : Disjoint goodB badInNab := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 : ¬badPair b x := (Finset.mem_filter.mp hx1).2
      have h2 : badPair b x := (Finset.mem_filter.mp hx2).2
      exact h1 h2
    have h_union : goodB ∪ badInNab = N a ∩ B' := by
      ext x
      simp only [goodB, badInNab, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        by_cases h : badPair b x
        · exact Or.inr ⟨hx, h⟩
        · exact Or.inl ⟨hx, h⟩
    have h1 : (N a ∩ B').card = goodB.card + badInNab.card := by
      rw [← Finset.card_union_of_disjoint h_disj, h_union]
    have h2 : (badInNab.card : ℝ) ≤ ((badPartners v b).card : ℝ) := by
      exact_mod_cast Finset.card_le_card h_bad_subset
    have h_bad_lt : (badInNab.card : ℝ) < (B.card : ℝ) / (32 * (K : ℝ)^2) := by
      calc
        (badInNab.card : ℝ) ≤ (badPartners v b).card := h2
        _ < (B.card : ℝ) / (32 * (K : ℝ)^2) := h_bad_count
    have h_good_card : (goodB.card : ℝ) ≥ (B.card : ℝ) / (32 * (K : ℝ)^2) := by
      have h3 : (goodB.card : ℝ) = ((N a ∩ B').card : ℝ) - (badInNab.card : ℝ) := by
        have h4 : ((N a ∩ B').card : ℝ) = (goodB.card : ℝ) + (badInNab.card : ℝ) := by
          exact_mod_cast h1
        linarith
      rw [h3]
      have h5 : (B.card : ℝ) / (16 * (K : ℝ)^2) - (B.card : ℝ) / (32 * (K : ℝ)^2) ≤
          ((N a ∩ B').card : ℝ) - (badInNab.card : ℝ) := by
        exact sub_le_sub h_na h_bad_lt.le
      have h6 : (B.card : ℝ) / (16 * (K : ℝ)^2) - (B.card : ℝ) / (32 * (K : ℝ)^2) =
          (B.card : ℝ) / (32 * (K : ℝ)^2) := by
        field_simp [hKpos.ne'] <;> ring
      linarith [h5, h6]
    have h_common : ∀ b' ∈ goodB,
        (commonNeighRight Gph' b b' : ℝ) ≥ (A.card : ℝ) / (128 * (K : ℝ)^3) := by
      intro b' hb'
      have h4 : ¬badPair b b' := (Finset.mem_filter.mp hb').2
      exact not_lt.mp h4
    let pathSet : Finset (G × G) := goodB.biUnion (fun b' =>
      (neighRight Gph' b ∩ neighRight Gph' b').image (fun a' => (b', a')))
    have h_subset : pathSet ⊆ path3Set Gph' a b := by
      intro p hp
      rcases Finset.mem_biUnion.mp hp with ⟨b', hb', hpin⟩
      rcases Finset.mem_image.mp hpin with ⟨a', ha', rfl⟩
      have h1 : a' ∈ neighRight Gph' b ∩ neighRight Gph' b' := ha'
      have h2 : a' ∈ neighRight Gph' b := (Finset.mem_inter.mp h1).1
      have h3 : a' ∈ neighRight Gph' b' := (Finset.mem_inter.mp h1).2
      have h4 : (a', b) ∈ Gph' := by simpa [neighRight] using h2
      have h5 : (a', b') ∈ Gph' := by simpa [neighRight] using h3
      have h6 : b' ∈ N a := by
        have h7 : b' ∈ N a ∩ B' := (Finset.mem_filter.mp hb').1
        exact (Finset.mem_inter.mp h7).1
      have h8 : (a, b') ∈ Gph' := by simpa [N, neighLeft] using h6
      exact (mem_path3Set_iff Gph' a b b' a').mpr ⟨h8, h5, h4⟩
    have h_disj2 : ∀ (b1 : G), b1 ∈ goodB → ∀ (b2 : G), b2 ∈ goodB → b1 ≠ b2 →
        Disjoint ((neighRight Gph' b ∩ neighRight Gph' b1).image (fun a' : G => (b1, a')))
          ((neighRight Gph' b ∩ neighRight Gph' b2).image (fun a' : G => (b2, a'))) := by
      intro b1 _ b2 _ hne
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨_, _, h_eq1⟩
      rcases Finset.mem_image.mp hp2 with ⟨_, _, h_eq2⟩
      have h9 : p.1 = b1 := (congr_arg Prod.fst h_eq1).symm
      have h10 : p.1 = b2 := (congr_arg Prod.fst h_eq2).symm
      exact hne (h9.symm.trans h10)
    have h_card_path : pathSet.card = ∑ b' ∈ goodB,
        (neighRight Gph' b ∩ neighRight Gph' b').card := by
      rw [Finset.card_biUnion h_disj2]
      apply Finset.sum_congr rfl
      intro b' _
      have h_inj : Set.InjOn (fun a' : G => (b', a'))
          (↑(neighRight Gph' b ∩ neighRight Gph' b') : Set G) := by
        intro x _ y _ h
        exact Prod.ext_iff.mp h |>.2
      exact Finset.card_image_of_injOn h_inj
    have h_lower : (pathSet.card : ℝ) ≥
        (goodB.card : ℝ) * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := by
      have h_card_path' : (pathSet.card : ℝ) = ∑ b' ∈ goodB, ((neighRight Gph' b ∩ neighRight Gph' b').card : ℝ) := by
        exact_mod_cast h_card_path
      rw [h_card_path']
      have h : ∑ b' ∈ goodB, ((neighRight Gph' b ∩ neighRight Gph' b').card : ℝ) ≥
          ∑ _b' ∈ goodB, (A.card : ℝ) / (128 * (K : ℝ)^3) :=
        Finset.sum_le_sum (fun b' hb' => h_common b' hb')
      calc
        ∑ b' ∈ goodB, ((neighRight Gph' b ∩ neighRight Gph' b').card : ℝ)
          ≥ ∑ _b' ∈ goodB, (A.card : ℝ) / (128 * (K : ℝ)^3) := h
        _ = (goodB.card : ℝ) * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := by
          simp [Finset.sum_const] <;> ring
    have h_final : (path3 Gph' a b : ℝ) ≥ (pathSet.card : ℝ) := by
      exact_mod_cast Finset.card_le_card h_subset
    calc
      (path3 Gph' a b : ℝ)
        ≥ (pathSet.card : ℝ) := h_final
      _ ≥ (goodB.card : ℝ) * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := h_lower
      _ ≥ ((B.card : ℝ) / (32 * (K : ℝ)^2)) *
            ((A.card : ℝ) / (128 * (K : ℝ)^3)) := by gcongr
      _ = (A.card : ℝ) * (B.card : ℝ) / (2^12 * (K : ℝ)^5) := by
          norm_num <;> ring
  exact ⟨A', B', hA'_sub, hB'_sub, hA'_card, hB'_card, h_path⟩

end KeyLemma

section PruningNeighborhood

variable {G : Type*} [AddCommGroup G] [DecidableEq G]
variable {A B : Finset G} {Gph : Finset (G × G)} {K : ℕ}

lemma prunedGraph_neighRight_eq {b : G}
    (hb : b ∈ (prunedGraph A B Gph K).image Prod.snd) :
    neighRight (prunedGraph A B Gph K) b = neighRight Gph b := by
  have h1 : ∃ (a : G), (a, b) ∈ prunedGraph A B Gph K := by
    rcases Finset.mem_image.mp hb with ⟨p, hp, rfl⟩
    exact ⟨p.1, hp⟩
  rcases h1 with ⟨a, ha⟩
  have h2 : A.card ≤ (neighRight Gph b).card * (2 * K) := by
    simp only [prunedGraph, Finset.mem_filter] at ha
    exact ha.2
  have h3 : ∀ (p : G × G), p ∈ Gph → p.2 = b → p ∈ prunedGraph A B Gph K := by
    intro p hp hpb
    simp only [prunedGraph, Finset.mem_filter]
    exact ⟨hp, by rwa [hpb]⟩
  have h4 : (prunedGraph A B Gph K).filter (fun p : G × G => p.2 = b) =
      Gph.filter (fun p : G × G => p.2 = b) := by
    apply Finset.Subset.antisymm
    · intro p hp
      have h5 : p ∈ prunedGraph A B Gph K := (Finset.mem_filter.mp hp).1
      exact Finset.mem_filter.mpr ⟨prunedGraph_subset h5, (Finset.mem_filter.mp hp).2⟩
    · intro p hp
      have h5 : p ∈ Gph := (Finset.mem_filter.mp hp).1
      have h6 : p.2 = b := (Finset.mem_filter.mp hp).2
      have h7 : p ∈ prunedGraph A B Gph K := h3 p h5 h6
      exact Finset.mem_filter.mpr ⟨h7, h6⟩
  have h5 : ((prunedGraph A B Gph K).filter (fun p : G × G => p.2 = b)).image Prod.fst =
      (Gph.filter (fun p : G × G => p.2 = b)).image Prod.fst := by
    rw [h4]
  simpa [neighRight] using h5

end PruningNeighborhood

section Main

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem balog_szemeredi_gowers
    (A B : Finset G) (Gph : Finset (G × G))
    (hG : Gph ⊆ A ×ˢ B)
    (K : ℕ) (hK : 1 ≤ K)
    (h_density : (A.card : ℝ) * (B.card : ℝ) ≤ (K : ℝ) * (Gph.card : ℝ))
    (h_sumset : (restrictedSum A B Gph).card ≤
        (K : ℝ) * Real.sqrt ((A.card : ℝ) * (B.card : ℝ))) :
    ∃ (A' : Finset G) (B' : Finset G),
      A' ⊆ A ∧ B' ⊆ B ∧
      (A'.card : ℝ) ≥ 1 / (K : ℝ)^10 * (A.card : ℝ) ∧
      (B'.card : ℝ) ≥ 1 / (K : ℝ)^10 * (B.card : ℝ) ∧
      (A' + B').card ≤
        (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
  classical
  by_cases hA_empty : A = ∅
  · refine' ⟨∅, B, by simp [hA_empty], by simp, _⟩
    have hK10 : (K : ℝ)^10 ≥ 1 := by
      have hK1 : (K : ℝ) ≥ 1 := by exact_mod_cast hK
      have h : (K : ℝ)^10 ≥ 1 := by
        have h2 : (K : ℝ)^10 ≥ (1 : ℝ)^10 := by gcongr
        norm_num at h2 ⊢ <;> exact h2
      exact h
    constructor
    · simp [hA_empty] <;> positivity
    constructor
    · have h : (B.card : ℝ) ≥ 1 / (K : ℝ)^10 * (B.card : ℝ) := by
        have hpos : 0 ≤ (B.card : ℝ) := by positivity
        have h2 : 1 / (K : ℝ)^10 ≤ 1 := by
          apply (div_le_one (by positivity)).mpr
          exact hK10
        nlinarith
      simpa using h
    · have h : (0 : ℝ) ≤ (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by positivity
      simpa [hA_empty] using h
  · have hA_ne : A.Nonempty := by
      exact Finset.nonempty_iff_ne_empty.mpr hA_empty
    by_cases hB_empty : B = ∅
    · refine' ⟨A, ∅, by simp, by simp [hB_empty], _⟩
      have hK10 : (K : ℝ)^10 ≥ 1 := by
        have hK1 : (K : ℝ) ≥ 1 := by exact_mod_cast hK
        have h : (K : ℝ)^10 ≥ 1 := by
          have h2 : (K : ℝ)^10 ≥ (1 : ℝ)^10 := by gcongr
          norm_num at h2 ⊢ <;> exact h2
        exact h
      constructor
      · have h : (A.card : ℝ) ≥ 1 / (K : ℝ)^10 * (A.card : ℝ) := by
          have hpos : 0 ≤ (A.card : ℝ) := by positivity
          have h2 : 1 / (K : ℝ)^10 ≤ 1 := by
            apply (div_le_one (by positivity)).mpr
            exact hK10
          nlinarith
        simpa using h
      constructor
      · simp [hB_empty] <;> positivity
      · have h : (0 : ℝ) ≤ (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by positivity
        simpa [hB_empty] using h
    · have hB_ne : B.Nonempty := by
        exact Finset.nonempty_iff_ne_empty.mpr hB_empty
      by_cases hK1 : K = 1
      · -- K = 1 case: Gph = A × B, take A'=A, B'=B
        subst hK1
        have hGph_eq : Gph = A ×ˢ B := by
          have h1 : (Gph.card : ℝ) ≥ (A.card : ℝ) * (B.card : ℝ) := by simpa using h_density
          have h2 : Gph.card ≤ (A ×ˢ B).card := Finset.card_le_card hG
          have h3 : (A ×ˢ B).card = A.card * B.card := by
            simp [Finset.card_product] <;> ring
          have h4 : (A ×ˢ B).card ≤ Gph.card := by
            have h5 : ((A ×ˢ B).card : ℝ) = (A.card : ℝ) * (B.card : ℝ) := by exact_mod_cast h3
            have h6 : ((A ×ˢ B).card : ℝ) ≤ (Gph.card : ℝ) := by
              rw [h5]
              exact h1
            exact_mod_cast h6
          have h7 : Gph.card = (A ×ˢ B).card := Nat.le_antisymm h2 h4
          exact Finset.eq_of_subset_of_card_le hG h7.symm.le
        refine' ⟨A, B, by simp, by simp, by simp, by simp, _⟩
        have h5 : restrictedSum A B Gph = A + B := by
          rw [hGph_eq] <;> rfl
        rw [h5] at h_sumset
        have h6 : (A + B).card ≤ (2 : ℝ)^12 * (1 : ℝ)^10 * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
          have h7 : ((A + B).card : ℝ) ≤ (1 : ℝ) * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
            simpa using h_sumset
          have h8 : (1 : ℝ) * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) ≤
              (2 : ℝ)^12 * (1 : ℝ)^10 * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
            have h9 : 0 ≤ Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := Real.sqrt_nonneg _
            nlinarith
          exact le_trans h7 h8
        simpa using h6
      · -- K ≥ 2 case
        have hK2 : K ≥ 2 := by omega
        have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K from by omega)
        set Gph' : Finset (G × G) := prunedGraph A B Gph K with hGph'
        have hG' : Gph' ⊆ A ×ˢ B := by
          exact Finset.Subset.trans (prunedGraph_subset) hG
        have h_edges : (Gph'.card : ℝ) ≥ (A.card : ℝ) * (B.card : ℝ) / (2 * (K : ℝ)) :=
          prunedGraph_density hG hK h_density hA_ne hB_ne
        have h_minDeg : ∀ p ∈ Gph', (A.card : ℝ) ≤ (neighRight Gph' p.2).card * (2 * (K : ℝ)) := by
          intro p hp
          have hb : p.2 ∈ Gph'.image Prod.snd := Finset.mem_image_of_mem _ hp
          have h_eq : neighRight Gph' p.2 = neighRight Gph p.2 := prunedGraph_neighRight_eq hb
          rw [h_eq]
          exact_mod_cast prunedGraph_minDegree hp
        rcases bsg_key_lemma (Gph' := Gph') (A := A) (B := B) (K := K) hG' hK hA_ne hB_ne h_edges h_minDeg
          with ⟨A', B', hA'_sub, hB'_sub, hA'_card, hB'_card, h_path⟩
        have hA'_weak : (A'.card : ℝ) ≥ 1 / (K : ℝ)^10 * (A.card : ℝ) := by
          have h1 : (16 : ℝ) * (K : ℝ)^2 ≤ (K : ℝ)^10 := by
            have h2 : (K : ℝ) ≥ 2 := by exact_mod_cast hK2
            have h3 : (K : ℝ)^8 ≥ 16 := by
              have h4 : (K : ℝ)^8 ≥ 2^8 := by gcongr <;> norm_num
              norm_num at h4 ⊢ <;> linarith
            have h5 : (K : ℝ)^10 = (K : ℝ)^2 * (K : ℝ)^8 := by ring
            rw [h5]
            nlinarith
          have h6 : (A.card : ℝ) / (16 * (K : ℝ)^2) ≥ (A.card : ℝ) / (K : ℝ)^10 := by
            gcongr
          have h6' : (A.card : ℝ) / (K : ℝ)^10 ≤ (A.card : ℝ) / (16 * (K : ℝ)^2) := h6
          have h_goal : (A'.card : ℝ) ≥ 1 / (K : ℝ)^10 * (A.card : ℝ) := by
            have h7 : 1 / (K : ℝ)^10 * (A.card : ℝ) = (A.card : ℝ) / (K : ℝ)^10 := by ring
            rw [h7]
            exact le_trans h6' hA'_card
          exact h_goal
        have hB'_weak : (B'.card : ℝ) ≥ 1 / (K : ℝ)^10 * (B.card : ℝ) := by
          have h1 : (4 : ℝ) * (K : ℝ) ≤ (K : ℝ)^10 := by
            have h2 : (K : ℝ) ≥ 2 := by exact_mod_cast hK2
            have h3 : (K : ℝ)^9 ≥ 4 := by
              have h4 : (K : ℝ)^9 ≥ 2^9 := by gcongr <;> norm_num
              norm_num at h4 ⊢ <;> linarith
            nlinarith
          have h6 : (B.card : ℝ) / (4 * (K : ℝ)) ≥ (B.card : ℝ) / (K : ℝ)^10 := by gcongr
          have h6' : (B.card : ℝ) / (K : ℝ)^10 ≤ (B.card : ℝ) / (4 * (K : ℝ)) := h6
          have h_goal : (B'.card : ℝ) ≥ 1 / (K : ℝ)^10 * (B.card : ℝ) := by
            have h7 : 1 / (K : ℝ)^10 * (B.card : ℝ) = (B.card : ℝ) / (K : ℝ)^10 := by ring
            rw [h7]
            exact le_trans h6' hB'_card
          exact h_goal
        set S : Finset G := restrictedSum A B Gph with hS
        have hS_card : (S.card : ℝ) ≤ (K : ℝ) * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := h_sumset
        by_cases h_small : (A.card : ℝ) * (B.card : ℝ) < (2 : ℝ)^13 * (K : ℝ)^5
        · -- Small case: |A||B| < 2^13 K^5
          have h_sumset_bound : ((A' + B').card : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) := by
            have h : (A' + B').card ≤ A'.card * B'.card := by
              exact Finset.card_image_le.trans (by simp [Finset.card_product] <;> ring)
            have h2 : A'.card * B'.card ≤ A.card * B.card := by
              have h3 : A'.card ≤ A.card := Finset.card_le_card hA'_sub
              have h4 : B'.card ≤ B.card := Finset.card_le_card hB'_sub
              exact mul_le_mul h3 h4 (by positivity) (by positivity)
            have h3 : (A' + B').card ≤ A.card * B.card := le_trans h h2
            exact_mod_cast h3
          have h_final : (A.card : ℝ) * (B.card : ℝ) ≤
              (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
            set x : ℝ := (A.card : ℝ) * (B.card : ℝ) with hx
            have hx_nonneg : 0 ≤ x := by positivity
            by_cases hx0 : x = 0
            · rw [hx0] <;> positivity
            · have hx_pos : 0 < x := by
                rw [hx] at * <;> positivity
              have h1 : x ≤ (2 : ℝ)^24 * (K : ℝ)^20 := by
                have h2 : x < (2 : ℝ)^13 * (K : ℝ)^5 := h_small
                have h3 : (2 : ℝ)^13 * (K : ℝ)^5 ≤ (2 : ℝ)^24 * (K : ℝ)^20 := by
                  have h4 : (K : ℝ) ≥ 2 := by exact_mod_cast hK2
                  have h5 : (2 : ℝ)^13 ≤ (2 : ℝ)^24 := by norm_num
                  have h6 : (K : ℝ)^5 ≤ (K : ℝ)^20 := by
                    gcongr
                    <;> linarith
                  nlinarith
                linarith
              have h_sqrt_le : Real.sqrt x ≤ (2 : ℝ)^12 * (K : ℝ)^10 := by
                have h4 : Real.sqrt x ≤ Real.sqrt ((2 : ℝ)^24 * (K : ℝ)^20) := Real.sqrt_le_sqrt h1
                have h5 : Real.sqrt ((2 : ℝ)^24 * (K : ℝ)^20) = (2 : ℝ)^12 * (K : ℝ)^10 := by
                  have h6 : 0 ≤ (2 : ℝ)^24 * (K : ℝ)^20 := by positivity
                  have h7 : Real.sqrt ((2 : ℝ)^24 * (K : ℝ)^20) =
                      Real.sqrt ((2 : ℝ)^24) * Real.sqrt ((K : ℝ)^20) := by
                    rw [Real.sqrt_mul (by positivity)]
                  rw [h7]
                  have h8 : Real.sqrt ((2 : ℝ)^24) = (2 : ℝ)^12 := by
                    rw [show (2 : ℝ)^24 = ((2 : ℝ)^12)^2 by ring]
                    rw [Real.sqrt_sq (by positivity)]
                  have h9 : Real.sqrt ((K : ℝ)^20) = (K : ℝ)^10 := by
                    rw [show (K : ℝ)^20 = ((K : ℝ)^10)^2 by ring]
                    rw [Real.sqrt_sq (by positivity)]
                  rw [h8, h9] <;> ring
                rw [h5] at h4
                exact h4
              have h10 : (Real.sqrt x)^2 = x := Real.sq_sqrt hx_nonneg
              have h11 : x ≤ (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt x := by
                have h12 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
                have h13 : (Real.sqrt x)^2 ≤ (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt x := by
                  calc
                    (Real.sqrt x)^2
                      = (Real.sqrt x) * (Real.sqrt x) := by ring
                    _ ≤ ((2 : ℝ)^12 * (K : ℝ)^10) * (Real.sqrt x) := by
                      gcongr
                      <;> exact h_sqrt_le
                    _ = (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt x := by ring
                rw [h10] at h13
                exact h13
              simpa [mul_comm] using h11
          exact ⟨A', B', hA'_sub, hB'_sub, hA'_weak, hB'_weak, le_trans h_sumset_bound h_final⟩
        · -- Large case: |A||B| ≥ 2^13 K^5
          have h_large : (A.card : ℝ) * (B.card : ℝ) ≥ (2 : ℝ)^13 * (K : ℝ)^5 := by linarith
          set P_real : ℝ := (A.card : ℝ) * (B.card : ℝ) / (2^12 * (K : ℝ)^5) with hP_real
          have hP2 : P_real ≥ 2 := by
            rw [hP_real]
            have h : (A.card : ℝ) * (B.card : ℝ) ≥ (2 : ℝ)^13 * (K : ℝ)^5 := h_large
            have hK5_pos : (K : ℝ)^5 > 0 := by positivity
            calc
              (A.card : ℝ) * (B.card : ℝ) / (2^12 * (K : ℝ)^5)
                ≥ ((2 : ℝ)^13 * (K : ℝ)^5) / (2^12 * (K : ℝ)^5) := by gcongr
              _ = 2 := by
                field_simp [hK5_pos.ne'] <;> norm_num
          let p_int : ℤ := ⌊P_real⌋
          have h_pint_nonneg : 0 ≤ p_int := by
            have h1 : P_real ≥ 2 := hP2
            have h2 : (0 : ℝ) ≤ P_real := by linarith
            exact Int.floor_nonneg.mpr h2
          let p : ℕ := Int.toNat p_int
          have h_coe_int : (p : ℤ) = p_int := Int.toNat_of_nonneg h_pint_nonneg
          have hp_coe : (p : ℝ) = (p_int : ℝ) := by
            exact_mod_cast h_coe_int
          have hp_pos : 0 < p := by
            have h1 : P_real ≥ 2 := hP2
            have h1' : (↑(1 : ℤ) : ℝ) ≤ P_real := by
              exact_mod_cast (show (1 : ℝ) ≤ P_real from by linarith)
            have h2 : (1 : ℤ) ≤ p_int := Int.le_floor.mpr h1'
            have h3 : (p : ℤ) ≥ 1 := by
              rw [h_coe_int] <;> exact h2
            exact_mod_cast h3
          have hp_lower : (p : ℝ) ≥ P_real / 2 := by
            have h1 : (p_int : ℝ) ≥ P_real - 1 := Int.sub_one_lt_floor P_real |>.le
            have h2 : P_real - 1 ≥ P_real / 2 := by linarith
            have h3 : (p : ℝ) = (p_int : ℝ) := hp_coe
            rw [h3]
            linarith
          have hP_lower : (p : ℝ) ≥ (A.card : ℝ) * (B.card : ℝ) / (2^13 * (K : ℝ)^5) := by
            have h3 : P_real / 2 = (A.card : ℝ) * (B.card : ℝ) / (2^13 * (K : ℝ)^5) := by
              rw [hP_real] <;> ring
            rw [h3] at hp_lower
            exact hp_lower
          have h_paths_nat : ∀ a ∈ A', ∀ b ∈ B', p ≤ path3 Gph' a b := by
            intro a ha b hb
            have h4 : (path3 Gph' a b : ℝ) ≥ P_real := h_path a ha b hb
            have h5 : (p_int : ℝ) ≤ P_real := Int.floor_le P_real
            have h6 : (p : ℝ) ≤ P_real := by
              rw [hp_coe] <;> exact h5
            have h7 : (p : ℝ) ≤ (path3 Gph' a b : ℝ) := le_trans h6 h4
            exact_mod_cast h7
          set S' : Finset G := restrictedSum A B Gph' with hS'
          have hS'_sub_S : S' ⊆ S := by
            apply Finset.image_subset_image _
            exact prunedGraph_subset
          have hS'_card : S'.card ≤ S.card := Finset.card_le_card hS'_sub_S
          have h_bound : p * (A' + B').card ≤ S'.card ^ 3 :=
            path_to_sumset_bound hA'_sub hB'_sub S' rfl p hp_pos h_paths_nat
          have h6 : (p : ℝ) * ((A' + B').card : ℝ) ≤ (S'.card : ℝ)^3 := by exact_mod_cast h_bound
          have h7 : ((A' + B').card : ℝ) ≤ (S'.card : ℝ)^3 / (p : ℝ) := by
            have hp_pos' : (p : ℝ) > 0 := by exact_mod_cast hp_pos
            calc
              ((A' + B').card : ℝ)
                = ((p : ℝ) * ((A' + B').card : ℝ)) / (p : ℝ) := by
                  field_simp [hp_pos'.ne'] <;> ring
              _ ≤ (S'.card : ℝ)^3 / (p : ℝ) := by gcongr
          set x : ℝ := (A.card : ℝ) * (B.card : ℝ) with hx
          have hx_pos : 0 < x := by positivity
          have h9 : (S'.card : ℝ) ≤ (K : ℝ) * Real.sqrt x := by
            calc
              (S'.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hS'_card
              _ ≤ (K : ℝ) * Real.sqrt x := hS_card
          have h10 : (S'.card : ℝ)^3 ≤ (K : ℝ)^3 * x * Real.sqrt x := by
            calc
              (S'.card : ℝ)^3
                ≤ ((K : ℝ) * Real.sqrt x) ^ 3 := by gcongr
              _ = (K : ℝ)^3 * (Real.sqrt x) ^ 3 := by ring
              _ = (K : ℝ)^3 * (x * Real.sqrt x) := by
                have h11 : (Real.sqrt x) ^ 3 = x * Real.sqrt x := by
                  have h12 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by positivity)
                  calc
                    (Real.sqrt x) ^ 3 = (Real.sqrt x) ^ 2 * Real.sqrt x := by ring
                    _ = x * Real.sqrt x := by rw [h12] <;> ring
                rw [h11] <;> ring
              _ = (K : ℝ)^3 * x * Real.sqrt x := by ring
          have h13 : (p : ℝ) ≥ x / (2^13 * (K : ℝ)^5) := hP_lower
          have h14 : (S'.card : ℝ)^3 / (p : ℝ) ≤
              (2 : ℝ)^13 * (K : ℝ)^8 * Real.sqrt x := by
            calc
              (S'.card : ℝ)^3 / (p : ℝ)
                ≤ ((K : ℝ)^3 * x * Real.sqrt x) / (x / (2^13 * (K : ℝ)^5)) := by gcongr
              _ = (2 : ℝ)^13 * (K : ℝ)^8 * Real.sqrt x := by
                field_simp [hx_pos.ne'] <;> ring
          have h15 : (2 : ℝ)^13 * (K : ℝ)^8 ≤ (2 : ℝ)^12 * (K : ℝ)^10 := by
            have h16 : (K : ℝ) ≥ 2 := by exact_mod_cast hK2
            have h17 : (2 : ℝ) ≤ (K : ℝ)^2 := by nlinarith
            have h18 : (2 : ℝ)^13 * (K : ℝ)^8 = (2 : ℝ)^12 * (2 : ℝ) * (K : ℝ)^8 := by ring
            rw [h18]
            have h19 : (2 : ℝ) * (K : ℝ)^8 ≤ (K : ℝ)^2 * (K : ℝ)^8 := by gcongr
            nlinarith
          have h8 : (S'.card : ℝ)^3 / (p : ℝ) ≤
              (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt x := by
            calc
              (S'.card : ℝ)^3 / (p : ℝ)
                ≤ (2 : ℝ)^13 * (K : ℝ)^8 * Real.sqrt x := h14
              _ ≤ (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt x := by
                gcongr
                <;> exact h15
          have h_final : ((A' + B').card : ℝ) ≤
              (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
            simpa [hx] using le_trans h7 h8
          exact ⟨A', B', hA'_sub, hB'_sub, hA'_weak, hB'_weak, h_final⟩

end Main

end AdditiveCombinatorics.BSG
