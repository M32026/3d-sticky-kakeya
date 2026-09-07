module

/-
  Covering number utility lemmas.

  Provides union bounds, Lipschitz image bounds, and bounded set finiteness
  for `Metric.externalCoveringNumber`, used throughout the discretised
  Furstenberg estimate proof.

  Whiteprint node: `covering_utils`
  Dependencies: none
-/
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace DiscretisedFurstenbergEstimate.CoveringUtils

section Union

variable {X : Type*} [PseudoMetricSpace X] {ε : NNReal}

/-- Existence of a cover attaining the external covering number when finite. -/
lemma exists_external_cover_eq {A : Set X}
    (h : Metric.externalCoveringNumber ε A < ⊤) :
    ∃ (C : Set X), Metric.IsCover ε A C ∧ C.encard = Metric.externalCoveringNumber ε A := by
  let n : ENat := Metric.externalCoveringNumber ε A
  have hn : n < ⊤ := h
  have h_ne : n ≠ ⊤ := hn.ne
  have h_exists_nat : ∃ (k : ℕ), n = ↑k := by
    have h : ∃ (m : ℕ), (↑m : ENat) = n := ENat.ne_top_iff_exists.mp h_ne
    rcases h with ⟨m, hm⟩
    exact ⟨m, hm.symm⟩
  rcases h_exists_nat with ⟨k, hk⟩
  have h_ge : ∀ (C : Set X), Metric.IsCover ε A C → n ≤ C.encard := by
    intro C hC
    exact Metric.IsCover.externalCoveringNumber_le_encard hC
  have h_exists : ∃ (C : Set X), Metric.IsCover ε A C ∧ C.encard ≤ n := by
    by_contra h2
    push Not at h2
    have h3 : ∀ (C : Set X), Metric.IsCover ε A C → n + 1 ≤ C.encard := by
      intro C hC
      have h4 : n < C.encard := h2 C hC
      rw [hk] at h4
      cases' e : C.encard with m
      · exact le_top
      · have h51 : (↑k : ENat) < (↑m : ENat) := by
          rw [e] at h4; exact h4
        have h5 : k < m := by exact_mod_cast h51
        have h6 : k + 1 ≤ m := by linarith
        have h7 : (↑(k + 1) : ENat) ≤ (↑m : ENat) := by exact_mod_cast h6
        simpa [e, hk] using h7
    have h4 : n + 1 ≤ n := by
      have h5 : n + 1 ≤ Metric.externalCoveringNumber ε A := by
        simp only [Metric.externalCoveringNumber, le_iInf_iff]
        intro C
        intro hC
        exact h3 C hC
      exact h5
    rw [hk] at h4
    have h8 : (↑(k + 1) : ENat) ≤ (↑k : ENat) := h4
    have h9 : k + 1 ≤ k := by exact_mod_cast h8
    linarith
  rcases h_exists with ⟨C, hC, hle⟩
  have hge : n ≤ C.encard := h_ge C hC
  exact ⟨C, hC, le_antisymm hle hge⟩

/-- Binary union bound for external covering numbers. -/
lemma externalCoveringNumber_union {A B : Set X} :
    Metric.externalCoveringNumber ε (A ∪ B) ≤
      Metric.externalCoveringNumber ε A + Metric.externalCoveringNumber ε B := by
  by_cases hA : Metric.externalCoveringNumber ε A = ⊤
  · rw [hA]; simp
  by_cases hB : Metric.externalCoveringNumber ε B = ⊤
  · rw [hB]; simp
  have hfinA : Metric.externalCoveringNumber ε A < ⊤ := by
    exact lt_top_iff_ne_top.mpr hA
  have hfinB : Metric.externalCoveringNumber ε B < ⊤ := by
    exact lt_top_iff_ne_top.mpr hB
  rcases exists_external_cover_eq hfinA with ⟨CA, hCA, h_eqA⟩
  rcases exists_external_cover_eq hfinB with ⟨CB, hCB, h_eqB⟩
  have h_union : Metric.IsCover ε (A ∪ B) (CA ∪ CB) := hCA.union hCB
  have h1 : Metric.externalCoveringNumber ε (A ∪ B) ≤ (CA ∪ CB).encard :=
    Metric.IsCover.externalCoveringNumber_le_encard h_union
  have h2 : (CA ∪ CB).encard ≤ CA.encard + CB.encard := Set.encard_union_le CA CB
  have h3 : Metric.externalCoveringNumber ε (A ∪ B) ≤ CA.encard + CB.encard := h1.trans h2
  rw [h_eqA, h_eqB] at h3
  exact h3

/-- Finite union bound for external covering numbers. -/
lemma externalCoveringNumber_biUnion {ι : Type*} [DecidableEq ι] {s : Finset ι} {A : ι → Set X} :
    Metric.externalCoveringNumber ε (⋃ i ∈ s, A i) ≤
      ∑ i ∈ s, Metric.externalCoveringNumber ε (A i) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    let U : Set X := ⋃ i ∈ s, A i
    have h_set : (⋃ i ∈ (insert a s), A i) = A a ∪ U := by
      ext x; simp [ha, U] <;> tauto
    rw [h_set, Finset.sum_insert ha]
    have h : Metric.externalCoveringNumber ε (A a ∪ U) ≤
        Metric.externalCoveringNumber ε (A a) + Metric.externalCoveringNumber ε U :=
      externalCoveringNumber_union
    exact h.trans (add_le_add_right ih _)

end Union

section Lipschitz

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- External covering number of a Lipschitz image. -/
lemma externalCoveringNumber_image_lipschitz
    {f : X → Y} {K : NNReal} (hf : LipschitzWith K f)
    {ε : NNReal} {A : Set X} :
    Metric.externalCoveringNumber (K * ε) (f '' A) ≤
      Metric.externalCoveringNumber ε A := by
  apply le_iInf
  intro C
  apply le_iInf
  intro hC
  have h1 : Metric.IsCover (K * ε) (f '' A) (f '' C) := hC.image_lipschitz hf
  have h2 : Metric.externalCoveringNumber (K * ε) (f '' A) ≤ (f '' C).encard :=
    Metric.IsCover.externalCoveringNumber_le_encard h1
  have h3 : (f '' C).encard ≤ C.encard := Set.encard_image_le f C
  exact h2.trans h3

/-- External covering number is invariant under isometric equivalences. -/
lemma externalCoveringNumber_image_isometryEquiv
    (f : X ≃ᵢ Y) {ε : NNReal} {A : Set X} :
    Metric.externalCoveringNumber ε (f '' A) = Metric.externalCoveringNumber ε A := by
  have h1 : LipschitzWith (1 : NNReal) f :=
    LipschitzWith.of_dist_le_mul (fun x y => by
      have h_dist : dist (f x) (f y) = dist x y := f.dist_eq x y
      rw [h_dist] <;> simp)
  have h2 : LipschitzWith (1 : NNReal) f.symm :=
    LipschitzWith.of_dist_le_mul (fun x y => by
      have h_dist : dist (f.symm x) (f.symm y) = dist x y := f.symm.dist_eq x y
      rw [h_dist] <;> simp)
  have h_forward : Metric.externalCoveringNumber ε (f '' A) ≤ Metric.externalCoveringNumber ε A := by
    have h_main : Metric.externalCoveringNumber ((1 : NNReal) * ε) (f '' A) ≤
        Metric.externalCoveringNumber ε A :=
      externalCoveringNumber_image_lipschitz (hf := h1)
    have h_eq : (1 : NNReal) * ε = ε := by simp
    rw [h_eq] at h_main
    exact h_main
  have h3 : f.symm '' (f '' A) = A := by ext z; simp
  have h_backward : Metric.externalCoveringNumber ε A ≤ Metric.externalCoveringNumber ε (f '' A) := by
    have h4 : Metric.externalCoveringNumber ((1 : NNReal) * ε) (f.symm '' (f '' A)) ≤
        Metric.externalCoveringNumber ε (f '' A) :=
      externalCoveringNumber_image_lipschitz (hf := h2)
    have h_eq : (1 : NNReal) * ε = ε := by simp
    rw [h_eq] at h4
    rw [h3] at h4
    exact h4
  exact le_antisymm h_forward h_backward

/-- Inverse covering bound: if `f` is `K'`-expanding on `S` (i.e. its inverse
    is `K'`-Lipschitz on the image), then a `ε`-cover of `f '' S` gives a
    `2*K'*ε`-cover of `S`. The factor 2 comes from choosing image points
    near cover centers. -/
lemma externalCoveringNumber_inverse_image
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {S : Set X} {f : X → Y} {K' : NNReal} {ε : NNReal}
    (hfinv : ∀ x y, x ∈ S → y ∈ S → dist x y ≤ (K' : ℝ) * dist (f x) (f y))
    (hS_nonempty : S.Nonempty)
    (hε_pos : 0 < ε) :
    Metric.externalCoveringNumber (2 * K' * ε) S ≤
      Metric.externalCoveringNumber ε (f '' S) := by
  classical
  let relevant (y : Y) : Prop := (Metric.closedBall y ε : Set Y) ∩ f '' S ≠ ∅
  let choose_point (y : Y) (hy : relevant y) : Y :=
    Classical.choose (Set.nonempty_iff_ne_empty.mpr hy)
  have hchoose_spec : ∀ (y : Y) (hy : relevant y),
      choose_point y hy ∈ (Metric.closedBall y ε : Set Y) ∩ f '' S := by
    intro y hy
    exact Classical.choose_spec (Set.nonempty_iff_ne_empty.mpr hy)
  let preimage (z : Y) (hz : z ∈ f '' S) : X := Classical.choose hz
  have hpreimage_spec : ∀ (z : Y) (hz : z ∈ f '' S),
      preimage z hz ∈ S ∧ f (preimage z hz) = z := by
    intro z hz
    exact Classical.choose_spec hz
  let h : Y → X := fun y =>
    if hrel : relevant y then
      preimage (choose_point y hrel) (hchoose_spec y hrel).2
    else hS_nonempty.some
  apply le_iInf
  intro C
  apply le_iInf
  intro hC
  let C' : Set X := h '' C
  have hC'_cover : Metric.IsCover (2 * K' * ε) S C' := by
    intro x hx
    have hfx : f x ∈ f '' S := ⟨x, hx, rfl⟩
    rcases hC hfx with ⟨y, hyC, hdist⟩
    have hdist' : edist (f x) y ≤ ↑ε := by simpa [Set.mem_setOf_eq] using hdist
    have h_fxy : dist (f x) y ≤ ε := by
      have h : edist (f x) y ≤ ↑ε := hdist'
      rw [edist_dist] at h
      exact_mod_cast h
    have h_fxy_ball : f x ∈ Metric.closedBall y ε := by
      simpa [Metric.mem_closedBall] using h_fxy
    have hrel : relevant y := by
      dsimp only [relevant]
      intro h
      have hmem : f x ∈ (Metric.closedBall y ε : Set Y) ∩ f '' S := ⟨h_fxy_ball, hfx⟩
      rw [h] at hmem
      simpa using hmem
    let z := choose_point y hrel
    have hz_in_ball : z ∈ Metric.closedBall y ε := (hchoose_spec y hrel).1
    have hz_in_image : z ∈ f '' S := (hchoose_spec y hrel).2
    let x' := preimage z hz_in_image
    have hx'_in_S : x' ∈ S := (hpreimage_spec z hz_in_image).1
    have hfx' : f x' = z := (hpreimage_spec z hz_in_image).2
    have hx'_in_C' : x' ∈ C' := by
      have h_eq : h y = x' := by
        simp [h, hrel, hfx'] <;> rfl
      exact ⟨y, hyC, h_eq⟩
    have h_yz_dist : dist z y ≤ ε := by
      simpa [Metric.mem_closedBall] using hz_in_ball
    have h_yz : dist y z ≤ ε := by
      rw [dist_comm]; exact h_yz_dist
    have h_dist1 : dist (f x) z ≤ 2 * ε := by
      linarith [dist_triangle (f x) y z]
    have h_dist2 : dist x x' ≤ (K' : ℝ) * dist (f x) (f x') := hfinv x x' hx hx'_in_S
    rw [hfx'] at h_dist2
    have h_dist3 : dist x x' ≤ 2 * (K' : ℝ) * ε := by
      calc dist x x' ≤ (K' : ℝ) * dist (f x) z := h_dist2
           _ ≤ (K' : ℝ) * (2 * ε) := by gcongr
           _ = 2 * (K' : ℝ) * ε := by ring
    have h_dist4 : edist x x' ≤ ↑(2 * K' * ε) := by
      rw [edist_dist]
      have h_pos : 0 ≤ (↑(2 * K' * ε) : ℝ) := by positivity
      have h_coe : (↑(2 * K' * ε) : ENNReal) = ENNReal.ofReal (↑(2 * K' * ε) : ℝ) := by
        simp
      rw [h_coe]
      exact (ENNReal.ofReal_le_ofReal_iff h_pos).mpr h_dist3
    exact ⟨x', hx'_in_C', h_dist4⟩
  have h1 : Metric.externalCoveringNumber (2 * K' * ε) S ≤ C'.encard :=
    Metric.IsCover.externalCoveringNumber_le_encard hC'_cover
  have h2 : C'.encard ≤ C.encard := by
    simpa [C'] using Set.encard_image_le h C
  exact h1.trans h2

end Lipschitz

section EuclideanPlane

abbrev EuclideanPlane : Type := EuclideanSpace ℝ (Fin 2)

/-- Bounded subsets of the Euclidean plane have finite external covering number
for any positive radius. -/
lemma externalCoveringNumber_bounded {ε : NNReal} (hε : 0 < ε)
    {A : Set EuclideanPlane} (hA : Bornology.IsBounded A) :
    Metric.externalCoveringNumber ε A < ⊤ := by
  by_cases hAempty : A = ∅
  · rw [hAempty]; simp
  · have h_main : ∃ (r : ℝ), 0 ≤ r ∧ A ⊆ Metric.closedBall (0 : EuclideanPlane) r := by
      have h : ∃ (r : ℝ), A ⊆ Metric.closedBall (0 : EuclideanPlane) r :=
        (Metric.isBounded_iff_subset_closedBall (0 : EuclideanPlane)).mp hA
      rcases h with ⟨r, hsub⟩
      by_cases hr : 0 ≤ r
      · exact ⟨r, hr, hsub⟩
      · have hneg : r < 0 := by linarith
        have h_empty : Metric.closedBall (0 : EuclideanPlane) r = ∅ := by
          ext z
          simp [Metric.mem_closedBall, hneg] <;> linarith
        rw [h_empty] at hsub
        exfalso
        exact hAempty (Set.subset_empty_iff.mp hsub)
    rcases h_main with ⟨r, hr, hsub⟩
    have hcompact : IsCompact (Metric.closedBall (0 : EuclideanPlane) r) :=
      isCompact_closedBall (0 : EuclideanPlane) r
    have hne : ε ≠ 0 := hε.ne'
    have hfin : ∃ (N : Set EuclideanPlane), N ⊆ Metric.closedBall (0 : EuclideanPlane) r ∧
        N.Finite ∧ Metric.IsCover ε (Metric.closedBall (0 : EuclideanPlane) r) N :=
      Metric.exists_finite_isCover_of_isCompact hne hcompact
    rcases hfin with ⟨N, _, hNfin, hNcover⟩
    have hcoverA : Metric.IsCover ε A N := hNcover.anti hsub
    have h1 : Metric.externalCoveringNumber ε A ≤ N.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hcoverA
    have h2 : N.encard < ⊤ := Set.Finite.encard_lt_top hNfin
    exact h1.trans_lt h2

end EuclideanPlane

end DiscretisedFurstenbergEstimate.CoveringUtils
