module

/-
# Simple Normalization — Unit-Chunk Selection with Grid Preservation and Fiber Transport

Uses `unit_chunk_pigeonhole_2d` for densest unit-chunk selection, then adds:
- δ-grid preservation under integer translation (for dyadic δ)
- Nonempty guarantee for selected chunk
- Fiber transport for per-direction projection families

## Key results
- `int_translate_preserves_grid1d`: integer translation preserves dyadic δ-grid in 1D
- `normalize_chunk_grid`: full normalization with grid + nonempty + density
- `transport_projection_families`: transports per-direction projection sets under graph translation
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProductLikeIncidence.RescalingRestructuring
public import MyLeanRepo.ProductLikeIncidence.DeltaSetTranslation
public import MyLeanRepo.ProductLikeSetBasics
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Finset ENNReal Bornology Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- For dyadic δ, integer translation preserves the δ-grid in 1D. -/
lemma int_translate_preserves_grid1d {δ : ℝ} (hδ_dyadic : δ ∈ dyadicScales)
    (k : ℤ) {S : Set ℝ}
    (hS_grid : ∀ x ∈ S, ∃ m : ℤ, x = δ * (m : ℝ)) :
    ∀ y ∈ (fun x : ℝ => x - (k : ℝ)) '' S, ∃ m : ℤ, y = δ * (m : ℝ) := by
  rcases hδ_dyadic with ⟨n, hδ_eq⟩
  let kk : ℤ := k * (2 ^ n)
  have hk : (k : ℝ) = δ * (kk : ℝ) := by
    rw [hδ_eq]; simp [kk, zpow_neg] <;> field_simp
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  rcases hS_grid x hx with ⟨m, hm⟩
  refine ⟨m - kk, ?_⟩
  rw [hm, hk, Int.cast_sub] ; ring

/-- Unit-chunk normalization with δ-grid preservation and nonempty guarantee. -/
lemma normalize_chunk_grid
    {δ R : ℝ} (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hR_pos : 0 < R) (hR_int : ∃ (c : ℤ), R = (c : ℝ))
    {S1 S2 : Set ℝ} {Gamma : Set (EuclideanSpace ℝ (Fin 2))}
    (hS1_bdd : ∀ x ∈ S1, |x| ≤ R)
    (hS2_bdd : ∀ x ∈ S2, |x| ≤ R)
    (hS1_fin : Set.Finite S1) (hS2_fin : Set.Finite S2)
    (hGamma_sub : ∀ p ∈ Gamma, p 0 ∈ S1 ∧ p 1 ∈ S2)
    (hGamma_fin : Set.Finite Gamma)
    (hS1_grid : ∀ x ∈ S1, ∃ k : ℤ, x = δ * (k : ℝ))
    (hS2_grid : ∀ x ∈ S2, ∃ k : ℤ, x = δ * (k : ℝ))
    (hS1_nonempty : S1.Nonempty) (hS2_nonempty : S2.Nonempty)
    {c_dense : ENNReal} (hc_dense_pos : 0 < c_dense)
    (h_density : c_dense * Nreal δ S1 * Nreal δ S2 ≤
        ENat.toENNReal (dyadicCoveringNumber δ Gamma)) :
    ∃ (k j : ℤ) (B1 B2 : Set ℝ)
      (G' : Set (EuclideanSpace ℝ (Fin 2))),
      B1 ⊆ productLikeUnitGrid δ ∧
      B2 ⊆ productLikeUnitGrid δ ∧
      B1.Nonempty ∧ B2.Nonempty ∧
      G'.Finite ∧
      (∀ p ∈ G', ∀ i : Fin 2, ∃ m : ℤ, p i = δ * (m : ℝ)) ∧
      (∀ p ∈ G', p 0 ∈ B1 ∧ p 1 ∈ B2) ∧
      c_dense * Nreal δ B1 * Nreal δ B2 ≤
        ENat.toENNReal (dyadicCoveringNumber δ G') ∧
      B1 = Set.image (fun x => x - (k : ℝ)) (unitChunk S1 k) ∧
      B2 = Set.image (fun x => x - (j : ℝ)) (unitChunk S2 j) := by
  rcases hR_int with ⟨cR, hR_eq⟩
  have hcR_pos : 0 < cR := by
    have h : (cR : ℝ) > 0 := by linarith [hR_eq]
    exact_mod_cast h
  let K : Finset ℤ := Finset.Icc (-cR) cR
  let K2 : Finset (ℤ × ℤ) := K ×ˢ K

  -- Chunk index in K for any x in [-R,R]
  have h_chunk_in_K : ∀ (x : ℝ), |x| ≤ R → Int.floor x ∈ K := by
    intro x h_abs
    have h1 : -R ≤ x := (abs_le.mp h_abs).1
    have h2 : x ≤ R := (abs_le.mp h_abs).2
    let k : ℤ := Int.floor x
    have hk_low : -cR ≤ k := by
      have h4 : (-(cR : ℝ)) ≤ x := by rw [hR_eq] at h1; exact h1
      have h5 : ((-cR : ℤ) : ℝ) ≤ x := by exact_mod_cast h4
      exact Int.le_floor.mpr h5
    have hk_high : k ≤ cR := by
      have h4 : (k : ℝ) ≤ x := Int.floor_le x
      have h5 : x ≤ (cR : ℝ) := by rw [hR_eq] at h2; exact h2
      have h6 : (k : ℝ) ≤ (cR : ℝ) := by linarith
      exact_mod_cast h6
    simp only [K, Finset.mem_Icc]; exact ⟨hk_low, hk_high⟩

  -- Finset-valued chunk functions
  let chunk1Fin (k : ℤ) : Finset ℝ :=
    if hk : k ∈ K then
      (hS1_fin.subset (fun {x : ℝ} (hx : x ∈ unitChunk S1 k) => hx.1)).toFinset
    else ∅
  let chunk2Fin (j : ℤ) : Finset ℝ :=
    if hj : j ∈ K then
      (hS2_fin.subset (fun {x : ℝ} (hx : x ∈ unitChunk S2 j) => hx.1)).toFinset
    else ∅
  let chunkGFin (kj : ℤ × ℤ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
    if hkj : kj ∈ K2 then
      (hGamma_fin.subset (fun {p} (hp : p ∈ chunkGraph Gamma S1 S2 kj.1 kj.2) => hp.1)).toFinset
    else ∅

  have h_chunk1Fin_mem : ∀ k ∈ K, ∀ x, x ∈ chunk1Fin k ↔ x ∈ unitChunk S1 k := by
    intro k hk x
    have h_eq : chunk1Fin k = (hS1_fin.subset (fun (x : ℝ) (hx : x ∈ unitChunk S1 k) => hx.1)).toFinset :=
      dif_pos hk
    rw [h_eq]; simp [Set.Finite.mem_toFinset]
  have h_chunk2Fin_mem : ∀ j ∈ K, ∀ x, x ∈ chunk2Fin j ↔ x ∈ unitChunk S2 j := by
    intro j hj x
    have h_eq : chunk2Fin j = (hS2_fin.subset (fun (x : ℝ) (hx : x ∈ unitChunk S2 j) => hx.1)).toFinset :=
      dif_pos hj
    rw [h_eq]; simp [Set.Finite.mem_toFinset]
  have h_chunkGFin_mem : ∀ kj ∈ K2, ∀ p, p ∈ chunkGFin kj ↔ p ∈ chunkGraph Gamma S1 S2 kj.1 kj.2 := by
    intro kj hkj p
    have h_eq : chunkGFin kj = (hGamma_fin.subset (fun (p : _) (hp : p ∈ chunkGraph Gamma S1 S2 kj.1 kj.2) => hp.1)).toFinset :=
      dif_pos hkj
    rw [h_eq]; simp [Set.Finite.mem_toFinset, chunkGraph]

  -- Cardinality sums
  have h_card1 : hS1_fin.toFinset.card = ∑ k ∈ K, (chunk1Fin k).card := by
    have h_disj : ∀ k1 ∈ K, ∀ k2 ∈ K, k1 ≠ k2 → Disjoint (chunk1Fin k1) (chunk1Fin k2) := by
      intro k1 hk1 k2 hk2 hne
      simp only [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 : x ∈ unitChunk S1 k1 := (h_chunk1Fin_mem k1 hk1 x).mp hx1
      have h2 : x ∈ unitChunk S1 k2 := (h_chunk1Fin_mem k2 hk2 x).mp hx2
      have hfl1 : Int.floor x = k1 := by
        rw [Int.floor_eq_iff] <;> exact ⟨h1.2.1, by exact h1.2.2⟩
      have hfl2 : Int.floor x = k2 := by
        rw [Int.floor_eq_iff] <;> exact ⟨h2.2.1, by exact h2.2.2⟩
      exact hne (hfl1.symm.trans hfl2)
    have h : (K.biUnion chunk1Fin).card = ∑ k ∈ K, (chunk1Fin k).card :=
      Finset.card_biUnion h_disj
    have h2 : K.biUnion chunk1Fin = hS1_fin.toFinset := by
      ext x
      simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨k, hk, hx⟩
        have h3 : x ∈ unitChunk S1 k := (h_chunk1Fin_mem k hk x).mp hx
        exact h3.1
      · intro hx
        let k := Int.floor x
        have hkK : k ∈ K := h_chunk_in_K x (hS1_bdd x hx)
        have h1 : (k : ℝ) ≤ x := Int.floor_le x
        have h2 : x < (k : ℝ) + 1 := Int.lt_floor_add_one x
        have hxk : x ∈ unitChunk S1 k := ⟨hx, ⟨h1, h2⟩⟩
        exact ⟨k, hkK, (h_chunk1Fin_mem k hkK x).mpr hxk⟩
    rw [←h2, h]
  have h_card2 : hS2_fin.toFinset.card = ∑ j ∈ K, (chunk2Fin j).card := by
    have h_disj : ∀ j1 ∈ K, ∀ j2 ∈ K, j1 ≠ j2 → Disjoint (chunk2Fin j1) (chunk2Fin j2) := by
      intro j1 hj1 j2 hj2 hne
      simp only [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 : x ∈ unitChunk S2 j1 := (h_chunk2Fin_mem j1 hj1 x).mp hx1
      have h2 : x ∈ unitChunk S2 j2 := (h_chunk2Fin_mem j2 hj2 x).mp hx2
      have hfl1 : Int.floor x = j1 := by
        rw [Int.floor_eq_iff] <;> exact ⟨h1.2.1, by exact h1.2.2⟩
      have hfl2 : Int.floor x = j2 := by
        rw [Int.floor_eq_iff] <;> exact ⟨h2.2.1, by exact h2.2.2⟩
      exact hne (hfl1.symm.trans hfl2)
    have h : (K.biUnion chunk2Fin).card = ∑ j ∈ K, (chunk2Fin j).card :=
      Finset.card_biUnion h_disj
    have h2 : K.biUnion chunk2Fin = hS2_fin.toFinset := by
      ext x
      simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨j, hj, hx⟩
        have h3 : x ∈ unitChunk S2 j := (h_chunk2Fin_mem j hj x).mp hx
        exact h3.1
      · intro hx
        let j := Int.floor x
        have hjK : j ∈ K := h_chunk_in_K x (hS2_bdd x hx)
        have h1 : (j : ℝ) ≤ x := Int.floor_le x
        have h2 : x < (j : ℝ) + 1 := Int.lt_floor_add_one x
        have hxj : x ∈ unitChunk S2 j := ⟨hx, ⟨h1, h2⟩⟩
        exact ⟨j, hjK, (h_chunk2Fin_mem j hjK x).mpr hxj⟩
    rw [←h2, h]
  have h_cardG : hGamma_fin.toFinset.card = ∑ kj ∈ K2, (chunkGFin kj).card := by
    have h_disj : ∀ kj1 ∈ K2, ∀ kj2 ∈ K2, kj1 ≠ kj2 → Disjoint (chunkGFin kj1) (chunkGFin kj2) := by
      intro kj1 hk1 kj2 hk2 hne
      simp only [Finset.disjoint_left]
      intro p hp1 hp2
      have h1 : p ∈ chunkGraph Gamma S1 S2 kj1.1 kj1.2 := (h_chunkGFin_mem kj1 hk1 p).mp hp1
      have h2 : p ∈ chunkGraph Gamma S1 S2 kj2.1 kj2.2 := (h_chunkGFin_mem kj2 hk2 p).mp hp2
      have hfl1 : Int.floor (p 0) = kj1.1 := by
        rw [Int.floor_eq_iff] <;> exact ⟨h1.2.1.2.1, by exact h1.2.1.2.2⟩
      have hfl2 : Int.floor (p 0) = kj2.1 := by
        rw [Int.floor_eq_iff] <;> exact ⟨h2.2.1.2.1, by exact h2.2.1.2.2⟩
      have h : kj1.1 = kj2.1 := hfl1.symm.trans hfl2
      have hfl3 : Int.floor (p 1) = kj1.2 := by
        rw [Int.floor_eq_iff] <;> exact ⟨h1.2.2.2.1, by exact h1.2.2.2.2⟩
      have hfl4 : Int.floor (p 1) = kj2.2 := by
        rw [Int.floor_eq_iff] <;> exact ⟨h2.2.2.2.1, by exact h2.2.2.2.2⟩
      have h' : kj1.2 = kj2.2 := hfl3.symm.trans hfl4
      exact hne (Prod.ext h h')
    have h : (K2.biUnion chunkGFin).card = ∑ kj ∈ K2, (chunkGFin kj).card :=
      Finset.card_biUnion h_disj
    have h2 : K2.biUnion chunkGFin = hGamma_fin.toFinset := by
      ext p
      simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨kj, hkj, hp⟩
        have h3 : p ∈ chunkGraph Gamma S1 S2 kj.1 kj.2 := (h_chunkGFin_mem kj hkj p).mp hp
        exact h3.1
      · intro hx
        have hpsub : p 0 ∈ S1 ∧ p 1 ∈ S2 := hGamma_sub p hx
        let k := Int.floor (p 0)
        let j := Int.floor (p 1)
        have hkK : k ∈ K := h_chunk_in_K (p 0) (hS1_bdd (p 0) hpsub.1)
        have hjK : j ∈ K := h_chunk_in_K (p 1) (hS2_bdd (p 1) hpsub.2)
        have hkj : (k, j) ∈ K2 := Finset.mem_product.mpr ⟨hkK, hjK⟩
        have h1 : (k : ℝ) ≤ p 0 := Int.floor_le (p 0)
        have h2 : p 0 < (k : ℝ) + 1 := Int.lt_floor_add_one (p 0)
        have h3 : (j : ℝ) ≤ p 1 := Int.floor_le (p 1)
        have h4 : p 1 < (j : ℝ) + 1 := Int.lt_floor_add_one (p 1)
        have hpkj : p ∈ chunkGraph Gamma S1 S2 k j := ⟨hx, ⟨⟨hpsub.1, ⟨h1, h2⟩⟩, ⟨hpsub.2, ⟨h3, h4⟩⟩⟩⟩
        exact ⟨(k, j), hkj, (h_chunkGFin_mem (k, j) hkj p).mpr hpkj⟩
    rw [←h2, h]

  -- ENNReal sums
  have h_sum1 : ENat.toENNReal S1.encard = ∑ k ∈ K, ENat.toENNReal (unitChunk S1 k).encard := by
    have h1 : ENat.toENNReal S1.encard = (↑hS1_fin.toFinset.card : ENNReal) := by
      rw [hS1_fin.encard_eq_coe_toFinset_card] <;> rfl
    rw [h1, h_card1, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hfin : Set.Finite (unitChunk S1 k) := hS1_fin.subset (fun x hx => hx.1)
    have h_eq : (chunk1Fin k).card = hfin.toFinset.card := by
      have h : chunk1Fin k = hfin.toFinset := by simp [chunk1Fin, hk]
      rw [h]
    rw [h_eq, hfin.encard_eq_coe_toFinset_card] <;> rfl
  have h_sum2 : ENat.toENNReal S2.encard = ∑ j ∈ K, ENat.toENNReal (unitChunk S2 j).encard := by
    have h1 : ENat.toENNReal S2.encard = (↑hS2_fin.toFinset.card : ENNReal) := by
      rw [hS2_fin.encard_eq_coe_toFinset_card] <;> rfl
    rw [h1, h_card2, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hfin : Set.Finite (unitChunk S2 j) := hS2_fin.subset (fun x hx => hx.1)
    have h_eq : (chunk2Fin j).card = hfin.toFinset.card := by
      have h : chunk2Fin j = hfin.toFinset := by simp [chunk2Fin, hj]
      rw [h]
    rw [h_eq, hfin.encard_eq_coe_toFinset_card] <;> rfl
  have h_sumG : ENat.toENNReal Gamma.encard = ∑ kj ∈ K2, ENat.toENNReal (chunkGraph Gamma S1 S2 kj.1 kj.2).encard := by
    have h1 : ENat.toENNReal Gamma.encard = (↑hGamma_fin.toFinset.card : ENNReal) := by
      rw [hGamma_fin.encard_eq_coe_toFinset_card] <;> rfl
    rw [h1, h_cardG, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro kj hkj
    have hfin : Set.Finite (chunkGraph Gamma S1 S2 kj.1 kj.2) :=
      hGamma_fin.subset (fun p hp => hp.1)
    have h_eq : (chunkGFin kj).card = hfin.toFinset.card := by
      have h : chunkGFin kj = hfin.toFinset := by simp [chunkGFin, hkj]
      rw [h]
    rw [h_eq, hfin.encard_eq_coe_toFinset_card] <;> rfl

  -- Nreal = encard for grid sets
  have h_nreal_S1 : Nreal δ S1 = ENat.toENNReal S1.encard :=
    nreal_grid_eq_encard hδ_pos hS1_fin hS1_grid
  have h_nreal_S2 : Nreal δ S2 = ENat.toENNReal S2.encard :=
    nreal_grid_eq_encard hδ_pos hS2_fin hS2_grid
  have h_nreal_G : ENat.toENNReal (dyadicCoveringNumber δ Gamma) = ENat.toENNReal Gamma.encard := by
    have hgrid : ∀ p ∈ Gamma, ∀ i : Fin 2, ∃ m : ℤ, p i = δ * (m : ℝ) := by
      intro p hp i
      have h : p 0 ∈ S1 ∧ p 1 ∈ S2 := hGamma_sub p hp
      fin_cases i <;> tauto
    have h : dyadicCoveringNumber δ Gamma = Gamma.encard :=
      grid_set_coveringNumber_eq_encard hδ_pos hgrid
    rw [h]

  have hK2_nonempty : K2.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    simp only [K2, Finset.mem_product]
    constructor <;> simp [K] <;> omega

  -- Gamma nonempty from density
  have hN_S1_pos : 0 < ENat.toENNReal S1.encard := by
    have h1 : 0 < S1.encard := Set.encard_pos.mpr hS1_nonempty
    exact_mod_cast h1
  have hN_S2_pos : 0 < ENat.toENNReal S2.encard := by
    have h1 : 0 < S2.encard := Set.encard_pos.mpr hS2_nonempty
    exact_mod_cast h1
  have h_density' : c_dense * ENat.toENNReal S1.encard * ENat.toENNReal S2.encard ≤ ENat.toENNReal Gamma.encard := by
    have h : c_dense * Nreal δ S1 * Nreal δ S2 ≤ ENat.toENNReal (dyadicCoveringNumber δ Gamma) := h_density
    rw [h_nreal_S1, h_nreal_S2, h_nreal_G] at h
    exact h
  have hGamma_nonempty : Gamma.Nonempty := by
    by_contra h
    have h_empty : Gamma = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [h_empty] at h_density'
    have h_pos : (0 : ENNReal) < c_dense * ENat.toENNReal S1.encard * ENat.toENNReal S2.encard := by
      positivity
    rw [Set.encard_empty] at h_density'
    have h_norm : c_dense * ENat.toENNReal S1.encard * ENat.toENNReal S2.encard ≤ (0 : ENNReal) := by
      simpa [ENat.toENNReal_zero] using h_density'
    have h_eq : c_dense * ENat.toENNReal S1.encard * ENat.toENNReal S2.encard = 0 :=
      le_zero_iff.mp h_norm
    rw [h_eq] at h_pos
    exact False.elim (lt_irrefl 0 h_pos)

  -- Per-chunk LHS and RHS
  let lhs (kj : ℤ × ℤ) : ENNReal :=
    c_dense * ENat.toENNReal (unitChunk S1 kj.1).encard * ENat.toENNReal (unitChunk S2 kj.2).encard
  let rhs (kj : ℤ × ℤ) : ENNReal :=
    ENat.toENNReal (chunkGraph Gamma S1 S2 kj.1 kj.2).encard

  -- Product sum identity
  have h_prod_sum : ∑ kj ∈ K2, lhs kj =
      c_dense * ENat.toENNReal S1.encard * ENat.toENNReal S2.encard := by
    have h_lhs_eq : ∀ (kj : ℤ × ℤ), lhs kj = c_dense *
        (ENat.toENNReal (unitChunk S1 kj.1).encard *
         ENat.toENNReal (unitChunk S2 kj.2).encard) := by
      intro kj; simp [lhs, mul_assoc]
    have h1 : ∑ kj ∈ K2, lhs kj =
        c_dense * ∑ kj ∈ K2, (ENat.toENNReal (unitChunk S1 kj.1).encard *
          ENat.toENNReal (unitChunk S2 kj.2).encard) := by
      have h_sum : ∑ kj ∈ K2, lhs kj = ∑ kj ∈ K2, (c_dense *
          (ENat.toENNReal (unitChunk S1 kj.1).encard *
           ENat.toENNReal (unitChunk S2 kj.2).encard)) :=
        Finset.sum_congr rfl (fun x _ => h_lhs_eq x)
      rw [h_sum, Finset.mul_sum]
    rw [h1]
    have h2 : ∑ kj ∈ K2, (ENat.toENNReal (unitChunk S1 kj.1).encard *
        ENat.toENNReal (unitChunk S2 kj.2).encard) =
        (∑ k ∈ K, ENat.toENNReal (unitChunk S1 k).encard) *
        (∑ j ∈ K, ENat.toENNReal (unitChunk S2 j).encard) := by
      have hK2_eq : K2 = K ×ˢ K := by rfl
      rw [hK2_eq]
      have h3 : ∑ kj ∈ K ×ˢ K, (ENat.toENNReal (unitChunk S1 kj.1).encard *
          ENat.toENNReal (unitChunk S2 kj.2).encard) =
          ∑ k ∈ K, ∑ j ∈ K, (ENat.toENNReal (unitChunk S1 k).encard *
            ENat.toENNReal (unitChunk S2 j).encard) := by
        let g : ℤ × ℤ → ENNReal := fun p =>
          ENat.toENNReal (unitChunk S1 p.1).encard * ENat.toENNReal (unitChunk S2 p.2).encard
        have h_sum_prod : ∑ p ∈ K ×ˢ K, g p = ∑ x ∈ K, ∑ y ∈ K, g (x, y) :=
          Finset.sum_product K K g
        exact h_sum_prod
      rw [h3]
      have h4 : ∀ k ∈ K, ∑ j ∈ K, (ENat.toENNReal (unitChunk S1 k).encard *
          ENat.toENNReal (unitChunk S2 j).encard) =
          ENat.toENNReal (unitChunk S1 k).encard * (∑ j ∈ K, ENat.toENNReal (unitChunk S2 j).encard) := by
        intro k _
        rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl h4, Finset.sum_mul]
    rw [h2, h_sum1, h_sum2]; ring

  -- Total sum inequality
  have h_total : ∑ kj ∈ K2, lhs kj ≤ ∑ kj ∈ K2, rhs kj := by
    rw [h_prod_sum, ←h_sumG]
    exact h_density'

  -- Filter to nonempty graph chunks
  let K2ne : Finset (ℤ × ℤ) :=
    K2.filter (fun kj => (chunkGraph Gamma S1 S2 kj.1 kj.2).Nonempty)

  -- K2ne nonempty
  have hK2ne_nonempty : K2ne.Nonempty := by
    rcases hGamma_nonempty with ⟨p, hp⟩
    have hpsub : p 0 ∈ S1 ∧ p 1 ∈ S2 := hGamma_sub p hp
    let k : ℤ := Int.floor (p 0)
    let j : ℤ := Int.floor (p 1)
    have hkK : k ∈ K := h_chunk_in_K (p 0) (hS1_bdd (p 0) hpsub.1)
    have hjK : j ∈ K := h_chunk_in_K (p 1) (hS2_bdd (p 1) hpsub.2)
    have hkj : (k, j) ∈ K2 := Finset.mem_product.mpr ⟨hkK, hjK⟩
    have h1 : (k : ℝ) ≤ p 0 := Int.floor_le (p 0)
    have h2 : p 0 < (k : ℝ) + 1 := Int.lt_floor_add_one (p 0)
    have h3 : (j : ℝ) ≤ p 1 := Int.floor_le (p 1)
    have h4 : p 1 < (j : ℝ) + 1 := Int.lt_floor_add_one (p 1)
    have hpkj : p ∈ chunkGraph Gamma S1 S2 k j :=
      ⟨hp, ⟨hpsub.1, h1, h2⟩, ⟨hpsub.2, h3, h4⟩⟩
    have hne : (chunkGraph Gamma S1 S2 k j).Nonempty := ⟨p, hpkj⟩
    exact ⟨(k, j), Finset.mem_filter.mpr ⟨hkj, hne⟩⟩

  -- Empty chunks contribute zero to rhs
  have h_sum_rhs_eq : ∑ kj ∈ K2, rhs kj = ∑ kj ∈ K2ne, rhs kj := by
    have h_disj : Disjoint K2ne (K2 \ K2ne) := by
      exact Finset.disjoint_left.mpr (fun x hx1 hx2 => (Finset.mem_sdiff.mp hx2).2 hx1)
    have h_union : K2 = K2ne ∪ (K2 \ K2ne) := by
      ext x; simp [K2ne, Finset.mem_filter]; tauto
    rw [h_union, Finset.sum_union h_disj]
    have h5 : ∑ kj ∈ (K2 \ K2ne), rhs kj = 0 := by
      apply Finset.sum_eq_zero
      intro kj hkj
      have h6 : kj ∉ K2ne := (Finset.mem_sdiff.mp hkj).2
      have h7 : kj ∈ K2 := (Finset.mem_sdiff.mp hkj).1
      have h8 : ¬(chunkGraph Gamma S1 S2 kj.1 kj.2).Nonempty := by
        simpa [K2ne, Finset.mem_filter, h7] using h6
      have h9 : chunkGraph Gamma S1 S2 kj.1 kj.2 = ∅ := Set.not_nonempty_iff_eq_empty.mp h8
      have h10 : rhs kj = 0 := by
        simp only [rhs, h9, Set.encard_empty]; norm_num
      exact h10
    rw [h5, add_zero]

  -- Sum over K2ne: lhs ≤ rhs
  have h_sum_ne : ∑ kj ∈ K2ne, lhs kj ≤ ∑ kj ∈ K2ne, rhs kj := by
    have h1 : ∑ kj ∈ K2ne, lhs kj ≤ ∑ kj ∈ K2, lhs kj :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    rw [h_sum_rhs_eq] at h_total
    exact le_trans h1 h_total

  -- Pigeonhole: exists nonempty chunk with lhs ≤ rhs
  have h_exists : ∃ kj ∈ K2ne, lhs kj ≤ rhs kj :=
    ENNReal.exists_le_of_sum_le hK2ne_nonempty h_sum_ne

  rcases h_exists with ⟨kj, hkj_ne, h_ineq⟩
  let k : ℤ := kj.1
  let j : ℤ := kj.2
  have hkj : kj ∈ K2 := (Finset.mem_filter.mp hkj_ne).1
  have hG_nonempty : (chunkGraph Gamma S1 S2 k j).Nonempty :=
    (Finset.mem_filter.mp hkj_ne).2
  -- Translate
  let B1 : Set ℝ := Set.image (fun x => x - (k : ℝ)) (unitChunk S1 k)
  let B2 : Set ℝ := Set.image (fun x => x - (j : ℝ)) (unitChunk S2 j)
  let G' : Set (EuclideanSpace ℝ (Fin 2)) :=
    translateGraph2D k j (chunkGraph Gamma S1 S2 k j)

  -- B1, B2 ⊆ [0,1]
  have hB1_sub_Icc : B1 ⊆ Set.Icc (0 : ℝ) 1 := by
    intro y hy; rcases hy with ⟨x, hx, rfl⟩
    exact ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
  have hB2_sub_Icc : B2 ⊆ Set.Icc (0 : ℝ) 1 := by
    intro y hy; rcases hy with ⟨x, hx, rfl⟩
    exact ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩

  -- Grid preservation
  have h_chunk1_grid : ∀ x ∈ unitChunk S1 k, ∃ m : ℤ, x = δ * (m : ℝ) :=
    fun x hx => hS1_grid x hx.1
  have h_chunk2_grid : ∀ x ∈ unitChunk S2 j, ∃ m : ℤ, x = δ * (m : ℝ) :=
    fun x hx => hS2_grid x hx.1
  have hB1_grid : B1 ⊆ productLikeIntegerGrid δ := by
    intro y hy
    exact int_translate_preserves_grid1d hδ_dyadic k h_chunk1_grid y hy
  have hB2_grid : B2 ⊆ productLikeIntegerGrid δ := by
    intro y hy
    exact int_translate_preserves_grid1d hδ_dyadic j h_chunk2_grid y hy
  have hB1_unit : B1 ⊆ productLikeUnitGrid δ :=
    fun x hx => ⟨hB1_grid hx, hB1_sub_Icc hx⟩
  have hB2_unit : B2 ⊆ productLikeUnitGrid δ :=
    fun x hx => ⟨hB2_grid hx, hB2_sub_Icc hx⟩

  -- Nonempty
  rcases hG_nonempty with ⟨p, hp⟩
  have hB1_nonempty : B1.Nonempty := ⟨p 0 - (k : ℝ), ⟨p 0, hp.2.1, by ring⟩⟩
  have hB2_nonempty : B2.Nonempty := ⟨p 1 - (j : ℝ), ⟨p 1, hp.2.2, by ring⟩⟩

  -- G' finite and grid
  have hG'_finite : G'.Finite :=
    (hGamma_fin.subset (fun p hp => hp.1)).image _
  have h_chunkG_grid : ∀ p ∈ chunkGraph Gamma S1 S2 k j, ∀ i : Fin 2, ∃ m : ℤ, p i = δ * (m : ℝ) := by
    intro p hp i
    have hsub : p 0 ∈ S1 ∧ p 1 ∈ S2 := hGamma_sub p hp.1
    fin_cases i <;> tauto
  have hG'_grid : ∀ p ∈ G', ∀ i : Fin 2, ∃ m : ℤ, p i = δ * (m : ℝ) :=
    int_translate_preserves_grid2d hδ_dyadic k j h_chunkG_grid

  -- G' subset
  have hG'_sub : ∀ p ∈ G', p 0 ∈ B1 ∧ p 1 ∈ B2 := by
    intro p hp
    rcases hp with ⟨q, hq, rfl⟩
    have hq0 : q 0 ∈ unitChunk S1 k := hq.2.1
    have hq1 : q 1 ∈ unitChunk S2 j := hq.2.2
    constructor
    · exact ⟨q 0, hq0, by simp [translateGraph2D]⟩
    · exact ⟨q 1, hq1, by simp [translateGraph2D]⟩

  -- Density: Nreal and Nplane preservation under translation
  have h_chunk1_bdd : IsBounded (unitChunk S1 k) :=
    IsBounded.subset (Metric.isBounded_Icc _ _) (by
      intro x hx; exact ⟨hx.2.1, hx.2.2.le⟩)
  have h_chunk2_bdd : IsBounded (unitChunk S2 j) :=
    IsBounded.subset (Metric.isBounded_Icc _ _) (by
      intro x hx; exact ⟨hx.2.1, hx.2.2.le⟩)
  have hN1_eq : Nreal δ B1 = Nreal δ (unitChunk S1 k) := by
    have h_cast : (↑(-k) : ℝ) = -(k : ℝ) := by simp
    have h_main := nreal_translate_by_int hδ_dyadic h_chunk1_bdd (-k)
    have h_eq : B1 = translateSet (↑(-k)) (unitChunk S1 k) := by
      dsimp only [B1, translateSet]
      congr with x; simp [h_cast]; ring
    rw [h_eq]; exact h_main
  have hN2_eq : Nreal δ B2 = Nreal δ (unitChunk S2 j) := by
    have h_cast : (↑(-j) : ℝ) = -(j : ℝ) := by simp
    have h_main := nreal_translate_by_int hδ_dyadic h_chunk2_bdd (-j)
    have h_eq : B2 = translateSet (↑(-j)) (unitChunk S2 j) := by
      dsimp only [B2, translateSet]
      congr with x; simp [h_cast]; ring
    rw [h_eq]; exact h_main
  have h_chunkG_fin : Set.Finite (chunkGraph Gamma S1 S2 k j) :=
    hGamma_fin.subset (fun p hp => hp.1)
  have hNG_eq : dyadicCoveringNumber δ G' = dyadicCoveringNumber δ (chunkGraph Gamma S1 S2 k j) :=
    covering2D_translate_by_int hδ_dyadic hδ_pos h_chunkG_fin h_chunkG_grid k j

  have h_ineq' : c_dense * Nreal δ B1 * Nreal δ B2 ≤
      ENat.toENNReal (dyadicCoveringNumber δ G') := by
    rw [hN1_eq, hN2_eq, hNG_eq]
    have h_chunk1_encard : Nreal δ (unitChunk S1 k) = ENat.toENNReal (unitChunk S1 k).encard :=
      nreal_grid_eq_encard hδ_pos (hS1_fin.subset (fun x hx => hx.1)) h_chunk1_grid
    have h_chunk2_encard : Nreal δ (unitChunk S2 j) = ENat.toENNReal (unitChunk S2 j).encard :=
      nreal_grid_eq_encard hδ_pos (hS2_fin.subset (fun x hx => hx.1)) h_chunk2_grid
    have h_chunkG_encard : dyadicCoveringNumber δ (chunkGraph Gamma S1 S2 k j) =
        (chunkGraph Gamma S1 S2 k j).encard :=
      grid_set_coveringNumber_eq_encard hδ_pos h_chunkG_grid
    rw [h_chunk1_encard, h_chunk2_encard, h_chunkG_encard]
    exact h_ineq

  exact ⟨k, j, B1, B2, G', hB1_unit, hB2_unit, hB1_nonempty, hB2_nonempty,
    hG'_finite, hG'_grid, hG'_sub, h_ineq', rfl, rfl⟩

/-- Transport per-direction projection families under graph translation.

    Given an arbitrary coefficient map `f` (for Phase7 this is the projective
    cross-ratio coefficient), translating the graph by integer `(k1, k2)` shifts
    each projection set by `t(y) = k1 * f(y) + k2`.

    Membership equivalence:
      `p0 * f(y) + p1 ∈ S y`
        iff `(p0 - k1) * f(y) + (p1 - k2) ∈ S' y`
    where `S' y = S y - t(y)`.

    Since `t(y)` is generally not a δ-grid multiple, the covering number changes
    by at most a fixed factor 2: `Nreal δ (S' y) ≤ 2 * Nreal δ (S y)`.
    This factor must be absorbed once in the Phase7 exponent budget. -/
lemma transport_projection_families
    {δ : ℝ} (hδ_pos : 0 < δ)
    (f : ℝ → ℝ) (k1 k2 : ℤ)
    (S : ℝ → Set ℝ) :
    ∃ (S' : ℝ → Set ℝ),
      (∀ y, S' y = (fun v : ℝ => v - ((k1 : ℝ) * f y + (k2 : ℝ))) '' S y) ∧
      (∀ (y : ℝ) (p : EuclideanSpace ℝ (Fin 2)),
        (p 0 * f y + p 1 ∈ S y) ↔
        ((p 0 - (k1 : ℝ)) * f y + (p 1 - (k2 : ℝ)) ∈ S' y)) ∧
      (∀ y, Bornology.IsBounded (S y) →
        Nreal δ (S' y) ≤ 2 * Nreal δ (S y)) := by
  let S' : ℝ → Set ℝ := fun y =>
    (fun v : ℝ => v - ((k1 : ℝ) * f y + (k2 : ℝ))) '' S y
  have h_def : ∀ y, S' y = (fun v : ℝ => v - ((k1 : ℝ) * f y + (k2 : ℝ))) '' S y := by
    intro y; rfl
  have h_incidence : ∀ (y : ℝ) (p : EuclideanSpace ℝ (Fin 2)),
      (p 0 * f y + p 1 ∈ S y) ↔
      ((p 0 - (k1 : ℝ)) * f y + (p 1 - (k2 : ℝ)) ∈ S' y) := by
    intro y p
    let t : ℝ := (k1 : ℝ) * f y + (k2 : ℝ)
    have h_alg : (p 0 - (k1 : ℝ)) * f y + (p 1 - (k2 : ℝ)) = (p 0 * f y + p 1) - t := by
      simp [t]; ring
    constructor
    · intro h
      have h5 : (p 0 * f y + p 1) - t ∈ S' y := by
        refine ⟨p 0 * f y + p 1, h, by ring⟩
      rw [h_alg]; exact h5
    · intro h
      rcases h with ⟨w, hw, h_eq⟩
      have h9 : w - t = (p 0 * f y + p 1) - t := by
        have h10 : w - t = (p 0 - (k1 : ℝ)) * f y + (p 1 - (k2 : ℝ)) := by
          simpa [S', t] using h_eq
        rw [h10, h_alg]
      have h10 : w = p 0 * f y + p 1 := by linarith
      rw [h10] at hw; exact hw
  have h_bound : ∀ y, Bornology.IsBounded (S y) →
      Nreal δ (S' y) ≤ 2 * Nreal δ (S y) := by
    intro y hS_bdd
    have h1 : S' y = ProductReduction.translateSet (-( (k1 : ℝ) * f y + (k2 : ℝ))) (S y) := by
      ext z
      simp only [S', ProductReduction.translateSet, Set.mem_image]
      constructor
      · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, by ring⟩
      · rintro ⟨v, hv, hz⟩; exact ⟨v, hv, by linarith⟩
    rw [h1]
    exact nreal_translate_real_le_two hδ_pos hS_bdd _
  exact ⟨S', h_def, h_incidence, h_bound⟩

end ProductLikeIncidence.ProductReduction
