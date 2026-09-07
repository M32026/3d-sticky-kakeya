module

public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.Homothety
public import MyLeanRepo.InductionOnScales.SSet
public import MyLeanRepo.InductionOnScales.SlopeCells
public import MyLeanRepo.InductionOnScales.FinePhaseComponents
public import MyLeanRepo.InductionOnScales.PadSSet

@[expose] public section

/-!
# Fine Phase Assembly

Constructs local fine configurations for each coarse square from retained
families that already have uniform slope-cell counts.

## Input assumptions (coarse phase responsibility):
- `C_in`: SSet constant of retained families
- `m_Q`: uniform tubes per slope cell
- `MQ Q`: uniform number of slope cells per point (same for all p in Q)
- `h_uniform`: each cell has exactly m_Q tubes
- `h_cell_count`: number of cells = MQ Q

## Output:
- `CQ Q = K * C₁` (geometric transfer `C_in * 16^s ≤ K * C₁` by `hC_in_bound`)
- NiceConfiguration at scale n-m for each coarse square Q
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace InductionOnScales

/-- Map a local square back to the original fine square. -/
def fine_local_p_of_q {n m : ℕ} (hnm : m ≤ n) (Q : DyadicSquare m) (q : DyadicSquare (n - m)) : DyadicSquare n :=
  ⟨q.i + Q.i * coarseRefinementFactor n m, q.j + Q.j * coarseRefinementFactor n m⟩

/-- fine_local_p_of_q is the inverse of squareHomothety. -/
lemma fine_local_p_of_q_inverse {n m : ℕ} (hnm : m ≤ n) (Q : DyadicSquare m) (p : DyadicSquare n) (hpQ : squareContained hnm p Q) :
    fine_local_p_of_q hnm Q (squareHomothety hnm Q p) = p := by
  have hi : (fine_local_p_of_q hnm Q (squareHomothety hnm Q p)).i = p.i := by
    simp [fine_local_p_of_q, squareHomothety] <;> ring
  have hj : (fine_local_p_of_q hnm Q (squareHomothety hnm Q p)).j = p.j := by
    simp [fine_local_p_of_q, squareHomothety] <;> ring
  let x := fine_local_p_of_q hnm Q (squareHomothety hnm Q p)
  have h_ext : ∀ (a b : DyadicSquare n), a.i = b.i → a.j = b.j → a = b := by
    intro a b h1 h2
    cases a <;> cases b <;> simp_all
  exact h_ext x p hi hj

/-- fine_local_p_of_q maps points_Q back into P_Q. -/
lemma fine_local_p_of_q_in_PQ {n m : ℕ} (hnm : m ≤ n) (P : Finset (DyadicSquare n)) (Q : DyadicSquare m)
    (q : DyadicSquare (n - m))
    (hq : q ∈ (P.filter (fun p => squareContained hnm p Q)).image (squareHomothety hnm Q)) :
    fine_local_p_of_q hnm Q q ∈ P.filter (fun p => squareContained hnm p Q) := by
  rcases Finset.mem_image.mp hq with ⟨p, hpQ, rfl⟩
  have h_eq : fine_local_p_of_q hnm Q (squareHomothety hnm Q p) = p := fine_local_p_of_q_inverse hnm Q p (Finset.mem_filter.mp hpQ).2
  rw [h_eq]
  exact hpQ

/-- The local tube family for a point in a coarse square. -/
def fine_local_tube_family
    {n m : ℕ} (hnm : m ≤ n)
    (P : Finset (DyadicSquare n))
    (Q : DyadicSquare m)
    (G : (p : DyadicSquare n) → (hp : p ∈ P) → (hpQ : squareContained hnm p Q) → Finset (DyadicTube (n - m)))
    (q : DyadicSquare (n - m))
    (hq : q ∈ (P.filter (fun p => squareContained hnm p Q)).image (squareHomothety hnm Q)) :
    Finset (DyadicTube (n - m)) :=
  let p := fine_local_p_of_q hnm Q q
  let hpQ_all : p ∈ P.filter (fun p => squareContained hnm p Q) := fine_local_p_of_q_in_PQ hnm P Q q hq
  G p (Finset.mem_filter.mp hpQ_all).1 (Finset.mem_filter.mp hpQ_all).2

/-- Reduce fine_local_tube_family when q is known to be squareHomothety of p. -/
lemma fine_local_tube_family_at_point
    {n m : ℕ} (hnm : m ≤ n)
    (P : Finset (DyadicSquare n))
    (Q : DyadicSquare m)
    (G : (p : DyadicSquare n) → (hp : p ∈ P) → (hpQ : squareContained hnm p Q) → Finset (DyadicTube (n - m)))
    (p : DyadicSquare n) (hp : p ∈ P) (hpQ : squareContained hnm p Q)
    (q : DyadicSquare (n - m)) (hq : q ∈ (P.filter (fun p => squareContained hnm p Q)).image (squareHomothety hnm Q))
    (h_q : q = squareHomothety hnm Q p) :
    fine_local_tube_family hnm P Q G q hq = G p hp hpQ := by
  have h_p_eq : fine_local_p_of_q hnm Q q = p := by
    rw [h_q]
    exact fine_local_p_of_q_inverse hnm Q p hpQ
  have h_main : fine_local_tube_family hnm P Q G q hq =
      G (fine_local_p_of_q hnm Q q)
        (Finset.mem_filter.mp (fine_local_p_of_q_in_PQ hnm P Q q hq)).1
        (Finset.mem_filter.mp (fine_local_p_of_q_in_PQ hnm P Q q hq)).2 := by
    rfl
  rw [h_main]
  exact h_p_eq ▸ rfl

/-- Build a single local NiceConfiguration for one coarse square Q. -/
noncomputable def build_single_fine_config
    {n m : ℕ} (hnm : m ≤ n)
    (s : ℝ) (hs : 0 ≤ s)
    (C₁ K C_in : ℝ) (hK : 1 ≤ K) (hC₁ : 1 ≤ C₁)
    (hC_in_bound : C_in * Real.rpow 16 s ≤ K * C₁)
    (P : Finset (DyadicSquare n))
    (tubeFamily : (p : DyadicSquare n) → p ∈ P → Finset (DyadicTube n))
    (m_Q : ℕ) (hmQ_pos : 0 < m_Q)
    (MQ : ℕ)
    (Q : DyadicSquare m) (hQ : Q ∈ P.image (containingSquare hnm))
    (G : (p : DyadicSquare n) → (hp : p ∈ P) → (hpQ : squareContained hnm p Q) →
      Finset (DyadicTube (n - m)))
    (hG_spec : ∀ (p : DyadicSquare n) (hp : p ∈ P) (hpQ : squareContained hnm p Q),
      (G p hp hpQ).image (fun U => U.a) = (tubeFamily p hp).image (fun T => localSlopeCellIndex m T.a) ∧
      Set.InjOn (fun U : DyadicTube (n - m) => U.a) (G p hp hpQ) ∧
      IsFiniteTubeSSet s (C_in * Real.rpow 16 s) (G p hp hpQ) ∧
      ∀ U ∈ G p hp hpQ, (U.toSet ∩ (squareHomothety hnm Q p).toSet).Nonempty)
    (h_cell_count : ∀ (p : DyadicSquare n) (hp : p ∈ P) (hpQ : squareContained hnm p Q),
      ((tubeFamily p hp).image (fun T => localSlopeCellIndex m T.a)).card = MQ)
    (h_tube_params : ∀ (p : DyadicSquare n) (hp : p ∈ P) (T : DyadicTube n),
      T ∈ tubeFamily p hp → T.IsInAllowedParameterStrip) :
    NiceConfiguration (n - m) s (K * C₁) MQ := by
  let P_Q := P.filter (fun p => squareContained hnm p Q)
  let points_Q := P_Q.image (squareHomothety hnm Q)
  let p_of_q := fine_local_p_of_q hnm Q
  have h_inverse : ∀ (p : DyadicSquare n) (hpQ : squareContained hnm p Q),
      p_of_q (squareHomothety hnm Q p) = p :=
    fun p hpQ => fine_local_p_of_q_inverse hnm Q p hpQ
  have h_p_of_q_in_PQ : ∀ (q : DyadicSquare (n - m)), q ∈ points_Q → p_of_q q ∈ P_Q :=
    fun q hq => fine_local_p_of_q_in_PQ hnm P Q q hq
  let tubes_Q := P_Q.attach.biUnion (fun (p : {x // x ∈ P_Q}) =>
    G p.val (Finset.mem_filter.mp p.property).1 (Finset.mem_filter.mp p.property).2)
  let tubeFamily_Q := fine_local_tube_family hnm P Q G
  have h_tube_eq : ∀ (q : DyadicSquare (n - m)) (hq : q ∈ points_Q),
      tubeFamily_Q q hq = G (p_of_q q) (Finset.mem_filter.mp (h_p_of_q_in_PQ q hq)).1 (Finset.mem_filter.mp (h_p_of_q_in_PQ q hq)).2 := by
    intro q hq
    simp [tubeFamily_Q, fine_local_tube_family]
    <;> rfl
  exact
    { points := points_Q
      tubes := tubes_Q
      tubeFamily := tubeFamily_Q
      h_subset := by
        intro q hq
        let hpQ := h_p_of_q_in_PQ q hq
        let p' : {x // x ∈ P_Q} := ⟨p_of_q q, hpQ⟩
        have h1 : p' ∈ P_Q.attach := by simp
        have h_eq2 : tubeFamily_Q q hq = G p'.val (Finset.mem_filter.mp p'.property).1 (Finset.mem_filter.mp p'.property).2 := h_tube_eq q hq
        intro U hU
        rw [h_eq2] at hU
        exact Finset.mem_biUnion.mpr ⟨p', h1, hU⟩
      h_size := by
        intro q hq
        let hpQ := h_p_of_q_in_PQ q hq
        let p := p_of_q q
        have hp : p ∈ P := (Finset.mem_filter.mp hpQ).1
        have hpQ' : squareContained hnm p Q := (Finset.mem_filter.mp hpQ).2
        have h_eq2 : tubeFamily_Q q hq = G p hp hpQ' := h_tube_eq q hq
        rw [h_eq2]
        rcases hG_spec p hp hpQ' with ⟨h1, h2, _, _⟩
        have h3 : (G p hp hpQ').card = ((G p hp hpQ').image (fun U => U.a)).card := by
          rw [Finset.card_image_of_injOn h2]
        rw [h3, h1, h_cell_count p hp hpQ']
      h_sset := by
        intro q hq
        let hpQ := h_p_of_q_in_PQ q hq
        let p := p_of_q q
        have hp : p ∈ P := (Finset.mem_filter.mp hpQ).1
        have hpQ' : squareContained hnm p Q := (Finset.mem_filter.mp hpQ).2
        have h_eq2 : tubeFamily_Q q hq = G p hp hpQ' := h_tube_eq q hq
        rw [h_eq2]
        rcases hG_spec p hp hpQ' with ⟨_, _, h_sset', _⟩
        exact IsFiniteTubeSSet.monotone_const hC_in_bound h_sset'
      h_incidence := by
        intro q hq U hU
        let hpQ := h_p_of_q_in_PQ q hq
        let p := p_of_q q
        have hp : p ∈ P := (Finset.mem_filter.mp hpQ).1
        have hpQ' : squareContained hnm p Q := (Finset.mem_filter.mp hpQ).2
        have h_eq2 : tubeFamily_Q q hq = G p hp hpQ' := h_tube_eq q hq
        have hU' : U ∈ G p hp hpQ' := by rw [←h_eq2]; exact hU
        have hq_eq : q = squareHomothety hnm Q p := by
          rcases Finset.mem_image.mp hq with ⟨p0, hp0, rfl⟩
          have h_eq : p = p0 := by
            have h : p_of_q (squareHomothety hnm Q p0) = p0 := h_inverse p0 (Finset.mem_filter.mp hp0).2
            simpa [p] using h
          rw [h_eq]
        rw [hq_eq]
        rcases hG_spec p hp hpQ' with ⟨_, _, _, h_inc'⟩
        exact h_inc' U hU'
      h_bounded := by
        intro q hq
        let hpQ := h_p_of_q_in_PQ q hq
        let p := p_of_q q
        have hpQ' : squareContained hnm p Q := (Finset.mem_filter.mp hpQ).2
        have hq_eq : q = squareHomothety hnm Q p := by
          rcases Finset.mem_image.mp hq with ⟨p0, hp0, rfl⟩
          have h_eq : p = p0 := by
            have h : p_of_q (squareHomothety hnm Q p0) = p0 := h_inverse p0 (Finset.mem_filter.mp hp0).2
            simpa [p] using h
          rw [h_eq]
        rw [hq_eq]
        exact squareHomothety_toSet_subset_unitSquare hpQ'
      h_tube_parameters := by
        intro T hT
        rcases Finset.mem_biUnion.mp hT with ⟨p', hp'_in, hT_in_G⟩
        let p : DyadicSquare n := p'.val
        have hp : p ∈ P := (Finset.mem_filter.mp p'.property).1
        have hpQ' : squareContained hnm p Q := (Finset.mem_filter.mp p'.property).2
        rcases hG_spec p hp hpQ' with ⟨h_img, _, _, _⟩
        have h1 : T.a ∈ (G p hp hpQ').image (fun U => U.a) := Finset.mem_image.mpr ⟨T, hT_in_G, rfl⟩
        have h2 : T.a ∈ (tubeFamily p hp).image (fun T_fine => localSlopeCellIndex m T_fine.a) := by
          rw [h_img] at h1 <;> exact h1
        rcases Finset.mem_image.mp h2 with ⟨T_fine, hT_fine, h_eq⟩
        have h_strip := FineConfig.local_slope_cell_in_strip hnm rfl T_fine (h_tube_params p hp T_fine hT_fine)
        rwa [h_eq] at h_strip }

/-- Fine phase: construct local fine configurations for each coarse square.

Assumes input families already have uniform cell counts (coarse phase's
responsibility). Uses `C_in` as the retained family's SSet constant; the
geometric transfer gives `C_in * 16^s ≤ K * C₁`. -/
theorem fine_phase
    {n m : ℕ} (hnm : m ≤ n)
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (M : ℕ) (hM : 0 < M)
    (config : NiceConfiguration n s C₁ M)
    (K : ℝ) (hK : 1 ≤ K)
    (C_in : ℝ) (hC_in : 1 ≤ C_in)
    (hC_in_bound : C_in * Real.rpow 16 s ≤ K * C₁)
    (P : Finset (DyadicSquare n))
    (hP_sub : P ⊆ config.points)
    (tubeFamily : (p : DyadicSquare n) → p ∈ P → Finset (DyadicTube n))
    (CΔ : ℝ) (MΔ : ℕ) (hMΔ : 0 < MΔ)
    (coarseConfig : NiceConfiguration m s CΔ MΔ)
    (h_coarse_points : coarseConfig.points = P.image (containingSquare hnm))
    (m_Q : ℕ) (hmQ_pos : 0 < m_Q)
    (MQ : DyadicSquare m → ℕ)
    (hMQ_pos : ∀ Q ∈ coarseConfig.points, 0 < MQ Q)
    (h_tube_properties : ∀ p, ∀ hp : p ∈ P,
        tubeFamily p hp ⊆ config.tubeFamily p (hP_sub hp) ∧
        (M : ℝ) ≤ K * ((tubeFamily p hp).card : ℝ) ∧
        IsFiniteTubeSSet s C_in (tubeFamily p hp) ∧
        ∀ T ∈ tubeFamily p hp, (T.toSet ∩ p.toSet).Nonempty ∧
          T.IsInAllowedParameterStrip)
    (h_uniform : ∀ (Q : DyadicSquare m) (hQ : Q ∈ coarseConfig.points)
        (p : DyadicSquare n) (hp : p ∈ P) (hpQ : squareContained hnm p Q),
        ∀ (a : ℤ), ((tubeFamily p hp).filter (fun T => localSlopeCellIndex m T.a = a)).card =
          if a ∈ (tubeFamily p hp).image (fun T => localSlopeCellIndex m T.a) then m_Q else 0)
    (h_cell_count : ∀ (Q : DyadicSquare m) (hQ : Q ∈ coarseConfig.points)
        (p : DyadicSquare n) (hp : p ∈ P) (hpQ : squareContained hnm p Q),
        ((tubeFamily p hp).image (fun T => localSlopeCellIndex m T.a)).card = MQ Q)
    (h_coarse_containment : ∀ p, ∀ hp : p ∈ P, ∀ T ∈ tubeFamily p hp,
        ∃ (hQ : containingSquare hnm p ∈ coarseConfig.points)
          (U : DyadicTube m),
          U ∈ coarseConfig.tubeFamily (containingSquare hnm p) hQ ∧
          T.toSet ⊆ U.toSet) :
    ∃ (CQ : DyadicSquare m → ℝ)
      (fineConfig : (Q : DyadicSquare m) → Q ∈ coarseConfig.points →
        NiceConfiguration (n - m) s (CQ Q) (MQ Q)),
      (∀ Q ∈ coarseConfig.points, CQ Q ≤ K * C₁ ∧ C₁ ≤ K * CQ Q) ∧
      (∀ Q, ∀ hQ : Q ∈ coarseConfig.points,
        (fineConfig Q hQ).points =
          (P.filter fun p => squareContained hnm p Q).image
            (squareHomothety hnm Q)) ∧
      (∀ Q, ∀ hQ : Q ∈ coarseConfig.points,
        ∀ p, ∀ hp : p ∈ P, squareContained hnm p Q →
          ∃ hq : squareHomothety hnm Q p ∈ (fineConfig Q hQ).points,
            ((fineConfig Q hQ).tubeFamily
                (squareHomothety hnm Q p) hq).image (fun U => U.a) =
              (tubeFamily p hp).image
                (fun T => localSlopeCellIndex m T.a)) := by
  let CQ : DyadicSquare m → ℝ := fun _ => K * C₁
  have h_main : ∀ (Q : DyadicSquare m) (hQ : Q ∈ coarseConfig.points)
      (p : DyadicSquare n) (hp : p ∈ P) (hpQ : squareContained hnm p Q),
      ∃ (G : Finset (DyadicTube (n - m))),
        G.image (fun U => U.a) = (tubeFamily p hp).image (fun T => localSlopeCellIndex m T.a) ∧
        Set.InjOn (fun U : DyadicTube (n - m) => U.a) G ∧
        IsFiniteTubeSSet s (C_in * Real.rpow 16 s) G ∧
        ∀ U ∈ G, (U.toSet ∩ (squareHomothety hnm Q p).toSet).Nonempty := by
    intro Q hQ p hp hpQ
    let q := squareHomothety hnm Q p
    let hprops := h_tube_properties p hp
    have h_sset : IsFiniteTubeSSet s C_in (tubeFamily p hp) := hprops.2.2.1
    have h_inc_strip : ∀ T ∈ tubeFamily p hp, (T.toSet ∩ p.toSet).Nonempty ∧ T.IsInAllowedParameterStrip := hprops.2.2.2
    have h_bounded : p.toSet ⊆ unitSquare := config.h_bounded p (hP_sub hp)
    exact FineConfig.construct_fine_tube_family hnm p hs (tubeFamily p hp)
      h_sset
      (fun T hT => (h_inc_strip T hT).1)
      h_bounded
      (fun T hT => (h_inc_strip T hT).2)
      m_Q hmQ_pos (h_uniform Q hQ p hp hpQ) rfl q
  choose G hG_spec using h_main
  let p_of_q (Q : DyadicSquare m) (q : DyadicSquare (n - m)) : DyadicSquare n :=
    ⟨q.i + Q.i * coarseRefinementFactor n m, q.j + Q.j * coarseRefinementFactor n m⟩
  have h_ext : ∀ (a b : DyadicSquare n), a.i = b.i → a.j = b.j → a = b := by
    intro a b h1 h2
    cases a <;> cases b <;> simp_all
  have h_inverse : ∀ (Q : DyadicSquare m) (p : DyadicSquare n) (hpQ : squareContained hnm p Q),
      p_of_q Q (squareHomothety hnm Q p) = p := by
    intro Q p hpQ
    have hi : (p_of_q Q (squareHomothety hnm Q p)).i = p.i := by
      simp [p_of_q, squareHomothety] <;> ring
    have hj : (p_of_q Q (squareHomothety hnm Q p)).j = p.j := by
      simp [p_of_q, squareHomothety] <;> ring
    exact h_ext (p_of_q Q (squareHomothety hnm Q p)) p hi hj
  let fineConfig (Q : DyadicSquare m) (hQ : Q ∈ coarseConfig.points) :
      NiceConfiguration (n - m) s (CQ Q) (MQ Q) :=
    build_single_fine_config hnm s hs C₁ K C_in hK hC₁ hC_in_bound P tubeFamily m_Q hmQ_pos (MQ Q) Q
      (h_coarse_points ▸ hQ)
      (G Q hQ) (hG_spec Q hQ)
      (fun p hp hpQ => h_cell_count Q hQ p hp hpQ)
      (fun p hp T hT => (h_tube_properties p hp).2.2.2 T hT |>.2)
  refine' ⟨CQ, fineConfig, _⟩
  constructor
  · -- CQ bounds
    intro Q hQ
    constructor
    · simp [CQ] <;> linarith
    · have h1 : 1 ≤ K := hK
      have h2 : 0 ≤ C₁ := by linarith [hC₁]
      have h3 : (1 : ℝ) * C₁ ≤ K * C₁ := mul_le_mul_of_nonneg_right h1 h2
      have h4 : C₁ ≤ K * C₁ := by simpa using h3
      have h5 : C₁ ≤ K * (K * C₁) := le_trans h4 (mul_le_mul_of_nonneg_left h4 (by linarith))
      simpa [CQ] using h5
  constructor
  · -- points equality
    intro Q hQ
    rfl
  · -- slope preservation
    intro Q hQ p hp hpQ
    let q := squareHomothety hnm Q p
    have hq : q ∈ (fineConfig Q hQ).points := by
      simp [fineConfig]
      have hpQ_in : p ∈ P.filter (fun p => squareContained hnm p Q) := by
        simp only [Finset.mem_filter] <;> exact ⟨hp, hpQ⟩
      exact Finset.mem_image.mpr ⟨p, hpQ_in, rfl⟩
    refine' ⟨hq, _⟩
    have h_goal : ((fineConfig Q hQ).tubeFamily q hq).image (fun U => U.a) =
        (tubeFamily p hp).image (fun T => localSlopeCellIndex m T.a) := by
      have h_eq1 : (fineConfig Q hQ).tubeFamily q hq = G Q hQ p hp hpQ := by
        have h1 : (fineConfig Q hQ).tubeFamily q hq = fine_local_tube_family hnm P Q (G Q hQ) q hq := by
          unfold fineConfig build_single_fine_config <;> rfl
        rw [h1]
        exact fine_local_tube_family_at_point hnm P Q (G Q hQ) p hp hpQ q hq rfl
      rw [h_eq1]
      exact (hG_spec Q hQ p hp hpQ).1
    exact h_goal

end InductionOnScales
