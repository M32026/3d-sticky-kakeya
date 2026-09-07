import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.VerticalScaling
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ClusterDefinitions

/-!
# Vertical scaling transport for rectangle and function families

Extends `VerticalScaling` to finite function families, rectangle families,
and all associated properties: centers, over-central-quarter, comparability,
incomparability, tangent counts, clusters, separation, diameter, and
subfamilies.  Scaling by a positive constant preserves every cardinality and
the bipartite normalized count exactly.

The main application is the normalization `t → 1` via `s := 1 / t` when
`t > 1`, so that the normalized coarse rectangle count (which requires
`t ≤ 1`) can be applied and its conclusion transferred back.
-/

noncomputable section

open Classical

namespace Kakeya.Cinematic

-- ============================================================================
-- Helper lemmas for C2Function scaling
-- ============================================================================

lemma C2Function_smul_injective {s : ℝ} (hs : 0 < s) :
    Function.Injective (fun f : C2Function => s • f) := by
  intro f g h
  have h_eq1 : (s • f).value = (s • g).value := by congr
  have h_eq2 : (s • f).firstDeriv = (s • g).firstDeriv := by congr
  have h_eq3 : (s • f).secondDeriv = (s • g).secondDeriv := by congr
  have hval : f.value = g.value := by
    have h4 : s • f.value = s • g.value := by
      rw [← C2Function.smul_value s f, ← C2Function.smul_value s g, h_eq1]
    apply ContinuousMap.ext
    intro x
    have h5 : (s • f.value) x = (s • g.value) x := by rw [h4]
    simpa using mul_left_cancel₀ hs.ne' h5
  have hfirst : f.firstDeriv = g.firstDeriv := by
    have h4 : s • f.firstDeriv = s • g.firstDeriv := by
      rw [← C2Function.smul_firstDeriv s f, ← C2Function.smul_firstDeriv s g, h_eq2]
    apply ContinuousMap.ext
    intro x
    have h5 : (s • f.firstDeriv) x = (s • g.firstDeriv) x := by rw [h4]
    simpa using mul_left_cancel₀ hs.ne' h5
  have hsecond : f.secondDeriv = g.secondDeriv := by
    have h4 : s • f.secondDeriv = s • g.secondDeriv := by
      rw [← C2Function.smul_secondDeriv s f, ← C2Function.smul_secondDeriv s g, h_eq3]
    apply ContinuousMap.ext
    intro x
    have h5 : (s • f.secondDeriv) x = (s • g.secondDeriv) x := by rw [h4]
    simpa using mul_left_cancel₀ hs.ne' h5
  have hjet : C2Function.toJet f = C2Function.toJet g := by
    simp [C2Function.toJet, hval, hfirst, hsecond]
  exact C2Function.toJet_injective hjet

lemma C2Function_smul_smul (r s : ℝ) (f : C2Function) :
    r • (s • f) = (r * s) • f := by
  have hval : (r • (s • f)).value = ((r * s) • f).value := by
    rw [C2Function.smul_value r (s • f), C2Function.smul_value (r * s) f,
      C2Function.smul_value s f]
    exact smul_smul r s f.value
  have hfirst : (r • (s • f)).firstDeriv = ((r * s) • f).firstDeriv := by
    rw [C2Function.smul_firstDeriv r (s • f), C2Function.smul_firstDeriv (r * s) f,
      C2Function.smul_firstDeriv s f]
    exact smul_smul r s f.firstDeriv
  have hsecond : (r • (s • f)).secondDeriv = ((r * s) • f).secondDeriv := by
    rw [C2Function.smul_secondDeriv r (s • f), C2Function.smul_secondDeriv (r * s) f,
      C2Function.smul_secondDeriv s f]
    exact smul_smul r s f.secondDeriv
  have hjet : C2Function.toJet (r • (s • f)) = C2Function.toJet ((r * s) • f) := by
    simp [C2Function.toJet, hval, hfirst, hsecond]
  exact C2Function.toJet_injective hjet

lemma C2Function_one_smul (f : C2Function) : (1 : ℝ) • f = f := by
  have hval : ((1 : ℝ) • f).value = f.value := by simp [C2Function.smul_value]
  have hfirst : ((1 : ℝ) • f).firstDeriv = f.firstDeriv := by simp [C2Function.smul_firstDeriv]
  have hsecond : ((1 : ℝ) • f).secondDeriv = f.secondDeriv := by simp [C2Function.smul_secondDeriv]
  have hjet : C2Function.toJet ((1 : ℝ) • f) = C2Function.toJet f := by
    simp [C2Function.toJet, hval, hfirst, hsecond]
  exact C2Function.toJet_injective hjet

/-- Membership in a scaled c2Ball is equivalent to membership in the original ball. -/
lemma mem_c2Ball_smul {s : ℝ} (hs : 0 < s) {f c : C2Function} {r : ℝ} :
    s • f ∈ c2Ball (s • c) (s * r) ↔ f ∈ c2Ball c r := by
  simp only [mem_c2Ball]
  constructor
  · intro h
    rw [c2Distance_smul hs.le] at h
    exact le_of_mul_le_mul_left h hs
  · intro h
    rw [c2Distance_smul hs.le]
    exact mul_le_mul_of_nonneg_left h hs.le

-- ============================================================================
-- FiniteFunctionFamily scaling
-- ============================================================================

namespace FiniteFunctionFamily

/-- Scale every function in a finite family by `s`. -/
def smul (s : ℝ) (F : FiniteFunctionFamily) : FiniteFunctionFamily :=
  { carrier := Set.image (fun f => s • f) F.carrier,
    finite := F.finite.image _ }

instance : SMul ℝ FiniteFunctionFamily := ⟨FiniteFunctionFamily.smul⟩

lemma smul_carrier (s : ℝ) (F : FiniteFunctionFamily) :
    (s • F).carrier = Set.image (fun f => s • f) F.carrier := rfl

lemma smul_card {s : ℝ} (hs : 0 < s) (F : FiniteFunctionFamily) :
    (s • F).card = F.card := by
  have h : (s • F).carrier = Set.image (fun f : C2Function => s • f) F.carrier := rfl
  rw [FiniteFunctionFamily.card, h,
    Set.ncard_image_of_injective F.carrier (C2Function_smul_injective hs),
    FiniteFunctionFamily.card]

lemma mem_smul_iff {s : ℝ} (hs : 0 < s) {F : FiniteFunctionFamily} {f : C2Function} :
    f ∈ (s • F).carrier ↔ ∃ g ∈ F.carrier, f = s • g := by
  simp only [smul_carrier, Set.mem_image]
  constructor
  · rintro ⟨g, hg, h_eq⟩
    exact ⟨g, hg, h_eq.symm⟩
  · rintro ⟨g, hg, h_eq⟩
    exact ⟨g, hg, h_eq.symm⟩

lemma smul_subset {s : ℝ} (hs : 0 < s) {F G : FiniteFunctionFamily}
    (h : F.carrier ⊆ G.carrier) : (s • F).carrier ⊆ (s • G).carrier := by
  intro f hf
  rcases (mem_smul_iff hs).mp hf with ⟨g, hg, rfl⟩
  exact (mem_smul_iff hs).mpr ⟨g, h hg, rfl⟩

lemma smul_cluster {s : ℝ} (hs : 0 < s) (F : FiniteFunctionFamily)
    (c : C2Function) (r : ℝ) :
    (s • F).cluster (s • c) (s * r) = s • (F.cluster c r) := by
  let A := (s • F).cluster (s • c) (s * r)
  let B := s • (F.cluster c r)
  have h_carrier : A.carrier = B.carrier := by
    ext f
    simp only [A, B, FiniteFunctionFamily.cluster, Set.mem_inter_iff, mem_c2Ball,
      smul_carrier, Set.mem_image]
    constructor
    · rintro ⟨⟨g, hg, rfl⟩, hdist⟩
      rw [c2Distance_smul hs.le] at hdist
      exact ⟨g, ⟨hg, le_of_mul_le_mul_left hdist hs⟩, rfl⟩
    · rintro ⟨g, ⟨hg, hdist⟩, rfl⟩
      constructor
      · exact ⟨g, hg, rfl⟩
      · rw [c2Distance_smul hs.le]
        exact mul_le_mul_of_nonneg_left hdist hs.le
  have h_ext : ∀ (x y : FiniteFunctionFamily), x.carrier = y.carrier → x = y := by
    intro x y h
    cases x <;> cases y <;> simp_all
  exact h_ext A B h_carrier

end FiniteFunctionFamily

-- ============================================================================
-- IsLambdaTangent iff under scaling
-- ============================================================================

namespace CurvilinearRectangle

lemma IsLambdaTangent.smul_iff {δ t : ℝ} {R : CurvilinearRectangle δ t}
    {f : C2Function} {lambda s : ℝ} (hs : 0 < s) :
    (R.smul s hs).IsLambdaTangent (s • f) lambda ↔
    R.IsLambdaTangent f lambda := by
  constructor
  · -- Backward direction: descale the point
    intro h p hp
    have hfn : (R.smul s hs).function = s • R.function := by
      simp [CurvilinearRectangle.smul]
    have h4 : (R.smul s hs).function.value p.1 = s * R.function.value p.1 := by
      rw [hfn]
      exact C2Function.smul_apply s R.function p.1
    have hq : (p.1, s * p.2) ∈ (R.smul s hs).carrier := by
      simp only [carrier, verticalNeighborhoodOn, Set.mem_setOf_eq] at hp ⊢
      constructor
      · exact hp.1
      · rw [h4]
        have h5 : |s * p.2 - s * R.function.value p.1| = s * |p.2 - R.function.value p.1| := by
          rw [show s * p.2 - s * R.function.value p.1 = s * (p.2 - R.function.value p.1) by ring]
          rw [abs_mul, abs_of_pos hs]
        rw [h5]
        exact mul_le_mul_of_nonneg_left hp.2 hs.le
    have h6 := h (p.1, s * p.2) hq
    have h7 : |s * p.2 - (s • f).value p.1| ≤ lambda * (s * δ) := h6
    have h8 : (s • f).value p.1 = s * f.value p.1 := C2Function.smul_apply s f p.1
    rw [h8] at h7
    have h9 : |s * p.2 - s * f.value p.1| = s * |p.2 - f.value p.1| := by
      rw [show s * p.2 - s * f.value p.1 = s * (p.2 - f.value p.1) by ring]
      rw [abs_mul, abs_of_pos hs]
    rw [h9] at h7
    have h10 : lambda * (s * δ) = s * (lambda * δ) := by ring
    rw [h10] at h7
    exact le_of_mul_le_mul_left h7 hs
  · -- Forward direction: existing lemma
    exact IsLambdaTangent.smul hs

end CurvilinearRectangle

-- ============================================================================
-- Carrier scaling helper
-- ============================================================================

namespace CurvilinearRectangle

/-- A point is in the scaled rectangle's carrier iff its descaled y-coordinate
is in the original rectangle's carrier. -/
lemma carrier_smul_iff {δ t : ℝ} {R : CurvilinearRectangle δ t} {s : ℝ}
    (hs : 0 < s) (p : UnitPoint × ℝ) :
    p ∈ (R.smul s hs).carrier ↔ (p.1, p.2 / s) ∈ R.carrier := by
  have hfn : (R.smul s hs).function = s • R.function := by
    simp [CurvilinearRectangle.smul]
  have h4 : (R.smul s hs).function.value p.1 = s * R.function.value p.1 := by
    rw [hfn]
    exact C2Function.smul_apply s R.function p.1
  simp only [carrier, verticalNeighborhoodOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have h5 : |p.2 - (R.smul s hs).function.value p.1| ≤ s * δ := h2
    rw [h4] at h5
    have h6 : |p.2 - s * R.function.value p.1| = s * |p.2 / s - R.function.value p.1| := by
      rw [show p.2 - s * R.function.value p.1 = s * (p.2 / s - R.function.value p.1) by
          field_simp [hs.ne'] <;> ring]
      rw [abs_mul, abs_of_pos hs]
    rw [h6] at h5
    exact ⟨h1, le_of_mul_le_mul_left h5 hs⟩
  · rintro ⟨h1, h2⟩
    have h5 : |p.2 / s - R.function.value p.1| ≤ δ := h2
    have h6 : |p.2 - s * R.function.value p.1| = s * |p.2 / s - R.function.value p.1| := by
      rw [show p.2 - s * R.function.value p.1 = s * (p.2 / s - R.function.value p.1) by
          field_simp [hs.ne'] <;> ring]
      rw [abs_mul, abs_of_pos hs]
    have h7 : |p.2 - (R.smul s hs).function.value p.1| ≤ s * δ := by
      rw [h4, h6]
      exact mul_le_mul_of_nonneg_left h5 hs.le
    exact ⟨h1, h7⟩

end CurvilinearRectangle

-- ============================================================================
-- AreLambdaComparable transport
-- ============================================================================

namespace CurvilinearRectangle

lemma AreLambdaComparable.smul_forward {δ t : ℝ}
    {R S : CurvilinearRectangle δ t}
    {family : Set C2Function} {lambda s : ℝ} (hs : 0 < s)
    (h : R.AreLambdaComparable S family lambda) :
    (R.smul s hs).AreLambdaComparable (S.smul s hs)
      (Set.image (fun f => s • f) family) lambda := by
  rcases h with ⟨U, hU_family, hU_contains⟩
  let U' : CurvilinearRectangle (lambda * (s * δ)) (s * t) :=
    { function := s • U.function,
      interval := U.interval,
      interval_length := by
        rw [U.interval_length]
        congr 1
        field_simp [hs.ne'] <;> ring }
  have h1 : U'.function ∈ Set.image (fun f => s • f) family :=
    ⟨U.function, hU_family, rfl⟩
  have hU'_val : ∀ (x : UnitPoint), U'.function.value x = s * U.function.value x := by
    intro x
    have hfn : U'.function = s • U.function := by simp [U']
    rw [hfn]
    exact C2Function.smul_apply s U.function x
  have h2 : (R.smul s hs).carrier ∪ (S.smul s hs).carrier ⊆ U'.carrier := by
    intro p hp
    rcases hp with (hp | hp)
    · have hq : (p.1, p.2 / s) ∈ R.carrier := (carrier_smul_iff hs p).mp hp
      have hq' : (p.1, p.2 / s) ∈ U.carrier := hU_contains (Or.inl hq)
      simp only [carrier, verticalNeighborhoodOn, Set.mem_setOf_eq]
      constructor
      · exact hq'.1
      · have h6 : |p.2 / s - U.function.value p.1| ≤ lambda * δ := hq'.2
        have h_goal : |p.2 - U'.function.value p.1| ≤ lambda * (s * δ) := by
          rw [hU'_val p.1]
          have h8 : |p.2 - s * U.function.value p.1| = s * |p.2 / s - U.function.value p.1| := by
            rw [show p.2 - s * U.function.value p.1 = s * (p.2 / s - U.function.value p.1) by
                field_simp [hs.ne'] <;> ring]
            rw [abs_mul, abs_of_pos hs]
          rw [h8]
          have h9 : s * |p.2 / s - U.function.value p.1| ≤ s * (lambda * δ) :=
            mul_le_mul_of_nonneg_left h6 hs.le
          have h10 : s * (lambda * δ) = lambda * (s * δ) := by ring
          rw [h10] at h9
          exact h9
        exact h_goal
    · have hq : (p.1, p.2 / s) ∈ S.carrier := (carrier_smul_iff hs p).mp hp
      have hq' : (p.1, p.2 / s) ∈ U.carrier := hU_contains (Or.inr hq)
      simp only [carrier, verticalNeighborhoodOn, Set.mem_setOf_eq]
      constructor
      · exact hq'.1
      · have h6 : |p.2 / s - U.function.value p.1| ≤ lambda * δ := hq'.2
        have h_goal : |p.2 - U'.function.value p.1| ≤ lambda * (s * δ) := by
          rw [hU'_val p.1]
          have h8 : |p.2 - s * U.function.value p.1| = s * |p.2 / s - U.function.value p.1| := by
            rw [show p.2 - s * U.function.value p.1 = s * (p.2 / s - U.function.value p.1) by
                field_simp [hs.ne'] <;> ring]
            rw [abs_mul, abs_of_pos hs]
          rw [h8]
          have h9 : s * |p.2 / s - U.function.value p.1| ≤ s * (lambda * δ) :=
            mul_le_mul_of_nonneg_left h6 hs.le
          have h10 : s * (lambda * δ) = lambda * (s * δ) := by ring
          rw [h10] at h9
          exact h9
        exact h_goal
  exact ⟨U', h1, h2⟩

lemma AreLambdaComparable.smul_backward {δ t : ℝ}
    {R S : CurvilinearRectangle δ t}
    {family : Set C2Function} {lambda s : ℝ} (hs : 0 < s)
    (h : (R.smul s hs).AreLambdaComparable (S.smul s hs)
      (Set.image (fun f => s • f) family) lambda) :
    R.AreLambdaComparable S family lambda := by
  rcases h with ⟨U', hU'_family, hU'_contains⟩
  rcases hU'_family with ⟨f, hf, hU'_fn⟩
  let U : CurvilinearRectangle (lambda * δ) t :=
    { function := (1 / s : ℝ) • U'.function,
      interval := U'.interval,
      interval_length := by
        rw [U'.interval_length]
        congr 1
        field_simp [hs.ne'] <;> ring }
  have hU_fn : U.function = f := by
    have h1 : U.function = (1 / s : ℝ) • U'.function := by simp [U]
    have h2 : (1 / s : ℝ) • U'.function = (1 / s : ℝ) • (s • f) := by
      congr 1
      exact hU'_fn.symm
    have h3 : (1 / s : ℝ) • (s • f) = ((1 / s) * s) • f := C2Function_smul_smul (1 / s) s f
    have h4 : ((1 / s) * s) = 1 := by field_simp [hs.ne']
    calc U.function
      = (1 / s : ℝ) • U'.function := h1
    _ = (1 / s : ℝ) • (s • f) := h2
    _ = ((1 / s) * s) • f := h3
    _ = (1 : ℝ) • f := by rw [h4]
    _ = f := C2Function_one_smul f
  have hU_val : ∀ (x : UnitPoint), U.function.value x = (1 / s) * U'.function.value x := by
    intro x
    have hfn : U.function = (1 / s : ℝ) • U'.function := by simp [U]
    rw [hfn]
    exact C2Function.smul_apply (1 / s) U'.function x
  have hU_contains : R.carrier ∪ S.carrier ⊆ U.carrier := by
    intro p hp
    rcases hp with (hp | hp)
    · have h_eq : (s * p.2) / s = p.2 := by field_simp [hs.ne']
      have h_hp : (p.1, (s * p.2) / s) ∈ R.carrier := by
        rw [h_eq]
        exact hp
      have hq : (p.1, s * p.2) ∈ (R.smul s hs).carrier :=
        (carrier_smul_iff hs (p.1, s * p.2)).mpr h_hp
      have hq' : (p.1, s * p.2) ∈ U'.carrier := hU'_contains (Or.inl hq)
      simp only [carrier, verticalNeighborhoodOn, Set.mem_setOf_eq] at hq' ⊢
      constructor
      · exact hq'.1
      · have h6 : |s * p.2 - U'.function.value p.1| ≤ lambda * (s * δ) := hq'.2
        have h_goal : |p.2 - U.function.value p.1| ≤ lambda * δ := by
          rw [hU_val p.1]
          have h8 : |p.2 - (1 / s) * U'.function.value p.1| =
              (1 / s) * |s * p.2 - U'.function.value p.1| := by
            rw [show p.2 - (1 / s) * U'.function.value p.1 =
                (1 / s) * (s * p.2 - U'.function.value p.1) by
              field_simp [hs.ne'] <;> ring]
            rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / s)]
          rw [h8]
          have h9 : (1 / s) * |s * p.2 - U'.function.value p.1| ≤ (1 / s) * (lambda * (s * δ)) :=
            mul_le_mul_of_nonneg_left h6 (by positivity)
          have h10 : (1 / s) * (lambda * (s * δ)) = lambda * δ := by
            field_simp [hs.ne'] <;> ring
          rw [h10] at h9
          exact h9
        exact h_goal
    · have h_eq2 : (s * p.2) / s = p.2 := by field_simp [hs.ne']
      have h_hp2 : (p.1, (s * p.2) / s) ∈ S.carrier := by
        rw [h_eq2]
        exact hp
      have hq : (p.1, s * p.2) ∈ (S.smul s hs).carrier :=
        (carrier_smul_iff hs (p.1, s * p.2)).mpr h_hp2
      have hq' : (p.1, s * p.2) ∈ U'.carrier := hU'_contains (Or.inr hq)
      simp only [carrier, verticalNeighborhoodOn, Set.mem_setOf_eq] at hq' ⊢
      constructor
      · exact hq'.1
      · have h6 : |s * p.2 - U'.function.value p.1| ≤ lambda * (s * δ) := hq'.2
        have h_goal : |p.2 - U.function.value p.1| ≤ lambda * δ := by
          rw [hU_val p.1]
          have h8 : |p.2 - (1 / s) * U'.function.value p.1| =
              (1 / s) * |s * p.2 - U'.function.value p.1| := by
            rw [show p.2 - (1 / s) * U'.function.value p.1 =
                (1 / s) * (s * p.2 - U'.function.value p.1) by
              field_simp [hs.ne'] <;> ring]
            rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / s)]
          rw [h8]
          have h9 : (1 / s) * |s * p.2 - U'.function.value p.1| ≤ (1 / s) * (lambda * (s * δ)) :=
            mul_le_mul_of_nonneg_left h6 (by positivity)
          have h10 : (1 / s) * (lambda * (s * δ)) = lambda * δ := by
            field_simp [hs.ne'] <;> ring
          rw [h10] at h9
          exact h9
        exact h_goal
  exact ⟨U, by rw [hU_fn]; exact hf, hU_contains⟩

lemma AreLambdaComparable.smul_iff {δ t : ℝ}
    {R S : CurvilinearRectangle δ t}
    {family : Set C2Function} {lambda s : ℝ} (hs : 0 < s) :
    (R.smul s hs).AreLambdaComparable (S.smul s hs)
      (Set.image (fun f => s • f) family) lambda ↔
    R.AreLambdaComparable S family lambda :=
  ⟨AreLambdaComparable.smul_backward hs, AreLambdaComparable.smul_forward hs⟩

lemma AreLambdaIncomparable.smul_iff {δ t : ℝ}
    {R S : CurvilinearRectangle δ t}
    {family : Set C2Function} {lambda s : ℝ} (hs : 0 < s) :
    (R.smul s hs).AreLambdaIncomparable (S.smul s hs)
      (Set.image (fun f => s • f) family) lambda ↔
    R.AreLambdaIncomparable S family lambda := by
  simp only [CurvilinearRectangle.AreLambdaIncomparable]
  rw [AreLambdaComparable.smul_iff hs]

end CurvilinearRectangle

-- ============================================================================
-- RectangleFamily scaling
-- ============================================================================

namespace RectangleFamily

/-- Scale every rectangle in a family by `s`. -/
def smul {δ t : ℝ} (s : ℝ) (hs : 0 < s)
    (R : RectangleFamily δ t) : RectangleFamily (s * δ) (s * t) :=
  { card := R.card,
    rectangle := fun i => (R.rectangle i).smul s hs }

lemma smul_card {δ t : ℝ} {s : ℝ} (hs : 0 < s)
    (R : RectangleFamily δ t) :
    (R.smul s hs).card = R.card := rfl

lemma smul_rectangle {δ t : ℝ} {s : ℝ} (hs : 0 < s)
    (R : RectangleFamily δ t) (i : Fin R.card) :
    (R.smul s hs).rectangle i = (R.rectangle i).smul s hs := rfl

lemma smul_nonempty {δ t : ℝ} {s : ℝ} (hs : 0 < s)
    (R : RectangleFamily δ t) :
    (R.smul s hs).Nonempty ↔ R.Nonempty := by
  simp [RectangleFamily.Nonempty, smul_card]

lemma smul_centersIn_forward {δ t : ℝ} {s : ℝ} (hs : 0 < s)
    {R : RectangleFamily δ t} {family : Set C2Function}
    (h : R.CentersIn family) :
    (R.smul s hs).CentersIn (Set.image (fun f => s • f) family) := by
  intro i
  have h1 : (R.rectangle i).function ∈ family := h i
  exact ⟨(R.rectangle i).function, h1, rfl⟩

lemma smul_centersIn_backward {δ t : ℝ} {s : ℝ} (hs : 0 < s)
    {R : RectangleFamily δ t} {family : Set C2Function}
    (h : (R.smul s hs).CentersIn (Set.image (fun f => s • f) family)) :
    R.CentersIn family := by
  intro i
  have h1 : s • (R.rectangle i).function ∈ Set.image (fun f => s • f) family := h i
  rcases h1 with ⟨g, hg, h_eq⟩
  have h2 : (R.rectangle i).function = g :=
    C2Function_smul_injective hs h_eq.symm
  rw [h2]
  exact hg

lemma smul_overCentralQuarterOf {δ t : ℝ} {s : ℝ} (hs : 0 < s)
    {R : RectangleFamily δ t} {I : ParameterInterval}
    (h : R.IsOverCentralQuarterOf I) :
    (R.smul s hs).IsOverCentralQuarterOf I := by
  intro i
  exact CurvilinearRectangle.IsOverCentralQuarterOf.smul hs (h i)

lemma smul_pairwiseIncomparable_forward {δ t : ℝ} {s : ℝ} (hs : 0 < s)
    {R : RectangleFamily δ t} {family : Set C2Function} {lambda : ℝ}
    (h : R.IsPairwiseIncomparable family lambda) :
    (R.smul s hs).IsPairwiseIncomparable
      (Set.image (fun f => s • f) family) lambda := by
  intro i j hij
  have h1 : (R.rectangle i).AreLambdaIncomparable (R.rectangle j) family lambda :=
    h i j hij
  exact (CurvilinearRectangle.AreLambdaIncomparable.smul_iff hs).mpr h1

lemma smul_pairwiseIncomparable_backward {δ t : ℝ} {s : ℝ} (hs : 0 < s)
    {R : RectangleFamily δ t} {family : Set C2Function} {lambda : ℝ}
    (h : (R.smul s hs).IsPairwiseIncomparable
      (Set.image (fun f => s • f) family) lambda) :
    R.IsPairwiseIncomparable family lambda := by
  intro i j hij
  have h1 : ((R.smul s hs).rectangle i).AreLambdaIncomparable
      ((R.smul s hs).rectangle j)
      (Set.image (fun f => s • f) family) lambda :=
    h i j hij
  have h2 : (R.smul s hs).rectangle i = (R.rectangle i).smul s hs := rfl
  have h3 : (R.smul s hs).rectangle j = (R.rectangle j).smul s hs := rfl
  rw [h2, h3] at h1
  exact (CurvilinearRectangle.AreLambdaIncomparable.smul_iff hs).mp h1

/-- Tangent count is invariant under positive vertical scaling. -/
lemma smul_tangentCount {δ t : ℝ} {R : CurvilinearRectangle δ t}
    {F : FiniteFunctionFamily} {lambda s : ℝ} (hs : 0 < s) :
    RectangleFamily.tangentCount (R.smul s hs) (s • F) lambda =
    RectangleFamily.tangentCount R F lambda := by
  classical
  let g : C2Function → C2Function := fun f => s • f
  have h_inj : Function.Injective g := C2Function_smul_injective hs
  have h_iff : ∀ (f : C2Function),
      (R.smul s hs).IsLambdaTangent (g f) lambda ↔ R.IsLambdaTangent f lambda :=
    fun f => CurvilinearRectangle.IsLambdaTangent.smul_iff hs
  have h_filter : (Finset.image g F.toFinset).filter
        (fun f' => (R.smul s hs).IsLambdaTangent f' lambda) =
      Finset.image g (F.toFinset.filter (fun f => R.IsLambdaTangent f lambda)) := by
    ext f'
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨f, hf, rfl⟩, h_tan⟩
      exact ⟨f, ⟨hf, (h_iff f).mp h_tan⟩, rfl⟩
    · rintro ⟨f, ⟨hf, h_tan⟩, rfl⟩
      exact ⟨⟨f, hf, rfl⟩, (h_iff f).mpr h_tan⟩
  have h_toFinset : (s • F).toFinset = Finset.image g F.toFinset := by
    ext f
    simp [FiniteFunctionFamily.toFinset, FiniteFunctionFamily.smul_carrier,
      Set.Finite.mem_toFinset]
    <;> aesop
  rw [RectangleFamily.tangentCount, h_toFinset, h_filter,
    Finset.card_image_of_injective _ h_inj]
  <;> rfl

/-- Bipartite normalized count is invariant under scaling. -/
lemma smul_bipartiteNormalizedCount {s : ℝ} (hs : 0 < s)
    {W B : FiniteFunctionFamily} {mu nu : ℕ} :
    RectangleFamily.bipartiteNormalizedCount (s • W) (s • B) mu nu =
    RectangleFamily.bipartiteNormalizedCount W B mu nu := by
  simp [RectangleFamily.bipartiteNormalizedCount,
    FiniteFunctionFamily.smul_card hs]

end RectangleFamily

-- ============================================================================
-- Separation and diameter transport
-- ============================================================================

namespace FiniteFunctionFamily

lemma smul_AreSeparated {s : ℝ} (hs : 0 < s)
    {W B : FiniteFunctionFamily} {t : ℝ} :
    (s • W).AreSeparated (s • B) (s * t) ↔ W.AreSeparated B t := by
  constructor
  · intro h w hw b hb
    have h1 : s • w ∈ (s • W).carrier := by
      exact (mem_smul_iff hs).mpr ⟨w, hw, rfl⟩
    have h2 : s • b ∈ (s • B).carrier := by
      exact (mem_smul_iff hs).mpr ⟨b, hb, rfl⟩
    have h3 : s * t ≤ dist (s • w) (s • b) := h h1 h2
    have h4 : dist (s • w) (s • b) = s * dist w b := by
      simpa [c2Distance_eq_dist] using c2Distance_smul hs.le w b
    rw [h4] at h3
    exact le_of_mul_le_mul_left h3 hs
  · intro h w' hw' b' hb'
    rcases (mem_smul_iff hs).mp hw' with ⟨w, hw, rfl⟩
    rcases (mem_smul_iff hs).mp hb' with ⟨b, hb, rfl⟩
    have h4 : t ≤ dist w b := h hw hb
    have h5 : dist (s • w) (s • b) = s * dist w b := by
      simpa [c2Distance_eq_dist] using c2Distance_smul hs.le w b
    rw [h5]
    exact mul_le_mul_of_nonneg_left h4 hs.le

lemma smul_DiameterLE {s : ℝ} (hs : 0 < s)
    {F : FiniteFunctionFamily} {d : ℝ} :
    (s • F).DiameterLE (s * d) ↔ F.DiameterLE d := by
  constructor
  · intro h f hf g hg
    have h1 : s • f ∈ (s • F).carrier := by
      exact (mem_smul_iff hs).mpr ⟨f, hf, rfl⟩
    have h2 : s • g ∈ (s • F).carrier := by
      exact (mem_smul_iff hs).mpr ⟨g, hg, rfl⟩
    have h3 : dist (s • f) (s • g) ≤ s * d := h h1 h2
    have h4 : dist (s • f) (s • g) = s * dist f g := by
      simpa [c2Distance_eq_dist] using c2Distance_smul hs.le f g
    rw [h4] at h3
    exact le_of_mul_le_mul_left h3 hs
  · intro h f' hf' g' hg'
    rcases (mem_smul_iff hs).mp hf' with ⟨f, hf, rfl⟩
    rcases (mem_smul_iff hs).mp hg' with ⟨g, hg, rfl⟩
    have h4 : dist f g ≤ d := h hf hg
    have h5 : dist (s • f) (s • g) = s * dist f g := by
      simpa [c2Distance_eq_dist] using c2Distance_smul hs.le f g
    rw [h5]
    exact mul_le_mul_of_nonneg_left h4 hs.le

end FiniteFunctionFamily

-- ============================================================================
-- Finset centers transport
-- ============================================================================

namespace Finset

lemma image_smul_card {s : ℝ} (hs : 0 < s) (centers : Finset C2Function) :
    (centers.image (fun f : C2Function => s • f)).card = centers.card := by
  have h_inj : Function.Injective (fun f : C2Function => s • f) := C2Function_smul_injective hs
  exact Finset.card_image_of_injective centers h_inj

lemma mem_image_smul {s : ℝ} (hs : 0 < s) {centers : Finset C2Function}
    {c : C2Function} :
    s • c ∈ centers.image (fun f : C2Function => s • f) ↔ c ∈ centers := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨d, hd, h_eq⟩
    have h2 : c = d := C2Function_smul_injective hs h_eq.symm
    rw [h2]
    exact hd
  · intro h
    exact Finset.mem_image.mpr ⟨c, h, rfl⟩

end Finset

-- ============================================================================
-- RectangleSubfamily transport
-- ============================================================================

namespace RectangleSubfamily

/--
Given a subfamily of the scaled rectangle family, produce the corresponding
subfamily of the original family with the same cardinality and embedding.
-/
def ofSmul {δ t : ℝ} {s : ℝ} {hs : 0 < s}
    {R : RectangleFamily δ t}
    (S' : RectangleSubfamily (R.smul s hs)) :
    RectangleSubfamily R :=
  { card := S'.card,
    embedding := S'.embedding }

lemma ofSmul_family_smul {δ t : ℝ} {s : ℝ} {hs : 0 < s}
    {R : RectangleFamily δ t}
    (S' : RectangleSubfamily (R.smul s hs)) :
    (S'.ofSmul.family).smul s hs = S'.family := by
  rfl

end RectangleSubfamily

end Kakeya.Cinematic
