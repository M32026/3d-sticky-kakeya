import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Max-score broadness selection lemma

Given a finite family of tubes, find a scale `thetaLocal ∈ [δ, 1]` such that
for all unit w and r ∈ [δ, thetaLocal]:
  `#{T ∈ through : angle(T.direction, w) ≤ r} ≤ (r/thetaLocal)^eta * #through`
-/

noncomputable section

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

section MaxScore

variable {δ eta : ℝ} (hδ : 0 < δ) (hδ_le1 : δ ≤ 1) (heta : 0 < eta)

/-- The unit sphere in Point3. -/
def unitSphere : Set Point3 := {w | ‖w‖ = 1}

lemma isCompact_unitSphere : IsCompact (unitSphere : Set Point3) := by
  have hnorm : Continuous (fun w : Point3 => ‖w‖) := continuous_norm
  have h1 : IsClosed (unitSphere : Set Point3) :=
    isClosed_singleton.preimage hnorm
  have h2 : (unitSphere : Set Point3) ⊆ Metric.closedBall (0 : Point3) 1 := by
    intro w hw
    have h3 : ‖w‖ = 1 := by simpa [unitSphere] using hw
    simpa [Metric.mem_closedBall] using h3.le
  exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Point3) 1) h1 h2

/-- Continuity of angle in second argument. -/
lemma continuous_angle_right (v : Point3) :
    Continuous fun w : Point3 => hairbrushAcuteDirectionAngle v w := by
  have h1 : Continuous (fun w : Point3 => inner ℝ v w) :=
    continuous_const.inner continuous_id
  have h2 : Continuous (fun w : Point3 => Real.arccos (inner ℝ v w)) :=
    Real.continuous_arccos.comp h1
  have h3 : Continuous (fun w : Point3 => Real.pi - Real.arccos (inner ℝ v w)) :=
    continuous_const.sub h2
  exact h2.min h3

/-- The set of radii at which a finite tube-subset is cap-coverable is closed. -/
lemma isClosed_coverable {δ' : ℝ} (S : Finset (Kakeya.DeltaTube δ')) :
    IsClosed {r : ℝ | ∃ (w : Point3), ‖w‖ = 1 ∧
      ∀ T ∈ S, hairbrushAcuteDirectionAngle T.direction w ≤ r} := by
  let K : Type _ := {w : Point3 // w ∈ unitSphere}
  have hK_compact : CompactSpace K :=
    isCompact_iff_compactSpace.mp isCompact_unitSphere
  let E_of : Finset (Kakeya.DeltaTube δ') → Set (K × ℝ) := fun S' =>
    {p | ∀ T ∈ S', hairbrushAcuteDirectionAngle T.direction p.1.val ≤ p.2}
  have hE_of_closed : ∀ (S' : Finset (Kakeya.DeltaTube δ')), IsClosed (E_of S') := by
    intro S'
    induction S' using Finset.induction with
    | empty =>
      simp [E_of]
    | @insert T S' hT ih =>
      have h_eq : E_of (insert T S') = E_of S' ∩
          {p : K × ℝ | hairbrushAcuteDirectionAngle T.direction p.1.val ≤ p.2} := by
        ext p
        simp [E_of, Finset.mem_insert]
        <;> tauto
      rw [h_eq]
      let f : K × ℝ → ℝ := fun p =>
          hairbrushAcuteDirectionAngle T.direction p.1.val - p.2
      have h_cont : Continuous f := by
        have h1 : Continuous (fun (p : K × ℝ) =>
            hairbrushAcuteDirectionAngle T.direction (p.1 : Point3)) :=
          (continuous_angle_right T.direction).comp
            (continuous_subtype_val.comp continuous_fst)
        exact h1.sub continuous_snd
      have h_set_closed : IsClosed {p : K × ℝ | hairbrushAcuteDirectionAngle T.direction p.1.val ≤ p.2} := by
        have h4 : {p : K × ℝ | hairbrushAcuteDirectionAngle T.direction p.1.val ≤ p.2} =
            f ⁻¹' Set.Iic 0 := by
          ext p
          simp [Set.mem_preimage, f]
        rw [h4]
        exact isClosed_Iic.preimage h_cont
      exact IsClosed.inter ih h_set_closed
  let E := E_of S
  have hE_closed : IsClosed E := hE_of_closed S
  have h_proj_closed : IsClosed (Prod.snd '' E) :=
    isClosedMap_snd_of_compactSpace E hE_closed
  have h_eq : (Prod.snd '' E) =
      {r : ℝ | ∃ (w : Point3), ‖w‖ = 1 ∧
        ∀ T ∈ S, hairbrushAcuteDirectionAngle T.direction w ≤ r} := by
    ext r
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hxE, rfl⟩
      exact ⟨x.1.val, x.1.property, hxE⟩
    · rintro ⟨w, hw, h⟩
      let x : K × ℝ := (⟨w, by simpa [unitSphere] using hw⟩, r)
      have hxE : x ∈ E := h
      exact ⟨x, hxE, rfl⟩
  rw [←h_eq]
  exact h_proj_closed

variable {through : Finset (Kakeya.DeltaTube δ)}

/-- Coverability proposition for a subset at radius r. -/
def Coverable (S : Finset (Kakeya.DeltaTube δ)) (r : ℝ) : Prop :=
  ∃ (w : Point3), ‖w‖ = 1 ∧ ∀ T ∈ S, hairbrushAcuteDirectionAngle T.direction w ≤ r

/-- Maximum number of tubes from `through` fitable in a direction cap of radius r. -/
def maxCapCount (r : ℝ) : ℕ :=
  through.powerset.sup (fun S => if Coverable S r then S.card else 0)

lemma maxCapCount_ge_count (r : ℝ) (w : Point3) (hw : ‖w‖ = 1) :
    (through.filter fun T => hairbrushAcuteDirectionAngle T.direction w ≤ r).card ≤
      maxCapCount (through := through) r := by
  let S := through.filter fun T => hairbrushAcuteDirectionAngle T.direction w ≤ r
  have hS : S ∈ through.powerset :=
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hcover : Coverable S r := by
    refine ⟨w, hw, fun T hT => (Finset.mem_filter.mp hT).2⟩
  have h_val : (if Coverable S r then S.card else 0) = S.card := by
    rw [if_pos hcover]
  have h : S.card ≤ maxCapCount (through := through) r := by
    let f : Finset (Kakeya.DeltaTube δ) → ℕ := fun S => if Coverable S r then S.card else 0
    have h' : f S ≤ through.powerset.sup f := Finset.le_sup hS
    have h_fS : f S = S.card := by
      simpa [f, hcover] using rfl
    rw [h_fS] at h'
    exact h'
  exact h

lemma maxCapCount_le_card (r : ℝ) :
    maxCapCount (through := through) r ≤ through.card := by
  apply Finset.sup_le
  intro S _
  by_cases hcover : Coverable S r
  · rw [if_pos hcover]
    have hsub : S ⊆ through := Finset.mem_powerset.mp ‹S ∈ through.powerset›
    exact Finset.card_le_card hsub
  · rw [if_neg hcover]
    exact Nat.zero_le _

lemma maxCapCount_mono (r1 r2 : ℝ) (h : r1 ≤ r2) :
    maxCapCount (through := through) r1 ≤
    maxCapCount (through := through) r2 := by
  apply Finset.sup_le
  intro S hS
  by_cases hcover1 : Coverable S r1
  · have hcover2 : Coverable S r2 := by
      rcases hcover1 with ⟨w, hw_norm, h1⟩
      exact ⟨w, hw_norm, fun T hT => (h1 T hT).trans h⟩
    have h_val1 : (if Coverable S r1 then S.card else 0) = S.card := by
      rw [if_pos hcover1]
    have h_f2S : (if Coverable S r2 then S.card else 0) = S.card := by
      rw [if_pos hcover2]
    have h_le2 : (if Coverable S r2 then S.card else 0) ≤
        through.powerset.sup (fun S => if Coverable S r2 then S.card else 0) := by
      exact Finset.le_sup (f := (fun S => if Coverable S r2 then S.card else 0)) hS
    rw [h_val1]
    rw [h_f2S] at h_le2
    exact h_le2
  · have h_val : (if Coverable S r1 then S.card else 0) = 0 := by
      rw [if_neg hcover1]
    rw [h_val]
    exact Nat.zero_le _

/-- N(r) ≥ k iff some subset of size ≥ k is coverable at r. -/
lemma maxCapCount_ge_iff (r : ℝ) {k : ℕ} (hk : 0 < k) :
    maxCapCount (through := through) r ≥ k ↔
      ∃ S ∈ through.powerset, S.card ≥ k ∧ Coverable S r := by
  dsimp only [maxCapCount]
  constructor
  · intro h
    have h_exists : ∃ S ∈ through.powerset,
        (if Coverable S r then S.card else 0) ≥ k := by
      let f : Finset (Kakeya.DeltaTube δ) → ℕ := fun S => if Coverable S r then S.card else 0
      have h_nonempty : through.powerset.Nonempty :=
        ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
      rcases Finset.exists_max_image through.powerset f h_nonempty with ⟨S0, hS0, hmax⟩
      have h_eq : f S0 = maxCapCount (through := through) r := by
        have h1 : f S0 ≤ through.powerset.sup f := Finset.le_sup hS0
        have h2 : through.powerset.sup f ≤ f S0 := by
          apply Finset.sup_le
          intro y hy
          exact hmax y hy
        exact le_antisymm h1 h2
      have h_ge : f S0 ≥ k := by
        rw [h_eq] <;> exact h
      exact ⟨S0, hS0, h_ge⟩
    rcases h_exists with ⟨S, hS, hge⟩
    by_cases hcover : Coverable S r
    · have hcard : S.card ≥ k := by
        rw [if_pos hcover] at hge <;> exact hge
      exact ⟨S, hS, hcard, hcover⟩
    · rw [if_neg hcover] at hge
      linarith
  · rintro ⟨S, hS, hcard, hcover⟩
    have h_val : (if Coverable S r then S.card else 0) = S.card := by
      rw [if_pos hcover]
    let f : Finset (Kakeya.DeltaTube δ) → ℕ := fun S => if Coverable S r then S.card else 0
    have h : f S ≤ through.powerset.sup f := Finset.le_sup hS
    have h_fS : f S = S.card := by simpa [f, hcover] using rfl
    rw [h_fS] at h
    exact hcard.trans h

/-- The set P_k = {r ∈ [δ,1] : N(r) ≥ k} is closed. -/
lemma isClosed_P (k : ℕ) :
    IsClosed {r : ℝ | δ ≤ r ∧ r ≤ 1 ∧ maxCapCount (through := through) r ≥ k} := by
  by_cases hk : k = 0
  · have h_set : {r : ℝ | δ ≤ r ∧ r ≤ 1 ∧ maxCapCount (through := through) r ≥ k} = Set.Icc δ 1 := by
      ext r
      simp [hk]
      <;> constructor <;> intro h <;> exact ⟨h.1, h.2⟩
    rw [h_set]
    exact isClosed_Icc
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
    have h_set_eq : {r : ℝ | δ ≤ r ∧ r ≤ 1 ∧ maxCapCount (through := through) r ≥ k} =
        Set.Icc δ 1 ∩ ⋃ S ∈ through.powerset.filter (fun S => S.card ≥ k),
          {r : ℝ | Coverable S r} := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro h
        have h1 : maxCapCount (through := through) r ≥ k := h.2.2
        have h2 := (maxCapCount_ge_iff r hk_pos).mp h1
        rcases h2 with ⟨S, hS_powerset, hcard, hcover⟩
        have hS_filter : S ∈ through.powerset.filter (fun S => S.card ≥ k) := by
          simp only [Finset.mem_filter, hS_powerset, hcard, true_and]
        exact ⟨⟨h.1, h.2.1⟩, S, hS_filter, hcover⟩
      · rintro ⟨h_range, S, hS_filter, hcover⟩
        have hS_powerset : S ∈ through.powerset := (Finset.mem_filter.mp hS_filter).1
        have hcard : S.card ≥ k := (Finset.mem_filter.mp hS_filter).2
        have h3 : maxCapCount (through := through) r ≥ k :=
          (maxCapCount_ge_iff r hk_pos).mpr ⟨S, hS_powerset, hcard, hcover⟩
        exact ⟨h_range.1, h_range.2, h3⟩
    rw [h_set_eq]
    have h : IsClosed (⋃ S ∈ through.powerset.filter (fun S => S.card ≥ k), {r : ℝ | Coverable S r}) := by
      exact isClosed_biUnion_finset (fun S _ => isClosed_coverable S)
    exact IsClosed.inter isClosed_Icc h

/-- The main max-score broadness selection lemma. -/
theorem max_score_broadness
    {δ eta : ℝ} (hδ : 0 < δ) (hδ_le1 : δ ≤ 1) (heta : 0 < eta)
    {through : Finset (Kakeya.DeltaTube δ)}
    (hthrough : through.Nonempty) :
    ∃ thetaLocal : ℝ, δ ≤ thetaLocal ∧ thetaLocal ≤ 1 ∧
      ∀ (w : Point3), ‖w‖ = 1 → ∀ r : ℝ, δ ≤ r → r ≤ thetaLocal →
        ((through.filter fun T => hairbrushAcuteDirectionAngle T.direction w ≤ r).card : ℝ) ≤
          Real.rpow (r / thetaLocal) eta * (through.card : ℝ) := by
  let N := maxCapCount (through := through)
  let P (k : ℕ) : Set ℝ := {r | δ ≤ r ∧ r ≤ 1 ∧ N r ≥ k}
  have hP_closed : ∀ k, IsClosed (P k) := isClosed_P
  let a (k : ℕ) : ℝ := sInf (P k)
  let activeKs : Finset ℕ :=
    Finset.filter (fun k => (P k).Nonempty) (Finset.range (through.card + 1))
  let candidateRadii : Finset ℝ :=
    insert δ (insert 1 (Finset.image a activeKs))
  have h_candidate_nonempty : candidateRadii.Nonempty := by
    simp [candidateRadii]
  have h_candidates_in_range : ∀ r ∈ candidateRadii, δ ≤ r ∧ r ≤ 1 := by
    intro r hr
    have h_cases : r = δ ∨ r = 1 ∨ ∃ k ∈ activeKs, a k = r := by
      simp only [candidateRadii, Finset.mem_insert, Finset.mem_image] at hr
      tauto
    rcases h_cases with (h_eq | h_eq | ⟨k, hk, h_eq⟩)
    · rw [h_eq]
      exact ⟨by linarith, hδ_le1⟩
    · rw [h_eq]
      exact ⟨hδ_le1, by linarith⟩
    · have hk_active : k ∈ activeKs := hk
      have hP_nonempty : (P k).Nonempty := (Finset.mem_filter.mp hk_active).2
      have h1δ : ∀ x ∈ P k, δ ≤ x := fun x hx => hx.1
      have h2 : δ ≤ a k := le_csInf hP_nonempty h1δ
      have h3 : a k ≤ 1 := by
        have h_closed2 : IsClosed (P k) := hP_closed k
        have h_bdd2 : BddBelow (P k) := ⟨δ, fun y hy => hy.1⟩
        have h_ak_in : a k ∈ P k := h_closed2.csInf_mem hP_nonempty h_bdd2
        exact h_ak_in.2.1
      rw [←h_eq]
      exact ⟨h2, h3⟩
  rcases Finset.exists_max_image candidateRadii
      (fun r : ℝ => (N r : ℝ) / Real.rpow r eta) h_candidate_nonempty with
    ⟨rStar, hrStar_in, hmax⟩
  have hrStar_range : δ ≤ rStar ∧ rStar ≤ 1 := h_candidates_in_range rStar hrStar_in
  have h_main_ineq : ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      (N r : ℝ) / Real.rpow r eta ≤ (N rStar : ℝ) / Real.rpow rStar eta := by
    intro r hr1 hr2
    let k := N r
    have hk_in_range : k ∈ Finset.range (through.card + 1) := by
      simp [Finset.mem_range, N]
      <;> exact maxCapCount_le_card r
    have h_r_in_Pk : r ∈ P k := by
      exact ⟨hr1, hr2, by simp [k]⟩
    have hP_k_nonempty : (P k).Nonempty := ⟨r, h_r_in_Pk⟩
    have hk_active : k ∈ activeKs := by
      simp only [activeKs, Finset.mem_filter, hk_in_range, hP_k_nonempty, true_and]
    have ha_k_in_Pk : a k ∈ P k := by
      have h_closed : IsClosed (P k) := hP_closed k
      have h_bdd : BddBelow (P k) := ⟨δ, fun y hy => hy.1⟩
      exact h_closed.csInf_mem hP_k_nonempty h_bdd
    have h_bdd : BddBelow (P k) := ⟨δ, fun y hy => hy.1⟩
    have ha_k_le_r : a k ≤ r := csInf_le h_bdd h_r_in_Pk
    have hN_ak : N (a k) = k := by
      have h1 : N (a k) ≥ k := ha_k_in_Pk.2.2
      have h2 : N (a k) ≤ N r := maxCapCount_mono (a k) r ha_k_le_r
      simpa [k] using h2.antisymm h1
    have h5 : 0 < a k := by
      have hδak : δ ≤ a k := ha_k_in_Pk.1
      linarith [hδ]
    have h6 : 0 < r := by linarith [hδ]
    have h7 : Real.rpow (a k) eta ≤ Real.rpow r eta :=
      Real.rpow_le_rpow (by linarith) ha_k_le_r heta.le
    have h8 : (N r : ℝ) = (N (a k) : ℝ) := by
      simp [hN_ak, k]
    have h4 : (N r : ℝ) / Real.rpow r eta ≤ (N (a k) : ℝ) / Real.rpow (a k) eta := by
      rw [h8]
      have hA_nonneg : 0 ≤ (N (a k) : ℝ) := by positivity
      have hC_pos : 0 < Real.rpow (a k) eta := Real.rpow_pos_of_pos h5 _
      exact div_le_div_of_nonneg_left hA_nonneg hC_pos h7
    have h9 : a k ∈ candidateRadii := by
      simp only [candidateRadii, Finset.mem_insert, Finset.mem_image]
      exact Or.inr (Or.inr ⟨k, hk_active, rfl⟩)
    have h10 : (N (a k) : ℝ) / Real.rpow (a k) eta ≤
        (N rStar : ℝ) / Real.rpow rStar eta := hmax (a k) h9
    exact h4.trans h10
  have hN_rStar_le : N rStar ≤ through.card := maxCapCount_le_card rStar
  have h_final : ∀ (w : Point3), ‖w‖ = 1 → ∀ r : ℝ, δ ≤ r → r ≤ rStar →
      ((through.filter fun T => hairbrushAcuteDirectionAngle T.direction w ≤ r).card : ℝ) ≤
        Real.rpow (r / rStar) eta * (through.card : ℝ) := by
    intro w hw r hr1 hr2
    have h1 : (through.filter fun T => hairbrushAcuteDirectionAngle T.direction w ≤ r).card ≤ N r :=
      maxCapCount_ge_count r w hw
    have h2 : δ ≤ r := hr1
    have h3 : r ≤ 1 := hr2.trans hrStar_range.2
    have h4 : (N r : ℝ) / Real.rpow r eta ≤ (N rStar : ℝ) / Real.rpow rStar eta :=
      h_main_ineq r h2 h3
    have h5 : 0 < r := by linarith [hδ]
    have h6 : 0 < rStar := by linarith [hrStar_range.1]
    have h10 : 0 < Real.rpow r eta := Real.rpow_pos_of_pos h5 _
    have h11 : 0 < Real.rpow rStar eta := Real.rpow_pos_of_pos h6 _
    have h_div : Real.rpow (r / rStar) eta = Real.rpow r eta / Real.rpow rStar eta :=
      Real.div_rpow (by linarith) (by linarith) eta
    have h7 : (N r : ℝ) ≤ Real.rpow (r / rStar) eta * (N rStar : ℝ) := by
      rw [h_div]
      have h9 : (N r : ℝ) / Real.rpow r eta ≤ (N rStar : ℝ) / Real.rpow rStar eta := h4
      have h_goal : (N r : ℝ) ≤ (N rStar : ℝ) * (Real.rpow r eta / Real.rpow rStar eta) := by
        have h_eq1 : (N r : ℝ) = ((N r : ℝ) / Real.rpow r eta) * Real.rpow r eta := by
          field_simp [h10.ne'] <;> ring
        rw [h_eq1]
        have h_pos : 0 ≤ Real.rpow r eta := by positivity
        have h_mul : ((N r : ℝ) / Real.rpow r eta) * Real.rpow r eta ≤
            ((N rStar : ℝ) / Real.rpow rStar eta) * Real.rpow r eta :=
          mul_le_mul_of_nonneg_right h9 h_pos
        have h_rhs : ((N rStar : ℝ) / Real.rpow rStar eta) * Real.rpow r eta =
            (N rStar : ℝ) * (Real.rpow r eta / Real.rpow rStar eta) := by ring
        rw [h_rhs] at h_mul
        exact h_mul
      have h_final_goal : (N r : ℝ) ≤ (Real.rpow r eta / Real.rpow rStar eta) * (N rStar : ℝ) := by
        have h_comm : (N rStar : ℝ) * (Real.rpow r eta / Real.rpow rStar eta) =
            (Real.rpow r eta / Real.rpow rStar eta) * (N rStar : ℝ) := by ring
        rw [h_comm] at h_goal
        exact h_goal
      exact h_final_goal
    have h12 : (N rStar : ℝ) ≤ (through.card : ℝ) := by exact_mod_cast hN_rStar_le
    calc ((through.filter fun T => hairbrushAcuteDirectionAngle T.direction w ≤ r).card : ℝ)
      ≤ (N r : ℝ) := by exact_mod_cast h1
    _ ≤ Real.rpow (r / rStar) eta * (N rStar : ℝ) := h7
    _ ≤ Real.rpow (r / rStar) eta * (through.card : ℝ) := by
      have h_rpos : 0 < r / rStar := by positivity
      have h_pos2 : 0 ≤ Real.rpow (r / rStar) eta := Real.rpow_nonneg (by positivity) _
      exact mul_le_mul_of_nonneg_left h12 h_pos2
  exact ⟨rStar, hrStar_range.1, hrStar_range.2, h_final⟩

end MaxScore

end Kakeya.Assouad
