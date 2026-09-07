import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.Reparametrize
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ReparametrizeBridge
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Lenses

/-!
# Reparametrize graph lenses over a parameter interval

Given a `GraphLens` whose endpoints lie in `I.carrier`, produce a new
`GraphLens` between the reparametrized functions with endpoints pulled back
to `UnitPoint` via the inverse of `phiMap I`.
-/

noncomputable section

namespace Kakeya.Cinematic

open C2Function

local instance instDecidableEqC2FunctionLensReparam : DecidableEq C2Function :=
  Classical.decEq _

/-- Inverse of `phiMap I` on `I.carrier`. -/
def invPhiMap (I : ParameterInterval) (hI : 0 < I.length)
    (y : UnitPoint) (hy : y ∈ I.carrier) : UnitPoint :=
  let val := ((y : ℝ) - I.left) / I.length
  have h1 : 0 ≤ val := by
    have h_a : 0 ≤ (y : ℝ) - I.left := by linarith [hy.1]
    exact div_nonneg h_a (by linarith)
  have h2 : val ≤ 1 := by
    have h_b : (y : ℝ) - I.left ≤ I.length := by
      have h_c : I.length = I.right - I.left := by rfl
      rw [h_c]
      linarith [hy.2]
    have h_d : ((y : ℝ) - I.left) / I.length ≤ 1 := by
      rw [div_le_one (by linarith)] <;> linarith
    exact h_d
  ⟨val, ⟨h1, h2⟩⟩

lemma phiMap_invPhiMap (I : ParameterInterval) (hI : 0 < I.length)
    (y : UnitPoint) (hy : y ∈ I.carrier) :
    phiMap I (invPhiMap I hI y hy) = y := by
  apply Subtype.ext
  dsimp only [invPhiMap, phiMap, ParameterInterval.reparamPhi]
  field_simp [hI.ne'] <;> ring

lemma invPhiMap_phiMap (I : ParameterInterval) (hI : 0 < I.length)
    (x : UnitPoint) :
    invPhiMap I hI (phiMap I x) (phiMap_mem_carrier I x) = x := by
  apply Subtype.ext
  dsimp only [invPhiMap, phiMap, ParameterInterval.reparamPhi]
  field_simp [hI.ne'] <;> ring

lemma invPhiMap_strictMono (I : ParameterInterval) (hI : 0 < I.length) :
    ∀ (y₁ y₂ : UnitPoint) (hy₁ : y₁ ∈ I.carrier) (hy₂ : y₂ ∈ I.carrier),
      (y₁ : ℝ) < (y₂ : ℝ) →
      (invPhiMap I hI y₁ hy₁ : ℝ) < (invPhiMap I hI y₂ hy₂ : ℝ) := by
  intro y₁ y₂ hy₁ hy₂ h
  dsimp only [invPhiMap]
  have h5 : ((y₁ : ℝ) - I.left) / I.length < ((y₂ : ℝ) - I.left) / I.length := by
    apply div_lt_div_of_pos_right
    · linarith
    · exact hI
  exact h5

namespace GraphLens

/--
Reparametrize a graph lens over `I`. The endpoints must lie in `I.carrier`.
-/
def reparam (L : GraphLens) (I : ParameterInterval) (hI : 0 < I.length)
    (hleft : L.left ∈ I.carrier) (hright : L.right ∈ I.carrier) : GraphLens :=
  let left' := invPhiMap I hI L.left hleft
  let right' := invPhiMap I hI L.right hright
  have h_phi_left : (phiMap I left' : ℝ) = (L.left : ℝ) := by
    exact congr_arg (fun (p : UnitPoint) => (p : ℝ)) (phiMap_invPhiMap I hI L.left hleft)
  have h_phi_right : (phiMap I right' : ℝ) = (L.right : ℝ) := by
    exact congr_arg (fun (p : UnitPoint) => (p : ℝ)) (phiMap_invPhiMap I hI L.right hright)
  have h_f_ne_g : L.f.reparam I ≠ L.g.reparam I := by
    intro h_eq
    let mid_val : ℝ := ((L.left : ℝ) + (L.right : ℝ)) / 2
    have hmid_val1 : (L.left : ℝ) < mid_val := by
      dsimp only [mid_val] <;> linarith [L.left_lt_right]
    have hmid_val2 : mid_val < (L.right : ℝ) := by
      dsimp only [mid_val] <;> linarith [L.left_lt_right]
    have hmid_in : mid_val ∈ Set.Icc (0 : ℝ) 1 := by
      have h1 : 0 ≤ (L.left : ℝ) := L.left.property.1
      have h2 : (L.right : ℝ) ≤ 1 := L.right.property.2
      exact ⟨by linarith, by linarith⟩
    let mid : UnitPoint := ⟨mid_val, hmid_in⟩
    have hmid1 : (L.left : ℝ) < (mid : ℝ) := by
      exact_mod_cast hmid_val1
    have hmid2 : (mid : ℝ) < (L.right : ℝ) := by
      exact_mod_cast hmid_val2
    have hmid_carrier : mid ∈ I.carrier := by
      exact ⟨by linarith [hleft.1], by linarith [hright.2]⟩
    let z := invPhiMap I hI mid hmid_carrier
    have hz1 : phiMap I z = mid := phiMap_invPhiMap I hI mid hmid_carrier
    have h_eq_at : (L.f.reparam I) z = (L.g.reparam I) z := by
      rw [h_eq]
    have h_contra : L.f mid = L.g mid := by
      have h := (reparam_intersection_iff L.f L.g I z).mp h_eq_at
      rw [hz1] at h
      exact h
    exact L.no_interior_intersection mid hmid1 hmid2 h_contra
  have h_left_lt_right : (left' : ℝ) < (right' : ℝ) :=
    invPhiMap_strictMono I hI L.left L.right hleft hright L.left_lt_right
  have h_eq_left : (L.f.reparam I) left' = (L.g.reparam I) left' := by
    have h_goal : L.f (phiMap I left') = L.g (phiMap I left') := by
      have h_eq_unit : phiMap I left' = L.left := phiMap_invPhiMap I hI L.left hleft
      exact h_eq_unit ▸ L.eq_left
    exact (reparam_intersection_iff L.f L.g I left').mpr h_goal
  have h_eq_right : (L.f.reparam I) right' = (L.g.reparam I) right' := by
    have h_goal : L.f (phiMap I right') = L.g (phiMap I right') := by
      have h_eq_unit : phiMap I right' = L.right := phiMap_invPhiMap I hI L.right hright
      exact h_eq_unit ▸ L.eq_right
    exact (reparam_intersection_iff L.f L.g I right').mpr h_goal
  have h_no_interior : ∀ (x : UnitPoint), (left' : ℝ) < (x : ℝ) → (x : ℝ) < (right' : ℝ) →
      (L.f.reparam I) x ≠ (L.g.reparam I) x := by
    intro x hx1 hx2
    let y := phiMap I x
    have hy1 : (L.left : ℝ) < (y : ℝ) := by
      have h : (phiMap I left' : ℝ) < (phiMap I x : ℝ) := phiMap_strictMono I hI hx1
      rw [h_phi_left] at h
      exact h
    have hy2 : (y : ℝ) < (L.right : ℝ) := by
      have h : (phiMap I x : ℝ) < (phiMap I right' : ℝ) := phiMap_strictMono I hI hx2
      rw [h_phi_right] at h
      exact h
    have h_contra : L.f y ≠ L.g y := L.no_interior_intersection y hy1 hy2
    exact (reparam_intersection_iff L.f L.g I x).not.mp h_contra
  { f := L.f.reparam I
    g := L.g.reparam I
    f_ne_g := h_f_ne_g
    left := left'
    right := right'
    left_lt_right := h_left_lt_right
    eq_left := h_eq_left
    eq_right := h_eq_right
    no_interior_intersection := h_no_interior }

end GraphLens

end Kakeya.Cinematic

end
