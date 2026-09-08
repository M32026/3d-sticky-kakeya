import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.HierarchicalPrefixGrouping

/-!
# Proof of hierarchical prefix grouping

Constructs balanced prefix groups and prefix/suffix shift decomposition
for an arbitrary finite product of positive copy counts.
-/

open BigOperators

namespace Kakeya.Streamlined.RandomTranslation

theorem hierarchical_prefix_grouping :
    HierarchicalPrefixGroupingStatement := by
  intro M J hJ radius hr shiftAt hshift cut

  let prefixSet : Finset (Fin M) :=
    Finset.univ.filter (fun k => k.val < cut.val)
  let suffixSet : Finset (Fin M) :=
    Finset.univ.filter (fun k => cut.val ≤ k.val)

  let prefixType : Type _ := {k : Fin M // k.val < cut.val}
  let suffixType : Type _ := {k : Fin M // cut.val ≤ k.val}
  let prefixChoicesType : Type _ := (k : prefixType) → Fin (J k)
  let suffixChoicesType : Type _ := (k : suffixType) → Fin (J k)

  let groupCount : ℕ := Fintype.card prefixChoicesType
  let e_prefix : prefixChoicesType ≃ Fin groupCount :=
    Fintype.equivFin prefixChoicesType

  let group : Fin (multiscaleTotalJ J) → Fin groupCount :=
    fun i => e_prefix (fun k : prefixType => (finPiFinEquiv.symm i) k)

  let prefixShift (p : prefixChoicesType) (k : Fin M) : Point3 :=
    if h : k.val < cut.val then shiftAt k (p ⟨k, h⟩) else 0

  let cumulative (g : Fin groupCount) : Point3 :=
    ∑ k ∈ prefixSet, prefixShift (e_prefix.symm g) k

  let residual (i : Fin (multiscaleTotalJ J)) : Point3 :=
    ∑ k ∈ suffixSet, shiftAt k ((finPiFinEquiv.symm i) k)

  let combine (p : prefixChoicesType) (s : suffixChoicesType)
      (k : Fin M) : Fin (J k) :=
    if h : k.val < cut.val then p ⟨k, h⟩ else s ⟨k, by omega⟩

  have h_disj : Disjoint prefixSet suffixSet := by
    simp [prefixSet, suffixSet, Finset.disjoint_left]
    <;> omega

  have h_union : prefixSet ∪ suffixSet = (Finset.univ : Finset (Fin M)) := by
    ext k
    simp [prefixSet, suffixSet]
    <;> omega

  have h_prefix_nonempty : Nonempty prefixChoicesType := by
    refine' ⟨fun k => ⟨0, hJ k⟩⟩

  have h_suffix_nonempty : Nonempty suffixChoicesType := by
    refine' ⟨fun k => ⟨0, hJ k⟩⟩

  have h1 : 0 < groupCount := by
    exact Fintype.card_pos

  have h2 : Function.Surjective group := by
    intro g
    let p : prefixChoicesType := e_prefix.symm g
    let s : suffixChoicesType := fun k => ⟨0, hJ k⟩
    let i : Fin (multiscaleTotalJ J) :=
      finPiFinEquiv (combine p s)
    use i
    have h_eq : (finPiFinEquiv.symm i) = combine p s := by
      simp [i] <;> rfl
    have h_prefix_combine : (fun k : prefixType => (combine p s) k) = p := by
      funext k
      simp [combine, k.property]
      <;> congr
      <;> apply Subtype.ext
      <;> rfl
    have h_goal : group i = g := by
      simp [group, h_eq, h_prefix_combine]
      <;> exact e_prefix.apply_symm_apply g
    exact h_goal

  have h_fiber_card : ∀ (g : Fin groupCount),
      (Finset.univ.filter fun i : Fin (multiscaleTotalJ J) => group i = g).card =
        Fintype.card suffixChoicesType := by
    intro g
    let p_g : prefixChoicesType := e_prefix.symm g

    let toSuffix (i : Fin (multiscaleTotalJ J)) : suffixChoicesType :=
      fun k : suffixType => (finPiFinEquiv.symm i) k

    let fromSuffix (s : suffixChoicesType) : Fin (multiscaleTotalJ J) :=
      finPiFinEquiv (combine p_g s)

    have h_from_mem : ∀ (s : suffixChoicesType),
        group (fromSuffix s) = g := by
      intro s
      have h_eq : (finPiFinEquiv.symm (fromSuffix s)) = combine p_g s := by
        simp [fromSuffix] <;> rfl
      have h_prefix_combine : (fun k : prefixType => (combine p_g s) k) = p_g := by
        funext k
        simp [combine, k.property]
        <;> congr
        <;> apply Subtype.ext
        <;> rfl
      have h : group (fromSuffix s) = e_prefix p_g := by
        simp [group, h_eq, h_prefix_combine]
      rw [h]
      exact e_prefix.apply_symm_apply g

    have h_right_inv : ∀ (s : suffixChoicesType),
        toSuffix (fromSuffix s) = s := by
      intro s
      have h_eq : (finPiFinEquiv.symm (fromSuffix s)) = combine p_g s := by
        simp [fromSuffix] <;> rfl
      funext k
      have h_ge : cut.val ≤ (k : Fin M).val := k.property
      have hnlt : ¬(k : Fin M).val < cut.val := by omega
      have h_sub : (⟨(k : Fin M), h_ge⟩ : suffixType) = k := by
        apply Subtype.ext; rfl
      have h_goal : (combine p_g s) (k : Fin M) = s k := by
        dsimp only [combine]
        rw [dif_neg hnlt]
      simpa [toSuffix, h_eq] using h_goal

    have h_left_inv : ∀ (i : Fin (multiscaleTotalJ J)) (hi : group i = g),
        fromSuffix (toSuffix i) = i := by
      intro i hi
      have h_prefix_eq : (fun k : prefixType => (finPiFinEquiv.symm i) k) = p_g := by
        have h_grp : e_prefix (fun k : prefixType => (finPiFinEquiv.symm i) k) = g := by
          simpa [group] using hi
        have h_eq : e_prefix (fun k : prefixType => (finPiFinEquiv.symm i) k) = e_prefix p_g := by
          rw [h_grp, e_prefix.apply_symm_apply g]
        exact e_prefix.injective h_eq
      have h_combine_eq : combine p_g (toSuffix i) = finPiFinEquiv.symm i := by
        funext k
        by_cases h : k.val < cut.val
        · have h' : (p_g ⟨k, h⟩) = (finPiFinEquiv.symm i) k := by
            have h'' := congr_fun h_prefix_eq ⟨k, h⟩
            exact h''.symm
          simp [combine, h, h']
        · have h' : cut.val ≤ k.val := by omega
          simp [combine, h, h', toSuffix]
          <;> rfl
      have h : fromSuffix (toSuffix i) =
          finPiFinEquiv (finPiFinEquiv.symm i) := by
        simp [fromSuffix, h_combine_eq]
      rw [h]
      <;> simp

    let e_fiber : {i : Fin (multiscaleTotalJ J) // group i = g} ≃ suffixChoicesType :=
      { toFun := fun x => toSuffix x.val
        invFun := fun s => ⟨fromSuffix s, h_from_mem s⟩
        left_inv := fun x => Subtype.ext (h_left_inv x.val x.property)
        right_inv := fun s => h_right_inv s }

    have h_card1 : Fintype.card {i : Fin (multiscaleTotalJ J) // group i = g} =
        Fintype.card suffixChoicesType :=
      Fintype.card_congr e_fiber

    have h_card2 : (Finset.univ.filter fun i : Fin (multiscaleTotalJ J) => group i = g).card =
        Fintype.card {i : Fin (multiscaleTotalJ J) // group i = g} := by
      have h_map : Finset.map (Function.Embedding.subtype (fun i : Fin (multiscaleTotalJ J) => group i = g))
          (Finset.univ : Finset {i : Fin (multiscaleTotalJ J) // group i = g}) =
          (Finset.univ.filter fun i : Fin (multiscaleTotalJ J) => group i = g) := by
        rw [Finset.univ_map_subtype]
        <;> rfl
      rw [← h_map]
      rw [Finset.card_map]
      <;> rfl

    rw [h_card2, h_card1]

  have h3 : ∀ (g h : Fin groupCount),
      (Finset.univ.filter fun i => group i = g).card =
      (Finset.univ.filter fun i => group i = h).card := by
    intro g h
    rw [h_fiber_card g, h_fiber_card h]

  have h4 : ∀ (g : Fin groupCount),
      0 < (Finset.univ.filter fun i => group i = g).card := by
    intro g
    rw [h_fiber_card g]
    exact Fintype.card_pos

  have h5 : ∀ (i j : Fin (multiscaleTotalJ J)),
      group i = group j ↔
        ∀ (k : Fin M), k.val < cut.val →
          (finPiFinEquiv.symm i) k = (finPiFinEquiv.symm j) k := by
    intro i j
    have h_iff : group i = group j ↔
        (fun k : prefixType => (finPiFinEquiv.symm i) k) =
        (fun k : prefixType => (finPiFinEquiv.symm j) k) := by
      simp [group]
      <;> constructor <;> intro h <;> exact e_prefix.injective h
    rw [h_iff]
    constructor
    · intro h k hk
      have h' := congr_fun h ⟨k, hk⟩
      exact h'
    · intro h
      funext k
      exact h k.val k.property

  have h6 : ∀ (i : Fin (multiscaleTotalJ J)),
      multiscaleShiftFun shiftAt i = cumulative (group i) + residual i := by
    intro i
    let choices : (k : Fin M) → Fin (J k) := finPiFinEquiv.symm i
    have h_sum_split : (∑ k : Fin M, shiftAt k (choices k)) =
        (∑ k ∈ prefixSet, shiftAt k (choices k)) +
        (∑ k ∈ suffixSet, shiftAt k (choices k)) := by
      rw [← Finset.sum_union h_disj, h_union]
      <;> rfl
    have h_prefix_eq : ∑ k ∈ prefixSet, shiftAt k (choices k) =
        ∑ k ∈ prefixSet, prefixShift (e_prefix.symm (group i)) k := by
      apply Finset.sum_congr rfl
      intro k hk
      have h_k_lt : k.val < cut.val := by
        simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact hk
      have h_e_prefix : e_prefix.symm (group i) =
          (fun k : prefixType => choices k) := by
        simp [group]
        <;> rfl
      rw [h_e_prefix]
      simp [prefixShift, h_k_lt]
      <;> rfl
    have h_residual_eq : ∑ k ∈ suffixSet, shiftAt k (choices k) = residual i := by
      rfl
    have h_final : (∑ k : Fin M, shiftAt k (choices k)) =
        cumulative (group i) + residual i := by
      rw [h_sum_split, h_prefix_eq, h_residual_eq]
      <;> rfl
    simpa [multiscaleShiftFun] using h_final

  have h7 : ∀ (i : Fin (multiscaleTotalJ J)),
      ‖residual i‖ ≤ ∑ k ∈ suffixSet, radius k := by
    intro i
    let choices : (k : Fin M) → Fin (J k) := finPiFinEquiv.symm i
    have h_norm1 : ‖residual i‖ ≤ ∑ k ∈ suffixSet, ‖shiftAt k (choices k)‖ := by
      exact norm_sum_le suffixSet (fun k => shiftAt k (choices k))
    have h_norm2 : ∑ k ∈ suffixSet, ‖shiftAt k (choices k)‖ ≤ ∑ k ∈ suffixSet, radius k := by
      apply Finset.sum_le_sum
      intro k _
      exact hshift k (choices k)
    exact le_trans h_norm1 h_norm2

  exact ⟨groupCount, group, cumulative, residual, h1, h2, h3, h4, h5, h6, h7⟩

end Kakeya.Streamlined.RandomTranslation
