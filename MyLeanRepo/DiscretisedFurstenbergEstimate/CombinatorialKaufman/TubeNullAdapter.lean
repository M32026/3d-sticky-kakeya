module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.IntervalUtils
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Adapter: Finset to List for TubeNullResult

Converts the Finset output of the non-uniform tube-null lemma to the List
format required by `TubeNullResult`, including sorting by left endpoint and
proving pairwise interior disjointness.
-/

noncomputable section

open MeasureTheory Set Metric Finset List

namespace CombinatorialKaufman.TubeNull

/-- Convert a Finset of intervals satisfying the non-uniform tube-null properties
    to a sorted List satisfying the TubeNullResult properties. -/
lemma adapt_finset_to_list
    {f : ℝ → ℝ} {ε τ m : ℝ} (hτ_pos : 0 < τ) (hm_pos : 0 < m)
    {I : Finset (ℝ × ℝ)}
    (hI_eps : ∀ p ∈ I, EpsilonLinear f ε p.1 p.2)
    (hI_len : ∀ p ∈ I, p.2 - p.1 ≥ τ * m)
    (hI_cont : ∀ p ∈ I, 0 ≤ p.1 ∧ p.2 ≤ m)
    (hI_nonover : ∀ p ∈ I, ∀ q ∈ I, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1)
    (hI_cover : m - ∑ p ∈ I, (p.2 - p.1) ≤ ε * m) :
    ∃ (L : List (ℝ × ℝ)),
      (∀ p ∈ L, EpsilonLinear f ε p.1 p.2) ∧
      (∀ p ∈ L, p.2 - p.1 ≥ τ * m) ∧
      (∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ≤ m ∧ p.1 < p.2) ∧
      SortedByLeft L ∧
      PairwiseInteriorDisjointList L ∧
      m - (L.map (fun p => p.2 - p.1)).sum ≤ ε * m := by
  -- All intervals have positive length
  have h_pos_len : ∀ p ∈ I, p.1 < p.2 := by
    intro p hp
    have h : p.2 - p.1 ≥ τ * m := hI_len p hp
    have h' : 0 < τ * m := mul_pos hτ_pos hm_pos
    linarith
  -- All left endpoints are distinct
  have h_distinct_left : ∀ p ∈ I, ∀ q ∈ I, p ≠ q → p.1 ≠ q.1 := by
    intro p hp q hq hne
    intro h_eq
    have h : p.2 ≤ q.1 ∨ q.2 ≤ p.1 := hI_nonover p hp q hq hne
    rcases h with (h | h)
    · have h' : p.2 ≤ p.1 := by simpa [h_eq] using h
      have h'' : p.1 < p.2 := h_pos_len p hp
      linarith
    · have h' : q.2 ≤ q.1 := by simpa [h_eq] using h
      have h'' : q.1 < q.2 := h_pos_len q hq
      linarith
  -- Non-overlap implies disjoint interiors
  have h_disj_interiors : ∀ p ∈ I, ∀ q ∈ I, p ≠ q →
      Disjoint (Set.Ioo p.1 p.2) (Set.Ioo q.1 q.2) := by
    intro p hp q hq hne
    have h : p.2 ≤ q.1 ∨ q.2 ≤ p.1 := hI_nonover p hp q hq hne
    rcases h with (h | h)
    · apply Set.disjoint_left.mpr
      intro x hx1 hx2
      have h1 : x < p.2 := hx1.2
      have h2 : q.1 < x := hx2.1
      linarith
    · apply Set.disjoint_left.mpr
      intro x hx1 hx2
      have h1 : x < q.2 := hx2.2
      have h2 : p.1 < x := hx1.1
      linarith
  -- Set of left endpoints
  let lefts : Finset ℝ := Finset.image Prod.fst I
  have h_exists : ∀ (x : ℝ), x ∈ lefts → ∃ (p : ℝ × ℝ), p ∈ I ∧ p.1 = x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩
  -- get_interval x returns the unique interval in I with left endpoint x.
  -- For x ∉ lefts, return (x, x+1) so that .1 = x always holds.
  let get_interval (x : ℝ) : ℝ × ℝ :=
    if h : x ∈ lefts then Classical.choose (h_exists x h) else (x, x + 1)
  have h_get_interval_spec : ∀ (x : ℝ), x ∈ lefts →
      (get_interval x ∈ I ∧ (get_interval x).1 = x) := by
    intro x hx
    have h_def : get_interval x = Classical.choose (h_exists x hx) := by
      simp [get_interval, hx]
    rw [h_def]
    exact Classical.choose_spec (h_exists x hx)
  have h_get_interval_fst : ∀ (x : ℝ), (get_interval x).1 = x := by
    intro x
    by_cases h : x ∈ lefts
    · exact (h_get_interval_spec x h).2
    · simp [get_interval, h]
  -- get_interval(p.1) = p for p ∈ I
  have h_get_interval_eq : ∀ (p : ℝ × ℝ), p ∈ I → get_interval (p.1) = p := by
    intro p hp
    have hx : p.1 ∈ lefts := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have h4 : get_interval (p.1) ∈ I := (h_get_interval_spec p.1 hx).1
    have h5 : (get_interval (p.1)).1 = p.1 := (h_get_interval_spec p.1 hx).2
    by_contra hne
    have h6 : (get_interval (p.1)).1 ≠ p.1 := h_distinct_left (get_interval (p.1)) h4 p hp hne
    exact h6 h5
  -- Sorted list of left endpoints
  let sorted_lefts : List ℝ := Finset.sort lefts
  have h_sorted_lefts : sorted_lefts.SortedLT := Finset.sortedLT_sort lefts
  have h_mem_lefts : ∀ x ∈ sorted_lefts, x ∈ lefts := by
    intro x hx
    rw [Finset.mem_sort] at hx
    exact hx
  -- Map to intervals
  let L : List (ℝ × ℝ) := sorted_lefts.map get_interval
  -- Basic properties
  have hL_mem : ∀ p ∈ L, p ∈ I := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨x, hx, rfl⟩
    exact (h_get_interval_spec x (h_mem_lefts x hx)).1
  have hL_eps : ∀ p ∈ L, EpsilonLinear f ε p.1 p.2 := by
    intro p hp; exact hI_eps p (hL_mem p hp)
  have hL_len : ∀ p ∈ L, p.2 - p.1 ≥ τ * m := by
    intro p hp; exact hI_len p (hL_mem p hp)
  have hL_cont : ∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ≤ m := by
    intro p hp; exact hI_cont p (hL_mem p hp)
  have hL_valid : ∀ p ∈ L, p.1 < p.2 := by
    intro p hp; exact h_pos_len p (hL_mem p hp)
  have hL_cont' : ∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ≤ m ∧ p.1 < p.2 := by
    intro p hp
    have h1 := hL_cont p hp
    have h2 := hL_valid p hp
    exact ⟨h1.1, h1.2, h2⟩
  -- L contains exactly the elements of I
  have hL_surj : ∀ p ∈ I, p ∈ L := by
    intro p hp
    have hx : p.1 ∈ lefts := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have h_in_sorted : p.1 ∈ sorted_lefts := by
      rw [Finset.mem_sort] <;> exact hx
    have h3 : get_interval (p.1) = p := h_get_interval_eq p hp
    exact List.mem_map.mpr ⟨p.1, h_in_sorted, h3⟩
  -- Sorted by left endpoint: use Pairwise.map with h_get_interval_fst
  have h_sorted : SortedByLeft L := by
    dsimp only [SortedByLeft, L]
    have h : List.Pairwise (fun (x y : ℝ) => x < y) sorted_lefts :=
      (List.sortedLT_iff_pairwise).mp h_sorted_lefts
    exact h.map get_interval (fun {x y} hxy => by
      rw [h_get_interval_fst x, h_get_interval_fst y]
      exact hxy)
  -- L.Nodup follows from SortedByLeft (< is Irrefl)
  have hL_nodup : L.Nodup := h_sorted.nodup
  -- Pairwise interior disjointness
  have h_disj_list : PairwiseInteriorDisjointList L := by
    dsimp only [PairwiseInteriorDisjointList]
    have h_forall : ∀ (p : ℝ × ℝ), p ∈ L → ∀ (q : ℝ × ℝ), q ∈ L → p ≠ q →
        Disjoint (Set.Ioo p.1 p.2) (Set.Ioo q.1 q.2) := by
      intro p hp q hq hne
      have hpI : p ∈ I := hL_mem p hp
      have hqI : q ∈ I := hL_mem q hq
      exact h_disj_interiors p hpI q hqI hne
    exact hL_nodup.pairwise_of_forall_ne h_forall
  -- Sum conversion via List.sum_toFinset
  have h_get_interval_inj : Set.InjOn get_interval lefts := by
    intro x hx y hy h
    have h1 : (get_interval x).1 = x := (h_get_interval_spec x hx).2
    have h2 : (get_interval y).1 = y := (h_get_interval_spec y hy).2
    have h_eq : (get_interval x).1 = (get_interval y).1 := by rw [h]
    rw [h1, h2] at h_eq
    exact h_eq
  have h_image_eq : Finset.image get_interval lefts = I := by
    ext p
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h_get_interval_spec x hx).1
    · intro hp
      refine ⟨p.1, Finset.mem_image.mpr ⟨p, hp, rfl⟩, h_get_interval_eq p hp⟩
  have h_sum : (L.map (fun p : ℝ × ℝ => p.2 - p.1)).sum = ∑ p ∈ I, (p.2 - p.1) := by
    have h_nodup : sorted_lefts.Nodup := sort_nodup lefts fun a b => a ≤ b
    let g : ℝ → ℝ := fun x => (get_interval x).2 - (get_interval x).1
    have h_map_eq : (L.map (fun p : ℝ × ℝ => p.2 - p.1)) = sorted_lefts.map g := by
      dsimp only [L]
      rw [List.map_map]
      <;> rfl
    have h3 : sorted_lefts.toFinset = lefts := by
      ext x
      simp only [List.mem_toFinset]
      exact mem_sort fun a b => a ≤ b
    calc
      (L.map (fun p : ℝ × ℝ => p.2 - p.1)).sum
        = (sorted_lefts.map g).sum := by rw [h_map_eq]
      _ = ∑ x ∈ sorted_lefts.toFinset, g x := (List.sum_toFinset g h_nodup).symm
      _ = ∑ x ∈ lefts, g x := by rw [h3]
      _ = ∑ p ∈ Finset.image get_interval lefts, (p.2 - p.1) := by
        rw [Finset.sum_image h_get_interval_inj] <;> rfl
      _ = ∑ p ∈ I, (p.2 - p.1) := by rw [h_image_eq]
  have hL_cover : m - (L.map (fun p => p.2 - p.1)).sum ≤ ε * m := by
    rw [h_sum]
    exact hI_cover
  exact ⟨L, hL_eps, hL_len, hL_cont', h_sorted, h_disj_list, hL_cover⟩

end CombinatorialKaufman.TubeNull

end
