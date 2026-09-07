import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.GraphLensBridge.Crossing

/-!
# Fibers of graph lenses over their positive sides

Non-overlap and the two-intersection hypothesis make the negative side
injective inside every host fiber.  Consequently the moon-face sequence is
nodup, and summing its lengths over all curves counts every lens exactly once.
-/

noncomputable section

namespace Kakeya.Cinematic.GraphLensBridge

open Kakeya.Cinematic

theorem upper_lower_eq_at_left (lens : GraphLens) :
    upper lens lens.left = lower lens lens.left := by
  rcases upper_eq_f_or_g lens with hu | hu <;>
    rcases lower_eq_f_or_g lens with hl | hl
  · exact False.elim (upper_ne_lower lens (hu.trans hl.symm))
  · simpa [hu, hl] using lens.eq_left
  · simpa [hu, hl] using lens.eq_left.symm
  · exact False.elim (upper_ne_lower lens (hu.trans hl.symm))

theorem upper_lower_eq_at_right (lens : GraphLens) :
    upper lens lens.right = lower lens lens.right := by
  rcases upper_eq_f_or_g lens with hu | hu <;>
    rcases lower_eq_f_or_g lens with hl | hl
  · exact False.elim (upper_ne_lower lens (hu.trans hl.symm))
  · simpa [hu, hl] using lens.eq_right
  · simpa [hu, hl] using lens.eq_right.symm
  · exact False.elim (upper_ne_lower lens (hu.trans hl.symm))

theorem shares_upper (first second : GraphLens)
    (hupper : upper first = upper second) :
    first.f = second.f ∨ first.f = second.g ∨
      first.g = second.f ∨ first.g = second.g := by
  rcases upper_eq_f_or_g first with hfirst | hfirst <;>
    rcases upper_eq_f_or_g second with hsecond | hsecond
  · exact Or.inl (hfirst.symm.trans (hupper.trans hsecond))
  · exact Or.inr (Or.inl (hfirst.symm.trans (hupper.trans hsecond)))
  · exact Or.inr (Or.inr (Or.inl (hfirst.symm.trans (hupper.trans hsecond))))
  · exact Or.inr (Or.inr (Or.inr (hfirst.symm.trans (hupper.trans hsecond))))

theorem disjoint_intervals_of_nonoverlap_of_upper_eq
    {first second : GraphLens} (hupper : upper first = upper second)
    (hnonoverlap : first.Nonoverlap second) :
    (first.right : ℝ) ≤ second.left ∨ (second.right : ℝ) ≤ first.left := by
  have hnot :
      ¬max (first.left : ℝ) second.left <
        min (first.right : ℝ) second.right := by
    intro hinterior
    exact hnonoverlap ⟨shares_upper first second hupper, hinterior⟩
  by_contra h
  push Not at h
  apply hnot
  simp only [max_lt_iff, lt_min_iff]
  exact ⟨⟨first.left_lt_right, h.1⟩,
    ⟨h.2, second.left_lt_right⟩⟩

theorem shares_lower (first second : GraphLens)
    (hlower : lower first = lower second) :
    first.f = second.f ∨ first.f = second.g ∨
      first.g = second.f ∨ first.g = second.g := by
  rcases lower_eq_f_or_g first with hfirst | hfirst <;>
    rcases lower_eq_f_or_g second with hsecond | hsecond
  · exact Or.inl (hfirst.symm.trans (hlower.trans hsecond))
  · exact Or.inr (Or.inl (hfirst.symm.trans (hlower.trans hsecond)))
  · exact Or.inr (Or.inr (Or.inl (hfirst.symm.trans (hlower.trans hsecond))))
  · exact Or.inr (Or.inr (Or.inr (hfirst.symm.trans (hlower.trans hsecond))))

theorem disjoint_intervals_of_nonoverlap_of_lower_eq
    {first second : GraphLens} (hlower : lower first = lower second)
    (hnonoverlap : first.Nonoverlap second) :
    (first.right : ℝ) ≤ second.left ∨ (second.right : ℝ) ≤ first.left := by
  have hnot :
      ¬max (first.left : ℝ) second.left <
        min (first.right : ℝ) second.right := by
    intro hinterior
    exact hnonoverlap ⟨shares_lower first second hlower, hinterior⟩
  by_contra h
  push Not at h
  apply hnot
  simp only [max_lt_iff, lt_min_iff]
  exact ⟨⟨first.left_lt_right, h.1⟩,
    ⟨h.2, second.left_lt_right⟩⟩

private theorem distinct_intersections_contradiction
    {curves : Finset C2Function}
    (hfamily : IsGraphPseudoCircleFamily curves)
    {first second : GraphLens}
    (hfirstSides : first.f ∈ curves ∧ first.g ∈ curves)
    (hupper : upper first = upper second)
    (hlower : lower first = lower second)
    (hordered : (first.right : ℝ) ≤ second.left) : False := by
  have huMem : upper first ∈ curves := upper_mem_curves hfirstSides
  have hlMem : lower first ∈ curves := lower_mem_curves hfirstSides
  have hthree := hfamily.1 (upper first) huMem (lower first) hlMem
    (upper_ne_lower first)
  by_cases heq : (first.right : ℝ) = second.left
  · have h12 : (first.left : ℝ) < second.left := by
      linarith [first.left_lt_right]
    have h23 : (second.left : ℝ) < second.right :=
      second.left_lt_right
    have hpoint : first.right = second.left := Subtype.ext heq
    exact hthree first.left second.left second.right h12 h23
      (upper_lower_eq_at_left first)
      (by
        rw [← hpoint]
        exact upper_lower_eq_at_right first)
      (by simpa [hupper, hlower] using upper_lower_eq_at_right second)
  · have h12 : (first.left : ℝ) < first.right :=
      first.left_lt_right
    have h23 : (first.right : ℝ) < second.left :=
      lt_of_le_of_ne hordered heq
    exact hthree first.left first.right second.left h12 h23
      (upper_lower_eq_at_left first)
      (upper_lower_eq_at_right first)
      (by simpa [hupper, hlower] using upper_lower_eq_at_left second)

theorem lower_injective_on_hosted
    {curves : Finset C2Function} {lenses : Finset GraphLens}
    (hfamily : IsGraphPseudoCircleFamily curves)
    (hsides : ∀ lens ∈ lenses, lens.f ∈ curves ∧ lens.g ∈ curves)
    (hnonoverlap : ∀ first ∈ lenses, ∀ second ∈ lenses,
      first ≠ second → first.Nonoverlap second)
    (host : C2Function) :
    Set.InjOn lower (hostedLenses lenses host) := by
  intro first hfirst second hsecond hlower
  classical
  have hfirstMem : first ∈ lenses := (Finset.mem_filter.mp hfirst).1
  have hsecondMem : second ∈ lenses := (Finset.mem_filter.mp hsecond).1
  have hfirstUpper : upper first = host :=
    (Finset.mem_filter.mp hfirst).2
  have hsecondUpper : upper second = host :=
    (Finset.mem_filter.mp hsecond).2
  by_contra hne
  have hnon := hnonoverlap first hfirstMem second hsecondMem hne
  have hupper : upper first = upper second :=
    hfirstUpper.trans hsecondUpper.symm
  rcases disjoint_intervals_of_nonoverlap_of_upper_eq hupper hnon with horder | horder
  · exact distinct_intersections_contradiction hfamily
      (hsides first hfirstMem) hupper hlower horder
  · exact distinct_intersections_contradiction hfamily
      (hsides second hsecondMem) hupper.symm hlower.symm horder

theorem moonSequence_nodup
    {curves : Finset C2Function} {lenses : Finset GraphLens}
    (hfamily : IsGraphPseudoCircleFamily curves)
    (hsides : ∀ lens ∈ lenses, lens.f ∈ curves ∧ lens.g ∈ curves)
    (hnonoverlap : ∀ first ∈ lenses, ∀ second ∈ lenses,
      first ≠ second → first.Nonoverlap second)
    (host : C2Function) :
    (moonSequence lenses host).Nodup := by
  letI := graphLensOrder
  exact (Finset.sort_nodup (hostedLenses lenses host) (· ≤ ·)).map_on
    (fun first hfirst second hsecond =>
      lower_injective_on_hosted hfamily hsides hnonoverlap host
        ((Finset.mem_sort (· ≤ ·)).mp hfirst)
        ((Finset.mem_sort (· ≤ ·)).mp hsecond))

theorem moonSequence_length (lenses : Finset GraphLens)
    (host : C2Function) :
    (moonSequence lenses host).length = (hostedLenses lenses host).card := by
  letI := graphLensOrder
  simp [moonSequence, hostedList]

theorem sum_moonSequence_length
    {curves : Finset C2Function} {lenses : Finset GraphLens}
    (hsides : ∀ lens ∈ lenses, lens.f ∈ curves ∧ lens.g ∈ curves) :
    ∑ host ∈ curves, (moonSequence lenses host).length = lenses.card := by
  classical
  simp_rw [moonSequence_length]
  change ∑ host ∈ curves,
      (lenses.filter fun lens => upper lens = host).card = lenses.card
  rw [Finset.sum_card_fiberwise_eq_card_filter lenses curves upper]
  apply congrArg Finset.card
  ext lens
  simp only [Finset.mem_filter]
  constructor
  · exact fun h => h.1
  · intro hlens
    exact ⟨hlens, upper_mem_curves (hsides lens hlens)⟩

end Kakeya.Cinematic.GraphLensBridge
