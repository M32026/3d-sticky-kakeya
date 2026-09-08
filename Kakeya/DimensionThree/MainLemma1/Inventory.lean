/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

/-!
# Supporting constructions for Main Lemma 1

`exists_relativePlankSelection` regularizes the common refinement of the plank
partition and all grid levels. It retains two-sided shading uniformity,
cardinality and aggregate shade mass while factoring the active blocks.
`ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset` transfers
the multiplicity estimate to the original family.

The parent-family constructions in `Rescaling/CoarseDensity.lean` distinguish
essential distinctness from separation of the families contained in parent
dilates. In particular, the latter does not follow merely by choosing
essentially distinct parents. The relevant statements are
`exists_plankTube_parentFamily_essDistinct`, `exists_merged_parentFamily`,
`dilate_le_dilate_of_not_essDistinct` and
`disjoint_familyIn_of_familyIn_subset_fibre`.
-/
