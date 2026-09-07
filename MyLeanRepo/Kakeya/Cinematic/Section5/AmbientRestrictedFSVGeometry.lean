import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedFSVGeometryInputs

/-!
# Fixed ambient geometry after fine-shading transport
-/

namespace Kakeya.Cinematic

theorem ambient_restricted_fsv_geometry :
    AmbientRestrictedFSVGeometryStatement := by
  intro family E K delta diameter epsilon eta tRep DeltaRep C_R₀ C_R
    data hdelta center hE pointData hfib hCR
  have h1 : ∀ (p : ambientRestrictedSet data center),
      (pointData.fiber p).carrier ⊆
        (data.ambientSource.cluster center (3 * tRep)).carrier := by
    intro p
    rw [hfib p]
    exact ambientRestrictedData_fiber_subset_cluster
      data hdelta center hE p
  have h2 : ∀ f ∈ (data.ambientSource.cluster center (3 * tRep)).carrier,
      ∀ g ∈ (data.ambientSource.cluster center (3 * tRep)).carrier,
        dist f g ≤ 6 * (C_R * tRep) := by
    intro f hf g hg
    have hdiam : c2Distance f g ≤ 6 * tRep :=
      ambientRestrictedData_cluster_diameter data center f hf g hg
    rw [c2Distance_eq_dist f g] at hdiam
    have hpos : 0 < tRep := data.tRep_pos
    have hle : 6 * tRep ≤ 6 * (C_R * tRep) := by
      have h : tRep ≤ C_R * tRep := by
        nlinarith
      nlinarith
    linarith
  exact ⟨h1, h2⟩

end Kakeya.Cinematic
