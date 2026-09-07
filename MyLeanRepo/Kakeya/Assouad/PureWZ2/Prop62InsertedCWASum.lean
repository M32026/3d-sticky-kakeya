import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentGeometry

/-!
# Proposition 6.2 inserted level: finite packet CWA sum

This is the finite summation in equation `prop62-inserted-cwa`.  No geometric
inheritance is assumed: a normalized estimate is supplied separately on
every complete packet, and the packets are then summed exactly.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem pureWZ2_prop62_sum_packet_cwa
    {Leaf Packet : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Packet] [DecidableEq Packet]
    (parent : Leaf → Packet)
    (active : Finset Packet)
    (predicate : Leaf → Prop)
    (C volumeFactor : ENNReal)
    (localBound :
      ∀ packet ∈ active,
        (((Finset.univ.filter fun leaf =>
            parent leaf = packet ∧ predicate leaf).card :
          ENNReal)) ≤
          C * volumeFactor *
            (((Finset.univ.filter fun leaf =>
              parent leaf = packet).card : ENNReal))) :
    (((Finset.univ.filter fun leaf =>
        parent leaf ∈ active ∧ predicate leaf).card : ENNReal)) ≤
      C * volumeFactor *
        (((Finset.univ.filter fun leaf =>
          parent leaf ∈ active).card : ENNReal)) := by
  let contained : Finset Leaf :=
    Finset.univ.filter predicate
  have containedFiber :
      ∀ packet,
        Finset.univ.filter (fun leaf =>
            parent leaf = packet ∧ predicate leaf) =
          contained.filter fun leaf =>
            parent leaf = packet := by
    intro packet
    ext leaf
    simp [contained, and_left_comm, and_comm]
  have totalContained :
      (∑ packet ∈ active,
          ((Finset.univ.filter fun leaf =>
            parent leaf = packet ∧ predicate leaf).card :
            ENNReal)) =
        ((Finset.univ.filter fun leaf =>
          parent leaf ∈ active ∧ predicate leaf).card :
          ENNReal) := by
    have hnatural :=
      Finset.sum_card_fiberwise_eq_card_filter
        contained active parent
    have hnatural' :
        (∑ packet ∈ active,
            (Finset.univ.filter fun leaf =>
              parent leaf = packet ∧ predicate leaf).card) =
          (Finset.univ.filter fun leaf =>
            parent leaf ∈ active ∧ predicate leaf).card := by
      calc
        ∑ packet ∈ active,
            (Finset.univ.filter fun leaf =>
              parent leaf = packet ∧ predicate leaf).card =
          ∑ packet ∈ active,
            (contained.filter fun leaf =>
              parent leaf = packet).card := by
            apply Finset.sum_congr rfl
            intro packet _
            rw [containedFiber packet]
        _ = (contained.filter fun leaf =>
              parent leaf ∈ active).card := hnatural
        _ = (Finset.univ.filter fun leaf =>
              parent leaf ∈ active ∧ predicate leaf).card := by
            congr 1
            ext leaf
            simp [contained, and_comm]
    exact_mod_cast hnatural'
  have totalFiber :
      (∑ packet ∈ active,
          ((Finset.univ.filter fun leaf =>
            parent leaf = packet).card : ENNReal)) =
        ((Finset.univ.filter fun leaf =>
          parent leaf ∈ active).card : ENNReal) := by
    have hnatural :=
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset Leaf) active parent
    exact_mod_cast (by simpa using hnatural)
  rw [← totalContained, ← totalFiber]
  calc
    ∑ packet ∈ active,
        ((Finset.univ.filter fun leaf =>
          parent leaf = packet ∧ predicate leaf).card : ENNReal) ≤
      ∑ packet ∈ active,
        C * volumeFactor *
          ((Finset.univ.filter fun leaf =>
            parent leaf = packet).card : ENNReal) := by
      exact Finset.sum_le_sum fun packet hpacket =>
        localBound packet hpacket
    _ =
      C * volumeFactor *
        ∑ packet ∈ active,
          ((Finset.univ.filter fun leaf =>
            parent leaf = packet).card : ENNReal) := by
      rw [Finset.mul_sum]

end Kakeya.Assouad

end
