/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberNodeMaps

/-!
# The actual local node comparison at t=v=0

The principal open of the full three-line fiber is isomorphic to the matching
principal open of the existing product-zero node. This keeps both coordinates;
it does not identify the whole three-line fiber with a single node.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (a : R)

/-- The first actual fiber neighborhood is the corresponding open in the split node. -/
def firstNodeEquiv : FirstFiberOpen a ≃ₐ[R] FirstNodeOpen a := by
  apply AlgEquiv.ofAlgHom (firstNodeForward a) (firstNodeBackward a)
  · apply IsLocalization.algHom_ext
      (Submonoid.powers (NodalFiber.q (0 : R) + algebraMap R _ a))
    apply NodalFiber.hom_ext
    · change firstNodeForward a (firstNodeBackward a
        (algebraMap _ _ (NodalFiber.p (0 : R)))) = _
      rw [firstNodeBackward_base, nodeToFirstFiber_p, firstNodeForward_base,
        fiberToFirstNode_t]
      rfl
    · change firstNodeForward a (firstNodeBackward a
        (algebraMap _ _ (NodalFiber.q (0 : R)))) = _
      rw [firstNodeBackward_base, nodeToFirstFiber_q, firstNodeForward_base,
        fiberToFirstNode_v]
      rfl
  · apply IsLocalization.algHom_ext
      (Submonoid.powers (fiberV a 0 + algebraMap R _ a))
    apply fiber_hom_ext
    · change firstNodeBackward a (firstNodeForward a
        (algebraMap _ _ (fiberT a 0))) = _
      rw [firstNodeForward_base, fiberToFirstNode_t, firstNodeBackward_base,
        nodeToFirstFiber_p]
      rfl
    · change firstNodeBackward a (firstNodeForward a
        (algebraMap _ _ (fiberV a 0))) = _
      rw [firstNodeForward_base, fiberToFirstNode_v, firstNodeBackward_base,
        nodeToFirstFiber_q]
      rfl

/-- The node equivalence retains the original incidence function. -/
@[simp] theorem firstNodeEquiv_t :
    firstNodeEquiv a (algebraMap _ _ (fiberT a 0)) =
      algebraMap _ _ (NodalFiber.p (0 : R)) := by
  change firstNodeForward a _ = _
  rw [firstNodeForward_base, fiberToFirstNode_t]

/-- The node equivalence retains the original tangent slope. -/
@[simp] theorem firstNodeEquiv_v :
    firstNodeEquiv a (algebraMap _ _ (fiberV a 0)) =
      algebraMap _ _ (NodalFiber.q (0 : R)) := by
  change firstNodeForward a _ = _
  rw [firstNodeForward_base, fiberToFirstNode_v]

/-- Every point of the first tangent component lies in this node neighborhood. -/
theorem first_tangent_mem_node_open (ha : IsUnit a)
    (p : PrimeSpectrum (FiberCoordinate a 0)) (hv : fiberV a 0 ∈ p.asIdeal) :
    fiberV a 0 + algebraMap R _ a ∉ p.asIdeal := by
  intro h
  exact fiber_tangent_branches_disjoint a ha p ⟨hv, h⟩

/-- The corresponding node open contains its whole second-coordinate-zero branch. -/
theorem first_node_origin_mem_open (ha : IsUnit a)
    (p : PrimeSpectrum (NodalFiber.Coordinate (0 : R)))
    (hq : NodalFiber.q (0 : R) ∈ p.asIdeal) :
    NodalFiber.q (0 : R) + algebraMap R _ a ∉ p.asIdeal := by
  intro h
  have hu : algebraMap R (NodalFiber.Coordinate (0 : R)) a ∈ p.asIdeal := by
    simpa only [add_sub_cancel_left] using p.asIdeal.sub_mem h hq
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hu (ha.map (algebraMap R _)))

end FLT.Mazur.WeierstrassModificationX
