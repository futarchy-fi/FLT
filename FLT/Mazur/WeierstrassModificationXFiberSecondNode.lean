/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberFirstNode
public import FLT.Mazur.WeierstrassModificationXFiberTangentSwitch

/-!
# The second oriented horizontal fiber node

Removing v=0 leaves the node with coordinates t and v+a. Recentering the
actual fiber gives the first-node construction with parameter -a. Thus both
node neighborhoods retain the original incidence ratio and tangent orientation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (a : R)

/-- The actual fiber neighborhood containing the second oriented tangent. -/
abbrev SecondFiberOpen := Localization.Away (fiberV a 0)

/-- Recenter the second neighborhood using the original translated slope. -/
def secondFiberOpenEquiv : SecondFiberOpen a ≃ₐ[R] FirstFiberOpen (-a) :=
  IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (fiberV a 0))
    (T := Submonoid.powers (fiberV (-a) 0 + algebraMap R _ (-a)))
    _ _ (fiberTangentEquiv a 0) (by
    rw [Submonoid.map_powers, fiberTangentEquiv_v])

/-- The recentered localization uses the original coordinate substitution. -/
@[simp] theorem secondFiberOpenEquiv_base (z : FiberCoordinate a 0) :
    secondFiberOpenEquiv a (algebraMap _ _ z) =
      algebraMap _ _ (fiberTangentEquiv a 0 z) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ z

/-- The second actual neighborhood is the matching open of the existing split node. -/
def secondNodeEquiv : SecondFiberOpen a ≃ₐ[R] FirstNodeOpen (-a) :=
  (secondFiberOpenEquiv a).trans (firstNodeEquiv (-a))

/-- The second node retains the original incidence ratio. -/
@[simp] theorem secondNodeEquiv_t :
    secondNodeEquiv a (algebraMap _ _ (fiberT a 0)) =
      algebraMap _ _ (NodalFiber.p (0 : R)) := by
  rw [secondNodeEquiv, AlgEquiv.trans_apply, secondFiberOpenEquiv_base,
    fiberTangentEquiv_t, firstNodeEquiv_t]

/-- The second node's slope coordinate is exactly v+a, with no orientation discarded. -/
theorem secondNodeEquiv_second :
    secondNodeEquiv a (algebraMap _ _ (fiberV a 0 + algebraMap R _ a)) =
      algebraMap _ _ (NodalFiber.q (0 : R)) := by
  rw [secondNodeEquiv, AlgEquiv.trans_apply, secondFiberOpenEquiv_base,
    fiberTangentEquiv_second, firstNodeEquiv_v]

/-- The second neighborhood contains the full second tangent component. -/
theorem second_tangent_mem_node_open (ha : IsUnit a)
    (p : PrimeSpectrum (FiberCoordinate a 0))
    (hv : fiberV a 0 + algebraMap R _ a ∈ p.asIdeal) : fiberV a 0 ∉ p.asIdeal := by
  intro h
  exact fiber_tangent_branches_disjoint a ha p ⟨h, hv⟩

/-- The two node neighborhoods cover the entire three-line fiber over a split base. -/
theorem fiber_node_opens_cover (ha : IsUnit a) (p : PrimeSpectrum (FiberCoordinate a 0)) :
    fiberV a 0 + algebraMap R _ a ∉ p.asIdeal ∨ fiberV a 0 ∉ p.asIdeal := by
  by_cases hv : fiberV a 0 ∈ p.asIdeal
  · exact Or.inl (first_tangent_mem_node_open a ha p hv)
  · exact Or.inr hv

end FLT.Mazur.WeierstrassModificationX
