/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSingularCriterion
public import FLT.Mazur.CyclicMarkingDivisorTransport
public import FLT.Mazur.RetainedSubgroupCartierMarking

/-!
# Transport of singular orbit subgroup equations across full curve isomorphisms

Transport keeps the whole subgroup carrier and every original orbit factor.
The multiplication criterion is therefore invariant without faithful labels.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E F : GeneralizedEllipticCurve S} {n : ℕ}
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (ψ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ F.group))
  (e : E ≅ F) (he : ∀ i, φ i ≫ e.hom.group = ψ i)

include he in
/-- An exact orbit subgroup transports with its full ideal, retaining repeated labels. -/
theorem singularOrbitSubgroup_transport_ideal (H : E.FiniteSubgroup n)
    (hH : H.ideal = E.cyclicMarkingIdeal φ) :
    (H.transport e).ideal = F.cyclicMarkingIdeal ψ := by
  let a := H.transportCompatibleIso e
  rw [FiniteSubgroup.ideal_transport H (H.transport e) e a.subgroup a.compatible,
    hH, cyclicMarkingIdeal_transport φ ψ e he]

include he in
/-- The exact orbit-subgroup existence condition is invariant under full curve transport. -/
theorem singularOrbitSubgroup_transport_iff :
    (∃ H : E.FiniteSubgroup n, H.ideal = E.cyclicMarkingIdeal φ) ↔
      ∃ J : F.FiniteSubgroup n, J.ideal = F.cyclicMarkingIdeal ψ := by
  constructor
  · rintro ⟨H, hH⟩
    exact ⟨H.transport e, singularOrbitSubgroup_transport_ideal φ ψ e he H hH⟩
  · rintro ⟨J, hJ⟩
    refine ⟨J.transport e.symm, singularOrbitSubgroup_transport_ideal ψ φ e.symm ?_ J hJ⟩
    intro i
    rw [← he i, Category.assoc]
    have h := congrArg Hom.group e.hom_inv_id
    change e.hom.group ≫ e.inv.group = 𝟙 E.group at h
    change φ i ≫ (e.hom.group ≫ e.inv.group) = φ i
    rw [h, Category.comp_id]

variable [NeZero n] [SmoothOfRelativeDimension 1 E.group.hom]
  [SmoothOfRelativeDimension 1 F.group.hom]

include he in
/-- The full multiplication equation vanishes on exactly the same transported parameters. -/
theorem singularOrbitMultiplication_transport_iff :
    ClosedGroupIdeal.multiplicationEquation E.group (E.cyclicMarkingGroupIdeal φ) = 0 ↔
      ClosedGroupIdeal.multiplicationEquation F.group (F.cyclicMarkingGroupIdeal ψ) = 0 := by
  rw [E.singularCyclicDivisorMultiplication_iff_subgroup,
    F.singularCyclicDivisorMultiplication_iff_subgroup]
  exact singularOrbitSubgroup_transport_iff φ ψ e he

end FLT.Mazur.GeneralizedEllipticCurve
