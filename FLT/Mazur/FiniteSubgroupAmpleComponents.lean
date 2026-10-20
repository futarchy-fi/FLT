/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSubgroupAmpleOpen
public import FLT.Mazur.GeneralizedCurveFiberAmple

/-!
# Component support detects the subgroup's ample open

On each geometric test, the actual subgroup divisor must meet every irreducible
component of the full curve. This criterion includes singular polygon fibers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [IsAlgClosed K]

/-- On a geometric generalized curve, actual component support is exactly ampleness. -/
theorem isAmple_iff_meets_components {E : GeneralizedEllipticCurve (Spec (.of K))}
    {n : ℕ} (H : E.FiniteSubgroup n) (hI : EffectiveCartier H.ideal) :
    H.IsAmple ↔ ∀ Z ∈ irreducibleComponents E.curve.left,
      ((H.ideal.support : Set E.curve.left) ∩ Z).Nonempty := by
  let _ := E.family.family.1
  let _ : IsFinite (H.ideal.subschemeι ≫ E.curve.hom) := H.ideal_degree.1
  have hc := E.family.classified.fiber K (𝟙 _) (𝟙 _) E.curve.hom IsPullback.of_id_fst
  constructor
  · rintro ⟨hJ, ha⟩
    exact (classifiedFiber_divisor_relativeAmple_iff E.curve.hom hc hJ).mp ha
  · intro hs
    exact ⟨hI, (classifiedFiber_divisor_relativeAmple_iff E.curve.hom hc hI).mpr hs⟩

/-- A geometric test lands in the ample open exactly when its divisor meets all components. -/
theorem range_ampleOpen_iff_meets_components {S : Scheme} {E : GeneralizedEllipticCurve S}
    {n : ℕ} (H : E.FiniteSubgroup n) (hI : EffectiveCartier H.ideal)
    (g : Spec (.of K) ⟶ S) :
    Set.range g ⊆ H.ampleOpen hI ↔
      ∀ Z ∈ irreducibleComponents (E.baseChange g).curve.left,
        (((H.baseChange g).ideal.support : Set (E.baseChange g).curve.left) ∩ Z).Nonempty :=
  (H.isAmple_baseChange_iff_range hI g).symm.trans
    ((H.baseChange g).isAmple_iff_meets_components (H.effectiveCartier_baseChange hI g))

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
