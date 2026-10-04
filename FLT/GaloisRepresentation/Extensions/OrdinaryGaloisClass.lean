/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep
public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltrationClass

/-!
# Extension classes for actual continuous Galois representations

The continuity hypothesis of the filtration construction is discharged from
the existing `GaloisRep` topology by continuous linear evaluation.
-/

@[expose] public noncomputable section

namespace GaloisRepresentation.Extensions.OrdinaryFiltration

variable {K k V : Type*} [Field K] [Field k] [TopologicalSpace k] [DiscreteTopology k]
    [AddCommGroup V] [Module k V] [TopologicalSpace V] [DiscreteTopology V]
    [IsModuleTopology k V] (ρ : GaloisRep K k V)
    {α β : Field.absoluteGaloisGroup K →* kˣ}

omit [DiscreteTopology k] in
/-- The orbit maps of the given continuous Galois representation are continuous. -/
theorem continuous_galoisOrbit (x : V) :
    Continuous (fun g ↦ ρ.toRepresentation g x) := by
  let := moduleTopology k (Module.End k V)
  exact (IsModuleTopology.continuous_of_linearMap
    (LinearMap.applyₗ (R := k) (M := V) (M₂ := V) x)).comp ρ.continuous

/-- The class of a filtration on the actual `GaloisRep`, with no continuity premise. -/
def galoisClass (E : OrdinaryFiltration ρ.toRepresentation α β) :
    ContinuousClass (Field.absoluteGaloisGroup K) (OrdinaryHomModule α β) :=
  E.extensionClass (continuous_galoisOrbit ρ)

/-- Any quotient section computes the actual Galois extension class. -/
theorem galoisClass_eq (E : OrdinaryFiltration ρ.toRepresentation α β)
    (w : V) (hw : E.projection w = 1) :
    galoisClass ρ E = continuousClassMk (E.cocycleOf (continuous_galoisOrbit ρ) w hw) :=
  E.extensionClass_eq (continuous_galoisOrbit ρ) w hw

end GaloisRepresentation.Extensions.OrdinaryFiltration
