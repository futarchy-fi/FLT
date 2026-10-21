/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryScalarRelation
public import FLT.Mazur.SchemeRelationScalarCartesian

/-!
# Original cartesian boundary relations on scalar branches

An original full boundary kernel pair supplies the canonical comparison
isomorphism on every scalar branch. This preservation theorem requires no
etaleness, flatness or independently assumed branch coverage.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars FlatScalarSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} (p q : D ⟶ A) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local notation "R" => invariants p.appTop.hom q.appTop.hom
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
variable (S : Type) [CommRing S] [Algebra (invariants p.appTop.hom q.appTop.hom) S]
set_option quotPrecheck false
local notation "f" => SchemeScalarPrincipalNeighborhood.scalarMorphism
  (algebraMap R Γ(J.subscheme, ⊤))

/-- An original full boundary kernel pair supplies every scalar branch comparison. -/
theorem originalBoundaryKernelComparison_isIso_of_original
    (H : IsPullback (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ) f f) :
    IsIso (originalBoundaryKernelComparison p q J hJ S) := by
  exact SchemeRelationScalarBaseChange.kernelComparison_isIso_of_original
    (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ) f
    (originalBoundary_scalar_condition p q J hJ) (algebraMap R S) H

/-- Original cartesianity constructs full branch domination, including nilpotent equations. -/
theorem originalBoundaryKernelComparison_epi_of_original
    (H : IsPullback (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ) f f) :
    Epi (originalBoundaryKernelComparison p q J hJ S) := by
  let _ := originalBoundaryKernelComparison_isIso_of_original p q J hJ S H
  infer_instance

end FLT.Mazur.EquivalenceRelationOrderedFrames
