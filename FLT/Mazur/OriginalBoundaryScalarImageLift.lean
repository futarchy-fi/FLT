/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryKernelPairLift
public import FLT.Mazur.OriginalBoundaryScalarRelation
public import FLT.Mazur.SchemeScalarImageDescent

/-!
# Full original boundary lifts from the constructed scalar image

The quotient, quotient surjection, boundary projection and full kernel
comparison are now fixed constructions. Faithful flatness of the exact image
coefficients and epimorphy of this comparison construct full boundary lifts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars FlatScalarSchemeBaseChange SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} (p q : D ⟶ A) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local notation "R" => invariants p.appTop.hom q.appTop.hom
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] FlatScalarSchemeBaseChange.baseChange
variable (S : Type) [CommRing S] [Algebra (invariants p.appTop.hom q.appTop.hom) S]
  [IsAffine (baseChange (invariants p.appTop.hom q.appTop.hom) S J.subscheme)]
local notation "b" => base R S J.subscheme

/-- The constructed scalar image and full relation comparison produce a full scalar solution. -/
theorem originalBoundary_scalar_of_image
    (hflat : (RingHom.kerLift (FlatScalarFunctionPushout.scalarMap b)).FaithfullyFlat)
    [Epi (originalBoundaryKernelComparison p q J hJ S)]
    (t : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    ∃ s : S, FlatScalarFunctionPushout.scalarMap b s =
      (source R S J.subscheme).appTop t.val := by
  let _ := SchemeScalarImageQuotient.projection_effectiveEpi b hflat
  exact originalBoundary_scalar_of_kernelPair_cover p q J hJ S
    (SchemeScalarImageQuotient.quotient b) (SchemeScalarImageQuotient.quotient_surjective b)
    (SchemeScalarImageQuotient.projection b) (SchemeScalarImageQuotient.projection_inclusion b)
    (originalBoundaryKernelComparison p q J hJ S) _
    (originalBoundaryKernelComparison_first p q J hJ S)
    (originalBoundaryKernelComparison_second p q J hJ S) t

/-- Scalar descent on the fixed full image constructs an invariant source numerator. -/
theorem originalBoundary_geometric_lift_of_image
    (hflat : (RingHom.kerLift (FlatScalarFunctionPushout.scalarMap b)).FaithfullyFlat)
    [Epi (originalBoundaryKernelComparison p q J hJ S)]
    (t : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    ∃ a : Γ(baseChange R S A, ⊤),
      (originalBranchFirst p q S).appTop a = (originalBranchSecond p q S).appTop a ∧
      (originalBranchBoundary p q J S).appTop a = (source R S J.subscheme).appTop t.val := by
  obtain ⟨s, hs⟩ := originalBoundary_scalar_of_image p q J hJ S hflat t
  exact originalBranch_lift_of_scalar p q S J t.val s hs

end FLT.Mazur.EquivalenceRelationOrderedFrames
