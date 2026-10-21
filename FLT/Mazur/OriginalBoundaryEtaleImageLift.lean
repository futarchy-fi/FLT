/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryKernelPairLift
public import FLT.Mazur.OriginalBoundaryScalarRelation
public import FLT.Mazur.SchemeRelationScalarEtale

/-!
# Full boundary descent from etale scalar-image geometry

Etaleness of the original first endpoint and of the constructed image
projection makes the canonical full kernel comparison etale. Surjectivity
of both constructed maps therefore gives all the effective descent data.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars FlatScalarSchemeBaseChange SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} (p q : D ⟶ A) [Etale p]
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
local notation "R" => invariants p.appTop.hom q.appTop.hom
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
variable (S : Type) [CommRing S] [Algebra (invariants p.appTop.hom q.appTop.hom) S]
local notation "b" => base R S J.subscheme
local notation "c" => SchemeScalarImageQuotient.projection b

/-- Surjectivity of the canonical full comparison now implies effective domination. -/
theorem originalBoundaryKernelComparison_effectiveEpi [Etale c]
    [Surjective (originalBoundaryKernelComparison p q J hJ S)] :
    EffectiveEpi (originalBoundaryKernelComparison p q J hJ S) := by
  dsimp only [base, originalBoundaryKernelComparison] at *
  exact SchemeRelationScalarBaseChange.kernelComparison_effectiveEpi
    (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ) _
    (originalBoundary_scalar_condition p q J hJ) (algebraMap R S)

attribute [local irreducible] FlatScalarSchemeBaseChange.baseChange

/-- Full etale image geometry constructs scalar boundary solutions for every original section. -/
theorem originalBoundary_scalar_of_etale_image [Etale c] [Surjective c]
    [Surjective (originalBoundaryKernelComparison p q J hJ S)]
    (t : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    ∃ s : S, FlatScalarFunctionPushout.scalarMap b s =
      (source R S J.subscheme).appTop t.val := by
  let _ := originalBoundaryKernelComparison_effectiveEpi p q J hJ S
  exact originalBoundary_scalar_of_kernelPair_cover p q J hJ S
    (SchemeScalarImageQuotient.quotient b) (SchemeScalarImageQuotient.quotient_surjective b)
    c (SchemeScalarImageQuotient.projection_inclusion b)
    (originalBoundaryKernelComparison p q J hJ S) _
    (originalBoundaryKernelComparison_first p q J hJ S)
    (originalBoundaryKernelComparison_second p q J hJ S) t

/-- The descended scalar constructs a full invariant source numerator. -/
theorem originalBoundary_geometric_lift_of_etale_image [Etale c] [Surjective c]
    [Surjective (originalBoundaryKernelComparison p q J hJ S)]
    (t : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    ∃ a : Γ(baseChange R S A, ⊤),
      (originalBranchFirst p q S).appTop a = (originalBranchSecond p q S).appTop a ∧
      (originalBranchBoundary p q J S).appTop a = (source R S J.subscheme).appTop t.val := by
  obtain ⟨s, hs⟩ := originalBoundary_scalar_of_etale_image p q J hJ S t
  exact originalBranch_lift_of_scalar p q S J t.val s hs

end FLT.Mazur.EquivalenceRelationOrderedFrames
