/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryGeometricTensor
public import FLT.Mazur.SchemeScalarImageQuotient
public import FLT.Mazur.SchemeRelationScalarBaseChange

/-!
# The full original boundary relation over the scalar image

Construct both boundary endpoint maps after scalar base change, then the
comparison from the full original boundary relation to the kernel pair of
its exact scalar-image projection. No domination or effectivity is presumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars FlatScalarSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} (p q : D ⟶ A) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
attribute [local irreducible] InvariantIdealRelation.snd
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "B" => pullback p J.subschemeι
local notation "a" => pullback.snd p J.subschemeι
local notation "b" => InvariantIdealRelation.snd J p q hJ
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra


/-- The full original boundary relation coequalizes the actual original scalar morphism. -/
theorem originalBoundary_scalar_condition :
    a ≫ SchemeScalarPrincipalNeighborhood.scalarMorphism (algebraMap R Γ(J.subscheme, ⊤)) =
      b ≫ SchemeScalarPrincipalNeighborhood.scalarMorphism
        (algebraMap R Γ(J.subscheme, ⊤)) := by
  have hj := FlatScalarFunctionPushout.scalarMorphism_natural
    J.subschemeι (originalBoundaryMap (p := p) (q := q) J) rfl
  rw [← hj, ← Category.assoc, ← Category.assoc, ← pullback.condition,
    InvariantIdealRelation.snd_ι, Category.assoc, Category.assoc]
  exact congrArg (fun v ↦ pullback.fst p J.subschemeι ≫ v)
    (SchemeRelationInvariantSpectrum.projection_condition p q)

variable (S : Type) [CommRing S] [Algebra (invariants p.appTop.hom q.appTop.hom) S]
local notation "f" =>
  SchemeScalarPrincipalNeighborhood.scalarMorphism
    (J.subschemeι.appTop.hom.comp (Subring.subtype R))
local notation "ρ" => algebraMap R S

/-- Base change of the full original closed relation, with no selected component. -/
def originalBoundaryScalarRelation : Scheme := SchemeRelationScalarBaseChange.relation a f ρ

/-- The actual map from the whole original relation to the exact scalar-image kernel pair. -/
def originalBoundaryKernelComparison : originalBoundaryScalarRelation p q J S ⟶
    pullback (SchemeScalarImageQuotient.projection (base R S J.subscheme))
      (SchemeScalarImageQuotient.projection (base R S J.subscheme)) :=
  SchemeRelationScalarBaseChange.kernelComparison a b f
    (originalBoundary_scalar_condition p q J hJ) ρ

/-- The comparison's first endpoint is the literal original boundary relation arrow. -/
theorem originalBoundaryKernelComparison_first :
    originalBoundaryKernelComparison p q J hJ S ≫ pullback.fst _ _ ≫
      source R S J.subscheme = SchemeRelationScalarBaseChange.original a f ρ ≫ a := by
  exact (SchemeRelationScalarBaseChange.kernelComparison_first_assoc a b f
    (originalBoundary_scalar_condition p q J hJ) ρ _).trans
      (SchemeRelationScalarBaseChange.first_original a f ρ)

/-- Its second endpoint retains the independent full original boundary equation. -/
theorem originalBoundaryKernelComparison_second :
    originalBoundaryKernelComparison p q J hJ S ≫ pullback.snd _ _ ≫
      source R S J.subscheme = SchemeRelationScalarBaseChange.original a f ρ ≫ b := by
  exact (SchemeRelationScalarBaseChange.kernelComparison_second_assoc a b f
    (originalBoundary_scalar_condition p q J hJ) ρ _).trans
      (SchemeRelationScalarBaseChange.second_original a b f
        (originalBoundary_scalar_condition p q J hJ) ρ)

end FLT.Mazur.EquivalenceRelationOrderedFrames
