/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChangeEquationUniversal
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The affine scheme of varying Weierstrass equation comparisons

The comparison scheme is an actual closed subscheme of the unrestricted
change space. Its affine-test maps classify precisely the full compatible
changes, over the original coefficient base and in every characteristic.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)

/-- The scheme of all admissible changes, before imposing equation compatibility. -/
def parameterScheme : Scheme := Spec (.of (ParameterRing R))

/-- The actual affine scheme cut out by all five comparison equations. -/
def comparisonScheme : Scheme := Spec (.of (EquationRing W V))

/-- The closed comparison locus retains its unrestricted change parameter. -/
def comparisonInclusion : comparisonScheme W V ⟶ parameterScheme (R := R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (equationIdeal W V)))

instance comparisonInclusion_closed : IsClosedImmersion (comparisonInclusion W V) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The comparison parameter is over the unchanged coefficient base. -/
def comparisonStructure : comparisonScheme W V ⟶ Spec (.of R) :=
  Spec.algebraMap R (EquationRing W V)

/-- The equation locus represents precisely all compatible admissible changes on affine tests. -/
def comparisonSchemePointEquiv (A : Type) [CommRing A] [Algebra R A] :
    {f : Spec (.of A) ⟶ comparisonScheme W V //
      f ≫ comparisonStructure W V = Spec.algebraMap R A} ≃
        {C : VariableChange A // C • V.map (algebraMap R A) = W.map (algebraMap R A)} :=
  Spec.homEquivAlgHom.trans (equationParameterEquiv W V)

/-- Every admissible full equation comparison has a unique actual parameter morphism. -/
theorem comparisonSchemePoint_unique (A : Type) [CommRing A] [Algebra R A]
    (C : VariableChange A) (h : C • V.map (algebraMap R A) = W.map (algebraMap R A)) :
    ∃! f : {f : Spec (.of A) ⟶ comparisonScheme W V //
        f ≫ comparisonStructure W V = Spec.algebraMap R A},
      comparisonSchemePointEquiv W V A f = ⟨C, h⟩ :=
  (comparisonSchemePointEquiv W V A).bijective.existsUnique ⟨C, h⟩

end FLT.Mazur.WeierstrassChangeParameter
