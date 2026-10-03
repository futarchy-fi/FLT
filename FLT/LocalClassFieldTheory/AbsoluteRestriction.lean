/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.GaloisKernelTopology
public import FLT.LocalClassFieldTheory.ContinuousRestriction

/-!
# Restriction to an intermediate base field

Restrict continuous field-unit cochains along the actual inclusion of Galois
groups, leaving their coefficients unchanged.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex

variable (K C : Type) [Field K] [Field C] [Algebra K C] [IsGalois K C]
  (E : IntermediateField K C)

attribute [local instance] fieldUnitAction

/-- The coefficient identity intertwines restriction of scalars on Galois groups. -/
def absoluteRestrictionCoefficients :
    Rep.res (AlgEquiv.restrictScalarsHom K : Gal(C/E) →* Gal(C/K))
      (Rep.of (Representation.ofDistribMulAction ℤ Gal(C/K) (Additive Cˣ))) ⟶
      Rep.of (Representation.ofDistribMulAction ℤ Gal(C/E) (Additive Cˣ)) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

variable [TopologicalSpace (Additive Cˣ)] [DiscreteTopology (Additive Cˣ)]

/-- Actual restriction of continuous cochains to the intermediate base field. -/
def absoluteRestrictionComplex : continuousCochains ℤ Gal(C/K) (Additive Cˣ) ⟶
    continuousCochains ℤ Gal(C/E) (Additive Cˣ) :=
  continuousRestriction (AlgEquiv.restrictScalarsHom K)
    (galoisRestrictScalars_continuous K C E) (absoluteRestrictionCoefficients K C E)

/-- Actual restriction of continuous multiplicative cohomology. -/
def absoluteRestriction (n : ℕ) : continuousCohomology ℤ Gal(C/K) (Additive Cˣ) n ⟶
    continuousCohomology ℤ Gal(C/E) (Additive Cˣ) n :=
  homologyMap (absoluteRestrictionComplex K C E) n

end LocalClassFieldTheory
