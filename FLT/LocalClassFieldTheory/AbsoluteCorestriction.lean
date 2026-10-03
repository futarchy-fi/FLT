/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FixingSubgroupTopology
public import FLT.LocalClassFieldTheory.CorestrictionRestrictionH2
public import FLT.LocalClassFieldTheory.AbsoluteRestriction

/-!
# Absolute corestriction for a finite intermediate field

Identify the extension's Galois group with the open fixing subgroup and apply
the constructed continuous transfer. The restriction-degree formula follows
from the actual cochain comparison.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex

variable (K C : Type) [Field K] [Field C] [Algebra K C] [IsGalois K C]
  (E : IntermediateField K C) [FiniteDimensional K E]

attribute [local instance] fieldUnitAction fixingSubgroupCompact fixingSubgroupCosetFintype

variable [TopologicalSpace (Additive Cˣ)] [DiscreteTopology (Additive Cˣ)]

/-- Coefficients are unchanged by identification with the fixing subgroup. -/
def fixingSubgroupCoefficients :
    Rep.res (IntermediateField.fixingSubgroupEquiv E).toMonoidHom
      (Rep.of (Representation.ofDistribMulAction ℤ Gal(C/E) (Additive Cˣ))) ⟶
      Rep.of (Representation.ofDistribMulAction ℤ E.fixingSubgroup (Additive Cˣ)) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- Pull back continuous cochains to the actual fixing subgroup. -/
def fixingSubgroupComplex : continuousCochains ℤ Gal(C/E) (Additive Cˣ) ⟶
    continuousCochains ℤ E.fixingSubgroup (Additive Cˣ) :=
  continuousRestriction (IntermediateField.fixingSubgroupEquiv E).toMonoidHom
    (fixingSubgroupEquiv_continuous K C E) (fixingSubgroupCoefficients K C E)

/-- Corestriction of absolute continuous H2, constructed from finite coset sums. -/
def absoluteCorestriction : continuousCohomology ℤ Gal(C/E) (Additive Cˣ) 2 →+
    continuousCohomology ℤ Gal(C/K) (Additive Cˣ) 2 :=
  (continuousCorestrictionH2 E.fixingSubgroup E.fixingSubgroup_isOpen).comp
    (homologyMap (fixingSubgroupComplex K C E) 2).hom.toAddMonoidHom

/-- Scalar restriction followed by subgroup identification is subgroup restriction. -/
theorem fixingSubgroupComplex_restriction :
    absoluteRestrictionComplex K C E ≫ fixingSubgroupComplex K C E =
      continuousRestriction E.fixingSubgroup.subtype continuous_subtype_val
        (subgroupRestrictionCoefficients (M := Additive Cˣ) E.fixingSubgroup) := by
  ext n c
  rfl

/-- Actual corestriction after restriction multiplies by the extension degree. -/
theorem absoluteCorestriction_restriction
    (x : continuousCohomology ℤ Gal(C/K) (Additive Cˣ) 2) :
    absoluteCorestriction K C E ((absoluteRestriction K C E 2).hom x) =
      Module.finrank K E • x := by
  have he : (homologyMap (fixingSubgroupComplex K C E) 2).hom
      ((absoluteRestriction K C E 2).hom x) = subgroupRestrictionH2 E.fixingSubgroup x := by
    change ((homologyMap (absoluteRestrictionComplex K C E) 2 ≫
      homologyMap (fixingSubgroupComplex K C E) 2).hom) x = _
    rw [← homologyMap_comp, fixingSubgroupComplex_restriction]
    rfl
  change continuousCorestrictionH2 E.fixingSubgroup E.fixingSubgroup_isOpen
    ((homologyMap (fixingSubgroupComplex K C E) 2).hom
      ((absoluteRestriction K C E 2).hom x)) = _
  rw [he, continuousCorestrictionH2_restriction, fixingSubgroup_card_eq_finrank]

end LocalClassFieldTheory
