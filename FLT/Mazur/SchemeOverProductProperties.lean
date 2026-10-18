/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Geometric properties of the actual product over a scheme

Transport the standard pullback properties to the binary product in `Over S`.
The comparison keeps the original structure map used by parameter schemes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeOverProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} (X Y : Over S)

/-- The product structure map factors through the canonical pullback comparison. -/
theorem structure_eq :
    (X ⨯ Y).hom = (Over.prodLeftIsoPullback X Y).hom ≫
      pullback.fst X.hom Y.hom ≫ X.hom := by
  rw [Over.prodLeftIsoPullback_hom_fst_assoc, Over.w]

/-- Finite type is preserved by the actual binary product over the base. -/
instance locallyOfFiniteType [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (X ⨯ Y).hom := by
  rw [structure_eq]
  infer_instance

/-- Quasi-compactness is preserved by the actual binary product over the base. -/
instance quasiCompact [QuasiCompact X.hom] [QuasiCompact Y.hom] :
    QuasiCompact (X ⨯ Y).hom := by
  rw [structure_eq]
  infer_instance

/-- Separatedness is preserved by the actual binary product over the base. -/
instance isSeparated [IsSeparated X.hom] [IsSeparated Y.hom] :
    IsSeparated (X ⨯ Y).hom := by
  rw [structure_eq]
  infer_instance

end FLT.Mazur.SchemeOverProduct
