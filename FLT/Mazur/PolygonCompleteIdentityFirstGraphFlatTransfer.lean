/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstErrorOriginalFlat
public import FLT.Mazur.PolygonCompleteIdentityFirstGraphOriginalFlat

/-!
# Flatness of the unchanged finite branch graph over its original base

The error algebra and source-target graph have identical elements inside
the original branch pair. Their concrete equivalence preserves the full
original coefficient map, so the constructed chart comparison proves the
flatness required for original defect descent.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "S" => Ring K[T;T⁻¹] 1
local notation "E" => completeIdentityFirstErrorAlgebra K n h (0 : Fin n)
local notation "G" => completeIdentityFirstGraphAlgebra K n h (0 : Fin n)

/-- Cache the unchanged error algebra ring structure. -/
local instance firstGraphFlatTransferErrorCommRing : CommRing (E) := inferInstance

/-- Cache the unchanged branch graph ring structure. -/
local instance firstGraphFlatTransferGraphCommRing : CommRing (G) := inferInstance

/-- The identity on the original branch pair identifies the two constructed graph algebras. -/
def completeIdentityFirstErrorGraphEquiv : (E) ≃ₐ[S] (G) :=
  Subalgebra.equivOfEq ((E).restrictScalars (S)) (G)
    (completeIdentityFirstErrorAlgebra_eq_graph K n h 0)

/-- This concrete equivalence retains every coefficient of the original truncated base. -/
theorem completeIdentityFirstErrorGraphEquiv_originalScalars :
    (completeIdentityFirstErrorGraphEquiv K n h).toRingHom.comp
      (completeIdentityFirstErrorOriginalScalars K n h) =
        completeIdentityFirstGraphOriginalScalars K n h 0 := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  exact (firstNodeBranchPair K[T;T⁻¹]).commutes
    (stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1 r)

/-- The actual finite branch graph is flat over its unchanged original coefficient map. -/
theorem completeIdentityFirstGraphOriginalScalars_flat :
    (completeIdentityFirstGraphOriginalScalars K n h 0).Flat := by
  rw [← completeIdentityFirstErrorGraphEquiv_originalScalars]
  exact (completeIdentityFirstErrorOriginalScalars_flat K n h).comp
    (RingHom.Flat.of_bijective (completeIdentityFirstErrorGraphEquiv K n h).bijective)

end FLT.Mazur.PolygonInfinitesimalStages
