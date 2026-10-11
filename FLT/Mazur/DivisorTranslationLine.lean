/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeAcyclicPicardOpen

/-!
# Actual translation lines from full Cartier divisors

Tensoring the positive divisor line with the dual of an original line gives
an explicit translation. Its tensor with the original line is isomorphic to
the full divisor line, so the relative class equation retains that divisor.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X S : Scheme} (f : X ⟶ S) (D : Divisor X)
  (L : X.Modules) (hL : LocallyFreeRankOne L)

/-- The translation is an actual line on the original total space. -/
def divisorTranslationLine : X.Modules :=
  ModuleSheafTensor.tensor (divisorLineBundle D.val D.property) (moduleSheafDual L)

include hL in
/-- Both factors are lines, so the translation is a line. -/
theorem divisorTranslationLine_rankOne : LocallyFreeRankOne (divisorTranslationLine D L) :=
  D.property.divisorLineBundle_locallyFreeRankOne.tensor hL.dual

/-- The constructed translation has the exact quotient class of the full divisor. -/
theorem divisorTranslationLine_class :
    relativeClass f (mk (divisorTranslationLine D L) (divisorTranslationLine_rankOne D L hL)) =
      abel f D / relativeClass f (mk L hL) := by
  change relativeClass f (mk (divisorLineBundle D.val D.property)
    D.property.divisorLineBundle_locallyFreeRankOne * (mk L hL)⁻¹) = _
  rw [map_mul, map_inv]
  rfl

include hL in
/-- Tensoring the original line by the constructed translation recovers the full divisor line. -/
theorem divisorTranslationLine_tensor_iso :
    Nonempty (ModuleSheafTensor.tensor L (divisorTranslationLine D L) ≅
      divisorLineBundle D.val D.property) := by
  apply (mk_eq_mk_iff (hL.tensor (divisorTranslationLine_rankOne D L hL))
    D.property.divisorLineBundle_locallyFreeRankOne).mp
  change mk L hL * (mk (divisorLineBundle D.val D.property)
    D.property.divisorLineBundle_locallyFreeRankOne * (mk L hL)⁻¹) = _
  rw [mul_left_comm, mul_inv_cancel, mul_one]

/-- The original relative class is recovered by division by the actual translation line. -/
theorem divisorTranslationLine_recover :
    abel f D / relativeClass f
      (mk (divisorTranslationLine D L) (divisorTranslationLine_rankOne D L hL)) =
        relativeClass f (mk L hL) := by
  rw [divisorTranslationLine_class, div_div_cancel]

end FLT.Mazur.CartierAbel
