/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineBundleDualEvaluation
public import FLT.Mazur.SchemePicardClasses

/-!
# The Picard group of a scheme

Duality descends to isomorphism classes and canonical contraction proves the
inverse law. No representability or finiteness assertion is part of this group.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.SchemePicard

open FCurve

variable {X : Scheme.{u}}

instance : Inv (Pic X) where
  inv a := Quotient.liftOn a
    (fun M ↦ mk (moduleSheafDual M.val) (dual_locallyFreeRankOne M.property))
    (fun _ _ ⟨e⟩ ↦ mk_eq_of_iso _ _ (moduleSheafDualIso _ e).symm)

/-- The intrinsic dual represents the inverse Picard class. -/
@[simp]
theorem mk_dual (M : X.Modules) (hM : LocallyFreeRankOne M) :
    mk (moduleSheafDual M) (dual_locallyFreeRankOne hM) = (mk M hM)⁻¹ := rfl

instance : CommGroup (Pic X) where
  inv_mul_cancel a := by
    induction a using inductionOn with | h M hM =>
      exact mk_eq_of_iso _ _ (evaluationIso hM)

/-- Tensoring with a line bundle reflects isomorphism of line bundles. -/
theorem tensor_iso_iff (L M N : X.Modules) (hL : LocallyFreeRankOne L)
    (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N) :
    Nonempty (ModuleSheafTensor.tensor L M ≅ ModuleSheafTensor.tensor L N) ↔
      Nonempty (M ≅ N) := by
  rw [← mk_eq_mk_iff (hL.tensor hM) (hL.tensor hN)]
  change mk L hL * mk M hM = mk L hL * mk N hN ↔ _
  rw [mul_left_cancel_iff, mk_eq_mk_iff]

/-- A tensor product is trivial exactly when its factors have inverse classes. -/
theorem tensor_trivial_iff (M N : X.Modules)
    (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N) :
    Nonempty (ModuleSheafTensor.tensor M N ≅ structureModule X) ↔
      mk M hM = (mk N hN)⁻¹ := by
  rw [← mk_eq_one_iff _ (hM.tensor hN), mk_tensor, mul_eq_one_iff_eq_inv]

end FLT.Mazur.SchemePicard
