/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfTorsor
public import FLT.GroupScheme.SquareZeroAugmentationPoints

/-! # Differences of actual local lifts and their infinitesimal tangents -/

@[expose] public noncomputable section
open WithConv
namespace HopfAlgebra
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [HopfAlgebra R A] [Algebra R B] [Algebra R C]

/-- Convolution on points with arbitrary test-algebra values is a group. -/
local instance pointDifferenceGroup : Group (WithConv (A →ₐ[R] B)) where
  inv f := toConv (f.ofConv.comp (antipodeAlgHom R A))
  inv_mul_cancel f := conv_antipode_mul f.ofConv

/-- The group difference of two actual points, using the original antipode. -/
def pointDifference (f g : A →ₐ[R] B) : A →ₐ[R] B :=
  (toConv (f.comp (antipodeAlgHom R A)) * toConv g).ofConv

/-- Equal reductions put the actual group difference in the infinitesimal kernel. -/
theorem pointDifference_reduction (q : B →ₐ[R] C) (f g : A →ₐ[R] B)
    (hfg : q.comp f = q.comp g) :
    q.comp (pointDifference f g) =
      (Algebra.ofId R C).comp (Bialgebra.counitAlgHom R A) := by
  rw [pointDifference, AlgHom.comp_convMul_distrib]
  simp only [← AlgHom.comp_assoc, hfg]
  exact congrArg WithConv.ofConv (conv_antipode_mul (q.comp g))

/-- Translating the difference back by the first point recovers the second point. -/
theorem pointDifference_recover (f g : A →ₐ[R] B) :
    (toConv f * toConv (pointDifference f g)).ofConv = g := by
  change (toConv f * ((toConv f)⁻¹ * toConv g)).ofConv = g
  rw [mul_inv_cancel_left]

/-- Group differences obey the cocycle identity before any choice of local correction. -/
theorem pointDifference_cocycle (f g h : A →ₐ[R] B) :
    (toConv (pointDifference f g) * toConv (pointDifference g h)).ofConv =
      pointDifference f h := by
  change (((toConv f)⁻¹ * toConv g) * ((toConv g)⁻¹ * toConv h)).ofConv =
    ((toConv f)⁻¹ * toConv h).ofConv
  rw [mul_assoc, ← mul_assoc (toConv g), mul_inv_cancel, one_mul]

/-- The discrepancy is the identity exactly when the two points already agree. -/
theorem pointDifference_eq_one_iff (f g : A →ₐ[R] B) :
    pointDifference f g = (1 : WithConv (A →ₐ[R] B)).ofConv ↔ f = g := by
  change ((toConv f)⁻¹ * toConv g).ofConv = (1 : WithConv (A →ₐ[R] B)).ofConv ↔ _
  rw [ofConv_injective.eq_iff, inv_mul_eq_one, toConv_injective.eq_iff]

/-- The actual discrepancy determines a tangent in the square-zero reduction kernel. -/
def pointDifferenceTangent (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥)
    (f g : A →ₐ[R] B) (hfg : q.comp f = q.comp g) :
    (Bialgebra.counitAlgHom R A).augmentationTangent (M := RingHom.ker q) :=
  AlgHom.augmentationPointToTangent _ q hJ
    ⟨pointDifference f g, pointDifference_reduction q f g hfg⟩

/-- The tangent reconstructs the same original group difference. -/
theorem pointDifferenceTangent_recover (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥)
    (f g : A →ₐ[R] B) (hfg : q.comp f = q.comp g) :
    (AlgHom.tangentToAugmentationPoint _ q hJ (pointDifferenceTangent q hJ f g hfg)).val =
      pointDifference f g :=
  congrArg Subtype.val ((AlgHom.augmentationPointKernelEquiv _ q hJ).symm_apply_apply
    ⟨pointDifference f g, pointDifference_reduction q f g hfg⟩)

end HopfAlgebra
