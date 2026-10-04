/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfPointFiberTorsor

/-!
# Kernel action on points of Hopf quotient fibres

These formulas work over every test algebra, including those with no point in
the fibre. They construct the action and its inverse difference without choosing
a section of the quotient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open WithConv
namespace HopfAlgebra

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra R C]
  (f : B →ₐc[R] A)

/-- Convolution points form a group over an arbitrary test algebra. -/
local instance fiberTestAlgebraGroup {D : Type*} [CommRing D] [HopfAlgebra R D] :
    Group (WithConv (D →ₐ[R] C)) where
  inv x := toConv (x.ofConv.comp (antipodeAlgHom R D))
  inv_mul_cancel x := conv_antipode_mul x.ofConv

/-- The quotient morphism on points in an arbitrary test algebra. -/
def quotientPointHom : WithConv (A →ₐ[R] C) →* WithConv (B →ₐ[R] C) where
  toFun x := toConv (x.ofConv.comp f.toAlgHom)
  map_one' := by
    apply ofConv_injective
    ext b
    exact congrArg (algebraMap R C) (CoalgHomClass.counit_comp_apply f b)
  map_mul' x y := congrArg toConv (AlgHom.convMul_comp_bialgHom_distrib x y f)

/-- The points over a specified quotient point. -/
abbrev FiberPoints (p : WithConv (B →ₐ[R] C)) := {x // quotientPointHom f x = p}

variable (p : WithConv (B →ₐ[R] C))

/-- Right translation by a kernel point preserves the quotient fibre. -/
def fiberTranslate (x : FiberPoints f p) (k : (quotientPointHom (C := C) f).ker) :
    FiberPoints f p :=
  ⟨x.val * k.val, by rw [map_mul, x.property, k.property, mul_one]⟩

/-- Identity translation fixes every fibre point. -/
@[simp] theorem fiberTranslate_one (x : FiberPoints f p) : fiberTranslate f p x 1 = x := by
  apply Subtype.ext
  exact mul_one x.val

/-- Successive translations give the actual kernel right action. -/
theorem fiberTranslate_mul (x : FiberPoints f p)
    (k l : (quotientPointHom (C := C) f).ker) :
    fiberTranslate f p (fiberTranslate f p x k) l = fiberTranslate f p x (k * l) := by
  apply Subtype.ext
  exact mul_assoc x.val k.val l.val

/-- The difference of two points of a quotient fibre lies in the kernel. -/
def fiberDifference (x y : FiberPoints f p) : (quotientPointHom (C := C) f).ker :=
  ⟨x.val⁻¹ * y.val, by simp [x.property, y.property]⟩

/-- Translation by the difference recovers the second point. -/
@[simp] theorem fiberTranslate_difference (x y : FiberPoints f p) :
    fiberTranslate f p x (fiberDifference f p x y) = y := by
  apply Subtype.ext
  exact mul_inv_cancel_left x.val y.val

/-- The difference recovers the unique translating kernel point. -/
@[simp] theorem fiberDifference_translate (x : FiberPoints f p)
    (k : (quotientPointHom (C := C) f).ker) :
    fiberDifference f p x (fiberTranslate f p x k) = k := by
  apply Subtype.ext
  exact inv_mul_cancel_left x.val k.val

/-- The torsor comparison on points, constructed with the difference inverse. -/
def fiberPointComparison :
    FiberPoints f p × (quotientPointHom (C := C) f).ker ≃
      FiberPoints f p × FiberPoints f p where
  toFun x := (x.1, fiberTranslate f p x.1 x.2)
  invFun x := (x.1, fiberDifference f p x.1 x.2)
  left_inv x := by simp
  right_inv x := by simp

end HopfAlgebra
