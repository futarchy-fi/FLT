/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationAlgebra

/-!
# Coordinate-preserving congruence of divided chart parameters

Equal parameters identify the actual divided algebras, retaining both
universal coordinates. This makes the arithmetic equality of successive
uniformizer powers usable without opaque transport of chart functions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s t b3 b4 b6 c3 c4 c6 : R)
  (hs : s = t) (h3 : b3 = c3) (h4 : b4 = c4) (h6 : b6 = c6)

/-- Equal parameters give the actual identity on divided chart coordinates. -/
def parameterEquiv : Coordinate W s b3 b4 b6 ≃ₐ[R] Coordinate W t c3 c4 c6 := by
  subst t c3 c4 c6
  exact AlgEquiv.refl

/-- Parameter congruence retains the first divided coordinate. -/
@[simp] theorem parameterEquiv_x :
    parameterEquiv W s t b3 b4 b6 c3 c4 c6 hs h3 h4 h6 (x W s b3 b4 b6) =
      x W t c3 c4 c6 := by
  subst t c3 c4 c6
  rfl

/-- Parameter congruence retains the second divided coordinate. -/
@[simp] theorem parameterEquiv_y :
    parameterEquiv W s t b3 b4 b6 c3 c4 c6 hs h3 h4 h6 (y W s b3 b4 b6) =
      y W t c3 c4 c6 := by
  subst t c3 c4 c6
  rfl

/-- The reverse congruence also retains the first divided coordinate. -/
@[simp] theorem parameterEquiv_symm_x :
    (parameterEquiv W s t b3 b4 b6 c3 c4 c6 hs h3 h4 h6).symm (x W t c3 c4 c6) =
      x W s b3 b4 b6 := by
  subst t c3 c4 c6
  rfl

/-- The reverse congruence also retains the second divided coordinate. -/
@[simp] theorem parameterEquiv_symm_y :
    (parameterEquiv W s t b3 b4 b6 c3 c4 c6 hs h3 h4 h6).symm (y W t c3 c4 c6) =
      y W s b3 b4 b6 := by
  subst t c3 c4 c6
  rfl

end FLT.Mazur.WeierstrassDilatation
