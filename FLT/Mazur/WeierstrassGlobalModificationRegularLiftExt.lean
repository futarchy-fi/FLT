/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RegularCenterSeparatedLiftExt
public import FLT.Mazur.WeierstrassGlobalModificationOriginalOpen

/-!
# Uniqueness of global modification lifts with regular center

The actual contraction is separated and is unchanged on every original
center-generator open. Thus equality after contraction determines any two
lifts from an affine source with regular principal output center. Different
regular generators and different Rees presentations require no comparison
choices in the conclusion.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassGlobalModification

open WeierstrassIntegralChart WeierstrassModificationReesCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R B : Type u} [CommRing R] [IsDomain R] [IsBezout R] [CommRing B]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- Actual global lifts are determined by their contraction over a regular principal center. -/
theorem regular_center_lift_ext (φ : Coordinate W 2 →+* B) (d : B)
    (hI : (WeierstrassDilatation.modificationCenter W s).map φ = Ideal.span {d}) (hd : IsRegular d)
    (f g : Spec (.of B) ⟶ model W s b3 b4 b6 h3 h4 h6 hs)
    (hf : f ≫ contraction W s b3 b4 b6 h3 h4 h6 hs =
      Spec.map (CommRingCat.ofHom φ) ≫ integralCurveChart W 2)
    (hg : g ≫ contraction W s b3 b4 b6 h3 h4 h6 hs =
      Spec.map (CommRingCat.ofHom φ) ≫ integralCurveChart W 2) : f = g := by
  let _ := contraction_isProper W s b3 b4 b6 h3 h4 h6 hs
  exact RegularCenter.separated_lift_ext (WeierstrassDilatation.modificationCenter W s) φ d hI hd
    (centerGenerators W s) (centerGenerators_mem W s) (centerGenerators_span W s)
    (contraction W s b3 b4 b6 h3 h4 h6 hs) (integralCurveChart W 2)
    (fun i => originalOpen W s b3 b4 b6 h3 h4 h6 hs
      (centerGenerators W s i) (centerGenerators_mem W s i))
    (fun i => originalOpen_isPullback W s b3 b4 b6 h3 h4 h6 hs
      (centerGenerators W s i) (centerGenerators_mem W s i)) f g hf hg

end FLT.Mazur.WeierstrassGlobalModification
