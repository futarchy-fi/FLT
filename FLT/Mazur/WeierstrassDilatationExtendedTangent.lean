/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationExtendedCast

/-!
# Bounded evaluation of the extended tangent comparison

Construct and seal the generic comparison before specializing its coefficients.
The seal retains a proved equality with the original coefficient transport.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R) (a : Sˣ)
  (hs : algebraMap R S s = 0) (h3 : algebraMap R S b3 = 0)
  (h4 : algebraMap R S b4 = 0)
  (h1 : (W.map (algebraMap R S)).a₁ = a)
  (h2 : (W.map (algebraMap R S)).a₂ = 0)
local notation "c" => algebraMap R S b6
local notation "W'" => W.map (algebraMap R S)

/-- The tangent normal form after the three coefficients vanish. -/
def extendedTangentEquiv : ExtendedCoordinate W s b3 b4 b6 S ≃ₐ[S]
    NodalFiber.Coordinate c :=
  extendedCoefficientCast W s b3 b4 b6 0 0 0 hs h3 h4
    (fiberTangentEquiv W' a c h1 h2)

/-- Seal the constructed map together with its proved equality. -/
opaque extendedTangentSeal :
    {e : ExtendedCoordinate W s b3 b4 b6 S ≃ₐ[S] NodalFiber.Coordinate c //
      e = extendedTangentEquiv W s b3 b4 b6 a hs h3 h4 h1 h2} :=
  ⟨extendedTangentEquiv W s b3 b4 b6 a hs h3 h4 h1 h2, rfl⟩

/-- The same comparison with a bounded definitional reduction boundary. -/
def extendedTangentSealedEquiv : ExtendedCoordinate W s b3 b4 b6 S ≃ₐ[S]
    NodalFiber.Coordinate c :=
  (extendedTangentSeal W s b3 b4 b6 a hs h3 h4 h1 h2).val

/-- Sealing preserves the constructed comparison exactly. -/
theorem extendedTangentSealedEquiv_def :
    extendedTangentSealedEquiv W s b3 b4 b6 a hs h3 h4 h1 h2 =
      extendedTangentEquiv W s b3 b4 b6 a hs h3 h4 h1 h2 :=
  (extendedTangentSeal W s b3 b4 b6 a hs h3 h4 h1 h2).property

/-- The generic sealed comparison preserves the horizontal tangent difference. -/
theorem extendedTangentSealedEquiv_x :
    extendedTangentSealedEquiv W s b3 b4 b6 a hs h3 h4 h1 h2
      (x W' (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) c) =
      algebraMap S _ (↑a⁻¹ : S) * (NodalFiber.q c - NodalFiber.p c) := by
  rw [extendedTangentSealedEquiv_def, extendedTangentEquiv, extendedCoefficientCast_x]
  exact fiberToTangent_x W' a c h1 h2

/-- The generic sealed comparison preserves the vertical tangent factor. -/
theorem extendedTangentSealedEquiv_y :
    extendedTangentSealedEquiv W s b3 b4 b6 a hs h3 h4 h1 h2
      (y W' (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) c) =
      NodalFiber.p c := by
  rw [extendedTangentSealedEquiv_def, extendedTangentEquiv, extendedCoefficientCast_y]
  exact fiberToTangent_y W' a c h1 h2

end FLT.Mazur.WeierstrassDilatation
