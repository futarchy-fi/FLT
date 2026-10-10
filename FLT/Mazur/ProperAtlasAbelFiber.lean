/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperRelativeCartierBaseOrbits

/-!
# The actual direct-image projective atlas maps onto the relative Abel fiber

Retained base-line orbits preserve the full zero divisor, so the constructed
atlas equivalence supplies an actual surjection to the relative Cartier
Abel fiber. Injectivity requires descent of total-space line isomorphisms
and is not asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)
  [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsProper f] [Flat f]
  [Surjective f] (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (LineSectionBaseChange.residueAlgebraFiberLine f L z) (n + 1)))

/-- The original full zero divisor descends through retained base-line orbits. -/
def relativeBaseLineQuotientToFiber :
    Quotient (relativeBaseLineSetoid f L hL hV) → RelativeFiber f L hL :=
  Quotient.lift (relativeSectionToFiber f L hL)
    (relativeSectionToFiber_eq_of_baseLine f L hL hV)

/-- Every relative Abel divisor has a representative even with the finer base-line relation. -/
theorem relativeBaseLineQuotientToFiber_surjective :
    Function.Surjective (relativeBaseLineQuotientToFiber f L hL hV) := by
  intro D
  obtain ⟨q, hq⟩ := relativeQuotientToFiber_surjective f L hL D
  induction q using Quotient.inductionOn with | h s =>
    exact ⟨Quotient.mk _ s, hq⟩

variable [GeometricallyIntegral f]

/-- The relative Abel divisor of an actual section of the direct-image projective atlas. -/
def atlasToRelativeFiber : DirectImageAtlasSection f L hL hV → RelativeFiber f L hL :=
  relativeBaseLineQuotientToFiber f L hL hV ∘ (relativeBaseLineAtlasEquiv f L hL hV).symm

/-- The atlas map recovers the full original zero divisor of every original relative section. -/
lemma atlasToRelativeFiber_toAtlas (s : RelativeSection f L hL) :
    atlasToRelativeFiber f L hL hV (s.toAtlas f L hL hV) =
      relativeSectionToFiber f L hL s := by
  change relativeBaseLineQuotientToFiber f L hL hV
    ((relativeBaseLineAtlasEquiv f L hL hV).symm
      (relativeBaseLineAtlasEquiv f L hL hV (Quotient.mk _ s))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The constructed geometric atlas covers the entire actual relative Cartier Abel fiber. -/
theorem atlasToRelativeFiber_surjective : Function.Surjective (atlasToRelativeFiber f L hL hV) :=
  (relativeBaseLineQuotientToFiber_surjective f L hL hV).comp
    (relativeBaseLineAtlasEquiv f L hL hV).symm.surjective

end FLT.Mazur.CartierAbel
