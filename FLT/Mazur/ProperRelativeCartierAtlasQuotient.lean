/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperRelativeCartierAtlas

/-!
# Projective atlas representation of retained relative section orbits

The relation uses actual isomorphisms of the dual base lines preserving their
direct-image maps. The affine Noetherian proper-family criterion identifies
these relative Cartier section orbits with sections of the constructed atlas.
This does not identify the coarser total-space section relation in the Abel fiber.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve DualAtlasLineQuotient
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)
  [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsProper f] [Flat f]
  [GeometricallyIntegral f] [Surjective f] (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (LineSectionBaseChange.residueAlgebraFiberLine f L z) (n + 1)))

/-- Actual dual base-line isomorphisms preserving the original direct-image maps. -/
def relativeBaseLineSetoid : Setoid (RelativeSection f L hL) :=
  (lineSetoid ((pushforward f).obj L)).comap
    (fun s ↦ (s.toSplitDirectImage f L hL hV).toLine f L)

omit [GeometricallyIntegral f] in
/-- The orbit relation retains an actual isomorphism of the dual base lines. -/
lemma relativeBaseLineSetoid_iff (s t : RelativeSection f L hL) :
    (relativeBaseLineSetoid f L hL hV).r s t ↔
      ∃ e : moduleSheafDual s.val.baseLine.val ≅ moduleSheafDual t.val.baseLine.val,
        e.hom ≫ (t.val.toDirectImage f L).map = (s.val.toDirectImage f L).map := Iff.rfl

omit [GeometricallyIntegral f] in
/-- The geometric atlas detects exactly the retained base-line orbit relation. -/
lemma relativeSection_toAtlas_eq_iff (s t : RelativeSection f L hL) :
    s.toAtlas f L hL hV = t.toAtlas f L hL hV ↔
      (relativeBaseLineSetoid f L hL hV).r s t :=
  toSection_eq_iff _ _ _ _

/-- The actual geometric atlas map on retained relative section orbits. -/
def relativeBaseLineQuotientToAtlas :
    Quotient (relativeBaseLineSetoid f L hL hV) → DirectImageAtlasSection f L hL hV :=
  Quotient.lift (RelativeSection.toAtlas f L hL hV)
    (fun s t h ↦ (relativeSection_toAtlas_eq_iff f L hL hV s t).mpr h)

/-- Actual atlas sections represent relative Cartier sections modulo retained base-line orbits. -/
def relativeBaseLineAtlasEquiv :
    Quotient (relativeBaseLineSetoid f L hL hV) ≃ DirectImageAtlasSection f L hL hV where
  toFun := relativeBaseLineQuotientToAtlas f L hL hV
  invFun p := Quotient.mk _ (relativeSectionOfAtlas f L hL hV p)
  left_inv q := by
    induction q using Quotient.inductionOn with | h s =>
      exact Quotient.sound ((relativeSection_toAtlas_eq_iff f L hL hV _ _).mp
        (toAtlas_relativeSectionOfAtlas f L hL hV (s.toAtlas f L hL hV)))
  right_inv := toAtlas_relativeSectionOfAtlas f L hL hV

/-- The equivalence evaluates on each original relative section by its actual atlas morphism. -/
lemma relativeBaseLineAtlasEquiv_mk (s : RelativeSection f L hL) :
    relativeBaseLineAtlasEquiv f L hL hV (Quotient.mk _ s) = s.toAtlas f L hL hV := rfl

end FLT.Mazur.CartierAbel
