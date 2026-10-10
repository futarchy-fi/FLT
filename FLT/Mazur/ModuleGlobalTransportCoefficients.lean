/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackSectionTransport
public import FLT.Mazur.ModuleSectionTransportRestriction

/-!
# Global transport with explicit target section types

Sealing the global section map keeps concrete pushforward representations
out of subsequent kernel conversions. Local coefficients still pull back
by the original scheme morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace FLT.Mazur.FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
variable (a : (pullback f).obj M ⟶ N)

/-- Global transport as a function into the target module's own section type. -/
@[irreducible] def globalSectionTransport (s : Γ(M, ⊤)) : Γ(N, ⊤) :=
  (moduleSectionTransport f a).app ⊤ s

/-- A preserved section morphism gives a preserved actual global section. -/
theorem globalSectionTransport_section (c : structureModule Y ⟶ M)
    (d : structureModule X ⟶ N)
    (h : (pullback f).map c ≫ a = (modulePullbackUnitIso f).hom ≫ d) :
    globalSectionTransport f a (c.app ⊤ (1 : Γ(Y, ⊤))) = d.app ⊤ (1 : Γ(X, ⊤)) := by
  unfold globalSectionTransport
  exact moduleSectionTransport_section f a c d h

/-- Local multiples of a preserved global section transport by the actual section-ring map. -/
theorem globalSectionTransport_coefficient (c s : Γ(M, ⊤)) (d : Γ(N, ⊤))
    (hc : globalSectionTransport f a c = d)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) (r : Γ(Y, U))
    (hs : M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s =
      r • M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op c) :
    N.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (globalSectionTransport f a s) =
      f.appLE U V h r • N.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op d := by
  unfold globalSectionTransport at hc ⊢
  exact ModuleSectionTransportRestriction.local_coefficient f (moduleSectionTransport f a)
    c s d hc U V h r hs

end FLT.Mazur.FCurve
