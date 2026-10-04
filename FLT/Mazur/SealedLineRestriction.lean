/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineEndpointTransport
public import Mathlib.Tactic.IrreducibleDef

/-!
# Sealed geometric line restrictions

Keep the adjunction and projection constructions behind an opaque boundary.
The defining theorem retains equality with the existing geometric restriction.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LinePullbackRestriction
open FCurve
/-- Geometric line restriction sealed against kernel unfolding of the adjunctions. -/
irreducible_def sealedAlong {X Y Z : Scheme.{u}}
    (s : X ⟶ Y) (p : Y ⟶ Z) (q : X ⟶ Z) (w : s ≫ p = q) (L : Z.Modules) :
    (pushforward p).obj ((Scheme.Modules.pullback p).obj L) ⟶
      (pushforward q).obj ((Scheme.Modules.pullback q).obj L) := along s p q w L
/-- Sealed line restrictions agree on a commuting square. -/
lemma sealedAlong_square {V W X Y Z : Scheme.{u}}
    (t : W ⟶ X) (s : X ⟶ Y) (g : W ⟶ V) (f : V ⟶ Y)
    (p : Y ⟶ Z) (q : X ⟶ Z) (r : V ⟶ Z) (u : W ⟶ Z)
    (w : s ≫ p = q) (v : t ≫ q = u) (w' : f ≫ p = r) (v' : g ≫ r = u)
    (hs : t ≫ s = g ≫ f) (L : Z.Modules) (hL : LocallyFreeRankOne L) :
    sealedAlong s p q w L ≫ sealedAlong t q u v L =
      sealedAlong f p r w' L ≫ sealedAlong g r u v' L := by
  simp only [sealedAlong_def]
  exact along_square t s g f p q r u w v w' v' hs L hL
/-- On global sections, the sealed restriction is the existing endpoint transport. -/
lemma sealedAlong_eq_transport {X Y Z : Scheme.{u}}
    (f : Y ⟶ Z) (g : X ⟶ Y) (q : X ⟶ Z) (w : g ≫ f = q)
    {L : Z.Modules} {M : Y.Modules} (e : (Scheme.Modules.pullback f).obj L ≅ M)
    (s : Γ((Scheme.Modules.pullback f).obj L, ⊤)) :
    (sealedAlong g f q w L).app ⊤ s =
      (LineEndpointTransport.iso f g q w e).hom.app ⊤
        (pullGlobal g M (e.hom.app ⊤ s)) := by
  rw [sealedAlong_def]
  exact LineEndpointTransport.along_eq_transport f g q w e s
end FLT.Mazur.LinePullbackRestriction
