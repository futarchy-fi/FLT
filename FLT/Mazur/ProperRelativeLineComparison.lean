/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierRetainedLineBaseChange

/-!
# Comparing relative retained lines before inspecting their geometric witnesses

The relation between pulled and transported line records is equivalent to an
isomorphism preserving the original direct-image maps. This interface leaves
the actual relative sections abstract throughout the record conversion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange DualAtlasLineQuotient
attribute [local irreducible] twistedSectionPushforwardEquiv ModuleSheafTensor.tensor
variable {X S Y T : Scheme.{0}} (f : X ⟶ S) (q : Y ⟶ T) (g : T ⟶ S)
  (L : X.Modules) (N : Y.Modules)
  [IsAffine S] [IsAffine T] [IsNoetherianRing Γ(S, ⊤)] [IsNoetherianRing Γ(T, ⊤)]
  [IsProper f] [Flat f] [Surjective f] [IsProper q] [Flat q] [Surjective q]
  (hL : LocallyFreeRankOne L) (hN : LocallyFreeRankOne N)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
  (hW : ∀ (z : PrimeSpectrum Γ(T, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine q N z) (n + 1)))

/-- The retained-line relation can be checked entirely on the original twisted sections. -/
lemma relativeLine_baseChange_relation_iff
    (s : RelativeSection f L hL) (t : RelativeSection q N hN)
    (e : (pullback g).obj ((pushforward f).obj L) ≅ (pushforward q).obj N) :
    (lineSetoid ((pushforward q).obj N)).r
      ((((s.toSplitDirectImage f L hL hV).toLine f L).baseChange g).changeAmbient e)
      ((t.toSplitDirectImage q N hN hW).toLine q N) ↔
    ∃ d : (pullback g).obj (moduleSheafDual s.val.baseLine.val) ≅
        moduleSheafDual t.val.baseLine.val,
      d.hom ≫ (t.val.toDirectImage q N).map =
        (pullback g).map (s.val.toDirectImage f L).map ≫ e.hom := Iff.rfl

end FLT.Mazur.CartierAbel
