/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperAtlasSectionBaseChange
public import FLT.Mazur.ProperRelativeLineComparison

/-!
# Naturality of the actual atlas and relative Abel-fiber equivalence

Pull back the geometric atlas section using its cartesian square, then
transport along the independently constructed proper direct-image comparison.
The result agrees with the original Cartier section pullback, including
its full zero ideal. Both affine bases retain their stated acyclicity data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange DualAtlasLineQuotient
attribute [local irreducible] RelativeSection.toSplitDirectImage
  SplitDirectImageSection.toLine relativeSectionBaseChange
attribute [local irreducible] twistedSectionPushforwardEquiv moduleSheafDualPullbackIso
  properLinePushforwardBaseChangeIso
  LocallySplitLineAtlasSection.morphism sectionChangeAmbient
  DualAtlasLineQuotient.sectionBaseChange toSection
variable {X S T : Scheme.{0}} (f : X ⟶ S) (g : T ⟶ S) (L : X.Modules)
  [IsAffine S] [IsAffine T] [IsNoetherianRing Γ(S, ⊤)] [IsNoetherianRing Γ(T, ⊤)]
  [IsProper f] [Flat f] [Surjective f] [GeometricallyIntegral f]
  (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
  (hW : ∀ (z : PrimeSpectrum Γ(T, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine (Limits.pullback.snd f g)
      ((pullback (Limits.pullback.fst f g)).obj L) z) (n + 1)))

omit [GeometricallyIntegral f] in
/-- Original and pulled Cartier maps give the same retained line after ambient transport. -/
lemma properAtlasBaseChange_lineRelation (s : RelativeSection f L hL) :
    (lineSetoid ((pushforward (Limits.pullback.snd f g)).obj
      ((pullback (Limits.pullback.fst f g)).obj L))).r
      ((((s.toSplitDirectImage f L hL hV).toLine f L).baseChange g).changeAmbient
        (properLinePushforwardBaseChangeIso (IsPullback.of_hasPullback f g) L hL hV))
      (((relativeSectionBaseChange f g L hL s).toSplitDirectImage
        (Limits.pullback.snd f g) _ (hL.pullback (Limits.pullback.fst f g)) hW).toLine _ _) := by
  rw [relativeLine_baseChange_relation_iff, relativeSectionBaseChange_val]
  exact ⟨moduleSheafDualPullbackIso g s.val.baseLine.property,
    properAtlasBaseChange_inclusion f g L hL hV s⟩

omit [GeometricallyIntegral f] in
/-- Actual atlas base change carries every original Cartier section to its pulled section. -/
lemma properAtlasBaseChange_toAtlas (s : RelativeSection f L hL) :
    properAtlasBaseChange f g L hL hV hW (s.toAtlas f L hL hV) =
      (relativeSectionBaseChange f g L hL s).toAtlas (Limits.pullback.snd f g) _
        (hL.pullback (Limits.pullback.fst f g)) hW :=
  (properAtlasBaseChange_toSection f g L hL hV hW _).trans
    ((toSection_eq_iff _ _ _ _).mpr (properAtlasBaseChange_lineRelation f g L hL hV hW s))

/-- The actual geometric atlas map commutes with pullback of full relative Cartier divisors. -/
theorem atlasToRelativeFiber_baseChange (p : DirectImageAtlasSection f L hL hV) :
    atlasToRelativeFiber (Limits.pullback.snd f g) _
        (hL.pullback (Limits.pullback.fst f g)) hW (properAtlasBaseChange f g L hL hV hW p) =
      fiberBaseChange f g L hL (atlasToRelativeFiber f L hL hV p) := by
  obtain ⟨s, rfl⟩ := relativeSection_toAtlas_surjective f L hL hV p
  rw [properAtlasBaseChange_toAtlas, atlasToRelativeFiber_toAtlas, atlasToRelativeFiber_toAtlas]
  exact relativeSectionToFiber_baseChange f g L hL s

/-- The atlas-to-fiber equivalence is natural for the independently constructed geometric map. -/
theorem atlasRelativeFiberEquiv_baseChange (p : DirectImageAtlasSection f L hL hV) :
    atlasRelativeFiberEquiv (Limits.pullback.snd f g) _
        (hL.pullback (Limits.pullback.fst f g)) hW (properAtlasBaseChange f g L hL hV hW p) =
      fiberBaseChange f g L hL (atlasRelativeFiberEquiv f L hL hV p) :=
  atlasToRelativeFiber_baseChange f g L hL hV hW p

end FLT.Mazur.CartierAbel
