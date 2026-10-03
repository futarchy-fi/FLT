/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSplitGroup
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# OverPullbackCoproduct

Universality of finite scheme coproducts identifies the coproduct of
base changes with the base change of the coproduct.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.OverPullbackCoproduct
variable {S T : Scheme.{u}} (g : T ⟶ S) {ι : Type} [Finite ι] (X : ι → Over S)

/-- Pulling back a finite coproduct of schemes over a base remains a coproduct. -/
def isColimit : IsColimit (Cofan.mk ((Over.pullback g).obj (∐ X))
    (fun i ↦ (Over.pullback g).map (Sigma.ι X i))) := by
  apply isColimitOfReflects (Over.forget T)
  let a : Cofan (fun i ↦ (X i).left) := Cofan.mk (∐ X).left fun i ↦ (Sigma.ι X i).left
  have ha : IsColimit a := isColimitOfHasCoproductOfPreservesColimit (Over.forget S) X
  refine (isColimitMapCoconeCofanMkEquiv (Over.forget T) _ _).symm ?_
  exact (IsUniversalColimit.nonempty_isColimit_of_isPullback_right
    (FinitaryPreExtensive.isUniversal_finiteCoproducts ha)
    (fun i ↦ (X i).hom) (∐ X).hom g
    (fun i ↦ pullback.fst (X i).hom g) (fun i ↦ pullback.snd (X i).hom g)
    (fun i ↦ IsPullback.of_hasPullback (X i).hom g)
    (IsPullback.of_hasPullback (∐ X).hom g)
    (Cofan.mk _ fun i ↦ ((Over.pullback g).map (Sigma.ι X i)).left) (Iso.refl _)
    (fun i ↦ (Sigma.ι X i).w)
    (by intro i; simp [Over.pullback, a])
    (by intro i; simp [Over.pullback])).some

/-- The finite-coproduct comparison for base change. -/
def equivalence : (∐ fun i ↦ (Over.pullback g).obj (X i)) ≅ (Over.pullback g).obj (∐ X) :=
  (coproductIsCoproduct _).coconePointUniqueUpToIso (isColimit g X)

@[reassoc (attr := simp)] theorem inclusion (i : ι) :
    Sigma.ι _ i ≫ (equivalence g X).hom = (Over.pullback g).map (Sigma.ι X i) :=
  (coproductIsCoproduct _).fac _ ⟨i⟩
end FLT.Mazur.OverPullbackCoproduct
