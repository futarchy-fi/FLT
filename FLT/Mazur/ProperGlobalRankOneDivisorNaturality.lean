/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperGlobalRankOneDivisor
public import FLT.Mazur.RelativeAbelFiberOriginalSquare

/-!
# Full-ideal naturality of varying canonical rank-one divisors

Actual maps of cartesian test families give Cartier pullback independently
of any parameter atlas. Uniqueness identifies this full ideal comap with the
canonical divisor on the new test, retaining its actual coefficient line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
variable {P X T S Q U : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  {p' : Q ⟶ X} {q' : Q ⟶ U} {g' : U ⟶ S}
  (h : IsPullback p q f g) (h' : IsPullback p' q' f g')
  (k : U ⟶ T) (r : Q ⟶ P)
  (hp : r ≫ p = p') (hq : r ≫ q = q' ≫ k) (hg : k ≫ g = g')

include h h' hp hq hg in
/-- The original maps of cartesian tests themselves form a cartesian square. -/
lemma originalFamilyMap_isPullback : IsPullback r q' q k := by
  have H : IsPullback (r ≫ p) q' f (k ≫ g) := by
    simpa only [hp, hg] using h'
  exact H.of_right hq h

/-- Geometric pullback of the actual relative fiber, retaining the original coefficient line. -/
def originalFamilyFiberPullback (L : X.Modules) (hL : LocallyFreeRankOne L)
    (D : RelativeFiber q ((pullback p).obj L) (hL.pullback p)) :
    RelativeFiber q' ((pullback p').obj L) (hL.pullback p') :=
  relativeFiberCoefficientEquiv q' ((hL.pullback p).pullback r) (hL.pullback p')
    ((pullbackComp r p).app L ≪≫ (pullbackCongr hp).app L)
      (relativeFiberOriginalPullback (originalFamilyMap_isPullback h h' k r hp hq hg)
        ((pullback p).obj L) (hL.pullback p) D)

/-- No quotient of the ideal is taken in geometric pullback of the original family fiber. -/
lemma originalFamilyFiberPullback_ideal (L : X.Modules) (hL : LocallyFreeRankOne L)
    (D : RelativeFiber q ((pullback p).obj L) (hL.pullback p)) :
    (originalFamilyFiberPullback h h' k r hp hq hg L hL D).val.val.val =
      D.val.val.val.comap r := rfl

variable [IsLocallyNoetherian S] [IsProper f] [Flat f] [GeometricallyIntegral f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ t : T, ∀ n, Subsingleton
    (ModuleH ((pullback (q.fiberι t)).obj ((pullback p).obj L)) (n + 1)))
  (hN : LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L)))
  (hV' : ∀ u : U, ∀ n, Subsingleton
    (ModuleH ((pullback (q'.fiberι u)).obj ((pullback p').obj L)) (n + 1)))
  (hN' : LocallyFreeRankOne ((pushforward q').obj ((pullback p').obj L)))

include hp hq hg in
/-- The canonical full divisor is natural along every original map of acyclic rank-one tests. -/
theorem acyclicRankOneFamilyDivisor_natural_ideal :
    (acyclicRankOneFamilyDivisor h' L hL hV' hN').val.val.val =
      (acyclicRankOneFamilyDivisor h L hL hV hN).val.val.val.comap r := by
  have he := acyclicRankOneFamilyDivisor_unique h' L hL hV' hN'
    (originalFamilyFiberPullback h h' k r hp hq hg L hL
      (acyclicRankOneFamilyDivisor h L hL hV hN))
  exact (congrArg (fun D : RelativeFiber q' ((pullback p').obj L) (hL.pullback p') ↦
    D.val.val.val) he).symm

end FLT.Mazur.CartierAbel
