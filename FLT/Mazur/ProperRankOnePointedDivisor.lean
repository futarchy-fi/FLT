/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperRankOneDivisorNaturality
public import FLT.Mazur.PointNormalizedDivisorFiber

/-!
# The canonical full divisor in the pointed normalized fiber

The constructed rank-one divisor gives a unique full relative Cartier ideal
with the prescribed normalized line class. The pointed equivalence also
supplies actual isomorphisms preserving the constructed point trivializations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange
open SchemePicard (pointNormalizedLinePointIso)
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
variable {P X T S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] [GeometricallyIntegral f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
  (hN : LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L)))
  (e : T ⟶ P) (he : e ≫ q = 𝟙 T)

/-- The canonical full relative divisor with the prescribed pointed normalized class. -/
def rankOnePointedDivisor :
    PointedRelativeFiber q e he ((pullback p).obj L) (hL.pullback p) :=
  relativePointedFiberEquiv q e he _ (hL.pullback p) (rankOneFamilyDivisor h L hL hV hN)

/-- Passing to the pointed fiber retains the full original normalized-section ideal. -/
lemma rankOnePointedDivisor_ideal :
    (rankOnePointedDivisor h L hL hV hN e he).val.val =
      (rankOneFamilyDivisor h L hL hV hN).val.val.val := rfl

/-- Every relative Cartier divisor with this pointed class is the constructed full divisor. -/
theorem rankOnePointedDivisor_unique
    (D : PointedRelativeFiber q e he ((pullback p).obj L) (hL.pullback p)) :
    D = rankOnePointedDivisor h L hL hV hN e he := by
  apply (relativePointedFiberEquiv q e he _ (hL.pullback p)).symm.injective
  exact rankOneFamilyDivisor_unique h L hL hV hN _

/-- The pointed normalized fiber is inhabited and unique on every rank-one test. -/
@[instance_reducible] def rankOnePointedFiberUnique :
    Unique (PointedRelativeFiber q e he ((pullback p).obj L) (hL.pullback p)) where
  default := rankOnePointedDivisor h L hL hV hN e he
  uniq := rankOnePointedDivisor_unique h L hL hV hN e he

/-- The point-normalized divisor line recovers the original point-normalized coefficient line. -/
theorem rankOnePointedDivisor_rigidifiedIso :
    Nonempty (LineSheafSectionRigidity.RigidifiedIso e
      (pointNormalizedLinePointIso q e
        (divisorLineBundle (rankOnePointedDivisor h L hL hV hN e he).val.val
          (rankOnePointedDivisor h L hL hV hN e he).val.property)
        (rankOnePointedDivisor h L hL hV hN e he).val.property.divisorLineBundle_locallyFreeRankOne
        he)
      (pointNormalizedLinePointIso q e ((pullback p).obj L) (hL.pullback p) he)) :=
  pointedRelativeFiber_rigidifiedIso q e he _ (hL.pullback p) _

variable {Q U : Scheme.{0}} {p' : Q ⟶ X} {q' : Q ⟶ U} {g' : U ⟶ S}
  (h' : IsPullback p' q' f g')
  (hN' : LocallyFreeRankOne ((pushforward q').obj ((pullback p').obj L)))
  (e' : U ⟶ Q) (he' : e' ≫ q' = 𝟙 U)
  (k : U ⟶ T) (r : Q ⟶ P)
  (hp : r ≫ p = p') (hq : r ≫ q = q' ≫ k) (hg : k ≫ g = g')

include hp hq hg in
/-- The pointed construction is natural as a full ideal on the actual original test families. -/
theorem rankOnePointedDivisor_natural_ideal :
    (rankOnePointedDivisor h' L hL hV hN' e' he').val.val =
      (rankOnePointedDivisor h L hL hV hN e he).val.val.comap r :=
  rankOneFamilyDivisor_natural_ideal h L hL hV hN h' hN' k r hp hq hg

end FLT.Mazur.CartierAbel
