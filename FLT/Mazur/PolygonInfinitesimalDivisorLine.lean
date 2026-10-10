/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealPullbackComparison
public import FLT.Mazur.PolygonInfinitesimalDivisor

/-!
# The actual positive marking line and coefficient pullback

Dualizing the actual Cartier ideal gives a locally free rank-one sheaf. The
canonical ideal pullback, rather than a chosen trivialization, identifies these
lines under coefficient change.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.PolygonInfinitesimal

open FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type u) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n)

/-- The positive divisor line of the actual marked Cartier sum. -/
def markingLine (a : Fin n → Rˣ) : (scheme R t n h).Modules :=
  divisorLineBundle (markingDivisor R t n h a) (markingDivisor_cartier R t n h a).1

/-- The marking divisor gives an actual line bundle over every coefficient ring. -/
theorem markingLine_rankOne (a : Fin n → Rˣ) : LocallyFreeRankOne (markingLine R t n h a) :=
  (markingDivisor_cartier R t n h a).1.divisorLineBundle_locallyFreeRankOne

variable {R} {S : Type u} [CommRing S] (φ : R →+* S) (s : S)
  [Fact (IsNilpotent s)] (ht : φ t = s)

/-- The actual ideal pullback is invertible, even for nonflat coefficient change. -/
instance markingIdealPullback_isIso (a : Fin n → Rˣ) :
    IsIso (idealModulePullbackHom (markingDivisor R t n h a)
      (parameterProjection φ t s ht n h)) := by
  apply idealModulePullbackHom_isIso_of_cartier _ (markingDivisor_cartier R t n h a).1
  rw [markingDivisor_parameterProjection]
  exact (markingDivisor_cartier S s n h _).1

/-- The coefficient comparison retains the positive divisor line itself. -/
def markingLineParameterIso (a : Fin n → Rˣ) :
    (pullback (parameterProjection φ t s ht n h)).obj (markingLine R t n h a) ≅
      markingLine S s n h (fun i ↦ Units.map φ (a i)) :=
  divisorLinePullbackIsoOfEq _ (markingDivisor_cartier R t n h a).1
    (markingDivisor_cartier S s n h _).1 (markingDivisor_parameterProjection t n h φ s ht a)

end FLT.Mazur.PolygonInfinitesimal
