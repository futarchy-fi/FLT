/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegralCyclotomicAffineCover
public import FLT.Mazur.RootsOfUnityArithmeticPullback
public import FLT.Mazur.CyclotomicSchemeOrbit

/-!
# The cyclotomic root on the actual pulled-back arithmetic subgroup

The explicit finite faithfully flat arithmetic cover carries a specified root
section of the actual subgroup pullback. Its original Laurent coordinate and
the full orbit ideal in the extended coordinates retain all multiplicities.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.CyclotomicCoverRootSection

open IntegralCyclotomicAffineCover

variable (R : Type) [CommRing R] (n : ℕ) [NeZero n]

/-- The original integral root in the affine arithmetic cover. -/
def rootUnit : (Algebra R n)ˣ :=
  Units.map (specialization R n).toMonoidHom (IntegralCyclotomicCoordinates.rootUnit n)

/-- The root relation holds on the entire cover, including its nonreduced fibers. -/
theorem rootUnit_pow : rootUnit R n ^ n = 1 := by
  apply Units.ext
  change specialization R n (IntegralCyclotomicCoordinates.root n) ^ n = 1
  rw [← map_pow, IntegralCyclotomicCoordinates.root_pow, map_one]

/-- The actual roots-of-unity pullback along the explicit fppf cover. -/
abbrev subgroup : Over (Spec (.of (Algebra R n))) :=
  (Over.pullback (CharacterSchemeBaseChange.baseMap R (Algebra R n))).obj
    (RootsOfUnityScheme.model R n)

/-- The cyclotomic coordinate gives a section of that actual subgroup pullback. -/
def rootSection : 𝟙_ (Over (Spec (.of (Algebra R n)))) ⟶ subgroup R n :=
  RootsOfUnityArithmeticPullback.rootSection R (Algebra R n) n
    (rootUnit R n) (rootUnit_pow R n)

/-- Its image in the original torus is the specified Laurent evaluation. -/
@[reassoc] theorem rootSection_laurent :
    (rootSection R n).left ≫ pullback.fst (RootsOfUnityScheme.model R n).hom
      (CharacterSchemeBaseChange.baseMap R (Algebra R n)) ≫
      (RootsOfUnityScheme.inclusion R n).left =
    Spec.map (CommRingCat.ofHom
      (LaurentUnitPoints.evalUnit (R := R) (rootUnit R n)).toRingHom) :=
  RootsOfUnityArithmeticPullback.rootSection_inclusion_fst R (Algebra R n) n
    (rootUnit R n) (rootUnit_pow R n)

/-- In the extended torus coordinates the full orbit is the subgroup ideal. -/
theorem orbitIdeal : RootsOfUnityCartier.ideal (Algebra R n) n =
    ∏ i : Fin n, ((ArithmeticTorusPoints.point (Algebra R n) (rootUnit R n)) ^ i.val).left.ker := by
  simp only [← ArithmeticTorusPoints.point_pow, ArithmeticTorusPoints.point_left]
  exact CyclotomicSchemeOrbit.ideal n (specialization R n)

end FLT.Mazur.CyclotomicCoverRootSection
