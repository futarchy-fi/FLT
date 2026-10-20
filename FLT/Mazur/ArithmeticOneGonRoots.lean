/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonTorus
public import FLT.Mazur.ArithmeticOneGonSubgroupAmple
public import FLT.Mazur.TorusArithmeticCyclicity
public import FLT.Mazur.GeneralizedCurveAmpleBaseChange

/-!
# Ample cyclic arithmetic boundary subgroups of every positive order

The original zero-parameter arithmetic cubic carries the actual roots-of-unity
subgroup. Its full ideal is Cartier and ample, and its cyclicity uses the
cyclotomic fppf cover even where the order is not invertible.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.ArithmeticOneGonRoots

open ArithmeticOneGonTorus GeneralizedEllipticCurve

variable (R : Type) [CommRing R] (n : ℕ) [NeZero n]

/-- The original roots-of-unity carrier inside the arithmetic boundary curve. -/
def subgroup : (boundaryCurve R).FiniteSubgroup n :=
  (boundaryCurve R).torusRootsOfUnitySubgroup (torusIso R) n

/-- The inclusion retains the original roots and the corrected torus coordinate. -/
theorem subgroup_inclusion :
    (subgroup R n).inclusion = RootsOfUnityScheme.inclusion R n ≫ (torusIso R).hom := rfl

/-- Its whole-curve map retains the actual arithmetic smooth-open embedding. -/
theorem subgroup_curveMap :
    (subgroup R n).curveMap =
      RootsOfUnityScheme.inclusion R n ≫ (torusIso R).hom ≫ (boundaryCurve R).inclusion :=
  (boundaryCurve R).torusRootsOfUnitySubgroup_curveMap (torusIso R) n

/-- Its full ideal, including infinitesimal multiplicities, is relative Cartier. -/
theorem subgroup_relativeCartier :
    FCurve.RelativeEffectiveCartier (boundaryCurve R).curve.hom (subgroup R n).ideal :=
  (boundaryCurve R).torusRootsOfUnitySubgroup_relativeCartier (torusIso R) n

/-- The divisor is ample over the original arithmetic base. -/
theorem subgroup_isAmple : (subgroup R n).IsAmple :=
  ArithmeticOneGonSubgroupAmple.isAmple (0 : R) (by simp) (subgroup R n)
    (NeZero.pos n) (subgroup_relativeCartier R n).1

/-- The full subgroup is Cartier-cyclic over the original arithmetic base. -/
theorem subgroup_isCyclic : (subgroup R n).IsCyclic :=
  (boundaryCurve R).torusRootsOfUnitySubgroup_isCyclic (torusIso R) n

variable {T : Scheme} (g : T ⟶ Spec (.of R))

/-- Every scheme test retains the full original subgroup ideal. -/
theorem subgroup_baseChange_ideal :
    ((subgroup R n).baseChange g).ideal =
      (subgroup R n).ideal.comap (pullback.fst (boundaryCurve R).curve.hom g) :=
  (subgroup R n).baseChange_ideal g

/-- The full pulled-back divisor is ample, including on nonreduced arithmetic tests. -/
theorem subgroup_baseChange_isAmple : ((subgroup R n).baseChange g).IsAmple :=
  (subgroup_isAmple R n).baseChange g

/-- The original subgroup remains cyclic after any scheme test. -/
theorem subgroup_baseChange_isCyclic : ((subgroup R n).baseChange g).IsCyclic :=
  (subgroup_isCyclic R n).baseChange _ g

end FLT.Mazur.ArithmeticOneGonRoots
