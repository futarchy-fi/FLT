/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonOriginalFiber
public import FLT.Mazur.ArithmeticOneGonRoots
public import FLT.Mazur.OneGonAllOrderAmple
public import FLT.Mazur.AmpleCyclicClassPresheaf
public import FLT.Mazur.TorusRootsOfUnityTransport

/-!
# Arithmetic boundary levels retain the original roots-of-unity divisor

The full curve comparison is compatible with the identity on the original
roots-of-unity carrier. Consequently the entire ideal, including nonreduced
multiplicities, and the ample cyclic moduli class are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.ArithmeticOneGonOriginalRoots

open OneGonSmoothing ArithmeticOneGonTorus ArithmeticOneGonRoots
open ArithmeticOneGonOriginalFiber GeneralizedEllipticCurve.FiniteSubgroup

variable (K : Type) [Field K] (n : ℕ) [NeZero n]

attribute [local irreducible] ArithmeticOneGonOriginalFiber.curveIso

/-- The full curve comparison is the identity on the original root subgroup carrier. -/
def compatibleIso : CompatibleIso (originalRootsOfUnitySubgroup K n) (subgroup K n) :=
  GeneralizedEllipticCurve.torusRootsOfUnityCompatibleIso
    (rootsOfUnityTorusIso K) (torusIso K) (curveIso K) (by
      rw [curveIso_group]
      change (rootsOfUnityTorusIso K).hom ≫
        (rootsOfUnityTorusIso K).inv ≫ (torusIso K).hom = _
      rw [Iso.hom_inv_id_assoc]) n

/-- The original whole-curve ideal is retained, rather than only its point support. -/
theorem ideal :
    (subgroup K n).ideal = (originalRootsOfUnitySubgroup K n).ideal.comap
      (curveIso K).inv.curve.left :=
  ideal_transport _ _ (compatibleIso K n).curve (compatibleIso K n).subgroup
    (compatibleIso K n).compatible

/-- The arithmetic boundary object with its proved ample cyclic level. -/
def level (R : Type) [CommRing R] : ampleCyclicLevels (Spec (.of R)) n :=
  ⟨⟨boundaryCurve R, subgroup R n⟩, subgroup_isCyclic R n, subgroup_isAmple R n⟩

/-- The original pinched object with its proved ample cyclic level. -/
def originalLevel : ampleCyclicLevels (Spec (.of K)) n :=
  ⟨⟨_, originalRootsOfUnitySubgroup K n⟩,
    originalRootsOfUnitySubgroup_isCyclic K n, originalRootsOfUnitySubgroup_isAmple K n⟩

/-- The arithmetic boundary class is exactly the original pinched ample cyclic class. -/
theorem level_class :
    (Quotient.mk _ (level n K) : ampleCyclicClasses (Spec (.of K)) n) =
      Quotient.mk _ (originalLevel K n) :=
  Quotient.sound ⟨(compatibleIso K n).symm⟩

end FLT.Mazur.ArithmeticOneGonOriginalRoots
