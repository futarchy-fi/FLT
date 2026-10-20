/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonTorusBaseChange
public import FLT.Mazur.ArithmeticOneGonOriginalRoots
public import FLT.Mazur.TorusRootsOfUnityBaseChange

/-!
# Actual arithmetic boundary roots on every coefficient test

The original roots-of-unity subgroup pulls back to the subgroup in the proved
fiber torus coordinate. Its full ideal and ample cyclic moduli class agree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.ArithmeticOneGonRootsBaseChange

open ArithmeticOneGonTorus CharacterSchemeBaseChange GeneralizedEllipticCurve
open GeneralizedEllipticCurve.FiniteSubgroup

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) [NeZero n]
local notation "q" => baseMap R A
local notation "F" => GeneralizedEllipticCurve.baseChange (boundaryCurve R) q
local notation "e" => ArithmeticOneGonFiberTorus.torusIso A (0 : R) (map_zero _)

/-- The root subgroup in the actual arithmetic fiber torus coordinate. -/
def subgroup : (F).FiniteSubgroup n := (F).torusRootsOfUnitySubgroup (e) n

/-- The character comparison identifies it with the actual original subgroup pullback. -/
def compatibleIso : CompatibleIso (subgroup R A n)
    ((ArithmeticOneGonRoots.subgroup R n).baseChange q) :=
  torusRootsOfUnityBaseChangeCompatibleIso (boundaryCurve R) (torusIso R) (e)
    (ArithmeticOneGonTorusBaseChange.torus_comparison R A) n

/-- The carrier is the original roots-of-unity scheme over the test ring. -/
theorem subgroup_carrier : (subgroup R A n).carrier = RootsOfUnityScheme.model A n := rfl

/-- The inclusion retains the actual tested torus coordinate. -/
theorem subgroup_inclusion :
    (subgroup R A n).inclusion = RootsOfUnityScheme.inclusion A n ≫ (e).hom := rfl

/-- The full subgroup ideal is the actual comap of the original arithmetic ideal. -/
theorem subgroup_ideal :
    (subgroup R A n).ideal = (ArithmeticOneGonRoots.subgroup R n).ideal.comap
      (pullback.fst (boundaryCurve R).curve.hom q) := by
  exact (torusRootsOfUnity_baseChange_ideal_eq (boundaryCurve R) (torusIso R) (e)
    (ArithmeticOneGonTorusBaseChange.torus_comparison R A) n).trans
      ((ArithmeticOneGonRoots.subgroup R n).baseChange_ideal q)

/-- Cartier cyclicity persists on the entire coefficient test. -/
theorem subgroup_isCyclic : (subgroup R A n).IsCyclic :=
  (compatibleIso R A n).isCyclic_iff.mpr
    (ArithmeticOneGonRoots.subgroup_baseChange_isCyclic R n q)

/-- The entire tested root divisor is ample. -/
theorem subgroup_isAmple : (subgroup R A n).IsAmple :=
  (compatibleIso R A n).isAmple_iff.mpr
    (ArithmeticOneGonRoots.subgroup_baseChange_isAmple R n q)

/-- The tested divisor remains relative Cartier, even for nonreduced coefficient rings. -/
theorem subgroup_relativeCartier :
    FCurve.RelativeEffectiveCartier (F).curve.hom (subgroup R A n).ideal :=
  (F).torusRootsOfUnitySubgroup_relativeCartier (e) n

/-- The actual tested boundary level with both proved moduli conditions. -/
def level : ampleCyclicLevels (Spec (.of A)) n :=
  ⟨⟨F, subgroup R A n⟩, subgroup_isCyclic R A n, subgroup_isAmple R A n⟩

/-- Its class is the presheaf pullback of the original arithmetic boundary class. -/
theorem level_class :
    (Quotient.mk _ (level R A n) : ampleCyclicClasses (Spec (.of A)) n) =
      ampleCyclicClassesPullback q n
        (Quotient.mk _ (ArithmeticOneGonOriginalRoots.level n R)) :=
  Quotient.sound ⟨compatibleIso R A n⟩

end FLT.Mazur.ArithmeticOneGonRootsBaseChange
