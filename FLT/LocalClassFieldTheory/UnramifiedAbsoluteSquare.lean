/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedBaseChangeInflationSquare
public import FLT.LocalClassFieldTheory.AbsoluteRestriction

/-!
# Unramified inflation commutes with absolute restriction

Both routes act on cochains by the same field inclusions and Galois maps.
This identifies the arithmetic base-change square before applying invariants.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory HomologicalComplex

variable (R S K C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  (E : IntermediateField K C)
  [Algebra S E] [IsFractionRing S E] [Algebra S C] [IsScalarTower S E C]
  [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S E C

attribute [local instance] unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

attribute [local instance] relativeBaseTower

/-- The unramified group restriction square agrees with actual restriction of scalars. -/
theorem unramifiedBaseChange_absolute_square (g : Gal(C/E)) :
    unramifiedBaseChangeRestriction R S K E C (unramifiedRestriction S E C g) =
      unramifiedRestriction R K C (g.restrictScalars K) := by
  ext x
  calc
    _ = (unramifiedRestriction S E C g
        (maximalUnramifiedBaseChange R S K E C x) : C) :=
      congrArg Subtype.val (unramifiedBaseChangeRestriction_apply R S K E C
        (unramifiedRestriction S E C g) x)
    _ = g (x : C) := AlgEquiv.restrictNormal_apply B g _
    _ = _ := (AlgEquiv.restrictNormal_apply A (g.restrictScalars K) x).symm

/-- Actual unramified base change and absolute restriction commute on cochains. -/
theorem unramifiedAbsolute_cochains :
    continuousRestriction (unramifiedBaseChangeRestriction R S K E C)
        (unramifiedBaseChangeRestriction_continuous R S K E C)
        (unramifiedBaseChangeCoefficients R S K E C) ≫
      continuousRestriction (unramifiedRestriction S E C)
        (unramifiedRestriction_continuous S E C)
        (unramifiedMultiplicativeInflationCoefficients S E C) =
    continuousRestriction (unramifiedRestriction R K C)
        (unramifiedRestriction_continuous R K C)
        (unramifiedMultiplicativeInflationCoefficients R K C) ≫
      absoluteRestrictionComplex K C E := by
  ext n c : 3
  apply Subtype.ext
  funext g
  change Additive.ofMul (Units.map (A).val.toMonoidHom
    (c.val (fun i => unramifiedBaseChangeRestriction R S K E C
      (unramifiedRestriction S E C (g i)))).toMul) =
    Additive.ofMul (Units.map (A).val.toMonoidHom
      (c.val (fun i => unramifiedRestriction R K C ((g i).restrictScalars K))).toMul)
  congr 4
  apply congrArg c.val
  funext i
  exact unramifiedBaseChange_absolute_square R S K C E (g i)

/-- Actual unramified base change and absolute restriction commute on cohomology. -/
theorem unramifiedAbsolute_cohomology (n : ℕ) :
    unramifiedBaseChangeCohomology R S K E C n ≫ unramifiedMultiplicativeInflation S E C n =
      unramifiedMultiplicativeInflation R K C n ≫ absoluteRestriction K C E n := by
  unfold unramifiedBaseChangeCohomology unramifiedMultiplicativeInflation absoluteRestriction
  rw [← homologyMap_comp, ← homologyMap_comp, unramifiedAbsolute_cochains]

end LocalClassFieldTheory
