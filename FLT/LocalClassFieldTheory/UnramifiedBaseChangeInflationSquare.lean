/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedKernelInflation
public import FLT.LocalClassFieldTheory.UnramifiedBaseChangeCohomology

/-!
# Base change and inflation commute with relative restriction

Both routes evaluate the same field-unit cochain on the same overfield
automorphisms. The comparison uses the actual restriction kernel, so its
vanishing can be used by continuous inflation-restriction exactness.
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
  (E : IntermediateField K C) [IsGalois K E]
  [Algebra S E] [IsFractionRing S E] [Algebra S C] [IsScalarTower S E C]
  [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S E C
local notation "N" => (MonoidHom.ker (AlgEquiv.restrictNormalHom E : Gal(C/K) →* Gal(E/K)))

attribute [local instance] unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

local instance relativeBaseTower : IsScalarTower R E C :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The actual group restriction square commutes on the relative kernel. -/
theorem unramifiedBaseChange_kernel_square (g : N) :
    unramifiedBaseChangeRestriction R S K E C (unramifiedKernelRestriction S K C E g) =
      unramifiedRestriction R K C g.val := by
  ext x
  calc
    _ = (unramifiedKernelRestriction S K C E g
        (maximalUnramifiedBaseChange R S K E C x) : C) :=
      congrArg Subtype.val (unramifiedBaseChangeRestriction_apply R S K E C
        (unramifiedKernelRestriction S K C E g) x)
    _ = g.val (x : C) := unramifiedKernelRestriction_apply S K C E g _
    _ = _ := (AlgEquiv.restrictNormal_apply A g.val x).symm

/-- Base change then kernel inflation equals absolute inflation then kernel restriction. -/
theorem unramifiedBaseChangeInflation_cochains :
    continuousRestriction (unramifiedBaseChangeRestriction R S K E C)
        (unramifiedBaseChangeRestriction_continuous R S K E C)
        (unramifiedBaseChangeCoefficients R S K E C) ≫
      continuousRestriction (unramifiedKernelRestriction S K C E)
        (unramifiedKernelRestriction_continuous S K C E)
        (unramifiedKernelInflationCoefficients S K C E) =
    continuousRestriction (unramifiedRestriction R K C)
        (unramifiedRestriction_continuous R K C)
        (unramifiedMultiplicativeInflationCoefficients R K C) ≫
      continuousRestriction (N).subtype continuous_subtype_val
        (galoisKernelRestrictionCoefficients K C E) := by
  ext n c : 3
  apply Subtype.ext
  funext g
  change Additive.ofMul (Units.map (A).val.toMonoidHom
      (c.val (fun i => unramifiedBaseChangeRestriction R S K E C
        (unramifiedKernelRestriction S K C E (g i)))).toMul) =
    Additive.ofMul (Units.map (A).val.toMonoidHom
      (c.val (fun i => unramifiedRestriction R K C (g i).val)).toMul)
  congr 4
  apply congrArg c.val
  funext i
  exact unramifiedBaseChange_kernel_square R S K C E (g i)

/-- The comparison on actual continuous multiplicative cohomology, in every degree. -/
theorem unramifiedBaseChangeInflation_cohomology (n : ℕ) :
    unramifiedBaseChangeCohomology R S K E C n ≫ unramifiedKernelInflation S K C E n =
      unramifiedMultiplicativeInflation R K C n ≫ galoisKernelRestriction K C E n := by
  unfold unramifiedBaseChangeCohomology unramifiedKernelInflation
    unramifiedMultiplicativeInflation galoisKernelRestriction
  rw [← homologyMap_comp, ← homologyMap_comp, unramifiedBaseChangeInflation_cochains]

end LocalClassFieldTheory
