/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedBaseChange
public import FLT.LocalClassFieldTheory.UnramifiedUnionOrderExact

/-!
# Integral units under unramified base change

An element integral over the old base remains integral over the new base.
The constructed ring map preserves units and proves the kernel inclusion
for the two normalized union orders.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S K L C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [Field C] [Algebra L C] [Algebra K C] [Algebra R C] [Algebra S C]
  [IsScalarTower K L C] [IsScalarTower R K C] [IsScalarTower R L C]
  [IsScalarTower S L C] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [Algebra.IsSeparable L C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S L C

local instance baseChangeIntegralTower : IsScalarTower R K B :=
  IsScalarTower.of_algebraMap_eq fun r => Subtype.ext (IsScalarTower.algebraMap_apply R K C r)

local instance baseChangeIntegralTower' : IsScalarTower R S B :=
  IsScalarTower.of_algebraMap_eq fun r => Subtype.ext (IsScalarTower.algebraMap_apply R S C r)

/-- The inclusion of unions restricts to their integral closures. -/
def unramifiedBaseChangeIntegral : integralClosure R A →+* integralClosure S B where
  toFun x := ⟨maximalUnramifiedBaseChange R S K L C x,
    (x.property.map
      ((show A →ₐ[K] B from maximalUnramifiedBaseChange R S K L C).restrictScalars R)).tower_top⟩
  map_zero' := Subtype.ext (map_zero (maximalUnramifiedBaseChange R S K L C))
  map_one' := Subtype.ext (map_one (maximalUnramifiedBaseChange R S K L C))
  map_add' x y := Subtype.ext (map_add (maximalUnramifiedBaseChange R S K L C) x.val y.val)
  map_mul' x y := Subtype.ext (map_mul (maximalUnramifiedBaseChange R S K L C) x.val y.val)

/-- Integral-unit inclusion commutes with the field-unit base-change map. -/
theorem unramifiedBaseChangeIntegral_units (u : (integralClosure R A)ˣ) :
    Units.map (maximalUnramifiedBaseChange R S K L C).toMonoidHom
      (Units.map (algebraMap (integralClosure R A) A).toMonoidHom u) =
    Units.map (algebraMap (integralClosure S B) B).toMonoidHom
      (Units.map (unramifiedBaseChangeIntegral R S K L C).toMonoidHom u) := Units.ext rfl

/-- Base change preserves the kernel of normalized union order. -/
theorem unramifiedBaseChange_order_kernel (x : Aˣ) (hx : unramifiedUnionOrder R K C x = 1) :
    unramifiedUnionOrder S L C
      (Units.map (maximalUnramifiedBaseChange R S K L C).toMonoidHom x) = 1 := by
  obtain ⟨u, rfl⟩ := (unramifiedUnionOrder_eq_one_iff R K C x).mp hx
  rw [unramifiedBaseChangeIntegral_units]
  exact unramifiedUnionOrder_integralUnit S L C _

end LocalClassFieldTheory
