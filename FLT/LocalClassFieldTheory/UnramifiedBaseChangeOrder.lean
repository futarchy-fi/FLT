/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.OrderHomScale
public import FLT.LocalClassFieldTheory.RamifiedOrderScale
public import FLT.LocalClassFieldTheory.UnramifiedBaseChangeIntegral
public import FLT.LocalClassFieldTheory.UnramifiedUnionBaseOrder

/-!
# Ramified scaling on the maximal unramified unions

The inclusion preserves integral units. Its value on a base uniformizer
is the ramification index of the original local extension. These two
proved facts determine the scaling of the actual union order homomorphism.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

set_option backward.isDefEq.respectTransparency false

open IsLocalRing

variable (R S K L C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [Field C] [Algebra L C] [Algebra K C] [Algebra R C] [Algebra S C]
  [IsScalarTower K L C] [IsScalarTower R K C] [IsScalarTower R L C]
  [IsScalarTower S L C] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [Algebra.IsSeparable L C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S L C

/-- The order square for the constructed unramified base-change inclusion scales by ramification. -/
theorem unramifiedUnionOrder_baseChange (x : Aˣ) :
    unramifiedUnionOrder S L C
      (Units.map (maximalUnramifiedBaseChange R S K L C).toMonoidHom x) =
    unramifiedUnionOrder R K C x ^ (maximalIdeal R).ramificationIdx' (maximalIdeal S) := by
  let : Module.IsTorsionFree R S := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective R S)
  let : IsLocalHom (algebraMap R S) :=
    (algebraMap_isIntegral_iff.mpr inferInstance).isLocalHom (FaithfulSMul.algebraMap_injective R S)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let f := (unramifiedUnionOrder S L C).comp
    (Units.map (maximalUnramifiedBaseChange R S K L C).toMonoidHom)
  have hπmap : Units.map (maximalUnramifiedBaseChange R S K L C).toMonoidHom
      (unramifiedUniformizerUnit R K C hπ) =
    Units.map (algebraMap L B).toMonoidHom
      (Units.map (algebraMap K L).toMonoidHom (fractionUniformizer R K hπ)) := by
    apply Units.ext
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply K L C (algebraMap R K π)
  have he : f (unramifiedUniformizerUnit R K C hπ) =
      Multiplicative.ofAdd ((maximalIdeal R).ramificationIdx' (maximalIdeal S) : ℤ) := by
    change unramifiedUnionOrder S L C (Units.map _ _) = _
    rw [hπmap, unramifiedUnionOrder_base S L C, discreteOrder_ramified_scale R S K L,
      discreteOrder_fractionUniformizer]
    apply Multiplicative.toAdd.injective
    simp
  exact orderHom_scale (unramifiedUnionOrder R K C) f (unramifiedUniformizerUnit R K C hπ)
    (unramifiedUnionOrder_uniformizer R K C hπ) _ he
    (unramifiedBaseChange_order_kernel R S K L C) x

end LocalClassFieldTheory
