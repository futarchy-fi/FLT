/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.DiscreteOrderExact
public import FLT.LocalClassFieldTheory.UnramifiedUniformizer

/-!
# Compatibility of order in unramified towers

The same base uniformizer has order one in both extensions. Consequently,
embedding fraction-field units in a larger unramified stage preserves order.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

variable (R S T L E : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Field L] [Field E] [Algebra S L] [IsFractionRing S L]
  [Algebra T E] [IsFractionRing T E] [Algebra R S] [Algebra R T]
  [Algebra S T] [Algebra L E] [Algebra S E] [Algebra R E]
  [IsScalarTower R S E] [IsScalarTower R T E]
  [IsScalarTower S L E] [IsScalarTower S T E]
  [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R T)]
  [Module.Finite R S] [Module.Finite R T]
  [Algebra.FormallyUnramified R S] [Algebra.FormallyUnramified R T]

include R in
/-- The classical order is unchanged by embedding into a larger unramified stage. -/
theorem discreteOrder_unramified_tower (x : Lˣ) :
    discreteOrder T E (Units.map (algebraMap L E).toMonoidHom x) = discreteOrder S L x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hs := unramified_uniformizer_irreducible R S hπ
  have ht := unramified_uniformizer_irreducible R T hπ
  have hπmap : Units.map (algebraMap L E).toMonoidHom (fractionUniformizer S L hs) =
      fractionUniformizer T E ht := by
    apply Units.ext
    change algebraMap L E (algebraMap S L (algebraMap R S π)) =
      algebraMap T E (algebraMap R T π)
    simp only [← IsScalarTower.algebraMap_apply]
  obtain ⟨u, n, rfl⟩ := exists_unit_mul_fractionUniformizer_zpow S L hs x
  have hu : Units.map (algebraMap L E).toMonoidHom (Units.map (algebraMap S L).toMonoidHom u) =
      Units.map (algebraMap T E).toMonoidHom (Units.map (algebraMap S T).toMonoidHom u) := by
    apply Units.ext
    change algebraMap L E (algebraMap S L (u : S)) =
      algebraMap T E (algebraMap S T (u : S))
    simp only [← IsScalarTower.algebraMap_apply]
  rw [map_mul, map_zpow, hπmap]
  calc
    _ = discreteOrder T E (Units.map (algebraMap T E).toMonoidHom
        (Units.map (algebraMap S T).toMonoidHom u) * fractionUniformizer T E ht ^ n) :=
      congrArg (fun w : Eˣ => discreteOrder T E (w * fractionUniformizer T E ht ^ n)) hu
    _ = _ := by
      rw [map_mul, map_mul, map_zpow, map_zpow]
      exact congrArg₂ (· * ·)
        ((discreteOrder_unit T E (Units.map (algebraMap S T).toMonoidHom u)).trans
          (discreteOrder_unit S L u).symm)
        (congrArg (fun a => a ^ n) ((discreteOrder_fractionUniformizer T E ht).trans
          (discreteOrder_fractionUniformizer S L hs).symm))

end LocalClassFieldTheory
