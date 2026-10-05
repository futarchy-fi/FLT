/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProperPointExtension
public import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-!
# Spreading a proper point extension to a neighborhood

At a valuation stalk of an integral scheme, properness extends a function-field
point to the stalk. Finite type then spreads this lift to an open neighborhood.
The resulting partial map has the original function-field value and lies over
the base. This is the local input to gluing, not an assumed global extension.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur

variable {S : Scheme.{u}} [IsIntegral S]

/-- Restricting a partial map from a stalk to the generic point agrees with its
function-field value. -/
theorem partialMap_fromFunctionField_eq {Y : Scheme.{u}} (f : S.PartialMap Y)
    {s : S} (hs : s ∈ f.domain) :
    f.fromFunctionField =
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) S.functionField)) ≫
        f.fromSpecStalkOfMem hs := by
  unfold Scheme.PartialMap.fromFunctionField Scheme.PartialMap.fromSpecStalkOfMem
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono f.domain.ι).mp
  simp only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes s)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A generic point of a proper scheme spreads across any valuation stalk. -/
theorem exists_partialMap_at_valuation_stalk (X : Over S) [IsProper X.hom]
    (x : Points X (S.fromSpecStalk (genericPoint S))) (s : S)
    [ValuationRing (S.presheaf.stalk s)] :
    ∃ f : S.PartialMap X.left, s ∈ f.domain ∧
      f.hom ≫ X.hom = f.domain.ι ∧ f.fromFunctionField = x.left := by
  let sq : ValuativeCommSq X.hom :=
    { R := S.presheaf.stalk s
      K := S.functionField
      i₁ := x.left
      i₂ := S.fromSpecStalk s
      commSq := ⟨by
        rw [Over.w x]
        exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk
          (genericPoint_specializes s)).symm⟩ }
  have hc : ValuativeCriterion X.hom := by
    have hp : IsProper X.hom := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  obtain ⟨l, hl, hs⟩ := (hc.existence sq).exists_lift
  have hs' : l ≫ X.hom = S.fromSpecStalk s ≫ 𝟙 S := by simpa using hs
  let f := Scheme.PartialMap.ofFromSpecStalk (𝟙 S) X.hom l hs'
  have hmem : s ∈ f.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
  refine ⟨f, hmem, ?_, ?_⟩
  · simpa using Scheme.PartialMap.ofFromSpecStalk_comp (𝟙 S) X.hom l hs'
  · rw [partialMap_fromFunctionField_eq f hmem]
    change _ ≫ (Scheme.PartialMap.ofFromSpecStalk _ _ _ _).fromSpecStalkOfMem _ = _
    rw [Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
    exact hl

end FLT.Mazur
