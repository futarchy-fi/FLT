/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryCoprimeMarking
public import FLT.Mazur.AuxiliaryDistinctSectionParameter
public import FLT.Mazur.UniversalWeierstrassCyclicAuxiliary

/-!
# Full auxiliary and original cyclic labels over arbitrary bases

A complete auxiliary basis and an original universally distinct cyclic marking
produce an actual faithful product parameter when four and the cyclic order
are coprime. Both factors retain every original section exactly.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.AuxiliaryLevel
open UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [CommGrpObj E] [IsSeparated E.hom]
  {n : ℕ} [NeZero n] (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E))
  (hφ : UniversallyDistinctSections.UniversallyDistinct
    (fun i : ZMod n ↦ φ (Multiplicative.ofAdd i)))

/-- The original cyclic sections define their actual faithful cyclic parameter. -/
def cyclicDistinctParameter : 𝟙_ (Over S) ⟶ faithfulScheme E (Multiplicative (ZMod n)) :=
  distinctSectionParameter E _ φ (by
    intro V k hV a b hab
    exact congrArg Multiplicative.ofAdd (hφ V k hV hab))

/-- The cyclic parameter retains all original cyclic sections. -/
@[reassoc] theorem cyclicDistinctParameter_value (b : Multiplicative (ZMod n)) :
    cyclicDistinctParameter E φ hφ ≫ faithfulInclusion E (Multiplicative (ZMod n)) ≫
      value E (Multiplicative (ZMod n)) b = φ b :=
  distinctSectionParameter_value E _ φ _ b

variable (h : Nat.Coprime 4 n) (f : 𝟙_ (Over S) ⟶ faithfulScheme E (Labels 4))

/-- Combine the complete auxiliary basis with the exact original cyclic marking. -/
def auxiliaryCyclicParameter : 𝟙_ (Over S) ⟶ faithfulScheme E (CyclicLabels n) :=
  coprimeParameter E (Labels 4) (Multiplicative (ZMod n)) (labels_pow 4)
    (fun b ↦ congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero n b.toAdd))
    h f (cyclicDistinctParameter E φ hφ)

/-- Restricting the full parameter to the cyclic factor returns the original cyclic section. -/
@[reassoc] theorem auxiliaryCyclicParameter_cyclic (b : Multiplicative (ZMod n)) :
    auxiliaryCyclicParameter E φ hφ h f ≫ faithfulInclusion E (CyclicLabels n) ≫
      value E (CyclicLabels n) (1, b) = φ b := by
  rw [auxiliaryCyclicParameter, coprimeParameter_value, coprimeMarking_apply,
    map_one, _root_.one_mul]
  exact cyclicDistinctParameter_value E φ hφ b

/-- Restricting the full parameter to the auxiliary factor returns every original basis section. -/
@[reassoc] theorem auxiliaryCyclicParameter_auxiliary (a : Labels 4) :
    auxiliaryCyclicParameter E φ hφ h f ≫ faithfulInclusion E (CyclicLabels n) ≫
      value E (CyclicLabels n) (a, 1) =
        markingOf E (Labels 4) (f ≫ faithfulInclusion E (Labels 4)) a := by
  rw [auxiliaryCyclicParameter, coprimeParameter_value, coprimeMarking_apply,
    map_one, _root_.mul_one]

end FLT.Mazur.AuxiliaryLevel
