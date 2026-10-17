/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomProperPresentationInvariant
public import FLT.Mazur.OddWeierstrassAuxiliaryAffineCubicIso

/-!
# Actual affine family comparisons preserve unrestricted cyclic normalization

The original family comparison supplies the proper presentation and all value
diagrams. The two markings stay independent; cyclic values may coincide.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme} [IsAffine T]
  (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (e : (auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f)).X ≅
    (auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g)).X)
  (ha : ∀ c : Labels 3, auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) c ≫ e.hom =
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) c)
  (hc : ∀ c : Multiplicative (ZMod n), cyclicHomSourceMarking n f c ≫ e.hom =
    cyclicHomSourceMarking n g c)

include ha hc in
/-- An actual affine marked comparison supplies all proper comparison data. -/
theorem cyclicHomProperRelated_of_affine_iso : CyclicHomProperRelated n f g := by
  let a := cyclicHomAuxiliaryPoint n f
  let b := cyclicHomAuxiliaryPoint n g
  refine ⟨auxiliaryAffineCubicIso a b e, auxiliaryAffineCubicIso_base a b e,
    auxiliaryAffineCubicIso_zero a b e ha, auxiliaryAffineCubicIso_section a b e ha, ?_⟩
  intro c
  rw [cyclicHomOriginalCubicValue, cyclicHomOriginalCubicValue,
    Category.assoc, auxiliaryAffineCubicIso_projection, ← Category.assoc, ← Over.comp_left, hc c]

include ha hc in
/-- Original independent marked affine families have the same full normalized parameter. -/
theorem cyclicHomNormalizedPoint_invariant_of_affine_iso :
    cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g :=
  (cyclicHomProperRelated_of_affine_iso n f g e ha hc).normalized_eq n f g

end FLT.Mazur.OddWeierstrassParameter
