/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RootsOfUnityArithmeticPullback

/-!
# The actual roots-of-unity inclusion under arithmetic base change

The scalar-extension comparisons commute with the original subgroup inclusion.
Thus the extended Laurent quotient is the actual pulled-back closed subgroup,
with its original defining ideal and not only its pointwise support.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial

namespace FLT.Mazur.RootsOfUnityInclusionBaseChange

open CharacterAlgebraScalarExtension CharacterSchemeBaseChange

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)

/-- Reduction of characters modulo n commutes with the specified scalar extension. -/
theorem restriction_coeff :
    ((RootsOfUnityAlgebra.restriction A n).toAlgHom.restrictScalars R).comp (coeff R A ℤ) =
      (coeff R A (ZMod n)).comp (RootsOfUnityAlgebra.restriction R n).toAlgHom := by
  apply AddMonoidAlgebra.algHom_ext
  · intro i
    change RootsOfUnityAlgebra.restriction A n (coeff R A ℤ
      (AddMonoidAlgebra.single i 1)) =
      coeff R A (ZMod n) (RootsOfUnityAlgebra.restriction R n (AddMonoidAlgebra.single i 1))
    rw [coeff_single, RootsOfUnityAlgebra.restriction_single,
      RootsOfUnityAlgebra.restriction_single, coeff_single]
  · ext

/-- The arithmetic torus is the actual categorical pullback of the original torus. -/
def torusComparison : MultiplicativeGroupScheme.gm A ≅
    (Over.pullback (baseMap R A)).obj (MultiplicativeGroupScheme.gm R) :=
  overIso R A ℤ

/-- The torus comparison retains the Laurent coefficient map. -/
@[reassoc] theorem torusComparison_fst :
    (torusComparison R A).hom.left ≫ pullback.fst (MultiplicativeGroupScheme.gm R).hom
      (baseMap R A) = Spec.map (CommRingCat.ofHom (coeff R A ℤ).toRingHom) :=
  overIso_fst R A ℤ

/-- The actual pulled-back subgroup inclusion is the extended Laurent quotient map. -/
theorem inclusion_comparison :
    RootsOfUnityScheme.inclusion A n ≫ (torusComparison R A).hom =
      (RootsOfUnityArithmeticPullback.comparison R A n).hom ≫
        (Over.pullback (baseMap R A)).map (RootsOfUnityScheme.inclusion R n) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, torusComparison_fst,
      Over.pullback_map_left, pullback.lift_fst]
    rw [← Category.assoc, RootsOfUnityArithmeticPullback.comparison_fst,
      RootsOfUnityScheme.inclusion_left, RootsOfUnityScheme.inclusion_left,
      ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
      (restriction_coeff R A n)
  · exact (RootsOfUnityScheme.inclusion A n ≫ (torusComparison R A).hom).w.trans
      ((RootsOfUnityArithmeticPullback.comparison R A n).hom ≫
        (Over.pullback (baseMap R A)).map (RootsOfUnityScheme.inclusion R n)).w.symm

end FLT.Mazur.RootsOfUnityInclusionBaseChange
