/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterGroupBaseChange
public import FLT.Mazur.RootsOfUnityInclusionBaseChange

/-!
# Group laws on the actual arithmetic roots-of-unity pullback

Both arithmetic comparisons preserve multiplication. Powers of the specified
root section therefore retain their original Laurent evaluations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace FLT.Mazur.RootsOfUnityGroupBaseChange

open CharacterSchemeBaseChange RootsOfUnityArithmeticPullback RootsOfUnityInclusionBaseChange

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)

instance torus_isMonHom : IsMonHom (torusComparison R A).hom :=
  CharacterGroupBaseChange.comparison_isMonHom R A ℤ

instance roots_isMonHom : IsMonHom (comparison R A n).hom :=
  CharacterGroupBaseChange.comparison_isMonHom R A (ZMod n)

/-- Every power of the pulled-back root is the comparison of its original power. -/
theorem rootSection_pow [NeZero n] (a : Aˣ) (ha : a ^ n = 1) (k : ℕ) :
    rootSection R A n a ha ^ k =
      (ArithmeticRootsOfUnitySections.rootSection A n a ha ^ k) ≫
        (comparison R A n).hom :=
  (MonObj.pow_comp _ k _).symm

/-- The power orbit in the pulled-back torus is the actual unit-power orbit. -/
theorem rootSection_pow_inclusion [NeZero n] (a : Aˣ) (ha : a ^ n = 1) (k : ℕ) :
    (rootSection R A n a ha ^ k) ≫
        (Over.pullback (baseMap R A)).map (RootsOfUnityScheme.inclusion R n) =
      ArithmeticTorusPoints.point A (a ^ k) ≫ (torusComparison R A).hom := by
  rw [rootSection_pow, Category.assoc, ← inclusion_comparison, ← Category.assoc,
    ArithmeticRootsOfUnitySections.section_pow_inclusion]

/-- The original subgroup projection retains the Laurent evaluation of every power. -/
@[reassoc] theorem rootSection_pow_laurent [NeZero n]
    (a : Aˣ) (ha : a ^ n = 1) (k : ℕ) :
    (rootSection R A n a ha ^ k).left ≫
        pullback.fst (RootsOfUnityScheme.model R n).hom (baseMap R A) ≫
          (RootsOfUnityScheme.inclusion R n).left =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) (a ^ k)).toRingHom) := by
  have h := congrArg (fun f ↦ f.left ≫
    pullback.fst (MultiplicativeGroupScheme.gm R).hom (baseMap R A))
      (rootSection_pow_inclusion R A n a ha k)
  simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst,
    torusComparison_fst] at h
  exact h.trans (by
      rw [ArithmeticTorusPoints.point_left, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro p
      change LaurentUnitPoints.evalUnit (R := A) (a ^ k)
        (CharacterAlgebraScalarExtension.coeff R A ℤ p) = _
      have hc : ((LaurentUnitPoints.evalUnit (R := A) (a ^ k)).restrictScalars R).comp
          (CharacterAlgebraScalarExtension.coeff R A ℤ) =
            LaurentUnitPoints.evalUnit (R := R) (a ^ k) := by
        apply AddMonoidAlgebra.algHom_ext
        · intro i
          change LaurentUnitPoints.evalUnit (R := A) (a ^ k)
            (CharacterAlgebraScalarExtension.coeff R A ℤ (AddMonoidAlgebra.single i 1)) =
              LaurentUnitPoints.evalUnit (R := R) (a ^ k) (AddMonoidAlgebra.single i 1)
          rw [CharacterAlgebraScalarExtension.coeff_single, map_one]
          change LaurentUnitPoints.evalUnit (R := A) (a ^ k) (LaurentPolynomial.T i) =
            LaurentUnitPoints.evalUnit (R := R) (a ^ k) (LaurentPolynomial.T i)
          rw [LaurentUnitPoints.evalUnit_T, LaurentUnitPoints.evalUnit_T]
        · ext
      exact congrArg (fun f ↦ f p) hc)

end FLT.Mazur.RootsOfUnityGroupBaseChange
