/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonTorusBaseChange
public import FLT.Mazur.OneGonAdicInitialRoots
public import FLT.Mazur.WeierstrassCharacterCoefficientHom

/-!
# The native arithmetic boundary roots commute with coefficients

The corrected torus coordinate on the new arithmetic cubic is compared with
the original coordinate, including its inversion. This identifies the actual
boundary roots homomorphisms over arbitrary coefficient rings.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonRootsCoefficientNaturality
open OneGonSmoothing WeierstrassIntegralChart CharacterSchemeBaseChange
open CharacterAlgebraScalarExtension RootsOfUnityInclusionBaseChange
open OneGonAdicCharacterTower
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]

/-- The native corrected boundary torus projects to the original corrected torus. -/
@[reassoc] theorem nativeTorus_projection :
    (ArithmeticOneGonTorus.torusIso S).hom.left ≫
      smoothCoefficientMapTo (equation (0 : R)) (equation (0 : S)) (algebraMap R S)
        (ArithmeticOneGonNodalCoefficient.equation_zero R S).symm =
      Spec.map (CommRingCat.ofHom (coeff R S ℤ).toRingHom) ≫
        (ArithmeticOneGonTorus.torusIso R).hom.left := by
  have h := congrArg (fun k => k.left ≫
    pullback.fst (relativeGroup (0 : R)).X.hom (baseMap R S))
    (ArithmeticOneGonTorusBaseChange.torus_comparison R S)
  simp only [Over.comp_left, Over.pullback_map_left] at h
  erw [Category.assoc, pullback.lift_fst] at h
  rw [← Category.assoc, torusComparison_fst] at h
  apply (cancel_mono (integralSmoothOpen (equation (0 : R))).ι).mp
  rw [Category.assoc, smoothCoefficientMapTo_inclusion, h, Category.assoc]
  erw [ArithmeticOneGonFiberTorus.torusIso_inclusion S (0 : R) (map_zero _)]
  rw [ArithmeticOneGonTorus.torusIso_hom, Over.comp_left, Category.assoc]
  rfl

variable (n : ℕ) [NeZero n]

/-- Native roots inclusions retain their original character coefficient projection. -/
@[reassoc] theorem nativeRoots_projection :
    (boundaryRootsHom (R := S) n).hom.hom.hom.left ≫
      smoothCoefficientMapTo (equation (0 : R)) (equation (0 : S)) (algebraMap R S)
        (ArithmeticOneGonNodalCoefficient.equation_zero R S).symm =
      Spec.map (CommRingCat.ofHom (coeff R S (ZMod n)).toRingHom) ≫
        (boundaryRootsHom (R := R) n).hom.hom.hom.left := by
  have h := congrArg (fun k => k.left ≫
    pullback.fst (MultiplicativeGroupScheme.gm R).hom (baseMap R S))
    (inclusion_comparison R S n)
  simp only [Over.comp_left, Category.assoc, torusComparison_fst,
    Over.pullback_map_left, pullback.lift_fst] at h
  rw [← Category.assoc, RootsOfUnityArithmeticPullback.comparison_fst] at h
  change ((RootsOfUnityScheme.inclusion S n).left ≫
    (ArithmeticOneGonTorus.torusIso S).hom.left) ≫ _ =
      _ ≫ (RootsOfUnityScheme.inclusion R n).left ≫
        (ArithmeticOneGonTorus.torusIso R).hom.left
  rw [Category.assoc, nativeTorus_projection, ← Category.assoc, h, Category.assoc]

end FLT.Mazur.ArithmeticOneGonRootsCoefficientNaturality
