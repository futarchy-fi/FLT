/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantSource
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The universal product of two divided inputs

The tensor product retains both complete divided coordinate algebras. Its
secant localization is flat over the original coefficients, so a regular
scale remains regular without being inverted.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The full product algebra of two arbitrary divided inputs. -/
def DividedPairRing := Coordinate W s b3 b4 b6 ⊗[R] Coordinate W s b3 b4 b6

instance dividedPairCommRing : CommRing (DividedPairRing W s b3 b4 b6) :=
  inferInstanceAs (CommRing (Coordinate W s b3 b4 b6 ⊗[R] Coordinate W s b3 b4 b6))

instance dividedPairAlgebra : Algebra R (DividedPairRing W s b3 b4 b6) :=
  inferInstanceAs (Algebra R (Coordinate W s b3 b4 b6 ⊗[R] Coordinate W s b3 b4 b6))

instance dividedPairFlat : Module.Flat R (DividedPairRing W s b3 b4 b6) :=
  inferInstanceAs (Module.Flat R (Coordinate W s b3 b4 b6 ⊗[R] Coordinate W s b3 b4 b6))

/-- The first full divided input. -/
def dividedPairLeft : Coordinate W s b3 b4 b6 →ₐ[R] DividedPairRing W s b3 b4 b6 :=
  Algebra.TensorProduct.includeLeft

/-- The second full divided input. -/
def dividedPairRight : Coordinate W s b3 b4 b6 →ₐ[R] DividedPairRing W s b3 b4 b6 :=
  Algebra.TensorProduct.includeRight

/-- Every pair of actual divided points evaluates the universal product. -/
def dividedPairEvaluation {S : Type u} [CommRing S] [Algebra R S]
    (a c : Coordinate W s b3 b4 b6 →ₐ[R] S) : DividedPairRing W s b3 b4 b6 →ₐ[R] S :=
  Algebra.TensorProduct.lift a c (fun _ _ => Commute.all _ _)

/-- Evaluation retains the first input on every coordinate function. -/
@[simp] theorem dividedPairEvaluation_left {S : Type u} [CommRing S] [Algebra R S]
    (a c : Coordinate W s b3 b4 b6 →ₐ[R] S) (t : Coordinate W s b3 b4 b6) :
    dividedPairEvaluation W s b3 b4 b6 a c (dividedPairLeft W s b3 b4 b6 t) = a t := by
  exact DFunLike.congr_fun
    (Algebra.TensorProduct.lift_comp_includeLeft a c (fun _ _ => Commute.all _ _)) t

/-- Evaluation retains the second input on every coordinate function. -/
@[simp] theorem dividedPairEvaluation_right {S : Type u} [CommRing S] [Algebra R S]
    (a c : Coordinate W s b3 b4 b6 →ₐ[R] S) (t : Coordinate W s b3 b4 b6) :
    dividedPairEvaluation W s b3 b4 b6 a c (dividedPairRight W s b3 b4 b6 t) = c t := by
  exact DFunLike.congr_fun
    (Algebra.TensorProduct.lift_comp_includeRight' a c (fun _ _ => Commute.all _ _)) t

attribute [irreducible] DividedPairRing

/-- The universal divided secant principal open, with both inputs unrestricted. -/
abbrev DividedPairSecantRing := DividedSecantRing W s b3 b4 b6
  (dividedPairLeft W s b3 b4 b6) (dividedPairRight W s b3 b4 b6)

instance dividedPairSecantFlat : Module.Flat R (DividedPairSecantRing W s b3 b4 b6) := by
  let _ : Module.Flat (DividedPairRing W s b3 b4 b6) (DividedPairSecantRing W s b3 b4 b6) :=
    IsLocalization.flat _ (Submonoid.powers
      (dividedPairLeft W s b3 b4 b6 (x W s b3 b4 b6) -
        dividedPairRight W s b3 b4 b6 (x W s b3 b4 b6)))
  exact Module.Flat.trans R (DividedPairRing W s b3 b4 b6) (DividedPairSecantRing W s b3 b4 b6)

/-- Regularity needed for original-addition comparison is proved for the universal source. -/
theorem dividedPairSecant_scale_regular (hs : IsRegular s) :
    IsRegular (algebraMap R (DividedPairSecantRing W s b3 b4 b6) s) :=
  WeierstrassIntegralChart.flatRingHom_isRegular _
    (RingHom.flat_algebraMap_iff.mpr inferInstance) hs

end FLT.Mazur.WeierstrassDilatation
