/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessiveTensorCoordinates
public import FLT.Mazur.WeierstrassDividedUnequalPair

/-!
# The full pair of successive tensor charts and its original divided inputs

Both tensor factors share their actual coefficient algebra. Their coordinates
map to the unchanged integral divided pair, retaining both creation depths.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k l : ℕ} (hπ : π ≠ 0) (d : Data W π k) (d' : Data W π (k + 1))
  (e : Data W π l) (e' : Data W π (l + 1)) (S : Type u) [CommRing S] [Algebra R S]
local notation "A" => ScalarExtension W (π ^ k) π d'.b3 d'.b4 d'.b6 S
local notation "B" => ScalarExtension W (π ^ l) π e'.b3 e'.b4 e'.b6 S

/-- The entire relative tensor pair over the actual extended coefficient ring. -/
def SuccessiveTensorPairRing := A ⊗[S] B

instance successiveTensorPairCommRing : CommRing (SuccessiveTensorPairRing d' e' S) :=
  inferInstanceAs (CommRing (A ⊗[S] B))

instance successiveTensorPairAlgebra : Algebra R (SuccessiveTensorPairRing d' e' S) :=
  inferInstanceAs (Algebra R (A ⊗[S] B))

instance successiveTensorPairBaseAlgebra : Algebra S (SuccessiveTensorPairRing d' e' S) :=
  inferInstanceAs (Algebra S (A ⊗[S] B))

instance successiveTensorPairTower : IsScalarTower R S (SuccessiveTensorPairRing d' e' S) :=
  inferInstanceAs (IsScalarTower R S (A ⊗[S] B))

local notation "P" => SuccessiveTensorPairRing d' e' S

/-- The first full tensor input, regarded over the original coefficients. -/
def successiveTensorPairLeft : A →ₐ[R] P :=
  (Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] B).restrictScalars R

/-- The second full tensor input, with its independent own-depth coordinates. -/
def successiveTensorPairRight : B →ₐ[R] P :=
  (Algebra.TensorProduct.includeRight : B →ₐ[S] A ⊗[S] B).restrictScalars R

local notation "a" => (successiveTensorPairLeft d' e' S).comp (successiveTensorInput hπ d d' S)
local notation "b" => (successiveTensorPairRight d' e' S).comp (successiveTensorInput hπ e e' S)

attribute [local semireducible] UnequalPairRing

/-- Both actual contractions define the integral divided pair input. -/
def successiveTensorPairInput : UnequalPairRing d e →ₐ[R] P :=
  Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _)

/-- Every first divided coordinate is the exact contraction of the first tensor input. -/
theorem successiveTensorPairInput_left :
    (successiveTensorPairInput hπ d d' e e' S).comp (unequalPairLeft d e) = a := by
  exact Algebra.TensorProduct.lift_comp_includeLeft a b _

/-- Every second divided coordinate retains the second input's own depth. -/
theorem successiveTensorPairInput_right :
    (successiveTensorPairInput hπ d d' e e' S).comp (unequalPairRight d e) = b := by
  exact Algebra.TensorProduct.lift_comp_includeRight' a b _

/-- Evaluate any first divided coordinate using its exact tensor contraction. -/
theorem successiveTensorPairInput_left_apply
    (z : WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6) :
    successiveTensorPairInput hπ d d' e e' S (unequalPairLeft d e z) =
      successiveTensorPairLeft d' e' S (successiveTensorInput hπ d d' S z) :=
  congrArg (fun f => f z) (successiveTensorPairInput_left hπ d d' e e' S)

/-- Evaluate any second divided coordinate without first lowering its depth. -/
theorem successiveTensorPairInput_right_apply
    (z : WeierstrassDilatation.Coordinate W (π ^ l) e.b3 e.b4 e.b6) :
    successiveTensorPairInput hπ d d' e e' S (unequalPairRight d e z) =
      successiveTensorPairRight d' e' S (successiveTensorInput hπ e e' S z) :=
  congrArg (fun f => f z) (successiveTensorPairInput_right hπ d d' e e' S)

attribute [irreducible] SuccessiveTensorPairRing

end FLT.Mazur.WeierstrassDividedDepth
