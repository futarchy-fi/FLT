/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthData
public import FLT.Mazur.WeierstrassDividedPairSecantGeometry

/-!
# The complete product of two different divided charts

Retain both coordinate algebras at their own depths. Their tensor spectrum
is the full relative product, and is flat over the original coefficients.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {π : R} {k l : ℕ}
  (d : Data W π k) (e : Data W π l)
local notation "A" => Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "B" => Coordinate W (π ^ l) e.b3 e.b4 e.b6

/-- The whole pair algebra, with no contraction or input restriction. -/
def UnequalPairRing := A ⊗[R] B

instance unequalPairCommRing : CommRing (UnequalPairRing d e) :=
  inferInstanceAs (CommRing (A ⊗[R] B))

instance unequalPairAlgebra : Algebra R (UnequalPairRing d e) :=
  inferInstanceAs (Algebra R (A ⊗[R] B))

instance unequalPairFlat : Module.Flat R (UnequalPairRing d e) :=
  inferInstanceAs (Module.Flat R (A ⊗[R] B))

/-- The unchanged first divided input. -/
def unequalPairLeft : A →ₐ[R] UnequalPairRing d e := Algebra.TensorProduct.includeLeft

/-- The unchanged deeper divided input. -/
def unequalPairRight : B →ₐ[R] UnequalPairRing d e := Algebra.TensorProduct.includeRight

local notation "qa" => Spec.map (CommRingCat.ofHom (algebraMap R A))
local notation "qb" => Spec.map (CommRingCat.ofHom (algebraMap R B))

/-- The entire tensor spectrum is the exact relative product of the two divided charts. -/
def unequalPairSpecIso : pullback qa qb ≅ Spec (.of (UnequalPairRing d e)) :=
  pullbackSpecIso R A B

/-- The first projection retains every coordinate of the shallower input. -/
@[reassoc] theorem unequalPairSpecIso_fst :
    (unequalPairSpecIso d e).inv ≫ pullback.fst qa qb =
      Spec.map (CommRingCat.ofHom (unequalPairLeft d e).toRingHom) :=
  pullbackSpecIso_inv_fst R A B

/-- The second projection retains every uncontracted coordinate of the deeper input. -/
@[reassoc] theorem unequalPairSpecIso_snd :
    (unequalPairSpecIso d e).inv ≫ pullback.snd qa qb =
      Spec.map (CommRingCat.ofHom (unequalPairRight d e).toRingHom) :=
  pullbackSpecIso_inv_snd R A B

attribute [irreducible] UnequalPairRing

end FLT.Mazur.WeierstrassDividedDepth
