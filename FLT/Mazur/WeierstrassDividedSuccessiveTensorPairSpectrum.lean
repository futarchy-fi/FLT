/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessiveTensorPair
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The full successive tensor pair is the relative affine product

The product uses the actual extended coefficient algebra, with both original
projections unchanged. No flatness of an arithmetic quotient is required.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} {π : R}
  {k l : ℕ} (d' : Data W π (k + 1)) (e' : Data W π (l + 1))
  (S : Type u) [CommRing S] [Algebra R S]
local notation "A" => ScalarExtension W (π ^ k) π d'.b3 d'.b4 d'.b6 S
local notation "B" => ScalarExtension W (π ^ l) π e'.b3 e'.b4 e'.b6 S
local notation "a" => Spec.map (CommRingCat.ofHom (algebraMap S A))
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap S B))
local notation "P" => SuccessiveTensorPairRing d' e' S
attribute [local semireducible] SuccessiveTensorPairRing

/-- The full pair spectrum identifies with the product over its actual coefficient scheme. -/
def successiveTensorPairSpectrumIso : pullback a b ≅ Spec (.of P) :=
  pullbackSpecIso S A B

/-- The comparison preserves the first full tensor input. -/
@[reassoc] theorem successiveTensorPairSpectrumIso_left :
    (successiveTensorPairSpectrumIso d' e' S).hom ≫
      Spec.map (CommRingCat.ofHom (successiveTensorPairLeft d' e' S).toRingHom) =
        pullback.fst a b :=
  pullbackSpecIso_hom_fst S A B

/-- The comparison preserves the second full tensor input. -/
@[reassoc] theorem successiveTensorPairSpectrumIso_right :
    (successiveTensorPairSpectrumIso d' e' S).hom ≫
      Spec.map (CommRingCat.ofHom (successiveTensorPairRight d' e' S).toRingHom) =
        pullback.snd a b :=
  pullbackSpecIso_hom_snd S A B

end FLT.Mazur.WeierstrassDividedDepth
