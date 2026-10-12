/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonAmbientAffineFullRelation

/-!
# The actual affine-chart overlaps are open in the full original relation

Both endpoint restrictions are open immersions into the original relation.
Their endpoint maps are etale over an etale translation base, by actual
scheme pullback. No finiteness of these etale maps is assumed or inferred.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) (V : Over (Spec (.of R)))
  {L : X.Modules} (hL : AmpleLineBundle L)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  (i j : (commonAmbientGrassmannianAffineCover f d V hL).I₀)
local notation "a" => commonAmbientAffineInclusion f d V hL i
local notation "b" => commonAmbientAffineInclusion f d V hL j
local notation "p" => variableChartRelationFst f hL d V c
local notation "q" => variableChartRelationSnd f hL d V c
local notation "o" => commonAmbientAffineRelationOther f d V hL c i

/-- The first endpoint restriction embeds openly in the actual full relation. -/
instance commonAmbientAffineRelationFirst_isOpenImmersion :
    IsOpenImmersion (pullback.fst p a).left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback p a).map (Over.forget _)).flip
    (inferInstanceAs (IsOpenImmersion (a).left))

/-- The second endpoint restriction embeds openly in the first restriction. -/
instance commonAmbientAffineRelationSecond_isOpenImmersion :
    IsOpenImmersion (pullback.fst o b).left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback o b).map (Over.forget _)).flip
    (inferInstanceAs (IsOpenImmersion (b).left))

/-- Every constructed overlap is an open subscheme of the ORIGINAL full relation. -/
instance commonAmbientAffineRelationOriginal_isOpenImmersion :
    IsOpenImmersion (commonAmbientAffineRelationOriginal f d V hL c i j).left :=
  inferInstanceAs (IsOpenImmersion ((pullback.fst o b).left ≫ (pullback.fst p a).left))

variable [Etale V.hom]

/-- The first restriction's projection to its actual affine endpoint is etale. -/
instance commonAmbientAffineRelationFirst_snd_etale : Etale (pullback.snd p a).left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback p a).map (Over.forget _))
    (inferInstanceAs (Etale (p).left))

instance commonAmbientAffineRelationOther_etale : Etale (o).left :=
  inferInstanceAs (Etale ((pullback.fst p a).left ≫ (q).left))

/-- The first full-overlap endpoint remains etale after the second open restriction. -/
instance commonAmbientAffineRelationFst_etale :
    Etale (commonAmbientAffineRelationFst f d V hL c i j).left :=
  inferInstanceAs (Etale ((pullback.fst o b).left ≫ (pullback.snd p a).left))

/-- The second full-overlap endpoint is the actual etale pullback. -/
instance commonAmbientAffineRelationSnd_etale :
    Etale (commonAmbientAffineRelationSnd f d V hL c i j).left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback o b).map (Over.forget _))
    (inferInstanceAs (Etale (o).left))

end FLT.Mazur.HilbertChart
