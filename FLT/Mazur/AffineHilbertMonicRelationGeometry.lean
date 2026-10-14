/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertMonicModelRelation
public import FLT.Mazur.AffineHilbertDerivedNoetherianRelation

/-!
# Geometric properties of the retained Picard relation

The full original endpoints stay étale and surjective under monomorphic finite
model base change. Where the original relation is quasi-compact, that property
also survives. These are properties of the original relation, not its kernel.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  {B : Over (Spec (.of R))} (u : B ⟶ A) {T : Scheme}
  (i : T ⟶ (finiteKernelModel f hL d V c k).left) [Mono i] (w : B.left ⟶ T)
  (h : IsPullback u.left w (finiteKernelProjection f hL d V c k).left i)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "p'" => fst f hL d V c (u ≫ k)
local notation "q'" => snd f hL d V c (u ≫ k)

include h in
/-- Étaleness survives on the entire first endpoint of the original relation. -/
theorem monicModelRelation_fst_etale : Etale (p').left :=
  MorphismProperty.of_isPullback
    (monicModelRelation_fst_isPullback f hL d V c k u i w h) inferInstance

include h in
/-- The complete second endpoint is étale as well. -/
theorem monicModelRelation_snd_etale : Etale (q').left :=
  MorphismProperty.of_isPullback
    (monicModelRelation_snd_isPullback f hL d V c k u i w h) inferInstance

include h in
/-- The first endpoint retains all points, by base change of the original identity arrows. -/
theorem monicModelRelation_fst_surjective : Surjective (p').left :=
  MorphismProperty.of_isPullback
    (monicModelRelation_fst_isPullback f hL d V c k u i w h) inferInstance

include h in
/-- The second endpoint also retains every original-source point. -/
theorem monicModelRelation_snd_surjective : Surjective (q').left :=
  MorphismProperty.of_isPullback
    (monicModelRelation_snd_isPullback f hL d V c k u i w h) inferInstance

include h in
/-- No original first-endpoint arrows are lost in the quasi-compact base change. -/
theorem monicModelRelation_fst_quasiCompact [QuasiCompact (p).left] :
    QuasiCompact (p').left :=
  MorphismProperty.of_isPullback
    (monicModelRelation_fst_isPullback f hL d V c k u i w h) inferInstance

include h in
/-- Quasi-compactness of the full second endpoint is likewise preserved. -/
theorem monicModelRelation_snd_quasiCompact [QuasiCompact (q).left] :
    QuasiCompact (q').left :=
  MorphismProperty.of_isPullback
    (monicModelRelation_snd_isPullback f hL d V c k u i w h) inferInstance

end FLT.Mazur.HilbertChart.AffineRestriction
