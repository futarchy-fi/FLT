/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertModelFppfPicard
public import FLT.Mazur.AffineHilbertRelationNeighborhoods
public import FLT.Mazur.KernelPairEffectiveUnramified

/-!
# Derived etale geometry of the full original Picard regions

For every selected translation and every coequalizing finite presentation
model, the effective projection is formally unramified and its actual fppf
restriction is etale. These properties are proved from the original proper
family relation, without assuming them for the original model projection.
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
  {T : Over (Spec (.of R))} (w : A ⟶ T)
  (hw : (fst f hL d V c k).left ≫ w.left = (snd f hL d V c k).left ≫ w.left)
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local instance modelEtaleKernelMono : Mono (pullback.lift p q hw) :=
  modelRelationKernelMap_mono f hL d V c k w.left hw

/-- The whole effective source is unramified over the original nonreduced target open. -/
instance modelEffectiveRelativeProjection_formallyUnramified :
    FormallyUnramified (modelEffectiveRelativeProjection f hL d V c k w hw).left :=
  KernelPairEffectiveOpen.projection_formallyUnramified p q w.left hw

variable [LocallyOfFinitePresentation w.left]

/-- The constructed fppf region is actually etale for every original coefficient model. -/
instance modelFppfProjection_etale : Etale (modelFppfProjection f hL d V c k w hw).left :=
  KernelPairEffectiveOpen.fppfProjection_etale p q w.left hw

end FLT.Mazur.HilbertChart.AffineRestriction
