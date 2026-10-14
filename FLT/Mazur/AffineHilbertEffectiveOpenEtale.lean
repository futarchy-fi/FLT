/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertEffectiveOpenDescent
public import FLT.Mazur.KernelPairEffectiveOpenEtale

/-!
# Etale effective models for the original Picard relation

The full original relation has etale endpoints. On the constructed effective
target open, these endpoints form the actual kernel pair. Fppf descent then
proves that the actual effective quotient projection is etale.
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
local notation "p" => Over.Hom.left (fst f hL d V c (u ≫ k))
local notation "q" => Over.Hom.left (snd f hL d V c (u ≫ k))
local notation "H" => monicModelRelation_condition f hL d V c k u i w h

variable [Flat w] [Surjective w]

/-- The effective original-source projection is actually etale, not merely flat. -/
theorem monicModelEffectiveProjection_etale :
    Etale (monicModelEffectiveProjection f hL d V c k u i w h) := by
  let _ := monicModelRelation_fst_etale f hL d V c k u i w h
  let _ := monicModelProjection_locallyOfFinitePresentation f hL d V c k u i w h
  exact @KernelPairEffectiveOpen.projection_etale _ _ _ p q w H
    (monicModelRelationKernelMap_mono f hL d V c k u i w h) _ _ _ _

/-- The relative projection is an etale cover over the unchanged original coefficient base. -/
instance monicModelEffectiveRelativeProjection_etale :
    Etale (monicModelEffectiveRelativeProjection f hL d V c k u i w h).left :=
  monicModelEffectiveProjection_etale f hL d V c k u i w h

end FLT.Mazur.HilbertChart.AffineRestriction
