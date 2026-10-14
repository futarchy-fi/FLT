/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertMonicKernelGeometry
public import FLT.Mazur.KernelPairEffectiveOpen

/-!
# Effective target opens for the full original Picard relation

Apply the intrinsic open construction to the actual monomorphic comparison.
The resulting whole-source relation is an effective kernel pair over an open
of the actual target. These opens may be empty; global coverage is still open.
The original proper family and both independent relation endpoints are retained.
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

/-- The constructed open is in the original model target, with its full scheme structure. -/
def monicModelEffectiveTargetOpen : T.Opens := KernelPairEffectiveOpen.targetOpen p q w H

/-- The whole original source above that target open, without choosing an affine branch. -/
def monicModelEffectiveSource : Scheme := KernelPairEffectiveOpen.source p q w H

/-- The complete original relation above the same open, without replacing it by a kernel. -/
def monicModelEffectiveRelation : Scheme := KernelPairEffectiveOpen.relation p q w H

/-- The actual quotient projection over the constructed open. -/
def monicModelEffectiveProjection : monicModelEffectiveSource f hL d V c k u i w h ⟶
    (monicModelEffectiveTargetOpen f hL d V c k u i w h).toScheme :=
  KernelPairEffectiveOpen.projection p q w H

/-- Both actual original endpoints form an effective kernel pair on the retained target. -/
theorem monicModelEffective_isPullback :
    IsPullback (KernelPairEffectiveOpen.fst p q w H) (KernelPairEffectiveOpen.snd p q w H)
      (monicModelEffectiveProjection f hL d V c k u i w h)
      (monicModelEffectiveProjection f hL d V c k u i w h) :=
  @KernelPairEffectiveOpen.isPullback _ _ _ p q w H
    (monicModelRelationKernelMap_mono f hL d V c k u i w h)

/-- Flatness of an actual model projection survives on the constructed effective open. -/
instance monicModelEffectiveProjection_flat [Flat w] :
    Flat (monicModelEffectiveProjection f hL d V c k u i w h) :=
  inferInstanceAs (Flat (KernelPairEffectiveOpen.projection p q w H))

/-- Surjectivity is inherited from the original projection, not imposed on the comparison. -/
instance monicModelEffectiveProjection_surjective [Surjective w] :
    Surjective (monicModelEffectiveProjection f hL d V c k u i w h) :=
  inferInstanceAs (Surjective (KernelPairEffectiveOpen.projection p q w H))

/-- Finite presentation follows from the actual finite-model square. -/
instance monicModelEffectiveProjection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (monicModelEffectiveProjection f hL d V c k u i w h) := by
  let _ := monicModelProjection_locallyOfFinitePresentation f hL d V c k u i w h
  exact inferInstanceAs
    (LocallyOfFinitePresentation (KernelPairEffectiveOpen.projection p q w H))

/-- Quasi-compactness likewise follows from the original affine finite-model projection. -/
instance monicModelEffectiveProjection_quasiCompact :
    QuasiCompact (monicModelEffectiveProjection f hL d V c k u i w h) := by
  let _ : QuasiCompact w := MorphismProperty.of_isPullback h inferInstance
  exact inferInstanceAs (QuasiCompact (KernelPairEffectiveOpen.projection p q w H))

end FLT.Mazur.HilbertChart.AffineRestriction
