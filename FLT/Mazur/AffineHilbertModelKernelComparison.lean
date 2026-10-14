/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFullRelationRestriction
public import FLT.Mazur.KernelPairEffectiveOpen

/-!
# Full Picard relations in arbitrary coefficient models

Any morphism coequalizing the original relation gives a monomorphic comparison
with its entire scheme kernel. The target need not be a monomorphic base change
of a previously selected model. This includes reselected joint coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
variable {T : Scheme} (w : A.left ⟶ T)
  (hw : (fst f hL d V c k).left ≫ w = (snd f hL d V c k).left ≫ w)

/-- The full original relation maps into the actual candidate kernel. -/
def modelRelationKernelMap : (relation f hL d V c k).left ⟶ pullback w w :=
  pullback.lift (p).left (q).left hw

@[reassoc]
theorem modelRelationKernelMap_fst : modelRelationKernelMap f hL d V c k w hw ≫
    pullback.fst w w = (p).left := pullback.lift_fst _ _ _

@[reassoc]
theorem modelRelationKernelMap_snd : modelRelationKernelMap f hL d V c k w hw ≫
    pullback.snd w w = (q).left := pullback.lift_snd _ _ _

/-- The comparison loses no arrows; its surjectivity remains a separate geometric task. -/
instance modelRelationKernelMap_mono :
    Mono (modelRelationKernelMap f hL d V c k w hw) where
  right_cancellation := by
    intro Z a b hab
    have ha : a ≫ (p).left = b ≫ (p).left := by
      simpa only [modelRelationKernelMap, Category.assoc, pullback.lift_fst] using
        congrArg (fun z ↦ z ≫ pullback.fst w w) hab
    have hb : a ≫ (q).left = b ≫ (q).left := by
      simpa only [modelRelationKernelMap, Category.assoc, pullback.lift_snd] using
        congrArg (fun z ↦ z ≫ pullback.snd w w) hab
    let Z' := Over.mk (a ≫ (relation f hL d V c k).hom)
    let a' : Z' ⟶ relation f hL d V c k := Over.homMk a
    let b' : Z' ⟶ relation f hL d V c k := Over.homMk b (by
      change b ≫ (relation f hL d V c k).hom =
        a ≫ (relation f hL d V c k).hom
      rw [← (p).w, ← Category.assoc, ← Category.assoc, ha])
    exact congrArg Over.Hom.left (hom_ext f hL d V c k
      (a := a') (b := b') (Over.OverMorphism.ext ha) (Over.OverMorphism.ext hb))


end FLT.Mazur.HilbertChart.AffineRestriction
