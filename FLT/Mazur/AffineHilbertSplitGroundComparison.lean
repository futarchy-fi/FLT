/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertUnramifiedSplitOrbits
public import FLT.Mazur.SchemeRelationSplitOrbitGround

/-!
# Proper-family split orbits in actual ground-changed Hilbert parameters

The new ground is the entire original affine source. The coefficient split
source immerses into the actual ground pullback of the Hilbert parameter
scheme. The full original relation is retained. These immersions are not
asserted to be open charts or to give an fppf cover of the old model.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd finiteKernelProjection finiteKernelModel
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "w" => Over.Hom.left (finiteKernelProjection f hL d V c k)
local notation "i" => Over.hom (finiteKernelModel f hL d V c k)
local notation "H" => variableHilbertTest f d V
local notation "h" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "e" => equivalence f hL d V c k
local notation "a" => 𝟙 A.left
local instance splitGroundKernelMono : Mono (pullback.lift (p).left (q).left h) :=
  modelRelationKernelMap_mono f hL d V c k w h
local instance splitGroundModelSeparated : IsSeparated i := inferInstance

/-- The parameter target is exactly the ground pullback by the ORIGINAL source structure map. -/
def finiteModelSplitGroundParameterIso :
    SchemeSplitSeedGroundComparison.groundParameter w i a (H).hom ≅
      pullback (H).hom A.hom :=
  pullback.congrHom rfl (by rw [Category.id_comp, (finiteKernelProjection f hL d V c k).w])

local notation "hk" => Eq.trans (Over.w (finiteKernelProjection f hL d V c k)) (Eq.symm (Over.w k))

/-- The full coefficient split source maps to the genuine ground-changed Hilbert parameters. -/
def finiteModelSplitGroundChart : SchemeSplitEtaleSourceSeed.source w a ⟶
    pullback (H).hom A.hom :=
  SchemeSplitSeedGroundComparison.splitChart w i a k.left (H).hom hk ≫
    (finiteModelSplitGroundParameterIso f hL d V c k).hom

/-- No old unramifiedness is needed for this immersion of the complete coefficient source. -/
instance finiteModelSplitGroundChart_isImmersion :
    IsImmersion (finiteModelSplitGroundChart f hL d V c k) :=
  inferInstanceAs (IsImmersion
    (SchemeSplitSeedGroundComparison.splitChart w i a k.left (H).hom hk ≫
      (finiteModelSplitGroundParameterIso f hL d V c k).hom))

@[reassoc]
theorem finiteModelSplitGroundChart_old : finiteModelSplitGroundChart f hL d V c k ≫
    pullback.fst (H).hom A.hom = SchemeSplitEtaleSourceSeed.toSource w a ≫ k.left := by
  simp only [finiteModelSplitGroundChart, finiteModelSplitGroundParameterIso, Category.assoc,
    pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
    SchemeSplitSeedGroundComparison.splitChart_old]

@[reassoc]
theorem finiteModelSplitGroundChart_new : finiteModelSplitGroundChart f hL d V c k ≫
    pullback.snd (H).hom A.hom = SchemeSplitEtaleSourceSeed.projection w a := by
  simp only [finiteModelSplitGroundChart, finiteModelSplitGroundParameterIso, Category.assoc,
    pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
    SchemeSplitSeedGroundComparison.splitChart_new]

/-- Every original parameter point survives with its exact original parameter and new ground. -/
theorem finiteModelSplitGroundChart_point (x : A.left) :
    (finiteModelSplitGroundChart f hL d V c k ≫ pullback.fst (H).hom A.hom)
        (SchemeSplitEtaleSourceSeed.seed w a x) = k.left x ∧
    (finiteModelSplitGroundChart f hL d V c k ≫ pullback.snd (H).hom A.hom)
        (SchemeSplitEtaleSourceSeed.seed w a x) = x := by
  constructor
  · rw [finiteModelSplitGroundChart_old]
    change k.left (SchemeSplitEtaleSourceSeed.toSource w a
      (SchemeSplitEtaleSourceSeed.seed w a x)) = k.left x
    rw [SchemeSplitEtaleSourceSeed.seed_point]
    rfl
  · rw [finiteModelSplitGroundChart_new]
    exact congrArg (fun g ↦ g x) (SchemeSplitEtaleSourceSeed.seed_projection w a)

/-- The full original orbit relation agrees across the coefficient/ground comparison. -/
def finiteModelSplitGroundRelationIso : SchemeRelationSplitOrbit.fullRelation w h a ≅
    SchemeRelationSplitOrbit.fullRelation (w ≫ i)
      (SchemeRelationSplitOrbit.ground_condition w h i) a :=
  SchemeRelationSplitOrbit.fullGroundRelationIso e w h i a

variable [FormallyUnramified (finiteKernelProjection f hL d V c k).left]

/-- Actual affine split selections immerse in the genuine changed Hilbert parameter scheme. -/
theorem finiteModelSplitGroundAffine_isImmersion (x : A.left) :
    IsImmersion (SchemeRelationSplitOrbit.affineToOrbit e a x ≫
      SchemeRelationSplitOrbit.inclusion w h a ≫ finiteModelSplitGroundChart f hL d V c k) := by
  let _ := SchemeRelationSplitOrbit.inclusion_isOpenImmersion w h a
  infer_instance

end FLT.Mazur.HilbertChart.AffineRestriction
