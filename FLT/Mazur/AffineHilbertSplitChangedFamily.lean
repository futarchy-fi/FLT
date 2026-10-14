/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertSplitGroundComparison
public import FLT.Mazur.VariableHilbertCanonicalGroundIso

/-!
# Split sources in freshly constructed changed-family Hilbert parameters

An affine seed determines an actual ground change and the complete pulled-back
translation. The coefficient split source maps to the new family's Hilbert
parameter scheme by an immersion. Both the old parameter and new ground
coordinate are proved correct. Open Hilbert selections and old-model fppf
coverage still require further geometry.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd finiteKernelProjection finiteKernelModel
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R'] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  (s : Spec (.of R') ⟶ A.left)
local notation "w" => Over.Hom.left (finiteKernelProjection f hL d V c k)
local notation "i" => Over.hom (finiteKernelModel f hL d V c k)
local notation "H" => variableHilbertTest f d V
local notation "a" => s ≫ A.hom
local notation "q" => Limits.pullback.snd f a
local notation "W" => RelativeCoefficientBaseChange.target a (T := V)
local notation "t" => RelativeCoefficientBaseChange.toOld a (T := V)
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
local notation "hk" =>
  Eq.trans (Over.w (finiteKernelProjection f hL d V c k)) (Eq.symm (Over.w k))
local instance splitChangedFamilySmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local instance splitChangedFamilySeparated : IsSeparated i := inferInstance

/-- The seed's ground map is the original source structure, without a coefficient substitution. -/
def splitChangedGroundParameterIso :
    SchemeSplitSeedGroundComparison.groundParameter w i s (H).hom ≅
      pullback (H).hom a :=
  pullback.congrHom rfl (by rw [Category.assoc, (finiteKernelProjection f hL d V c k).w])

/-- The map lands in the freshly constructed Hilbert parameters of the changed proper family. -/
def splitChangedFamilyChart : SchemeSplitEtaleSourceSeed.source w s ⟶
    (variableHilbertTest q d W).left :=
  SchemeSplitSeedGroundComparison.splitChart w i s k.left (H).hom hk ≫
    (splitChangedGroundParameterIso f hL d V c k s).hom ≫
      (variableHilbertCanonicalGroundIso f a hL d V).inv

/-- This constructed map is an immersion of schemes, not a claimed open selection. -/
instance splitChangedFamilyChart_isImmersion :
    IsImmersion (splitChangedFamilyChart f hL d V c k s) :=
  inferInstanceAs (IsImmersion
    (SchemeSplitSeedGroundComparison.splitChart w i s k.left (H).hom hk ≫
      (splitChangedGroundParameterIso f hL d V c k s).hom ≫
        (variableHilbertCanonicalGroundIso f a hL d V).inv))

@[reassoc]
theorem splitChangedFamilyChart_old : splitChangedFamilyChart f hL d V c k s ≫ (P).left =
    SchemeSplitEtaleSourceSeed.toSource w s ≫ k.left := by
  simp only [splitChangedFamilyChart, Category.assoc, variableHilbertCanonicalGroundIso_old,
    splitChangedGroundParameterIso, pullback.congrHom_hom, pullback.lift_fst,
    Category.comp_id, SchemeSplitSeedGroundComparison.splitChart_old]

@[reassoc]
theorem splitChangedFamilyChart_new : splitChangedFamilyChart f hL d V c k s ≫
    (variableHilbertTest q d W).hom = SchemeSplitEtaleSourceSeed.projection w s := by
  simp only [splitChangedFamilyChart, Category.assoc, variableHilbertCanonicalGroundIso_new,
    splitChangedGroundParameterIso, pullback.congrHom_hom, pullback.lift_snd,
    Category.comp_id, SchemeSplitSeedGroundComparison.splitChart_new]

/-- Every seed point survives in the actual changed family with the prescribed two coordinates. -/
theorem splitChangedFamilyChart_point (z : Spec (.of R')) :
    (splitChangedFamilyChart f hL d V c k s ≫ (P).left)
        (SchemeSplitEtaleSourceSeed.seed w s z) = k.left (s z) ∧
    (splitChangedFamilyChart f hL d V c k s ≫ (variableHilbertTest q d W).hom)
        (SchemeSplitEtaleSourceSeed.seed w s z) = z := by
  constructor
  · rw [splitChangedFamilyChart_old]
    change k.left (SchemeSplitEtaleSourceSeed.toSource w s
      (SchemeSplitEtaleSourceSeed.seed w s z)) = k.left (s z)
    rw [SchemeSplitEtaleSourceSeed.seed_point]
  · rw [splitChangedFamilyChart_new]
    exact congrArg (fun g ↦ g z) (SchemeSplitEtaleSourceSeed.seed_projection w s)

local notation "h" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local notation "e" => equivalence f hL d V c k
local instance splitChangedFamilyKernelMono :
    Mono (pullback.lift (fst f hL d V c k).left (snd f hL d V c k).left h) :=
  modelRelationKernelMap_mono f hL d V c k w h

/-- Actual affine orbit selections map immersively to the freshly constructed family parameters. -/
theorem splitChangedFamilyAffine_isImmersion [Etale s]
    [FormallyUnramified (finiteKernelProjection f hL d V c k).left] (z : Spec (.of R')) :
    IsImmersion (SchemeRelationSplitOrbit.affineToOrbit e s z ≫
      SchemeRelationSplitOrbit.inclusion w h s ≫ splitChangedFamilyChart f hL d V c k s) := by
  let _ := SchemeRelationSplitOrbit.inclusion_isOpenImmersion w h s
  infer_instance

end FLT.Mazur.HilbertChart.AffineRestriction
