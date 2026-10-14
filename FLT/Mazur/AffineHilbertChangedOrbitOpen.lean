/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertSplitChangedFamily
public import FLT.Mazur.SchemeOrbitOpenAffineSelection

/-!
# Genuine open Hilbert selections from the changed original orbit

The full original orbit maps monically to the freshly constructed changed
family parameters without old coefficient unramifiedness. Its maximal open
image is an actual relative Hilbert selection with a surjective etale scheme
quotient. Retained seeds are explicit; global coverage remains a separate task.
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
local notation "h" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "e" => equivalence f hL d V c k
local notation "π" => pullback.snd (Over.Hom.left q) s
local notation "a" => s ≫ A.hom
local notation "g" => Limits.pullback.snd f a
local notation "W" => RelativeCoefficientBaseChange.target a (T := V)
local notation "t" => RelativeCoefficientBaseChange.toOld a (T := V)
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
local notation "H" => variableHilbertTest g d W
local instance changedOrbitSmooth : SmoothOfRelativeDimension 1 g :=
  MorphismProperty.pullback_snd _ _ inferInstance
local instance changedOrbitKernelMono : Mono (pullback.lift (p).left (q).left h) :=
  modelRelationKernelMap_mono f hL d V c k w h

/-- Map the complete original orbit into freshly constructed changed-family parameters. -/
def changedOrbitChart : pullback (q).left s ⟶ (H).left :=
  SchemeRelationSplitOrbit.inclusion w h s ≫ splitChangedFamilyChart f hL d V c k s

instance changedOrbitChart_mono : Mono (changedOrbitChart f hL d V c k s) := by
  let _ := SchemeRelationSplitOrbit.inclusion_mono w h s
  exact inferInstanceAs (Mono
    (SchemeRelationSplitOrbit.inclusion w h s ≫ splitChangedFamilyChart f hL d V c k s))

@[reassoc]
theorem changedOrbitChart_old : changedOrbitChart f hL d V c k s ≫ (P).left =
    SchemeRelationEtaleBranchPropagation.branch (p).left (q).left s ≫ k.left := by
  rw [changedOrbitChart, Category.assoc, splitChangedFamilyChart_old,
    SchemeRelationSplitOrbit.inclusion_source_assoc]

@[reassoc]
theorem changedOrbitChart_new : changedOrbitChart f hL d V c k s ≫ (H).hom = π := by
  rw [changedOrbitChart, Category.assoc, splitChangedFamilyChart_new,
    SchemeRelationSplitOrbit.inclusion_projection]

local notation "j" => changedOrbitChart f hL d V c k s
local notation "U" => SchemeOrbitOpenSelection.parameterOpen s j
local notation "l" => MonomorphismOpenImage.lift j

/-- An actual relative source over the NEW ground, with its original scheme structure. -/
def changedOrbitOpenSource : Over (Spec (.of R')) := Over.mk ((U).ι ≫ (H).hom)

/-- This is a genuine open Hilbert selection for the freshly changed proper family. -/
def changedOrbitOpenChart : changedOrbitOpenSource f hL d V c k s ⟶ H :=
  Over.homMk (U).ι rfl

instance changedOrbitOpenChart_isOpenImmersion :
    IsOpenImmersion (changedOrbitOpenChart f hL d V c k s).left :=
  inferInstanceAs (IsOpenImmersion (U).ι)

/-- Its literal new ground morphism is the restricted original orbit projection. -/
theorem changedOrbitOpenSource_ground : (changedOrbitOpenSource f hL d V c k s).hom =
    SchemeOrbitOpenSelection.projection s j := by
  change (U).ι ≫ (H).hom = l ≫ π
  rw [← changedOrbitChart_new f hL d V c k s, ← Category.assoc,
    MonomorphismOpenImage.lift_comp]

/-- Every constructed open source is etale over the actual new ground.
This necessary geometry limits which original seeds can be retained. -/
instance changedOrbitOpenSource_etale :
    Etale (changedOrbitOpenSource f hL d V c k s).hom := by
  rw [changedOrbitOpenSource_ground]
  infer_instance

/-- Both original Hilbert parameters and all new ground coordinates survive the open selection. -/
@[reassoc]
theorem changedOrbitOpenChart_old : (changedOrbitOpenChart f hL d V c k s).left ≫ (P).left =
    l ≫ SchemeRelationEtaleBranchPropagation.branch (p).left (q).left s ≫ k.left := by
  change (U).ι ≫ (P).left = _
  rw [← MonomorphismOpenImage.lift_comp j, Category.assoc, changedOrbitChart_old]

/-- The selected source has a constructed surjective etale quotient onto an actual seed open. -/
theorem changedOrbitOpen_cover :
    Etale (SchemeOrbitOpenSelection.quotient s j) ∧
      Surjective (SchemeOrbitOpenSelection.quotient s j) := ⟨inferInstance, inferInstance⟩

/-- Every retained reflexive seed reaches the quotient, without assuming old unramifiedness. -/
theorem changedOrbitOpen_seed_coverage : SchemeOrbitOpenSelection.seedOpen e s j ≤
    SchemeOrbitOpenSelection.targetOpen s j :=
  SchemeOrbitOpenSelection.seedOpen_le_targetOpen e s j

attribute [local irreducible] changedOrbitChart SchemeOrbitOpenSelection.affineSource
  SchemeOrbitOpenSelection.affineToOpen SchemeOrbitOpenSelection.affineChart
  SchemeOrbitOpenSelection.seed SchemeOrbitOpenSelection.seedOpen

/-- An actual affine relative source through each retained seed in the changed family. -/
def changedOrbitAffineSource (z : (SchemeOrbitOpenSelection.seedOpen e s j).toScheme) :
    Over (Spec (.of R')) :=
  Over.mk (SchemeOrbitOpenSelection.affineToOpen e s j z ≫
    SchemeOrbitOpenSelection.projection s j)


instance changedOrbitAffineSource_isAffine
    (z : (SchemeOrbitOpenSelection.seedOpen e s j).toScheme) :
    IsAffine (changedOrbitAffineSource f hL d V c k s z).left :=
  inferInstanceAs (IsAffine (SchemeOrbitOpenSelection.affineSource e s j z))

/-- The constructed affine chart is a genuine relative Hilbert selection. -/
def changedOrbitAffineChart
    (z : (SchemeOrbitOpenSelection.seedOpen e s j).toScheme) :
    changedOrbitAffineSource f hL d V c k s z ⟶ H :=
  Over.homMk (SchemeOrbitOpenSelection.affineChart e s j z) (by
    change SchemeOrbitOpenSelection.affineChart e s j z ≫ (H).hom =
      SchemeOrbitOpenSelection.affineToOpen e s j z ≫ SchemeOrbitOpenSelection.projection s j
    rw [SchemeOrbitOpenSelection.affineChart, Category.assoc,
      ← changedOrbitOpenSource_ground f hL d V c k s]
    rfl)

instance changedOrbitAffineChart_isOpenImmersion
    (z : (SchemeOrbitOpenSelection.seedOpen e s j).toScheme) :
    IsOpenImmersion (changedOrbitAffineChart f hL d V c k s z).left :=
  inferInstanceAs (IsOpenImmersion (SchemeOrbitOpenSelection.affineChart e s j z))

/-- The original parameter morphism is preserved on the new affine Hilbert chart. -/
@[reassoc]
theorem changedOrbitAffineChart_old
    (z : (SchemeOrbitOpenSelection.seedOpen e s j).toScheme) :
    (changedOrbitAffineChart f hL d V c k s z).left ≫ (P).left =
      SchemeOrbitOpenSelection.affineToOpen e s j z ≫ l ≫
        SchemeRelationEtaleBranchPropagation.branch (p).left (q).left s ≫ k.left := by
  change SchemeOrbitOpenSelection.affineChart e s j z ≫ (P).left = _
  rw [SchemeOrbitOpenSelection.affineChart, Category.assoc]
  have he := changedOrbitOpenChart_old f hL d V c k s
  change (U).ι ≫ (P).left = _ at he
  rw [he]

end FLT.Mazur.HilbertChart.AffineRestriction
