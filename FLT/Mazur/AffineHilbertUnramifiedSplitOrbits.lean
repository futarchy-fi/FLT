/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteModelUnramifiedInverses
public import FLT.Mazur.SchemeRelationSplitOrbitAffineSeed

/-!
# Initial split orbit models for unramified proper-family coefficients

Every original selected parameter point has a constructed seed after the
explicit coefficient base change by the entire original source. Its orbit is
an actual open with a split etale quotient. No old flatness, monic seed,
generic coverage, irreducibility or reducedness is assumed. Unramifiedness
of the original finite coefficient projection remains a geometric input.
This coefficient change is not asserted to be fppf over the old model.
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
local notation "h" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "e" => equivalence f hL d V c k
local instance splitOrbitKernelMono : Mono (pullback.lift (p).left (q).left h) :=
  modelRelationKernelMap_mono f hL d V c k w h
variable [FormallyUnramified (finiteKernelProjection f hL d V c k).left]
local notation "a" => 𝟙 A.left
local notation "U" => SchemeRelationSplitOrbit.sourceOpen w h a
local notation "π" => SchemeRelationSplitOrbit.openProjection w h a
local notation "s" => SchemeRelationSplitOrbit.openSection e w h a

/-- An actual open in the complete coefficient pullback, constructed through every source point. -/
def finiteModelSplitOrbitOpen : (SchemeSplitEtaleSourceSeed.source w a).Opens := U

/-- The quotient is the entire original source used as the new coefficient base. -/
def finiteModelSplitOrbitProjection : (finiteModelSplitOrbitOpen f hL d V c k).toScheme ⟶
    A.left := π

/-- The split orbit quotient is a surjective etale morphism of actual schemes. -/
theorem finiteModelSplitOrbit_cover :
    Etale (finiteModelSplitOrbitProjection f hL d V c k) ∧
      Surjective (finiteModelSplitOrbitProjection f hL d V c k) :=
  SchemeRelationSplitOrbit.openProjection_cover e w h a

/-- Every original parameter point is retained, together with its new coefficient coordinate. -/
theorem finiteModelSplitOrbit_exists_point (x : A.left) :
    ∃ z : (finiteModelSplitOrbitOpen f hL d V c k).toScheme,
      ((U).ι ≫ SchemeSplitEtaleSourceSeed.toSource w a) z = x ∧
        finiteModelSplitOrbitProjection f hL d V c k z = x := by
  refine ⟨s x, ?_, ?_⟩
  · have he : s ≫ (U).ι ≫ SchemeSplitEtaleSourceSeed.toSource w a = a := by
      rw [SchemeRelationSplitOrbit.openSection_ι_assoc,
        SchemeSplitEtaleSourceSeed.seed_toSource]
    exact congrArg (fun g ↦ g x) he
  · exact congrArg (fun g ↦ g x) (SchemeRelationSplitOrbit.openSection_projection e w h a)

/-- Original finite coefficients survive without changing or reducing their scheme. -/
@[reassoc]
theorem finiteModelSplitOrbit_coefficients :
    (U).ι ≫ SchemeSplitEtaleSourceSeed.toSource w a ≫ w =
      finiteModelSplitOrbitProjection f hL d V c k ≫ w := by
  simpa only [finiteModelSplitOrbitProjection, Category.id_comp] using
    SchemeRelationSplitOrbit.openProjection_oldCoefficient w h a

/-- Both original ground maps agree as scheme morphisms, not merely at points. -/
@[reassoc]
theorem finiteModelSplitOrbit_ground :
    (U).ι ≫ SchemeSplitEtaleSourceSeed.toSource w a ≫ A.hom =
      finiteModelSplitOrbitProjection f hL d V c k ≫ A.hom := by
  have he := congrArg (fun g ↦ g ≫ (finiteKernelModel f hL d V c k).hom)
    (finiteModelSplitOrbit_coefficients f hL d V c k)
  simpa only [Category.assoc, (finiteKernelProjection f hL d V c k).w] using he

local notation "r" => SchemeRelationSplitOrbit.fullComparison w h a
local notation "v" => pullback.snd (Over.Hom.left q) a
local notation "j" => Iso.hom (SchemeRelationSplitOrbit.sourceOpenIso w h a)

/-- The original relation with both changed endpoints is the actual kernel of this quotient. -/
theorem finiteModelSplitOrbit_isPullback : IsPullback
    ((r ≫ pullback.fst v v) ≫ j) ((r ≫ pullback.snd v v) ≫ j)
    (finiteModelSplitOrbitProjection f hL d V c k)
    (finiteModelSplitOrbitProjection f hL d V c k) :=
  SchemeRelationSplitOrbit.openRelation_isPullback e w h a

/-- Every original point has an actual affine open selection of the complete changed source. -/
theorem finiteModelSplitOrbit_affine (x : A.left) :
    IsAffine (SchemeRelationSplitOrbit.affineSource e a x) ∧
      IsOpenImmersion (SchemeRelationSplitOrbit.affineToOrbit e a x ≫
        SchemeRelationSplitOrbit.inclusion w h a) :=
  ⟨inferInstance, SchemeRelationSplitOrbit.affineSource_isOpenImmersion e a x w h⟩

omit [IsAffine A.left]
  [FormallyUnramified (finiteKernelProjection f hL d V c k).left] in
/-- The monic etale seed in that affine source is constructed without old coefficient flatness. -/
theorem finiteModelSplitOrbit_affine_seed (x : A.left) :
    Etale (SchemeRelationSplitOrbit.affineSeed e a x) ∧
      Etale (SchemeRelationSplitOrbit.affineSeed e a x ≫
        (SchemeRelationSplitOrbit.affineToOrbit e a x ≫ v)) ∧
      Mono (SchemeRelationSplitOrbit.affineSeed e a x ≫
        (SchemeRelationSplitOrbit.affineToOrbit e a x ≫ v)) :=
  SchemeRelationSplitOrbit.affineSeed_geometry e a x

end FLT.Mazur.HilbertChart.AffineRestriction
