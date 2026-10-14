/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertChangedOrbitKernel

/-!
# Comparing the rebuilt and original full orbit relations

The freshly changed family's relation is isomorphic to the full original
relation restricted along the complete orbit. The isomorphism preserves both
independent endpoints and the literal original relation arrow.
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
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "e" => equivalence f hL d V c k
local notation "π" => pullback.snd (Over.Hom.left q) s
local notation "b" =>
  SchemeRelationEtaleBranchPropagation.branch (Over.Hom.left p) (Over.Hom.left q) s
local notation "a" => s ≫ A.hom
local notation "g" => Limits.pullback.snd f a
local notation "W" => RelativeCoefficientBaseChange.target a (T := V)
local notation "t" => RelativeCoefficientBaseChange.toOld a (T := V)
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
local instance changedOrbitComparisonSmooth : SmoothOfRelativeDimension 1 g :=
  MorphismProperty.pullback_snd _ _ inferInstance

local notation "B" => changedOrbitSource f hL d V c k s
local notation "l" => changedOrbitParameter f hL d V c k s
local notation "u" => changedOrbitToOld f hL d V c k s
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "p'" => fst g h d W c' l
local notation "q'" => snd g h d W c' l
local notation "D'" => relation g h d W c' l
local notation "r" => fixedBaseRelationMap f a hL d V W t c k l u
  (changedOrbitParameter_compat f hL d V c k s)
local notation "K" => (pullback (Over.hom B) (Over.hom B) : Scheme)
local notation "x" => pullback.fst (Over.hom B) (Over.hom B)
local notation "y" => pullback.snd (Over.hom B) (Over.hom B)

local notation "w" => Over.Hom.left (finiteKernelProjection f hL d V c k)
local notation "hw" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local instance changedOrbitComparisonMono : Mono (pullback.lift (p).left (q).left hw) :=
  modelRelationKernelMap_mono f hL d V c k w hw
local notation "N" => changedOrbitRelationKernelIso f hL d V c k s
local notation "O" => SchemeRelationSplitOrbit.fullKernelIso e w hw s

/-- The actual rebuilt relation and the entire original orbit relation are isomorphic. -/
def changedOrbitOriginalRelationIso : (D').left ≅
    SchemeRelationSplitOrbit.fullRelation w hw s := N ≪≫ (O).symm

/-- The comparison keeps the full ground kernel with both independently varying endpoints. -/
@[reassoc]
theorem changedOrbitOriginalRelationIso_kernel :
    (changedOrbitOriginalRelationIso f hL d V c k s).hom ≫
      SchemeRelationSplitOrbit.fullComparison w hw s = (N).hom := by
  change ((N).hom ≫ (O).inv) ≫ (O).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The first original endpoint is the rebuilt relation's first endpoint. -/
@[reassoc]
theorem changedOrbitOriginalRelationIso_fst :
    (changedOrbitOriginalRelationIso f hL d V c k s).hom ≫
      SchemeRelationSplitOrbit.fullComparison w hw s ≫ x = (p').left := by
  rw [changedOrbitOriginalRelationIso_kernel_assoc]
  exact modelRelationKernelMap_fst g h d W c' l _ _

/-- The independently varying second original endpoint is preserved too. -/
@[reassoc]
theorem changedOrbitOriginalRelationIso_snd :
    (changedOrbitOriginalRelationIso f hL d V c k s).hom ≫
      SchemeRelationSplitOrbit.fullComparison w hw s ≫ y = (q').left := by
  rw [changedOrbitOriginalRelationIso_kernel_assoc]
  exact modelRelationKernelMap_snd g h d W c' l _ _

/-- The isomorphism preserves the actual original arrow, including its scheme structure. -/
@[reassoc]
theorem changedOrbitOriginalRelationIso_arrow :
    (changedOrbitOriginalRelationIso f hL d V c k s).hom ≫
      SchemeRelationSplitOrbit.fullArrow w hw s = (r).left := by
  change ((N).hom ≫ SchemeRelationSplitOrbit.kernelLift e w hw s) ≫
    SchemeRelationSplitOrbit.fullArrow w hw s = _
  rw [Category.assoc, SchemeRelationSplitOrbit.kernelLift_arrow,
    ← changedOrbitKernelInverse_old f hL d V c k s]
  change (N).hom ≫ (N).inv ≫ (r).left = _
  rw [Iso.hom_inv_id_assoc]

end FLT.Mazur.HilbertChart.AffineRestriction
