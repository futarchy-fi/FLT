/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertChangedOrbitSource

/-!
# The rebuilt Picard relation on the complete changed orbit

Division of original arrows constructs the inverse kernel map in the freshly
changed family's own Picard relation. This proves effectivity on the complete
orbit, including nilpotents and both endpoints, without extracting an open.
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
local instance changedOrbitKernelSmooth : SmoothOfRelativeDimension 1 g :=
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

/-- The original division arrow lifts into the newly constructed family's full relation. -/
theorem changedOrbitKernel_lift : ∃! v : K ⟶ (D').left,
    v ≫ (p').left = x ∧ v ≫ (q').left = y ∧
      v ≫ (r).left = SchemeRelationSplitOrbit.kernelArrow e s :=
  fixedBaseRelationMap_scheme_lift f a hL d V W t c k l u
    (changedOrbitParameter_compat f hL d V c k s) x y
    (pullback.condition) (SchemeRelationSplitOrbit.kernelArrow e s)
    (SchemeRelationSplitOrbit.kernelArrow_fst e s)
    (SchemeRelationSplitOrbit.kernelArrow_snd e s)

/-- An actual inverse, built from original arrows on the entire scheme kernel. -/
def changedOrbitKernelInverse : K ⟶ (D').left :=
  (changedOrbitKernel_lift f hL d V c k s).choose

@[reassoc]
theorem changedOrbitKernelInverse_fst :
    changedOrbitKernelInverse f hL d V c k s ≫ (p').left = x :=
  (changedOrbitKernel_lift f hL d V c k s).choose_spec.1.1

@[reassoc]
theorem changedOrbitKernelInverse_snd :
    changedOrbitKernelInverse f hL d V c k s ≫ (q').left = y :=
  (changedOrbitKernel_lift f hL d V c k s).choose_spec.1.2.1

@[reassoc]
theorem changedOrbitKernelInverse_old : changedOrbitKernelInverse f hL d V c k s ≫
    (r).left = SchemeRelationSplitOrbit.kernelArrow e s :=
  (changedOrbitKernel_lift f hL d V c k s).choose_spec.1.2.2

/-- Both endpoints of every rebuilt relation arrow have the same literal new ground. -/
theorem changedOrbitRelation_ground : (p').left ≫ (B).hom = (q').left ≫ (B).hom :=
  (p').w.trans (q').w.symm

local notation "m" => modelRelationKernelMap g h d W c' l (Over.hom B)
  (changedOrbitRelation_ground f hL d V c k s)

/-- The rebuilt family's own Picard relation is the full ground kernel of the complete orbit. -/
def changedOrbitRelationKernelIso : (D').left ≅ K where
  hom := m
  inv := changedOrbitKernelInverse f hL d V c k s
  hom_inv_id := by
    apply (cancel_mono m).mp
    have hi : changedOrbitKernelInverse f hL d V c k s ≫ m = 𝟙 K := by
      apply pullback.hom_ext
      · rw [Category.assoc, modelRelationKernelMap_fst, changedOrbitKernelInverse_fst,
          Category.id_comp]
      · rw [Category.assoc, modelRelationKernelMap_snd, changedOrbitKernelInverse_snd,
          Category.id_comp]
    rw [Category.assoc, hi, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, modelRelationKernelMap_fst, changedOrbitKernelInverse_fst,
        Category.id_comp]
    · rw [Category.assoc, modelRelationKernelMap_snd, changedOrbitKernelInverse_snd,
        Category.id_comp]

/-- This Cartesian square uses the actual rebuilt relation, not a substitute relation. -/
theorem changedOrbitRelation_isPullback :
    IsPullback (p').left (q').left (B).hom (B).hom :=
  IsPullback.of_iso_pullback ⟨changedOrbitRelation_ground f hL d V c k s⟩
    (changedOrbitRelationKernelIso f hL d V c k s)
    (modelRelationKernelMap_fst g h d W c' l _ _)
    (modelRelationKernelMap_snd g h d W c' l _ _)

end FLT.Mazur.HilbertChart.AffineRestriction
