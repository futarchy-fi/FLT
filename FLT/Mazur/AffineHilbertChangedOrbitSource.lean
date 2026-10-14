/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertChangedOrbitOpen
public import FLT.Mazur.AffineHilbertFixedBaseRelationSchemeLift

/-!
# The complete orbit in the actual changed family

The entire original orbit defines a relative parameter map for the freshly
changed proper family. Reflexivity retains every seed, without the ground-etale
neighborhood condition needed for an open Hilbert chart. This parameter map is
monic; it is not asserted to be an open immersion.
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
local instance changedOrbitSourceSmooth : SmoothOfRelativeDimension 1 g :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- The full original orbit, with its actual new ground map. -/
def changedOrbitSource : Over (Spec (.of R')) := Over.mk π

instance changedOrbitSource_etale : Etale (changedOrbitSource f hL d V c k s).hom :=
  inferInstanceAs (Etale π)

instance changedOrbitSource_surjective :
    Surjective (changedOrbitSource f hL d V c k s).hom :=
  SchemeRelationSplitOrbit.projection_surjective e s

/-- A genuine relative parameter map, without an unsupported openness assertion. -/
def changedOrbitParameter : changedOrbitSource f hL d V c k s ⟶
    variableHilbertTest g d W :=
  Over.homMk (changedOrbitChart f hL d V c k s)
    (changedOrbitChart_new f hL d V c k s)

instance changedOrbitParameter_mono : Mono (changedOrbitParameter f hL d V c k s).left :=
  inferInstanceAs (Mono (changedOrbitChart f hL d V c k s))

/-- The original source map retains the old ground coordinate as well. -/
def changedOrbitToOld : (Over.map a).obj (changedOrbitSource f hL d V c k s) ⟶ A :=
  Over.homMk b (by
    change (pullback.fst (q).left s ≫ (p).left) ≫ A.hom = π ≫ a
    rw [Category.assoc, (p).w, ← (q).w, ← Category.assoc,
      pullback.condition, Category.assoc])

/-- The parameter map satisfies the actual changed-family comparison square. -/
theorem changedOrbitParameter_compat : changedOrbitToOld f hL d V c k s ≫ k =
    (Over.map a).map (changedOrbitParameter f hL d V c k s) ≫ P :=
  Over.OverMorphism.ext (changedOrbitChart_old f hL d V c k s).symm

/-- Every original seed has a literal section in the complete relative orbit. -/
def changedOrbitSection : Spec (.of R') ⟶ (changedOrbitSource f hL d V c k s).left :=
  SchemeRelationSplitOrbit.sectionMap e s

omit [Algebra.FiniteType ℤ R'] [Etale V.hom] [IsAffine A.left]
  [IsOpenImmersion k.left] in
@[reassoc]
theorem changedOrbitSection_ground : changedOrbitSection f hL d V c k s ≫
    (changedOrbitSource f hL d V c k s).hom = 𝟙 _ :=
  SchemeRelationSplitOrbit.sectionMap_projection e s

omit [Algebra.FiniteType ℤ R'] [Etale V.hom] [IsAffine A.left]
  [IsOpenImmersion k.left] in
@[reassoc]
theorem changedOrbitSection_old : changedOrbitSection f hL d V c k s ≫
    (changedOrbitToOld f hL d V c k s).left = s :=
  SchemeRelationSplitOrbit.sectionMap_source e s

/-- All seed points survive with both their old parameter and new ground coordinate. -/
theorem changedOrbitSection_point (z : Spec (.of R')) :
    ((changedOrbitParameter f hL d V c k s).left ≫ (P).left)
        (changedOrbitSection f hL d V c k s z) = k.left (s z) ∧
      (changedOrbitSource f hL d V c k s).hom
        (changedOrbitSection f hL d V c k s z) = z := by
  constructor
  · change (changedOrbitSection f hL d V c k s ≫
      changedOrbitChart f hL d V c k s ≫ (P).left) z = _
    rw [changedOrbitChart_old]
    change ((changedOrbitSection f hL d V c k s ≫
      (changedOrbitToOld f hL d V c k s).left) ≫ k.left) z = _
    rw [changedOrbitSection_old]
    rfl
  · exact congrArg (fun v ↦ v z) (changedOrbitSection_ground f hL d V c k s)

end FLT.Mazur.HilbertChart.AffineRestriction
