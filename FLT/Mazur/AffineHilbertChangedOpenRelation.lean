/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertChangedOrbitKernel
public import FLT.Mazur.AffineHilbertGroundKernelRestriction

/-!
# The rebuilt relation on existing open orbit selections

W277's actual open Hilbert selections carry the newly changed family's FULL
Picard relation. Its kernel is the selected projection, so its scheme quotient
is effective for that rebuilt relation too. No additional coverage is claimed.
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
local instance changedOpenRelationSmooth : SmoothOfRelativeDimension 1 g :=
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

local notation "C" => changedOrbitOpenSource f hL d V c k s
local notation "j" => changedOrbitChart f hL d V c k s
local notation "l'" => changedOrbitOpenChart f hL d V c k s
local notation "p₁" => fst g h d W c' l'
local notation "q₁" => snd g h d W c' l'

/-- The existing selected open maps into the complete original orbit over the new ground. -/
def changedOrbitOpenToFull : C ⟶ B :=
  Over.homMk (MonomorphismOpenImage.lift j)
    (changedOrbitOpenSource_ground f hL d V c k s).symm

/-- Its parameter map is literally the existing open Hilbert chart. -/
theorem changedOrbitOpenToFull_parameter :
    changedOrbitOpenToFull f hL d V c k s ≫ l = l' :=
  Over.OverMorphism.ext (MonomorphismOpenImage.lift_comp j)

/-- The actual newly rebuilt Picard relation is the full selected ground kernel. -/
theorem changedOrbitOpenRelation_isPullback :
    IsPullback (p₁).left (q₁).left (C).hom (C).hom := by
  rw [← changedOrbitOpenToFull_parameter f hL d V c k s]
  exact groundKernelRestriction_isPullback g h d W c' l
    (changedOrbitRelation_isPullback f hL d V c k s)
    (changedOrbitOpenToFull f hL d V c k s)

/-- Passing to the actual image retains every rebuilt relation arrow, not just point orbits. -/
theorem changedOrbitOpenRelation_quotient_isPullback :
    IsPullback (p₁).left (q₁).left
      (SchemeOrbitOpenSelection.quotient s j) (SchemeOrbitOpenSelection.quotient s j) := by
  have hh := changedOrbitOpenRelation_isPullback f hL d V c k s
  rw [changedOrbitOpenSource_ground] at hh
  exact SchemeEtaleImageQuotient.isPullback _ hh

/-- Scheme maps invariant under the rebuilt relation descend to the entire selected quotient. -/
theorem changedOrbitOpenRelation_existsUnique_descend {Y : Scheme} (v : (C).left ⟶ Y)
    (hv : (p₁).left ≫ v = (q₁).left ≫ v) :
    ∃! v' : (SchemeOrbitOpenSelection.targetOpen s j).toScheme ⟶ Y,
      SchemeOrbitOpenSelection.quotient s j ≫ v' = v := by
  have hh := changedOrbitOpenRelation_isPullback f hL d V c k s
  rw [changedOrbitOpenSource_ground] at hh
  exact ⟨SchemeEtaleImageQuotient.descend _ hh v hv,
    SchemeEtaleImageQuotient.projection_descend _ hh v hv,
    fun v' hv' ↦ SchemeEtaleImageQuotient.descend_unique _ hh v hv v' hv'⟩

end FLT.Mazur.HilbertChart.AffineRestriction
