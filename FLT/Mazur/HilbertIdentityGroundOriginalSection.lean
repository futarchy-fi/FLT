/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertIdentityGroundSourceIso

/-!
# Original Picard data on the identity-ground effective source

Transport the original base map and parameter through the constructed source
isomorphism. These are sections of the original relative Picard sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local instance : Algebra.FiniteType ℤ Γ(V.left, ⊤) :=
  AffineEtaleIdentityGroundBase.coefficient_finiteType V
local notation "a" => AffineEtaleIdentityGroundBase.base V
local notation "W" => AffineEtaleIdentityGroundBase.translation V
local notation "t" => AffineEtaleIdentityGroundBase.comparison V
local notation "q" => Limits.pullback.snd f a
local instance : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "u" => groundBaseSourceMap f a hL d V W t k
local notation "l" => groundBaseSourceChart f a hL d V W t k
local notation "h'" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "e" => variableChartEquivalenceRelation f hL d V c

local instance : IsIso (W).hom := inferInstanceAs (IsIso (𝟙 _))

/-- The effective affine source, now with its ORIGINAL coefficient map. -/
def identityGroundOriginalTest : Over (Spec (.of R)) :=
  Over.mk ((identityGroundQuotientSourceIso f hL d V c k).hom ≫ A.hom)

/-- Recover the original affine parameter source over the original base. -/
def identityGroundOriginalArrow : identityGroundOriginalTest f hL d V c k ⟶ A :=
  Over.homMk (identityGroundQuotientSourceIso f hL d V c k).hom

instance identityGroundOriginalArrow_isIso :
    IsIso (identityGroundOriginalArrow f hL d V c k) := by
  let _ : IsIso ((Over.forget _).map
      (identityGroundOriginalArrow f hL d V c k)) :=
    inferInstanceAs (IsIso (identityGroundQuotientSourceIso f hL d V c k).hom)
  exact isIso_of_reflects_iso _ (Over.forget _)

/-- The actual original Hilbert parameter, without changing the translation coordinate. -/
def identityGroundOriginalParameter :
    identityGroundOriginalTest f hL d V c k ⟶ variableHilbertTest f d V :=
  identityGroundOriginalArrow f hL d V c k ≫ k

/-- The original Picard section transported to the constructed effective affine source. -/
def identityGroundOriginalSection :
    (relativeFppfSheaf f).obj.obj (op (identityGroundOriginalTest f hL d V c k)) :=
  sectionAt f hL d V c (identityGroundOriginalParameter f hL d V c k)

/-- Transport retains exactly the original restricted Picard section. -/
theorem identityGroundOriginalSection_eq : identityGroundOriginalSection f hL d V c k =
    (relativeFppfSheaf f).obj.map (identityGroundOriginalArrow f hL d V c k).op
      (sectionAt f hL d V c k) := by
  simp only [identityGroundOriginalSection, identityGroundOriginalParameter, sectionAt,
    op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- The retained parameter is an actual open immersion of schemes. -/
instance identityGroundOriginalParameter_openImmersion :
    IsOpenImmersion (identityGroundOriginalParameter f hL d V c k).left := by
  change IsOpenImmersion ((identityGroundQuotientSourceIso f hL d V c k).hom ≫ k.left)
  infer_instance

end FLT.Mazur.HilbertChart.AffineRestriction
