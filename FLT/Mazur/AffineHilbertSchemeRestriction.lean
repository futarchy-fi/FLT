/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFullRelationRestriction
public import FLT.Mazur.SchemeRelationOverRestriction

/-!
# Scheme coordinates for the full restricted Hilbert relation

The existing equal-class relation is identified with the double scheme pullback.
The isomorphism preserves the original arrow, and its endpoint equations identify
exactly the same compatible regular functions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "p" => variableChartRelationFst f hL d V c
local notation "q" => variableChartRelationSnd f hL d V c
local notation "r" => fst f hL d V c k
local notation "s" => snd f hL d V c k

/-- The full Hilbert relation restriction in the scheme-level coordinates used for descent. -/
def fullSchemeDoubleIso : (relation f hL d V c k).left ≅
    SchemeRelationRestriction.doubleDomain (p).left (q).left k.left :=
  (Over.forget _).mapIso (fullDoubleIso f hL d V c k) ≪≫
    SchemeRelationRestriction.overDoubleIso p q k

@[reassoc]
theorem fullSchemeDoubleIso_fst : (fullSchemeDoubleIso f hL d V c k).hom ≫
    SchemeRelationRestriction.fst (p).left (q).left k.left = (r).left := by
  dsimp only [fullSchemeDoubleIso, Iso.trans_hom, Functor.mapIso_hom,
    SchemeRelationRestriction.overDoubleIso]
  rw [Category.assoc, SchemeRelationRestriction.overToDouble_fst]
  change (toFullDouble f hL d V c k ≫ fullDoubleFst f hL d V c k).left = _
  rw [toFullDouble_fst]

@[reassoc]
theorem fullSchemeDoubleIso_snd : (fullSchemeDoubleIso f hL d V c k).hom ≫
    SchemeRelationRestriction.snd (p).left (q).left k.left = (s).left := by
  dsimp only [fullSchemeDoubleIso, Iso.trans_hom, Functor.mapIso_hom,
    SchemeRelationRestriction.overDoubleIso]
  rw [Category.assoc, SchemeRelationRestriction.overToDouble_snd]
  change (toFullDouble f hL d V c k ≫ fullDoubleSnd f hL d V c k).left = _
  rw [toFullDouble_snd]

@[reassoc]
theorem fullSchemeDoubleIso_arrow : (fullSchemeDoubleIso f hL d V c k).hom ≫
    SchemeRelationRestriction.arrow (p).left (q).left k.left =
      (toFullRelation f hL d V c k).left := by
  dsimp only [fullSchemeDoubleIso, Iso.trans_hom, Functor.mapIso_hom,
    SchemeRelationRestriction.overDoubleIso]
  rw [Category.assoc, SchemeRelationRestriction.overToDouble_arrow]
  change (toFullDouble f hL d V c k ≫ fullDoubleArrow f hL d V c k).left = _
  simp only [toFullDouble, fullDoubleArrow, pullback.lift_fst_assoc, pullback.lift_fst]

/-- Compatibility on the scheme double pullback is exactly full Hilbert compatibility. -/
theorem fullScheme_compatible_iff (v : Γ(A.left, ⊤)) :
    v ∈ SchemeEffectiveEpiSections.compatibleFunctions
      (SchemeRelationRestriction.fst (p).left (q).left k.left)
      (SchemeRelationRestriction.snd (p).left (q).left k.left) ↔
        v ∈ SchemeEffectiveEpiSections.compatibleFunctions (r).left (s).left := by
  change _ = _ ↔ (r).left.appTop v = (s).left.appTop v
  constructor
  · intro h
    have h' := congrArg (fullSchemeDoubleIso f hL d V c k).hom.appTop h
    change ((fullSchemeDoubleIso f hL d V c k).hom ≫
      SchemeRelationRestriction.fst (p).left (q).left k.left).appTop v =
        ((fullSchemeDoubleIso f hL d V c k).hom ≫
          SchemeRelationRestriction.snd (p).left (q).left k.left).appTop v at h'
    simpa only [fullSchemeDoubleIso_fst, fullSchemeDoubleIso_snd] using h'
  · intro h
    apply SchemeEffectiveEpiSections.appTop_injective
      (fullSchemeDoubleIso f hL d V c k).hom
    change ((fullSchemeDoubleIso f hL d V c k).hom ≫
      SchemeRelationRestriction.fst (p).left (q).left k.left).appTop v =
        ((fullSchemeDoubleIso f hL d V c k).hom ≫
          SchemeRelationRestriction.snd (p).left (q).left k.left).appTop v
    simpa only [fullSchemeDoubleIso_fst, fullSchemeDoubleIso_snd] using h

/-- The compatible-function ring is unchanged by the actual geometric identification. -/
def fullSchemeFunctionEquiv : SchemeEffectiveEpiSections.compatibleFunctions
    (SchemeRelationRestriction.fst (p).left (q).left k.left)
    (SchemeRelationRestriction.snd (p).left (q).left k.left) ≃+*
      SchemeEffectiveEpiSections.compatibleFunctions (r).left (s).left :=
  RingEquiv.subringCongr (SetLike.ext fun v ↦ fullScheme_compatible_iff f hL d V c k v)

/-- The comparison changes only the equation, retaining the original regular function. -/
theorem fullSchemeFunctionEquiv_val (v : SchemeEffectiveEpiSections.compatibleFunctions
    (SchemeRelationRestriction.fst (p).left (q).left k.left)
    (SchemeRelationRestriction.snd (p).left (q).left k.left)) :
    (fullSchemeFunctionEquiv f hL d V c k v).val = v.val := rfl

end FLT.Mazur.HilbertChart.AffineRestriction
