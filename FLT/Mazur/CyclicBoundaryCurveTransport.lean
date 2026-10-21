/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryProjectionFaithfulness
public import FLT.Mazur.GeneralizedCurveCategory

/-!
# Faithful boundary parameters retain full curve isomorphisms

Transport all labels through the smooth-group part of a generalized-curve
isomorphism. Only cyclic faithfulness is imposed; the auxiliary labels stay
unrestricted. The construction is an isomorphism of the actual parameter schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E F : GeneralizedEllipticCurve S}
  [IsSeparated E.group.hom] [IsSeparated F.group.hom]
  (e : E ≅ F) (n : ℕ) [NeZero n]

/-- Transport every original label through the actual smooth-group comparison. -/
def curveTransportParameter {U : Over S} (f : U ⟶ parameter E.group n) :
    U ⟶ parameter F.group n :=
  AuxiliaryLevel.liftMarking F.group (Label n)
    ((IsMonHom.monoidHom e.hom.group U).comp (AuxiliaryLevel.markingOf E.group (Label n) f))

omit [IsSeparated E.group.hom] [IsSeparated F.group.hom] in
/-- The transported equation parameter retains each original label. -/
@[reassoc] theorem curveTransportParameter_value {U : Over S}
    (f : U ⟶ parameter E.group n) (a : Label n) :
    curveTransportParameter e n f ≫ AuxiliaryLevel.value F.group (Label n) a =
      f ≫ AuxiliaryLevel.value E.group (Label n) a ≫ e.hom.group :=
  AuxiliaryLevel.liftMarking_value _ _ _ _

omit [IsSeparated F.group.hom] in
/-- Transport preserves faithfulness of the cyclic factor over every test scheme. -/
theorem curveTransportParameter_faithful {U : Over S}
    (f : U ⟶ cyclicFaithfulParameter E.group n) :
    AuxiliaryLevel.UniversallyFaithful F.group (Multiplicative (ZMod n))
      (curveTransportParameter e n (f ≫ cyclicFaithfulInclusion E.group n) ≫
        cyclicProjection F.group n) := by
  intro V k hV a b hab
  apply cyclicFaithful_projection E.group n f V k hV
  change (k ≫ _ ≫ cyclicProjection F.group n) ≫ AuxiliaryLevel.value _ _ a =
    (k ≫ _ ≫ cyclicProjection F.group n) ≫ AuxiliaryLevel.value _ _ b at hab
  simp only [Category.assoc, cyclicProjection_value, curveTransportParameter_value] at hab
  have : Mono e.hom.group := inferInstanceAs (Mono (GeneralizedEllipticCurve.groupIso e).hom)
  change (k ≫ f ≫ cyclicFaithfulInclusion E.group n ≫ cyclicProjection E.group n) ≫
    AuxiliaryLevel.value _ _ a =
    (k ≫ f ≫ cyclicFaithfulInclusion E.group n ≫ cyclicProjection E.group n) ≫
      AuxiliaryLevel.value _ _ b
  apply (cancel_mono e.hom.group).mp
  simpa only [Category.assoc, cyclicProjection_value] using hab

/-- The entire transported parameter factors through the actual cyclically faithful open. -/
def faithfulCurveTransport {U : Over S} (f : U ⟶ cyclicFaithfulParameter E.group n) :
    U ⟶ cyclicFaithfulParameter F.group n :=
  projectionFaithfulLift F.group n
    (curveTransportParameter e n (f ≫ cyclicFaithfulInclusion E.group n))
    (curveTransportParameter_faithful e n f)

/-- Transport on the faithful open retains the actual equation parameter. -/
@[reassoc] theorem faithfulCurveTransport_inclusion {U : Over S}
    (f : U ⟶ cyclicFaithfulParameter E.group n) :
    faithfulCurveTransport e n f ≫ cyclicFaithfulInclusion F.group n =
      curveTransportParameter e n (f ≫ cyclicFaithfulInclusion E.group n) :=
  projectionFaithfulLift_inclusion _ _ _ _

/-- Each auxiliary and cyclic label is retained by the faithful transport. -/
@[reassoc] theorem faithfulCurveTransport_value {U : Over S}
    (f : U ⟶ cyclicFaithfulParameter E.group n) (a : Label n) :
    faithfulCurveTransport e n f ≫ cyclicFaithfulInclusion F.group n ≫
      AuxiliaryLevel.value F.group (Label n) a =
    f ≫ cyclicFaithfulInclusion E.group n ≫ AuxiliaryLevel.value E.group (Label n) a ≫
      e.hom.group := by
  rw [faithfulCurveTransport_inclusion_assoc, curveTransportParameter_value, Category.assoc]

/-- Faithful transport commutes with arbitrary changes of test scheme. -/
@[reassoc] theorem faithfulCurveTransport_natural {U V : Over S}
    (f : U ⟶ cyclicFaithfulParameter E.group n) (k : V ⟶ U) :
    k ≫ faithfulCurveTransport e n f = faithfulCurveTransport e n (k ≫ f) := by
  apply (cancel_mono (cyclicFaithfulInclusion F.group n)).mp
  apply AuxiliaryLevel.homScheme_ext
  intro a
  simp only [Category.assoc, faithfulCurveTransport_value]

/-- The inverse curve comparison restores all original parameter labels. -/
theorem faithfulCurveTransport_inverse {U : Over S}
    (f : U ⟶ cyclicFaithfulParameter E.group n) :
    faithfulCurveTransport e.symm n (faithfulCurveTransport e n f) = f := by
  apply (cancel_mono (cyclicFaithfulInclusion E.group n)).mp
  apply AuxiliaryLevel.homScheme_ext
  intro a
  simp only [Category.assoc, faithfulCurveTransport_value]
  rw [faithfulCurveTransport_value_assoc]
  have he : e.hom.group ≫ e.symm.hom.group = 𝟙 _ :=
    (GeneralizedEllipticCurve.groupIso e).hom_inv_id
  rw [he, Category.comp_id]

/-- The actual faithful boundary parameter is invariant under full curve isomorphisms. -/
def faithfulCurveTransportIso :
    cyclicFaithfulParameter E.group n ≅ cyclicFaithfulParameter F.group n where
  hom := faithfulCurveTransport e n (𝟙 _)
  inv := faithfulCurveTransport e.symm n (𝟙 _)
  hom_inv_id := by
    rw [faithfulCurveTransport_natural, Category.comp_id, faithfulCurveTransport_inverse]
  inv_hom_id := by
    rw [faithfulCurveTransport_natural, Category.comp_id]
    exact faithfulCurveTransport_inverse e.symm n (𝟙 _)

end FLT.Mazur.CyclicBoundaryParameter
