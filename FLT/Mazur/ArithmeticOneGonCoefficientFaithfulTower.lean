/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonCoefficientAmpleTower
public import FLT.Mazur.ArithmeticOneGonCoefficientFaithful

/-!
# The whole arithmetic faithful chart satisfies the coefficient cocycle

The full-curve coefficient cocycle acts on the entire original faithful
parameter scheme. Every auxiliary label survives, and the comparison also
commutes with the arithmetic faithful-to-ample identification.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonGeneralizedCurve
open CyclicBoundaryParameter GeneralizedEllipticCurve CharacterSchemeBaseChange OneGonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] faithfulCurveTransportIso coefficientFaithfulToOriginal
variable {R : Type} [CommRing R] {u v : R}
  {hu : IsUnit (1 + 432 * u)} {hv : IsUnit (1 + 432 * v)}
  (e : curve u hu ≅ curve v hv) (n : ℕ) [NeZero n]

/-- Full curve transport commutes with the arithmetic faithful-to-ample identification. -/
@[reassoc] theorem faithfulToAmple_curveTransport :
    faithfulToAmple u hu n ≫ ampleCurveTransport e n =
      (faithfulCurveTransportIso e n).hom.left ≫ faithfulToAmple v hv n := by
  apply (cancel_mono (ampleParameterOpen (curve v hv) n).ι).mp
  simp only [Category.assoc, ampleCurveTransport_inclusion,
    faithfulToAmple_inclusion_assoc, faithfulToAmple_inclusion, Category.comp_id]

/-- Full curve composition gives the same actual faithful scheme map. -/
theorem faithfulCoefficientTransport_comp {S : Scheme}
    {E F G : GeneralizedEllipticCurve S}
    [IsSeparated E.group.hom] [IsSeparated F.group.hom] [IsSeparated G.group.hom]
    (a : E ≅ F) (b : F ≅ G) :
    (faithfulCurveTransportIso (a ≪≫ b) n).hom.left =
      (faithfulCurveTransportIso a n).hom.left ≫ (faithfulCurveTransportIso b n).hom.left :=
  (congrArg Over.Hom.left (faithfulCurveTransportIso_comp a b n)).symm

variable (A B C : Type) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  (t : A) (ht : IsUnit (1 + 432 * t))

local instance coefficientFaithfulTower_separated {S T : Scheme}
    (E : GeneralizedEllipticCurve S) [IsSeparated E.group.hom] (g : T ⟶ S) :
    IsSeparated (E.baseChange g).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.group.hom g))

/-- The actual iterated coefficient comparison retains the direct whole faithful parameter. -/
@[reassoc] theorem iteratedCoefficientFaithful_original :
    (faithfulCurveTransportIso (iteratedCoefficientIso A B C t ht) n).hom.left ≫
        faithfulBaseChangeToOriginal (baseMap B C) ((curve t ht).baseChange (baseMap A B)).group n ≫
          faithfulBaseChangeToOriginal (baseMap A B) (curve t ht).group n =
      coefficientFaithfulToOriginal (S := C) t ht n := by
  have he : iteratedCoefficientIso A B C t ht = coefficientIso (S := C) t ht ≪≫
      (curve t ht).baseChangeCompEqIso (baseMap A B) (baseMap B C) (baseMap A C)
        (coefficientTower_baseMap A B C).symm := Iso.ext (coefficientIso_tower A B C t ht)
  rw [he, faithfulCoefficientTransport_comp, Category.assoc, faithfulCurveTowerParameter_original]
  exact (coefficientFaithfulToOriginal.eq_def t ht n).symm

/-- Actual successive coefficient recovery agrees with direct recovery on the whole chart. -/
theorem coefficientFaithfulToOriginal_tower :
    (faithfulCurveTransportIso
        (parameterIso (IsScalarTower.algebraMap_apply A B C t)
          (coefficientParameter_isUnit (S := C) t ht)
          (coefficientParameter_isUnit (S := C) _ (coefficientParameter_isUnit (S := B) t ht)))
        n).hom.left ≫
      coefficientFaithfulToOriginal (S := C) (algebraMap A B t)
        (coefficientParameter_isUnit (S := B) t ht) n ≫
      coefficientFaithfulToOriginal (S := B) t ht n =
        coefficientFaithfulToOriginal (S := C) t ht n := by
  rw [coefficientFaithfulToOriginal.eq_def, coefficientFaithfulToOriginal.eq_def]
  simp only [Category.assoc]
  rw [← faithfulCurveTransportIso_baseChange_assoc]
  have he := iteratedCoefficientFaithful_original n A B C t ht
  rw [iteratedCoefficientIso_def, faithfulCoefficientTransport_comp,
    faithfulCoefficientTransport_comp] at he
  simpa only [Category.assoc] using he

end FLT.Mazur.ArithmeticOneGonGeneralizedCurve
