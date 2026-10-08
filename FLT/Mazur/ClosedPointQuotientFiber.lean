/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicQuotientSpectrum
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Closed-point fibers as base-ideal closed subschemes

At a maximal prime the quotient ring is already the residue field. The resulting
comparison identifies the actual closed source with the scheme-theoretic fiber,
including its map to the total space.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.BaseAdicThickening

variable (R : CommRingCat.{u}) (p : Spec R) [p.asIdeal.IsMaximal]

/-- At a closed point, the affine quotient is the scheme's residue field. -/
def closedPointQuotientRingIso :
    CommRingCat.of (R ⧸ p.asIdeal) ≅ (Spec R).residueField p :=
  (RingEquiv.ofBijective (algebraMap (R ⧸ p.asIdeal) p.asIdeal.ResidueField)
    p.asIdeal.bijective_algebraMap_quotient_residueField).toCommRingCatIso ≪≫
      (Scheme.Spec.residueFieldIso R p).symm

/-- The quotient spectrum agrees with the actual residue-field spectrum. -/
def closedPointQuotientIso :
    Spec ((Spec R).residueField p) ≅ Spec (CommRingCat.of (R ⧸ p.asIdeal)) :=
  Scheme.Spec.mapIso (closedPointQuotientRingIso R p).op

@[reassoc (attr := simp)]
lemma closedPointQuotientIso_hom_map :
    (closedPointQuotientIso R p).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p.asIdeal)) =
        (Spec R).fromSpecResidueField p := by
  change Spec.map (closedPointQuotientRingIso R p).hom ≫ _ = _
  rw [← Spec.map_comp,
    ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R p,
    ← Spec.map_comp]
  congr 1

/-- The base ideal's closed subscheme is the closed-point spectrum, over the base. -/
def closedPointBaseIso :
    Spec ((Spec R).residueField p) ≅ (baseIdeal R p.asIdeal).subscheme :=
  closedPointQuotientIso R p ≪≫ quotientSpecIso R p.asIdeal

@[reassoc (attr := simp)]
lemma closedPointBaseIso_hom_ι :
    (closedPointBaseIso R p).hom ≫ (baseIdeal R p.asIdeal).subschemeι =
      (Spec R).fromSpecResidueField p := by
  simp [closedPointBaseIso]

/-- The closed source cut out by a maximal base ideal is the actual point fiber. -/
def closedSourceFiberIso {X : Scheme.{u}} (f : X ⟶ Spec R) :
    ((baseIdeal R p.asIdeal).comap f).subscheme ≅ f.fiber p :=
  (baseIdeal R p.asIdeal).comapIso f ≪≫
    asIso (pullback.map _ _ _ _ (𝟙 X) (closedPointBaseIso R p).inv (𝟙 _)
      (by simp) (by
        rw [← closedPointBaseIso_hom_ι R p, Iso.inv_hom_id_assoc, Category.comp_id]))

/-- The fiber comparison retains the original closed immersion. -/
@[reassoc (attr := simp)]
lemma closedSourceFiberIso_hom_ι {X : Scheme.{u}} (f : X ⟶ Spec R) :
    (closedSourceFiberIso R p f).hom ≫ f.fiberι p =
      ((baseIdeal R p.asIdeal).comap f).subschemeι := by
  simp [closedSourceFiberIso, Scheme.Hom.fiberι]

end FLT.Mazur.BaseAdicThickening
