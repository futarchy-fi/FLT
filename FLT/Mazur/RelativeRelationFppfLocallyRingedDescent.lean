/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationFppfInvariantQuotient

/-!
# Fppf descent of morphisms to arbitrary locally ringed spaces

The constructed full invariant quotient comparison descends compatible maps
into arbitrary locally ringed targets. This supplies descent across comparison
covers before their quotient targets have been proved to be schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A U T : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (g : U ⟶ T)
  (H : IsPullback p q g g)
  [Flat g.left] [LocallyOfFinitePresentation g.left] [Surjective g.left]

/-- The abstract locally ringed coequalizer is the actual fppf target scheme. -/
def fppfLocallyRingedQuotientIso :
    locallyRingedQuotient (p := p) (q := q) ≅ T.left.toLocallyRingedSpace :=
  invariantLocallyRingedIso e ≪≫ fppfInvariantQuotientIso e g H

/-- The coequalizer comparison preserves the actual geometric projection. -/
@[reassoc]
theorem fppfLocallyRingedQuotientIso_projection :
    locallyRingedProjection (p := p) (q := q) ≫
      (fppfLocallyRingedQuotientIso e g H).hom = g.left.toLRSHom := by
  exact (Category.assoc _ _ _).symm.trans (fppfInvariantQuotientIso_projection e g H)

include e H in
/-- An actual fppf cover detects morphisms to any locally ringed target. -/
theorem fppfLocallyRinged_epi : Epi g.left.toLRSHom := by
  rw [← fppfLocallyRingedQuotientIso_projection e g H]
  dsimp only [locallyRingedProjection]
  infer_instance

variable {Z : LocallyRingedSpace.{u}} (a : U.left.toLocallyRingedSpace ⟶ Z)
  (ha : p.left.toLRSHom ≫ a = q.left.toLRSHom ≫ a)

/-- Descent of a compatible locally ringed morphism across the actual fppf cover. -/
def fppfLocallyRingedDescend : T.left.toLocallyRingedSpace ⟶ Z :=
  (fppfLocallyRingedQuotientIso e g H).inv ≫ coequalizer.desc a ha

/-- Descent recovers the original locally ringed morphism on the cover. -/
@[reassoc]
theorem fppfLocallyRingedDescend_projection :
    g.left.toLRSHom ≫ fppfLocallyRingedDescend e g H a ha = a := by
  rw [← fppfLocallyRingedQuotientIso_projection e g H]
  dsimp only [fppfLocallyRingedDescend]
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact coequalizer.π_desc _ _

/-- The descended locally ringed morphism is unique, including its structure-sheaf map. -/
theorem fppfLocallyRingedDescend_unique (b : T.left.toLocallyRingedSpace ⟶ Z)
    (hb : g.left.toLRSHom ≫ b = a) : b = fppfLocallyRingedDescend e g H a ha := by
  let _ := fppfLocallyRinged_epi e g H
  exact (cancel_epi g.left.toLRSHom).mp
    (hb.trans (fppfLocallyRingedDescend_projection e g H a ha).symm)

/-- Descent commutes with arbitrary locally ringed target maps. -/
theorem fppfLocallyRingedDescend_comp {Z' : LocallyRingedSpace.{u}} (b : Z ⟶ Z') :
    fppfLocallyRingedDescend e g H a ha ≫ b =
      fppfLocallyRingedDescend e g H (a ≫ b)
        (by rw [← Category.assoc, ha, Category.assoc]) := by
  apply fppfLocallyRingedDescend_unique
  rw [fppfLocallyRingedDescend_projection_assoc]

end FLT.Mazur.RelativeRelationOrbit
