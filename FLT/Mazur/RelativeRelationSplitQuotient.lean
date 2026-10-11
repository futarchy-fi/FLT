/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantLocallyRinged

/-!
# Effective invariant quotients from actual split relation maps

A scheme map with a section represents the full invariant quotient when an
actual relation arrow joins each source point to its section representative.
The proof identifies locally ringed spaces, including their structure sheaves.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {A U T : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (g : U ⟶ T) (s : T ⟶ U)
  (hg : p ≫ g = q ≫ g) (hs : s ≫ g = 𝟙 T)
  (r : U ⟶ A) (hrp : r ≫ p = 𝟙 U) (hrq : r ≫ q = g ≫ s)

/-- The actual split relation has the prescribed target as its locally ringed coequalizer. -/
def splitLocallyRingedQuotientIso :
    locallyRingedQuotient (p := p) (q := q) ≅ T.left.toLocallyRingedSpace where
  hom := coequalizer.desc g.left.toLRSHom (congrArg (fun k ↦ k.left.toLRSHom) hg)
  inv := s.left.toLRSHom ≫ locallyRingedProjection (p := p) (q := q)
  hom_inv_id := by
    dsimp only [locallyRingedQuotient, locallyRingedProjection]
    apply coequalizer.hom_ext
    rw [coequalizer.π_desc_assoc, Category.comp_id]
    have h := congrArg (fun k ↦ r.left.toLRSHom ≫ k) (coequalizer.condition
      p.left.toLRSHom q.left.toLRSHom)
    have hp : r.left.toLRSHom ≫ p.left.toLRSHom = 𝟙 _ :=
      congrArg (fun k ↦ k.left.toLRSHom) hrp
    have hq : r.left.toLRSHom ≫ q.left.toLRSHom =
        g.left.toLRSHom ≫ s.left.toLRSHom := congrArg (fun k ↦ k.left.toLRSHom) hrq
    simpa only [← Category.assoc, hp, hq, Category.id_comp] using h.symm
  inv_hom_id := by
    dsimp only [locallyRingedProjection]
    rw [Category.assoc, coequalizer.π_desc]
    exact congrArg (fun k ↦ k.left.toLRSHom) hs

/-- The actual invariant orbit quotient is an effective scheme quotient. -/
def splitInvariantQuotientIso :
    invariantLocallyRingedSpace e ≅ T.left.toLocallyRingedSpace :=
  (invariantLocallyRingedIso e).symm ≪≫ splitLocallyRingedQuotientIso g s hg hs r hrp hrq

/-- The effective quotient comparison is induced by the original scheme map. -/
theorem splitInvariantQuotientIso_projection :
    invariantLocallyRingedProjection e ≫
        (splitInvariantQuotientIso e g s hg hs r hrp hrq).hom = g.left.toLRSHom := by
  simp only [invariantLocallyRingedProjection, splitInvariantQuotientIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact coequalizer.π_desc _ _

/-- The identified scheme carries exactly the original quotient's relative base map. -/
theorem splitInvariantQuotientIso_baseMap :
    (splitInvariantQuotientIso e g s hg hs r hrp hrq).hom ≫ T.hom.toLRSHom =
      invariantLocallyRingedBaseMap e := by
  let _ : Epi (invariantLocallyRingedProjection e) := by
    unfold invariantLocallyRingedProjection locallyRingedProjection
    infer_instance
  apply (cancel_epi (invariantLocallyRingedProjection e)).mp
  rw [← Category.assoc, splitInvariantQuotientIso_projection,
    invariantLocallyRingedProjection_baseMap]
  exact congrArg Scheme.Hom.toLRSHom (Over.w g)

end FLT.Mazur.RelativeRelationOrbit
