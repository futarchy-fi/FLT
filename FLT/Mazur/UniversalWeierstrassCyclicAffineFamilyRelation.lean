/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryAffineCubicIso
public import FLT.Mazur.UniversalWeierstrassCyclicLocalPresentationInvariant
public import FLT.Mazur.UniversalWeierstrassCyclicRelationOriginalMarking

/-!
# The genuine marked family relation on affine tests

An isomorphism of the original marked families induces the proper comparison
used in full normalization invariance. Conversely equal normalized parameters
construct an actual group isomorphism preserving every original full label.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicAuxiliaryScheme n).left)

/-- The actual original group families admit an isomorphism preserving every full label. -/
def CyclicMarkedFamilyRelated : Prop :=
  ∃ e : auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f) ≅
      auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n g),
    ∀ c : CyclicLabels n,
      cyclicSchemeOriginalMarking n f c ≫ e.hom.hom.hom.hom = cyclicSchemeOriginalMarking n g c

/-- Equality of the entire normalized parameter constructs a genuine marked family comparison. -/
theorem cyclicMarkedFamilyRelated_of_normalized_eq
    (h : cyclicSchemeNormalizedPoint n f = cyclicSchemeNormalizedPoint n g) :
    CyclicMarkedFamilyRelated n f g :=
  ⟨cyclicRelationFamilyIso n f g h, cyclicRelationFamilyIso_marking n f g h⟩

variable (e : (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f)).X ≅
  (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n g)).X)
  (hm : ∀ c : CyclicLabels n,
    cyclicSchemeOriginalMarking n f c ≫ e.hom = cyclicSchemeOriginalMarking n g c)

include hm in
/-- A full original marking comparison preserves the entire auxiliary submarking. -/
theorem cyclicFamilyIso_auxiliary_marking (c : Labels 4) :
    auxiliarySchemeMarking (cyclicSchemeAuxiliaryPoint n f) c ≫ e.hom =
      auxiliarySchemeMarking (cyclicSchemeAuxiliaryPoint n g) c := by
  rw [← cyclicSchemeOriginalMarking_auxiliary, ← cyclicSchemeOriginalMarking_auxiliary]
  exact hm (c, 1)

include hm in
/-- On an affine source every actual marked family comparison gives a proper presentation. -/
theorem cyclicProperPresentationRelated_of_affine_family_iso [IsAffine T] :
    CyclicProperPresentationRelated n f g := by
  let a := cyclicSchemeAuxiliaryPoint n f
  let b := cyclicSchemeAuxiliaryPoint n g
  have ha := cyclicFamilyIso_auxiliary_marking n f g e hm
  refine ⟨auxiliaryAffineCubicIso a b e, auxiliaryAffineCubicIso_base a b e,
    auxiliaryAffineCubicIso_zero a b e ha, auxiliaryAffineCubicIso_section a b e ha, ?_⟩
  intro c
  change ((cyclicSchemeOriginalMarking n f c).left ≫
    auxiliarySchemeOriginalCubicProjection a) ≫ _ =
      (cyclicSchemeOriginalMarking n g c).left ≫ auxiliarySchemeOriginalCubicProjection b
  rw [Category.assoc, auxiliaryAffineCubicIso_projection, ← Category.assoc, ← Over.comp_left,
    hm c]

/-- On affine sources the actual full marked family relation is exactly normalization equality. -/
theorem cyclicMarkedFamilyRelated_iff_normalized_eq [IsAffine T] :
    CyclicMarkedFamilyRelated n f g ↔
      cyclicSchemeNormalizedPoint n f = cyclicSchemeNormalizedPoint n g := by
  constructor
  · rintro ⟨e, hm⟩
    exact (cyclicProperPresentationRelated_of_affine_family_iso n f g
      ((CommGrp.forget (Over T)).mapIso e) hm).normalized_eq n
  · exact cyclicMarkedFamilyRelated_of_normalized_eq n f g

end FLT.Mazur.UniversalWeierstrass
