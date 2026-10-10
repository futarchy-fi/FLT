/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupSpectrumAction
public import FLT.Mazur.SchemeFiniteGroupDescent

/-!
# Arbitrary-target descent from the spectrum of a fixed ring

The coordinate quotient of the actual spectrum action and the original
fixed-ring spectrum are canonically isomorphic. This transports the full
scheme-target universal property to the fixed-ring quotient used by tensor models.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteGroupQuotient

universe u
variable (G A : Type u) [Group G] [Finite G] [CommRing A] [MulSemiringAction G A]

/-- The coordinate quotient maps to the original fixed-ring spectrum by affine descent. -/
def fromCoordinateQuotient :
    SchemeFiniteGroupQuotient.quotient (spectrumAction G A) ⟶ affineQuotient G A :=
  (SchemeFiniteGroupQuotient.existsUnique_affine_desc (spectrumAction G A)
    (quotientMap G A) (spectrumAction_quotientMap G A)).choose

omit [Finite G] in
/-- The coordinate-to-ring comparison preserves the actual quotient maps. -/
@[reassoc]
lemma fromCoordinateQuotient_fac :
    SchemeFiniteGroupQuotient.quotientMap (spectrumAction G A) ≫
      fromCoordinateQuotient G A = quotientMap G A :=
  (SchemeFiniteGroupQuotient.existsUnique_affine_desc (spectrumAction G A)
    (quotientMap G A) (spectrumAction_quotientMap G A)).choose_spec.1

/-- The fixed-ring quotient maps to the coordinate quotient by the ring universal property. -/
def toCoordinateQuotient :
    affineQuotient G A ⟶ SchemeFiniteGroupQuotient.quotient (spectrumAction G A) :=
  (existsUnique_affine_desc G A
    (SchemeFiniteGroupQuotient.invariantCoordinates (spectrumAction G A))
    (SchemeFiniteGroupQuotient.quotientMap (spectrumAction G A))
    ((spectrumAction_invariant_iff G A _).mp
      (SchemeFiniteGroupQuotient.quotientMap_invariant (spectrumAction G A)))).choose

omit [Finite G] in
/-- The ring-to-coordinate comparison preserves the actual quotient maps. -/
@[reassoc]
lemma toCoordinateQuotient_fac :
    quotientMap G A ≫ toCoordinateQuotient G A =
      SchemeFiniteGroupQuotient.quotientMap (spectrumAction G A) :=
  (existsUnique_affine_desc G A
    (SchemeFiniteGroupQuotient.invariantCoordinates (spectrumAction G A))
    (SchemeFiniteGroupQuotient.quotientMap (spectrumAction G A))
    ((spectrumAction_invariant_iff G A _).mp
      (SchemeFiniteGroupQuotient.quotientMap_invariant (spectrumAction G A)))).choose_spec.1

/-- The actual invariant-coordinate and original fixed-ring quotients are isomorphic. -/
def coordinateQuotientIso :
    SchemeFiniteGroupQuotient.quotient (spectrumAction G A) ≅ affineQuotient G A where
  hom := fromCoordinateQuotient G A
  inv := toCoordinateQuotient G A
  hom_inv_id := by
    rw [← cancel_epi (SchemeFiniteGroupQuotient.quotientMap (spectrumAction G A)),
      fromCoordinateQuotient_fac_assoc, toCoordinateQuotient_fac, Category.comp_id]
  inv_hom_id := by
    obtain ⟨k, _, hk⟩ := existsUnique_affine_desc G A (invariantRing G A)
      (quotientMap G A) (actionMap_quotientMap G A)
    have h₁ := hk (toCoordinateQuotient G A ≫ fromCoordinateQuotient G A)
      (by
        dsimp only
        rw [toCoordinateQuotient_fac_assoc, fromCoordinateQuotient_fac])
    have h₂ := hk (𝟙 _) (Category.comp_id _)
    exact h₁.trans h₂.symm

/-- The fixed-ring quotient is an epimorphism for arbitrary scheme targets. -/
instance quotientMap_epi : Epi (quotientMap G A) := by
  rw [← fromCoordinateQuotient_fac]
  change Epi (SchemeFiniteGroupQuotient.quotientMap (spectrumAction G A) ≫
    (coordinateQuotientIso G A).hom)
  infer_instance

variable {Y : Scheme.{u}} (f : Spec (.of A) ⟶ Y)
variable (hf : ∀ g : G, actionMap G A g ≫ f = f)

/-- Every invariant morphism to any scheme descends through the actual fixed-ring spectrum. -/
def desc : affineQuotient G A ⟶ Y :=
  toCoordinateQuotient G A ≫ SchemeFiniteGroupQuotient.desc (spectrumAction G A) f
    ((spectrumAction_invariant_iff G A f).mpr hf)

/-- The descended scheme morphism factors the original map. -/
@[reassoc]
lemma desc_fac : quotientMap G A ≫ desc G A f hf = f := by
  unfold desc
  rw [toCoordinateQuotient_fac_assoc, SchemeFiniteGroupQuotient.desc_fac]

include hf in
/-- The fixed-ring quotient has the full categorical universal property. -/
theorem existsUnique_desc : ∃! k : affineQuotient G A ⟶ Y, quotientMap G A ≫ k = f := by
  refine ⟨desc G A f hf, desc_fac G A f hf, ?_⟩
  intro k hk
  rw [← cancel_epi (quotientMap G A), hk, desc_fac]

end FLT.Mazur.FiniteGroupQuotient
