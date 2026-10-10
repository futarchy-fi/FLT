/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCommonCoverSection
public import FLT.Mazur.SchemeDescentPairTransport

/-!
# Original transport along a common-cover section

The constructed section retains the two original maps into the source
scheme. When these maps agree, the normalized common-cover transport is
the identity by the original descent datum's diagonal law.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {A : CommRingCat.{u}} (f : C.baseRing ⟶ A) (g : C'.baseRing ⟶ A)
variable (b : C.coverRing ⟶ A) (c : C'.coverRing ⟶ A)
variable (hb : C.ringMap ≫ b = f) (hc : C'.ringMap ≫ c = g)
variable (w : Spec.map f ≫ C.base = Spec.map g ≫ C'.base)

/-- The section's first common-cover branch retains the original source map. -/
@[reassoc]
lemma commonCoverSection_leftChart :
    Spec.map (C.commonCoverSection f b hb C' g c hc) ≫
        (C.commonBaseCrossRefinement C' f g w).leftChart.cover =
      Spec.map b ≫ C.cover := by
  change _ ≫ (Spec.map (C.commonCoverLeft C' f g) ≫ C.cover) = _
  rw [← Category.assoc, commonCoverSection_spec_left]

/-- The section's second branch retains its independently prescribed source map. -/
@[reassoc]
lemma commonCoverSection_rightChart :
    Spec.map (C.commonCoverSection f b hb C' g c hc) ≫
        (C.commonBaseCrossRefinement C' f g w).rightChart.cover =
      Spec.map c ≫ C'.cover := by
  change _ ≫ (Spec.map (C.commonCoverRight C' f g) ≫ C'.cover) = _
  rw [← Category.assoc, commonCoverSection_spec_right]

/-- Equal original source maps force the common-cover transport to become the identity. -/
lemma commonCoverSection_transport_self {M : Y.Modules}
    (D : SchemeGeometricDescent.Data p M)
    (hs : Spec.map b ≫ C.cover = Spec.map c ≫ C'.cover) :
    let ρ := C.commonBaseCrossRefinement C' f g w
    SchemeOverlapDiagonalChart.normalize ρ.leftChart.cover ρ.rightChart.cover
      (Spec.map (C.commonCoverSection f b hb C' g c hc))
      (Spec.map b ≫ C.cover) (Spec.map b ≫ C.cover)
      (C.commonCoverSection_leftChart C' f g b c hb hc w)
      ((C.commonCoverSection_rightChart C' f g b c hb hc w).trans hs.symm)
      M (D.transport ρ.leftChart.cover ρ.rightChart.cover ρ.covers_over) = Iso.refl _ := by
  dsimp only
  rw [D.transport_pullback _ _ _ _ _ _ _ _ rfl, D.transport_self]

end FLT.Mazur.SchemeAffineDescent.Chart
