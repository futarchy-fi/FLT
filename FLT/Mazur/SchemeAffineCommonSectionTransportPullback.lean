/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCommonSectionTransport
public import FLT.Mazur.SchemeDescentPairTransport
public import FLT.Mazur.SchemeAffineCoverRecoveryCompatibility

/-!
# Common-section transport between independent original source maps

The section recovers the descent transport between its original source
maps. Equality of the source maps is not required.
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

/-- Restricting transport along the common section retains both original source maps. -/
lemma commonCoverSection_transport {M : Y.Modules}
    (D : SchemeGeometricDescent.Data p M) :
    let ρ := C.commonBaseCrossRefinement C' f g w
    SchemeOverlapDiagonalChart.normalize ρ.leftChart.cover ρ.rightChart.cover
      (Spec.map (C.commonCoverSection f b hb C' g c hc))
      (Spec.map b ≫ C.cover) (Spec.map c ≫ C'.cover)
      (C.commonCoverSection_leftChart C' f g b c hb hc w)
      (C.commonCoverSection_rightChart C' f g b c hb hc w)
      M (D.transport ρ.leftChart.cover ρ.rightChart.cover ρ.covers_over) =
        D.transport (Spec.map b ≫ C.cover) (Spec.map c ≫ C'.cover)
          ((C.cover_spec_over f b hb).trans (w.trans (C'.cover_spec_over g c hc).symm)) := by
  exact D.transport_pullback _ _ _ _ _ _ _ _ _

end FLT.Mazur.SchemeAffineDescent.Chart
