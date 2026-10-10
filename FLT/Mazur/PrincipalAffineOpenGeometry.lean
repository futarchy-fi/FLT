/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalAffineOpenCoordinates

/-!
# Geometric incidence for principal section coordinates

The spectrum of the principal-coordinate equivalence recovers the actual
affine open inclusion. This identifies the coordinate maps with the original
scheme atlas, including its scalar maps and geometric images.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicRees

namespace FLT.Mazur.Approximation

universe u

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (U W : X.affineOpens) (r : Γ(X, U.1)) (he : W.1 = X.basicOpen r)

/-- Principal coordinates retain the entire original geometric inclusion. -/
@[reassoc] theorem principalAffineOpenEquiv_spec :
    Spec.map (CommRingCat.ofHom (principalAffineOpenEquiv f U W r he).toRingHom) ≫
        PrincipalLocalizationSquare.inclusion r ≫ U.2.fromSpec = W.2.fromSpec := by
  have hmap : CommRingCat.ofHom (algebraMap Γ(X, U.1) (Localization.Away r)) ≫
      CommRingCat.ofHom (principalAffineOpenEquiv f U W r he).toRingHom =
        X.presheaf.map (homOfLE (he ▸ X.basicOpen_le r)).op := by
    ext s
    exact principalAffineOpenEquiv_numerator f U W r he s
  dsimp only [PrincipalLocalizationSquare.inclusion]
  rw [← Category.assoc, ← Spec.map_comp, hmap]
  exact U.2.map_fromSpec W.2 _

/-- The uniform unit-localized overlap chart has its original open as geometric image. -/
def affineOpenUnitChart : Spec (.of (Localization.Away (1 : Γ(X, W.1)))) ⟶ X :=
  Spec.map (CommRingCat.ofHom (affineOpenUnitEquiv f W).toRingHom) ≫ W.2.fromSpec

/-- The actual unit-localized overlap chart is an open immersion. -/
instance affineOpenUnitChart_isOpenImmersion : IsOpenImmersion (affineOpenUnitChart f W) := by
  let _ := chartAlgebra f W
  let _ : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
  change IsOpenImmersion
    ((Scheme.Spec.mapIso (affineOpenUnitEquiv f W).toRingEquiv.toCommRingCatIso.op).hom ≫
      W.2.fromSpec)
  exact IsOpenImmersion.comp _ W.2.fromSpec

/-- The image of the unit-localized chart is exactly the prescribed open. -/
theorem affineOpenUnitChart_opensRange : (affineOpenUnitChart f W).opensRange = W.1 := by
  let _ := chartAlgebra f W
  let _ : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
  change ((Scheme.Spec.mapIso
    (affineOpenUnitEquiv f W).toRingEquiv.toCommRingCatIso.op).hom ≫ W.2.fromSpec).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact W.2.opensRange_fromSpec

end FLT.Mazur.Approximation
