/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalTripleAlgebra
public import FLT.Mazur.WeierstrassOrdinaryTripleSchemes
public import FLT.Mazur.WeierstrassAdditionStructure

/-!
# Reciprocal triple outputs on arbitrary common schemes

Global sections transport the actual algebra-map comparison to every common
scheme domain, with no reducedness or affine-output assumptions.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

variable (W : WeierstrassCurve R)

/-- Reciprocal outer outputs agree when the ordinary inner inputs match. -/
theorem reciprocalTriple_commonScheme (b c d e : Bool)
    (f : X ⟶ Spec (additionChartRing W (ordinaryIndex b)))
    (g : X ⟶ Spec (additionChartRing W (ordinaryIndex c)))
    (h : X ⟶ Spec (additionChartRing W (reciprocalIndex d)))
    (k : X ⟶ Spec (additionChartRing W (reciprocalIndex e)))
    (hmid : f ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W b).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W c).toRingHom))
    (hleft : h ≫ Spec.map (CommRingCat.ofHom (reciprocalInputLeft W d).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom))
    (hthird : h ≫ Spec.map (CommRingCat.ofHom (reciprocalInputRight W d).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W c).toRingHom))
    (hfirst : k ≫ Spec.map (CommRingCat.ofHom (reciprocalInputLeft W e).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W b).toRingHom))
    (hright : k ≫ Spec.map (CommRingCat.ofHom (reciprocalInputRight W e).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W c).toRingHom)) :
    h ≫ Spec.map (CommRingCat.ofHom (reciprocalChartAddition W d).toRingHom) =
      k ≫ Spec.map (CommRingCat.ofHom (reciprocalChartAddition W e).toRingHom) := by
  let s := f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (additionChartRing W (ordinaryIndex b))))
  have hg := (ordinaryTriple_input_base
    (A := additionChartRing W (ordinaryIndex b))
    (B := additionChartRing W (ordinaryIndex c)) f g _ _ hmid).symm
  have hh := ordinaryTriple_input_base
    (A := additionChartRing W (reciprocalIndex d))
    (B := additionChartRing W (ordinaryIndex b)) h f _ _ hleft
  have hk := ordinaryTriple_input_base
    (A := additionChartRing W (reciprocalIndex e))
    (B := additionChartRing W (ordinaryIndex b)) k f _ _ hfirst
  let _ := specSectionAlgebra s
  apply specSectionAlgHom_compare
    (A := additionChartRing W (reciprocalIndex d))
    (B := additionChartRing W (reciprocalIndex e)) s h k hh hk
  exact reciprocalTripleAlgebra W b c d e
    (specSectionAlgHom (A := additionChartRing W (ordinaryIndex b)) s f rfl)
    (specSectionAlgHom (A := additionChartRing W (ordinaryIndex c)) s g hg)
    (specSectionAlgHom (A := additionChartRing W (reciprocalIndex d)) s h hh)
    (specSectionAlgHom (A := additionChartRing W (reciprocalIndex e)) s k hk)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (ordinaryIndex b))
      (B := additionChartRing W (ordinaryIndex c))
      s f g rfl hg _ _ hmid)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (reciprocalIndex d))
      (B := additionChartRing W (ordinaryIndex b)) s h f hh rfl _ _ hleft)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (reciprocalIndex d))
      (B := additionChartRing W (ordinaryIndex c)) s h g hh hg _ _ hthird)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (reciprocalIndex e))
      (B := additionChartRing W (ordinaryIndex b)) s k f hk rfl _ _ hfirst)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (reciprocalIndex e))
      (B := additionChartRing W (ordinaryIndex c)) s k g hk hg _ _ hright)

end FLT.Mazur.WeierstrassIntegralChart
