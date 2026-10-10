/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalSecantTripleAlgebra
public import FLT.Mazur.WeierstrassOrdinaryTripleSchemes
public import FLT.Mazur.WeierstrassAdditionStructure

/-!
# Reciprocal secant triple outputs on arbitrary common schemes

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

/-- Reciprocal secant outer outputs agree when the ordinary inner inputs match. -/
theorem reciprocalSecantTriple_commonScheme (b c : Bool)
    (f : X ⟶ Spec (additionChartRing W (ordinaryIndex b)))
    (g : X ⟶ Spec (additionChartRing W (ordinaryIndex c)))
    (h : X ⟶ Spec (additionChartRing W (reciprocalIndex false)))
    (k : X ⟶ Spec (additionChartRing W (reciprocalIndex false)))
    (hmid : f ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W b).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W c).toRingHom))
    (hleft : h ≫ Spec.map (CommRingCat.ofHom (reciprocalInputLeft W false).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom))
    (hthird : h ≫ Spec.map (CommRingCat.ofHom (reciprocalInputRight W false).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W c).toRingHom))
    (hfirst : k ≫ Spec.map (CommRingCat.ofHom (reciprocalInputLeft W false).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W b).toRingHom))
    (hright : k ≫ Spec.map (CommRingCat.ofHom (reciprocalInputRight W false).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W c).toRingHom)) :
    h ≫ Spec.map (CommRingCat.ofHom (reciprocalChartAddition W false).toRingHom) =
      k ≫ Spec.map (CommRingCat.ofHom (reciprocalChartAddition W false).toRingHom) := by
  let s := f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (additionChartRing W (ordinaryIndex b))))
  have hg := (ordinaryTriple_input_base
    (A := additionChartRing W (ordinaryIndex b))
    (B := additionChartRing W (ordinaryIndex c)) f g _ _ hmid).symm
  have hh := ordinaryTriple_input_base
    (A := additionChartRing W (reciprocalIndex false))
    (B := additionChartRing W (ordinaryIndex b)) h f _ _ hleft
  have hk := ordinaryTriple_input_base
    (A := additionChartRing W (reciprocalIndex false))
    (B := additionChartRing W (ordinaryIndex b)) k f _ _ hfirst
  let _ := specSectionAlgebra s
  apply specSectionAlgHom_compare
    (A := additionChartRing W (reciprocalIndex false))
    (B := additionChartRing W (reciprocalIndex false)) s h k hh hk
  exact reciprocalSecantTripleAlgebra W b c
    (specSectionAlgHom (A := additionChartRing W (ordinaryIndex b)) s f rfl)
    (specSectionAlgHom (A := additionChartRing W (ordinaryIndex c)) s g hg)
    (specSectionAlgHom (A := additionChartRing W (reciprocalIndex false)) s h hh)
    (specSectionAlgHom (A := additionChartRing W (reciprocalIndex false)) s k hk)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (ordinaryIndex b))
      (B := additionChartRing W (ordinaryIndex c))
      s f g rfl hg _ _ hmid)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (reciprocalIndex false))
      (B := additionChartRing W (ordinaryIndex b)) s h f hh rfl _ _ hleft)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (reciprocalIndex false))
      (B := additionChartRing W (ordinaryIndex c)) s h g hh hg _ _ hthird)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (reciprocalIndex false))
      (B := additionChartRing W (ordinaryIndex b)) s k f hk rfl _ _ hfirst)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (reciprocalIndex false))
      (B := additionChartRing W (ordinaryIndex c)) s k g hk hg _ _ hright)

end FLT.Mazur.WeierstrassIntegralChart
