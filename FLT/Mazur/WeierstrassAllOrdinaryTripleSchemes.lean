/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAllOrdinaryTripleAlgebra
public import FLT.Mazur.WeierstrassOrdinaryTripleSchemes
public import FLT.Mazur.WeierstrassAdditionStructure

/-!
# Ordinary triple outputs on arbitrary common schemes

The actual chart algebra comparison descends through global sections. Matching
inputs force the same coefficient action, so the result needs no independent
base-compatibility hypotheses and applies to nonreduced source schemes.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

variable (W : WeierstrassCurve R)

/-- All ordinary outer outputs agree whenever their ordinary inner inputs match. -/
theorem allOrdinaryTriple_commonScheme (b c d e : Bool)
    (f : X ⟶ Spec (additionChartRing W (ordinaryIndex b)))
    (g : X ⟶ Spec (additionChartRing W (ordinaryIndex c)))
    (h : X ⟶ Spec (additionChartRing W (ordinaryIndex d)))
    (k : X ⟶ Spec (additionChartRing W (ordinaryIndex e)))
    (hmid : f ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W b).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W c).toRingHom))
    (hleft : h ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W d).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom))
    (hthird : h ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W d).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W c).toRingHom))
    (hfirst : k ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W e).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W b).toRingHom))
    (hright : k ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W e).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W c).toRingHom)) :
    h ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W d).toRingHom) =
      k ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W e).toRingHom) := by
  let s := f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (additionChartRing W (ordinaryIndex b))))
  have hg := (ordinaryTriple_input_base
    (A := additionChartRing W (ordinaryIndex b))
    (B := additionChartRing W (ordinaryIndex c)) f g _ _ hmid).symm
  have hh := ordinaryTriple_input_base
    (A := additionChartRing W (ordinaryIndex d))
    (B := additionChartRing W (ordinaryIndex b)) h f _ _ hleft
  have hk := ordinaryTriple_input_base
    (A := additionChartRing W (ordinaryIndex e))
    (B := additionChartRing W (ordinaryIndex b)) k f _ _ hfirst
  let _ := specSectionAlgebra s
  apply specSectionAlgHom_compare
    (A := additionChartRing W (ordinaryIndex d))
    (B := additionChartRing W (ordinaryIndex e)) s h k hh hk
  exact allOrdinaryTripleAlgebra W b c d e
    (specSectionAlgHom (A := additionChartRing W (ordinaryIndex b)) s f rfl)
    (specSectionAlgHom (A := additionChartRing W (ordinaryIndex c)) s g hg)
    (specSectionAlgHom (A := additionChartRing W (ordinaryIndex d)) s h hh)
    (specSectionAlgHom (A := additionChartRing W (ordinaryIndex e)) s k hk)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (ordinaryIndex b))
      (B := additionChartRing W (ordinaryIndex c))
      s f g rfl hg _ _ hmid)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (ordinaryIndex d))
      (B := additionChartRing W (ordinaryIndex b)) s h f hh rfl _ _ hleft)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (ordinaryIndex d))
      (B := additionChartRing W (ordinaryIndex c)) s h g hh hg _ _ hthird)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (ordinaryIndex e))
      (B := additionChartRing W (ordinaryIndex b)) s k f hk rfl _ _ hfirst)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (ordinaryIndex e))
      (B := additionChartRing W (ordinaryIndex c)) s k g hk hg _ _ hright)

end FLT.Mazur.WeierstrassIntegralChart
