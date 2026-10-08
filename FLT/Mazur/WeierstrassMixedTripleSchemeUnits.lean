/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassMixedTripleAlgebraUnits
public import FLT.Mazur.WeierstrassOrdinaryTripleSchemes
public import FLT.Mazur.WeierstrassAdditionStructure

/-!
# Mixed outer outputs are affine on arbitrary common schemes

Global sections transport the scalar inverse to the original normalized reciprocal
output. Matching inputs suffice, without assumptions about the output coordinates.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

variable (W : WeierstrassCurve R)

/-- The right reciprocal output has unit z on every compatible common scheme. -/
theorem mixedRightReciprocalScheme_z_isUnit (b c d e : Bool)
    (f : X ⟶ Spec (additionChartRing W (ordinaryIndex b)))
    (g : X ⟶ Spec (additionChartRing W (ordinaryIndex c)))
    (h : X ⟶ Spec (additionChartRing W (ordinaryIndex d)))
    (k : X ⟶ Spec (additionChartRing W (reciprocalIndex e)))
    (hmid : f ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W b).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W c).toRingHom))
    (hleft : h ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W d).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom))
    (hthird : h ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W d).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W c).toRingHom))
    (hfirst : k ≫ Spec.map (CommRingCat.ofHom (reciprocalInputLeft W e).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W b).toRingHom))
    (hright : k ≫ Spec.map (CommRingCat.ofHom (reciprocalInputRight W e).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W c).toRingHom)) :
    IsUnit (specSectionHom k (reciprocalChartAddition W e (coord W 1 2))) := by
  let s := f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (additionChartRing W (ordinaryIndex b))))
  have hg := (ordinaryTriple_input_base
    (A := additionChartRing W (ordinaryIndex b))
    (B := additionChartRing W (ordinaryIndex c)) f g _ _ hmid).symm
  have hh := ordinaryTriple_input_base
    (A := additionChartRing W (ordinaryIndex d))
    (B := additionChartRing W (ordinaryIndex b)) h f _ _ hleft
  have hk := ordinaryTriple_input_base
    (A := additionChartRing W (reciprocalIndex e))
    (B := additionChartRing W (ordinaryIndex b)) k f _ _ hfirst
  let _ := specSectionAlgebra s
  exact mixedRightReciprocalAlgebra_z_isUnit W b c d e
    (specSectionAlgHom (A := additionChartRing W (ordinaryIndex b)) s f rfl)
    (specSectionAlgHom (A := additionChartRing W (ordinaryIndex c)) s g hg)
    (specSectionAlgHom (A := additionChartRing W (ordinaryIndex d)) s h hh)
    (specSectionAlgHom (A := additionChartRing W (reciprocalIndex e)) s k hk)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (ordinaryIndex b))
      (B := additionChartRing W (ordinaryIndex c))
      s f g rfl hg _ _ hmid)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (ordinaryIndex d))
      (B := additionChartRing W (ordinaryIndex b)) s h f hh rfl _ _ hleft)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (ordinaryIndex d))
      (B := additionChartRing W (ordinaryIndex c)) s h g hh hg _ _ hthird)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (reciprocalIndex e))
      (B := additionChartRing W (ordinaryIndex b)) s k f hk rfl _ _ hfirst)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (reciprocalIndex e))
      (B := additionChartRing W (ordinaryIndex c)) s k g hk hg _ _ hright)

/-- The left reciprocal output has unit z on every compatible common scheme. -/
theorem mixedLeftReciprocalScheme_z_isUnit (b c d e : Bool)
    (f : X ⟶ Spec (additionChartRing W (ordinaryIndex b)))
    (g : X ⟶ Spec (additionChartRing W (ordinaryIndex c)))
    (h : X ⟶ Spec (additionChartRing W (reciprocalIndex d)))
    (k : X ⟶ Spec (additionChartRing W (ordinaryIndex e)))
    (hmid : f ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W b).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W c).toRingHom))
    (hleft : h ≫ Spec.map (CommRingCat.ofHom (reciprocalInputLeft W d).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom))
    (hthird : h ≫ Spec.map (CommRingCat.ofHom (reciprocalInputRight W d).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W c).toRingHom))
    (hfirst : k ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W e).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W b).toRingHom))
    (hright : k ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W e).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W c).toRingHom)) :
    IsUnit (specSectionHom h (reciprocalChartAddition W d (coord W 1 2))) := by
  let s := f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (additionChartRing W (ordinaryIndex b))))
  have hg := (ordinaryTriple_input_base
    (A := additionChartRing W (ordinaryIndex b))
    (B := additionChartRing W (ordinaryIndex c)) f g _ _ hmid).symm
  have hh := ordinaryTriple_input_base
    (A := additionChartRing W (reciprocalIndex d))
    (B := additionChartRing W (ordinaryIndex b)) h f _ _ hleft
  have hk := ordinaryTriple_input_base
    (A := additionChartRing W (ordinaryIndex e))
    (B := additionChartRing W (ordinaryIndex b)) k f _ _ hfirst
  let _ := specSectionAlgebra s
  exact mixedLeftReciprocalAlgebra_z_isUnit W b c d e
    (specSectionAlgHom (A := additionChartRing W (ordinaryIndex b)) s f rfl)
    (specSectionAlgHom (A := additionChartRing W (ordinaryIndex c)) s g hg)
    (specSectionAlgHom (A := additionChartRing W (reciprocalIndex d)) s h hh)
    (specSectionAlgHom (A := additionChartRing W (ordinaryIndex e)) s k hk)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (ordinaryIndex b))
      (B := additionChartRing W (ordinaryIndex c))
      s f g rfl hg _ _ hmid)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (reciprocalIndex d))
      (B := additionChartRing W (ordinaryIndex b)) s h f hh rfl _ _ hleft)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (reciprocalIndex d))
      (B := additionChartRing W (ordinaryIndex c)) s h g hh hg _ _ hthird)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (ordinaryIndex e))
      (B := additionChartRing W (ordinaryIndex b)) s k f hk rfl _ _ hfirst)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (ordinaryIndex e))
      (B := additionChartRing W (ordinaryIndex c)) s k g hk hg _ _ hright)

end FLT.Mazur.WeierstrassIntegralChart
