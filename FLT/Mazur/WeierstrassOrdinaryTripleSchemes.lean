/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryTripleAlgebra
public import FLT.Mazur.WeierstrassSpecSections
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

/-- Matching an affine input also matches the coefficient morphism. -/
theorem ordinaryTriple_input_base {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra R A] [Algebra R B] [Algebra R C]
    (f : X ⟶ Spec (.of A)) (g : X ⟶ Spec (.of B)) (a : C →ₐ[R] A) (b : C →ₐ[R] B)
    (h : f ≫ Spec.map (CommRingCat.ofHom a.toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom b.toRingHom)) :
    f ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      g ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  have hc := congrArg (fun t => t ≫ Spec.map (CommRingCat.ofHom (algebraMap R C))) h
  simpa only [Category.assoc, specAlgHom_structure] using hc

variable (W : WeierstrassCurve R)

/-- Both actual secant outer outputs agree whenever their ordinary inner inputs match. -/
theorem ordinaryTriple_commonScheme (b c : Bool)
    (f : X ⟶ Spec (additionChartRing W (ordinaryIndex b)))
    (g : X ⟶ Spec (additionChartRing W (ordinaryIndex c)))
    (h k : X ⟶ Spec (additionChartRing W (ordinaryIndex false)))
    (hmid : f ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W b).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W c).toRingHom))
    (hleft : h ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W false).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom))
    (hthird : h ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W false).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W c).toRingHom))
    (hfirst : k ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W false).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W b).toRingHom))
    (hright : k ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W false).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W c).toRingHom)) :
    h ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W false).toRingHom) =
      k ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W false).toRingHom) := by
  let s := f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (additionChartRing W (ordinaryIndex b))))
  have hg := (ordinaryTriple_input_base
    (A := additionChartRing W (ordinaryIndex b))
    (B := additionChartRing W (ordinaryIndex c)) f g _ _ hmid).symm
  have hh := ordinaryTriple_input_base
    (B := additionChartRing W (ordinaryIndex b)) h f _ _ hleft
  have hk := ordinaryTriple_input_base
    (B := additionChartRing W (ordinaryIndex b)) k f _ _ hfirst
  let _ := specSectionAlgebra s
  apply specSectionAlgHom_compare s h k hh hk
  exact ordinaryTripleAlgebra W b c
    (specSectionAlgHom (A := additionChartRing W (ordinaryIndex b)) s f rfl)
    (specSectionAlgHom (A := additionChartRing W (ordinaryIndex c)) s g hg)
    (specSectionAlgHom s h hh) (specSectionAlgHom s k hk)
    (specSectionAlgHom_comp_eq (A := additionChartRing W (ordinaryIndex b))
      (B := additionChartRing W (ordinaryIndex c))
      s f g rfl hg _ _ hmid)
    (specSectionAlgHom_comp_eq (B := additionChartRing W (ordinaryIndex b))
      s h f hh rfl _ _ hleft)
    (specSectionAlgHom_comp_eq (B := additionChartRing W (ordinaryIndex c))
      s h g hh hg _ _ hthird)
    (specSectionAlgHom_comp_eq (B := additionChartRing W (ordinaryIndex b))
      s k f hk rfl _ _ hfirst)
    (specSectionAlgHom_comp_eq (B := additionChartRing W (ordinaryIndex c))
      s k g hk hg _ _ hright)

end FLT.Mazur.WeierstrassIntegralChart
