/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedGroupIdealOperations
public import FLT.Mazur.OverPullbackLocalPushout

/-!
# Base change of full closed carriers

Equality of the actual pulled ideal gives a cartesian carrier comparison
before any group closure equation is imposed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.ClosedGroupIdeal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme.{u}} (G : Over S) (I : G.left.IdealSheafData) (g : T ⟶ S)
  (J : ((Over.pullback g).obj G).left.IdealSheafData)
  (h : I.comap (pullback.fst G.hom g) = J)

/-- The actual map of full closed subschemes induced by the ambient projection. -/
def carrierBaseChangeMap : J.subscheme ⟶ I.subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ (pullback.fst G.hom g)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr h.le)

/-- The map retains the original closed immersions. -/
@[reassoc] theorem carrierBaseChangeMap_inclusion :
    carrierBaseChangeMap G I g J h ≫ I.subschemeι =
      J.subschemeι ≫ pullback.fst G.hom g :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The closed carrier is cartesian over the original parameter scheme. -/
theorem carrierBaseChangeMap_isPullback :
    IsPullback (carrierBaseChangeMap G I g J h)
      (carrier ((Over.pullback g).obj G) J).hom (carrier G I).hom g := by
  have hc : IsPullback J.subschemeι (carrierBaseChangeMap G I g J h)
      (pullback.fst G.hom g) I.subschemeι := by
    apply isPullback_of_isClosedImmersion
    · exact (carrierBaseChangeMap_inclusion G I g J h).symm
    · simpa only [Scheme.IdealSheafData.ker_subschemeι] using h
  exact hc.flip.paste_vert (IsPullback.of_hasPullback G.hom g)

/-- Canonical comparison with pullback in the slice category. -/
def carrierBaseChangeIso :
    carrier ((Over.pullback g).obj G) J ≅ (Over.pullback g).obj (carrier G I) :=
  Over.isoMk (carrierBaseChangeMap_isPullback G I g J h).isoPullback
    (carrierBaseChangeMap_isPullback G I g J h).isoPullback_hom_snd

/-- Projection from the comparison is the original full closed-subscheme map. -/
@[reassoc] theorem carrierBaseChangeIso_fst :
    (carrierBaseChangeIso G I g J h).hom.left ≫ pullback.fst (carrier G I).hom g =
      carrierBaseChangeMap G I g J h :=
  (carrierBaseChangeMap_isPullback G I g J h).isoPullback_hom_fst

/-- Base change respects the inclusion before any subgroup equations vanish. -/
theorem carrierBaseChangeIso_inclusion :
    inclusion ((Over.pullback g).obj G) J =
      (carrierBaseChangeIso G I g J h).hom ≫ (Over.pullback g).map (inclusion G I) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    rw [carrierBaseChangeIso_fst_assoc]
    exact (carrierBaseChangeMap_inclusion G I g J h).symm
  · exact (Over.w _).trans (Over.w _).symm

end FLT.Mazur.ClosedGroupIdeal
