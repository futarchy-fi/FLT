/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedGroupIdealCarrierBaseChange

/-!
# Cartesian base change of the closed carrier product

The monoidal comparison preserves the ambient multiplication on the entire
closed product, without assuming that it already defines a subgroup.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
universe u
namespace FLT.Mazur.ClosedGroupIdeal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme.{u}} (G : Over S)
  (I : G.left.IdealSheafData) (g : T ⟶ S)
  (J : ((Over.pullback g).obj G).left.IdealSheafData)
  (h : I.comap (pullback.fst G.hom g) = J)

/-- The whole closed product is the monoidal pullback of the original product. -/
def productBaseChangeIso :
    carrier ((Over.pullback g).obj G) J ⊗ carrier ((Over.pullback g).obj G) J ≅
      (Over.pullback g).obj (carrier G I ⊗ carrier G I) :=
  (carrierBaseChangeIso G I g J h ⊗ᵢ carrierBaseChangeIso G I g J h) ≪≫
    Functor.Monoidal.μIso (Over.pullback g) (carrier G I) (carrier G I)

/-- The map on products retains the original projection to the old parameter family. -/
def productBaseChangeMap :
    (carrier ((Over.pullback g).obj G) J ⊗ carrier ((Over.pullback g).obj G) J).left ⟶
      (carrier G I ⊗ carrier G I).left :=
  (productBaseChangeIso G I g J h).hom.left ≫ pullback.fst (carrier G I ⊗ carrier G I).hom g

/-- The product comparison is cartesian over the parameter base. -/
theorem productBaseChangeMap_isPullback :
    IsPullback (productBaseChangeMap G I g J h)
      (carrier ((Over.pullback g).obj G) J ⊗ carrier ((Over.pullback g).obj G) J).hom
      (carrier G I ⊗ carrier G I).hom g := by
  have hw : productBaseChangeMap G I g J h ≫ (carrier G I ⊗ carrier G I).hom =
      (carrier ((Over.pullback g).obj G) J ⊗ carrier ((Over.pullback g).obj G) J).hom ≫ g := by
    rw [productBaseChangeMap, Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ g) (productBaseChangeIso G I g J h).hom.w
  exact IsPullback.of_iso_pullback ⟨hw⟩
    ((Over.forget T).mapIso (productBaseChangeIso G I g J h)) rfl
    (productBaseChangeIso G I g J h).hom.w

variable [CommGrpObj G]

/-- Base change preserves the full restricted ambient multiplication. -/
theorem productMap_baseChange :
    productMap ((Over.pullback g).obj G) J =
      (productBaseChangeIso G I g J h).hom ≫ (Over.pullback g).map (productMap G I) := by
  dsimp only [productMap]
  rw [carrierBaseChangeIso_inclusion G I g J h, ← tensorHom_comp_tensorHom, Category.assoc]
  change _ ≫ _ ≫ (Functor.LaxMonoidal.μ (Over.pullback g) G G ≫
    (Over.pullback g).map μ[G]) = _
  rw [Functor.LaxMonoidal.μ_natural_assoc, ← Functor.map_comp]
  rfl

/-- The scheme square retains the actual ambient multiplication map. -/
@[reassoc] theorem productBaseChangeMap_multiplication :
    productBaseChangeMap G I g J h ≫ (productMap G I).left =
      (productMap ((Over.pullback g).obj G) J).left ≫ pullback.fst G.hom g := by
  have hw := congrArg (fun a ↦ a.left ≫ pullback.fst G.hom g)
    (productMap_baseChange G I g J h)
  simpa only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst,
    productBaseChangeMap] using hw.symm

end FLT.Mazur.ClosedGroupIdeal
