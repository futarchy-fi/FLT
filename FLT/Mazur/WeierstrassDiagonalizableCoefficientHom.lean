/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DiagonalizableProductScheme
public import FLT.Mazur.WeierstrassDiagonalizableDefect
public import FLT.Mazur.WeierstrassSmoothBaseGroupHom

/-!
# Original character homomorphisms over a coefficient extension

A homomorphism into the actual base-changed smooth group gives a point of the
original group on the extended character algebra. Its original coface defect
vanishes by the group law, with no choice of coordinates on the target.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.WeierstrassDiagonalizableDefect

open WeierstrassIntegralChart WeierstrassDividedDepth DiagonalizableCobar
open CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] productSchemeIso productEquiv

variable {R S G : Type} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup G]

/-- The source carries the original character Hopf group structure. -/
local instance : CommGrpObj (model S G) :=
  inferInstanceAs (CommGrpObj ((Spec (.of (AddMonoidAlgebra S G))).asOver (Spec (.of S))))

variable (W : WeierstrassCurve R)
  (f : CommGrp.mk (model S G) ⟶ originalSmoothBaseChangeGroup S W)

local notation "j" => f.hom.hom.hom.left ≫
  pullback.fst (integralSmoothStructure W)
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The original point underlying a character homomorphism over the extended coefficient base. -/
def coefficientHomPoint : Points W (AddMonoidAlgebra S G) :=
  Over.homMk (j) (by
      refine (smoothBaseGroupHom_structure W (CommGrp.mk (model S G)) f).trans ?_
      change Spec.map _ ≫ Spec.map _ = _
      rw [← Spec.map_comp]
      exact congrArg (fun a : R →+* AddMonoidAlgebra S G => Spec.map (CommRingCat.ofHom a))
        (IsScalarTower.algebraMap_eq R S (AddMonoidAlgebra S G)).symm)

/-- Every genuine extended group homomorphism has zero original character-coface defect. -/
theorem coefficientHomPoint_defect : defect W (coefficientHomPoint W f) = 1 := by
  apply div_eq_one.mpr
  apply Over.OverMorphism.ext
  have hm := congrArg ((productSchemeIso S G).hom ≫ ·)
    (smoothBaseGroupHom_mul W (CommGrp.mk (model S G)) f)
  have hd : (productSchemeIso S G).hom ≫ μ[model S G].left =
      Spec.map (CommRingCat.ofHom (diagonalMap S G).toRingHom) :=
by
    convert congrArg Over.Hom.left (productOverIso_mul S G) using 1 <;> rfl
  have hc : (Spec.map (CommRingCat.ofHom (firstMap S G).toRingHom) ≫ j) ≫
      integralSmoothStructure W =
        (Spec.map (CommRingCat.ofHom (secondMap S G).toRingHom) ≫ j) ≫
          integralSmoothStructure W := by
    rw [← productSchemeIso_fst S G, ← productSchemeIso_snd S G]
    simpa only [Category.assoc] using congrArg ((productSchemeIso S G).hom ≫ ·)
      (smoothBaseGroupHom_pair_condition W (CommGrp.mk (model S G)) f)
  have hl : (productSchemeIso S G).hom ≫
      pullback.lift (pullback.fst _ _ ≫ j) (pullback.snd _ _ ≫ j)
        (smoothBaseGroupHom_pair_condition W (CommGrp.mk (model S G)) f) =
      pullback.lift (Spec.map (CommRingCat.ofHom (firstMap S G).toRingHom) ≫ j)
        (Spec.map (CommRingCat.ofHom (secondMap S G).toRingHom) ≫ j) hc := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        productSchemeIso_fst_assoc, productSchemeIso_snd_assoc]
  change (productSchemeIso S G).hom ≫ μ[model S G].left ≫ (j) =
    (productSchemeIso S G).hom ≫ _ ≫ smoothFactorAddition W at hm
  rw [← Category.assoc, hd] at hm
  rw [← Category.assoc (productSchemeIso S G).hom _ (smoothFactorAddition W), hl] at hm
  exact hm.symm

end FLT.Mazur.WeierstrassDiagonalizableDefect
