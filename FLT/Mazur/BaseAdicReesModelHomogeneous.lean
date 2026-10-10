/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelScalarRestriction
public import FLT.Mazur.BaseAdicReesModelSheafSum
public import FLT.Mazur.BaseAdicCohomologyFiltration
public import FLT.Mazur.PowerScalarSectionCoordinates
public import FLT.Mazur.ReesAlgebraDirectSum

/-!
# Original homogeneous maps on the actual Rees model

Multiplication on the actual model carries each original degree inclusion
through the original power-sheaf scalar lift. The identity is checked on
the affine basis, retaining the original polynomial coefficients.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.BaseAdicThickening FLT.Mazur.Chow.AffineBase
open FLT.Mazur.IdealAdicQuotient
open scoped DirectSum

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{0}} {X : Scheme.{0}} (f : X ⟶ Spec R) (J : Ideal R)
  [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] modelPushforward modelPushforwardPowerSectionsIso

/-- On each affine chart the global degree inclusion is the original single coordinate. -/
lemma modelPowerInclusion_affine (n : ℕ) (V : X.affineOpens)
    (s : Γ(modelPowerSheaves f J M n, V.1)) :
    (modelPushforwardPowerSectionsIso f J M V).hom
      ((modelPowerInclusion f J M n).app V.1 s) =
      DirectSum.of (fun k ↦ Γ(modelPowerSheaves f J M k, V.1)) n s := by
  change (modelPushforwardPowerSectionsIso f J M V).hom
    ((AffineBasisSumMaps.ι _ _ (modelPowerBasisIso f J M) _ n).app V.1 s) = _
  rw [AffineBasisSumMaps.ι_app]
  exact (modelPushforwardPowerSectionsIso f J M V).inv_hom_id_apply _

/-- Homogeneous model multiplication is precisely the original power-sheaf scalar shift. -/
lemma modelPowerInclusion_reesEnd (a n : ℕ) (r : ↥(J ^ a)) :
    modelPowerInclusion f J M n ≫ modelReesEnd f J M (Rees.monomial J a r) =
      powerScalarMap (baseCohomologyScalars f) ((baseIdeal R J).comap f) M J
        (BaseAdicCohomology.scalar_mem f J) a n r ≫ modelPowerInclusion f J M (a + n) := by
  apply AffineBasisModuleMorphism.hom_ext
  intro V
  apply ConcreteCategory.hom_ext
  intro s
  apply (ConcreteCategory.bijective_of_isIso
    (modelPushforwardPowerSectionsIso f J M V).hom).injective
  change (modelPushforwardPowerSectionsIso f J M V).hom
    ((modelReesEnd f J M (Rees.monomial J a r)).app V.1
      ((modelPowerInclusion f J M n).app V.1 s)) =
    (modelPushforwardPowerSectionsIso f J M V).hom
      ((modelPowerInclusion f J M (a + n)).app V.1
        ((powerScalarMap (baseCohomologyScalars f) ((baseIdeal R J).comap f) M J
          (BaseAdicCohomology.scalar_mem f J) a n r).app V.1 s))
  let _ := IdealPowerRees.sectionsModule ((baseIdeal R J).comap f) M V
  rw [modelReesEnd_powerSections, modelPowerInclusion_affine, modelPowerInclusion_affine]
  unfold chartReesScalars Rees.monomial
  dsimp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Rees.algebraMap_monomial J _ _ _ a r r.property]
  exact powerScalarMap_sections (baseCohomologyScalars f) ((baseIdeal R J).comap f)
    M J (BaseAdicCohomology.scalar_mem f J) a n r V s

end FLT.Mazur.BaseAdicRees
