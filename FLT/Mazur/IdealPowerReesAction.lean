/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealPowerReesChart
public import Mathlib.Algebra.Module.TransferInstance

/-!
# The Rees action on all actual affine power sections

Transport polynomial convolution through the original power inclusions.
This gives a finite module on the full direct sum, with restrictions
semilinear over the actual Rees ring maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.GlobalIdealPower

universe u

namespace FLT.Mazur.IdealPowerRees

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]
  (V : X.affineOpens)

/-- The polynomial Rees action on the full direct sum of original power sections. -/
@[instance_reducible]
def sectionsModule : Module (reesAlgebra (I.ideal V)) (Sections I M V) :=
  (sectionsEquiv I M V).toAddEquiv.module _

/-- The original coordinate equivalence is linear for the constructed Rees action. -/
def sectionsReesEquiv :
    let _ := sectionsModule I M V
    Sections I M V ≃ₗ[reesAlgebra (I.ideal V)] affineModule I M V :=
  (sectionsEquiv I M V).toAddEquiv.linearEquiv _

/-- The constructed action is exactly polynomial convolution in the original inclusions. -/
lemma sectionsModule_smul (r : reesAlgebra (I.ideal V)) (s : Sections I M V) :
    let _ := sectionsModule I M V
    sectionsEquiv I M V (r • s) = r • sectionsEquiv I M V s :=
  (sectionsReesEquiv I M V).map_smul r s

/-- All actual affine power sections form a finite module over the local Rees algebra. -/
theorem sectionsModule_finite :
    let _ := sectionsModule I M V
    Module.Finite (reesAlgebra (I.ideal V)) (Sections I M V) := by
  let _ := sectionsModule I M V
  let _ := affineModule_finite I M V
  exact Module.Finite.equiv (sectionsReesEquiv I M V).symm

/-- The original power restrictions are semilinear for the constructed Rees actions. -/
lemma chartRestriction_smul {U : X.affineOpens} (h : U.1 ≤ V.1)
    (r : reesAlgebra (I.ideal V)) (s : Sections I M V) :
    let _ := sectionsModule I M V
    let _ := sectionsModule I M U
    chartRestriction I M V h le_rfl (homOfLE h) (r • s) =
      ringRestriction I h r • (show Sections I M U from
        chartRestriction I M V h le_rfl (homOfLE h) s) := by
  let _ := sectionsModule I M V
  let _ := sectionsModule I M U
  apply (sectionsEquiv I M U).injective
  change chartEquiv I M V U h (chartRestriction I M V h le_rfl (homOfLE h) (r • s)) = _
  rw [chartEquiv_restriction]
  change moduleRestriction I M h (sectionsEquiv I M V (r • s)) = _
  rw [sectionsModule_smul, map_smulₛₗ, sectionsModule_smul]
  congr 1
  exact (chartEquiv_restriction I M V h le_rfl h s).symm

end FLT.Mazur.IdealPowerRees
