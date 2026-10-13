/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkingEffectiveDescent

/-!
# The canonical marking section under effective full-family descent

The original vanishing section gives a section of the glued positive line.
The prescribed recovery returns exactly the section of the actual test
marking divisor, with the structure-sheaf unit comparison retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeMarkingDivisor completeFiberMarking completeMarkingLineBaseChangeIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  [Flat s] [Surjective s] [LocallyOfFinitePresentation s]
local notation "p" => pullback.fst (exactVeroneseProjToBase K n h) s

/-- The canonical vanishing section on the actually glued positive marking line. -/
def completeMarkingGluedSection :
    structureModule (exactVeroneseProj K n h) ⟶ (completeMarkingGluedLine K n h s).val :=
  divisorSectionMap (completeMarkingDivisor_relativeCartier K n h).1 ≫
    (completeMarkingDescentIso K n h s).hom.hom

/-- Recovery gives the actual test marking section, rather than a unit multiple. -/
theorem completeMarkingGluedSection_recovery :
    (Scheme.Modules.pullback p).map (completeMarkingGluedSection K n h s) ≫
      (completeMarkingGluedRecovery K n h s).hom.val =
        (modulePullbackUnitIso p).hom ≫
          divisorSectionMap (completeFiberMarkingDivisor_relativeCartier K n h s).1 := by
  rw [completeMarkingGluedSection, Functor.map_comp, Category.assoc,
    completeMarkingDescentIso_sheaf_recovery]
  exact (completeMarkingLineBaseChangeIso_section K n h s).section

/-- Identification back with the original line recovers the original vanishing section. -/
theorem completeMarkingGluedSection_original :
    completeMarkingGluedSection K n h s ≫ (completeMarkingDescentIso K n h s).inv.hom =
      divisorSectionMap (completeMarkingDivisor_relativeCartier K n h).1 := by
  change (_ ≫ _) ≫ _ = _
  rw [Category.assoc]
  have he := congrArg (fun f ↦ f.hom) (completeMarkingDescentIso K n h s).hom_inv_id
  change (completeMarkingDescentIso K n h s).hom.hom ≫
    (completeMarkingDescentIso K n h s).inv.hom = 𝟙 _ at he
  rw [he]
  exact Category.comp_id _

end FLT.Mazur.PolygonInfinitesimalStages
