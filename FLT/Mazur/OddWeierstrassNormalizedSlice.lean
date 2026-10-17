/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassNormalizedSliceRing
public import FLT.Mazur.OddWeierstrassAuxiliaryLevel

/-!
# The normalized slice of the full auxiliary marking scheme

Pull back the four frame equations to the original faithful level-three space.
This retains its order-three group equations, faithful open, and full scheme
basis. The construction does not replace that space by its affinization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj

namespace FLT.Mazur.OddWeierstrassParameter

open UniversalWeierstrass (Labels labels_pow)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Impose the four frame equations on the actual full auxiliary scheme. -/
def normalizedSlice : Scheme :=
  pullback levelThree.left.toSpecΓ (Spec.map (CommRingCat.ofHom normalizedSliceQuotient))

/-- The actual closed inclusion in the faithful auxiliary marking scheme. -/
def normalizedSliceInclusion : normalizedSlice ⟶ levelThree.left := pullback.fst _ _

instance normalizedSliceInclusion_closed : IsClosedImmersion normalizedSliceInclusion := by
  let _ : IsClosedImmersion (Spec.map (CommRingCat.ofHom normalizedSliceQuotient)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  change IsClosedImmersion (pullback.fst _ _)
  infer_instance

/-- The normalized slice keeps the original arithmetic parameter map. -/
def normalizedSliceOver : Over parameterBase :=
  Over.mk (normalizedSliceInclusion ≫ levelThree.hom)

/-- Forget only normalization, retaining the original complete auxiliary object. -/
def normalizedSliceToAuxiliary : normalizedSliceOver ⟶ levelThree :=
  Over.homMk normalizedSliceInclusion rfl

/-- The full normalized marking, as an actual group homomorphism of scheme sections. -/
def normalizedSliceMarking : Labels 3 →* (normalizedSliceOver ⟶ universalGroup) :=
  AuxiliaryLevel.markingOf universalGroup (Labels 3)
    (normalizedSliceToAuxiliary ≫ levelThreeInclusion)

/-- Every normalized marked section is killed by three in the actual group scheme. -/
theorem normalizedSliceMarking_three (a : Labels 3) : normalizedSliceMarking a ^ 3 = 1 := by
  rw [← map_pow, labels_pow, map_one]

/-- The full marking remains faithful after every nonempty test scheme. -/
theorem normalizedSliceMarking_faithful {U : Over parameterBase}
    (f : U ⟶ normalizedSliceOver) [Nonempty U.left] :
    Function.Injective (AuxiliaryLevel.markingOf universalGroup (Labels 3)
      (f ≫ normalizedSliceToAuxiliary ≫ levelThreeInclusion)) := by
  simpa only [Category.assoc] using
    levelThreeMarking_injective (f ≫ normalizedSliceToAuxiliary)

end FLT.Mazur.OddWeierstrassParameter
