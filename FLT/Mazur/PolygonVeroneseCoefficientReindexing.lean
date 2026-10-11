/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonVeroneseMultipleInclusion
public import FLT.Mazur.PolygonVeroneseCoefficientMap

/-!
# Coefficient pullback commutes with common-step inclusions

Recomposition identifies both paths with the same original compatible section.
Thus passing to a common multiple retains the constructed coefficient map.
-/

@[expose] public noncomputable section
open scoped DirectSum
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] compatibleCoefficientMap compatibleEval
variable {R S : Type} [CommRing R] [CommRing S]
  (f : R →+* S) (n : ℕ) (h : 2 ≤ n) (q r : ℕ)

/-- Coefficient pullback on the direct sum retains the original compatible-section map. -/
theorem compatibleVeroneseCoefficientMap_recompose (s : CompatibleVeroneseSections R n h q) :
    compatibleVeroneseToSections S n h q (compatibleVeroneseCoefficientMap f n h q s) =
      compatibleCoefficientMap f n h (compatibleVeroneseToSections R n h q s) := by
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of d s =>
    rw [compatibleVeroneseCoefficientMap_of]
    change DirectSum.coeRingHom (compatibleVeroneseDegree S n h q)
      (DirectSum.of _ d (compatibleCoefficientDegreeMap f n h (q * d) s)) =
        compatibleCoefficientMap f n h
          (DirectSum.coeRingHom (compatibleVeroneseDegree R n h q) (DirectSum.of _ d s))
    rw [DirectSum.coeRingHom_of, DirectSum.coeRingHom_of]
    rfl
  | add s t hs ht => simp only [map_add, hs, ht]

variable [NeZero q]

/-- The ring inclusion keeps the original compatible section. -/
theorem multipleVeroneseInclusion_recompose (s : CompatibleVeroneseSections R n h (q * r)) :
    compatibleVeroneseToSections R n h q (multipleVeroneseInclusion R n h q r s) =
      compatibleVeroneseToSections R n h (q * r) s :=
  multipleVeroneseAddInclusion_recompose R n h q r s

/-- The original coefficient pullback commutes with the inclusion from a common step. -/
theorem compatibleVeroneseCoefficientMap_inclusion
    (s : CompatibleVeroneseSections R n h (q * r)) :
    compatibleVeroneseCoefficientMap f n h q (multipleVeroneseInclusion R n h q r s) =
      multipleVeroneseInclusion S n h q r (compatibleVeroneseCoefficientMap f n h (q * r) s) := by
  apply compatibleVeroneseToSections_injective S n h q (NeZero.pos q)
  rw [compatibleVeroneseCoefficientMap_recompose, multipleVeroneseInclusion_recompose,
    multipleVeroneseInclusion_recompose, compatibleVeroneseCoefficientMap_recompose]

/-- The coefficient square commutes as actual maps of the original retained rings. -/
theorem compatibleVeroneseCoefficientMap_inclusion_square :
    (compatibleVeroneseCoefficientMap f n h q).comp (multipleVeroneseInclusion R n h q r) =
      (multipleVeroneseInclusion S n h q r).comp
        (compatibleVeroneseCoefficientMap f n h (q * r)) := by
  apply RingHom.ext
  intro s
  exact compatibleVeroneseCoefficientMap_inclusion f n h q r s

end FLT.Mazur.PolygonInfinitesimalStages
