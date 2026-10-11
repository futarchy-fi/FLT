/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMultipleCoefficientProjMap
public import FLT.Mazur.PolygonCompatibleCoefficientScalars
public import FLT.Mazur.PolygonMultipleVeroneseStructuralMap
public import FLT.Mazur.GradedDegreeProjCoefficientStructure

/-!
# The complete coefficient morphism over the actual power-series map

Recomposition retains the original compatible coefficient substitution.
The resulting scalar identity proves the complete structural square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] compatibleCoefficientMap compatibleEval
variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (h : 2 ≤ n) (q : ℕ)

/-- Recomposition of the actual retained coefficient map keeps the original compatible map. -/
theorem compatibleVeroneseCoefficientMap_recompose (s : CompatibleVeroneseSections R n h q) :
    compatibleVeroneseToSections S n h q (compatibleVeroneseCoefficientMap f n h q s) =
      compatibleCoefficientMap f n h (compatibleVeroneseToSections R n h q s) := by
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of d s =>
    rw [compatibleVeroneseCoefficientMap_of]
    change DirectSum.coeRingHom _ (DirectSum.of _ d _) =
      compatibleCoefficientMap f n h (DirectSum.coeRingHom _ (DirectSum.of _ d s))
    rw [DirectSum.coeRingHom_of, DirectSum.coeRingHom_of]
    rfl
  | add s t hs ht => simp only [map_add, hs, ht]

variable [NeZero q]

/-- The retained coefficient map uses the original power-series coefficient homomorphism. -/
theorem compatibleVeroneseCoefficientMap_algebraMap (a : PowerSeries R) :
    compatibleVeroneseCoefficientMap f n h q
        (algebraMap (PowerSeries R) (CompatibleVeroneseSections R n h q) a) =
      algebraMap (PowerSeries S) (CompatibleVeroneseSections S n h q) (PowerSeries.map f a) := by
  apply compatibleVeroneseToSections_injective S n h q (NeZero.pos q)
  rw [compatibleVeroneseCoefficientMap_recompose]
  change compatibleCoefficientMap f n h
    (DirectSum.coeAlgHom (compatibleVeroneseDegree R n h q) (algebraMap (PowerSeries R) _ a)) =
      DirectSum.coeAlgHom (compatibleVeroneseDegree S n h q)
        (algebraMap (PowerSeries S) _ (PowerSeries.map f a))
  rw [AlgHom.commutes, AlgHom.commutes, compatibleCoefficientMap_algebraMap]

variable {K L : Type} [Field K] [Field L] (g : K →+* L) [NeZero n]
  (hK : exactVeroneseStep K n h ∣ q) (hL : exactVeroneseStep L n h ∣ q)

/-- The constructed global coefficient morphism lies over the actual power-series substitution. -/
@[reassoc]
theorem multipleCoefficientProjMap_toBase :
    multipleCoefficientProjMap g n h q hK hL ≫ multipleVeroneseToBase K n h q =
      multipleVeroneseToBase L n h q ≫ Spec.map (CommRingCat.ofHom (PowerSeries.map g)) :=
  GradedDegreeProjCoefficientStructure.map_toSpecBase _ _ _ 1
    (compatibleVeroneseCoefficientMap_mem_scaled g n h q) (PowerSeries.map g)
    (compatibleVeroneseCoefficientMap_algebraMap g n h q) Nat.zero_lt_one
    (coefficientImage_complete_cover g n h q hK hL)

end FLT.Mazur.PolygonInfinitesimalStages
