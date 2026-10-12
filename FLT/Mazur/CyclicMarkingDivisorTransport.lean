/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingOrbitDivisor
public import FLT.Mazur.CompatibleSubgroupIdealIso

/-!
# Full curve comparisons preserve cyclic orbit divisors

All ideal factors are transported through the actual full curve isomorphism.
Consequently equal Cartier-generator markings determine compatible original
subgroups without etaleness or distinctness assumptions.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E F : GeneralizedEllipticCurve S} {n : ℕ}
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (ψ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ F.group))
  (e : E ≅ F) (h : ∀ i, φ i ≫ e.hom.group = ψ i)

include h in
/-- Transport of the full product ideal retains each occurrence of a repeated section. -/
theorem cyclicMarkingIdeal_transport :
    F.cyclicMarkingIdeal ψ = (E.cyclicMarkingIdeal φ).comap e.inv.curve.left := by
  have : IsProper E.curve.hom := E.family.family.1
  unfold cyclicMarkingIdeal
  rw [FCurve.idealSheaf_comap_prod]
  apply Finset.prod_congr rfl
  intro i _
  have : IsClosedImmersion (φ (.ofAdd (i.val : ZMod n)) ≫ E.inclusion).left :=
    FCurve.isClosedImmersion_section E.curve.hom _ (Over.w _)
  rw [← h _, Category.assoc, ← e.hom.inclusion, ← Category.assoc]
  exact FiniteSubgroup.ker_comp_iso (φ (.ofAdd (i.val : ZMod n)) ≫ E.inclusion).left
    ((Over.forget S).mapIso (curveIso e))

variable [NeZero n] (H J : E.FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} {Q : 𝟙_ (Over S) ⟶ J.carrier}
  (hP : H.IsCartierGenerator P) (hQ : J.IsCartierGenerator Q)

/-- Equal generator markings identify actual subgroup ideals, with all multiplicities. -/
theorem FiniteSubgroup.ideal_eq_of_generator_marking
    (h : H.generatorCurveMarking hP = J.generatorCurveMarking hQ) : H.ideal = J.ideal := by
  rw [← H.generatorCurveMarking_ideal E hP, ← J.generatorCurveMarking_ideal E hQ, h]

/-- The same marked orbit determines the original subgroup up to compatible isomorphism. -/
def FiniteSubgroup.compatibleIsoOfGeneratorMarking
    (h : H.generatorCurveMarking hP = J.generatorCurveMarking hQ) :
    FiniteSubgroup.CompatibleIso H J :=
  FiniteSubgroup.compatibleIsoOfIdealEq H J (H.ideal_eq_of_generator_marking J hP hQ h)

end FLT.Mazur.GeneralizedEllipticCurve
