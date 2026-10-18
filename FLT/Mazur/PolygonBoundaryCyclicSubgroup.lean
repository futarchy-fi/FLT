/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryGroupSections
public import FLT.Mazur.RelativeCyclicSubgroupSmoothOpen
public import FLT.Mazur.PolygonGeneralizedCurve
public import FLT.Mazur.PolygonSmoothRelativeDimension

/-!
# Actual faithful cyclic subgroups on arbitrary polygon boundary tests

The rank of the cyclic marking is independent of the number of components.
Its actual section homomorphism constructs a finite etale subgroup, and its
generator is relative Cartier on the whole polygon, including for one-gons.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction CyclicBoundaryParameter GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (m : ℕ) [NeZero m] (hm : 0 < m)
  {C : Over (Spec (.of K))} (p : components K m ⟶ C) (q : nodes K m ⟶ C)
  (h : IsPushout (toComponents K m hm) (toNodes K m) p q)
local notation "E" => PolygonGeneralizedCurve.curve K m hm p q h

include h in
/-- The full split group of every specified polygon has relative dimension one. -/
theorem boundaryGroup_relativeDimension : SmoothOfRelativeDimension 1 (G K m).hom := by
  let _ := polygon_lfp K m hm p q h
  let _ := smoothPolygon_relativeDimension K m hm p q h
  let e := (Over.forget (Spec (.of K))).mapIso (smoothIso K m hm p q h).symm
  rw [← (smoothIso K m hm p q h).inv.w]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension 1) inferInstance e.hom

variable (n : ℕ) [NeZero n] {T : Scheme} (g : T ⟶ Spec (.of K))
  (f : Over.mk g ⟶ parameter (G K m) n)
  (hf : UniversallyDistinctSections.UniversallyDistinct
    (fun i : ZMod n ↦ cyclicSectionMarking (G K m) n g f (.ofAdd i)))
local notation "φ" => cyclicSectionMarking (G K m) n g f

/-- The original parameter's faithful cyclic sections cut out their actual finite subgroup. -/
def parameterSubgroup : ((E).baseChange g).FiniteSubgroup n :=
  ((E).baseChange g).relativeCyclicSubgroup φ hf

/-- The subgroup has its original component-one generator. -/
def parameterGenerator : 𝟙_ (Over T) ⟶ (parameterSubgroup K m hm p q h n g f hf).carrier :=
  ((E).baseChange g).relativeCyclicGenerator φ hf

/-- The actual generator retains the parameter's original cyclic section. -/
theorem parameterGenerator_inclusion :
    parameterGenerator K m hm p q h n g f hf ≫
      (parameterSubgroup K m hm p q h n g f hf).inclusion =
        markedSection (G K m) n g f (1, 1, .ofAdd 1) :=
  (((E).baseChange g).relativeCyclicGenerator_inclusion φ hf).trans
    (cyclicSectionMarking_apply (G K m) n g f (.ofAdd 1))

/-- The original subgroup is finite etale, for any cyclic rank and number of components. -/
theorem parameterSubgroup_etale :
    Etale (parameterSubgroup K m hm p q h n g f hf).carrier.hom :=
  ((E).baseChange g).relativeCyclicSubgroup_etale φ hf

/-- The generator presents the original relative Cartier divisor even on a one-gon. -/
theorem parameterGenerator_cartier :
    (parameterSubgroup K m hm p q h n g f hf).IsCartierGenerator
      (parameterGenerator K m hm p q h n g f hf) := by
  let _ := boundaryGroup_relativeDimension K m hm p q h
  let _ : SmoothOfRelativeDimension 1 ((E).baseChange g).group.hom :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) (G K m).hom g
      inferInstance
  exact ((E).baseChange g).relativeCyclicGenerator_smoothOpen_cartier φ hf

/-- The original parameter subgroup is cyclic across every singular polygon boundary. -/
theorem parameterSubgroup_isCyclic :
    (parameterSubgroup K m hm p q h n g f hf).IsCyclic :=
  (parameterGenerator_cartier K m hm p q h n g f hf).isCyclic _

end FLT.Mazur.PolygonCyclicBoundary
