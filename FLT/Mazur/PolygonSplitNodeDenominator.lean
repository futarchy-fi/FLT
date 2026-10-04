/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalAffineRefinement
public import FLT.Mazur.PolygonNodeAffineCharts

/-!
# Actual affine split-node opens avoiding the marked divisor

For each specified node, shrink its actual A-chart by a genuine principal
open inside the divisor complement. The coordinate ring is a localization of
A, not the ring of the unshrunk chart. Both two-gon indices remain available.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonNodeAffineCharts
open PolygonPinching PolygonNodePresentation PolygonNodeEqualizer PolygonCubicSections
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (hn₂ : 2 ≤ n) (i : Fin n) (x : Spec (.of K))

/-- A principal denominator avoiding the marks and nonzero at the split origin. -/
def splitDenominator : A (R := K) :=
  PrincipalAffineRefinement.denominator (splitChart K n hn p q h hn₂ i)
    (divisorComplement K n p a) (aOrigin K x)
    (splitChart_origin_mem K n hn p q h a hn₂ i x)

/-- The refined node chart with its actual localized coordinate ring. -/
def splitDenominatorChart :
    Spec (.of (Localization.Away (splitDenominator K n hn p q h a hn₂ i x))) ⟶ C.left :=
  PrincipalAffineRefinement.chart (splitChart K n hn p q h hn₂ i)
    (splitDenominator K n hn p q h a hn₂ i x)

instance splitDenominatorChart_isOpenImmersion :
    IsOpenImmersion (splitDenominatorChart K n hn p q h a hn₂ i x) := by
  unfold splitDenominatorChart
  infer_instance

/-- The chosen basic open contains the actual origin in Spec A. -/
lemma splitDenominator_origin_mem :
    aOrigin K x ∈ PrimeSpectrum.basicOpen (splitDenominator K n hn p q h a hn₂ i x) :=
  PrincipalAffineRefinement.mem_denominator _ _ _ _

/-- Every point of the refined chart avoids every marked divisor point. -/
lemma splitDenominatorChart_range_subset :
    Set.range (splitDenominatorChart K n hn p q h a hn₂ i x) ⊆
      divisorComplement K n p a :=
  PrincipalAffineRefinement.range_chart_subset _ _ _
    (PrincipalAffineRefinement.denominator_subset _ _ _ _)

/-- The specified polygon node is retained by the refinement. -/
lemma splitDenominatorChart_node_mem :
    (nodeι K n i ≫ q).left x ∈
      Set.range (splitDenominatorChart K n hn p q h a hn₂ i x) := by
  have hh := PrincipalAffineRefinement.mem_range_chart
    (splitChart K n hn p q h hn₂ i) _ (aOrigin K x)
    (splitDenominator_origin_mem K n hn p q h a hn₂ i x)
  change (aOrigin K ≫ splitChart K n hn p q h hn₂ i) x ∈ _ at hh
  rwa [splitChart_origin] at hh

/-- Regular functions on the refined image are exactly the specified localization of A. -/
def splitDenominatorSectionsIso :
    Γ(C.left, splitDenominatorChart K n hn p q h a hn₂ i x ''ᵁ ⊤) ≅
      CommRingCat.of (Localization.Away (splitDenominator K n hn p q h a hn₂ i x)) :=
  PrincipalAffineRefinement.sectionsIso _ _

end FLT.Mazur.PolygonNodeAffineCharts
