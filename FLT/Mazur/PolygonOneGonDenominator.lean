/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalAffineRefinement
public import FLT.Mazur.PolygonNodeAffineCharts

/-!
# An actual one-gon node open avoiding the marked point

The one-gon refinement localizes B, the equal-value subalgebra of K[X].
It retains the self-pinched node and avoids the actual marked divisor.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonNodeAffineCharts
open PolygonPinching PolygonNodePresentation PolygonCubicSections
variable (K : Type u) [Field K] (hn : 0 < 1)
  {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
  (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q)
  (a : Fin 1 → Kˣ) (x : Spec (.of K))

/-- A denominator in B, chosen inside the actual divisor complement. -/
def oneDenominator : B (R := K) :=
  PrincipalAffineRefinement.denominator (oneChart K hn p q h)
    (divisorComplement K 1 p a) (bOrigin K x)
    (oneChart_origin_mem K hn p q h a 0 x)

/-- The refined chart has coordinate ring B with the chosen denominator inverted. -/
def oneDenominatorChart :
    Spec (.of (Localization.Away (oneDenominator K hn p q h a x))) ⟶ C.left :=
  PrincipalAffineRefinement.chart (oneChart K hn p q h) (oneDenominator K hn p q h a x)

instance oneDenominatorChart_isOpenImmersion :
    IsOpenImmersion (oneDenominatorChart K hn p q h a x) := by
  unfold oneDenominatorChart
  infer_instance

/-- The identified endpoints lie in the selected basic open of Spec B. -/
lemma oneDenominator_origin_mem :
    bOrigin K x ∈ PrimeSpectrum.basicOpen (oneDenominator K hn p q h a x) :=
  PrincipalAffineRefinement.mem_denominator _ _ _ _

/-- The refined image excludes the marked divisor point. -/
lemma oneDenominatorChart_range_subset :
    Set.range (oneDenominatorChart K hn p q h a x) ⊆ divisorComplement K 1 p a :=
  PrincipalAffineRefinement.range_chart_subset _ _ _
    (PrincipalAffineRefinement.denominator_subset _ _ _ _)

/-- The actual specified self-pinched node remains in the image. -/
lemma oneDenominatorChart_node_mem (i : Fin 1) :
    (nodeι K 1 i ≫ q).left x ∈ Set.range (oneDenominatorChart K hn p q h a x) := by
  have hh := PrincipalAffineRefinement.mem_range_chart (oneChart K hn p q h) _
    (bOrigin K x) (oneDenominator_origin_mem K hn p q h a x)
  change (bOrigin K ≫ oneChart K hn p q h) x ∈ _ at hh
  rwa [oneChart_origin K hn p q h i] at hh

/-- The regular functions on the actual image form the specified localization of B. -/
def oneDenominatorSectionsIso :
    Γ(C.left, oneDenominatorChart K hn p q h a x ''ᵁ ⊤) ≅
      CommRingCat.of (Localization.Away (oneDenominator K hn p q h a x)) :=
  PrincipalAffineRefinement.sectionsIso _ _

end FLT.Mazur.PolygonNodeAffineCharts
