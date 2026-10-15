/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticMarkedClosedFiber
public import FLT.Mazur.PolygonArithmeticSmoothDimensionOpen
public import FLT.Mazur.PolygonArithmeticSchemePointExt
public import FLT.Mazur.SmoothOpenSectionCartier

/-!
# The actual complete markings are relative Cartier divisors

Each original marked point is smooth on the closed polygon. Its relative-curve
neighborhood contains the whole complete section, since the coefficient base
is local. Smooth-section theory applies to the original section ideal.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] exactVeroneseProjToBase_lfp PolygonPinching.cyclic_lfp

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

local notation "K" => IsLocalRing.ResidueField A

/-- The original complete marking lies in a smooth relative-curve neighborhood. -/
theorem completeBaseMarking_exists_dimensionOpen (i : Fin n) :
    ∃ V : (exactVeroneseProj A π n h hne hgen).Opens,
      Set.range (completeBaseMarking A π hne hgen n h i) ⊆
        (V : Set (exactVeroneseProj A π n h hne hgen)) ∧
        SmoothOfRelativeDimension 1 (V.ι ≫ exactVeroneseProjToBase A π n h hne hgen) := by
  let x := PolygonMarkedSections.sectionMap K n (PolygonCyclicAtlas.normalization K n h)
    1 i (default : Spec (.of K))
  let _ : LocallyOfFinitePresentation (PolygonCyclicAtlas.polygon K n h).hom :=
    PolygonPinching.cyclic_lfp K n h
  have hx : x ∈ ((PolygonCyclicAtlas.polygon K n h).hom.smoothLocus :
      Set (PolygonCyclicAtlas.polygon K n h).left) := by
    rw [PolygonPinching.smooth_range K n (by omega)
      (PolygonCyclicAtlas.normalization K n h) (PolygonCyclicAtlas.nodes K n h)
      (PolygonCyclicPushout.isPushout K n h (by omega))]
    exact Set.mem_iUnion.mpr ⟨i, PolygonMarkedSections.section_mem_torus K n _ 1 i _⟩
  obtain ⟨V, hxV, hd⟩ := completeClosedSmooth_exists_dimensionOpen A π hne hgen n h x hx
  refine ⟨V, arithmeticPoint_range_subset A
    (completeBaseMarking A π hne hgen n h i) V ?_, hd⟩
  rw [completeBaseMarking_closedPoint_boundary]
  exact hxV

/-- Every original complete marking lies in the total family's smooth locus. -/
theorem completeBaseMarking_range_smoothLocus (i : Fin n) :
    Set.range (completeBaseMarking A π hne hgen n h i) ⊆
      ((exactVeroneseProjToBase A π n h hne hgen).smoothLocus :
        Set (exactVeroneseProj A π n h hne hgen)) := by
  obtain ⟨V, hV, hd⟩ := completeBaseMarking_exists_dimensionOpen A π hne hgen n h i
  let _ := hd
  let _ := SmoothOfRelativeDimension.smooth 1 (V.ι ≫ exactVeroneseProjToBase A π n h hne hgen)
  intro x hx
  have he := congrArg (fun U ↦ (⟨x, hV hx⟩ : V) ∈ U)
    (Scheme.Hom.preimage_smoothLocus_eq V.ι (exactVeroneseProjToBase A π n h hne hgen))
  rw [Scheme.Hom.smoothLocus_eq_top (V.ι ≫ exactVeroneseProjToBase A π n h hne hgen)] at he
  exact he.mpr trivial

/-- The actual complete marking ideal is a relative effective Cartier divisor. -/
theorem completeBaseMarking_relativeCartier (i : Fin n) :
    FCurve.RelativeEffectiveCartier (exactVeroneseProjToBase A π n h hne hgen)
      (completeBaseMarking A π hne hgen n h i).ker := by
  let _ := exactVeroneseProjToBase_isProper A π n h hne hgen
  obtain ⟨V, hV, hd⟩ := completeBaseMarking_exists_dimensionOpen A π hne hgen n h i
  let t := IsOpenImmersion.lift V.ι (completeBaseMarking A π hne hgen n h i)
    (by simpa only [Scheme.Opens.range_ι] using hV)
  have ht : t ≫ V.ι = completeBaseMarking A π hne hgen n h i :=
    IsOpenImmersion.lift_fac _ _ _
  have hs : t ≫ V.ι ≫ exactVeroneseProjToBase A π n h hne hgen = 𝟙 _ := by
    rw [← Category.assoc, ht, completeBaseMarking_toBase]
  have hc := FCurve.smoothOpenSectionCartier V.ι (exactVeroneseProjToBase A π n h hne hgen) t
    inferInstance hd inferInstance hs
  rwa [ht] at hc

end FLT.Mazur.PolygonArithmeticStages
