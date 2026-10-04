/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierCharts
public import FLT.Mazur.AffinePullbackIdeal
public import FLT.Mazur.IntegralClosedSupport

/-!
# Restricting a Cartier divisor to an integral component

A Cartier divisor pulls back to a Cartier divisor on an integral scheme when
its generic point avoids the divisor. In particular the restriction to a
reduced irreducible closed component is Cartier if the original support does
not contain that component. No flatness of the component immersion is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve

open CoherentDevissage

variable {X Y : Scheme.{u}} {I : X.IdealSheafData}

/-- Generic avoidance makes a Cartier equation remain regular on an integral source. -/
theorem EffectiveCartier.comap_of_integral (hI : EffectiveCartier I)
    (i : Y ⟶ X) [IsIntegral Y] (hi : i (genericPoint Y) ∉ I.support) :
    EffectiveCartier (I.comap i) := by
  intro y
  obtain ⟨U, hyU, a, _, hUa⟩ := hI (i y)
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyU (i ⁻¹ᵁ U.1).isOpen
  let b : Γ(Y, V) := i.appLE U V hVU a
  have hVb : (I.comap i).ideal ⟨V, hV⟩ = Ideal.span {b} := by
    rw [Scheme.IdealSheafData.ideal_comap I i U ⟨V, hV⟩ hVU, hUa,
      Ideal.map_span, Set.image_singleton]
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  refine ⟨⟨V, hV⟩, hyV, b, isRegular_iff_ne_zero.mpr ?_, hVb⟩
  intro hb
  have hg : genericPoint Y ∈ V := (genericPoint_spec Y).mem_open_set_iff V.isOpen |>.mpr
    ⟨y, trivial, hyV⟩
  apply hi
  have hs : genericPoint Y ∈ (I.comap i).support := by
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hg, hVb, hb,
      Ideal.span_singleton_zero]
    simp
  rw [Scheme.IdealSheafData.support_comap] at hs
  exact hs

/-- Restriction to the reduced irreducible closed subscheme is Cartier unless it is contained. -/
theorem EffectiveCartier.comap_reducedClosedSubscheme (hI : EffectiveCartier I)
    (Z : Closeds X) (hZ : IsIrreducible (Z : Set X)) (hZI : ¬ Z ≤ I.support) :
    EffectiveCartier (I.comap (reducedClosedSubschemeι Z)) := by
  have := reducedClosedSubscheme_isIntegral Z hZ
  apply hI.comap_of_integral (reducedClosedSubschemeι Z)
  intro hg
  apply hZI
  exact (closedSubschemeGenericPoint_mem_closed_iff Z I.support hZ).mp hg

end FLT.Mazur.FCurve
