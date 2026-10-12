/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCyclicOriginalIndependentCoverage
public import FLT.Mazur.EtaleCyclicSmoothLocusNormalizedCoverage

/-!
# Original smooth-locus coverage without coprimality with four

A generalized curve may have singular fibers elsewhere. Restrict its actual
subgroup to the canonical smooth base open, apply the proved smooth coverage,
and flatten the resulting map and modular pullback to the original base.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] {E : GeneralizedEllipticCurve S}
  {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n) [Etale H.carrier.hom]
  (hc : H.IsCyclic) (ha : H.IsAmple)
  (h₂ : IsUnit (2 : Γ(S, ⊤)))

include h₂ in
/-- Every original smooth-locus point is covered by an actual independent cyclic chart. -/
theorem exists_smoothLocus_independent_neighborhood {V : S.Opens} {x : S}
    (hx : x ∈ smoothBaseOpen E) (hxV : x ∈ V) :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ LocallyOfFinitePresentation g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ p : U ⟶ (independentCyclicAuxiliaryScheme n).left,
          independentCyclicSourceModuliClass n p =
            ampleCyclicClassesPullback g n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  let B := smoothBaseOpen E
  let _ : IsLocallyNoetherian B.toScheme := isLocallyNoetherian_of_isOpenImmersion B.ι
  let _ : Smooth (E.baseChange B.ι).curve.hom :=
    SmoothOfRelativeDimension.smooth 1 _
  let _ : Etale (H.baseChange B.ι).carrier.hom :=
    inferInstanceAs (Etale (pullback.snd H.carrier.hom B.ι))
  have hB₂ : IsUnit (2 : Γ(B.toScheme, ⊤)) := by
    simpa only [map_ofNat] using h₂.map B.ι.appTop.hom
  obtain ⟨U, g, hg, hl, hxg, hV, p, hp⟩ :=
    exists_original_independent_neighborhood (H.baseChange B.ι)
      (hc.baseChange H B.ι) (ha.baseChange B.ι) hB₂
      (x := (⟨x, hx⟩ : B.toScheme)) (V := B.ι ⁻¹ᵁ V) hxV
  let _ := hg
  let _ := hl
  refine ⟨U, g ≫ B.ι, inferInstance, inferInstance, ?_, ?_, p, ?_⟩
  · obtain ⟨u, hu⟩ := hxg
    exact ⟨u, by change B.ι (g u) = x; rw [hu]; rfl⟩
  · rintro _ ⟨u, rfl⟩
    exact hV ⟨u, rfl⟩
  · exact hp.trans ((congrFun (ampleCyclicClassesPullback_comp B.ι g n)
      (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩)).symm)

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
