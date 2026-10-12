/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCyclicOriginalLocalCubic
public import FLT.Mazur.PointedCubicIndependentSourceSubgroup

/-!
# Original smooth cyclic coverage without coprimality with four

The independent chart retains the original full curve and Cartier subgroup.
Its auxiliary and cyclic labels may intersect, so the construction now covers
even cyclic orders too. Two must still be invertible and the subgroup etale.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  [Etale H.carrier.hom] (hc : H.IsCyclic) (ha : H.IsAmple)
  (h₂ : IsUnit (2 : Γ(S, ⊤)))

include h₂ in
/-- Independent charts cover every original smooth etale object, including even orders. -/
theorem exists_original_independent_neighborhood {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ LocallyOfFinitePresentation g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ p : U ⟶ (independentCyclicAuxiliaryScheme n).left,
          independentCyclicSourceModuliClass n p =
            ampleCyclicClassesPullback g n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  obtain ⟨T, hT, f, hf, hl, hxf, hV, W, hW, φ, hφ, ⟨a⟩⟩ :=
    hc.exists_original_local_cubic H hx
  let _ := hT
  let _ := hW
  let _ := hf
  let _ := hl
  have hT₂ : IsUnit (2 : Γ(T, ⊤)) := by
    simpa only [map_ofNat] using h₂.map f.appTop.hom
  let k := (pointedCubicAuxiliaryCover W hT₂).hom
  let _ : AlgebraicGeometry.Surjective k := pointedCubicAuxiliaryCover_surjective W hT₂
  let _ : Etale k := pointedCubicAuxiliaryCover_etale W hT₂
  refine ⟨(pointedCubicAuxiliaryCover W hT₂).left, k ≫ f,
    inferInstance, inferInstance, ?_, ?_,
    (pointedCubicIndependentParameter W hT₂ φ hφ).left, ?_⟩
  · obtain ⟨t, ht⟩ := hxf
    obtain ⟨u, hu⟩ := k.surjective t
    exact ⟨u, by change f (k u) = x; rw [hu, ht]⟩
  · rintro _ ⟨u, rfl⟩
    exact hV ⟨k u, rfl⟩
  · rw [pointedCubicIndependentSource_originalClass W hT₂ φ hφ (H.baseChange f) a
      (hc.baseChange H f) (ha.baseChange f)]
    exact (congrFun (ampleCyclicClassesPullback_comp f k n)
      (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩)).symm

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
