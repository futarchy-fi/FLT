/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCyclicOriginalLocalCubic
public import FLT.Mazur.PointedCubicNormalizedOriginalClass

/-!
# Full normalized charts cover original smooth etale cyclic objects locally

Over a locally noetherian base with two invertible and cyclic order coprime to
four, each original smooth ample etale cyclic object is represented by the full
normalized slice on flat finitely presented neighborhoods covering every base
point. The represented modular class is the actual original pullback class.
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
  (h₂ : IsUnit (2 : Γ(S, ⊤))) (hn : Nat.Coprime 4 n)

include h₂ hn in
/-- The full normalized slice covers each original smooth etale cyclic object locally. -/
theorem exists_original_normalized_neighborhood {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ LocallyOfFinitePresentation g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ p : U ⟶ cyclicNormalizedSlice n,
          (cyclicNormalizedSliceModuliMap n).app (Opposite.op U) (ULift.up p) =
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
  have hk : AlgebraicGeometry.Surjective k := pointedCubicAuxiliaryCover_surjective W hT₂
  let _ := hk
  let _ : Etale k := pointedCubicAuxiliaryCover_etale W hT₂
  refine ⟨(pointedCubicAuxiliaryCover W hT₂).left, k ≫ f,
    inferInstance, inferInstance, ?_, ?_, pointedCubicNormalizedPoint W hT₂ φ hφ hn, ?_⟩
  · obtain ⟨t, ht⟩ := hxf
    obtain ⟨u, hu⟩ := k.surjective t
    exact ⟨u, by change f (k u) = x; rw [hu, ht]⟩
  · rintro _ ⟨u, rfl⟩
    exact hV ⟨k u, rfl⟩
  · rw [pointedCubicNormalizedPoint_originalClass W hT₂ φ hφ hn (H.baseChange f) a
      (hc.baseChange H f) (ha.baseChange f)]
    exact (congrFun (ampleCyclicClassesPullback_comp f k n)
      (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩)).symm

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
