/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalTranscendentalOpenAllLifts

/-!
# Independent lifts in the unchanged original smooth fiber

The intermediate residue fiber is constructed by a pullback. All output
maps and all prescribed larger-field opens remain on the original smooth
family and its specified actual geometric fiber.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OriginalSmoothFiberAllLifts
set_option backward.isDefEq.respectTransparency false
variable {R k L K : Type} [CommRing R] [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra k K] [IsScalarTower k L K]
  [Algebra.IsAlgebraic k L] [IsAlgClosed L] {V Y : Scheme}

include L

/-- An actual original smooth fiber admits an étale test controlling every independent lift. -/
theorem exists_all_lifts (f : V ⟶ Spec (.of R)) [Smooth f] [GeometricallyIntegral f]
    (t : Spec (.of k) ⟶ Spec (.of R)) [IsPreimmersion t]
    (a : Y ⟶ V) (b : Y ⟶ Spec (.of K))
    (H : IsPullback a b f (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t))
    {J : Type*} [Finite J] (U : J → Y.Opens) (hU : ∀ j, (U j : Set Y).Nonempty) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of R)) (v : E ⟶ V)
      (z : Spec (.of K) ⟶ E), IsAffine E ∧ Etale e ∧ v ≫ f = e ∧
      z ≫ e = Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t ∧
      ∀ w : Spec (.of K) ⟶ E,
        w ≫ e = Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t →
        ∃ u : Spec (.of K) ⟶ Y, u ≫ b = 𝟙 _ ∧
          w ≫ v = u ≫ a ∧ ∀ j, Set.range u ⊆ U j := by
  let H₀ := IsPullback.of_hasPullback f t
  have H' := H.of_right' H₀
  obtain ⟨E, e, v, z, hE, he, hv, hz, hall⟩ :=
    OriginalTranscendentalOpenAllLifts.exists_all_lifts (L := L) f t
      (pullback.fst f t) (pullback.snd f t) H₀ b _ H'.flip U hU
  refine ⟨E, e, v, z, hE, he, hv, hz, fun w hw ↦ ?_⟩
  obtain ⟨u, hu, hv, hm⟩ := hall w hw
  refine ⟨u, hu, ?_, hm⟩
  simpa only [IsPullback.lift_fst] using hv

end FLT.Mazur.OriginalSmoothFiberAllLifts
