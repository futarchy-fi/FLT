/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorOpenChart
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The exact image of a tensor chart

The tensor chart covers precisely the inverse image of its original chart.
This applies to whole charts and hence to atlases after coefficient extension.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.TensorOpenChart
universe u
variable {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) (i : Spec (.of A) ⟶ X)
  (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- The actual tensor chart has exactly the full inverse image of its original image. -/
theorem chart_range : Set.range (chart (S := S) f i hi) =
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S))) f) ⁻¹' Set.range i := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨projection a, congrArg (fun g => g a) (chart_snd f i hi).symm⟩
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb, _⟩ := Scheme.exists_preimage_of_isPullback (chart_isPullback f i hi) z a ha.symm
    exact ⟨b, hb⟩

end FLT.Mazur.TensorOpenChart
