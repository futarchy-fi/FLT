/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.KernelPairEffectiveOpen
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Actual etale quotient projections on effective opens

Both complete restricted endpoints are pullbacks of their original endpoints.
When these are etale and the actual model projection is fppf, descent proves
that the constructed effective quotient projection is itself etale.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.KernelPairEffectiveOpen
set_option backward.isDefEq.respectTransparency false
variable {D A T : Scheme.{u}} (p q : D ⟶ A) (w : A ⟶ T) (h : p ≫ w = q ≫ w)
local notation "U" => targetOpen p q w h

/-- Restricting the first endpoint retains its entire base change over the original source. -/
theorem fst_isPullback : IsPullback (pullback.fst (p ≫ w) (U).ι)
    (fst p q w h) p (pullback.fst w (U).ι) := by
  have s : IsPullback (pullback.fst (p ≫ w) (U).ι)
      (fst p q w h ≫ projection p q w h) (p ≫ w) (U).ι := by
    simpa only [fst, projection, pullback.lift_snd] using
      (IsPullback.of_hasPullback (p ≫ w) (U).ι)
  exact s.of_bot (fst_original p q w h).symm (.of_hasPullback _ _)

/-- The independent second endpoint is also a full base change. -/
theorem snd_isPullback : IsPullback (pullback.fst (p ≫ w) (U).ι)
    (snd p q w h) q (pullback.fst w (U).ι) := by
  have s : IsPullback (pullback.fst (p ≫ w) (U).ι)
      (snd p q w h ≫ projection p q w h) (q ≫ w) (U).ι := by
    simpa only [snd, projection, pullback.lift_snd, ← h] using
      (IsPullback.of_hasPullback (p ≫ w) (U).ι)
  exact s.of_bot (snd_original p q w h).symm (.of_hasPullback _ _)

/-- Etaleness is preserved on the full first endpoint. -/
instance fst_etale [Etale p] : Etale (fst p q w h) :=
  MorphismProperty.of_isPullback (fst_isPullback p q w h) inferInstance

/-- Etaleness is preserved on the full second endpoint. -/
instance snd_etale [Etale q] : Etale (snd p q w h) :=
  MorphismProperty.of_isPullback (snd_isPullback p q w h) inferInstance

/-- The effective projection is etale by descent of the actual original endpoint. -/
theorem projection_etale [Mono (pullback.lift p q h)] [Etale p]
    [Flat w] [Surjective w] [LocallyOfFinitePresentation w] :
    Etale (projection p q w h) :=
  MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    (isPullback p q w h) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

end FLT.Mazur.KernelPairEffectiveOpen
