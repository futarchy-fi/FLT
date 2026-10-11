/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicFormalLiftContinuity
public import FLT.Mazur.AdicInfinitesimalPresentationLift

/-!
# Constructed maps between completed infinitesimal presentations

The original polynomial lift descends through the relation square, and its
proved maximal-ideal continuity extends it through source completion. Thus
no choice of a map between completed presenting rings is assumed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCompletedInfinitesimalLift

open AdicExtensionProjection AdicInfinitesimalPresentationLift

universe u

variable {R A B ι : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (P : Algebra.Generators R A ι)
  (Q : Algebra.Extension.{u} R B)
  [IsNoetherianRing P.Ring] [IsNoetherianRing Q.Ring]
  (I : Ideal A) (J : Ideal B) [I.IsMaximal] [J.IsMaximal]
  (e : AdicCompletion I A ≃ₐ[R] AdicCompletion J B)

/-- The source infinitesimal presenting ring is Noetherian. -/
local instance sourceNoetherian : IsNoetherianRing P.toExtension.infinitesimal.Ring :=
  inferInstanceAs (IsNoetherianRing (P.Ring ⧸ P.ker ^ 2))

/-- The target infinitesimal presenting ring is Noetherian. -/
local instance targetNoetherian : IsNoetherianRing Q.infinitesimal.Ring :=
  inferInstanceAs (IsNoetherianRing (Q.Ring ⧸ Q.ker ^ 2))

/-- Extend the constructed infinitesimal lift through the original presenting-ring completion. -/
def lift : AdicCompletion (ideal P.toExtension.infinitesimal I) P.toExtension.infinitesimal.Ring
    →ₐ[R] AdicCompletion (ideal Q.infinitesimal J) Q.infinitesimal.Ring :=
  AdicFormalLiftContinuity.extend P.toExtension.infinitesimal Q.infinitesimal I J e
    (infinitesimalLift P Q I J e.toAlgHom)
    (projection_infinitesimalLift P Q I J e.toAlgHom)

/-- On original infinitesimal elements the completed lift retains the constructed lift. -/
@[simp] theorem lift_of (x : P.toExtension.infinitesimal.Ring) :
    lift P Q I J e (AdicCompletion.of (ideal P.toExtension.infinitesimal I)
      P.toExtension.infinitesimal.Ring x) = infinitesimalLift P Q I J e.toAlgHom x :=
  AdicFormalLiftContinuity.extend_of P.toExtension.infinitesimal Q.infinitesimal I J e
    (infinitesimalLift P Q I J e.toAlgHom)
    (projection_infinitesimalLift P Q I J e.toAlgHom) x

/-- The completed lift lies over the formal comparison on all original elements. -/
theorem projection_lift_of (x : P.toExtension.infinitesimal.Ring) :
    projection Q.infinitesimal J
      (lift P Q I J e (AdicCompletion.of (ideal P.toExtension.infinitesimal I)
        P.toExtension.infinitesimal.Ring x)) =
      e (AdicCompletion.of I A (algebraMap P.toExtension.infinitesimal.Ring A x)) := by
  rw [lift_of]
  exact projection_infinitesimalLift P Q I J e.toAlgHom x

end FLT.Mazur.AdicCompletedInfinitesimalLift
