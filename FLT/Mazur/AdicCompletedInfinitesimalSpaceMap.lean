/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicInfinitesimalSpaceMap
public import FLT.Mazur.AdicCompletedInfinitesimalHom

/-!
# Degree-zero maps from constructed completed infinitesimal lifts

The actual lifts constructed from formal equivalences now induce maps of
completed ORIGINAL presentation cotangent spaces. Neither a degree-zero
map nor a lift is an additional input.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCompletedInfinitesimalSpaceMap

open AdicExtensionProjection AdicCompletedInfinitesimalLift

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B ι : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Finite ι] (P : Algebra.Generators R A ι)
  (Q : Algebra.Extension.{u} R B)
  [IsNoetherianRing P.Ring] [IsNoetherianRing Q.Ring]
  (I : Ideal A) (J : Ideal B) [I.IsMaximal] [J.IsMaximal]
  (e : AdicCompletion I A ≃ₐ[R] AdicCompletion J B)

include P in
omit [Finite ι] in
/-- The original target inherits Noetherianity from its polynomial presentation. -/
theorem targetNoetherian : IsNoetherianRing A :=
  isNoetherianRing_of_surjective P.Ring A (algebraMap P.Ring A) P.algebraMap_surjective

/-- The original finite presentation has a finite free degree-zero space. -/
local instance finiteSpace : Module.Finite A P.toExtension.CotangentSpace :=
  Module.Finite.of_basis P.cotangentSpaceBasis

/-- The constructed lift gives a semilinear map of completed ORIGINAL degree-zero spaces. -/
def map : AdicCompletion I P.toExtension.CotangentSpace →ₛₗ[e.toRingHom]
    AdicCompletion J Q.CotangentSpace := by
  let _ := targetNoetherian P
  exact AdicInfinitesimalSpaceMap.map P.toExtension Q I J e.toAlgHom (lift P Q I J e)
    (AdicCompletedInfinitesimalHom.projection_lift P Q I J e)

open scoped TensorProduct in
/-- The degree-zero map records derivatives of the actual constructed formal lift. -/
theorem map_of_tmul (a : A) (x : P.toExtension.Ring) :
    map P Q I J e (AdicCompletion.of I P.toExtension.CotangentSpace
      (a ⊗ₜ[P.toExtension.Ring] KaehlerDifferential.D R P.toExtension.Ring x)) =
        e (AdicCompletion.of I A a) • (AdicInfinitesimalCotangentSpace.equiv Q J).symm
          (AdicPresentationDerivation.derivation Q.infinitesimal J
            (lift P Q I J e (AdicCompletion.of (ideal P.toExtension.infinitesimal I)
              P.toExtension.infinitesimal.Ring (P.toExtension.toInfinitesimal.toAlgHom x)))) := by
  let _ := targetNoetherian P
  exact AdicInfinitesimalSpaceMap.map_of_tmul P.toExtension Q I J e.toAlgHom (lift P Q I J e)
    (AdicCompletedInfinitesimalHom.projection_lift P Q I J e) a x

end FLT.Mazur.AdicCompletedInfinitesimalSpaceMap
