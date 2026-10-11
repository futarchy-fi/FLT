/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletedInfinitesimalLift
public import FLT.Mazur.AdicFormalLiftProjection
public import FLT.Mazur.AdicInfinitesimalConormal

/-!
# Actual completed infinitesimal morphisms and original conormal maps

The constructed completed lift is a genuine extension morphism over the
formal equivalence. Transporting its conormal map through the original
conormal comparisons gives a map between completed original conormals,
with its actual completed-target scalar action.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCompletedInfinitesimalHom

open AdicExtensionProjection AdicFormalPresentationHom
  AdicInfinitesimalPresentationLift AdicCompletedInfinitesimalLift

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B ι : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (P : Algebra.Generators R A ι)
  (Q : Algebra.Extension.{u} R B)
  [IsNoetherianRing P.Ring] [IsNoetherianRing Q.Ring]
  (I : Ideal A) (J : Ideal B) [I.IsMaximal] [J.IsMaximal]
  (e : AdicCompletion I A ≃ₐ[R] AdicCompletion J B)

/-- The polynomial presentation retains its original Noetherian ring. -/
local instance presentationNoetherian : IsNoetherianRing P.toExtension.Ring :=
  inferInstanceAs (IsNoetherianRing P.Ring)

/-- The source infinitesimal presenting ring is Noetherian. -/
local instance sourceNoetherian : IsNoetherianRing P.toExtension.infinitesimal.Ring :=
  inferInstanceAs (IsNoetherianRing (P.Ring ⧸ P.ker ^ 2))

/-- The target infinitesimal presenting ring is Noetherian. -/
local instance targetNoetherian : IsNoetherianRing Q.infinitesimal.Ring :=
  inferInstanceAs (IsNoetherianRing (Q.Ring ⧸ Q.ker ^ 2))

/-- The actual completed lift lies over the formal comparison on the whole completed ring. -/
theorem projection_lift
    (x : AdicCompletion (ideal P.toExtension.infinitesimal I) P.toExtension.infinitesimal.Ring) :
    projection Q.infinitesimal J (lift P Q I J e x) =
      e (projection P.toExtension.infinitesimal I x) :=
  AdicFormalLiftProjection.projection_extend P.toExtension.infinitesimal Q.infinitesimal I J e
    (infinitesimalLift P Q I J e.toAlgHom)
    (projection_infinitesimalLift P Q I J e.toAlgHom) x

/-- The constructed completed lift is a genuine extension morphism over the formal equivalence. -/
def hom :
    let _ := e.toAlgHom.toAlgebra
    (completed P.toExtension.infinitesimal I).Hom (completed Q.infinitesimal J) := by
  let _ := e.toAlgHom.toAlgebra
  exact
    { toRingHom := (lift P Q I J e).toRingHom
      toRingHom_algebraMap := (lift P Q I J e).commutes
      algebraMap_toRingHom := projection_lift P Q I J e }

/-- The genuine extension morphism induces a map between completed ORIGINAL conormals. -/
def conormalMap : AdicCompletion I P.toExtension.Cotangent →+
    AdicCompletion J Q.Cotangent := by
  let _ := e.toAlgHom.toAlgebra
  exact (AdicInfinitesimalConormal.equiv Q J).symm.toLinearMap.toAddMonoidHom.comp
    ((Algebra.Extension.Cotangent.map (hom P Q I J e)).toAddMonoidHom.comp
      (AdicInfinitesimalConormal.equiv P.toExtension I).toLinearMap.toAddMonoidHom)

/-- The original-conormal comparison map retains the actual formal scalar map. -/
theorem conormalMap_smul (a : AdicCompletion I A)
    (x : AdicCompletion I P.toExtension.Cotangent) :
    conormalMap P Q I J e (a • x) = e a • conormalMap P Q I J e x := by
  let _ := e.toAlgHom.toAlgebra
  change (AdicInfinitesimalConormal.equiv Q J).symm
    (Algebra.Extension.Cotangent.map (hom P Q I J e)
      (AdicInfinitesimalConormal.equiv P.toExtension I (a • x))) = _
  rw [map_smul, map_smul]
  change (AdicInfinitesimalConormal.equiv Q J).symm
    (e a • Algebra.Extension.Cotangent.map (hom P Q I J e)
      (AdicInfinitesimalConormal.equiv P.toExtension I x)) = _
  exact (AdicInfinitesimalConormal.equiv Q J).symm.map_smul _ _

end FLT.Mazur.AdicCompletedInfinitesimalHom
