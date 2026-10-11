/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicInfinitesimalOriginalChainMap
public import FLT.Mazur.AdicCompletedInfinitesimalSpaceMap

/-!
# Constructed infinitesimal lifts give genuine original chain maps

The degree-one map previously constructed from the genuine completed
extension morphism and the new degree-zero map commute with the completed
ORIGINAL differentials. No replacement of the original complex is assumed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCompletedInfinitesimalChainMap

open AdicCompletedInfinitesimalLift

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B ι : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Finite ι] (P : Algebra.Generators R A ι)
  (Q : Algebra.Extension.{u} R B)
  [IsNoetherianRing P.Ring] [IsNoetherianRing Q.Ring]
  (I : Ideal A) (J : Ideal B) [I.IsMaximal] [J.IsMaximal]
  (e : AdicCompletion I A ≃ₐ[R] AdicCompletion J B)

/-- The polynomial presentation retains its original Noetherian ring. -/
local instance presentationNoetherian : IsNoetherianRing P.toExtension.Ring :=
  inferInstanceAs (IsNoetherianRing P.Ring)

omit [Finite ι] in
/-- Transport agrees with the existing conormal map of the genuine completed extension morphism. -/
theorem conormalMap_eq (x : AdicCompletion I P.toExtension.Cotangent) :
    AdicInfinitesimalOriginalChainMap.conormalMap P.toExtension Q I J e.toAlgHom
      (lift P Q I J e) (AdicCompletedInfinitesimalHom.projection_lift P Q I J e) x =
        AdicCompletedInfinitesimalHom.conormalMap P Q I J e x := rfl

/-- The constructed degree-zero and degree-one maps form a chain map on the ORIGINAL complexes. -/
theorem chainMap (x : AdicCompletion I P.toExtension.Cotangent) :
    AdicCompletedInfinitesimalSpaceMap.map P Q I J e
      (AdicCompletion.map I P.toExtension.cotangentComplex x) =
      AdicCompletion.map J Q.cotangentComplex
        (AdicCompletedInfinitesimalHom.conormalMap P Q I J e x) := by
  let _ := AdicCompletedInfinitesimalSpaceMap.targetNoetherian P
  let _ := AdicCompletedInfinitesimalSpaceMap.finiteSpace P
  exact AdicInfinitesimalOriginalChainMap.chainMap P.toExtension Q I J e.toAlgHom
    (lift P Q I J e) (AdicCompletedInfinitesimalHom.projection_lift P Q I J e) x

end FLT.Mazur.AdicCompletedInfinitesimalChainMap
