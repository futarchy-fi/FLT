/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.AdicFractionFieldComplete

/-!
# A complete topological copy of the DVR

Power-series substitution treats the coefficient ring as discrete while
its target has the adic topology. This copy permits both structures to
coexist and derives all completeness and linear-topology instances.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory
open IsLocalRing

/-- The integer ring, tagged by the fraction field inducing its topology. -/
def AdicInteger (S _L : Type) : Type := S

variable (S L : Type) [CommRing S]

instance instAdicIntegerCommRing : CommRing (AdicInteger S L) := inferInstanceAs (CommRing S)

/-- Forget the topology tag on the integer ring. -/
def adicIntegerEquiv : AdicInteger S L ≃+* S := RingEquiv.refl S

instance instAdicIntegerAlgebra : Algebra S (AdicInteger S L) :=
  (adicIntegerEquiv S L).symm.toRingHom.toAlgebra

variable [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L]

instance instAdicIntegerUniformSpace : UniformSpace (AdicInteger S L) :=
  dvrIntegerUniformity S L

instance instAdicIntegerUniformAddGroup : IsUniformAddGroup (AdicInteger S L) :=
  letI := dvrAdicValued S L
  IsUniformAddGroup.comap ((algebraMap S L).comp (adicIntegerEquiv S L).toRingHom)

instance instAdicIntegerTopologicalRing : IsTopologicalRing (AdicInteger S L) := by
  let := dvrAdicValued S L
  let : ContinuousMul (AdicInteger S L) :=
    continuousMul_induced ((algebraMap S L).comp (adicIntegerEquiv S L).toRingHom)
  exact
    { continuous_add := continuous_add
      continuous_mul := continuous_mul
      continuous_neg := continuous_neg }

/-- The uniform copy has the original maximal-ideal adic topology. -/
theorem adicInteger_isAdic :
    IsAdic ((maximalIdeal S).map (algebraMap S (AdicInteger S L))) := by
  change @IsAdic S _ (dvrIntegerUniformity S L).toTopologicalSpace
    ((maximalIdeal S).map (RingHom.id S))
  rw [Ideal.map_id]
  exact dvrIntegerUniformity_isAdic S L

instance instAdicIntegerLinearTopology : IsLinearTopology (AdicInteger S L) (AdicInteger S L) := by
  rw [adicInteger_isAdic S L]
  exact Ideal.isLinearTopology _

variable [IsAdicComplete (maximalIdeal S) S]

instance instAdicIntegerCompleteSpace : CompleteSpace (AdicInteger S L) := by
  let := dvrIntegerUniformity S L
  let : IsUniformAddGroup S := IsUniformAddGroup.comap (algebraMap S L)
  exact (dvrIntegerUniformity_isAdic S L).isPrecomplete_iff.mp
    (inferInstance : IsPrecomplete (maximalIdeal S) S)

instance instAdicIntegerT2Space : T2Space (AdicInteger S L) := by
  let := dvrIntegerUniformity S L
  exact (dvrIntegerUniformity_isAdic S L).isHausdorff_iff.mp
    (inferInstance : IsHausdorff (maximalIdeal S) S)

end LocalClassFieldTheory
