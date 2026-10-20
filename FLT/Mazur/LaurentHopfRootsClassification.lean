/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentHopfCyclicCharacters
public import FLT.Mazur.RootsOfUnityAlgebra

/-!
# Classification of finite Laurent Hopf quotients as roots of unity

The comparison preserves the given quotient map on every Laurent polynomial.
Thus it recovers the full defining ideal in every characteristic, with no
reducedness, etaleness or invertibility assumption on the subgroup order.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped LaurentPolynomial

namespace FLT.Mazur.LaurentHopfRootsClassification

open ToricHopfCharacterKernel LaurentHopfCyclicCharacters

variable {K A : Type*} [Field K] [Ring A] [HopfAlgebra K A]
  (f : K[T;T⁻¹] →ₐc[K] A) (hf : Function.Surjective f)

/-- The actual quotient is the roots algebra of its dimension, with Hopf operations retained. -/
def coordinatesEquiv : RootsOfUnityAlgebra.Coordinate K (Module.finrank K A) ≃ₐc[K] A :=
  (AddMonoidAlgebra.toMultiplicativeBialgEquiv K K (ZMod (Module.finrank K A))).trans
    ((MonoidAlgebra.domCongrBialgEquiv K K (cyclicEquiv f hf)).trans
      (quotientCoordinatesEquiv (multiplicativeMap f) (multiplicativeMap_surjective f hf)))

/-- Every integer monomial is sent to its original quotient value. -/
theorem coordinatesEquiv_single_intCast (i : ℤ) :
    coordinatesEquiv f hf (AddMonoidAlgebra.single (i : ZMod (Module.finrank K A)) 1) =
      f (LaurentPolynomial.T i) := by
  change quotientCoordinates (multiplicativeMap f)
    (MonoidAlgebra.domCongrBialgEquiv K K (cyclicEquiv f hf)
      ((AddMonoidAlgebra.toMultiplicativeBialgEquiv K K (ZMod (Module.finrank K A)))
        (AddMonoidAlgebra.single (i : ZMod (Module.finrank K A)) 1))) = _
  rw [AddMonoidAlgebra.toMultiplicativeBialgEquiv_single]
  have hd (j : Multiplicative (ZMod (Module.finrank K A))) :
      MonoidAlgebra.domCongrBialgEquiv K K (cyclicEquiv f hf)
        (MonoidAlgebra.single j 1) = MonoidAlgebra.single (cyclicEquiv f hf j) 1 :=
    MonoidAlgebra.domCongr_single (R := K) (A := K) (cyclicEquiv f hf) j 1
  rw [hd, cyclicEquiv_intCast, quotientCoordinates_single, quotientCharacter_mk]
  change f ((AddMonoidAlgebra.toMultiplicativeBialgEquiv K K ℤ).symm
    (MonoidAlgebra.single (Multiplicative.ofAdd i) 1)) = _
  apply congrArg f
  let e := AddMonoidAlgebra.toMultiplicativeBialgEquiv K K ℤ
  exact (congrArg e.symm
    (AddMonoidAlgebra.toMultiplicativeBialgEquiv_single (R := K) i (1 : K)).symm).trans
      (e.symm_apply_apply (AddMonoidAlgebra.single i 1))

/-- The roots restriction agrees with the entire original subgroup coordinate map. -/
theorem coordinatesEquiv_restriction :
    (coordinatesEquiv f hf).toBialgHom.comp
      (RootsOfUnityAlgebra.restriction K (Module.finrank K A)) = f := by
  apply BialgHom.coe_toAlgHom_injective
  apply AddMonoidAlgebra.algHom_ext
  · intro i
    change coordinatesEquiv f hf
      (RootsOfUnityAlgebra.restriction K _ (AddMonoidAlgebra.single i 1)) = _
    rw [RootsOfUnityAlgebra.restriction_single]
    exact coordinatesEquiv_single_intCast f hf i
  · ext

include hf in
/-- The defining ideal equals the roots ideal as an ideal, retaining all multiplicities. -/
theorem kernel_eq_roots : RingHom.ker f.toAlgHom.toRingHom =
    RingHom.ker (RootsOfUnityAlgebra.restriction K
      (Module.finrank K A)).toAlgHom.toRingHom := by
  ext x
  change f x = 0 ↔ _
  rw [← DFunLike.congr_fun (coordinatesEquiv_restriction f hf) x]
  exact map_eq_zero_iff (coordinatesEquiv f hf) (coordinatesEquiv f hf).injective

end FLT.Mazur.LaurentHopfRootsClassification
