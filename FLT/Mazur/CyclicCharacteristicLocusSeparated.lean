/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicLocusFiniteType

/-!
# Absolute separatedness of the actual characteristic subgroup loci

The marking opens are separated over their coefficient bases. Products,
closed subgroup equations, and the affine coefficient maps then prove absolute
separatedness of both subgroup loci and both normalized loci.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A faithful marking open in a proper homomorphism scheme is separated. -/
instance faithfulMarking_isSeparated {S : Scheme} (E : Over S) [GrpObj E] [IsProper E.hom]
    (A : Type) [Group A] [Fintype A] : IsSeparated (AuxiliaryLevel.faithfulScheme E A).hom := by
  rw [← (AuxiliaryLevel.faithfulInclusion E A).w]
  infer_instance

/-- The even coefficient map is separated. -/
instance evenCoefficientToInt_isSeparated : IsSeparated evenCoefficientToInt := by
  unfold evenCoefficientToInt
  infer_instance

/-- The odd coefficient map is separated. -/
instance oddCoefficientToInt_isSeparated : IsSeparated oddCoefficientToInt := by
  unfold oddCoefficientToInt
  infer_instance

variable (n : ℕ) [NeZero n]

/-- The entire even auxiliary/cyclic parameter map is separated. -/
instance evenParameterToInt_isSeparated : IsSeparated (evenParameterToInt n) := by
  let _ : IsSeparated UniversalWeierstrass.levelFour.hom := faithfulMarking_isSeparated _ _
  unfold evenParameterToInt UniversalWeierstrass.cyclicHomAuxiliaryScheme
  infer_instance

/-- The entire odd auxiliary/cyclic parameter map is separated. -/
instance oddParameterToInt_isSeparated : IsSeparated (oddParameterToInt n) := by
  let _ : IsSeparated OddWeierstrassParameter.levelThree.hom := faithfulMarking_isSeparated _ _
  unfold oddParameterToInt OddWeierstrassParameter.cyclicHomAuxiliaryScheme
  infer_instance

/-- The even subgroup parameter map is separated. -/
instance evenLocusToInt_isSeparated : IsSeparated (evenLocusToInt n) := by
  unfold evenLocusToInt
  infer_instance

/-- The odd subgroup parameter map is separated. -/
instance oddLocusToInt_isSeparated : IsSeparated (oddLocusToInt n) := by
  unfold oddLocusToInt
  infer_instance

/-- The even subgroup locus is absolutely separated. -/
instance evenLocus_isSeparated :
    (UniversalWeierstrass.cyclicHomUniversalMultiplicationLocus n).IsSeparated :=
  (HasAffineProperty.iff_of_isAffine
    (P := @IsSeparated) (f := evenLocusToInt n)).mp inferInstance

/-- The odd subgroup locus is absolutely separated. -/
instance oddLocus_isSeparated :
    (OddWeierstrassParameter.cyclicHomUniversalMultiplicationLocus n).IsSeparated :=
  (HasAffineProperty.iff_of_isAffine
    (P := @IsSeparated) (f := oddLocusToInt n)).mp inferInstance

/-- The even normalized subgroup locus is absolutely separated. -/
instance evenNormalizedLocus_isSeparated :
    (UniversalWeierstrass.cyclicHomNormalizedLocus n).IsSeparated := by
  let _ : IsSeparated (evenNormalizedLocusToInt n) := by
    unfold evenNormalizedLocusToInt
    infer_instance
  exact (HasAffineProperty.iff_of_isAffine (P := @IsSeparated)
    (f := evenNormalizedLocusToInt n)).mp inferInstance

/-- The odd normalized subgroup locus is absolutely separated. -/
instance oddNormalizedLocus_isSeparated :
    (OddWeierstrassParameter.cyclicHomNormalizedLocus n).IsSeparated := by
  let _ : IsSeparated (oddNormalizedLocusToInt n) := by
    unfold oddNormalizedLocusToInt
    infer_instance
  exact (HasAffineProperty.iff_of_isAffine (P := @IsSeparated)
    (f := oddNormalizedLocusToInt n)).mp inferInstance

end FLT.Mazur.CyclicCharacteristicAtlas
