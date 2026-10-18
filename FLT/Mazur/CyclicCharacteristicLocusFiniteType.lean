/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicParameterFiniteType
public import FLT.Mazur.CyclicHomNormalizedLocus
public import FLT.Mazur.OddWeierstrassCyclicHomNormalizedLocus

/-!
# Finite type of the actual subgroup and normalized loci

The multiplication equations and normalized slices are closed immersions in
the full parameter spaces. Their actual maps to Spec Z are finite type, for
every nonzero cyclic order and without an etaleness restriction on the subgroup.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (n : ℕ) [NeZero n]

/-- The actual even multiplication locus over the integers. -/
def evenLocusToInt :
    UniversalWeierstrass.cyclicHomUniversalMultiplicationLocus n ⟶ Spec (.of ℤ) :=
  UniversalWeierstrass.cyclicHomUniversalMultiplicationLocusInclusion n ≫ evenParameterToInt n

/-- The actual odd multiplication locus over the integers. -/
def oddLocusToInt :
    OddWeierstrassParameter.cyclicHomUniversalMultiplicationLocus n ⟶ Spec (.of ℤ) :=
  OddWeierstrassParameter.cyclicHomUniversalMultiplicationLocusInclusion n ≫ oddParameterToInt n

/-- The even normalized subgroup locus over the integers. -/
def evenNormalizedLocusToInt :
    UniversalWeierstrass.cyclicHomNormalizedLocus n ⟶ Spec (.of ℤ) :=
  UniversalWeierstrass.cyclicHomNormalizedLocusInclusion n ≫ evenLocusToInt n

/-- The odd normalized subgroup locus over the integers. -/
def oddNormalizedLocusToInt :
    OddWeierstrassParameter.cyclicHomNormalizedLocus n ⟶ Spec (.of ℤ) :=
  OddWeierstrassParameter.cyclicHomNormalizedLocusInclusion n ≫ oddLocusToInt n

/-- The original even subgroup equations define a locally finite type scheme. -/
instance evenLocusToInt_locallyOfFiniteType : LocallyOfFiniteType (evenLocusToInt n) := by
  unfold evenLocusToInt
  infer_instance

/-- The original odd subgroup equations define a locally finite type scheme. -/
instance oddLocusToInt_locallyOfFiniteType : LocallyOfFiniteType (oddLocusToInt n) := by
  unfold oddLocusToInt
  infer_instance

/-- The original even subgroup locus is quasi-compact over the integers. -/
instance evenLocusToInt_quasiCompact : QuasiCompact (evenLocusToInt n) := by
  unfold evenLocusToInt
  infer_instance

/-- The original odd subgroup locus is quasi-compact over the integers. -/
instance oddLocusToInt_quasiCompact : QuasiCompact (oddLocusToInt n) := by
  unfold oddLocusToInt
  infer_instance

/-- Normalizing the even locus preserves local finite type. -/
instance evenNormalizedLocusToInt_locallyOfFiniteType :
    LocallyOfFiniteType (evenNormalizedLocusToInt n) := by
  unfold evenNormalizedLocusToInt
  infer_instance

/-- Normalizing the odd locus preserves local finite type. -/
instance oddNormalizedLocusToInt_locallyOfFiniteType :
    LocallyOfFiniteType (oddNormalizedLocusToInt n) := by
  unfold oddNormalizedLocusToInt
  infer_instance

/-- Normalizing the even locus preserves quasi-compactness. -/
instance evenNormalizedLocusToInt_quasiCompact : QuasiCompact (evenNormalizedLocusToInt n) := by
  unfold evenNormalizedLocusToInt
  infer_instance

/-- Normalizing the odd locus preserves quasi-compactness. -/
instance oddNormalizedLocusToInt_quasiCompact : QuasiCompact (oddNormalizedLocusToInt n) := by
  unfold oddNormalizedLocusToInt
  infer_instance

end FLT.Mazur.CyclicCharacteristicAtlas
