/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicFiniteNeighborhood
public import FLT.Mazur.CyclicCharacteristicNormalizedAtlas

/-!
# Finite type and affine neighborhoods on the combined characteristic atlas

Package the proved properties on the existing Bool-indexed loci. Both the
original and normalized targets are Noetherian and separated, and every finite
orbit of the common relabeling group admits a common affine neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The original characteristic subgroup loci over the integers. -/
def locusToInt : (b : Bool) → locus n b ⟶ Spec (.of ℤ)
  | false => evenLocusToInt n
  | true => oddLocusToInt n

/-- The original subgroup loci are locally of finite type. -/
instance locusToInt_locallyOfFiniteType (b : Bool) : LocallyOfFiniteType (locusToInt n b) := by
  cases b <;> dsimp [locusToInt] <;> infer_instance

/-- The original subgroup loci are quasi-compact over the integers. -/
instance locusToInt_quasiCompact (b : Bool) : QuasiCompact (locusToInt n b) := by
  cases b <;> dsimp [locusToInt] <;> infer_instance

/-- The original subgroup loci are Noetherian. -/
instance locus_isNoetherian (b : Bool) : IsNoetherian (locus n b) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (locusToInt n b)
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (locusToInt n b)

/-- Both original subgroup loci are absolutely separated. -/
instance locus_isSeparated (b : Bool) : (locus n b).IsSeparated := by
  cases b <;> dsimp [locus] <;> infer_instance

/-- Finite sets in either original locus have a common affine neighborhood. -/
theorem locus_hasFiniteNeighborhoods (b : Bool) :
    FiniteAffineNeighborhood.HasNeighborhoods (locus n b) := by
  cases b
  · exact evenLocus_hasFiniteNeighborhoods n
  · exact oddLocus_hasFiniteNeighborhoods n

/-- Both normalized characteristic subgroup loci over the integers. -/
def normalizedLocusToInt (b : Bool) : normalizedLocus n b ⟶ Spec (.of ℤ) :=
  normalizedInclusion n b ≫ locusToInt n b

/-- Both normalized subgroup loci are locally of finite type. -/
instance normalizedLocusToInt_locallyOfFiniteType (b : Bool) :
    LocallyOfFiniteType (normalizedLocusToInt n b) := by
  unfold normalizedLocusToInt
  infer_instance

/-- Both normalized subgroup loci are quasi-compact over the integers. -/
instance normalizedLocusToInt_quasiCompact (b : Bool) :
    QuasiCompact (normalizedLocusToInt n b) := by
  unfold normalizedLocusToInt
  infer_instance

/-- Both normalized subgroup loci are Noetherian. -/
instance normalizedLocus_isNoetherian (b : Bool) : IsNoetherian (normalizedLocus n b) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (normalizedLocusToInt n b)
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (normalizedLocusToInt n b)

/-- Both normalized subgroup loci are absolutely separated. -/
instance normalizedLocus_isSeparated (b : Bool) : (normalizedLocus n b).IsSeparated := by
  cases b <;> dsimp [normalizedLocus] <;> infer_instance

/-- Finite sets in either normalized locus have a common affine neighborhood. -/
theorem normalizedLocus_hasFiniteNeighborhoods (b : Bool) :
    FiniteAffineNeighborhood.HasNeighborhoods (normalizedLocus n b) :=
  FiniteAffineNeighborhood.of_affineHom (normalizedInclusion n b)
    (locus_hasFiniteNeighborhoods n b)

end FLT.Mazur.CyclicCharacteristicAtlas
