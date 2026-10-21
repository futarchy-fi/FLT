/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGroupFiniteness
public import FLT.Mazur.AuxiliarySeparatedMarkingFiniteType
public import FLT.Mazur.CyclicBoundaryUnrestrictedAmpleCoverage

/-!
# Finite type unrestricted charts for arbitrary original generalized curves

The complete marking scheme, closed cyclic locus and ample open are locally
of finite type and separated over the original base. Over a Noetherian base
all three charts are quasi-compact and locally of finite presentation.
No smoothness of the entire curve or restriction on residue characteristic
is imposed. These are relative charts over a supplied family, not versal families.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]

/-- The entire independent marking parameter is separated over every original base. -/
instance originalParameter_separated : IsSeparated (parameter E.group n).hom :=
  AuxiliaryLevel.homScheme_separated E.group (Label n)

/-- All independent markings have locally finite type parameters, also on singular families. -/
instance originalParameter_locallyOfFiniteType :
    LocallyOfFiniteType (parameter E.group n).hom :=
  AuxiliaryLevel.homScheme_locallyOfFiniteType_of_separated E.group (Label n)

/-- The structure map of the closed cyclic locus to the original coefficient base. -/
def unrestrictedLocusBase : unrestrictedMultiplicationLocus E n ⟶ S :=
  unrestrictedMultiplicationLocusInclusion E n ≫ (parameter E.group n).hom

/-- The structure map of the ample open to the same original coefficient base. -/
def unrestrictedAmpleBase : (unrestrictedAmpleOpen E n).toScheme ⟶ S :=
  (unrestrictedAmpleOpen E n).ι ≫ unrestrictedLocusBase E n

instance unrestrictedLocusBase_separated : IsSeparated (unrestrictedLocusBase E n) :=
  inferInstanceAs (IsSeparated (_ ≫ (parameter E.group n).hom))

instance unrestrictedLocusBase_locallyOfFiniteType :
    LocallyOfFiniteType (unrestrictedLocusBase E n) :=
  inferInstanceAs (LocallyOfFiniteType (_ ≫ (parameter E.group n).hom))

instance unrestrictedAmpleBase_separated : IsSeparated (unrestrictedAmpleBase E n) :=
  inferInstanceAs (IsSeparated ((unrestrictedAmpleOpen E n).ι ≫ _))

instance unrestrictedAmpleBase_locallyOfFiniteType :
    LocallyOfFiniteType (unrestrictedAmpleBase E n) :=
  inferInstanceAs (LocallyOfFiniteType ((unrestrictedAmpleOpen E n).ι ≫ _))

variable [IsNoetherian S]

instance originalParameter_quasiCompact : QuasiCompact (parameter E.group n).hom :=
  AuxiliaryLevel.homScheme_quasiCompact_of_separated E.group (Label n)

instance unrestrictedLocusBase_quasiCompact : QuasiCompact (unrestrictedLocusBase E n) :=
  inferInstanceAs (QuasiCompact (_ ≫ (parameter E.group n).hom))

/-- The full closed chart is Noetherian over a Noetherian original coefficient base. -/
instance unrestrictedLocus_isNoetherian : IsNoetherian (unrestrictedMultiplicationLocus E n) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (unrestrictedLocusBase E n)
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (unrestrictedLocusBase E n)

/-- The actual ample open is Noetherian, including its singular-family parameters. -/
instance unrestrictedAmple_isNoetherian : IsNoetherian (unrestrictedAmpleOpen E n).toScheme := by
  let _ : NoetherianSpace (unrestrictedAmpleOpen E n).toScheme :=
    Topology.IsEmbedding.subtypeVal.isInducing.noetherianSpace
  exact {
    toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (unrestrictedAmpleBase E n)
    toCompactSpace := inferInstance }

instance unrestrictedAmpleBase_quasiCompact : QuasiCompact (unrestrictedAmpleBase E n) := by
  infer_instance

/-- The closed chart has finite presentation locally over every Noetherian original base. -/
theorem unrestrictedLocusBase_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (unrestrictedLocusBase E n) := inferInstance

/-- The ample chart has finite presentation locally over every Noetherian original base. -/
theorem unrestrictedAmpleBase_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (unrestrictedAmpleBase E n) := inferInstance

end FLT.Mazur.CyclicBoundaryParameter
