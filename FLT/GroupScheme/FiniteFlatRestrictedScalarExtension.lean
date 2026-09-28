/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatScalarExtension
public import FLT.GroupScheme.GenericFieldChange
public import FLT.GroupScheme.RaynaudGenericSplitExtension

/-!
# Restricted Galois points of the actual scalar extension

The generic-field comparison identifies the actual tensor-product model with
the restriction of its original Galois module. A rational split sequence can
therefore supply order-three filtrations of the base-changed models.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/-- The finite continuous Galois module already carried by a finite-flat model. -/
@[implicit_reducible]
def FF.galoisModule (X : FF R K) : FiniteContinuousGaloisModule K where
  Carrier := X.Points

variable [PerfectField K] [IsFractionRing R K]
    (S L : Type) [CommRing S] [Field L] [PerfectField L] [Algebra R S]
    [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    [Algebra K L] [IsScalarTower R K L]

/-- The actual tensor-product model, with its generic points identified with
the restricted original Galois module. -/
@[implicit_reducible]
def FF.restrictedScalarExtension (X : FF R K) : FF S L := by
  let W := X.galoisModule.restrict (algebraMap K L)
  let H := S ⊗[R] X.CoordinateRing
  let : HopfAlgebra.IsFiniteFlat S H := ⟨⟩
  let e : L ⊗[S] H ≃ₐc[L] W.GenericCoordinateAlgebra :=
    (X.scalarExtensionGenericEquiv S L).trans
      ((bialgebraBaseChangeEquiv K L (K ⊗[R] X.CoordinateRing)
        X.galoisModule.GenericCoordinateAlgebra X.genericCoordinates.symm).trans
          X.galoisModule.genericFieldChangeBialgEquiv)
  let M := HasFiniteFlatModel.ofGenericBialgEquiv W H e
  exact
    { CoordinateRing := H
      genericEtale := M.genericEtale
      Points := W
      points := M.points
      points_bijective := M.points_bijective }

/-- A generic map restricts along the same absolute-Galois homomorphism. -/
def GenericGaloisHom.restrictScalars {X Y : FF R K} (f : GenericGaloisHom X Y) :
    GenericGaloisHom (X.restrictedScalarExtension S L) (Y.restrictedScalarExtension S L) where
  toAddMonoidHom := f.toAddMonoidHom
  map_smul' σ x := f.map_smul (Field.absoluteGaloisGroup.map (algebraMap K L) σ) x

/-- Restriction of a split generic sequence remains split, on the actual
base-changed coordinate rings with their restricted point comparisons. -/
def GenericSplitSequence.restrictScalars {A X Q : FF R K}
    (E : GenericSplitSequence A X Q) :
    GenericSplitSequence (A.restrictedScalarExtension S L)
      (X.restrictedScalarExtension S L) (Q.restrictedScalarExtension S L) where
  inclusion := E.inclusion.restrictScalars S L
  retraction := E.retraction.restrictScalars S L
  projection := E.projection.restrictScalars S L
  sectionMap := E.sectionMap.restrictScalars S L
  retract := E.retract
  sectionProjection := E.sectionProjection
  decomposition := E.decomposition

/-- A split generic sequence of order-three groups gives a length-two
filtration of the actual scalar extension of its middle model. -/
theorem GenericSplitSequence.scalarExtension_hasOrderThreeFiltration
    [IsDedekindDomain S] [IsFractionRing S L]
    {A X Q : FF R K} (E : GenericSplitSequence A X Q)
    (hA : Nat.card A.Points = 3) (hQ : Nat.card Q.Points = 3) :
    (X.scalarExtension S L).HasOrderThreeFiltration 2 := by
  have h := (E.restrictScalars S L).hasOrderThreeFiltration hA hQ
  let e : GenericGaloisHom (X.restrictedScalarExtension S L) (X.scalarExtension S L) :=
    (X.restrictedScalarExtension S L).inversePoints
  exact h.of_generic_bijective e (X.restrictedScalarExtension S L).pointsEquiv.symm.bijective

end ThreeAdicPlan
