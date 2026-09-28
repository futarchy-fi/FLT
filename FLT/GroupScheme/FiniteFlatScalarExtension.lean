/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.BialgebraBaseChange
public import FLT.GroupScheme.HopfPoints
public import FLT.GroupScheme.RaynaudModelArithmetic

/-!
# Scalar extension of specified finite-flat models

The coordinate ring of the extended model is the tensor product of the original
coordinate ring. Its generic points are the actual geometric points over the new
field. Thus the construction keeps the original integral model, including when
both the integral base and its fraction field change.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/-- Package a finite-flat Hopf algebra with its actual geometric generic points. -/
def FF.ofCoordinateRing (A : Type) [CommRing A] [HopfAlgebra R A]
    [HopfAlgebra.IsFiniteFlat R A] [Coalgebra.IsCocomm R A]
    [Algebra.Etale K (K ⊗[R] A)] : FF R K := by
  let := HopfAlgebra.pointsCommGroup K (AlgebraicClosure K) (K ⊗[R] A)
  exact
    { CoordinateRing := A
      Points := Additive (K ⊗[R] A →ₐ[K] AlgebraicClosure K)
      points :=
        { toFun := id
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      points_bijective := Function.bijective_id }

variable [PerfectField K] [IsFractionRing R K]
    (S L : Type) [CommRing S] [Field L] [Algebra R S]
    [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    [Algebra K L] [IsScalarTower R K L]

/-- The generic coordinates of scalar extension can instead be computed by
extending the original generic coordinates from `K` to `L`. -/
def FF.scalarExtensionGenericEquiv (X : FF R K) :
    L ⊗[S] (S ⊗[R] X.CoordinateRing) ≃ₐc[L]
      L ⊗[K] (K ⊗[R] X.CoordinateRing) :=
  (bialgebraCancelBaseChange R S L X.CoordinateRing).trans
    (bialgebraCancelBaseChange R K L X.CoordinateRing).symm

/-- The specified model after extending its integral base and generic field. -/
def FF.scalarExtension (X : FF R K) : FF S L := by
  let : HopfAlgebra.IsFiniteFlat S (S ⊗[R] X.CoordinateRing) := ⟨⟩
  let : Algebra.Etale L (L ⊗[S] (S ⊗[R] X.CoordinateRing)) :=
    Algebra.Etale.of_equiv (X.scalarExtensionGenericEquiv S L).symm.toAlgEquiv
  exact FF.ofCoordinateRing (S ⊗[R] X.CoordinateRing)

/-- Extend the specified integral morphism along with its source and target. -/
def ModelHom.scalarExtension {X Y : FF R K} (f : ModelHom X Y) :
    ModelHom (X.scalarExtension S L) (Y.scalarExtension S L) :=
  Bialgebra.TensorProduct.map (BialgHom.id S S) f

/-- Scalar extension of a morphism retains its action on original coordinates. -/
@[simp] theorem ModelHom.scalarExtension_tmul {X Y : FF R K} (f : ModelHom X Y)
    (s : S) (y : Y.CoordinateRing) :
    f.scalarExtension S L (s ⊗ₜ[R] y) = s ⊗ₜ[R] f y := rfl

/-- A generic Hopf morphism extends to the generic coordinates of the actual
base-changed models, through the canonical cancellation comparisons. -/
def GenericGaloisHom.scalarExtensionBialgHom {X Y : FF R K} (f : GenericGaloisHom X Y) :
    L ⊗[S] (Y.scalarExtension S L).CoordinateRing →ₐc[L]
      L ⊗[S] (X.scalarExtension S L).CoordinateRing :=
  (X.scalarExtensionGenericEquiv S L).symm.toBialgHom.comp
    ((Bialgebra.TensorProduct.map (BialgHom.id L L) f.toBialgHom).comp
      (Y.scalarExtensionGenericEquiv S L).toBialgHom)

/-- The number of geometric points does not change with the base or generic
field. Freeness is needed only over the original integral coefficient ring. -/
theorem FF.card_scalarExtension [Nontrivial R] [Nontrivial S]
    (X : FF R K) [Module.Free R X.CoordinateRing] :
    Nat.card (X.scalarExtension S L).Points = Nat.card X.Points := by
  have hcard (T F : Type) [CommRing T] [Nontrivial T] [Field F] [Algebra T F]
      (Y : FF T F) [Module.Free T Y.CoordinateRing] :
      Nat.card Y.Points = Module.finrank T Y.CoordinateRing := by
    rw [← Module.finrank_baseChange (R := F)]
    rw [GaloisModule.finrank_eq_natCard_algHom F (AlgebraicClosure F)]
    exact Nat.card_congr (Equiv.ofBijective Y.points Y.points_bijective).symm
  let : Module.Free S (X.scalarExtension S L).CoordinateRing :=
    inferInstanceAs (Module.Free S (S ⊗[R] X.CoordinateRing))
  rw [hcard S L (X.scalarExtension S L), hcard R K X]
  exact Module.finrank_baseChange

end ThreeAdicPlan
