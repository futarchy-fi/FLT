/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianMorphismRecoveredPoint
public import FLT.Mazur.FiniteProjectiveTildeLocal
public import FLT.Mazur.AffineCoherent

/-!
# Actual quotient sheaves attached to original Grassmannian points

Sheafification retains the whole original relation as a cokernel presentation.
The quotient is finitely presented and locally finite free, and arbitrary scheme
pullbacks retain the cokernel presentation and local finite freeness.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] {d : ℕ}
variable (N : Module.Grassmannian A (A ⊗[R] M) d)

private instance tildePreservesZero : (tilde.functor (.of A)).PreservesZeroMorphisms where
  map_zero _ _ := tilde.map_zero

/-- The actual original relation as a quasi-coherent sheaf. -/
def grassmannianRelationSheaf : (Spec (.of A)).Modules :=
  tilde (ModuleCat.of A N.toSubmodule)

/-- The full original quotient as a quasi-coherent sheaf. -/
def grassmannianQuotientSheaf : (Spec (.of A)).Modules :=
  tilde (ModuleCat.of A ((A ⊗[R] M) ⧸ N.toSubmodule))

/-- Inclusion of the entire relation into the original ambient module sheaf. -/
def grassmannianRelationSheafMap :
    grassmannianRelationSheaf N ⟶ tilde (ModuleCat.of A (A ⊗[R] M)) :=
  (tilde.functor (.of A)).map (ModuleCat.ofHom N.toSubmodule.subtype)

/-- Projection of the original ambient module onto its actual quotient sheaf. -/
def grassmannianQuotientSheafMap :
    tilde (ModuleCat.of A (A ⊗[R] M)) ⟶ grassmannianQuotientSheaf N :=
  (tilde.functor (.of A)).map (ModuleCat.ofHom N.toSubmodule.mkQ)

/-- The quotient projection kills every original relation. -/
@[reassoc] theorem grassmannianRelationSheafMap_comp :
    grassmannianRelationSheafMap N ≫ grassmannianQuotientSheafMap N = 0 := by
  change (tilde.functor (.of A)).map _ ≫ (tilde.functor (.of A)).map _ = _
  rw [← Functor.map_comp]
  have h := (LinearMap.exact_subtype_mkQ N.toSubmodule).linearMap_comp_eq_zero
  rw [← ModuleCat.ofHom_comp, h, ModuleCat.ofHom_zero, Functor.map_zero]
  rfl

/-- The full relation gives the actual sheaf cokernel universal property. -/
def grassmannianQuotientSheafIsCokernel :
    IsColimit (CokernelCofork.ofπ (grassmannianQuotientSheafMap N)
      (grassmannianRelationSheafMap_comp N)) :=
  by
    let i : ModuleCat.of A N.toSubmodule ⟶ ModuleCat.of A (A ⊗[R] M) :=
      ModuleCat.ofHom N.toSubmodule.subtype
    let q : ModuleCat.of A (A ⊗[R] M) ⟶
        ModuleCat.of A ((A ⊗[R] M) ⧸ N.toSubmodule) := ModuleCat.ofHom N.toSubmodule.mkQ
    let h := ModuleCat.isColimitCokernelCofork i q
      (LinearMap.exact_subtype_mkQ N.toSubmodule) N.toSubmodule.mkQ_surjective
    let F : ModuleCat.{u} (CommRingCat.of A) ⥤ (Spec (.of A)).Modules := tilde.functor (.of A)
    let _ : F.IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
    let _ : F.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
    exact CokernelCofork.mapIsColimit _ h F

/-- The quotient sheaf projection is an epimorphism. -/
instance grassmannianQuotientSheafMap_epi : Epi (grassmannianQuotientSheafMap N) :=
  Cofork.IsColimit.epi (grassmannianQuotientSheafIsCokernel N)

/-- Finite presentation holds for the actual original quotient sheaf. -/
instance grassmannianQuotientSheaf_finitePresentation :
    (grassmannianQuotientSheaf N).IsFinitePresentation := by
  let _ := Module.finitePresentation_of_projective A ((A ⊗[R] M) ⧸ N.toSubmodule)
  exact FCurve.affineTilde_isFinitePresentation _

/-- The actual quotient sheaf has finite free charts, constructed from projectivity. -/
theorem grassmannianQuotientSheaf_locallyFiniteFree :
    FCurve.LocallyFiniteFree (grassmannianQuotientSheaf N) :=
  FCurve.finiteProjective_tilde_locallyFiniteFree _

/-- Arbitrary scheme pullback preserves the full quotient presentation. -/
def grassmannianQuotientSheafPullbackIsCokernel {X : Scheme.{u}}
    (g : X ⟶ Spec (.of A)) :
    IsColimit (CokernelCofork.ofπ
      (f := (Scheme.Modules.pullback g).map (grassmannianRelationSheafMap N))
      ((Scheme.Modules.pullback g).map (grassmannianQuotientSheafMap N))
      (by rw [← Functor.map_comp, grassmannianRelationSheafMap_comp, Functor.map_zero])) :=
  CokernelCofork.mapIsColimit _ (grassmannianQuotientSheafIsCokernel N) (Scheme.Modules.pullback g)

/-- Pulling back to any coefficient scheme retains actual finite free charts. -/
theorem grassmannianQuotientSheaf_pullback_locallyFiniteFree {X : Scheme.{u}}
    (g : X ⟶ Spec (.of A)) :
    FCurve.LocallyFiniteFree ((Scheme.Modules.pullback g).obj (grassmannianQuotientSheaf N)) :=
  (grassmannianQuotientSheaf_locallyFiniteFree N).pullback g

end FLT.Mazur.GrassmannianChart
