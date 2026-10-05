/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTensorCocycleTransport
public import FLT.Mazur.AffineModuleCoalgebraDescent

/-!
# Recover tensor overlap data from faithfully flat coalgebras

Effective module descent supplies a coefficient isomorphism from a scalar
extension. Transport its canonical cocycle along that isomorphism; the
reconstruction square proves recovery of the specified original coaction.
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct
open FLT.Mazur.AffineModuleCoalgebraDescent

universe u

namespace FLT.Mazur.AffineTensorCocycle

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.FaithfullyFlat)

/-- Recover an overlap cocycle from a scalar-extension coalgebra. -/
def fromCoalgebra (D : AffineModuleCoalgebraDescent.Data φ) :
    letI := φ.hom.toAlgebra
    letI := Module.compHom D.A φ.hom
    letI : IsScalarTower R S D.A := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    Datum R S D.A := by
  letI := φ.hom.toAlgebra
  letI := Module.compHom D.A φ.hom
  letI : IsScalarTower R S D.A := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  exact transportDatum (canonicalDatum (descendedModule φ hφ D))
    (coefficientIso φ hφ D).toLinearEquiv

/-- Recovery gives exactly the original coaction, not an isomorphic replacement. -/
theorem fromCoalgebra_coaction (D : AffineModuleCoalgebraDescent.Data φ) :
    (toCoalgebra φ D.A (fromCoalgebra φ hφ D)).a = D.a := by
  let := φ.hom.toAlgebra
  let := Module.compHom D.A φ.hom
  let : IsScalarTower R S D.A := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  dsimp only [toCoalgebra]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro n
  have h := congrArg (fun f ↦ f.hom ((coefficientIso φ hφ D).inv n))
    (coefficientIso_coaction φ hφ D)
  simp only [Adjunction.toComonad_coe, Functor.comp_obj, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, Iso.inv_hom_id_apply,
    Comonad.comparison_obj_A, Comonad.comparison_obj_a, Functor.comp_map] at h
  erw [h]
  change (transportDatum (canonicalDatum (descendedModule φ hφ D))
    (coefficientIso φ hφ D).toLinearEquiv).coaction n = _
  rw [transportDatum_coaction]
  change ((show S ⊗[R] descendedModule φ hφ D →ₗ[S] D.A from
    (coefficientIso φ hφ D).hom.hom).restrictScalars R).lTensor S
    (canonicalOverlap (descendedModule φ hφ D)
      (((coefficientIso φ hφ D).inv n) ⊗ₜ[R] (1 : S))) = _
  generalize (coefficientIso φ hφ D).inv n = x
  induction x using TensorProduct.inductionOn with
  | tmul s m => rfl
  | add x y hx hy => simp only [map_add, add_tmul, hx, hy]

/-- Recovered tensor data reconstruct the original coalgebra by the identity on coefficients. -/
def fromCoalgebraIso (D : AffineModuleCoalgebraDescent.Data φ) :
    toCoalgebra φ D.A (fromCoalgebra φ hφ D) ≅ D :=
  Comonad.Coalgebra.isoMk (Iso.refl _) (by
    change (toCoalgebra φ D.A (fromCoalgebra φ hφ D)).a ≫
      (ModuleCat.extendRestrictScalarsAdj φ.hom).toComonad.toFunctor.map (𝟙 D.A) = 𝟙 D.A ≫ D.a
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
    exact fromCoalgebra_coaction φ hφ D)

/-- The reverse translation recovers the specified overlap isomorphism. -/
theorem fromCoalgebra_toCoalgebra_overlap (M : ModuleCat.{u} S) :
    letI := φ.hom.toAlgebra
    letI := Module.compHom M φ.hom
    letI : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    ∀ D : Datum R S M,
      (show Datum R S M from fromCoalgebra φ hφ (toCoalgebra φ M D)).overlap = D.overlap := by
  let := φ.hom.toAlgebra
  let := Module.compHom M φ.hom
  let : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  intro D
  apply Datum.overlap_eq_of_coaction_eq
  exact congrArg ModuleCat.Hom.hom (fromCoalgebra_coaction φ hφ (toCoalgebra φ M D))

end FLT.Mazur.AffineTensorCocycle
