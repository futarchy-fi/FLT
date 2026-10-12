/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSchemeAmbientQuotient
public import FLT.Mazur.SheafPullbackAmbientRefinement

/-!
# Refinement of original Grassmannian quotient projections

The normalized original ambient projection commutes with pullback along an
arbitrary scheme map, retaining the whole quotient and the original base.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
open SheafPullbackPathComparison SheafPullbackAmbientNormalization
universe u
variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] {d : ℕ}
variable {T X : Scheme.{u}} (z : T ⟶ X) (β : X ⟶ Spec (.of R))
  (β' : T ⟶ Spec (.of R)) (hβ : z ≫ β = β')
attribute [local irreducible] Scheme.Modules.pullback comparison
attribute [local irreducible] grassmannianAmbientSheafPullbackIso grassmannianQuotientSheaf

/-- The original ambient sheaf is compatible with arbitrary geometric refinement. -/
@[irreducible] def grassmannianSchemeAmbientRefinementIso :
    (pullback z).obj (grassmannianSchemeAmbient (M := M) β) ≅
      grassmannianSchemeAmbient (M := M) β' := by
  unfold grassmannianSchemeAmbient
  exact (comparison z β β' hβ).app _

variable (p : X ⟶ Spec (.of A)) (g : T ⟶ Spec (.of A))
  (hp : p ≫ Spec.algebraMap R A = β) (hg : z ≫ p = g)
  (hgp : g ≫ Spec.algebraMap R A = β')

/-- Refinement preserves the full normalized quotient map from the original ambient sheaf. -/
theorem grassmannianSchemeQuotientMap_refines
    (N : Module.Grassmannian A (A ⊗[R] M) d) :
    (pullback z).map (grassmannianSchemeQuotientMap β p hp N) ≫
        (comparison z p g hg).hom.app (grassmannianQuotientSheaf N) =
      (grassmannianSchemeAmbientRefinementIso (M := M) z β β' hβ).hom ≫
        grassmannianSchemeQuotientMap β' g hgp N := by
  unfold grassmannianSchemeQuotientMap grassmannianSchemeAmbientIso
    grassmannianSchemeAmbientRefinementIso grassmannianSchemeAmbient
  simpa only [chartIso, id, Iso.app_hom] using
    quotientMap_refines z p (Spec.algebraMap R A) β g β' hp hg hβ hgp
    _ _ (grassmannianAmbientSheafPullbackIso (M := M) (Algebra.ofId R A))
    _ (grassmannianQuotientSheafMap N)

end FLT.Mazur.GrassmannianChart
