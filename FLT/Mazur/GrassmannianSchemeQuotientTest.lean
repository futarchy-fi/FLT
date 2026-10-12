/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSchemeAmbientQuotient
public import FLT.Mazur.GrassmannianAmbientCompositionLaw
public import FLT.Mazur.GrassmannianQuotientSheafTransition
public import FLT.Mazur.SheafPullbackAmbientMatch
public import FLT.Mazur.SheafPullbackAmbientCoherence

/-!
# Original global Grassmannian projections on affine tests

The normalized projection from the single base ambient sheaf recovers the
entire coordinate quotient projection on every compatible affine test.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
open SheafPullbackPathComparison
universe u
variable {R A D M : Type u} [CommRing R] [CommRing A] [CommRing D]
  [Algebra R A] [Algebra R D] [AddCommGroup M] [Module R M] {d : ℕ}
variable {X : Scheme.{u}} (β : X ⟶ Spec (.of R)) (z : Spec (.of D) ⟶ X)
  (hz : z ≫ β = Spec.algebraMap R D)
attribute [local irreducible] Scheme.Modules.pullback grassmannianAmbientSheafPullbackIso
attribute [local irreducible] comparison grassmannianQuotientSheaf

/-- The single base ambient sheaf on an affine coefficient test. -/
@[irreducible] def grassmannianSchemeAmbientTestIso :
    (pullback z).obj (grassmannianSchemeAmbient (M := M) β) ≅
      tilde (ModuleCat.of D (D ⊗[R] M)) := by
  unfold grassmannianSchemeAmbient
  exact SheafPullbackAmbientNormalization.testIso z β (Spec.algebraMap R D) hz
    (tilde (ModuleCat.of R (R ⊗[R] M))) (tilde (ModuleCat.of D (D ⊗[R] M)))
    (grassmannianAmbientSheafPullbackIso (Algebra.ofId R D))

variable (p : X ⟶ Spec (.of A)) (hp : p ≫ Spec.algebraMap R A = β)
  (f : A →ₐ[R] D) (hf : z ≫ p = Spec.map (CommRingCat.ofHom f.toRingHom))
  (N : Module.Grassmannian A (A ⊗[R] M) d)

/-- The original chart and test comparisons form the actual ambient square. -/
theorem grassmannianSchemeAmbientIso_matches :
    SheafPullbackAmbientMatch.Matches (pullback p) (pullback z)
      (pullback (Spec.map (CommRingCat.ofHom f.toRingHom))) (comparison z p _ hf)
      (grassmannianSchemeAmbientIso (M := M) β p hp)
      (grassmannianSchemeAmbientTestIso β z hz)
      (grassmannianAmbientSheafPullbackIso (M := M) f) := by
  have hw : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.algebraMap R A =
      Spec.algebraMap R D := by rw [← hf, Category.assoc, hp, hz]
  have hc := grassmannianBaseAmbientComposes (M := M) f hw
  unfold grassmannianSchemeAmbientTestIso grassmannianSchemeAmbientIso
    grassmannianSchemeAmbient
  simpa only [SheafPullbackAmbientNormalization.chartIso, id] using
    SheafPullbackAmbientSectionMatch.toMatch
      (Spec.map (CommRingCat.ofHom f.toRingHom)) (Spec.algebraMap R A)
      (Spec.algebraMap R D) hw (tilde (ModuleCat.of R (R ⊗[R] M)))
      (grassmannianAmbientSheafPullbackIso (M := M) (Algebra.ofId R A))
      (grassmannianAmbientSheafPullbackIso (M := M) f)
      (grassmannianAmbientSheafPullbackIso (M := M) (Algebra.ofId R D)) hc z p β hp hf hz

/-- The normalized global projection recovers the full original coefficient projection. -/
theorem grassmannianSchemeQuotientMap_test :
    (grassmannianSchemeAmbientTestIso β z hz).inv ≫
      (pullback z).map (grassmannianSchemeQuotientMap β p hp N) =
    grassmannianRefinedQuotientMap f N ≫ (comparison z p _ hf).inv.app
      (grassmannianQuotientSheaf N) := by
  unfold grassmannianSchemeQuotientMap grassmannianRefinedQuotientMap
  exact SheafPullbackAmbientMatch.projection (pullback p) (pullback z)
    (pullback (Spec.map (CommRingCat.ofHom f.toRingHom))) (comparison z p _ hf)
    (grassmannianSchemeAmbientIso (M := M) β p hp)
    (grassmannianSchemeAmbientTestIso β z hz) (grassmannianAmbientSheafPullbackIso f)
    (grassmannianSchemeAmbientIso_matches β z hz p hp f hf) (grassmannianQuotientSheafMap N)

end FLT.Mazur.GrassmannianChart
