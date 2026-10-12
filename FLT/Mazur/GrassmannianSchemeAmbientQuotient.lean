/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientBaseChange
public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Original ambient quotients on arbitrary schemes

Normalize a chart quotient against the single ambient sheaf pulled back from
Spec R. The construction works on arbitrary schemes mapping into the chart;
it does not assume that the source is affine.
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
variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] {d : ℕ}
variable {X : Scheme.{u}} (β : X ⟶ Spec (.of R))

/-- The original ambient module pulled back to an arbitrary coefficient scheme. -/
@[irreducible] def grassmannianSchemeAmbient : X.Modules :=
  (pullback β).obj (tilde (ModuleCat.of R (R ⊗[R] M)))

variable (p : X ⟶ Spec (.of A)) (hp : p ≫ Spec.algebraMap R A = β)
attribute [local irreducible] Scheme.Modules.pullback grassmannianAmbientSheafPullbackIso
attribute [local irreducible] comparison

/-- The chart ambient sheaf is canonically the single original ambient sheaf on the source. -/
@[irreducible] def grassmannianSchemeAmbientIso :
    (pullback p).obj (tilde (ModuleCat.of A (A ⊗[R] M))) ≅
      grassmannianSchemeAmbient (M := M) β := by
  unfold grassmannianSchemeAmbient
  exact (pullback p).mapIso
    (grassmannianAmbientSheafPullbackIso (M := M) (Algebra.ofId R A)).symm ≪≫
      (comparison p (Spec.algebraMap R A) β hp).app _

variable (N : Module.Grassmannian A (A ⊗[R] M) d)
attribute [local irreducible] grassmannianQuotientSheaf

/-- The full original chart quotient projected from the global ambient sheaf. -/
def grassmannianSchemeQuotientMap :
    grassmannianSchemeAmbient (M := M) β ⟶ (pullback p).obj (grassmannianQuotientSheaf N) :=
  (grassmannianSchemeAmbientIso β p hp).inv ≫ (pullback p).map (grassmannianQuotientSheafMap N)

/-- Every such original chart projection is epi on the arbitrary source scheme. -/
instance grassmannianSchemeQuotientMap_epi : Epi (grassmannianSchemeQuotientMap β p hp N) := by
  unfold grassmannianSchemeQuotientMap
  infer_instance

/-- The normalized map recovers the entire original pulled-back quotient projection. -/
@[reassoc] theorem grassmannianSchemeAmbientIso_projection :
    (grassmannianSchemeAmbientIso β p hp).hom ≫ grassmannianSchemeQuotientMap β p hp N =
      (pullback p).map (grassmannianQuotientSheafMap N) := by
  simp only [grassmannianSchemeQuotientMap, Iso.hom_inv_id_assoc]

/-- Agreement on this full original ambient quotient determines any outgoing sheaf map. -/
theorem grassmannianSchemeQuotientMap_cancel {Q : X.Modules}
    (f g : (pullback p).obj (grassmannianQuotientSheaf N) ⟶ Q)
    (h : grassmannianSchemeQuotientMap β p hp N ≫ f =
      grassmannianSchemeQuotientMap β p hp N ≫ g) : f = g :=
  (cancel_epi (grassmannianSchemeQuotientMap β p hp N)).mp h

end FLT.Mazur.GrassmannianChart
