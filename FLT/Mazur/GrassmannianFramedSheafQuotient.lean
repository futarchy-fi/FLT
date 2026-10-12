/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSheafQuotientPoint

/-!
# Grassmannian points from actual sheaf frames

An actual finite frame of an affine sheaf quotient constructs the full original
relation point. Neither its algebraic presentation nor a splitting of its
ambient projection is required as input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M τ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype τ] {d : ℕ}
variable {P : (Spec (.of A)).Modules}
  (p : tilde (ModuleCat.of A (A ⊗[R] M)) ⟶ P) [Epi p]
variable (e : P ≅ SheafOfModules.free τ) (hd : Fintype.card τ = d)

include hd in
/-- A finite frame has the prescribed rank at every actual prime of its coefficient ring. -/
theorem framedQuotient_rank (x : PrimeSpectrum A) :
    Module.rankAtStalk (R := A) (τ →₀ A) x = d := by
  let _ := x.nontrivial
  rw [Module.rankAtStalk_eq_finrank_of_free]
  change Module.finrank A (τ →₀ A) = d
  rw [Module.finrank_finsupp, Module.finrank_self, mul_one, hd]

/-- Construct the original relation point directly from an affine sheaf quotient frame. -/
def framedSheafQuotientPoint : Module.Grassmannian A (A ⊗[R] M) d :=
  sheafQuotientPoint p (ModuleCat.of A (τ →₀ A)) (tildeFinsupp τ ≪≫ e.symm)
    (framedQuotient_rank hd)

/-- The frame constructs an isomorphism from the full algebraic quotient to the given sheaf. -/
def framedSheafQuotientIso :
    grassmannianQuotientSheaf (framedSheafQuotientPoint p e hd) ≅ P :=
  sheafQuotientPointIso p (ModuleCat.of A (τ →₀ A)) (tildeFinsupp τ ≪≫ e.symm)
    (framedQuotient_rank hd)

/-- The constructed identification retains the original ambient epimorphism. -/
@[reassoc] theorem framedSheafQuotientIso_projection :
    grassmannianQuotientSheafMap (framedSheafQuotientPoint p e hd) ≫
      (framedSheafQuotientIso p e hd).hom = p :=
  sheafQuotientPointIso_projection p _ _ _

/-- Any two target presentations recover the same full original relation point. -/
theorem sheafQuotientPoint_eq_of_projection
    (N : Module.Grassmannian A (A ⊗[R] M) d)
    (a : grassmannianQuotientSheaf N ≅ P)
    (ha : grassmannianQuotientSheafMap N ≫ a.hom = p) :
    N = framedSheafQuotientPoint p e hd := by
  apply grassmannianPoint_eq_of_quotientSheafIso N _ (a ≪≫ (framedSheafQuotientIso p e hd).symm)
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ha]
  apply (cancel_mono (framedSheafQuotientIso p e hd).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (framedSheafQuotientIso_projection p e hd).symm

/-- Changing the frame, even its index type, preserves every original relation. -/
theorem framedSheafQuotientPoint_independent {σ : Type u} [Fintype σ]
    (e' : P ≅ SheafOfModules.free σ) (hd' : Fintype.card σ = d) :
    framedSheafQuotientPoint p e hd = framedSheafQuotientPoint p e' hd' :=
  sheafQuotientPoint_eq_of_projection p e' hd' _ (framedSheafQuotientIso p e hd)
    (framedSheafQuotientIso_projection p e hd)

end FLT.Mazur.GrassmannianChart
