/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSpecialization

/-!
# Reindexing the actual coefficient gluing

Equal stage expressions give a canonical comparison preserving both projections
and commuting with full coefficient specialization. This permits independent
component constructions to be assembled at one common final stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (j k : ℕ) (hj : j ≤ n) (hk : k ≤ n) (h : j = k)

/-- Change only the expression for a stage of the actual coefficient model. -/
def coefficientShearStageIso :
    coefficientShearGlued hπ data S r j hj ≅ coefficientShearGlued hπ data S r k hk := by
  subst k
  exact Iso.refl _

/-- Reindexing preserves the coefficient projection on the full model. -/
@[reassoc] theorem coefficientShearStageIso_structure :
    (coefficientShearStageIso hπ data S r j k hj hk h).hom ≫
        coefficientShearGluedStructure hπ data S r k hk =
      coefficientShearGluedStructure hπ data S r j hj := by
  subst k
  exact Category.id_comp _

variable (T : Type u) [CommRing T] [Algebra R T] (t : T) (f : S →ₐ[R] T)

/-- Full coefficient specialization commutes with the canonical stage comparison. -/
@[reassoc] theorem coefficientShearStageIso_specialization :
    (coefficientShearStageIso hπ data T t j k hj hk h).hom ≫
        coefficientShearSpecialization hπ data S T r t k hk f =
      coefficientShearSpecialization hπ data S T r t j hj f ≫
        (coefficientShearStageIso hπ data S r j k hj hk h).hom := by
  subst k
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end FLT.Mazur.WeierstrassDividedDepth
