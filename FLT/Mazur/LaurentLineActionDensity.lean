/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentLineActionEvaluation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Extending a line-action formula from a dominant coefficient evaluation

The domain is reduced and the target separated. Only the test source used to
detect equality is restricted; the resulting whole scheme map specializes freely.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentLineActionEvaluation
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {K : Type u} [CommRing K] {Y : Scheme.{u}}
  (s : Y ⟶ Spec (.of K)) [IsSeparated s] (l : Spec (.of (Polynomial K)) ⟶ Y)
  (hl : l ≫ s = Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K))))
  (actMap : pullback (MultiplicativeGroupScheme.gm K).hom s ⟶ Y)
  (ha : actMap ≫ s = pullback.fst _ _ ≫ (MultiplicativeGroupScheme.gm K).hom)
  {B C : Type u} [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
  [IsReduced (Spec (.of B))] (f : B →ₐ[K] C)
  [IsDominant (Spec.map (CommRingCat.ofHom f.toRingHom))]
  (q z o : Bˣ)
local notation "pt" => fun x => (laurentUnitOverPoint (R := K) x).left
local notation "p" => Spec.map (CommRingCat.ofHom
  (Polynomial.toLaurent : Polynomial K →+* K[T;T⁻¹]))
local notation "fu" => Units.map f.toMonoidHom

include ha in
/-- Equality after a dominant evaluation proves the whole unrestricted action formula. -/
theorem action_eq_of_dominant
    (h : action s l hl (fu q) (fu z) actMap = pt (fu o) ≫ p ≫ l) :
    action s l hl q z actMap = pt o ≫ p ≫ l := by
  refine ext_of_isDominant_of_isSeparated s ?_
    (Spec.map (CommRingCat.ofHom f.toRingHom)) ?_
  · exact (action_structure s l hl q z actMap ha).trans (point_structure s l hl o).symm
  · rw [action_natural, ← Category.assoc, laurentUnitOverPoint_natural]
    exact h

end FLT.Mazur.LaurentLineActionEvaluation
