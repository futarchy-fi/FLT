/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentUnitPointNaturality
public import FLT.Mazur.WeierstrassDividedTerminalParameterStructure

/-!
# Evaluating a relative action on a parametrized affine line

Both independent units retain their coefficient maps. Evaluation commutes with
arbitrary maps of test algebras, including maps into nonreduced algebras.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentLineActionEvaluation
open WeierstrassIntegralChart WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {K : Type u} [CommRing K] {Y : Scheme.{u}}
  (s : Y ⟶ Spec (.of K)) (l : Spec (.of (Polynomial K)) ⟶ Y)
  (hl : l ≫ s = Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K))))
local notation "t" => (MultiplicativeGroupScheme.gm K).hom
local notation "p" => Spec.map (CommRingCat.ofHom
  (Polynomial.toLaurent : Polynomial K →+* K[T;T⁻¹]))
local notation "pt" => fun q => (laurentUnitOverPoint (R := K) q).left
variable {B : Type u} [CommRing B] [Algebra K B] (q z : Bˣ)

include hl in
/-- The punctured line point is over the specified coefficient algebra. -/
theorem point_structure :
    (pt z ≫ p ≫ l) ≫ s = Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
  simp only [Category.assoc, hl]
  erw [terminalComponent_algebra_structure (Polynomial.toLaurentAlg (R := K))]
  exact (laurentUnitOverPoint (R := K) z).w

include hl in
/-- The two independent units give an actual point of the relative product. -/
theorem condition : pt q ≫ t = (pt z ≫ p ≫ l) ≫ s := by
  rw [point_structure s l hl]
  exact (laurentUnitOverPoint (R := K) q).w

variable (actMap : pullback (MultiplicativeGroupScheme.gm K).hom s ⟶ Y)

/-- Evaluate the given whole action on its two independent unit inputs. -/
def action : Spec (.of B) ⟶ Y :=
  pullback.lift (pt q) (pt z ≫ p ≫ l) (condition s l hl q z) ≫ actMap

/-- Evaluation of a relative action preserves the source coefficient map. -/
theorem action_structure (ha : actMap ≫ s = pullback.fst t s ≫ t) :
    action s l hl q z actMap ≫ s = Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
  rw [action, Category.assoc, ha, pullback.lift_fst_assoc]
  exact (laurentUnitOverPoint (R := K) q).w

variable {C : Type u} [CommRing C] [Algebra K C] (f : B →ₐ[K] C)

/-- Both original domain projections commute with a change of test algebra. -/
theorem domain_natural :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        pullback.lift (pt q) (pt z ≫ p ≫ l) (condition s l hl q z) =
      pullback.lift (pt (Units.map f.toMonoidHom q))
        (pt (Units.map f.toMonoidHom z) ≫ p ≫ l)
        (condition s l hl (Units.map f.toMonoidHom q) (Units.map f.toMonoidHom z)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    exact laurentUnitOverPoint_natural f q
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd,
      ← Category.assoc, laurentUnitOverPoint_natural]

/-- The whole action formula specializes, with both inputs and the action unchanged. -/
theorem action_natural :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ action s l hl q z actMap =
      action s l hl (Units.map f.toMonoidHom q) (Units.map f.toMonoidHom z) actMap := by
  rw [action, ← Category.assoc, domain_natural s l hl q z f]
  rfl

end FLT.Mazur.LaurentLineActionEvaluation
