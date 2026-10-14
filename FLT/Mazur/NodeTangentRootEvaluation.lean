/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentAlgebra

/-!
# Evaluating the actual tangent cover at a chosen root

Any root over a coefficient algebra gives an actual point of the original
quadratic cover. Companion-root evaluation is composition with its involution.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
  (S : Type v) [CommRing S] [Algebra R S] (r : S)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)

/-- Evaluation of the original tangent algebra at a root over any coefficient algebra. -/
def nodeTangentRootEvaluation : AdjoinRoot (nodeTangentPolynomial W) →ₐ[R] S :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R S) r (by
    rw [nodeTangentPolynomial_eval₂]
    exact hr)

/-- Evaluation retains the chosen root exactly. -/
@[simp] theorem nodeTangentRootEvaluation_root :
    nodeTangentRootEvaluation W S r hr (AdjoinRoot.root (nodeTangentPolynomial W)) = r :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

include hr in
/-- The companion is a root without a characteristic or invertibility assumption. -/
theorem nodeTangentCompanion_equation :
    (-algebraMap R S W.a₁ - r) ^ 2 +
        algebraMap R S W.a₁ * (-algebraMap R S W.a₁ - r) - algebraMap R S W.a₂ = 0 := by
  linear_combination hr

/-- Evaluation at the companion is the actual original quadratic conjugation. -/
theorem nodeTangentRootEvaluation_conjugation :
    (nodeTangentRootEvaluation W S r hr).comp (nodeTangentConjugation W).toAlgHom =
      nodeTangentRootEvaluation W S (-algebraMap R S W.a₁ - r)
        (nodeTangentCompanion_equation W S r hr) := by
  apply AdjoinRoot.algHom_ext
  change nodeTangentRootEvaluation W S r hr
    (nodeTangentConjugationHom W (AdjoinRoot.root _)) = _
  rw [nodeTangentConjugationHom_root, map_sub, map_neg, AlgHom.commutes,
    nodeTangentRootEvaluation_root, nodeTangentRootEvaluation_root]

/-- A named companion gives the same equality, with the original chosen roots retained. -/
theorem nodeTangentRootEvaluation_companion (t : S)
    (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
    (hrt : r + t = -algebraMap R S W.a₁) :
    (nodeTangentRootEvaluation W S r hr).comp (nodeTangentConjugation W).toAlgHom =
      nodeTangentRootEvaluation W S t ht := by
  rw [nodeTangentRootEvaluation_conjugation]
  congr 1
  linear_combination -hrt

/-- Coefficient specialization of an evaluated root still evaluates the original tangent algebra. -/
theorem nodeTangentRootEvaluation_map {T : Type*} [CommRing T] [Algebra R T]
    (f : S →ₐ[R] T) (t : T)
    (ht : t ^ 2 + algebraMap R T W.a₁ * t - algebraMap R T W.a₂ = 0)
    (hrt : f r = t) :
    f.comp (nodeTangentRootEvaluation W S r hr) = nodeTangentRootEvaluation W T t ht := by
  apply AdjoinRoot.algHom_ext
  simpa only [AlgHom.comp_apply, nodeTangentRootEvaluation_root] using hrt

end FLT.Mazur
