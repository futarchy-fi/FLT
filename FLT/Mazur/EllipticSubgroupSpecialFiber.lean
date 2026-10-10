/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupFiniteFlatModel
public import FLT.Mazur.EllipticSubgroupHopfSpecialization

/-!
# The actual special fiber of the finite subgroup closure

The residue-field tensor algebra inherits the constructed Hopf structure and
has the original subgroup rank. Its evaluation points restrict to the actual
reductions of the original integral sections; no reducedness is asserted.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]

/-- The coordinate algebra of the actual residue-field fiber. -/
abbrev GlobalClosureSpecialFiber := IsLocalRing.ResidueField A ⊗[A] GlobalClosure A W H

/-- A point of the actual special fiber obtained from an original integral point. -/
def globalClosureSpecialFiberEvaluation (P : H) :
    GlobalClosureSpecialFiber A W H →ₐ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField A :=
  AlgHom.liftEquiv A (IsLocalRing.ResidueField A) _ _
    (globalClosureSpecializedEvaluation A W H (IsLocalRing.ResidueField A) P)

omit [Finite H] in
/-- Special-fiber evaluation restricts to the original reduced integral evaluation. -/
@[simp] theorem globalClosureSpecialFiberEvaluation_one_tmul (P : H) (a : GlobalClosure A W H) :
    globalClosureSpecialFiberEvaluation A W H P (1 ⊗ₜ[A] a) =
      algebraMap A (IsLocalRing.ResidueField A) (globalClosureEvaluation A W H P a) := by
  change (1 : IsLocalRing.ResidueField A) •
    globalClosureSpecializedEvaluation A W H (IsLocalRing.ResidueField A) P a = _
  exact one_smul _ _

/-- The actual special-fiber point lies over the original specialized integral section. -/
theorem globalClosureSpecialFiberEvaluation_spec (P : H) :
    Spec.map (CommRingCat.ofHom (globalClosureSpecialFiberEvaluation A W H P).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : GlobalClosure A W H →ₐ[A]
          GlobalClosureSpecialFiber A W H).toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A))) ≫
        integralSection A W H P ≫ (gluedClosure A W H 1 2).isoSpec.hom := by
  rw [← Spec.map_comp]
  have he : (globalClosureSpecialFiberEvaluation A W H P).toRingHom.comp
      (Algebra.TensorProduct.includeRight : GlobalClosure A W H →ₐ[A]
        GlobalClosureSpecialFiber A W H).toRingHom =
      (globalClosureSpecializedEvaluation A W H (IsLocalRing.ResidueField A) P).toRingHom := by
    ext a
    exact globalClosureSpecialFiberEvaluation_one_tmul A W H P a
  exact (congrArg (fun f : GlobalClosure A W H →+* IsLocalRing.ResidueField A =>
    Spec.map (CommRingCat.ofHom f)) he).trans
      (globalClosureSpecializedEvaluation_spec A W H (IsLocalRing.ResidueField A) P)

variable [IsDedekindDomain A]

/-- The residue-field fiber has exactly the original subgroup rank. -/
theorem globalClosureSpecialFiber_finrank :
    Module.finrank (IsLocalRing.ResidueField A) (GlobalClosureSpecialFiber A W H) =
      Nat.card H := by
  rw [Module.finrank_baseChange]
  exact globalClosure_finrank A W H

/-- The actual special fiber carries the scalar extension of the original closure Hopf algebra. -/
def globalClosureSpecialFiberHopf (hΔ : IsUnit W.Δ) :
    CommHopfAlgCat (IsLocalRing.ResidueField A) := by
  letI := globalClosureHopfAlgebra A W H hΔ
  exact CommHopfAlgCat.of (IsLocalRing.ResidueField A) (GlobalClosureSpecialFiber A W H)

/-- The special-fiber Hopf packaging retains the actual residue-field tensor algebra. -/
theorem globalClosureSpecialFiberHopf_carrier (hΔ : IsUnit W.Δ) :
    (globalClosureSpecialFiberHopf A W H hΔ : Type) = GlobalClosureSpecialFiber A W H := rfl

end FLT.Mazur.EllipticSubgroupChart
