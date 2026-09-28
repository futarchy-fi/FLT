/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CategoryD
public import Mathlib.RingTheory.Etale.Descent

/-!
# Integral finite-flat filtrations

An extension retains the two integral Hopf maps, exactness of their induced
geometric point maps, and the canonical torsor comparison for the faithfully
flat quotient. These are model and exactness data, not classification or
ramification hypotheses. Faithfully flat descent proves that extensions of
étale objects are étale.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

variable {R : Type} [CommRing R] [Algebra R ℚ]

/-- The inverse of the chosen generic point comparison, retaining equivariance. -/
def HasFiniteFlatModel.inversePoints {W : FiniteContinuousGaloisModule}
    (M : HasFiniteFlatModel R W) :
    W →+[AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ]
      Additive (ℚ ⊗[R] M.CoordinateRing →ₐ[ℚ] AlgebraicClosure ℚ) := by
  let e := AddEquiv.ofBijective M.points.toAddMonoidHom M.points_bijective
  exact
    { toAddMonoidHom := e.symm.toAddMonoidHom
      map_smul' := fun σ w ↦ by
        apply M.points_bijective.1
        change e (e.symm (σ • w)) = M.points (σ • e.symm w)
        rw [e.apply_symm_apply, map_smul]
        exact congrArg (σ • ·) (e.apply_symm_apply w).symm }

/-- An integral morphism, contravariantly represented on Hopf coordinate algebras. -/
abbrev FiniteFlatObject.Hom (H J : FiniteFlatObject R) :=
  J.model.CoordinateRing →ₐc[R] H.model.CoordinateRing

/-- The geometric point map induced by an integral morphism. -/
def FiniteFlatObject.pointMap {H J : FiniteFlatObject R} (f : H.Hom J) :
    H.points →+[AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ] J.points :=
  J.model.points.comp ((BialgHom.precompPoints
    (Bialgebra.TensorProduct.map (BialgHom.id ℚ ℚ) f)).comp H.model.inversePoints)

/-- An integral extension `0 → A → H → Q → 0`, including its canonical torsor
comparison. The comparison expresses that the fibres of the quotient are
torsors under the kernel, and its formula ties it to the given Hopf maps. -/
structure FiniteFlatExtension (A H Q : FiniteFlatObject R) where
  /-- Pullback along the kernel inclusion. -/
  inclusion : A.Hom H
  /-- Pullback along the quotient morphism. -/
  quotient : H.Hom Q
  /-- The composite inclusion and quotient is the zero group morphism. -/
  compositionZero : inclusion.toAlgHom.comp quotient.toAlgHom =
    (Algebra.ofId R A.model.CoordinateRing).comp (Bialgebra.counitAlgHom R Q.model.CoordinateRing)
  /-- The kernel map on geometric points is injective. -/
  pointsInjective : Function.Injective (FiniteFlatObject.pointMap inclusion)
  /-- The quotient map on geometric points is surjective. -/
  pointsSurjective : Function.Surjective (FiniteFlatObject.pointMap quotient)
  /-- The image on geometric points is precisely the kernel of the quotient. -/
  pointsExact : ∀ h : H.points, FiniteFlatObject.pointMap quotient h = 0 ↔
    ∃ a : A.points, FiniteFlatObject.pointMap inclusion a = h
  /-- The integral quotient morphism is faithfully flat. -/
  quotientFaithfullyFlat : letI := quotient.toAlgHom.toRingHom.toAlgebra
    Module.FaithfullyFlat Q.model.CoordinateRing H.model.CoordinateRing
  /-- The torsor comparison `(h,a) ↦ (h,h+a)` on coordinate rings. -/
  torsorEquiv : letI := quotient.toAlgHom.toRingHom.toAlgebra
    H.model.CoordinateRing ⊗[Q.model.CoordinateRing] H.model.CoordinateRing ≃ₐ[
      H.model.CoordinateRing] H.model.CoordinateRing ⊗[R] A.model.CoordinateRing
  /-- On the second coordinate, the torsor comparison is comultiplication followed
  by the kernel inclusion. Its first coordinate is fixed by algebra-linearity. -/
  torsorEquivSecond : letI := quotient.toAlgHom.toRingHom.toAlgebra
    ∀ b : H.model.CoordinateRing,
      torsorEquiv (1 ⊗ₜ[Q.model.CoordinateRing] b) =
        Algebra.TensorProduct.map (AlgHom.id R H.model.CoordinateRing) inclusion.toAlgHom
          (Coalgebra.comul (R := R) b)

/-- Extensions of étale finite-flat group schemes are étale, by descent through
the faithfully flat quotient and its kernel torsor. -/
theorem FiniteFlatExtension.etale {A H Q : FiniteFlatObject R} (E : FiniteFlatExtension A H Q)
    [Algebra.Etale R A.model.CoordinateRing] [Algebra.Etale R Q.model.CoordinateRing] :
    Algebra.Etale R H.model.CoordinateRing := by
  let : Algebra Q.model.CoordinateRing H.model.CoordinateRing :=
    E.quotient.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R Q.model.CoordinateRing H.model.CoordinateRing := by
    apply IsScalarTower.of_algebraMap_eq'
    exact E.quotient.toAlgHom.comp_algebraMap.symm
  let : Module.FaithfullyFlat Q.model.CoordinateRing H.model.CoordinateRing :=
    E.quotientFaithfullyFlat
  let : Algebra.Etale H.model.CoordinateRing
      (H.model.CoordinateRing ⊗[Q.model.CoordinateRing] H.model.CoordinateRing) :=
    Algebra.Etale.of_equiv E.torsorEquiv.symm
  let : Algebra.Etale Q.model.CoordinateRing H.model.CoordinateRing :=
    Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat H.model.CoordinateRing
  exact Algebra.Etale.comp R Q.model.CoordinateRing H.model.CoordinateRing

/-- A finite filtration by a specified integral finite-flat object. The zero
case has the coordinate algebra of the zero group; each step is an actual
integral extension with the prescribed quotient. -/
inductive HasFiltration : FiniteFlatObject R → FiniteFlatObject R → Prop
  /-- A coordinate algebra isomorphic to the base represents the zero object. -/
  | zero {H Q : FiniteFlatObject R} (e : H.model.CoordinateRing ≃ₐ[R] R) : HasFiltration H Q
  /-- The object itself has a one-step filtration with itself as quotient. -/
  | single (Q : FiniteFlatObject R) : HasFiltration Q Q
  /-- Add one quotient through an integral exact sequence. -/
  | extension {A H Q : FiniteFlatObject R} (E : FiniteFlatExtension A H Q)
      (hA : HasFiltration A Q) : HasFiltration H Q

/-- A finite-flat object filtered by étale group schemes is itself étale. -/
theorem HasFiltration.etale {H Q : FiniteFlatObject R} (hF : HasFiltration H Q)
    (hQ : Algebra.Etale R Q.model.CoordinateRing) :
    Algebra.Etale R H.model.CoordinateRing := by
  induction hF with
  | zero e => exact Algebra.Etale.of_equiv e.symm
  | single _ => exact hQ
  | extension E hA ih =>
    let := hQ
    let := ih hQ
    exact E.etale

end ThreeAdicPlan
