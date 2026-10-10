/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupGenericHopfComparison
public import FLT.GroupScheme.IntegralCartierPoints
public import FLT.GroupScheme.HopfTorsor
public import FLT.GroupScheme.RaynaudModelArithmetic

/-!
# The original subgroup closure as a finite flat arithmetic model

The actual global coordinate algebra is finite flat with split étale generic
fiber. The proved generic Hopf comparison supplies its abelian geometric point
group, so it can be used by the existing finite-flat rigidity interface.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open HopfAlgebra HopfAlgebra.CartierDual

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] globalClosureGenericHopfEquiv

variable {K : Type} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]

/-- The actual generic closure algebra is split étale. -/
instance globalClosure_generic_etale : Algebra.Etale K (K ⊗[A] GlobalClosure A W H) :=
  Algebra.Etale.of_equiv (globalClosureGenericEquiv A W H).symm

variable [IsDedekindDomain A]

/-- The original global coordinate ring satisfies the arithmetic finite-flat predicate. -/
instance globalClosure_isFiniteFlat : IsFiniteFlat A (GlobalClosure A W H) := ⟨⟩

/-- The original generic bialgebra equivalence also preserves antipodes. -/
theorem globalClosureGenericHopfEquiv_antipode (hΔ : IsUnit W.Δ) :
    letI := globalClosureHopfAlgebra A W H hΔ
    (antipodeAlgHom K (CartierDual K (MonoidAlgebra K (Multiplicative H)))).comp
      (globalClosureGenericHopfEquiv A W H hΔ).toAlgEquiv.toAlgHom =
    (globalClosureGenericHopfEquiv A W H hΔ).toAlgEquiv.toAlgHom.comp
      (antipodeAlgHom K (K ⊗[A] GlobalClosure A W H)) := by
  let _ := globalClosureHopfAlgebra A W H hΔ
  have he := antipodeAlgHom_comp_bialgHom (R := K)
    (A := CartierDual K (MonoidAlgebra K (Multiplicative H)))
    (B := K ⊗[A] GlobalClosure A W H) (globalClosureGenericHopfEquiv A W H hΔ).toBialgHom
  apply AlgHom.ext
  intro x
  exact AlgHom.congr_fun he x

/-- The actual closure is a finite-flat model with its identified generic geometric points. -/
def globalClosureFiniteFlatModel (hΔ : IsUnit W.Δ) : ThreeAdicPlan.FF A K := by
  letI := globalClosureHopfAlgebra A W H hΔ
  letI := pointsCommGroup K (AlgebraicClosure K)
    (CartierDual K (MonoidAlgebra K (Multiplicative H)))
  letI : MulDistribMulAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (CartierDual K (MonoidAlgebra K (Multiplicative H)) →ₐ[K] AlgebraicClosure K) :=
    instMulDistribMulActionAlgEquivAlgHom_fLT K (AlgebraicClosure K)
      (A := CartierDual K (MonoidAlgebra K (Multiplicative H)))
  let E := (precompPointsEquiv (K := K) (A := K ⊗[A] GlobalClosure A W H)
    (B := CartierDual K (MonoidAlgebra K (Multiplicative H))) (AlgebraicClosure K)
    (globalClosureGenericHopfEquiv A W H hΔ)).symm
  exact
    { CoordinateRing := GlobalClosure A W H
      Points := Additive (CartierDual K (MonoidAlgebra K (Multiplicative H)) →ₐ[K]
        AlgebraicClosure K)
      points := { E.toAddMonoidHom with map_smul' := fun _ _ => rfl }
      points_bijective := E.bijective }

/-- Packaging the model retains the original coordinate ring definitionally. -/
theorem globalClosureFiniteFlatModel_coordinates (hΔ : IsUnit W.Δ) :
    (globalClosureFiniteFlatModel A W H hΔ).CoordinateRing = GlobalClosure A W H := rfl

/-- Over a perfect generic field the actual integral Hopf algebra is cocommutative. -/
theorem globalClosureHopf_isCocomm [PerfectField K] (hΔ : IsUnit W.Δ) :
    letI := globalClosureHopfAlgebra A W H hΔ
    Coalgebra.IsCocomm A (GlobalClosure A W H) := by
  let _ := globalClosureHopfAlgebra A W H hΔ
  exact ThreeAdicPlan.FF.cocomm (globalClosureFiniteFlatModel A W H hΔ)

end FLT.Mazur.EllipticSubgroupChart
