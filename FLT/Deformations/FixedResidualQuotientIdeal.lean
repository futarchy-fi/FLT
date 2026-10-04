/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.FramedQuotientIdeal
public import FLT.GaloisRepresentation.HardlyRamified.QuadraticQuotientLift

/-!
# Framed equations for the constructed fixed residual quotient lift

The target rank-one representation is W45's constructed integral sign lift.
A chosen coordinate projection in the framed deformation is forced to
intertwine with that representation by a concrete closed ideal.
-/

@[expose] public noncomputable section
open CategoryTheory ThreeAdicPlan
namespace Deformation.ProartinianCat

universe u
variable {k V : Type*} [Field k] [TopologicalSpace k] [DiscreteTopology k]
  [AddCommGroup V] [Module k V]
  (ρ₀ : GaloisRep ℚ k V) (π : V →ₗ[k] k) (hπ : Function.Surjective π)
  (hstable : ∀ g, (LinearMap.ker π).map (ρ₀ g) ≤ LinearMap.ker π)
  (hsquare : ∀ g v, π (ρ₀ g (ρ₀ g v)) = π v)
  {O : Type u} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  (U : ProartinianCat O) (ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) U) (q : Fin 2)

/-- Concrete equations with the quotient character constructed from `ρ₀` and `π`. -/
def fixedResidualQuotientIdeal : Ideal U :=
  framedQuotientIdeal U ρ (fixedQuotientCharacter ρ₀ π hπ hstable hsquare O) q

omit [TopologicalSpace O] [IsTopologicalRing O] in
/-- The actual fixed-quotient condition is a closed ideal condition. -/
theorem fixedResidualQuotientIdeal_closed :
    IsClosed (fixedResidualQuotientIdeal ρ₀ π hπ hstable hsquare U ρ q : Set U) :=
  framedQuotientIdeal_closed U ρ _ q

/-- Its equations refer to the constructed integral Galois representation. -/
theorem kills_fixedResidualQuotientIdeal_iff {A : ProartinianCat O} (f : U ⟶ A) :
    KillsClosedIdeal U (fixedResidualQuotientIdeal ρ₀ π hπ hstable hsquare U ρ q) f ↔
      ∀ g j, f.hom (ρ g q j) = if j = q then
        algebraMap O A (fixedQuotientGaloisRep ρ₀ π hπ hstable hsquare O g 1) else 0 := by
  have hact (g) : fixedQuotientGaloisRep ρ₀ π hπ hstable hsquare O g 1 =
      (fixedQuotientCharacter ρ₀ π hπ hstable hsquare O g : O) := mul_one _
  simp only [hact]
  exact kills_framedQuotientIdeal_iff U ρ _ q f

/-- The fixed-lift equations form a subfunctor of the framed parameter functor. -/
def fixedResidualQuotientCondition : Subfunctor (coyoneda.obj (Opposite.op U)) :=
  closedIdealCondition U (fixedResidualQuotientIdeal ρ₀ π hπ hstable hsquare U ρ q)

/-- Membership in that subfunctor is the actual fixed-representation row condition. -/
theorem fixedResidualQuotientCondition_obj (A : ProartinianCat O) (f : U ⟶ A) :
    f ∈ (fixedResidualQuotientCondition ρ₀ π hπ hstable hsquare U ρ q).obj A ↔
      ∀ g j, f.hom (ρ g q j) = if j = q then
        algebraMap O A (fixedQuotientGaloisRep ρ₀ π hπ hstable hsquare O g 1) else 0 :=
  kills_fixedResidualQuotientIdeal_iff ρ₀ π hπ hstable hsquare U ρ q f

variable [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  (hne : fixedResidualQuotientIdeal ρ₀ π hπ hstable hsquare U ρ q ≠ ⊤)

/-- Maps from the constructed quotient classify exactly these fixed-lift equations. -/
def fixedResidualQuotientFactorEquiv (A : ProartinianCat O) :
    (closedIdealQuotient U (fixedResidualQuotientIdeal ρ₀ π hπ hstable hsquare U ρ q)
      (fixedResidualQuotientIdeal_closed ρ₀ π hπ hstable hsquare U ρ q) hne ⟶ A) ≃
      {f : U ⟶ A // ∀ g j, f.hom (ρ g q j) = if j = q then
        algebraMap O A (fixedQuotientGaloisRep ρ₀ π hπ hstable hsquare O g 1) else 0} :=
  (closedIdealFactorEquiv U _
    (fixedResidualQuotientIdeal_closed ρ₀ π hπ hstable hsquare U ρ q) hne A).trans
    (Equiv.subtypeEquivRight (kills_fixedResidualQuotientIdeal_iff ρ₀ π hπ hstable hsquare U ρ q))

end Deformation.ProartinianCat
