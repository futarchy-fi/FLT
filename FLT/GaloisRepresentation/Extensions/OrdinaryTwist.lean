/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.ExtendedUnitSubspace
public import FLT.GaloisRepresentation.Extensions.OrdinaryHomCoordinates
public import FLT.GaloisRepresentation.Extensions.LiftBasisTransport

/-!
# Unit membership under ordinary coefficient changes

The unit condition is pulled back along an actual equivariant linear
coordinate map. Scalar changes commute with this transport, including the
b/a factor of the proved lift-basis formula. Simultaneous twists cancel
in the actual Hom character by `homCharacter_twist`.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

open KummerTheory

variable {K L k : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {p : ℕ} [Fact p.Prime] [Field k] [Algebra (ZMod p) k]
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    (roots : ∀ q : Kˣ, ∃ b : Lˣ, b ^ p = Units.map (algebraMap K L) q)
    (A : ValuationSubring K)
    {M : Type*} [AddCommGroup M] [Module k M] [DistribMulAction Gal(L/K) M]
    [SMulCommClass Gal(L/K) k M] [TopologicalSpace M] [DiscreteTopology M]
    (e : M ≃ₗ[k] CharacterModule (primeCyclotomicCharacter (K := K) hζ) k)
    (he : ∀ (g : Gal(L/K)) (x : M), e (g • x) = g • e x)

/-- The unit condition in any proved ordinary coefficient coordinates. -/
def OrdinaryUnitClass (x : ContinuousClass Gal(L/K) M) : Prop :=
  IsExtendedUnitClass hζ k roots A (mapCoefficientClass e.toAddEquiv he x)

omit [IsGalois K L] in
/-- Equivariant linear coordinates commute with actual scalar changes on classes. -/
theorem ordinaryCoordinates_scalar (a : kˣ) (x : ContinuousClass Gal(L/K) M) :
    mapCoefficientClass e.toAddEquiv he
      (mapCoefficientClass (scalarCoefficientEquiv a) (scalarCoefficientEquiv_equivariant a) x) =
    mapCoefficientClass (scalarCoefficientEquiv a) (scalarCoefficientEquiv_equivariant a)
      (mapCoefficientClass e.toAddEquiv he x) := by
  induction x using Quotient.inductionOn with | h c =>
    apply congrArg continuousClassMk
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    exact e.map_smul (a : k) (c.1 g)

/-- All invertible coefficient scalars preserve and reflect ordinary unit membership. -/
theorem ordinaryUnitClass_scalar_iff (a : kˣ) (x : ContinuousClass Gal(L/K) M) :
    OrdinaryUnitClass hζ roots A e he
      (mapCoefficientClass (scalarCoefficientEquiv a) (scalarCoefficientEquiv_equivariant a) x) ↔
        OrdinaryUnitClass hζ roots A e he x := by
  unfold OrdinaryUnitClass
  rw [ordinaryCoordinates_scalar hζ e he]
  exact isExtendedUnitClass_scalar_iff hζ k roots A a _

/-- The actual two-line basis factor b/a preserves the unit condition. -/
theorem ordinaryUnitClass_basis_iff (a b : kˣ) (x : ContinuousClass Gal(L/K) M) :
    OrdinaryUnitClass hζ roots A e he
      (mapCoefficientClass (scalarCoefficientEquiv (b / a))
        (scalarCoefficientEquiv_equivariant (b / a)) x) ↔
      OrdinaryUnitClass hζ roots A e he x :=
  ordinaryUnitClass_scalar_iff hζ roots A e he (b / a) x

omit [IsGalois K L] in
/-- Simultaneous twists preserve the actual ordinary Hom coefficient character. -/
theorem ordinary_homCharacter_twist (α β χ : Gal(L/K) →* kˣ)
    (h : homCharacter α β =
      (Units.map (algebraMap (ZMod p) k).toMonoidHom).comp (primeCyclotomicCharacter hζ)) :
    homCharacter (α * χ) (β * χ) =
      (Units.map (algebraMap (ZMod p) k).toMonoidHom).comp (primeCyclotomicCharacter hζ) := by
  rw [homCharacter_twist, h]

variable (α β : Gal(L/K) →* kˣ)
    (hχ : homCharacter α β = (Units.map (algebraMap (ZMod p) k).toMonoidHom).comp
      (primeCyclotomicCharacter (K := K) hζ))

/-- The basis criterion for the actual Hom coefficient module uses constructed coordinates. -/
theorem ordinaryHomUnit_basis_iff (a b : kˣ)
    (x : ContinuousClass Gal(L/K) (OrdinaryHomModule α β)) :
    OrdinaryUnitClass hζ roots A (ordinaryHomCoordinates α β (primeCyclotomicCharacter hζ))
      (ordinaryHomCoordinates_equivariant α β _ hχ)
      (mapCoefficientClass (scalarCoefficientEquiv (b / a))
        (scalarCoefficientEquiv_equivariant (b / a)) x) ↔
    OrdinaryUnitClass hζ roots A (ordinaryHomCoordinates α β (primeCyclotomicCharacter hζ))
      (ordinaryHomCoordinates_equivariant α β _ hχ) x :=
  ordinaryUnitClass_basis_iff hζ roots A _ _ a b x

/-- Any simultaneous twist preserves unit membership in the actual Hom module. -/
theorem ordinaryHomUnit_twist_iff (ψ : Gal(L/K) →* kˣ)
    (x : ContinuousClass Gal(L/K) (OrdinaryHomModule α β)) :
    OrdinaryUnitClass hζ roots A
      (ordinaryHomCoordinates (α * ψ) (β * ψ) (primeCyclotomicCharacter hζ))
      (ordinaryHomCoordinates_twist_equivariant α β _ hχ ψ)
      (mapCoefficientClass (ordinaryHomTwistEquiv α β ψ)
        (ordinaryHomTwistEquiv_equivariant α β ψ) x) ↔
    OrdinaryUnitClass hζ roots A (ordinaryHomCoordinates α β (primeCyclotomicCharacter hζ))
      (ordinaryHomCoordinates_equivariant α β _ hχ) x := by
  induction x using Quotient.inductionOn with | h c => rfl

/-- Unit membership for the actual lifted-difference cocycle is independent of both line bases. -/
theorem liftedUnitClass_basis_iff {V : Type*} [AddCommGroup V] [Module k V]
    [DistribMulAction Gal(L/K) V] [SMulCommClass Gal(L/K) k V]
    (j : k →ₗ[k] V) (hj : Function.Injective j) (w : V)
    (hw : ∀ g : Gal(L/K), g • w - w ∈ j.toAddMonoidHom.range) (a b : kˣ)
    (c d : ContinuousCocycle Gal(L/K) (CharacterModule (primeCyclotomicCharacter hζ) k))
    (hc : ∀ g, c.1 g = liftCocycle j.toAddMonoidHom w hw g)
    (hd : ∀ g, d.1 g = liftCocycle (lineBasisInjection j a).toAddMonoidHom ((b : k) • w)
      (lift_range_change_bases j w hw a b) g) :
    IsExtendedUnitClass hζ k roots A (continuousClassMk d) ↔
      IsExtendedUnitClass hζ k roots A (continuousClassMk c) := by
  have heq : d = mapCoefficientCocycle (scalarCoefficientEquiv (b / a))
      (scalarCoefficientEquiv_equivariant (b / a)) c := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    rw [hd, liftCocycle_change_bases j hj w hw a b]
    change ((b / a : kˣ) : k) * liftCocycle j.toAddMonoidHom w hw g =
      ((b / a : kˣ) : k) * (show k from c.1 g)
    rw [hc]
  rw [heq]
  exact isExtendedUnitClass_scalar_iff hζ k roots A (b / a) (continuousClassMk c)

end GaloisRepresentation.Extensions
