/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.OrdinaryFiniteRootRatio
public import FLT.GroupScheme.OrdinaryIntegralFiberGalois
public import FLT.GroupScheme.KummerUnitTransport
public import FLT.GaloisRepresentation.Extensions.OrdinaryFiniteRootClass
public import FLT.GroupScheme.AlgebraicClosureKummer

/-!
# The ordinary class has the constructed integral Kummer parameter

The root of the integral unit is obtained by evaluating the original fibre.
Its field-action ratio is exactly the extracted ordinary root cocycle.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HopfAlgebra
open NumberField IsLocalRing GaloisRepresentation.Extensions KummerTheory
namespace ThreeAdicPlan

variable {K k : Type} [Field K] [NumberField K] [Field k] [Finite k]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) k] [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K)) [Module k X.Points]
  [SMulCommClass (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) k X.Points]
  {α β : (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) →* kˣ}
  (E : OrdinaryFiltration (Representation.ofDistribMulAction k
    (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) X.Points) α β)
  {ζ : (AlgebraicClosure (v.adicCompletion K))ˣ} (hζ : IsPrimitiveRoot ζ p)
  (hα : α = (Units.map (algebraMap (ZMod p) k).toMonoidHom).comp
    (primeCyclotomicCharacter hζ))

local instance : Finite (Module.Dual (ZMod p) k) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

local instance : IsDedekindDomain (v.adicCompletionIntegers K) :=
  IsPrincipalIdealRing.isDedekindDomain _

variable (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)

variable (hβ : β = 1) (a : Module.Dual (ZMod p) k)

/-- The actual quotient arrow defines the fibre algebra. -/
local instance finiteKummerAlgebra :
    Algebra (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotient.toAlgHom.toRingHom.toAlgebra

/-- The quotient arrow respects the local base. -/
local instance finiteKummerTower : IsScalarTower (v.adicCompletionIntegers K)
    (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  IsScalarTower.of_algebraMap_eq'
    (ordinaryModelExtension X E).quotient.toAlgHom.comp_algebraMap.symm

/-- Faithful flatness is supplied by the constructed ordinary extension. -/
local instance finiteKummerFaithfullyFlat :
    Module.FaithfullyFlat (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotientFaithfullyFlat

variable [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace X.Points] [DiscreteTopology X.Points]
  (hρ : ∀ x : X.Points, Continuous
    (fun g : AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K) ↦ g • x))

/-- Evaluate the integral generator at an original vector above one. -/
def ordinaryFiniteKummerRoot (w : X.Points) (hw : E.projection w = 1) :
    (AlgebraicClosure (v.adicCompletion K))ˣ :=
  Units.map (ordinaryIntegralFiberPoint X E hβ w hw).toMonoidHom
    (ordinaryFiniteFiberGenerator v p X E hζ hα he hβ a)

/-- Its field-action ratio is the original ordinary cocycle in root coordinates. -/
theorem ordinaryFiniteKummerRoot_ratio (w : X.Points) (hw : E.projection w = 1)
    (g : AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) :
    unitRatio (ordinaryFiniteKummerRoot v p X E hζ hα he hβ a w hw) g =
      rootUnit (primeRootCoordinates hζ
        (a ((show k →ₗ[k] k from (E.cocycleOf hρ w hw).val g) 1))) := by
  have h := ordinaryFiniteFiberGenerator_ratio v p X E hζ hα he hβ a hρ w hw g
  rw [ordinaryIntegralFiberPoint_galois X E hβ w hw g] at h
  exact h

omit [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  [TopologicalSpace k] [DiscreteTopology k] [Finite k] in
include hα hβ in
/-- The character ratio is cyclotomic when the quotient character is trivial. -/
theorem ordinaryFinite_homCharacter :
    homCharacter α β = (Units.map (algebraMap (ZMod p) k).toMonoidHom).comp
      (primeCyclotomicCharacter hζ) := by
  simp [homCharacter, hβ, hα]

/-- The original root-valued extension class has the explicitly constructed integral parameter. -/
theorem ordinaryFiniteRootClass_parameter
    (roots : ∀ q : (v.adicCompletion K)ˣ, ∃ b : (AlgebraicClosure (v.adicCompletion K))ˣ,
      b ^ p = Units.map (algebraMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))) q)
    (w : X.Points) (hw : E.projection w = 1) :
    continuousClassMk
      (E.finiteRootCocycle hζ α β (ordinaryFinite_homCharacter v p hζ hα hβ) hρ a w hw) =
    parameterClass roots (Units.map (algebraMap (v.adicCompletionIntegers K)
      (v.adicCompletion K)).toMonoidHom (ordinaryFiniteUnitParameter v p X E hζ hα he hβ a)) := by
  let q := Units.map (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K)).toMonoidHom (ordinaryFiniteUnitParameter v p X E hζ hα he hβ a)
  let b := ordinaryFiniteKummerRoot v p X E hζ hα he hβ a w hw
  have hb : b ^ p = Units.map
      (algebraMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))) q := by
    exact ordinaryFiniteUnitParameter_evaluation v p X E hζ hα he hβ a w hw
  have hc : E.finiteRootCocycle hζ α β (ordinaryFinite_homCharacter v p hζ hα hβ) hρ a w hw =
      continuousRootCocycle q b hb := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    apply rootUnit_injective
    exact (ordinaryFiniteKummerRoot_ratio v p X E hζ hα he hβ a hρ w hw g).symm
  rw [hc]
  exact continuousRootCocycle_independent q b (roots q).choose hb (roots q).choose_spec

include he in
/-- The actual root cocycle belongs to the independently defined integral unit subgroup. -/
theorem ordinaryFiniteRootClass_unit (w : X.Points) (hw : E.projection w = 1) :
    IsUnitContinuousClass (exists_unit_root (L := AlgebraicClosure (v.adicCompletion K)))
      (v.adicCompletionIntegers K)
      (continuousClassMk
        (E.finiteRootCocycle hζ α β (ordinaryFinite_homCharacter v p hζ hα hβ) hρ a w hw)) := by
  rw [ordinaryFiniteRootClass_parameter v p X E hζ hα he hβ a hρ
    (exists_unit_root (L := AlgebraicClosure (v.adicCompletion K))) w hw]
  change IsUnitClass (v.adicCompletionIntegers K) p
    ((continuousKummerEquiv _).symm ((continuousKummerEquiv _)
      (powerClassMap p (Units.map (algebraMap (v.adicCompletionIntegers K)
        (v.adicCompletion K)).toMonoidHom (ordinaryFiniteUnitParameter v p X E hζ hα he hβ a)))))
  rw [Equiv.symm_apply_apply]
  exact ⟨ordinaryFiniteUnitParameter v p X E hζ hα he hβ a, rfl⟩

end ThreeAdicPlan
