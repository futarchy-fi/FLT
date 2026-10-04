/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.OrdinaryLocalRootRatio
public import FLT.GroupScheme.OrdinaryIntegralFiberGalois
public import FLT.GroupScheme.KummerUnitTransport
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

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K)) [Module (ZMod p) X.Points]
  [SMulCommClass (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) (ZMod p) X.Points]
  {α β : (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) →* (ZMod p)ˣ}
  (E : OrdinaryFiltration (Representation.ofDistribMulAction (ZMod p)
    (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) X.Points) α β)
  {ζ : (AlgebraicClosure (v.adicCompletion K))ˣ} (hζ : IsPrimitiveRoot ζ p)
  (hα : α = primeCyclotomicCharacter hζ)

local instance : IsDedekindDomain (v.adicCompletionIntegers K) :=
  IsPrincipalIdealRing.isDedekindDomain _

variable (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)

variable (hβ : β = 1)

/-- The actual quotient arrow defines the fibre algebra. -/
local instance localKummerAlgebra :
    Algebra (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotient.toAlgHom.toRingHom.toAlgebra

/-- The quotient arrow respects the local base. -/
local instance localKummerTower : IsScalarTower (v.adicCompletionIntegers K)
    (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  IsScalarTower.of_algebraMap_eq'
    (ordinaryModelExtension X E).quotient.toAlgHom.comp_algebraMap.symm

/-- Faithful flatness is supplied by the constructed ordinary extension. -/
local instance localKummerFaithfullyFlat :
    Module.FaithfullyFlat (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotientFaithfullyFlat

variable [TopologicalSpace (ZMod p)] [DiscreteTopology (ZMod p)]
  [TopologicalSpace X.Points] [DiscreteTopology X.Points]
  (hρ : ∀ x : X.Points, Continuous
    (fun g : AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K) ↦ g • x))

/-- Evaluate the integral generator at an original vector above one. -/
def ordinaryLocalKummerRoot (w : X.Points) (hw : E.projection w = 1) :
    (AlgebraicClosure (v.adicCompletion K))ˣ :=
  Units.map (ordinaryIntegralFiberPoint X E hβ w hw).toMonoidHom
    (ordinaryLocalFiberGenerator v p X E hζ hα he hβ)

/-- Its field-action ratio is the original ordinary cocycle in root coordinates. -/
theorem ordinaryLocalKummerRoot_ratio (w : X.Points) (hw : E.projection w = 1)
    (g : AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) :
    unitRatio (ordinaryLocalKummerRoot v p X E hζ hα he hβ w hw) g =
      rootUnit (primeRootCoordinates hζ
        ((show ZMod p →ₗ[ZMod p] ZMod p from (E.cocycleOf hρ w hw).val g) 1)) := by
  have h := ordinaryLocalFiberGenerator_ratio v p X E hζ hα he hβ hρ w hw g
  rw [ordinaryIntegralFiberPoint_galois X E hβ w hw g] at h
  exact h

omit [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  [TopologicalSpace (ZMod p)] [DiscreteTopology (ZMod p)] in
include hα hβ in
/-- The character ratio is cyclotomic when the quotient character is trivial. -/
theorem ordinaryLocal_homCharacter : homCharacter α β = primeCyclotomicCharacter hζ := by
  simp [homCharacter, hβ, hα]

/-- The original root-valued extension class has the explicitly constructed integral parameter. -/
theorem ordinaryLocalRootClass_parameter
    (roots : ∀ q : (v.adicCompletion K)ˣ, ∃ b : (AlgebraicClosure (v.adicCompletion K))ˣ,
      b ^ p = Units.map (algebraMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))) q)
    (w : X.Points) (hw : E.projection w = 1) :
    continuousClassMk
      (E.rootCocycle hζ α β (ordinaryLocal_homCharacter v p hζ hα hβ) hρ w hw) =
    parameterClass roots (Units.map (algebraMap (v.adicCompletionIntegers K)
      (v.adicCompletion K)).toMonoidHom (ordinaryLocalUnitParameter v p X E hζ hα he hβ)) := by
  let q := Units.map (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K)).toMonoidHom (ordinaryLocalUnitParameter v p X E hζ hα he hβ)
  let b := ordinaryLocalKummerRoot v p X E hζ hα he hβ w hw
  have hb : b ^ p = Units.map
      (algebraMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))) q := by
    exact ordinaryLocalUnitParameter_evaluation v p X E hζ hα he hβ w hw
  have hc : E.rootCocycle hζ α β (ordinaryLocal_homCharacter v p hζ hα hβ) hρ w hw =
      continuousRootCocycle q b hb := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    apply rootUnit_injective
    exact (ordinaryLocalKummerRoot_ratio v p X E hζ hα he hβ hρ w hw g).symm
  rw [hc]
  exact continuousRootCocycle_independent q b (roots q).choose hb (roots q).choose_spec

include he in
/-- The actual root cocycle belongs to the independently defined integral unit subgroup. -/
theorem ordinaryLocalRootClass_unit (w : X.Points) (hw : E.projection w = 1) :
    IsUnitContinuousClass (exists_unit_root (L := AlgebraicClosure (v.adicCompletion K)))
      (v.adicCompletionIntegers K)
      (continuousClassMk
        (E.rootCocycle hζ α β (ordinaryLocal_homCharacter v p hζ hα hβ) hρ w hw)) := by
  rw [ordinaryLocalRootClass_parameter v p X E hζ hα he hβ hρ
    (exists_unit_root (L := AlgebraicClosure (v.adicCompletion K))) w hw]
  change IsUnitClass (v.adicCompletionIntegers K) p
    ((continuousKummerEquiv _).symm ((continuousKummerEquiv _)
      (powerClassMap p (Units.map (algebraMap (v.adicCompletionIntegers K)
        (v.adicCompletion K)).toMonoidHom (ordinaryLocalUnitParameter v p X E hζ hα he hβ)))))
  rw [Equiv.symm_apply_apply]
  exact ⟨ordinaryLocalUnitParameter v p X E hζ hα he hβ, rfl⟩

include he in
/-- The original continuous ordinary extension class has integral unit Kummer coefficients. -/
theorem ordinaryLocalExtensionClass_unit :
    IsUnitContinuousClass (exists_unit_root (L := AlgebraicClosure (v.adicCompletion K)))
      (v.adicCompletionIntegers K)
      (mapCoefficientClass (ordinaryRootCoefficients hζ α β)
        (ordinaryRootCoefficients_equivariant hζ α β (ordinaryLocal_homCharacter v p hζ hα hβ))
        (E.extensionClass hρ)) := by
  obtain ⟨w, hw⟩ := E.surjective 1
  rw [← E.rootCocycle_class hζ α β (ordinaryLocal_homCharacter v p hζ hα hβ) hρ w hw]
  exact ordinaryLocalRootClass_unit v p X E hζ hα he hβ hρ w hw

end ThreeAdicPlan
