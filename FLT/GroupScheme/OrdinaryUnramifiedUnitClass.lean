/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalUnramifiedTwistFiltration
public import FLT.GroupScheme.OrdinaryFiniteUnitClass
public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltrationUnit
public import FLT.LocalClassFieldTheory.OrdinaryPeuUnitCriterion

/-!
# Integral ordinary unit classes with an unramified quotient

The actual finite-flat inverse-quotient twist has trivial quotient and the
cyclotomic sub-line. Its integral fibre supplies the unit parameter. Transport
of the extracted class and simultaneous-twist invariance return the unit
condition for the original extension, without an assumed unit witness.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField IsLocalRing GaloisRepresentation.Extensions KummerTheory LocalRamification
namespace ThreeAdicPlan
variable {K k : Type} [Field K] [NumberField K] [Field k] [Finite k]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) k] [CharP k p]
  [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K)) [Module k X.Points]
  [SMulCommClass k (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) X.Points]
  (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)
  [TopologicalSpace k] [DiscreteTopology k]
  {α β : Field.absoluteGaloisGroup (v.adicCompletion K) →* kˣ}
  (hβ : Continuous β) (hI : localInertiaGroup v ≤ β.ker)

local instance : SMulCommClass (Field.absoluteGaloisGroup (v.adicCompletion K)) k X.Points :=
  SMulCommClass.symm _ _ _

variable (E : OrdinaryFiltration (Representation.ofDistribMulAction k
    (Field.absoluteGaloisGroup (v.adicCompletion K)) X.Points) α β)
  {ζ : (AlgebraicClosure (v.adicCompletion K))ˣ} (hζ : IsPrimitiveRoot ζ p)
  (hχ : homCharacter α β = (Units.map (algebraMap (ZMod p) k).toMonoidHom).comp
    (primeCyclotomicCharacter hζ))
  [TopologicalSpace X.Points] [DiscreteTopology X.Points]
  (hρ : ∀ x : X.Points, Continuous
    (fun g : Field.absoluteGaloisGroup (v.adicCompletion K) ↦ g • x))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Y" => localUnramifiedTwistModel v p X he β hβ hI

include he hβ hI in
/-- The original ordinary extension has an integral unit class for any unramified quotient. -/
theorem ordinaryUnramifiedExtensionUnit :
    OrdinaryUnitClass hζ (exists_unit_root (L := AlgebraicClosure Kv)) O
      (ordinaryHomCoordinates α β (primeCyclotomicCharacter hζ))
      (ordinaryHomCoordinates_equivariant α β _ hχ) (E.extensionClass hρ) := by
  let := localUnramifiedTwistModule v p X he β hβ hI
  let := localUnramifiedTwistSMulComm v p X he β hβ hI
  let : TopologicalSpace (Y).Points := ⊥
  let : DiscreteTopology (Y).Points := ⟨rfl⟩
  let l := localUnramifiedTwistLinearEquiv v p X he β hβ hI
  have hb : Continuous (fun g : Field.absoluteGaloisGroup Kv ↦ (β⁻¹ g : k)) :=
    (continuous_of_discreteTopology : Continuous (fun b : kˣ ↦ (b⁻¹ : kˣ).val)).comp hβ
  have hY : ∀ y : (Y).Points, Continuous (fun g : Field.absoluteGaloisGroup Kv ↦ g • y) := by
    intro y
    obtain ⟨x, rfl⟩ := l.surjective y
    have hh := (continuous_of_discreteTopology : Continuous l).comp
      (OrdinaryFiltration.continuous_twistOrbit
        (ρ := Representation.ofDistribMulAction k (Field.absoluteGaloisGroup Kv) X.Points)
        β⁻¹ hρ hb x)
    exact hh.congr (fun g ↦ (localUnramifiedTwistPointAddEquiv_equivariant
      v p X he β hβ hI g x).symm)
  let F := localUnramifiedTwistFiltration v p X he β hβ hI E
  have hα : α * β⁻¹ = (Units.map (algebraMap (ZMod p) k).toMonoidHom).comp
      (primeCyclotomicCharacter hζ) := by simpa [homCharacter, div_eq_mul_inv] using hχ
  have hq : β * β⁻¹ = 1 := mul_inv_cancel β
  have hu := ordinaryFiniteExtensionClass_unit v p Y F hζ hα he hq hY
  have ht := (E.twist β⁻¹).extensionClass_transport
    (σ := Representation.ofDistribMulAction k (Field.absoluteGaloisGroup Kv) (Y).Points) l
    (fun g x ↦ localUnramifiedTwistPointAddEquiv_equivariant v p X he β hβ hI g x)
    (OrdinaryFiltration.continuous_twistOrbit
        (ρ := Representation.ofDistribMulAction k (Field.absoluteGaloisGroup Kv) X.Points)
        β⁻¹ hρ hb) hY
  change F.extensionClass hY = _ at ht
  rw [ht] at hu
  exact (E.extensionUnit_twist hζ (exists_unit_root (L := AlgebraicClosure Kv)) O hχ
    hρ β⁻¹ hb).mp hu

include he hβ hI hχ in
/-- Finite flatness excludes the independent non-peu branch for an unramified quotient. -/
theorem ordinaryUnramifiedExtensionPeu :
    IsPeuRamifiedClass (k := k) (localInertiaGroup v) (E.extensionClass hρ) :=
  (LocalClassFieldTheory.localOrdinaryPeuRamified_iff_unit v p hζ k α β hχ
    (E.extensionClass hρ)).mpr
      (ordinaryUnramifiedExtensionUnit v p X he hβ hI E hζ hχ hρ)

end ThreeAdicPlan
