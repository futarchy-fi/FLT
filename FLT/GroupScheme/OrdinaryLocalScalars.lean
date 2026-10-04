/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalIntegralScalars
public import FLT.GroupScheme.OrdinaryFiltrationModels

/-!
# Integral scalar compatibility of the actual ordinary sequence

The schematic kernel and contracted quotient inherit integral coefficient
actions. Both original integral arrows commute with these constructed actions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField IsLocalRing GaloisRepresentation.Extensions
namespace ThreeAdicPlan

variable {K k : Type} [Field K] [NumberField K] [Field k]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  (p : ℕ) [Fact p.Prime] [CharP k p]
  [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K)) [Module k X.Points]
  [SMulCommClass (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) k X.Points]
  {α β : (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) →* kˣ}
  (E : OrdinaryFiltration (Representation.ofDistribMulAction k
    (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) X.Points) α β)
  (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)

local instance : SMulCommClass k
    (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) X.Points := SMulCommClass.symm _ _ _

local instance : IsDedekindDomain (v.adicCompletionIntegers K) :=
  IsPrincipalIdealRing.isDedekindDomain _

/-- Keep the kernel's original coefficient module during local specialization. -/
local instance : Module k (ordinaryKernelModel (k := k) X E).Points :=
  inferInstanceAs (Module k (CharacterModule α k))

/-- Keep the quotient's original coefficient module during local specialization. -/
local instance : Module k (ordinaryQuotientModel (k := k) X E).Points :=
  inferInstanceAs (Module k (CharacterModule β k))

local instance : SMulCommClass k
    (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) (ordinaryKernelModel (k := k) X E).Points :=
  SMulCommClass.symm _ _ (CharacterModule α k)

local instance : SMulCommClass k
    (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) (ordinaryQuotientModel (k := k) X E).Points :=
  SMulCommClass.symm _ _ (CharacterModule β k)

/-- The actual schematic kernel inclusion commutes with integral coefficient multiplication. -/
theorem ordinaryLocalScalar_inclusion (a : k) :
    (localIntegralScalar (k := k) v p (ordinaryKernelModel (k := k) X E) he a).comp
      (ordinaryModelExtension X E).inclusion =
    (ordinaryModelExtension X E).inclusion.comp (localIntegralScalar (k := k) v p X he a) := by
  apply localIntegralScalar_natural (k := k)
  intro b x
  simp only [ordinaryModelExtension_inclusion, map_smul]

/-- The actual contracted quotient commutes with integral coefficient multiplication. -/
theorem ordinaryLocalScalar_quotient (a : k) :
    (localIntegralScalar (k := k) v p X he a).comp (ordinaryModelExtension X E).quotient =
    (ordinaryModelExtension X E).quotient.comp
      (localIntegralScalar (k := k) v p (ordinaryQuotientModel (k := k) X E) he a) := by
  apply localIntegralScalar_natural (k := k)
  intro b x
  simp only [ordinaryModelExtension_quotient, map_smul]

end ThreeAdicPlan
