/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudLocalPrescribedExtension

/-!
# Integral identification of local p-killed models

In small ramification, a specified equivariant generic isomorphism determines
one integral Hopf isomorphism. Only the source must be known to be p-killed:
the generic equivalence transports annihilation to the target.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open NumberField IsLocalRing

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  {X Y : FF (v.adicCompletionIntegers K) (v.adicCompletion K)}

/-- A prescribed generic equivalence extends uniquely to the original integral models. -/
theorem existsUnique_iso_of_local_killed
    (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)
    (hX : ∀ x : X.Points, p • x = 0)
    (f : GenericGaloisHom X Y) (hf : Function.Bijective f) :
    ∃! e : X.Iso Y, genericHom e.toBialgHom = f := by
  let : Module (ZMod p) X.Points := AddCommGroup.zmodModule hX
  let : Module (ZMod p) Y.Points := AddCommGroup.zmodModule (fun y ↦ by
    obtain ⟨x, rfl⟩ := hf.2 y
    rw [← map_nsmul, hX, map_zero])
  obtain ⟨a, ha, -⟩ := extend_from_local_prime_field v p he f
  obtain ⟨b, hb, -⟩ := extend_from_local_prime_field v p he (f.inverse hf)
  have hab (x) : genericHom b (genericHom a x) = x := by
    rw [ha, hb, GenericGaloisHom.inverse_apply]
  have hba (y) : genericHom a (genericHom b y) = y := by
    obtain ⟨x, rfl⟩ := hf.2 y
    rw [ha, hb, GenericGaloisHom.inverse_apply]
  refine ⟨FF.isoOfGenericInverse a b hab hba, ha, ?_⟩
  intro e he'
  apply BialgEquiv.toBialgHom_injective
  exact genericHom_injective X Y (he'.trans ha.symm)

/-- Generic equivalences over any characteristic-p coefficient field determine
integral isomorphisms; the coefficient field need not be the prime field. -/
theorem existsUnique_iso_of_local_coefficients
    {k : Type} [Field k] [CharP k p] [Module k X.Points]
    (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)
    (f : GenericGaloisHom X Y) (hf : Function.Bijective f) :
    ∃! e : X.Iso Y, genericHom e.toBialgHom = f := by
  apply existsUnique_iso_of_local_killed v p he _ f hf
  intro x
  rw [← Nat.cast_smul_eq_nsmul (R := k), CharP.cast_eq_zero, zero_smul]

end ThreeAdicPlan
