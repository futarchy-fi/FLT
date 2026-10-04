/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.LocalPeuUnitCriterion
public import FLT.GaloisRepresentation.Extensions.OrdinaryTwist

/-!
# The unit annihilator on actual ordinary Hom coefficients

Evaluation at one is the existing constructed Hom coordinate map. Its
proved equivariance transports the independent cup condition to the
cyclotomic residual line and hence to the independent extended unit criterion.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing NumberField KummerTheory GaloisRepresentation.Extensions

variable {F : Type} [Field F] [NumberField F]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

local notation "K" => v.adicCompletion F
local notation "A" => v.adicCompletionIntegers F
local notation "C" => AlgebraicClosure K

variable [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers F))
  (v.adicCompletionIntegers F)] (q : ℕ) [Fact q.Prime]

/-- The independent predicate on actual Hom classes is exactly the extended unit condition. -/
theorem localOrdinaryPeuRamified_iff_unit {ζ : Cˣ} (hζ : IsPrimitiveRoot ζ q)
    (k : Type*) [Field k] [TopologicalSpace k] [DiscreteTopology k] [Algebra (ZMod q) k]
    [FiniteDimensional (ZMod q) k] (α β : Gal(C/K) →* kˣ)
    (hχ : homCharacter α β = (Units.map (algebraMap (ZMod q) k).toMonoidHom).comp
      (primeCyclotomicCharacter («K» := K) hζ))
    (x : ContinuousClass Gal(C/K) (OrdinaryHomModule α β)) :
    IsPeuRamifiedClass (k := k) (localInertiaGroup v) x ↔
      OrdinaryUnitClass hζ (exists_unit_root («K» := K) (L := C) (n := q)) A
        (ordinaryHomCoordinates α β (primeCyclotomicCharacter («K» := K) hζ))
        (ordinaryHomCoordinates_equivariant α β _ hχ) x := by
  unfold OrdinaryUnitClass
  rw [← localPeuRamified_iff_extendedUnitClass v q hζ k]
  obtain ⟨y, rfl⟩ := (linearClassEquiv (k := k)).surjective x
  have h := peuClass_linearEquiv_iff (localInertiaGroup v)
    (ordinaryHomCoordinates α β (primeCyclotomicCharacter («K» := K) hζ))
    (ordinaryHomCoordinates_equivariant α β _ hχ) y
  change IsPeuRamifiedClass (k := k) (localInertiaGroup v) (linearClassEquiv y) ↔ _
  convert h.symm using 1
  all_goals induction y using Quotient.inductionOn with | h c => rfl

end LocalClassFieldTheory
