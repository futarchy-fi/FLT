/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelClosedDescent

/-!
# Finite etale degree of the original rational kernel

The closed source kernel has the prime degree of its actual descended coordinate
algebra, at every rational-base point. Its original algebra is etale.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry

namespace WeierstrassCurve.Velu

open FLT.Mazur

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

/-- The actual rational source-kernel scheme is etale over Q. -/
instance primeKernelRationalScheme_etale :
    Etale (primeKernelRationalScheme E p q hq hfixed).hom := by
  change Etale (Spec.map (CommRingCat.ofHom (algebraMap ℚ _)))
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- The degree of the rational closed kernel is exactly the original prime. -/
theorem primeKernelRationalScheme_degree :
    FCurve.FiniteLocallyFreeDegree (primeKernelRationalScheme E p q hq hfixed).hom p := by
  refine ⟨inferInstance, inferInstance, inferInstance, fun s ↦ ?_⟩
  change (Spec.map (CommRingCat.ofHom
    (algebraMap ℚ (PrimeKernelDescentAlgebra E p q hq hfixed)))).finrank s = p
  rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  exact primeKernelDescentAlgebra_finrank E p q hq hfixed

/-- In particular every fiber of the rational kernel has rank p. -/
theorem primeKernelRationalScheme_rank (s : Spec (.of ℚ)) :
    (primeKernelRationalScheme E p q hq hfixed).hom.finrank s = p :=
  (primeKernelRationalScheme_degree E p q hq hfixed).2.2.2 s

end WeierstrassCurve.Velu
