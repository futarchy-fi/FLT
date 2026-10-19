/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelScalarExtension
public import FLT.FreyCurve.Serre.VeluGeometricKernelScheme

/-!
# Comparing the descended algebra with the actual geometric kernel

The spectrum of the scalar extension is identified with the existing closed
subgroup. Every original evaluation maps to its original component section.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace WeierstrassCurve.Velu

open FLT.Mazur

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

/-- The geometric closed subgroup is the spectrum of the actual scalar extension. -/
def primeKernelGeometricIso : (primeKernelClosedSubgroup E p q hq).carrier.left ≅
    Spec (.of (AlgebraicClosure ℚ ⊗[ℚ] PrimeKernelDescentAlgebra E p q hq hfixed)) :=
  ConstantCyclicFiniteEtale.coordinateIso (AlgebraicClosure ℚ) p ≪≫
    Scheme.Spec.mapIso (primeKernelScalarEquiv E p q hq hfixed).toRingEquiv.toCommRingCatIso.op

/-- Each component of the geometric subgroup becomes its scalar-extended evaluation. -/
@[reassoc] theorem primeKernelGeometricIso_component (i : ZMod p) :
    (ConstantCyclicGroup.component (Spec (.of (AlgebraicClosure ℚ))) p i).left ≫
      (primeKernelGeometricIso E p q hq hfixed).hom =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.liftEquivRight ℚ (AlgebraicClosure ℚ) _ _
            (primeKernelDescentEvaluation E p q hq hfixed i)).toRingHom) := by
  rw [← ConstantCyclicFiniteEtale.component_underlyingIso]
  simp only [primeKernelGeometricIso, ConstantCyclicFiniteEtale.coordinateIso,
    Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc, ι_sigmaSpec_assoc]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The scalar-extension comparison retains the geometric structure map. -/
@[reassoc] theorem primeKernelGeometricIso_base :
    (primeKernelGeometricIso E p q hq hfixed).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ)
        (AlgebraicClosure ℚ ⊗[ℚ] PrimeKernelDescentAlgebra E p q hq hfixed))) =
          (primeKernelClosedSubgroup E p q hq).carrier.hom := by
  have hs : Spec.map (CommRingCat.ofHom
      (primeKernelScalarEquiv E p q hq hfixed).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ)
        (AlgebraicClosure ℚ ⊗[ℚ] PrimeKernelDescentAlgebra E p q hq hfixed))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (AlgebraicClosure ℚ) (ZMod p → AlgebraicClosure ℚ))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (primeKernelScalarEquiv E p q hq hfixed).commutes
  exact (congrArg (fun f ↦
    (ConstantCyclicFiniteEtale.coordinateIso (AlgebraicClosure ℚ) p).hom ≫ f) hs).trans
      (ConstantCyclicFiniteEtale.coordinateIso_base (AlgebraicClosure ℚ) p)

/-- The original geometric inclusion, now with the descended scalar-extension source. -/
def primeKernelScalarInclusion :
    Spec (.of (AlgebraicClosure ℚ ⊗[ℚ] PrimeKernelDescentAlgebra E p q hq hfixed)) ⟶
      (WeierstrassIntegralChart.integralGeneralizedEllipticCurve
        (E.map (algebraMap ℚ (AlgebraicClosure ℚ)))
        (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).isUnit_Δ).group.left :=
  (primeKernelGeometricIso E p q hq hfixed).inv ≫
    (primeKernelClosedSubgroup E p q hq).inclusion.left

/-- The transported inclusion remains a closed immersion of schemes. -/
instance primeKernelScalarInclusion_closed :
    IsClosedImmersion (primeKernelScalarInclusion E p q hq hfixed) := by
  unfold primeKernelScalarInclusion
  infer_instance

end WeierstrassCurve.Velu
