/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelRationalDegree
public import FLT.GroupScheme.EquivariantHopfCocommutative
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# The rational source kernel's actual commutative group scheme

The existing label-induced Hopf algebra supplies the scheme operations. Its
identity is evaluation at the original zero label and maps to the original zero.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace WeierstrassCurve.Velu

open FLT.Mazur.WeierstrassIntegralChart

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

attribute [local instance] primeKernelDescentHopfAlgebra

/-- The original label-induced rational Hopf algebra is cocommutative. -/
instance primeKernelDescent_cocomm :
    Coalgebra.IsCocomm ℚ (PrimeKernelDescentAlgebra E p q hq hfixed) := by
  let _ := primeKernelLabelAction E p q hq hfixed
  let _ := primeKernelLabelAction_continuous E p q hq hfixed
  exact GaloisModule.GenericFiber.equivariantHopf_cocomm ℚ (AlgebraicClosure ℚ) (ZMod p)

/-- The actual rational spectrum inherits the group law induced by the original labels. -/
instance primeKernelRationalSchemeCommGroup :
    CommGrpObj (primeKernelRationalScheme E p q hq hfixed) :=
  inferInstanceAs (CommGrpObj
    ((Spec (.of (PrimeKernelDescentAlgebra E p q hq hfixed))).asOver (Spec (.of ℚ))))

/-- The original rational map, now as a morphism over the rational base. -/
def primeKernelRationalInclusion : primeKernelRationalScheme E p q hq hfixed ⟶
    (integralGeneralizedEllipticCurve E E.isUnit_Δ).group :=
  Over.homMk (primeKernelRationalMap E p q hq hfixed)
    (primeKernelRationalMap_base E p q hq hfixed)

/-- The rational group identity has the original zero-label evaluation over Qbar. -/
@[reassoc] theorem primeKernelRationalScheme_identity_evaluation :
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
      η[primeKernelRationalScheme E p q hq hfixed].left =
        Spec.map (CommRingCat.ofHom
          (primeKernelDescentEvaluation E p q hq hfixed 0).toRingHom) := by
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom
    (Bialgebra.counitAlgHom ℚ (PrimeKernelDescentAlgebra E p q hq hfixed)).toRingHom) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  let _ := primeKernelLabelAction E p q hq hfixed
  let _ := primeKernelLabelAction_continuous E p q hq hfixed
  exact GaloisModule.GenericFiber.algebraMap_counitAlgHom ℚ (AlgebraicClosure ℚ) (ZMod p) a

/-- The actual rational inclusion preserves the original identity section. -/
@[reassoc] theorem primeKernelRationalInclusion_identity :
    η[primeKernelRationalScheme E p q hq hfixed] ≫
      primeKernelRationalInclusion E p q hq hfixed =
        η[(integralGeneralizedEllipticCurve E E.isUnit_Δ).group] := by
  apply Over.OverMorphism.ext
  let b := Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))
  have hb := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  let _ : Flat b := hb.1
  let _ : Surjective b := hb.2
  let _ : Epi b := Flat.epi_of_flat_of_surjective b
  apply (cancel_epi b).mp
  change b ≫ η[primeKernelRationalScheme E p q hq hfixed].left ≫
    primeKernelRationalMap E p q hq hfixed = b ≫ integralCurveZero E
  rw [primeKernelRationalScheme_identity_evaluation_assoc,
    primeKernelRationalMap_evaluation_zero]

end WeierstrassCurve.Velu
