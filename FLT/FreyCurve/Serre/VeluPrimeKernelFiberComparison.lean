/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGeometricKernelScheme
public import FLT.FreyCurve.Serre.VeluGlobalKernelClosedComparison

/-!
# The original prime kernel closed subgroup is the actual global Vélu fiber

The comparison retains the constructed inclusion and its original component
labels. The full fiber is reduced by its exact translated neighborhoods.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q) [Fintype (torsionKernel E p q)]
  (hp : Odd p)

local notation "EQ" => E.map (algebraMap ℚ (AlgebraicClosure ℚ))
local notation "GQ" => torsionKernel E p q
/-- The original finite subgroup instance, cached in the mapped-cubic presentation. -/
local instance primeFiberFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

local notation "φ" => veluGlobalMorphism EQ GQ (torsionKernel_ne_neg E p q hp)
local notation "H" => primeKernelClosedSubgroup E p q hq

omit [Fintype (torsionKernel E p q)] in
/-- The existing closed subgroup component retains the exact original source point. -/
@[reassoc] theorem primeKernelClosedSubgroup_component_source (i : ZMod p) :
    (ConstantCyclicGroup.component (Spec (.of (AlgebraicClosure ℚ))) p i).left ≫
        (H).inclusion.left =
      affineSmoothPoint EQ (primeKernelParam E p q hq i) ≫ (integralSmoothOpen EQ).ι := by
  rw [← Over.comp_left, primeKernelClosedSubgroup_component]
  change (𝟙 _ ≫ (projectiveToIntegral EQ
    (Projective.Point.fromAffine (primeKernelParam E p q hq i))).left) = _
  rw [Category.id_comp, affineSmoothPoint, projectiveToSmooth_inclusion]

/-- The original full geometric subgroup is killed by the actual global Vélu morphism. -/
@[reassoc] theorem primeKernelClosedSubgroup_global_zero :
    (H).inclusion.left ≫ φ = (H).carrier.hom ≫ integralCurveZero (curve EQ GQ) := by
  apply (cancel_epi
    (ConstantCyclicFiniteEtale.underlyingIso (AlgebraicClosure ℚ) p).hom).mp
  apply Sigma.hom_ext
  intro i
  simp only [← Category.assoc, ConstantCyclicFiniteEtale.component_underlyingIso]
  rw [primeKernelClosedSubgroup_component_source]
  rw [veluGlobalMorphism_kernel EQ GQ (torsionKernel_ne_neg E p q hp)
    (primeKernelParam E p q hq i) (primeKernelParamEquiv E p q hq i).property]
  have hb : (ConstantCyclicGroup.component (Spec (.of (AlgebraicClosure ℚ))) p i).left ≫
      (H).carrier.hom = 𝟙 _ :=
    (ConstantCyclicGroup.component (Spec (.of (AlgebraicClosure ℚ))) p i).w
  rw [hb]
  exact (Category.id_comp _).symm

/-- The original inclusion induces a canonical map to the original full identity fiber. -/
def primeKernelToGlobalFiber : (H).carrier.left ⟶
    veluGlobalKernel EQ GQ (torsionKernel_ne_neg E p q hp) :=
  veluGlobalKernelClosedLift EQ GQ (torsionKernel_ne_neg E p q hp)
    (H).inclusion.left (H).carrier.hom (primeKernelClosedSubgroup_global_zero E p q hq hp)

/-- The original closed subgroup equals the full scheme-theoretic kernel. -/
instance primeKernelToGlobalFiber_isIso : IsIso (primeKernelToGlobalFiber E p q hq hp) := by
  apply veluGlobalKernelClosedLift_isIso
  intro P
  let i := (primeKernelParamEquiv E p q hq).symm P
  refine ⟨(ConstantCyclicGroup.component (Spec (.of (AlgebraicClosure ℚ))) p i).left,
    ?_, (ConstantCyclicGroup.component (Spec (.of (AlgebraicClosure ℚ))) p i).w⟩
  rw [primeKernelClosedSubgroup_component_source]
  congr 2
  exact congrArg Subtype.val ((primeKernelParamEquiv E p q hq).apply_symm_apply P)

/-- The comparison is an actual scheme isomorphism, retaining the original closed subgroup. -/
def primeKernelGlobalFiberIso : (H).carrier.left ≅
    veluGlobalKernel EQ GQ (torsionKernel_ne_neg E p q hp) :=
  asIso (primeKernelToGlobalFiber E p q hq hp)

/-- The isomorphism retains exactly the original inclusion in the original source curve. -/
@[reassoc] theorem primeKernelGlobalFiberIso_fst :
    (primeKernelGlobalFiberIso E p q hq hp).hom ≫ pullback.fst _ _ = (H).inclusion.left :=
  veluGlobalKernelClosedLift_fst _ _ _ _ _ _

/-- The isomorphism retains the original field structure. -/
@[reassoc] theorem primeKernelGlobalFiberIso_snd :
    (primeKernelGlobalFiberIso E p q hq hp).hom ≫ pullback.snd _ _ = (H).carrier.hom :=
  veluGlobalKernelClosedLift_snd _ _ _ _ _ _

/-- The original closed inclusion is the actual Cartesian identity fiber square. -/
theorem primeKernelClosedSubgroup_global_isPullback :
    IsPullback (H).inclusion.left (H).carrier.hom φ (integralCurveZero (curve EQ GQ)) :=
  IsPullback.of_iso_pullback ⟨primeKernelClosedSubgroup_global_zero E p q hq hp⟩
    (primeKernelGlobalFiberIso E p q hq hp) (primeKernelGlobalFiberIso_fst E p q hq hp)
    (primeKernelGlobalFiberIso_snd E p q hq hp)

end WeierstrassCurve.Velu
