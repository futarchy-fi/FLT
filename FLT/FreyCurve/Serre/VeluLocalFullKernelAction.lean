/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalGenericKernelGroup
public import FLT.Mazur.WeierstrassDividedMixedKernelAction

/-!
# The original prime smooth kernel acts on its full divided closure

The generic subgroup is the actual kernel of the original transported quotient.
Its proved group law supplies the mixed action, retaining the original source,
target, both variable changes and every point of the full integral closure.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart FLT.Mazur.WeierstrassDividedDepth
namespace WeierstrassCurve.Velu
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  [Fintype (torsionKernel E p q)] (hp : Odd p)
local notation "EQ" => E.map (algebraMap ℚ (AlgebraicClosure ℚ))
local notation "GQ" => torsionKernel E p q

/-- Retain the original kernel enumeration used to construct the quotient curve. -/
local instance fullKernelActionFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

variable (V : WeierstrassCurve ℚ)
  (hcurve : V.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    @curve (AlgebraicClosure ℚ) inferInstance inferInstance
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (torsionKernel E p q)
      (fullKernelActionFintype E p q))
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)
  (hq : Function.Surjective q)
  {L R : Type} [Field L] [CommRing R] [Algebra ℚ L] [Algebra R L]
  [IsDomain R] [ValuationRing R] [IsNoetherianRing R] [IsFractionRing R L]
  (W U : WeierstrassCurve R) (C D : VariableChange L)
  (hC : C • E.map (algebraMap ℚ L) = W.map (algebraMap R L))
  (hD : D • V.map (algebraMap ℚ L) = U.map (algebraMap R L))
  {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (a : Fin (n + 1)) → Data W π (start + a.val)) (j : ℕ) (hj : j ≤ n)
local notation "i" => primeKernelRationalMap E p q hq hfixed
local notation "iL" => localGenericKernelInclusion E W C hC i
local notation "hΔ" => (primeLocalSource_isElliptic E W C hC).isUnit
local notation "G" => primeLocalGenericKernelGroup E p q hp V hcurve hfixed hq W U C D hC hD
local notation "I" =>
  primeLocalGenericKernelGroupInclusion E p q hp V hcurve hfixed hq W U C D hC hD
local notation "s" => genericClosureSmoothStructure W iL
local notation "f" => finiteGlobalKernelClosureStructure hπ data j hj hΔ iL
local notation "c" => finiteGlobalKernelClosureInclusion hπ data j hj hΔ iL

/-- The original smooth prime kernel preserves the entire original divided kernel closure. -/
def primeLocalFullKernelAction :
    pullback s f ⟶ finiteGlobalKernelClosure hπ data j hj hΔ iL := by
  have hd := primeLocalGenericGroupHom_kernel_degree E p q hp V hcurve hfixed hq W U C D hC hD
  let _ : IsClosedImmersion (I).hom.hom.hom.left := inferInstanceAs (IsClosedImmersion iL)
  let _ : Flat ((I).hom.hom.hom.left ≫ integralCurveStructure (W.map (algebraMap R L))) :=
    hd.2.1
  exact finiteGlobalMixedKernelAction hπ data j hj hΔ G I

/-- The action is the original whole-model action on the exact original kernel inclusions. -/
@[reassoc] theorem primeLocalFullKernelAction_inclusion :
    primeLocalFullKernelAction E p q hp V hcurve hfixed hq W U C D hC hD hπ data j hj ≫ c =
      finiteGlobalPointAction hπ data j hj
        (pullback.fst s f ≫ genericClosureSmoothInclusion W iL) (pullback.snd s f ≫ c)
        (by
          simp only [Category.assoc, genericClosureSmoothInclusion_structure]
          exact pullback.condition) := by
  have hd := primeLocalGenericGroupHom_kernel_degree E p q hp V hcurve hfixed hq W U C D hC hD
  let _ : IsClosedImmersion (I).hom.hom.hom.left := inferInstanceAs (IsClosedImmersion iL)
  let _ : Flat ((I).hom.hom.hom.left ≫ integralCurveStructure (W.map (algebraMap R L))) :=
    hd.2.1
  exact finiteGlobalMixedKernelAction_inclusion hπ data j hj hΔ G I

/-- The full original kernel action remains over the same integral coefficient base. -/
@[reassoc] theorem primeLocalFullKernelAction_structure :
    primeLocalFullKernelAction E p q hp V hcurve hfixed hq W U C D hC hD hπ data j hj ≫ f =
      pullback.fst s f ≫ s := by
  have hd := primeLocalGenericGroupHom_kernel_degree E p q hp V hcurve hfixed hq W U C D hC hD
  let _ : IsClosedImmersion (I).hom.hom.hom.left := inferInstanceAs (IsClosedImmersion iL)
  let _ : Flat ((I).hom.hom.hom.left ≫ integralCurveStructure (W.map (algebraMap R L))) :=
    hd.2.1
  exact finiteGlobalMixedKernelAction_structure hπ data j hj hΔ G I

end WeierstrassCurve.Velu
