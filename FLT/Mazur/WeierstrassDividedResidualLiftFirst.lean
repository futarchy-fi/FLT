/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidualLiftGeometry
public import FLT.Mazur.PolygonArithmeticTwoBranchRebaseIdentification

/-!
# Recovery of the original first-order geometric corrections

The rebased terminal inverse and the normalized retained factors recover the
previous full-chart isomorphisms. The terminal parameter identification is explicit.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.PolygonSmoothing
variable {R : Type*} [CommRing R]
set_option backward.isDefEq.respectTransparency false

/-- A rebased ring equality identifies the inverse correction on spectra. -/
theorem rebasedCorrection_spec (s t : R) (h : s = t)
    (F : ChartRing t ≃ₐ[R] ChartRing s) (G : ChartRing t ≃ₐ[R] ChartRing t)
    (hF : (ringMap (RingHom.id R) s t h).comp F.toAlgHom.toRingHom = G.toAlgHom.toRingHom) :
    (Scheme.Spec.mapIso F.toRingEquiv.toCommRingCatIso.op).symm ≪≫ nodeParameterIso s t h =
      (Scheme.Spec.mapIso G.toRingEquiv.toCommRingCatIso.op).symm := by
  subst s
  rw [ringMap_id, RingHom.id_comp] at hF
  have hFG : F = G := AlgEquiv.ext (fun z ↦ DFunLike.congr_fun hF z)
  subst G
  simp only [nodeParameterIso, eqToIso_refl]
  exact Iso.trans_refl _

/-- A source ring identification identifies the forward correction on spectra. -/
theorem sourceCorrection_spec (s t : R) (h : s = t)
    (F : ChartRing s ≃ₐ[R] ChartRing t) (G : ChartRing t ≃ₐ[R] ChartRing t)
    (hF : F.toAlgHom.toRingHom = G.toAlgHom.toRingHom.comp (ringMap (RingHom.id R) s t h)) :
    Scheme.Spec.mapIso F.toRingEquiv.toCommRingCatIso.op ≪≫ nodeParameterIso s t h =
      Scheme.Spec.mapIso G.toRingEquiv.toCommRingCatIso.op := by
  subst s
  rw [ringMap_id, RingHom.comp_id] at hF
  have hFG : F = G := AlgEquiv.ext (fun z ↦ DFunLike.congr_fun hF z)
  subst G
  simp only [nodeParameterIso, eqToIso_refl]
  exact Iso.trans_refl _

end FLT.Mazur.PolygonSmoothing

namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "σ" => arithmeticTerminalChangedSmoothing data H 1 j hj u hu
local notation "s" => arithmeticResidualLiftTerminalSmoothing hπ data H 1 j hj u hu

/-- The inverse drift disappears on the original first arithmetic layer. -/
theorem arithmeticResidualLiftTerminalSmoothing_first : s = σ :=
  twoBranchCorrectionRebasedSmoothing_first R π σ
    (arithmeticFirstChangedSmoothing_annihilated data H j hj u hu) _

/-- The corrected terminal chart comparison is exactly the old first-order inverse. -/
theorem arithmeticResidualLiftTerminalIso_first :
    arithmeticResidualLiftTerminalIso hπ data H 1 j hj u hu ≪≫
        nodeParameterIso s σ (arithmeticResidualLiftTerminalSmoothing_first hπ data H j hj u hu) =
      arithmeticFirstResidualTerminalIso hπ data H j hj u hu := by
  apply rebasedCorrection_spec
  exact twoBranchCorrectionRebasedFactor_first R π σ
    (arithmeticFirstChangedSmoothing_annihilated data H j hj u hu) _ _
    (arithmeticTerminalIntegralField_first hπ data H j hj u hu)

/-- The normalized retained comparison is the entire original first-order factor. -/
theorem arithmeticResidualLiftRetainedIso_first (b : Bool) :
    arithmeticResidualLiftRetainedIso hπ data H 1 j hj u hu b =
      arithmeticFirstResidualRetainedIso hπ data H j hj u hu b := by
  apply sourceCorrection_spec
  exact arithmeticResidualRetainedLift_first hπ data H j hj u hu b

/-- The first-order correction also agrees in the original labeled retained orientation. -/
theorem arithmeticResidualLiftOrientedIso_first (b : Bool) :
    arithmeticResidualLiftOrientedIso hπ data H 1 j hj u hu b =
      arithmeticFirstResidualOrientedIso hπ data H j hj u hu b := by
  unfold arithmeticResidualLiftOrientedIso arithmeticFirstResidualOrientedIso
  rw [arithmeticResidualLiftRetainedIso_first]

end FLT.Mazur.WeierstrassDividedDepth
