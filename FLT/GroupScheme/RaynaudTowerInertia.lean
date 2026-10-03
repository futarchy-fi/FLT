/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.RootCharacter
public import FLT.GroupScheme.RaynaudStrictHenselian
public import FLT.GroupScheme.RaynaudUnramifiedHom

/-!
# Original inertia fixes the constructed unramified tower

Residue uniqueness applies to the actual finite subalgebras of the original
closure. Passing to their union retains the chosen embeddings.
-/

@[expose] public noncomputable section

namespace RaynaudParameters
open NumberField IsLocalRing

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ωv" => AlgebraicClosure Kv
local notation "Av" => IntegralClosure O Ωv

/-- Original inertia fixes every element of every actual finite unramified stage. -/
theorem inertia_fixes_unramifiedStage {π : O}
    (S : UnramifiedStage (Ω := Ωv) π) (σ : localInertiaGroup v) (x : S.1) :
    σ.1 (x : Ωv) = (x : Ωv) := by
  let : FaithfulSMul O S.1 := (faithfulSMul_iff_algebraMap_injective O S.1).mpr
    (fun _ _ h ↦ FaithfulSMul.algebraMap_injective O Ωv (congrArg Subtype.val h))
  let f : S.1 →ₐ[O] Av := S.1.val.codRestrict (integralClosure O Ωv) fun x ↦
    (Algebra.IsIntegral.isIntegral (R := O) x).map S.1.val
  let g : S.1 →ₐ[O] Av := (MulSemiringAction.toAlgHom O Av σ.1).comp f
  have h : g = f := unramified_hom_ext g f fun x ↦ residue_smul_eq v σ (f x)
  exact congrArg Subtype.val (AlgHom.congr_fun h x)

/-- Original inertia fixes the entire constructed union in its original embedding. -/
theorem inertia_fixes_unramifiedUnion {π : O}
    (σ : localInertiaGroup v) (x : unramifiedUnion (Ω := Ωv) π) :
    σ.1 (x : Ωv) = (x : Ωv) := by
  let T := AlgHom.equalizer (σ.1.toAlgHom.restrictScalars O) (AlgHom.id O Ωv)
  have hle : unramifiedUnion (Ω := Ωv) π ≤ T := by
    apply iSup_le
    intro S y hy
    exact inertia_fixes_unramifiedStage v S σ ⟨y, hy⟩
  exact hle x.property

/-- Fixing the integral tower forces its fraction-field embedding to be fixed. -/
theorem inertia_fixes_fractionField {π : O}
    (e : FractionRing (unramifiedUnion (Ω := Ωv) π) →ₐ[O] Ωv)
    (he : ∀ x : unramifiedUnion (Ω := Ωv) π, e (algebraMap _ _ x) = (x : Ωv))
    (σ : localInertiaGroup v) (x : FractionRing (unramifiedUnion (Ω := Ωv) π)) :
    σ.1 (e x) = e x := by
  have h : (σ.1.toAlgHom.restrictScalars O).comp e = e := by
    apply AlgHom.coe_ringHom_injective
    apply IsFractionRing.ringHom_ext (A := unramifiedUnion (Ω := Ωv) π)
    intro a
    change σ.1 (e (algebraMap _ _ a)) = e (algebraMap _ _ a)
    rw [he]
    exact inertia_fixes_unramifiedUnion v σ a
  exact AlgHom.congr_fun h x

end RaynaudParameters
