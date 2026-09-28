/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatFiltration
public import FLT.GroupScheme.IntegralCartierDual
public import FLT.GroupScheme.CartierDualMaps

/-!
# Integral kernel inclusions and their Cartier transposes

The canonical torsor comparison in a finite-flat extension forces the
kernel's coordinate map to be surjective. Consequently its Cartier
transpose is injective. Relative faithful flatness of that transpose is
a separate assertion and is not assumed or asserted here.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

variable {R : Type} [CommRing R] [Algebra R ℚ]

/-- Specializing the first group coordinate to the identity. -/
def FiniteFlatObject.kernelEvaluation (A H : FiniteFlatObject R) :
    H.model.CoordinateRing ⊗[R] A.model.CoordinateRing →ₐ[R] A.model.CoordinateRing :=
  Algebra.TensorProduct.lift
    ((Algebra.ofId R A.model.CoordinateRing).comp
      (Bialgebra.counitAlgHom R H.model.CoordinateRing))
    (AlgHom.id R A.model.CoordinateRing) (fun _ _ ↦ Commute.all _ _)

/-- Specializing translation by a kernel element at the identity recovers the kernel map. -/
theorem FiniteFlatObject.kernelEvaluation_comul {A H : FiniteFlatObject R}
    (f : A.Hom H) (b : H.model.CoordinateRing) :
    FiniteFlatObject.kernelEvaluation A H
      (Algebra.TensorProduct.map (AlgHom.id R H.model.CoordinateRing) f.toAlgHom
        (Coalgebra.comul (R := R) b)) = f b := by
  have he : (FiniteFlatObject.kernelEvaluation A H).comp
      (Algebra.TensorProduct.map (AlgHom.id R H.model.CoordinateRing) f.toAlgHom) =
      Algebra.TensorProduct.lift
        ((Algebra.ofId R A.model.CoordinateRing).comp
          (Bialgebra.counitAlgHom R H.model.CoordinateRing))
        f.toAlgHom (fun _ _ ↦ Commute.all _ _) := by
    apply AlgHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        FiniteFlatObject.kernelEvaluation, Algebra.TensorProduct.lift_tmul]
    | add x y hx hy =>
      simp only [map_add, AlgHom.comp_apply] at *
      exact congrArg₂ (· + ·) hx hy
  rw [← AlgHom.comp_apply, he]
  have h := congrArg
    (fun φ : WithConv (H.model.CoordinateRing →ₐ[R] A.model.CoordinateRing) ↦ φ b)
    (one_mul (WithConv.toConv f.toAlgHom))
  rw [AlgHom.convMul_apply] at h
  exact h

/-- The torsor comparison on a pure tensor is the canonical translation formula. -/
theorem FiniteFlatExtension.torsorEquiv_tmul {A H Q : FiniteFlatObject R}
    (E : FiniteFlatExtension A H Q) :
    letI := E.quotient.toAlgHom.toRingHom.toAlgebra
    ∀ h b : H.model.CoordinateRing,
      E.torsorEquiv (h ⊗ₜ[Q.model.CoordinateRing] b) =
        (h ⊗ₜ[R] (1 : A.model.CoordinateRing)) *
          Algebra.TensorProduct.map (AlgHom.id R H.model.CoordinateRing) E.inclusion.toAlgHom
            (Coalgebra.comul (R := R) b) := by
  let := E.quotient.toAlgHom.toRingHom.toAlgebra
  intro h b
  have hh : E.torsorEquiv (h ⊗ₜ[Q.model.CoordinateRing] (1 : H.model.CoordinateRing)) =
      h ⊗ₜ[R] (1 : A.model.CoordinateRing) := E.torsorEquiv.commutes h
  calc
    _ = E.torsorEquiv ((h ⊗ₜ[Q.model.CoordinateRing] (1 : H.model.CoordinateRing)) *
        (1 ⊗ₜ[Q.model.CoordinateRing] b)) := by simp
    _ = _ := by rw [map_mul, hh, E.torsorEquivSecond]

/-- The integral kernel coordinate map in a finite-flat extension is surjective. -/
theorem FiniteFlatExtension.inclusion_surjective {A H Q : FiniteFlatObject R}
    (E : FiniteFlatExtension A H Q) : Function.Surjective E.inclusion := by
  let := E.quotient.toAlgHom.toRingHom.toAlgebra
  have hp (z : H.model.CoordinateRing ⊗[Q.model.CoordinateRing] H.model.CoordinateRing) :
      ∃ b : H.model.CoordinateRing,
        E.inclusion b = FiniteFlatObject.kernelEvaluation A H (E.torsorEquiv z) := by
    induction z using TensorProduct.inductionOn with
    | tmul h b =>
      refine ⟨Coalgebra.counit (R := R) h • b, ?_⟩
      rw [E.torsorEquiv_tmul, map_mul, FiniteFlatObject.kernelEvaluation_comul]
      rw [map_smul]
      simp [FiniteFlatObject.kernelEvaluation, Algebra.smul_def]
    | add x y hx hy =>
      obtain ⟨b, hb⟩ := hx
      obtain ⟨c, hc⟩ := hy
      exact ⟨b + c, by simp only [map_add, hb, hc]⟩
  intro a
  obtain ⟨z, hz⟩ := E.torsorEquiv.surjective (1 ⊗ₜ[R] a)
  obtain ⟨b, hb⟩ := hp z
  refine ⟨b, ?_⟩
  rw [hz] at hb
  simpa [FiniteFlatObject.kernelEvaluation] using hb

/-- Faithful flatness makes the integral quotient coordinate map injective. -/
theorem FiniteFlatExtension.quotient_injective {A H Q : FiniteFlatObject R}
    (E : FiniteFlatExtension A H Q) : Function.Injective E.quotient := by
  let := E.quotient.toAlgHom.toRingHom.toAlgebra
  let := E.quotientFaithfullyFlat
  exact FaithfulSMul.algebraMap_injective Q.model.CoordinateRing H.model.CoordinateRing

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Cartier transpose of an integral model morphism. -/
def FiniteFlatObject.Hom.cartierDual {H J : FiniteFlatObject R} (f : H.Hom J) :
    J.cartierDual.Hom H.cartierDual := HopfAlgebra.CartierDual.bialgMap f

/-- The two transposed integral maps still compose to the zero group morphism. -/
theorem FiniteFlatExtension.dualCompositionZero {A H Q : FiniteFlatObject R}
    (E : FiniteFlatExtension A H Q) :
    E.quotient.cartierDual.toAlgHom.comp E.inclusion.cartierDual.toAlgHom =
      (Algebra.ofId R Q.cartierDual.model.CoordinateRing).comp
        (Bialgebra.counitAlgHom R A.cartierDual.model.CoordinateRing) := by
  apply AlgHom.ext
  intro φ
  apply WithConv.ext
  ext q
  let ψ : HopfAlgebra.CartierDual R A.model.CoordinateRing := φ
  change ψ (E.inclusion (E.quotient q)) = ψ 1 * Coalgebra.counit (R := R) q
  have hq : E.inclusion (E.quotient q) =
      algebraMap R A.model.CoordinateRing (Coalgebra.counit (R := R) q) :=
    AlgHom.congr_fun E.compositionZero q
  rw [hq, Algebra.algebraMap_eq_smul_one]
  change ψ.ofConv (Coalgebra.counit (R := R) q • (1 : A.model.CoordinateRing)) = _
  rw [map_smul, smul_eq_mul, mul_comm]

/-- Evaluation identifies an integral model with its integral double Cartier dual. -/
def FiniteFlatObject.cartierBidualEquiv (H : FiniteFlatObject R) :
    H.cartierDual.cartierDual.model.CoordinateRing ≃ₐc[R] H.model.CoordinateRing :=
  HopfAlgebra.CartierDual.bidualEquiv.symm

/-- Dualizing the kernel inclusion gives an injective integral coordinate map. -/
theorem FiniteFlatExtension.dualInclusion_injective {A H Q : FiniteFlatObject R}
    (E : FiniteFlatExtension A H Q) :
    Function.Injective E.inclusion.cartierDual := by
  intro φ ψ h
  apply WithConv.ext
  ext a
  obtain ⟨b, rfl⟩ := E.inclusion_surjective a
  exact congrArg (fun χ : HopfAlgebra.CartierDual R H.model.CoordinateRing ↦ χ b) h

end ThreeAdicPlan
