/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.FlatIntersection

/-!
# Finite-flat models and framed changes of coefficients

Coordinatewise coefficient maps are equivariant. Injections reflect finite
flatness by schematic closure, and surjections preserve it by quotient closure.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField
open scoped TensorProduct
namespace FramedGaloisRep
variable {K : Type} [Field K] [NumberField K]
  {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  {n : Type} [Fintype n] [DecidableEq n]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ρ : FramedGaloisRep K A n)
  (f : A →+* B) (hf : Continuous f)

/-- Coordinatewise scalar change intertwines the local actions. -/
def flatCoefficientMap : (ρ.toLocal v).Space →+[
    Field.absoluteGaloisGroup (v.adicCompletion K)] ((ρ.baseChange f hf).toLocal v).Space :=
  { toFun := fun x i ↦ f (x i)
    map_zero' := funext fun _ ↦ f.map_zero
    map_add' := fun x y ↦ funext fun i ↦ f.map_add (x i) (y i)
    map_smul' := by
      intro g x
      change (fun i ↦ f (ρ.toLocal v g x i)) =
        (FramedGaloisRep.baseChange (ρ.toLocal v) f hf) g (fun i ↦ f (x i))
      ext i
      rw [← LinearMap.toMatrix'_mulVec (ρ.toLocal v g) x]
      exact RingHom.map_mulVec f (ρ.toLocal v g).toMatrix' x i }

/-- Injective coefficient maps reflect finite-flat prolongations. -/
theorem hasFlatProlongationAt_of_injective (hinj : Function.Injective f)
    (h : (ρ.baseChange f hf).HasFlatProlongationAt v) : ρ.HasFlatProlongationAt v := by
  apply h.subobject_universes _ _ _ _ (flatCoefficientMap v ρ f hf)
  intro x y hxy
  funext i
  exact hinj (congrFun hxy i)

/-- Surjective coefficient maps preserve finite-flat prolongations. -/
theorem hasFlatProlongationAt_of_surjective (hsurj : Function.Surjective f)
    (h : ρ.HasFlatProlongationAt v) : (ρ.baseChange f hf).HasFlatProlongationAt v := by
  apply GaloisModule.IsFiniteFlat.quotient _ _ _ _ h (flatCoefficientMap v ρ f hf)
  intro y
  choose x hx using fun i ↦ hsurj (y i)
  exact ⟨x, funext hx⟩

/-- The tensor realization and the framed realization have the same finite-flat models. -/
theorem hasFlatProlongationAt_baseChange_iff [Algebra A B] [ContinuousSMul A B] :
    (GaloisRep.baseChange B ρ).HasFlatProlongationAt v ↔
      (ρ.baseChange (algebraMap A B) (continuous_algebraMap A B)).HasFlatProlongationAt v := by
  let e := TensorProduct.piScalarRight A B B n
  let q : ((GaloisRep.baseChange B ρ).toLocal v).Space →+[
      Field.absoluteGaloisGroup (v.adicCompletion K)]
      ((ρ.baseChange (algebraMap A B) (continuous_algebraMap A B)).toLocal v).Space :=
    { e.toAddMonoidHom with
      map_smul' := by
        intro g x
        change e (((GaloisRep.baseChange B ρ).toLocal v) g x) =
          ((ρ.baseChange (algebraMap A B) (continuous_algebraMap A B)).toLocal v) g (e x)
        induction x using TensorProduct.inductionOn with
        | tmul a m =>
          change e (a ⊗ₜ[A] ρ.toLocal v g m) =
            (FramedGaloisRep.baseChange (ρ.toLocal v)
              (algebraMap A B) (continuous_algebraMap A B)) g
              (e (a ⊗ₜ[A] m))
          have hc := (flatCoefficientMap v ρ (algebraMap A B)
            (continuous_algebraMap A B)).map_smul g m
          change (fun i ↦ algebraMap A B (ρ.toLocal v g m i)) =
            (FramedGaloisRep.baseChange (ρ.toLocal v)
              (algebraMap A B) (continuous_algebraMap A B)) g
              (fun i ↦ algebraMap A B (m i)) at hc
          have he (m : n → A) : e (a ⊗ₜ[A] m) =
              a • (fun i ↦ algebraMap A B (m i)) := by
            ext i
            simp [e, Algebra.smul_def, mul_comm]
          rw [he, he, map_smul, ← hc]
        | add x y hx hy => simp_all }
  constructor
  · exact fun h ↦ h.map _ _ _ _ q e.bijective
  · exact fun h ↦ h.subobject_universes _ _ _ _ q e.injective

/-- A finite-flat specialization supplies a model on the quotient by its kernel.
The injective coefficient map is the canonical kernel lift. -/
theorem hasFlatProlongationAt_kernel
    (h : (ρ.baseChange f hf).HasFlatProlongationAt v) :
    (GaloisRep.baseChange (A ⧸ RingHom.ker f) ρ).HasFlatProlongationAt v := by
  let I := RingHom.ker f
  let g := RingHom.kerLift f
  have hg : Continuous g :=
    (QuotientRing.isOpenQuotientMap_mk I).isQuotientMap.continuous_iff.mpr hf
  apply (hasFlatProlongationAt_baseChange_iff v ρ).mpr
  apply hasFlatProlongationAt_of_injective v
    (ρ.baseChange (Ideal.Quotient.mk I) continuous_quot_mk) g hg
    (RingHom.kerLift_injective f)
  convert h using 1
  apply FramedGaloisRep.GL.injective
  ext s i j
  simp only [FramedGaloisRep.baseChange_GL]
  rfl

end FramedGaloisRep
