/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.FlatReduction
public import FLT.GroupScheme.FiniteFlatSubobjectUniverses

/-!
# Intersections of finite-flat coefficient reductions

The reduction modulo an intersection embeds equivariantly into the product
of the two reductions. Schematic closure supplies its finite-flat model.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField
open scoped TensorProduct
namespace GaloisRep
variable {K : Type} [Field K] [NumberField K]
  {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {n : Type} [Finite n]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ρ : FramedGaloisRep K A n)

/-- The canonical transition between coefficient reductions is equivariant. -/
def flatReductionMap {I J : Ideal A} (hIJ : I ≤ J) :
    ((GaloisRep.baseChange (A ⧸ I) ρ).toLocal v).Space →+[
      Field.absoluteGaloisGroup (v.adicCompletion K)]
      ((GaloisRep.baseChange (A ⧸ J) ρ).toLocal v).Space :=
  { (TensorProduct.map (Ideal.Quotient.factorₐ A hIJ).toLinearMap
      (LinearMap.id : (n → A) →ₗ[A] (n → A))).toAddMonoidHom with
    map_smul' := by
      intro g x
      change TensorProduct.map _ _ (((GaloisRep.baseChange (A ⧸ I) ρ).toLocal v) g x) =
        ((GaloisRep.baseChange (A ⧸ J) ρ).toLocal v) g (TensorProduct.map _ _ x)
      induction x using TensorProduct.inductionOn with
      | tmul a x => rfl
      | add x y hx hy => simp_all }

/-- Two finite-flat reductions give a finite-flat reduction at their intersection. -/
theorem hasFlatProlongationAt_quotient_inf {I J : Ideal A}
    (hI : (GaloisRep.baseChange (A ⧸ I) ρ).HasFlatProlongationAt v)
    (hJ : (GaloisRep.baseChange (A ⧸ J) ρ).HasFlatProlongationAt v) :
    (GaloisRep.baseChange (A ⧸ I ⊓ J) ρ).HasFlatProlongationAt v := by
  classical
  let := Fintype.ofFinite n
  let f := flatReductionMap v ρ (inf_le_left : I ⊓ J ≤ I)
  let g := flatReductionMap v ρ (inf_le_right : I ⊓ J ≤ J)
  let q : ((GaloisRep.baseChange (A ⧸ I ⊓ J) ρ).toLocal v).Space →+[
      Field.absoluteGaloisGroup (v.adicCompletion K)]
      ((GaloisRep.baseChange (A ⧸ I) ρ).toLocal v).Space ×
      ((GaloisRep.baseChange (A ⧸ J) ρ).toLocal v).Space :=
    { f.toAddMonoidHom.prod g.toAddMonoidHom with
      map_smul' := fun s x ↦ Prod.ext (f.map_smul s x) (g.map_smul s x) }
  have hq : Function.Injective q := by
    apply (injective_iff_map_eq_zero q).mpr
    intro x hx
    let e := TensorProduct.piScalarRight A (A ⧸ I ⊓ J) (A ⧸ I ⊓ J) n
    apply e.injective
    rw [map_zero]
    ext i
    have coord (L : Ideal A) (hL : I ⊓ J ≤ L) :
        Ideal.Quotient.factor hL (e x i) =
          TensorProduct.piScalarRight A (A ⧸ L) (A ⧸ L) n
            (flatReductionMap v ρ hL x) i := by
      clear hx
      induction x using TensorProduct.inductionOn with
      | tmul a m =>
        change Ideal.Quotient.factor hL
          (TensorProduct.piScalarRight A (A ⧸ I ⊓ J) (A ⧸ I ⊓ J) n (a ⊗ₜ[A] m) i) =
          TensorProduct.piScalarRight A (A ⧸ L) (A ⧸ L) n
            (Ideal.Quotient.factor hL a ⊗ₜ[A] m) i
        simp [Algebra.smul_def]
      | add x y hx hy => simp_all
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e x i)
    rw [← ha]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    constructor
    · apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hz := coord I inf_le_left
      rw [← ha] at hz
      change Ideal.Quotient.mk I a = _ at hz
      rw [show flatReductionMap v ρ inf_le_left x = 0 from congrArg Prod.fst hx,
        map_zero, Pi.zero_apply] at hz
      exact hz
    · apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hz := coord J inf_le_right
      rw [← ha] at hz
      change Ideal.Quotient.mk J a = _ at hz
      rw [show flatReductionMap v ρ inf_le_right x = 0 from congrArg Prod.snd hx,
        map_zero, Pi.zero_apply] at hz
      exact hz
  exact (hI.prod _ _ _ _ hJ).subobject_universes _ _ _ _ q hq

end GaloisRep
