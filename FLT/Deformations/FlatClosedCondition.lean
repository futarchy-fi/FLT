/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.FlatClosedQuotient
public import FLT.Deformations.ClosedIdealCondition
public import FLT.Deformations.LiftFunctor

/-!
# Classification by the effective flat quotient

A continuous coefficient specialization is flat exactly when it kills the
constructed closed ideal. Thus the quotient classifies the actual predicate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory NumberField
namespace Deformation
open ProartinianCat
variable {O : Type} [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)] (U : ProartinianCat O)
  {K : Type} [Field K] [NumberField K] {n : Type} [Fintype n] [DecidableEq n]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ρ : FramedGaloisRep K U n)

omit [Finite (IsLocalRing.ResidueField O)] in
/-- The existing flat subfunctor gives coefficient-map stability for framed representations. -/
theorem flat_specialization {A : ProartinianCat O} (f : U ⟶ A) (h : ρ.IsFlatAt v) :
    (ρ.baseChange f.hom.toRingHom f.hom.cont).IsFlatAt v := by
  have hh : ρ.GL ∈ (flatFunctor n O v).obj U := by
    change (FramedGaloisRep.GL.symm (FramedGaloisRep.GL ρ)).IsFlatAt v
    simpa only [Equiv.symm_apply_apply] using h
  have hm := (flatFunctor n O v).map f hh
  change (toFramedGaloisRep
    ((repnFunctor n (Field.absoluteGaloisGroup K) O).map f ρ.GL)).IsFlatAt v at hm
  rw [toFramedGaloisRep_map] at hm
  simp only [toFramedGaloisRep, Equiv.symm_apply_apply] at hm
  convert hm using 1
  apply FramedGaloisRep.GL.injective
  ext s i j
  simp only [FramedGaloisRep.baseChange_GL]
  rfl

omit [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- A flat specialization kills the defining ideal, detected in every open target reduction. -/
theorem flatReductionIdeal_le_ker {A : ProartinianCat O} (f : U ⟶ A)
    (h : (ρ.baseChange f.hom.toRingHom f.hom.cont).IsFlatAt v) :
    flatReductionIdeal U v ρ ≤ RingHom.ker f.hom.toRingHom := by
  intro x hx
  change f.hom x = 0
  by_contra hne
  have hN : ({f.hom x}ᶜ : Set A) ∈ nhds (0 : A) :=
    isOpen_compl_singleton.mem_nhds (by simpa using (Ne.symm hne))
  obtain ⟨J, hJ, hJN⟩ := IsLinearTopology.hasBasis_open_ideal.mem_iff.mp hN
  let F : U →+* A ⧸ J := (Ideal.Quotient.mk J).comp f.hom.toRingHom
  have hF : Continuous F := continuous_quot_mk.comp f.hom.cont
  have hmodel := (FramedGaloisRep.hasFlatProlongationAt_baseChange_iff v
    (ρ.baseChange f.hom.toRingHom f.hom.cont)).mp (h.cond J hJ)
  have hrep : (ρ.baseChange f.hom.toRingHom f.hom.cont).baseChange
      (Ideal.Quotient.mk J) continuous_quot_mk = ρ.baseChange F hF := by
    apply FramedGaloisRep.GL.injective
    ext g i j
    simp only [FramedGaloisRep.baseChange_GL]
    rfl
  have hmodel' : (ρ.baseChange F hF).HasFlatProlongationAt v := hrep ▸ hmodel
  have hI : RingHom.ker F ∈ flatReductionIdeals U v ρ := by
    refine ⟨?_, FramedGaloisRep.hasFlatProlongationAt_kernel v ρ F hF hmodel'⟩
    convert hJ.preimage f.hom.cont using 1
    ext y
    exact Ideal.Quotient.eq_zero_iff_mem
  have hz : F x = 0 := flatReductionIdeal_le U v ρ hI hx
  have hmem : f.hom x ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hz
  exact hJN hmem (by simp)

/-- The quotient condition is precisely flatness, for every proartinian target. -/
theorem kills_flatReductionIdeal_iff
    (hex : (flatReductionIdeals U v ρ).Nonempty) (hne : flatReductionIdeal U v ρ ≠ ⊤)
    {A : ProartinianCat O} (f : U ⟶ A) :
    KillsClosedIdeal U (flatReductionIdeal U v ρ) f ↔
      (ρ.baseChange f.hom.toRingHom f.hom.cont).IsFlatAt v := by
  constructor
  · intro hf
    let g := factorClosedIdeal U (flatReductionIdeal U v ρ)
      (flatReductionIdeal_closed U v ρ) hne f hf
    have hg := flat_specialization (flatClosedObject U v ρ hne) v
      (flatClosedRepresentation U v ρ hne) g
      (flatClosedRepresentation_isFlat U v ρ hex hne)
    convert hg using 1
    apply FramedGaloisRep.GL.injective
    ext s i j
    simp only [flatClosedRepresentation, FramedGaloisRep.baseChange_GL]
    rfl
  · exact flatReductionIdeal_le_ker U v ρ f

/-- The constructed equivalence classifies flat specializations, with no equivalence premise. -/
def flatClosedEquiv
    (hex : (flatReductionIdeals U v ρ).Nonempty) (hne : flatReductionIdeal U v ρ ≠ ⊤)
    (A : ProartinianCat O) :
    (flatClosedObject U v ρ hne ⟶ A) ≃
      {f : U ⟶ A // (ρ.baseChange f.hom.toRingHom f.hom.cont).IsFlatAt v} :=
  (closedIdealFactorEquiv U (flatReductionIdeal U v ρ)
    (flatReductionIdeal_closed U v ρ) hne A).trans
    (Equiv.subtypeEquivRight fun f ↦ kills_flatReductionIdeal_iff U v ρ hex hne f)

end Deformation
