/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.IntegralSubquotientExtension
public import FLT.GroupScheme.RaynaudOrderNineExtension

/-!
# Integral extensions for Galois-stable point subgroups

Every Galois-stable subgroup of the points of a chosen finite-flat object over
a principal ideal domain is the point image of the kernel in an integral
finite-flat extension of that object. This applies to `ZInvTwo` without
classification, order, or ramification hypotheses.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R : Type} [CommRing R] [Algebra R ℚ] [IsFractionRing R ℚ]

/-- Transfer an integral extension with rational generic field to the bundled
finite-flat-object interface, retaining all its integral maps and torsor data. -/
def ModelExtension.toFiniteFlatExtension {A H Q : FF R ℚ} (E : ModelExtension A H Q) :
    FiniteFlatExtension A.toFiniteFlatObject H.toFiniteFlatObject Q.toFiniteFlatObject where
  inclusion := E.inclusion
  quotient := E.quotient
  compositionZero := E.compositionZero
  pointsInjective := E.pointsInjective
  pointsSurjective := E.pointsSurjective
  pointsExact := E.pointsExact
  quotientFaithfullyFlat := E.quotientFaithfullyFlat
  torsorEquiv := E.torsorEquiv
  torsorEquivSecond := E.torsorEquivSecond

variable [IsDedekindDomain R] [IsPrincipalIdealRing R]

/-- The integral extension of an exact generic sequence keeps the specified
middle finite-flat object, replacing only the subgroup and quotient models. -/
def FiniteFlatObject.extensionOfGenericExact (H : FiniteFlatObject R)
    {S Q : FF R ℚ} (i : GenericGaloisHom S H.toFF) (q : GenericGaloisHom H.toFF Q)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x) :
    FiniteFlatExtension (i.closure hi).toFiniteFlatObject H
      (q.flatQuotient hq).toFiniteFlatObject :=
  (i.integralModelExtension q hi hq hexact).toFiniteFlatExtension

/-- Every Galois-stable point subgroup is realized by an integral kernel and
faithfully flat quotient of the chosen middle model, with the full torsor data. -/
theorem FiniteFlatObject.existsExtensionOfGaloisStable (H : FiniteFlatObject R)
    (P : AddSubgroup H.points) (hP : GaloisStable H.points P) :
    ∃ A Q : FiniteFlatObject R, ∃ E : FiniteFlatExtension A H Q,
      (FiniteFlatObject.pointMap E.inclusion).toAddMonoidHom.range = P := by
  let subgroupAction : DistribMulAction
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) P :=
    { smul := fun σ p ↦ ⟨σ • p.val, hP σ p.val p.property⟩
      one_smul := fun p ↦ Subtype.ext (one_smul _ _)
      mul_smul := fun σ τ p ↦ Subtype.ext (mul_smul σ τ p.val)
      smul_zero := fun σ ↦ Subtype.ext (smul_zero σ)
      smul_add := fun σ p p' ↦ Subtype.ext (smul_add σ p.val p'.val) }
  let i : P →+[AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ] H.points :=
    { toFun := Subtype.val
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hH : GaloisModule.IsFiniteFlat R ℚ (AlgebraicClosure ℚ) H.points :=
    H.toFF.isFiniteFlat
  let S := FF.ofIsFiniteFlat (R := R) (K := ℚ) P
    (hH.subobject R ℚ (AlgebraicClosure ℚ) H.points i Subtype.val_injective)
  let j : GenericGaloisHom S H.toFF := i
  have hj : Function.Injective j := Subtype.val_injective
  obtain ⟨Q, q, hq, hexact, _⟩ := j.exists_exact_quotient
  let E := H.extensionOfGenericExact j q hj hq hexact
  refine ⟨_, _, E, ?_⟩
  ext x
  change (∃ a : S.Points, genericHom (j.closureInclusion hj) a = x) ↔ x ∈ P
  constructor
  · rintro ⟨a, ha⟩
    rw [j.genericHom_closureInclusion] at ha
    exact ha ▸ a.property
  · intro hx
    exact ⟨⟨x, hx⟩, j.genericHom_closureInclusion hj ⟨x, hx⟩⟩

end ThreeAdicPlan
