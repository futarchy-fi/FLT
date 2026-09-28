/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.CartierDualKernelInclusion
public import FLT.GroupScheme.FiniteFlatExtensionKernelIso
public import FLT.GroupScheme.StableSubgroupExtension

/-!
# Integral closed subgroups and their flat closures

A closed immersion of finite-flat models identifies its source with the flat
closure of its generic image. Consequently the contracted quotient construction
keeps a specified closed subgroup, including its actual inclusion map.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
    {A H : FF R K}

/-- The comparison from a closed integral subgroup to its generic flat closure. -/
def ModelHom.closureComparison (f : ModelHom A H)
    (hi : Function.Injective (genericHom f)) :
    ModelHom A ((genericHom f).closure hi) :=
  (genericHom f).closureLift hi f (DistribMulActionHom.id _) (by ext; rfl)

/-- The closure comparison preserves the prescribed inclusion. -/
theorem ModelHom.closureComparisonInclusion (f : ModelHom A H)
    (hi : Function.Injective (genericHom f)) :
    (f.closureComparison hi).comp ((genericHom f).closureInclusion hi) = f := by
  ext a
  rfl

/-- The closure comparison is the identity on the prescribed generic points. -/
theorem ModelHom.closureComparisonPoints (f : ModelHom A H)
    (hi : Function.Injective (genericHom f)) (a : A.Points) :
    genericHom (f.closureComparison hi) a = a :=
  (genericHom f).genericHom_closureLift hi f (DistribMulActionHom.id _) (by ext; rfl) a

/-- A closed integral subgroup is isomorphic to its generic flat closure. -/
def ModelHom.closureIso (f : ModelHom A H)
    (hi : Function.Injective (genericHom f)) (hf : Function.Surjective f) :
    A.Iso ((genericHom f).closure hi) := by
  apply BialgEquiv.ofBijective (f.closureComparison hi)
  constructor
  · apply ModelHom.injective_of_baseChange_injective
    rw [← ModelHom.toBialgHom_genericHom]
    apply GenericGaloisHom.toBialgHom_injective
    exact fun a ↦ ⟨a, f.closureComparisonPoints hi a⟩
  · intro a
    obtain ⟨h, rfl⟩ := hf a
    exact ⟨(genericHom f).closureInclusion hi h, rfl⟩

variable [IsPrincipalIdealRing R] [Algebra R ℚ] [IsFractionRing R ℚ]

/-- A specified closed subgroup yields an integral extension with its original
kernel model, faithfully flat quotient, and canonical torsor. -/
def FiniteFlatObject.extensionOfClosedImmersion
    {A H : FiniteFlatObject R} (f : A.Hom H)
    (hi : Function.Injective (FiniteFlatObject.pointMap f)) (hf : Function.Surjective f)
    {Q : FF R ℚ} (q : GenericGaloisHom H.toFF Q) (hq : Function.Surjective q)
    (hexact : ∀ h, q h = 0 ↔ ∃ a, FiniteFlatObject.pointMap f a = h) :
    FiniteFlatExtension A H (q.flatQuotient hq).toFiniteFlatObject :=
  (H.extensionOfGenericExact (genericHom (X := A.toFF) (Y := H.toFF) f)
    q hi hq hexact).transportKernel
    (ModelHom.closureIso (A := A.toFF) (H := H.toFF) f hi hf).symm

/-- The extension of a closed subgroup uses exactly its given inclusion. -/
theorem FiniteFlatObject.extensionOfClosedImmersionInclusion
    {A H : FiniteFlatObject R} (f : A.Hom H)
    (hi : Function.Injective (FiniteFlatObject.pointMap f)) (hf : Function.Surjective f)
    {Q : FF R ℚ} (q : GenericGaloisHom H.toFF Q) (hq : Function.Surjective q)
    (hexact : ∀ h, q h = 0 ↔ ∃ a, FiniteFlatObject.pointMap f a = h) :
    (FiniteFlatObject.extensionOfClosedImmersion f hi hf q hq hexact).inclusion = f := by
  ext a
  rfl

end ThreeAdicPlan
