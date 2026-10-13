/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalLocalizationTensor
public import FLT.Mazur.RingPairInvariantFlatScalars
public import FLT.Mazur.SchemeRelationPrincipalLocalization
public import Mathlib.RingTheory.Flat.Localization

/-!
# Invariant principal tensors are actual geometric sections

Both tensor coefficient rings identify with sections on the original source
principal open and the full relation's preimage. The two tensor arrows become
the actual independent endpoint pullbacks. Quasi-compactness and quasi-separation
are explicit; no replacement by a finite collection of relation branches occurs.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct TopologicalSpace
universe u
namespace FLT.Mazur.SchemeRelationPrincipalLocalization
open SchemeEffectiveEpiSections RingPairInvariantFlatScalars
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{u}} (p q : D ⟶ A) (s : invariants p.appTop.hom q.appTop.hom)
local notation "I" => invariants p.appTop.hom q.appTop.hom
local notation "W" => A.basicOpen s.val
local notation "hW" => compatibleFunctions_basicOpen p q s
attribute [local instance] sourceAlgebra targetAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable [CompactSpace A] [QuasiSeparatedSpace A]

/-- Invariant localization of original source tensors is its actual principal section ring. -/
def sourceTensorEquiv : Localization.Away s ⊗[I] Γ(A, ⊤) ≃+* Γ(A, W) := by
  let _ : IsLocalization.Away (algebraMap I Γ(A, ⊤) s) Γ(A, W) := by
    change IsLocalization.Away s.val Γ(A, W)
    exact isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ _
  exact (PrincipalLocalizationTensor.comparison s Γ(A, W)).toRingEquiv

/-- Original source coefficients retain their literal geometric restriction. -/
theorem sourceTensorEquiv_one (a : Γ(A, ⊤)) :
    sourceTensorEquiv p q s (1 ⊗ₜ[I] a) = algebraMap Γ(A, ⊤) Γ(A, W) a := by
  let _ : IsLocalization.Away (algebraMap I Γ(A, ⊤) s) Γ(A, W) := by
    change IsLocalization.Away s.val Γ(A, W)
    exact isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ _
  exact PrincipalLocalizationTensor.comparison_one_tmul s Γ(A, W) a

variable [CompactSpace D] [QuasiSeparatedSpace D]

/-- The entire relation tensor ring is its actual principal-preimage section ring. -/
def relationTensorEquiv : Localization.Away s ⊗[I] Γ(D, ⊤) ≃+* Γ(D, p ⁻¹ᵁ W) := by
  let _ := relationAlgebra p q s
  let _ : IsLocalization.Away (algebraMap I Γ(D, ⊤) s) Γ(D, p ⁻¹ᵁ W) := by
    change IsLocalization.Away (p.appTop s.val) Γ(D, p ⁻¹ᵁ W)
    exact relation_isLocalization p q s
  exact (PrincipalLocalizationTensor.comparison s Γ(D, p ⁻¹ᵁ W)).toRingEquiv

omit [CompactSpace A] [QuasiSeparatedSpace A] in
/-- Full relation coefficients retain the actual restriction to the common endpoint preimage. -/
theorem relationTensorEquiv_one (a : Γ(D, ⊤)) :
    relationTensorEquiv p q s (1 ⊗ₜ[I] a) =
      D.presheaf.map (homOfLE le_top : p ⁻¹ᵁ W ⟶ ⊤).op a := by
  let _ := relationAlgebra p q s
  let _ : IsLocalization.Away (algebraMap I Γ(D, ⊤) s) Γ(D, p ⁻¹ᵁ W) := by
    change IsLocalization.Away (p.appTop s.val) Γ(D, p ⁻¹ᵁ W)
    exact relation_isLocalization p q s
  exact PrincipalLocalizationTensor.comparison_one_tmul s Γ(D, p ⁻¹ᵁ W) a

local notation "α" => first p.appTop.hom q.appTop.hom
local notation "β" => second p.appTop.hom q.appTop.hom

/-- The first tensor equation becomes precisely the first original geometric endpoint equation. -/
theorem first_tensor_square (z : Localization.Away s ⊗[I] Γ(A, ⊤)) :
    relationTensorEquiv p q s (FlatAlgebraEqualizer.tensorMap (Localization.Away s) α z) =
      p.app W (sourceTensorEquiv p q s z) := by
  let _ := relationAlgebra p q s
  let _ : IsLocalization.Away (algebraMap I Γ(D, ⊤) s) Γ(D, p ⁻¹ᵁ W) := by
    change IsLocalization.Away (p.appTop s.val) Γ(D, p ⁻¹ᵁ W)
    exact relation_isLocalization p q s
  let _ : IsLocalization.Away (algebraMap I Γ(A, ⊤) s) Γ(A, W) := by
    change IsLocalization.Away s.val Γ(A, W)
    exact isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ _
  apply PrincipalLocalizationTensor.naturality s Γ(D, p ⁻¹ᵁ W) α (p.app W).hom _ z
  intro a
  change p.app W (algebraMap Γ(A, ⊤) Γ(A, W) a) =
    D.presheaf.map (homOfLE le_top : p ⁻¹ᵁ W ⟶ ⊤).op (p.appTop a)
  simpa only [Scheme.Hom.appLE_eq_app] using restriction_square p q s p le_rfl a

/-- The second tensor equation retains the independent second geometric endpoint. -/
theorem second_tensor_square (z : Localization.Away s ⊗[I] Γ(A, ⊤)) :
    relationTensorEquiv p q s (FlatAlgebraEqualizer.tensorMap (Localization.Away s) β z) =
      q.appLE W (p ⁻¹ᵁ W) (hW).le (sourceTensorEquiv p q s z) := by
  let _ := relationAlgebra p q s
  let _ : IsLocalization.Away (algebraMap I Γ(D, ⊤) s) Γ(D, p ⁻¹ᵁ W) := by
    change IsLocalization.Away (p.appTop s.val) Γ(D, p ⁻¹ᵁ W)
    exact relation_isLocalization p q s
  let _ : IsLocalization.Away (algebraMap I Γ(A, ⊤) s) Γ(A, W) := by
    change IsLocalization.Away s.val Γ(A, W)
    exact isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ _
  exact PrincipalLocalizationTensor.naturality s Γ(D, p ⁻¹ᵁ W) β
    (q.appLE W (p ⁻¹ᵁ W) (hW).le).hom (restriction_square p q s q (hW).le) z

attribute [irreducible] sourceTensorEquiv relationTensorEquiv

/-- The full tensor equation detects exactly the original geometric invariant sections. -/
theorem tensor_invariant_iff (z : Localization.Away s ⊗[I] Γ(A, ⊤)) :
    FlatAlgebraEqualizer.tensorMap (Localization.Away s) α z =
      FlatAlgebraEqualizer.tensorMap (Localization.Away s) β z ↔
        sourceTensorEquiv p q s z ∈ relationOpenFunctions p q W hW := by
  change _ ↔ p.app W (sourceTensorEquiv p q s z) =
    q.appLE W (p ⁻¹ᵁ W) (hW).le (sourceTensorEquiv p q s z)
  constructor
  · intro h
    exact (first_tensor_square p q s z).symm.trans
      ((congrArg (relationTensorEquiv p q s) h).trans (second_tensor_square p q s z))
  · intro h
    apply (relationTensorEquiv p q s).injective
    exact (first_tensor_square p q s z).trans (h.trans (second_tensor_square p q s z).symm)

/-- The complete tensor equalizer is the actual geometric invariant section ring. -/
def tensorInvariantEquiv :
    AlgHom.equalizer (FlatAlgebraEqualizer.tensorMap (Localization.Away s) α)
      (FlatAlgebraEqualizer.tensorMap (Localization.Away s) β) ≃+*
        relationOpenFunctions p q W hW :=
  (sourceTensorEquiv p q s).restrict _ _ (fun z ↦ by
    change _ = _ ↔ sourceTensorEquiv p q s z ∈ relationOpenFunctions p q W hW
    exact tensor_invariant_iff p q s z)

/-- The earlier flat scalar equalizer now lands in the actual geometric section ring. -/
def scalarSectionEquiv : Localization.Away s ≃+* relationOpenFunctions p q W hW :=
  (scalarEquiv p.appTop.hom q.appTop.hom (Localization.Away s)).trans
    (tensorInvariantEquiv p q s)

end FLT.Mazur.SchemeRelationPrincipalLocalization
