/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryGeometricTensor

/-!
# Actual invariant functions on full geometric scalar branches

Flatness and the full endpoint comparisons identify every actual branch
invariant with a scalar from the new base. A boundary lift therefore amounts
to scalarity of its literal pullback on the whole geometric boundary.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars FlatAlgebraEqualizer
open FlatScalarSchemeBaseChange FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} (p q : D ⟶ A)
local notation "R" => invariants p.appTop.hom q.appTop.hom
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
variable (S : Type) [CommRing S] [Algebra (invariants p.appTop.hom q.appTop.hom) S]
  [Module.Flat (invariants p.appTop.hom q.appTop.hom) S]
  [CompactSpace A] [QuasiSeparatedSpace A] [CompactSpace D] [QuasiSeparatedSpace D]

/-- Every invariant actual branch function is a scalar from the flat new base. -/
theorem originalBranch_invariant_is_scalar (a : Γ(baseChange R S A, ⊤))
    (he : (originalBranchFirst p q S).appTop a = (originalBranchSecond p q S).appTop a) :
    ∃ s : S, FlatScalarFunctionPushout.scalarMap (base R S A) s = a := by
  let ea := sectionsEquiv (square R S A)
  let ec := sectionsEquiv (square R S D)
  let z := ea.symm a
  have hza : ea z = a := ea.apply_symm_apply a
  have hp : ec (tensorMap S (first p.appTop.hom q.appTop.hom) z) =
      (originalBranchFirst p q S).appTop a :=
    (map_sectionsEquiv p _ rfl z).trans (congrArg _ hza)
  have hq : ec (tensorMap S (second p.appTop.hom q.appTop.hom) z) =
      (originalBranchSecond p q S).appTop a :=
    (map_sectionsEquiv q _ rfl z).trans (congrArg _ hza)
  obtain ⟨s, hs⟩ := RingPairInvariantFlatScalars.scalarMap_surjective
    p.appTop.hom q.appTop.hom S ⟨z, ec.injective (hp.trans (he.trans hq.symm))⟩
  have hz : algebraMap S (S ⊗[R] Γ(A, ⊤)) s = z := congrArg Subtype.val hs
  exact ⟨s, (sectionsEquiv_left (square R S A) s).symm.trans
    ((congrArg ea hz).trans hza)⟩

variable (J : A.IdealSheafData)

omit [Module.Flat (invariants p.appTop.hom q.appTop.hom) S]
  [CompactSpace A] [QuasiSeparatedSpace A] [CompactSpace D] [QuasiSeparatedSpace D] in
/-- Scalar pullback constructs a full invariant branch function with the literal boundary. -/
theorem originalBranch_lift_of_scalar (t : Γ(J.subscheme, ⊤)) (s : S)
    (hs : FlatScalarFunctionPushout.scalarMap (base R S J.subscheme) s =
      (source R S J.subscheme).appTop t) :
    ∃ a : Γ(baseChange R S A, ⊤),
      (originalBranchFirst p q S).appTop a = (originalBranchSecond p q S).appTop a ∧
      (originalBranchBoundary p q J S).appTop a = (source R S J.subscheme).appTop t := by
  refine ⟨FlatScalarFunctionPushout.scalarMap (base R S A) s, ?_, ?_⟩
  · exact (scalarMap_natural _ (map_base p _ rfl) s).trans
      (scalarMap_natural _ (map_base q _ rfl) s).symm
  · exact (scalarMap_natural _ (map_base J.subschemeι _ rfl) s).trans hs

/-- Existence of a full branch lift is exactly scalarity on the entire branch boundary. -/
theorem originalBranch_lift_iff_scalar (t : Γ(J.subscheme, ⊤)) :
    (∃ a : Γ(baseChange R S A, ⊤),
      (originalBranchFirst p q S).appTop a = (originalBranchSecond p q S).appTop a ∧
      (originalBranchBoundary p q J S).appTop a = (source R S J.subscheme).appTop t) ↔
    ∃ s : S, FlatScalarFunctionPushout.scalarMap (base R S J.subscheme) s =
      (source R S J.subscheme).appTop t := by
  constructor
  · rintro ⟨a, he, hb⟩
    obtain ⟨s, hs⟩ := originalBranch_invariant_is_scalar p q S a he
    refine ⟨s, ?_⟩
    exact (scalarMap_natural _ (map_base J.subschemeι _ rfl) s).symm.trans
      ((congrArg (originalBranchBoundary p q J S).appTop hs).trans hb)
  · rintro ⟨s, hs⟩
    exact originalBranch_lift_of_scalar p q S J t s hs

end FLT.Mazur.EquivalenceRelationOrderedFrames
