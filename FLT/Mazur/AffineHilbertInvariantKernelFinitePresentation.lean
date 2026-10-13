/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertInvariantFiniteType
public import FLT.Mazur.AffineHilbertDerivedNoetherianRelation

/-!
# Finite presentation of the full original kernel comparison

The actual scheme kernel of the invariant candidate is affine and Noetherian,
even though the invariant ring is not known to be Noetherian. Both projections
and the original full relation comparison are locally of finite presentation.
This retains the entire original relation, without assuming effectivity.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "v" => invariantAffineProjection f hL d V c k
local notation "K" => pullback v v
local notation "a" => invariantAffineKernelMap f hL d V c k

omit [IsAffine V.left] [Etale V.hom] [IsAffine A.left] [IsOpenImmersion k.left] in
/-- The actual relative kernel square remains a scheme pullback after forgetting the base. -/
theorem invariantAffineKernel_isPullback :
    IsPullback (pullback.fst v v).left (pullback.snd v v).left (v).left (v).left :=
  (IsPullback.of_hasPullback v v).map (Over.forget _)

/-- The actual relative kernel has an affine underlying scheme. -/
instance invariantAffineKernel_isAffine : IsAffine (K).left :=
  IsAffine.of_isPullback (invariantAffineKernel_isPullback f hL d V c k)

/-- The first kernel projection is the base change of the actual candidate projection. -/
instance invariantAffineKernel_fst_locallyOfFiniteType :
    LocallyOfFiniteType (pullback.fst v v).left :=
  MorphismProperty.of_isPullback
    (invariantAffineKernel_isPullback f hL d V c k).flip inferInstance

/-- The second kernel projection retains the independent second coordinate. -/
instance invariantAffineKernel_snd_locallyOfFiniteType :
    LocallyOfFiniteType (pullback.snd v v).left :=
  MorphismProperty.of_isPullback
    (invariantAffineKernel_isPullback f hL d V c k) inferInstance

/-- Noetherianity follows over the original source, not over the unknown invariant ring. -/
instance invariantAffineKernel_isNoetherian : IsNoetherian (K).left := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst v v).left
  exact ⟨⟩

omit [IsAffine V.left] [IsAffine A.left] in
/-- Both complete kernel projections are locally of finite presentation. -/
theorem invariantAffineKernel_endpoints_finitePresentation :
    LocallyOfFinitePresentation (pullback.fst v v).left ∧
      LocallyOfFinitePresentation (pullback.snd v v).left := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  exact ⟨inferInstance, inferInstance⟩

/-- The full original relation comparison is locally of finite type. -/
instance invariantAffineKernelMap_locallyOfFiniteType : LocallyOfFiniteType (a).left := by
  have h : LocallyOfFiniteType ((a).left ≫ (pullback.fst v v).left) := by
    rw [← Over.comp_left, invariantAffineKernelMap_fst]
    infer_instance
  exact locallyOfFiniteType_of_comp (a).left (pullback.fst v v).left

/-- The original full comparison has local finite presentation over the actual kernel. -/
instance invariantAffineKernelMap_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (a).left := by
  let _ := invariantAffineKernel_isNoetherian f hL d V c k
  infer_instance

/-- The whole relation comparison is quasi-compact; no relation arrow has been discarded. -/
instance invariantAffineKernelMap_quasiCompact : QuasiCompact (a).left := by
  let _ := fullRelation_isNoetherian f hL d V c k
  infer_instance

end FLT.Mazur.HilbertChart.AffineRestriction
