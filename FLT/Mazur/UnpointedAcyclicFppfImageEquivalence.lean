/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UnpointedAcyclicAbelInjectivity
public import FLT.Mazur.FiniteTypeAbelNaturalIso
public import FLT.Mazur.UnpointedAcyclicFppfDetection

/-!
# Unpointed Abel equivalence with the represented acyclic image

The actual relative classes in the geometric acyclic locus inject into the
Picard sheaf without a section. Thus the full-divisor presheaf is naturally
isomorphic to its represented image. Effective existence of representatives
for the local closure is still a separate obligation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]

/-- The comparison into the actual sheaf is injective on the intrinsic acyclic class locus. -/
theorem finiteTypeGeometricAcyclicFppf_injective (T : Over (Spec (.of R))) :
    Function.Injective (fun c : (geometricAcyclicPicardSubfunctor f).toFunctor.obj (op T) ↦
      relativeFppfClass f T c.val) := by
  intro c d h
  let e := finiteTypeTestAbelEquiv (IsPullback.of_hasPullback f T.hom)
  have he : e.symm c = e.symm d := by
    apply finiteTypeAcyclicAbelFppf_injective f T
    change relativeFppfClass f T (e (e.symm c)).val =
      relativeFppfClass f T (e (e.symm d)).val
    exact (congrArg (fun a ↦ relativeFppfClass f T a.val) (e.apply_symm_apply c)).trans
      (h.trans (congrArg (fun a ↦ relativeFppfClass f T a.val)
        (e.apply_symm_apply d)).symm)
  exact e.symm.injective he

/-- The represented image comparison is an equivalence without an original section. -/
def finiteTypeUnpointedAcyclicFppfEquiv (T : Over (Spec (.of R))) :
    (geometricAcyclicPicardSubfunctor f).toFunctor.obj (op T) ≃
      (geometricAcyclicFppfSubfunctor f).toFunctor.obj (op T) :=
  Equiv.ofBijective (fun c ↦ ⟨relativeFppfClass f T c.val, c.val, c.property, rfl⟩)
    ⟨fun _ _ h ↦ finiteTypeGeometricAcyclicFppf_injective f T (congrArg Subtype.val h),
      fun s ↦ by
        obtain ⟨c, hc, hcs⟩ := s.property
        exact ⟨⟨c, hc⟩, Subtype.ext hcs⟩⟩

/-- The unpointed comparison is natural for all actual test maps. -/
def finiteTypeUnpointedAcyclicFppfIso :
    (geometricAcyclicPicardSubfunctor f).toFunctor ≅
      (geometricAcyclicFppfSubfunctor f).toFunctor :=
  NatIso.ofComponents (fun T ↦ (finiteTypeUnpointedAcyclicFppfEquiv f T.unop).toIso)
    (fun {T U} g ↦ by
      apply ConcreteCategory.hom_ext
      intro c
      exact Subtype.ext (relativeFppfClass_naturality f g.unop c.val).symm)

/-- Full acyclic divisors identify naturally with the represented acyclic sheaf image. -/
def finiteTypeUnpointedAbelFppfImageIso :
    finiteTypeAcyclicDivisorPresheaf f ⋙ uliftFunctor.{1} ≅
      (geometricAcyclicFppfSubfunctor f).toFunctor :=
  finiteTypeAbelNaturalIso f ≪≫ finiteTypeUnpointedAcyclicFppfIso f

/-- This equivalence preserves the original positive-divisor line class exactly. -/
lemma finiteTypeUnpointedAbelFppfImageIso_class (T : Over (Spec (.of R)))
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f T.hom)) :
    ((finiteTypeUnpointedAbelFppfImageIso f).hom.app (op T) (ULift.up D)).val =
      relativeFppfClass f T (abel (Limits.pullback.snd f T.hom) D.val) := rfl

/-- Each represented acyclic section has a unique full-divisor representative. -/
theorem finiteTypeUnpointedAcyclicFppf_existsUnique (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T))
    (hs : s ∈ (geometricAcyclicFppfSubfunctor f).obj (op T)) :
    ∃! D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f T.hom),
      relativeFppfClass f T (abel (Limits.pullback.snd f T.hom) D.val) = s := by
  obtain ⟨c, hc, rfl⟩ := hs
  let D := finiteTypeTestClassDivisor (IsPullback.of_hasPullback f T.hom) c hc
  have hD : relativeFppfClass f T (abel (Limits.pullback.snd f T.hom) D.val) =
      relativeFppfClass f T c := congrArg (relativeFppfClass f T)
        (finiteTypeTestClassDivisor_class _ c hc)
  exact ⟨D, hD, fun E hE ↦ finiteTypeAcyclicAbelFppf_injective f T (hE.trans hD.symm)⟩

end FLT.Mazur.CartierAbel
