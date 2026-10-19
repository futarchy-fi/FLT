/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationNegation
public import FLT.Mazur.WeierstrassGlobalNegationInvolution

/-!
# A negation-invariant cover of the entire modified projective cubic

The whole local modification and the unchanged infinity negation neighborhood
cover the entire model. Each domain has its constructed involution, and its
original contraction is equivariant for the actual global cubic negative.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassGlobalModification
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
local notation "M" => model W s b3 b4 b6 h3 h4 h6 hs
local notation "c" => contraction W s b3 b4 b6 h3 h4 h6 hs

/-- The complete local chart and the actual infinity neighborhood. -/
def negationDomain (b : Bool) : Scheme :=
  if b then Spec (.of (InfinityNegationOpen W))
  else WeierstrassModificationX.modification W s b3 b4 b6

/-- Both original domains embed into the same whole modified projective cubic. -/
def negationInclusion (b : Bool) : negationDomain W s b3 b4 b6 b ⟶ M :=
  match b with
  | false => localChart W s b3 b4 b6 h3 h4 h6 hs
  | true => infinityNegationInclusion W ≫ infinityChart W s b3 b4 b6 h3 h4 h6 hs

instance negationInclusion_isOpenImmersion (b : Bool) :
    IsOpenImmersion (negationInclusion W s b3 b4 b6 h3 h4 h6 hs b) := by
  cases b <;> dsimp [negationInclusion] <;> infer_instance

/-- The invariant local and infinity domains cover every point of the whole model. -/
theorem negationInclusion_covers (z : M) :
    ∃ b, ∃ y, negationInclusion W s b3 b4 b6 h3 h4 h6 hs b y = z := by
  rcases charts_cover W s b3 b4 b6 h3 h4 h6 hs z with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨b, t, ht⟩ := (negationYCover W).exists_eq y
    cases b
    · let _ : IsIso (chartTransition W 2 1) :=
        inferInstanceAs (IsIso ((integralCurveGlueData W).t ⟨2⟩ ⟨1⟩))
      refine ⟨false, (inv (chartTransition W 2 1) ≫
        boundary W s b3 b4 b6 h3 h4 h6 hs) t, ?_⟩
      have he : (inv (chartTransition W 2 1) ≫ boundary W s b3 b4 b6 h3 h4 h6 hs) ≫
          localChart W s b3 b4 b6 h3 h4 h6 hs =
          overlapInclusion W 1 2 ≫ infinityChart W s b3 b4 b6 h3 h4 h6 hs := by
        rw [Category.assoc]
        change inv _ ≫ (_ ≫ pushout.inr _ _) = _ ≫ pushout.inl _ _
        rw [← pushout.condition]
        change inv (chartTransition W 2 1) ≫
          (chartTransition W 2 1 ≫ overlapInclusion W 1 2) ≫ _ = _
        rw [Category.assoc, IsIso.inv_hom_id_assoc]
      change ((inv (chartTransition W 2 1) ≫ boundary W s b3 b4 b6 h3 h4 h6 hs) ≫
        localChart W s b3 b4 b6 h3 h4 h6 hs) t = _
      rw [he]
      exact congrArg (infinityChart W s b3 b4 b6 h3 h4 h6 hs) ht
    · exact ⟨true, t, congrArg (infinityChart W s b3 b4 b6 h3 h4 h6 hs) ht⟩
  · exact ⟨false, y, rfl⟩

/-- The actual invariant two-domain cover of the complete projective modification. -/
def modificationNegationCover : (M).OpenCover where
  I₀ := Bool
  X := negationDomain W s b3 b4 b6
  f := negationInclusion W s b3 b4 b6 h3 h4 h6 hs
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨negationInclusion_covers W s b3 b4 b6 h3 h4 h6 hs,
      fun b => negationInclusion_isOpenImmersion W s b3 b4 b6 h3 h4 h6 hs b⟩

/-- The existing integral infinity endomorphism is an automorphism of its whole domain. -/
def infinityNegationIso : Spec (.of (InfinityNegationOpen W)) ≅
    Spec (.of (InfinityNegationOpen W)) :=
  Scheme.Spec.mapIso (AlgEquiv.ofAlgHom (infinityNegationEnd W) (infinityNegationEnd W)
    (infinityNegationEnd_comp W) (infinityNegationEnd_comp W)).toRingEquiv.toCommRingCatIso.op

/-- Each complete cover domain carries its constructed integral involution. -/
def negationDomainIso (b : Bool) :
    negationDomain W s b3 b4 b6 b ≅ negationDomain W s b3 b4 b6 b :=
  match b with
  | false => WeierstrassModificationX.modificationNegationIso W s b3 b4 b6 h3 h4 h6 hs
  | true => infinityNegationIso W

/-- The two domain involutions retain precisely the original global cubic negative. -/
@[reassoc] theorem negationDomainIso_contraction (b : Bool) :
    (negationDomainIso W s b3 b4 b6 h3 h4 h6 hs b).hom ≫
        negationInclusion W s b3 b4 b6 h3 h4 h6 hs b ≫ c =
      negationInclusion W s b3 b4 b6 h3 h4 h6 hs b ≫ c ≫ integralCurveNegation W := by
  cases b
  · change WeierstrassModificationX.modificationNegation W s b3 b4 b6 h3 h4 h6 hs ≫
      localChart W s b3 b4 b6 h3 h4 h6 hs ≫ c =
      localChart W s b3 b4 b6 h3 h4 h6 hs ≫ c ≫ _
    rw [localChart_contraction, localChart_contraction_assoc,
      WeierstrassModificationX.modificationNegation_contraction]
  · change Spec.map (CommRingCat.ofHom (infinityNegationEnd W).toRingHom) ≫
        (infinityNegationInclusion W ≫ infinityChart W s b3 b4 b6 h3 h4 h6 hs) ≫ c =
      (infinityNegationInclusion W ≫ infinityChart W s b3 b4 b6 h3 h4 h6 hs) ≫ c ≫ _
    simp only [Category.assoc, infinityChart_contraction, infinityChart_contraction_assoc]
    rw [← Category.assoc, infinityNegationEnd_spec_restriction,
      integralCurveChart_negation_infinity]

end FLT.Mazur.WeierstrassGlobalModification
