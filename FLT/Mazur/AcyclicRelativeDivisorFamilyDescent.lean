/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FullDivisorFlatFppfDescent
public import FLT.Mazur.UnpointedLocalAcyclicDivisorCover

/-!
# Effective descent of acyclic full relative divisors

The global full ideal is Cartier and its closed subscheme is flat over the
test base. Its actual Abel class is geometrically acyclic by fppf locality.
The intrinsic Abel inverse recovers this very ideal, giving an acyclic full
divisor whose restrictions are the original supplied divisors.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]

omit [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f] in
/-- Equality of full relative comaps identifies their original Abel classes. -/
theorem relativeAbel_comap_class {T U : Over (Spec (.of R))} (g : U ⟶ T)
    (D : Divisor (pullback f T.hom))
    (hD : RelativeEffectiveCartier (pullback.snd f T.hom) D.val)
    (E : Divisor (pullback f U.hom)) (hE : D.val.comap (relativeTotalMap f g) = E.val) :
    relativeBaseMap f g (abel (pullback.snd f T.hom) D) =
      abel (pullback.snd f U.hom) E := by
  have H := abel_originalSquare (relativeTotalMap_isPullback f g) D hD
  exact H.symm.trans (congrArg (abel (pullback.snd f U.hom)) (Subtype.ext hE))

/-- A recovered full relative Cartier ideal inherits the local acyclic divisor condition. -/
theorem acyclicRelativeDivisor_of_ideal_recovery (T : Over (Spec (.of R)))
    (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
    (D : ∀ i, AcyclicRankOneRelativeDivisor
      (pullback.snd f (relativeCoverMember T 𝒰 i).hom))
    (J : (pullback f T.hom).IdealSheafData)
    (hJ : RelativeEffectiveCartier (pullback.snd f T.hom) J)
    (h : ∀ i, J.comap (relativeTotalMap f (relativeCoverArrow T 𝒰 i)) = (D i).val.val) :
    ∃ E : AcyclicRankOneRelativeDivisor (pullback.snd f T.hom), E.val.val = J := by
  let F : Divisor (pullback f T.hom) := ⟨J, hJ.1⟩
  have hc : RelativeGeometricAcyclicRankOne (pullback.snd f T.hom)
      (abel (pullback.snd f T.hom) F) := by
    apply (relativeGeometricAcyclicRankOne_fppf_iff f T 𝒰 _).mpr
    intro i
    rw [relativeAbel_comap_class f _ F hJ (D i).val (h i)]
    exact (finiteTypeTestAbel
      (IsPullback.of_hasPullback f (relativeCoverMember T 𝒰 i).hom) (D i)).property
  let E := finiteTypeTestClassDivisor (IsPullback.of_hasPullback f T.hom) _ hc
  have he : F = E.val := finiteTypeTestClassDivisor_unique
    (IsPullback.of_hasPullback f T.hom) _ hc F hJ.2 rfl
  exact ⟨E, (congrArg Subtype.val he).symm⟩

/-- Matching full acyclic divisors descend uniquely, without an original family section. -/
theorem existsUnique_acyclicRelativeDivisor_family_descent (T : Over (Spec (.of R)))
    (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
    (D : ∀ i, AcyclicRankOneRelativeDivisor
      (pullback.snd f (relativeCoverMember T 𝒰 i).hom))
    (h : ∀ i j, (D i).val.val.comap
        (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j)) =
      (D j).val.val.comap (relativeTotalMap f (relativeCoverPairRight T 𝒰 i j))) :
    ∃! E : AcyclicRankOneRelativeDivisor (pullback.snd f T.hom),
      ∀ i, finiteTypeAcyclicDivisorMap f (relativeCoverArrow T 𝒰 i) E = D i := by
  obtain ⟨J, hJ, _⟩ := existsUnique_relativeEffectiveCartier_family_descent f T 𝒰
    (fun i ↦ (D i).val.val) (fun i ↦ ⟨(D i).val.property, (D i).property.1⟩) h
  obtain ⟨E, hE⟩ := acyclicRelativeDivisor_of_ideal_recovery f T 𝒰 D J hJ.1 hJ.2
  have he (i : 𝒰.I₀) :
      finiteTypeAcyclicDivisorMap f (relativeCoverArrow T 𝒰 i) E = D i := by
    apply acyclicRankOneRelativeDivisor_ext
    rw [finiteTypeAcyclicDivisorMap_ideal, hE, hJ.2 i]
  exact ⟨E, he, fun F hF ↦ finiteTypeAcyclicDivisor_eq_of_cover f T 𝒰
    (fun i ↦ (hF i).trans (he i).symm)⟩

end FLT.Mazur.CartierAbel
