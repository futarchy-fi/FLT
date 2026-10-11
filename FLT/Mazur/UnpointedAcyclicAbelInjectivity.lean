/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafFlatDetection
public import FLT.Mazur.FiniteTypeAcyclicDivisorPresheaf
public import FLT.Mazur.RelativeFppfComparisonCover

/-!
# The unpointed acyclic Abel map is injective in the actual Picard sheaf

Equality in the sheaf gives an actual fppf cover of equal relative classes.
Uniqueness of acyclic full divisors there, followed by faithful flatness,
detects equality of the original full ideals. No original section is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard FCurve
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]

omit [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f] in
/-- Full ideals on the test total space are detected on the original fppf members. -/
theorem relativeIdeal_eq_of_fppf_cover (T : Over (Spec (.of R)))
    (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
    {I J : (Limits.pullback f T.hom).IdealSheafData}
    (h : ∀ i, I.comap (relativeTotalMap f (relativeCoverArrow T 𝒰 i)) =
      J.comap (relativeTotalMap f (relativeCoverArrow T 𝒰 i))) : I = J := by
  let C := relativeTotalCover f T 𝒰
  let V : (Limits.pullback f T.hom).Cover
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := C
  let _ (i : C.I₀) : Flat (C.f i) :=
    (Scheme.Cover.map_prop (P := @Flat ⊓ @LocallyOfFinitePresentation) C i).1
  exact idealSheaf_eq_of_flat_family C.X C.f (fun x ↦ V.exists_eq x) h

/-- An fppf covering family detects equality of original acyclic full divisors. -/
theorem finiteTypeAcyclicDivisor_eq_of_cover (T : Over (Spec (.of R)))
    (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
    {D E : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f T.hom)}
    (h : ∀ i, finiteTypeAcyclicDivisorMap f (relativeCoverArrow T 𝒰 i) D =
      finiteTypeAcyclicDivisorMap f (relativeCoverArrow T 𝒰 i) E) : D = E := by
  apply acyclicRankOneRelativeDivisor_ext
  apply relativeIdeal_eq_of_fppf_cover f T 𝒰
  intro i
  simpa only [finiteTypeAcyclicDivisorMap_ideal] using
    congrArg (fun F ↦ F.val.val) (h i)

/-- Equality of actual Picard-sheaf Abel classes detects the entire original divisor. -/
theorem finiteTypeAcyclicAbelFppf_injective (T : Over (Spec (.of R))) :
    Function.Injective (fun D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f T.hom) ↦
      relativeFppfClass f T (abel (Limits.pullback.snd f T.hom) D.val)) := by
  intro D E h
  obtain ⟨𝒰, h𝒰⟩ := relativeFppfClass_eq_exists_cover f T _ _ h
  apply finiteTypeAcyclicDivisor_eq_of_cover f T 𝒰
  intro i
  apply (finiteTypeTestAbelEquiv
    (IsPullback.of_hasPullback f (relativeCoverMember T 𝒰 i).hom)).injective
  apply Subtype.ext
  exact (finiteTypeAcyclicDivisorMap_class f _ D).trans
    ((h𝒰 i).trans (finiteTypeAcyclicDivisorMap_class f _ E).symm)

end FLT.Mazur.CartierAbel
