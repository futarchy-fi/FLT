/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicRelativeDivisorFamilyDescent

/-!
# Global representatives for the unpointed local acyclic Picard locus

The full matching local divisors descend to an actual acyclic relative
divisor. Separation of the original Picard sheaf recovers the supplied
section. Consequently the local acyclic subsheaf equals the globally
represented acyclic image, without assuming a section of the family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]

omit [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f] in
/-- Actual fppf covering members separate sections of the original Picard sheaf. -/
theorem relativeFppfSheaf_eq_of_cover (T : Over (Spec (.of R)))
    (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
    (s t : (relativeFppfSheaf f).obj.obj (op T))
    (h : ∀ i, (relativeFppfSheaf f).obj.map (relativeCoverArrow T 𝒰 i).op s =
      (relativeFppfSheaf f).obj.map (relativeCoverArrow T 𝒰 i).op t) : s = t := by
  have hs := ((sheafCompose (Scheme.fppfTopology.over (Spec (.of R)))
    (forget CommGrpCat.{1})).obj (relativeFppfSheaf f)).property
  rw [isSheaf_iff_isSheaf_of_type] at hs
  have hcov : Sieve.ofArrows (relativeCoverMember T 𝒰) (relativeCoverArrow T 𝒰) ∈
      (Scheme.fppfTopology.over (Spec (.of R))) T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact Precoverage.generate_mem_toGrothendieck 𝒰.mem₀
  apply (Presieve.isSeparatedFor_iff_generate.mpr (hs.isSeparated _ hcov)).ext
  rintro U g ⟨i⟩
  exact h i

/-- Every locally acyclic original sheaf section has a unique global full acyclic divisor. -/
theorem finiteTypeUnpointedLocalAcyclicFppf_existsUnique (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T))
    (hs : s ∈ (localGeometricAcyclicFppfSubfunctor f).obj (op T)) :
    ∃! D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f T.hom),
      relativeFppfClass f T (abel (Limits.pullback.snd f T.hom) D.val) = s := by
  obtain ⟨𝒰, D, hD, hm⟩ := localGeometricAcyclicFppf_exists_divisor_cover f T s hs
  obtain ⟨E, hE, _⟩ := existsUnique_acyclicRelativeDivisor_family_descent f T 𝒰 D
    (fun i j ↦ hm i j (relativeCoverPair T 𝒰 i j)
      (relativeCoverPairLeft T 𝒰 i j) (relativeCoverPairRight T 𝒰 i j)
      (relativeCoverPair_condition T 𝒰 i j))
  have he : relativeFppfClass f T (abel (Limits.pullback.snd f T.hom) E.val) = s := by
    apply relativeFppfSheaf_eq_of_cover f T 𝒰
    intro i
    rw [relativeFppfClass_naturality, ← finiteTypeAcyclicDivisorMap_class, hE i]
    exact hD i
  exact ⟨E, he, fun F hF ↦ finiteTypeAcyclicAbelFppf_injective f T (hF.trans he.symm)⟩

/-- Local acyclic membership always has a global actual relative Picard representative. -/
theorem finiteTypeLocalGeometricAcyclicFppf_eq :
    localGeometricAcyclicFppfSubfunctor f = geometricAcyclicFppfSubfunctor f := by
  apply le_antisymm
  · intro T s hs
    obtain ⟨D, hD, _⟩ := finiteTypeUnpointedLocalAcyclicFppf_existsUnique f T.unop s hs
    exact ⟨abel _ D.val, (finiteTypeTestAbel
      (IsPullback.of_hasPullback f T.unop.hom) D).property, hD⟩
  · exact (geometricAcyclicFppfSubfunctor f).le_sheafify _

/-- The globally represented acyclic image satisfies effective fppf descent without a section. -/
theorem finiteTypeUnpointedGeometricAcyclicFppf_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of R)))
      (geometricAcyclicFppfSubfunctor f).toFunctor := by
  rw [← finiteTypeLocalGeometricAcyclicFppf_eq f]
  exact localGeometricAcyclicFppf_isSheaf f

end FLT.Mazur.CartierAbel
