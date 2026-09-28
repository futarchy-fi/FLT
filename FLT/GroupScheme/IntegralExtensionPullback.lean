/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.IntegralKernelBaseChange

/-!
# Pulling an integral subgroup back through a finite-flat quotient

An integral subgroup of a quotient pulls back to an integral intermediate
model. Both resulting sequences retain the original endpoints, compatible
maps, faithful flatness, and the prescribed second-coordinate torsor formula.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R : Type} [CommRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    [IsDedekindDomain R] [IsPrincipalIdealRing R]

/-- Pull an integral kernel back through an integral quotient, keeping all maps
in the two resulting extensions compatible with the original diagram. -/
theorem pullbackIntegralExtensionsCompatible
    {A H T M Q : FiniteFlatObject R}
    (E : FiniteFlatExtension A H T) (S : FiniteFlatExtension M T Q) :
    ∃ B : FiniteFlatObject R, ∃ F : FiniteFlatExtension A B M,
      ∃ G : FiniteFlatExtension B H Q,
        F.inclusion.comp G.inclusion = E.inclusion ∧
        F.quotient.comp S.inclusion = G.inclusion.comp E.quotient ∧
        G.quotient = E.quotient.comp S.quotient := by
  let qH := E.quotient.comp S.quotient
  have hqH : Function.Surjective (FiniteFlatObject.pointMap qH) := by
    intro q
    obtain ⟨t, ht⟩ := S.pointsSurjective q
    obtain ⟨h, hh⟩ := E.pointsSurjective t
    exact ⟨h, by rw [FiniteFlatObject.pointMap_comp, hh, ht]⟩
  have hqHO : qH.toAlgHom.toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.stableUnderComposition _ _
      S.quotientFaithfullyFlat E.quotientFaithfullyFlat
  obtain ⟨B, G, hG⟩ := FiniteFlatObject.existsExtensionOfQuotient qH hqH hqHO
  have hf : E.inclusion.toAlgHom.comp G.quotient.toAlgHom =
      (Algebra.ofId R A.model.CoordinateRing).comp
        (Bialgebra.counitAlgHom R Q.model.CoordinateRing) := by
    rw [hG]
    change (E.inclusion.toAlgHom.comp E.quotient.toAlgHom).comp S.quotient.toAlgHom = _
    rw [E.compositionZero]
    ext q
    exact congrArg (algebraMap R A.model.CoordinateRing)
      (CoalgHomClass.counit_comp_apply S.quotient q)
  let f : A.Hom B := G.liftKernel E.inclusion hf
  have hfi : f.comp G.inclusion = E.inclusion := G.liftKernelComp _ hf
  have hg : (G.inclusion.comp E.quotient).toAlgHom.comp S.quotient.toAlgHom =
      (Algebra.ofId R B.model.CoordinateRing).comp
        (Bialgebra.counitAlgHom R Q.model.CoordinateRing) := by
    change G.inclusion.toAlgHom.comp qH.toAlgHom = _
    rw [← hG]
    exact G.compositionZero
  let g : B.Hom M := S.liftKernel (G.inclusion.comp E.quotient) hg
  have hgi : g.comp S.inclusion = G.inclusion.comp E.quotient := S.liftKernelComp _ hg
  have hgO : letI := g.toAlgHom.toRingHom.toAlgebra;
      Module.FaithfullyFlat M.model.CoordinateRing B.model.CoordinateRing :=
    kernelMapFaithfullyFlat G S E.quotient g hG.symm hgi E.quotientFaithfullyFlat
  have hfP (a : A.points) :
      FiniteFlatObject.pointMap G.inclusion (FiniteFlatObject.pointMap f a) =
        FiniteFlatObject.pointMap E.inclusion a := by
    simpa only [FiniteFlatObject.pointMap_comp] using
      congrArg (fun k : A.Hom H ↦ FiniteFlatObject.pointMap k a) hfi
  have hgP (b : B.points) :
      FiniteFlatObject.pointMap S.inclusion (FiniteFlatObject.pointMap g b) =
        FiniteFlatObject.pointMap E.quotient (FiniteFlatObject.pointMap G.inclusion b) := by
    simpa only [FiniteFlatObject.pointMap_comp] using
      congrArg (fun k : B.Hom T ↦ FiniteFlatObject.pointMap k b) hgi
  have hfG : Function.Injective (FiniteFlatObject.pointMap f) := by
    intro a b hab
    apply E.pointsInjective
    rw [← hfP, ← hfP, hab]
  have hfO : Function.Surjective f := by
    intro a
    obtain ⟨h, hh⟩ := E.inclusion_surjective a
    exact ⟨G.inclusion h, (DFunLike.congr_fun hfi h).trans hh⟩
  have hgG : Function.Surjective (FiniteFlatObject.pointMap g) := by
    intro m
    obtain ⟨h, hh⟩ := E.pointsSurjective (FiniteFlatObject.pointMap S.inclusion m)
    have hh0 : FiniteFlatObject.pointMap G.quotient h = 0 := by
      rw [hG, FiniteFlatObject.pointMap_comp, hh]
      exact (S.pointsExact _).mpr ⟨m, rfl⟩
    obtain ⟨b, hb⟩ := (G.pointsExact h).mp hh0
    refine ⟨b, S.pointsInjective ?_⟩
    rw [hgP, hb, hh]
  have hexact : ∀ b, FiniteFlatObject.pointMap g b = 0 ↔
      ∃ a, FiniteFlatObject.pointMap f a = b := by
    intro b
    constructor
    · intro hb
      have hh : FiniteFlatObject.pointMap E.quotient
          (FiniteFlatObject.pointMap G.inclusion b) = 0 := by
        rw [← hgP, hb, map_zero]
      obtain ⟨a, ha⟩ := (E.pointsExact _).mp hh
      exact ⟨a, G.pointsInjective ((hfP a).trans ha)⟩
    · rintro ⟨a, rfl⟩
      apply S.pointsInjective
      rw [map_zero, hgP, hfP]
      exact (E.pointsExact _).mpr ⟨a, rfl⟩
  let F := FiniteFlatObject.extensionOfExactMaps f g hfG hfO hgG hexact hgO
  refine ⟨B, F, G, ?_, ?_, hG⟩
  · dsimp only [F]
    rw [FiniteFlatObject.extensionOfExactMapsInclusion]
    exact hfi
  · dsimp only [F]
    rw [FiniteFlatObject.extensionOfExactMapsQuotient]
    exact hgi

/-- Pullback of integral extensions produces an extension by the original inner
kernel and an extension with the original outer quotient. -/
theorem pullbackIntegralExtensions
    {A H T M Q : FiniteFlatObject R}
    (E : FiniteFlatExtension A H T) (S : FiniteFlatExtension M T Q) :
    ∃ B : FiniteFlatObject R,
      Nonempty (FiniteFlatExtension A B M) ∧ Nonempty (FiniteFlatExtension B H Q) := by
  obtain ⟨B, F, G, _, _, _⟩ := pullbackIntegralExtensionsCompatible E S
  exact ⟨B, ⟨F⟩, ⟨G⟩⟩

end ThreeAdicPlan
