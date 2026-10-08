/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperAmpleFiberModel
public import FLT.Mazur.ProperAmpleFiberNoetherian
public import FLT.Mazur.RelativeSectionAmpleLocality

/-!
# An ample fiber spreads over an arbitrary coefficient ring

Descend the proper finitely presented family and its invertible sheaf to
a finite integer coefficient model. Its ample fiber spreads by the
Noetherian theorem, and an affine neighborhood pulls that ampleness back
to the original family through the cartesian recovery square.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace FLT.Mazur.FCurve

/-- Noetherian approximation spreads an ample fiber for a proper finitely presented family. -/
theorem exists_relativeAmple_neighborhood_spectrum {A : Type} [CommRing A]
    {X : Scheme.{0}} (p : X ⟶ Spec (.of A)) [IsProper p] [LocallyOfFinitePresentation p]
    (L : X.Modules) (hL : LocallyFreeRankOne L) (x : Spec (.of A))
    (hA : RelativeAmple (p.fiberToSpecResidueField x)
      ((pullback (p.fiberι x)).obj L)) :
    ∃ U : (Spec (.of A)).Opens, x ∈ U ∧ IsAffineOpen U ∧
      RelativeAmple (p ∣_ U) (L.restrict (p ⁻¹ᵁ U).ι) := by
  obtain ⟨S, hS, _, Y, q, M, hq, _, _, hM, a, ha, ⟨e⟩, hF⟩ :=
    Approximation.exists_proper_ample_fiber_model p L hL x hA ∅ Set.finite_empty
  let _ : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  let b := Spec.map (CommRingCat.ofHom (algebraMap S A))
  have hFa : AmpleLineBundle ((pullback (q.fiberι (b x))).obj M) :=
    (hF.relativelyAmpleLineBundle (hM.pullback _)).ample_of_affine
  obtain ⟨V, hxV, _, hV⟩ :=
    exists_relativeAmple_neighborhood_locally_noetherian q (b x) hM hFa
  have hVr : RelativeAmple (q ∣_ V) (M.restrict (q ⁻¹ᵁ V).ι) :=
    hV.of_iso ((restrictFunctorIsoPullback (q ⁻¹ᵁ V).ι).app M)
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ b ⁻¹ᵁ V from hxV)
  let _ : IsAffine U.toScheme := hU
  have hB := ample_cartesian_open_of_relative ha V
    (hVr.relativelyAmpleLineBundle (hM.restrict _)) U hU hUV
  have hC : AmpleLineBundle (L.restrict (p ⁻¹ᵁ U).ι) :=
    hB.of_iso (((restrictFunctor (p ⁻¹ᵁ U).ι).mapIso e).symm)
  exact ⟨U, hxU, hU, (hC.relative_of_affine (p ∣_ U)).relativeAmple⟩

/-- The spectrum neighborhood theorem in the affine-section-open formulation. -/
theorem exists_ample_neighborhood_spectrum {A : Type} [CommRing A]
    {X : Scheme.{0}} (p : X ⟶ Spec (.of A)) [IsProper p] [LocallyOfFinitePresentation p]
    (L : X.Modules) (hL : LocallyFreeRankOne L) (x : Spec (.of A))
    (hA : AmpleLineBundle ((pullback (p.fiberι x)).obj L)) :
    ∃ U : (Spec (.of A)).Opens, x ∈ U ∧ IsAffineOpen U ∧
      AmpleLineBundle ((pullback (p ⁻¹ᵁ U).ι).obj L) := by
  let _ : IsProper (p.fiberToSpecResidueField x) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField]
    infer_instance
  obtain ⟨U, hxU, hU, ha⟩ := exists_relativeAmple_neighborhood_spectrum p L hL x
    (hA.relative_of_affine (p.fiberToSpecResidueField x)).relativeAmple
  let _ : IsAffine U.toScheme := hU
  have hb := (ha.relativelyAmpleLineBundle (hL.restrict _)).ample_of_affine
  exact ⟨U, hxU, hU, hb.of_iso ((restrictFunctorIsoPullback (p ⁻¹ᵁ U).ι).app L).symm⟩

end FLT.Mazur.FCurve
