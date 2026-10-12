/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianOverlapTransitionEquiv
public import FLT.Mazur.GrassmannianLocalizedTransitionScheme

/-!
# Scheme isomorphisms between actual Grassmannian overlaps

The inverse localized algebra transitions give a scheme isomorphism between the
two principal overlap opens. Its map into the second chart is the earlier rational
transition morphism, so that morphism is now proved to be an open immersion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R : Type u} [CommRing R] {ι κ : Type u} [Fintype ι] [Fintype κ] {d : ℕ}
  (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))

/-- The determinant principal open scheme belonging to an actual ambient change. -/
abbrev ambientOverlapScheme :=
  principalOverlapScheme (ambientBlockP e.toLinearMap) (ambientBlockQ e.toLinearMap)

/-- The actual isomorphism between the forward and reverse determinant overlap schemes. -/
def ambientOverlapSchemeIso : ambientOverlapScheme e ≅ ambientOverlapScheme e.symm :=
  Scheme.Spec.mapIso (ambientOverlapTransitionEquiv e).toRingEquiv.toCommRingCatIso.op

/-- Its forward map is precisely the spectrum of the constructed localized transition. -/
theorem ambientOverlapSchemeIso_hom :
    (ambientOverlapSchemeIso e).hom =
      Spec.map (CommRingCat.ofHom (ambientOverlapTransitionHom e).toRingHom) := rfl

/-- Its inverse is precisely the spectrum of the reverse ambient transition. -/
theorem ambientOverlapSchemeIso_inv :
    (ambientOverlapSchemeIso e).inv =
      Spec.map (CommRingCat.ofHom (ambientOverlapTransitionHom e.symm).toRingHom) := rfl

/-- The overlap isomorphism factors the earlier rational scheme transition into the second chart. -/
theorem ambientOverlapSchemeIso_factor :
    (ambientOverlapSchemeIso e).hom ≫
      principalOverlapInclusion (ambientBlockP e.symm.toLinearMap)
        (ambientBlockQ e.symm.toLinearMap) =
      localizedChartTransitionScheme (ambientBlockP e.toLinearMap) (ambientBlockQ e.toLinearMap)
        (ambientBlockU e.toLinearMap) (ambientBlockT e.toLinearMap) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact ambientOverlapTransitionHom_algebraMap e

/-- The original rational transition is an open immersion with its actual reverse open domain. -/
instance ambientTransition_isOpenImmersion :
    IsOpenImmersion (localizedChartTransitionScheme (ambientBlockP e.toLinearMap)
      (ambientBlockQ e.toLinearMap) (ambientBlockU e.toLinearMap)
      (ambientBlockT e.toLinearMap)) := by
  rw [← ambientOverlapSchemeIso_factor e]
  infer_instance

/-- The overlap isomorphism respects the original coefficient-ring base. -/
theorem ambientOverlapSchemeIso_over :
    (ambientOverlapSchemeIso e).hom ≫
      principalOverlapStructure (ambientBlockP e.symm.toLinearMap)
        (ambientBlockQ e.symm.toLinearMap) =
      principalOverlapStructure (ambientBlockP e.toLinearMap) (ambientBlockQ e.toLinearMap) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (ambientOverlapTransitionHom e).comp_algebraMap

end FLT.Mazur.GrassmannianChart
