/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianCanonicalImageRepresentative
public import FLT.Mazur.GrassmannianSheafClassificationFaithful

/-!
# Full recovery on the fixed canonical source cover

A classification of any original global quotient constructs a unique
projection-preserving isomorphism to its image on the fixed canonical cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable {X : Scheme.{u}} (β : X ⟶ Spec (.of R))
  {P : X.Modules} (p : grassmannianSchemeAmbient (M := M) β ⟶ P) [Epi p]
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)

/-- A classified quotient is uniquely its actual full image on the fixed canonical cover. -/
theorem SheafQuotientClassifies.canonicalImageRecovery
    {f : X ⟶ ambientGrassmannianScheme R M κ d}
    (h : SheafQuotientClassifies β p b hκ f)
    (hf : f ≫ ambientGrassmannianStructure R M κ d = β) :
    ∃! e : P ≅ (imageRepresentativeOver b hκ f β hf).sheaf,
      p ≫ e.hom = (imageRepresentativeOver b hκ f β hf).projection :=
  h.existsUnique_iso β p _ b hκ (imageRepresentativeOver_classifies b hκ f β hf)

/-- Local frames recover the original sheaf and the entire projection on the fixed cover. -/
theorem existsUnique_locallyFreeQuotientCanonicalRecovery {τ : Type u} [Fintype τ]
    (hP : ModuleSheafLocalFrames.HasFrames τ P) (hd : Fintype.card τ = d) :
    let f := locallyFreeQuotientClassifyingMap β p b hκ hP hd
    let hf := locallyFreeQuotientClassifyingMap_over β p b hκ hP hd
    ∃! e : P ≅ (imageRepresentativeOver b hκ f β hf).sheaf,
      p ≫ e.hom = (imageRepresentativeOver b hκ f β hf).projection :=
  (locallyFreeQuotientClassifyingMap_spec β p b hκ hP hd).canonicalImageRecovery
    β p b hκ (locallyFreeQuotientClassifyingMap_over β p b hκ hP hd)

end FLT.Mazur.GrassmannianChart
