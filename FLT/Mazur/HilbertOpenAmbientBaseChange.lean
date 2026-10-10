/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOpenAmbientFamilies

/-!
# Cartesian base change of actual open ambient families

The inverse-image ambient opens commute with every map of scheme bases.
Their actual restriction maps form cartesian squares, so pulling back a full
ideal family preserves finite locally free degree without extra hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (K : Ideal (MvPolynomial I R))
variable (U : (Spec (.of (MvPolynomial I R ⧸ K))).Opens)
variable {X Y : Scheme.{u}} (s : X ⟶ Spec (.of R)) (t : Y ⟶ Spec (.of R))
variable (g : Y ⟶ X) (hg : g ≫ s = t)

/-- The relative ambient open is exactly the inverse image after arbitrary base change. -/
theorem quotientRelativeOpen_preimage :
    quotientRelativeAmbientMap R I K s t g hg ⁻¹ᵁ quotientRelativeOpen R I K U s =
      quotientRelativeOpen R I K U t := by
  unfold quotientRelativeOpen
  rw [← Scheme.Hom.comp_preimage, quotientRelativeAmbientMap_snd]

/-- The actual ambient base-change morphism restricted to the original ambient open. -/
def quotientRelativeOpenMap :
    (quotientRelativeOpen R I K U t).toScheme ⟶ (quotientRelativeOpen R I K U s).toScheme :=
  (quotientRelativeAmbientMap R I K s t g hg).resLE _ _
    (quotientRelativeOpen_preimage R I K U s t g hg).ge

/-- The restricted base-change map preserves the actual open immersion. -/
@[reassoc]
theorem quotientRelativeOpenMap_ι :
    quotientRelativeOpenMap R I K U s t g hg ≫ (quotientRelativeOpen R I K U s).ι =
      (quotientRelativeOpen R I K U t).ι ≫ quotientRelativeAmbientMap R I K s t g hg :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The relative-open comparison is cartesian on the actual containing ambient schemes. -/
theorem quotientRelativeOpenMap_ambient_isPullback :
    IsPullback (quotientRelativeOpenMap R I K U s t g hg)
      (quotientRelativeOpen R I K U t).ι (quotientRelativeOpen R I K U s).ι
      (quotientRelativeAmbientMap R I K s t g hg) := by
  apply IsOpenImmersion.isPullback
  · exact (quotientRelativeOpenMap_ι R I K U s t g hg).symm
  · simpa only [Scheme.Opens.opensRange_ι] using
      quotientRelativeOpen_preimage R I K U s t g hg

/-- Actual open ambient families base-change over the same arbitrary map of bases. -/
theorem quotientRelativeOpenMap_isPullback :
    IsPullback (quotientRelativeOpenMap R I K U s t g hg)
      ((quotientRelativeOpen R I K U t).ι ≫ pullback.fst _ _)
      ((quotientRelativeOpen R I K U s).ι ≫ pullback.fst _ _) g :=
  (quotientRelativeOpenMap_ambient_isPullback R I K U s t g hg).paste_vert
    (quotientRelativeAmbientMap_isPullback R I K s t g hg)

/-- Pull back the full ideal of an open ambient family; its degree follows from cartesianness. -/
def openQuotientSchemeFamilyBaseChange (d : ℕ)
    (J : OpenQuotientSchemeFamilies R I d K U s) : OpenQuotientSchemeFamilies R I d K U t :=
  ⟨J.val.comap (quotientRelativeOpenMap R I K U s t g hg),
    ClosedIdealCover.restriction_degree J.val _
      (quotientRelativeOpenMap_isPullback R I K U s t g hg) d J.property⟩

end FLT.Mazur.HilbertChart
