/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertParameterCartier
public import FLT.Mazur.RelativeAbelFiberOriginalSquare
public import FLT.Mazur.RelativePicardFppfSheaf
public import FLT.Mazur.RelativePicardPullbackSquares

/-!
# The actual Hilbert universal divisor maps to the Picard sheaf

Exchange the two fiber-product factors to use the original Picard convention.
The full Cartier ideal, its flatness, and its Abel class commute with every
test morphism. No acyclicity is assumed of the universal family.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
open FLT.Mazur.FCurve FLT.Mazur.ClosedIdealCover FLT.Mazur.SchemePicard
namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts
open CartierAbel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {Z : Scheme} {z : Z ⟶ Spec (.of R)}
  (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]
  [SmoothOfRelativeDimension 1 z]

/-- The Hilbert family's entire ideal in the original Picard total-space convention. -/
def parameterPicardIdeal (T : Over (Spec (.of R))) (p : A.GluedParameters d T.hom) :=
  (A.parameterFamily d T.hom p).val.comap (pullbackSymmetry z T.hom).hom

/-- Exchanging total-space factors preserves both Cartier equations and relative flatness. -/
theorem parameterPicardIdeal_relative (T : Over (Spec (.of R)))
    (p : A.GluedParameters d T.hom) :
    RelativeEffectiveCartier (pullback.snd z T.hom) (A.parameterPicardIdeal d T p) := by
  have h := (A.parameterFamily_relativeEffectiveCartier d T.hom p).comap_of_isOpenImmersion
    (pullbackSymmetry z T.hom).hom
  simpa only [pullbackSymmetry_hom_comp_fst, parameterPicardIdeal] using h

/-- The actual full relative Hilbert divisor on the original Picard total space. -/
def parameterPicardDivisor (T : Over (Spec (.of R))) (p : A.GluedParameters d T.hom) :
    Divisor (pullback z T.hom) :=
  ⟨A.parameterPicardIdeal d T p, (A.parameterPicardIdeal_relative d T p).1⟩

omit [IsSeparated z] [SmoothOfRelativeDimension 1 z] in
/-- Factor exchange intertwines the two actual total-space base-change maps. -/
lemma parameterPicard_swap_natural {T U : Over (Spec (.of R))} (g : U ⟶ T) :
    (pullbackSymmetry z U.hom).hom ≫
        relativeIdealAmbientMap z T.hom U.hom g.left (Over.w g) =
      relativeTotalMap z g ≫ (pullbackSymmetry z T.hom).hom := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, relativeIdealAmbientMap_fst, relativeIdealAmbientMap_snd,
      pullbackSymmetry_hom_comp_fst_assoc,
      pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd,
      relativeTotalMap_fst, relativeTotalMap_snd]

omit [SmoothOfRelativeDimension 1 z] in
/-- All full equations commute with arbitrary test change in Picard's factor convention. -/
lemma parameterPicardIdeal_natural {T U : Over (Spec (.of R))} (g : U ⟶ T)
    (p : A.GluedParameters d T.hom) :
    A.parameterPicardIdeal d U ⟨g.left ≫ p.val, by rw [Category.assoc, p.property, Over.w]⟩ =
      (A.parameterPicardIdeal d T p).comap (relativeTotalMap z g) := by
  unfold parameterPicardIdeal
  rw [← A.parameterFamily_natural d T.hom U.hom g.left (Over.w g) p]
  change ((A.parameterFamily d T.hom p).val.comap _).comap _ = _
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    parameterPicard_swap_natural]

/-- The full Hilbert divisor's Abel class as a section of the original fppf Picard sheaf. -/
def parameterAbelClass (T : Over (Spec (.of R))) (p : A.GluedParameters d T.hom) :=
  relativeFppfClass z T (abel (pullback.snd z T.hom) (A.parameterPicardDivisor d T p))

/-- The actual Hilbert Abel map is natural on arbitrary original test schemes. -/
lemma parameterAbelClass_natural {T U : Over (Spec (.of R))} (g : U ⟶ T)
    (p : A.GluedParameters d T.hom) :
    A.parameterAbelClass d U ⟨g.left ≫ p.val, by rw [Category.assoc, p.property, Over.w]⟩ =
      (relativeFppfSheaf z).obj.map g.op (A.parameterAbelClass d T p) := by
  rw [parameterAbelClass, parameterAbelClass, relativeFppfClass_naturality]
  apply congrArg (relativeFppfClass z U)
  change _ = relativeMap _ _ _ _ _ _
  rw [← abel_originalSquare (relativeTotalMap_isPullback z g)
    (A.parameterPicardDivisor d T p) (A.parameterPicardIdeal_relative d T p)]
  apply congrArg (abel (pullback.snd z U.hom))
  exact Subtype.ext (A.parameterPicardIdeal_natural d g p)

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
