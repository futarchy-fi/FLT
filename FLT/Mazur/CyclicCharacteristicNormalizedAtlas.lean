/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAtlasRelabel
public import FLT.Mazur.CyclicHomNormalizedRelabelAction
public import FLT.Mazur.OddWeierstrassCyclicHomNormalizedRelabelAction

/-!
# Actual normalized subgroup charts in both characteristics

The two constructed closed slices retain the original subgroup loci and
normalization retractions. The same finite relabeling group acts on both.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n]

/-- The actual normalized subgroup loci in the two characteristic charts. -/
def normalizedLocus : Bool → Scheme
  | false => UniversalWeierstrass.cyclicHomNormalizedLocus n
  | true => OddWeierstrassParameter.cyclicHomNormalizedLocus n

/-- Each closed normalized slice retains its original subgroup parameter. -/
def normalizedInclusion : (b : Bool) → normalizedLocus n b ⟶ locus n b
  | false => UniversalWeierstrass.cyclicHomNormalizedLocusInclusion n
  | true => OddWeierstrassParameter.cyclicHomNormalizedLocusInclusion n

/-- Both actual normalized chart inclusions are closed immersions. -/
instance normalizedInclusion_isClosedImmersion (b : Bool) :
    IsClosedImmersion (normalizedInclusion n b) := by
  cases b
  · exact UniversalWeierstrass.cyclicHomNormalizedLocusInclusion_isClosedImmersion n
  · exact OddWeierstrassParameter.cyclicHomNormalizedLocusInclusion_isClosedImmersion n

/-- Normalize the entire original marked subgroup family in either characteristic. -/
def normalization : (b : Bool) → locus n b ⟶ normalizedLocus n b
  | false => UniversalWeierstrass.cyclicHomLocusNormalization n
  | true => OddWeierstrassParameter.cyclicHomLocusNormalization n

/-- The actual normalization morphisms retract both original closed slices. -/
@[reassoc] theorem normalizedInclusion_normalization (b : Bool) :
    normalizedInclusion n b ≫ normalization n b = 𝟙 _ := by
  cases b
  · exact UniversalWeierstrass.cyclicHomNormalizedLocusInclusion_normalization n
  · exact OddWeierstrassParameter.cyclicHomNormalizedLocusInclusion_normalization n

/-- The same finite marking group acts on both normalized characteristic charts. -/
def normalizedRelabelAction : (b : Bool) → RelabelGroup n →* Aut (normalizedLocus n b)
  | false => (UniversalWeierstrass.cyclicHomNormalizedRelabelAction n).comp (evenLabels n)
  | true => (OddWeierstrassParameter.cyclicHomNormalizedRelabelAction n).comp
      (MonoidHom.snd _ _)

/-- Normalization intertwines the original and normalized full relabeling actions. -/
@[reassoc] theorem normalization_equivariant (b : Bool) (e : RelabelGroup n) :
    normalization n b ≫ (normalizedRelabelAction n b e).hom =
      (relabelAction n b e).hom ≫ normalization n b := by
  cases b
  · exact UniversalWeierstrass.cyclicHomLocusNormalization_equivariant n e.1 e.2.2
  · exact OddWeierstrassParameter.cyclicHomLocusNormalization_equivariant n e.2.1 e.2.2

end FLT.Mazur.CyclicCharacteristicAtlas
