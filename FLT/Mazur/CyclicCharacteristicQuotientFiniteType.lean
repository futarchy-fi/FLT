/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicQuotientCover
public import FLT.Mazur.SchemeFiniteGroupQuotientFiniteType

/-!
# Finite type of the actual characteristic quotient targets

Artin--Tate applies to the invariant coordinates of the actual selected
finite type affine source charts. Their open cover proves finite type of
each glued quotient target over the integers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The integer structure map on each selected affine quotient chart. -/
def invariantAffineQuotientToInt (i : InvariantAffineIndex n) :
    invariantAffineQuotient n i ⟶ Spec (.of ℤ) :=
  invariantAffineQuotientInclusion n i ≫ normalizedQuotientToInt n i.1

/-- The affine quotient target is finite type over the integers by invariant coordinates. -/
instance invariantAffineQuotientToInt_locallyOfFiniteType (i : InvariantAffineIndex n) :
    LocallyOfFiniteType (invariantAffineQuotientToInt n i) := by
  have he : invariantAffineQuotientToInt n i =
      SchemeFiniteGroupQuotient.quotientToInt (invariantAffineAction n i) :=
    specZIsTerminal.hom_ext _ _
  rw [he]
  exact SchemeFiniteGroupQuotient.quotientToInt_locallyOfFiniteType _ (invariantAffineToInt n i)

/-- The selected affine quotient chart is quasi-compact over the integers. -/
instance invariantAffineQuotientToInt_quasiCompact (i : InvariantAffineIndex n) :
    QuasiCompact (invariantAffineQuotientToInt n i) :=
  (HasAffineProperty.iff_of_isAffine
    (Q := fun X _ _ _ => CompactSpace X)).mpr inferInstance

/-- The constructed affine quotient targets are Noetherian. -/
instance invariantAffineQuotient_isNoetherian (i : InvariantAffineIndex n) :
    IsNoetherian (invariantAffineQuotient n i) where
  toIsLocallyNoetherian :=
    LocallyOfFiniteType.isLocallyNoetherian (invariantAffineQuotientToInt n i)
  toCompactSpace := inferInstance

/-- The actual glued characteristic quotient is locally of finite type over the integers. -/
instance normalizedQuotientToInt_locallyOfFiniteType (b : Bool) :
    LocallyOfFiniteType (normalizedQuotientToInt n b) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (normalizedQuotientCover n b)
  intro i
  exact invariantAffineQuotientToInt_locallyOfFiniteType n ⟨b, i⟩

/-- The quotient of the original quasi-compact locus remains quasi-compact. -/
instance normalizedQuotient_compactSpace (b : Bool) : CompactSpace (normalizedQuotient n b) :=
  Function.Surjective.compactSpace (normalizedQuotientMap n b).continuous
    (normalizedQuotientMap n b).surjective

/-- The actual quotient target is quasi-compact over the integers. -/
instance normalizedQuotientToInt_quasiCompact (b : Bool) :
    QuasiCompact (normalizedQuotientToInt n b) :=
  (HasAffineProperty.iff_of_isAffine
    (Q := fun X _ _ _ => CompactSpace X)).mpr inferInstance

/-- Both constructed characteristic quotients are Noetherian schemes. -/
instance normalizedQuotient_isNoetherian (b : Bool) : IsNoetherian (normalizedQuotient n b) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (normalizedQuotientToInt n b)
  toCompactSpace := inferInstance

end FLT.Mazur.CyclicCharacteristicAtlas
