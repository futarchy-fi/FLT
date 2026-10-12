/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleFaithfulSpectrum

/-!
# Original parameter sources over constructed faithful translation neighborhoods

The source is restricted by the original base function, with a cartesian square
and its original map to the translation scheme. Its chosen point is retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineEtaleFaithfulNeighborhood
variable {A V S : Scheme.{0}} (g : V ⟶ S) [IsAffine S] [Etale g] (β : A ⟶ V)

/-- The whole original parameter source over the constructed principal base neighborhood. -/
def parameterOpen (v : V) : A.Opens := β ⁻¹ᵁ sourceOpen g v

/-- The source restriction is literally by the original base coefficient. -/
theorem parameterOpen_eq_basicOpen (v : V) :
    parameterOpen g β v = A.basicOpen ((β ≫ g).appTop (parameter g v)) :=
  Scheme.Hom.preimage_basicOpen_top (β ≫ g) (parameter g v)

instance parameterOpen_affine [IsAffine A] (v : V) :
    IsAffine (parameterOpen g β v).toScheme := by
  rw [parameterOpen_eq_basicOpen]
  exact (isAffineOpen_top A).basicOpen _

/-- The original parameter-to-translation morphism on the full inverse image. -/
def parameterMap (v : V) :
    (parameterOpen g β v).toScheme ⟶ (sourceOpen g v).toScheme :=
  β ∣_ sourceOpen g v

/-- The restricted translation coordinate remains the original coordinate. -/
@[reassoc]
theorem parameterMap_ι (v : V) :
    parameterMap g β v ≫ (sourceOpen g v).ι = (parameterOpen g β v).ι ≫ β :=
  morphismRestrict_ι β (sourceOpen g v)

/-- The parameter restriction is a full scheme pullback, not a selected set of points. -/
theorem parameter_isPullback (v : V) :
    IsPullback (parameterOpen g β v).ι (parameterMap g β v) β (sourceOpen g v).ι :=
  (isPullback_morphismRestrict β (sourceOpen g v)).flip

/-- Its structural map to the new spectrum uses the original translation coordinate. -/
def parameterBase (v : V) :
    (parameterOpen g β v).toScheme ⟶ Spec (.of (BaseRing g v)) :=
  parameterMap g β v ≫ spectrumMap g v

/-- The constructed local parameter retains its entire original base-change square. -/
theorem parameterBase_isPullback (v : V) :
    IsPullback (parameterOpen g β v).ι (parameterBase g β v) (β ≫ g)
      (spectrumBase g v) :=
  (parameter_isPullback g β v).paste_vert (spectrum_isPullback g v)

/-- Every original parameter point survives its own translation neighborhood. -/
theorem mem_parameterOpen (a : A) : a ∈ parameterOpen g β (β a) := mem_baseOpen g (β a)

/-- The actual retained point, with its original residue-field point unchanged. -/
def parameterPoint (a : A) : (parameterOpen g β (β a)).toScheme :=
  ⟨a, mem_parameterOpen g β a⟩

/-- The retained point projects to exactly the original source point. -/
theorem parameterPoint_ι (a : A) :
    (parameterOpen g β (β a)).ι (parameterPoint g β a) = a := rfl

end FLT.Mazur.AffineEtaleFaithfulNeighborhood
