/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupSectionCover
public import FLT.Mazur.UniversallyClosedFiniteCover
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finiteness of the actual Y/Z subgroup closure

A finite coproduct of integral sections surjects onto the closure. Its composite
with the structural map is universally closed, so the structural map is too.
Separatedness and finite type give properness; quasi-finiteness gives finiteness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.EllipticSubgroupChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]

/-- The map from the finite coproduct of all actual integral subgroup sections. -/
def integralSectionsMap : (∐ fun _ : H => Spec (.of A)) ⟶ gluedClosure A W H 1 2 :=
  Sigma.desc (integralSection A W H)

/-- The integral sections jointly surject onto the glued subgroup closure. -/
instance integralSectionsMap_surjective : Surjective (integralSectionsMap A W H) := by
  constructor
  intro x
  obtain ⟨P, a, rfl⟩ := integralSections_cover A W H x
  refine ⟨Sigma.ι (fun _ : H => Spec (.of A)) P a, ?_⟩
  change (Sigma.ι (fun _ : H => Spec (.of A)) P ≫ integralSectionsMap A W H) a = _
  rw [integralSectionsMap, Sigma.ι_comp_desc]

/-- Universal closedness descends from the finite coproduct of sections. -/
instance closureToBase_universallyClosed : UniversallyClosed (closureToBase A W H 1 2) := by
  let X : H → Scheme := fun _ => Spec (.of A)
  have : Finite (sigmaOpenCover X).I₀ := inferInstanceAs (Finite H)
  have : UniversallyClosed (integralSectionsMap A W H ≫ closureToBase A W H 1 2) := by
    apply UniversallyClosedFiniteCover.universallyClosed _ (sigmaOpenCover X)
    intro P
    change H at P
    change UniversallyClosed
      (Sigma.ι X P ≫ integralSectionsMap A W H ≫ closureToBase A W H 1 2)
    dsimp only [X]
    rw [← Category.assoc, integralSectionsMap, Sigma.ι_comp_desc, integralSection_toBase]
    infer_instance
  exact UniversallyClosed.of_comp_surjective (integralSectionsMap A W H)
    (closureToBase A W H 1 2)

/-- The actual Y/Z closure of a finite subgroup is proper over the valuation ring. -/
instance closureToBase_isProper : IsProper (closureToBase A W H 1 2) := ⟨⟩

/-- Properness and the proved finite fibers make the actual global closure finite. -/
instance closureToBase_isFinite : IsFinite (closureToBase A W H 1 2) :=
  IsFinite.of_isProper_of_locallyQuasiFinite _

/-- The global closure is affine; its standard charts need not be finite over the base. -/
instance gluedClosure_isAffine : IsAffine (gluedClosure A W H 1 2) :=
  isAffine_of_isAffineHom (closureToBase A W H 1 2)

end FLT.Mazur.EllipticSubgroupChart
