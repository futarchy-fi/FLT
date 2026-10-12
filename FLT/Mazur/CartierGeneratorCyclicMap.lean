/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierGeneratorOrbitCover
public import FLT.Mazur.ConstantCyclicRelativeGeometry
public import FLT.Mazur.ConstantCyclicSectionMap

/-!
# The actual constant-group morphism associated to a Cartier generator

Only torsion is needed to construct the group morphism. The Cartier orbit
identity proves surjectivity; when the target subgroup is etale, the same
morphism is a finite etale cover retaining the prescribed generator.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  (H : E.FiniteSubgroup n) (P : 𝟙_ (Over S) ⟶ H.carrier) (hP : P ^ n = 1)

/-- The powers of any n-torsion subgroup section, with residue-class labels. -/
def generatorPowers : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ H.carrier) where
  toFun i := P ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change P ^ (i.toAdd + j.toAdd).val = P ^ i.toAdd.val * P ^ j.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hP).symm

/-- Natural-number labels retain the original section powers. -/
theorem generatorPowers_natCast (k : ℕ) :
    H.generatorPowers P hP (Multiplicative.ofAdd (k : ZMod n)) = P ^ k := by
  change P ^ (k : ZMod n).val = P ^ k
  rw [ZMod.val_natCast]
  exact (pow_eq_pow_mod _ hP).symm

/-- The original torsion section defines a morphism of actual group schemes. -/
def generatorCyclicMap : ConstantCyclicGroup.model S n ⟶ H.carrier :=
  ConstantCyclicSectionMap.toScheme (H.generatorPowers P hP)

/-- The cyclic map preserves the subgroup group law. -/
instance generatorCyclicMap_isMonHom : IsMonHom (H.generatorCyclicMap P hP) :=
  inferInstanceAs (IsMonHom (ConstantCyclicSectionMap.toScheme (H.generatorPowers P hP)))

/-- The map retains each original orbit section, including the generator. -/
@[reassoc] theorem generatorCyclicMap_component (k : ℕ) :
    ConstantCyclicGroup.component S n (k : ZMod n) ≫ H.generatorCyclicMap P hP =
      P ^ k := by
  rw [generatorCyclicMap, ConstantCyclicSectionMap.component_toScheme,
    generatorPowers_natCast]

/-- The cyclic map is finite over the original subgroup. -/
instance generatorCyclicMap_finite : IsFinite (H.generatorCyclicMap P hP).left := by
  have : IsFinite (ConstantCyclicGroup.model S n).hom :=
    (ConstantCyclicRelativeGeometry.degree S n).1
  have : IsFinite ((H.generatorCyclicMap P hP).left ≫ H.carrier.hom) := by
    rw [Over.w]
    infer_instance
  exact IsFinite.of_comp _ H.carrier.hom

/-- If the actual subgroup is etale, its cyclic presentation map is etale. -/
instance generatorCyclicMap_etale [Etale H.carrier.hom] :
    Etale (H.generatorCyclicMap P hP).left := by
  have : Etale ((H.generatorCyclicMap P hP).left ≫ H.carrier.hom) := by
    rw [Over.w]
    exact ConstantCyclicRelativeGeometry.etale S n
  exact Etale.of_comp _ H.carrier.hom

variable {P}

/-- The Cartier identity makes the finite cyclic map cover the actual subgroup. -/
theorem IsCartierGenerator.cyclicMap_surjective (h : H.IsCartierGenerator P) :
    Surjective (H.generatorCyclicMap P h.1).left := by
  constructor
  intro x
  obtain ⟨i, hi⟩ := h.exists_orbit_point H x
  refine ⟨(ConstantCyclicGroup.component S n (i.val : ZMod n)).left
    (H.carrier.hom x), ?_⟩
  have he := congrArg (fun f : 𝟙_ (Over S) ⟶ H.carrier ↦ f.left (H.carrier.hom x))
    (H.generatorCyclicMap_component P h.1 i.val)
  exact he.trans hi

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
