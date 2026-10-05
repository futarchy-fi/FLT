/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechConnecting
public import FLT.Mazur.SequentialCochainBoundary
public import FLT.Mazur.SequentialFiniteProducts

/-!
# Finite-stage localization of finite-cover Cech cohomology

Local section lifting and kernel annihilation on the finite cover
intersections imply finite-stage annihilation in the actual Cech complex.
The target complex must have zero cohomology in the degree considered.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.SequentialCechLocalization

open CechSheafHZero CechAcyclicCokernel

variable {X : TopCat.{u}} {ι : Type u} [Finite ι] (U : ι → Opens X)
  (F G : ℕ ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) (a : F ⟶ G)

/-- The sequence of sections on one specified open. -/
def sections (W : Opens X) : ℕ ⥤ AddCommGrpCat.{u} :=
  F ⋙ sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op W)

/-- The induced sectionwise morphism of sequences. -/
def sectionMap (W : Opens X) : sections F W ⟶ sections G W :=
  Functor.whiskerRight a (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op W))

/-- The actual Cech cochain system of the coefficient sequence. -/
abbrev complexes : ℕ ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  F ⋙ CechConnecting.sheafCechFunctor U

/-- The actual cochain restriction maps induced by the coefficient morphisms. -/
abbrev complexMap : complexes U F ⟶ complexes U G :=
  Functor.whiskerRight a (CechConnecting.sheafCechFunctor U)

/-- Finite products of local section lifts give a lift of an actual Cech cochain. -/
theorem cochain_lift (q : ℕ)
    (hLift : ∀ v : Fin (q + 1) → ι, ∀ n (b : (G.obj n).obj.obj (op (V U q v))),
      ∃ (m : ℕ) (h : n ≤ m) (c : (F.obj m).obj.obj (op (V U q v))),
        (a.app m).hom.app (op (V U q v)) c = (G.map (homOfLE h)).hom.app (op (V U q v)) b)
    (n : ℕ) (b : ((complexes U G).obj n).X q) :
    ∃ (m : ℕ) (h : n ≤ m) (c : ((complexes U F).obj m).X q),
      ((complexMap U F G a).app m).f q c = ((complexes U G).map (homOfLE h)).f q b := by
  obtain ⟨m, h, c, hc⟩ := SequentialFiniteProducts.common_stage_lift
    (fun v ↦ sections F (V U q v)) (fun v ↦ sections G (V U q v))
    (fun v ↦ sectionMap F G a (V U q v)) hLift n (termEquiv U (G.obj n) q b)
  refine ⟨m, h, (termEquiv U (F.obj m) q).symm c, ?_⟩
  apply (termEquiv U (G.obj m) q).injective
  funext v
  change termEquiv U (G.obj m) q
    (((cechComplexFunctor U).map (a.app m).hom).f q _) v =
      termEquiv U (G.obj m) q
        (((cechComplexFunctor U).map (G.map (homOfLE h)).hom).f q b) v
  rw [termEquiv_naturality, termEquiv_naturality]
  erw [AddEquiv.apply_symm_apply]
  exact hc v

/-- A finite family of local restriction-kernel elements dies at one common cochain stage. -/
theorem cochain_annihilator (q : ℕ)
    (hKill : ∀ v : Fin (q + 1) → ι, ∀ n (x : (F.obj n).obj.obj (op (V U q v))),
      (a.app n).hom.app (op (V U q v)) x = 0 →
      ∃ (m : ℕ) (h : n ≤ m), (F.map (homOfLE h)).hom.app (op (V U q v)) x = 0)
    (n : ℕ) (x : ((complexes U F).obj n).X q)
    (hx : ((complexMap U F G a).app n).f q x = 0) :
    ∃ (m : ℕ) (h : n ≤ m), ((complexes U F).map (homOfLE h)).f q x = 0 := by
  have hx' (v : Fin (q + 1) → ι) :
      (a.app n).hom.app (op (V U q v)) (termEquiv U (F.obj n) q x v) = 0 := by
    rw [← termEquiv_naturality]
    erw [hx, map_zero]
    rfl
  obtain ⟨m, h, hm⟩ := SequentialFiniteProducts.common_stage_annihilator
    (fun v ↦ sections F (V U q v)) (fun v ↦ sections G (V U q v))
    (fun v ↦ sectionMap F G a (V U q v)) hKill n (termEquiv U (F.obj n) q x) hx'
  refine ⟨m, h, (termEquiv U (F.obj m) q).injective ?_⟩
  funext v
  change termEquiv U (F.obj m) q
    (((cechComplexFunctor U).map (F.map (homOfLE h)).hom).f q x) v = _
  rw [termEquiv_naturality, map_zero]
  exact hm v

/-- The local finite-stage conditions kill actual Cech cohomology classes. -/
theorem homology_annihilator (q : ℕ)
    (hExact : ∀ n, ((complexes U G).obj n).ExactAt (q + 1))
    (hLift : ∀ v : Fin (q + 1) → ι, ∀ n (b : (G.obj n).obj.obj (op (V U q v))),
      ∃ (m : ℕ) (h : n ≤ m) (c : (F.obj m).obj.obj (op (V U q v))),
        (a.app m).hom.app (op (V U q v)) c = (G.map (homOfLE h)).hom.app (op (V U q v)) b)
    (hKill : ∀ v : Fin (q + 2) → ι, ∀ n (x : (F.obj n).obj.obj (op (V U (q + 1) v))),
      (a.app n).hom.app (op (V U (q + 1) v)) x = 0 →
      ∃ (m : ℕ) (h : n ≤ m), (F.map (homOfLE h)).hom.app (op (V U (q + 1) v)) x = 0)
    (n : ℕ) (x : CH U (F.obj n) (q + 1)) :
    ∃ (m : ℕ) (h : n ≤ m), CHmap U (F.map (homOfLE h)) (q + 1) x = 0 := by
  apply SequentialCochainBoundary.homology_annihilator_of_boundaries (complexes U F) q
  exact SequentialCochainBoundary.exists_boundary_at_stage (complexes U F) (complexes U G)
    (complexMap U F G a) q hExact (cochain_lift U F G a q hLift)
    (cochain_annihilator U F G a (q + 1) hKill)

end FLT.Mazur.SequentialCechLocalization
