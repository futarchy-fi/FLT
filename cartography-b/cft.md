# Cartography B — bead hub-lsb1u.9.2: Class field theory + solvable extensions

Second independent pass, 2026-08-14. Sources: /Users/kas/FLT working tree (main), Mathlib pin in
`.lake/packages/mathlib`, web. No cartography/ or cartography-b/ material consulted (independence rule).

## 1. Where CFT lives in the repo today

The blueprint concentrates everything CFT in the "bestiary" appendix,
`blueprint/src/chapter/chtopbestiary.tex`:

- `chtopbestiary.tex:5` — `\section{Results from class field theory}`.
- `chtopbestiary.tex:11-13` — `maximal_unramified_extension_of_p-adic_field` (Gal(K^un/K) ≅ Ẑ, arith vs geom Frobenius), `\notready`.
- `chtopbestiary.tex:19` — `local_Weil_group` definition.
- `chtopbestiary.tex:24-27` — `local_class_field_theory`: "two 'canonical' isomorphisms ... between $K^\times$ and the abelianisation of the Weil group of $K$", proof cited to Cassels–Fröhlich; `\notready`.
- `chtopbestiary.tex:29` — "Note that María Inés de Frutos Fernández and Filippo Nuccio are working on a formalisation of the proof of this using Lubin--Tate formal groups."
- `chtopbestiary.tex:38-77` — local Galois cohomology package: `local_galois_coh_finite` (finiteness, Serre §5.2 Prop 14), `local_galois_coh_dim_two` (cd = 2), `local_galois_coh_top_degree` (H²(G_K, μ_n) ≅ ℤ/n), H²(K, μ_∞) = ℚ/ℤ, `local_galois_coh_poincare` (local Tate duality via cup product), `local_galois_coh_euler_poincare` (h⁰−h¹+h² = 0). All `\notready`.
- `chtopbestiary.tex:83-86` — `global_class_field_theory`: π₀(𝔸_N^×/N^×) ≅ G_N^ab, compatible with local maps; `\uses{local_class_field_theory}`; `\notready`.
- `chtopbestiary.tex:90-94` — `Skinner_Wiles_CFT_trick` (`\uses{global_class_field_theory}`): finite solvable Galois L/K realizing prescribed local extensions L_v/K_v at a finite set S, linearly disjoint from any given K^avoid.
- `chtopbestiary.tex:96` — "We also need Poitou-Tate duality; I'll refrain from writing it down for now" (note: the parenthetical "we don't even have Galois cohomology in Lean yet" is now stale — see §4).
- `chtopbestiary.tex:255-266` — `moret-bailly` (points on curves with prescribed local behaviour; the CFT-trick's big brother; blocked on algebraic geometry, "we do not even have the definition of a curve over a field in Lean", line 268).

Assumptions layer:

- `FLT/Assumptions/README.md:36-37` — "Existence of a solvable extension of a number field with prescribed behaviour at a finite set of places (the proof uses class field theory)" — explicitly on the planned axiom list.
- `FLT/Assumptions/KnownIn1980s.lean:78` — `axiom knownin1980s {P : Prop} : P`, the sanctioned escape hatch; its docstring (lines 33-47) names "Langlands on cyclic base change" as an intended use.
- `FLT/Assumptions/Odlyzko.lean:31-34` — notes the 3-adic switch "avoids the Langlands-Tunnell theorem".

## 2. Consumer inventory (numbered), with the weakest CFT slice each needs

**N1. Tame-inertia character (local, sub-CFT).**
`blueprint/src/chapter/ch04overview.tex:46`: "Local class field theory (or a more elementary
approach) gives a map $I_v\to\calO_{F_v}^\times$". Implemented already as a Kummer-theory hack:
`FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean:178` defines
`localTameAbelianInertiaGroup` ("Note that this definition is somewhat cheating ... TODO: show that
this is indeed the right group", lines 172-176), on top of `localInertiaGroup` (line 167) and
`adicArithFrob` (line 213). Consumers: `FLT/Deformations/LiftFunctor.lean:132` (deformation
conditions), `FLT/GaloisRepresentation/Automorphic.lean:176` (tame rank-1 quotient hypothesis),
`FLT/GaloisRepresentation/HardlyRamified/*`.
Weakest slice: **none of CFT proper** — unramified theory + Kummer theory of the tame quotient
(I_v/wild ≅ lim k(v)^×). Local, no reciprocity.

**N2. `cyclic_base_change` — the solvable-extension consumer.**
`FLT/GaloisRepresentation/Automorphic.lean:127-184` (`sorry` at 184): statement takes
`[IsGalois F E] [Group.IsSolvable (E ≃ₐ[F] E)]` (line 133) and concludes automorphy transfer
`ρ.IsAutomorphicOfLevel ↔ (ρ.map ...).IsAutomorphicOfLevel` (lines 180-183). This is
Langlands' cyclic base change packaged for solvable towers; destined to be a
`knownin1980s`-class assumption (`FLT/Assumptions/KnownIn1980s.lean:39,69,90`).
Weakest slice: **no CFT theorem needed to state it** — statement infrastructure (GaloisRep,
Hecke algebras, quaternionic forms) already exists in-repo; the *proof* is automorphic-side
(trace formula), permanently out of scope.

**N3. Skinner–Wiles CFT trick — the solvable-extension *producer*.**
`chtopbestiary.tex:90-94`, consumed by the modularity lifting theorem
(`ch04overview.tex:68` `\uses{Skinner_Wiles_CFT_trick, ...}`) and by the potential-modularity
step (`ch04overview.tex:86`: "First one uses the Skinner--Wiles trick to reduce to the 'minimal
case', and this needs cyclic base change for GL(2)...").
Weakest slice: **global existence side only** — one needs, iteratively, cyclic global extensions
with prescribed local behaviour at finitely many places (Grunwald–Wang-style avoidance of the
special case, or ray-class-field existence). **No global reciprocity map, no Artin map, no
cohomological CFT** is needed for this consumer. It is also exactly the item pre-declared as an
axiom in `FLT/Assumptions/README.md:36-37` — so the *project-critical* slice is just being able
to **state** it: number fields, `adicCompletion`, `IsGalois`, `Group.IsSolvable`, places above
places — all already in Mathlib/FLT (cf. `Automorphic.lean:129-136`,
`HeightOneSpectrum.preimageComapFinset` at `Automorphic.lean:183`).

**N4. Local Galois cohomology package for the modularity lifting theorem.**
`ch04overview.tex:68-69`: `modularity_lifting_theorem` `\uses{Skinner_Wiles_CFT_trick,
local_galois_coh_dim_two, local_galois_coh_top_degree, local_galois_coh_poincare,
local_galois_coh_euler_poincare, ...}`. This is the deformation-theoretic dimension count
(Wiles product formula) inside Taylor–Wiles patching (`FLT/Patching/` is the module-theoretic
half, already far along; the Galois-cohomological half is not yet stated).
Weakest slice: **local Tate duality + local Euler characteristic for finite modules**
(Serre, Galois cohomology II.5). This needs H²(G_K, μ_n) ≅ ℤ/n — i.e. inv: Br(K)[n] ≅ ℤ/n, the
one genuinely CFT-flavoured local input — but **not** the reciprocity isomorphism K^× ≅ W_K^ab
and not Lubin–Tate.

**N5. Poitou–Tate / global duality.** `chtopbestiary.tex:96`; also
`FLT/GlobalLanglandsConjectures/GLzero.lean:26`: "Wiles' work used class field theory (in the
form of global Tate duality) crucially". Consumer: the global Selmer-group dimension formula
feeding N4's global step. Weakest slice: **Poitou–Tate for finite modules over number fields**
— the single largest honest CFT obligation if the project ever proves (rather than axiomatizes)
the lifting theorem's cohomological bookkeeping. Blueprint deliberately hasn't stated it.

**N6. GL(1) reciprocity for automorphic induction / "induced from a character ⇒ modular".**
`chtopbestiary.tex:213-214`: "automorphic induction from $\GL_1(K)$ to $\GL_2(F)$ when $K/F$ is a
degree 2 totally imaginary extension"; `ch04overview.tex:31` (converse-theorem item). Weakest
slice: **global Artin reciprocity for GL(1)** (Hecke characters of the idele class group ↔
characters of G_K^ab) — needed even to *state* the dictionary cleanly; sits behind
`global_class_field_theory` (`chtopbestiary.tex:83`). Likely absorbed into a `knownin1980s`
assumption together with the automorphic-induction theorem itself.

**N7. Brauer-group consumers (adjacent, not CFT proper).**
`FLT/Mathlib/RingTheory/SimpleRing/TensorProduct.lean:25`: "a prerequisite for defining the group
law on the Brauer [group]"; `FLT/Mathlib/LinearAlgebra/Determinant.lean:62`: "in a repo on
brauergroup which has been PRed into mathlib". Consumers: quaternion-algebra infrastructure
(`FLT/QuaternionAlgebra/`, `Automorphic.lean:100` `IsQuaternionAlgebra E (E ⊗[F] D) := sorry`).
Classification of quaternion algebras by ramification (Hilbert reciprocity / Br(K) ↪ ⊕ Br(K_v))
is *not currently stated anywhere* in blueprint or Lean — the repo works with a concrete
discriminant-1 D (`Automorphic.lean:80-81`) and dodges it so far.

**N8. Frobenius / unramified-extension bedrock (done or nearly done).**
`blueprint/src/chapter/FrobeniusProject.tex:93-99` (Frobenius miniproject);
`FLT/Deformations/RepresentationTheory/Frobenius.lean` (Andrew Yang, builds on
`Mathlib.RingTheory.Frobenius` — `IsArithFrobAt`, existence, uniqueness-mod-inertia at line 38-44
of the docstring); used by `GaloisRep.lean:350` (`mul_inv_mem_inertia`). Theorem
`maximal_unramified_extension_of_p-adic_field` (`chtopbestiary.tex:11`) is the remaining
unramified-CFT gap, but its working substitute (`adicArithFrob`, `localInertiaGroup`) exists.

**N9. Fujisaki / idele-class compactness (done).** `FLT/DivisionAlgebra/Finiteness.lean:44-62`
proves Fujisaki's lemma using `NumberField.AdeleRing.cocompact` (line 253) — the analytic
half of "first inequality"-style global CFT input is already formalized and in use. Not a
consumer of anything further.

## 3. Dependency edges

- N8 (Frobenius/inertia) → N1 (tame character) → N2 statement, LiftFunctor deformation conditions, HardlyRamified.
- ContCohomology (Mathlib, §4) → N4 (local duality/EP) → modularity_lifting_theorem; ContCohomology → N5 (Poitou–Tate) → global Selmer counts.
- `local_class_field_theory` (chtopbestiary.tex:24) → `global_class_field_theory` (:83, per `\uses`) → N3 (SW trick, :90) and N6 (GL(1) reciprocity) → potential modularity + minimal-case reduction (`ch04overview.tex:86`).
- N3 and N4 jointly → `modularity_lifting_theorem` (`ch04overview.tex:68`).
- N7 (Brauer group law) → quaternion algebra base change (`Automorphic.lean:100`) → N2.
- Moret–Bailly (`chtopbestiary.tex:255`) strictly stronger than N3's conclusion but gated on algebraic-geometry definitions (curves), an unrelated bottleneck.

## 4. Honest Mathlib coverage (checked against the repo's Mathlib pin)

Present in the pinned Mathlib (`.lake/packages/mathlib`):

- **Continuous group cohomology**: `Mathlib/RepresentationTheory/Homological/ContCohomology/{Basic,Functoriality,LowDegree}.lean` — the blueprint's "we don't even have Galois cohomology in Lean yet" (`chtopbestiary.tex:96`) is stale. FLT is actively extending it: `FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/CupProduct.lean` and `.../Basic.lean` ("Material destined for `Mathlib...ContCohomology.Basic`", Basic.lean:37) — cup products are the exact prerequisite for N4's duality pairing.
- **Discrete group cohomology**: `GroupCohomology/{Basic,Hilbert90,LongExactSequence,LowDegree,Shapiro,FiniteCyclic,Functoriality}.lean` plus `TateCohomology/Basic.lean` and `GroupHomology/` — Hilbert 90, Shapiro, and Tate cohomology of finite groups exist; herbrand-quotient-style cyclic machinery is beginning (`FiniteCyclic`). This is precisely the toolkit the classical cohomological proof of local CFT consumes.
- **Local fields**: `Mathlib/NumberTheory/LocalField/Basic.lean` (Andrew Yang, 2025): `IsNonarchimedeanLocalField` via `ValuativeRel` (locally compact, nondiscrete valuative topology; yields DVR integers, finite residue field). Definition-level only — no ramification filtration, no norm map theory, **no Lubin–Tate anywhere in Mathlib**.
- **Frobenius**: `Mathlib/RingTheory/Frobenius.lean` (`IsArithFrobAt`, existence/uniqueness) — consumed by FLT's `Frobenius.lean` (see N8).
- **Adeles/ideles**: `Mathlib/NumberTheory/NumberField/AdeleRing.lean` incl. `AdeleRing.cocompact`; `Topology/Algebra/RestrictedProduct/{Basic,TopologicalSpace,Units}.lean` (idele groups as restricted-product units). The *statement* language for global CFT (π₀ of the idele class group) is essentially available.
- **Brauer**: `Mathlib/Algebra/BrauerGroup/Defs.lean` only — group-law prerequisites mid-PR from the "brauergroup" repo (per `FLT/Mathlib/LinearAlgebra/Determinant.lean:62`). No Br(local field) ≅ ℚ/ℤ, no Hasse invariant.
- **Kummer**: `Mathlib/FieldTheory/KummerExtension.lean` exists (plus `KummerDedekind` for factorization, unrelated). Sufficient for N1-style tame arguments.
- **Ramification/inertia**: `Mathlib/NumberTheory/RamificationInertia/{Basic,Galois,Inertia,Unramified,HilbertTheory,Valuation}.lean` — inertia groups and Hilbert-theory decomposition exist at the Dedekind-domain level.

**Absent from Mathlib**: local or global reciprocity maps, Weil groups, Lubin–Tate formal
groups, local Tate duality, Euler characteristic formulas, Poitou–Tate, ray class fields /
existence theorem, Grunwald–Wang, Hasse norm theorem, Br(K_v) computation.

In-flight external projects (URL-checked 2026-08-14):

- https://github.com/kbuzzard/ClassFieldTheory — "ongoing project to formalize the main theorems of local and global class field theory", hub of the July 2025 Clay/CMI-HIMR Oxford summer school; 315 commits, active, blueprint at kbuzzard.github.io/ClassFieldTheory/blueprint/. This is the designated long-term home for N4/N5/N6-grade theory; blueprint `chtopbestiary.tex` predates it but `:29` already outsources local CFT.
- https://github.com/mariainesdff/LocalClassFieldTheory (de Frutos-Fernández–Nuccio) — "Formalization of local fields, and eventually LCFT", 472 commits, has a `PR'ed files` directory (steady Mathlib upstreaming); foundation published as the CPP 2024 paper *A Formalization of Complete Discrete Valuation Rings and Local Fields* (arXiv:2310.01998). Lubin–Tate portion still in-repo, not in Mathlib.
- Mathlib-side: ContCohomology landing (above) + FLT's own CupProduct/homology files marked "destined for Mathlib" — group-cohomology pipeline is live and converging with the ClassFieldTheory project's needs.

## 5. Risks

1. **Statement-vs-proof ambiguity is the main planning risk.** Every genuine CFT theorem here is scheduled to be an axiom (`knownin1980s` / Assumptions list), so the near-term work is *stating* N3, N4, N5 — but N4/N5 statements need duality pairings (cup products, invariant maps), which drag in real formalization even at statement level (`chtopbestiary.tex:58`: Serre's `=` "may well actually be a definition, giving the map"). The ℤ/n-identification of H² cannot be axiomatized as a bare `Prop` without choosing normalizations (arith vs geom Frobenius, `chtopbestiary.tex:12-15`) — a wrong sign convention here silently corrupts every downstream consumer.
2. **`localTameAbelianInertiaGroup` is admitted cheating** (`AbsoluteGaloisGroup.lean:172-176` TODO). If the Kummer-theoretic subgroup is not proved equal to the honest kernel, N2's tameness hypothesis and LiftFunctor's deformation condition rest on a definition nobody has certified.
3. **Duplication/convergence risk** with kbuzzard/ClassFieldTheory: FLT may state Poitou–Tate one way while the CFT project builds another; the shared ContCohomology base mitigates but doesn't eliminate interface drift.
4. **Blueprint staleness**: `chtopbestiary.tex:96` (no Galois cohomology) and `:3` (unorganised appendix) are out of date relative to Mathlib; a fresh consumer audit at planning time should trust the Lean sources over the tex.
5. **Brauer/quaternion seam untracked**: nothing in blueprint states the local-global classification of quaternion algebras; if any future step needs "D unramified everywhere ⇒ D ≅ M₂" style facts (Hilbert reciprocity), that is an unbudgeted M–L item.

## 6. Size verdict (S/M/L/XL), cheap seams vs full theory

| # | Node | Size | Notes |
|---|------|------|-------|
| 1 | N1 justify tame-inertia hack (TODO) | **M** | unramified + Kummer theory only; no CFT |
| 2 | N3 *state* Skinner–Wiles trick as assumption | **S** | all vocabulary exists; matches Assumptions/README.md:36 |
| 3 | N2 cyclic base change: keep as `knownin1980s` | **S** (stated, sorry'd already) | proof permanently out of scope |
| 4 | N4 *state* local duality + Euler char (with maps) | **M–L** | needs invariant map as data; cup products in flight FLT-side |
| 5 | N4 *prove* local Tate duality + EP | **L** | classical cohomological CFT slice; natural home = ClassFieldTheory project |
| 6 | N5 state Poitou–Tate | **L** | nine-term sequence over restricted products; statement alone is heavy |
| 7 | N5 prove Poitou–Tate | **XL** | full global cohomological CFT |
| 8 | Local reciprocity (Lubin–Tate route) | **XL** standalone, **outsourced** | dFF–Nuccio 472-commit repo + Clay project |
| 9 | Global reciprocity + existence theorem | **XL** | multi-year; only N3/N6 consume it, both axiomatizable |
| 10 | N7 Brauer group law upstream | **M** (in flight) | quaternion consumers; Hasse invariants would be +L |

**Verdict.** The FLT project's actual CFT exposure is far smaller than "class field theory"
suggests. Cheap seams that fully unblock the critical path: (a) state the SW solvable-extension
trick as an assumption (S), (b) certify the tame-inertia definition (M), (c) state the local
Galois cohomology quartet with explicit maps (M–L, gated on FLT's own cup-product files). The
only unavoidable *proved* CFT-adjacent content on FLT's books is the local Galois cohomology
package if the lifting theorem's dimension count is to be proved rather than axiomatized (L),
and Poitou–Tate behind it (XL) — both plausibly delivered by the in-flight
kbuzzard/ClassFieldTheory + de Frutos-Fernández–Nuccio pipeline rather than by FLT itself.
Full local+global reciprocity is XL but is, by explicit project design
(`Assumptions/README.md`, `knownin1980s`), not on FLT's critical path.
