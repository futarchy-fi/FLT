# Moret–Bailly chapter map (FLT-on-Lean, bead `lsb1u.8`)

Scope is read-only inspection of `/Users/kas/FLT`; no network lookup was attempted.  “Size” is the estimated formalisation effort for a real Lean theorem, not the effort to paste an opaque axiom.

## Verdict and search audit

The blueprint **does use** Moret–Bailly in the intended Taylor-style potential-modularity route: it lists the result among the required machinery (`blueprint/src/chapter/ch04overview.tex:21-33`), puts `moret-bailly` in the modularity-lifting theorem’s dependency list (`blueprint/src/chapter/ch04overview.tex:66-76`), and explicitly uses it to choose `F,p,E/F` in the potential-modularity sketch (`blueprint/src/chapter/ch04overview.tex:93-98`).  The standalone theorem is present but marked `\notready` (`blueprint/src/chapter/chtopbestiary.tex:253-266`), and the document says Lean does not yet have even a definition of a curve over a field (`blueprint/src/chapter/chtopbestiary.tex:268`).

The current Lean implementation has **no implemented Moret–Bailly/potential-modularity route**.  An exhaustive, case-insensitive fixed-string search was run over blueprint LaTeX/BibTeX/style files, `FLT/Assumptions` (`.lean`/`.md`), and all project `.lean` files (generated `/.lake/` files excluded), for: `Moret-Bailly`, TeX `Moret--Bailly`, Unicode `Moret–Bailly`, `Moret Bailly`, `prescribed`, `prescribed local`, `local behaviour`, `local behavior`, `potential modularity`, `potentially modular`, `potentially modularity`, broad `potential`, and broad `modularity`.

| scope | `Moret-Bailly` | `Moret--Bailly` | `prescribed` | `prescribed local` | `local behaviour` | `potential modularity` | `potentially modular` | broad `modularity` |
|---|---:|---:|---:|---:|---:|---:|---:|
| `blueprint/src` (`.tex/.bib/.sty`) | 7 lines / 4 files | 2 / 1 | 1 / 1 | 0 (TeX line break) | 1 / 1 | 2 / 1 | 1 / 1 | 23 / 7 |
| `FLT/Assumptions` | 1 / 1 | 0 | 2 / 1 | 0 | 0 | 0 | 0 | 2 / 2 |
| all project `.lean` | 0 | 0 | 1 / 1 (unrelated) | 0 | 0 | 0 | 0 | 5 / 5 |

The Unicode `Moret–Bailly` and space-separated `Moret Bailly` variants both returned zero in all three scopes.

The zero Lean counts are not the whole argument: the main spine is visibly a placeholder at `FLT/Proof.lean:98-105` (`B4_proof : B4 := sorry`, then the B3/B2/B1 chain), while the completed reduction from no Frey package is elementary at `FLT/FreyCurve/FreyPackage.lean:217-226`.  The five Lean `modularity` hits are documentation/history only (for example `FLT/FreyCurve/FreyPackage.lean:59-73`, `FLT/Assumptions/Mazur.lean:72-79`, and `FLT/Assumptions/Odlyzko.lean:30-41`); the one Lean `prescribed` hit is an unrelated “prescribed flat / finite ramification” comment (`FLT/GaloisRepresentation/HardlyRamified/Defs.lean:17-20`), and the one Lean `potential` hit is unrelated topology documentation (`FLT/Mathlib/Topology/Algebra/ContinuousSMulDiscrete.lean:15`).  None names Moret–Bailly or potential modularity.  Thus “bypassed” is not a proved alternative route: it is an unimplemented gap currently hidden behind `sorry`.

The only blueprint reference attached to the Wiles/Frey endpoint is also a comment, not an active dependency (`blueprint/src/chapter/ch02reductions.tex:193-205`, especially line 202).  The bibliography identifies the intended source as Moret–Bailly, *Groupes de Picard et problèmes de Skolem. I, II*, Ann. Sci. ENS 22 (1989), 161–179 and 181–194 (`blueprint/src/FLT.bib:64-78`) (literature-verify).

## Weakest sufficient statement for this route

For the written Taylor-style sketch, the weakest useful interface is the following application corollary (strictly weaker than the general theorem below): for every hardly-ramified irreducible `ρ : G_Q → GL₂(F_ℓ)` as in the overview, with kernel field `K`, there are a totally real, even-degree, Galois `F/Q` (unramified at `ℓ` and disjoint from `K`), an auxiliary prime `p`, and an elliptic curve `E/F` such that

1. `E[ℓ] ≅ ρ|G_F`;
2. `E[p]` is induced from a character; and
3. the prescribed local conditions make the stated modularity-lifting theorem applicable.

This is exactly the data consumed by the sketch (`blueprint/src/chapter/ch04overview.tex:21-24` and `:93-98`).  If one only wants the headline potential-modularity conclusion, it can be weakened further to existence of such an `F` with `ρ|G_F` modular (`blueprint/src/chapter/ch04overview.tex:21-24`); the `p,E` clauses are needed for the displayed Taylor-style construction.

## Numbered chapter/node map

1. **Moret–Bailly local-point theorem (statement). — XL.**  Input: `K^avoid/K`, finitely many places `S`, local Galois extensions `L_v/K_v`, a smooth geometrically connected curve `T/K`, and nonempty invariant open sets `Ω_v`; output: a finite Galois `L/K`, linearly disjoint from `K^avoid`, with matching completions and `P ∈ T(L)` in every `Ω_v` (`blueprint/src/chapter/chtopbestiary.tex:253-266`).  Edges: nodes 2 and 3 → this node; this node → node 4.  The statement is `\notready` and currently unexpressible with the available curve language (`blueprint/src/chapter/chtopbestiary.tex:255-268`).

2. **Curves, elliptic/modular/Shimura moduli, and points. — XL.**  The blueprint asks for Shimura curves/surfaces and their Galois/automorphic cohomology (`blueprint/src/chapter/chtopbestiary.tex:247-251`) but immediately records that Lean lacks a definition of a curve over a field (`:268`).  Existing anchors are only elliptic Weierstrass curves imported by `FLT/FreyCurve/FreyPackage.lean:8-18` and the concrete Frey-curve data described at `:59-73`; these do not supply the general `T/K`, `Ω_v`, or Shimura geometry required by node 1.

3. **Local/global field engineering and prescribed conditions. — L–XL.**  The overview requires `F` to be totally real, even degree, Galois, `ℓ`-unramified, and disjoint from `K` (`blueprint/src/chapter/ch04overview.tex:21-24`), and lists global class field theory, Jacquet–Langlands, induced-representation converse theorems, and modularity lifting as additional machinery (`:25-33`).  The local input format (completions, inertia, residue fields) is spelled out at `:40-56`.  Edges: node 3 → nodes 1 and 4; the local cohomology/automorphic anchors named by `:68-72` feed node 5.

4. **Potential-modularity application (Taylor-style `F,p,E` construction). — XL.**  Moret–Bailly is used here to find `F,p,E`, then converse theorems and Jacquet–Langlands give mod-`p` modularity, and modularity lifting gives the `ℓ`-torsion conclusion (`blueprint/src/chapter/ch04overview.tex:93-98`).  Edges: nodes 1–3 → node 4; node 5 → node 4's final lift.  The blueprint supplies only a sketch, not the local open sets or the moduli map that instantiate them.

5. **Modularity-lifting theorem interface and proof. — XL.**  The theorem is explicitly `\notready` and says the project is “very far” from stating it in Lean (`blueprint/src/chapter/ch04overview.tex:66-82`); its declared dependencies include `moret-bailly`, local Galois cohomology, automorphic decomposition, and Galois representations (`:68-72`).  Edges: node 5 → node 4 and the eventual B4 endpoint.  This is a separate XL project even after node 1 is available.

6. **FLT endpoint (B4) and current Lean spine. — XL (or S as an opaque assumption).**  The LaTeX endpoint is Wiles/Taylor–Wiles/Ribet's reducibility theorem, whose proof is explicitly omitted (`blueprint/src/chapter/ch02reductions.tex:193-206`).  In Lean, `FLT/Proof.lean:39-60` defines B1–B4, `:78-96` proves the reduction B4 → B3 using Mazur, and `:98-105` leaves B4 as `sorry` before deriving B3, B2, and B1.  `FLT/Proof.lean:8-11` imports only basic/Frey/torsion/Mazur modules; no Moret–Bailly interface is connected to this spine (the exhaustive Lean search above is zero).

7. **Assumption registration / stopgap. — M for an opaque axiom; XL for proof.**  `FLT/Assumptions/README.md:31-40` classifies Moret–Bailly as “formalizable” (not a formalized axiom).  The directory contains only `KnownIn1980s.lean`, `Mazur.lean`, `Odlyzko.lean`, and `README.md`; `FLT/FLT.lean:3-5` imports only the existing three assumption modules.  A short-term `MoretBailly_statement` assumption could unblock node 6, but it would document the gap rather than implement the theorem.

## Dependency edges to preserve

- **Blueprint dependency:** `ch04overview.tex:27-32` (listed machinery) → `:66-76` (MLT interface with `moret-bailly`) → `:93-98` (application).  The `ch02reductions.tex:202` edge is commented and therefore non-operative.
- **Geometry dependency:** `chtopbestiary.tex:247-268` (Shimura/curve prerequisites and missing Lean curve definition) → node 1.
- **Lean FLT spine:** `FLT/FreyCurve/FreyPackage.lean:217-226` → `FLT/Proof.lean:78-81` (B3 → B2) → `FLT/Proof.lean:98-105` (B4 placeholder → B1).  The existing Frey/Mazur anchor is `FLT/Proof.lean:83-96` and `FLT/FreyCurve/Mazur.lean:30-36`.
- **Hardly-ramified planned machinery:** the representation property is defined at `FLT/GaloisRepresentation/HardlyRamified/Defs.lean:17-20,90-120`; lifting and compatible-family theorems are still `sorry` at `FLT/GaloisRepresentation/HardlyRamified/Lift.lean:34-48` and `.../Family.lean:37-68`.  These are relevant downstream, but neither imports nor invokes Moret–Bailly.

## Literature inventory (all items require literature verification)

1. Moret–Bailly (1989), *Groupes de Picard et problèmes de Skolem. I, II* — the exact bibliography entry used by the blueprint (`blueprint/src/FLT.bib:64-78`) (literature-verify).
2. Barnet-Lamb–Gee–Geraghty–Taylor (2014), *Potential automorphy and change of weight* (`blueprint/src/FLT.bib:80-95`) (literature-verify); modern potential-automorphy context, not evidence that the current Lean route uses it.
3. Taylor (2006), *On the meromorphic continuation of degree two (L)-functions* (`blueprint/src/FLT.bib:51-62`); the overview calls its Theorem 3.3 a near-reference with stronger splitting hypotheses (`blueprint/src/chapter/ch04overview.tex:81-82`) (literature-verify).
4. Gee (2022), *Modularity lifting theorems* (`blueprint/src/FLT.bib:178-192`); the overview calls Theorem 5.2 a near-reference with a stronger image hypothesis (`blueprint/src/chapter/ch04overview.tex:81-82`) (literature-verify).
5. Khare–Wintenberger (2009), *Serre's modularity conjecture II* (`blueprint/src/FLT.bib:321-335`), relevant to the later potentially modular lift mentioned at `blueprint/src/chapter/ch04overview.tex:100-105` (literature-verify).

## Route risks and overall size verdict

- The general theorem quantifies over curves, local completions, invariant opens, and linear disjointness, while the blueprint marks it `\notready` and lacks curves in Lean (`blueprint/src/chapter/chtopbestiary.tex:255-268`).
- The application never specifies the actual modular/Shimura curve or the `Ω_v` that force the `E[ℓ]` and induced `E[p]` conditions (`blueprint/src/chapter/ch04overview.tex:93-98`); constructing these is the main mathematical risk.
- The MLT itself is `\notready` and “very far” from Lean (`blueprint/src/chapter/ch04overview.tex:66-82`), and the Lean B4 proof is still `sorry` (`FLT/Proof.lean:98-105`), so a zero-symbol Lean search cannot certify a genuine bypass.

**Overall verdict: XL for a proved, reusable Moret–Bailly chapter and its Taylor-style application; M/S only for an explicitly labeled opaque assumption.  The campaign should track it as a planned blueprint dependency, currently unimplemented in Lean, rather than as a completed bypass.**
