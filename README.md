# Coherence Calculus

This repository contains the public source for *Coherence Calculus*, a research
program in structural mathematics built around finite observability, reduction,
and closure from a deliberately narrow foundational bedrock. It includes the
monograph LaTeX sources, the Lean 4 formalization, and the build/audit tooling
used to inspect the current public release.

The project asks what mathematical structure is forced from a small explicit
foundational surface, what remains exact under finite observability and
reduction, and which later law-side conclusions require additional explicit
hypotheses. A central goal is to keep those boundaries visible: what is
derived, what is conditional, and what remains open.

From that effort, Coherence Calculus has emerged as a usable structural
calculus: a proved grammar for reduction, defect, and closure under finite
observability, with later law-side extensions kept explicitly conditional.

Mechanization is used here as a discipline, not decoration. The repository is
set up to make the dependency spine explicit, keep the foundational assumptions
narrow, and expose the project to adversarial inspection. The work is
exploratory, but it is not casual; effort is made to isolate overreach, record
conditional surfaces honestly, and keep the manuscript and formalization in
sync.

## Repository contents

- `manuscripts/monograph/`: LaTeX source for the current public monograph
- `CoherenceCalculus/`: Lean 4 formalization of the core certified development
- `CoherenceCalculusMathlibBridge/`: separate one-way mathlib validation package
- `supplemental/`: coverage, tag-audit, dashboard, flattening, and release-support scripts
- `build.sh`: public build entry point for the monograph, Lean audits, and dashboard artifacts

## Scope and status

This repository should be read as an active research effort, not as a finished
theory. Some parts are tightly formalized and mechanically checked; other parts
remain exploratory and are included because they appear structurally promising,
not because every broader interpretation is final.

The current monograph is organized in two broad layers:

1. Structural mathematics
   - bedrock, counting, horizon calculus, carrier forcing, and the continuum bridge
2. Law-side extensions
   - explicit additional hypotheses and the consequences proved from them

The Lean source still uses some historical lane names such as `PartIII` and
`PartIV`. Those names are retained for source stability; the README and
manuscript are the right place to read the current conceptual organization.

## Where to start

New readers may want to begin with:

1. `manuscripts/monograph/` for the current public monograph
2. `CoherenceCalculus/` for the bedrock and core certified Lean development
3. the tagged release and corresponding Zenodo snapshot for a stable public version
4. `CoherenceCalculusMathlibBridge/` only after the strict source lanes are clear

## Build and verification

From the repository root:

```bash
bash build.sh
```

This builds the monograph, runs the Lean certification/audit lanes, and
generates the dashboard and related reproducibility artifacts under
`artifacts/`.

The separate mathlib validation package can also be built directly:

```bash
cd CoherenceCalculusMathlibBridge
lake build
```

## Scrutiny

This project is developed with an explicitly adversarial mindset toward its own
claims. Effort is made to expose hidden assumptions, isolate exact dependency
surfaces, and separate verified results from forward-looking extensions.
Critical issues, counterexamples, boundary cases, and structural objections are
useful and welcome. If something is wrong, unclear, overstated, or fails under
closer scrutiny, please open an issue.

## Releases

Public source snapshots are intended to be tied to tagged repository releases
and corresponding Zenodo records. The repository is the living source tree; a
release tag is the citation target for a specific public snapshot.

## Licensing

- Software and source code in this repository, including Lean files and build scripts, are licensed under the MIT License; see `LICENSE`.
- Manuscript text, figures, and other non-software content are licensed under CC BY 4.0; see `LICENSE-docs`.
