# AGENTS.md

## Repository purpose

This repository contains coursework for DSC 291 (Formal Learning Theory, Spring 2026). The main source artifacts are:

- Typst documents for homework submissions and slides
- Python scripts for experiments and plots
- Lean formalizations for proof-oriented work

Keep changes aligned with an academic course repository: correctness and clarity matter more than feature work.

## Repository layout

- `hwN/`: homework source, typically with `main.typ`
- `slides/`: lecture slide sources and related material
- `formalization-perceptron/`: Lean formalizations and a Typst presentation
- `README.md`: short repo description

## General expectations

- Prefer editing source files (`.typ`, `.py`, `.lean`) rather than generated outputs (`.pdf`, `.png`).
- Do not convert Typst content to LaTeX or another format.
- Preserve the existing structure and formatting conventions of each file you edit.
- Be mathematically rigorous and concise. Proofs should be complete, precise, and not padded with unnecessary prose.
- Do not modify homework template macros, document preambles, or course metadata unless the task explicitly requires it.
- Avoid adding new dependencies or changing toolchain versions unless explicitly asked.

## Typst guidance

Applies to homework and slide sources.

- Keep the existing document structure intact.
- Reuse the local macros and formatting patterns already present in the file.
- When revising mathematical exposition, favor short, direct statements over narrative explanation.
- Only update compiled PDFs when the task explicitly calls for regenerated deliverables.

## Python guidance

Applies to scripts such as those in `hw1/`.

- Keep scripts simple and dependency-light; prefer the existing `numpy`-based style.
- Preserve deterministic behavior when randomness is involved.
- Match the surrounding style: short functions, straightforward control flow, and concise docstrings.

## Lean guidance

Applies under `formalization-perceptron/`.

- Follow the existing Lake project structure.
- Keep theorem and lemma names consistent with nearby files.
- Prefer small helper lemmas over large monolithic proofs when a proof needs restructuring.
- Do not change `lean-toolchain`, `lakefile.toml`, or mathlib revisions unless explicitly asked.

## Validation

Run the narrowest relevant checks after making changes.

- Typst: `typst compile path/to/main.typ`
- Python: `python3 path/to/script.py`
- Lean: `cd path/to/lean-project && lake build`

If a change affects only documentation-style guidance files such as `AGENTS.md`, no additional build step is required.
