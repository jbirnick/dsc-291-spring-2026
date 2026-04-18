# DSC 291 — Formal Learning Theory (Spring 2026)

This repository is used for creating homework submissions and presentations for a university course. It contains:
- Typst files for homework submissions and slides
- Python code for coding tasks and plots
- Lean code for formal proofs

## Structure

- Each homework lives in `hwN/` with a `main.typ` (Typst source).
- Lecture slides live in `slides/` as `slides_N.pdf` (one per week).
- `README.md` is the repo-level description.

## Lecture Topics by Week

- **Week 1 — Why Learning Theory?** Online prediction, the No-Free-Lunch Theorem, how structure helps (hypothesis classes), Halving algorithm (finite classes), Perceptron (linear predictors with margin).
- **Week 2 — The combinatorial core of learning.** Restriction and growth function, shattering and VC dimension, Sauer-Shelah lemma.
- **Week 3 — Transductive, i.i.d., and PAC learning.** Classical (Vapnik) transductive setting, the i.i.d. model, PAC learning.

## Guidelines

- Homework is written in **Typst**. Do not convert to LaTeX or other formats.
- Be mathematically rigorous. Proofs must be precise and complete — no hand-waving.
- Be concise. Avoid unnecessary prose; let the math speak.
- Do not modify the homework template preamble unless asked.
- When editing `main.typ`, preserve the existing document structure and formatting conventions.
- Do not commit compiled PDFs or auxiliary build artifacts.
