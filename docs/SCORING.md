# Snippet Scoring System

The pfuzz tool now includes a snippet scoring system that evaluates snippet compatibility with available simulators and synthesizers, then uses these scores to weight snippet injection probability.

## Overview

The scoring system addresses the issue where "bad" snippets (that cause compilation failures) are injected as frequently as "good" snippets (that compile and simulate successfully), leading to excessive compiler failures.

## How It Works

1. **Tool Evaluation**: Each snippet is tested against available simulators and synthesizers
2. **Score Calculation**:
   - Simulators: 1 point for compilation success, +1 additional for simulation success (max 2 per simulator)
   - Synthesizers: 1 point for successful synthesis/transformation (max 1 per synthesizer)
3. **Probability Calculation**: `probability = reached_score / max_possible_score`
4. **Weighted Injection**: Snippets with higher scores are injected more frequently during fuzzing

## Usage

```bash
# Alternative scoring method
./scripts/score_snippets.sh
```

## Score File Format

Score files (`.sscr`) are created alongside each snippet file and contain 6 numbers:

```txt
2      # number of simulators
1      # number of synthesizers  
3      # simulator score achieved
1      # synthesizer score achieved
5      # maximum possible score (2*n_simulators + 1*n_synthesizers)
4      # total reached score (score_sim + score_synth)
```

This example shows a snippet that compiled successfully on all simulators (2 points each) plus simulated on one (1 additional point), and synthesized successfully (1 point), for a final probability of 4/5 = 0.8.

## Supported Tools

**Simulators:**

- IVerilog - Open source Verilog simulator
- Verilator - C++ based Verilog simulator  
- CXXRTL - Yosys-based C++ simulation (requires Yosys)
- CXXSLG - CXXRTL with Slang frontend (requires Yosys + Slang)

**Synthesizers:**

- Yosys - Open source synthesis suite
- SV2V - SystemVerilog to Verilog converter
