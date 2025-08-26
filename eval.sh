#!/bin/bash
cd ~/Documents/GitHub/Putnam-Bench-tests
lean_code=$(python3 eval.py)

# run crewai agent with lean_code as the context
cd ~/Documents/GitHub/Putnam-Bench-tests/lean4_formalizer
crewai install
crewai run "$lean_code"